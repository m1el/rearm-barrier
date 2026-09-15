# Contention model

`examples/contention.rs` models what one barrier round costs in cache-line
transfers, gives a lower bound for *any* spin-waiting barrier with
`RearmBarrier`'s interface under the same rules, and fits the model's costs to
`benches/barrier.rs` output. The ratio *measured / bound* is the answer to "is
this near optimal?", as far as the model is believed.

```
cargo run --release --example contention -- sim --workers 63,255,767 --results skip
cargo run --release --example contention -- fit --min-workers 7 docs/contention/corey-3970x-sweep.txt
cargo run --release --example contention -- check TRACE..   # counter writes vs. real crate traces
```

## Rules

Cores run the barrier programs over cache lines (every `CacheLine` in the
crate is one line). A core either holds a valid copy of a line or does not.

| access | condition | cost |
|---|---|---|
| read (load, spin check) | holder | 0 |
| read | not a holder (**pull**) | `t` |
| write (`fetch_add`) | sole holder | 0 |
| write | holder among others (**upgrade**) | `u` |
| write | not a holder (**RFO**) | `t` |

A write makes the writer the only holder. A spinning core re-checks a line it
holds for free. When someone else writes it, the spinner must pull it again,
and then acts after an extra delay drawn from an exponential distribution with
mean `jitter`. That delay stands for the spin-loop period, SMT siblings,
interrupts and so on.

Lines serve transfers under one of two *disciplines*:

- **serial**: one transfer at a time per line.
- **parallel**: any number of pulls at once, writes exclusive.

A core always does one thing at a time.

The programs are the crate's (`rearm:C`) and the benchmark's single shared
counter (`atomic`). Either can take `+split`, a what-if the crate does not
implement: workers spin on a publish line and the producer spins on a separate
done line, so idle workers stop pulling the finish write.

The counter walk is the crate's own code, including the tree layout (checked
against `ticket_storage`). `contention check` confirms, on real traces, that
the crate does exactly the model's number of counter writes every round.
Checked shapes: (1,2), (5,2), (5,4), (6,8), (7,2), (7,3).

## Formulas

`W` workers, fan-in `C`, `h` tree levels above the leaves, `F` work per worker,
`R = 1` if the producer reads every result each round, `H_W = 1 + 1/2 + … + 1/W ≈ ln W + 0.58`.

**Transfers per round** (upper estimates; the simulation counts the exact ones):

- pulls: `2W` of the probe (`W + 1` with split), `W` of the job, `R·W` of results
- RFOs: one per counter write shared by more than one worker. That is `W` for `atomic`, and `W` plus about `W/(C-1)` tree updates for `rearm`.
- upgrades: publish, job, finish, and `R·W` result writes

**Time per round, parallel lines**, valid when `jitter ≫ C·t` so workers reach
shared counters one at a time (`closed_time_parallel`):

```
T ≈ 2u + 2t + jitter·H_W + F + R·u + (1 + h)·t + u + t + jitter + R·W·t
```

For `atomic`, and whenever a counter is shared by many workers relative to
`jitter/t`, the writes queue and cost up to `W·t` more. That is where the tree
pays off (see below).

**Time per round, serial lines** (`closed_time`):

```
T ≈ 2u + (W + 1)·t + F + R·u + (1 + h)·t + u + k·t + R·W·t + jitter·(H_W + 1)
```

Here `k` is the producer's wait to pull the finish write:
- `k = 1` with split;
- otherwise `k = (W + 1)/2` (it is behind half of the idle spinners) when results are read;
- otherwise `k = W`.

Both closed forms agree with the simulation to within a few percent wherever
they apply.

**Lower bound** for any barrier with this interface (`lower_bound`), with `m = min(t, u)`:

```
LB = S(W) + jitter·H_W + F + m + max(t, ⌈log₂ W⌉·m + t) + jitter
     and, if results are read, at least  2m + t + F + W·t
```

Why each term is there:

- **`S(W)`** is the fastest way to get the job to `W` cores. It is `m + t` with
  parallel lines. With serial lines it is the fastest "write a line, someone
  pulls it" spreading schedule, which grows logarithmically.
- **`jitter·H_W`**: every worker has to notice the job by spinning, and the
  round waits for the slowest. `H_W` is the expected maximum of `W`
  independent unit exponentials, whatever the design.
- **`⌈log₂ W⌉·m`**: each transfer merges what one core and one line know, so
  the largest known set of completions at most doubles per transfer.
- **`W·t`**: the producer is a single core and `complete` hands it `W`
  distinct result lines.

The bound holds in expectation. Simulated means carry about ±1.5% sampling
noise at 200 rounds, so an occasional gap of 0.98× is noise.

## Fit to a Threadripper 3970X (64 threads)

Data: `docs/contention/corey-3970x-sweep.txt`. It has 90 rows, for 1 to 63
workers, with results read and skipped, `C` = 2, 4, 16 and 64 and `atomic`,
and 5 trials × 300 ms each.

**Worker counts below 7 do not fit (35% error).** The measured time jumps from
~130 ns at 1 worker to ~1200 ns at 7. The 3970X's cores come in groups of 4
that share an L3 cache (Zen 2 CCXs), and one uniform `t` cannot describe both
transfers within a group and transfers between groups. The fits below use
`--min-workers 7`.

| discipline | t | u | jitter | constant | rms error |
|---|---|---|---|---|---|
| serial | 14.1 ns | 0 | 226 ns | 232 ns | 10.1% |
| parallel | 21.3 ns | 0 | 340 ns | 0 | 10.7% |

About 10% is roughly the run-to-run noise of the benchmark. So both fits
explain the data, and the sweep cannot choose between them outright. At the
top end, parallel matches better:

| W = 63, rearm C=4 and atomic, mean | measured | serial model | parallel model |
|---|---|---|---|
| results skip | 2129 ns | 2590 ns (+22%) | 2048 ns (−4%) |
| results read | 3408 ns | 3450 ns | 3390 ns |

Both miss a bump at W = 31 with results read (2980 ns measured, about 2.4 µs
predicted).

Two things the data does show clearly:

- **Reading results costs about 20 ns per worker at large W.** That is the
  producer pulling `W` lines one after another, and it matches `R·W·t`.
- **The growth is logarithmic, not linear**, and it is the same for every
  design. The dominant term is `jitter·H_W`, waiting for the slowest spinner,
  which no design avoids.

## Verdict

**Up to 64 threads the crate is near optimal in this model.** Measured over the
bound is 1.1–1.5× with results skipped. With results read it is 1.2–2.2×,
where the bound already includes the producer's `W·t` result pulls. Every
design tested is within noise of every other, so the ticket tree neither helps
nor hurts at this size.

**Beyond 64 threads the two disciplines disagree**, and it matters. With the
fitted costs:

| W | results skip | rearm C=16 | atomic | rearm C=16+split |
|---|---|---|---|---|
| 767 | parallel lines | 1.04× bound | 5.9× | 1.05× |
| 767 | serial lines | 8.3× | 8.3× | 5.7× |

- **If pulls of a hot line can happen in parallel** (the better fit at W = 63),
  the tree is what keeps the crate near the bound. A single counter queues
  `W·t` on its cache line. The remaining cost is jitter, and a cheaper spin
  loop is the only lever.
- **If a line serves one core at a time**, the probe is the bottleneck. All
  `W` workers pull it after a publish, and the idle ones pull it again after a
  finish. The tree is irrelevant, and splitting the probe into publish and done
  lines is the fix: it removes about `W·t` per round.

Settling this needs a sweep on a machine with ≥ 256 hardware threads, or a
microbenchmark of `N` spinners detecting one write as `N` grows. Both are
cheap to run with the existing tools: `cargo bench --bench barrier --
--workers sweep --results skip`, then `contention fit`.

## Not modeled

- **Topology.** A single `t` covers transfers within a cache group and across
  groups. This is why W < 7 does not fit.
- **Hardware details.** No prefetching, cache capacity, or store-to-load
  forwarding.
- **The mutex baseline.** It blocks in the kernel.
- **Work.** Rows with `work > 0` are ignored by `fit`, since the cost of the
  xorshift work is not calibrated.
