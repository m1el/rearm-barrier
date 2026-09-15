# rearm-barrier

A re-arming broadcast barrier for low-latency benchmarking of tasks across a
fixed set of worker threads. `no_std`, allocation-free, stable Rust.

One producer builds a job, it is broadcast to `WORKERS` consumers behind a
shared reference, every consumer processes it and writes into its own
cache-line-aligned result slot, the producer observes all results, and the
barrier re-arms for the next job. All waiting is by spinning.

Completion is tracked through a tree of counters with fan-in `CLUSTER`, so
finishing workers touch different cache lines instead of one hot counter.

```rust
use rearm_barrier::RearmBarrier;

const WORKERS: usize = 4;
let barrier = RearmBarrier::<u64, u64, WORKERS, 2>::new();

std::thread::scope(|s| {
    for id in 0..WORKERS {
        let barrier = &barrier;
        s.spawn(move || {
            barrier.consumer(100, id, 0, |_version, job, result| {
                *result = job * id as u64;
            });
        });
    }

    barrier.producer(100, |version| version as u64 + 1, |version, results| {
        for (id, r) in results.iter().enumerate() {
            assert_eq!(**r, (version as u64 + 1) * id as u64);
        }
    });
});
```

`RearmBarrier::new` is a `const fn`, so a barrier can live in a `static`.
Invalid configurations (`WORKERS == 0`, `CLUSTER < 2`) are rejected at
compile time.

## Testing

```
cargo test --release
```

## Formal model

`model/` is a Lean 4 project (no Mathlib) that models the barrier as a
transition system and is differentially tested against the crate.

* `RearmBarrier/Tree.lean` mirrors `ticket_tree_alloc` / `ticket_storage`
  and proves the compile-time sizing claim
  `ticket_storage(w, c) <= 2 * w` for every `w >= 1`, `c >= 2`, that the
  ticket walk terminates, and that its first ticket is in bounds.
* `RearmBarrier/Model.lean` is the state machine: one step per atomic
  operation (or successful spin-loop exit) of `producer` and `consumer`,
  with the non-atomic accesses to the job and result slots split into
  begin/end steps so that overlapping accesses are visible as states.
  The atomics are interleaved sequentially consistently, which is exact
  for counters only ever modified by `fetch_add`; on top of that the model
  tracks C11 happens-before with vector clocks (the scheme of Miri's data
  race detector and loom), using the orderings of `src/lib.rs`: Release on
  publishing, AcqRel on the tickets, Release on finishing, and the Acquire
  fences after the spin loops. Every non-atomic access must happen after
  each conflicting earlier one, otherwise the step is a data race.
* `RearmBarrier/Spec.lean` states what the barrier promises: `func` sees
  the job of its version, `complete` sees every result of its version, no
  conflicting accesses to the job or result slots overlap, the walk stays
  inside `ticket_storage`, and the counters never run ahead.
* `RearmBarrier/Explore.lean` enumerates every interleaving of a small
  configuration and checks the invariants plus deadlock freedom.
* `RearmBarrier/Trace.lean` replays a trace recorded from the crate and
  decides whether it is an execution of the model.

```
cd model && lake build
.lake/build/bin/rearm-model explore 5 2 2        # every interleaving of 5 workers, fan-in 2, 2 versions
.lake/build/bin/rearm-model explore 3 2 2 consumer-fence   # ... with the consumer's Acquire fence removed
.lake/build/bin/rearm-model check trace.txt      # is this crate trace an execution of the model?
.lake/build/bin/rearm-model simulate 7 3 4 42    # a random execution of the model, in trace syntax
.lake/build/bin/rearm-model storage 64 8         # ticket_storage for every shape
```

### Differential testing

With the `trace` cargo feature, every atomic operation of the barrier reports
an event to a hook (`rearm_barrier::trace`); without the feature the hook is
an empty inline function. `examples/trace.rs` installs a hook that records
each thread's events in program order, runs a shape on real threads with
optional random delays, and prints the trace. `scripts/difftest.sh` then

1. compares `ticket_storage` between the crate and the model for every shape
   up to 4096 workers and fan-in 16,
2. exhaustively explores small shapes in the model, and
3. records traces from the crate for every shape in the harness and replays
   each on the model, which must accept it and find every invariant intact.

```
./scripts/difftest.sh                      # defaults: 10 traces per shape
ITERS=50 COUNT=200 ./scripts/difftest.sh   # longer
```

A trace is accepted only if the model, stepping each thread from the same
observed counter values, performs exactly the operations the crate recorded
(same tickets, same amounts, same spin-loop exits) and every invariant holds
along the way. If the crate hangs, the harness prints the events so far and
the checker reports whether the model agrees that they lead to a deadlock.

Weakening any single ordering (`publish`, `ticket`, `finish`,
`producer-fence`, `consumer-fence`) makes exploration report a data race
with the two accesses involved. Traces cannot exhibit ordering bugs, since
the hardware will not show them; the runtime oracle for orderings is
`cargo miri test`, whose data race detector uses the same happens-before
rules. Removing the consumer's Acquire fence, for example, is reported by
both Miri and `rearm-model explore` as a race between the producer's job
write and the consumer's read inside `func`.

What the model does not cover: stale relaxed loads that change control
flow (they cannot here, since every spin condition is monotone in a counter
that only grows), and the `panic` paths for duplicate producers or
consumers.
