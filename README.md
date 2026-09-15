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
* `RearmBarrier/TreeModel.lean` is the completion tree. Where the crate
  keeps a flat heap-indexed array, the model keeps an inductive tree whose
  nodes own a window of consumers and count `(version, finished)`; the
  crate's counter is `size * version + finished` and its `WORKERS *
  (version + 1)` test is "the node covering every worker fills". The
  mapping to the crate's flat state goes both ways: `heapIndex` and
  `pathOfIndex` translate between paths and heap indices (proved inverse
  by `heapIndex_pathOfIndex` and `pathOfIndex_heapIndex`), and
  `toCounters` / `ofCounters` translate between the tree and the counter
  array, which is how traces from the crate, which name tickets by heap
  index, are replayed. The file also checks the counting invariant in
  every state: a leaf's `finished` is the number of its consumers past
  their `fetch_add`, a live inner node's `finished` plus the contributions
  in flight towards it is the size of its children one version ahead, and
  the ancestors of the node covering every worker are never touched.
* `RearmBarrier/TreeProofs.lean` proves the executable tree's basic
  properties: `modifyAt` changes exactly the node at its path and, for a
  window-preserving update, no window anywhere (`get_modifyAt_self`,
  `get_window_modifyAt`); `Tree.walk` is one `fetch_add` on the node under
  the cursor, with the crate's ticket index, the cursor's amount and the
  node's counter as `old`, leaving that counter at `old + amount` and every
  window unchanged (`walk_spec`); its decision is the crate's, `if new_val ==
  WORKERS * (v + 1) { finished } else if ticket_id == 0 || new_val !=
  target_val * (v + 1) { stop } else { continue at (ticket_id - 1) /
  CLUSTER with target_val }` (`walk_crate`); `Tree.build` places a node of
  height `h` at `lo` over `[lo, lo + C ^ (h + 1)) ∩ [0, W)` (`build_lo`,
  `build_hi`) and the root of every valid configuration covers exactly
  `[0, WORKERS)` (`init_root_size`), which is where the crate's
  `ticket_tree_alloc` loop enters (`pow_levels_ge`). Well-formedness
  (`Wf`: every node covers a non-empty window inside `[0, WORKERS)`, leaves
  at most `CLUSTER` consumers, inner nodes at most `CLUSTER` children whose
  windows tile the parent's) holds for `Tree.init` (`init_wf`), is kept by
  every walk step (`walk_wf`), gives every node's `target_val` as the sum of
  its children's (`Wf.sum_children`), and discharges the side conditions of
  the decision theorem along every execution (`walk_crate_wf`).
* `RearmBarrier/TreeInvariant.lean` restates the counting invariant as a
  proposition, `TreeInv`, indexed by paths (so no induction over the nested
  tree is needed) and abstracting the consumers as a function, and proves
  that every consumer step preserves it: the `fetch_add` on a ticket
  (`walk_preserves`, the core: the node under the cursor, its parent, and
  every other node), the steps that only change a phase
  (`phase_preserves`), starting to walk at the consumer's leaf
  (`startWalk_preserves`), and, once every consumer has finished the
  version, moving the invariant to the next version (`advance_preserves`,
  which shows every live node has advanced). The hypotheses are exactly
  what the global protocol supplies: a walking consumer is at the
  producer's version and below `count`.
* `RearmBarrier/Completion.lean` is the proved part of the protocol. It isolates one
  version's completion as a "game" on the tree, meaning a nondeterministic
  transition system (a `Step` relation whose rules may fire anywhere, in
  any order; a run is any sequence of steps): consumers are unit leaves, a
  consumer finishing or a pending child being applied to its parent are
  the two moves, and applying joins the child's clock into the parent's
  (the `AcqRel` `fetch_add`).
  For every tree shape and every sequence of moves it proves that the
  counting invariant is preserved, that a done node has every consumer
  below it finished and a clock dominating all of theirs (the
  happens-before edge from every result write to the completing
  `fetch_add`), that a done node never changes again (the barrier
  completes exactly once), and that once every consumer has finished a
  move is always possible while the root is not done and every move
  decreases a measure, so any ordering of completion events finishes.
  The theorems use only `propext`, `Quot.sound` and `Classical.choice`.
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

What is proved versus checked: the completion game in `Completion.lean`
is proved for all shapes and all orderings; so are the path/index mapping
and, for the executable tree, the update, the single-step behaviour of
`walk` and its agreement with the crate's decision rule, and the window of
the root. Not proved: the global protocol invariant relating the probe, the
producer's phase and the consumers' versions, which is what turns the
per-step results of `TreeInvariant.lean` into a theorem about `step` on
`State` (the initial state's `leaves` / `leaf_unique` facts about
`Cursor.start` are also still unproved), and the refinement from the
executable tree to the game; these are checked by exploration and by
replaying crate traces. The
step from the completing `fetch_add` to the producer's `complete` (one
Release on the probe, one Acquire fence) and the per-version re-arming are
likewise only checked. Not covered at all: stale relaxed loads that change
control flow (they cannot here, since every spin condition is monotone in
a counter that only grows), and the `panic` paths for duplicate producers
or consumers.
