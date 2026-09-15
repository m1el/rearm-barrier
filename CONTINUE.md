# Continuing the rearm-barrier verification

State of the work as of 2026-09-15, including `WeakMemory.lean`'s
history-based reduction with stale probe reads and separate fences.
Read [MEMORY_MODEL.md](MEMORY_MODEL.md) before claiming coverage of Rust
weak-memory executions: the operational reduction is proved, while the
full external event/state and clock correspondence remains open. A separate
`ExecutionOrder.lean` now proves the required graph-ordering lemma.

## What exists

- `src/lib.rs`: the crate. `trace` feature + `src/trace.rs` report every
  atomic op to a hook; `examples/trace.rs` records per-thread traces on real
  threads (watchdog dumps a partial trace with a trailing `timeout` line).
- `scripts/difftest.sh`: (1) diffs `ticket_storage` crate vs model for
  61,440 shapes, (2) exhaustive exploration of ten small shapes, (3) replays
  crate traces on the model (count depends on `MAX_WORKERS` and `ITERS`).
  Run it after any change to executable Lean.
  Env: `ITERS`, `COUNT`, `MAX_WORKERS`, `TIMEOUT`, `OUT`.
- `model/` (Lean 4.34.0, no Mathlib, `lake build`; binary
  `model/.lake/build/bin/rearm-model {explore|check|simulate|storage}`;
  `explore W C N [MAX_STATES] [publish|ticket|finish|producer-fence|consumer-fence]`
  weakens an ordering).

Executable definitions (their model safety properties are proved below):

| file | contents |
|---|---|
| `Basics.lean` | `Config`, `Orderings`, `VC` clocks, `Slot` (FastTrack hb), `Thread`, `Event` |
| `TreeModel.lean` | inductive `Tree` (nodes `(version, finished, rel, lo, hi, children)`), `build`/`buildChildren`, `get`/`modifyAt` by path, `heapIndex`/`pathOfIndex`, `toCounters`/`ofCounters`, `Cursor`, `ConsumerPhase`, `Tree.walk` (one `fetch_add`), `inFlightTo`, `Tree.nodeViolations` + `Tree.invariant`/`invariantChildren` (the executable check, loop-free and structurally recursive so it can be reasoned about) |
| `Model.lean` | `State`, producer/consumer steps, `step`, hb tracking, `writeAllSlots` |
| `Spec.lean`, `Explore.lean`, `Trace.lean`, `Main.lean` | `violations` (loop-free), `finalViolations`, DFS explorer, trace replay (greedy scheduler, complete by the argument in the file header), CLI |

Proved (all `sorry`-free, axioms only `propext`, `Quot.sound`, `Classical.choice`):

| file | main theorems |
|---|---|
| `Tree.lean` | `ticketStorage_le` (the crate's compile-time sizing claim), `parent_lt`, `start_ticket_lt` |
| `TreeProofs.lean` | `get_modifyAt_self`, `get_window_modifyAt`; `walk_spec` (walk = one fetch_add on the cursor node, updated node's version/counter stated explicitly); `walk_crate` / `walk_crate_wf` (tree's next move = crate's `if new_val == W*(v+1) … else if id==0 \|\| new_val != target*(v+1) … else continue (id-1)/C`); `build_lo/hi`, `rootHeight_pow`, `init_root_size`; `Wf` (windows tile), `Wf_build`, `init_wf`, `Wf.modifyAt`, `walk_wf`, `Wf.sum_children` |
| `TreeInvariant.lean` | `TreeInv cfg V phase t` (path-indexed Prop version of the counting invariant, consumers as `Nat → ConsumerPhase`); `walk_preserves` (via `nodeInv_self` / `nodeInv_parent` / `nodeInv_other`), `phase_preserves`, `startWalk_preserves`, `advance_preserves` (+ `all_advanced`) |
| `TreeInit.lean` | `get_build_char` (node at path q = `build (H-\|q\|) (digits q * C^(H-\|q\|+1))`), `init_leaves`, `init_leaf_unique`, `init_treeInv` |
| `StepInvariant.lean` | `phaseOf` (default `.start` out of range, so `phaseOf_replicate`), `phaseOf_setIfInBounds`, `step_consumer_move` (every consumer `step` = one `ConsumerMove` + `setConsumer`; also reports `s'.producer = s.producer` and `s'.probe = probeAfter s.probe ph`; the `waitReady` move records its guard), `step_producer_move` (`ProducerMove`: phase before/after and the probe after), `step_consumer_treeInv` (hypothesis `hV : walk/inFunc/finish v → v = V ∧ V < count`), `step_producer_treeInv`, `step_producer_unchanged` |
| `Protocol.lean` | the global invariant (`version_le_below`: versions do not decrease going down through live nodes). `ProducerPhase.version` (`done ↦ count`), `ProbeOk` (probe per producer phase), `ConsumerOk cfg V probe ph` (allowed consumer phases at probe `2V`, `2V+1`, `2V+2`), `Finished cfg V ph` (`waitReady (V+1)` or `done ∧ V+1 = count`), `InvAt cfg probe tree producer V consumers` (fields: `version`, `size`, `wf`, `tree : TreeInv`, `probeOk`, `version_lt`, `consumers`, `finisher` = "a consumer in `finish V` ⇒ every other one is `Finished`"), `Inv cfg s` (abbrev). `InvAt.active` (inFunc/walk/finish ⇒ version `V`, producer `waiting V`, probe `2V+1`), `others_done` (a node of size `W` at version `V+1` ⇒ every consumer is `finish V` or `Finished`; uses `descend`/`tiles_cover`/`below_advanced`/`size_le_of_below`), `step_producer_inv`, `step_consumer_inv`, `step_inv`, `init_inv`, `Reachable`, `reachable_inv`, `reachable_probe_le` (`probe ≤ 2·count` in every reachable state) |
| `Completion.lean` | one-version abstract protocol ("game" = nondeterministic `Step` relation on a nested `Node` type): `Step.inv`, `done_contributed`, `done_clock` (hb: done node's clock dominates every consumer's), `noStep_of_done`, `progress`, `Step.measure_lt`, `run_completes` |
| `TreeCheck.lean` | the executable check follows from the invariant: `mem_inFlightTo`, `inFlight_eq` (`inFlightTo` sums to `carriedTo`), `nodeViolations_nil` (each check ↔ a `NodeInv` clause), `Tree.invariant_nil`, `InvAt.leafDone_le`, `Inv.version_le_count` (no node beyond `count`; needs `descend` + `version_le_below`), `Inv.invariant_nil` |
| `WalkInv.lean` | `WalkInv cfg V phase t`: a walker above its leaf carries exactly the child it came through (the next digit of its leaf path), which counts `V+1` (`carries`), and two walkers at one node came through different children (`distinct`); `walkInv_walk` (the only interesting step: filling a node and continuing), `WInv cfg s`, `step_wInv`, `reachable_wInv` |
| `Refinement.lean` | the model refines `Completion`: `absNode cfg V phase p t : Completion.Node` (node at `V+1` ↦ filled, at `V` ↦ its counter, dead ↦ 0; a crate leaf's children are its consumers via `consumerDone`; `pendingAt` = filled ∧ (covers every worker ∨ `carriedFrom`, some walker still carries it); all clocks `zeroClock`), `absState`; `absNode_size`, `absChildren_getElem?/set/length`, `Agree` + `absNode_congr` (what the abstraction looks at), `Steps.inner_lift`; `carriedFrom_iff`, `carriedFrom_walk`/`pendingAt_walk`/`consumerDone_walk`/`agree_walk` (what one walk changes); `core_leaf` (leaf `fetch_add` = `inner (finish)` then `apply` of the consumer), `core_inner` (`apply` of the child the walker came through), `sim` (path-indexed), `refine_walk`; `agree_of_update` (every other consumer move leaves the abstract tree alone), `fresh_of`/`init_fresh` (start of a version is `Fresh`), `refine_step` (every step is `Steps` or a reset to `Fresh`), `reachable_absInv` (`Completion.Inv` of the abstract tree in every reachable state) |
| `Hb.lean` | race freedom: `Strong` (the crate's orderings: publish/finish release, ticket acquires+releases, both fences), `HbInv` (sizes of every clock; `State.mark j` = consumer `j`'s job-read epoch = its result-write epoch; `published`/`beforeFunc` for producer→consumer order; `resultMark`, `TreeHb` (`filled`/`leaf`/`counted`/`walker`: which release clocks and walker clocks know which result writes), `finisherKnows`, `probeKnows`, `producerKnows` for consumer→producer order), `init_hbInv`, `treeHb_walk` (the tree clauses across one `fetch_add`), `HbInv.walk`, `step_producer_hbInv`, `step_consumer_hbInv`, `reachable_hbInv`, `step_no_race`, **`reachable_no_race`**: with `Strong` orderings no reachable state has a step that is `Outcome.race` |
| `NoFault.lean` | `Tree.get_of_prefix`, `walk_ok` (a walker's `Tree.walk` returns `.ok`: node exists, version matches, no overflow, root covers every worker), `step_tree_window`, `reachable_root_window`, `producer_no_fault`, `consumer_no_fault`, **`reachable_no_fault`**: no thread in `threads cfg` has a step that is `Outcome.fault` from a reachable state |
| `ExecutionOrder.lean` | Abstract `Graph` with HB, one probe modification order, and write-write coherence. `Path.compress`, `acyclic` (their union is acyclic without SC/race-freedom premises), `rank_lt`, `key_before`, `key_injective` (finite events have distinct positions respecting both orders). This proves the graph-ordering component; labeled program-state reconstruction and clock soundness remain open. |
| `WeakMemory.lean` | `Machine` / `Transition` (probe-write history, arbitrary stale loads, saved observations and separate fences); `consumer_observed_eq`, `producer_observed_eq`, `Waiting.probe_stable`, `step_probeRel`; `reachable_machineInv`, `transition_projects`, `reachable_projection` (stuttering reduction, proved together with the invariant); `lift_step`, `lift_reachable` (all original executions lift back); `reachable_write_source`, `consumer_reads_publication`, `producer_reads_completion` (actual supplying RMWs); `pending_write_stable`; `reachable_attempt_no_race`, `reachable_attempt_no_fault`, and both specification-check theorems for the history machine. **Not** a formalization or coverage proof of all Rust/C++ execution graphs. |
| `SpecProofs.lean` | `JobOk` (job slot per producer phase), `ResultOk` (result slot per consumer phase), `DataInv` (job + result slots), `init_dataInv`, `step_dataInv` (given `Inv`), `reachable_dataInv`, `violations_nil` / `reachable_violations_nil` (every clause of `Spec.violations`), `isFinal_producer`, `reachable_finalViolations_nil` |

No protocol invariant hypotheses are taken as given: `reachable_inv` needs
only `1 ≤ workers` and `2 ≤ cluster`. Race freedom additionally needs `Strong`.
These are model theorems; Rust arithmetic, access abstraction, and weak-memory
coverage require the correspondence obligations in `MEMORY_MODEL.md`.

## What changed in this session

- Added `WeakMemory.lean`, imported by `RearmBarrier.lean`. No Rust code or
  existing executable transition rules changed; the new semantics is a
  separate relation with proved reduction and converse lifting.
- Successful reads are proved current, not constrained to be current by the
  transition rules. Their saved release clocks survive arbitrary interleavings
  before the fence. Only the fence performs the acquisition.
- `MachineInv` and original-model reachability are derived together. This
  avoids assuming `Inv` of history-machine executions; it does not establish
  that arbitrary C++ graphs have history-machine executions.
- Corrected the generic DRF-to-SC claim in `Model.lean` and the stale proof
  status in the README. `MEMORY_MODEL.md` states the exact proved boundary,
  standard synchronization rules, and remaining graph/clock obligations.
- Added `model/ProofAudit.lean` and `scripts/check_axioms.sh` to build and audit
  the original and new theorem entrypoints for unapproved axioms.
- Added `ExecutionOrder.lean`: HB plus a single coherent probe modification
  order is acyclic and admits distinct finite ordering keys. This is independent
  of the protocol invariant and does not assume race freedom or a global order.
  Ticket RMW order is already HB under `Strong`; interpreting a source graph
  this way still requires the labeled-event/state and clock correspondence.
- Validation: full `lake build` passed (48 jobs); the axiom audit passed for
  19 entrypoints, using only `propext`, `Classical.choice`, and `Quot.sound`
  (`ExecutionOrder.acyclic` uses no axioms).
  `MAX_WORKERS=7 ./scripts/difftest.sh` passed all 61,440 storage shapes, ten
  exhaustive explorations, and 140 traces with zero failures. Rust code was
  unchanged; Miri was not rerun in this session.

## Previous session

- Committed `WalkInv.lean` / `Refinement.lean` (previous session's work).
- New `Hb.lean` (imports `SpecProofs`, `WalkInv`): the happens-before
  conclusion, done as a direct concrete invariant rather than through the
  relational clock refinement sketched earlier. `#print axioms
  reachable_no_race` gives only `propext`, `Quot.sound`, `Classical.choice`.
  No executable Lean changed.
- Proof-engineering notes: an epoch of a result write is not in the state
  after the slot is overwritten, but the consumer reads the job slot in the
  same step, and `jobSlot.reads[j+1]` survives until the producer's next job
  write, exactly as long as it is needed (`State.mark`). `TreeHb.counted`
  needs `¬ deadAt` (dead nodes are never touched). Record updates are defeq
  to their pieces, but anything through `rmwProbe` or a fence `if` is not:
  use `rmwProbe_unchanged'` / `Inv.congr` / `mark_of_jobSlot`, or
  `rw [if_pos hS.…]` first. `by` blocks inside `⟨…⟩` that use `|` or `<;>`
  need parentheses. A consumer step whose state is built by `access` then
  `setConsumer` is proved by applying the lemmas in the order that makes each
  intermediate state satisfy the invariant (e.g. `setConsumer` before
  `writeResult` for `start`), relying on defeq of the final records.
- New `NoFault.lean`: `reachable_no_fault`. The root's window is not in any
  invariant, so it is its own small induction (`reachable_root_window`).
  `./scripts/difftest.sh` still ends "140 traces checked, 0 failures".

## Plan: what is left

The original and history-model safety theorems are proved. Remaining work:

1. **External weak-memory correspondence**, detailed in `MEMORY_MODEL.md`:
   define an execution-graph source with program order, modification order,
   reads-from, and synchronization. Prove every relevant source execution
   maps into the history machine, and the model's clock edges are sound for
   its real accesses. `ExecutionOrder.key_before` / `key_injective` now provide
   the compatible order once the graph is instantiated: ticket MO and
   release-source-to-fence edges must be HB. Reconstruct labeled program
   states in that order. Do not reuse `reachable_inv` on a source graph
   before establishing the relation.
2. **Rust arithmetic and API coverage**: representability bounds for `usize`
   (including `2 * count`, `workers * count`, and index/window intermediates),
   callback/access abstraction, and initialization/destruction/panic paths.
   `NoFault`'s logical node overflow is not machine-integer overflow.
3. **Concrete deadlock freedom**: every reachable state with no enabled
   thread is final. `Completion.progress` plus forward refinement does not
   suffice: prove abstract enabled moves have concrete implementations, or
   prove progress directly using the protocol/counting invariants. Eventual
   completion additionally needs suitable scheduling/visibility and callback
   termination assumptions.
4. Transfer other game theorems if useful. The zero-clock abstraction remains
   separate from the direct happens-before proof in `Hb.lean`.

## Lean pitfalls hit in this project (core only, no Mathlib)

- No `set`, `by_contra`, `List.reverseRecOn`, `Iff.not`, `Nat.pos_pow_of_pos` (use `Nat.pow_pos`), `List.le_sum_of_mem` (local `le_sum_of_mem'`). `if_pos/if_neg` are deprecated but work (`set_option linter.deprecated false in`).
- `omega` treats `x * y` as an atom only if the two occurrences are syntactically identical; normalise with `Nat.mul_add`, `Nat.mul_one`, `Nat.add_mul` first, or `generalize` the product. Never unfold `Tree.lo/hi/size` on a *variable* node with `simp only [Tree.lo]` (it produces `match` terms); use `Tree.lo_mk`-style constructor lemmas and `Tree.size` only.
- `cases h : e` with `e` a projection rewrites the goal too (witnesses become `rfl`). `subst h` with `h : a = b` eliminates whichever variable it can; refer to the survivor.
- `split at h` on an `Outcome.accessing`/`match` chain splits the innermost match; prefer `cases hx : e with` and `rw [hx] at h`, then `dsimp only at h`.
- `Tree` is a nested inductive: avoid induction on it. Everything in `TreeInvariant.lean` is path-indexed; `all_advanced` uses strong induction on `sizeOf`.
- Constructor named `continue` must be written `«continue»` in `cases … with`.
- zsh does not word-split unquoted variables; run shape loops under `bash -c`.

## Validation commands

```
(cd model && lake build)
./scripts/check_axioms.sh                 # from the repo root
./scripts/difftest.sh                     # from the repo root; must end "N traces checked, 0 failures"
(cd model && lake env lean /path/to/Ax.lean)  # with `#print axioms <thm>` lines to confirm no sorryAx
cargo test --release; cargo miri test --release
```
