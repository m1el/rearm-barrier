# Continuing the rearm-barrier verification

State of the work as of 2026-09-15, after commit `32d5ca4` (the global
invariant) plus the uncommitted `TreeCheck.lean` / `SpecProofs.lean` work (see
"What changed in the last session"). Everything below the "Plan" heading is
what remains; everything above it is context a new session needs before
touching the Lean.

## What exists

- `src/lib.rs`: the crate. `trace` feature + `src/trace.rs` report every
  atomic op to a hook; `examples/trace.rs` records per-thread traces on real
  threads (watchdog dumps a partial trace with a trailing `timeout` line).
- `scripts/difftest.sh`: (1) diffs `ticket_storage` crate vs model for
  61,440 shapes, (2) exhaustive exploration of ten small shapes, (3) replays
  140 crate traces on the model. Run it after any change to executable Lean.
  Env: `ITERS`, `COUNT`, `MAX_WORKERS`, `TIMEOUT`, `OUT`.
- `model/` (Lean 4.34.0, no Mathlib, `lake build`; binary
  `model/.lake/build/bin/rearm-model {explore|check|simulate|storage}`;
  `explore W C N [MAX_STATES] [publish|ticket|finish|producer-fence|consumer-fence]`
  weakens an ordering).

Executable model (checked, not proved):

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
| `SpecProofs.lean` | `JobOk` (job slot per producer phase), `ResultOk` (result slot per consumer phase), `DataInv` (job + result slots), `init_dataInv`, `step_dataInv` (given `Inv`), `reachable_dataInv`, `violations_nil` / `reachable_violations_nil` (every clause of `Spec.violations`), `isFinal_producer`, `reachable_finalViolations_nil` |

No hypotheses are taken as given any more: `reachable_inv` needs only
`1 ≤ workers` and `2 ≤ cluster` (the crate's `VALID_CONFIG`).

## What changed in the last session (uncommitted)

- `Tree.invariant` and `Spec.violations` were rewritten without `partial`,
  `Id.run do` or `for` loops (same checks, same messages, same order), as
  `filterMap`/`if`/`sum` over lists, with the tree recursion as a `mutual`
  structural recursion (`Tree.invariant` / `Tree.invariantChildren`).
  `inFlightTo` now iterates `List.range cs.size` with `cs[id]!`.
  `scripts/difftest.sh` still passes (see below), so the executable
  behaviour is unchanged.
- `StepInvariant.lean`: `access_unchanged` & co. now also report `job` and
  `results`; `step_producer_move` reports `s'.job = jobAfter s.job p` and
  `s'.results = s.results`; `step_consumer_move` reports `s'.job = s.job` and
  `s'.results = resultsAfter s.results id ph`.
- New `TreeCheck.lean` and `SpecProofs.lean` (table above); `RearmBarrier.lean`
  imports them. `#print axioms` on `reachable_violations_nil`,
  `reachable_finalViolations_nil`, `Inv.invariant_nil` gives only `propext`,
  `Quot.sound`, `Classical.choice`.
- Design notes: `InvAt` carries the version `V` as an explicit parameter
  (with field `version : p.version cfg = V`) so that after `cases` on a
  `ProducerMove` every field mentions a plain `v` and `omega` works; convert
  with `have hinv : InvAt cfg s.probe s.tree (.publish v) v s.consumers := hinv`
  (defeq) or `hinv.at hp` when only `hp : s.producer = p` is known (`rw … at`
  cannot see through the `Inv` abbrev). When calling `InvAt.simple_move`,
  pass `(ph' := …)` explicitly, otherwise a `nofun` argument elaborated
  before `htree` unifies `ph'` with `.finish V`; prefer
  `absurd h (not_finished_of_ne nofun nofun)` for the same reason.
  `rw [getElem!_phaseOf …]` fails on "motive is not type correct" under a
  `decide`; use `simp only [getElem!_phaseOf …]`. `by decide` refuses goals
  with free variables even when they reduce; `cases h`/`nomatch h` on a
  `(… == …) = true` hypothesis works.

## Plan: what is left

Both executable checks are now proved to pass in every reachable state
(`reachable_violations_nil`, `reachable_finalViolations_nil`), so the
explorer and the replay can only ever report faults of `Tree.walk` (index
out of range) or data races, never an invariant violation. Remaining items:

1. The refinement `Tree.walk` ↦ `Completion.Step` and the multi-version
   version of `Completion`.
2. The happens-before conclusion: track `probeRel` and the consumers'/producer's
   clocks in an invariant (one Release on `finish`, one Acquire fence on
   `observeDone`) to conclude that every consumer's `func` for `v` happens
   before `complete` for `v`; `Completion.done_clock` is the tree half of that
   argument. With it, `Outcome.race` would be unreachable too.
3. `Tree.walk` never faults from a reachable state (the node under the cursor
   exists, counts version `V`, does not overflow, and the root covers every
   worker): the ingredients are in `TreeInv` (`walkers`, `carried_version`,
   `not_full`, `leaves`) and `init_root_size`.

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
cd model && lake build
./scripts/difftest.sh                     # from the repo root; must end "140 traces checked, 0 failures"
cd model && lake env lean /path/to/Ax.lean  # with `#print axioms <thm>` lines to confirm no sorryAx
cargo test --release; cargo miri test --release
```
