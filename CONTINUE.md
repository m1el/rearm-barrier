# Continuing the rearm-barrier verification

State of the work as of 2026-09-14, after commit `a049d91` plus the uncommitted
`Protocol.lean` (see "What changed in the last session"). Everything below the
"Plan" heading is what remains; everything above it is context a new session
needs before touching the Lean.

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
| `TreeModel.lean` | inductive `Tree` (nodes `(version, finished, rel, lo, hi, children)`), `build`/`buildChildren`, `get`/`modifyAt` by path, `heapIndex`/`pathOfIndex`, `toCounters`/`ofCounters`, `Cursor`, `ConsumerPhase`, `Tree.walk` (one `fetch_add`), `Tree.invariant` (partial def, executable check) |
| `Model.lean` | `State`, producer/consumer steps, `step`, hb tracking, `writeAllSlots` |
| `Spec.lean`, `Explore.lean`, `Trace.lean`, `Main.lean` | invariants, DFS explorer, trace replay (greedy scheduler, complete by the argument in the file header), CLI |

Proved (all `sorry`-free, axioms only `propext`, `Quot.sound`, `Classical.choice`):

| file | main theorems |
|---|---|
| `Tree.lean` | `ticketStorage_le` (the crate's compile-time sizing claim), `parent_lt`, `start_ticket_lt` |
| `TreeProofs.lean` | `get_modifyAt_self`, `get_window_modifyAt`; `walk_spec` (walk = one fetch_add on the cursor node, updated node's version/counter stated explicitly); `walk_crate` / `walk_crate_wf` (tree's next move = crate's `if new_val == W*(v+1) … else if id==0 \|\| new_val != target*(v+1) … else continue (id-1)/C`); `build_lo/hi`, `rootHeight_pow`, `init_root_size`; `Wf` (windows tile), `Wf_build`, `init_wf`, `Wf.modifyAt`, `walk_wf`, `Wf.sum_children` |
| `TreeInvariant.lean` | `TreeInv cfg V phase t` (path-indexed Prop version of the counting invariant, consumers as `Nat → ConsumerPhase`); `walk_preserves` (via `nodeInv_self` / `nodeInv_parent` / `nodeInv_other`), `phase_preserves`, `startWalk_preserves`, `advance_preserves` (+ `all_advanced`) |
| `TreeInit.lean` | `get_build_char` (node at path q = `build (H-\|q\|) (digits q * C^(H-\|q\|+1))`), `init_leaves`, `init_leaf_unique`, `init_treeInv` |
| `StepInvariant.lean` | `phaseOf` (default `.start` out of range, so `phaseOf_replicate`), `phaseOf_setIfInBounds`, `step_consumer_move` (every consumer `step` = one `ConsumerMove` + `setConsumer`; also reports `s'.producer = s.producer` and `s'.probe = probeAfter s.probe ph`; the `waitReady` move records its guard), `step_producer_move` (`ProducerMove`: phase before/after and the probe after), `step_consumer_treeInv` (hypothesis `hV : walk/inFunc/finish v → v = V ∧ V < count`), `step_producer_treeInv`, `step_producer_unchanged` |
| `Protocol.lean` | the global invariant. `ProducerPhase.version` (`done ↦ count`), `ProbeOk` (probe per producer phase), `ConsumerOk cfg V probe ph` (allowed consumer phases at probe `2V`, `2V+1`, `2V+2`), `Finished cfg V ph` (`waitReady (V+1)` or `done ∧ V+1 = count`), `InvAt cfg probe tree producer V consumers` (fields: `version`, `size`, `wf`, `tree : TreeInv`, `probeOk`, `version_lt`, `consumers`, `finisher` = "a consumer in `finish V` ⇒ every other one is `Finished`"), `Inv cfg s` (abbrev). `InvAt.active` (inFunc/walk/finish ⇒ version `V`, producer `waiting V`, probe `2V+1`), `others_done` (a node of size `W` at version `V+1` ⇒ every consumer is `finish V` or `Finished`; uses `descend`/`tiles_cover`/`below_advanced`/`size_le_of_below`), `step_producer_inv`, `step_consumer_inv`, `step_inv`, `init_inv`, `Reachable`, `reachable_inv`, `reachable_probe_le` (`probe ≤ 2·count` in every reachable state) |
| `Completion.lean` | one-version abstract protocol ("game" = nondeterministic `Step` relation on a nested `Node` type): `Step.inv`, `done_contributed`, `done_clock` (hb: done node's clock dominates every consumer's), `noStep_of_done`, `progress`, `Step.measure_lt`, `run_completes` |

No hypotheses are taken as given any more: `reachable_inv` needs only
`1 ≤ workers` and `2 ≤ cluster` (the crate's `VALID_CONFIG`).

## What changed in the last session (uncommitted)

- `model/RearmBarrier/Protocol.lean` (new), `StepInvariant.lean` (extended as
  in the table), `RearmBarrier.lean` (imports `Protocol`). `lake build` is
  clean; `#print axioms` on `reachable_inv` gives only `propext`,
  `Quot.sound`, `Classical.choice`.
- Design notes for whoever extends `Inv`: `InvAt` carries the version `V` as
  an explicit parameter (with field `version : p.version cfg = V`) so that
  after `cases` on a `ProducerMove` every field mentions a plain `v` and
  `omega` works; in `step_producer_inv` each case starts with
  `have hinv : InvAt cfg s.probe s.tree (.publish v) v s.consumers := hinv`
  (defeq). When calling `InvAt.simple_move`, pass `(ph' := …)` explicitly,
  otherwise a `nofun` argument elaborated before `htree` unifies `ph'` with
  `.finish V`. Prefer `absurd h (not_finished_of_ne nofun nofun)` over
  `not_finished_of_ne nofun nofun h` for the same reason.

## Plan: what is left

The global invariant is done. Remaining items, in the order they seem worth
doing:

1. The executable `Tree.invariant` check is implied by `TreeInv` (optional;
   would connect the explorer's check to the proof).
2. `Spec.violations`'s racing/`job`/`results` clauses follow from `Inv`
   (optional, longer): e.g. "producer `writing v` ⇒ no consumer `inFunc _`"
   is immediate from `ConsumerOk` at probe `2v`; "`inFunc v` ⇒ `job = some v`"
   and "`completing v` ⇒ every result is `some v`" need `job`/`results` added
   to `InvAt`.
3. The refinement `Tree.walk` ↦ `Completion.Step` and the multi-version
   version of `Completion`.
4. The happens-before conclusion: track `probeRel` and the consumers'/producer's
   clocks in `Inv` (one Release on `finish`, one Acquire fence on `observeDone`)
   to conclude that every consumer's `func` for `v` happens before
   `complete` for `v`; `Completion.done_clock` is the tree half of that
   argument.

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
