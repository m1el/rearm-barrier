# proof-map — the rearm-barrier dependency map

An interactive, self-contained HTML visualization of every theorem beneath the
20 audited entrypoints of [`model/ProofAudit.lean`](../../model/ProofAudit.lean)
(`reachable_inv`, `reachable_no_race`, `reachable_no_fault`, the `WeakMemory`
reduction theorems, `ExecutionOrder.acyclic`, `Completion.run_completes`, …).

**Open [rearm-map.html](rearm-map.html) in a browser.** Light/dark themed,
hover any box, dot or toolbox chip for details including the full theorem
statement. No network access needed.

The **Root theorem** selector at the top switches the map to the subtree
beneath any one audited entrypoint, or to all 20 together. Theorems listed in
`extraRoots` in `DepGraph.lean` (currently none) also get a view, marked
“not audited”. It opens on
`WeakMemory.reachable_attempt_no_race`, the broadest safety result (race freedom
on the stale-read history machine, which pulls in `reachable_no_race` and
`reachable_inv`). The choice is kept in the URL hash, e.g.
`rearm-map.html#reachable_absInv` or `#all`.

## How to read it

With all entrypoints selected, the 508 reachable project theorems are folded
into a 56-node graph (the default root: 357 theorems, 26 boxes) so the argument
reads top → down at a glance:

- **Boxes** are the load-bearing lemmas. **Dashed boxes** are the audited
  entrypoints; the numbered ones are the spine (`WeakMemory.reachable_attempt_no_race → reachable_no_race →
  reachable_hbInv → reachable_inv → step_consumer_inv → step_consumer_treeInv →
  walk_preserves → nodeInv_self → walk_spec`). An arrow means the upper lemma —
  or its private support — uses the lower one (transitively reduced).
- **Dots inside a box** are its *private* support lemmas: a minor lemma is
  absorbed by a major iff it is reachable from that major without passing
  through any other major. Dot area ≈ proof length, color = source file.
- **Dots below a box's dashed “shared” divider** are support lemmas reachable
  from 2–5 boxes; they appear in every owning box (hover names the co-owners).
- **The toolbox strip** holds the plumbing facts used beneath 6+ boxes
  (`InvAt.*` projections, `Wf.*`, `upd_self`, …); their edges are omitted.

## Regenerating

The pipeline is deterministic; each step reads/writes files in this directory.

```sh
# 1. extract the raw dependency graph from the compiled Lean environment
cd model && lake build RearmBarrier && DEPGRAPH_OUT=../docs/proof-map/depgraph.json \
  lake env lean ../docs/proof-map/DepGraph.lean         # -> depgraph.json

# 2. contract around the major lemmas, lay out, render
cd ../docs/proof-map
python3 contract.py                                     # -> contracted.json
uv run --with grandalf layout.py                        # -> layout.json
python3 render.py                                       # -> rearm-map.html
```

| File | Role |
|---|---|
| [DepGraph.lean](DepGraph.lean) | `CoreM` meta-program: reads the roots from `ProofAudit.lean` (override with `PROOF_AUDIT`), walks proof terms, inlines `_proof_`/matcher auxiliaries, emits the theorem-level graph with each theorem's pretty-printed statement. Private theorems are kept under their user-facing names. |
| [contract.py](contract.py) | One view per audited entrypoint plus one for all of them: ownership partition (major / absorbed / shared / toolbox) and contracted, transitively-reduced edges over the theorems reachable from that root. The default root, spine and major-lemma list are curated at the top; every audit root is always a major. |
| [layout.py](layout.py) | Narrow vertical Sugiyama layout per view (grandalf ranks per connected component, merged by rank, width-capped row wrapping). |
| [render.py](render.py) | Emits the final self-contained HTML/SVG page: every view pre-rendered, a `<select>` to switch; module color groups and per-box descriptions live here. |
| depgraph.json | Snapshot of the extracted graph. |
| [rearm-map.html](rearm-map.html) | The rendered map. |

Adapted from the `prog_sim` map in `riscv-fv-bootstrap/docs/proof-map`.
`contracted.json`/`layout.json` are intermediates and not checked in.
