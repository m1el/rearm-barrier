import RearmBarrier.Model

/-!
# The tree engine

The completion tree as an inductive tree instead of a heap-indexed array.
Every node owns a window `[lo, hi)` of consumer IDs; leaves own at most
`CLUSTER` consecutive IDs, inner nodes have at most `CLUSTER` children whose
windows partition the node's window. The number of consumers under a node,
`hi - lo`, is what the crate computes as `win_size.min(WORKERS - win_id *
win_size)`.

## Node state

A node counts, for its current `version`, how many of its consumers have
`finished` it; the rest are in flight. A leaf's consumer finishes by its
`fetch_add`; an inner node's child finishes when the child's window fills,
and the consumer that filled it then propagates the child's size upwards.
When a node fills it moves to the next version with nothing finished. The
crate's single cumulative counter is `size * version + finished`, and its
`new_val == WORKERS * (version + 1)` test is "a node covering every worker
fills": the crate stops there, so the ancestors of the lowest such node are
never touched (`dead`).

A consumer's cursor is the path from the root to its current node, and the
update is `modifyAt`, which by construction cannot change the shape of the
tree: only the counters and release clock of one node change.

## Invariant

`invariant` is the counting invariant this representation is built to make
statable, checked by the explorer in every reachable state:

* a node's version is the version of any consumer contributing to it;
* a leaf's `finished` is the number of its consumers past their leaf
  `fetch_add` for that version, and no consumer is more than one version
  ahead of its leaf;
* a live inner node's `finished`, plus the contributions in flight towards
  it, is the total size of its children that are one version ahead, and no
  child is further ahead;
* a dead node is never touched.

## Layout

The heap index of a node is recovered from its path (`heapIndex`), so the
events this engine produces carry the same ticket IDs as the flat engine;
`heapIndex_append` and `parent_heapIndex` show that this is exactly the
crate's layout (`children of i are i * C + 1 ..= i * C + C`).
-/

namespace RearmBarrier.TreeModel

/-- A node of the completion tree: the version it is counting, how many of
its consumers have finished that version, its release clock, the window
`[lo, hi)` of consumer IDs it covers, and its children (none for a leaf). -/
inductive Tree
  | mk (version finished : Nat) (rel : VC) (lo hi : Nat) (children : List Tree)
deriving Repr, BEq, Hashable, Inhabited

namespace Tree

def version : Tree → Nat
  | .mk v _ _ _ _ _ => v

def finished : Tree → Nat
  | .mk _ f _ _ _ _ => f

def rel : Tree → VC
  | .mk _ _ r _ _ _ => r

def lo : Tree → Nat
  | .mk _ _ _ lo _ _ => lo

def hi : Tree → Nat
  | .mk _ _ _ _ hi _ => hi

def children : Tree → List Tree
  | .mk _ _ _ _ _ cs => cs

/-- The number of consumers under the node: the crate's `target_val`. -/
def size (t : Tree) : Nat := t.hi - t.lo

/-- The consumers under the node still working on its version. -/
def inFlight (t : Tree) : Nat := t.size - t.finished

/-- The crate's cumulative counter for this node. -/
def counter (t : Tree) : Nat := t.size * t.version + t.finished

def isLeaf (t : Tree) : Bool := t.children.isEmpty

/-- The node at `path` -/
def get : Tree → List Nat → Option Tree
  | t, [] => some t
  | .mk _ _ _ _ _ cs, k :: p =>
    match cs[k]? with
    | some c => c.get p
    | none => none

/-- Apply `f` to the node at `path` (the identity if there is no such node). -/
def modifyAt (f : Tree → Tree) : Tree → List Nat → Tree
  | t, [] => f t
  | .mk v n r lo hi cs, k :: p =>
    match cs[k]? with
    | some child => .mk v n r lo hi (cs.set k (child.modifyAt f p))
    | none => .mk v n r lo hi cs

/-- The tree of `RearmBarrier<_, _, W, C>`: a node of height `h` at `lo`
covers `[lo, lo + C ^ (h + 1)) ∩ [0, W)`; children whose window would be
empty do not exist. -/
def build (W C : Nat) : (h : Nat) → (lo : Nat) → Tree
  | 0, lo => .mk 0 0 (VC.zero (W + 1)) lo (min (lo + C) W) []
  | h + 1, lo =>
    let w := C ^ (h + 1)
    .mk 0 0 (VC.zero (W + 1)) lo (min (lo + w * C) W) <|
      (List.range C).filterMap fun k =>
        if lo + k * w < W then some (build W C h (lo + k * w)) else none

partial def summary : Tree → List (Nat × Nat)
  | .mk v f _ _ _ cs => (v, f) :: cs.flatMap summary

end Tree

/-- The number of levels above the leaves: the loop of `ticket_tree_alloc`
runs once per level above the level just above the leaves. -/
def levels (baseSize cluster : Nat) : Nat :=
  go 1 1
where
  go (botSize acc : Nat) : Nat :=
    if botSize * cluster < baseSize ∧ 2 ≤ cluster ∧ 1 ≤ botSize then
      go (botSize * cluster) (acc + 1)
    else acc
  termination_by baseSize - botSize
  decreasing_by
    have : botSize * 2 ≤ botSize * cluster := Nat.mul_le_mul_left _ (by omega)
    omega

/-- The height of the root: the leaves are at depth `levels`. -/
def rootHeight (cfg : Config) : Nat := levels cfg.baseSize cfg.cluster

/-- The heap index of the node at `path`, in the crate's layout. -/
def heapIndex (C : Nat) (path : List Nat) : Nat :=
  path.foldl (fun i k => C * i + k + 1) 0

theorem heapIndex_append (C : Nat) (p : List Nat) (k : Nat) :
    heapIndex C (p ++ [k]) = C * heapIndex C p + k + 1 := by
  simp [heapIndex, List.foldl_append]

/-- The parent of a child in the heap is the node its path came from:
`(ticket_id - 1) / CLUSTER` undoes `heapIndex_append`. -/
theorem parent_heapIndex (C : Nat) (hC : 0 < C) (p : List Nat) (k : Nat) (hk : k < C) :
    parent (heapIndex C (p ++ [k])) C = heapIndex C p := by
  rw [heapIndex_append]
  unfold parent
  have : C * heapIndex C p + k + 1 - 1 = k + C * heapIndex C p := by omega
  rw [this, Nat.add_mul_div_left _ _ hC, Nat.div_eq_of_lt hk]
  simp

/-- The path (most significant digit first) of the `j`-th node at depth `d`. -/
def pathAt (C d j : Nat) : List Nat :=
  (List.range d).foldl (fun (acc : List Nat × Nat) _ => (acc.2 % C :: acc.1, acc.2 / C)) ([], j) |>.1

/-- A consumer's cursor: the path to its current node and the amount it adds. -/
structure Cursor where
  path : List Nat
  mergeAmount : Nat
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

instance : ToString Cursor := ⟨fun c => s!"path {c.path}, merge {c.mergeAmount}"⟩

def init (cfg : Config) : Tree := Tree.build cfg.workers cfg.cluster (rootHeight cfg) 0

/-- Consumer `id` starts at its leaf, adding 1. -/
def start (cfg : Config) (id : Nat) : Cursor :=
  { path := pathAt cfg.cluster (rootHeight cfg) (id / cfg.cluster), mergeAmount := 1 }

/-- One iteration of the walk: add to the node under the cursor; if that
fills the node, either the whole barrier is complete (the node covers every
worker) or the consumer carries the node's size to the parent. -/
def step (cfg : Config) (t : Tree) (c : Cursor) (v : Nat) (vc : VC) (ord : MemOrd) :
    EngineResult Tree Cursor :=
  match t.get c.path with
  | none => .fault s!"no node at path {c.path}"
  | some node =>
    if node.version != v then
      .fault s!"a consumer at version {v} contributes to the node at {c.path}, which counts version {node.version}"
    else
      let old := node.counter
      let finished := node.finished + c.mergeAmount
      let (vc, rel) := rmwTicketClocks vc node.rel ord
      let rmw := { ticketId := heapIndex cfg.cluster c.path, amount := c.mergeAmount, old }
      if finished < node.size then
        let t := t.modifyAt (fun n => .mk n.version finished rel n.lo n.hi n.children) c.path
        .ok t vc rmw .stop
      else if finished > node.size then
        .fault s!"the node at {c.path} overflows: {finished} finished out of {node.size}"
      else
        -- the window filled: this version is done here, count the next one
        let t := t.modifyAt (fun n => .mk (n.version + 1) 0 rel n.lo n.hi n.children) c.path
        if node.size = cfg.workers then
          .ok t vc rmw .finished
        else if c.path.isEmpty then
          .fault s!"the root covers only {node.size} of {cfg.workers} workers"
        else
          .ok t vc rmw (.continue { path := c.path.dropLast, mergeAmount := node.size })

/-! ## The counting invariant -/

/-- How many leaf `fetch_add`s consumer `id` has done, given its phase and
the path of its leaf. -/
def leafDone (leafPath : List Nat) (count : Nat) : ConsumerPhase Cursor → Nat
  | .start | .initializing => 0
  | .waitReady v | .beforeFunc v | .inFunc v => v
  | .walk v c => if c.path == leafPath then v else v + 1
  | .finish v => v + 1
  | .done => count

/-- The contributions currently carried towards the node at `path`. -/
def inFlightTo (path : List Nat) (cs : Array (ConsumerPhase Cursor)) : List (Nat × Nat × Nat) :=
  cs.toList.zipIdx.filterMap fun (ph, id) =>
    match ph with
    | .walk v c => if c.path == path then some (id, v, c.mergeAmount) else none
    | _ => none

partial def invariant (cfg : Config) (cs : Array (ConsumerPhase Cursor)) (path : List Nat) (t : Tree) :
    List String := Id.run do
  let mut out : List String := []
  let here := s!"node {path} (window [{t.lo}, {t.hi}), version {t.version}, finished {t.finished})"
  let carried := inFlightTo path cs
  for (id, v, _) in carried do
    if v != t.version then
      out := out ++ [s!"consumer {id} at version {v} carries a contribution to {here}"]
  let inFlight := (carried.map (·.2.2)).sum
  if t.version > cfg.count then
    out := out ++ [s!"{here} is beyond the last version"]
  if t.finished ≥ t.size && t.size > 0 then
    out := out ++ [s!"{here} is full but was not advanced"]
  if t.isLeaf then
    -- a leaf counts the consumers of its window that did their fetch_add
    let mut contributed := 0
    for id in [t.lo:t.hi] do
      let d := leafDone path cfg.count cs[id]!
      if d < t.version || d > t.version + 1 then
        out := out ++ [s!"consumer {id} has done {d} leaf contributions but its leaf is {here}"]
      if d == t.version + 1 then contributed := contributed + 1
    if t.finished != contributed then
      out := out ++ [s!"{here} has {contributed} consumers past their fetch_add"]
    for (id, _, amount) in carried do
      if amount != 1 then
        out := out ++ [s!"consumer {id} carries {amount} to leaf {here}"]
  else if t.children.any (·.size == cfg.workers) then
    -- dead: the crate stops at the child that covers every worker
    if t.version != 0 || t.finished != 0 || !carried.isEmpty then
      out := out ++ [s!"{here} is above the node covering every worker but was touched"]
  else
    -- live: children one version ahead have filled and been (or are being) propagated
    let mut filled := 0
    for (child, k) in t.children.zipIdx do
      if child.version < t.version || child.version > t.version + 1 then
        out := out ++ [s!"child {k} of {here} counts version {child.version}"]
      if child.version == t.version + 1 then filled := filled + child.size
    if t.finished + inFlight != filled then
      out := out ++ [s!"{here} plus {inFlight} in flight does not match {filled} finished below it"]
  for (child, k) in t.children.zipIdx do
    out := out ++ invariant cfg cs (path ++ [k]) child
  return out

def violations (cfg : Config) (t : Tree) (cs : Array (ConsumerPhase Cursor)) : List String :=
  invariant cfg cs [] t

def engine : Engine Tree Cursor :=
  { init, start, step, violations, summary := fun t => s!"tree (version, finished) = {t.summary}" }

end RearmBarrier.TreeModel
