import RearmBarrier.Basics

/-!
# The completion tree

The crate keeps its completion counters in a flat array laid out as a heap
(`children of i are i * C + 1 ..= i * C + C`). The model keeps them as an
inductive tree instead: every node owns a window `[lo, hi)` of consumer IDs,
leaves own at most `CLUSTER` consecutive IDs, inner nodes have at most
`CLUSTER` children whose windows partition the node's window. The number of
consumers under a node, `hi - lo`, is what the crate computes as
`win_size.min(WORKERS - win_id * win_size)`.

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

## The two-way mapping to the crate's flat state

Traces from the crate name tickets by heap index. `heapIndex` maps a path to
its index and `pathOfIndex` maps back; `heapIndex_pathOfIndex` and
`pathOfIndex_heapIndex` prove they are inverse. `toCounters` renders the
tree as the crate's counter array and `ofCounters` reads one back, with
`(version, finished) = (counter / size, counter % size)`.

## Invariant

`invariant` is the counting invariant this representation is built to make
statable, checked by the explorer in every reachable state (and proved for
a single version, abstractly, in `RearmBarrier.Completion`):

* a node's version is the version of any consumer contributing to it;
* a leaf's `finished` is the number of its consumers past their leaf
  `fetch_add` for that version, and no consumer is more than one version
  ahead of its leaf;
* a live inner node's `finished`, plus the contributions in flight towards
  it, is the total size of its children that are one version ahead, and no
  child is further ahead;
* a dead node is never touched.
-/

namespace RearmBarrier

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

/-- The window of consumer IDs a node covers. -/
def window (t : Tree) : Nat × Nat := (t.lo, t.hi)

/-- The node with its children replaced. -/
def withChildren : Tree → List Tree → Tree
  | .mk v n r lo hi _, cs => .mk v n r lo hi cs

/-- The node at `path` -/
def get : Tree → List Nat → Option Tree
  | t, [] => some t
  | t, k :: p =>
    match t.children[k]? with
    | some c => c.get p
    | none => none

/-- Apply `f` to the node at `path` (the identity if there is no such node). -/
def modifyAt (f : Tree → Tree) : Tree → List Nat → Tree
  | t, [] => f t
  | t, k :: p =>
    match t.children[k]? with
    | some child => t.withChildren (t.children.set k (child.modifyAt f p))
    | none => t

/-- The children of a node at `lo` whose children have width `w`: slot `k`
covers `[lo + k * w, ...)`, and slots start at or beyond `W` do not exist
(once one is missing, so are all later ones). `n` slots remain from slot `k`. -/
def buildChildren (child : Nat → Tree) (W w lo : Nat) : Nat → Nat → List Tree
  | 0, _ => []
  | n + 1, k =>
    if lo + k * w < W then child (lo + k * w) :: buildChildren child W w lo n (k + 1) else []

/-- The tree of `RearmBarrier<_, _, W, C>`: a node of height `h` at `lo`
covers `[lo, lo + C ^ (h + 1)) ∩ [0, W)`; children whose window would be
empty do not exist. -/
def build (W C : Nat) : (h : Nat) → (lo : Nat) → Tree
  | 0, lo => .mk 0 0 (VC.zero (W + 1)) lo (min (lo + C) W) []
  | h + 1, lo =>
    .mk 0 0 (VC.zero (W + 1)) lo (min (lo + C ^ (h + 1) * C) W)
      (buildChildren (build W C h) W (C ^ (h + 1)) lo C 0)

/-- Every node with its path, in pre-order. -/
partial def nodes (t : Tree) (path : List Nat := []) : List (List Nat × Tree) :=
  (path, t) :: (t.children.zipIdx.flatMap fun (c, k) => c.nodes (path ++ [k]))

/-- Every node's `(version, finished)`, in pre-order. -/
def summary (t : Tree) : List (Nat × Nat) :=
  t.nodes.map fun (_, n) => (n.version, n.finished)

/-- Rebuild every node's counters from its path. -/
partial def mapWithPath (f : List Nat → Tree → Nat × Nat) (t : Tree) (path : List Nat := []) : Tree :=
  match t with
  | .mk _ _ r lo hi cs =>
    let (v, n) := f path t
    .mk v n r lo hi (cs.zipIdx.map fun (c, k) => c.mapWithPath f (path ++ [k]))

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

/-! ## Paths and heap indices -/

/-- The heap index of the node at `path`, in the crate's layout. -/
def heapIndex (C : Nat) (path : List Nat) : Nat :=
  path.foldl (fun i k => C * i + k + 1) 0

/-- The path of the node with heap index `i`: undo `heapIndex` one level at
a time with `(i - 1) / C` and `(i - 1) % C`. -/
def pathOfIndex (C : Nat) : Nat → List Nat
  | 0 => []
  | i + 1 => pathOfIndex C (i / C) ++ [i % C]
termination_by i => i
decreasing_by
  have := Nat.div_le_self i C
  omega

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

/-- Every heap index is the index of its path. -/
theorem heapIndex_pathOfIndex (C : Nat) : ∀ i, heapIndex C (pathOfIndex C i) = i
  | 0 => by simp [pathOfIndex, heapIndex]
  | i + 1 => by
    have ih := heapIndex_pathOfIndex C (i / C)
    rw [pathOfIndex, heapIndex_append, ih]
    have := Nat.div_add_mod i C
    omega
termination_by i => i
decreasing_by
  have := Nat.div_le_self i C
  omega

private theorem pathOfIndex_heapIndex_rev (C : Nat) (hC : 0 < C) :
    ∀ (q : List Nat), (∀ k ∈ q, k < C) → pathOfIndex C (heapIndex C q.reverse) = q.reverse
  | [], _ => by simp [heapIndex, pathOfIndex]
  | k :: q, hq => by
    have hk : k < C := hq k (by simp)
    have hq' : ∀ j ∈ q, j < C := fun j hj => hq j (by simp [hj])
    rw [List.reverse_cons, heapIndex_append, pathOfIndex]
    have h1 : (C * heapIndex C q.reverse + k) / C = heapIndex C q.reverse := by
      rw [Nat.mul_add_div hC, Nat.div_eq_of_lt hk, Nat.add_zero]
    have h2 : (C * heapIndex C q.reverse + k) % C = k := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
    rw [h1, h2, pathOfIndex_heapIndex_rev C hC q hq']

/-- Every path with digits below `C` is the path of its index. -/
theorem pathOfIndex_heapIndex (C : Nat) (hC : 0 < C) (p : List Nat) (hp : ∀ k ∈ p, k < C) :
    pathOfIndex C (heapIndex C p) = p := by
  have := pathOfIndex_heapIndex_rev C hC p.reverse (by simpa using hp)
  simpa using this

/-- The path (most significant digit first) of the `j`-th node at depth `d`:
the base-`C` digits of `j`. -/
def pathAt (C : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | d + 1, j => pathAt C d (j / C) ++ [j % C]

/-! ## The flat state -/

/-- The crate's counter array: every node's counter at its heap index, dead
entries zero. -/
def Tree.toCounters (cfg : Config) (t : Tree) : Array Nat :=
  t.nodes.foldl (init := Array.replicate cfg.storage 0) fun a (path, n) =>
    a.setIfInBounds (heapIndex cfg.cluster path) n.counter

/-- The tree whose counters are the given crate array (clocks zero). -/
def Tree.ofCounters (cfg : Config) (counts : Array Nat) : Tree :=
  (Tree.build cfg.workers cfg.cluster (rootHeight cfg) 0).mapWithPath fun path n =>
    let c := counts[heapIndex cfg.cluster path]!
    if n.size = 0 then (0, 0) else (c / n.size, c % n.size)

/-! ## Consumers -/

/-- A consumer's cursor: the path to its current node and the amount it adds. -/
structure Cursor where
  path : List Nat
  mergeAmount : Nat
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

instance : ToString Cursor := ⟨fun c => s!"path {c.path}, merge {c.mergeAmount}"⟩

/-- The program counter of a consumer thread. -/
inductive ConsumerPhase
  /-- has claimed its ID, has not yet written its initial state -/
  | start
  /-- writing the initial state into its result slot -/
  | initializing
  /-- spinning until `probe > 2 * v` -/
  | waitReady (version : Nat)
  /-- about to call `func` -/
  | beforeFunc (version : Nat)
  /-- inside `func` (holding `&T` and `&mut R`) -/
  | inFunc (version : Nat)
  /-- about to `fetch_add` the ticket under the cursor -/
  | walk (version : Nat) (cursor : Cursor)
  /-- about to `fetch_add` the probe: this consumer completed the version -/
  | finish (version : Nat)
  | done
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

def ConsumerPhase.toString : ConsumerPhase → String
  | .start => "start"
  | .initializing => "initializing"
  | .waitReady v => s!"waitReady {v}"
  | .beforeFunc v => s!"beforeFunc {v}"
  | .inFunc v => s!"inFunc {v}"
  | .walk v c => s!"walk {v} ({c})"
  | .finish v => s!"finish {v}"
  | .done => "done"

instance : ToString ConsumerPhase := ⟨ConsumerPhase.toString⟩

/-- The tree of a fresh barrier. -/
def Tree.init (cfg : Config) : Tree := Tree.build cfg.workers cfg.cluster (rootHeight cfg) 0

/-- Consumer `id` starts at its leaf, adding 1. -/
def Cursor.start (cfg : Config) (id : Nat) : Cursor :=
  { path := pathAt cfg.cluster (rootHeight cfg) (id / cfg.cluster), mergeAmount := 1 }

/-- What one `fetch_add` on a ticket looked like: the heap index of the
ticket, the amount added and the value returned. -/
structure Rmw where
  ticketId : Nat
  amount : Nat
  old : Nat
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

instance : ToString Rmw := ⟨fun r => s!"ticket {r.ticketId} += {r.amount} (was {r.old})"⟩

/-- What a consumer does after a `fetch_add` on a ticket. -/
inductive Next
  /-- `new_val == WORKERS * (version + 1)`: bump the probe -/
  | finished
  /-- the window is not full yet: this version is done here -/
  | stop
  /-- the window filled: continue at the parent -/
  | continue (cursor : Cursor)
deriving Repr, BEq, Hashable, Inhabited

inductive WalkResult
  /-- the tree after the `fetch_add`, the thread's clock after the acquire
  part of the ordering, the operation performed, and what follows -/
  | ok (tree : Tree) (vc : VC) (rmw : Rmw) (next : Next)
  /-- the Rust code would panic (an index out of bounds) -/
  | fault (msg : String)
deriving Inhabited

/-- One iteration of the walk: add to the node under the cursor; if that
fills the node, either the whole barrier is complete (the node covers every
worker) or the consumer carries the node's size to the parent. -/
def Tree.walk (cfg : Config) (t : Tree) (c : Cursor) (v : Nat) (vc : VC) (ord : MemOrd) :
    WalkResult :=
  match t.get c.path with
  | none => .fault s!"no node at path {c.path}"
  | some node =>
    if node.version != v then
      .fault s!"a consumer at version {v} contributes to the node at {c.path}, which counts version {node.version}"
    else
      let old := node.counter
      let finished := node.finished + c.mergeAmount
      let clocks := rmwClocks vc node.rel ord
      let vc := clocks.1
      let rel := clocks.2
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
def leafDone (leafPath : List Nat) (count : Nat) : ConsumerPhase → Nat
  | .start | .initializing => 0
  | .waitReady v | .beforeFunc v | .inFunc v => v
  | .walk v c => if c.path == leafPath then v else v + 1
  | .finish v => v + 1
  | .done => count

/-- The contributions currently carried towards the node at `path`:
`(consumer, version, amount)`. -/
def inFlightTo (path : List Nat) (cs : Array ConsumerPhase) : List (Nat × Nat × Nat) :=
  (List.range cs.size).filterMap fun id =>
    match cs[id]! with
    | .walk v c => if c.path == path then some (id, v, c.mergeAmount) else none
    | _ => none

/-- The violations of the counting invariant at one node (see the module
header). Written without loops so that `RearmBarrier.TreeCheck` can prove it
empty under `TreeInv`. -/
def Tree.nodeViolations (cfg : Config) (cs : Array ConsumerPhase) (path : List Nat) (t : Tree) :
    List String :=
  let here := s!"node {path} (window [{t.lo}, {t.hi}), version {t.version}, finished {t.finished})"
  let carried := inFlightTo path cs
  let inFlight := (carried.map (·.2.2)).sum
  (carried.filterMap fun (id, v, _) =>
    if v != t.version then some s!"consumer {id} at version {v} carries a contribution to {here}"
    else none) ++
  (if t.version > cfg.count then [s!"{here} is beyond the last version"] else []) ++
  (if t.finished ≥ t.size && t.size > 0 then [s!"{here} is full but was not advanced"] else []) ++
  (if t.isLeaf then
    -- a leaf counts the consumers of its window that did their fetch_add
    let ids := List.range' t.lo (t.hi - t.lo)
    let done := fun id => leafDone path cfg.count cs[id]!
    (ids.filterMap fun id =>
      if done id < t.version || done id > t.version + 1 then
        some s!"consumer {id} has done {done id} leaf contributions but its leaf is {here}"
      else none) ++
    (let contributed := (ids.map fun id => if done id == t.version + 1 then 1 else 0).sum
     if t.finished != contributed then [s!"{here} has {contributed} consumers past their fetch_add"]
     else []) ++
    (carried.filterMap fun (id, _, amount) =>
      if amount != 1 then some s!"consumer {id} carries {amount} to leaf {here}" else none)
  else if t.children.any (·.size == cfg.workers) then
    -- dead: the crate stops at the child that covers every worker
    if t.version != 0 || t.finished != 0 || !carried.isEmpty then
      [s!"{here} is above the node covering every worker but was touched"]
    else []
  else
    -- live: children one version ahead have filled and been (or are being) propagated
    (t.children.zipIdx.filterMap fun (child, k) =>
      if child.version < t.version || child.version > t.version + 1 then
        some s!"child {k} of {here} counts version {child.version}"
      else none) ++
    (let filled := (t.children.map fun child => if child.version == t.version + 1 then child.size else 0).sum
     if t.finished + inFlight != filled then
       [s!"{here} plus {inFlight} in flight does not match {filled} finished below it"]
     else []))

mutual
/-- The violations of the counting invariant at the node at `path` and
everything below it, in pre-order. -/
def Tree.invariant (cfg : Config) (cs : Array ConsumerPhase) (path : List Nat) : Tree → List String
  | .mk v f r lo hi children =>
    Tree.nodeViolations cfg cs path (.mk v f r lo hi children) ++
      Tree.invariantChildren cfg cs path 0 children

/-- The violations below the children from slot `k` on. -/
def Tree.invariantChildren (cfg : Config) (cs : Array ConsumerPhase) (path : List Nat) (k : Nat) :
    List Tree → List String
  | [] => []
  | c :: rest => c.invariant cfg cs (path ++ [k]) ++ Tree.invariantChildren cfg cs path (k + 1) rest
end

end RearmBarrier
