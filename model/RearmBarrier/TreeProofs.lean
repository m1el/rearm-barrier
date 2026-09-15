import RearmBarrier.TreeModel

/-!
# Properties of the executable tree

What is proved about `RearmBarrier.TreeModel`:

* `modifyAt` is a well-defined update: it changes exactly the node at its
  path (`get_modifyAt_self`) and, when the function keeps a node's window
  and children, no window anywhere changes (`get_window_modifyAt`);
* `Tree.walk` is one `fetch_add` on the node under the cursor
  (`walk_spec`): the event carries the crate's ticket index, the cursor's
  amount and the node's counter as `old`, afterwards that node's counter is
  `old + amount`, no window changes, and the consumer's next move is
  decided by whether the node filled and whether it covers every worker;
* that decision is the crate's (`walk_crate`): expressed on the crate's
  numbers — heap index, `target_val`, `new_val` — the tree's next move is
  `if new_val == WORKERS * (v + 1) { finished } else if ticket_id == 0 ||
  new_val != target_val * (v + 1) { stop } else { continue at (ticket_id -
  1) / CLUSTER with target_val }`, provided the node covers at most every
  worker (the walk itself checks the version and refuses to overflow or to
  fill a root that does not cover every worker);
* `Tree.build` places a node of height `h` at `lo` over the window
  `[lo, lo + C ^ (h + 1)) ∩ [0, W)` (`build_lo`, `build_hi`), and the root
  of `Tree.init` covers exactly `[0, WORKERS)` for every valid
  configuration (`init_root_window`), which is where the crate's
  `ticket_tree_alloc` loop enters (`pow_levels_ge`).
-/

namespace RearmBarrier

/-! ## Lists -/

theorem getElem?_set_self' : (cs : List Tree) → (k : Nat) → (ch x : Tree) → cs[k]? = some ch →
    (cs.set k x)[k]? = some x
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _ => by simp
  | _ :: cs, k + 1, ch, x, h => by
    simp at h
    simp [getElem?_set_self' cs k ch x h]

theorem getElem?_set_ne' : (cs : List Tree) → (k j : Nat) → (x : Tree) → j ≠ k →
    (cs.set k x)[j]? = cs[j]?
  | [], _, _, _, _ => by simp
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => by simp
  | _ :: _, _ + 1, 0, _, _ => by simp
  | _ :: cs, k + 1, j + 1, x, h => by
    simp
    exact getElem?_set_ne' cs k j x (by omega)

/-! ## `modifyAt` -/

namespace Tree

@[simp] theorem version_mk (v f : Nat) (r : VC) (lo hi : Nat) (cs : List Tree) :
    (Tree.mk v f r lo hi cs).version = v := rfl
@[simp] theorem finished_mk (v f : Nat) (r : VC) (lo hi : Nat) (cs : List Tree) :
    (Tree.mk v f r lo hi cs).finished = f := rfl
@[simp] theorem lo_mk (v f : Nat) (r : VC) (lo hi : Nat) (cs : List Tree) :
    (Tree.mk v f r lo hi cs).lo = lo := rfl
@[simp] theorem hi_mk (v f : Nat) (r : VC) (lo hi : Nat) (cs : List Tree) :
    (Tree.mk v f r lo hi cs).hi = hi := rfl
@[simp] theorem children_mk (v f : Nat) (r : VC) (lo hi : Nat) (cs : List Tree) :
    (Tree.mk v f r lo hi cs).children = cs := rfl

@[simp] theorem children_withChildren (t : Tree) (cs : List Tree) : (t.withChildren cs).children = cs := by
  cases t; rfl

@[simp] theorem lo_withChildren (t : Tree) (cs : List Tree) : (t.withChildren cs).lo = t.lo := by
  cases t; rfl

@[simp] theorem hi_withChildren (t : Tree) (cs : List Tree) : (t.withChildren cs).hi = t.hi := by
  cases t; rfl

@[simp] theorem window_withChildren (t : Tree) (cs : List Tree) : (t.withChildren cs).window = t.window := by
  simp [window]

/-- `modifyAt` changes exactly the node at its path. -/
theorem get_modifyAt_self (f : Tree → Tree) : ∀ (t : Tree) (p : List Nat),
    (t.modifyAt f p).get p = (t.get p).map f
  | _, [] => by simp [modifyAt, get]
  | t, k :: p => by
    simp only [modifyAt, get]
    cases hk : t.children[k]? with
    | none => simp [hk]
    | some child =>
      simp only [children_withChildren, getElem?_set_self' _ _ _ _ hk]
      exact get_modifyAt_self f child p

/-- A node update that keeps the node's window and children. -/
structure Preserves (f : Tree → Tree) : Prop where
  lo : ∀ n, (f n).lo = n.lo
  hi : ∀ n, (f n).hi = n.hi
  children : ∀ n, (f n).children = n.children

theorem Preserves.window {f : Tree → Tree} (hf : Preserves f) (n : Tree) : (f n).window = n.window := by
  simp [Tree.window, hf.lo, hf.hi]

theorem Preserves.size {f : Tree → Tree} (hf : Preserves f) (n : Tree) : (f n).size = n.size := by
  simp [Tree.size, hf.lo, hf.hi]

/-- Updating a node with a window-preserving function changes no window
anywhere in the tree: the shape is fixed. -/
theorem get_window_modifyAt (f : Tree → Tree) (hf : Preserves f) : ∀ (t : Tree) (p q : List Nat),
    ((t.modifyAt f p).get q).map window = (t.get q).map window
  | t, [], q => by
    simp only [modifyAt]
    cases q with
    | nil => simp [get, hf.window]
    | cons j rest => simp [get, hf.children]
  | t, k :: p, q => by
    simp only [modifyAt]
    cases hk : t.children[k]? with
    | none => simp
    | some child =>
      cases q with
      | nil => simp [get]
      | cons j rest =>
        simp only [get, children_withChildren]
        by_cases hj : j = k
        · subst hj
          rw [getElem?_set_self' _ _ _ _ hk, hk]
          exact get_window_modifyAt f hf child p rest
        · rw [getElem?_set_ne' _ _ _ _ hj]

end Tree

/-! ## `walk` -/

/-- Everything `Tree.walk` does when it succeeds. -/
theorem walk_spec {cfg : Config} {t : Tree} {c : Cursor} {v : Nat} {vc : VC} {ord : MemOrd}
    {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next}
    (h : t.walk cfg c v vc ord = .ok t' vc' rmw next) :
    ∃ node, t.get c.path = some node ∧ node.version = v ∧
      rmw.ticketId = heapIndex cfg.cluster c.path ∧
      rmw.amount = c.mergeAmount ∧
      rmw.old = node.counter ∧
      node.finished + c.mergeAmount ≤ node.size ∧
      (t'.get c.path).map Tree.counter = some (node.counter + c.mergeAmount) ∧
      (∀ q, ((t'.get q).map Tree.window) = (t.get q).map Tree.window) ∧
      (∃ f, Tree.Preserves f ∧ t' = t.modifyAt f c.path) ∧
      (next = .finished ↔ node.finished + c.mergeAmount = node.size ∧ node.size = cfg.workers) ∧
      (next = .stop ↔ node.finished + c.mergeAmount < node.size) ∧
      (∀ c', next = .continue c' →
        c' = ⟨c.path.dropLast, node.size⟩ ∧ node.finished + c.mergeAmount = node.size ∧
        node.size ≠ cfg.workers ∧ c.path ≠ []) := by
  unfold Tree.walk at h
  split at h
  · simp at h
  · rename_i node hnode
    by_cases hv : node.version = v
    · simp only [hv, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      -- the two updates keep the window and the children
      have hpres1 : Tree.Preserves fun n =>
          Tree.mk n.version (node.finished + c.mergeAmount) (rmwClocks vc node.rel ord).2
            n.lo n.hi n.children :=
        ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
      have hpres2 : Tree.Preserves fun n =>
          Tree.mk (n.version + 1) 0 (rmwClocks vc node.rel ord).2 n.lo n.hi n.children :=
        ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
      refine ⟨node, hnode, hv, ?_⟩
      by_cases hlt : node.finished + c.mergeAmount < node.size
      · -- the window is not full yet
        simp only [hlt, ↓reduceIte, WalkResult.ok.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        refine ⟨rfl, rfl, rfl, by omega, ?_, ?_, ⟨_, hpres1, rfl⟩, ?_, by simp [hlt], by simp⟩
        · rw [Tree.get_modifyAt_self, hnode]
          simp only [Option.map_some, Tree.counter, Tree.size, Tree.version_mk, Tree.finished_mk,
            Tree.lo_mk, Tree.hi_mk]
          generalize (node.hi - node.lo) * node.version = A
          congr 1
          omega
        · intro q
          exact Tree.get_window_modifyAt _ hpres1 t c.path q
        · exact ⟨fun h' => by simp at h', fun h' => absurd h'.1 (Nat.ne_of_lt hlt)⟩
      · by_cases hgt : node.size < node.finished + c.mergeAmount
        · simp only [hlt, gt_iff_lt, hgt, ↓reduceIte, reduceCtorEq] at h
        · -- the window filled
          have heq : node.finished + c.mergeAmount = node.size := by omega
          have hcounter : Option.map Tree.counter ((t.modifyAt (fun n => Tree.mk (n.version + 1) 0
              (rmwClocks vc node.rel ord).2 n.lo n.hi n.children) c.path).get c.path)
              = some (node.counter + c.mergeAmount) := by
            rw [Tree.get_modifyAt_self, hnode]
            simp only [Option.map_some, Tree.counter, Tree.size, Tree.version_mk, Tree.finished_mk,
              Tree.lo_mk, Tree.hi_mk, Nat.mul_add, Nat.mul_one, Nat.add_zero]
            have heq' := heq
            simp only [Tree.size] at heq'
            generalize (node.hi - node.lo) * node.version = A
            congr 1
            omega
          simp only [hlt, gt_iff_lt, hgt, ↓reduceIte] at h
          by_cases hall : node.size = cfg.workers
          · -- every worker: finished
            simp only [hall, ↓reduceIte, WalkResult.ok.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            refine ⟨rfl, rfl, rfl, by omega, hcounter, ?_, ⟨_, hpres2, rfl⟩, by simp [heq, hall], ?_,
              by simp⟩
            · intro q
              exact Tree.get_window_modifyAt _ hpres2 t c.path q
            · exact ⟨fun h' => by simp at h', fun h' => absurd heq (Nat.ne_of_lt h')⟩
          · simp only [hall, ↓reduceIte] at h
            by_cases hnil : c.path = []
            · simp only [hnil, List.isEmpty_nil, ↓reduceIte, reduceCtorEq] at h
            · -- carry the window's size to the parent
              have hne : c.path.isEmpty = false := by
                cases hp : c.path with
                | nil => exact absurd hp hnil
                | cons _ _ => rfl
              simp only [hne, Bool.false_eq_true, ↓reduceIte, WalkResult.ok.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              refine ⟨rfl, rfl, rfl, by omega, hcounter, ?_, ⟨_, hpres2, rfl⟩, ?_, ?_, ?_⟩
              · intro q
                exact Tree.get_window_modifyAt _ hpres2 t c.path q
              · exact ⟨fun h' => by simp at h', fun h' => absurd h'.2 hall⟩
              · exact ⟨fun h' => by simp at h', fun h' => absurd heq (Nat.ne_of_lt h')⟩
              · intro c' hc'
                simp only [Next.continue.injEq] at hc'
                exact ⟨hc'.symm, heq, hall, hnil⟩
    · simp only [bne_iff_ne, ne_eq, hv, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- What the crate's loop does after `fetch_add` returned `old` on a ticket
whose window holds `target` workers. -/
inductive CrateNext
  | finished
  | stop
  | continue (ticketId mergeAmount : Nat)
deriving Repr, DecidableEq

def crateNext (W C ticketId target v newVal : Nat) : CrateNext :=
  if newVal = W * (v + 1) then .finished
  else if ticketId = 0 ∨ newVal ≠ target * (v + 1) then .stop
  else .continue (parent ticketId C) target

/-- The tree's next move in the crate's terms. -/
def Next.toCrate (C : Nat) : Next → CrateNext
  | .finished => .finished
  | .stop => .stop
  | .continue c => .continue (heapIndex C c.path) c.mergeAmount

theorem heapIndex_pos (C : Nat) (q : List Nat) (k : Nat) : 0 < heapIndex C (q ++ [k]) := by
  rw [heapIndex_append]
  omega

/-- The tree decides exactly as the crate does. -/
theorem walk_crate {cfg : Config} {t : Tree} {c : Cursor} {v : Nat} {vc : VC} {ord : MemOrd}
    {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next} {node : Tree}
    (h : t.walk cfg c v vc ord = .ok t' vc' rmw next)
    (hnode : t.get c.path = some node)
    (hC : 0 < cfg.cluster)
    (hdigits : ∀ k ∈ c.path, k < cfg.cluster)
    (hsize : node.size ≤ cfg.workers) :
    next.toCrate cfg.cluster =
      crateNext cfg.workers cfg.cluster rmw.ticketId node.size v (rmw.old + rmw.amount) := by
  obtain ⟨node', hnode', hv, hid, hamount, hold, hle, _, _, _, hfin, hstop, hcont⟩ := walk_spec h
  rw [hnode] at hnode'
  obtain rfl := Option.some.inj hnode'
  subst hv
  rw [hid, hold, hamount]
  have hW : node.size * node.version + node.size ≤ cfg.workers * node.version + cfg.workers := by
    have := Nat.mul_le_mul_right (node.version + 1) hsize
    simpa only [Nat.mul_add, Nat.mul_one] using this
  cases next with
  | finished =>
    obtain ⟨heq, hall⟩ := hfin.mp rfl
    simp only [Next.toCrate, crateNext, Tree.counter, Nat.mul_add, Nat.mul_one]
    -- make the products opaque: everything else is linear
    generalize hA : node.size * node.version = A at *
    generalize hB : cfg.workers * node.version = B at *
    split
    · rfl
    · exfalso
      rw [hall] at hA
      omega
  | stop =>
    have hlt := hstop.mp rfl
    simp only [Next.toCrate, crateNext, Tree.counter, Nat.mul_add, Nat.mul_one]
    generalize hA : node.size * node.version = A at *
    generalize hB : cfg.workers * node.version = B at *
    split
    · exfalso
      omega
    · split
      · rfl
      · exfalso
        omega
  | «continue» c' =>
    obtain ⟨rfl, heq, hnall, hne⟩ := hcont c' rfl
    have hlt : node.size < cfg.workers := Nat.lt_of_le_of_ne hsize hnall
    have hW' : node.size * node.version + node.size + (node.version + 1) ≤
        cfg.workers * node.version + cfg.workers := by
      have := Nat.mul_le_mul_right (node.version + 1) hlt
      simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul] at this
      omega
    obtain ⟨q, k, hqk⟩ : ∃ q k, c.path = q ++ [k] := by
      rcases List.eq_nil_or_concat c.path with h' | ⟨q, k, h'⟩
      · exact absurd h' hne
      · exact ⟨q, k, by rw [h', List.concat_eq_append]⟩
    have hk : k < cfg.cluster := hdigits k (by simp [hqk])
    have hpos := heapIndex_pos cfg.cluster q k
    simp only [Next.toCrate, crateNext, hqk, List.dropLast_concat, Tree.counter, Nat.mul_add,
      Nat.mul_one]
    generalize hA : node.size * node.version = A at *
    generalize hB : cfg.workers * node.version = B at *
    split
    · exfalso
      omega
    · split
      · exfalso
        omega
      · rw [parent_heapIndex _ hC _ _ hk]

/-! ## `build` -/

theorem build_lo (W C h lo : Nat) : (Tree.build W C h lo).lo = lo := by
  cases h <;> simp [Tree.build, Tree.lo]

theorem build_hi (W C h lo : Nat) : (Tree.build W C h lo).hi = min (lo + C ^ (h + 1)) W := by
  cases h with
  | zero => simp [Tree.build, Tree.hi]
  | succ h => simp [Tree.build, Tree.hi, Nat.pow_succ]

theorem build_children (W C h lo : Nat) :
    (Tree.build W C (h + 1) lo).children =
      Tree.buildChildren (Tree.build W C h) W (C ^ (h + 1)) lo C 0 := by
  simp [Tree.build, Tree.children]

theorem build_size_le (W C h lo : Nat) : (Tree.build W C h lo).size ≤ W := by
  simp only [Tree.size, build_lo, build_hi]
  omega

/-- The loop of `levels` stops at the first level whose width times the
fan-in reaches the number of leaves. -/
theorem levels_go_spec (base C : Nat) (hC : 2 ≤ C) :
    ∀ bot acc, bot = C ^ (acc - 1) → 1 ≤ acc →
      1 ≤ levels.go base C bot acc ∧ base ≤ C ^ (levels.go base C bot acc - 1) * C := by
  intro bot acc
  induction bot, acc using levels.go.induct base C with
  | case1 bot acc h ih =>
    intro hb hacc
    unfold levels.go
    simp only [h, and_self, ↓reduceIte]
    refine ih ?_ (by omega)
    rw [hb, ← Nat.pow_succ]
    congr 1
    omega
  | case2 bot acc h =>
    intro hb hacc
    unfold levels.go
    simp only [h, ↓reduceIte]
    refine ⟨hacc, ?_⟩
    have hpos : 1 ≤ bot := by
      rw [hb]
      exact Nat.pow_pos (by omega)
    rw [← hb]
    generalize bot * C = m at h ⊢
    omega

theorem pow_levels_ge (base C : Nat) (hC : 2 ≤ C) : base ≤ C ^ levels base C := by
  obtain ⟨h1, h2⟩ := levels_go_spec base C hC 1 1 (by simp) (by omega)
  unfold levels
  rw [← Nat.pow_succ] at h2
  have e : levels.go base C 1 1 - 1 + 1 = levels.go base C 1 1 := by omega
  change base ≤ C ^ (levels.go base C 1 1 - 1 + 1) at h2
  rw [e] at h2
  exact h2

theorem divCeil_mul_ge (W C : Nat) (hC : 1 ≤ C) : W ≤ divCeil W C * C := by
  unfold divCeil
  have h1 := Nat.div_add_mod (W + C - 1) C
  have h2 := Nat.mod_lt (W + C - 1) (show 0 < C by omega)
  rw [Nat.mul_comm]
  generalize C * ((W + C - 1) / C) = m at h1 ⊢
  omega

/-- The root of a valid configuration's tree covers exactly `[0, WORKERS)`. -/
theorem init_root_window (cfg : Config) (hC : 2 ≤ cfg.cluster) :
    (Tree.init cfg).lo = 0 ∧ (Tree.init cfg).hi = cfg.workers := by
  unfold Tree.init
  refine ⟨build_lo _ _ _ _, ?_⟩
  rw [build_hi]
  have h1 := pow_levels_ge cfg.baseSize cfg.cluster hC
  have h2 := divCeil_mul_ge cfg.workers cfg.cluster (by omega)
  have h3 : cfg.workers ≤ cfg.cluster ^ (rootHeight cfg + 1) := by
    rw [Nat.pow_succ]
    exact Nat.le_trans h2 (Nat.mul_le_mul_right _ h1)
  simp only [Nat.zero_add]
  exact Nat.min_eq_right h3

/-- Hence the root covers every worker, which is what `Tree.walk` relies on
to never fault at the root. -/
theorem init_root_size (cfg : Config) (hC : 2 ≤ cfg.cluster) :
    (Tree.init cfg).size = cfg.workers := by
  obtain ⟨h1, h2⟩ := init_root_window cfg hC
  simp [Tree.size, h1, h2]

/-! ## Well-formedness

`Wf C W` says what a completion tree for `W` workers and fan-in `C` looks
like: every node covers a non-empty window inside `[0, W)`, a leaf covers at
most `C` consumers, and an inner node has at most `C` children whose windows
tile its own window consecutively (`Tiles`). `Wf_build` shows `build`
produces such trees, `Wf.modifyAt` and `walk_wf` that the walk keeps them,
and `Wf.sum_children` is the fact the counting argument needs: a node's
`target_val` is the sum of its children's.
-/

/-- The windows of the nodes tile `[a, b)` consecutively. -/
def Tiles : Nat → Nat → List Tree → Prop
  | a, b, [] => a = b
  | a, b, t :: rest => t.lo = a ∧ Tiles t.hi b rest

inductive Wf (C W : Nat) : Tree → Prop
  | leaf (v f : Nat) (r : VC) (lo hi : Nat) (hlt : lo < hi) (hW : hi ≤ W) (hC : hi - lo ≤ C) :
      Wf C W (.mk v f r lo hi [])
  | node (v f : Nat) (r : VC) (lo hi : Nat) (cs : List Tree) (hne : cs ≠ [])
      (hlt : lo < hi) (hW : hi ≤ W) (hlen : cs.length ≤ C)
      (htiles : Tiles lo hi cs) (hcs : ∀ c ∈ cs, Wf C W c) :
      Wf C W (.mk v f r lo hi cs)

/-! ### `buildChildren` -/

theorem buildChildren_length_le (child : Nat → Tree) (W w lo : Nat) :
    ∀ n k, (Tree.buildChildren child W w lo n k).length ≤ n
  | 0, _ => by simp [Tree.buildChildren]
  | n + 1, k => by
    simp only [Tree.buildChildren]
    split
    · simp
      exact buildChildren_length_le child W w lo n (k + 1)
    · simp

theorem buildChildren_mem (child : Nat → Tree) (W w lo : Nat) :
    ∀ n k t, t ∈ Tree.buildChildren child W w lo n k → ∃ x, x < W ∧ t = child x
  | 0, _, _, h => by simp [Tree.buildChildren] at h
  | n + 1, k, t, h => by
    simp only [Tree.buildChildren] at h
    split at h
    · rename_i hk
      simp at h
      rcases h with rfl | h
      · exact ⟨_, hk, rfl⟩
      · exact buildChildren_mem child W w lo n (k + 1) t h
    · simp at h

theorem buildChildren_ne_nil (child : Nat → Tree) (W w lo n k : Nat) (hn : 0 < n)
    (hk : lo + k * w < W) : Tree.buildChildren child W w lo n k ≠ [] := by
  cases n with
  | zero => omega
  | succ n => simp [Tree.buildChildren, hk]

/-- The children tile the window: slot `k` starts at `lo + k * w`, capped at `W`. -/
theorem buildChildren_tiles (child : Nat → Tree) (W w lo : Nat)
    (hlo : ∀ x, (child x).lo = x) (hhi : ∀ x, (child x).hi = min (x + w) W) :
    ∀ n k, Tiles (min (lo + k * w) W) (min (lo + (k + n) * w) W)
      (Tree.buildChildren child W w lo n k)
  | 0, k => by simp [Tree.buildChildren, Tiles]
  | n + 1, k => by
    simp only [Tree.buildChildren]
    split
    · rename_i hk
      simp only [Tiles, hlo, hhi]
      refine ⟨by omega, ?_⟩
      have ih := buildChildren_tiles child W w lo hlo hhi n (k + 1)
      have e1 : lo + k * w + w = lo + (k + 1) * w := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have e2 : k + (n + 1) = k + 1 + n := by omega
      rw [e1, e2]
      exact ih
    · rename_i hk
      simp only [Tiles]
      have : lo + (k + (n + 1)) * w = lo + k * w + (n + 1) * w := by
        rw [Nat.add_mul]
        omega
      rw [this]
      omega

/-! ### `build` is well formed -/

theorem Wf_build (W C : Nat) (hC : 1 ≤ C) : ∀ h lo, lo < W → Wf C W (Tree.build W C h lo)
  | 0, lo, hlo => by
    simp only [Tree.build]
    exact .leaf _ _ _ _ _ (by omega) (Nat.min_le_right _ _) (by omega)
  | h + 1, lo, hlo => by
    have hw : 0 < C ^ (h + 1) := Nat.pow_pos (by omega)
    have hwC : 1 ≤ C ^ (h + 1) * C := Nat.mul_pos hw (by omega)
    simp only [Tree.build]
    refine .node _ _ _ _ _ _ ?_ ?_ (Nat.min_le_right _ _) ?_ ?_ ?_
    · exact buildChildren_ne_nil _ _ _ _ _ _ (by omega) (by simpa using hlo)
    · omega
    · exact buildChildren_length_le _ _ _ _ _ _
    · have := buildChildren_tiles (Tree.build W C h) W (C ^ (h + 1)) lo
        (build_lo W C h) (build_hi W C h) C 0
      simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.min_eq_left (Nat.le_of_lt hlo)] at this
      rw [Nat.mul_comm] at this
      exact this
    · intro c hc
      obtain ⟨x, hx, rfl⟩ := buildChildren_mem _ _ _ _ _ _ _ hc
      exact Wf_build W C hC h x hx

/-- The tree of every valid configuration is well formed. -/
theorem init_wf (cfg : Config) (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) :
    Wf cfg.cluster cfg.workers (Tree.init cfg) :=
  Wf_build _ _ (by omega) _ 0 hW

/-! ### Consequences of well-formedness -/

theorem Wf.lo_lt_hi {C W : Nat} {t : Tree} (h : Wf C W t) : t.lo < t.hi := by
  cases h <;> assumption

theorem Wf.hi_le {C W : Nat} {t : Tree} (h : Wf C W t) : t.hi ≤ W := by
  cases h <;> assumption

theorem Wf.size_pos {C W : Nat} {t : Tree} (h : Wf C W t) : 0 < t.size := by
  have := h.lo_lt_hi
  simp only [Tree.size]
  omega

theorem Wf.size_le {C W : Nat} {t : Tree} (h : Wf C W t) : t.size ≤ W := by
  have := h.hi_le
  simp only [Tree.size]
  omega

theorem Wf.children_wf {C W : Nat} {t : Tree} (h : Wf C W t) : ∀ c ∈ t.children, Wf C W c := by
  cases h with
  | leaf => simp [Tree.children]
  | node _ _ _ _ _ _ _ _ _ _ _ hcs => exact hcs

theorem Wf.children_length {C W : Nat} {t : Tree} (h : Wf C W t) : t.children.length ≤ C := by
  cases h with
  | leaf => simp [Tree.children]
  | node _ _ _ _ _ _ _ _ _ hlen => exact hlen

/-- Every node reachable by a path is well formed. -/
theorem Wf.get {C W : Nat} : ∀ (p : List Nat) {t n : Tree}, Wf C W t → t.get p = some n → Wf C W n
  | [], t, n, h, hg => by
    simp [Tree.get] at hg
    exact hg ▸ h
  | k :: p, t, n, h, hg => by
    simp only [Tree.get] at hg
    split at hg
    · rename_i c hk
      exact Wf.get p (h.children_wf c (mem_of_getElem?' _ _ _ hk)) hg
    · simp at hg
where
  mem_of_getElem?' : (cs : List Tree) → (k : Nat) → (c : Tree) → cs[k]? = some c → c ∈ cs
    | [], _, _, h => by simp at h
    | _ :: _, 0, _, h => by simp at h; simp [h]
    | _ :: cs, k + 1, c, h => by
      simp at h
      exact List.mem_cons_of_mem _ (mem_of_getElem?' cs k c h)

theorem lt_length_of_getElem?' : (cs : List Tree) → (k : Nat) → (c : Tree) → cs[k]? = some c →
    k < cs.length
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => by simp
  | _ :: cs, k + 1, c, h => by
    simp at h
    have := lt_length_of_getElem?' cs k c h
    simp
    omega

/-- Every digit of a path into a well-formed tree is below the fan-in. -/
theorem Wf.digits {C W : Nat} : ∀ (p : List Nat) {t n : Tree}, Wf C W t → t.get p = some n →
    ∀ k ∈ p, k < C
  | [], _, _, _, _ => by simp
  | j :: p, t, n, h, hg => by
    simp only [Tree.get] at hg
    split at hg
    · rename_i c hj
      have hjlt : j < t.children.length := lt_length_of_getElem?' _ _ _ hj
      have hlen := h.children_length
      have hrest := Wf.digits p (h.children_wf c (Wf.get.mem_of_getElem?' _ _ _ hj)) hg
      intro k hk
      simp at hk
      rcases hk with rfl | hk
      · omega
      · exact hrest k hk
    · simp at hg

/-- A node's window is the sum of its children's: `target_val` adds up. -/
theorem tiles_sum : ∀ (cs : List Tree) (a b : Nat), Tiles a b cs → (∀ c ∈ cs, c.lo ≤ c.hi) →
    a ≤ b ∧ (cs.map Tree.size).sum = b - a
  | [], a, b, h, _ => by simp [Tiles] at h; simp [h]
  | c :: cs, a, b, h, hle => by
    simp only [Tiles] at h
    obtain ⟨hlo, hrest⟩ := h
    have hc := hle c (by simp)
    obtain ⟨h1, h2⟩ := tiles_sum cs c.hi b hrest fun x hx => hle x (by simp [hx])
    simp only [List.map_cons, List.sum_cons, Tree.size, h2, hlo]
    omega

theorem Wf.sum_children {C W : Nat} {v f : Nat} {r : VC} {lo hi : Nat} {cs : List Tree}
    (h : Wf C W (.mk v f r lo hi cs)) (hne : cs ≠ []) : (cs.map Tree.size).sum = hi - lo := by
  cases h with
  | leaf => exact absurd rfl hne
  | node _ _ _ _ _ _ _ _ _ _ htiles hcs =>
    exact (tiles_sum cs lo hi htiles fun c hc => Nat.le_of_lt (hcs c hc).lo_lt_hi).2

/-! ### Well-formedness is preserved by updates -/

theorem tiles_set : ∀ (cs : List Tree) (a b k : Nat) (c c' : Tree), Tiles a b cs →
    cs[k]? = some c → c'.window = c.window → Tiles a b (cs.set k c')
  | [], _, _, _, _, _, _, hk, _ => by simp at hk
  | x :: cs, a, b, 0, c, c', h, hk, hw => by
    simp at hk
    subst hk
    simp only [Tiles, List.set_cons_zero] at h ⊢
    simp only [Tree.window, Prod.mk.injEq] at hw
    rw [hw.1, hw.2]
    exact h
  | x :: cs, a, b, k + 1, c, c', h, hk, hw => by
    simp at hk
    simp only [Tiles, List.set_cons_succ] at h ⊢
    exact ⟨h.1, tiles_set cs _ b k c c' h.2 hk hw⟩

theorem Wf.modifyAt {C W : Nat} {f : Tree → Tree} (hf : Tree.Preserves f) :
    ∀ (p : List Nat) {t : Tree}, Wf C W t → Wf C W (t.modifyAt f p)
  | [], t, h => by
    simp only [Tree.modifyAt]
    cases hft : f t with
    | mk v' f' r' lo' hi' cs' =>
      have hlo := hf.lo t
      have hhi := hf.hi t
      have hcs := hf.children t
      rw [hft] at hlo hhi hcs
      simp only [Tree.lo_mk, Tree.hi_mk, Tree.children_mk] at hlo hhi hcs
      subst hlo hhi hcs
      cases h with
      | leaf _ _ _ _ _ hlt hW hC => exact .leaf _ _ _ _ _ hlt hW hC
      | node _ _ _ _ _ _ hne hlt hW hlen htiles hcs => exact .node _ _ _ _ _ _ hne hlt hW hlen htiles hcs
  | k :: p, t, h => by
    simp only [Tree.modifyAt]
    cases hk : t.children[k]? with
    | none => exact h
    | some child =>
      cases h with
      | leaf => simp [Tree.children] at hk
      | node v n r lo hi cs hne hlt hW hlen htiles hcs =>
        simp only [Tree.children_mk] at hk
        have hchild := hcs child (Wf.get.mem_of_getElem?' _ _ _ hk)
        have ih := Wf.modifyAt hf p hchild
        simp only [Tree.withChildren]
        refine .node _ _ _ _ _ _ ?_ hlt hW (by simpa using hlen) ?_ ?_
        · intro he
          have := congrArg List.length he
          simp at this
          exact hne this
        · refine tiles_set cs lo hi k child _ htiles hk ?_
          have := Tree.get_window_modifyAt f hf child p []
          simpa [Tree.get] using this
        · intro c hc
          rcases mem_of_mem_set' cs k _ c hc with hc | rfl
          · exact hcs c hc
          · exact ih
where
  mem_of_mem_set' : (cs : List Tree) → (k : Nat) → (x y : Tree) → y ∈ cs.set k x → y ∈ cs ∨ y = x
    | [], _, _, _, h => by simp at h
    | _ :: _, 0, _, _, h => by
      simp at h
      rcases h with rfl | h
      · exact Or.inr rfl
      · exact Or.inl (by simp [h])
    | c :: cs, k + 1, x, y, h => by
      simp at h
      rcases h with rfl | h
      · exact Or.inl (by simp)
      · rcases mem_of_mem_set' cs k x y h with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr h

/-- The walk keeps the tree well formed. -/
theorem walk_wf {cfg : Config} {t : Tree} {c : Cursor} {v : Nat} {vc : VC} {ord : MemOrd}
    {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next}
    (hwf : Wf cfg.cluster cfg.workers t) (h : t.walk cfg c v vc ord = .ok t' vc' rmw next) :
    Wf cfg.cluster cfg.workers t' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨f, hf, rfl⟩, _⟩ := walk_spec h
  exact Wf.modifyAt hf _ hwf

/-- On a well-formed tree the walk decides as the crate does, with no side
conditions: this holds along every execution from `Tree.init`. -/
theorem walk_crate_wf {cfg : Config} {t : Tree} {c : Cursor} {v : Nat} {vc : VC} {ord : MemOrd}
    {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next} {node : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hC : 0 < cfg.cluster)
    (h : t.walk cfg c v vc ord = .ok t' vc' rmw next) (hnode : t.get c.path = some node) :
    next.toCrate cfg.cluster =
      crateNext cfg.workers cfg.cluster rmw.ticketId node.size v (rmw.old + rmw.amount) :=
  walk_crate h hnode hC (hwf.digits _ hnode) (Wf.get _ hwf hnode).size_le

end RearmBarrier
