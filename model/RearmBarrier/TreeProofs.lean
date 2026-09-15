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
        refine ⟨rfl, rfl, rfl, by omega, ?_, ?_, ?_, by simp [hlt], by simp⟩
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
            refine ⟨rfl, rfl, rfl, by omega, hcounter, ?_, by simp [heq, hall], ?_, by simp⟩
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
              refine ⟨rfl, rfl, rfl, by omega, hcounter, ?_, ?_, ?_, ?_⟩
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
  obtain ⟨node', hnode', hv, hid, hamount, hold, hle, _, _, hfin, hstop, hcont⟩ := walk_spec h
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

end RearmBarrier
