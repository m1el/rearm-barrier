import RearmBarrier.TreeProofs
import RearmBarrier.Model

/-!
# The counting invariant, as a proposition

`Tree.invariant` in `RearmBarrier.TreeModel` is executable (and `partial`),
so nothing can be proved about it. This file restates it as a `Prop`,
`TreeInv`, indexed by paths: a property of every node reachable by `get`,
whose children are addressed as `path ++ [k]`. That way no induction over
the nested inductive `Tree` is ever needed; the preservation proof only has
to know how `get` composes over paths (`get_append_singleton`) and what
`modifyAt` at one path does to every other node (`get_modifyAt_ne`).

Consumers are abstracted as a function `phase : Nat → ConsumerPhase`, so that
updating one consumer is `upd`, a point update.

`V` is the version the producer is working on. The invariant says, for a
node counting version `n.version`:

* every contribution carried towards it is for `n.version`, and
  `n.version` is `V` or `V + 1` (`0` for a dead node);
* a leaf's counter is the number of its consumers past their leaf
  `fetch_add`, each of them at most one version ahead, and carried
  contributions to a leaf are `1`;
* a live inner node's counter plus what is carried towards it is the size
  of its children one version ahead, no child being further ahead;
* a dead node (one with a child covering every worker) is never touched;

plus shape facts about the consumers' cursors: a walking consumer's cursor
is on the path to its leaf, the leaf containing a consumer is the one
`Cursor.start` points to, and every carried amount is positive.
-/

namespace RearmBarrier

/-! ## Paths -/

theorem Tree.get_append_singleton (t : Tree) : ∀ (q : List Nat) (k : Nat),
    t.get (q ++ [k]) = (t.get q).bind fun n => n.children[k]?
  | [], k => by
    simp only [List.nil_append, Tree.get, Option.bind_some]
    cases t.children[k]? <;> simp
  | j :: q, k => by
    simp only [List.cons_append, Tree.get]
    cases t.children[j]? with
    | none => simp
    | some c => exact c.get_append_singleton q k

/-- The part of a node that `modifyAt` at another path cannot change. -/
def Tree.fields (n : Tree) : Nat × Nat × Nat × Nat × Nat :=
  (n.version, n.finished, n.lo, n.hi, n.children.length)

theorem Tree.fields_withChildren (t : Tree) (cs : List Tree) (h : cs.length = t.children.length) :
    (t.withChildren cs).fields = t.fields := by
  cases t
  simp [Tree.fields, Tree.withChildren, Tree.version, Tree.finished, Tree.lo, Tree.hi,
    Tree.children] at h ⊢
  exact h

/-- `modifyAt` at `p` leaves the version, counter, window and number of
children of every node at a path `q ≠ p` unchanged. -/
theorem Tree.get_modifyAt_ne (f : Tree → Tree) (hf : Tree.Preserves f) :
    ∀ (t : Tree) (p q : List Nat), q ≠ p →
      ((t.modifyAt f p).get q).map Tree.fields = (t.get q).map Tree.fields
  | t, [], q, hq => by
    simp only [Tree.modifyAt]
    cases q with
    | nil => exact absurd rfl hq
    | cons j rest => simp [Tree.get, hf.children]
  | t, k :: p, q, hq => by
    simp only [Tree.modifyAt]
    cases hk : t.children[k]? with
    | none => rfl
    | some child =>
      cases q with
      | nil =>
        simp only [Tree.get, Option.map_some]
        rw [Tree.fields_withChildren]
        simp
      | cons j rest =>
        simp only [Tree.get, Tree.children_withChildren]
        by_cases hj : j = k
        · subst hj
          rw [getElem?_set_self' _ _ _ _ hk, hk]
          exact Tree.get_modifyAt_ne f hf child p rest (fun h => hq (by rw [h]))
        · rw [getElem?_set_ne' _ _ _ _ hj]

theorem Tree.fields_inj {a b : Tree} (h : a.fields = b.fields) :
    a.version = b.version ∧ a.finished = b.finished ∧ a.lo = b.lo ∧ a.hi = b.hi ∧
      a.children.length = b.children.length := by
  simp only [Tree.fields, Prod.mk.injEq] at h
  exact h

theorem Tree.size_of_fields {a b : Tree} (h : a.fields = b.fields) : a.size = b.size := by
  obtain ⟨_, _, h3, h4, _⟩ := Tree.fields_inj h
  simp [Tree.size, h3, h4]

/-! ## Consumers -/

/-- Point update of the consumers' phases. -/
def upd (phase : Nat → ConsumerPhase) (id : Nat) (ph : ConsumerPhase) : Nat → ConsumerPhase :=
  fun j => if j = id then ph else phase j

@[simp] theorem upd_self (phase : Nat → ConsumerPhase) (id : Nat) (ph : ConsumerPhase) :
    upd phase id ph id = ph := by simp [upd]

theorem upd_ne (phase : Nat → ConsumerPhase) (id : Nat) (ph : ConsumerPhase) {j : Nat} (h : j ≠ id) :
    upd phase id ph j = phase j := by simp [upd, h]

/-- What a consumer carries towards the node at `path`. -/
def carryOf (path : List Nat) : ConsumerPhase → Nat
  | .walk _ c => if c.path = path then c.mergeAmount else 0
  | _ => 0

/-- Everything carried towards the node at `path`. -/
def carriedTo (W : Nat) (path : List Nat) (phase : Nat → ConsumerPhase) : Nat :=
  ((List.range W).map fun id => carryOf path (phase id)).sum

/-- Whether consumer `id` in the window of the leaf at `path` is past its leaf
`fetch_add` for version `ver`. -/
def pastLeaf (count : Nat) (path : List Nat) (ver : Nat) (ph : ConsumerPhase) : Nat :=
  if leafDone path count ph = ver + 1 then 1 else 0

/-- How many consumers of the window `[lo, hi)` are past their leaf `fetch_add`. -/
def contributedIn (count : Nat) (path : List Nat) (lo hi ver : Nat) (phase : Nat → ConsumerPhase) : Nat :=
  ((List.range' lo (hi - lo)).map fun id => pastLeaf count path ver (phase id)).sum

/-- What a child contributes to `filledBelow`: its size if it counts version `w`. -/
def filledOf (w : Nat) : Option Tree → Nat
  | some c => if c.version = w then c.size else 0
  | none => 0

/-- The total size of the children of the node `n` at `path` that are one
version ahead of it. -/
def filledBelow (t : Tree) (path : List Nat) (n : Tree) : Nat :=
  ((List.range n.children.length).map fun k => filledOf (n.version + 1) (t.get (path ++ [k]))).sum

/-- A node above the one covering every worker: the crate never touches it. -/
def deadAt (W : Nat) (t : Tree) (path : List Nat) (n : Tree) : Prop :=
  ∃ k, k < n.children.length ∧ ∃ c, t.get (path ++ [k]) = some c ∧ c.size = W

/-! ## The invariant -/

structure NodeInv (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (t : Tree)
    (path : List Nat) (n : Tree) : Prop where
  carried_version : ∀ id, id < cfg.workers → ∀ v c, phase id = .walk v c → c.path = path →
    v = n.version
  not_full : n.finished < n.size
  version_le : n.version ≤ V + 1
  version_ge : ¬ deadAt cfg.workers t path n → V ≤ n.version
  leaf : n.children = [] →
    (∀ id, n.lo ≤ id → id < n.hi →
      n.version ≤ leafDone path cfg.count (phase id) ∧
      leafDone path cfg.count (phase id) ≤ n.version + 1) ∧
    n.finished = contributedIn cfg.count path n.lo n.hi n.version phase ∧
    (∀ id, id < cfg.workers → ∀ v c, phase id = .walk v c → c.path = path → c.mergeAmount = 1)
  live : n.children ≠ [] → ¬ deadAt cfg.workers t path n →
    (∀ k, k < n.children.length → ∃ c, t.get (path ++ [k]) = some c ∧
      n.version ≤ c.version ∧ c.version ≤ n.version + 1) ∧
    n.finished + carriedTo cfg.workers path phase = filledBelow t path n
  dead : deadAt cfg.workers t path n →
    n.version = 0 ∧ n.finished = 0 ∧ carriedTo cfg.workers path phase = 0

structure TreeInv (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (t : Tree) : Prop where
  nodes : ∀ path n, t.get path = some n → NodeInv cfg V phase t path n
  /-- a walking consumer's cursor is on the path from the root to its leaf -/
  walkers : ∀ id, id < cfg.workers → ∀ v c, phase id = .walk v c →
    c.path <+: (Cursor.start cfg id).path
  /-- every carried amount is positive -/
  carry_pos : ∀ id, id < cfg.workers → ∀ v c, phase id = .walk v c → 0 < c.mergeAmount
  /-- `Cursor.start` points every consumer to a leaf containing it -/
  leaves : ∀ id, id < cfg.workers → ∃ leaf, t.get (Cursor.start cfg id).path = some leaf ∧
    leaf.children = [] ∧ leaf.lo ≤ id ∧ id < leaf.hi
  /-- and it is the only leaf containing it -/
  leaf_unique : ∀ q leaf, t.get q = some leaf → leaf.children = [] →
    ∀ id, leaf.lo ≤ id → id < leaf.hi → q = (Cursor.start cfg id).path

/-! ## Sums over consumers -/

theorem sum_map_upd_of_not_mem (g : ConsumerPhase → Nat) (phase : Nat → ConsumerPhase)
    (id : Nat) (ph : ConsumerPhase) :
    ∀ (l : List Nat), id ∉ l →
      (l.map fun j => g (upd phase id ph j)).sum = (l.map fun j => g (phase j)).sum
  | [], _ => rfl
  | j :: l, h => by
    have hj : j ≠ id := fun e => h (by simp [e])
    have hl : id ∉ l := fun e => h (by simp [e])
    simp [upd_ne phase id ph hj, sum_map_upd_of_not_mem g phase id ph l hl]

theorem sum_map_upd (g : ConsumerPhase → Nat) (phase : Nat → ConsumerPhase)
    (id : Nat) (ph : ConsumerPhase) :
    ∀ (l : List Nat), l.Nodup → id ∈ l →
      (l.map fun j => g (upd phase id ph j)).sum + g (phase id) =
        (l.map fun j => g (phase j)).sum + g ph
  | [], _, h => by simp at h
  | j :: l, hnd, h => by
    simp only [List.nodup_cons] at hnd
    simp at h
    rcases h with rfl | h
    · rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, upd_self,
        sum_map_upd_of_not_mem g phase id ph l hnd.1]
      omega
    · have hj : j ≠ id := fun e => hnd.1 (e ▸ h)
      have := sum_map_upd g phase id ph l hnd.2 h
      simp only [List.map_cons, List.sum_cons, upd_ne phase id ph hj]
      omega

theorem carriedTo_upd_of_ge (W path phase id ph) (h : W ≤ id) :
    carriedTo W path (upd phase id ph) = carriedTo W path phase := by
  unfold carriedTo
  exact sum_map_upd_of_not_mem _ _ _ _ _ (by simp; omega)

theorem carriedTo_upd (W path phase id ph) (h : id < W) :
    carriedTo W path (upd phase id ph) + carryOf path (phase id) =
      carriedTo W path phase + carryOf path ph := by
  unfold carriedTo
  exact sum_map_upd _ _ _ _ _ List.nodup_range (by simp [h])

theorem contributedIn_upd_of_not_mem (count path lo hi ver phase id ph) (h : ¬ (lo ≤ id ∧ id < hi)) :
    contributedIn count path lo hi ver (upd phase id ph) = contributedIn count path lo hi ver phase := by
  unfold contributedIn
  refine sum_map_upd_of_not_mem _ _ _ _ _ ?_
  simp only [List.mem_range'_1]
  omega

theorem contributedIn_upd (count path lo hi ver phase id ph) (h : lo ≤ id ∧ id < hi) :
    contributedIn count path lo hi ver (upd phase id ph) + pastLeaf count path ver (phase id) =
      contributedIn count path lo hi ver phase + pastLeaf count path ver ph := by
  unfold contributedIn
  refine sum_map_upd _ _ _ _ _ (List.nodup_range' (s := lo) (n := hi - lo) 1) ?_
  simp only [List.mem_range'_1]
  omega

/-! ## More about paths -/

theorem Tree.get_append (t : Tree) : ∀ (p r : List Nat), t.get (p ++ r) = (t.get p).bind fun n => n.get r
  | [], r => by simp [Tree.get]
  | j :: p, r => by
    simp only [List.cons_append, Tree.get]
    cases t.children[j]? with
    | none => simp
    | some c => exact c.get_append p r

/-- A leaf has nothing below it. -/
theorem Tree.get_leaf_append {t : Tree} {p : List Nat} {n : Tree} (hn : t.get p = some n)
    (hleaf : n.children = []) : ∀ r m, t.get (p ++ r) = some m → r = []
  | [], _, _ => rfl
  | j :: r, m, h => by
    rw [Tree.get_append, hn, Option.bind_some] at h
    simp [Tree.get, hleaf] at h

/-- The only node at or below a leaf is the leaf itself. -/
theorem Tree.prefix_leaf {t : Tree} {p q : List Nat} {n m : Tree} (hn : t.get p = some n)
    (hleaf : n.children = []) (hpq : p <+: q) (hm : t.get q = some m) : q = p := by
  obtain ⟨r, rfl⟩ := hpq
  have := Tree.get_leaf_append hn hleaf r m hm
  simp [this]

/-- A node with a child is not a leaf. -/
theorem Tree.children_ne_nil_of_get {t : Tree} {q : List Nat} {k : Nat} {n c : Tree}
    (hn : t.get q = some n) (hc : t.get (q ++ [k]) = some c) : n.children ≠ [] := by
  intro h
  rw [Tree.get_append_singleton, hn, Option.bind_some, h] at hc
  simp at hc

/-- The shape of a node: what no update touches. -/
def Tree.shape (n : Tree) : Nat × Nat × Nat := (n.lo, n.hi, n.children.length)

theorem Tree.shape_of_fields {a b : Tree} (h : a.fields = b.fields) : a.shape = b.shape := by
  obtain ⟨_, _, h3, h4, h5⟩ := Tree.fields_inj h
  simp [Tree.shape, h3, h4, h5]

theorem Tree.get_modifyAt_shape (f : Tree → Tree) (hf : Tree.Preserves f) (t : Tree) (p q : List Nat) :
    ((t.modifyAt f p).get q).map Tree.shape = (t.get q).map Tree.shape := by
  by_cases hq : q = p
  · subst hq
    rw [Tree.get_modifyAt_self]
    cases t.get q with
    | none => rfl
    | some n => simp [Tree.shape, hf.lo, hf.hi, hf.children]
  · have := Tree.get_modifyAt_ne f hf t p q hq
    cases h1 : (t.modifyAt f p).get q <;> cases h2 : t.get q <;> simp [h1, h2] at this ⊢
    exact Tree.shape_of_fields this

theorem Tree.shape_inj {a b : Tree} (h : a.shape = b.shape) :
    a.lo = b.lo ∧ a.hi = b.hi ∧ a.children.length = b.children.length := by
  simp only [Tree.shape, Prod.mk.injEq] at h
  exact h

theorem Tree.size_of_shape {a b : Tree} (h : a.shape = b.shape) : a.size = b.size := by
  obtain ⟨h1, h2, _⟩ := Tree.shape_inj h
  simp [Tree.size, h1, h2]

/-- Dead-ness depends only on the shape below the node. -/
theorem deadAt_of_shape {W : Nat} {t t' : Tree} {q : List Nat} {n n' : Tree}
    (hshape : ∀ r, (t'.get r).map Tree.shape = (t.get r).map Tree.shape)
    (hlen : n'.children.length = n.children.length) :
    deadAt W t' q n' ↔ deadAt W t q n := by
  unfold deadAt
  rw [hlen]
  constructor
  · rintro ⟨k, hk, c', hc', hs⟩
    have := hshape (q ++ [k])
    rw [hc'] at this
    cases hc : t.get (q ++ [k]) with
    | none => simp [hc] at this
    | some c =>
      simp [hc] at this
      exact ⟨k, hk, c, hc, by rw [← Tree.size_of_shape this]; exact hs⟩
  · rintro ⟨k, hk, c, hc, hs⟩
    have := hshape (q ++ [k])
    rw [hc] at this
    cases hc' : t'.get (q ++ [k]) with
    | none => simp [hc'] at this
    | some c' =>
      simp [hc'] at this
      exact ⟨k, hk, c', hc', by rw [Tree.size_of_shape this]; exact hs⟩

/-! ## Values of the per-consumer functions -/

@[simp] theorem carryOf_walk (path : List Nat) (v : Nat) (c : Cursor) :
    carryOf path (.walk v c) = if c.path = path then c.mergeAmount else 0 := rfl

@[simp] theorem carryOf_finish (path : List Nat) (v : Nat) : carryOf path (.finish v) = 0 := rfl
@[simp] theorem carryOf_waitReady (path : List Nat) (v : Nat) : carryOf path (.waitReady v) = 0 := rfl
@[simp] theorem carryOf_done (path : List Nat) : carryOf path .done = 0 := rfl

theorem carryOf_nextConsumer (cfg : Config) (path : List Nat) (v : Nat) :
    carryOf path (nextConsumer cfg v) = 0 := by
  unfold nextConsumer
  split <;> rfl

@[simp] theorem leafDone_walk (leafPath : List Nat) (count v : Nat) (c : Cursor) :
    leafDone leafPath count (.walk v c) = if c.path == leafPath then v else v + 1 := rfl

@[simp] theorem leafDone_finish (leafPath : List Nat) (count v : Nat) :
    leafDone leafPath count (.finish v) = v + 1 := rfl

theorem leafDone_nextConsumer (cfg : Config) (leafPath : List Nat) (v : Nat) (hv : v < cfg.count) :
    leafDone leafPath cfg.count (nextConsumer cfg v) = v + 1 := by
  unfold nextConsumer
  split
  · rfl
  · simp only [leafDone]
    omega

theorem le_sum_of_mem' : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.sum
  | [], _, h => by simp at h
  | a :: l, x, h => by
    simp at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := le_sum_of_mem' l x h
      omega

theorem carryOf_le_carriedTo (W : Nat) (path : List Nat) (phase : Nat → ConsumerPhase) (id : Nat)
    (h : id < W) : carryOf path (phase id) ≤ carriedTo W path phase := by
  unfold carriedTo
  have hm : id ∈ List.range W := by simp [h]
  exact le_sum_of_mem' _ _ (List.mem_map_of_mem hm)

/-! ## Sums over `List.range` -/

theorem sum_range_congr_except (g g' : Nat → Nat) (k : Nat) :
    ∀ n, k < n → (∀ j, j < n → j ≠ k → g' j = g j) →
      ((List.range n).map g').sum + g k = ((List.range n).map g).sum + g' k
  | 0, h, _ => by omega
  | n + 1, hk, hne => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hkn : k = n
    · subst hkn
      have : ((List.range k).map g').sum = ((List.range k).map g).sum := by
        apply congrArg
        apply List.map_congr_left
        intro j hj
        simp at hj
        exact hne j (by omega) (by omega)
      rw [this]
      omega
    · have := sum_range_congr_except g g' k n (by omega) (fun j hj hjk => hne j (by omega) hjk)
      rw [hne n (by omega) (Ne.symm hkn)]
      omega

theorem sum_range_congr (g g' : Nat → Nat) (n : Nat) (h : ∀ j, j < n → g' j = g j) :
    ((List.range n).map g').sum = ((List.range n).map g).sum := by
  apply congrArg
  apply List.map_congr_left
  intro j hj
  simp at hj
  exact h j hj

theorem sum_map_eq_zero {α : Type} (l : List α) (g : α → Nat) (h : ∀ x ∈ l, g x = 0) :
    (l.map g).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (by simp), ih fun x hx => h x (by simp [hx])]

/-- An indicator sum over a window is at most the window's length, with
equality only when every indicator is `1`. -/
theorem sum_indicator_le {α : Type} (l : List α) (g : α → Nat) (h : ∀ x ∈ l, g x ≤ 1) :
    (l.map g).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (by simp)
    have := ih fun x hx => h x (by simp [hx])
    omega

theorem all_one_of_sum_indicator {α : Type} (l : List α) (g : α → Nat) (h : ∀ x ∈ l, g x ≤ 1)
    (hsum : (l.map g).sum = l.length) : ∀ x ∈ l, g x = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have ha := h a (by simp)
    have hl := sum_indicator_le l g fun x hx => h x (by simp [hx])
    intro x hx
    simp at hx
    rcases hx with rfl | hx
    · omega
    · exact ih (fun y hy => h y (by simp [hy])) (by omega) x hx

/-- The children of the node at `path`, addressed by paths, are its children list. -/
theorem get_child {t : Tree} {path : List Nat} {n : Tree} (hn : t.get path = some n) (k : Nat) :
    t.get (path ++ [k]) = n.children[k]? := by
  rw [Tree.get_append_singleton, hn, Option.bind_some]

theorem sum_range_getElem? {α : Type} (g : Option α → Nat) (h0 : g none = 0) :
    ∀ (l : List α), ((List.range l.length).map fun k => g l[k]?).sum = (l.map fun x => g (some x)).sum
  | [] => by simp [h0]
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_cons,
      List.sum_cons, List.map_map]
    simp only [List.getElem?_cons_zero, Function.comp_def, List.getElem?_cons_succ]
    rw [sum_range_getElem? g h0 l]

/-- `filledBelow` as a sum over the children list. -/
theorem filledBelow_eq {t : Tree} {path : List Nat} {n : Tree} (hn : t.get path = some n) :
    filledBelow t path n = (n.children.map fun c => filledOf (n.version + 1) (some c)).sum := by
  unfold filledBelow
  have : ∀ k, filledOf (n.version + 1) (t.get (path ++ [k])) =
      filledOf (n.version + 1) n.children[k]? := fun k => by rw [get_child hn]
  simp only [this]
  exact sum_range_getElem? _ rfl n.children

theorem filledOf_some (w : Nat) (c : Tree) :
    filledOf w (some c) = if c.version = w then c.size else 0 := rfl

theorem sum_filledOf_le (w : Nat) : ∀ (cs : List Tree),
    (cs.map fun c => filledOf w (some c)).sum ≤ (cs.map Tree.size).sum
  | [] => by simp
  | c :: cs => by
    have := sum_filledOf_le w cs
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, filledOf_some]
    split <;> omega

set_option linter.deprecated false in
theorem all_version_of_sum_filledOf (w : Nat) : ∀ (cs : List Tree), (∀ c ∈ cs, 0 < c.size) →
    (cs.map fun c => filledOf w (some c)).sum = (cs.map Tree.size).sum → ∀ c ∈ cs, c.version = w
  | [], _, _, _, h => by simp at h
  | x :: cs, hpos, heq, c, hc => by
    have hle := sum_filledOf_le w cs
    have hx := hpos x (by simp)
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, filledOf_some] at heq
    have hxv : x.version = w := by
      by_cases h : x.version = w
      · exact h
      · exfalso
        rw [if_neg h] at heq
        omega
    simp at hc
    rcases hc with rfl | hc
    · exact hxv
    · refine all_version_of_sum_filledOf w cs (fun c hc => hpos c (by simp [hc])) ?_ c hc
      rw [if_pos hxv] at heq
      omega

theorem Wf.sum_children' {C W : Nat} {n : Tree} (h : Wf C W n) (hne : n.children ≠ []) :
    (n.children.map Tree.size).sum = n.size := by
  cases n with
  | mk v f r lo hi cs =>
    simp only [Tree.children_mk] at hne
    have := h.sum_children hne
    simpa [Tree.children_mk, Tree.size_mk] using this

/-- `filledBelow` never exceeds the node's size ... -/
theorem filledBelow_le {C W : Nat} {t : Tree} {path : List Nat} {n : Tree}
    (hwf : Wf C W t) (hn : t.get path = some n) (hne : n.children ≠ []) :
    filledBelow t path n ≤ n.size := by
  rw [filledBelow_eq hn, ← (Wf.get path hwf hn).sum_children' hne]
  exact sum_filledOf_le _ _

/-- ... and reaches it only when every child is one version ahead. -/
theorem all_filled_of_filledBelow_eq {C W : Nat} {t : Tree} {path : List Nat} {n : Tree}
    (hwf : Wf C W t) (hn : t.get path = some n) (hne : n.children ≠ [])
    (heq : filledBelow t path n = n.size) :
    ∀ k c, t.get (path ++ [k]) = some c → c.version = n.version + 1 := by
  intro k c hc
  have hwfn := Wf.get path hwf hn
  rw [filledBelow_eq hn, ← hwfn.sum_children' hne] at heq
  rw [get_child hn] at hc
  exact all_version_of_sum_filledOf _ _ (fun c hc => (hwfn.children_wf c hc).size_pos) heq c
    (Wf.get.mem_of_getElem?' _ _ _ hc)

/-! ## The walk step preserves the invariant -/

/-- The phase a consumer moves to after its `fetch_add`, as in `consumerStep`. -/
def nextPhase (cfg : Config) (v : Nat) : Next → ConsumerPhase
  | .finished => .finish v
  | .stop => nextConsumer cfg v
  | .continue c => .walk v c

theorem get_of_shape {t t' : Tree} {q : List Nat} {n' : Tree}
    (h : (t'.get q).map Tree.shape = (t.get q).map Tree.shape) (hq : t'.get q = some n') :
    ∃ n, t.get q = some n ∧ n'.shape = n.shape := by
  rw [hq] at h
  cases hn : t.get q with
  | none => simp [hn] at h
  | some n => simp [hn] at h; exact ⟨n, rfl, h⟩

theorem get_of_fields {t t' : Tree} {q : List Nat} {n' : Tree}
    (h : (t'.get q).map Tree.fields = (t.get q).map Tree.fields) (hq : t'.get q = some n') :
    ∃ n, t.get q = some n ∧ n'.fields = n.fields := by
  rw [hq] at h
  cases hn : t.get q with
  | none => simp [hn] at h
  | some n => simp [hn] at h; exact ⟨n, rfl, h⟩

theorem dropLast_ne_self {p : List Nat} (h : p ≠ []) : p.dropLast ≠ p := by
  intro e
  have := congrArg List.length e
  rw [List.length_dropLast] at this
  cases p with
  | nil => exact h rfl
  | cons _ _ => simp at this

theorem carryOf_nextPhase_ne (cfg : Config) (v : Nat) (next : Next) (q : List Nat)
    (h : ∀ c', next = .continue c' → c'.path ≠ q) : carryOf q (nextPhase cfg v next) = 0 := by
  cases next with
  | finished => rfl
  | stop => exact carryOf_nextConsumer cfg q v
  | «continue» c' => simp [nextPhase, h c' rfl]

theorem leafDone_nextPhase (cfg : Config) (v : Nat) (next : Next) (q : List Nat) (hv : v < cfg.count)
    (h : ∀ c', next = .continue c' → c'.path ≠ q) :
    leafDone q cfg.count (nextPhase cfg v next) = v + 1 := by
  cases next with
  | finished => rfl
  | stop => exact leafDone_nextConsumer cfg q v hv
  | «continue» c' =>
    have := h c' rfl
    simp [nextPhase, this]

theorem nextPhase_walk {cfg : Config} {V : Nat} {next : Next} {v' : Nat} {c' : Cursor}
    (h : nextPhase cfg V next = .walk v' c') : next = .continue c' ∧ v' = V := by
  cases next with
  | finished => simp [nextPhase] at h
  | stop =>
    exfalso
    have h' : nextConsumer cfg V = .walk v' c' := h
    unfold nextConsumer at h'
    split at h' <;> injection h'
  | «continue» c'' =>
    have h' : ConsumerPhase.walk V c'' = .walk v' c' := h
    injection h' with h1 h2
    subst h1 h2
    exact ⟨rfl, rfl⟩

theorem get_of_fields' {t t' : Tree} {q : List Nat} {n : Tree}
    (h : (t'.get q).map Tree.fields = (t.get q).map Tree.fields) (hq : t.get q = some n) :
    ∃ n', t'.get q = some n' ∧ n'.fields = n.fields := by
  rw [hq] at h
  cases hn : t'.get q with
  | none => simp [hn] at h
  | some n' => simp [hn] at h; exact ⟨n', rfl, h⟩

theorem get_of_shape' {t t' : Tree} {q : List Nat} {n : Tree}
    (h : (t'.get q).map Tree.shape = (t.get q).map Tree.shape) (hq : t.get q = some n) :
    ∃ n', t'.get q = some n' ∧ n'.shape = n.shape := by
  rw [hq] at h
  cases hn : t'.get q with
  | none => simp [hn] at h
  | some n' => simp [hn] at h; exact ⟨n', rfl, h⟩

theorem filledOf_of_fields {w : Nat} {o o' : Option Tree} (h : o'.map Tree.fields = o.map Tree.fields) :
    filledOf w o' = filledOf w o := by
  cases o <;> cases o' <;> simp at h <;> simp [filledOf]
  obtain ⟨h1, _, _⟩ := Tree.fields_inj h
  rw [h1, Tree.size_of_fields h]

theorem append_singleton_ne (q : List Nat) (k : Nat) : q ++ [k] ≠ q := by
  intro h
  have := congrArg List.length h
  simp at this

theorem pastLeaf_le_one (count : Nat) (path : List Nat) (ver : Nat) (ph : ConsumerPhase) :
    pastLeaf count path ver ph ≤ 1 := by
  unfold pastLeaf
  split <;> omega

/-- The node under the cursor after its `fetch_add`. -/
theorem nodeInv_self {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t)
    {id : Nat} {c : Cursor} (hid : id < cfg.workers) (hph : phase id = .walk V c) (hvc : V < cfg.count)
    {vc : VC} {ord : MemOrd} {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next}
    (hwalk : t.walk cfg c V vc ord = .ok t' vc' rmw next)
    {n' : Tree} (hn' : t'.get c.path = some n') :
    NodeInv cfg V (upd phase id (nextPhase cfg V next)) t' c.path n' := by
  obtain ⟨n, hn, hver, -, -, -, hle, ⟨f, hf, rfl⟩, ⟨n'', hn'', hlo, hhi, hch, hnf, hfl⟩, hfin, hstop, hcont⟩ :=
    walk_spec hwalk
  rw [hn''] at hn'
  rw [← Option.some.inj hn']
  have hnode := hinv.nodes _ n hn
  have hwfn := Wf.get _ hwf hn
  have hmpos := hinv.carry_pos id hid V c hph
  have hcarry : carryOf c.path (phase id) = c.mergeAmount := by simp [hph]
  have hshape := Tree.get_modifyAt_shape f hf t c.path
  have hfields : ∀ r, r ≠ c.path →
      ((t.modifyAt f c.path).get r).map Tree.fields = (t.get r).map Tree.fields :=
    fun r hr => Tree.get_modifyAt_ne f hf t c.path r hr
  have hsize : n''.size = n.size := by simp [Tree.size, hlo, hhi]
  have hlive : ¬ deadAt cfg.workers t c.path n := by
    intro hd
    have := hnode.dead hd
    have := carryOf_le_carriedTo cfg.workers c.path phase id hid
    omega
  have hdead' : deadAt cfg.workers (t.modifyAt f c.path) c.path n'' ↔ deadAt cfg.workers t c.path n :=
    deadAt_of_shape hshape (by rw [hch])
  have hnext_ne : ∀ c', next = .continue c' → c'.path ≠ c.path := by
    intro c' hc'
    obtain ⟨rfl, -, -, hne⟩ := hcont c' hc'
    exact dropLast_ne_self hne
  have hcarry' : carryOf c.path (nextPhase cfg V next) = 0 := carryOf_nextPhase_ne cfg V next _ hnext_ne
  have hcarried := carriedTo_upd cfg.workers c.path phase id (nextPhase cfg V next) hid
  rw [hcarry, hcarry'] at hcarried
  have hcle := carryOf_le_carriedTo cfg.workers c.path phase id hid
  rw [hcarry] at hcle
  have hlD' : leafDone c.path cfg.count (nextPhase cfg V next) = V + 1 :=
    leafDone_nextPhase cfg V next _ hvc hnext_ne
  have hchild : ∀ k, ((t.modifyAt f c.path).get (c.path ++ [k])).map Tree.fields =
      (t.get (c.path ++ [k])).map Tree.fields :=
    fun k => hfields _ (append_singleton_ne _ _)
  -- the stepping consumer never carries anything to `c.path` afterwards
  have hno_self : ∀ v' c', upd phase id (nextPhase cfg V next) id = .walk v' c' → c'.path ≠ c.path := by
    intro v' c' h
    rw [upd_self] at h
    obtain ⟨h1, -⟩ := nextPhase_walk h
    exact hnext_ne c' h1
  -- if `n` is a leaf, the consumer is at its own leaf and inside its window
  have hleafcase : n.children = [] → c.path = (Cursor.start cfg id).path ∧ n.lo ≤ id ∧ id < n.hi := by
    intro hnil
    obtain ⟨leaf, hleaf, -, hleaflo, hleafhi⟩ := hinv.leaves id hid
    have hpre := hinv.walkers id hid V c hph
    have hpl := Tree.prefix_leaf hn hnil hpre hleaf
    rw [hpl] at hleaf
    obtain rfl := Option.some.inj (hleaf.symm.trans hn)
    exact ⟨hpl.symm, hleaflo, hleafhi⟩
  by_cases hfill : n.finished + c.mergeAmount = n.size
  · -- the window filled
    obtain ⟨hv', hf'⟩ := hfl hfill
    -- an inner node: everything carried was this consumer's, and every child is one version ahead
    have hW4 : n.children ≠ [] → carriedTo cfg.workers c.path phase = c.mergeAmount ∧
        ∀ k cc, t.get (c.path ++ [k]) = some cc → cc.version = V + 1 := by
      intro hne
      obtain ⟨-, heq⟩ := hnode.live hne hlive
      have h1 := filledBelow_le hwf hn hne
      have hfb : filledBelow t c.path n = n.size := by omega
      refine ⟨by omega, ?_⟩
      intro k cc hcc
      have := all_filled_of_filledBelow_eq hwf hn hne hfb k cc hcc
      rw [hver] at this
      exact this
    -- a leaf: every consumer of the window is now past its fetch_add
    have hW3 : n.children = [] → ∀ j, n.lo ≤ j → j < n.hi →
        leafDone c.path cfg.count (upd phase id (nextPhase cfg V next) j) = V + 1 := by
      intro hnil
      obtain ⟨hpl, hidlo, hidhi⟩ := hleafcase hnil
      obtain ⟨-, hcount, hamt⟩ := hnode.leaf hnil
      have hm1 : c.mergeAmount = 1 := hamt id hid V c hph rfl
      have hsum := contributedIn_upd cfg.count c.path n.lo n.hi V phase id (nextPhase cfg V next)
        ⟨hidlo, hidhi⟩
      have h0 : pastLeaf cfg.count c.path V (phase id) = 0 := by simp [pastLeaf, hph]
      have h1 : pastLeaf cfg.count c.path V (nextPhase cfg V next) = 1 := by simp [pastLeaf, hlD']
      rw [hver] at hcount
      rw [h0, h1, ← hcount] at hsum
      have hall := all_one_of_sum_indicator (List.range' n.lo (n.hi - n.lo))
        (fun j => pastLeaf cfg.count c.path V (upd phase id (nextPhase cfg V next) j))
        (fun _ _ => pastLeaf_le_one _ _ _ _)
        (by rw [List.length_range']; unfold contributedIn at hsum; simp only [Tree.size] at hfill; omega)
      intro j hj1 hj2
      have := hall j (by simp only [List.mem_range'_1]; omega)
      unfold pastLeaf at this
      split at this
      · assumption
      · omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- carried_version: nobody carries to a node that just filled
      intro id' hid' v' c' hph' hpath
      by_cases h : id' = id
      · subst h
        exact absurd hpath (hno_self v' c' hph')
      · rw [upd_ne _ _ _ h] at hph'
        exfalso
        by_cases hnil : n.children = []
        · obtain ⟨leaf', hleaf', hleafnil', hlo', hhi'⟩ := hinv.leaves id' hid'
          have hpre := hinv.walkers id' hid' v' c' hph'
          rw [hpath] at hpre
          have hpl := Tree.prefix_leaf hn hnil hpre hleaf'
          rw [hpl] at hleaf'
          obtain rfl := Option.some.inj (hleaf'.symm.trans hn)
          have := hW3 hnil id' hlo' hhi'
          rw [upd_ne _ _ _ h, hph'] at this
          simp [hpath] at this
          have := hnode.carried_version id' hid' v' c' hph' hpath
          omega
        · have hcar := (hW4 hnil).1
          have hpos := hinv.carry_pos id' hid' v' c' hph'
          have h2 := carryOf_le_carriedTo cfg.workers c.path (upd phase id (nextPhase cfg V next)) id' hid'
          rw [upd_ne _ _ _ h, hph'] at h2
          simp [hpath] at h2
          omega
    · rw [hf', hsize]; exact hwfn.size_pos
    · omega
    · intro _; omega
    · intro hnil
      rw [hch] at hnil
      obtain ⟨hpl, hidlo, hidhi⟩ := hleafcase hnil
      obtain ⟨-, -, hamt⟩ := hnode.leaf hnil
      have h3 := hW3 hnil
      refine ⟨?_, ?_, ?_⟩
      · intro j hj1 hj2
        rw [hlo] at hj1; rw [hhi] at hj2
        rw [hv', h3 j hj1 hj2]
        omega
      · rw [hf', hlo, hhi, hv']
        symm
        apply sum_map_eq_zero
        intro j hj
        simp only [List.mem_range'_1] at hj
        simp [pastLeaf, h3 j hj.1 (by omega)]
      · intro id' hid' v' c' hph' hpath
        by_cases h : id' = id
        · subst h; exact absurd hpath (hno_self v' c' hph')
        · rw [upd_ne _ _ _ h] at hph'
          exact hamt id' hid' v' c' hph' hpath
    · intro hne hnd
      rw [hch] at hne
      obtain ⟨hcar, hall⟩ := hW4 hne
      obtain ⟨hcb, -⟩ := hnode.live hne hlive
      refine ⟨?_, ?_⟩
      · intro k hk
        rw [hch] at hk
        obtain ⟨cc, hcc, -, -⟩ := hcb k hk
        obtain ⟨cc', hcc', hfe⟩ := get_of_fields' (hchild k) hcc
        obtain ⟨hv1, -⟩ := Tree.fields_inj hfe
        refine ⟨cc', hcc', ?_, ?_⟩ <;> rw [hv1, hall k cc hcc, hv'] <;> omega
      · rw [hf']
        have hz : carriedTo cfg.workers c.path (upd phase id (nextPhase cfg V next)) = 0 := by omega
        rw [hz]
        symm
        unfold filledBelow
        rw [hch, hv']
        apply sum_map_eq_zero
        intro k hk
        simp only [List.mem_range] at hk
        rw [filledOf_of_fields (hchild k)]
        cases hcc : t.get (c.path ++ [k]) with
        | none => rfl
        | some cc =>
          have := hall k cc hcc
          simp [filledOf, this]
    · intro hd
      exact absurd (hdead'.mp hd) hlive
  · -- the window is not full yet
    have hlt : n.finished + c.mergeAmount < n.size := by omega
    obtain ⟨hv', hf'⟩ := hnf hlt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro id' hid' v' c' hph' hpath
      by_cases h : id' = id
      · subst h; exact absurd hpath (hno_self v' c' hph')
      · rw [upd_ne _ _ _ h] at hph'
        rw [hv', ← hver]
        exact hnode.carried_version id' hid' v' c' hph' hpath
    · rw [hf', hsize]; exact hlt
    · omega
    · intro _; omega
    · intro hnil
      rw [hch] at hnil
      obtain ⟨hpl, hidlo, hidhi⟩ := hleafcase hnil
      obtain ⟨hb, hcount, hamt⟩ := hnode.leaf hnil
      have hm1 : c.mergeAmount = 1 := hamt id hid V c hph rfl
      refine ⟨?_, ?_, ?_⟩
      · intro j hj1 hj2
        rw [hlo] at hj1; rw [hhi] at hj2
        rw [hv']
        by_cases h : j = id
        · subst h; rw [upd_self, hlD']; omega
        · rw [upd_ne _ _ _ h, ← hver]
          exact hb j hj1 hj2
      · rw [hf', hlo, hhi, hv', hm1]
        have hsum := contributedIn_upd cfg.count c.path n.lo n.hi V phase id (nextPhase cfg V next)
          ⟨hidlo, hidhi⟩
        have h0 : pastLeaf cfg.count c.path V (phase id) = 0 := by simp [pastLeaf, hph]
        have h1 : pastLeaf cfg.count c.path V (nextPhase cfg V next) = 1 := by simp [pastLeaf, hlD']
        rw [hver] at hcount
        rw [h0, h1, ← hcount] at hsum
        omega
      · intro id' hid' v' c' hph' hpath
        by_cases h : id' = id
        · subst h; exact absurd hpath (hno_self v' c' hph')
        · rw [upd_ne _ _ _ h] at hph'
          exact hamt id' hid' v' c' hph' hpath
    · intro hne hnd
      rw [hch] at hne
      obtain ⟨hcb, heq⟩ := hnode.live hne hlive
      refine ⟨?_, ?_⟩
      · intro k hk
        rw [hch] at hk
        obtain ⟨cc, hcc, h1, h2⟩ := hcb k hk
        obtain ⟨cc', hcc', hfe⟩ := get_of_fields' (hchild k) hcc
        obtain ⟨hv1, -⟩ := Tree.fields_inj hfe
        refine ⟨cc', hcc', ?_, ?_⟩ <;> rw [hv1, hv', ← hver] <;> assumption
      · rw [hf']
        have hfb : filledBelow (t.modifyAt f c.path) c.path n'' = filledBelow t c.path n := by
          unfold filledBelow
          rw [hch, hv', ← hver]
          apply sum_range_congr
          intro k _
          exact filledOf_of_fields (hchild k)
        rw [hfb, ← heq]
        omega
    · intro hd
      exact absurd (hdead'.mp hd) hlive

/-- Two distinct entries of a list of numbers are bounded by its sum. -/
theorem getElem?_two_le_sum : ∀ (l : List Nat) (i j a b : Nat), i ≠ j → l[i]? = some a → l[j]? = some b →
    a + b ≤ l.sum
  | [], _, _, _, _, _, h, _ => by simp at h
  | x :: l, 0, 0, _, _, hij, _, _ => absurd rfl hij
  | x :: l, 0, j + 1, a, b, _, ha, hb => by
    simp at ha hb
    subst ha
    have := le_sum_of_mem' l b (List.mem_of_getElem? hb)
    simp only [List.sum_cons]
    omega
  | x :: l, i + 1, 0, a, b, _, ha, hb => by
    simp at ha hb
    subst hb
    have := le_sum_of_mem' l a (List.mem_of_getElem? ha)
    simp only [List.sum_cons]
    omega
  | x :: l, i + 1, j + 1, a, b, hij, ha, hb => by
    simp at ha hb
    have := getElem?_two_le_sum l i j a b (by omega) ha hb
    simp only [List.sum_cons]
    omega

/-- Two different children of a well-formed node together are no bigger than
the node. -/
theorem two_children_le {C W : Nat} {t : Tree} {q : List Nat} {nq : Tree} (hwf : Wf C W t)
    (hq : t.get q = some nq) (hne : nq.children ≠ []) {j k : Nat} {cj ck : Tree}
    (hjk : j ≠ k) (hj : t.get (q ++ [j]) = some cj) (hk : t.get (q ++ [k]) = some ck) :
    cj.size + ck.size ≤ nq.size := by
  rw [← (Wf.get q hwf hq).sum_children' hne]
  rw [get_child hq] at hj hk
  have hj' : (nq.children.map Tree.size)[j]? = some cj.size := by simp [hj]
  have hk' : (nq.children.map Tree.size)[k]? = some ck.size := by simp [hk]
  exact getElem?_two_le_sum _ j k _ _ hjk hj' hk'

theorem append_singleton_inj {q : List Nat} {j k : Nat} (h : q ++ [j] = q ++ [k]) : j = k := by
  have := List.append_cancel_left h
  simpa using this

/-- The parent of the node under the cursor. -/
theorem nodeInv_parent {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t)
    {id : Nat} {c : Cursor} (hid : id < cfg.workers) (hph : phase id = .walk V c) (hvc : V < cfg.count)
    {vc : VC} {ord : MemOrd} {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next}
    (hwalk : t.walk cfg c V vc ord = .ok t' vc' rmw next)
    {q : List Nat} {k : Nat} (hpq : c.path = q ++ [k]) {nq' : Tree} (hq' : t'.get q = some nq') :
    NodeInv cfg V (upd phase id (nextPhase cfg V next)) t' q nq' := by
  obtain ⟨n, hn, hver, -, -, -, hle, ⟨f, hf, rfl⟩, ⟨n'', hn'', hlo, hhi, hch, hnf, hfl⟩, hfin, hstop, hcont⟩ :=
    walk_spec hwalk
  have hqne : q ≠ c.path := by rw [hpq]; exact (append_singleton_ne q k).symm
  have hfields := Tree.get_modifyAt_ne f hf t c.path
  have hshape := Tree.get_modifyAt_shape f hf t c.path
  obtain ⟨nq, hq, hfe⟩ := get_of_fields (hfields q hqne) hq'
  obtain ⟨hqv, hqf, hqlo, hqhi, hqlen⟩ := Tree.fields_inj hfe
  have hqsize : nq'.size = nq.size := Tree.size_of_fields hfe
  have hnodeq := hinv.nodes q nq hq
  have hchildk : t.get (q ++ [k]) = some n := by rw [← hpq]; exact hn
  have hchildk' : (t.modifyAt f c.path).get (q ++ [k]) = some n'' := by rw [← hpq]; exact hn''
  have hne : nq.children ≠ [] := Tree.children_ne_nil_of_get hq hchildk
  have hklt : k < nq.children.length := by
    rw [get_child hq] at hchildk
    exact lt_length_of_getElem?' _ _ _ hchildk
  have hcarry0 : carryOf q (phase id) = 0 := by simp [hph, hqne.symm]
  have hcarried := carriedTo_upd cfg.workers q phase id (nextPhase cfg V next) hid
  rw [hcarry0] at hcarried
  have hdead' : deadAt cfg.workers (t.modifyAt f c.path) q nq' ↔ deadAt cfg.workers t q nq :=
    deadAt_of_shape hshape hqlen
  have hchild : ∀ j, j ≠ k → ((t.modifyAt f c.path).get (q ++ [j])).map Tree.fields =
      (t.get (q ++ [j])).map Tree.fields := by
    intro j hj
    apply hfields
    rw [hpq]
    intro h
    exact hj (append_singleton_inj h)
  have hn''size : n''.size = n.size := by simp [Tree.size, hlo, hhi]
  have hnotleaf : nq'.children ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [hqlen] at this
    exact hne (List.eq_nil_of_length_eq_zero this)
  -- the walker's phase afterwards
  have hph' : ∀ v' c', upd phase id (nextPhase cfg V next) id = .walk v' c' →
      next = .continue c' ∧ v' = V := by
    intro v' c' h
    rw [upd_self] at h
    exact nextPhase_walk h
  by_cases hfill : n.finished + c.mergeAmount = n.size
  · obtain ⟨hv', hf'⟩ := hfl hfill
    by_cases hall : n.size = cfg.workers
    · -- the barrier completed: `q` is dead and stays untouched
      have hnext : next = .finished := hfin.mpr ⟨hfill, hall⟩
      subst hnext
      have hdead : deadAt cfg.workers t q nq := ⟨k, hklt, n, hchildk, hall⟩
      obtain ⟨hdv, hdf, hdc⟩ := hnodeq.dead hdead
      have hc' : carryOf q (nextPhase cfg V .finished) = 0 := rfl
      rw [hc'] at hcarried
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro id' hid' v' c' h hpath
        by_cases hh : id' = id
        · subst hh
          obtain ⟨h1, -⟩ := hph' v' c' h
          cases h1
        · rw [upd_ne _ _ _ hh] at h
          rw [hqv]
          exact hnodeq.carried_version id' hid' v' c' h hpath
      · rw [hqf, hqsize]; exact hnodeq.not_full
      · rw [hqv]; exact hnodeq.version_le
      · intro h; rw [hqv]; exact hnodeq.version_ge (fun hd => h (hdead'.mpr hd))
      · intro h; exact absurd h hnotleaf
      · intro _ h; exact absurd (hdead'.mpr hdead) h
      · intro _; exact ⟨by rw [hqv, hdv], by rw [hqf, hdf], by omega⟩
    · -- the window filled below `W`: the consumer carries its size to `q`
      have hnext : next = .continue ⟨q, n.size⟩ := by
        cases next with
        | finished => exact absurd (hfin.mp rfl).2 hall
        | stop => have := hstop.mp rfl; omega
        | «continue» c' =>
          obtain ⟨rfl, -, -, -⟩ := hcont c' rfl
          rw [hpq, List.dropLast_concat]
      subst hnext
      have hqlive : ¬ deadAt cfg.workers t q nq := by
        rintro ⟨j, hj, cj, hcj, hcjs⟩
        by_cases hjk : j = k
        · subst hjk
          rw [hchildk] at hcj
          obtain rfl := Option.some.inj hcj
          exact hall hcjs
        · have := two_children_le hwf hq hne hjk hcj hchildk
          have := (Wf.get q hwf hq).size_le
          have := (Wf.get _ hwf hchildk).size_pos
          omega
      obtain ⟨hcb, heq⟩ := hnodeq.live hne hqlive
      have hqV : nq.version = V := by
        obtain ⟨cc, hcc, h1, h2⟩ := hcb k hklt
        rw [hchildk] at hcc
        obtain rfl := Option.some.inj hcc
        have := hnodeq.version_ge hqlive
        omega
      have hc' : carryOf q (nextPhase cfg V (.continue ⟨q, n.size⟩)) = n.size := by
        simp [nextPhase]
      rw [hc'] at hcarried
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro id' hid' v' c' h hpath
        by_cases hh : id' = id
        · subst hh
          obtain ⟨-, rfl⟩ := hph' v' c' h
          omega
        · rw [upd_ne _ _ _ hh] at h
          rw [hqv]
          exact hnodeq.carried_version id' hid' v' c' h hpath
      · rw [hqf, hqsize]; exact hnodeq.not_full
      · rw [hqv]; exact hnodeq.version_le
      · intro _; omega
      · intro h; exact absurd h hnotleaf
      · intro _ _
        refine ⟨?_, ?_⟩
        · intro j hj
          rw [hqlen] at hj
          by_cases hjk : j = k
          · subst hjk
            exact ⟨n'', hchildk', by omega, by omega⟩
          · obtain ⟨cc, hcc, h1, h2⟩ := hcb j hj
            obtain ⟨cc', hcc', hfe'⟩ := get_of_fields' (hchild j hjk) hcc
            obtain ⟨hv1, -⟩ := Tree.fields_inj hfe'
            exact ⟨cc', hcc', by omega, by omega⟩
        · rw [hqf]
          have hfb : filledBelow (t.modifyAt f c.path) q nq' + filledOf (nq.version + 1) (some n) =
              filledBelow t q nq + filledOf (nq.version + 1) (some n'') := by
            unfold filledBelow
            rw [hqlen, hqv]
            have := sum_range_congr_except
              (fun j => filledOf (nq.version + 1) (t.get (q ++ [j])))
              (fun j => filledOf (nq.version + 1) ((t.modifyAt f c.path).get (q ++ [j])))
              k nq.children.length hklt
              (fun j _ hjk => filledOf_of_fields (hchild j hjk))
            simp only [hchildk, hchildk'] at this
            exact this
          have h1 : filledOf (nq.version + 1) (some n) = 0 := by simp [filledOf, hver, hqV]
          have h2 : filledOf (nq.version + 1) (some n'') = n.size := by
            simp [filledOf, hv', hqV, hn''size]
          rw [h1, h2] at hfb
          omega
      · intro h; exact absurd (hdead'.mp h) hqlive
  · -- the window is not full: nothing changes for `q`
    have hlt : n.finished + c.mergeAmount < n.size := by omega
    obtain ⟨hv', hf'⟩ := hnf hlt
    have hnext : next = .stop := hstop.mpr hlt
    subst hnext
    have hc' : carryOf q (nextPhase cfg V .stop) = 0 := carryOf_nextConsumer cfg q V
    rw [hc'] at hcarried
    have hfb : filledBelow (t.modifyAt f c.path) q nq' = filledBelow t q nq := by
      unfold filledBelow
      rw [hqlen, hqv]
      apply sum_range_congr
      intro j _
      by_cases hjk : j = k
      · subst hjk
        rw [hchildk, hchildk']
        simp [filledOf, hv', hver, hn''size]
      · exact filledOf_of_fields (hchild j hjk)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro id' hid' v' c' h hpath
      by_cases hh : id' = id
      · subst hh
        obtain ⟨h1, -⟩ := hph' v' c' h
        cases h1
      · rw [upd_ne _ _ _ hh] at h
        rw [hqv]
        exact hnodeq.carried_version id' hid' v' c' h hpath
    · rw [hqf, hqsize]; exact hnodeq.not_full
    · rw [hqv]; exact hnodeq.version_le
    · intro h; rw [hqv]; exact hnodeq.version_ge (fun hd => h (hdead'.mpr hd))
    · intro h; exact absurd h hnotleaf
    · intro _ hnd
      obtain ⟨hcb, heq⟩ := hnodeq.live hne (fun hd => hnd (hdead'.mpr hd))
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [hqlen] at hj
        by_cases hjk : j = k
        · subst hjk
          obtain ⟨cc, hcc, h1, h2⟩ := hcb j hj
          rw [hchildk] at hcc
          obtain rfl := Option.some.inj hcc
          exact ⟨n'', hchildk', by omega, by omega⟩
        · obtain ⟨cc, hcc, h1, h2⟩ := hcb j hj
          obtain ⟨cc', hcc', hfe'⟩ := get_of_fields' (hchild j hjk) hcc
          obtain ⟨hv1, -⟩ := Tree.fields_inj hfe'
          exact ⟨cc', hcc', by omega, by omega⟩
      · rw [hqf, hfb]
        omega
    · intro h
      obtain ⟨h1, h2, h3⟩ := hnodeq.dead (hdead'.mp h)
      exact ⟨by rw [hqv, h1], by rw [hqf, h2], by omega⟩

/-- Every node that is neither under the cursor nor its parent. -/
theorem nodeInv_other {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (_hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t)
    {id : Nat} {c : Cursor} (hid : id < cfg.workers) (hph : phase id = .walk V c) (hvc : V < cfg.count)
    {vc : VC} {ord : MemOrd} {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next}
    (hwalk : t.walk cfg c V vc ord = .ok t' vc' rmw next)
    {q : List Nat} (hqp : q ≠ c.path) (hpar : ¬ ∃ k, c.path = q ++ [k])
    {nq' : Tree} (hq' : t'.get q = some nq') :
    NodeInv cfg V (upd phase id (nextPhase cfg V next)) t' q nq' := by
  obtain ⟨n, hn, hver, -, -, -, hle, ⟨f, hf, rfl⟩, -, hfin, hstop, hcont⟩ := walk_spec hwalk
  have hfields := Tree.get_modifyAt_ne f hf t c.path
  have hshape := Tree.get_modifyAt_shape f hf t c.path
  obtain ⟨nq, hq, hfe⟩ := get_of_fields (hfields q hqp) hq'
  obtain ⟨hqv, hqf, hqlo, hqhi, hqlen⟩ := Tree.fields_inj hfe
  have hqsize : nq'.size = nq.size := Tree.size_of_fields hfe
  have hnodeq := hinv.nodes q nq hq
  have hchild : ∀ j, ((t.modifyAt f c.path).get (q ++ [j])).map Tree.fields =
      (t.get (q ++ [j])).map Tree.fields :=
    fun j => hfields _ fun h => hpar ⟨j, h.symm⟩
  have hdead' : deadAt cfg.workers (t.modifyAt f c.path) q nq' ↔ deadAt cfg.workers t q nq :=
    deadAt_of_shape hshape hqlen
  -- the consumer never carries anything to `q`, before or after
  have hnext_ne : ∀ c', next = .continue c' → c'.path ≠ q := by
    intro c' hc' hcq
    obtain ⟨rfl, -, -, hne⟩ := hcont c' hc'
    apply hpar
    rcases List.eq_nil_or_concat c.path with h0 | ⟨q', k', hq'⟩
    · exact absurd h0 hne
    · refine ⟨k', ?_⟩
      rw [hq', List.concat_eq_append] at hcq ⊢
      rw [List.dropLast_concat] at hcq
      dsimp only at hcq
      rw [hcq]
  have hcarry0 : carryOf q (phase id) = 0 := by simp [hph, hqp.symm]
  have hcarry' : carryOf q (nextPhase cfg V next) = 0 := carryOf_nextPhase_ne cfg V next q hnext_ne
  have hcarried := carriedTo_upd cfg.workers q phase id (nextPhase cfg V next) hid
  rw [hcarry0, hcarry'] at hcarried
  have hph' : ∀ v' c', upd phase id (nextPhase cfg V next) id = .walk v' c' → c'.path ≠ q := by
    intro v' c' h
    rw [upd_self] at h
    obtain ⟨h1, -⟩ := nextPhase_walk h
    exact hnext_ne c' h1
  have hfb : filledBelow (t.modifyAt f c.path) q nq' = filledBelow t q nq := by
    unfold filledBelow
    rw [hqlen, hqv]
    apply sum_range_congr
    intro j _
    exact filledOf_of_fields (hchild j)
  -- if `q` is a leaf holding the consumer, its leaf count is unchanged
  have hlD : nq.children = [] → nq.lo ≤ id → id < nq.hi →
      leafDone q cfg.count (phase id) = V + 1 ∧
      leafDone q cfg.count (nextPhase cfg V next) = V + 1 := by
    intro hnil hlo hhi
    have hq_start := hinv.leaf_unique q nq hq hnil id hlo hhi
    have hpre := hinv.walkers id hid V c hph
    rw [← hq_start] at hpre
    have hne : (c.path == q) = false := by
      cases h : c.path == q
      · rfl
      · exact absurd (beq_iff_eq.mp h) hqp.symm
    refine ⟨by simp [hph, hne], leafDone_nextPhase cfg V next q hvc hnext_ne⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id' hid' v' c' h hpath
    by_cases hh : id' = id
    · subst hh; exact absurd hpath (hph' v' c' h)
    · rw [upd_ne _ _ _ hh] at h
      rw [hqv]
      exact hnodeq.carried_version id' hid' v' c' h hpath
  · rw [hqf, hqsize]; exact hnodeq.not_full
  · rw [hqv]; exact hnodeq.version_le
  · intro h; rw [hqv]; exact hnodeq.version_ge (fun hd => h (hdead'.mpr hd))
  · intro hnil
    have hnil0 : nq.children = [] := by
      have := congrArg List.length hnil
      rw [hqlen] at this
      exact List.eq_nil_of_length_eq_zero this
    obtain ⟨hb, hcount, hamt⟩ := hnodeq.leaf hnil0
    refine ⟨?_, ?_, ?_⟩
    · intro j hj1 hj2
      rw [hqlo] at hj1; rw [hqhi] at hj2
      rw [hqv]
      by_cases hh : j = id
      · subst hh
        obtain ⟨h1, h2⟩ := hlD hnil0 hj1 hj2
        rw [upd_self, h2, ← h1]
        exact hb j hj1 hj2
      · rw [upd_ne _ _ _ hh]
        exact hb j hj1 hj2
    · rw [hqf, hqlo, hqhi, hqv, hcount]
      by_cases hin : nq.lo ≤ id ∧ id < nq.hi
      · obtain ⟨h1, h2⟩ := hlD hnil0 hin.1 hin.2
        have hsum := contributedIn_upd cfg.count q nq.lo nq.hi nq.version phase id (nextPhase cfg V next) hin
        have : pastLeaf cfg.count q nq.version (phase id) =
            pastLeaf cfg.count q nq.version (nextPhase cfg V next) := by
          unfold pastLeaf
          rw [h1, h2]
        omega
      · exact (contributedIn_upd_of_not_mem cfg.count q nq.lo nq.hi nq.version phase id
          (nextPhase cfg V next) hin).symm
    · intro id' hid' v' c' h hpath
      by_cases hh : id' = id
      · subst hh; exact absurd hpath (hph' v' c' h)
      · rw [upd_ne _ _ _ hh] at h
        exact hamt id' hid' v' c' h hpath
  · intro hne hnd
    have hne0 : nq.children ≠ [] := by
      intro h
      apply hne
      have := congrArg List.length h
      rw [← hqlen] at this
      exact List.eq_nil_of_length_eq_zero this
    obtain ⟨hcb, heq⟩ := hnodeq.live hne0 (fun hd => hnd (hdead'.mpr hd))
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [hqlen] at hj
      obtain ⟨cc, hcc, h1, h2⟩ := hcb j hj
      obtain ⟨cc', hcc', hfe'⟩ := get_of_fields' (hchild j) hcc
      obtain ⟨hv1, -⟩ := Tree.fields_inj hfe'
      exact ⟨cc', hcc', by omega, by omega⟩
    · rw [hqf, hfb]
      omega
  · intro h
    obtain ⟨h1, h2, h3⟩ := hnodeq.dead (hdead'.mp h)
    exact ⟨by rw [hqv, h1], by rw [hqf, h2], by omega⟩

/-- The consumer's `fetch_add` on a ticket preserves the counting invariant. -/
theorem walk_preserves {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t)
    {id : Nat} {c : Cursor} (hid : id < cfg.workers) (hph : phase id = .walk V c) (hvc : V < cfg.count)
    {vc : VC} {ord : MemOrd} {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next}
    (hwalk : t.walk cfg c V vc ord = .ok t' vc' rmw next) :
    TreeInv cfg V (upd phase id (nextPhase cfg V next)) t' := by
  obtain ⟨n, hn, -, -, -, -, -, ⟨f, hf, rfl⟩, -, -, -, hcont⟩ := walk_spec hwalk
  have hshape := Tree.get_modifyAt_shape f hf t c.path
  have hwfn := Wf.get _ hwf hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q nq' hq'
    by_cases hqp : q = c.path
    · subst hqp
      exact nodeInv_self hwf hinv hid hph hvc hwalk hq'
    · by_cases hpar : ∃ k, c.path = q ++ [k]
      · obtain ⟨k, hk⟩ := hpar
        exact nodeInv_parent hwf hinv hid hph hvc hwalk hk hq'
      · exact nodeInv_other hwf hinv hid hph hvc hwalk hqp hpar hq'
  · intro id' hid' v' c' h
    by_cases hh : id' = id
    · rw [hh] at h ⊢
      rw [upd_self] at h
      obtain ⟨hc', -⟩ := nextPhase_walk h
      obtain ⟨rfl, -, -, -⟩ := hcont c' hc'
      exact (List.dropLast_prefix _).trans (hinv.walkers id hid V c hph)
    · rw [upd_ne _ _ _ hh] at h
      exact hinv.walkers id' hid' v' c' h
  · intro id' hid' v' c' h
    by_cases hh : id' = id
    · rw [hh, upd_self] at h
      obtain ⟨hc', -⟩ := nextPhase_walk h
      obtain ⟨rfl, -, -, -⟩ := hcont c' hc'
      exact hwfn.size_pos
    · rw [upd_ne _ _ _ hh] at h
      exact hinv.carry_pos id' hid' v' c' h
  · intro id' hid'
    obtain ⟨leaf, hleaf, hnil, hlo, hhi⟩ := hinv.leaves id' hid'
    obtain ⟨leaf', hleaf', hsh⟩ := get_of_shape' (hshape _) hleaf
    obtain ⟨h1, h2, h3⟩ := Tree.shape_inj hsh
    refine ⟨leaf', hleaf', ?_, by omega, by omega⟩
    rw [hnil] at h3
    exact List.eq_nil_of_length_eq_zero h3
  · intro q leaf' hq' hnil' id' hlo' hhi'
    obtain ⟨leaf, hq, hsh⟩ := get_of_shape (hshape q) hq'
    obtain ⟨h1, h2, h3⟩ := Tree.shape_inj hsh
    rw [hnil'] at h3
    exact hinv.leaf_unique q leaf hq (List.eq_nil_of_length_eq_zero h3.symm) id' (by omega) (by omega)

/-! ## The other consumer steps -/

/-- A change of one consumer's phase that does not touch the tree and leaves
what the consumer contributes anywhere unchanged (no walk starts or moves)
preserves the invariant. This covers `start → initializing → waitReady 0`,
`waitReady v → beforeFunc v → inFunc v` and `finish v → waitReady (v + 1) / done`. -/
theorem phase_preserves {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hinv : TreeInv cfg V phase t) {id : Nat} (hid : id < cfg.workers) {ph' : ConsumerPhase}
    (hleaf : ∀ q, leafDone q cfg.count ph' = leafDone q cfg.count (phase id))
    (hcarry : ∀ q, carryOf q ph' = carryOf q (phase id))
    (hwalk : ∀ v c, ph' = .walk v c → phase id = .walk v c) :
    TreeInv cfg V (upd phase id ph') t := by
  have hcarried : ∀ q, carriedTo cfg.workers q (upd phase id ph') = carriedTo cfg.workers q phase := by
    intro q
    have := carriedTo_upd cfg.workers q phase id ph' hid
    rw [hcarry q] at this
    omega
  have hwalk' : ∀ id' v c, id' < cfg.workers → upd phase id ph' id' = .walk v c → phase id' = .walk v c := by
    intro id' v c _ h
    by_cases hh : id' = id
    · rw [hh] at h ⊢; rw [upd_self] at h; exact hwalk v c h
    · rw [upd_ne _ _ _ hh] at h; exact h
  refine ⟨?_, ?_, ?_, hinv.leaves, hinv.leaf_unique⟩
  · intro q n hq
    have hnode := hinv.nodes q n hq
    refine ⟨?_, hnode.not_full, hnode.version_le, hnode.version_ge, ?_, ?_, ?_⟩
    · intro id' hid' v c h hpath
      exact hnode.carried_version id' hid' v c (hwalk' id' v c hid' h) hpath
    · intro hnil
      obtain ⟨hb, hcount, hamt⟩ := hnode.leaf hnil
      refine ⟨?_, ?_, ?_⟩
      · intro j hj1 hj2
        by_cases hh : j = id
        · rw [hh, upd_self, hleaf q]; exact hb id (hh ▸ hj1) (hh ▸ hj2)
        · rw [upd_ne _ _ _ hh]; exact hb j hj1 hj2
      · rw [hcount]
        by_cases hin : n.lo ≤ id ∧ id < n.hi
        · have hsum := contributedIn_upd cfg.count q n.lo n.hi n.version phase id ph' hin
          have : pastLeaf cfg.count q n.version (phase id) = pastLeaf cfg.count q n.version ph' := by
            unfold pastLeaf
            rw [hleaf q]
          omega
        · exact (contributedIn_upd_of_not_mem cfg.count q n.lo n.hi n.version phase id ph' hin).symm
      · intro id' hid' v c h hpath
        exact hamt id' hid' v c (hwalk' id' v c hid' h) hpath
    · intro hne hnd
      obtain ⟨hcb, heq⟩ := hnode.live hne hnd
      exact ⟨hcb, by rw [hcarried]; exact heq⟩
    · intro hd
      obtain ⟨h1, h2, h3⟩ := hnode.dead hd
      exact ⟨h1, h2, by rw [hcarried]; exact h3⟩
  · intro id' hid' v c h
    exact hinv.walkers id' hid' v c (hwalk' id' v c hid' h)
  · intro id' hid' v c h
    exact hinv.carry_pos id' hid' v c (hwalk' id' v c hid' h)

/-- A leaf is never dead. -/
theorem not_deadAt_of_leaf {W : Nat} {t : Tree} {q : List Nat} {n : Tree} (hnil : n.children = []) :
    ¬ deadAt W t q n := by
  rintro ⟨k, hk, -⟩
  rw [hnil] at hk
  simp at hk

/-- The consumer that finished `func` starts walking at its leaf, adding `1`. -/
theorem startWalk_preserves {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hinv : TreeInv cfg V phase t) {id : Nat} (hid : id < cfg.workers)
    (hph : phase id = .inFunc V) :
    TreeInv cfg V (upd phase id (.walk V (Cursor.start cfg id))) t := by
  obtain ⟨leaf, hleaf, hnil, hlo, hhi⟩ := hinv.leaves id hid
  have hnode := hinv.nodes _ leaf hleaf
  obtain ⟨hb, hcount, hamt⟩ := hnode.leaf hnil
  -- the leaf counts the consumer's version
  have hlv : leaf.version = V := by
    have h1 := hb id hlo hhi
    rw [hph] at h1
    simp only [leafDone] at h1
    have h2 := hnode.version_ge (not_deadAt_of_leaf hnil)
    omega
  have hstart : (Cursor.start cfg id).mergeAmount = 1 := rfl
  have hcarry0 : ∀ q, carryOf q (phase id) = 0 := by intro q; simp [hph, carryOf]
  have hcarried : ∀ q, q ≠ (Cursor.start cfg id).path →
      carriedTo cfg.workers q (upd phase id (.walk V (Cursor.start cfg id))) =
        carriedTo cfg.workers q phase := by
    intro q hq
    have := carriedTo_upd cfg.workers q phase id (.walk V (Cursor.start cfg id)) hid
    rw [hcarry0, carryOf_walk, if_neg (Ne.symm hq)] at this
    omega
  have hwalk' : ∀ id' v c, id' < cfg.workers → upd phase id (.walk V (Cursor.start cfg id)) id' = .walk v c →
      phase id' = .walk v c ∨ (id' = id ∧ v = V ∧ c = Cursor.start cfg id) := by
    intro id' v c _ h
    by_cases hh : id' = id
    · rw [hh, upd_self] at h
      simp only [ConsumerPhase.walk.injEq] at h
      exact Or.inr ⟨hh, h.1.symm, h.2.symm⟩
    · rw [upd_ne _ _ _ hh] at h; exact Or.inl h
  refine ⟨?_, ?_, ?_, hinv.leaves, hinv.leaf_unique⟩
  · intro q n hq
    have hnodeq := hinv.nodes q n hq
    by_cases hqs : q = (Cursor.start cfg id).path
    · -- the consumer's own leaf
      subst hqs
      rw [hleaf] at hq
      obtain rfl := Option.some.inj hq
      refine ⟨?_, hnode.not_full, hnode.version_le, hnode.version_ge, ?_, ?_, ?_⟩
      · intro id' hid' v c h hpath
        rcases hwalk' id' v c hid' h with h | ⟨-, rfl, -⟩
        · exact hnode.carried_version id' hid' v c h hpath
        · exact hlv.symm
      · intro _
        refine ⟨?_, ?_, ?_⟩
        · intro j hj1 hj2
          by_cases hh : j = id
          · rw [hh, upd_self]
            simp only [leafDone, beq_self_eq_true, ↓reduceIte]
            omega
          · rw [upd_ne _ _ _ hh]; exact hb j hj1 hj2
        · rw [hcount]
          have hsum := contributedIn_upd cfg.count (Cursor.start cfg id).path leaf.lo leaf.hi
            leaf.version phase id (.walk V (Cursor.start cfg id)) ⟨hlo, hhi⟩
          have : pastLeaf cfg.count (Cursor.start cfg id).path leaf.version (phase id) =
              pastLeaf cfg.count (Cursor.start cfg id).path leaf.version (.walk V (Cursor.start cfg id)) := by
            simp [pastLeaf, hph, leafDone]
          omega
        · intro id' hid' v c h hpath
          rcases hwalk' id' v c hid' h with h | ⟨-, -, rfl⟩
          · exact hamt id' hid' v c h hpath
          · rfl
      · intro hne; exact absurd hnil hne
      · intro hd; exact absurd hd (not_deadAt_of_leaf hnil)
    · -- any other node: the consumer contributes nothing to it, before or after
      have hcq : carryOf q (.walk V (Cursor.start cfg id)) = 0 := by simp [Ne.symm hqs]
      refine ⟨?_, hnodeq.not_full, hnodeq.version_le, hnodeq.version_ge, ?_, ?_, ?_⟩
      · intro id' hid' v c h hpath
        rcases hwalk' id' v c hid' h with h | ⟨-, -, rfl⟩
        · exact hnodeq.carried_version id' hid' v c h hpath
        · exact absurd hpath (Ne.symm hqs)
      · intro hnil'
        obtain ⟨hb', hcount', hamt'⟩ := hnodeq.leaf hnil'
        have hnotin : ¬ (n.lo ≤ id ∧ id < n.hi) := by
          intro hin
          exact hqs (hinv.leaf_unique q n hq hnil' id hin.1 hin.2)
        refine ⟨?_, ?_, ?_⟩
        · intro j hj1 hj2
          have hh : j ≠ id := fun e => hnotin ⟨e ▸ hj1, e ▸ hj2⟩
          rw [upd_ne _ _ _ hh]; exact hb' j hj1 hj2
        · rw [hcount']
          exact (contributedIn_upd_of_not_mem cfg.count q n.lo n.hi n.version phase id _ hnotin).symm
        · intro id' hid' v c h hpath
          rcases hwalk' id' v c hid' h with h | ⟨-, -, rfl⟩
          · exact hamt' id' hid' v c h hpath
          · exact absurd hpath (Ne.symm hqs)
      · intro hne hnd
        obtain ⟨hcb, heq⟩ := hnodeq.live hne hnd
        exact ⟨hcb, by rw [hcarried q hqs]; exact heq⟩
      · intro hd
        obtain ⟨h1, h2, h3⟩ := hnodeq.dead hd
        exact ⟨h1, h2, by rw [hcarried q hqs]; exact h3⟩
  · intro id' hid' v c h
    rcases hwalk' id' v c hid' h with h | ⟨rfl, -, rfl⟩
    · exact hinv.walkers id' hid' v c h
    · exact List.prefix_refl _
  · intro id' hid' v c h
    rcases hwalk' id' v c hid' h with h | ⟨-, -, rfl⟩
    · exact hinv.carry_pos id' hid' v c h
    · exact Nat.one_pos

/-! ## Advancing the version -/

theorem sizeOf_child_lt {n c : Tree} (h : c ∈ n.children) : sizeOf c < sizeOf n := by
  have := List.sizeOf_lt_of_mem h
  cases n
  simp only [Tree.children] at this
  simp
  omega

/-- A child of a well-formed node is no bigger than the node. -/
theorem child_size_le {C W : Nat} {t : Tree} {q : List Nat} {n c : Tree} (hwf : Wf C W t)
    (hn : t.get q = some n) {k : Nat} (hc : t.get (q ++ [k]) = some c) : c.size ≤ n.size := by
  have hne := Tree.children_ne_nil_of_get hn hc
  rw [← (Wf.get q hwf hn).sum_children' hne]
  rw [get_child hn] at hc
  exact le_sum_of_mem' _ _ (List.mem_map_of_mem (Wf.get.mem_of_getElem?' _ _ _ hc))

/-- A child of a live node is live. -/
theorem live_child {C W : Nat} {t : Tree} {q : List Nat} {n c : Tree} (hwf : Wf C W t)
    (hn : t.get q = some n) {k : Nat} (hk : k < n.children.length) (hc : t.get (q ++ [k]) = some c)
    (hnd : ¬ deadAt W t q n) : ¬ deadAt W t (q ++ [k]) c := by
  rintro ⟨j, hj, g, hg, hgs⟩
  apply hnd
  refine ⟨k, hk, c, hc, ?_⟩
  have h1 := child_size_le hwf hc hg
  have h2 := (Wf.get _ hwf hc).size_le
  omega

theorem sum_map_const_one {α : Type} (l : List α) (g : α → Nat) (h : ∀ x ∈ l, g x = 1) :
    (l.map g).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h a (by simp), ih fun x hx => h x (by simp [hx])]
    omega

/-- Once every consumer has finished version `V`, every live node counts `V + 1`. -/
theorem all_advanced {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t)
    (hall : ∀ id, id < cfg.workers →
      phase id = .waitReady (V + 1) ∨ (phase id = .done ∧ cfg.count = V + 1)) :
    ∀ (m : Nat) (q : List Nat) (n : Tree), sizeOf n = m → t.get q = some n →
      ¬ deadAt cfg.workers t q n → n.version = V + 1 := by
  have hld : ∀ q id, id < cfg.workers → leafDone q cfg.count (phase id) = V + 1 := by
    intro q id hid
    rcases hall id hid with h | ⟨h, hc⟩
    · rw [h]; rfl
    · rw [h]; simp [leafDone, hc]
  have hcarry : ∀ q, carriedTo cfg.workers q phase = 0 := by
    intro q
    unfold carriedTo
    apply sum_map_eq_zero
    intro id hid
    simp only [List.mem_range] at hid
    rcases hall id hid with h | ⟨h, -⟩ <;> simp [h]
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro q n hm hq hnd
    subst hm
    have hnode := hinv.nodes q n hq
    have hwfn := Wf.get q hwf hq
    by_cases hnil : n.children = []
    · obtain ⟨hb, hcount, -⟩ := hnode.leaf hnil
      have hlt := hwfn.lo_lt_hi
      have hb' := hb n.lo (Nat.le_refl _) hlt
      rw [hld q n.lo (by have := hwfn.hi_le; omega)] at hb'
      by_cases hv : n.version = V + 1
      · exact hv
      · exfalso
        have hvV : n.version = V := by omega
        have hfull : contributedIn cfg.count q n.lo n.hi n.version phase = n.hi - n.lo := by
          unfold contributedIn
          have := sum_map_const_one (List.range' n.lo (n.hi - n.lo))
            (fun j => pastLeaf cfg.count q n.version (phase j)) (by
              intro j hj
              simp only [List.mem_range'_1] at hj
              have := hwfn.hi_le
              simp [pastLeaf, hld q j (by omega), hvV])
          rw [List.length_range'] at this
          exact this
        have := hnode.not_full
        simp only [Tree.size] at this
        omega
    · obtain ⟨hcb, heq⟩ := hnode.live hnil hnd
      have hchildren : ∀ k, k < n.children.length → ∃ c, t.get (q ++ [k]) = some c ∧ c.version = V + 1 := by
        intro k hk
        obtain ⟨c, hc, -, -⟩ := hcb k hk
        refine ⟨c, hc, ?_⟩
        have hmem : c ∈ n.children := by
          rw [get_child hq] at hc
          exact Wf.get.mem_of_getElem?' _ _ _ hc
        exact ih (sizeOf c) (sizeOf_child_lt hmem) (q ++ [k]) c rfl hc (live_child hwf hq hk hc hnd)
      by_cases hv : n.version = V + 1
      · exact hv
      · exfalso
        have hvV : n.version = V := by have := hnode.version_le; have := hnode.version_ge hnd; omega
        have hfb : filledBelow t q n = n.size := by
          rw [filledBelow_eq hq, ← hwfn.sum_children' hnil]
          apply congrArg
          apply List.map_congr_left
          intro c hc
          obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
          have hk' : k < n.children.length := lt_length_of_getElem?' _ _ _ hk
          obtain ⟨c', hc', hcv⟩ := hchildren k hk'
          rw [get_child hq, hk] at hc'
          obtain rfl := Option.some.inj hc'
          simp [filledOf, hcv, hvV]
        have := hnode.not_full
        rw [hcarry q] at heq
        omega

/-- The producer moving on to the next version: once every consumer has
finished version `V`, the invariant holds for `V + 1`. -/
theorem advance_preserves {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t)
    (hall : ∀ id, id < cfg.workers →
      phase id = .waitReady (V + 1) ∨ (phase id = .done ∧ cfg.count = V + 1)) :
    TreeInv cfg (V + 1) phase t := by
  refine ⟨?_, hinv.walkers, hinv.carry_pos, hinv.leaves, hinv.leaf_unique⟩
  intro q n hq
  have hnode := hinv.nodes q n hq
  refine ⟨hnode.carried_version, hnode.not_full, ?_, ?_, hnode.leaf, hnode.live, hnode.dead⟩
  · have := hnode.version_le; omega
  · intro hnd
    have := all_advanced hwf hinv hall (sizeOf n) q n rfl hq hnd
    omega

end RearmBarrier
