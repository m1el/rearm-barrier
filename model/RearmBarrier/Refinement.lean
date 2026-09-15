import RearmBarrier.WalkInv
import RearmBarrier.TreeInit
import RearmBarrier.Completion

/-!
# The model refines the completion game

`RearmBarrier.Completion` proves the completion tree's properties for an
abstract game with three rules. This file maps the model's state onto that
game and shows every step of the model is a run of the game:

* `absNode` abstracts a `Tree` at the producer's version `V`: a node at
  `V + 1` has filled (`finished = size`), a node at `V` shows its counter, a
  dead node nothing; a crate leaf's children are its consumers, each
  finished once past its leaf `fetch_add`; a filled node is `pending` while
  the walker that filled it is still carrying it (or, for the node covering
  every worker, forever — the crate stops there);
* a walker's `fetch_add` is one or two steps of the game (`refine_walk`):
  `finish` and `apply` of the consumer for a leaf `fetch_add`, `apply` of the
  child the walker came through (`WalkInv`) for an inner one;
* every other step of the model leaves the abstract tree alone, except the
  producer moving to the next version, which resets it to a `Fresh` tree
  (`refine_step`).

Hence `Completion.Inv` holds of the abstract tree in every reachable state
(`reachable_absInv`), and the game's theorems apply to the model. Clocks are
not refined (every abstract clock is `0`).
-/

namespace RearmBarrier

open Completion

def zeroClock : Clock := fun _ => 0

theorem zeroClock_join : zeroClock.join zeroClock = zeroClock := by
  funext i; simp [Clock.join, zeroClock]

/-- The abstract counter of consumer `id` (whose leaf is at `leaf`): one once
past its leaf `fetch_add` for version `V`. -/
def consumerDone (count V : Nat) (leaf : List Nat) (ph : ConsumerPhase) : Nat :=
  if V + 1 ≤ leafDone leaf count ph then 1 else 0

def consumerNode (count V : Nat) (leaf : List Nat) (ph : ConsumerPhase) : Node :=
  .mk (consumerDone count V leaf ph) false zeroClock []

/-- Some walker at `p.dropLast` came up through `p` and still carries it. -/
def carriedFrom (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) : Bool :=
  !p.isEmpty && (List.range cfg.workers).any fun id =>
    match phase id with
    | .walk v c => v == V && c.path == p.dropLast && p.isPrefixOf (Cursor.start cfg id).path
    | _ => false

/-- A filled node not yet applied to its parent. -/
def pendingAt (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) (ver size : Nat) :
    Bool :=
  ver == V + 1 && (size == cfg.workers || carriedFrom cfg V phase p)

/-- The abstract counter of a node at version `ver` with counter `f`. -/
def absFinished (V ver f size : Nat) : Nat :=
  if ver = V + 1 then size else if ver = V then f else 0

mutual
def absNode (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) : Tree → Node
  | .mk ver f _ lo hi cs =>
    .mk (absFinished V ver f (hi - lo)) (pendingAt cfg V phase p ver (hi - lo)) zeroClock
      (absKids cfg V phase p lo hi cs)

/-- The abstract children: the consumers of a leaf, or the abstract children. -/
def absKids (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) (lo hi : Nat) :
    List Tree → List Node
  | [] => (List.range' lo (hi - lo)).map fun id => consumerNode cfg.count V p (phase id)
  | c :: cs => absChildren cfg V phase p 0 (c :: cs)

def absChildren (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) (k : Nat) :
    List Tree → List Node
  | [] => []
  | c :: cs => absNode cfg V phase (p ++ [k]) c :: absChildren cfg V phase p (k + 1) cs
end

/-- The abstract tree of a state. -/
def absState (cfg : Config) (s : State) : Node :=
  absNode cfg (s.producer.version cfg) (phaseOf s.consumers) [] s.tree

/-! ## Structure of the abstraction -/

theorem absNode_mk (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat)
    (ver f : Nat) (r : VC) (lo hi : Nat) (cs : List Tree) :
    absNode cfg V phase p (.mk ver f r lo hi cs) =
      .mk (absFinished V ver f (hi - lo)) (pendingAt cfg V phase p ver (hi - lo)) zeroClock
        (absKids cfg V phase p lo hi cs) := by
  rw [absNode]

theorem absKids_of_ne_nil (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat)
    (lo hi : Nat) {cs : List Tree} (h : cs ≠ []) :
    absKids cfg V phase p lo hi cs = absChildren cfg V phase p 0 cs := by
  cases cs with
  | nil => exact absurd rfl h
  | cons c cs => rw [absKids]

theorem absChildren_getElem? (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) :
    ∀ (k j : Nat) (cs : List Tree),
      (absChildren cfg V phase p k cs)[j]? = cs[j]?.map (absNode cfg V phase (p ++ [k + j]))
  | _, _, [] => by simp [absChildren]
  | k, 0, c :: cs => by simp [absChildren]
  | k, j + 1, c :: cs => by
    rw [absChildren]
    simp only [List.getElem?_cons_succ]
    rw [absChildren_getElem? cfg V phase p (k + 1) j cs]
    have e : k + 1 + j = k + (j + 1) := by omega
    rw [e]

theorem absChildren_length (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) :
    ∀ (k : Nat) (cs : List Tree), (absChildren cfg V phase p k cs).length = cs.length
  | _, [] => by simp [absChildren]
  | k, c :: cs => by rw [absChildren]; simp [absChildren_length cfg V phase p (k + 1) cs]

theorem absChildren_set (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) :
    ∀ (k j : Nat) (cs : List Tree) (c : Tree),
      absChildren cfg V phase p k (cs.set j c) =
        (absChildren cfg V phase p k cs).set j (absNode cfg V phase (p ++ [k + j]) c)
  | _, _, [], _ => by simp [absChildren]
  | k, 0, x :: cs, c => by simp [absChildren]
  | k, j + 1, x :: cs, c => by
    simp only [List.set_cons_succ]
    rw [absChildren, absChildren, absChildren_set cfg V phase p (k + 1) j cs c]
    have e : k + 1 + j = k + (j + 1) := by omega
    rw [e]
    rfl

/-! ### Sizes -/

theorem sizes_map_consumer (count V : Nat) (p : List Nat) (phase : Nat → ConsumerPhase) :
    ∀ (l : List Nat), sizes (l.map fun id => consumerNode count V p (phase id)) = l.length
  | [] => rfl
  | id :: l => by
    rw [List.map_cons, sizes_cons, sizes_map_consumer count V p phase l]
    simp only [consumerNode, Node.size_nil, List.length_cons]
    omega

theorem Node.size_of_children (f : Nat) (p : Bool) (c : Clock) (cs : List Node) (hne : cs ≠ []) :
    (Node.mk f p c cs).size = sizes cs := Node.size_of_ne_nil f p c cs hne

theorem sizes_absChildren (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) :
    ∀ (k : Nat) (cs : List Tree), (∀ c ∈ cs, ∀ q, (absNode cfg V phase q c).size = c.size) →
      sizes (absChildren cfg V phase p k cs) = (cs.map Tree.size).sum
  | _, [], _ => by simp [absChildren, sizes]
  | k, c :: cs, h => by
    rw [absChildren, sizes_cons, List.map_cons, List.sum_cons, h c (by simp),
      sizes_absChildren cfg V phase p (k + 1) cs fun x hx q => h x (by simp [hx]) q]

/-- The abstraction preserves sizes. -/
theorem absNode_size (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) :
    ∀ (m : Nat) (n : Tree), sizeOf n = m → Wf cfg.cluster cfg.workers n → ∀ q,
      (absNode cfg V phase q n).size = n.size := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro n hm hwf q
    subst hm
    cases n with
    | mk ver f r lo hi cs =>
      rw [absNode_mk]
      cases cs with
      | nil =>
        rw [absKids]
        have hlt := hwf.lo_lt_hi
        simp only [Tree.lo_mk, Tree.hi_mk] at hlt
        have hne : ((List.range' lo (hi - lo)).map fun id => consumerNode cfg.count V q (phase id)) ≠ [] := by
          intro h
          have := congrArg List.length h
          simp at this
          omega
        rw [Node.size_of_children _ _ _ _ hne, sizes_map_consumer]
        simp [Tree.size]
      | cons c cs =>
        rw [absKids]
        have hne : absChildren cfg V phase q 0 (c :: cs) ≠ [] := by rw [absChildren]; simp
        rw [Node.size_of_children _ _ _ _ hne, sizes_absChildren, Tree.size_mk]
        · exact hwf.sum_children (by simp)
        · intro x hx q'
          exact ih (sizeOf x) (sizeOf_child_lt (n := Tree.mk ver f r lo hi (c :: cs)) hx) x rfl
            (hwf.children_wf x hx) q'

/-! ## Congruence: what the abstraction looks at -/

/-- `phase` and `phase'` agree on everything the abstraction of the subtree
`n` at `p` looks at: the pending flags below `p` and the consumers of the
leaves below `p`. -/
def Agree (cfg : Config) (V : Nat) (phase phase' : Nat → ConsumerPhase) (p : List Nat) (n : Tree) :
    Prop :=
  ∀ r m, n.get r = some m →
    pendingAt cfg V phase (p ++ r) m.version m.size = pendingAt cfg V phase' (p ++ r) m.version m.size ∧
    (m.children = [] → ∀ id, m.lo ≤ id → id < m.hi →
      consumerDone cfg.count V (p ++ r) (phase id) = consumerDone cfg.count V (p ++ r) (phase' id))

theorem Agree.child {cfg : Config} {V : Nat} {phase phase' : Nat → ConsumerPhase} {p : List Nat}
    {n : Tree} (h : Agree cfg V phase phase' p n) {k : Nat} {c : Tree} (hc : n.children[k]? = some c) :
    Agree cfg V phase phase' (p ++ [k]) c := by
  intro r m hm
  have := h (k :: r) m (by simp only [Tree.get, hc]; exact hm)
  rw [← List.append_cons]
  exact this

theorem absChildren_congr (cfg : Config) (V : Nat) (phase phase' : Nat → ConsumerPhase) (p : List Nat) :
    ∀ (k : Nat) (cs : List Tree),
      (∀ j c, cs[j]? = some c →
        absNode cfg V phase (p ++ [k + j]) c = absNode cfg V phase' (p ++ [k + j]) c) →
      absChildren cfg V phase p k cs = absChildren cfg V phase' p k cs
  | _, [], _ => by rw [absChildren, absChildren]
  | k, c :: cs, h => by
    rw [absChildren, absChildren]
    have h0 := h 0 c rfl
    simp only [Nat.add_zero] at h0
    rw [h0, absChildren_congr cfg V phase phase' p (k + 1) cs]
    intro j c' hj
    have := h (j + 1) c' (by simpa using hj)
    have e : k + (j + 1) = k + 1 + j := by omega
    rw [e] at this
    exact this

theorem absNode_congr (cfg : Config) (V : Nat) (phase phase' : Nat → ConsumerPhase) :
    ∀ (m : Nat) (n : Tree), sizeOf n = m → ∀ p, Agree cfg V phase phase' p n →
      absNode cfg V phase p n = absNode cfg V phase' p n := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro n hm p h
    subst hm
    cases n with
    | mk ver f r lo hi cs =>
      obtain ⟨hpend, hleaf⟩ := h [] _ rfl
      simp only [Tree.version_mk, Tree.size_mk, Tree.children_mk, Tree.lo_mk, Tree.hi_mk,
        List.append_nil] at hpend hleaf
      rw [absNode_mk, absNode_mk, hpend]
      congr 1
      cases cs with
      | nil =>
        rw [absKids, absKids]
        apply List.map_congr_left
        intro id hid
        simp only [List.mem_range'_1] at hid
        unfold consumerNode
        rw [hleaf rfl id (by omega) (by omega)]
      | cons c cs =>
        rw [absKids, absKids]
        apply absChildren_congr
        intro j c' hj
        simp only [Nat.zero_add]
        exact ih (sizeOf c') (sizeOf_child_lt (n := Tree.mk ver f r lo hi (c :: cs))
          (Wf.get.mem_of_getElem?' _ _ _ hj)) c' rfl (p ++ [j]) (h.child hj)

/-! ## Steps inside a child -/

theorem set_of_getElem? : ∀ (cs : List Node) (k : Nat) (ch : Node), cs[k]? = some ch → cs.set k ch = cs
  | [], _, _, h => by simp at h
  | c :: cs, 0, ch, h => by simp at h; simp [h]
  | c :: cs, k + 1, ch, h => by simp at h; simp [set_of_getElem? cs k ch h]

theorem Steps.inner_lift (f : Nat) (p : Bool) (c : Clock) (cs : List Node) (k : Nat) {ch ch' : Node}
    (hk : cs[k]? = some ch) (h : Steps ch ch') : Steps (.mk f p c cs) (.mk f p c (cs.set k ch')) := by
  induction h with
  | refl => rw [set_of_getElem? cs k ch hk]; exact .refl _
  | tail _ hs ih =>
    have := Step.inner f p c (cs.set k _) k _ _
      (List.getElem?_set_self (List.getElem?_eq_some_iff.mp hk).1) hs
    rw [List.set_set] at this
    exact .tail ih this

/-! ## What one walk changes -/

theorem carriedFrom_iff (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (x : List Nat) :
    carriedFrom cfg V phase x = true ↔
      x ≠ [] ∧ ∃ id, id < cfg.workers ∧ ∃ c, phase id = .walk V c ∧ c.path = x.dropLast ∧
        x <+: (Cursor.start cfg id).path := by
  unfold carriedFrom
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff,
    List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨h1, id, hid, h2⟩
    refine ⟨h1, id, hid, ?_⟩
    cases hph : phase id <;> rw [hph] at h2 <;> simp at h2
    rename_i v c
    obtain ⟨⟨rfl, h3⟩, h4⟩ := h2
    exact ⟨c, rfl, h3, h4⟩
  · rintro ⟨h1, id, hid, c, hc, h3, h4⟩
    refine ⟨h1, id, hid, ?_⟩
    rw [hc]
    simp [h3, h4]

theorem carriedFrom_false {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {x : List Nat}
    (h : ¬ (x ≠ [] ∧ ∃ id, id < cfg.workers ∧ ∃ c, phase id = .walk V c ∧ c.path = x.dropLast ∧
        x <+: (Cursor.start cfg id).path)) : carriedFrom cfg V phase x = false := by
  cases hc : carriedFrom cfg V phase x
  · rfl
  · exact absurd ((carriedFrom_iff cfg V phase x).mp hc) h

/-- Two non-empty prefixes of the same list with the same `dropLast` are equal. -/
theorem eq_of_dropLast_eq_of_prefix {x y l : List Nat} (hx : x ≠ []) (hy : y ≠ [])
    (hd : x.dropLast = y.dropLast) (hxl : x <+: l) (hyl : y <+: l) : x = y := by
  have hlen : x.length = y.length := by
    have h1 := congrArg List.length hd
    simp only [List.length_dropLast] at h1
    have : 0 < x.length := by cases x with | nil => exact absurd rfl hx | cons _ _ => simp
    have : 0 < y.length := by cases y with | nil => exact absurd rfl hy | cons _ _ => simp
    omega
  exact (List.prefix_of_prefix_length_le hxl hyl (by omega)).eq_of_length hlen

/-- Where a walk continues to. -/
theorem walk_cont {cfg : Config} {t : Tree} {c : Cursor} {v : Nat} {vc : VC} {ord : MemOrd}
    {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next} (h : t.walk cfg c v vc ord = .ok t' vc' rmw next) :
    ∀ c', next = .continue c' → c'.path = c.path.dropLast ∧ c.path ≠ [] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcont⟩ := walk_spec h
  intro c' hc'
  obtain ⟨rfl, -, -, hnil⟩ := hcont c' hc'
  exact ⟨rfl, hnil⟩

/-- The facts about a walk of consumer `id` at cursor `c` that the
abstraction needs. -/
structure WalkFacts (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (id : Nat) (c : Cursor)
    (next : Next) : Prop where
  hid : id < cfg.workers
  hph : phase id = .walk V c
  hpre : c.path <+: (Cursor.start cfg id).path
  hcont : ∀ c', next = .continue c' → c'.path = c.path.dropLast ∧ c.path ≠ []
  hv : V < cfg.count

/-- Where the walker is afterwards, if it is still walking. -/
theorem WalkFacts.after {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {id : Nat} {c : Cursor}
    {next : Next} (w : WalkFacts cfg V phase id c next) {c' : Cursor}
    (h : nextPhase cfg V next = .walk V c') : c'.path = c.path.dropLast ∧ c.path ≠ [] := by
  obtain ⟨rfl, -⟩ := nextPhase_walk h
  exact w.hcont c' rfl

/-- A walk changes `carriedFrom` only at the node it fills (which becomes
carried) and at the child it came through (which stops being carried). -/
theorem carriedFrom_walk {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {id : Nat} {c : Cursor}
    {next : Next} (w : WalkFacts cfg V phase id c next) (x : List Nat) (hx1 : x ≠ c.path)
    (hx2 : x.dropLast = c.path → ¬ x <+: (Cursor.start cfg id).path) :
    carriedFrom cfg V (upd phase id (nextPhase cfg V next)) x = carriedFrom cfg V phase x := by
  apply Bool.eq_iff_iff.mpr
  rw [carriedFrom_iff, carriedFrom_iff]
  constructor
  · rintro ⟨hx0, id', hid', c', hc', hp, hpx⟩
    refine ⟨hx0, id', hid', ?_⟩
    by_cases h : id' = id
    · subst h
      rw [upd_self] at hc'
      exfalso
      obtain ⟨hp', hnil⟩ := w.after hc'
      apply hx1
      exact eq_of_dropLast_eq_of_prefix hx0 hnil (by rw [← hp, hp']) hpx w.hpre
    · rw [upd_ne _ _ _ h] at hc'
      exact ⟨c', hc', hp, hpx⟩
  · rintro ⟨hx0, id', hid', c', hc', hp, hpx⟩
    refine ⟨hx0, id', hid', ?_⟩
    by_cases h : id' = id
    · subst h
      rw [w.hph] at hc'
      exfalso
      injection hc' with _ hc'
      subst hc'
      exact hx2 hp.symm hpx
    · rw [upd_ne _ _ _ h]
      exact ⟨c', hc', hp, hpx⟩

theorem pendingAt_walk {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {id : Nat} {c : Cursor}
    {next : Next} (w : WalkFacts cfg V phase id c next) (x : List Nat) (hx1 : x ≠ c.path)
    (hx2 : x.dropLast = c.path → ¬ x <+: (Cursor.start cfg id).path) (ver size : Nat) :
    pendingAt cfg V (upd phase id (nextPhase cfg V next)) x ver size = pendingAt cfg V phase x ver size := by
  unfold pendingAt
  rw [carriedFrom_walk w x hx1 hx2]

/-- A walk changes no consumer's counter except at the walker's own leaf,
when the walk is its leaf `fetch_add`. -/
theorem consumerDone_walk {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {id : Nat} {c : Cursor}
    {next : Next} (w : WalkFacts cfg V phase id c next) (x : List Nat) (hx : ¬ x <+: c.path) (id' : Nat) :
    consumerDone cfg.count V x (upd phase id (nextPhase cfg V next) id') =
      consumerDone cfg.count V x (phase id') := by
  by_cases h : id' = id
  · subst h
    rw [upd_self, w.hph]
    have hne : c.path ≠ x := fun e => hx (e ▸ List.prefix_refl _)
    have h1 : leafDone x cfg.count (.walk V c) = V + 1 := by
      simp [leafDone, hne]
    have h2 : leafDone x cfg.count (nextPhase cfg V next) = V + 1 := by
      apply leafDone_nextPhase cfg V next x w.hv
      intro c' hc' e
      obtain ⟨hp, -⟩ := w.hcont c' hc'
      rw [← e, hp] at hx
      exact hx (List.dropLast_prefix _)
    unfold consumerDone
    rw [h1, h2]
  · rw [upd_ne _ _ _ h]

/-- Paths that diverge from `q` at the position of `p`. -/
theorem not_prefix_of_ne_digit {p : List Nat} {j k : Nat} {r r' : List Nat} (h : j ≠ k) :
    ¬ (p ++ j :: r) <+: (p ++ k :: r') := by
  intro hp
  rw [List.prefix_append_right_inj, List.cons_prefix_cons] at hp
  exact h hp.1

theorem ne_of_ne_digit {p : List Nat} {j k : Nat} {r r' : List Nat} (h : j ≠ k) :
    p ++ j :: r ≠ p ++ k :: r' := by
  intro e
  have := List.append_cancel_left e
  simp at this
  exact h this.1

/-- The abstraction of a subtree the walk does not touch is unchanged. -/
theorem agree_walk {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {id : Nat} {c : Cursor}
    {next : Next} (w : WalkFacts cfg V phase id c next) (p' : List Nat) (n : Tree)
    (h : ∀ r, p' ++ r ≠ c.path ∧ ((p' ++ r).dropLast = c.path → ¬ (p' ++ r) <+: (Cursor.start cfg id).path) ∧
      ¬ (p' ++ r) <+: c.path) :
    Agree cfg V phase (upd phase id (nextPhase cfg V next)) p' n := by
  intro r m _
  obtain ⟨h1, h2, h3⟩ := h r
  exact ⟨(pendingAt_walk w _ h1 h2 _ _).symm, fun _ id' _ _ => (consumerDone_walk w _ h3 id').symm⟩


/-! ## Small helpers -/

theorem Tree.get_modifyAt_append (f : Tree → Tree) :
    ∀ (p r : List Nat) (t : Tree), (t.modifyAt f (p ++ r)).get p = (t.get p).map fun n => n.modifyAt f r
  | [], r, t => by simp [Tree.get]
  | k :: p, r, t => by
    simp only [List.cons_append, Tree.modifyAt]
    cases hk : t.children[k]? with
    | none => simp [Tree.get, hk]
    | some child =>
      simp only [Tree.get, Tree.children_withChildren, getElem?_set_self' _ _ _ _ hk, hk]
      exact Tree.get_modifyAt_append f p r child

theorem map_range'_set (g g' : Nat → Node) (id : Nat) (h : ∀ j, j ≠ id → g' j = g j) :
    ∀ (lo n : Nat), lo ≤ id → id < lo + n →
      (List.range' lo n).map g' = ((List.range' lo n).map g).set (id - lo) (g' id)
  | _, 0, h1, h2 => by omega
  | lo, n + 1, h1, h2 => by
    rw [List.range'_succ, List.map_cons, List.map_cons]
    by_cases hlo : id = lo
    · subst hlo
      simp only [Nat.sub_self, List.set_cons_zero, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro j hj
      simp only [List.mem_range'_1] at hj
      exact h j (by omega)
    · have e : id - lo = (id - (lo + 1)) + 1 := by omega
      rw [e, List.set_cons_succ, h lo (Ne.symm hlo), map_range'_set g g' id h (lo + 1) n (by omega) (by omega)]

theorem mem_absChildren (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) :
    ∀ (k : Nat) (cs : List Tree) (x : Node), x ∈ absChildren cfg V phase p k cs →
      ∃ j c, cs[j]? = some c ∧ x = absNode cfg V phase (p ++ [k + j]) c
  | _, [], _, h => by simp [absChildren] at h
  | k, c :: cs, x, h => by
    rw [absChildren] at h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, c, rfl, by simp⟩
    · obtain ⟨j, c', hj, rfl⟩ := mem_absChildren cfg V phase p (k + 1) cs x h
      refine ⟨j + 1, c', by simpa using hj, ?_⟩
      have e : k + 1 + j = k + (j + 1) := by omega
      rw [e]

theorem absNode_clock (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) (n : Tree) :
    (absNode cfg V phase p n).clock = zeroClock := by
  cases n; rw [absNode_mk]; rfl

theorem absNode_pending (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) (n : Tree) :
    (absNode cfg V phase p n).pending = pendingAt cfg V phase p n.version n.size := by
  cases n; rw [absNode_mk]; rfl

set_option linter.deprecated false in
/-- The fields of the node under the cursor after its `fetch_add`, in the
abstraction: its counter grew by the amount, and it is pending iff it filled. -/
theorem after_fields {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {id : Nat} {c : Cursor}
    {next : Next} (w : WalkFacts cfg V phase id c next) {n n' : Tree} (hnv : n.version = V)
    (hle : n.finished + c.mergeAmount ≤ n.size) (hsize : n'.size = n.size)
    (hnotfull : n.finished + c.mergeAmount < n.size → n'.version = V ∧ n'.finished = n.finished + c.mergeAmount)
    (hfill : n.finished + c.mergeAmount = n.size → n'.version = V + 1 ∧ n'.finished = 0)
    (hfin : next = .finished ↔ n.finished + c.mergeAmount = n.size ∧ n.size = cfg.workers)
    (hstop : next = .stop ↔ n.finished + c.mergeAmount < n.size) :
    absFinished V n.version n.finished n.size = n.finished ∧
    pendingAt cfg V phase c.path n.version n.size = false ∧
    absFinished V n'.version n'.finished n'.size = n.finished + c.mergeAmount ∧
    pendingAt cfg V (upd phase id (nextPhase cfg V next)) c.path n'.version n'.size =
      decide (n.finished + c.mergeAmount = n.size) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold absFinished; rw [if_neg (by omega), if_pos hnv]
  · unfold pendingAt; simp [hnv]
  · by_cases hfull : n.finished + c.mergeAmount < n.size
    · obtain ⟨h1, h2⟩ := hnotfull hfull
      unfold absFinished; rw [if_neg (by omega), if_pos h1, h2]
    · obtain ⟨h1, -⟩ := hfill (by omega)
      unfold absFinished; rw [if_pos h1, hsize]; omega
  · by_cases hfull : n.finished + c.mergeAmount < n.size
    · obtain ⟨h1, -⟩ := hnotfull hfull
      unfold pendingAt
      simp [h1, Nat.ne_of_lt hfull]
    · have heq : n.finished + c.mergeAmount = n.size := by omega
      obtain ⟨h1, -⟩ := hfill heq
      unfold pendingAt
      rw [h1, hsize]
      simp only [beq_self_eq_true, Bool.true_and, heq, decide_true]
      cases next with
      | finished =>
        obtain ⟨-, hW⟩ := hfin.mp rfl
        simp [hW]
      | stop => exact absurd (hstop.mp rfl) (by omega)
      | «continue» c' =>
        obtain ⟨hp, hnil⟩ := w.hcont c' rfl
        have : carriedFrom cfg V (upd phase id (nextPhase cfg V (.continue c'))) c.path = true := by
          rw [carriedFrom_iff]
          refine ⟨hnil, id, w.hid, c', ?_, hp, w.hpre⟩
          rw [upd_self]; rfl
        rw [this]
        simp

/-! ## The node under the cursor -/

set_option linter.deprecated false in
/-- A leaf `fetch_add`: the consumer finishes and is applied to its leaf. -/
theorem core_leaf {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hinv : TreeInv cfg V phase t) {id : Nat} {c : Cursor} {next : Next}
    (w : WalkFacts cfg V phase id c next) {vc : VC} {ord : MemOrd} {t' : Tree} {vc' : VC} {rmw : Rmw}
    (hwalk : t.walk cfg c V vc ord = .ok t' vc' rmw next) {n : Tree} (hn : t.get c.path = some n)
    (hnil : n.children = []) {n' : Tree} (hn' : t'.get c.path = some n') :
    Steps (absNode cfg V phase c.path n) (absNode cfg V (upd phase id (nextPhase cfg V next)) c.path n') := by
  obtain ⟨n₀, hn₀, hnv, -, -, -, hle, -, ⟨n₁, hn₁, hlo, hhi, hch, hnotfull, hfill⟩, hfin, hstop, -⟩ :=
    walk_spec hwalk
  rw [hn] at hn₀
  obtain rfl := Option.some.inj hn₀
  rw [hn'] at hn₁
  obtain rfl := Option.some.inj hn₁
  -- the leaf is the walker's own leaf, containing it
  obtain ⟨leaf, hleaf, -, hlo', hhi'⟩ := hinv.leaves id w.hid
  have hpath : (Cursor.start cfg id).path = c.path := Tree.prefix_leaf hn hnil w.hpre hleaf
  rw [hpath, hn] at hleaf
  obtain rfl := Option.some.inj hleaf
  obtain ⟨-, -, hamt1⟩ := (hinv.nodes _ n hn).leaf hnil
  have hamt : c.mergeAmount = 1 := hamt1 id w.hid V c w.hph rfl
  have hsize : n'.size = n.size := by simp [Tree.size, hlo, hhi]
  obtain ⟨hF, hP, hF', hP'⟩ := after_fields w hnv hle hsize hnotfull hfill hfin hstop
  rw [hamt] at hF' hP' hle
  -- the consumer's abstract node before and after
  have hbefore : consumerNode cfg.count V c.path (phase id) = .mk 0 false zeroClock [] := by
    unfold consumerNode consumerDone
    rw [w.hph]
    simp [leafDone]
  have hafter : consumerNode cfg.count V c.path (upd phase id (nextPhase cfg V next) id) =
      .mk 1 false zeroClock [] := by
    unfold consumerNode consumerDone
    rw [upd_self, leafDone_nextPhase cfg V next c.path w.hv]
    · simp
    · intro c' hc' e
      obtain ⟨hp, hnil'⟩ := w.hcont c' hc'
      rw [e] at hp
      exact dropLast_ne_self hnil' hp.symm
  cases n with
  | mk ver f r lo hi cs =>
  cases n' with
  | mk ver' f' r' lo' hi' cs' =>
  simp only [Tree.children_mk, Tree.lo_mk, Tree.hi_mk, Tree.version_mk, Tree.finished_mk,
    Tree.size_mk] at hlo hhi hch hnil hlo' hhi' hF hP hF' hP' hle hsize
  subst hnil
  obtain rfl : lo = lo' := hlo.symm
  obtain rfl : hi = hi' := hhi.symm
  subst hch
  rw [absNode_mk, absNode_mk, absKids, absKids, hF, hP, hF', hP']
  generalize hL : ((List.range' lo (hi - lo)).map fun id' => consumerNode cfg.count V c.path (phase id')) = L
  have hidx : L[id - lo]? = some (.mk 0 false zeroClock []) := by
    rw [← hL, List.getElem?_map, List.getElem?_range']
    simp [Nat.add_sub_cancel' hlo', hbefore]
    omega
  have hL' : ((List.range' lo (hi - lo)).map fun id' =>
      consumerNode cfg.count V c.path (upd phase id (nextPhase cfg V next) id')) =
      L.set (id - lo) (.mk 1 false zeroClock []) := by
    rw [← hL, ← hafter]
    apply map_range'_set _ _ id _ lo (hi - lo) hlo' (by omega)
    intro j hj
    rw [upd_ne _ _ _ hj]
  rw [hL']
  have hsizes : sizes (L.set (id - lo) (.mk 1 true zeroClock [])) = hi - lo := by
    rw [sizes_set L (id - lo) _ _ hidx (by simp [Node.size_nil]), ← hL, sizes_map_consumer,
      List.length_range']
  have step1 := Step.inner f false zeroClock L (id - lo) _ _ hidx (Step.finish zeroClock)
  have step2 := Step.apply f false zeroClock (L.set (id - lo) (.mk 1 true zeroClock [])) (id - lo)
    (.mk 1 true zeroClock []) (List.getElem?_set_self (List.getElem?_eq_some_iff.mp hidx).1) rfl
  simp only [Node.size_nil, Node.clock, Node.unpend, hsizes, zeroClock_join, List.set_set] at step2
  exact .tail (.tail (.refl _) step1) step2


/-- Paths at least two levels below the cursor are untouched. -/
theorem far_below {cp p' L : List Nat} (h : cp.length + 2 ≤ p'.length) (r : List Nat) :
    p' ++ r ≠ cp ∧ ((p' ++ r).dropLast = cp → ¬ (p' ++ r) <+: L) ∧ ¬ (p' ++ r) <+: cp := by
  have hl : (p' ++ r).length = p'.length + r.length := List.length_append ..
  refine ⟨fun e => ?_, fun e _ => ?_, fun hp => ?_⟩
  · have := congrArg List.length e; omega
  · have := congrArg List.length e; simp only [List.length_dropLast] at this; omega
  · have := hp.length_le; omega

/-- Paths below a sibling of the child the walker came through are untouched. -/
theorem sibling_cond {cp L : List Nat} {j k : Nat} (hjk : j ≠ k) (hk : (cp ++ [k]) <+: L) (r : List Nat) :
    (cp ++ [j]) ++ r ≠ cp ∧ (((cp ++ [j]) ++ r).dropLast = cp → ¬ ((cp ++ [j]) ++ r) <+: L) ∧
      ¬ ((cp ++ [j]) ++ r) <+: cp := by
  refine ⟨fun e => ?_, fun e hp => ?_, fun hp => ?_⟩
  · have := congrArg List.length e; simp at this
  · cases r with
    | nil =>
      simp only [List.append_nil] at hp
      have := (List.prefix_of_prefix_length_le hp hk (by simp)).eq_of_length (by simp)
      have := List.append_cancel_left this
      simp at this
      exact hjk this
    | cons a r =>
      have := congrArg List.length e
      simp only [List.length_dropLast, List.length_append, List.length_cons] at this
      omega
  · have := hp.length_le; simp at this; omega

set_option linter.deprecated false in
/-- An inner `fetch_add`: the child the walker came through is applied. -/
theorem core_inner {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t) (hw : WalkInv cfg V phase t)
    {id : Nat} {c : Cursor} {next : Next} (w : WalkFacts cfg V phase id c next)
    {vc : VC} {ord : MemOrd} {t' : Tree} {vc' : VC} {rmw : Rmw}
    (hwalk : t.walk cfg c V vc ord = .ok t' vc' rmw next) {n : Tree} (hn : t.get c.path = some n)
    (hne : n.children ≠ []) {n' : Tree} (hn' : t'.get c.path = some n') :
    Steps (absNode cfg V phase c.path n) (absNode cfg V (upd phase id (nextPhase cfg V next)) c.path n') := by
  obtain ⟨n₀, hn₀, hnv, -, -, -, hle, -, ⟨n₁, hn₁, hlo, hhi, hch, hnotfull, hfill⟩, hfin, hstop, -⟩ :=
    walk_spec hwalk
  rw [hn] at hn₀
  obtain rfl := Option.some.inj hn₀
  rw [hn'] at hn₁
  obtain rfl := Option.some.inj hn₁
  have hsize : n'.size = n.size := by simp [Tree.size, hlo, hhi]
  obtain ⟨hF, hP, hF', hP'⟩ := after_fields w hnv hle hsize hnotfull hfill hfin hstop
  -- the walker is above its leaf: the digit it came through
  have hnleaf : c.path ≠ (Cursor.start cfg id).path := by
    intro e
    obtain ⟨leaf, hleaf, hlnil, -, -⟩ := hinv.leaves id w.hid
    rw [← e, hn] at hleaf
    obtain rfl := Option.some.inj hleaf
    exact hne hlnil
  obtain ⟨k, hk⟩ : ∃ k, (c.path ++ [k]) <+: (Cursor.start cfg id).path := by
    obtain ⟨rest, hrest⟩ := w.hpre
    cases rest with
    | nil => exact absurd (by simpa using hrest) hnleaf
    | cons k rest => exact ⟨k, rest, by rw [← hrest]; simp⟩
  obtain ⟨child, hchild, hcv, hamt⟩ := hw.carries id w.hid c w.hph k hk
  have hck : n.children[k]? = some child := by rw [← get_child hn]; exact hchild
  have hklt : k < n.children.length := lt_length_of_getElem?' _ _ _ hck
  -- the node is live (something is carried towards it), so no child covers every worker
  have hnd : ¬ deadAt cfg.workers t c.path n := fun hd => by
    obtain ⟨-, -, h0⟩ := (hinv.nodes _ n hn).dead hd
    have h1 := carryOf_le_carriedTo cfg.workers c.path phase id w.hid
    rw [w.hph, carryOf_walk, if_pos rfl] at h1
    have h2 := hinv.carry_pos id w.hid V c w.hph
    omega
  have hcW : child.size ≠ cfg.workers := fun e => hnd ⟨k, hklt, child, hchild, e⟩
  have hwfc := Wf.get _ hwf hchild
  -- the abstract child: filled and carried
  have hcsize : (absNode cfg V phase (c.path ++ [k]) child).size = child.size :=
    absNode_size cfg V phase _ child rfl hwfc _
  have hcpend : (absNode cfg V phase (c.path ++ [k]) child).pending = true := by
    rw [absNode_pending]
    unfold pendingAt
    have : carriedFrom cfg V phase (c.path ++ [k]) = true := by
      rw [carriedFrom_iff]
      exact ⟨by simp, id, w.hid, c, w.hph, by simp, hk⟩
    simp [hcv, this]
  -- after the step nobody carries it any more
  have hcpend' :
      (absNode cfg V (upd phase id (nextPhase cfg V next)) (c.path ++ [k]) child).pending = false := by
    rw [absNode_pending]
    unfold pendingAt
    have : carriedFrom cfg V (upd phase id (nextPhase cfg V next)) (c.path ++ [k]) = false := by
      apply carriedFrom_false
      rintro ⟨-, id', hid', c', hc', hp, hpx⟩
      simp only [List.dropLast_concat] at hp
      by_cases h : id' = id
      · subst h
        rw [upd_self] at hc'
        obtain ⟨hp', hnil⟩ := w.after hc'
        rw [hp'] at hp
        exact dropLast_ne_self hnil hp
      · rw [upd_ne _ _ _ h] at hc'
        exact h (hw.distinct id id' w.hid hid' c c' k w.hph hc' hp hk hpx).symm
    simp [hcv, this, hcW]
  -- the abstract child afterwards is the old one, no longer pending
  have hchild_eq : absNode cfg V (upd phase id (nextPhase cfg V next)) (c.path ++ [k]) child =
      (absNode cfg V phase (c.path ++ [k]) child).unpend := by
    have hp' := hcpend'
    cases child with
    | mk cv cf cr clo chi ccs =>
      rw [absNode_pending] at hp'
      simp only [Tree.version_mk, Tree.size_mk] at hp'
      rw [absNode_mk, absNode_mk, Node.unpend, hp']
      congr 1
      cases ccs with
      | nil =>
        rw [absKids, absKids]
        apply List.map_congr_left
        intro id' _
        unfold consumerNode
        rw [consumerDone_walk w _ (not_prefix_append_singleton_self _ _) id']
      | cons c₀ cs₀ =>
        rw [absKids, absKids]
        apply absChildren_congr
        intro j c' _
        exact (absNode_congr cfg V phase _ (sizeOf c') c' rfl _
          (agree_walk w _ c' (far_below (by simp)))).symm
  -- the abstract children afterwards
  have hkids : absChildren cfg V (upd phase id (nextPhase cfg V next)) c.path 0 n.children =
      (absChildren cfg V phase c.path 0 n.children).set k
        (absNode cfg V phase (c.path ++ [k]) child).unpend := by
    apply List.ext_getElem?
    intro j
    rw [absChildren_getElem?, List.getElem?_set]
    by_cases hjk : k = j
    · subst hjk
      rw [if_pos rfl, if_pos (by rw [absChildren_length]; exact hklt), hck, Nat.zero_add]
      simp only [Option.map_some, Option.some.injEq]
      exact hchild_eq
    · rw [if_neg hjk, absChildren_getElem?, Nat.zero_add]
      cases hj : n.children[j]? with
      | none => rfl
      | some cj =>
        simp only [Option.map_some, Option.some.injEq]
        exact (absNode_congr cfg V phase _ (sizeOf cj) cj rfl _
          (agree_walk w _ cj (sibling_cond (Ne.symm hjk) hk))).symm
  cases n with
  | mk ver f r lo hi cs =>
  cases n' with
  | mk ver' f' r' lo' hi' cs' =>
  simp only [Tree.children_mk, Tree.version_mk, Tree.finished_mk, Tree.size_mk, Tree.lo_mk,
    Tree.hi_mk] at hlo hhi hch hne hck hF hP hF' hP' hle hsize hkids hklt
  obtain rfl : lo = lo' := hlo.symm
  obtain rfl : hi = hi' := hhi.symm
  obtain rfl : cs = cs' := hch.symm
  rw [absNode_mk, absNode_mk, absKids_of_ne_nil _ _ _ _ _ _ hne, absKids_of_ne_nil _ _ _ _ _ _ hne,
    hF, hP, hF', hP', hkids]
  have hsizes : sizes (absChildren cfg V phase c.path 0 cs) = hi - lo := by
    rw [sizes_absChildren]
    · exact (Wf.get _ hwf hn).sum_children hne
    · intro x hx q
      exact absNode_size cfg V phase _ x rfl ((Wf.get _ hwf hn).children_wf x hx) q
  have hkidx : (absChildren cfg V phase c.path 0 cs)[k]? =
      some (absNode cfg V phase (c.path ++ [k]) child) := by
    rw [absChildren_getElem?, hck, Nat.zero_add]
    rfl
  have step := Step.apply f false zeroClock (absChildren cfg V phase c.path 0 cs) k _ hkidx hcpend
  rw [hcsize, hsizes, absNode_clock, zeroClock_join, ← hamt] at step
  exact .tail (.refl _) step


/-! ## The simulation -/

theorem sibling_cond' {p : List Nat} {j k : Nat} {r L : List Nat} (hjk : j ≠ k) (r'' : List Nat) :
    (p ++ [j]) ++ r'' ≠ (p ++ [k]) ++ r ∧
      (((p ++ [j]) ++ r'').dropLast = (p ++ [k]) ++ r → ¬ ((p ++ [j]) ++ r'') <+: L) ∧
      ¬ ((p ++ [j]) ++ r'') <+: (p ++ [k]) ++ r := by
  rw [← List.append_cons, ← List.append_cons]
  refine ⟨ne_of_ne_digit hjk, fun e _ => ?_, not_prefix_of_ne_digit hjk⟩
  have := List.dropLast_prefix (p ++ j :: r'')
  rw [e] at this
  exact not_prefix_of_ne_digit (Ne.symm hjk) this

set_option linter.deprecated false in
/-- Along the path from the root to the cursor, the abstract tree makes the
core steps inside the right child. -/
theorem sim {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t) (hw : WalkInv cfg V phase t)
    {id : Nat} {c : Cursor} {next : Next} (w : WalkFacts cfg V phase id c next)
    {vc : VC} {ord : MemOrd} {t' : Tree} {vc' : VC} {rmw : Rmw}
    (hwalk : t.walk cfg c V vc ord = .ok t' vc' rmw next) {f : Tree → Tree}
    (ht' : t' = t.modifyAt f c.path) :
    ∀ (r p : List Nat) (n : Tree), t.get p = some n → p ++ r = c.path →
      Steps (absNode cfg V phase p n)
        (absNode cfg V (upd phase id (nextPhase cfg V next)) p (n.modifyAt f r))
  | [], p, n, hn, hpr => by
    simp only [List.append_nil] at hpr
    subst hpr
    have hn' : t'.get c.path = some (n.modifyAt f []) := by
      rw [ht', Tree.get_modifyAt_self, hn]; rfl
    by_cases hnil : n.children = []
    · exact core_leaf hinv w hwalk hn hnil hn'
    · exact core_inner hwf hinv hw w hwalk hn hnil hn'
  | k :: r, p, n, hn, hpr => by
    rw [List.append_cons] at hpr
    obtain ⟨n₀, hn₀, -⟩ := walk_spec hwalk
    cases hc : n.children[k]? with
    | none =>
      exfalso
      rw [← hpr, Tree.get_append, get_child hn, hc] at hn₀
      simp at hn₀
    | some child =>
      have ih := sim hwf hinv hw w hwalk ht' r (p ++ [k]) child (by rw [get_child hn]; exact hc) hpr
      have hlen : p.length + 1 ≤ c.path.length := by
        rw [← hpr]; simp
      have hp1 : p ≠ c.path := fun e => by rw [e] at hlen; omega
      have hp2 : p.dropLast = c.path → ¬ p <+: (Cursor.start cfg id).path := fun e _ => by
        have := congrArg List.length e
        simp only [List.length_dropLast] at this
        omega
      cases n with
      | mk ver f₀ rr lo hi cs =>
      simp only [Tree.children_mk] at hc
      have hne : cs ≠ [] := by intro h; subst h; simp at hc
      have hne' : cs.set k (child.modifyAt f r) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
        exact hne this
      rw [show Tree.modifyAt f (Tree.mk ver f₀ rr lo hi cs) (k :: r) =
          Tree.mk ver f₀ rr lo hi (cs.set k (child.modifyAt f r)) by
        rw [Tree.modifyAt]; simp [hc, Tree.withChildren]]
      rw [absNode_mk, absNode_mk, absKids_of_ne_nil _ _ _ _ _ _ hne, absKids_of_ne_nil _ _ _ _ _ _ hne',
        absChildren_set, Nat.zero_add, pendingAt_walk w p hp1 hp2]
      -- the other children are untouched
      have hset : ∀ X, (absChildren cfg V (upd phase id (nextPhase cfg V next)) p 0 cs).set k X =
          (absChildren cfg V phase p 0 cs).set k X := by
        intro X
        apply List.ext_getElem?
        intro j
        rw [List.getElem?_set, List.getElem?_set]
        by_cases hjk : k = j
        · rw [if_pos hjk, if_pos hjk, absChildren_length, absChildren_length]
        · rw [if_neg hjk, if_neg hjk, absChildren_getElem?, absChildren_getElem?, Nat.zero_add]
          cases hj : cs[j]? with
          | none => rfl
          | some cj =>
            simp only [Option.map_some, Option.some.injEq]
            exact (absNode_congr cfg V phase _ (sizeOf cj) cj rfl _ (agree_walk w _ cj fun r'' => by
              rw [← hpr]
              exact sibling_cond' (Ne.symm hjk) r'')).symm
      rw [hset]
      exact Steps.inner_lift _ _ zeroClock _ k (by rw [absChildren_getElem?, hc, Nat.zero_add]; rfl) ih

/-- A walker's `fetch_add` is a run of the game. -/
theorem refine_walk {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t) (hw : WalkInv cfg V phase t)
    {id : Nat} {c : Cursor} {next : Next} (w : WalkFacts cfg V phase id c next)
    {vc : VC} {ord : MemOrd} {t' : Tree} {vc' : VC} {rmw : Rmw}
    (hwalk : t.walk cfg c V vc ord = .ok t' vc' rmw next) :
    Steps (absNode cfg V phase [] t) (absNode cfg V (upd phase id (nextPhase cfg V next)) [] t') := by
  obtain ⟨-, -, -, -, -, -, -, ⟨f, -, rfl⟩, -⟩ := walk_spec hwalk
  exact sim hwf hinv hw w hwalk rfl c.path [] t rfl (List.nil_append _)

/-! ## Every other step leaves the abstract tree alone -/

theorem not_prefix_dropLast {r : List Nat} (hr : r ≠ []) : ¬ r <+: r.dropLast := by
  intro h
  have := h.length_le
  simp only [List.length_dropLast] at this
  have : 0 < r.length := by cases r with | nil => exact absurd rfl hr | cons _ _ => simp
  omega

/-- A change of one consumer's phase that neither starts nor ends a walk
above its leaf, and does not change its own leaf counter. -/
theorem agree_of_update {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hinv : TreeInv cfg V phase t) {id : Nat} (hid : id < cfg.workers) (ph' : ConsumerPhase)
    (h1 : ∀ c, phase id = .walk V c → c.path = (Cursor.start cfg id).path)
    (h2 : ∀ c, ph' = .walk V c → c.path = (Cursor.start cfg id).path)
    (h3 : consumerDone cfg.count V (Cursor.start cfg id).path ph' =
      consumerDone cfg.count V (Cursor.start cfg id).path (phase id)) :
    Agree cfg V phase (upd phase id ph') [] t := by
  intro r m hm
  simp only [List.nil_append]
  refine ⟨?_, ?_⟩
  · have : carriedFrom cfg V phase r = carriedFrom cfg V (upd phase id ph') r := by
      apply Bool.eq_iff_iff.mpr
      rw [carriedFrom_iff, carriedFrom_iff]
      constructor
      · rintro ⟨hr, id', hid', c', hc', hp, hpx⟩
        refine ⟨hr, id', hid', ?_⟩
        by_cases h : id' = id
        · subst h
          exfalso
          rw [h1 c' hc'] at hp
          rw [hp] at hpx
          exact not_prefix_dropLast hr hpx
        · rw [upd_ne _ _ _ h]
          exact ⟨c', hc', hp, hpx⟩
      · rintro ⟨hr, id', hid', c', hc', hp, hpx⟩
        refine ⟨hr, id', hid', ?_⟩
        by_cases h : id' = id
        · subst h
          exfalso
          rw [upd_self] at hc'
          rw [h2 c' hc'] at hp
          rw [hp] at hpx
          exact not_prefix_dropLast hr hpx
        · rw [upd_ne _ _ _ h] at hc'
          exact ⟨c', hc', hp, hpx⟩
    unfold pendingAt
    rw [this]
  · intro hnil id' hlo hhi
    by_cases h : id' = id
    · subst h
      rw [upd_self, hinv.leaf_unique r m hm hnil id' hlo hhi]
      exact h3.symm
    · rw [upd_ne _ _ _ h]

/-! ## The start of a version -/

/-- With every counter at zero and every consumer waiting, the abstract tree
is fresh. -/
theorem fresh_of {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t)
    (hver : ∀ q n, t.get q = some n → ¬ deadAt cfg.workers t q n → n.version = V)
    (hcons : ∀ id, id < cfg.workers → ∀ q, leafDone q cfg.count (phase id) = V)
    (hnw : ∀ id, id < cfg.workers → ∀ v c, phase id ≠ .walk v c) :
    ∀ (m : Nat) (q : List Nat) (n : Tree), sizeOf n = m → t.get q = some n →
      Fresh (absNode cfg V phase q n) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro q n hm hq
    subst hm
    have hnode := hinv.nodes q n hq
    have hwfn := Wf.get q hwf hq
    have hcarried : carriedTo cfg.workers q phase = 0 := by
      unfold carriedTo
      apply sum_map_eq_zero
      intro id hid
      simp only [List.mem_range] at hid
      cases h : phase id
      case walk v c => exact absurd h (hnw id hid v c)
      all_goals rfl
    -- the counter is zero and the version is not `V + 1`
    have hfields : n.finished = 0 ∧ n.version ≠ V + 1 := by
      by_cases hd : deadAt cfg.workers t q n
      · obtain ⟨h1, h2, -⟩ := hnode.dead hd
        exact ⟨h2, by omega⟩
      · have hv := hver q n hq hd
        refine ⟨?_, by omega⟩
        by_cases hnil : n.children = []
        · obtain ⟨-, hcount, -⟩ := hnode.leaf hnil
          rw [hcount]
          unfold contributedIn
          apply sum_map_eq_zero
          intro id hid
          simp only [List.mem_range'_1] at hid
          have := hwfn.hi_le
          unfold pastLeaf
          rw [hcons id (by omega) q, hv]
          simp
        · obtain ⟨-, heq⟩ := hnode.live hnil hd
          rw [hcarried, filledBelow_eq hq] at heq
          have : (n.children.map fun c => filledOf (n.version + 1) (some c)).sum = 0 := by
            apply sum_map_eq_zero
            intro c hc
            obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
            have hck : t.get (q ++ [k]) = some c := by rw [get_child hq]; exact hk
            have hcl := live_child hwf hq (lt_length_of_getElem?' _ _ _ hk) hck hd
            rw [filledOf_some, hver _ c hck hcl, hv]
            simp
          omega
    obtain ⟨hf0, hvne⟩ := hfields
    cases n with
    | mk ver f r lo hi cs =>
    simp only [Tree.finished_mk, Tree.version_mk] at hf0 hvne
    subst hf0
    have hF : absFinished V ver 0 (hi - lo) = 0 := by
      unfold absFinished; simp [hvne]
    have hP : pendingAt cfg V phase q ver (hi - lo) = false := by
      unfold pendingAt; simp [hvne]
    rw [absNode_mk, hF, hP]
    have hlt := hwfn.lo_lt_hi
    have hhi := hwfn.hi_le
    simp only [Tree.lo_mk, Tree.hi_mk] at hlt hhi
    cases cs with
    | nil =>
      rw [absKids]
      refine Fresh.node zeroClock _ ?_ ?_
      · intro h
        have := congrArg List.length h
        simp at this
        omega
      · intro ch hch
        rw [List.mem_map] at hch
        obtain ⟨id, hid, rfl⟩ := hch
        simp only [List.mem_range'_1] at hid
        unfold consumerNode consumerDone
        rw [hcons id (by omega) q]
        simp only [Nat.not_succ_le_self, ↓reduceIte]
        exact Fresh.leaf zeroClock
    | cons c cs =>
      rw [absKids]
      refine Fresh.node zeroClock _ (by rw [absChildren]; simp) ?_
      intro ch hch
      obtain ⟨j, c', hj, rfl⟩ := mem_absChildren cfg V phase q 0 (c :: cs) ch hch
      rw [Nat.zero_add]
      have hc' : t.get (q ++ [j]) = some c' := by rw [get_child hq]; exact hj
      exact ih (sizeOf c') (sizeOf_child_lt (n := Tree.mk ver 0 r lo hi (c :: cs))
        (Wf.get.mem_of_getElem?' _ _ _ hj)) (q ++ [j]) c' rfl hc'

theorem init_version (cfg : Config) (hC : 2 ≤ cfg.cluster) :
    ∀ q n, (Tree.init cfg).get q = some n → n.version = 0 := by
  intro q n hq
  obtain ⟨-, -, rfl⟩ :=
    get_build_char cfg.workers cfg.cluster (rootHeight cfg) (rootHeight_pow cfg hC) (by omega) q n hq
  exact build_version _ _ _ _

theorem init_fresh (cfg : Config) (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) :
    Fresh (absState cfg (State.init cfg)) := by
  have hinv := init_treeInv cfg hW hC
  rw [← phaseOf_replicate cfg.workers] at hinv
  have hV : (if cfg.count = 0 then ProducerPhase.done else .beforeWrite 0).version cfg = 0 := by
    split
    · rename_i h; simp [ProducerPhase.version, h]
    · rfl
  show Fresh (absNode cfg ((if cfg.count = 0 then ProducerPhase.done else .beforeWrite 0).version cfg)
    (phaseOf (Array.replicate cfg.workers .start)) [] (Tree.init cfg))
  rw [hV]
  exact fresh_of (init_wf cfg hW hC) hinv (fun q n hq _ => init_version cfg hC q n hq)
    (fun id _ q => by rw [phaseOf_replicate]; rfl)
    (fun id _ v c h => by rw [phaseOf_replicate] at h; cases h) _ [] _ rfl rfl

/-! ## The refinement -/

/-- Every step of the model is a run of the game on the abstract tree, or
the producer moving to the next version, whose abstract tree is fresh. -/
theorem refine_step {cfg : Config} {s s' : State} {th : Thread} {ev : Option Event}
    (hinv : Inv cfg s) (hw : WInv cfg s) (h : step cfg s th = .step s' ev) :
    Steps (absState cfg s) (absState cfg s') ∨ Fresh (absState cfg s') := by
  cases th with
  | producer =>
    obtain ⟨p, p', pr, hp, hmove, hp', hpr, hcs, ht, -, -⟩ := step_producer_move h
    have hinv := hinv.at hp
    unfold absState
    rw [hp', hcs, ht, hp]
    cases hmove with
    | beforeWrite v => exact Or.inl (.refl _)
    | writing v => exact Or.inl (.refl _)
    | publish v => exact Or.inl (.refl _)
    | waiting v _ => exact Or.inl (.refl _)
    | beforeComplete v => exact Or.inl (.refl _)
    | completing v =>
      right
      have hinv : InvAt cfg s.probe s.tree (.completing v) v s.consumers := hinv
      have hprobe : s.probe = 2 * v + 2 := hinv.probeOk
      have hall : ∀ id, id < cfg.workers →
          phaseOf s.consumers id = .waitReady (v + 1) ∨
            (phaseOf s.consumers id = .done ∧ cfg.count = v + 1) := by
        intro id hid
        rcases (hinv.consumers id hid).2.2 hprobe with hc | ⟨hc, hcount⟩
        · exact Or.inl hc
        · exact Or.inr ⟨hc, hcount.symm⟩
      have htree := advance_preserves hinv.wf hinv.tree hall
      have hver : ∀ q n, s.tree.get q = some n → ¬ deadAt cfg.workers s.tree q n → n.version = v + 1 :=
        fun q n hq hnd => all_advanced hinv.wf hinv.tree hall (sizeOf n) q n rfl hq hnd
      have hcons : ∀ id, id < cfg.workers → ∀ q, leafDone q cfg.count (phaseOf s.consumers id) = v + 1 := by
        intro id hid q
        rcases hall id hid with h1 | ⟨h1, h2⟩
        · rw [h1]; rfl
        · rw [h1]; simp [leafDone, h2]
      have hnw : ∀ id, id < cfg.workers → ∀ v' c, phaseOf s.consumers id ≠ .walk v' c := by
        intro id hid v' c hc
        rcases hall id hid with h1 | ⟨h1, -⟩ <;> rw [hc] at h1 <;> cases h1
      unfold nextProducer
      split
      · exact fresh_of hinv.wf htree hver hcons hnw _ [] _ rfl rfl
      · have hcount : cfg.count = v + 1 := by
          have := hinv.version_lt nofun
          omega
        show Fresh (absNode cfg cfg.count _ [] _)
        rw [hcount]
        exact fresh_of hinv.wf htree hver hcons hnw _ [] _ rfl rfl
  | consumer id =>
    obtain ⟨ph, ph', t', hph, hmove, hcs, ht, hprod, -, -, -⟩ := step_consumer_move h
    have hid : id < cfg.workers := by
      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hph
      rw [hinv.size] at hlt
      exact hlt
    have hsize : id < s.consumers.size := by rw [hinv.size]; exact hid
    have hph' : phaseOf s.consumers id = ph := phaseOf_eq hph
    unfold absState
    rw [hprod, hcs, ht, phaseOf_setIfInBounds _ _ _ hsize]
    -- a move that leaves the abstract tree alone
    have hsame : ∀ (ph'' : ConsumerPhase),
        (∀ c, ph = .walk (s.producer.version cfg) c → c.path = (Cursor.start cfg id).path) →
        (∀ c, ph'' = .walk (s.producer.version cfg) c → c.path = (Cursor.start cfg id).path) →
        consumerDone cfg.count (s.producer.version cfg) (Cursor.start cfg id).path ph'' =
          consumerDone cfg.count (s.producer.version cfg) (Cursor.start cfg id).path ph →
        Steps (absNode cfg (s.producer.version cfg) (phaseOf s.consumers) [] s.tree)
            (absNode cfg (s.producer.version cfg) (upd (phaseOf s.consumers) id ph'') [] s.tree) ∨
          Fresh (absNode cfg (s.producer.version cfg) (upd (phaseOf s.consumers) id ph'') [] s.tree) := by
      intro ph'' h1 h2 h3
      left
      rw [← absNode_congr cfg _ _ _ (sizeOf s.tree) s.tree rfl []
        (agree_of_update hinv.tree hid ph'' (by rw [hph']; exact h1) h2 (by rw [hph']; exact h3))]
      exact .refl _
    cases hmove with
    | start => exact hsame _ nofun nofun rfl
    | initializing =>
      split
      · rename_i hc0
        refine hsame _ nofun nofun ?_
        unfold consumerDone
        simp [leafDone, hc0]
      · exact hsame _ nofun nofun rfl
    | waitReady v _ => exact hsame _ nofun nofun rfl
    | beforeFunc v => exact hsame _ nofun nofun rfl
    | inFunc v =>
      refine hsame _ nofun (fun c hc => by injection hc with _ hc; rw [← hc]) ?_
      unfold consumerDone
      rw [leafDone_walk]
      simp only [beq_self_eq_true, ↓reduceIte]
      rfl
    | walk v c t' vc' rmw next hwalk =>
      obtain ⟨rfl, -, -, hlt⟩ := hinv.active hid (Or.inr (Or.inl ⟨c, hph'⟩))
      left
      have w : WalkFacts cfg (s.producer.version cfg) (phaseOf s.consumers) id c next :=
        ⟨hid, hph', hinv.tree.walkers id hid _ c hph', walk_cont hwalk, hlt⟩
      exact refine_walk hinv.wf hinv.tree hw w hwalk
    | finish v =>
      obtain ⟨rfl, -, -, hlt⟩ := hinv.active hid (Or.inr (Or.inr hph'))
      refine hsame _ nofun (by unfold nextConsumer; split <;> nofun) ?_
      unfold consumerDone
      rw [leafDone_nextConsumer cfg _ _ hlt]
      rfl

/-- The game's invariant holds of the abstract tree in every reachable state. -/
theorem reachable_absInv {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) {s : State}
    (h : Reachable cfg s) : Completion.Inv (absState cfg s) := by
  induction h with
  | init => exact (init_fresh cfg hW hC).inv
  | step hr hstep ih =>
    rcases refine_step (reachable_inv hW hC hr) (reachable_wInv hW hC hr) hstep with hs | hf
    · exact hs.inv ih
    · exact hf.inv


end RearmBarrier
