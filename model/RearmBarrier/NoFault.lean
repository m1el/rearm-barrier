import RearmBarrier.Hb

/-!
# No step faults

`Outcome.fault` stands for a panic of the Rust code (an index out of
bounds) or a state the model cannot continue from. `reachable_no_fault`
shows that no reachable state has a faulting step for any thread of the
barrier: the only interesting case is `Tree.walk`, whose node under the
cursor exists (the cursor is on the path to the consumer's leaf), counts the
walker's version (`carried_version`), does not overflow (at the leaf the
amount is `1` and the leaf is not full; above it the amount is part of what
is carried towards the node, which with what it has finished is at most its
size), and is not the root unless the root covers every worker
(`reachable_root_window`: walks never change a window).
-/

set_option linter.deprecated false

namespace RearmBarrier

theorem Tree.get_of_prefix {t : Tree} {p q : List Nat} {n : Tree} (h : t.get q = some n) (hpq : p <+: q) :
    ∃ m, t.get p = some m := by
  obtain ⟨r, rfl⟩ := hpq
  rw [Tree.get_append] at h
  cases hp : t.get p with
  | none => rw [hp] at h; simp at h
  | some m => exact ⟨m, rfl⟩

/-- The walk step of a walking consumer succeeds. -/
theorem walk_ok {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (htree : TreeInv cfg V phase t) (hroot : t.size = cfg.workers)
    {id : Nat} (hid : id < cfg.workers) {c : Cursor} (hph : phase id = .walk V c) (vc : VC) (ord : MemOrd) :
    ∃ t' vc' rmw next, t.walk cfg c V vc ord = .ok t' vc' rmw next := by
  obtain ⟨leaf, hleaf, hlnil, -, -⟩ := htree.leaves id hid
  have hpre := htree.walkers id hid V c hph
  obtain ⟨node, hnode⟩ := Tree.get_of_prefix hleaf hpre
  have hver : node.version = V := ((htree.nodes _ node hnode).carried_version id hid V c hph rfl).symm
  have hle : node.finished + c.mergeAmount ≤ node.size := by
    have hnf := (htree.nodes _ node hnode).not_full
    by_cases hL : c.path = (Cursor.start cfg id).path
    · rw [hL, hleaf] at hnode
      obtain rfl := Option.some.inj hnode
      have := ((htree.nodes _ leaf hleaf).leaf hlnil).2.2 id hid V c hph hL
      omega
    · obtain ⟨k, hk⟩ := prefix_append_singleton_of_ne hpre hL
      obtain ⟨ch, hch⟩ := Tree.get_of_prefix hleaf hk
      have hne := Tree.children_ne_nil_of_get hnode hch
      obtain ⟨-, hsum⟩ := (htree.nodes _ node hnode).live hne (not_dead_of_walker htree hid hph hnode)
      have hfb := filledBelow_le hwf hnode hne
      have hcarry := carryOf_le_carriedTo cfg.workers c.path phase id hid
      rw [hph, carryOf_walk, if_pos rfl] at hcarry
      omega
  have hrootc : c.path = [] → node.size = cfg.workers := by
    intro hnil
    rw [hnil] at hnode
    simp only [Tree.get, Option.some.injEq] at hnode
    rw [← hnode]; exact hroot
  unfold Tree.walk
  rw [hnode]
  simp only [hver, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split
  · exact ⟨_, _, _, _, rfl⟩
  · split
    · omega
    · split
      · exact ⟨_, _, _, _, rfl⟩
      · split
        · rename_i hW hemp
          exact absurd (hrootc (List.isEmpty_iff.mp hemp)) hW
        · exact ⟨_, _, _, _, rfl⟩

/-! ## The root window never changes -/

theorem step_tree_window {cfg : Config} {s s' : State} {t : Thread} {ev : Option Event}
    (h : step cfg s t = .step s' ev) : s'.tree.window = s.tree.window := by
  cases t with
  | producer => rw [(step_producer_unchanged h).2]
  | consumer id =>
    obtain ⟨ph, ph', t', -, hmove, -, ht, -⟩ := step_consumer_move h
    rw [ht]
    cases hmove with
    | walk v c t' vc' rmw next hw =>
      obtain ⟨-, -, -, -, -, -, -, ⟨f, hf, rfl⟩, -⟩ := walk_spec hw
      have := Tree.get_window_modifyAt f hf s.tree c.path []
      simpa [Tree.get] using this
    | _ => rfl

theorem reachable_root_window {cfg : Config} (hC : 2 ≤ cfg.cluster) {s : State} (h : Reachable cfg s) :
    s.tree.lo = 0 ∧ s.tree.hi = cfg.workers := by
  induction h with
  | init => exact init_root_window cfg hC
  | step _ hstep ih =>
    have := step_tree_window hstep
    simp only [Tree.window, Prod.mk.injEq] at this
    omega

/-! ## No step faults -/

theorem producer_no_fault {cfg : Config} {s : State} {m : String} (hr : producerStep cfg s = .fault m) : False := by
  unfold producerStep at hr
  cases hp : s.producer <;> rw [hp] at hr <;> dsimp only at hr
  all_goals first
    | cases hr
    | (split at hr <;> cases hr)
    | (unfold Outcome.accessing at hr; split at hr <;> cases hr)

theorem consumer_no_fault {cfg : Config} {s : State} (hinv : Inv cfg s) (hroot : s.tree.size = cfg.workers)
    {id : Nat} (hid : id < cfg.workers) {m : String} (hr : consumerStep cfg s id = .fault m) : False := by
  unfold consumerStep at hr
  simp only [threadIndex] at hr
  cases hph : s.consumers[id]? with
  | none =>
    rw [Array.getElem?_eq_none_iff, hinv.size] at hph
    omega
  | some ph =>
    rw [hph] at hr
    have hph' : phaseOf s.consumers id = ph := phaseOf_eq hph
    cases ph with
    | walk v c =>
      dsimp only at hr
      obtain ⟨rfl, -, -, -⟩ := hinv.active hid (Or.inr (Or.inl ⟨c, hph'⟩))
      obtain ⟨t', vc', rmw, next, hwk⟩ :=
        walk_ok hinv.wf hinv.tree hroot hid hph' s.clocks[id + 1]! cfg.orderings.ticket
      rw [hwk] at hr
      cases hr
    | beforeFunc v =>
      dsimp only at hr
      unfold Outcome.accessing at hr
      split at hr
      · dsimp only at hr
        split at hr <;> cases hr
      · cases hr
    | start =>
      dsimp only at hr
      unfold Outcome.accessing at hr
      split at hr <;> cases hr
    | waitReady v => dsimp only at hr; split at hr <;> cases hr
    | initializing => dsimp only at hr; cases hr
    | inFunc v => dsimp only at hr; cases hr
    | finish v => dsimp only at hr; cases hr
    | done => dsimp only at hr; cases hr

/-- **No faults.** No thread of the barrier has a faulting step from a
reachable state: no out-of-bounds ticket, no version mismatch, no overflow,
no walk past the root. -/
theorem reachable_no_fault {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) {s : State}
    (h : Reachable cfg s) {t : Thread} (ht : t ∈ threads cfg) (m : String) : step cfg s t ≠ .fault m := by
  have hinv := reachable_inv hW hC h
  have hroot : s.tree.size = cfg.workers := by
    obtain ⟨h1, h2⟩ := reachable_root_window hC h
    simp [Tree.size, h1, h2]
  intro hs
  unfold step at hs
  cases t with
  | producer =>
    simp only at hs
    cases hr : producerStep cfg s with
    | fault m' => exact producer_no_fault hr
    | blocked => rw [hr] at hs; cases hs
    | step s' ev => rw [hr] at hs; cases hs
    | race m' => rw [hr] at hs; cases hs
  | consumer id =>
    have hid : id < cfg.workers := by simpa [threads] using ht
    simp only at hs
    cases hr : consumerStep cfg s id with
    | fault m' => exact consumer_no_fault hinv hroot hid hr
    | blocked => rw [hr] at hs; cases hs
    | step s' ev => rw [hr] at hs; cases hs
    | race m' => rw [hr] at hs; cases hs

end RearmBarrier
