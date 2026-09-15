import RearmBarrier.Protocol

/-!
# What a walker carries

`TreeInv` only says how much is carried towards a node in total. The
refinement to the completion game (`RearmBarrier.Refinement`) needs to know
*which* child each carried contribution stands for: a walker above its leaf
came up through one child of the node under its cursor — the next digit of
the path to its leaf — and it carries exactly that child's size, the child
having just filled (`carries`); and no two walkers at the same node came
through the same child (`distinct`). `WalkInv` states this, `step_wInv`
shows every step keeps it (the only interesting one is a walk that fills a
node and continues to the parent), and `reachable_wInv` lifts it to every
reachable state.
-/

namespace RearmBarrier

structure WalkInv (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (t : Tree) : Prop where
  /-- a walker above its leaf carries the child it came through, which has filled -/
  carries : ∀ id, id < cfg.workers → ∀ c, phase id = .walk V c → ∀ k,
    (c.path ++ [k]) <+: (Cursor.start cfg id).path →
    ∃ child, t.get (c.path ++ [k]) = some child ∧ child.version = V + 1 ∧ c.mergeAmount = child.size
  /-- two walkers at the same node came through different children -/
  distinct : ∀ id id', id < cfg.workers → id' < cfg.workers → ∀ c c' k,
    phase id = .walk V c → phase id' = .walk V c' → c'.path = c.path →
    (c.path ++ [k]) <+: (Cursor.start cfg id).path → (c.path ++ [k]) <+: (Cursor.start cfg id').path →
    id = id'

theorem not_prefix_append_singleton_self (p : List Nat) (k : Nat) : ¬ (p ++ [k]) <+: p := by
  intro h
  have := h.length_le
  simp at this
  omega

/-- The digit a walker at `p.dropLast` came through, if `p` is on the path to its leaf, is `p`'s last. -/
theorem digit_eq_getLast {p q : List Nat} (hnil : p ≠ []) (hpre : p <+: q) {k : Nat}
    (hk : (p.dropLast ++ [k]) <+: q) : k = p.getLast hnil := by
  have h2 : (p.dropLast ++ [p.getLast hnil]) <+: q := by
    rw [List.dropLast_concat_getLast hnil]; exact hpre
  have heq := (List.prefix_of_prefix_length_le hk h2 (by simp)).eq_of_length (by simp)
  have := List.append_cancel_left heq
  simp at this
  exact this

theorem WalkInv.of_no_walkers {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (h : ∀ id, id < cfg.workers → ∀ c, phase id ≠ .walk V c) : WalkInv cfg V phase t :=
  ⟨fun id hid c hc => absurd hc (h id hid c), fun id _ hid _ c _ _ hc => absurd hc (h id hid c)⟩

/-- Walkers may disappear, or start at their leaf. -/
theorem WalkInv.mono {cfg : Config} {V : Nat} {phase phase' : Nat → ConsumerPhase} {t : Tree}
    (hw : WalkInv cfg V phase t)
    (h : ∀ id, id < cfg.workers → ∀ c, phase' id = .walk V c →
      phase id = .walk V c ∨ c.path = (Cursor.start cfg id).path) : WalkInv cfg V phase' t := by
  refine ⟨?_, ?_⟩
  · intro id hid c hc k hk
    rcases h id hid c hc with hc' | hleaf
    · exact hw.carries id hid c hc' k hk
    · rw [← hleaf] at hk
      exact absurd hk (not_prefix_append_singleton_self _ _)
  · intro id id' hid hid' c c' k hc hc' hpath hk hk'
    rcases h id hid c hc with hc1 | hleaf
    · rcases h id' hid' c' hc' with hc2 | hleaf'
      · exact hw.distinct id id' hid hid' c c' k hc1 hc2 hpath hk hk'
      · have e : (Cursor.start cfg id').path = c.path := by rw [← hleaf', hpath]
        rw [e] at hk'
        exact absurd hk' (not_prefix_append_singleton_self _ _)
    · rw [← hleaf] at hk
      exact absurd hk (not_prefix_append_singleton_self _ _)

/-- Only the walkers' children matter in the tree. -/
theorem WalkInv.tree_congr {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t t' : Tree}
    (hw : WalkInv cfg V phase t)
    (h : ∀ id, id < cfg.workers → ∀ c, phase id = .walk V c → ∀ k,
      (c.path ++ [k]) <+: (Cursor.start cfg id).path →
      (t'.get (c.path ++ [k])).map Tree.fields = (t.get (c.path ++ [k])).map Tree.fields) :
    WalkInv cfg V phase t' := by
  refine ⟨?_, hw.distinct⟩
  intro id hid c hc k hk
  obtain ⟨child, hchild, hver, hamt⟩ := hw.carries id hid c hc k hk
  have := h id hid c hc k hk
  rw [hchild] at this
  cases hg : t'.get (c.path ++ [k]) with
  | none => rw [hg] at this; simp at this
  | some child' =>
    rw [hg] at this
    simp only [Option.map_some, Option.some.injEq] at this
    obtain ⟨h1, -, -, -, -⟩ := Tree.fields_inj this
    exact ⟨child', rfl, by rw [h1, hver], by rw [hamt]; exact (Tree.size_of_fields this).symm⟩

/-- A walker's `fetch_add` keeps the invariant: if it fills the node it
continues to the parent carrying the node it just filled. -/
theorem walkInv_walk {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hinv : TreeInv cfg V phase t) (hw : WalkInv cfg V phase t)
    {id : Nat} {c : Cursor} (hid : id < cfg.workers) (hph : phase id = .walk V c)
    {vc : VC} {ord : MemOrd} {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next}
    (hwalk : t.walk cfg c V vc ord = .ok t' vc' rmw next) :
    WalkInv cfg V (upd phase id (nextPhase cfg V next)) t' := by
  obtain ⟨n, hn, hnv, -, -, -, -, ⟨f, hf, rfl⟩, ⟨n', hn', hlo, hhi, -, -, hfill⟩, -, -, hcont⟩ :=
    walk_spec hwalk
  -- no walker's child is the node under the cursor: it counts `V`, a walker's child `V + 1`
  have hne : ∀ id', id' < cfg.workers → ∀ c', phase id' = .walk V c' → ∀ k,
      (c'.path ++ [k]) <+: (Cursor.start cfg id').path → c'.path ++ [k] ≠ c.path := by
    intro id' hid' c' hc' k hk heq
    obtain ⟨child, hchild, hver, -⟩ := hw.carries id' hid' c' hc' k hk
    rw [heq, hn] at hchild
    have := Option.some.inj hchild
    subst this
    omega
  have hw' : WalkInv cfg V phase (t.modifyAt f c.path) :=
    hw.tree_congr fun id' hid' c' hc' k hk =>
      Tree.get_modifyAt_ne f hf t c.path _ (hne id' hid' c' hc' k hk)
  have hother : ∀ id', id' ≠ id → ∀ c', upd phase id (nextPhase cfg V next) id' = .walk V c' →
      phase id' = .walk V c' := by
    intro id' h c' hc'
    rw [upd_ne _ _ _ h] at hc'
    exact hc'
  cases next with
  | stop =>
    refine hw'.mono fun id' hid' c' hc' => ?_
    by_cases h : id' = id
    · subst h
      rw [upd_self] at hc'
      exact absurd hc' (by show nextConsumer cfg V ≠ _; unfold nextConsumer; split <;> nofun)
    · exact Or.inl (hother id' h c' hc')
  | finished =>
    refine hw'.mono fun id' hid' c' hc' => ?_
    by_cases h : id' = id
    · subst h
      rw [upd_self] at hc'
      cases hc'
    · exact Or.inl (hother id' h c' hc')
  | «continue» c' =>
    obtain ⟨rfl, hfull, -, hnil⟩ := hcont c' rfl
    have hver' := (hfill hfull).1
    have hsize' : n'.size = n.size := by simp [Tree.size, hlo, hhi]
    have hpre := hinv.walkers id hid V c hph
    have hsplit := List.dropLast_concat_getLast hnil
    -- the walker at `c.path.dropLast` came through `c.path`'s last digit
    have hself : ∀ k, (c.path.dropLast ++ [k]) <+: (Cursor.start cfg id).path →
        c.path.dropLast ++ [k] = c.path := by
      intro k hk
      rw [digit_eq_getLast hnil hpre hk, hsplit]
    refine ⟨?_, ?_⟩
    · intro id' hid' c'' hc'' k hk
      by_cases h : id' = id
      · subst h
        rw [upd_self] at hc''
        simp only [nextPhase, ConsumerPhase.walk.injEq, true_and] at hc''
        subst hc''
        rw [hself k hk]
        exact ⟨n', hn', hver', hsize'.symm⟩
      · exact hw'.carries id' hid' c'' (hother id' h c'' hc'') k hk
    · intro id₁ id₂ hid₁ hid₂ c₁ c₂ k hc₁ hc₂ hpath hk₁ hk₂
      -- a second walker through `c.path` would have found it at `V + 1` before the step
      have hno : ∀ id', id' ≠ id → id' < cfg.workers → ∀ c', phase id' = .walk V c' →
          c'.path = c.path.dropLast → (c.path.dropLast ++ [k]) <+: (Cursor.start cfg id).path →
          (c.path.dropLast ++ [k]) <+: (Cursor.start cfg id').path → False := by
        intro id' _ hid' c' hc' hp hk hk'
        obtain ⟨child, hchild, hver, -⟩ := hw.carries id' hid' c' hc' k (by rw [hp]; exact hk')
        rw [hp, hself k hk, hn] at hchild
        have := Option.some.inj hchild
        subst this
        omega
      by_cases h₁ : id₁ = id
      · by_cases h₂ : id₂ = id
        · rw [h₁, h₂]
        · exfalso
          subst h₁
          rw [upd_self] at hc₁
          simp only [nextPhase, ConsumerPhase.walk.injEq, true_and] at hc₁
          subst hc₁
          exact hno id₂ h₂ hid₂ c₂ (hother id₂ h₂ c₂ hc₂) hpath hk₁ hk₂
      · by_cases h₂ : id₂ = id
        · exfalso
          subst h₂
          rw [upd_self] at hc₂
          simp only [nextPhase, ConsumerPhase.walk.injEq, true_and] at hc₂
          subst hc₂
          simp only at hpath
          rw [← hpath] at hk₁ hk₂
          exact hno id₁ h₁ hid₁ c₁ (hother id₁ h₁ c₁ hc₁) hpath.symm hk₂ hk₁
        · exact hw.distinct id₁ id₂ hid₁ hid₂ c₁ c₂ k (hother id₁ h₁ c₁ hc₁) (hother id₂ h₂ c₂ hc₂)
            hpath hk₁ hk₂

/-! ## Over the whole state -/

def WInv (cfg : Config) (s : State) : Prop :=
  WalkInv cfg (s.producer.version cfg) (phaseOf s.consumers) s.tree

theorem init_wInv (cfg : Config) : WInv cfg (State.init cfg) := by
  show WalkInv cfg _ (phaseOf (Array.replicate cfg.workers .start)) _
  rw [phaseOf_replicate]
  exact WalkInv.of_no_walkers fun _ _ _ h => by cases h

theorem step_producer_wInv {cfg : Config} {s s' : State} {ev : Option Event}
    (hinv : Inv cfg s) (hw : WInv cfg s) (h : step cfg s .producer = .step s' ev) : WInv cfg s' := by
  obtain ⟨p, p', pr, hp, hmove, hp', hpr, hcs, ht, -, -⟩ := step_producer_move h
  have hinv := hinv.at hp
  have hw : WalkInv cfg (p.version cfg) (phaseOf s.consumers) s.tree := by
    unfold WInv at hw; rw [hp] at hw; exact hw
  show WalkInv cfg (s'.producer.version cfg) (phaseOf s'.consumers) s'.tree
  rw [hp', hcs, ht]
  cases hmove with
  | beforeWrite v => exact hw
  | writing v => exact hw
  | publish v => exact hw
  | waiting v _ => exact hw
  | beforeComplete v => exact hw
  | completing v =>
    have hinv : InvAt cfg s.probe s.tree (.completing v) v s.consumers := hinv
    have hprobe : s.probe = 2 * v + 2 := hinv.probeOk
    have hnone : ∀ V', ∀ id, id < cfg.workers → ∀ c, phaseOf s.consumers id ≠ .walk V' c := by
      intro V' id hid c hc
      rcases (hinv.consumers id hid).2.2 hprobe with h1 | ⟨h1, -⟩ <;> rw [hc] at h1 <;> cases h1
    unfold nextProducer
    split
    · exact WalkInv.of_no_walkers (hnone _)
    · exact WalkInv.of_no_walkers (hnone _)

theorem step_consumer_wInv {cfg : Config} {s s' : State} {id : Nat} {ev : Option Event}
    (hinv : Inv cfg s) (hw : WInv cfg s) (h : step cfg s (.consumer id) = .step s' ev) : WInv cfg s' := by
  obtain ⟨ph, ph', t', hph, hmove, hcs, ht, hprod, -, -, -⟩ := step_consumer_move h
  have hid : id < cfg.workers := by
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hph
    rw [hinv.size] at hlt
    exact hlt
  have hsize : id < s.consumers.size := by rw [hinv.size]; exact hid
  have hph' : phaseOf s.consumers id = ph := phaseOf_eq hph
  show WalkInv cfg (s'.producer.version cfg) (phaseOf s'.consumers) s'.tree
  rw [hprod, hcs, ht, phaseOf_setIfInBounds _ _ _ hsize]
  have hw : WalkInv cfg (s.producer.version cfg) (phaseOf s.consumers) s.tree := hw
  -- a move that does not start or continue a walk
  have hmono : ∀ {ph'' : ConsumerPhase} (_ : ∀ v c, ph'' ≠ .walk v c),
      WalkInv cfg (s.producer.version cfg) (upd (phaseOf s.consumers) id ph'') s.tree := by
    intro ph'' hnw
    refine hw.mono fun id' _ c hc => ?_
    by_cases h : id' = id
    · subst h; rw [upd_self] at hc; exact absurd hc (hnw _ _)
    · rw [upd_ne _ _ _ h] at hc; exact Or.inl hc
  cases hmove with
  | start => exact hmono nofun
  | initializing => exact hmono (by split <;> nofun)
  | waitReady v _ => exact hmono nofun
  | beforeFunc v => exact hmono nofun
  | inFunc v =>
    refine hw.mono fun id' _ c hc => ?_
    by_cases h : id' = id
    · subst h
      rw [upd_self] at hc
      simp only [ConsumerPhase.walk.injEq] at hc
      exact Or.inr (by rw [← hc.2])
    · rw [upd_ne _ _ _ h] at hc; exact Or.inl hc
  | walk v c t' vc' rmw next hwalk =>
    obtain ⟨rfl, -, -, -⟩ := hinv.active hid (Or.inr (Or.inl ⟨c, hph'⟩))
    exact walkInv_walk hinv.tree hw hid hph' hwalk
  | finish v => exact hmono (by unfold nextConsumer; split <;> nofun)

theorem step_wInv {cfg : Config} {s s' : State} {t : Thread} {ev : Option Event}
    (hinv : Inv cfg s) (hw : WInv cfg s) (h : step cfg s t = .step s' ev) : WInv cfg s' := by
  cases t with
  | producer => exact step_producer_wInv hinv hw h
  | consumer id => exact step_consumer_wInv hinv hw h

theorem reachable_wInv {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) {s : State}
    (h : Reachable cfg s) : WInv cfg s := by
  induction h with
  | init => exact init_wInv cfg
  | step hr hstep ih => exact step_wInv (reachable_inv hW hC hr) ih hstep

end RearmBarrier
