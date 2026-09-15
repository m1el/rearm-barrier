import RearmBarrier.TreeInvariant

/-!
# From `step` on `State` to the invariant

The bridge between the executable model and `TreeInv`: consumers in a
`State` are an array, the invariant abstracts them as a function
(`phaseOf`), and `State.setConsumer` is the point update `upd`
(`phaseOf_setIfInBounds`). With that, every step of the model that a
consumer takes preserves `TreeInv` (`step_consumer_treeInv`), and a producer
step leaves the tree and the consumers alone (`step_producer_unchanged`).

The hypotheses are the ones the global protocol invariant will supply: the
acting consumer, if it is inside `func`, walking or finishing, is at the
producer's version `V`, which is below `count`.
-/

namespace RearmBarrier

/-- The consumers of a state as a function. -/
def phaseOf (cs : Array ConsumerPhase) : Nat → ConsumerPhase := fun i => cs[i]?.getD .done

theorem phaseOf_eq {cs : Array ConsumerPhase} {id : Nat} {ph : ConsumerPhase} (h : cs[id]? = some ph) :
    phaseOf cs id = ph := by
  simp [phaseOf, h]

theorem phaseOf_setIfInBounds (cs : Array ConsumerPhase) (id : Nat) (ph : ConsumerPhase)
    (hid : id < cs.size) : phaseOf (cs.setIfInBounds id ph) = upd (phaseOf cs) id ph := by
  funext j
  unfold phaseOf upd
  by_cases h : j = id
  · subst h
    simp [Array.getElem?_setIfInBounds, hid]
  · simp [Array.getElem?_setIfInBounds, h, Ne.symm h]

/-! ## What the model's steps do to the consumers and the tree -/

theorem access_unchanged {s s' : State} {t : Nat} {a : Access} (h : s.access t a = .ok s') :
    s'.consumers = s.consumers ∧ s'.tree = s.tree := by
  cases a with
  | readJob =>
    unfold State.access at h
    simp only at h
    split at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩
  | writeJob =>
    unfold State.access at h
    simp only at h
    split at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩
  | writeResult i =>
    unfold State.access at h
    simp only at h
    split at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩
  | writeAllResults =>
    unfold State.access at h
    simp only at h
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h

theorem accessing_unchanged {s s' : State} {t : Nat} {a : Access} {k : State → Outcome} {ev : Option Event}
    (h : Outcome.accessing s t a k = .step s' ev) :
    ∃ s₁, s.access t a = .ok s₁ ∧ s₁.consumers = s.consumers ∧ s₁.tree = s.tree ∧ k s₁ = .step s' ev := by
  unfold Outcome.accessing at h
  split at h
  · rename_i s₁ h₁
    obtain ⟨h2, h3⟩ := access_unchanged h₁
    exact ⟨s₁, h₁, h2, h3, h⟩
  · simp at h

theorem tick_unchanged (s : State) (t : Nat) : (s.tick t).consumers = s.consumers ∧ (s.tick t).tree = s.tree :=
  ⟨rfl, rfl⟩

theorem rmwProbe_unchanged (s : State) (t : Nat) (o : MemOrd) :
    (s.rmwProbe t o).consumers = s.consumers ∧ (s.rmwProbe t o).tree = s.tree := by
  unfold State.rmwProbe
  split <;> split <;> exact ⟨rfl, rfl⟩

theorem fence_unchanged (s : State) (t : Nat) (b : Bool) :
    (if b then s.acquireProbe t else s).consumers = s.consumers ∧
      (if b then s.acquireProbe t else s).tree = s.tree := by
  split <;> exact ⟨rfl, rfl⟩

theorem setConsumer_tree (s : State) (id : Nat) (ph : ConsumerPhase) : (s.setConsumer id ph).tree = s.tree := rfl

theorem setConsumer_consumers (s : State) (id : Nat) (ph : ConsumerPhase) :
    (s.setConsumer id ph).consumers = s.consumers.setIfInBounds id ph := rfl

/-- A producer step never touches the consumers or the tree. -/
theorem step_producer_unchanged {cfg : Config} {s s' : State} {ev : Option Event}
    (h : step cfg s .producer = .step s' ev) : s'.consumers = s.consumers ∧ s'.tree = s.tree := by
  unfold step at h
  simp only at h
  split at h
  · rename_i s'' ev' hp
    simp only [Outcome.step.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [tick_unchanged s'' _ |>.1, tick_unchanged s'' _ |>.2]
    unfold producerStep at hp
    split at hp
    · obtain ⟨s₁, -, h2, h3, hk⟩ := accessing_unchanged hp
      simp only [Outcome.step.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact ⟨h2, h3⟩
    · simp only [Outcome.step.injEq] at hp; obtain ⟨rfl, -⟩ := hp; exact ⟨rfl, rfl⟩
    · simp only [Outcome.step.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      exact ⟨(rmwProbe_unchanged _ _ _).1, (rmwProbe_unchanged _ _ _).2⟩
    · split at hp
      · simp only [Outcome.step.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        exact ⟨(fence_unchanged _ _ _).1, (fence_unchanged _ _ _).2⟩
      · cases hp
    · obtain ⟨s₁, -, h2, h3, hk⟩ := accessing_unchanged hp
      simp only [Outcome.step.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact ⟨h2, h3⟩
    · simp only [Outcome.step.injEq] at hp; obtain ⟨rfl, -⟩ := hp; exact ⟨rfl, rfl⟩
    · cases hp
  · exfalso
    rename_i hne
    exact hne _ _ h

/-- What a consumer step does: the phase it starts from, the phase it moves
to, and the tree afterwards. -/
inductive ConsumerMove (cfg : Config) (s : State) (id : Nat) : ConsumerPhase → ConsumerPhase → Tree → Prop
  | start : ConsumerMove cfg s id .start .initializing s.tree
  | initializing : ConsumerMove cfg s id .initializing (if cfg.count = 0 then .done else .waitReady 0) s.tree
  | waitReady (v : Nat) : ConsumerMove cfg s id (.waitReady v) (.beforeFunc v) s.tree
  | beforeFunc (v : Nat) : ConsumerMove cfg s id (.beforeFunc v) (.inFunc v) s.tree
  | inFunc (v : Nat) : ConsumerMove cfg s id (.inFunc v) (.walk v (Cursor.start cfg id)) s.tree
  | walk (v : Nat) (c : Cursor) (t' : Tree) (vc' : VC) (rmw : Rmw) (next : Next)
      (h : s.tree.walk cfg c v s.clocks[id + 1]! cfg.orderings.ticket = .ok t' vc' rmw next) :
      ConsumerMove cfg s id (.walk v c) (nextPhase cfg v next) t'
  | finish (v : Nat) : ConsumerMove cfg s id (.finish v) (nextConsumer cfg v) s.tree

/-- Every consumer step is one of the moves, applied with `setConsumer`. -/
theorem step_consumer_move {cfg : Config} {s s' : State} {id : Nat} {ev : Option Event}
    (h : step cfg s (.consumer id) = .step s' ev) :
    ∃ ph ph' t', s.consumers[id]? = some ph ∧ ConsumerMove cfg s id ph ph' t' ∧
      s'.consumers = s.consumers.setIfInBounds id ph' ∧ s'.tree = t' := by
  unfold step at h
  simp only at h
  split at h
  · rename_i s'' ev' hc
    simp only [Outcome.step.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [tick_unchanged s'' _ |>.1, tick_unchanged s'' _ |>.2]
    unfold consumerStep at hc
    simp only [threadIndex] at hc
    cases hph : s.consumers[id]? with
    | none => rw [hph] at hc; cases hc
    | some ph =>
      rw [hph] at hc
      cases ph with
      | start =>
        dsimp only at hc
        obtain ⟨s₁, -, h2, h3, hk⟩ := accessing_unchanged hc
        simp only [Outcome.step.injEq] at hk
        obtain ⟨rfl, -⟩ := hk
        exact ⟨_, _, _, rfl, .start, by rw [setConsumer_consumers, h2], by rw [setConsumer_tree, h3]⟩
      | initializing =>
        dsimp only at hc
        simp only [Outcome.step.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        exact ⟨_, _, _, rfl, .initializing, rfl, rfl⟩
      | waitReady v =>
        dsimp only at hc
        split at hc
        · simp only [Outcome.step.injEq] at hc
          obtain ⟨rfl, -⟩ := hc
          exact ⟨_, _, _, rfl, .waitReady v,
            congrArg (fun a => a.setIfInBounds id (.beforeFunc v))
              (fence_unchanged s (id + 1) cfg.orderings.consumerFence).1,
            (fence_unchanged s (id + 1) cfg.orderings.consumerFence).2⟩
        · cases hc
      | beforeFunc v =>
        dsimp only at hc
        obtain ⟨s₁, -, h2, h3, hk⟩ := accessing_unchanged hc
        obtain ⟨s₂, -, h4, h5, hk'⟩ := accessing_unchanged hk
        simp only [Outcome.step.injEq] at hk'
        obtain ⟨rfl, -⟩ := hk'
        exact ⟨_, _, _, rfl, .beforeFunc v, by rw [setConsumer_consumers, h4, h2],
          by rw [setConsumer_tree, h5, h3]⟩
      | inFunc v =>
        dsimp only at hc
        simp only [Outcome.step.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        exact ⟨_, _, _, rfl, .inFunc v, rfl, rfl⟩
      | walk v c =>
        dsimp only at hc
        cases hw : s.tree.walk cfg c v s.clocks[id + 1]! cfg.orderings.ticket with
        | fault m => rw [hw] at hc; cases hc
        | ok t' vc' rmw next =>
          rw [hw] at hc
          simp only [Outcome.step.injEq] at hc
          obtain ⟨rfl, -⟩ := hc
          refine ⟨_, _, _, rfl, .walk v c t' vc' rmw next hw, ?_, rfl⟩
          cases next <;> rfl
      | finish v =>
        dsimp only at hc
        simp only [Outcome.step.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        exact ⟨_, _, _, rfl, .finish v,
          congrArg (fun a => a.setIfInBounds id (nextConsumer cfg v))
            (rmwProbe_unchanged s (id + 1) cfg.orderings.finish).1,
          (rmwProbe_unchanged s (id + 1) cfg.orderings.finish).2⟩
      | done => dsimp only at hc; cases hc
  · exfalso
    rename_i hne
    exact hne _ _ h

/-! ## Every consumer step preserves the invariant -/

theorem step_consumer_treeInv {cfg : Config} {V : Nat} {s s' : State} {id : Nat} {ev : Option Event}
    (hwf : Wf cfg.cluster cfg.workers s.tree)
    (hinv : TreeInv cfg V (phaseOf s.consumers) s.tree)
    (hsize : s.consumers.size = cfg.workers) (hid : id < cfg.workers) (hvc : V < cfg.count)
    (hV : ∀ v, (∃ c, s.consumers[id]? = some (.walk v c)) ∨ s.consumers[id]? = some (.inFunc v) ∨
      s.consumers[id]? = some (.finish v) → v = V)
    (h : step cfg s (.consumer id) = .step s' ev) :
    TreeInv cfg V (phaseOf s'.consumers) s'.tree := by
  obtain ⟨ph, ph', t', hph, hmove, hcs, ht⟩ := step_consumer_move h
  rw [hcs, ht, phaseOf_setIfInBounds _ _ _ (by omega)]
  have hph' := phaseOf_eq hph
  cases hmove with
  | start =>
    exact phase_preserves hinv hid (fun q => by rw [hph']; rfl) (fun q => by rw [hph']; rfl)
      (fun _ _ h => by simp at h)
  | initializing =>
    refine phase_preserves hinv hid (fun q => ?_) (fun q => ?_) (fun _ _ h => ?_)
    · rw [hph']; split <;> simp [leafDone] <;> omega
    · rw [hph']; split <;> rfl
    · split at h <;> simp at h
  | waitReady v =>
    exact phase_preserves hinv hid (fun q => by rw [hph']; rfl) (fun q => by rw [hph']; rfl)
      (fun _ _ h => by simp at h)
  | beforeFunc v =>
    exact phase_preserves hinv hid (fun q => by rw [hph']; rfl) (fun q => by rw [hph']; rfl)
      (fun _ _ h => by simp at h)
  | inFunc v =>
    have hv : v = V := hV v (Or.inr (Or.inl hph))
    subst hv
    exact startWalk_preserves hinv hid hph'
  | walk v c t' vc' rmw next hw =>
    have hv : v = V := hV v (Or.inl ⟨c, hph⟩)
    subst hv
    exact walk_preserves hwf hinv hid hph' hvc hw
  | finish v =>
    have hv : v = V := hV v (Or.inr (Or.inr hph))
    subst hv
    refine phase_preserves hinv hid (fun q => ?_) (fun q => ?_) (fun _ _ h => ?_)
    · rw [hph', leafDone_nextConsumer cfg q _ hvc]; rfl
    · rw [hph', carryOf_nextConsumer]; rfl
    · unfold nextConsumer at h; split at h <;> simp at h

/-- A producer step preserves the invariant at the same version. -/
theorem step_producer_treeInv {cfg : Config} {V : Nat} {s s' : State} {ev : Option Event}
    (hinv : TreeInv cfg V (phaseOf s.consumers) s.tree) (h : step cfg s .producer = .step s' ev) :
    TreeInv cfg V (phaseOf s'.consumers) s'.tree := by
  obtain ⟨h1, h2⟩ := step_producer_unchanged h
  rw [h1, h2]
  exact hinv

end RearmBarrier
