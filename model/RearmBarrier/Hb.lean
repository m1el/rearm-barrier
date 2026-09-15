import RearmBarrier.WalkInv
import RearmBarrier.SpecProofs

/-!
# Happens-before: no non-atomic access races

The model tracks C11 happens-before with vector clocks (see the header of
`RearmBarrier.Model`) and reports a data race (`Outcome.race`) whenever a
non-atomic access is not ordered after every conflicting earlier access.
`HbInv` is the invariant that makes every access ordered, and
`reachable_no_race` shows that no reachable state can take a racing step,
for the orderings the crate uses (`Strong`).

The epoch every clause is about is a consumer's *result write* for the
current version, which happens in the same step as its read of the job
slot, so the job slot's read clock holds it (`State.mark`). The chain from
that write to the producer's `complete` is:

* the consumer's leaf `fetch_add` releases its clock into the leaf's release
  clock (`TreeHb.leaf`);
* the walker that fills a node acquires that node's release clock, so it
  knows every result write counted there (`TreeHb.walker`), and its
  `fetch_add` on the parent releases them there (`TreeHb.counted`); a node
  that has filled knows every result write under it (`TreeHb.filled`);
* the consumer that fills the node covering every worker knows every result
  write (`finisherKnows`), its `fetch_add` on the probe releases them
  (`probeKnows`) and the producer's acquire fence after its spin loop
  acquires them (`producerKnows`).

The other direction — the producer's job write and `complete` are ordered
before the consumers' next `func` — is the producer's release on the probe
(`published`) and the consumer's acquire fence (`beforeFunc`).
-/

namespace RearmBarrier

/-- The orderings the proof needs: those of `src/lib.rs`. -/
structure Strong (o : Orderings) : Prop where
  publish : o.publish.releases = true
  producerFence : o.producerFence = true
  consumerFence : o.consumerFence = true
  ticket_acquires : o.ticket.acquires = true
  ticket_releases : o.ticket.releases = true
  finish : o.finish.releases = true

theorem Strong.default : Strong {} := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Vector clocks -/

theorem getElem!_modify {α : Type} [Inhabited α] (xs : Array α) (i j : Nat) (f : α → α) :
    (xs.modify i f)[j]! = if i = j ∧ j < xs.size then f xs[j]! else xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < xs.size
    · simp only [hi, and_self, ↓reduceIte]
      rw [getElem!_pos xs i hi]
      simp [Array.getElem?_eq_getElem hi]
    · simp only [hi, and_false, ↓reduceIte]
      rw [getElem!_neg xs i hi]
      simp [Array.getElem?_eq_none_iff.mpr (Nat.not_lt.mp hi)]
  · simp [hij, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem getElem!_setIfInBounds {α : Type} [Inhabited α] (xs : Array α) (i j : Nat) (a : α) :
    (xs.setIfInBounds i a)[j]! = if i = j ∧ j < xs.size then a else xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < xs.size
    · simp [hi]
    · simp only [hi, and_false, ↓reduceIte]
      rw [getElem!_neg xs i hi]
      rfl
  · simp [hij, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem getElem!_replicate {α : Type} [Inhabited α] (n : Nat) (v : α) (i : Nat) :
    (Array.replicate n v)[i]! = if i < n then v else default := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem getElem!_of_getElem? {α : Type} [Inhabited α] {xs : Array α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : xs[i]! = a := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, h]
  rfl

theorem getElem?_eq_some_getElem! {α : Type} [Inhabited α] {xs : Array α} {i : Nat} (h : i < xs.size) :
    xs[i]? = some xs[i]! := by
  rw [getElem!_pos xs i h]
  exact Array.getElem?_eq_getElem h

theorem VC.size_zero (n : Nat) : (VC.zero n).size = n := Array.size_replicate

theorem VC.getElem!_zero (n i : Nat) : (VC.zero n)[i]! = 0 := by
  unfold VC.zero
  rw [getElem!_replicate]
  split <;> rfl

theorem VC.size_join (a b : VC) : (a.join b).size = min a.size b.size := Array.size_zipWith

theorem VC.getElem!_join (a b : VC) (i : Nat) (ha : i < a.size) (hb : i < b.size) :
    (a.join b)[i]! = max a[i]! b[i]! := by
  have hs : i < (a.join b).size := by rw [VC.size_join]; omega
  rw [getElem!_pos (a.join b) i hs, getElem!_pos a i ha, getElem!_pos b i hb]
  exact Array.getElem_zipWith hs

theorem VC.le_join_left {a b : VC} (h : a.size ≤ b.size) (i : Nat) : a[i]! ≤ (a.join b)[i]! := by
  by_cases hi : i < a.size
  · rw [VC.getElem!_join a b i hi (by omega)]
    exact Nat.le_max_left _ _
  · rw [getElem!_neg a i hi]
    exact Nat.zero_le _

theorem VC.le_join_right {a b : VC} (h : b.size ≤ a.size) (i : Nat) : b[i]! ≤ (a.join b)[i]! := by
  by_cases hi : i < b.size
  · rw [VC.getElem!_join a b i (by omega) hi]
    exact Nat.le_max_right _ _
  · rw [getElem!_neg b i hi]
    exact Nat.zero_le _

theorem rmwClocks_size {vc rel : VC} (h : vc.size = rel.size) (ord : MemOrd) :
    (rmwClocks vc rel ord).1.size = vc.size ∧ (rmwClocks vc rel ord).2.size = vc.size := by
  unfold rmwClocks
  simp only
  split <;> split <;> simp [VC.size_join, h]

theorem rmwClocks_vc_le {vc rel : VC} (h : vc.size = rel.size) (ord : MemOrd) (i : Nat) :
    vc[i]! ≤ (rmwClocks vc rel ord).1[i]! := by
  unfold rmwClocks
  simp only
  split
  · exact VC.le_join_left (by omega) i
  · exact Nat.le_refl _

theorem rmwClocks_rel_le {vc rel : VC} (h : vc.size = rel.size) (ord : MemOrd) (i : Nat) :
    rel[i]! ≤ (rmwClocks vc rel ord).2[i]! := by
  unfold rmwClocks
  simp only
  split
  · split
    · exact VC.le_join_left (by simp [VC.size_join]; omega) i
    · exact VC.le_join_left (by omega) i
  · exact Nat.le_refl _

/-- With an acquire, the thread learns the location's release clock. -/
theorem rmwClocks_acquires {vc rel : VC} (h : vc.size = rel.size) {ord : MemOrd}
    (hacq : ord.acquires = true) (i : Nat) : rel[i]! ≤ (rmwClocks vc rel ord).1[i]! := by
  unfold rmwClocks
  simp only [hacq, ↓reduceIte]
  exact VC.le_join_right (by omega) i

/-- With a release, the location learns the thread's (new) clock. -/
theorem rmwClocks_releases {vc rel : VC} (h : vc.size = rel.size) {ord : MemOrd}
    (hrel : ord.releases = true) (i : Nat) : (rmwClocks vc rel ord).1[i]! ≤ (rmwClocks vc rel ord).2[i]! := by
  unfold rmwClocks
  simp only [hrel, ↓reduceIte]
  split
  · exact VC.le_join_right (by simp [VC.size_join]; omega) i
  · exact VC.le_join_right (by omega) i

/-! ## Clocks in a state -/

/-- Thread `t`'s knowledge of thread `u`'s clock. -/
def State.ck (s : State) (t u : Nat) : Nat := s.clocks[t]![u]!

/-- The epoch of consumer `j`'s last read of the job slot, which is the
epoch of its result write for the same version. -/
def State.mark (s : State) (j : Nat) : Nat := s.jobSlot.reads[j + 1]!

theorem ck_tick_le (s : State) (t t' u : Nat) : s.ck t' u ≤ (s.tick t).ck t' u := by
  unfold State.ck State.tick
  simp only
  rw [getElem!_modify]
  split
  · rename_i h
    obtain ⟨rfl, -⟩ := h
    rw [getElem!_modify]
    split
    · rename_i h'
      obtain ⟨rfl, -⟩ := h'
      exact Nat.le_add_right _ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem ck_tick_ne (s : State) {t t' u : Nat} (h : t' ≠ t ∨ u ≠ t) : (s.tick t).ck t' u = s.ck t' u := by
  unfold State.ck State.tick
  simp only
  rw [getElem!_modify]
  split
  · rename_i h1
    obtain ⟨rfl, -⟩ := h1
    rw [getElem!_modify]
    split
    · rename_i h2
      obtain ⟨rfl, -⟩ := h2
      rcases h with h | h <;> exact absurd rfl h
    · rfl
  · rfl

theorem tick_clocks_size (s : State) (t : Nat) : (s.tick t).clocks.size = s.clocks.size := by
  unfold State.tick
  simp only
  exact Array.size_modify

theorem tick_clock_size (s : State) (t t' : Nat) : (s.tick t).clocks[t']!.size = s.clocks[t']!.size := by
  unfold State.tick
  simp only
  rw [getElem!_modify]
  split
  · rename_i h
    obtain ⟨rfl, -⟩ := h
    exact Array.size_modify
  · rfl

theorem tick_unchanged' (s : State) (t : Nat) :
    (s.tick t).probeRel = s.probeRel ∧ (s.tick t).jobSlot = s.jobSlot ∧
      (s.tick t).resultSlots = s.resultSlots := ⟨rfl, rfl, rfl⟩

theorem acquireProbe_ck_ne (s : State) {t t' : Nat} (h : t' ≠ t) (u : Nat) :
    (s.acquireProbe t).ck t' u = s.ck t' u := by
  unfold State.ck State.acquireProbe
  simp only
  rw [getElem!_modify]
  split
  · rename_i h1; exact absurd h1.1.symm h
  · rfl

theorem acquireProbe_ck_le (s : State) {t : Nat} (hsize : s.clocks[t]!.size ≤ s.probeRel.size)
    (t' u : Nat) : s.ck t' u ≤ (s.acquireProbe t).ck t' u := by
  unfold State.ck State.acquireProbe
  simp only
  rw [getElem!_modify]
  split
  · rename_i h1
    obtain ⟨rfl, -⟩ := h1
    exact VC.le_join_left hsize u
  · exact Nat.le_refl _

theorem acquireProbe_ck_self (s : State) {t : Nat} (ht : t < s.clocks.size)
    (hsize : s.probeRel.size ≤ s.clocks[t]!.size) (u : Nat) : s.probeRel[u]! ≤ (s.acquireProbe t).ck t u := by
  unfold State.ck State.acquireProbe
  simp only
  rw [getElem!_modify, if_pos ⟨rfl, ht⟩]
  exact VC.le_join_right hsize u

theorem acquireProbe_clocks_size (s : State) (t : Nat) : (s.acquireProbe t).clocks.size = s.clocks.size :=
  Array.size_modify

theorem acquireProbe_clock_size (s : State) {t : Nat} (hsize : s.clocks[t]!.size = s.probeRel.size) (t' : Nat) :
    (s.acquireProbe t).clocks[t']!.size = s.clocks[t']!.size := by
  unfold State.acquireProbe
  simp only
  rw [getElem!_modify]
  split
  · rename_i h1
    obtain ⟨rfl, -⟩ := h1
    rw [VC.size_join, hsize, Nat.min_self]
  · rfl

theorem acquireProbe_unchanged (s : State) (t : Nat) :
    (s.acquireProbe t).probeRel = s.probeRel ∧ (s.acquireProbe t).jobSlot = s.jobSlot ∧
      (s.acquireProbe t).resultSlots = s.resultSlots ∧ (s.acquireProbe t).tree = s.tree ∧
      (s.acquireProbe t).consumers = s.consumers ∧ (s.acquireProbe t).producer = s.producer ∧
      (s.acquireProbe t).probe = s.probe := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem releaseProbe_le (s : State) {t : Nat} (hsize : s.probeRel.size ≤ s.clocks[t]!.size) (u : Nat) :
    s.probeRel[u]! ≤ (s.releaseProbe t).probeRel[u]! :=
  VC.le_join_left hsize u

theorem releaseProbe_ck_le (s : State) {t : Nat} (hsize : s.clocks[t]!.size ≤ s.probeRel.size) (u : Nat) :
    s.ck t u ≤ (s.releaseProbe t).probeRel[u]! :=
  VC.le_join_right hsize u

theorem releaseProbe_size (s : State) {t : Nat} (hsize : s.clocks[t]!.size = s.probeRel.size) :
    (s.releaseProbe t).probeRel.size = s.probeRel.size := by
  show (s.probeRel.join s.clocks[t]!).size = _
  rw [VC.size_join, hsize, Nat.min_self]

theorem releaseProbe_unchanged (s : State) (t : Nat) :
    (s.releaseProbe t).clocks = s.clocks ∧ (s.releaseProbe t).jobSlot = s.jobSlot ∧
      (s.releaseProbe t).resultSlots = s.resultSlots ∧ (s.releaseProbe t).tree = s.tree ∧
      (s.releaseProbe t).consumers = s.consumers ∧ (s.releaseProbe t).producer = s.producer ∧
      (s.releaseProbe t).probe = s.probe := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Slots -/

theorem Slot.readConflict_none {sl : Slot} {vc : VC}
    (h : ∀ tw c, sl.lastWrite = some (tw, c) → c ≤ vc[tw]!) : sl.readConflict vc = none := by
  unfold Slot.readConflict
  split
  · rename_i tw c hw
    have := h tw c hw
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false, Nat.not_lt]
    exact this
  · rfl

theorem Slot.writeConflict_none {sl : Slot} {vc : VC}
    (h : ∀ tw c, sl.lastWrite = some (tw, c) → c ≤ vc[tw]!) (hr : ∀ i : Nat, sl.reads[i]! ≤ vc[i]!) :
    sl.writeConflict vc = none := by
  unfold Slot.writeConflict
  rw [Slot.readConflict_none h]
  simp only [Option.map_eq_none_iff]
  rw [List.find?_eq_none]
  intro x hx
  obtain ⟨r, i⟩ := x
  rw [List.mem_zipIdx_iff_getElem?] at hx
  simp only [Array.getElem?_toList, Nat.add_zero] at hx
  have := hr i
  rw [getElem!_of_getElem? hx] at this
  simp only [decide_eq_true_eq, Nat.not_lt]
  exact this

theorem Slot.read_lastWrite (sl : Slot) (t : Nat) (vc : VC) : (sl.read t vc).lastWrite = sl.lastWrite := rfl

theorem Slot.read_reads (sl : Slot) (t : Nat) (vc : VC) :
    (sl.read t vc).reads = sl.reads.setIfInBounds t vc[t]! := by
  show sl.reads.set! t vc[t]! = _
  exact Array.set!_eq_setIfInBounds

theorem Slot.write_lastWrite (sl : Slot) (t : Nat) (vc : VC) :
    (sl.write t vc).lastWrite = some (t, vc[t]!) := rfl

theorem Slot.write_reads (sl : Slot) (t : Nat) (vc : VC) :
    (sl.write t vc).reads = VC.zero sl.reads.size := rfl

theorem access_readJob_ok {s s₁ : State} {t : Nat} (h : s.access t .readJob = .ok s₁) :
    s₁ = { s with jobSlot := s.jobSlot.read t s.clocks[t]! } := by
  unfold State.access at h
  simp only at h
  split at h
  · cases h
  · cases h; rfl

theorem access_writeJob_ok {s s₁ : State} {t : Nat} (h : s.access t .writeJob = .ok s₁) :
    s₁ = { s with jobSlot := s.jobSlot.write t s.clocks[t]! } := by
  unfold State.access at h
  simp only at h
  split at h
  · cases h
  · cases h; rfl

theorem access_writeResult_ok {s s₁ : State} {t i : Nat} (h : s.access t (.writeResult i) = .ok s₁) :
    s₁ = { s with resultSlots := s.resultSlots.modify i (·.write t s.clocks[t]!) } := by
  unfold State.access at h
  simp only at h
  split at h
  · cases h
  · cases h; rfl

theorem Slot.write_write (sl : Slot) (t : Nat) (vc : VC) : (sl.write t vc).write t vc = sl.write t vc := by
  simp [Slot.write, VC.size_zero]

/-- What `writeAllSlots` does when it succeeds: every listed slot is written. -/
theorem writeAllSlots_ok {t : Nat} {vc : VC} {race : Nat → String → String} :
    ∀ (l : List (Slot × Nat)) (rs rs' : Array Slot), writeAllSlots t vc race l rs = .ok rs' →
      rs'.size = rs.size ∧
      ∀ j, ((∃ x, (x, j) ∈ l) → rs'[j]? = rs[j]?.map (·.write t vc)) ∧
        ((¬ ∃ x, (x, j) ∈ l) → rs'[j]? = rs[j]?)
  | [], rs, rs', h => by
    simp only [writeAllSlots, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨rfl, fun j => ⟨fun h => ?_, fun _ => rfl⟩⟩
    simp at h
  | (slot, i) :: l, rs, rs', h => by
    simp only [writeAllSlots] at h
    split at h
    · cases h
    · obtain ⟨h1, h2⟩ := writeAllSlots_ok l _ rs' h
      refine ⟨by rw [h1, Array.size_modify], fun j => ?_⟩
      obtain ⟨h3, h4⟩ := h2 j
      by_cases hij : i = j
      · subst hij
        refine ⟨fun _ => ?_, fun hn => absurd ⟨slot, by simp⟩ hn⟩
        by_cases hl : ∃ x, (x, i) ∈ l
        · rw [h3 hl, Array.getElem?_modify, if_pos rfl]
          cases rs[i]? with
          | none => rfl
          | some x => simp [Slot.write_write]
        · rw [h4 hl, Array.getElem?_modify, if_pos rfl]
      · have hiff : (∃ x, (x, j) ∈ (slot, i) :: l) ↔ ∃ x, (x, j) ∈ l := by
          constructor
          · rintro ⟨x, hx⟩
            simp only [List.mem_cons, Prod.mk.injEq] at hx
            rcases hx with ⟨-, hji⟩ | hx
            · exact absurd hji.symm hij
            · exact ⟨x, hx⟩
          · rintro ⟨x, hx⟩; exact ⟨x, List.mem_cons_of_mem _ hx⟩
        refine ⟨fun hl => ?_, fun hl => ?_⟩
        · rw [h3 (hiff.mp hl), Array.getElem?_modify, if_neg hij]
        · rw [h4 (fun h => hl (hiff.mpr h)), Array.getElem?_modify, if_neg hij]

theorem writeAllSlots_of_no_conflict {t : Nat} {vc : VC} {race : Nat → String → String} :
    ∀ (l : List (Slot × Nat)) (rs : Array Slot), (∀ x ∈ l, x.1.writeConflict vc = none) →
      ∃ rs', writeAllSlots t vc race l rs = .ok rs'
  | [], rs, _ => ⟨rs, rfl⟩
  | (slot, i) :: l, rs, h => by
    simp only [writeAllSlots]
    rw [h (slot, i) (by simp)]
    exact writeAllSlots_of_no_conflict l _ fun x hx => h x (by simp [hx])

theorem access_writeAll_ok {s s₁ : State} {t : Nat} (h : s.access t .writeAllResults = .ok s₁) :
    s₁.resultSlots.size = s.resultSlots.size ∧
      (∀ j, j < s.resultSlots.size → s₁.resultSlots[j]! = s.resultSlots[j]!.write t s.clocks[t]!) ∧
      s₁.clocks = s.clocks ∧ s₁.probeRel = s.probeRel ∧ s₁.jobSlot = s.jobSlot ∧ s₁.tree = s.tree ∧
      s₁.consumers = s.consumers ∧ s₁.producer = s.producer ∧ s₁.probe = s.probe := by
  unfold State.access at h
  simp only at h
  split at h
  · rename_i rs hrs
    cases h
    obtain ⟨h1, h2⟩ := writeAllSlots_ok _ _ _ hrs
    refine ⟨h1, fun j hj => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hmem : ∃ x, (x, j) ∈ s.resultSlots.toList.zipIdx :=
      ⟨s.resultSlots[j]!, by rw [List.mem_zipIdx_iff_getElem?]; simp [getElem?_eq_some_getElem! hj]⟩
    have h3 := (h2 j).1 hmem
    rw [getElem?_eq_some_getElem! hj] at h3
    exact getElem!_of_getElem? h3
  · cases h

/-! ## The invariant -/

/-- Consumer `j` has done its leaf `fetch_add` for version `V`. -/
def PastLeaf (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (j : Nat) : Prop :=
  leafDone (Cursor.start cfg j).path cfg.count (phase j) = V + 1

/-- A consumer that has run `func` for version `V`: its result write for `V`
is its slot's last write. -/
def PastFunc (cfg : Config) (V : Nat) (ph : ConsumerPhase) : Prop :=
  ph = .inFunc V ∨ (∃ c, ph = .walk V c) ∨ ph = .finish V ∨ Finished cfg V ph

/-- Some walker at `p` came up through child `k`. -/
def Carrier (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (p : List Nat) (k : Nat) : Prop :=
  ∃ i, i < cfg.workers ∧ ∃ c, phase i = .walk V c ∧ c.path = p ∧ (p ++ [k]) <+: (Cursor.start cfg i).path

/-- What the release clocks of the tree and the clocks of the walkers know
about the result writes (`mark`) of the current version. -/
structure TreeHb (cfg : Config) (V : Nat) (phase : Nat → ConsumerPhase) (t : Tree)
    (clocks : Array VC) (mark : Nat → Nat) : Prop where
  /-- a node that has filled knows every result write under it -/
  filled : ∀ p n, t.get p = some n → n.version = V + 1 → ∀ j, n.lo ≤ j → j < n.hi →
    PastLeaf cfg V phase j → mark j ≤ n.rel[j + 1]!
  /-- a leaf knows the result write of every consumer that has counted itself there -/
  leaf : ∀ p n, t.get p = some n → n.children = [] → ∀ j, n.lo ≤ j → j < n.hi →
    PastLeaf cfg V phase j → mark j ≤ n.rel[j + 1]!
  /-- a node knows every result write under a filled child whose walker has
  already counted it here -/
  counted : ∀ p n, t.get p = some n → n.version = V → ¬ deadAt cfg.workers t p n →
    ∀ k child, t.get (p ++ [k]) = some child → child.version = V + 1 → ¬ Carrier cfg V phase p k →
    ∀ j, child.lo ≤ j → j < child.hi → PastLeaf cfg V phase j → mark j ≤ n.rel[j + 1]!
  /-- a walker knows every result write under the child it came through -/
  walker : ∀ i, i < cfg.workers → ∀ c, phase i = .walk V c → ∀ k,
    (c.path ++ [k]) <+: (Cursor.start cfg i).path → ∀ child, t.get (c.path ++ [k]) = some child →
    ∀ j, child.lo ≤ j → j < child.hi → PastLeaf cfg V phase j → mark j ≤ clocks[i + 1]![j + 1]!

structure HbInv (cfg : Config) (s : State) : Prop where
  clocks_size : s.clocks.size = cfg.workers + 1
  clock_size : ∀ t, t < cfg.workers + 1 → s.clocks[t]!.size = cfg.workers + 1
  probeRel_size : s.probeRel.size = cfg.workers + 1
  rel_size : ∀ p n, s.tree.get p = some n → n.rel.size = cfg.workers + 1
  jobReads_size : s.jobSlot.reads.size = cfg.workers + 1
  resultSlots_size : s.resultSlots.size = cfg.workers
  /-- result slots are never read -/
  resultReads : ∀ j, j < cfg.workers → s.resultSlots[j]!.reads = VC.zero (cfg.workers + 1)
  /-- the producer never reads the job slot -/
  jobReads_zero : s.jobSlot.reads[0]! = 0
  /-- a thread's recorded epochs are below its current clock -/
  mark_le : ∀ j, j < cfg.workers → s.mark j ≤ s.ck (j + 1) (j + 1)
  job_write : ∀ tw c, s.jobSlot.lastWrite = some (tw, c) → tw = 0 ∧ c ≤ s.ck 0 0
  result_write : ∀ j, j < cfg.workers → ∀ tw c, s.resultSlots[j]!.lastWrite = some (tw, c) →
    (tw = 0 ∨ tw = j + 1) ∧ c ≤ s.ck tw tw
  /-- nobody has touched a consumer's slot before it does -/
  start : ∀ j, j < cfg.workers → phaseOf s.consumers j = .start → s.resultSlots[j]!.lastWrite = none
  /-- a consumer about to run `func` knows the producer's writes -/
  beforeFunc : ∀ j, j < cfg.workers → ∀ v, phaseOf s.consumers j = .beforeFunc v →
    (∀ c, s.jobSlot.lastWrite = some (0, c) → c ≤ s.ck (j + 1) 0) ∧
    (∀ c, s.resultSlots[j]!.lastWrite = some (0, c) → c ≤ s.ck (j + 1) 0)
  /-- once the producer has published, its writes are in the probe's release clock -/
  published : ∀ v, s.producer = .waiting v →
    (∀ c, s.jobSlot.lastWrite = some (0, c) → c ≤ s.probeRel[0]!) ∧
    (∀ j, j < cfg.workers → ∀ c, s.resultSlots[j]!.lastWrite = some (0, c) → c ≤ s.probeRel[0]!)
  /-- a consumer's result write for the version is what `mark` says -/
  resultMark : ∀ v, s.producer = .waiting v ∨ s.producer = .beforeComplete v →
    ∀ j, j < cfg.workers → PastFunc cfg v (phaseOf s.consumers j) →
    s.resultSlots[j]!.lastWrite = some (j + 1, s.mark j)
  /-- the producer knows every result write before it touches the slots -/
  producerKnows : ∀ v, s.producer = .beforeWrite v ∨ s.producer = .beforeComplete v ∨
    s.producer = .completing v → ∀ j, j < cfg.workers → s.mark j ≤ s.ck 0 (j + 1)
  /-- once a consumer completed the version, the probe's release clock knows every result write -/
  probeKnows : ∀ v, s.producer = .waiting v → s.probe = 2 * v + 2 → ∀ j, j < cfg.workers →
    s.mark j ≤ s.probeRel[j + 1]!
  /-- the consumer completing the version knows every result write -/
  finisherKnows : ∀ i, i < cfg.workers → ∀ v, phaseOf s.consumers i = .finish v → ∀ j, j < cfg.workers →
    PastLeaf cfg v (phaseOf s.consumers) j → s.mark j ≤ s.ck (i + 1) (j + 1)
  tree : TreeHb cfg (s.producer.version cfg) (phaseOf s.consumers) s.tree s.clocks s.mark

/-! ## Monotonicity -/

/-- Guards may become stronger, clocks larger. -/
theorem TreeHb.mono {cfg : Config} {V : Nat} {phase phase' : Nat → ConsumerPhase} {t : Tree}
    {clocks clocks' : Array VC} {mark : Nat → Nat} (h : TreeHb cfg V phase t clocks mark)
    (hpast : ∀ j, PastLeaf cfg V phase' j → PastLeaf cfg V phase j)
    (hcarrier : ∀ p k, Carrier cfg V phase p k → Carrier cfg V phase' p k)
    (hwalk : ∀ i, i < cfg.workers → ∀ c, phase' i = .walk V c →
      phase i = .walk V c ∨ c.path = (Cursor.start cfg i).path)
    (hclocks : ∀ i j : Nat, clocks[i]![j]! ≤ clocks'[i]![j]!) :
    TreeHb cfg V phase' t clocks' mark := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p n hn hv j hlo hhi hp
    exact h.filled p n hn hv j hlo hhi (hpast j hp)
  · intro p n hn hnil j hlo hhi hp
    exact h.leaf p n hn hnil j hlo hhi (hpast j hp)
  · intro p n hn hv hnd k child hchild hcv hnc j hlo hhi hp
    exact h.counted p n hn hv hnd k child hchild hcv (fun hc => hnc (hcarrier p k hc)) j hlo hhi (hpast j hp)
  · intro i hi c hc k hk child hchild j hlo hhi hp
    rcases hwalk i hi c hc with hc' | hleaf
    · exact Nat.le_trans (h.walker i hi c hc' k hk child hchild j hlo hhi (hpast j hp)) (hclocks _ _)
    · rw [hleaf] at hk
      exact absurd hk (not_prefix_append_singleton_self _ _)

theorem TreeHb.of_no_past {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    {clocks : Array VC} {mark : Nat → Nat} (h : ∀ j, ¬ PastLeaf cfg V phase j) :
    TreeHb cfg V phase t clocks mark :=
  ⟨fun _ _ _ _ j _ _ hp => absurd hp (h j), fun _ _ _ _ j _ _ hp => absurd hp (h j),
    fun _ _ _ _ _ _ _ _ _ _ j _ _ hp => absurd hp (h j), fun _ _ _ _ _ _ _ _ j _ _ hp => absurd hp (h j)⟩

theorem TreeHb.of_mark_zero {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    {clocks : Array VC} {mark : Nat → Nat} (h : ∀ j, mark j = 0) :
    TreeHb cfg V phase t clocks mark :=
  ⟨fun _ _ _ _ j _ _ _ => by rw [h j]; exact Nat.zero_le _, fun _ _ _ _ j _ _ _ => by rw [h j]; exact Nat.zero_le _,
    fun _ _ _ _ _ _ _ _ _ _ j _ _ _ => by rw [h j]; exact Nat.zero_le _,
    fun _ _ _ _ _ _ _ _ j _ _ _ => by rw [h j]; exact Nat.zero_le _⟩

/-- Only the phases, the tree, the clocks and the marks matter to the tree part. -/
theorem TreeHb.congr {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t t' : Tree}
    {clocks : Array VC} {mark mark' : Nat → Nat} (h : TreeHb cfg V phase t clocks mark)
    (ht : t' = t) (hm : ∀ j, mark' j = mark j) : TreeHb cfg V phase t' clocks mark' := by
  subst ht
  have : mark' = mark := funext hm
  subst this
  exact h

/-- A step that changes nothing but the clocks, and only upwards. -/
theorem HbInv.frame {cfg : Config} {s s' : State} (hb : HbInv cfg s)
    (hclocks : ∀ t u, s.ck t u ≤ s'.ck t u)
    (hcsize : s'.clocks.size = s.clocks.size)
    (hcsize' : ∀ t, t < cfg.workers + 1 → s'.clocks[t]!.size = s.clocks[t]!.size)
    (hprobeRel : ∀ u : Nat, s.probeRel[u]! ≤ s'.probeRel[u]!)
    (hprsize : s'.probeRel.size = s.probeRel.size)
    (htree : s'.tree = s.tree) (hjob : s'.jobSlot = s.jobSlot) (hres : s'.resultSlots = s.resultSlots)
    (hcons : s'.consumers = s.consumers) (hprod : s'.producer = s.producer) (hprobe : s'.probe = s.probe) :
    HbInv cfg s' := by
  have hmark : ∀ j, s'.mark j = s.mark j := fun j => by unfold State.mark; rw [hjob]
  refine ⟨by rw [hcsize, hb.clocks_size], fun t ht => by rw [hcsize' t ht, hb.clock_size t ht],
    by rw [hprsize, hb.probeRel_size], by rw [htree]; exact hb.rel_size, by rw [hjob]; exact hb.jobReads_size,
    by rw [hres]; exact hb.resultSlots_size, by rw [hres]; exact hb.resultReads,
    by rw [hjob]; exact hb.jobReads_zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hmark]
    exact Nat.le_trans (hb.mark_le j hj) (hclocks _ _)
  · intro tw c hw
    rw [hjob] at hw
    obtain ⟨h1, h2⟩ := hb.job_write tw c hw
    exact ⟨h1, Nat.le_trans h2 (hclocks _ _)⟩
  · intro j hj tw c hw
    rw [hres] at hw
    obtain ⟨h1, h2⟩ := hb.result_write j hj tw c hw
    exact ⟨h1, Nat.le_trans h2 (hclocks _ _)⟩
  · intro j hj hph
    rw [hcons] at hph
    rw [hres]
    exact hb.start j hj hph
  · intro j hj v hph
    rw [hcons] at hph
    rw [hjob, hres]
    obtain ⟨h1, h2⟩ := hb.beforeFunc j hj v hph
    exact ⟨fun c hc => Nat.le_trans (h1 c hc) (hclocks _ _), fun c hc => Nat.le_trans (h2 c hc) (hclocks _ _)⟩
  · intro v hp
    rw [hprod] at hp
    rw [hjob, hres]
    obtain ⟨h1, h2⟩ := hb.published v hp
    exact ⟨fun c hc => Nat.le_trans (h1 c hc) (hprobeRel _),
      fun j hj c hc => Nat.le_trans (h2 j hj c hc) (hprobeRel _)⟩
  · intro v hp j hj hpf
    rw [hprod] at hp
    rw [hcons] at hpf
    rw [hres, hmark]
    exact hb.resultMark v hp j hj hpf
  · intro v hp j hj
    rw [hprod] at hp
    rw [hmark]
    exact Nat.le_trans (hb.producerKnows v hp j hj) (hclocks _ _)
  · intro v hp hpr j hj
    rw [hprod] at hp
    rw [hprobe] at hpr
    rw [hmark]
    exact Nat.le_trans (hb.probeKnows v hp hpr j hj) (hprobeRel _)
  · intro i hi v hph j hj hp
    rw [hcons] at hph hp
    rw [hmark]
    exact Nat.le_trans (hb.finisherKnows i hi v hph j hj hp) (hclocks _ _)
  · rw [hprod, hcons, htree]
    exact (hb.tree.mono (fun _ h => h) (fun _ _ h => h) (fun _ _ _ h => Or.inl h)
      (fun i j => hclocks i j)).congr rfl hmark

theorem HbInv.tick {cfg : Config} {s : State} (hb : HbInv cfg s) (t : Nat) : HbInv cfg (s.tick t) :=
  hb.frame (ck_tick_le s t) (tick_clocks_size s t) (fun t' _ => tick_clock_size s t t') (fun _ => Nat.le_refl _)
    rfl rfl rfl rfl rfl rfl rfl

theorem HbInv.acquireProbe {cfg : Config} {s : State} (hb : HbInv cfg s) {t : Nat} (ht : t < cfg.workers + 1) :
    HbInv cfg (s.acquireProbe t) :=
  have hsize : s.clocks[t]!.size = s.probeRel.size := by rw [hb.clock_size t ht, hb.probeRel_size]
  hb.frame (acquireProbe_ck_le s (Nat.le_of_eq hsize)) (acquireProbe_clocks_size s t)
    (fun t' _ => acquireProbe_clock_size s hsize t') (fun _ => Nat.le_refl _) rfl rfl rfl rfl rfl rfl rfl

theorem HbInv.releaseProbe {cfg : Config} {s : State} (hb : HbInv cfg s) {t : Nat} (ht : t < cfg.workers + 1) :
    HbInv cfg (s.releaseProbe t) :=
  have hsize : s.clocks[t]!.size = s.probeRel.size := by rw [hb.clock_size t ht, hb.probeRel_size]
  hb.frame (fun _ _ => Nat.le_refl _) rfl (fun _ _ => rfl) (releaseProbe_le s (Nat.le_of_eq hsize.symm))
    (releaseProbe_size s hsize) rfl rfl rfl rfl rfl rfl

theorem HbInv.rmwProbe {cfg : Config} {s : State} (hb : HbInv cfg s) {t : Nat} (ht : t < cfg.workers + 1)
    (ord : MemOrd) : HbInv cfg (s.rmwProbe t ord) := by
  unfold State.rmwProbe
  simp only
  split
  · split
    · exact (hb.acquireProbe ht).releaseProbe ht
    · exact hb.releaseProbe ht
  · split
    · exact hb.acquireProbe ht
    · exact hb

/-- A phase change of one consumer that touches nothing else. -/
theorem HbInv.setConsumer_frame {cfg : Config} {s : State} (hb : HbInv cfg s) (id : Nat) (ph : ConsumerPhase) :
    (s.setConsumer id ph).clocks = s.clocks ∧ (s.setConsumer id ph).probeRel = s.probeRel ∧
      (s.setConsumer id ph).jobSlot = s.jobSlot ∧ (s.setConsumer id ph).resultSlots = s.resultSlots ∧
      (s.setConsumer id ph).tree = s.tree ∧ (s.setConsumer id ph).producer = s.producer ∧
      (s.setConsumer id ph).probe = s.probe ∧
      (s.setConsumer id ph).consumers = s.consumers.setIfInBounds id ph :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


theorem HbInv.setResults {cfg : Config} {s : State} (hb : HbInv cfg s) (r : Array (Option Nat)) :
    HbInv cfg { s with results := r } :=
  hb.frame (fun _ _ => Nat.le_refl _) rfl (fun _ _ => rfl) (fun _ => Nat.le_refl _) rfl rfl rfl rfl rfl rfl rfl

theorem HbInv.setJob {cfg : Config} {s : State} (hb : HbInv cfg s) (j : Option Nat) :
    HbInv cfg { s with job := j } :=
  hb.frame (fun _ _ => Nat.le_refl _) rfl (fun _ _ => rfl) (fun _ => Nat.le_refl _) rfl rfl rfl rfl rfl rfl rfl

/-- Changing the probe. -/
theorem HbInv.setProbe {cfg : Config} {s : State} (hb : HbInv cfg s) {p' : Nat}
    (hpk : ∀ v, s.producer = .waiting v → p' = 2 * v + 2 → ∀ j, j < cfg.workers → s.mark j ≤ s.probeRel[j + 1]!) :
    HbInv cfg { s with probe := p' } :=
  ⟨hb.clocks_size, hb.clock_size, hb.probeRel_size, hb.rel_size, hb.jobReads_size, hb.resultSlots_size,
    hb.resultReads, hb.jobReads_zero, hb.mark_le, hb.job_write, hb.result_write, hb.start, hb.beforeFunc,
    hb.published, hb.resultMark, hb.producerKnows, hpk, hb.finisherKnows, hb.tree⟩

/-- Marks of consumers that have not counted themselves are irrelevant to the tree part. -/
theorem TreeHb.mark_congr {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    {clocks : Array VC} {mark mark' : Nat → Nat} (h : TreeHb cfg V phase t clocks mark)
    (hm : ∀ j, PastLeaf cfg V phase j → mark' j = mark j) : TreeHb cfg V phase t clocks mark' :=
  ⟨fun p n hn hv j hlo hhi hp => by rw [hm j hp]; exact h.filled p n hn hv j hlo hhi hp,
    fun p n hn hnil j hlo hhi hp => by rw [hm j hp]; exact h.leaf p n hn hnil j hlo hhi hp,
    fun p n hn hv hnd k ch hch hcv hnc j hlo hhi hp => by
      rw [hm j hp]; exact h.counted p n hn hv hnd k ch hch hcv hnc j hlo hhi hp,
    fun i hi c hc k hk ch hch j hlo hhi hp => by
      rw [hm j hp]; exact h.walker i hi c hc k hk ch hch j hlo hhi hp⟩

/-! ## Facts from the protocol invariant -/

theorem InvAt.leafDone_le_succ {cfg : Config} {probe : Nat} {t : Tree} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} (h : InvAt cfg probe t p V cs) (q : List Nat) {id : Nat}
    (hid : id < cfg.workers) : leafDone q cfg.count (phaseOf cs id) ≤ V + 1 := by
  have hle := h.V_le_count
  have hc := h.consumers id hid
  rcases probe_cases h.probeOk h.version with hp | hp | hp
  · rcases hc.1 hp with h1 | ⟨_, h1 | h1⟩ | ⟨h1', h1⟩ <;> rw [h1] <;> simp only [leafDone] <;> omega
  · rcases hc.2.1 hp with h1 | h1 | h1 | ⟨c, h1⟩ | h1 | (h1 | ⟨h1, _⟩) | ⟨_, h1 | h1⟩ <;> rw [h1] <;>
      simp only [leafDone] <;> (try split) <;> omega
  · rcases hc.2.2 hp with h1 | ⟨h1, h2⟩ <;> rw [h1] <;> simp only [leafDone] <;> omega

/-- A consumer leaving its spin loop is at the producer's version, which is published. -/
theorem InvAt.waitReady_enabled {cfg : Config} {probe : Nat} {t : Tree} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} (h : InvAt cfg probe t p V cs) {id : Nat} (hid : id < cfg.workers) {v : Nat}
    (hph : phaseOf cs id = .waitReady v) (hgt : v * 2 < probe) : v = V ∧ p = .waiting V ∧ probe = 2 * V + 1 := by
  have hc := h.consumers id hid
  rw [hph] at hc
  rcases probe_cases h.probeOk h.version with hp | hp | hp
  · rcases hc.1 hp with h1 | ⟨-, h1 | h1⟩ | ⟨-, h1⟩
    · injection h1 with h1; omega
    · cases h1
    · cases h1
    · cases h1
  · rcases hc.2.1 hp with h1 | h1 | h1 | ⟨c, h1⟩ | h1 | (h1 | ⟨h1, -⟩) | ⟨-, h1 | h1⟩
    · injection h1 with h1; subst h1; exact ⟨rfl, probe_odd h.probeOk h.version hp, hp⟩
    · cases h1
    · cases h1
    · cases h1
    · cases h1
    · injection h1 with h1; omega
    · cases h1
    · cases h1
    · cases h1
  · rcases hc.2.2 hp with h1 | ⟨h1, -⟩
    · injection h1 with h1; omega
    · cases h1

theorem InvAt.beforeFunc_active {cfg : Config} {probe : Nat} {t : Tree} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} (h : InvAt cfg probe t p V cs) {id : Nat} (hid : id < cfg.workers) {v : Nat}
    (hph : phaseOf cs id = .beforeFunc v) : v = V ∧ p = .waiting V ∧ probe = 2 * V + 1 := by
  have hc := h.consumers id hid
  rw [hph] at hc
  rcases probe_cases h.probeOk h.version with hp | hp | hp
  · rcases hc.1 hp with h1 | ⟨-, h1 | h1⟩ | ⟨-, h1⟩ <;> cases h1
  · rcases hc.2.1 hp with h1 | h1 | h1 | ⟨c, h1⟩ | h1 | h1 | ⟨-, h1 | h1⟩
    · cases h1
    · injection h1 with h1; subst h1; exact ⟨rfl, probe_odd h.probeOk h.version hp, hp⟩
    · cases h1
    · cases h1
    · cases h1
    · exact absurd h1 (not_finished_of_ne nofun nofun)
    · cases h1
    · cases h1
  · exact absurd (hc.2.2 hp) (not_finished_of_ne nofun nofun)

/-- Once the version is complete every consumer is past it. -/
theorem InvAt.all_finished {cfg : Config} {probe : Nat} {t : Tree} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} (h : InvAt cfg probe t p V cs) (hp : probe = 2 * V + 2) :
    ∀ j, j < cfg.workers → Finished cfg V (phaseOf cs j) :=
  fun j hj => (h.consumers j hj).2.2 hp

theorem Finished.pastLeaf {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {j : Nat}
    (h : Finished cfg V (phase j)) : PastLeaf cfg V phase j := by
  unfold PastLeaf
  rcases h with h1 | ⟨h1, h2⟩ <;> rw [h1] <;> simp only [leafDone] <;> omega

theorem Finished.pastFunc {cfg : Config} {V : Nat} {ph : ConsumerPhase} (h : Finished cfg V ph) :
    PastFunc cfg V ph := Or.inr (Or.inr (Or.inr h))

theorem Finished.ne_start {cfg : Config} {V : Nat} {ph : ConsumerPhase} (h : Finished cfg V ph) : ph ≠ .start := by
  rcases h with h1 | ⟨h1, -⟩ <;> rw [h1] <;> nofun

theorem Finished.ne_beforeFunc {cfg : Config} {V : Nat} {ph : ConsumerPhase} (h : Finished cfg V ph) (v : Nat) :
    ph ≠ .beforeFunc v := by
  rcases h with h1 | ⟨h1, -⟩ <;> rw [h1] <;> nofun

theorem Finished.ne_finish {cfg : Config} {V : Nat} {ph : ConsumerPhase} (h : Finished cfg V ph) (v : Nat) :
    ph ≠ .finish v := by
  rcases h with h1 | ⟨h1, -⟩ <;> rw [h1] <;> nofun

theorem pastLeaf_upd_ne {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {id : Nat} {ph : ConsumerPhase}
    {j : Nat} (h : j ≠ id) : PastLeaf cfg V (upd phase id ph) j ↔ PastLeaf cfg V phase j := by
  unfold PastLeaf
  rw [upd_ne _ _ _ h]

theorem pastLeaf_upd_self {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {id : Nat} {ph : ConsumerPhase} :
    PastLeaf cfg V (upd phase id ph) id ↔ leafDone (Cursor.start cfg id).path cfg.count ph = V + 1 := by
  unfold PastLeaf
  rw [upd_self]

/-! ## The tree: helper lemmas -/

theorem Tree.rel_withChildren (t : Tree) (cs : List Tree) : (t.withChildren cs).rel = t.rel := by
  cases t; rfl

/-- `modifyAt` at `p` leaves the release clock of every node at `q ≠ p` unchanged. -/
theorem Tree.get_modifyAt_ne_rel (f : Tree → Tree) (hf : Tree.Preserves f) :
    ∀ (t : Tree) (p q : List Nat), q ≠ p →
      ((t.modifyAt f p).get q).map Tree.rel = (t.get q).map Tree.rel
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
        rw [Tree.rel_withChildren]
      | cons j rest =>
        simp only [Tree.get, Tree.children_withChildren]
        by_cases hj : j = k
        · subst hj
          rw [getElem?_set_self' _ _ _ _ hk, hk]
          exact Tree.get_modifyAt_ne_rel f hf child p rest (fun h => hq (by rw [h]))
        · rw [getElem?_set_ne' _ _ _ _ hj]

/-- The node at `q ≠ p` after `modifyAt` at `p`: same fields, same release clock. -/
theorem get_modifyAt_ne' {f : Tree → Tree} (hf : Tree.Preserves f) {t : Tree} {p q : List Nat} (hq : q ≠ p)
    {n' : Tree} (hn' : (t.modifyAt f p).get q = some n') :
    ∃ n, t.get q = some n ∧ n'.fields = n.fields ∧ n'.rel = n.rel := by
  have h1 := Tree.get_modifyAt_ne f hf t p q hq
  have h2 := Tree.get_modifyAt_ne_rel f hf t p q hq
  rw [hn'] at h1 h2
  cases hn : t.get q with
  | none => rw [hn] at h1; simp at h1
  | some n =>
    rw [hn] at h1 h2
    simp only [Option.map_some, Option.some.injEq] at h1 h2
    exact ⟨n, rfl, h1, h2⟩

/-- The clock effects of a walk step: the thread acquires (per the ordering)
the release clock of the node under the cursor, and releases into it. -/
theorem walk_clocks {cfg : Config} {t : Tree} {c : Cursor} {v : Nat} {vc : VC} {ord : MemOrd}
    {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next}
    (h : t.walk cfg c v vc ord = .ok t' vc' rmw next) :
    ∃ node, t.get c.path = some node ∧ vc' = (rmwClocks vc node.rel ord).1 ∧
      ∃ node', t'.get c.path = some node' ∧ node'.rel = (rmwClocks vc node.rel ord).2 := by
  unfold Tree.walk at h
  split at h
  · simp at h
  · rename_i node hnode
    by_cases hv : node.version = v
    · simp only [hv, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      refine ⟨node, hnode, ?_⟩
      by_cases hlt : node.finished + c.mergeAmount < node.size
      · simp only [hlt, ↓reduceIte, WalkResult.ok.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, _, by rw [Tree.get_modifyAt_self, hnode]; rfl, rfl⟩
      · by_cases hgt : node.size < node.finished + c.mergeAmount
        · simp only [hlt, gt_iff_lt, hgt, ↓reduceIte, reduceCtorEq] at h
        · simp only [hlt, gt_iff_lt, hgt, ↓reduceIte] at h
          have hnode' : ∃ node', (t.modifyAt (fun n => Tree.mk (n.version + 1) 0
              (rmwClocks vc node.rel ord).2 n.lo n.hi n.children) c.path).get c.path = some node' ∧
              node'.rel = (rmwClocks vc node.rel ord).2 :=
            ⟨_, by rw [Tree.get_modifyAt_self, hnode]; rfl, rfl⟩
          by_cases hall : node.size = cfg.workers
          · simp only [hall, ↓reduceIte, WalkResult.ok.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            exact ⟨rfl, hnode'⟩
          · simp only [hall, ↓reduceIte] at h
            by_cases hnil : c.path = []
            · simp only [hnil, List.isEmpty_nil, ↓reduceIte, reduceCtorEq] at h
            · have hne : c.path.isEmpty = false := by
                cases hp : c.path with
                | nil => exact absurd hp hnil
                | cons _ _ => rfl
              simp only [hne, Bool.false_eq_true, ↓reduceIte, WalkResult.ok.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact ⟨rfl, hnode'⟩
    · simp only [bne_iff_ne, ne_eq, hv, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- While a consumer has not counted itself at its leaf, no node covering it
has filled. -/
theorem not_past_no_filled {cfg : Config} {probe : Nat} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} {t : Tree} (h : InvAt cfg probe t p V cs) {id : Nat} (hid : id < cfg.workers)
    (hnp : ¬ PastLeaf cfg V (phaseOf cs) id) :
    ∀ q m, t.get q = some m → m.lo ≤ id → id < m.hi → m.version ≠ V + 1 := by
  intro q m hm hlo hhi hver
  have hinv := h.tree
  have hwf := h.wf
  obtain ⟨r, leaf, hleaf, hnil, hl1, hl2⟩ := descend hwf id (sizeOf m) q m rfl hm hlo hhi
  have hpath := hinv.leaf_unique (q ++ r) leaf hleaf hnil id hl1 hl2
  have hnd : ¬ deadAt cfg.workers t q m := fun hd => by
    have := ((hinv.nodes q m hm).dead hd).1
    omega
  have hlv : leaf.version = V + 1 :=
    below_advanced hwf hinv r q m hm hver hnd leaf hleaf (not_deadAt_of_leaf hnil)
  obtain ⟨hb, -, -⟩ := (hinv.nodes _ leaf hleaf).leaf hnil
  have h1 := (hb id hl1 hl2).1
  have h2 := h.leafDone_le_succ (q ++ r) hid
  apply hnp
  unfold PastLeaf
  rw [← hpath]
  omega

/-- Two different walkers towards a node together carry at most its total. -/
theorem two_carry_le (W : Nat) (p : List Nat) (phase : Nat → ConsumerPhase) {i i' : Nat} (hne : i ≠ i')
    (hi : i < W) (hi' : i' < W) : carryOf p (phase i) + carryOf p (phase i') ≤ carriedTo W p phase := by
  unfold carriedTo
  apply getElem?_two_le_sum _ i i' _ _ hne <;> simp [List.getElem?_map, List.getElem?_range, hi, hi']

/-- A node a walker is heading for is live. -/
theorem not_dead_of_walker {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hinv : TreeInv cfg V phase t) {id : Nat} (hid : id < cfg.workers) {c : Cursor}
    (hph : phase id = .walk V c) {n : Tree} (hn : t.get c.path = some n) :
    ¬ deadAt cfg.workers t c.path n := fun hd => by
  obtain ⟨-, -, h0⟩ := (hinv.nodes _ n hn).dead hd
  have h1 := carryOf_le_carriedTo cfg.workers c.path phase id hid
  rw [hph, carryOf_walk, if_pos rfl] at h1
  have h2 := hinv.carry_pos id hid V c hph
  omega

/-! ## The initial state -/

theorem init_rel (cfg : Config) (hC : 2 ≤ cfg.cluster) :
    ∀ q n, (Tree.init cfg).get q = some n → n.rel = VC.zero (cfg.workers + 1) := by
  intro q n hq
  obtain ⟨-, -, rfl⟩ := get_build_char cfg.workers cfg.cluster (rootHeight cfg) (rootHeight_pow cfg hC)
    (by omega) q n hq
  cases rootHeight cfg - q.length <;> rfl

theorem init_hbInv (cfg : Config) (hC : 2 ≤ cfg.cluster) : HbInv cfg (State.init cfg) := by
  have hmark : ∀ j, (State.init cfg).mark j = 0 := fun j => by
    show (Slot.init _).reads[j + 1]! = 0
    exact VC.getElem!_zero _ _
  have hph : phaseOf (State.init cfg).consumers = fun _ => .start := phaseOf_replicate _
  refine ⟨Array.size_replicate, ?_, Array.size_replicate,
    fun q n h => by rw [init_rel cfg hC q n h]; exact VC.size_zero _, Array.size_replicate,
    Array.size_replicate, ?_, VC.getElem!_zero _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    show (Array.replicate (cfg.workers + 1) (VC.zero (cfg.workers + 1)))[t]!.size = _
    rw [getElem!_replicate, if_pos ht, VC.size_zero]
  · intro j hj
    show (Array.replicate cfg.workers (Slot.init (cfg.workers + 1)))[j]!.reads = _
    rw [getElem!_replicate, if_pos hj]
    rfl
  · intro j _; rw [hmark]; exact Nat.zero_le _
  · intro tw c h; cases h
  · intro j hj tw c h
    change (Array.replicate cfg.workers (Slot.init (cfg.workers + 1)))[j]!.lastWrite = _ at h
    rw [getElem!_replicate, if_pos hj] at h
    cases h
  · intro j hj _
    show (Array.replicate cfg.workers (Slot.init (cfg.workers + 1)))[j]!.lastWrite = none
    rw [getElem!_replicate, if_pos hj]
    rfl
  · intro j _ v h; rw [hph] at h; cases h
  · intro v h
    change (if cfg.count = 0 then ProducerPhase.done else .beforeWrite 0) = _ at h
    split at h <;> cases h
  · intro v h
    change (if cfg.count = 0 then ProducerPhase.done else .beforeWrite 0) = _ ∨
      (if cfg.count = 0 then ProducerPhase.done else .beforeWrite 0) = _ at h
    split at h <;> rcases h with h | h <;> cases h
  · intro v _ j _; rw [hmark]; exact Nat.zero_le _
  · intro v h
    change (if cfg.count = 0 then ProducerPhase.done else .beforeWrite 0) = _ at h
    split at h <;> cases h
  · intro i _ v h; rw [hph] at h; cases h
  · exact TreeHb.of_mark_zero hmark

/-! ## Consumer moves -/

/-- Changing one consumer's phase, when the new phase carries no obligation
the state does not already meet. -/
theorem HbInv.setConsumer {cfg : Config} {s : State} (hb : HbInv cfg s) (hinv : Inv cfg s) {id : Nat}
    (hid : id < cfg.workers) {ph' : ConsumerPhase} (hns : ph' ≠ .start)
    (hbf : ∀ v, ph' = .beforeFunc v →
      (∀ c, s.jobSlot.lastWrite = some (0, c) → c ≤ s.ck (id + 1) 0) ∧
      (∀ c, s.resultSlots[id]!.lastWrite = some (0, c) → c ≤ s.ck (id + 1) 0))
    (hpf : ∀ v, s.producer = .waiting v ∨ s.producer = .beforeComplete v → PastFunc cfg v ph' →
      s.resultSlots[id]!.lastWrite = some (id + 1, s.mark id))
    (hfin : ∀ v, ph' = .finish v → ∀ j, j < cfg.workers →
      PastLeaf cfg v (upd (phaseOf s.consumers) id ph') j → s.mark j ≤ s.ck (id + 1) (j + 1))
    (htree : TreeHb cfg (s.producer.version cfg) (upd (phaseOf s.consumers) id ph') s.tree s.clocks s.mark) :
    HbInv cfg (s.setConsumer id ph') := by
  have hsize : id < s.consumers.size := by rw [hinv.size]; exact hid
  have hcs : phaseOf (s.setConsumer id ph').consumers = upd (phaseOf s.consumers) id ph' := by
    rw [setConsumer_consumers, phaseOf_setIfInBounds _ _ _ hsize]
  refine ⟨hb.clocks_size, hb.clock_size, hb.probeRel_size, hb.rel_size, hb.jobReads_size, hb.resultSlots_size,
    hb.resultReads, hb.jobReads_zero, hb.mark_le, hb.job_write, hb.result_write, ?_, ?_, hb.published, ?_,
    hb.producerKnows, hb.probeKnows, ?_, ?_⟩
  · intro j hj hph
    rw [hcs] at hph
    by_cases hji : j = id
    · subst hji; rw [upd_self] at hph; exact absurd hph hns
    · rw [upd_ne _ _ _ hji] at hph; exact hb.start j hj hph
  · intro j hj v hph
    rw [hcs] at hph
    by_cases hji : j = id
    · subst hji; rw [upd_self] at hph; exact hbf v hph
    · rw [upd_ne _ _ _ hji] at hph; exact hb.beforeFunc j hj v hph
  · intro v hp j hj hpf'
    rw [hcs] at hpf'
    by_cases hji : j = id
    · subst hji; rw [upd_self] at hpf'; exact hpf v hp hpf'
    · rw [upd_ne _ _ _ hji] at hpf'; exact hb.resultMark v hp j hj hpf'
  · intro i hi v hph j hj hp
    rw [hcs] at hph hp
    by_cases hii : i = id
    · subst hii; rw [upd_self] at hph; exact hfin v hph j hj hp
    · rw [upd_ne _ _ _ hii] at hph
      have hpast : PastLeaf cfg v (phaseOf s.consumers) j := by
        by_cases hji : j = id
        · subst hji
          obtain ⟨hv, -, -, -⟩ := hinv.active hi (Or.inr (Or.inr hph))
          subst hv
          exact (hinv.finisher i hi hph j hj (Ne.symm hii)).pastLeaf
        · exact (pastLeaf_upd_ne hji).mp hp
      exact hb.finisherKnows i hi v hph j hj hpast
  · rw [hcs]; exact htree

/-- A consumer writing its own result slot. -/
theorem HbInv.writeResult {cfg : Config} {s : State} (hb : HbInv cfg s) {id : Nat} (hid : id < cfg.workers)
    (hns : phaseOf s.consumers id ≠ .start)
    (hpf : ∀ v, s.producer = .waiting v ∨ s.producer = .beforeComplete v →
      PastFunc cfg v (phaseOf s.consumers id) → s.mark id = s.ck (id + 1) (id + 1)) :
    HbInv cfg { s with resultSlots := s.resultSlots.modify id (·.write (id + 1) s.clocks[id + 1]!) } := by
  have hsize : id < s.resultSlots.size := by rw [hb.resultSlots_size]; exact hid
  have hslot : ∀ j, (s.resultSlots.modify id (·.write (id + 1) s.clocks[id + 1]!))[j]! =
      if j = id then s.resultSlots[id]!.write (id + 1) s.clocks[id + 1]! else s.resultSlots[j]! := by
    intro j
    rw [getElem!_modify]
    by_cases hji : j = id
    · subst hji; rw [if_pos ⟨rfl, hsize⟩, if_pos rfl]
    · rw [if_neg (fun h => hji h.1.symm), if_neg hji]
  refine ⟨hb.clocks_size, hb.clock_size, hb.probeRel_size, hb.rel_size, hb.jobReads_size,
    by rw [Array.size_modify]; exact hb.resultSlots_size, ?_, hb.jobReads_zero, hb.mark_le, hb.job_write, ?_,
    ?_, ?_, ?_, ?_, hb.producerKnows, hb.probeKnows, hb.finisherKnows, hb.tree⟩
  · intro j hj
    show (s.resultSlots.modify id _)[j]!.reads = _
    rw [hslot]
    split
    · rw [Slot.write_reads, hb.resultReads id hid, VC.size_zero]
    · exact hb.resultReads j hj
  · intro j hj tw c h
    change (s.resultSlots.modify id _)[j]!.lastWrite = _ at h
    rw [hslot] at h
    split at h
    · rename_i hji
      subst hji
      rw [Slot.write_lastWrite] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Or.inr rfl, Nat.le_refl _⟩
    · exact hb.result_write j hj tw c h
  · intro j hj hph
    show (s.resultSlots.modify id _)[j]!.lastWrite = none
    rw [hslot]
    split
    · rename_i hji; subst hji; exact absurd hph hns
    · exact hb.start j hj hph
  · intro j hj v hph
    change _ ∧ ∀ c, (s.resultSlots.modify id _)[j]!.lastWrite = some (0, c) → _
    rw [hslot]
    split
    · refine ⟨(hb.beforeFunc j hj v hph).1, fun c h => ?_⟩
      rw [Slot.write_lastWrite] at h
      simp at h
    · exact hb.beforeFunc j hj v hph
  · intro v hp
    refine ⟨(hb.published v hp).1, fun j hj c h => ?_⟩
    change (s.resultSlots.modify id _)[j]!.lastWrite = _ at h
    rw [hslot] at h
    split at h
    · rw [Slot.write_lastWrite] at h; simp at h
    · exact (hb.published v hp).2 j hj c h
  · intro v hp j hj hpf'
    show (s.resultSlots.modify id _)[j]!.lastWrite = some (j + 1, s.mark j)
    rw [hslot]
    split
    · rename_i hji
      subst hji
      rw [Slot.write_lastWrite, hpf v hp hpf']
      rfl
    · exact hb.resultMark v hp j hj hpf'

/-- A consumer about to run `func` reading the job slot. -/
theorem HbInv.readJob {cfg : Config} {s : State} (hb : HbInv cfg s) (hinv : Inv cfg s) {id : Nat}
    (hid : id < cfg.workers) {v : Nat} (hph : phaseOf s.consumers id = .beforeFunc v) :
    HbInv cfg { s with jobSlot := s.jobSlot.read (id + 1) s.clocks[id + 1]! } := by
  obtain ⟨hv, hp, hprobe⟩ := hinv.beforeFunc_active hid hph
  have hsize : id + 1 < s.jobSlot.reads.size := by rw [hb.jobReads_size]; omega
  have hmark : ∀ j, ({ s with jobSlot := s.jobSlot.read (id + 1) s.clocks[id + 1]! } : State).mark j =
      if j = id then s.ck (id + 1) (id + 1) else s.mark j := by
    intro j
    show (s.jobSlot.read (id + 1) s.clocks[id + 1]!).reads[j + 1]! = _
    rw [Slot.read_reads, getElem!_setIfInBounds]
    by_cases hji : j = id
    · subst hji; rw [if_pos ⟨rfl, hsize⟩, if_pos rfl]; rfl
    · rw [if_neg (fun h => hji (by omega)), if_neg hji]; rfl
  have hnp : ¬ PastLeaf cfg (s.producer.version cfg) (phaseOf s.consumers) id := by
    unfold PastLeaf
    rw [hph]
    simp only [leafDone]
    omega
  refine ⟨hb.clocks_size, hb.clock_size, hb.probeRel_size, hb.rel_size, ?_, hb.resultSlots_size, hb.resultReads,
    ?_, ?_, hb.job_write, hb.result_write, hb.start, hb.beforeFunc, hb.published, ?_, ?_, ?_, ?_, ?_⟩
  · show (s.jobSlot.read (id + 1) s.clocks[id + 1]!).reads.size = _
    rw [Slot.read_reads, Array.size_setIfInBounds]; exact hb.jobReads_size
  · show (s.jobSlot.read (id + 1) s.clocks[id + 1]!).reads[0]! = 0
    rw [Slot.read_reads, getElem!_setIfInBounds, if_neg (fun h => by omega)]
    exact hb.jobReads_zero
  · intro j hj
    rw [hmark]
    split
    · rename_i hji; subst hji; exact Nat.le_refl _
    · exact hb.mark_le j hj
  · intro v' hp' j hj hpf
    rw [hmark]
    split
    · rename_i hji
      subst hji
      exfalso
      rcases hpf with h1 | ⟨c, h1⟩ | h1 | h1 <;> rw [hph] at h1
      · cases h1
      · cases h1
      · cases h1
      · exact absurd h1 (not_finished_of_ne nofun nofun)
    · exact hb.resultMark v' hp' j hj hpf
  · intro v' hp'
    exfalso
    rw [hp] at hp'
    rcases hp' with h | h | h <;> cases h
  · intro v' hp' hprobe'
    exfalso
    rw [hp] at hp'
    injection hp' with hp'
    change s.probe = _ at hprobe'
    omega
  · intro i hi v' hph' j hj hpast
    rw [hmark]
    split
    · rename_i hji
      subst hji
      exfalso
      obtain ⟨hv', -, -, -⟩ := hinv.active hi (Or.inr (Or.inr hph'))
      subst hv'
      exact hnp hpast
    · exact hb.finisherKnows i hi v' hph' j hj hpast
  · refine hb.tree.mark_congr fun j hp => ?_
    rw [hmark]
    split
    · rename_i hji; subst hji; exact absurd hp hnp
    · rfl


/-! ## The walk step -/

theorem prefix_append_singleton_of_ne {p q : List Nat} (hpre : p <+: q) (hne : p ≠ q) :
    ∃ k, (p ++ [k]) <+: q := by
  obtain ⟨r, hr⟩ := hpre
  cases r with
  | nil => exact absurd (by simpa using hr) hne
  | cons k r' => exact ⟨k, ⟨r', by rw [← hr]; simp⟩⟩

theorem digit_unique {p q : List Nat} {k k' : Nat} (h : (p ++ [k]) <+: q) (h' : (p ++ [k']) <+: q) : k = k' :=
  append_singleton_inj ((List.prefix_of_prefix_length_le h h' (by simp)).eq_of_length (by simp))

/-- The tree part of the invariant survives a walker's `fetch_add`, and the
walker that completes the version knows every result write. -/
theorem treeHb_walk {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (htree : TreeInv cfg V phase t) (hw : WalkInv cfg V phase t)
    {clocks : Array VC} {mark : Nat → Nat} (hb : TreeHb cfg V phase t clocks mark)
    (hcsize : clocks.size = cfg.workers + 1)
    (hcs : ∀ u, u < cfg.workers + 1 → clocks[u]!.size = cfg.workers + 1)
    (hrels : ∀ q n, t.get q = some n → n.rel.size = cfg.workers + 1)
    (hmark : ∀ j, j < cfg.workers → mark j ≤ clocks[j + 1]![j + 1]!)
    (hV : V < cfg.count) {ord : MemOrd} (hacq : ord.acquires = true) (hrel : ord.releases = true)
    {id : Nat} (hid : id < cfg.workers) {c : Cursor} (hph : phase id = .walk V c)
    (hnf : ¬ PastLeaf cfg V phase id → ∀ q m, t.get q = some m → m.lo ≤ id → id < m.hi → m.version ≠ V + 1)
    {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next}
    (hwalk : t.walk cfg c V clocks[id + 1]! ord = .ok t' vc' rmw next) :
    TreeHb cfg V (upd phase id (nextPhase cfg V next)) t' (clocks.set! (id + 1) vc') mark ∧
      (next = .finished → ∀ j, j < cfg.workers → PastLeaf cfg V (upd phase id (nextPhase cfg V next)) j →
        mark j ≤ vc'[j + 1]!) := by
  obtain ⟨n, hn, hnv, -, -, -, hle, ⟨f, hf, ht'⟩, ⟨n', hn', hlo, hhi, hch, hnotfull, hfill⟩, hfin, hstop, hcont⟩ :=
    walk_spec hwalk
  obtain ⟨n₀, hn₀, hvc', n'', hn'', hrel''⟩ := walk_clocks hwalk
  rw [hn] at hn₀
  have := Option.some.inj hn₀
  subst this
  rw [hn'] at hn''
  have := Option.some.inj hn''
  subst this
  -- clocks
  have hvcs : clocks[id + 1]!.size = cfg.workers + 1 := hcs _ (by omega)
  have hrs : clocks[id + 1]!.size = n.rel.size := by rw [hvcs, hrels _ _ hn]
  have hvc_le : ∀ u, clocks[id + 1]![u]! ≤ vc'[u]! := fun u => by rw [hvc']; exact rmwClocks_vc_le hrs ord u
  have hrel_acq : ∀ u, n.rel[u]! ≤ vc'[u]! := fun u => by rw [hvc']; exact rmwClocks_acquires hrs hacq u
  have hrel_le : ∀ u, n.rel[u]! ≤ n'.rel[u]! := fun u => by rw [hrel'']; exact rmwClocks_rel_le hrs ord u
  have hvc'_rel : ∀ u, vc'[u]! ≤ n'.rel[u]! := fun u => by
    rw [hrel'', hvc']; exact rmwClocks_releases hrs hrel u
  have hck_id : (clocks.set! (id + 1) vc')[id + 1]! = vc' := by
    rw [Array.set!_eq_setIfInBounds, getElem!_setIfInBounds, if_pos ⟨rfl, by omega⟩]
  have hck_ne : ∀ u, u ≠ id + 1 → (clocks.set! (id + 1) vc')[u]! = clocks[u]! := fun u hu => by
    rw [Array.set!_eq_setIfInBounds, getElem!_setIfInBounds, if_neg (fun h => hu h.1.symm)]
  -- the leaf and the node under the cursor
  obtain ⟨leaf, hleaf, hlnil, hl1, hl2⟩ := htree.leaves id hid
  have hpre := htree.walkers id hid V c hph
  have hnd := not_dead_of_walker htree hid hph hn
  have hwfn := Wf.get _ hwf hn
  -- phases after the step
  have hpast' : ∀ j, j ≠ id →
      (PastLeaf cfg V (upd phase id (nextPhase cfg V next)) j ↔ PastLeaf cfg V phase j) :=
    fun j hj => pastLeaf_upd_ne hj
  have hnext_ne : ∀ c', next = .continue c' → c'.path ≠ (Cursor.start cfg id).path := by
    intro c' hc' heq
    obtain ⟨rfl, -, -, hnil⟩ := hcont c' hc'
    simp only at heq
    have h1 := hpre.length_le
    have h2 : c.path.dropLast.length = c.path.length - 1 := List.length_dropLast
    have h3 : 0 < c.path.length := List.length_pos_iff.mpr hnil
    rw [← heq] at h1
    omega
  have hpast_id' : PastLeaf cfg V (upd phase id (nextPhase cfg V next)) id := by
    rw [pastLeaf_upd_self]
    exact leafDone_nextPhase cfg V next _ hV hnext_ne
  have hpast_id : PastLeaf cfg V phase id ↔ c.path ≠ (Cursor.start cfg id).path := by
    unfold PastLeaf
    rw [hph, leafDone_walk]
    constructor
    · intro h heq; rw [if_pos (by simp [heq])] at h; omega
    · intro hne; rw [if_neg (by simpa using hne)]
  have hpast_of : ∀ j, PastLeaf cfg V (upd phase id (nextPhase cfg V next)) j → ¬ PastLeaf cfg V phase j →
      j = id ∧ c.path = (Cursor.start cfg id).path := by
    intro j hp hnp
    by_cases hji : j = id
    · subst hji
      refine ⟨rfl, ?_⟩
      by_cases hne : c.path = (Cursor.start cfg j).path
      · exact hne
      · exact absurd (hpast_id.mpr hne) hnp
    · exact absurd ((hpast' j hji).mp hp) hnp
  have hK1 : mark id ≤ vc'[id + 1]! := Nat.le_trans (hmark id hid) (hvc_le _)
  have hother_walk : ∀ i, i ≠ id → ∀ c', upd phase id (nextPhase cfg V next) i = .walk V c' →
      phase i = .walk V c' :=
    fun i hi c' h => by rw [upd_ne _ _ _ hi] at h; exact h
  have hget' : ∀ q, q ≠ c.path → ∀ m', t'.get q = some m' →
      ∃ m, t.get q = some m ∧ m'.fields = m.fields ∧ m'.rel = m.rel :=
    fun q hq m' hm' => get_modifyAt_ne' hf hq (by rw [← ht']; exact hm')
  have hshape : ∀ r, (t'.get r).map Tree.shape = (t.get r).map Tree.shape := fun r => by
    rw [ht']; exact Tree.get_modifyAt_shape f hf t c.path r
  have hchild_ne : ∀ i, i < cfg.workers → ∀ c', phase i = .walk V c' → ∀ k,
      (c'.path ++ [k]) <+: (Cursor.start cfg i).path → c'.path ++ [k] ≠ c.path := by
    intro i hi c' hc' k hk heq
    obtain ⟨ch, hch, hchv, -⟩ := hw.carries i hi c' hc' k hk
    rw [heq, hn] at hch
    have := Option.some.inj hch
    subst this
    omega
  -- what the walker knows
  have hKL : c.path = (Cursor.start cfg id).path → ∀ j, n.lo ≤ j → j < n.hi →
      PastLeaf cfg V (upd phase id (nextPhase cfg V next)) j → mark j ≤ vc'[j + 1]! := by
    intro hL j hlo' hhi' hp
    have hnil : n.children = [] := by rw [hL, hleaf] at hn; rw [← Option.some.inj hn]; exact hlnil
    by_cases hji : j = id
    · subst hji; exact hK1
    · exact Nat.le_trans (hb.leaf c.path n hn hnil j hlo' hhi' ((hpast' j hji).mp hp)) (hrel_acq _)
  have hKI : c.path ≠ (Cursor.start cfg id).path → ∀ k, (c.path ++ [k]) <+: (Cursor.start cfg id).path →
      ∀ ch, t.get (c.path ++ [k]) = some ch → ∀ j, ch.lo ≤ j → j < ch.hi →
      PastLeaf cfg V (upd phase id (nextPhase cfg V next)) j → mark j ≤ vc'[j + 1]! := by
    intro hL k hk ch hch j hlo' hhi' hp
    have hpj : PastLeaf cfg V phase j := by
      by_cases hji : j = id
      · subst hji; exact hpast_id.mpr hL
      · exact (hpast' j hji).mp hp
    exact Nat.le_trans (hb.walker id hid c hph k hk ch hch j hlo' hhi' hpj) (hvc_le _)
  have hnleaf : c.path ≠ (Cursor.start cfg id).path → n.children ≠ [] := fun hL hnil =>
    hL (Tree.prefix_leaf hn hnil hpre hleaf).symm
  have hKfull : n.finished + c.mergeAmount = n.size → ∀ j, n.lo ≤ j → j < n.hi →
      PastLeaf cfg V (upd phase id (nextPhase cfg V next)) j → mark j ≤ vc'[j + 1]! := by
    intro hfull j hlo' hhi' hp
    by_cases hL : c.path = (Cursor.start cfg id).path
    · exact hKL hL j hlo' hhi' hp
    · have hne := hnleaf hL
      obtain ⟨-, hsum⟩ := (htree.nodes _ n hn).live hne hnd
      have hfb := filledBelow_le hwf hn hne
      have hcarry := carryOf_le_carriedTo cfg.workers c.path phase id hid
      rw [hph, carryOf_walk, if_pos rfl] at hcarry
      have hfbeq : filledBelow t c.path n = n.size := by omega
      have hcarried : carriedTo cfg.workers c.path phase = c.mergeAmount := by omega
      obtain ⟨ch, hchmem, hchlo, hchhi⟩ := tiles_cover n.children n.lo n.hi j (hwfn.tiles hne)
        (fun x hx => (hwfn.children_wf x hx).lo_lt_hi) hlo' hhi'
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hchmem
      have hch : t.get (c.path ++ [k]) = some ch := by rw [get_child hn]; exact hk
      have hchv : ch.version = V + 1 := by
        rw [← hnv]; exact all_filled_of_filledBelow_eq hwf hn hne hfbeq k ch hch
      by_cases hkk : (c.path ++ [k]) <+: (Cursor.start cfg id).path
      · exact hKI hL k hkk ch hch j hchlo hchhi hp
      · have hnc : ¬ Carrier cfg V phase c.path k := by
          rintro ⟨i', hi', c', hc', hcp, hk'⟩
          by_cases hii : i' = id
          · subst hii
            rw [hph] at hc'
            obtain ⟨-, rfl⟩ := ConsumerPhase.walk.inj hc'
            exact hkk hk'
          · have h1 := two_carry_le cfg.workers c.path phase (Ne.symm hii) hid hi'
            rw [hph, hc', carryOf_walk, carryOf_walk, if_pos rfl, if_pos hcp, hcarried] at h1
            have h2 := htree.carry_pos i' hi' V c' hc'
            omega
        have hpj : PastLeaf cfg V phase j := by
          by_cases hji : j = id
          · subst hji; exact hpast_id.mpr hL
          · exact (hpast' j hji).mp hp
        exact Nat.le_trans (hb.counted c.path n hn hnv hnd k ch hch hchv hnc j hchlo hchhi hpj) (hrel_acq _)
  have hself : ∀ k, (c.path.dropLast ++ [k]) <+: (Cursor.start cfg id).path → c.path ≠ [] →
      c.path.dropLast ++ [k] = c.path := by
    intro k hk hnil
    rw [digit_eq_getLast hnil hpre hk, List.dropLast_concat_getLast hnil]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- filled
    intro q m' hm' hver j hlo' hhi' hp
    by_cases hq : q = c.path
    · subst hq
      rw [hn'] at hm'
      have := Option.some.inj hm'
      subst this
      have hfull : n.finished + c.mergeAmount = n.size := by
        by_cases hlt : n.finished + c.mergeAmount < n.size
        · have := (hnotfull hlt).1; omega
        · omega
      rw [hlo] at hlo'
      rw [hhi] at hhi'
      exact Nat.le_trans (hKfull hfull j hlo' hhi' hp) (hvc'_rel _)
    · obtain ⟨m, hm, hfields, hrelm⟩ := hget' q hq m' hm'
      obtain ⟨h1, -, h3, h4, -⟩ := Tree.fields_inj hfields
      rw [hrelm]
      rw [h3] at hlo'
      rw [h4] at hhi'
      rw [h1] at hver
      by_cases hpj : PastLeaf cfg V phase j
      · exact hb.filled q m hm hver j hlo' hhi' hpj
      · obtain ⟨rfl, hL⟩ := hpast_of j hp hpj
        exact absurd hver (hnf hpj q m hm hlo' hhi')
  · -- leaf
    intro q m' hm' hnil j hlo' hhi' hp
    by_cases hq : q = c.path
    · subst hq
      rw [hn'] at hm'
      have := Option.some.inj hm'
      subst this
      rw [hch] at hnil
      by_cases hL : c.path = (Cursor.start cfg id).path
      · rw [hlo] at hlo'
        rw [hhi] at hhi'
        exact Nat.le_trans (hKL hL j hlo' hhi' hp) (hvc'_rel _)
      · exact absurd hnil (hnleaf hL)
    · obtain ⟨m, hm, hfields, hrelm⟩ := hget' q hq m' hm'
      obtain ⟨-, -, h3, h4, h5⟩ := Tree.fields_inj hfields
      rw [hrelm]
      rw [h3] at hlo'
      rw [h4] at hhi'
      have hmnil : m.children = [] := by
        rw [hnil] at h5
        exact List.length_eq_zero_iff.mp h5.symm
      by_cases hpj : PastLeaf cfg V phase j
      · exact hb.leaf q m hm hmnil j hlo' hhi' hpj
      · obtain ⟨rfl, hL⟩ := hpast_of j hp hpj
        exact absurd (htree.leaf_unique q m hm hmnil j hlo' hhi') (by rw [← hL]; exact hq)
  · -- counted
    intro q m' hm' hver hnd' k ch' hch' hchv hnc j hlo' hhi' hp
    by_cases hq : q = c.path
    · subst hq
      rw [hn'] at hm'
      have := Option.some.inj hm'
      subst this
      have hlt : n.finished + c.mergeAmount < n.size := by
        by_cases hlt : n.finished + c.mergeAmount < n.size
        · exact hlt
        · have := (hfill (by omega)).1; omega
      by_cases hL : c.path = (Cursor.start cfg id).path
      · exfalso
        have hnil : n.children = [] := by rw [hL, hleaf] at hn; rw [← Option.some.inj hn]; exact hlnil
        rw [get_child hn', hch, hnil] at hch'
        simp at hch'
      · have hne : c.path ++ [k] ≠ c.path := append_singleton_ne _ _
        obtain ⟨ch, hch, hfields, -⟩ := hget' _ hne ch' hch'
        obtain ⟨h1, -, h3, h4, -⟩ := Tree.fields_inj hfields
        rw [h3] at hlo'
        rw [h4] at hhi'
        rw [h1] at hchv
        by_cases hkk : (c.path ++ [k]) <+: (Cursor.start cfg id).path
        · exact Nat.le_trans (hKI hL k hkk ch hch j hlo' hhi' hp) (hvc'_rel _)
        · have hnc' : ¬ Carrier cfg V phase c.path k := by
            rintro ⟨i', hi', c', hc', hcp, hk'⟩
            by_cases hii : i' = id
            · subst hii
              rw [hph] at hc'
              obtain ⟨-, rfl⟩ := ConsumerPhase.walk.inj hc'
              exact hkk hk'
            · exact hnc ⟨i', hi', c', by rw [upd_ne _ _ _ hii]; exact hc', hcp, hk'⟩
          have hpj : PastLeaf cfg V phase j := by
            by_cases hji : j = id
            · subst hji; exact hpast_id.mpr hL
            · exact (hpast' j hji).mp hp
          exact Nat.le_trans (hb.counted c.path n hn hnv hnd k ch hch hchv hnc' j hlo' hhi' hpj) (hrel_le _)
    · obtain ⟨m, hm, hfields, hrelm⟩ := hget' q hq m' hm'
      obtain ⟨h1, -, -, -, h5⟩ := Tree.fields_inj hfields
      rw [hrelm]
      rw [h1] at hver
      have hndm : ¬ deadAt cfg.workers t q m := fun hd => hnd' ((deadAt_of_shape hshape h5).mpr hd)
      by_cases hqk : q ++ [k] = c.path
      · -- the parent of the node under the cursor: its walker now carries the node
        exfalso
        rw [hqk, hn'] at hch'
        have := Option.some.inj hch'
        subst this
        have hfull : n.finished + c.mergeAmount = n.size := by
          by_cases hlt : n.finished + c.mergeAmount < n.size
          · have := (hnotfull hlt).1; omega
          · omega
        cases next with
        | stop => have := hstop.mp rfl; omega
        | finished =>
          obtain ⟨-, hW⟩ := hfin.mp rfl
          apply hndm
          refine ⟨k, ?_, n, by rw [hqk]; exact hn, hW⟩
          have := get_child hm k
          rw [hqk, hn] at this
          exact lt_length_of_getElem?' _ _ _ this.symm
        | «continue» c' =>
          obtain ⟨rfl, -, -, -⟩ := hcont c' rfl
          apply hnc
          refine ⟨id, hid, ⟨c.path.dropLast, n.size⟩, by rw [upd_self]; rfl, ?_, by rw [hqk]; exact hpre⟩
          show c.path.dropLast = q
          rw [← hqk, List.dropLast_concat]
      · obtain ⟨ch, hch, hfields', -⟩ := hget' _ hqk ch' hch'
        obtain ⟨h1', -, h3', h4', -⟩ := Tree.fields_inj hfields'
        rw [h3'] at hlo'
        rw [h4'] at hhi'
        rw [h1'] at hchv
        have hnc' : ¬ Carrier cfg V phase q k := by
          rintro ⟨i', hi', c', hc', hcp, hk'⟩
          by_cases hii : i' = id
          · subst hii
            rw [hph] at hc'
            obtain ⟨-, rfl⟩ := ConsumerPhase.walk.inj hc'
            exact hq hcp.symm
          · exact hnc ⟨i', hi', c', by rw [upd_ne _ _ _ hii]; exact hc', hcp, hk'⟩
        by_cases hpj : PastLeaf cfg V phase j
        · exact hb.counted q m hm hver hndm k ch hch hchv hnc' j hlo' hhi' hpj
        · obtain ⟨rfl, hL⟩ := hpast_of j hp hpj
          exact absurd hchv (hnf hpj _ ch hch hlo' hhi')
  · -- walker
    intro i hi c'' hc'' k hk ch' hch' j hlo' hhi' hp
    by_cases hii : i = id
    · subst hii
      rw [upd_self] at hc''
      obtain ⟨rfl, -⟩ := nextPhase_walk hc''
      obtain ⟨rfl, hfull, -, hnil⟩ := hcont c'' rfl
      simp only at hk
      rw [hself k hk hnil] at hch'
      rw [hn'] at hch'
      have := Option.some.inj hch'
      subst this
      rw [hlo] at hlo'
      rw [hhi] at hhi'
      rw [hck_id]
      exact hKfull hfull j hlo' hhi' hp
    · have hc' := hother_walk i hii c'' hc''
      rw [hck_ne _ (fun h => hii (by omega))]
      obtain ⟨ch, hch, hfields, -⟩ := hget' _ (hchild_ne i hi c'' hc' k hk) ch' hch'
      obtain ⟨h1, -, h3, h4, -⟩ := Tree.fields_inj hfields
      rw [h3] at hlo'
      rw [h4] at hhi'
      by_cases hpj : PastLeaf cfg V phase j
      · exact hb.walker i hi c'' hc' k hk ch hch j hlo' hhi' hpj
      · obtain ⟨rfl, hL⟩ := hpast_of j hp hpj
        obtain ⟨ch₂, hch₂, hchv, -⟩ := hw.carries i hi c'' hc' k hk
        rw [hch] at hch₂
        have := Option.some.inj hch₂
        subst this
        exact absurd hchv (hnf hpj _ ch hch hlo' hhi')
  · -- the finisher knows everything
    intro hnext j hj hp
    obtain ⟨hfull, hW⟩ := hfin.mp hnext
    have hlt := hwfn.lo_lt_hi
    have hle' := hwfn.hi_le
    simp only [Tree.size] at hW
    exact hKfull hfull j (by omega) (by omega) hp


/-! ## More helpers -/

theorem Inv.congr {cfg : Config} {s s' : State} (h : Inv cfg s) (h1 : s'.probe = s.probe)
    (h2 : s'.tree = s.tree) (h3 : s'.producer = s.producer) (h4 : s'.consumers = s.consumers) : Inv cfg s' := by
  show InvAt cfg s'.probe s'.tree s'.producer (s'.producer.version cfg) s'.consumers
  rw [h1, h2, h3, h4]
  exact h

theorem rmwProbe_unchanged' (s : State) (t : Nat) (o : MemOrd) :
    (s.rmwProbe t o).jobSlot = s.jobSlot ∧ (s.rmwProbe t o).resultSlots = s.resultSlots ∧
      (s.rmwProbe t o).tree = s.tree ∧ (s.rmwProbe t o).consumers = s.consumers ∧
      (s.rmwProbe t o).producer = s.producer ∧ (s.rmwProbe t o).probe = s.probe := by
  unfold State.rmwProbe
  split <;> split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mark_of_jobSlot {s s' : State} (h : s'.jobSlot = s.jobSlot) : s'.mark = s.mark := by
  funext j
  unfold State.mark
  rw [h]

/-- A release on the probe puts the thread's clock into the probe's release clock. -/
theorem rmwProbe_release_le (s : State) {t : Nat} (hsize : s.clocks[t]!.size = s.probeRel.size) {ord : MemOrd}
    (hrel : ord.releases = true) (u : Nat) : s.ck t u ≤ (s.rmwProbe t ord).probeRel[u]! := by
  unfold State.rmwProbe
  simp only [hrel, ↓reduceIte]
  split
  · refine Nat.le_trans (acquireProbe_ck_le s (Nat.le_of_eq hsize) t u) (releaseProbe_ck_le _ ?_ u)
    rw [acquireProbe_clock_size s hsize t]
    exact Nat.le_of_eq hsize
  · exact releaseProbe_ck_le s (Nat.le_of_eq hsize) u

theorem pastFunc_start {cfg : Config} {v : Nat} : ¬ PastFunc cfg v .start := by
  rintro (h | ⟨c, h⟩ | h | h | ⟨h, -⟩) <;> cases h

theorem pastFunc_initializing {cfg : Config} {v : Nat} : ¬ PastFunc cfg v .initializing := by
  rintro (h | ⟨c, h⟩ | h | h | ⟨h, -⟩) <;> cases h

theorem pastFunc_beforeFunc {cfg : Config} {v w : Nat} : ¬ PastFunc cfg v (.beforeFunc w) := by
  rintro (h | ⟨c, h⟩ | h | h | ⟨h, -⟩) <;> cases h

theorem nextPhase_ne_start (cfg : Config) (v : Nat) (next : Next) : nextPhase cfg v next ≠ .start := by
  cases next <;> simp only [nextPhase, ne_eq, reduceCtorEq, not_false_eq_true]
  unfold nextConsumer; split <;> nofun

theorem nextPhase_ne_beforeFunc (cfg : Config) (v : Nat) (next : Next) (w : Nat) :
    nextPhase cfg v next ≠ .beforeFunc w := by
  cases next <;> simp only [nextPhase, ne_eq, reduceCtorEq, not_false_eq_true]
  unfold nextConsumer; split <;> nofun

theorem nextConsumer_ne_walk (cfg : Config) (v w : Nat) (c : Cursor) : nextConsumer cfg v ≠ .walk w c := by
  unfold nextConsumer; split <;> nofun

theorem phaseOf_of_ge {cs : Array ConsumerPhase} {j : Nat} (h : cs.size ≤ j) : phaseOf cs j = .start := by
  simp [phaseOf, Array.getElem?_eq_none_iff.mpr h]

/-- A phase change of a consumer that is not walking, into a phase that is
not walking, with the same leaf count. -/
theorem TreeHb.upd_simple {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    {clocks : Array VC} {mark : Nat → Nat} (h : TreeHb cfg V phase t clocks mark) {id : Nat} {ph' : ConsumerPhase}
    (hld : leafDone (Cursor.start cfg id).path cfg.count ph' =
      leafDone (Cursor.start cfg id).path cfg.count (phase id))
    (hnw : ∀ v c, ph' ≠ .walk v c) (hnw0 : ∀ c, phase id ≠ .walk V c) :
    TreeHb cfg V (upd phase id ph') t clocks mark := by
  refine h.mono (fun j hp => ?_) (fun p k hc => ?_) (fun i _ c hc => ?_) (fun _ _ => Nat.le_refl _)
  · by_cases hji : j = id
    · subst hji
      rw [pastLeaf_upd_self, hld] at hp
      exact hp
    · exact (pastLeaf_upd_ne hji).mp hp
  · obtain ⟨i, hi, c, hc, hcp, hk⟩ := hc
    have hii : i ≠ id := fun e => hnw0 c (e ▸ hc)
    exact ⟨i, hi, c, by rw [upd_ne _ _ _ hii]; exact hc, hcp, hk⟩
  · by_cases hii : i = id
    · subst hii; rw [upd_self] at hc; exact absurd hc (hnw _ _)
    · rw [upd_ne _ _ _ hii] at hc; exact Or.inl hc

/-- A consumer leaving `func` and starting its walk at its leaf. -/
theorem TreeHb.upd_startWalk {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    {clocks : Array VC} {mark : Nat → Nat} (h : TreeHb cfg V phase t clocks mark) {id : Nat}
    (hph : phase id = .inFunc V) :
    TreeHb cfg V (upd phase id (.walk V (Cursor.start cfg id))) t clocks mark := by
  refine h.mono (fun j hp => ?_) (fun p k hc => ?_) (fun i _ c hc => ?_) (fun _ _ => Nat.le_refl _)
  · by_cases hji : j = id
    · subst hji
      rw [pastLeaf_upd_self, leafDone_walk] at hp
      simp at hp
    · exact (pastLeaf_upd_ne hji).mp hp
  · obtain ⟨i, hi, c, hc, hcp, hk⟩ := hc
    have hii : i ≠ id := fun e => by rw [e, hph] at hc; cases hc
    exact ⟨i, hi, c, by rw [upd_ne _ _ _ hii]; exact hc, hcp, hk⟩
  · by_cases hii : i = id
    · subst hii
      rw [upd_self] at hc
      injection hc with _ hc
      exact Or.inr (by rw [← hc])
    · rw [upd_ne _ _ _ hii] at hc; exact Or.inl hc

theorem mark_read {cfg : Config} {s : State} (hb : HbInv cfg s) {id : Nat} (hid : id < cfg.workers) (j : Nat) :
    ({ s with jobSlot := s.jobSlot.read (id + 1) s.clocks[id + 1]! } : State).mark j =
      if j = id then s.ck (id + 1) (id + 1) else s.mark j := by
  have hsize : id + 1 < s.jobSlot.reads.size := by rw [hb.jobReads_size]; omega
  show (s.jobSlot.read (id + 1) s.clocks[id + 1]!).reads[j + 1]! = _
  rw [Slot.read_reads, getElem!_setIfInBounds]
  by_cases hji : j = id
  · subst hji; rw [if_pos ⟨rfl, hsize⟩, if_pos rfl]; rfl
  · rw [if_neg (fun h => hji (by omega)), if_neg hji]; rfl

/-! ## Producer moves -/

theorem HbInv.producer_move {cfg : Config} {s : State} (hb : HbInv cfg s) (p' : ProducerPhase) (pr : Nat)
    (hpub : ∀ v, p' = .waiting v →
      (∀ c, s.jobSlot.lastWrite = some (0, c) → c ≤ s.probeRel[0]!) ∧
      (∀ j, j < cfg.workers → ∀ c, s.resultSlots[j]!.lastWrite = some (0, c) → c ≤ s.probeRel[0]!))
    (hrm : ∀ v, p' = .waiting v ∨ p' = .beforeComplete v → ∀ j, j < cfg.workers →
      PastFunc cfg v (phaseOf s.consumers j) → s.resultSlots[j]!.lastWrite = some (j + 1, s.mark j))
    (hpk : ∀ v, p' = .beforeWrite v ∨ p' = .beforeComplete v ∨ p' = .completing v →
      ∀ j, j < cfg.workers → s.mark j ≤ s.ck 0 (j + 1))
    (hprk : ∀ v, p' = .waiting v → pr = 2 * v + 2 → ∀ j, j < cfg.workers → s.mark j ≤ s.probeRel[j + 1]!)
    (htree : TreeHb cfg (p'.version cfg) (phaseOf s.consumers) s.tree s.clocks s.mark) :
    HbInv cfg { s with producer := p', probe := pr } :=
  ⟨hb.clocks_size, hb.clock_size, hb.probeRel_size, hb.rel_size, hb.jobReads_size, hb.resultSlots_size,
    hb.resultReads, hb.jobReads_zero, hb.mark_le, hb.job_write, hb.result_write, hb.start, hb.beforeFunc,
    hpub, hrm, hpk, hprk, hb.finisherKnows, htree⟩

/-- The producer's job write. -/
theorem HbInv.writeJob {cfg : Config} {s : State} (hinv : Inv cfg s) (hb : HbInv cfg s) {v : Nat}
    (hp : s.producer = .beforeWrite v) :
    HbInv cfg { s with jobSlot := s.jobSlot.write 0 s.clocks[0]!, producer := .writing v, job := none } := by
  have hinv' : InvAt cfg s.probe s.tree (.beforeWrite v) v s.consumers := hinv.at hp
  have hprobe : s.probe = 2 * v := hinv'.probeOk
  have hmark : ∀ j, State.mark { s with jobSlot := s.jobSlot.write 0 s.clocks[0]!, producer := .writing v, job := none } j = 0 := fun j => VC.getElem!_zero _ _
  refine ⟨hb.clocks_size, hb.clock_size, hb.probeRel_size, hb.rel_size, ?_, hb.resultSlots_size, hb.resultReads,
    VC.getElem!_zero _ _, fun j _ => (by rw [hmark]; exact Nat.zero_le _), ?_, hb.result_write, hb.start, ?_,
    fun v' h => (by cases h), fun v' h => (by rcases h with h | h <;> cases h),
    fun v' h => (by rcases h with h | h | h <;> cases h), fun v' h => (by cases h),
    fun _ _ _ _ j _ _ => (by rw [hmark]; exact Nat.zero_le _), TreeHb.of_mark_zero hmark⟩
  · show (VC.zero s.jobSlot.reads.size).size = _
    rw [VC.size_zero]; exact hb.jobReads_size
  · intro tw c h
    simp only [Slot.write_lastWrite, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, Nat.le_refl _⟩
  · intro j hj v' hph
    exfalso
    rcases (hinv'.consumers j hj).1 hprobe with h1 | ⟨-, h1 | h1⟩ | ⟨-, h1⟩ <;> rw [hph] at h1 <;> cases h1

/-- The producer's `complete`. -/
theorem HbInv.complete {cfg : Config} {s s₁ : State} (hinv : Inv cfg s) (hb : HbInv cfg s) {v : Nat}
    (hp : s.producer = .beforeComplete v)
    (h1 : s₁.resultSlots.size = s.resultSlots.size)
    (h2 : ∀ j, j < s.resultSlots.size → s₁.resultSlots[j]! = s.resultSlots[j]!.write 0 s.clocks[0]!)
    (h3 : s₁.clocks = s.clocks) (h4 : s₁.probeRel = s.probeRel) (h5 : s₁.jobSlot = s.jobSlot)
    (h6 : s₁.tree = s.tree) (h7 : s₁.consumers = s.consumers) :
    HbInv cfg { s₁ with producer := .completing v } := by
  have hinv' : InvAt cfg s.probe s.tree (.beforeComplete v) v s.consumers := hinv.at hp
  have hprobe : s.probe = 2 * v + 2 := hinv'.probeOk
  have hall := hinv'.all_finished hprobe
  have hmark : s₁.mark = s.mark := mark_of_jobSlot h5
  have hck : s₁.ck = s.ck := by funext a b; unfold State.ck; rw [h3]
  have hslot : ∀ j, j < cfg.workers → s₁.resultSlots[j]! = s.resultSlots[j]!.write 0 s.clocks[0]! :=
    fun j hj => h2 j (by rw [hb.resultSlots_size]; exact hj)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun v' h => (by cases h),
    fun v' h => (by rcases h with h | h <;> cases h), ?_, fun v' h => (by cases h), ?_, ?_⟩
  · show s₁.clocks.size = _; rw [h3]; exact hb.clocks_size
  · intro u hu; show s₁.clocks[u]!.size = _; rw [h3]; exact hb.clock_size u hu
  · show s₁.probeRel.size = _; rw [h4]; exact hb.probeRel_size
  · intro q n hn; rw [show s₁.tree = s.tree from h6] at hn; exact hb.rel_size q n hn
  · show s₁.jobSlot.reads.size = _; rw [h5]; exact hb.jobReads_size
  · show s₁.resultSlots.size = _; rw [h1]; exact hb.resultSlots_size
  · intro j hj
    show s₁.resultSlots[j]!.reads = _
    rw [hslot j hj, Slot.write_reads, hb.resultReads j hj, VC.size_zero]
  · show s₁.jobSlot.reads[0]! = 0; rw [h5]; exact hb.jobReads_zero
  · intro j hj; show s₁.mark j ≤ s₁.ck _ _; rw [hmark, hck]; exact hb.mark_le j hj
  · intro tw c h; change s₁.jobSlot.lastWrite = _ at h; rw [h5] at h
    show _ ∧ c ≤ s₁.ck _ _; rw [hck]; exact hb.job_write tw c h
  · intro j hj tw c h
    change s₁.resultSlots[j]!.lastWrite = _ at h
    rw [hslot j hj, Slot.write_lastWrite] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨Or.inl rfl, ?_⟩
    show _ ≤ s₁.ck 0 0; rw [hck]; exact Nat.le_refl _
  · intro j hj hph
    change phaseOf s₁.consumers j = _ at hph
    rw [h7] at hph
    exact absurd hph (hall j hj).ne_start
  · intro j hj v' hph
    change phaseOf s₁.consumers j = _ at hph
    rw [h7] at hph
    exact absurd hph ((hall j hj).ne_beforeFunc v')
  · intro v' _ j hj
    show s₁.mark j ≤ s₁.ck 0 (j + 1)
    rw [hmark, hck]
    exact hb.producerKnows v (Or.inr (Or.inl hp)) j hj
  · intro i hi v' hph
    change phaseOf s₁.consumers i = _ at hph
    rw [h7] at hph
    exact absurd hph ((hall i hi).ne_finish v')
  · show TreeHb cfg v (phaseOf s₁.consumers) s₁.tree s₁.clocks s₁.mark
    rw [h7, h6, h3, hmark]
    have := hb.tree
    rw [hp] at this
    exact this

theorem step_producer_hbInv {cfg : Config} (hS : Strong cfg.orderings) {s s' : State} {ev : Option Event}
    (hinv : Inv cfg s) (hb : HbInv cfg s) (h : step cfg s .producer = .step s' ev) : HbInv cfg s' := by
  unfold step at h
  simp only at h
  split at h
  · rename_i s'' ev' hp
    simp only [Outcome.step.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply HbInv.tick
    unfold producerStep at hp
    have htree := hb.tree
    cases hpp : s.producer with
    | beforeWrite v =>
      rw [hpp] at hp
      dsimp only at hp
      unfold Outcome.accessing at hp
      split at hp
      · rename_i s₁ ha
        obtain rfl := access_writeJob_ok ha
        simp only [Outcome.step.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        exact hb.writeJob hinv hpp
      · cases hp
    | writing v =>
      rw [hpp] at hp
      dsimp only at hp
      simp only [Outcome.step.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      rw [hpp] at htree
      exact (hb.producer_move (.publish v) s.probe (fun _ h => by cases h)
        (fun _ h => by rcases h with h | h <;> cases h) (fun _ h => by rcases h with h | h | h <;> cases h)
        (fun _ h => by cases h) htree).setJob (some v)
    | publish v =>
      rw [hpp] at hp
      dsimp only at hp
      simp only [Outcome.step.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      have hinv' : InvAt cfg s.probe s.tree (.publish v) v s.consumers := hinv.at hpp
      have hprobe : s.probe = 2 * v := hinv'.probeOk
      have hlt : v < cfg.count := hinv'.version_lt nofun
      obtain ⟨hj, hr, ht, hc, hpr, -⟩ := rmwProbe_unchanged' s (threadIndex .producer) cfg.orderings.publish
      have hsize : s.clocks[0]!.size = s.probeRel.size := by
        rw [hb.clock_size 0 (by omega), hb.probeRel_size]
      have hrel := rmwProbe_release_le s hsize hS.publish
      have hb₁ := hb.rmwProbe (t := threadIndex .producer) (by simp [threadIndex]) cfg.orderings.publish
      refine hb₁.producer_move (.waiting v) (s.probe + 1) ?_ ?_ (fun _ h => by rcases h with h | h | h <;> cases h) ?_ ?_
      · intro v' hv'
        refine ⟨fun c hc => ?_, fun j hj c hc => ?_⟩
        · rw [hj] at hc
          exact Nat.le_trans (hb.job_write 0 c hc).2 (hrel 0)
        · rw [hr] at hc
          exact Nat.le_trans (hb.result_write j hj 0 c hc).2 (hrel 0)
      · intro v' hv' j hj hpf
        exfalso
        rcases hv' with hv' | hv' <;> cases hv'
        rw [hc] at hpf
        rcases (hinv'.consumers j hj).1 hprobe with h1 | ⟨-, h1 | h1⟩ | ⟨h2, h1⟩ <;> rw [h1] at hpf
        · rcases hpf with h | ⟨c, h⟩ | h | h | ⟨h, -⟩ <;> cases h
        · exact pastFunc_start hpf
        · exact pastFunc_initializing hpf
        · have h2' : v = cfg.count := h2
          omega
      · intro v' hv' hp2
        cases hv'
        omega
      · have := hb₁.tree
        rw [rmwProbe_unchanged' s _ _ |>.2.2.2.2.1, hpp] at this
        exact this
    | waiting v =>
      rw [hpp] at hp
      dsimp only at hp
      split at hp
      · rename_i heq
        rw [if_pos hS.producerFence] at hp
        simp only [Outcome.step.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        have hb₁ := hb.acquireProbe (t := threadIndex .producer) (by simp [threadIndex])
        rw [hpp] at htree
        have htree₁ := hb₁.tree
        change TreeHb cfg (s.producer.version cfg) _ _ _ _ at htree₁
        rw [hpp] at htree₁
        refine hb₁.producer_move (.beforeComplete v) s.probe (fun _ h => by cases h) ?_ ?_
          (fun _ h => by cases h) htree₁
        · intro v' hv' j hj hpf
          rcases hv' with hv' | hv' <;> cases hv'
          exact hb.resultMark v (Or.inl hpp) j hj hpf
        · intro v' hv' j hj
          rcases hv' with hv' | hv' | hv' <;> cases hv'
          refine Nat.le_trans (hb.probeKnows v hpp (by omega) j hj) ?_
          exact acquireProbe_ck_self s (by rw [hb.clocks_size]; simp [threadIndex])
            (Nat.le_of_eq (by rw [hb.probeRel_size, hb.clock_size _ (by simp [threadIndex])])) (j + 1)
      · cases hp
    | beforeComplete v =>
      rw [hpp] at hp
      dsimp only at hp
      unfold Outcome.accessing at hp
      split at hp
      · rename_i s₁ ha
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ := access_writeAll_ok ha
        simp only [Outcome.step.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        exact HbInv.complete hinv hb hpp h1 h2 h3 h4 h5 h6 h7
      · cases hp
    | completing v =>
      rw [hpp] at hp
      dsimp only at hp
      simp only [Outcome.step.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      have hinv' : InvAt cfg s.probe s.tree (.completing v) v s.consumers := hinv.at hpp
      have hprobe : s.probe = 2 * v + 2 := hinv'.probeOk
      have hlt : v < cfg.count := hinv'.version_lt nofun
      have hall := hinv'.all_finished hprobe
      have hV' : (nextProducer cfg v).version cfg = v + 1 := by
        unfold nextProducer; split <;> simp only [ProducerPhase.version] <;> omega
      have hnw : ∀ w, nextProducer cfg v ≠ .waiting w := fun w => by unfold nextProducer; split <;> nofun
      have hnb : ∀ w, nextProducer cfg v ≠ .beforeComplete w := fun w => by
        unfold nextProducer; split <;> nofun
      refine hb.producer_move (nextProducer cfg v) s.probe (fun w h => absurd h (hnw w))
        (fun w h => by rcases h with h | h; exact absurd h (hnw w); exact absurd h (hnb w)) ?_
        (fun w h => absurd h (hnw w)) ?_
      · intro _ _ j hj
        exact hb.producerKnows v (Or.inr (Or.inr hpp)) j hj
      · rw [hV']
        refine TreeHb.of_no_past fun j hpj => ?_
        unfold PastLeaf at hpj
        by_cases hj : j < cfg.workers
        · rcases hall j hj with h1 | ⟨h1, h2⟩ <;> rw [h1] at hpj <;> simp only [leafDone] at hpj <;> omega
        · rw [phaseOf_of_ge (by rw [hinv.size]; omega)] at hpj
          simp only [leafDone] at hpj
          omega
    | done =>
      rw [hpp] at hp
      cases hp
  · exfalso
    rename_i hne
    exact hne _ _ h

/-! ## Consumer moves: the walk -/

theorem HbInv.walk {cfg : Config} (hS : Strong cfg.orderings) {s : State} (hinv : Inv cfg s) (hw : WInv cfg s)
    (hb : HbInv cfg s) {id : Nat} (hid : id < cfg.workers) {v : Nat} {c : Cursor}
    (hph' : phaseOf s.consumers id = .walk v c) {t' : Tree} {vc' : VC} {rmw : Rmw} {next : Next}
    (hwk : s.tree.walk cfg c v s.clocks[id + 1]! cfg.orderings.ticket = .ok t' vc' rmw next) :
    HbInv cfg (({ s with tree := t', clocks := s.clocks.set! (id + 1) vc' } : State).setConsumer id
      (nextPhase cfg v next)) := by
  obtain ⟨rfl, hpw, -, hlt⟩ := hinv.active hid (Or.inr (Or.inl ⟨c, hph'⟩))
  have hsize : id < s.consumers.size := by rw [hinv.size]; exact hid
  have hcs : phaseOf (({ s with tree := t', clocks := s.clocks.set! (id + 1) vc' } : State).setConsumer id
      (nextPhase cfg (s.producer.version cfg) next)).consumers =
      upd (phaseOf s.consumers) id (nextPhase cfg (s.producer.version cfg) next) := by
    rw [setConsumer_consumers, phaseOf_setIfInBounds _ _ _ hsize]
  obtain ⟨htr, hfinK⟩ := treeHb_walk hinv.wf hinv.tree hw hb.tree hb.clocks_size hb.clock_size hb.rel_size
    (fun j hj => hb.mark_le j hj) hlt hS.ticket_acquires hS.ticket_releases hid hph'
    (not_past_no_filled hinv hid) hwk
  obtain ⟨node, hnode, hvc', node', hnode', hrel'⟩ := walk_clocks hwk
  have hrs : s.clocks[id + 1]!.size = node.rel.size := by
    rw [hb.clock_size _ (by omega), hb.rel_size _ _ hnode]
  have hset : ∀ u, (s.clocks.set! (id + 1) vc')[u]! = if u = id + 1 then vc' else s.clocks[u]! := by
    intro u
    rw [Array.set!_eq_setIfInBounds, getElem!_setIfInBounds]
    by_cases hu : u = id + 1
    · subst hu; rw [if_pos ⟨rfl, by rw [hb.clocks_size]; omega⟩, if_pos rfl]
    · rw [if_neg (fun h => hu h.1.symm), if_neg hu]
  have hck : ∀ a b, s.ck a b ≤ (s.clocks.set! (id + 1) vc')[a]![b]! := by
    intro a b
    unfold State.ck
    rw [hset]
    split
    · rename_i ha; subst ha; rw [hvc']; exact rmwClocks_vc_le hrs _ b
    · exact Nat.le_refl _
  obtain ⟨-, -, -, -, -, -, -, ⟨f, hf, ht'⟩, -⟩ := walk_spec hwk
  refine ⟨?_, ?_, hb.probeRel_size, ?_, hb.jobReads_size, hb.resultSlots_size, hb.resultReads, hb.jobReads_zero,
    fun j hj => Nat.le_trans (hb.mark_le j hj) (hck _ _), ?_, ?_, ?_, ?_, hb.published, ?_,
    fun v' hp j hj => Nat.le_trans (hb.producerKnows v' hp j hj) (hck _ _), hb.probeKnows, ?_, ?_⟩
  · show (s.clocks.set! (id + 1) vc').size = _
    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hb.clocks_size
  · intro u hu
    show (s.clocks.set! (id + 1) vc')[u]!.size = _
    rw [hset]
    split
    · rw [hvc', (rmwClocks_size hrs _).1]; exact hb.clock_size _ (by omega)
    · exact hb.clock_size u hu
  · intro q n hn
    change t'.get q = some n at hn
    by_cases hq : q = c.path
    · subst hq
      rw [hnode'] at hn
      obtain rfl := Option.some.inj hn
      rw [hrel', (rmwClocks_size hrs _).2]
      exact hb.clock_size _ (by omega)
    · obtain ⟨m, hm, -, hmr⟩ := get_modifyAt_ne' hf hq (by rw [← ht']; exact hn)
      rw [hmr]; exact hb.rel_size q m hm
  · intro tw c' h
    obtain ⟨h1, h2⟩ := hb.job_write tw c' h
    exact ⟨h1, Nat.le_trans h2 (hck _ _)⟩
  · intro j hj tw c' h
    obtain ⟨h1, h2⟩ := hb.result_write j hj tw c' h
    exact ⟨h1, Nat.le_trans h2 (hck _ _)⟩
  · intro j hj h
    rw [hcs] at h
    by_cases hji : j = id
    · subst hji; rw [upd_self] at h; exact absurd h (nextPhase_ne_start _ _ _)
    · rw [upd_ne _ _ _ hji] at h; exact hb.start j hj h
  · intro j hj v' h
    rw [hcs] at h
    by_cases hji : j = id
    · subst hji; rw [upd_self] at h; exact absurd h (nextPhase_ne_beforeFunc _ _ _ _)
    · rw [upd_ne _ _ _ hji] at h
      obtain ⟨h1, h2⟩ := hb.beforeFunc j hj v' h
      exact ⟨fun c' hc => Nat.le_trans (h1 c' hc) (hck _ _), fun c' hc => Nat.le_trans (h2 c' hc) (hck _ _)⟩
  · intro v' hp j hj hpf
    rw [hcs] at hpf
    by_cases hji : j = id
    · subst hji
      change s.producer = _ ∨ s.producer = _ at hp
      rw [hpw] at hp
      rcases hp with hp | hp <;> cases hp
      exact hb.resultMark _ (Or.inl hpw) j hj (Or.inr (Or.inl ⟨c, hph'⟩))
    · rw [upd_ne _ _ _ hji] at hpf
      exact hb.resultMark v' hp j hj hpf
  · intro i hi v' hfin j hj hpast
    rw [hcs] at hfin hpast
    by_cases hii : i = id
    · subst hii
      rw [upd_self] at hfin
      cases next with
      | finished =>
        cases hfin
        show s.mark j ≤ (s.clocks.set! (i + 1) vc')[i + 1]![j + 1]!
        rw [hset, if_pos rfl]
        exact hfinK rfl j hj hpast
      | stop => exact absurd hfin (by show nextConsumer cfg _ ≠ _; unfold nextConsumer; split <;> nofun)
      | «continue» c' => cases hfin
    · rw [upd_ne _ _ _ hii] at hfin
      exfalso
      obtain ⟨hv', -, -, -⟩ := hinv.active hi (Or.inr (Or.inr hfin))
      subst hv'
      have := hinv.finisher i hi hfin id hid (Ne.symm hii)
      rw [hph'] at this
      exact absurd this (not_finished_of_ne nofun nofun)
  · show TreeHb cfg (s.producer.version cfg) (phaseOf (({ s with tree := t', clocks := s.clocks.set! (id + 1) vc' } :
      State).setConsumer id (nextPhase cfg (s.producer.version cfg) next)).consumers) t'
      (s.clocks.set! (id + 1) vc') s.mark
    rw [hcs]
    exact htr


/-! ## Consumer moves -/

theorem step_consumer_hbInv {cfg : Config} (hS : Strong cfg.orderings) {s s' : State} {id : Nat}
    {ev : Option Event} (hinv : Inv cfg s) (hw : WInv cfg s) (hb : HbInv cfg s)
    (h : step cfg s (.consumer id) = .step s' ev) : HbInv cfg s' := by
  unfold step at h
  simp only at h
  split at h
  · rename_i s'' ev' hc
    simp only [Outcome.step.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply HbInv.tick
    unfold consumerStep at hc
    simp only [threadIndex] at hc
    cases hph : s.consumers[id]? with
    | none => rw [hph] at hc; cases hc
    | some ph =>
      rw [hph] at hc
      have hid : id < cfg.workers := by
        obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hph
        rw [hinv.size] at hlt; exact hlt
      have hph' : phaseOf s.consumers id = ph := phaseOf_eq hph
      cases ph with
      | start =>
        dsimp only at hc
        unfold Outcome.accessing at hc
        split at hc
        · rename_i s₁ ha
          obtain rfl := access_writeResult_ok ha
          simp only [Outcome.step.injEq] at hc
          obtain ⟨rfl, -⟩ := hc
          have hb₁ := hb.setConsumer hinv hid (ph' := .initializing) nofun (fun _ h => by cases h)
            (fun _ _ h => absurd h pastFunc_initializing) (fun _ h => by cases h)
            (hb.tree.upd_simple (by rw [hph']; rfl) nofun (fun c h => by rw [hph'] at h; cases h))
          exact hb₁.writeResult hid
            (by rw [setConsumer_consumers, phaseOf_setIfInBounds _ _ _ (by rw [hinv.size]; exact hid), upd_self]
                exact nofun)
            (fun _ _ h => absurd (by rwa [setConsumer_consumers, phaseOf_setIfInBounds _ _ _
              (by rw [hinv.size]; exact hid), upd_self] at h) pastFunc_initializing)
        · cases hc
      | initializing =>
        dsimp only at hc
        simp only [Outcome.step.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        refine (hb.setConsumer hinv hid ?_ ?_ ?_ ?_ ?_).setResults _
        · split <;> nofun
        · intro v h; split at h <;> cases h
        · intro v _ hpf
          exfalso
          split at hpf
          · rename_i h0
            rcases hpf with h | ⟨c, h⟩ | h | h | ⟨-, h⟩ <;> first | cases h | omega
          · rcases hpf with h | ⟨c, h⟩ | h | h | ⟨h, -⟩ <;> cases h
        · intro v h; split at h <;> cases h
        · refine hb.tree.upd_simple ?_ (by intro v c; split <;> nofun) (fun c h => by rw [hph'] at h; cases h)
          rw [hph']
          split <;> simp [leafDone] <;> omega
      | waitReady v =>
        dsimp only at hc
        split at hc
        · rename_i hgt
          rw [if_pos hS.consumerFence] at hc
          simp only [Outcome.step.injEq] at hc
          obtain ⟨rfl, -⟩ := hc
          obtain ⟨rfl, hpw, -⟩ := hinv.waitReady_enabled hid hph' hgt
          have hb₁ := hb.acquireProbe (t := id + 1) (by omega)
          have hsz : s.probeRel.size ≤ s.clocks[id + 1]!.size := by
            rw [hb.probeRel_size, hb.clock_size _ (by omega)]; exact Nat.le_refl _
          have hacq := acquireProbe_ck_self s (t := id + 1) (by rw [hb.clocks_size]; omega) hsz 0
          have hph₁ : phaseOf (s.acquireProbe (id + 1)).consumers id = .waitReady (s.producer.version cfg) := hph'
          refine hb₁.setConsumer hinv hid nofun ?_ (fun _ _ h => absurd h pastFunc_beforeFunc)
            (fun _ h => by cases h)
            (hb₁.tree.upd_simple (by rw [hph₁]; rfl) nofun (fun c h => by rw [hph₁] at h; cases h))
          intro _ _
          refine ⟨fun c hc => Nat.le_trans ((hb.published _ hpw).1 c hc) hacq,
            fun c hc => Nat.le_trans ((hb.published _ hpw).2 id hid c hc) hacq⟩
        · cases hc
      | beforeFunc v =>
        dsimp only at hc
        unfold Outcome.accessing at hc
        split at hc
        · rename_i s₁ ha
          obtain rfl := access_readJob_ok ha
          dsimp only at hc
          split at hc
          · rename_i s₂ ha2
            obtain rfl := access_writeResult_ok ha2
            simp only [Outcome.step.injEq] at hc
            obtain ⟨rfl, -⟩ := hc
            obtain ⟨rfl, hpw, -⟩ := hinv.beforeFunc_active hid hph'
            have hb₁ := hb.readJob hinv hid hph'
            have hb₂ := hb₁.writeResult hid (by rw [hph']; nofun) (fun _ _ h => by
              change PastFunc cfg _ (phaseOf s.consumers id) at h
              rw [hph'] at h
              exact absurd h pastFunc_beforeFunc)
            have hph₂ : phaseOf ({ ({ s with jobSlot := s.jobSlot.read (id + 1) s.clocks[id + 1]! } : State) with
                resultSlots := s.resultSlots.modify id (·.write (id + 1) s.clocks[id + 1]!) } : State).consumers id =
                .beforeFunc (s.producer.version cfg) := hph'
            refine hb₂.setConsumer hinv hid nofun (fun _ h => by cases h) ?_ (fun _ h => by cases h)
              (hb₂.tree.upd_simple (by rw [hph₂]; rfl) nofun (fun c h => by rw [hph₂] at h; cases h))
            intro _ _ _
            have hsz : id < s.resultSlots.size := by rw [hb.resultSlots_size]; exact hid
            show (s.resultSlots.modify id (·.write (id + 1) s.clocks[id + 1]!))[id]!.lastWrite =
              some (id + 1, State.mark { s with jobSlot := s.jobSlot.read (id + 1) s.clocks[id + 1]! } id)
            rw [getElem!_modify, if_pos ⟨rfl, hsz⟩, Slot.write_lastWrite, mark_read hb hid, if_pos rfl]
            rfl
          · cases hc
        · cases hc
      | inFunc v =>
        dsimp only at hc
        simp only [Outcome.step.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        obtain ⟨rfl, hpw, -, -⟩ := hinv.active hid (Or.inl hph')
        refine (hb.setConsumer hinv hid (ph' := .walk _ (Cursor.start cfg id)) nofun (fun _ h => by cases h) ?_
          (fun _ h => by cases h) (hb.tree.upd_startWalk hph')).setResults _
        intro v' hp' _
        rw [hpw] at hp'
        rcases hp' with hp' | hp' <;> cases hp'
        exact hb.resultMark _ (Or.inl hpw) id hid (Or.inl hph')
      | walk v c =>
        dsimp only at hc
        cases hwk : s.tree.walk cfg c v s.clocks[id + 1]! cfg.orderings.ticket with
        | fault m => rw [hwk] at hc; cases hc
        | ok t' vc' rmw next =>
          rw [hwk] at hc
          simp only [Outcome.step.injEq] at hc
          obtain ⟨rfl, -⟩ := hc
          have := HbInv.walk hS hinv hw hb hid hph' hwk
          cases next <;> exact this
      | finish v =>
        dsimp only at hc
        simp only [Outcome.step.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        obtain ⟨hv, hpw, -, hlt⟩ := hinv.active hid (Or.inr (Or.inr hph'))
        subst hv
        obtain ⟨hj, hr, ht, hcs, hpr, hprb⟩ := rmwProbe_unchanged' s (id + 1) cfg.orderings.finish
        have hinv₁ : Inv cfg (s.rmwProbe (id + 1) cfg.orderings.finish) := hinv.congr hprb ht hpr hcs
        have hb₁ := hb.rmwProbe (t := id + 1) (by omega) cfg.orderings.finish
        have hph₁ : phaseOf (s.rmwProbe (id + 1) cfg.orderings.finish).consumers id = .finish (s.producer.version cfg) := by
          rw [hcs]; exact hph'
        have hmark₁ := mark_of_jobSlot hj
        have hb₂ := hb₁.setConsumer hinv₁ hid (ph' := nextConsumer cfg (s.producer.version cfg))
          (by unfold nextConsumer; split <;> nofun) (fun _ h => by unfold nextConsumer at h; split at h <;> cases h)
          (fun v' hp' _ => by
            rw [hpr, hpw] at hp'
            rcases hp' with hp' | hp' <;> cases hp'
            rw [hr, hmark₁]
            exact hb.resultMark _ (Or.inl hpw) id hid (Or.inr (Or.inr (Or.inl hph'))))
          (fun _ h => by unfold nextConsumer at h; split at h <;> cases h)
          (hb₁.tree.upd_simple (by rw [hph₁, leafDone_nextConsumer _ _ _ hlt]; rfl)
            (nextConsumer_ne_walk cfg _) (fun c h => by rw [hph₁] at h; cases h))
        refine hb₂.setProbe ?_
        intro v' _ _ j hj
        show State.mark (s.rmwProbe (id + 1) cfg.orderings.finish) j ≤ (s.rmwProbe (id + 1) cfg.orderings.finish).probeRel[j + 1]!
        rw [hmark₁]
        have hpast : PastLeaf cfg (s.producer.version cfg) (phaseOf s.consumers) j := by
          by_cases hji : j = id
          · subst hji; unfold PastLeaf; rw [hph']; rfl
          · exact (hinv.finisher id hid hph' j hj hji).pastLeaf
        refine Nat.le_trans (hb.finisherKnows id hid _ hph' j hj hpast) ?_
        exact rmwProbe_release_le s (by rw [hb.clock_size _ (by omega), hb.probeRel_size]) hS.finish (j + 1)
      | done =>
        dsimp only at hc
        cases hc
  · exfalso
    rename_i hne
    exact hne _ _ h

theorem step_hbInv {cfg : Config} (hS : Strong cfg.orderings) {s s' : State} {t : Thread} {ev : Option Event}
    (hinv : Inv cfg s) (hw : WInv cfg s) (hb : HbInv cfg s) (h : step cfg s t = .step s' ev) : HbInv cfg s' := by
  cases t with
  | producer => exact step_producer_hbInv hS hinv hb h
  | consumer id => exact step_consumer_hbInv hS hinv hw hb h

theorem reachable_hbInv {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) (hS : Strong cfg.orderings)
    {s : State} (h : Reachable cfg s) : HbInv cfg s := by
  induction h with
  | init => exact init_hbInv cfg hC
  | step hr hstep ih => exact step_hbInv hS (reachable_inv hW hC hr) (reachable_wInv hW hC hr) ih hstep


/-! ## No step races -/

theorem writeAllSlots_ne_error {t : Nat} {vc : VC} {race : Nat → String → String} :
    ∀ (l : List (Slot × Nat)) (rs : Array Slot), (∀ x ∈ l, x.1.writeConflict vc = none) →
      ∀ m, writeAllSlots t vc race l rs ≠ .error m
  | [], rs, _, m, h => by simp [writeAllSlots, pure, Except.pure] at h
  | (slot, i) :: l, rs, hc, m, h => by
    simp only [writeAllSlots, hc (slot, i) (by simp)] at h
    exact writeAllSlots_ne_error l _ (fun x hx => hc x (by simp [hx])) m h

theorem HbInv.jobWrite_ok {cfg : Config} {s : State} (hb : HbInv cfg s) {v : Nat}
    (hp : s.producer = .beforeWrite v) : s.jobSlot.writeConflict s.clocks[0]! = none := by
  refine Slot.writeConflict_none (fun tw c h => ?_) (fun i => ?_)
  · obtain ⟨rfl, h2⟩ := hb.job_write tw c h
    exact h2
  · cases i with
    | zero => rw [hb.jobReads_zero]; exact Nat.zero_le _
    | succ j =>
      by_cases hj : j < cfg.workers
      · exact hb.producerKnows v (Or.inl hp) j hj
      · rw [getElem!_neg s.jobSlot.reads (j + 1) (by rw [hb.jobReads_size]; omega)]
        exact Nat.zero_le _

theorem HbInv.resultWrite_ok {cfg : Config} {s : State} (hb : HbInv cfg s) {id : Nat} (hid : id < cfg.workers)
    (h0 : ∀ c, s.resultSlots[id]!.lastWrite = some (0, c) → c ≤ s.ck (id + 1) 0) :
    s.resultSlots[id]!.writeConflict s.clocks[id + 1]! = none := by
  refine Slot.writeConflict_none (fun tw c h => ?_) (fun i => ?_)
  · obtain ⟨htw, hc⟩ := hb.result_write id hid tw c h
    rcases htw with rfl | rfl
    · exact h0 c h
    · exact hc
  · rw [hb.resultReads id hid, VC.getElem!_zero]; exact Nat.zero_le _

theorem HbInv.allWrite_ok {cfg : Config} {s : State} (hinv : Inv cfg s) (hb : HbInv cfg s) {v : Nat}
    (hp : s.producer = .beforeComplete v) :
    ∀ x ∈ s.resultSlots.toList.zipIdx, x.1.writeConflict s.clocks[0]! = none := by
  have hinv' : InvAt cfg s.probe s.tree (.beforeComplete v) v s.consumers := hinv.at hp
  have hall := hinv'.all_finished hinv'.probeOk
  rintro ⟨r, j⟩ hx
  have hj := mem_toList_zipIdx hx
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hj
  rw [hb.resultSlots_size] at hlt
  have hr : r = s.resultSlots[j]! := (getElem!_of_getElem? hj).symm
  subst hr
  have hw := hb.resultMark v (Or.inr hp) j hlt (hall j hlt).pastFunc
  refine Slot.writeConflict_none (fun tw c h => ?_) (fun i => ?_)
  · rw [hw] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hb.producerKnows v (Or.inr (Or.inl hp)) j hlt
  · show s.resultSlots[j]!.reads[i]! ≤ _
    rw [hb.resultReads j hlt, VC.getElem!_zero]; exact Nat.zero_le _

theorem producer_no_race {cfg : Config} {s : State} (hinv : Inv cfg s) (hb : HbInv cfg s) {m : String}
    (hr : producerStep cfg s = .race m) : False := by
  unfold producerStep at hr
  cases hp : s.producer with
  | beforeWrite v =>
    rw [hp] at hr
    dsimp only [threadIndex] at hr
    unfold Outcome.accessing at hr
    split at hr
    · cases hr
    · rename_i m' ha
      unfold State.access at ha
      simp only at ha
      split at ha
      · rename_i c hc
        rw [hb.jobWrite_ok hp] at hc
        cases hc
      · cases ha
  | beforeComplete v =>
    rw [hp] at hr
    dsimp only [threadIndex] at hr
    unfold Outcome.accessing at hr
    split at hr
    · cases hr
    · rename_i m' ha
      unfold State.access at ha
      simp only at ha
      split at ha
      · cases ha
      · rename_i m'' hm
        exact writeAllSlots_ne_error _ _ (hb.allWrite_ok hinv hp) _ hm
  | waiting v =>
    rw [hp] at hr
    dsimp only at hr
    split at hr <;> cases hr
  | writing v => rw [hp] at hr; cases hr
  | publish v => rw [hp] at hr; cases hr
  | completing v => rw [hp] at hr; cases hr
  | done => rw [hp] at hr; cases hr

theorem consumer_no_race {cfg : Config} {s : State} (hinv : Inv cfg s) (hb : HbInv cfg s) {id : Nat}
    {m : String} (hr : consumerStep cfg s id = .race m) : False := by
  unfold consumerStep at hr
  simp only [threadIndex] at hr
  cases hph : s.consumers[id]? with
  | none => rw [hph] at hr; cases hr
  | some ph =>
    rw [hph] at hr
    have hid : id < cfg.workers := by
      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hph
      rw [hinv.size] at hlt; exact hlt
    have hph' : phaseOf s.consumers id = ph := phaseOf_eq hph
    cases ph with
    | start =>
      dsimp only at hr
      unfold Outcome.accessing at hr
      split at hr
      · cases hr
      · rename_i m' ha
        unfold State.access at ha
        simp only at ha
        split at ha
        · rename_i c hc
          rw [hb.resultWrite_ok hid (fun c h => by rw [hb.start id hid hph'] at h; cases h)] at hc
          cases hc
        · cases ha
    | beforeFunc v =>
      dsimp only at hr
      unfold Outcome.accessing at hr
      split at hr
      · rename_i s₁ ha
        obtain rfl := access_readJob_ok ha
        dsimp only at hr
        split at hr
        · cases hr
        · rename_i m' ha2
          unfold State.access at ha2
          simp only at ha2
          split at ha2
          · rename_i c hc
            rw [hb.resultWrite_ok hid (hb.beforeFunc id hid v hph').2] at hc
            cases hc
          · cases ha2
      · rename_i m' ha
        unfold State.access at ha
        simp only at ha
        split at ha
        · rename_i c hc
          rw [Slot.readConflict_none (fun tw c h => by
            obtain ⟨rfl, -⟩ := hb.job_write tw c h
            exact (hb.beforeFunc id hid v hph').1 c h)] at hc
          cases hc
        · cases ha
    | initializing => dsimp only at hr; cases hr
    | waitReady v => dsimp only at hr; split at hr <;> cases hr
    | inFunc v => dsimp only at hr; cases hr
    | walk v c =>
      dsimp only at hr
      cases hwk : s.tree.walk cfg c v s.clocks[id + 1]! cfg.orderings.ticket <;> rw [hwk] at hr <;> cases hr
    | finish v => dsimp only at hr; cases hr
    | done => dsimp only at hr; cases hr

/-- No step from a state satisfying the invariants is a data race. -/
theorem step_no_race {cfg : Config} {s : State} (hinv : Inv cfg s) (hb : HbInv cfg s) (t : Thread) (m : String) :
    step cfg s t ≠ .race m := by
  intro h
  unfold step at h
  cases t with
  | producer =>
    simp only at h
    cases hr : producerStep cfg s with
    | race m' => exact producer_no_race hinv hb hr
    | blocked => rw [hr] at h; cases h
    | step s' ev => rw [hr] at h; cases h
    | fault m' => rw [hr] at h; cases h
  | consumer id =>
    simp only at h
    cases hr : consumerStep cfg s id with
    | race m' => exact consumer_no_race hinv hb hr
    | blocked => rw [hr] at h; cases h
    | step s' ev => rw [hr] at h; cases h
    | fault m' => rw [hr] at h; cases h

/-- **Race freedom.** With the orderings of `src/lib.rs`, no reachable state
of the barrier has a step that is a data race: every access to the job slot
and the result slots is ordered, by happens-before, after every conflicting
earlier access. -/
theorem reachable_no_race {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) (hS : Strong cfg.orderings)
    {s : State} (h : Reachable cfg s) (t : Thread) (m : String) : step cfg s t ≠ .race m :=
  step_no_race (reachable_inv hW hC h) (reachable_hbInv hW hC hS h) t m

end RearmBarrier
