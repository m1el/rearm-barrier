import RearmBarrier.Protocol

/-!
# The executable check follows from the invariant

`Tree.invariant` (in `RearmBarrier.TreeModel`) is what the explorer and the
trace replay run in every state. This file shows it reports nothing in any
state satisfying the protocol invariant: `nodeViolations_nil` matches each
of its checks with the corresponding clause of `NodeInv`, and
`Inv.invariant_nil` assembles the whole tree. The one check `TreeInv` alone
does not cover, "no node is beyond the last version", follows from `Inv`:
a live node is no further ahead than the leaves below it
(`version_le_below`), and a leaf's version is bounded by its consumers'
`leafDone`, which the consumer phases keep below `count`
(`InvAt.leafDone_le`).
-/

namespace RearmBarrier

theorem getElem!_phaseOf (cs : Array ConsumerPhase) (id : Nat) (h : id < cs.size) :
    cs[id]! = phaseOf cs id := by
  simp [phaseOf, getElem!_pos, h]

/-- What an entry of `inFlightTo` says about the consumer. -/
theorem mem_inFlightTo {path : List Nat} {cs : Array ConsumerPhase} {id v amt : Nat}
    (h : (id, v, amt) ∈ inFlightTo path cs) :
    id < cs.size ∧ ∃ c, phaseOf cs id = .walk v c ∧ c.path = path ∧ amt = c.mergeAmount := by
  unfold inFlightTo at h
  rw [List.mem_filterMap] at h
  obtain ⟨id', hid', hf⟩ := h
  simp only [List.mem_range] at hid'
  rw [getElem!_phaseOf cs id' hid'] at hf
  cases hph : phaseOf cs id'
  case walk v' c =>
    rw [hph] at hf
    by_cases hc : c.path = path
    · simp [hc] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      exact ⟨hid', c, hph, hc, rfl⟩
    · simp [hc] at hf
  all_goals (rw [hph] at hf; simp at hf)

theorem sum_map_filterMap {α β : Type} (f : α → Option β) (g : β → Nat) : ∀ (l : List α),
    ((l.filterMap f).map g).sum = (l.map fun x => match f x with | some y => g y | none => 0).sum
  | [] => rfl
  | x :: l => by
    cases hx : f x with
    | none => simp [hx, sum_map_filterMap f g l]
    | some y => simp [hx, sum_map_filterMap f g l]

/-- The amounts in flight towards a node add up to `carriedTo`. -/
theorem inFlight_eq (path : List Nat) (cs : Array ConsumerPhase) :
    ((inFlightTo path cs).map (·.2.2)).sum = carriedTo cs.size path (phaseOf cs) := by
  unfold inFlightTo carriedTo
  rw [sum_map_filterMap]
  congr 1
  apply List.map_congr_left
  intro id hid
  simp only [List.mem_range] at hid
  rw [getElem!_phaseOf cs id hid]
  cases phaseOf cs id
  case walk v c =>
    by_cases hc : c.path = path
    · simp [hc]
    · simp [hc]
  all_goals rfl

set_option linter.deprecated false in
/-- Every check of `Tree.nodeViolations` is a clause of `NodeInv`. -/
theorem nodeViolations_nil {cfg : Config} {V : Nat} {cs : Array ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V (phaseOf cs) t)
    (hsize : cs.size = cfg.workers) {q : List Nat} {n : Tree} (hq : t.get q = some n)
    (hver : n.version ≤ cfg.count) : n.nodeViolations cfg cs q = [] := by
  have hnode := hinv.nodes q n hq
  have hwfn := Wf.get q hwf hq
  have hcarried : ((inFlightTo q cs).map (·.2.2)).sum = carriedTo cfg.workers q (phaseOf cs) := by
    rw [inFlight_eq, hsize]
  unfold Tree.nodeViolations
  simp only [List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- every contribution carried here is for this node's version
    intro x hx
    obtain ⟨id, v, amt⟩ := x
    obtain ⟨hid, c, hph, hcp, -⟩ := mem_inFlightTo hx
    have := hnode.carried_version id (by omega) v c hph hcp
    simp [this]
  · -- not beyond the last version
    rw [if_neg (by omega)]
  · -- not full
    have := hnode.not_full
    simp [Nat.not_le.mpr this]
  · by_cases hnil : n.children = []
    · -- a leaf
      have hleaf : n.isLeaf = true := by simp [Tree.isLeaf, hnil]
      rw [if_pos hleaf]
      obtain ⟨hb, hcount, hamt⟩ := hnode.leaf hnil
      have hhi := hwfn.hi_le
      simp only [List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro id hid
        simp only [List.mem_range'_1] at hid
        simp only [getElem!_phaseOf cs id (by omega)]
        obtain ⟨h1, h2⟩ := hb id (by omega) (by omega)
        simp [Nat.not_lt.mpr h1, Nat.not_lt.mpr h2]
      · rw [hcount]
        unfold contributedIn
        have : ∀ id ∈ List.range' n.lo (n.hi - n.lo),
            (if leafDone q cfg.count cs[id]! == n.version + 1 then 1 else 0) =
              pastLeaf cfg.count q n.version (phaseOf cs id) := by
          intro id hid
          simp only [List.mem_range'_1] at hid
          simp only [getElem!_phaseOf cs id (by omega)]
          simp [pastLeaf]
        rw [List.map_congr_left this]
        simp
      · intro x hx
        obtain ⟨id, v, amt⟩ := x
        obtain ⟨hid, c, hph, hcp, rfl⟩ := mem_inFlightTo hx
        have := hamt id (by omega) v c hph hcp
        simp [this]
    · have hleaf : n.isLeaf = false := by simp [Tree.isLeaf, hnil]
      rw [if_neg (by simp [hleaf])]
      by_cases hd : deadAt cfg.workers t q n
      · -- dead: never touched
        have hany : n.children.any (·.size == cfg.workers) = true := by
          obtain ⟨k, hk, c, hc, hcs⟩ := hd
          rw [get_child hq] at hc
          rw [List.any_eq_true]
          exact ⟨c, Wf.get.mem_of_getElem?' _ _ _ hc, by simp [hcs]⟩
        rw [if_pos hany]
        obtain ⟨h1, h2, h3⟩ := hnode.dead hd
        have hempty : inFlightTo q cs = [] := by
          cases hc : inFlightTo q cs with
          | nil => rfl
          | cons x rest =>
            exfalso
            obtain ⟨id, v, amt⟩ := x
            have hmem : (id, v, amt) ∈ inFlightTo q cs := by rw [hc]; simp
            obtain ⟨hid, c, hph, -, rfl⟩ := mem_inFlightTo hmem
            have hpos := hinv.carry_pos id (by omega) v c hph
            have hle : c.mergeAmount ≤ ((inFlightTo q cs).map (·.2.2)).sum := by
              rw [hc]; simp
            rw [hcarried, h3] at hle
            omega
        simp [h1, h2, hempty]
      · -- live: what is below adds up
        have hany : n.children.any (·.size == cfg.workers) = false := by
          apply Bool.eq_false_iff.mpr
          intro h
          apply hd
          rw [List.any_eq_true] at h
          obtain ⟨c, hc, hcs⟩ := h
          obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
          exact ⟨k, lt_length_of_getElem?' _ _ _ hk, c, by rw [get_child hq]; exact hk, by simpa using hcs⟩
        rw [if_neg (by simp [hany])]
        obtain ⟨hcb, heq⟩ := hnode.live hnil hd
        simp only [List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
        refine ⟨?_, ?_⟩
        · intro x hx
          obtain ⟨child, k⟩ := x
          have hk : n.children[k]? = some child := List.mem_zipIdx_iff_getElem?.mp hx
          obtain ⟨c, hc, h1, h2⟩ := hcb k (lt_length_of_getElem?' _ _ _ hk)
          rw [get_child hq, hk] at hc
          have := Option.some.inj hc
          subst this
          simp [Nat.not_lt.mpr h1, Nat.not_lt.mpr h2]
        · rw [hcarried, heq, filledBelow_eq hq]
          have : ∀ c ∈ n.children,
              (if c.version == n.version + 1 then c.size else 0) = filledOf (n.version + 1) (some c) := by
            intro c _
            rw [filledOf_some]
            simp
          rw [List.map_congr_left this]
          simp

theorem Tree.invariantChildren_nil (cfg : Config) (cs : Array ConsumerPhase) (path : List Nat) :
    ∀ (k : Nat) (l : List Tree), (∀ j (c : Tree), l[j]? = some c → c.invariant cfg cs (path ++ [k + j]) = []) →
      Tree.invariantChildren cfg cs path k l = []
  | _, [], _ => rfl
  | k, c :: rest, h => by
    rw [Tree.invariantChildren, List.append_eq_nil_iff]
    refine ⟨by simpa using h 0 c rfl, ?_⟩
    apply Tree.invariantChildren_nil cfg cs path (k + 1) rest
    intro j c' hj
    have := h (j + 1) c' (by simpa using hj)
    have e : k + (j + 1) = k + 1 + j := by omega
    rw [e] at this
    exact this

/-- The executable check passes on every node of a tree satisfying `TreeInv`
whose versions are within `count`. -/
theorem Tree.invariant_nil {cfg : Config} {V : Nat} {cs : Array ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V (phaseOf cs) t)
    (hsize : cs.size = cfg.workers) (hver : ∀ q n, t.get q = some n → n.version ≤ cfg.count) :
    ∀ (m : Nat) (q : List Nat) (n : Tree), sizeOf n = m → t.get q = some n →
      n.invariant cfg cs q = [] := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro q n hm hq
    subst hm
    have hnode := nodeViolations_nil hwf hinv hsize hq (hver q n hq)
    cases n with
    | mk v f r lo hi children =>
      rw [Tree.invariant, List.append_eq_nil_iff]
      refine ⟨hnode, ?_⟩
      apply Tree.invariantChildren_nil
      intro j c hj
      rw [Nat.zero_add]
      have hc : t.get (q ++ [j]) = some c := by rw [get_child hq]; exact hj
      have hmem : c ∈ (Tree.mk v f r lo hi children).children := Wf.get.mem_of_getElem?' _ _ _ hj
      exact ih (sizeOf c) (sizeOf_child_lt hmem) (q ++ [j]) c rfl hc

/-! ## Versions stay within `count` -/

theorem InvAt.V_le_count {cfg : Config} {probe : Nat} {t : Tree} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} (h : InvAt cfg probe t p V cs) : V ≤ cfg.count := by
  have := h.version
  have := h.version_lt
  cases p <;> simp only [ProducerPhase.version, ne_eq, reduceCtorEq, not_false_eq_true,
    forall_const, not_true_eq_false, false_implies] at * <;> omega

/-- Once the version is published the producer is not done. -/
theorem InvAt.lt_count_of_probe {cfg : Config} {probe : Nat} {t : Tree} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} (h : InvAt cfg probe t p V cs) (hp : probe ≠ 2 * V) : V < cfg.count := by
  apply h.version_lt
  intro hd
  subst hd
  have := h.version
  have := h.probeOk
  simp only [ProducerPhase.version, ProbeOk] at *
  omega

/-- No consumer has done more leaf contributions than there are versions. -/
theorem InvAt.leafDone_le {cfg : Config} {probe : Nat} {t : Tree} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} (h : InvAt cfg probe t p V cs) (q : List Nat) {id : Nat}
    (hid : id < cfg.workers) : leafDone q cfg.count (phaseOf cs id) ≤ cfg.count := by
  have hle := h.V_le_count
  have hc := h.consumers id hid
  rcases probe_cases h.probeOk h.version with hp | hp | hp
  · rcases hc.1 hp with h1 | ⟨_, h1 | h1⟩ | ⟨_, h1⟩ <;> rw [h1] <;> simp only [leafDone] <;> omega
  · have hlt := h.lt_count_of_probe (by omega)
    rcases hc.2.1 hp with h1 | h1 | h1 | ⟨c, h1⟩ | h1 | (h1 | ⟨h1, _⟩) | ⟨_, h1 | h1⟩ <;> rw [h1] <;>
      simp only [leafDone] <;> (try split) <;> omega
  · have hlt := h.lt_count_of_probe (by omega)
    rcases hc.2.2 hp with h1 | ⟨h1, _⟩ <;> rw [h1] <;> simp only [leafDone] <;> omega

/-- No node counts a version beyond the last one. -/
theorem Inv.version_le_count {cfg : Config} {s : State} (h : Inv cfg s) :
    ∀ q n, s.tree.get q = some n → n.version ≤ cfg.count := by
  intro q n hq
  by_cases hd : deadAt cfg.workers s.tree q n
  · have := ((h.tree.nodes q n hq).dead hd).1
    omega
  · have hwfn := Wf.get q h.wf hq
    obtain ⟨r, leaf, hleaf, hnil, hl1, hl2⟩ :=
      descend h.wf n.lo (sizeOf n) q n rfl hq (Nat.le_refl _) hwfn.lo_lt_hi
    have h1 := version_le_below h.wf h.tree r q n hq hd leaf hleaf (not_deadAt_of_leaf hnil)
    obtain ⟨hb, -, -⟩ := (h.tree.nodes _ leaf hleaf).leaf hnil
    have h2 := (hb n.lo hl1 hl2).1
    have h3 := h.leafDone_le (q ++ r) (id := n.lo) (by have := hwfn.hi_le; have := hwfn.lo_lt_hi; omega)
    omega

/-- The executable check passes in every state satisfying the invariant. -/
theorem Inv.invariant_nil {cfg : Config} {s : State} (h : Inv cfg s) :
    s.tree.invariant cfg s.consumers [] = [] :=
  Tree.invariant_nil h.wf h.tree h.size h.version_le_count _ [] _ rfl rfl

end RearmBarrier
