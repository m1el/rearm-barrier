import RearmBarrier.StepInvariant
import RearmBarrier.TreeInit

/-!
# The global protocol invariant

`Inv cfg s` is what holds in every reachable state of the model: the
counting invariant of the completion tree (`TreeInv`) at the producer's
version `V`, plus the bookkeeping that ties `ticket_probe`, the producer's
phase and every consumer's phase together:

* `ProbeOk`: the probe is `2V` until the producer publishes, `2V + 1` while
  the consumers work, `2V + 2` once one of them completed the version;
* `ConsumerOk`: which phases a consumer can be in for each of those three
  probe values — in particular nobody is inside `func`, walking or finishing
  unless the probe is `2V + 1`, and then at version `V`;
* `finisher`: once a consumer is about to bump the probe (`finish V`), every
  other consumer is already waiting for `V + 1` (or done).

The last clause is where the tree matters: `others_done` shows that when a
node covering every worker reaches version `V + 1`, `TreeInv` forces every
consumer past its work for `V` — the leaf of every consumer is below that
node, every live node below it counts `V + 1`, and a leaf at `V + 1` has
counted all its consumers.

`init_inv` and `step_inv` give `reachable_inv`: every reachable state
satisfies `Inv`; `Inv.probe_le` is the crate's "the probe never runs ahead"
claim.
-/

namespace RearmBarrier

/-- The version the producer is working on; `count` once it is done. -/
def ProducerPhase.version (cfg : Config) : ProducerPhase → Nat
  | .beforeWrite v | .writing v | .publish v | .waiting v | .beforeComplete v | .completing v => v
  | .done => cfg.count

/-- The value of `ticket_probe` in every producer phase. -/
def ProbeOk (cfg : Config) : ProducerPhase → Nat → Prop
  | .beforeWrite v, probe | .writing v, probe | .publish v, probe => probe = 2 * v
  | .waiting v, probe => probe = 2 * v + 1 ∨ probe = 2 * v + 2
  | .beforeComplete v, probe | .completing v, probe => probe = 2 * v + 2
  | .done, probe => probe = 2 * cfg.count

/-- A consumer that is done with version `V`. -/
def Finished (cfg : Config) (V : Nat) (ph : ConsumerPhase) : Prop :=
  ph = .waitReady (V + 1) ∨ (ph = .done ∧ V + 1 = cfg.count)

/-- Where a consumer can be, given the producer's version `V` and the probe. -/
def ConsumerOk (cfg : Config) (V probe : Nat) (ph : ConsumerPhase) : Prop :=
  (probe = 2 * V →
    ph = .waitReady V ∨ (V = 0 ∧ (ph = .start ∨ ph = .initializing)) ∨ (V = cfg.count ∧ ph = .done)) ∧
  (probe = 2 * V + 1 →
    ph = .waitReady V ∨ ph = .beforeFunc V ∨ ph = .inFunc V ∨ (∃ c, ph = .walk V c) ∨ ph = .finish V ∨
    Finished cfg V ph ∨ (V = 0 ∧ (ph = .start ∨ ph = .initializing))) ∧
  (probe = 2 * V + 2 → Finished cfg V ph)

/-- The invariant on the components of a state, at the producer's version `V`. -/
structure InvAt (cfg : Config) (probe : Nat) (t : Tree) (p : ProducerPhase) (V : Nat)
    (cs : Array ConsumerPhase) : Prop where
  version : p.version cfg = V
  size : cs.size = cfg.workers
  wf : Wf cfg.cluster cfg.workers t
  tree : TreeInv cfg V (phaseOf cs) t
  probeOk : ProbeOk cfg p probe
  version_lt : p ≠ .done → V < cfg.count
  consumers : ∀ id, id < cfg.workers → ConsumerOk cfg V probe (phaseOf cs id)
  finisher : ∀ i, i < cfg.workers → phaseOf cs i = .finish V →
    ∀ j, j < cfg.workers → j ≠ i → Finished cfg V (phaseOf cs j)

abbrev Inv (cfg : Config) (s : State) : Prop :=
  InvAt cfg s.probe s.tree s.producer (s.producer.version cfg) s.consumers

/-! ## Consequences of the bookkeeping -/

theorem probe_cases {cfg : Config} {p : ProducerPhase} {probe V : Nat} (hp : ProbeOk cfg p probe)
    (hV : p.version cfg = V) : probe = 2 * V ∨ probe = 2 * V + 1 ∨ probe = 2 * V + 2 := by
  subst hV
  cases p <;> simp only [ProbeOk, ProducerPhase.version] at hp ⊢ <;> omega

theorem probe_odd {cfg : Config} {p : ProducerPhase} {probe V : Nat} (hp : ProbeOk cfg p probe)
    (hV : p.version cfg = V) (h : probe = 2 * V + 1) : p = .waiting V := by
  subst hV
  cases p <;> simp only [ProbeOk, ProducerPhase.version] at hp h ⊢ <;> omega

theorem InvAt.probe_le {cfg : Config} {probe : Nat} {t : Tree} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} (h : InvAt cfg probe t p V cs) : probe ≤ 2 * cfg.count := by
  have := h.probeOk
  have := h.version_lt
  have := h.version
  cases p <;> simp only [ProbeOk, ProducerPhase.version, ne_eq, reduceCtorEq, not_false_eq_true,
    forall_const, not_true_eq_false, false_implies] at * <;> omega

/-- A consumer inside `func`, walking or finishing is at the producer's
version, and the probe is `2V + 1`. -/
theorem InvAt.active {cfg : Config} {probe : Nat} {t : Tree} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} (h : InvAt cfg probe t p V cs) {id : Nat} (hid : id < cfg.workers) {v : Nat}
    (hph : phaseOf cs id = .inFunc v ∨ (∃ c, phaseOf cs id = .walk v c) ∨ phaseOf cs id = .finish v) :
    v = V ∧ p = .waiting v ∧ probe = 2 * v + 1 ∧ v < cfg.count := by
  have hc := h.consumers id hid
  rcases probe_cases h.probeOk h.version with hp | hp | hp
  · exfalso
    rcases hph with hph | ⟨c, hph⟩ | hph <;>
      rcases hc.1 hp with h1 | ⟨_, h1 | h1⟩ | ⟨_, h1⟩ <;> rw [hph] at h1 <;> cases h1
  · have hw := probe_odd h.probeOk h.version hp
    have hlt := h.version_lt (by rw [hw]; nofun)
    rcases hph with hph | ⟨c, hph⟩ | hph <;>
      rcases hc.2.1 hp with h1 | h1 | h1 | ⟨c', h1⟩ | h1 | (h1 | ⟨h1, _⟩) | ⟨_, h1 | h1⟩ <;>
      rw [hph] at h1 <;> cases h1 <;> exact ⟨rfl, hw, hp, hlt⟩
  · exfalso
    rcases hph with hph | ⟨c, hph⟩ | hph <;>
      rcases hc.2.2 hp with h1 | ⟨h1, _⟩ <;> rw [hph] at h1 <;> cases h1

/-! ## Geometry of the tree: the node covering every worker -/

theorem tiles_cover : ∀ (cs : List Tree) (a b id : Nat), Tiles a b cs → (∀ c ∈ cs, c.lo < c.hi) →
    a ≤ id → id < b → ∃ c ∈ cs, c.lo ≤ id ∧ id < c.hi
  | [], a, b, id, h, _, h1, h2 => by simp [Tiles] at h; omega
  | c :: cs, a, b, id, h, hlt, h1, h2 => by
    simp only [Tiles] at h
    obtain ⟨hlo, hrest⟩ := h
    by_cases hid : id < c.hi
    · exact ⟨c, by simp, by omega, hid⟩
    · obtain ⟨c', hc', h3, h4⟩ :=
        tiles_cover cs c.hi b id hrest (fun x hx => hlt x (by simp [hx])) (by omega) h2
      exact ⟨c', by simp [hc'], h3, h4⟩

theorem Wf.tiles {C W : Nat} {n : Tree} (h : Wf C W n) (hne : n.children ≠ []) :
    Tiles n.lo n.hi n.children := by
  cases h with
  | leaf => exact absurd rfl hne
  | node _ _ _ _ _ _ _ _ _ _ htiles _ => exact htiles

/-- Below every node covering a consumer there is a leaf covering it. -/
theorem descend {C W : Nat} {t : Tree} (hwf : Wf C W t) (id : Nat) :
    ∀ (m : Nat) (q : List Nat) (n : Tree), sizeOf n = m → t.get q = some n → n.lo ≤ id → id < n.hi →
      ∃ r leaf, t.get (q ++ r) = some leaf ∧ leaf.children = [] ∧ leaf.lo ≤ id ∧ id < leaf.hi := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro q n hm hq hlo hhi
    subst hm
    by_cases hnil : n.children = []
    · exact ⟨[], n, by simpa using hq, hnil, hlo, hhi⟩
    · have hwfn := Wf.get q hwf hq
      obtain ⟨c, hc, hclo, hchi⟩ := tiles_cover n.children n.lo n.hi id (hwfn.tiles hnil)
        (fun c hc => (hwfn.children_wf c hc).lo_lt_hi) hlo hhi
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
      have hck : t.get (q ++ [k]) = some c := by rw [get_child hq]; exact hk
      obtain ⟨r, leaf, hleaf, hnil', hl1, hl2⟩ :=
        ih (sizeOf c) (sizeOf_child_lt hc) (q ++ [k]) c rfl hck hclo hchi
      exact ⟨k :: r, leaf, by rw [List.append_cons]; exact hleaf, hnil', hl1, hl2⟩

/-- A node below another is no bigger. -/
theorem size_le_of_below {C W : Nat} {t : Tree} (hwf : Wf C W t) :
    ∀ (r p : List Nat) {a b : Tree}, t.get p = some a → t.get (p ++ r) = some b → b.size ≤ a.size
  | [], p, a, b, ha, hb => by
    simp only [List.append_nil] at hb
    rw [ha] at hb
    have := Option.some.inj hb
    subst this
    exact Nat.le_refl _
  | k :: r, p, a, b, ha, hb => by
    rw [List.append_cons] at hb
    cases hc : t.get (p ++ [k]) with
    | none => rw [Tree.get_append, hc] at hb; simp at hb
    | some c =>
      have h1 := child_size_le hwf ha hc
      have h2 := size_le_of_below hwf r (p ++ [k]) hc hb
      omega

/-- Every live node below a live node at `V + 1` is at `V + 1`. -/
theorem below_advanced {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t) :
    ∀ (r q : List Nat) (n : Tree), t.get q = some n → n.version = V + 1 → ¬ deadAt cfg.workers t q n →
      ∀ m, t.get (q ++ r) = some m → ¬ deadAt cfg.workers t (q ++ r) m → m.version = V + 1
  | [], q, n, hq, hver, _, m, hm, _ => by
    simp only [List.append_nil] at hm
    rw [hq] at hm
    have := Option.some.inj hm
    subst this
    exact hver
  | k :: r, q, n, hq, hver, hnd, m, hm, hdm => by
    rw [List.append_cons] at hm hdm
    cases hc : t.get (q ++ [k]) with
    | none => rw [Tree.get_append, hc] at hm; simp at hm
    | some c =>
      have hne := Tree.children_ne_nil_of_get hq hc
      have hk : k < n.children.length := lt_length_of_getElem?' _ _ _ ((get_child hq k).symm.trans hc)
      obtain ⟨hcb, -⟩ := (hinv.nodes q n hq).live hne hnd
      obtain ⟨c', hc', hle, -⟩ := hcb k hk
      rw [hc] at hc'
      have := Option.some.inj hc'
      subst this
      have hcv : c.version = V + 1 := by
        have := (hinv.nodes _ c hc).version_le
        omega
      exact below_advanced hwf hinv r (q ++ [k]) c hc hcv (live_child hwf hq hk hc hnd) m hm hdm

set_option linter.deprecated false in
/-- When a node covering every worker reaches `V + 1`, every consumer is
past its work for `V`: finishing, waiting for `V + 1`, or done. -/
theorem others_done {cfg : Config} {V : Nat} {phase : Nat → ConsumerPhase} {t : Tree}
    (hwf : Wf cfg.cluster cfg.workers t) (hinv : TreeInv cfg V phase t)
    {q : List Nat} {n : Tree} (hq : t.get q = some n) (hsize : n.size = cfg.workers)
    (hver : n.version = V + 1)
    (hcons : ∀ j, j < cfg.workers → phase j = .waitReady V ∨ phase j = .beforeFunc V ∨
      phase j = .inFunc V ∨ (∃ c, phase j = .walk V c) ∨ phase j = .finish V ∨
      Finished cfg V (phase j) ∨ (V = 0 ∧ (phase j = .start ∨ phase j = .initializing))) :
    ∀ j, j < cfg.workers → phase j = .finish V ∨ Finished cfg V (phase j) := by
  intro j hj
  have hnd : ¬ deadAt cfg.workers t q n := fun hd => by
    have := ((hinv.nodes q n hq).dead hd).1
    omega
  have hwfn := Wf.get q hwf hq
  have hwin : n.lo = 0 ∧ n.hi = cfg.workers := by
    have := hwfn.hi_le
    have := hwfn.lo_lt_hi
    simp only [Tree.size] at hsize
    omega
  obtain ⟨r, leaf, hleaf, hnil, hl1, hl2⟩ :=
    descend hwf j (sizeOf n) q n rfl hq (by omega) (by omega)
  have hpath := hinv.leaf_unique (q ++ r) leaf hleaf hnil j hl1 hl2
  have hlv : leaf.version = V + 1 :=
    below_advanced hwf hinv r q n hq hver hnd leaf hleaf (not_deadAt_of_leaf hnil)
  obtain ⟨hb, -, -⟩ := (hinv.nodes _ leaf hleaf).leaf hnil
  have hld := (hb j hl1 hl2).1
  rw [hlv] at hld
  rcases hcons j hj with h | h | h | ⟨c, h⟩ | h | h | ⟨-, h | h⟩
  · exfalso; rw [h] at hld; simp only [leafDone] at hld; omega
  · exfalso; rw [h] at hld; simp only [leafDone] at hld; omega
  · exfalso; rw [h] at hld; simp only [leafDone] at hld; omega
  · exfalso
    rw [h, leafDone_walk] at hld
    by_cases hcp : c.path = q ++ r
    · rw [if_pos (by simp [hcp])] at hld
      omega
    · -- the consumer carries towards a node strictly above its leaf
      have hpre : c.path <+: q ++ r := by rw [hpath]; exact hinv.walkers j hj V c h
      obtain ⟨m, hm⟩ : ∃ m, t.get c.path = some m := by
        obtain ⟨r', hr'⟩ := hpre
        rw [← hr', Tree.get_append] at hleaf
        cases hm : t.get c.path with
        | none => rw [hm] at hleaf; simp at hleaf
        | some m => exact ⟨m, rfl⟩
      have hmv : V = m.version := (hinv.nodes _ m hm).carried_version j hj V c h rfl
      -- that node is live: something is carried towards it
      have hmd : ¬ deadAt cfg.workers t c.path m := fun hd => by
        obtain ⟨-, -, h0⟩ := (hinv.nodes _ m hm).dead hd
        have h1 := carryOf_le_carriedTo cfg.workers c.path phase j hj
        rw [h, carryOf_walk, if_pos rfl] at h1
        have h2 := hinv.carry_pos j hj V c h
        omega
      rcases List.prefix_or_prefix_of_prefix hpre (List.prefix_append q r) with ⟨r', hr'⟩ | ⟨r', hr'⟩
      · -- above (or at) `n`: then it has a child covering every worker, so it is dead
        cases r' with
        | nil =>
          simp only [List.append_nil] at hr'
          rw [hr'] at hm
          rw [hq] at hm
          have := Option.some.inj hm
          subst this
          omega
        | cons k r'' =>
          apply hmd
          rw [List.append_cons] at hr'
          obtain ⟨m', hm'⟩ : ∃ m', t.get (c.path ++ [k]) = some m' := by
            have hq' := hq
            rw [← hr', Tree.get_append] at hq'
            cases hm' : t.get (c.path ++ [k]) with
            | none => rw [hm'] at hq'; simp at hq'
            | some m' => exact ⟨m', rfl⟩
          refine ⟨k, lt_length_of_getElem?' _ _ _ ((get_child hm k).symm.trans hm'), m', hm', ?_⟩
          have h1 := size_le_of_below hwf r'' (c.path ++ [k]) hm' (by rw [hr']; exact hq)
          have h2 := (Wf.get _ hwf hm').size_le
          omega
      · -- below `n`: live nodes there are at `V + 1`
        have := below_advanced hwf hinv r' q n hq hver hnd m (by rw [hr']; exact hm)
          (by rw [hr']; exact hmd)
        omega
  · exact Or.inl h
  · exact Or.inr h
  · exfalso; rw [h] at hld; simp only [leafDone] at hld; omega
  · exfalso; rw [h] at hld; simp only [leafDone] at hld; omega

/-! ## Preservation -/

theorem not_finished_of_ne {cfg : Config} {V : Nat} {ph : ConsumerPhase}
    (h1 : ph ≠ .waitReady (V + 1)) (h2 : ph ≠ .done) : ¬ Finished cfg V ph := by
  rintro (h | ⟨h, -⟩)
  · exact h1 h
  · exact h2 h

/-- A consumer move that neither bumps the probe nor enters `finish`. -/
theorem InvAt.simple_move {cfg : Config} {probe : Nat} {t : Tree} {p : ProducerPhase} {V : Nat}
    {cs : Array ConsumerPhase} (h : InvAt cfg probe t p V cs) {id : Nat} (hid : id < cfg.workers)
    {ph' : ConsumerPhase} (hnf : ¬ Finished cfg V (phaseOf cs id))
    (hnf' : ph' ≠ .finish V) (hok : ConsumerOk cfg V probe ph')
    {t' : Tree} (hwf : Wf cfg.cluster cfg.workers t')
    (htree : TreeInv cfg V (phaseOf (cs.setIfInBounds id ph')) t') :
    InvAt cfg probe t' p V (cs.setIfInBounds id ph') := by
  have hsize : id < cs.size := by rw [h.size]; exact hid
  refine ⟨h.version, by rw [Array.size_setIfInBounds]; exact h.size, hwf, htree, h.probeOk,
    h.version_lt, ?_, ?_⟩
  · intro j hj
    rw [phaseOf_setIfInBounds _ _ _ hsize]
    by_cases hji : j = id
    · subst hji; rw [upd_self]; exact hok
    · rw [upd_ne _ _ _ hji]; exact h.consumers j hj
  · intro i hi hfin
    exfalso
    rw [phaseOf_setIfInBounds _ _ _ hsize] at hfin
    by_cases hii : i = id
    · subst hii; rw [upd_self] at hfin; exact hnf' hfin
    · rw [upd_ne _ _ _ hii] at hfin
      exact hnf (h.finisher i hi hfin id hid (Ne.symm hii))

theorem nextConsumer_finished {cfg : Config} {V : Nat} (hV : V < cfg.count) :
    Finished cfg V (nextConsumer cfg V) := by
  unfold nextConsumer Finished
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, by omega⟩

/-- The producer's steps. -/
theorem step_producer_inv {cfg : Config} {s s' : State} {ev : Option Event}
    (hinv : Inv cfg s) (h : step cfg s .producer = .step s' ev) : Inv cfg s' := by
  obtain ⟨p, p', pr, hp, hmove, hp', hpr, hcs, ht⟩ := step_producer_move h
  show InvAt cfg s'.probe s'.tree s'.producer (s'.producer.version cfg) s'.consumers
  rw [hp', hpr, hcs, ht]
  have hinv : InvAt cfg s.probe s.tree p (p.version cfg) s.consumers := by rw [← hp]; exact hinv
  cases hmove with
  | beforeWrite v =>
    have hinv : InvAt cfg s.probe s.tree (.beforeWrite v) v s.consumers := hinv
    exact ⟨rfl, hinv.size, hinv.wf, hinv.tree, hinv.probeOk, fun _ => hinv.version_lt nofun,
      hinv.consumers, hinv.finisher⟩
  | writing v =>
    have hinv : InvAt cfg s.probe s.tree (.writing v) v s.consumers := hinv
    exact ⟨rfl, hinv.size, hinv.wf, hinv.tree, hinv.probeOk, fun _ => hinv.version_lt nofun,
      hinv.consumers, hinv.finisher⟩
  | publish v =>
    have hinv : InvAt cfg s.probe s.tree (.publish v) v s.consumers := hinv
    have hprobe : s.probe = 2 * v := hinv.probeOk
    have hlt : v < cfg.count := hinv.version_lt nofun
    show InvAt cfg (s.probe + 1) s.tree (.waiting v) v s.consumers
    refine ⟨rfl, hinv.size, hinv.wf, hinv.tree, Or.inl (by omega), fun _ => hlt, ?_, ?_⟩
    · intro id hid
      have hc := (hinv.consumers id hid).1 hprobe
      refine ⟨fun h => by omega, fun _ => ?_, fun h => by omega⟩
      rcases hc with hc | ⟨h0, hc⟩ | ⟨hc, -⟩
      · exact Or.inl hc
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, hc⟩)))))
      · omega
    · intro i hi hfin
      exfalso
      rcases (hinv.consumers i hi).1 hprobe with hc | ⟨-, hc | hc⟩ | ⟨-, hc⟩ <;>
        rw [hfin] at hc <;> cases hc
  | waiting v heq =>
    have hinv : InvAt cfg s.probe s.tree (.waiting v) v s.consumers := hinv
    show InvAt cfg s.probe s.tree (.beforeComplete v) v s.consumers
    exact ⟨rfl, hinv.size, hinv.wf, hinv.tree, by show s.probe = 2 * v + 2; omega,
      fun _ => hinv.version_lt nofun, hinv.consumers, hinv.finisher⟩
  | beforeComplete v =>
    have hinv : InvAt cfg s.probe s.tree (.beforeComplete v) v s.consumers := hinv
    exact ⟨rfl, hinv.size, hinv.wf, hinv.tree, hinv.probeOk, fun _ => hinv.version_lt nofun,
      hinv.consumers, hinv.finisher⟩
  | completing v =>
    have hinv : InvAt cfg s.probe s.tree (.completing v) v s.consumers := hinv
    have hprobe : s.probe = 2 * v + 2 := hinv.probeOk
    have hlt : v < cfg.count := hinv.version_lt nofun
    have hall : ∀ id, id < cfg.workers →
        phaseOf s.consumers id = .waitReady (v + 1) ∨ (phaseOf s.consumers id = .done ∧ cfg.count = v + 1) := by
      intro id hid
      rcases (hinv.consumers id hid).2.2 hprobe with hc | ⟨hc, hcount⟩
      · exact Or.inl hc
      · exact Or.inr ⟨hc, hcount.symm⟩
    have htree := advance_preserves hinv.wf hinv.tree hall
    unfold nextProducer
    split
    · rename_i hnext
      show InvAt cfg s.probe s.tree (.beforeWrite (v + 1)) (v + 1) s.consumers
      refine ⟨rfl, hinv.size, hinv.wf, htree, by show s.probe = 2 * (v + 1); omega, fun _ => hnext, ?_, ?_⟩
      · intro id hid
        refine ⟨fun _ => ?_, fun h => by omega, fun h => by omega⟩
        rcases hall id hid with hc | ⟨hc, hcount⟩
        · exact Or.inl hc
        · omega
      · intro i hi hfin
        exfalso
        rcases hall i hi with hc | ⟨hc, -⟩ <;> rw [hfin] at hc <;> cases hc
    · rename_i hnext
      have hcount : cfg.count = v + 1 := by omega
      show InvAt cfg s.probe s.tree .done cfg.count s.consumers
      refine ⟨rfl, hinv.size, hinv.wf, ?_, by show s.probe = 2 * cfg.count; omega, fun h => absurd rfl h,
        ?_, ?_⟩
      · rw [hcount]; exact htree
      · intro id hid
        refine ⟨fun _ => ?_, fun h => by omega, fun h => by omega⟩
        rcases hall id hid with hc | ⟨hc, -⟩
        · rw [hc, hcount]; exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨rfl, hc⟩)
      · intro i hi hfin
        exfalso
        rcases hall i hi with hc | ⟨hc, -⟩ <;> rw [hfin] at hc <;> cases hc

/-- The consumers' steps. -/
theorem step_consumer_inv {cfg : Config} {s s' : State} {id : Nat} {ev : Option Event}
    (hinv : Inv cfg s) (h : step cfg s (.consumer id) = .step s' ev) : Inv cfg s' := by
  obtain ⟨ph, ph', t', hph, hmove, hcs, ht, hprod, hprobe⟩ := step_consumer_move h
  have hid : id < cfg.workers := by
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hph
    rw [hinv.size] at hlt
    exact hlt
  have hsize : id < s.consumers.size := by rw [hinv.size]; exact hid
  have hph' : phaseOf s.consumers id = ph := phaseOf_eq hph
  have hV : ∀ v, (∃ c, s.consumers[id]? = some (.walk v c)) ∨ s.consumers[id]? = some (.inFunc v) ∨
      s.consumers[id]? = some (.finish v) → v = s.producer.version cfg ∧ s.producer.version cfg < cfg.count := by
    intro v hv
    have := hinv.active hid (v := v) (by
      rcases hv with ⟨c, hc⟩ | hc | hc
      · exact Or.inr (Or.inl ⟨c, phaseOf_eq hc⟩)
      · exact Or.inl (phaseOf_eq hc)
      · exact Or.inr (Or.inr (phaseOf_eq hc)))
    obtain ⟨h1, -, -, h4⟩ := this
    exact ⟨h1, h1 ▸ h4⟩
  have htree := step_consumer_treeInv hinv.wf hinv.tree hinv.size hid hV h
  rw [hcs, ht] at htree
  show InvAt cfg s'.probe s'.tree s'.producer (s'.producer.version cfg) s'.consumers
  rw [hprod, hprobe, hcs, ht]
  have hle : s.probe ≤ 2 * s.producer.version cfg + 2 := by
    rcases probe_cases hinv.probeOk hinv.version with hp | hp | hp <;> omega
  cases hmove with
  | start =>
    show InvAt cfg s.probe s.tree s.producer _ _
    refine hinv.simple_move (ph' := .initializing) hid (by rw [hph']; exact not_finished_of_ne nofun nofun)
      nofun ?_ hinv.wf htree
    have hc := hinv.consumers id hid
    rw [hph'] at hc
    refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
    · rcases hc.1 hp with h1 | ⟨h0, -⟩ | ⟨-, h1⟩
      · cases h1
      · exact Or.inr (Or.inl ⟨h0, Or.inr rfl⟩)
      · cases h1
    · rcases hc.2.1 hp with h1 | h1 | h1 | ⟨c, h1⟩ | h1 | h1 | ⟨h0, -⟩
      · cases h1
      · cases h1
      · cases h1
      · cases h1
      · cases h1
      · exact absurd h1 (not_finished_of_ne nofun nofun)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, Or.inr rfl⟩)))))
    · exact absurd (hc.2.2 hp) (not_finished_of_ne nofun nofun)
  | initializing =>
    show InvAt cfg s.probe s.tree s.producer _ _
    refine hinv.simple_move (ph' := if cfg.count = 0 then .done else .waitReady 0) hid
      (by rw [hph']; exact not_finished_of_ne nofun nofun) (by split <;> nofun) ?_ hinv.wf htree
    have hc := hinv.consumers id hid
    rw [hph'] at hc
    -- the consumer is at version 0
    have h0 : s.producer.version cfg = 0 := by
      rcases probe_cases hinv.probeOk hinv.version with hp | hp | hp
      · rcases hc.1 hp with h1 | ⟨h0, -⟩ | ⟨-, h1⟩
        · cases h1
        · exact h0
        · cases h1
      · rcases hc.2.1 hp with h1 | h1 | h1 | ⟨c, h1⟩ | h1 | h1 | ⟨h0, -⟩
        · cases h1
        · cases h1
        · cases h1
        · cases h1
        · cases h1
        · exact absurd h1 (not_finished_of_ne nofun nofun)
        · exact h0
      · exact absurd (hc.2.2 hp) (not_finished_of_ne nofun nofun)
    rw [h0] at hc ⊢
    split
    · -- `count = 0`: the producer was done from the start, the probe is `0`
      rename_i hcount
      refine ⟨fun _ => Or.inr (Or.inr ⟨hcount.symm, rfl⟩), fun hp => ?_, fun hp => ?_⟩
      · exfalso
        have := probe_odd hinv.probeOk hinv.version (by rw [h0]; exact hp)
        have := hinv.version_lt (by rw [this]; nofun)
        omega
      · exfalso
        have := hinv.probe_le
        omega
    · refine ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun hp => ?_⟩
      exact absurd (hc.2.2 hp) (not_finished_of_ne nofun nofun)
  | waitReady v hgt =>
    show InvAt cfg s.probe s.tree s.producer _ _
    have hc := hinv.consumers id hid
    rw [hph'] at hc
    -- the guard rules out `v = V + 1`, so `v = V` and the probe is `2V + 1`
    have hvp : v = s.producer.version cfg ∧ s.probe = 2 * s.producer.version cfg + 1 := by
      rcases probe_cases hinv.probeOk hinv.version with hp | hp | hp
      · rcases hc.1 hp with h1 | ⟨-, h1 | h1⟩ | ⟨-, h1⟩
        · injection h1 with h1; omega
        · cases h1
        · cases h1
        · cases h1
      · rcases hc.2.1 hp with h1 | h1 | h1 | ⟨c, h1⟩ | h1 | (h1 | ⟨h1, -⟩) | ⟨-, h1 | h1⟩
        · injection h1 with h1; omega
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
    obtain ⟨rfl, hp⟩ := hvp
    refine hinv.simple_move (ph' := .beforeFunc _) hid
      (by rw [hph']; exact not_finished_of_ne (by intro h; injection h with h; omega) nofun)
      nofun ⟨fun h => by omega, fun _ => Or.inr (Or.inl rfl), fun h => by omega⟩ hinv.wf htree
  | beforeFunc v =>
    show InvAt cfg s.probe s.tree s.producer _ _
    have hc := hinv.consumers id hid
    rw [hph'] at hc
    have hvp : v = s.producer.version cfg ∧ s.probe = 2 * s.producer.version cfg + 1 := by
      rcases probe_cases hinv.probeOk hinv.version with hp | hp | hp
      · rcases hc.1 hp with h1 | ⟨-, h1 | h1⟩ | ⟨-, h1⟩ <;> cases h1
      · rcases hc.2.1 hp with h1 | h1 | h1 | ⟨c, h1⟩ | h1 | h1 | ⟨-, h1 | h1⟩
        · cases h1
        · injection h1 with h1; omega
        · cases h1
        · cases h1
        · cases h1
        · exact absurd h1 (not_finished_of_ne nofun nofun)
        · cases h1
        · cases h1
      · exact absurd (hc.2.2 hp) (not_finished_of_ne nofun nofun)
    obtain ⟨rfl, hp⟩ := hvp
    refine hinv.simple_move (ph' := .inFunc _) hid (by rw [hph']; exact not_finished_of_ne nofun nofun)
      nofun ⟨fun h => by omega, fun _ => Or.inr (Or.inr (Or.inl rfl)), fun h => by omega⟩ hinv.wf htree
  | inFunc v =>
    show InvAt cfg s.probe s.tree s.producer _ _
    obtain ⟨rfl, -, hp, -⟩ := hinv.active hid (Or.inl hph')
    refine hinv.simple_move (ph' := .walk _ (Cursor.start cfg id)) hid
      (by rw [hph']; exact not_finished_of_ne nofun nofun)
      nofun ⟨fun h => by omega, fun _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))), fun h => by omega⟩
      hinv.wf htree
  | walk v c t' vc' rmw next hw =>
    obtain ⟨rfl, -, hp, hlt⟩ := hinv.active hid (Or.inr (Or.inl ⟨c, hph'⟩))
    have hwf' := walk_wf hinv.wf hw
    cases next with
    | stop =>
      show InvAt cfg s.probe t' s.producer _ _
      refine hinv.simple_move (ph' := nextPhase cfg _ .stop) hid
        (by rw [hph']; exact not_finished_of_ne nofun nofun)
        (by show nextConsumer cfg _ ≠ _; unfold nextConsumer; split <;> nofun)
        ⟨fun h => by omega, fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))),
          fun h => by omega⟩ hwf' htree
      exact nextConsumer_finished hlt
    | «continue» c' =>
      show InvAt cfg s.probe t' s.producer _ _
      refine hinv.simple_move (ph' := nextPhase cfg _ (.continue c')) hid
        (by rw [hph']; exact not_finished_of_ne nofun nofun)
        nofun ⟨fun h => by omega, fun _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))), fun h => by omega⟩
        hwf' htree
    | finished =>
      -- the consumer filled the node covering every worker
      show InvAt cfg s.probe t' s.producer _ (s.consumers.setIfInBounds id (.finish _))
      obtain ⟨node, hnode, -, -, -, -, -, -, ⟨node', hnode', hlo, hhi, -, -, hfill⟩, hfin, -, -⟩ :=
        walk_spec hw
      obtain ⟨hfull, hsizeW⟩ := hfin.mp rfl
      have hsize' : node'.size = cfg.workers := by
        simp only [Tree.size] at hsizeW ⊢
        rw [hlo, hhi]; exact hsizeW
      have hver' := (hfill hfull).1
      rw [phaseOf_setIfInBounds _ _ _ hsize] at htree
      have hothers := others_done hwf' htree hnode' hsize' hver' (fun j hj => by
        by_cases hji : j = id
        · subst hji; rw [upd_self]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rw [upd_ne _ _ _ hji]
          exact (hinv.consumers j hj).2.1 hp)
      refine ⟨hinv.version, by rw [Array.size_setIfInBounds]; exact hinv.size, hwf', ?_, hinv.probeOk,
        hinv.version_lt, ?_, ?_⟩
      · rw [phaseOf_setIfInBounds _ _ _ hsize]; exact htree
      · intro j hj
        rw [phaseOf_setIfInBounds _ _ _ hsize]
        by_cases hji : j = id
        · subst hji
          rw [upd_self]
          exact ⟨fun h => by omega, fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
            fun h => by omega⟩
        · rw [upd_ne _ _ _ hji]; exact hinv.consumers j hj
      · intro i hi hfin'
        rw [phaseOf_setIfInBounds _ _ _ hsize] at hfin'
        by_cases hii : i = id
        · subst hii
          intro j hj hji
          rw [phaseOf_setIfInBounds _ _ _ hsize, upd_ne _ _ _ hji]
          rcases hothers j hj with hj' | hj'
          · exfalso
            rw [upd_ne _ _ _ hji] at hj'
            have := hinv.finisher j hj hj' i hid (Ne.symm hji)
            rw [hph'] at this
            exact absurd this (not_finished_of_ne nofun nofun)
          · rw [upd_ne _ _ _ hji] at hj'; exact hj'
        · exfalso
          rw [upd_ne _ _ _ hii] at hfin'
          have := hinv.finisher i hi hfin' id hid (Ne.symm hii)
          rw [hph'] at this
          exact absurd this (not_finished_of_ne nofun nofun)
  | finish v =>
    obtain ⟨hv, hw, hp, hlt⟩ := hinv.active hid (Or.inr (Or.inr hph'))
    show InvAt cfg (s.probe + 1) s.tree s.producer _ _
    have hothers := hinv.finisher id hid (by rw [hph', hv])
    refine ⟨hinv.version, by rw [Array.size_setIfInBounds]; exact hinv.size, hinv.wf, htree, ?_,
      hinv.version_lt, ?_, ?_⟩
    · rw [hw]; exact Or.inr (by show s.probe + 1 = 2 * v + 2; omega)
    · intro j hj
      rw [phaseOf_setIfInBounds _ _ _ hsize]
      refine ⟨fun h => by omega, fun h => by omega, fun _ => ?_⟩
      by_cases hji : j = id
      · subst hji; rw [upd_self]; rw [← hv]; exact nextConsumer_finished hlt
      · rw [upd_ne _ _ _ hji]; exact hothers j hj hji
    · intro i hi hfin
      exfalso
      rw [phaseOf_setIfInBounds _ _ _ hsize] at hfin
      by_cases hii : i = id
      · subst hii
        rw [upd_self] at hfin
        unfold nextConsumer at hfin
        split at hfin <;> cases hfin
      · rw [upd_ne _ _ _ hii] at hfin
        have := hothers i hi hii
        rw [hfin] at this
        exact absurd this (not_finished_of_ne nofun nofun)

/-- Every step of the model preserves the invariant. -/
theorem step_inv {cfg : Config} {s s' : State} {t : Thread} {ev : Option Event}
    (hinv : Inv cfg s) (h : step cfg s t = .step s' ev) : Inv cfg s' := by
  cases t with
  | producer => exact step_producer_inv hinv h
  | consumer id => exact step_consumer_inv hinv h

/-- The invariant holds at the start, for every valid configuration. -/
theorem init_inv (cfg : Config) (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) :
    Inv cfg (State.init cfg) := by
  have htree := init_treeInv cfg hW hC
  rw [← phaseOf_replicate cfg.workers] at htree
  show InvAt cfg 0 (Tree.init cfg) (if cfg.count = 0 then .done else .beforeWrite 0)
    ((if cfg.count = 0 then ProducerPhase.done else .beforeWrite 0).version cfg)
    (Array.replicate cfg.workers .start)
  split
  · rename_i hcount
    show InvAt cfg 0 (Tree.init cfg) .done cfg.count (Array.replicate cfg.workers .start)
    refine ⟨rfl, Array.size_replicate, init_wf cfg hW hC, by rw [hcount]; exact htree,
      by show 0 = 2 * cfg.count; omega, fun h => absurd rfl h, ?_, ?_⟩
    · intro id hid
      rw [phaseOf_replicate]
      exact ⟨fun _ => Or.inr (Or.inl ⟨hcount, Or.inl rfl⟩), fun h => by omega, fun h => by omega⟩
    · intro i hi hfin
      rw [phaseOf_replicate] at hfin
      cases hfin
  · rename_i hcount
    show InvAt cfg 0 (Tree.init cfg) (.beforeWrite 0) 0 (Array.replicate cfg.workers .start)
    refine ⟨rfl, Array.size_replicate, init_wf cfg hW hC, htree, rfl, fun _ => by omega, ?_, ?_⟩
    · intro id hid
      rw [phaseOf_replicate]
      exact ⟨fun _ => Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩), fun h => by omega, fun h => by omega⟩
    · intro i hi hfin
      rw [phaseOf_replicate] at hfin
      cases hfin

/-! ## Reachable states -/

/-- The states the model can reach from `State.init`. -/
inductive Reachable (cfg : Config) : State → Prop
  | init : Reachable cfg (State.init cfg)
  | step {s s' : State} {t : Thread} {ev : Option Event} :
      Reachable cfg s → step cfg s t = .step s' ev → Reachable cfg s'

theorem reachable_inv {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) {s : State}
    (h : Reachable cfg s) : Inv cfg s := by
  induction h with
  | init => exact init_inv cfg hW hC
  | step _ hstep ih => exact step_inv ih hstep

/-- The probe never runs ahead of the protocol (`Spec.violations`'s counter
clause). -/
theorem reachable_probe_le {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) {s : State}
    (h : Reachable cfg s) : s.probe ≤ 2 * cfg.count :=
  (reachable_inv hW hC h).probe_le

end RearmBarrier
