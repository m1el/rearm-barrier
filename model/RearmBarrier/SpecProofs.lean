import RearmBarrier.TreeCheck
import RearmBarrier.Spec

/-!
# `Spec.violations` is empty in every reachable state

`violations` is what the explorer and the trace replay check. Its clauses
about the counters and the tree follow from `Inv` (`Inv.probe_le`,
`Inv.invariant_nil`); the race clauses follow from `ConsumerOk` (nobody is
inside `func` while the producer writes the job, nobody writes a result
while it runs `complete`); the two data clauses need what `Inv` does not
track, the job slot and the result slots. `DataInv` adds that: the job slot
is a function of the producer's phase (`JobOk`) and every result slot is a
function of its consumer's phase (`ResultOk`). Both are preserved by every
step given `Inv`, so `reachable_violations_nil` and, at a final state,
`reachable_finalViolations_nil`.
-/

namespace RearmBarrier

/-- The job slot in every producer phase. -/
def JobOk (cfg : Config) : ProducerPhase → Option Nat → Prop
  | .beforeWrite v, job => job = (if v = 0 then none else some (v - 1))
  | .writing _, job => job = none
  | .publish v, job | .waiting v, job | .beforeComplete v, job | .completing v, job => job = some v
  | .done, job => job = (if cfg.count = 0 then none else some (cfg.count - 1))

/-- A consumer's result slot in every phase. -/
def ResultOk (cfg : Config) : ConsumerPhase → Option Nat → Prop
  | .start, r | .initializing, r => r = none
  | .waitReady v, r | .beforeFunc v, r | .inFunc v, r => r = (if v = 0 then none else some (v - 1))
  | .walk v _, r | .finish v, r => r = some v
  | .done, r => r = (if cfg.count = 0 then none else some (cfg.count - 1))

structure DataInv (cfg : Config) (s : State) : Prop where
  job : JobOk cfg s.producer s.job
  size : s.results.size = cfg.workers
  results : ∀ id, id < cfg.workers →
    ∃ r, s.results[id]? = some r ∧ ResultOk cfg (phaseOf s.consumers id) r

theorem init_dataInv (cfg : Config) : DataInv cfg (State.init cfg) := by
  refine ⟨?_, Array.size_replicate, ?_⟩
  · show JobOk cfg (if cfg.count = 0 then .done else .beforeWrite 0) none
    split
    · rename_i h; simp [JobOk, h]
    · simp [JobOk]
  · intro id hid
    refine ⟨none, ?_, ?_⟩
    · show (Array.replicate cfg.workers (none : Option Nat))[id]? = some none
      simp [hid]
    · show ResultOk cfg (phaseOf (Array.replicate cfg.workers .start) id) none
      rw [phaseOf_replicate]
      rfl

theorem step_producer_dataInv {cfg : Config} {s s' : State} {ev : Option Event}
    (hinv : Inv cfg s) (hd : DataInv cfg s) (h : step cfg s .producer = .step s' ev) : DataInv cfg s' := by
  obtain ⟨p, p', pr, hp, hmove, hp', hpr, hcs, ht, hjob, hres⟩ := step_producer_move h
  have hinv : InvAt cfg s.probe s.tree p (p.version cfg) s.consumers := by rw [← hp]; exact hinv
  have hj : JobOk cfg p s.job := by rw [← hp]; exact hd.job
  refine ⟨?_, by rw [hres]; exact hd.size, ?_⟩
  · rw [hp', hjob]
    cases hmove with
    | beforeWrite v => exact rfl
    | writing v => exact rfl
    | publish v => exact hj
    | waiting v _ => exact hj
    | beforeComplete v => exact hj
    | completing v =>
      have hinv : InvAt cfg s.probe s.tree (.completing v) v s.consumers := hinv
      have hlt : v < cfg.count := hinv.version_lt nofun
      have hj : s.job = some v := hj
      unfold nextProducer
      split
      · show jobAfter s.job (.completing v) = if v + 1 = 0 then none else some (v + 1 - 1)
        simp [jobAfter, hj]
      · rename_i hn
        have : cfg.count = v + 1 := by omega
        show jobAfter s.job (.completing v) = if cfg.count = 0 then none else some (cfg.count - 1)
        simp [jobAfter, hj, this]
  · intro id hid
    rw [hcs, hres]
    exact hd.results id hid

theorem step_consumer_dataInv {cfg : Config} {s s' : State} {id : Nat} {ev : Option Event}
    (hinv : Inv cfg s) (hd : DataInv cfg s) (h : step cfg s (.consumer id) = .step s' ev) :
    DataInv cfg s' := by
  obtain ⟨ph, ph', t', hph, hmove, hcs, ht, hprod, hprobe, hjob, hres⟩ := step_consumer_move h
  have hid : id < cfg.workers := by
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hph
    rw [hinv.size] at hlt
    exact hlt
  have hsize : id < s.consumers.size := by rw [hinv.size]; exact hid
  have hrsize : id < s.results.size := by rw [hd.size]; exact hid
  have hph' : phaseOf s.consumers id = ph := phaseOf_eq hph
  refine ⟨by rw [hprod, hjob]; exact hd.job, ?_, ?_⟩
  · rw [hres]; cases ph <;> simp [resultsAfter, hd.size]
  · intro j hj
    rw [hcs, hres, phaseOf_setIfInBounds _ _ _ hsize]
    obtain ⟨r, hr, hok⟩ := hd.results j hj
    by_cases hji : j = id
    · subst hji
      rw [upd_self]
      rw [hph'] at hok
      cases hmove with
      | start => exact ⟨r, hr, hok⟩
      | initializing =>
        refine ⟨none, ?_, ?_⟩
        · show (s.results.setIfInBounds j none)[j]? = some none
          simp [hrsize]
        · split <;> simp_all [ResultOk]
      | waitReady v _ => exact ⟨r, hr, hok⟩
      | beforeFunc v => exact ⟨r, hr, hok⟩
      | inFunc v =>
        refine ⟨some v, ?_, rfl⟩
        show (s.results.setIfInBounds j (some v))[j]? = some (some v)
        simp [hrsize]
      | walk v c t' vc' rmw next hw =>
        obtain ⟨-, -, -, hlt⟩ := hinv.active hj (Or.inr (Or.inl ⟨c, hph'⟩))
        have hok : r = some v := hok
        refine ⟨r, hr, ?_⟩
        cases next with
        | finished => exact hok
        | «continue» c' => exact hok
        | stop =>
          show ResultOk cfg (nextConsumer cfg v) r
          unfold nextConsumer
          split
          · simp [ResultOk, hok]
          · have : cfg.count = v + 1 := by omega
            simp [ResultOk, hok, this]
      | finish v =>
        obtain ⟨-, -, -, hlt⟩ := hinv.active hj (Or.inr (Or.inr hph'))
        have hok : r = some v := hok
        refine ⟨r, hr, ?_⟩
        unfold nextConsumer
        split
        · simp [ResultOk, hok]
        · have : cfg.count = v + 1 := by omega
          simp [ResultOk, hok, this]
    · rw [upd_ne _ _ _ hji]
      refine ⟨r, ?_, hok⟩
      cases ph <;> simp [resultsAfter, Ne.symm hji, hr]

theorem step_dataInv {cfg : Config} {s s' : State} {t : Thread} {ev : Option Event}
    (hinv : Inv cfg s) (hd : DataInv cfg s) (h : step cfg s t = .step s' ev) : DataInv cfg s' := by
  cases t with
  | producer => exact step_producer_dataInv hinv hd h
  | consumer id => exact step_consumer_dataInv hinv hd h

theorem reachable_dataInv {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) {s : State}
    (h : Reachable cfg s) : DataInv cfg s := by
  induction h with
  | init => exact init_dataInv cfg
  | step hr hstep ih => exact step_dataInv (reachable_inv hW hC hr) ih hstep

/-! ## The checks -/

/-- `Inv` at a known producer phase. -/
theorem Inv.at {cfg : Config} {s : State} {p : ProducerPhase} (h : Inv cfg s) (hp : s.producer = p) :
    InvAt cfg s.probe s.tree p (p.version cfg) s.consumers := by
  subst hp; exact h

/-- An entry of `zipIdx` over an array is an in-bounds element. -/
theorem mem_toList_zipIdx {α : Type} {xs : Array α} {x : α} {i : Nat} (h : (x, i) ∈ xs.toList.zipIdx) :
    xs[i]? = some x := by
  have := List.mem_zipIdx_iff_getElem?.mp h
  simpa using this

theorem violations_nil {cfg : Config} {s : State} (hinv : Inv cfg s) (hd : DataInv cfg s) :
    violations cfg s = [] := by
  have hcons : ∀ ph i, (ph, i) ∈ s.consumers.toList.zipIdx → i < cfg.workers ∧ phaseOf s.consumers i = ph := by
    intro ph i h
    have hi := mem_toList_zipIdx h
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hi
    rw [hinv.size] at hlt
    exact ⟨hlt, phaseOf_eq hi⟩
  unfold violations
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hinv.invariant_nil⟩
  · -- the producer writes the job only while nobody is inside `func`
    cases hp : s.producer <;> try rfl
    rename_i v
    have hinv : InvAt cfg s.probe s.tree (.writing v) v s.consumers := hinv.at hp
    have hprobe : s.probe = 2 * v := hinv.probeOk
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    obtain ⟨ph, i⟩ := x
    obtain ⟨hi, hph⟩ := hcons ph i hx
    rcases (hinv.consumers i hi).1 hprobe with h1 | ⟨-, h1 | h1⟩ | ⟨-, h1⟩ <;> rw [hph] at h1 <;>
      subst h1 <;> rfl
  · -- the producer runs `complete` only while nobody writes a result
    cases hp : s.producer <;> try rfl
    rename_i v
    have hinv : InvAt cfg s.probe s.tree (.completing v) v s.consumers := hinv.at hp
    have hprobe : s.probe = 2 * v + 2 := hinv.probeOk
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    obtain ⟨ph, i⟩ := x
    obtain ⟨hi, hph⟩ := hcons ph i hx
    rcases (hinv.consumers i hi).2.2 hprobe with h1 | ⟨h1, -⟩ <;> rw [hph] at h1 <;> subst h1 <;> rfl
  · -- `func` sees the job of its version
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    obtain ⟨ph, i⟩ := x
    obtain ⟨hi, hph⟩ := hcons ph i hx
    cases ph <;> try rfl
    rename_i v
    obtain ⟨-, hw, -, -⟩ := hinv.active hi (Or.inl hph)
    have hjob := hd.job
    rw [hw] at hjob
    have hjob : s.job = some v := hjob
    simp [hjob]
  · -- `complete` sees every result of its version
    cases hp : s.producer <;> try rfl
    rename_i v
    have hinv : InvAt cfg s.probe s.tree (.completing v) v s.consumers := hinv.at hp
    have hprobe : s.probe = 2 * v + 2 := hinv.probeOk
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    obtain ⟨r, i⟩ := x
    have hi := mem_toList_zipIdx hx
    have hiW : i < cfg.workers := by
      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hi
      rw [hd.size] at hlt
      exact hlt
    obtain ⟨r', hr', hok⟩ := hd.results i hiW
    rw [hi] at hr'
    have := Option.some.inj hr'
    subst this
    have hrv : r = some v := by
      rcases (hinv.consumers i hiW).2.2 hprobe with h1 | ⟨h1, hc⟩ <;> rw [h1] at hok
      · simpa [ResultOk] using hok
      · have hok : r = if cfg.count = 0 then none else some (cfg.count - 1) := hok
        rw [← hc] at hok
        simpa using hok
    simp [hrv]
  · -- the probe never runs ahead
    simp [Nat.not_lt.mpr hinv.probe_le]

theorem reachable_violations_nil {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {s : State} (h : Reachable cfg s) : violations cfg s = [] :=
  violations_nil (reachable_inv hW hC h) (reachable_dataInv hW hC h)

theorem isFinal_producer {s : State} (h : s.isFinal = true) : s.producer = .done := by
  unfold State.isFinal at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  cases hp : s.producer <;> rw [hp] at h1 <;> first | rfl | cases h1 | nomatch h1

/-- What the explorer checks at every state with no enabled thread and the
replay at the end of every trace. -/
theorem reachable_finalViolations_nil {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {s : State} (h : Reachable cfg s) (hfinal : s.isFinal = true) : finalViolations cfg s = [] := by
  have hinv := reachable_inv hW hC h
  unfold finalViolations
  rw [reachable_violations_nil hW hC h, hfinal]
  have hprobe : s.probe = 2 * cfg.count := by
    have := hinv.probeOk
    rw [isFinal_producer hfinal] at this
    exact this
  simp [hprobe]

end RearmBarrier
