import RearmBarrier.Hb
import RearmBarrier.NoFault

/-!
# Observed probe writes and separate acquire fences

This module proves a reduction from a history-based operational extension
of the executable model. Loads may observe any recorded probe write, and
successful loads and their fences are separate actions. It is not a
formalization of all Rust/C++ execution graphs; that external correspondence
is a separate obligation. In particular we do not assume SC from race freedom.
All arithmetic here is unbounded, as in `Model`.
-/

namespace RearmBarrier.WeakMemory

/-- A waiting consumer prevents completion of the version it is waiting for.
This also covers a consumer already waiting for the *next* producer version. -/
theorem consumer_probe_bound {cfg : Config} {s : State} (h : Inv cfg s)
    {id v : Nat} (hid : id < cfg.workers) (hp : phaseOf s.consumers id = .waitReady v) :
    s.probe ≤ 2 * v + 1 := by
  have hc := h.consumers id hid
  rcases probe_cases h.probeOk h.version with hpr | hpr | hpr
  · rcases hc.1 hpr with he | ⟨_, he | he⟩ | ⟨_, he⟩ <;> rw [hp] at he <;> cases he <;> omega
  · rcases hc.2.1 hpr with he | he | he | ⟨c, he⟩ | he | (he | ⟨he, _⟩) | ⟨_, he | he⟩ <;>
      rw [hp] at he <;> cases he <;> omega
  · rcases hc.2.2 hpr with he | ⟨he, _⟩ <;> rw [hp] at he <;> cases he <;> omega

/-- An old value can satisfy the consumer guard only if it is the current
publication value. The bound on `observed` will come from recorded history. -/
theorem consumer_observed_eq {cfg : Config} {s : State} (h : Inv cfg s)
    {id v observed : Nat} (hid : id < cfg.workers)
    (hp : phaseOf s.consumers id = .waitReady v)
    (hold : observed ≤ s.probe) (hguard : 2 * v < observed) :
    observed = s.probe ∧ observed = 2 * v + 1 := by
  have := consumer_probe_bound h hid hp
  omega

/-- Only the producer can publish the next version, after this wait. -/
theorem producer_observed_eq {cfg : Config} {s : State} (h : Inv cfg s)
    {v observed : Nat} (hp : s.producer = .waiting v)
    (hold : observed ≤ s.probe) (hguard : observed = 2 * v + 2) :
    observed = s.probe := by
  have hb := (h.at hp).probeOk
  simp only [ProbeOk] at hb
  omega

/-- A successful spin observation, before its acquire fence. -/
inductive Waiting (s : State) : Thread → Nat → Prop
  | producer {v value} : s.producer = .waiting v → value = 2 * v + 2 →
      Waiting s .producer value
  | consumer {id v value} : s.consumers[id]? = some (.waitReady v) → 2 * v < value →
      Waiting s (.consumer id) value

theorem Waiting.observed_eq {cfg : Config} {s : State} (h : Inv cfg s)
    {t : Thread} {value : Nat} (hw : Waiting s t value) (hold : value ≤ s.probe) :
    value = s.probe := by
  cases hw with
  | producer hp hg => exact producer_observed_eq h hp hold hg
  | consumer hp hg =>
    have hid : _ < s.consumers.size := (Array.getElem?_eq_some_iff.mp hp).1
    have hsize := h.size
    exact (consumer_observed_eq h (by omega) (phaseOf_eq hp) hold hg).1

/-- Program order forbids the waiting thread itself from acting before its
fence. Other threads preserve its waiting phase. -/
theorem Waiting.other {cfg : Config} {s s' : State} {t u : Thread} {value : Nat}
    (hw : Waiting s t value) (hne : u ≠ t)
    {ev : Option Event} (hs : step cfg s u = .step s' ev) : Waiting s' t value := by
  cases hw with
  | producer hp hg =>
    cases u with
    | producer => exact False.elim (hne rfl)
    | consumer id =>
      obtain ⟨_, _, _, _, _, _, _, hprod, _⟩ := step_consumer_move hs
      exact .producer (hprod.trans hp) hg
  | @consumer id v value hp hg =>
    cases u with
    | producer => exact .consumer (by rw [(step_producer_unchanged hs).1]; exact hp) hg
    | consumer j =>
      obtain ⟨_, _, _, _, _, hcs, _⟩ := step_consumer_move hs
      have hij : id ≠ j := by intro he; subst j; exact hne rfl
      exact .consumer (by rw [hcs]; simpa [hij, Ne.symm hij] using hp) hg

/-- Every modeled probe update increases it; it never decreases. -/
theorem step_probe_mono {cfg : Config} {s s' : State} {t : Thread} {ev : Option Event}
    (hs : step cfg s t = .step s' ev) : s.probe ≤ s'.probe := by
  cases t with
  | producer =>
    obtain ⟨_, _, _, _, hm, _, hpr, _⟩ := step_producer_move hs
    cases hm <;> omega
  | consumer id =>
    obtain ⟨ph, _, _, _, _, _, _, _, hpr, _⟩ := step_consumer_move hs
    cases ph <;> simp_all [probeAfter]

/-- The signal cannot change while its recipient is paused before the fence. -/
theorem Waiting.probe_stable {cfg : Config} {s s' : State} (h : Inv cfg s)
    {t u : Thread} {value : Nat} (hw : Waiting s t value) (heq : value = s.probe)
    (hne : u ≠ t) {ev : Option Event} (hs : step cfg s u = .step s' ev) :
    s'.probe = s.probe := by
  have hw' := hw.other hne hs
  have hm := step_probe_mono hs
  exact (hw'.observed_eq (step_inv h hs) (by omega)).symm.trans heq

/-- Non-atomic accesses cannot change a probe release clock. -/
theorem access_probeRel {s s' : State} {t : Nat} {a : Access}
    (ha : s.access t a = .ok s') : s'.probeRel = s.probeRel := by
  cases a <;> unfold State.access at ha <;> dsimp only at ha <;> split at ha <;> cases ha <;> rfl

theorem accessing_probeRel {s s' : State} {t : Nat} {a : Access}
    {k : State → Outcome} {ev : Option Event}
    (ha : Outcome.accessing s t a k = .step s' ev) :
    ∃ s₁, s₁.probeRel = s.probeRel ∧ k s₁ = .step s' ev := by
  unfold Outcome.accessing at ha
  split at ha
  · rename_i s₁ hh
    exact ⟨s₁, access_probeRel hh, ha⟩
  · cases ha

/-- An unchanged probe value also means its release clock is unchanged:
only a probe RMW can change either, and every such RMW increments the value. -/
theorem step_probeRel {cfg : Config} {s s' : State} {t : Thread} {ev : Option Event}
    (hs : step cfg s t = .step s' ev) (heq : s'.probe = s.probe) :
    s'.probeRel = s.probeRel := by
  unfold step at hs
  cases t with
  | producer =>
    simp only at hs
    cases hr : producerStep cfg s with
    | blocked => rw [hr] at hs; cases hs
    | fault m => rw [hr] at hs; cases hs
    | race m => rw [hr] at hs; cases hs
    | step s₁ ev₁ =>
      rw [hr] at hs
      cases hs
      change s₁.probe = s.probe at heq
      change s₁.probeRel = s.probeRel
      unfold producerStep at hr
      cases hp : s.producer <;> rw [hp] at hr
      · obtain ⟨s₂, hrel, hh⟩ := accessing_probeRel hr
        cases hh
        exact hrel
      · cases hr; rfl
      · cases hr; simp at heq
      · dsimp only at hr
        split at hr
        · cases hr
          split <;> rfl
        · cases hr
      · obtain ⟨s₂, hrel, hh⟩ := accessing_probeRel hr
        cases hh
        exact hrel
      · cases hr; rfl
      · cases hr
  | consumer id =>
    simp only at hs
    cases hr : consumerStep cfg s id with
    | blocked => rw [hr] at hs; cases hs
    | fault m => rw [hr] at hs; cases hs
    | race m => rw [hr] at hs; cases hs
    | step s₁ ev₁ =>
      rw [hr] at hs
      cases hs
      change s₁.probe = s.probe at heq
      change s₁.probeRel = s.probeRel
      unfold consumerStep at hr
      cases hp : s.consumers[id]? with
      | none => rw [hp] at hr; cases hr
      | some ph =>
        rw [hp] at hr
        cases ph with
        | start =>
          obtain ⟨s₂, hrel, hh⟩ := accessing_probeRel hr
          cases hh
          exact hrel
        | initializing => cases hr; rfl
        | waitReady v =>
          dsimp only at hr
          split at hr
          · cases hr
            split <;> rfl
          · cases hr
        | beforeFunc v =>
          obtain ⟨s₂, hrel, hh⟩ := accessing_probeRel hr
          obtain ⟨s₃, hrel', hh'⟩ := accessing_probeRel hh
          cases hh'
          exact hrel'.trans hrel
        | inFunc v => cases hr; rfl
        | walk v c =>
          dsimp only at hr
          split at hr
          · cases hr
          · cases hr; rfl
        | finish v => cases hr; simp at heq
        | done => cases hr

/-! ## A history-based operational model

Probe writes are identified by their (strictly increasing) values. The
initial value is also available to reads. History entries keep the release
clock at that write, not the clock at the later fence. We intentionally
allow even incoherent choices of old reads: this overapproximation makes
the safety reduction stronger, but makes no eventual-visibility claim.
-/

structure ProbeWrite where
  value : Nat
  release : VC
  deriving DecidableEq

def current (s : State) : ProbeWrite := ⟨s.probe, s.probeRel⟩

def record (s s' : State) (history : List ProbeWrite) : List ProbeWrite :=
  if s'.probe = s.probe then history else current s' :: history

structure HistoryOk (s : State) (history : List ProbeWrite) : Prop where
  bounded : ∀ w ∈ history, w.value ≤ s.probe
  latest : ∀ w ∈ history, w.value = s.probe → w.release = s.probeRel
  current_mem : current s ∈ history

theorem HistoryOk.advance {cfg : Config} {s s' : State} {history : List ProbeWrite}
    (hh : HistoryOk s history) {t : Thread} {ev : Option Event}
    (hs : step cfg s t = .step s' ev) : HistoryOk s' (record s s' history) := by
  have hm := step_probe_mono hs
  unfold record
  split
  · rename_i heq
    have hr := step_probeRel hs heq
    exact ⟨fun w hw => by have := hh.bounded w hw; omega,
      fun w hw hv => (hh.latest w hw (hv.trans heq)).trans hr.symm,
      by simpa [current, heq, hr] using hh.current_mem⟩
  · rename_i hne
    refine ⟨?_, ?_, by simp⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Nat.le_refl _
      · have := hh.bounded w hw; omega
    · intro w hw hv
      rcases List.mem_cons.mp hw with rfl | hw
      · rfl
      · have := hh.bounded w hw; omega

/-- A pending fence remembers the exact probe write read by its load. -/
structure Machine where
  base : State
  history : List ProbeWrite
  pending : Thread → Option ProbeWrite

def Machine.init (cfg : Config) : Machine :=
  ⟨State.init cfg, [current (State.init cfg)], fun _ => none⟩

def put (p : Thread → Option ProbeWrite) (t : Thread) (w : Option ProbeWrite) :
    Thread → Option ProbeWrite := fun u => if u = t then w else p u

/-- Spin phases must execute a load before they can execute their fence. -/
def Spinning (s : State) : Thread → Prop
  | .producer => ∃ v, s.producer = .waiting v
  | .consumer id => ∃ v, s.consumers[id]? = some (.waitReady v)

theorem Waiting.spinning {s : State} {t : Thread} {value : Nat} (h : Waiting s t value) :
    Spinning s t := by cases h <;> exact ⟨_, ‹_›⟩

/-- Execute the wait exit using the *saved* value and release clock. In
reachable machines these equal the current pair, but the definition does
not assume this. The saved clock is acquired only now, at the fence. -/
def fenceStep (cfg : Config) (s : State) (t : Thread) (w : ProbeWrite) : Outcome :=
  step cfg { s with probe := w.value, probeRel := w.release } t

inductive Transition (cfg : Config) : Machine → Machine → Prop
  /-- A failing load is an observable execution action but a model stutter. -/
  | spin {m : Machine} {t : Thread} {w : ProbeWrite} :
      m.pending t = none → Spinning m.base t → w ∈ m.history →
      ¬ Waiting m.base t w.value → Transition cfg m m
  /-- A successful load saves its supplying write, without acquiring yet. -/
  | load {m : Machine} {t : Thread} {w : ProbeWrite} :
      m.pending t = none → w ∈ m.history → Waiting m.base t w.value →
      Transition cfg m { m with pending := put m.pending t (some w) }
  /-- Non-spin actions retain the executable model's RMW semantics. -/
  | action {m : Machine} {t : Thread} {s' : State} {ev : Option Event} :
      m.pending t = none → ¬ Spinning m.base t → step cfg m.base t = .step s' ev →
      Transition cfg m ⟨s', record m.base s' m.history, m.pending⟩
  | fence {m : Machine} {t : Thread} {w : ProbeWrite} {s' : State} {ev : Option Event} :
      m.pending t = some w → fenceStep cfg m.base t w = .step s' ev →
      Transition cfg m ⟨s', record m.base s' m.history, put m.pending t none⟩

structure PendingOk (s : State) (p : Thread → Option ProbeWrite) : Prop where
  waiting : ∀ t w, p t = some w → Waiting s t w.value
  value : ∀ t w, p t = some w → w.value = s.probe
  release : ∀ t w, p t = some w → w.release = s.probeRel

structure MachineInv (cfg : Config) (m : Machine) : Prop where
  reachable : RearmBarrier.Reachable cfg m.base
  history : HistoryOk m.base m.history
  pending : PendingOk m.base m.pending

theorem PendingOk.fence_eq {s : State} {p : Thread → Option ProbeWrite}
    (h : PendingOk s p) {t : Thread} {w : ProbeWrite} (hp : p t = some w) (cfg : Config) :
    fenceStep cfg s t w = step cfg s t := by
  simp [fenceStep, h.value t w hp, h.release t w hp]

/-- Waiting phases and the saved write survive every action of another
thread, including an arbitrarily long delay between load and fence. -/
theorem PendingOk.advance {cfg : Config} {s s' : State} (hi : Inv cfg s)
    {p p' : Thread → Option ProbeWrite} (h : PendingOk s p)
    {t : Thread} {ev : Option Event} (hs : step cfg s t = .step s' ev)
    (hp : ∀ u w, p' u = some w → u ≠ t ∧ p u = some w) : PendingOk s' p' := by
  have stable : ∀ u w, p' u = some w →
      Waiting s' u w.value ∧ w.value = s'.probe ∧ w.release = s'.probeRel := by
    intro u w hu
    obtain ⟨hne, hu'⟩ := hp u w hu
    have hw := h.waiting u w hu'
    have he := hw.probe_stable hi (h.value u w hu') (Ne.symm hne) hs
    exact ⟨hw.other (Ne.symm hne) hs, (h.value u w hu').trans he.symm,
      (h.release u w hu').trans (step_probeRel hs he).symm⟩
  exact ⟨fun u w hu => (stable u w hu).1, fun u w hu => (stable u w hu).2.1,
    fun u w hu => (stable u w hu).2.2⟩

theorem machine_init (cfg : Config) : MachineInv cfg (Machine.init cfg) := by
  refine ⟨.init, ⟨?_, ?_, by simp [Machine.init]⟩, ⟨?_, ?_, ?_⟩⟩
  · intro w hw
    have : w = current (State.init cfg) := by simpa [Machine.init] using hw
    subst w
    exact Nat.le_refl _
  · intro w hw _
    have : w = current (State.init cfg) := by simpa [Machine.init] using hw
    subst w
    rfl
  all_goals intro t w hp; cases hp

theorem transition_inv {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m m' : Machine} (h : MachineInv cfg m) (ht : Transition cfg m m') : MachineInv cfg m' := by
  have hi := reachable_inv hW hC h.reachable
  cases ht with
  | spin => exact h
  | @load t w hp hm hw =>
    have hv := hw.observed_eq hi (h.history.bounded w hm)
    have hr := h.history.latest w hm hv
    refine ⟨h.reachable, h.history, ⟨?_, ?_, ?_⟩⟩
    all_goals
      intro u w' hu
      change (if u = t then some w else m.pending u) = some w' at hu
      split at hu
      · rename_i he
        subst u
        cases hu
        assumption
      · first | exact h.pending.waiting u w' hu | exact h.pending.value u w' hu | exact h.pending.release u w' hu
  | @action t s' ev hp _ hs =>
    refine ⟨.step h.reachable hs, h.history.advance hs, h.pending.advance hi hs ?_⟩
    intro u w hu
    refine ⟨?_, hu⟩
    intro he
    subst u
    rw [hp] at hu
    cases hu
  | @fence t w s' ev hp hs =>
    rw [h.pending.fence_eq hp cfg] at hs
    refine ⟨.step h.reachable hs, h.history.advance hs, h.pending.advance hi hs ?_⟩
    intro u w hu
    change (if u = t then none else m.pending u) = some w at hu
    split at hu
    · cases hu
    · exact ⟨‹u ≠ t›, hu⟩

inductive Reachable (cfg : Config) : Machine → Prop
  | init : Reachable cfg (Machine.init cfg)
  | next {m m' : Machine} : Reachable cfg m → Transition cfg m m' → Reachable cfg m'

/-- The invariant is derived together with the reduction, never assumed
of an arbitrary history-machine execution. -/
theorem reachable_machineInv {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m : Machine} (h : Reachable cfg m) : MachineInv cfg m := by
  induction h with
  | init => exact machine_init cfg
  | next _ ht ih => exact transition_inv hW hC ih ht

/-- Every reachable history-machine state projects to a reachable state of
the original model, despite arbitrary stale loads and split fences. -/
theorem reachable_projection {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m : Machine} (h : Reachable cfg m) : RearmBarrier.Reachable cfg m.base :=
  (reachable_machineInv hW hC h).reachable

/-- Non-load execution attempts. Loads themselves only read atomic history
and either stutter or install a pending fence. -/
noncomputable def attempt (cfg : Config) (m : Machine) (t : Thread) : Outcome := by
  classical
  exact match m.pending t with
  | some w => fenceStep cfg m.base t w
  | none => if Spinning m.base t then .blocked else step cfg m.base t

theorem reachable_attempt_no_race {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    (hS : Strong cfg.orderings) {m : Machine} (h : Reachable cfg m) (t : Thread) (msg : String) :
    attempt cfg m t ≠ .race msg := by
  have hi := reachable_machineInv hW hC h
  unfold attempt
  cases hp : m.pending t with
  | some w =>
    dsimp only
    rw [hi.pending.fence_eq hp cfg]
    exact RearmBarrier.reachable_no_race hW hC hS hi.reachable t msg
  | none =>
    dsimp only
    split
    · intro he; cases he
    · exact RearmBarrier.reachable_no_race hW hC hS hi.reachable t msg

theorem reachable_attempt_no_fault {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m : Machine} (h : Reachable cfg m) {t : Thread} (ht : t ∈ threads cfg) (msg : String) :
    attempt cfg m t ≠ .fault msg := by
  have hi := reachable_machineInv hW hC h
  unfold attempt
  cases hp : m.pending t with
  | some w =>
    dsimp only
    rw [hi.pending.fence_eq hp cfg]
    exact RearmBarrier.reachable_no_fault hW hC hi.reachable ht msg
  | none =>
    dsimp only
    split
    · intro he; cases he
    · exact RearmBarrier.reachable_no_fault hW hC hi.reachable ht msg

/-! ## The reduction does not remove any original execution -/

theorem spinning_step_waiting {cfg : Config} {s s' : State} {t : Thread} {ev : Option Event}
    (hp : Spinning s t) (hs : step cfg s t = .step s' ev) : Waiting s t s.probe := by
  cases t with
  | producer =>
    obtain ⟨v, hv⟩ := hp
    obtain ⟨_, _, _, he, hm, _, _, _⟩ := step_producer_move hs
    rw [hv] at he
    cases he
    cases hm with
    | waiting _ hg => exact .producer hv (by omega)
  | consumer id =>
    obtain ⟨v, hv⟩ := hp
    obtain ⟨_, _, _, he, hm, _⟩ := step_consumer_move hs
    rw [hv] at he
    cases he
    cases hm with
    | waitReady _ hg => exact .consumer hv (by omega)

inductive Transitions (cfg : Config) : Machine → Machine → Prop
  | refl (m : Machine) : Transitions cfg m m
  | tail {a b c : Machine} : Transitions cfg a b → Transition cfg b c → Transitions cfg a c

theorem Transitions.reachable {cfg : Config} {m m' : Machine} (hs : Transitions cfg m m')
    (h : Reachable cfg m) : Reachable cfg m' := by
  induction hs with
  | refl => exact h
  | tail _ ht ih => exact .next ih ht

/-- With no pending fences, an original step is either one ordinary action
or a latest-value load followed by its fence. Thus the new semantics is not
vacuously safe through exclusion of original steps. -/
theorem lift_step {cfg : Config} {m : Machine} (hh : HistoryOk m.base m.history)
    (hp : ∀ t, m.pending t = none) {t : Thread} {s' : State} {ev : Option Event}
    (hs : step cfg m.base t = .step s' ev) :
    ∃ m', Transitions cfg m m' ∧ m'.base = s' ∧ (∀ u, m'.pending u = none) := by
  classical
  by_cases hspin : Spinning m.base t
  · let loaded : Machine := { m with pending := put m.pending t (some (current m.base)) }
    have hl : Transition cfg m loaded := .load (hp t) hh.current_mem (spinning_step_waiting hspin hs)
    have hf : Transition cfg loaded ⟨s', record m.base s' m.history, put loaded.pending t none⟩ :=
      .fence (w := current m.base) (ev := ev) (by simp [loaded, put])
        (by simpa [fenceStep, current, loaded] using hs)
    refine ⟨_, .tail (.tail (.refl _) hl) hf, rfl, ?_⟩
    intro u
    simp [put, loaded, hp]
  · exact ⟨_, .tail (.refl _) (.action (hp t) hspin hs), rfl, hp⟩

/-- Every original reachable state has a history-machine execution ending
with no pending fences. -/
theorem lift_reachable {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {s : State} (h : RearmBarrier.Reachable cfg s) :
    ∃ m, Reachable cfg m ∧ m.base = s ∧ (∀ t, m.pending t = none) := by
  induction h with
  | init => exact ⟨Machine.init cfg, .init, rfl, fun _ => rfl⟩
  | step _ hs ih =>
    obtain ⟨m, hm, he, hp⟩ := ih
    rw [← he] at hs
    obtain ⟨m', ht, he', hp'⟩ := lift_step (reachable_machineInv hW hC hm).history hp hs
    exact ⟨m', ht.reachable hm, he', hp'⟩

/-! ## The write supplying a successful read

Provenance records actual probe RMWs, rather than postulating that a clock
with the right value came from a release. Under `Strong`, both of these
RMW kinds have release ordering (including their inherited release sequence).
-/

inductive WriteSource (cfg : Config) : ProbeWrite → Prop
  | initial : WriteSource cfg (current (State.init cfg))
  | publish {s s' : State} {v : Nat} {ev : Option Event} :
      RearmBarrier.Reachable cfg s → s.producer = .publish v →
      step cfg s .producer = .step s' ev → WriteSource cfg (current s')
  | finish {s s' : State} {id v : Nat} {ev : Option Event} :
      RearmBarrier.Reachable cfg s → s.consumers[id]? = some (.finish v) →
      step cfg s (.consumer id) = .step s' ev → WriteSource cfg (current s')

theorem changed_write_source {cfg : Config} {s s' : State}
    (hr : RearmBarrier.Reachable cfg s) {t : Thread} {ev : Option Event}
    (hs : step cfg s t = .step s' ev) (hne : s'.probe ≠ s.probe) : WriteSource cfg (current s') := by
  cases t with
  | producer =>
    obtain ⟨_, _, _, hp, hm, _, hpr, _⟩ := step_producer_move hs
    cases hm with
    | publish v => exact .publish hr hp hs
    | _ => exact False.elim (hne hpr)
  | consumer id =>
    obtain ⟨ph, _, _, hp, hm, _, _, _, hpr, _⟩ := step_consumer_move hs
    cases ph with
    | finish v => exact .finish hr hp hs
    | _ => exact False.elim (hne hpr)

theorem record_source {cfg : Config} {s s' : State} {history : List ProbeWrite}
    (hr : RearmBarrier.Reachable cfg s) (hh : ∀ w ∈ history, WriteSource cfg w)
    {t : Thread} {ev : Option Event} (hs : step cfg s t = .step s' ev) :
    ∀ w ∈ record s s' history, WriteSource cfg w := by
  unfold record
  split
  · exact hh
  · rename_i hne
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact changed_write_source hr hs hne
    · exact hh w hw

theorem reachable_write_source {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m : Machine} (hr : Reachable cfg m) : ∀ w ∈ m.history, WriteSource cfg w := by
  induction hr with
  | init =>
    intro w hw
    have he : w = current (State.init cfg) := by simpa [Machine.init] using hw
    subst w
    exact .initial
  | @next m m' hr ht ih =>
    have hi := reachable_machineInv hW hC hr
    cases ht with
    | spin => exact ih
    | load => exact ih
    | action _ _ hs => exact record_source hi.reachable ih hs
    | fence hp hs =>
      rw [hi.pending.fence_eq hp cfg] at hs
      exact record_source hi.reachable ih hs

theorem publish_value {cfg : Config} {s s' : State} (hi : Inv cfg s)
    {v : Nat} (hp : s.producer = .publish v) {ev : Option Event}
    (hs : step cfg s .producer = .step s' ev) : s'.probe = 2 * v + 1 := by
  have hb : s.probe = 2 * v := (hi.at hp).probeOk
  obtain ⟨_, _, _, he, hm, _, hpr, _⟩ := step_producer_move hs
  rw [hp] at he
  cases he
  cases hm
  omega

theorem finish_value {cfg : Config} {s s' : State} (hi : Inv cfg s)
    {id v : Nat} (hp : s.consumers[id]? = some (.finish v)) {ev : Option Event}
    (hs : step cfg s (.consumer id) = .step s' ev) : s'.probe = 2 * v + 2 := by
  have hid := (Array.getElem?_eq_some_iff.mp hp).1
  have hsize := hi.size
  obtain ⟨_, _, hpr, _⟩ := hi.active (by omega) (Or.inr (Or.inr (phaseOf_eq hp)))
  obtain ⟨_, _, _, he, _, _, _, _, hpr', _⟩ := step_consumer_move hs
  rw [hp] at he
  cases he
  simp only [probeAfter] at hpr'
  omega

/-- A successful consumer read identifies the actual publication RMW of
its version, not merely some numerically sufficient probe value. -/
theorem consumer_reads_publication {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m : Machine} (hr : Reachable cfg m) {id v : Nat} {w : ProbeWrite}
    (hp : m.base.consumers[id]? = some (.waitReady v)) (hm : w ∈ m.history)
    (hg : 2 * v < w.value) :
    ∃ s s' ev, RearmBarrier.Reachable cfg s ∧ s.producer = .publish v ∧
      step cfg s .producer = .step s' ev ∧ w = current s' := by
  have hi := reachable_machineInv hW hC hr
  have hinv := reachable_inv hW hC hi.reachable
  have hid := (Array.getElem?_eq_some_iff.mp hp).1
  have hsize := hinv.size
  have hv := (consumer_observed_eq hinv (by omega) (phaseOf_eq hp) (hi.history.bounded w hm) hg).2
  cases reachable_write_source hW hC hr w hm with
  | initial => simp [current, State.init] at hv
  | @publish s s' v' ev hrs hps hs =>
    have he := publish_value (reachable_inv hW hC hrs) hps hs
    change s'.probe = 2 * v + 1 at hv
    have : v' = v := by omega
    subst v'
    exact ⟨s, s', ev, hrs, hps, hs, rfl⟩
  | finish hrs hps hs =>
    have he := finish_value (reachable_inv hW hC hrs) hps hs
    dsimp only [current] at hv
    omega

/-- The producer's successful read identifies the actual completion RMW
of its version. -/
theorem producer_reads_completion {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m : Machine} (hr : Reachable cfg m) {v : Nat} {w : ProbeWrite}
    (hm : w ∈ m.history) (hg : w.value = 2 * v + 2) :
    ∃ s s' id ev, RearmBarrier.Reachable cfg s ∧ s.consumers[id]? = some (.finish v) ∧
      step cfg s (.consumer id) = .step s' ev ∧ w = current s' := by
  cases reachable_write_source hW hC hr w hm with
  | initial => simp [current, State.init] at hg
  | publish hrs hps hs =>
    have he := publish_value (reachable_inv hW hC hrs) hps hs
    dsimp only [current] at hg
    omega
  | @finish s s' id v' ev hrs hps hs =>
    have he := finish_value (reachable_inv hW hC hrs) hps hs
    change s'.probe = 2 * v + 2 at hg
    have : v' = v := by omega
    subst v'
    exact ⟨s, s', id, ev, hrs, hps, hs, rfl⟩

/-- Each history-machine transition is a stutter or exactly one original
step, including all of the original step's clock and data effects. -/
theorem transition_projects {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m m' : Machine} (hr : Reachable cfg m) (ht : Transition cfg m m') :
    m'.base = m.base ∨ ∃ t ev, step cfg m.base t = .step m'.base ev := by
  cases ht with
  | spin => exact Or.inl rfl
  | load => exact Or.inl rfl
  | action _ _ hs => exact Or.inr ⟨_, _, hs⟩
  | fence hp hs =>
    rw [(reachable_machineInv hW hC hr).pending.fence_eq hp cfg] at hs
    exact Or.inr ⟨_, _, hs⟩

/-- The pending fence still refers to the very same value/clock pair,
regardless of how many other threads' actions have intervened. -/
theorem pending_write_stable {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m : Machine} (hr : Reachable cfg m) {t : Thread} {w : ProbeWrite}
    (hp : m.pending t = some w) : w = current m.base := by
  have hi := (reachable_machineInv hW hC hr).pending
  obtain ⟨value, release⟩ := w
  have hv := hi.value t _ hp
  have hc := hi.release t _ hp
  simp only [current, ProbeWrite.mk.injEq]
  exact ⟨hv, hc⟩

theorem reachable_violations_nil {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m : Machine} (hr : Reachable cfg m) : violations cfg m.base = [] :=
  RearmBarrier.reachable_violations_nil hW hC (reachable_projection hW hC hr)

theorem reachable_finalViolations_nil {cfg : Config} (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster)
    {m : Machine} (hr : Reachable cfg m) (hf : m.base.isFinal = true) : finalViolations cfg m.base = [] :=
  RearmBarrier.reachable_finalViolations_nil hW hC (reachable_projection hW hC hr) hf

end RearmBarrier.WeakMemory
