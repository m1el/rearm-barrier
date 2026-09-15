import RearmBarrier.Basics

/-!
# Combining happens-before with one additional modification order

Under the crate's strong orderings, ticket modification-order edges are
already happens-before edges (all ticket RMWs are AcqRel). A successful
probe read followed by its acquire fence receives a happens-before edge
from its release source. After placing the read at its fence, the only
remaining extra modification-order edges are on the single probe.

This module proves the graph-theoretic part of a coverage argument, without
assuming global SC or race freedom: a coherent modification order on ONE
location can be added to happens-before without making a cycle. For finite
graphs, `key` gives distinct natural-number positions respecting both orders.
It does not yet translate Rust program events to the history machine or
prove vector-clock soundness for an external execution graph.
-/

namespace RearmBarrier.ExecutionOrder

/-- Abstract semantic premises, rather than an assumed global serialization.
`coherent` is write-write coherence on the distinguished atomic location. -/
structure Graph (E : Type) where
  hb : E → E → Prop
  probe : E → Prop
  mo : E → E → Prop
  hb_trans : ∀ {a b c}, hb a b → hb b c → hb a c
  hb_irrefl : ∀ a, ¬ hb a a
  mo_trans : ∀ {a b c}, mo a b → mo b c → mo a c
  mo_irrefl : ∀ a, ¬ mo a a
  mo_probe : ∀ {a b}, mo a b → probe a ∧ probe b
  coherent : ∀ {a b}, probe a → probe b → hb a b → mo a b

def Before {E : Type} (g : Graph E) (a b : E) : Prop := g.hb a b ∨ g.mo a b

def HbOrEq {E : Type} (g : Graph E) (a b : E) : Prop := a = b ∨ g.hb a b

theorem HbOrEq.trans {E : Type} {g : Graph E} {a b c : E}
    (h : HbOrEq g a b) (h' : HbOrEq g b c) : HbOrEq g a c := by
  rcases h with rfl | h
  · exact h'
  rcases h' with rfl | h'
  · exact Or.inr h
  · exact Or.inr (g.hb_trans h h')

inductive Path {E : Type} (g : Graph E) : E → E → Prop
  | one {a b} : Before g a b → Path g a b
  | cons {a b c} : Before g a b → Path g b c → Path g a c

theorem Path.trans {E : Type} {g : Graph E} {a b c : E}
    (h : Path g a b) (h' : Path g b c) : Path g a c := by
  induction h with
  | one he => exact .cons he h'
  | cons he _ ih => exact .cons he (ih h')

/-- Compress a mixed path to at most one probe-order segment. Every intervening
HB segment between probe writes is itself ordered by probe coherence. -/
theorem Path.compress {E : Type} {g : Graph E} {a b : E} (h : Path g a b) :
    g.hb a b ∨ ∃ p q, HbOrEq g a p ∧ g.mo p q ∧ HbOrEq g q b := by
  induction h with
  | @one a b he =>
    rcases he with he | he
    · exact Or.inl he
    · exact Or.inr ⟨a, b, Or.inl rfl, he, Or.inl rfl⟩
  | @cons a b c he _ ih =>
    rcases he with he | he
    · rcases ih with hh | ⟨p, q, hp, hmo, hq⟩
      · exact Or.inl (g.hb_trans he hh)
      · exact Or.inr ⟨p, q, HbOrEq.trans (Or.inr he) hp, hmo, hq⟩
    · rcases ih with hh | ⟨p, q, hp, hmo, hq⟩
      · exact Or.inr ⟨a, b, Or.inl rfl, he, Or.inr hh⟩
      · have hap : g.mo a p := by
          rcases hp with rfl | hp
          · exact he
          · exact g.mo_trans he (g.coherent (g.mo_probe he).2 (g.mo_probe hmo).1 hp)
        exact Or.inr ⟨a, q, Or.inl rfl, g.mo_trans hap hmo, hq⟩

/-- Adding the probe's modification order cannot create a cycle. This does
not hold for arbitrarily many extra locations' modification orders. -/
theorem acyclic {E : Type} (g : Graph E) (a : E) : ¬ Path g a a := by
  intro hp
  rcases hp.compress with hh | ⟨p, q, hap, hmo, hqa⟩
  · exact g.hb_irrefl a hh
  have hqp := hqa.trans hap
  rcases hqp with he | hh
  · subst q
    exact g.mo_irrefl p hmo
  · have hrev := g.coherent (g.mo_probe hmo).2 (g.mo_probe hmo).1 hh
    exact g.mo_irrefl p (g.mo_trans hmo hrev)

private theorem count_mono {E : Type} (xs : List E) (p q : E → Bool)
    (h : ∀ x ∈ xs, p x = true → q x = true) : xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hh := ih (fun x hx => h x (by simp [hx]))
    have ha := h a (by simp)
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

private theorem count_strict {E : Type} (xs : List E) (p q : E → Bool)
    (h : ∀ x ∈ xs, p x = true → q x = true)
    (hw : ∃ x ∈ xs, p x = false ∧ q x = true) : xs.countP p < xs.countP q := by
  induction xs with
  | nil => simp at hw
  | cons a xs ih =>
    have hh := count_mono xs p q (fun x hx => h x (by simp [hx]))
    have ha := h a (by simp)
    obtain ⟨x, hx, hp, hq⟩ := hw
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hp, hq]; omega
    · have ht := ih (fun x hx => h x (by simp [hx])) ⟨x, hx, hp, hq⟩
      cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

/-- Count strict predecessors in a finite graph. No chosen topological
ordering is needed to define this rank. -/
noncomputable def rank {n : Nat} (g : Graph (Fin n)) (a : Fin n) : Nat := by
  classical
  exact (List.finRange n).countP (fun x => decide (Path g x a))

theorem rank_lt {n : Nat} {g : Graph (Fin n)} {a b : Fin n} (h : Path g a b) :
    rank g a < rank g b := by
  classical
  apply count_strict
  · intro x _ hx
    exact of_decide_eq_true hx |>.trans h |> decide_eq_true
  · exact ⟨a, by simp, by simp [acyclic], by simp [h]⟩

/-- A distinct position for every event; rank ties are broken by its original
finite identifier, without imposing additional semantic constraints. -/
noncomputable def key {n : Nat} (g : Graph (Fin n)) (a : Fin n) : Nat :=
  rank g a * (n + 1) + a.val

private theorem key_lt_of_rank_lt {n : Nat} {g : Graph (Fin n)} {a b : Fin n}
    (h : rank g a < rank g b) : key g a < key g b := by
  have hm := Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt h)
  simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hm
  have ha := a.isLt
  unfold key
  omega

/-- Finite graphs have a concrete strict ordering respecting every HB and
probe-modification-order edge. -/
theorem key_before {n : Nat} {g : Graph (Fin n)} {a b : Fin n} (h : Before g a b) :
    key g a < key g b := key_lt_of_rank_lt (rank_lt (.one h))

theorem key_injective {n : Nat} (g : Graph (Fin n)) {a b : Fin n}
    (h : key g a = key g b) : a = b := by
  have hr : rank g a = rank g b := by
    by_cases hab : rank g a < rank g b
    · have := key_lt_of_rank_lt hab; omega
    by_cases hba : rank g b < rank g a
    · have := key_lt_of_rank_lt hba; omega
    omega
  apply Fin.ext
  unfold key at h
  rw [hr] at h
  omega

/-- Any further ordering constraints already contained in happens-before
(e.g. ticket RMW order or release-to-fence edges) use the same positions. -/
theorem key_hb {n : Nat} {g : Graph (Fin n)} {a b : Fin n} (h : g.hb a b) :
    key g a < key g b := key_before (Or.inl h)

end RearmBarrier.ExecutionOrder
