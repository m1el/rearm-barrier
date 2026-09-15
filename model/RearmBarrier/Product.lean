import RearmBarrier.Flat
import RearmBarrier.TreeModel

/-!
# Two engines in lockstep

The product of two engines runs both on every step and faults if they
disagree on anything observable: the ticket touched, the amount, the old
value, the thread's clock afterwards, or what the consumer does next.
Exploring a configuration with the product engine is therefore a
bisimulation check of the two ticket representations over every
interleaving; replaying a crate trace on it checks the trace against both.
-/

namespace RearmBarrier

variable {τ₁ κ₁ τ₂ κ₂ : Type}

def Engine.product (E₁ : Engine τ₁ κ₁) (E₂ : Engine τ₂ κ₂) : Engine (τ₁ × τ₂) (κ₁ × κ₂) :=
  { init := fun cfg => (E₁.init cfg, E₂.init cfg)
    start := fun cfg id => (E₁.start cfg id, E₂.start cfg id)
    step := fun cfg (t₁, t₂) (c₁, c₂) v vc ord =>
      match E₁.step cfg t₁ c₁ v vc ord, E₂.step cfg t₂ c₂ v vc ord with
      | .fault m, .fault m' => .fault s!"both engines fault: {m} / {m'}"
      | .fault m, .ok .. => .fault s!"the first engine faults ({m}) but the second does not"
      | .ok .., .fault m => .fault s!"the second engine faults ({m}) but the first does not"
      | .ok t₁ vc₁ rmw₁ n₁, .ok t₂ vc₂ rmw₂ n₂ =>
        if rmw₁ != rmw₂ then
          .fault s!"the engines disagree: {rmw₁} vs {rmw₂}"
        else if vc₁ != vc₂ then
          .fault s!"the engines disagree on the clock after {rmw₁}: {vc₁} vs {vc₂}"
        else
          match n₁, n₂ with
          | .finished, .finished => .ok (t₁, t₂) vc₁ rmw₁ .finished
          | .stop, .stop => .ok (t₁, t₂) vc₁ rmw₁ .stop
          | .continue c₁, .continue c₂ => .ok (t₁, t₂) vc₁ rmw₁ (.continue (c₁, c₂))
          | n₁, n₂ => .fault s!"the engines disagree after {rmw₁}: {n₁.kind} vs {n₂.kind}"
    violations := fun cfg (t₁, t₂) cs =>
      E₁.violations cfg t₁ (cs.map (·.mapCursor Prod.fst)) ++ E₂.violations cfg t₂ (cs.map (·.mapCursor Prod.snd))
    summary := fun (t₁, t₂) => s!"{E₁.summary t₁}, {E₂.summary t₂}" }

instance [ToString κ₁] [ToString κ₂] : ToString (κ₁ × κ₂) := ⟨fun (a, b) => s!"{a} | {b}"⟩

/-- The flat engine checked against the tree engine. -/
def bothEngines : Engine (Flat.Tickets × TreeModel.Tree) (Flat.Walk × TreeModel.Cursor) :=
  Flat.engine.product TreeModel.engine

end RearmBarrier
