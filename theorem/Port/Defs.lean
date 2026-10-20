import theorem.Flow.Basic
import theorem.Map.Defs

/-! # Port semantics

The single definition of the behaviour of systems with ports. A system has `n` states in
`ℝⁿ = EuclideanSpace ℝ (Fin n)` and `p` ports; the input `u` and the output `y` are conjugate
port variables, so `u ⬝ y` is the power supplied to the system. Solutions are integral curves on
finite segments under an arbitrary input signal, as in the Flow semantics. With the ports held at
zero the system is the autonomous field `zeroInput`, whose behaviour is the Flow semantics.

Passivity is dissipativity with respect to the supplied power: a nonnegative storage whose
increase on every solution segment is bounded by the energy supplied through the ports.

Scope.
* A complete system is read by the semantic layer in one of two kinds (`Behaviour`): a
  continuous-time system with ports, interpreted here and in `theorem/Flow/Defs.lean`, or a
  discrete-time system with ports, interpreted in `theorem/Map/Defs.lean`.
* The sentences of the library are the Flow sentences of the zero-input dynamics about the origin
  and passivity; their interpretation on both kinds of systems is fixed here once
  (`Sentence.holds`). An autonomous field or map is the system without ports.

Source: the flow semantics (`theorem/Flow/Defs.lean`; Mathlib's `IsIntegralCurveOn` for
solutions under an input) and the map semantics (`theorem/Map/Defs.lean`); dissipativity with
respect to the supply rate `u ⬝ y`.

Results.
* `Port.System` (field and conjugate output), `System.supply`, `System.IsTrajectoryOn` (solutions
  under an input signal), `System.zeroInput`, `System.PassiveWith`, `System.Passive`,
  `System.autonomous`.
* `Behaviour` (`continuous`, `discrete`), `Sentence` (`flow P`, `passive`) and `Sentence.holds`.
-/

noncomputable section

namespace powerlib

namespace Port

open Set MeasureTheory

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A system with `n` states and `p` ports. -/
structure System (n p : ℕ) where
  /-- The state dynamics under a port input. -/
  field : EuclideanSpace ℝ (Fin n) → (Fin p → ℝ) → EuclideanSpace ℝ (Fin n)
  /-- The conjugate port output. -/
  output : EuclideanSpace ℝ (Fin n) → (Fin p → ℝ) → (Fin p → ℝ)

/-- The power supplied through the ports. -/
def System.supply (s : System n p) (x : ℝⁿ) (u : Fin p → ℝ) : ℝ := u ⬝ᵥ s.output x u

/-- A solution segment under the input signal `u`. -/
def System.IsTrajectoryOn (s : System n p) (u : ℝ → Fin p → ℝ) (x : ℝ → ℝⁿ) (t₀ t₁ : ℝ) :
    Prop :=
  IsIntegralCurveOn x (fun t y => s.field y (u t)) (Icc t₀ t₁)

/-- The autonomous field with the ports held at zero. -/
def System.zeroInput (s : System n p) : ℝⁿ → ℝⁿ := fun x => s.field x 0

/-- Passivity with the storage `V`. -/
def System.PassiveWith (s : System n p) (V : ℝⁿ → ℝ) : Prop :=
  (∀ x, 0 ≤ V x) ∧ ∀ (u : ℝ → Fin p → ℝ) (x : ℝ → ℝⁿ) (t₀ t₁ : ℝ), t₀ ≤ t₁ →
    s.IsTrajectoryOn u x t₀ t₁ →
      IntervalIntegrable (fun t => s.supply (x t) (u t)) volume t₀ t₁ →
        V (x t₁) - V (x t₀) ≤ ∫ t in t₀..t₁, s.supply (x t) (u t)

/-- Passivity with some storage. -/
def System.Passive (s : System n p) : Prop := ∃ V, s.PassiveWith V

/-- The system of an autonomous field: no ports. -/
def System.autonomous (f : ℝⁿ → ℝⁿ) : System n 0 := ⟨fun x _ => f x, fun _ _ => 0⟩

end Port

variable {n p : ℕ}

/-- A complete system as the semantic layer reads it: a continuous-time system with ports or a
discrete-time system with ports. -/
inductive Behaviour (n p : ℕ)
  /-- A continuous-time system (`theorem/Flow/Defs.lean`). -/
  | continuous (s : Port.System n p)
  /-- A discrete-time system (`theorem/Map/Defs.lean`). -/
  | discrete (s : Map.System n p)

instance : Coe (Port.System n p) (Behaviour n p) := ⟨Behaviour.continuous⟩

/-- The sentences of the library: a behavioural sentence of the zero-input dynamics about the
origin, or passivity. -/
inductive Sentence
  | flow (P : Flow.Property)
  | passive

/-- The interpretation of every sentence on both kinds of systems, fixed once. -/
def Sentence.holds : Sentence → Behaviour n p → Prop
  | .flow P, .continuous s => P.holds s.zeroInput 0
  | .passive, .continuous s => s.Passive
  | .flow P, .discrete s => P.holdsMap s.period s.zeroInput 0
  | .passive, .discrete s => s.Passive

end powerlib
