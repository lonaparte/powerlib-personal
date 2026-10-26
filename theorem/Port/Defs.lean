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
* A complete system is read by the semantic layer in one of three kinds (`Behaviour`): a
  continuous-time system with ports, interpreted here and in `theorem/Flow/Defs.lean`; a
  discrete-time system with ports, interpreted in `theorem/Map/Defs.lean`; or a random
  continuous-time system with an operating envelope: a system for each sample of the disturbance
  (a random, time-invariant perturbation: parameters, biases, tolerances), an initial set, a safe
  set and the law of the samples. The behaviour holds no signal: a time-varying disturbance enters
  through states of an exosystem, and white noise is not represented.
* The sentences of the library are the Flow sentences of the zero-input dynamics about the origin,
  passivity, and the finite-time sentences about the operating envelope: safety over a horizon `T`
  at a level `ε` (some solution of the zero-input dynamics from the initial set leaves the safe set
  before `T` with probability at most `ε`) and a mean-square bound before `T`. Their
  interpretation on every kind of system is fixed here once (`Sentence.holds`): on a random system
  the flow sentences and passivity hold for every sample, and a system read without an envelope
  satisfies every envelope sentence. An autonomous field or map is the system without ports.

Source: the flow semantics (`theorem/Flow/Defs.lean`; Mathlib's `IsIntegralCurveOn` for
solutions under an input) and the map semantics (`theorem/Map/Defs.lean`); dissipativity with
respect to the supply rate `u ⬝ y`; finite-time stability over a horizon with given bounds
(Dorato 1961; Amato, Ariola and Dorato 2001) and its stochastic form (Kushner 1966).

Results.
* `Port.System` (field and conjugate output), `System.supply`, `System.IsTrajectoryOn` (solutions
  under an input signal), `System.zeroInput`, `System.PassiveWith`, `System.Passive`,
  `System.autonomous`; the envelope notions `System.Exceeds`, `System.reach`, `System.Solvable`,
  `System.squareAt`.
* `Envelope.Sample`, `Envelope.Property` (`safe T ε`, `meanSquare T c`).
* `Behaviour` (`continuous`, `discrete`, `disturbed`), `Behaviour.exceedance`, `Sentence`
  (`flow P`, `passive`, `envelope E`) and `Sentence.holds`.
-/

noncomputable section

namespace powerlib

open MeasureTheory
open scoped ENNReal

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

/-- Some solution of the zero-input dynamics starting in `S` leaves `A` before the horizon `T`:
a solution segment on `[0, t]`, `t < T`, with `x 0 ∈ S` and `x t ∉ A`. -/
def System.Exceeds (s : System n p) (S A : Set ℝⁿ) (T : ℝ≥0∞) : Prop :=
  ∃ (x : ℝ → ℝⁿ) (t : ℝ), 0 ≤ t ∧ ENNReal.ofReal t < T ∧ x 0 ∈ S ∧ s.IsTrajectoryOn 0 x 0 t ∧
    x t ∉ A

/-- The states reached before the horizon `T` by the solutions of the zero-input dynamics starting
in `S`. -/
def System.reach (s : System n p) (S : Set ℝⁿ) (T : ℝ≥0∞) : Set ℝⁿ :=
  {y | ∃ (x : ℝ → ℝⁿ) (t : ℝ), 0 ≤ t ∧ ENNReal.ofReal t < T ∧ x 0 ∈ S ∧ s.IsTrajectoryOn 0 x 0 t ∧
    x t = y}

/-- Every state of `S` starts a solution segment of the zero-input dynamics on `[0, T]`. -/
def System.Solvable (s : System n p) (S : Set ℝⁿ) (T : ℝ) : Prop :=
  ∀ x₀ ∈ S, ∃ x : ℝ → ℝⁿ, x 0 = x₀ ∧ s.IsTrajectoryOn 0 x 0 T

/-- The largest square norm at time `t` over the solutions of the zero-input dynamics starting in
`S`. -/
def System.squareAt (s : System n p) (S : Set ℝⁿ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (x : ℝ → ℝⁿ) (_ : x 0 ∈ S ∧ s.IsTrajectoryOn 0 x 0 t), ‖x t‖ₑ ^ 2

end Port

namespace Envelope

/-- The sample space of disturbances: countably many real coordinates (a standard Borel space).
A sample fixes one realization of the system: its uncertain parameters, biases and tolerances. -/
abbrev Sample : Type := ℕ → ℝ

/-- The finite-time sentences about the operating envelope of a system (an initial set and a
safe set). -/
inductive Property
  /-- With probability at most `ε`, some solution from the initial set leaves the safe set before
  the horizon `T` (`T = ⊤`: ever). -/
  | safe (T ε : ℝ≥0∞)
  /-- At every time before the horizon `T`, the mean over disturbances of the largest square norm
  of the solutions from the initial set is at most `c`. -/
  | meanSquare (T c : ℝ≥0∞)

end Envelope

variable {n p : ℕ}

/-- A complete system as the semantic layer reads it: a continuous-time system with ports, a
discrete-time system with ports, or a random continuous-time system within an operating envelope. -/
inductive Behaviour (n p : ℕ)
  /-- A continuous-time system (`theorem/Flow/Defs.lean`). -/
  | continuous (s : Port.System n p)
  /-- A discrete-time system (`theorem/Map/Defs.lean`). -/
  | discrete (s : Map.System n p)
  /-- A continuous-time system `s ω` for each sample `ω` of the disturbance, distributed by `ν`,
  with the initial set `S` and the safe set `A`. The disturbance is a random, time-invariant
  perturbation of the system (parameters, biases, tolerances); a time-varying disturbance enters
  through states of an exosystem. -/
  | disturbed (s : Envelope.Sample → Port.System n p) (S A : Set (EuclideanSpace ℝ (Fin n)))
      (ν : Measure Envelope.Sample)

instance : Coe (Port.System n p) (Behaviour n p) := ⟨Behaviour.continuous⟩

/-- The probability that some solution from the initial set leaves the safe set before the horizon
`T`; a system read without an envelope has no initial states. -/
def Behaviour.exceedance (T : ℝ≥0∞) : Behaviour n p → ℝ≥0∞
  | .continuous _ => 0
  | .discrete _ => 0
  | .disturbed s S A ν => ν {ω | (s ω).Exceeds S A T}

/-- The sentences of the library: a behavioural sentence of the zero-input dynamics about the
origin, passivity, or a finite-time sentence about the operating envelope. -/
inductive Sentence
  | flow (P : Flow.Property)
  | passive
  | envelope (E : Envelope.Property)

/-- The interpretation of every sentence on every kind of system, fixed once. The flow sentences
are sentences of the zero-input dynamics and passivity quantifies every input; on a random system
both are read for every sample. A system read without an envelope has no initial states, so its
envelope sentences hold. -/
def Sentence.holds : Sentence → Behaviour n p → Prop
  | .flow P, .continuous s => P.holds s.zeroInput 0
  | .passive, .continuous s => s.Passive
  | .envelope _, .continuous _ => True
  | .flow P, .discrete s => P.holdsMap s.period s.zeroInput 0
  | .passive, .discrete s => s.Passive
  | .envelope _, .discrete _ => True
  | .flow P, .disturbed s _ _ _ => ∀ ω, P.holds (s ω).zeroInput 0
  | .passive, .disturbed s _ _ _ => ∀ ω, (s ω).Passive
  | .envelope (.safe T ε), .disturbed s S A ν => ν {ω | (s ω).Exceeds S A T} ≤ ε
  | .envelope (.meanSquare T c), .disturbed s S _ ν =>
      ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < T → ∫⁻ ω, (s ω).squareAt S t ∂ν ≤ c

end powerlib
