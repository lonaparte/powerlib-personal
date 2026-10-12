import dependencies.LeanForControl
import theorem.Attributes

/-! # Flow semantics

The single definition of the behaviour of autonomous systems. Every model family of the library
is read through these definitions and nothing else.

A system is a complete autonomous vector field `f : ℝⁿ → ℝⁿ` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`,
after inputs are fixed and feedback is closed: continuous time, no delay, sampling, PWM or
switching. Solutions are Mathlib integral curves on finite forward segments (LeanForControl's
`IsTrajectoryOn`), so finite-time escape never makes a property vacuous. The local notions —
Lyapunov stability, local asymptotic and local exponential stability, instability — are
LeanForControl's definitions, reused unchanged. The two global notions are defined here because
they also assert that every solution exists for all forward time. Three further notions complete
the sentence language: a decay rate on every solution segment, contraction of solutions sampled
at an integer horizon, and conservation of an energy with a strict minimum at the equilibrium. -/

noncomputable section

namespace powerlib.Flow

open Set

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Every initial state at every initial time has a solution on the whole forward ray. -/
def ForwardComplete (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ (t₀ : ℝ) (x₀ : ℝⁿ), ∃ φ : ℝ → ℝⁿ,
    φ t₀ = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici t₀)

/-- Global exponential stability: an equilibrium, a solution through every state, and one
exponential estimate on every solution segment. -/
def GloballyExponentiallyStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  IsEquilibrium f x_eq ∧ ForwardComplete f ∧
    ∃ C a : ℝ, 1 ≤ C ∧ 0 < a ∧ ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ →
      ∀ t ∈ Icc t₀ t₁, ‖φ t - x_eq‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x_eq‖

/-- Global asymptotic stability, including a solution through every state. -/
def GloballyAsymptoticallyStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  IsEquilibrium f x_eq ∧ ForwardComplete f ∧ GlobalAsymptoticStable f x_eq

/-- Decay at the rate `a`: one constant `C` bounds every solution segment by
`C e^{-a (t - t₀)}` times its initial distance to the equilibrium. A negative rate bounds the
growth. -/
def Decay (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (a : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ →
    ∀ t ∈ Icc t₀ t₁, ‖φ t - x_eq‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x_eq‖

/-- Sampled contraction: over some positive integer horizon every solution segment ends closer to
the equilibrium by a fixed factor below one. -/
def SampledContraction (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ c < 1, ∀ (t₀ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ (t₀ + k) →
    ‖φ (t₀ + k) - x_eq‖ ≤ c * ‖φ t₀ - x_eq‖

/-- Conservation: a continuous energy with a strict minimum at the equilibrium is constant along
every solution segment. -/
def Conservative (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∃ V : ℝⁿ → ℝ, Continuous V ∧ (∀ x, x ≠ x_eq → V x_eq < V x) ∧
    ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ → ∀ t ∈ Icc t₀ t₁, V (φ t) = V (φ t₀)

/-- The behavioural sentences of the library about an autonomous field and its equilibrium. -/
inductive Property
  | lyapunovStable
  | locallyAsymptoticallyStable
  | locallyExponentiallyStable
  | globallyAsymptoticallyStable
  | globallyExponentiallyStable
  | unstable
  | decay (a : ℝ)
  | contractive
  | conservative

/-- The interpretation of every sentence, fixed once. -/
def Property.holds : Property → (ℝⁿ → ℝⁿ) → ℝⁿ → Prop
  | .lyapunovStable => LyapunovStable
  | .locallyAsymptoticallyStable => LocalAsymptoticStable
  | .locallyExponentiallyStable => LocallyExponentiallyStable
  | .globallyAsymptoticallyStable => GloballyAsymptoticallyStable
  | .globallyExponentiallyStable => GloballyExponentiallyStable
  | .unstable => Unstable
  | .decay a => fun f x_eq => Decay f x_eq a
  | .contractive => SampledContraction
  | .conservative => Conservative

/-- The sentences asserting convergence to the equilibrium. -/
def Property.Attractive : Property → Prop
  | .locallyAsymptoticallyStable | .locallyExponentiallyStable
  | .globallyAsymptoticallyStable | .globallyExponentiallyStable => True
  | _ => False

@[simp, powerlib_foundation] theorem Property.attractive_locallyAsymptoticallyStable :
    Property.locallyAsymptoticallyStable.Attractive := trivial

@[simp, powerlib_foundation] theorem Property.attractive_locallyExponentiallyStable :
    Property.locallyExponentiallyStable.Attractive := trivial

@[simp, powerlib_foundation] theorem Property.attractive_globallyAsymptoticallyStable :
    Property.globallyAsymptoticallyStable.Attractive := trivial

@[simp, powerlib_foundation] theorem Property.attractive_globallyExponentiallyStable :
    Property.globallyExponentiallyStable.Attractive := trivial

end powerlib.Flow
