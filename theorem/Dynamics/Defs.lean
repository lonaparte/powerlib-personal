import dependencies.Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.ODE.Basic
import theorem.Attributes

/-! Trajectory semantics for finite-dimensional continuous-time autonomous systems.
The vector field is the complete nonlinear field, after fixing the input or closing
the feedback loop. There is no linearization, amplitude restriction, discretization,
delay, PWM, or implicit external forcing. `ForwardComplete` explicitly requires a
solution through every initial state and every initial time.
-/

noncomputable section
namespace powerlib.Dynamics

abbrev State (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A solution on a set of times, including the one-sided derivative at endpoints. -/
abbrev IsIntegralCurveOn (φ : ℝ → E) (f : ℝ → E → E) (s : Set ℝ) : Prop :=
  _root_.IsIntegralCurveOn φ f s

@[powerlib_foundation] theorem IsIntegralCurveOn.continuousOn
    {φ : ℝ → E} {f : ℝ → E → E} {s : Set ℝ} (hφ : IsIntegralCurveOn φ f s) :
    ContinuousOn φ s :=
  _root_.IsIntegralCurveOn.continuousOn hφ

@[powerlib_foundation] theorem IsIntegralCurveOn.mono
    {φ : ℝ → E} {f : ℝ → E → E} {s u : Set ℝ}
    (hφ : IsIntegralCurveOn φ f s) (hu : u ⊆ s) : IsIntegralCurveOn φ f u :=
  _root_.IsIntegralCurveOn.mono hφ hu

@[powerlib_foundation] theorem isIntegralCurveOn_upstream_iff
    {φ : ℝ → E} {f : ℝ → E → E} {s : Set ℝ} :
    IsIntegralCurveOn φ f s ↔ _root_.IsIntegralCurveOn φ f s := Iff.rfl

/-- A finite solution segment; finite-time escape cannot make stability vacuous. -/
abbrev IsTrajectoryOn (φ : ℝ → E) (f : E → E) (a b : ℝ) : Prop :=
  IsIntegralCurveOn φ (fun _ x => f x) (Set.Icc a b)

/-- Every initial condition has a solution on its entire forward time ray. -/
def ForwardComplete (f : E → E) : Prop :=
  ∀ (a : ℝ) (x₀ : E), ∃ φ : ℝ → E,
    φ a = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici a)

/-- Exponential stability of the full state for every initial amplitude.
The predicate includes equilibrium and global solution existence, and its estimate
quantifies over every finite solution segment, not a selected response. -/
def GloballyExponentiallyStable (f : E → E) (equilibrium : E) : Prop :=
  f equilibrium = 0 ∧ ForwardComplete f ∧
  ∃ C rate : ℝ, 1 ≤ C ∧ 0 < rate ∧
    ∀ (a b : ℝ) (φ : ℝ → E), IsTrajectoryOn φ f a b →
      ∀ t ∈ Set.Icc a b,
        ‖φ t - equilibrium‖ ≤ C * Real.exp (-(rate * (t - a))) * ‖φ a - equilibrium‖

end powerlib.Dynamics
