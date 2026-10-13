import dependencies.LeanForControl
import theorem.Attributes

/-! # Variation of constants for linear time-varying systems (LeanForControl wrappers)

Foundation layer (category C: direct reuse of upstream theorems, Rules §15–§16).

System (continuous time, finite state index `X`, input index `U`, real coefficients):
`ẋ = A(t) x + B(t) u(t)` with continuous `A : ℝ → Matrix X X ℝ`, `B : ℝ → Matrix X U ℝ` and
input `u : ℝ → U → ℝ`. The state transition matrix `Φ(t, t₀)` is LeanForControl's Peano–Baker
series `LinearSystems.stateTransitionMatrix`; the forced response is LeanForControl's
`LinearSystems.forcedResponse A B u t₀ x₀ t = Φ(t, t₀) x₀ + ∫_{t₀}^{t} Φ(t, τ) B(τ) u(τ) dτ`
(Hespanha, *Linear Systems Theory*, Thm. 5.2).

Results (each a thin wrapper that invokes the upstream theorem; no upstream proof is copied):
* `forcedResponse_hasDerivAt`: the forced response solves the state equation at every time
  (upstream `LinearSystems.ContinuousLinearSystem.isTrajectory_forcedResponse`, applied to the
  system `(A, B, 0, 0)`).
* `forcedResponse_self`: it starts at `x₀` (upstream `LinearSystems.variationOfConstants_self`).
* `eq_forcedResponse_of_isIntegralCurveOn`: every solution on the segment between `t₀` and `t₁`
  (a Mathlib integral curve, one-sided at the endpoints) with `x(t₀) = x₀` equals the forced
  response there (upstream `IsIntegralCurveOn.isIntegralSolution`,
  `LinearSystems.isIntegralSolution_forcedResponse`, `LinearSystems.continuousOn_forcedResponse`
  and the uniqueness theorem `LinearSystems.variationOfConstants_unique`).
* `eq_variationOfConstants_of_hasDerivAt`: the variation-of-constants formula for every global
  solution, written out with `Φ`.

The only additional step is the compactness bound `‖A s‖ ≤ M` on the segment (operator `L∞`
norm, `Matrix.Norms.Operator`, the norm of the upstream track) required by the upstream
hypotheses.

Dependency note: LeanForControl's `LinearSystems/Solutions/CtsLTV.lean` did not build against the
pinned Mathlib; `dependencies/LeanForControl-4.34.1.patch` contains the minimal compatibility diff
(three proof-local changes, no statement changes) and `dependencies/LeanForControl.lean` imports
the module.

Architecture: generic mathematical support (no `Family`, no definitions); the statements are
about arbitrary continuous coefficient maps, so they are public foundation.

Source: work-sync theory/T-singular-perturbation.md and theory/T-tikhonov.md use the linear
solution formula for the slow and boundary-layer subsystems; the formula itself is Hespanha,
Ch. 5, Thm. 5.2, as formalized upstream.
-/

noncomputable section
namespace powerlib.Dynamics
open Matrix Set
open scoped Matrix.Norms.Operator

variable {X U : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-- The forced response solves `ẋ = A(t) x + B(t) u(t)` at every time. -/
@[powerlib_foundation] theorem forcedResponse_hasDerivAt {A : ℝ → Matrix X X ℝ}
    {B : ℝ → Matrix X U ℝ} {u : ℝ → U → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) (t₀ : ℝ) (x₀ : X → ℝ) (t : ℝ) :
    HasDerivAt (LinearSystems.forcedResponse A B u t₀ x₀)
      (A t *ᵥ LinearSystems.forcedResponse A B u t₀ x₀ t + B t *ᵥ u t) t :=
  LinearSystems.ContinuousLinearSystem.isTrajectory_forcedResponse
    (⟨A, B, 0, 0⟩ : LinearSystems.ContinuousLinearSystem X U X ℝ) hA hB hu t₀ x₀ t

/-- The forced response starts at `x₀`. -/
@[powerlib_foundation] theorem forcedResponse_self (A : ℝ → Matrix X X ℝ)
    (B : ℝ → Matrix X U ℝ) (u : ℝ → U → ℝ) (t₀ : ℝ) (x₀ : X → ℝ) :
    LinearSystems.forcedResponse A B u t₀ x₀ t₀ = x₀ :=
  LinearSystems.variationOfConstants_self t₀ x₀

/-- Every solution of `ẋ = A(t) x + B(t) u(t)` on the segment between `t₀` and `t₁` with
`x(t₀) = x₀` is the forced response there. -/
@[powerlib_foundation] theorem eq_forcedResponse_of_isIntegralCurveOn {A : ℝ → Matrix X X ℝ}
    {B : ℝ → Matrix X U ℝ} {u : ℝ → U → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ : ℝ} {x₀ : X → ℝ} {x : ℝ → X → ℝ}
    (hx : IsIntegralCurveOn x (fun s v => A s *ᵥ v + B s *ᵥ u s) (uIcc t₀ t₁))
    (h0 : x t₀ = x₀) :
    ∀ t ∈ uIcc t₀ t₁, x t = LinearSystems.forcedResponse A B u t₀ x₀ t := by
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn (f := A)
    (s := uIcc t₀ t₁) hA.continuousOn
  have hxc : ContinuousOn x (uIcc t₀ t₁) := hx.continuousOn
  have hFx : ContinuousOn (fun s => A s *ᵥ x s + B s *ᵥ u s) (uIcc t₀ t₁) :=
    ((continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk hxc)).add (hB.matrix_mulVec hu).continuousOn
  have hsol := hx.isIntegralSolution hFx
  rw [h0] at hsol
  exact LinearSystems.variationOfConstants_unique hA hB hu hM hsol
    (LinearSystems.isIntegralSolution_forcedResponse hA hB hu hM x₀) hxc
    (LinearSystems.continuousOn_forcedResponse hA hB hu hM x₀)

/-- **Variation of constants.** Every global solution of `ẋ = A(t) x + B(t) u(t)` satisfies
`x(t) = Φ(t, t₀) x(t₀) + ∫_{t₀}^{t} Φ(t, τ) B(τ) u(τ) dτ` for all `t`. -/
@[powerlib_foundation] theorem eq_variationOfConstants_of_hasDerivAt {A : ℝ → Matrix X X ℝ}
    {B : ℝ → Matrix X U ℝ} {u : ℝ → U → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {x : ℝ → X → ℝ} (hx : ∀ t, HasDerivAt x (A t *ᵥ x t + B t *ᵥ u t) t)
    (t₀ t : ℝ) :
    x t = LinearSystems.stateTransitionMatrix A t t₀ *ᵥ x t₀ +
      ∫ τ in t₀..t, LinearSystems.stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ) :=
  eq_forcedResponse_of_isIntegralCurveOn hA hB hu (t₁ := t)
    (fun s _ => (hx s).hasDerivWithinAt) rfl t right_mem_uIcc

end powerlib.Dynamics
