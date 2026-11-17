import dependencies.LeanForControl
import theorem.Estimation.KalmanLTV
import theorem.Dynamics.VariationOfConstants

/-! # LTV Kalman covariance with LeanForControl's state-transition matrix

The fundamental-matrix hypothesis of `theorem/Estimation/KalmanLTV.lean`, discharged for every
continuous time-varying `A(t)` with LeanForControl's Peano–Baker state-transition matrix.

Scope.
* Linear algebra / matrix ODE, not an engineering result.
* The state-transition matrix is `LinearSystems.stateTransitionMatrix` (Hespanha, *Linear
  Systems Theory*, Ch. 5), reused directly through the dependency interface
  (`dependencies/LeanForControl.lean` imports `LeanForControl.LinearSystems.Solutions.CtsLTV`).
  The upstream norm on matrices is the `L∞`-operator norm (`Matrix.Norms.Operator`), used here
  only to supply its segment bounds.

Source: work-sync theory/T-kalman-filter.md §1.2, §1.4 (as in
`theorem/Estimation/KalmanLTV.lean`).

Results. The fundamental-matrix hypothesis is the generic law `Dynamics.stm_hasDerivAt`
(`theorem/Dynamics/VariationOfConstants.lean`: `∂_t Φ(t, s) = A(t) Φ(t, s)` at every `t ∈ ℝ`)
with `Φ(s, s) = I` (upstream `stateTransitionMatrix_self`). With it the variation-of-constants
laws of `theorem/LinearAlgebra/LyapunovODE.lean` (`ltvCov_self`, `hasDerivAt_ltvCov`,
`ltvCov_unique`) give the LTV prediction covariance
`P(t) = Φ(t, t₀) P₀ Φ(t, t₀)ᵀ + ∫_{t₀}^t Φ(t, τ) Q(τ) Φ(t, τ)ᵀ dτ` as the unique solution of
`Ṗ = A(t) P + P A(t)ᵀ + Q(t)`, `P(t₀) = P₀`, for continuous `A(t)`, `Q(t)`.
* `riccati_joseph_form_stateTransition` — a symmetric Riccati solution equals its closed-loop
  (Joseph) integral representation with `Φ_K` the state-transition matrix of `A − P Cᵀ R⁻¹ C`.
* `riccati_posSemidef_of_continuous` — `Q ⪰ 0`, `R ≻ 0`, `P(t₀) ⪰ 0` ⇒ the Riccati solution is
  `⪰ 0` for `t ≥ t₀` (no fundamental-matrix hypothesis left).
-/

noncomputable section
namespace powerlib.Estimation.LTV

open Matrix Set powerlib.LinearAlgebra
open scoped Matrix.Norms.Operator

variable {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}

variable {p : ℕ} {C : ℝ → Matrix (Fin p) (Fin n) ℝ} {Q : ℝ → Matrix (Fin n) (Fin n) ℝ}
  {R : ℝ → Matrix (Fin p) (Fin p) ℝ}

/-- **Riccati solution, closed-loop integral form, with LeanForControl's state-transition
matrix**: a symmetric solution of `Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P` (continuous coefficients,
`R` symmetric invertible) equals
`Φ_K(t, t₀) P(t₀) Φ_K(t, t₀)ᵀ + ∫_{t₀}^t Φ_K(t, τ) (Q + K R Kᵀ)(τ) Φ_K(t, τ)ᵀ dτ`, where
`K = P Cᵀ R⁻¹` and `Φ_K` is the Peano–Baker state-transition matrix of `A − K C`. -/
@[tmio T, powerlib_foundation] theorem riccati_joseph_form_stateTransition (hA : Continuous A)
    (hC : Continuous C) (hQ : Continuous Q) (hR : Continuous R) (hRs : ∀ t, (R t)ᵀ = R t)
    (hRu : ∀ t, IsUnit (R t).det) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P
      (A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t) t)
    (hPs : ∀ t, (P t)ᵀ = P t) (t₀ : ℝ) :
    P = ltvCov (LinearSystems.stateTransitionMatrix
        fun t => A t - P t * (C t)ᵀ * (R t)⁻¹ * C t)
      (fun t => Q t + (P t * (C t)ᵀ * (R t)⁻¹) * R t * (P t * (C t)ᵀ * (R t)⁻¹)ᵀ) (P t₀) t₀ := by
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  exact riccati_joseph_form hA hC hQ hR hRs hRu hP hPs
    (Dynamics.stm_hasDerivAt (closedLoop_continuous hA hC hR hRu hPc))
    LinearSystems.stateTransitionMatrix_self t₀

/-- **The Kalman–Bucy Riccati covariance stays positive semidefinite** (no extra hypothesis):
for continuous `A, C, Q, R` with `Q(t) ⪰ 0`, `R(t) ≻ 0`, every solution of
`Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P` with `P(t₀) ⪰ 0` has `P(t) ⪰ 0` for all `t ≥ t₀`. -/
@[tmio T, powerlib_foundation] theorem riccati_posSemidef_of_continuous (hA : Continuous A)
    (hC : Continuous C) (hQ : Continuous Q) (hR : Continuous R) (hQp : ∀ t, (Q t).PosSemidef)
    (hRp : ∀ t, (R t).PosDef) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P
      (A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t) t)
    {t₀ : ℝ} (hP₀ : (P t₀).PosSemidef) {t : ℝ} (ht : t₀ ≤ t) : (P t).PosSemidef := by
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hRu : ∀ t, IsUnit (R t).det := fun t => (hRp t).isUnit.map Matrix.detMonoidHom
  exact riccati_posSemidef hA hC hQ hR hQp hRp hP
    (Dynamics.stm_hasDerivAt (closedLoop_continuous hA hC hR hRu hPc))
    LinearSystems.stateTransitionMatrix_self hP₀ ht

end powerlib.Estimation.LTV
