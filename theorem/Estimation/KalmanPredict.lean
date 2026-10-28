import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes
import theorem.Stochastic.LyapunovCovariance
import Mathlib.Analysis.Matrix.Order

/-! # Kalman prediction step: covariance propagation

The discrete prediction keeps the covariance positive semidefinite, and the time-invariant
continuous prediction ODE has an explicit solution converging to the stationary covariance.

Scope.
* Linear algebra / matrix ODE, not an engineering result. These are statements about the
  deterministic covariance recursion and ODE; that `P` is the conditional covariance of a
  linear-Gaussian state-space model is not formalized.
* Time-invariant `A`, `Q = Σ Σᵀ`.
* The general variation-of-constants form `P(t) = Φ(t, t₀) P₀ Φ(t, t₀)ᵀ +
  ∫_{t₀}^t Φ(t, τ) Q(τ) Φ(t, τ)ᵀ dτ` for time-varying `A(t)` (relative to a fundamental matrix
  `Φ`), its constant-`A` instance without an algebraic solution `P∞`, and the Riccati integral
  representation are in `theorem/Estimation/KalmanLTV.lean`.

Source: work-sync theory/T-kalman-filter.md §1.2 (continuous-time prediction between
measurements `Ṗ = A P + P Aᵀ + Σ Σᵀ`; discrete prediction `P_{k|k−1} = Φ_k P Φ_kᵀ + Q_k`),
§1.3 (steady state / Lyapunov limit).

Results.
* `predict_posSemidef` — `P ⪰ 0`, `Q ⪰ 0` ⇒ `Φ P Φᵀ + Q ⪰ 0` (discrete prediction keeps PSD).
* `predict_cov_ode_solution` — if `P∞` solves the algebraic equation `A P∞ + P∞ Aᵀ + Q = 0`,
  then `P(t) = e^{tA} (P₀ − P∞) e^{tAᵀ} + P∞` (`Lyapunov.covSol`) solves
  `Ṗ = A P + P Aᵀ + Q`, `P(0) = P₀`; `predict_cov_ode_unique`: it is the only solution.
* `predict_cov_hurwitz` — for `A` Hurwitz and `Q ⪰ 0` such a `P∞ ⪰ 0` exists (uniquely), the
  prediction ODE has the explicit solution above and `P(t) → P∞`.
-/

noncomputable section
namespace powerlib.Estimation

open Matrix Filter powerlib.Stochastic.Lyapunov
open scoped Matrix.Norms.Frobenius Topology

variable {n : ℕ}

noncomputable local instance frobeniusENormedAddMonoid'' :
    ENormedAddMonoid (Matrix (Fin n) (Fin n) ℝ) :=
  (NormedAddCommGroup.toENormedAddCommMonoid :
    ENormedAddCommMonoid (Matrix (Fin n) (Fin n) ℝ)).toENormedAddMonoid

/-- Discrete prediction preserves positive semidefiniteness: `Φ P Φᵀ + Q ⪰ 0`. -/
@[tmio T, powerlib_foundation] theorem predict_posSemidef {m : Type*} [Fintype m] {k : Type*}
    [Fintype k] (Φ : Matrix m k ℝ) {P : Matrix k k ℝ} {Q : Matrix m m ℝ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : (Φ * P * Φᵀ + Q).PosSemidef := by
  have h := hP.mul_mul_conjTranspose_same Φ
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact h.add hQ

/-- The explicit prediction covariance `e^{tA}(P₀ − P∞)e^{tAᵀ} + P∞` solves the prediction ODE
`Ṗ = A P + P Aᵀ + Q` with `P(0) = P₀`, whenever `P∞` solves the algebraic equation. -/
@[tmio T, powerlib_foundation] theorem predict_cov_ode_solution {A Q Pinf : Matrix (Fin n) (Fin n) ℝ}
    (hinf : SolvesCovLyapunov A Pinf Q) (P₀ : Matrix (Fin n) (Fin n) ℝ) :
    covSol A Pinf P₀ 0 = P₀ ∧
      ∀ t, HasDerivAt (covSol A Pinf P₀) (A * covSol A Pinf P₀ t + covSol A Pinf P₀ t * Aᵀ + Q) t :=
  ⟨covSol_zero A Pinf P₀, covSol_hasDerivAt hinf P₀⟩

/-- Uniqueness of the prediction covariance trajectory. -/
@[tmio T, powerlib_foundation] theorem predict_cov_ode_unique {A Q Pinf P₀ : Matrix (Fin n) (Fin n) ℝ}
    (hinf : SolvesCovLyapunov A Pinf Q) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P (A * P t + P t * Aᵀ + Q) t) (h0 : P 0 = P₀) :
    P = covSol A Pinf P₀ :=
  covODE_unique hinf hP h0

/-- **Hurwitz prediction**: for `A` Hurwitz and `Q ⪰ 0` there is a unique `P∞ ⪰ 0` with
`A P∞ + P∞ Aᵀ + Q = 0`; every solution of the prediction ODE with `P(0) = P₀` equals
`e^{tA}(P₀ − P∞)e^{tAᵀ} + P∞`, and it converges to `P∞`. -/
@[tmio T, powerlib_foundation] theorem predict_cov_hurwitz {A Q : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) (hQ : Q.PosSemidef) (P₀ : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Pinf : Matrix (Fin n) (Fin n) ℝ, Pinf.PosSemidef ∧ SolvesCovLyapunov A Pinf Q ∧
      (∀ P : ℝ → Matrix (Fin n) (Fin n) ℝ, (∀ t, HasDerivAt P (A * P t + P t * Aᵀ + Q) t) →
        P 0 = P₀ → P = covSol A Pinf P₀) ∧
      Tendsto (fun t => ‖covSol A Pinf P₀ t - Pinf‖) atTop (𝓝 0) := by
  obtain ⟨Pinf, hpsd, hsol, -⟩ := exists_unique_posSemidef_covLyapunov hA Q hQ
  exact ⟨Pinf, hpsd, hsol, fun P hP h0 => covODE_unique hsol hP h0, covSol_tendsto_norm hA⟩

end powerlib.Estimation
