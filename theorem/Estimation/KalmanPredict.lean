import dependencies.Mathlib
import theorem.Attributes
import theorem.LinearAlgebra.Congruence

/-! # Kalman prediction step: covariance propagation

The discrete prediction `Φ P Φᵀ + Q` keeps the covariance positive semidefinite.

Scope.
* Linear algebra, not an engineering result. These are statements about the deterministic
  covariance recursion; that `P` is the conditional covariance of a linear-Gaussian state-space
  model is not formalized.
* The continuous prediction `Ṗ = A P + P Aᵀ + Q`: for time-invariant `A` with an algebraic
  solution `P∞` (`A P∞ + P∞ Aᵀ + Q = 0`) the unique solution `e^{tA} (P₀ − P∞) e^{tAᵀ} + P∞`, and
  for Hurwitz `A` existence, uniqueness and semidefiniteness of `P∞` and `P(t) → P∞`, are in
  `theorem/Stochastic/LyapunovCovariance.lean`; the variation-of-constants form
  `P(t) = Φ(t, t₀) P₀ Φ(t, t₀)ᵀ + ∫_{t₀}^t Φ(t, τ) Q(τ) Φ(t, τ)ᵀ dτ` for time-varying `A(t)` (and
  constant `A` without `P∞`) is in `theorem/LinearAlgebra/LyapunovODE.lean`; the Riccati
  integral representation is in `theorem/Estimation/KalmanLTV.lean`.

Source: work-sync theory/T-kalman-filter.md §1.2 (discrete prediction
`P_{k|k−1} = Φ_k P Φ_kᵀ + Q_k`).

Results.
* `predict_posSemidef` — `P ⪰ 0`, `Q ⪰ 0` ⇒ `Φ P Φᵀ + Q ⪰ 0` (discrete prediction keeps PSD; with
  `Φ = I − K H`, `Q = K R Kᵀ` it is the Joseph form, `joseph_posSemidef`).
-/

noncomputable section
namespace powerlib.Estimation

open Matrix

/-- Discrete prediction preserves positive semidefiniteness: `Φ P Φᵀ + Q ⪰ 0`. -/
@[tmio T, powerlib_foundation] theorem predict_posSemidef {m : Type*} [Fintype m] {k : Type*}
    [Fintype k] (Φ : Matrix m k ℝ) {P : Matrix k k ℝ} {Q : Matrix m m ℝ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : (Φ * P * Φᵀ + Q).PosSemidef :=
  (LinearAlgebra.posSemidef_congr hP Φ).add hQ

end powerlib.Estimation
