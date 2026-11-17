import dependencies.Mathlib
import theorem.Attributes
import theorem.LinearAlgebra.LyapunovODE

/-! # Kalman–Bucy filter Riccati equation: closed-loop integral form, symmetry, positivity

The closed-loop (Joseph) integral representation, symmetry and positivity of the filter Riccati
solution, relative to an abstract fundamental matrix of the closed-loop matrix.

Scope.
* Linear algebra / matrix ODE, not an engineering result. Statements are about the
  deterministic covariance ODEs; that `P(t)` is the conditional covariance of a continuous-time
  linear-Gaussian model needs Itô/Kalman–Bucy filtering theory and is not formalized.
* Matrices are real `n × n` (`p × n` for `C`), coefficients `A(t), C(t), Q(t), R(t)` are
  continuous in `t ∈ ℝ`; norms are Frobenius norms (with
  `LinearAlgebra.frobeniusENormedAddMonoid` enabled locally,
  `theorem/LinearAlgebra/Frobenius.lean`).
* The prediction covariance `Ṗ = A(t) P + P A(t)ᵀ + Q(t)` (variation of constants `ltvCov`, its
  uniqueness and positivity, relative to a fundamental matrix `Φ` of `ẋ = A(t) x`; the
  constant-`A` case with `expFund_hasDerivAt`, `expFund_self`) is
  `theorem/LinearAlgebra/LyapunovODE.lean`. The fundamental matrix stays abstract here (this
  module imports no LeanForControl); for continuous `A(t)` it is
  LeanForControl's state-transition matrix in `theorem/Estimation/KalmanLTVTransition.lean`.
* The time-invariant prediction with an algebraic solution `P∞` is
  `theorem/Stochastic/LyapunovCovariance.lean` (`Lyapunov.covSol`, `Lyapunov.covSol_eq_ltvCov`).

Source: work-sync theory/T-kalman-filter.md §1.2 (continuous-time prediction between
measurements `Ṗ = A P + P Aᵀ + Q`), §1.4 (continuous-time filter Riccati equation
`Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P`, gain `K = P Cᵀ R⁻¹`).

Results.
* `closedLoop_continuous` — continuity of the closed-loop matrix `A − P Cᵀ R⁻¹ C`.
* `riccati_joseph_form` — **integral representation of the Riccati solution**: a symmetric
  solution of `Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P` equals
  `Φ_K(t, t₀) P(t₀) Φ_K(t, t₀)ᵀ + ∫_{t₀}^t Φ_K(t, τ) (Q + K R Kᵀ)(τ) Φ_K(t, τ)ᵀ dτ`, where
  `K = P Cᵀ R⁻¹` and `Φ_K` is a fundamental matrix of the closed-loop matrix `A − K C`
  (an implicit representation: `Φ_K` depends on `P`).
* `riccati_symm` — symmetric `P(t₀)`, `Q`, `R` ⇒ the Riccati solution stays symmetric.
* `riccati_posSemidef` — `P(t₀) ⪰ 0`, `Q ⪰ 0`, `R ≻ 0` ⇒ `P(t) ⪰ 0` for `t ≥ t₀`.

Not formalized.
* Existence of Riccati solutions on a given interval (global existence for `R ≻ 0`, `Q ⪰ 0`).
-/

noncomputable section
namespace powerlib.Estimation.LTV

open Matrix Filter Set powerlib.LinearAlgebra
open scoped Matrix.Norms.Frobenius Topology

variable {n : ℕ}

attribute [local instance] powerlib.LinearAlgebra.frobeniusENormedAddMonoid

/-! ## Positivity and the Riccati equation -/

section Riccati

variable {A Q : ℝ → Matrix (Fin n) (Fin n) ℝ} {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}
variable {p : ℕ} {C : ℝ → Matrix (Fin p) (Fin n) ℝ} {R : ℝ → Matrix (Fin p) (Fin p) ℝ}

/-- Continuity of `t ↦ R(t)⁻¹` for continuous, pointwise invertible `R`. -/
@[tmio T, powerlib_foundation] private lemma inv_continuous (hR : Continuous R)
    (hRu : ∀ t, IsUnit (R t).det) : Continuous fun t => (R t)⁻¹ := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hinv : ContinuousAt Ring.inverse (R t).det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (hRu t).ne_zero
  exact ContinuousAt.comp (f := R) (continuousAt_matrix_inv _ hinv) hR.continuousAt

/-- Continuity of the closed-loop matrix `A − P Cᵀ R⁻¹ C`. -/
@[tmio T, powerlib_foundation] theorem closedLoop_continuous (hA : Continuous A)
    (hC : Continuous C) (hR : Continuous R) (hRu : ∀ t, IsUnit (R t).det)
    {P : ℝ → Matrix (Fin n) (Fin n) ℝ} (hPc : Continuous P) :
    Continuous fun t => A t - P t * (C t)ᵀ * (R t)⁻¹ * C t :=
  hA.sub (((hPc.matrix_mul hC.matrix_transpose).matrix_mul (inv_continuous hR hRu)).matrix_mul hC)

/-- **Riccati solution in closed-loop (Joseph) integral form.**  Let `P` be a symmetric solution of
the filter Riccati equation `Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P` with continuous `A, C, Q`,
continuous symmetric invertible `R`, and let `K = P Cᵀ R⁻¹`.  If `Φ_K` is a fundamental matrix of
the closed-loop matrix `A − K C`, then
`P(t) = Φ_K(t, t₀) P(t₀) Φ_K(t, t₀)ᵀ + ∫_{t₀}^t Φ_K(t, τ) (Q + K R Kᵀ)(τ) Φ_K(t, τ)ᵀ dτ`. -/
@[tmio T, powerlib_foundation] theorem riccati_joseph_form (hA : Continuous A) (hC : Continuous C)
    (hQ : Continuous Q) (hR : Continuous R) (hRs : ∀ t, (R t)ᵀ = R t)
    (hRu : ∀ t, IsUnit (R t).det) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P
      (A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t) t)
    (hPs : ∀ t, (P t)ᵀ = P t)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) ((A t - P t * (C t)ᵀ * (R t)⁻¹ * C t) * Φ t s) t)
    (hΦ0 : ∀ s, Φ s s = 1) (t₀ : ℝ) :
    P = ltvCov Φ (fun t => Q t + (P t * (C t)ᵀ * (R t)⁻¹) * R t * (P t * (C t)ᵀ * (R t)⁻¹)ᵀ)
      (P t₀) t₀ := by
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hRi := inv_continuous hR hRu
  have hK : Continuous fun t => P t * (C t)ᵀ * (R t)⁻¹ :=
    (hPc.matrix_mul hC.matrix_transpose).matrix_mul hRi
  have hAK := closedLoop_continuous hA hC hR hRu hPc
  have hQK : Continuous fun t =>
      Q t + (P t * (C t)ᵀ * (R t)⁻¹) * R t * (P t * (C t)ᵀ * (R t)⁻¹)ᵀ :=
    hQ.add ((hK.matrix_mul hR).matrix_mul hK.matrix_transpose)
  refine ltvCov_unique hAK hQK hΦ hΦ0 (fun t => ?_) rfl
  convert! hP t using 1
  have hRit : ((R t)⁻¹)ᵀ = (R t)⁻¹ := by rw [transpose_nonsing_inv, hRs]
  have hRR : (R t)⁻¹ * R t = 1 := nonsing_inv_mul _ (hRu t)
  simp only [transpose_mul, hRit, hPs, transpose_sub, transpose_transpose]
  have e : P t * (C t)ᵀ * (R t)⁻¹ * R t * ((R t)⁻¹ * C t * P t) =
      P t * (C t)ᵀ * (R t)⁻¹ * C t * P t := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (R t) ((R t)⁻¹), mul_nonsing_inv _ (hRu t), Matrix.one_mul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc] at e ⊢
  rw [e]
  abel

/-- **Symmetry of Riccati solutions.**  If `Q(t)` and `R(t)` are symmetric and `P(t₀)` is
symmetric, every solution of `Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P` stays symmetric
(`D = P − Pᵀ` solves a linear equation with continuous coefficients and `D(t₀) = 0`). -/
@[tmio T, powerlib_foundation] theorem riccati_symm (hA : Continuous A) (hC : Continuous C)
    (hR : Continuous R) (hRs : ∀ t, (R t)ᵀ = R t) (hRu : ∀ t, IsUnit (R t).det)
    (hQs : ∀ t, (Q t)ᵀ = Q t) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P
      (A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t) t)
    {t₀ : ℝ} (h0 : (P t₀)ᵀ = P t₀) (t : ℝ) : (P t)ᵀ = P t := by
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hRi := inv_continuous hR hRu
  set M : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => (C t)ᵀ * (R t)⁻¹ * C t with hM
  have hMc : Continuous M := (hC.matrix_transpose.matrix_mul hRi).matrix_mul hC
  have hMs : ∀ t, (M t)ᵀ = M t := fun t => by
    simp only [hM, transpose_mul, transpose_transpose, transpose_nonsing_inv, hRs,
      Matrix.mul_assoc]
  have hT : ∀ t, HasDerivAt (fun z => (P z)ᵀ)
      ((A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t)ᵀ) t := fun t =>
    hasDerivAt_transpose (hP t)
  have h := eq_zero_of_norm_deriv_le (f := fun z => P z - (P z)ᵀ)
    (f' := fun z => A z * (P z - (P z)ᵀ) + (P z - (P z)ᵀ) * (A z)ᵀ -
      ((P z - (P z)ᵀ) * M z * P z + (P z)ᵀ * M z * (P z - (P z)ᵀ)))
    (c := fun z => ‖A z‖ + ‖(A z)ᵀ‖ + (‖M z‖ * ‖P z‖ + ‖(P z)ᵀ‖ * ‖M z‖))
    (((continuous_norm.comp hA).add (continuous_norm.comp hA.matrix_transpose)).add
      (((continuous_norm.comp hMc).mul (continuous_norm.comp hPc)).add
        ((continuous_norm.comp hPc.matrix_transpose).mul (continuous_norm.comp hMc))))
    (fun z => ?_) (fun z => ?_) (s := t₀) (by simp [h0]) t
  · exact (sub_eq_zero.mp h).symm
  · have := (hP z).sub (hT z)
    convert! this using 1
    have e : P z * (C z)ᵀ * (R z)⁻¹ * C z * P z = P z * M z * P z := by
      simp only [hM, Matrix.mul_assoc]
    rw [e, transpose_sub, transpose_add, transpose_add, transpose_mul, transpose_mul,
      transpose_mul, transpose_mul, transpose_transpose, hQs, hMs]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  · set D := P z - (P z)ᵀ
    calc ‖A z * D + D * (A z)ᵀ - (D * M z * P z + (P z)ᵀ * M z * D)‖
        ≤ ‖A z * D + D * (A z)ᵀ‖ + ‖D * M z * P z + (P z)ᵀ * M z * D‖ := norm_sub_le _ _
      _ ≤ (‖A z‖ * ‖D‖ + ‖D‖ * ‖(A z)ᵀ‖) + (‖D‖ * ‖M z‖ * ‖P z‖ + ‖(P z)ᵀ‖ * ‖M z‖ * ‖D‖) := by
          gcongr
          · exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
          · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                (norm_nonneg _))
            · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                (norm_nonneg _))
      _ = (‖A z‖ + ‖(A z)ᵀ‖ + (‖M z‖ * ‖P z‖ + ‖(P z)ᵀ‖ * ‖M z‖)) * ‖D‖ := by ring

/-- **The Riccati covariance stays positive semidefinite.**  For the filter Riccati equation with
`Q(t) ⪰ 0`, `R(t) ≻ 0` and `P(t₀) ⪰ 0`, given a fundamental matrix of the closed-loop matrix
`A − P Cᵀ R⁻¹ C`, `P(t) ⪰ 0` for all `t ≥ t₀`. -/
@[tmio T, powerlib_foundation] theorem riccati_posSemidef (hA : Continuous A) (hC : Continuous C)
    (hQ : Continuous Q) (hR : Continuous R) (hQp : ∀ t, (Q t).PosSemidef)
    (hRp : ∀ t, (R t).PosDef) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P
      (A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t) t)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) ((A t - P t * (C t)ᵀ * (R t)⁻¹ * C t) * Φ t s) t)
    (hΦ0 : ∀ s, Φ s s = 1)
    {t₀ : ℝ} (hP₀ : (P t₀).PosSemidef) {t : ℝ} (ht : t₀ ≤ t) : (P t).PosSemidef := by
  have hRs : ∀ t, (R t)ᵀ = R t := fun t => by
    have := (hRp t).isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hRu : ∀ t, IsUnit (R t).det := fun t => (hRp t).isUnit.map Matrix.detMonoidHom
  have hQs : ∀ t, (Q t)ᵀ = Q t := fun t => by
    have := (hQp t).isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hP0s : (P t₀)ᵀ = P t₀ := by
    have := hP₀.isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hPs := riccati_symm hA hC hR hRs hRu hQs hP hP0s
  have hrep := riccati_joseph_form hA hC hQ hR hRs hRu hP hPs hΦ hΦ0 t₀
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hRi := inv_continuous hR hRu
  have hK : Continuous fun t => P t * (C t)ᵀ * (R t)⁻¹ :=
    (hPc.matrix_mul hC.matrix_transpose).matrix_mul hRi
  have hAK := closedLoop_continuous hA hC hR hRu hPc
  have hQK : Continuous fun t =>
      Q t + (P t * (C t)ᵀ * (R t)⁻¹) * R t * (P t * (C t)ᵀ * (R t)⁻¹)ᵀ :=
    hQ.add ((hK.matrix_mul hR).matrix_mul hK.matrix_transpose)
  rw [hrep]
  refine ltvCov_posSemidef hAK hQK hΦ hΦ0 hP₀ (fun τ => ?_) ht
  exact (hQp τ).add (posSemidef_congr (hRp τ).posSemidef (P τ * (C τ)ᵀ * (R τ)⁻¹))

end Riccati

end powerlib.Estimation.LTV
