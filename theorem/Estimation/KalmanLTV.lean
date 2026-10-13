import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Matrix.Normed

/-! # Kalman covariance for time-varying systems: variation-of-constants and Riccati forms

Source: work-sync `theory/T-kalman-filter.md` §1.2 (continuous-time prediction between
measurements `Ṗ = A P + P Aᵀ + Q`; discrete analogue `P_{k|k−1} = Φ_k P Φ_kᵀ + Q_k`), §1.4
(continuous-time filter Riccati equation `Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P`, gain
`K = P Cᵀ R⁻¹`).  The time-invariant prediction with an algebraic solution `P∞` is
`theorem/Estimation/KalmanPredict.lean`.

Foundation (linear algebra / matrix ODE), not an engineering result.  Statements are about the
deterministic covariance ODEs; that `P(t)` is the conditional covariance of a continuous-time
linear-Gaussian model needs Itô/Kalman–Bucy filtering theory and is not formalized.  Matrices are
real `n × n` (`p × n` for `C`), coefficients `A(t), C(t), Q(t), R(t)` are continuous in `t ∈ ℝ`;
norms are Frobenius norms (local instances, as in `theorem/Stochastic/LyapunovCovariance.lean`).

Transition matrix.  `Φ : ℝ → ℝ → Matrix` is a fundamental matrix of `ẋ = A(t) x`, assumed via
its defining properties `∂_t Φ(t, s) = A(t) Φ(t, s)` (all `t, s`) and `Φ(s, s) = I` — exactly the
content of LeanForControl's Peano–Baker theorem for `LinearSystems.stateTransitionMatrix`
(Theorem 5.1, P5.1).  This module keeps `Φ` abstract (and imports only Mathlib); for constant `A`
the hypothesis is discharged by `Φ(t, s) = e^{(t−s)A}` (`expFund_hasDerivAt`, `expFund_self`), and
for continuous time-varying `A` by LeanForControl's state-transition matrix in
`theorem/Estimation/KalmanLTVTransition.lean`.

Main results.
* `eq_zero_of_norm_deriv_le`: Grönwall uniqueness on all of `ℝ` (both time directions), from
  Mathlib's `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`.
* `fund_cocycle`, `fund_mul_inv`, `fund_continuous_snd`: `Φ(t, s) Φ(s, τ) = Φ(t, τ)`,
  `Φ(t, s) Φ(s, t) = I`, continuity in the second argument (derived, not assumed).
* `hasDerivAt_ltvCov`, `ltvCov_self`, `ltvCov_unique` (**LTV prediction covariance**):
  `P(t) = Φ(t, t₀) P₀ Φ(t, t₀)ᵀ + ∫_{t₀}^t Φ(t, τ) Q(τ) Φ(t, τ)ᵀ dτ` (`ltvCov`) solves
  `Ṗ = A(t) P + P A(t)ᵀ + Q(t)`, `P(t₀) = P₀`, and is its only differentiable solution.
* `lti_cov_integral_form`: constant `A`, continuous `Q(t)`, no Hurwitz assumption:
  `P(t) = e^{(t−t₀)A} P₀ e^{(t−t₀)A}ᵀ + ∫_{t₀}^t e^{(t−τ)A} Q(τ) e^{(t−τ)A}ᵀ dτ`.
* `ltvCov_posSemidef`: `P₀ ⪰ 0`, `Q ⪰ 0`, `t ≥ t₀` ⇒ `P(t) ⪰ 0`.
* `riccati_joseph_form` (**integral representation of the Riccati solution**): a symmetric
  solution of `Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P` equals
  `Φ_K(t, t₀) P(t₀) Φ_K(t, t₀)ᵀ + ∫_{t₀}^t Φ_K(t, τ) (Q + K R Kᵀ)(τ) Φ_K(t, τ)ᵀ dτ`, where
  `K = P Cᵀ R⁻¹` and `Φ_K` is a fundamental matrix of the closed-loop matrix `A − K C`
  (an implicit representation: `Φ_K` depends on `P`).
* `riccati_symm`: symmetric `P(t₀)`, `Q`, `R` ⇒ the Riccati solution stays symmetric.
* `riccati_posSemidef`: `P(t₀) ⪰ 0`, `Q ⪰ 0`, `R ≻ 0` ⇒ `P(t) ⪰ 0` for `t ≥ t₀`.

Not proved: existence of Riccati solutions on a given interval (global existence for `R ≻ 0`,
`Q ⪰ 0`).
-/

noncomputable section
namespace powerlib.Estimation.LTV

open Matrix Filter Set
open scoped Matrix.Norms.Frobenius Topology

variable {n : ℕ}

noncomputable local instance frobeniusENormedAddMonoidLTV :
    ENormedAddMonoid (Matrix (Fin n) (Fin n) ℝ) :=
  (NormedAddCommGroup.toENormedAddCommMonoid :
    ENormedAddCommMonoid (Matrix (Fin n) (Fin n) ℝ)).toENormedAddMonoid

/-! ## Grönwall uniqueness on the whole line -/

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forward half: on `[s, t]`. -/
private lemma eq_zero_forward {f f' : ℝ → E} {c : ℝ → ℝ} (hc : Continuous c)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, ‖f' t‖ ≤ c t * ‖f t‖) {s : ℝ} (hs : f s = 0)
    {t : ℝ} (hst : s ≤ t) : f t = 0 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := t)).exists_bound_of_continuousOn hc.continuousOn
  refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := C)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).hasDerivWithinAt) hs (fun x hx => ?_) t ⟨hst, le_rfl⟩
  have hx' : x ∈ Icc s t := Ico_subset_Icc_self hx
  have := hC x hx'
  rw [Real.norm_eq_abs] at this
  calc ‖f' x‖ ≤ c x * ‖f x‖ := hb x
    _ ≤ C * ‖f x‖ := mul_le_mul_of_nonneg_right ((le_abs_self _).trans this) (norm_nonneg _)

/-- **Grönwall uniqueness.**  If `‖f'(t)‖ ≤ c(t) ‖f(t)‖` with `c` continuous and `f(s) = 0`, then
`f ≡ 0` on all of `ℝ` (both time directions). -/
@[powerlib_foundation] theorem eq_zero_of_norm_deriv_le {f f' : ℝ → E} {c : ℝ → ℝ}
    (hc : Continuous c) (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, ‖f' t‖ ≤ c t * ‖f t‖)
    {s : ℝ} (hs : f s = 0) (t : ℝ) : f t = 0 := by
  rcases le_total s t with hst | hts
  · exact eq_zero_forward hc hf hb hs hst
  · -- reflect time
    have hg : ∀ u, HasDerivAt (fun u => f (-u)) (-f' (-u)) u := by
      intro u
      have := (hf (-u)).scomp u (hasDerivAt_neg u)
      simpa [Function.comp_def] using this
    have := eq_zero_forward (f := fun u => f (-u)) (c := fun u => c (-u))
      (hc.comp continuous_neg) hg (fun u => by simpa using hb (-u)) (s := -s) (by simpa using hs)
      (t := -t) (neg_le_neg hts)
    simpa using this

end Uniqueness

/-! ## Fundamental matrices of `ẋ = A(t) x` -/

section Fundamental

variable {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}

/-- **Cocycle (semigroup) property** of a fundamental matrix: if `∂_t Φ(t, s) = A(t) Φ(t, s)` and
`Φ(s, s) = I` with `A` continuous, then `Φ(t, s) Φ(s, τ) = Φ(t, τ)` for all `t, s, τ`. -/
@[powerlib_foundation] theorem fund_cocycle (hA : Continuous A)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t) (hΦ0 : ∀ s, Φ s s = 1)
    (t s τ : ℝ) : Φ t s * Φ s τ = Φ t τ := by
  have h := eq_zero_of_norm_deriv_le (f := fun z => Φ z s * Φ s τ - Φ z τ)
    (f' := fun z => A z * (Φ z s * Φ s τ - Φ z τ)) (c := fun z => ‖A z‖)
    (continuous_norm.comp hA) (fun z => ?_) (fun z => norm_mul_le _ _) (s := s)
    (by simp [hΦ0]) t
  · exact sub_eq_zero.mp h
  · have := ((hΦ z s).mul_const (Φ s τ)).sub (hΦ z τ)
    convert! this using 1
    rw [Matrix.mul_sub, Matrix.mul_assoc]

/-- `Φ(t, s) Φ(s, t) = I`: every fundamental matrix is invertible. -/
@[powerlib_foundation] theorem fund_mul_inv (hA : Continuous A)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t) (hΦ0 : ∀ s, Φ s s = 1)
    (t s : ℝ) : Φ t s * Φ s t = 1 := by
  rw [fund_cocycle hA hΦ hΦ0, hΦ0]

/-- Continuity in the second argument: `τ ↦ Φ(t, τ) = Φ(τ, t)⁻¹`. -/
@[powerlib_foundation] theorem fund_continuous_snd (hA : Continuous A)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t) (hΦ0 : ∀ s, Φ s s = 1)
    (t : ℝ) : Continuous fun τ => Φ t τ := by
  have heq : (fun τ => Φ t τ) = fun τ => (Φ τ t)⁻¹ := by
    funext τ
    exact (Matrix.inv_eq_left_inv (fund_mul_inv hA hΦ hΦ0 t τ)).symm
  rw [heq, continuous_iff_continuousAt]
  intro τ
  have hdet : (Φ τ t).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (fund_mul_inv hA hΦ hΦ0 τ t)
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have hinv : ContinuousAt Ring.inverse (Φ τ t).det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet
  exact ContinuousAt.comp (f := fun z => Φ z t) (continuousAt_matrix_inv _ hinv)
    (hΦ τ t).continuousAt

end Fundamental

/-! ## Prediction covariance `Ṗ = A(t) P + P A(t)ᵀ + Q(t)` -/

section Covariance

variable {A Q : ℝ → Matrix (Fin n) (Fin n) ℝ} {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}

/-- Variation-of-constants covariance
`P(t) = Φ(t, t₀) P₀ Φ(t, t₀)ᵀ + ∫_{t₀}^t Φ(t, τ) Q(τ) Φ(t, τ)ᵀ dτ`. -/
def ltvCov (Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ) (Q : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (P₀ : Matrix (Fin n) (Fin n) ℝ) (t₀ t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Φ t t₀ * P₀ * (Φ t t₀)ᵀ + ∫ τ in t₀..t, Φ t τ * Q τ * (Φ t τ)ᵀ

/-- Congruence `M ↦ C M Cᵀ` as a continuous linear map. -/
private def congrCLM (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => C * M * Cᵀ
      map_add' := fun M N => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c M => by simp }

private lemma congrCLM_apply (C M : Matrix (Fin n) (Fin n) ℝ) : congrCLM C M = C * M * Cᵀ := rfl

/-- Transposition as a continuous linear map. -/
private def transposeCLM : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := transpose
      map_add' := transpose_add
      map_smul' := fun c M => transpose_smul c M }

/-- Factorization through the base point:
`P(z) = Φ(z, t₀) [P₀ + ∫_{t₀}^z Φ(t₀, τ) Q(τ) Φ(t₀, τ)ᵀ dτ] Φ(z, t₀)ᵀ`. -/
private lemma ltvCov_eq (hA : Continuous A) (hQ : Continuous Q)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t) (hΦ0 : ∀ s, Φ s s = 1)
    (P₀ : Matrix (Fin n) (Fin n) ℝ) (t₀ z : ℝ) :
    ltvCov Φ Q P₀ t₀ z = Φ z t₀ * (P₀ + ∫ τ in t₀..z, Φ t₀ τ * Q τ * (Φ t₀ τ)ᵀ) * (Φ z t₀)ᵀ := by
  have hc : Continuous fun τ => Φ t₀ τ * Q τ * (Φ t₀ τ)ᵀ :=
    ((fund_continuous_snd hA hΦ hΦ0 t₀).mul hQ).mul
      (fund_continuous_snd hA hΦ hΦ0 t₀).matrix_transpose
  have hcomm := (congrCLM (Φ z t₀)).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := MeasureTheory.volume) t₀ z)
  rw [Matrix.mul_add, Matrix.add_mul, ltvCov]
  congr 1
  have hpt : ∫ τ in t₀..z, Φ z τ * Q τ * (Φ z τ)ᵀ =
      ∫ τ in t₀..z, congrCLM (Φ z t₀) (Φ t₀ τ * Q τ * (Φ t₀ τ)ᵀ) := by
    refine intervalIntegral.integral_congr fun τ _ => ?_
    simp only [congrCLM_apply]
    rw [← fund_cocycle hA hΦ hΦ0 z t₀ τ, transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [hpt]
  exact hcomm

/-- `P(t₀) = P₀`. -/
@[powerlib_foundation] theorem ltvCov_self (Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hΦ0 : ∀ s, Φ s s = 1) (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (P₀ : Matrix (Fin n) (Fin n) ℝ)
    (t₀ : ℝ) : ltvCov Φ Q P₀ t₀ t₀ = P₀ := by
  simp [ltvCov, hΦ0]

/-- **LTV prediction covariance, existence.**  For continuous `A(t)`, `Q(t)` and a fundamental
matrix `Φ` of `ẋ = A(t) x` (`∂_t Φ(t, s) = A(t) Φ(t, s)`, `Φ(s, s) = I`), the variation-of-constants
matrix `P(t) = Φ(t, t₀) P₀ Φ(t, t₀)ᵀ + ∫_{t₀}^t Φ(t, τ) Q(τ) Φ(t, τ)ᵀ dτ` solves
`Ṗ = A(t) P + P A(t)ᵀ + Q(t)` at every `t`. -/
@[powerlib_foundation] theorem hasDerivAt_ltvCov (hA : Continuous A) (hQ : Continuous Q)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t) (hΦ0 : ∀ s, Φ s s = 1)
    (P₀ : Matrix (Fin n) (Fin n) ℝ) (t₀ t : ℝ) :
    HasDerivAt (ltvCov Φ Q P₀ t₀)
      (A t * ltvCov Φ Q P₀ t₀ t + ltvCov Φ Q P₀ t₀ t * (A t)ᵀ + Q t) t := by
  have hc : Continuous fun τ => Φ t₀ τ * Q τ * (Φ t₀ τ)ᵀ :=
    ((fund_continuous_snd hA hΦ hΦ0 t₀).mul hQ).mul
      (fund_continuous_snd hA hΦ hΦ0 t₀).matrix_transpose
  have hW : HasDerivAt (fun z => P₀ + ∫ τ in t₀..z, Φ t₀ τ * Q τ * (Φ t₀ τ)ᵀ)
      (Φ t₀ t * Q t * (Φ t₀ t)ᵀ) t :=
    ((hc.integral_hasStrictDerivAt t₀ t).hasDerivAt).const_add P₀
  have hT : HasDerivAt (fun z => (Φ z t₀)ᵀ) ((A t * Φ t t₀)ᵀ) t :=
    transposeCLM.hasFDerivAt.comp_hasDerivAt t (hΦ t t₀)
  have h := ((hΦ t t₀).mul hW).mul hT
  have hfun : ltvCov Φ Q P₀ t₀ = fun z =>
      Φ z t₀ * (P₀ + ∫ τ in t₀..z, Φ t₀ τ * Q τ * (Φ t₀ τ)ᵀ) * (Φ z t₀)ᵀ :=
    funext (ltvCov_eq hA hQ hΦ hΦ0 P₀ t₀)
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  set W := P₀ + ∫ τ in t₀..t, Φ t₀ τ * Q τ * (Φ t₀ τ)ᵀ
  have hinv := fund_mul_inv hA hΦ hΦ0 t t₀
  have hQt : Φ t t₀ * (Φ t₀ t * Q t * (Φ t₀ t)ᵀ) * (Φ t t₀)ᵀ = Q t := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul, Matrix.mul_assoc,
      ← transpose_mul, hinv, transpose_one, Matrix.mul_one]
  rw [Matrix.add_mul, hQt, transpose_mul]
  simp only [Matrix.mul_assoc]
  abel

/-- **LTV prediction covariance, uniqueness.**  Every differentiable solution of
`Ṗ = A(t) P + P A(t)ᵀ + Q(t)` with `P(t₀) = P₀` is the variation-of-constants matrix. -/
@[powerlib_foundation] theorem ltvCov_unique (hA : Continuous A) (hQ : Continuous Q)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t) (hΦ0 : ∀ s, Φ s s = 1)
    {P₀ : Matrix (Fin n) (Fin n) ℝ} {t₀ : ℝ} {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P (A t * P t + P t * (A t)ᵀ + Q t) t) (h0 : P t₀ = P₀) :
    P = ltvCov Φ Q P₀ t₀ := by
  funext t
  have h := eq_zero_of_norm_deriv_le (f := fun z => P z - ltvCov Φ Q P₀ t₀ z)
    (f' := fun z => A z * (P z - ltvCov Φ Q P₀ t₀ z) + (P z - ltvCov Φ Q P₀ t₀ z) * (A z)ᵀ)
    (c := fun z => ‖A z‖ + ‖(A z)ᵀ‖)
    ((continuous_norm.comp hA).add (continuous_norm.comp hA.matrix_transpose))
    (fun z => ?_) (fun z => ?_) (s := t₀) (by simp [h0, ltvCov_self Φ hΦ0]) t
  · exact sub_eq_zero.mp h
  · have := (hP z).sub (hasDerivAt_ltvCov hA hQ hΦ hΦ0 P₀ t₀ z)
    convert! this using 1
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  · calc ‖A z * (P z - ltvCov Φ Q P₀ t₀ z) + (P z - ltvCov Φ Q P₀ t₀ z) * (A z)ᵀ‖
        ≤ ‖A z * (P z - ltvCov Φ Q P₀ t₀ z)‖ + ‖(P z - ltvCov Φ Q P₀ t₀ z) * (A z)ᵀ‖ :=
          norm_add_le _ _
      _ ≤ ‖A z‖ * ‖P z - ltvCov Φ Q P₀ t₀ z‖ + ‖P z - ltvCov Φ Q P₀ t₀ z‖ * ‖(A z)ᵀ‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = (‖A z‖ + ‖(A z)ᵀ‖) * ‖P z - ltvCov Φ Q P₀ t₀ z‖ := by ring

end Covariance

/-! ## Constant `A`: the integral form without an algebraic solution -/

section Constant

/-- `Φ(t, s) = e^{(t−s)A}` is the fundamental matrix of `ẋ = A x`. -/
@[powerlib_foundation] theorem expFund_hasDerivAt (A : Matrix (Fin n) (Fin n) ℝ) (t s : ℝ) :
    HasDerivAt (fun z => NormedSpace.exp ((z - s) • A)) (A * NormedSpace.exp ((t - s) • A)) t :=
  (hasDerivAt_exp_smul_const' A (t - s)).comp_sub_const t s

@[powerlib_foundation] theorem expFund_self (A : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    NormedSpace.exp ((s - s) • A) = 1 := by
  simp [NormedSpace.exp_zero]

/-- **Prediction covariance, constant `A`, integral form.**  For constant `A` and continuous
`Q(t)` (no Hurwitz assumption and no algebraic solution `P∞` needed),
`P(t) = e^{(t−t₀)A} P₀ e^{(t−t₀)A}ᵀ + ∫_{t₀}^t e^{(t−τ)A} Q(τ) e^{(t−τ)A}ᵀ dτ` is the unique
solution of `Ṗ = A P + P Aᵀ + Q(t)`, `P(t₀) = P₀`. -/
@[powerlib_foundation] theorem lti_cov_integral_form (A : Matrix (Fin n) (Fin n) ℝ)
    {Q : ℝ → Matrix (Fin n) (Fin n) ℝ} (hQ : Continuous Q) (P₀ : Matrix (Fin n) (Fin n) ℝ)
    (t₀ : ℝ) :
    ltvCov (fun t s => NormedSpace.exp ((t - s) • A)) Q P₀ t₀ t₀ = P₀ ∧
      (∀ t, HasDerivAt (ltvCov (fun t s => NormedSpace.exp ((t - s) • A)) Q P₀ t₀)
        (A * ltvCov (fun t s => NormedSpace.exp ((t - s) • A)) Q P₀ t₀ t +
          ltvCov (fun t s => NormedSpace.exp ((t - s) • A)) Q P₀ t₀ t * Aᵀ + Q t) t) ∧
      ∀ P : ℝ → Matrix (Fin n) (Fin n) ℝ, (∀ t, HasDerivAt P (A * P t + P t * Aᵀ + Q t) t) →
        P t₀ = P₀ → P = ltvCov (fun t s => NormedSpace.exp ((t - s) • A)) Q P₀ t₀ :=
  ⟨ltvCov_self _ (expFund_self A) Q P₀ t₀,
    fun t => hasDerivAt_ltvCov (A := fun _ => A) continuous_const hQ (expFund_hasDerivAt A)
      (expFund_self A) P₀ t₀ t,
    fun _ hP h0 => ltvCov_unique (A := fun _ => A) continuous_const hQ (expFund_hasDerivAt A)
      (expFund_self A) hP h0⟩

end Constant

/-! ## Positivity and the Riccati equation -/

section Riccati

variable {A Q : ℝ → Matrix (Fin n) (Fin n) ℝ} {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}

/-- **The prediction covariance stays positive semidefinite**: for `t ≥ t₀`, `P₀ ⪰ 0` and
`Q(τ) ⪰ 0` give `P(t) ⪰ 0`. -/
@[powerlib_foundation] theorem ltvCov_posSemidef (hA : Continuous A) (hQ : Continuous Q)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t) (hΦ0 : ∀ s, Φ s s = 1)
    {P₀ : Matrix (Fin n) (Fin n) ℝ} (hP₀ : P₀.PosSemidef) (hQp : ∀ τ, (Q τ).PosSemidef)
    {t₀ t : ℝ} (ht : t₀ ≤ t) : (ltvCov Φ Q P₀ t₀ t).PosSemidef := by
  have hc : Continuous fun τ => Φ t τ * Q τ * (Φ t τ)ᵀ :=
    ((fund_continuous_snd hA hΦ hΦ0 t).mul hQ).mul
      (fund_continuous_snd hA hΦ hΦ0 t).matrix_transpose
  have hint := hc.intervalIntegrable (μ := MeasureTheory.volume) t₀ t
  have hpsd : ∀ τ, (Φ t τ * Q τ * (Φ t τ)ᵀ).PosSemidef := fun τ => by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (hQp τ).mul_mul_conjTranspose_same (Φ t τ)
  have h0 : (Φ t t₀ * P₀ * (Φ t t₀)ᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hP₀.mul_mul_conjTranspose_same (Φ t t₀)
  refine h0.add ?_
  -- the integral of positive semidefinite matrices is positive semidefinite
  have hsymm : (∫ τ in t₀..t, Φ t τ * Q τ * (Φ t τ)ᵀ)ᵀ = ∫ τ in t₀..t, Φ t τ * Q τ * (Φ t τ)ᵀ := by
    have := transposeCLM.intervalIntegral_comp_comm hint
    refine this.symm.trans (intervalIntegral.integral_congr fun τ _ => ?_)
    show (Φ t τ * Q τ * (Φ t τ)ᵀ)ᵀ = _
    have := (hpsd τ).isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hsymm]
  · let Lx : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      { toFun := fun M => x ⬝ᵥ (M *ᵥ x)
        map_add' := fun M N => by simp [add_mulVec, dotProduct_add]
        map_smul' := fun c M => by simp [smul_mulVec, dotProduct_smul] }
    have hcomm := Lx.intervalIntegral_comp_comm hint
    simp only [star_trivial]
    change 0 ≤ Lx (∫ τ in t₀..t, Φ t τ * Q τ * (Φ t τ)ᵀ)
    have hcomm' : Lx (∫ τ in t₀..t, Φ t τ * Q τ * (Φ t τ)ᵀ) =
        ∫ τ in t₀..t, Lx (Φ t τ * Q τ * (Φ t τ)ᵀ) := hcomm.symm
    rw [hcomm']
    refine intervalIntegral.integral_nonneg ht fun τ _ => ?_
    have := (hpsd τ).dotProduct_mulVec_nonneg x
    simp only [star_trivial] at this
    exact this

variable {p : ℕ} {C : ℝ → Matrix (Fin p) (Fin n) ℝ} {R : ℝ → Matrix (Fin p) (Fin p) ℝ}

/-- **Riccati solution in closed-loop (Joseph) integral form.**  Let `P` be a symmetric solution of
the filter Riccati equation `Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P` with continuous `A, C, Q`,
continuous symmetric invertible `R`, and let `K = P Cᵀ R⁻¹`.  If `Φ_K` is a fundamental matrix of
the closed-loop matrix `A − K C`, then
`P(t) = Φ_K(t, t₀) P(t₀) Φ_K(t, t₀)ᵀ + ∫_{t₀}^t Φ_K(t, τ) (Q + K R Kᵀ)(τ) Φ_K(t, τ)ᵀ dτ`. -/
@[powerlib_foundation] theorem riccati_joseph_form (hA : Continuous A) (hC : Continuous C)
    (hQ : Continuous Q) (hR : Continuous R) (hRs : ∀ t, (R t)ᵀ = R t)
    (hRu : ∀ t, IsUnit (R t).det) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P
      (A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t) t)
    (hPs : ∀ t, (P t)ᵀ = P t)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s)
      ((A t - P t * (C t)ᵀ * (R t)⁻¹ * C t) * Φ t s) t) (hΦ0 : ∀ s, Φ s s = 1) (t₀ : ℝ) :
    P = ltvCov Φ (fun t => Q t + (P t * (C t)ᵀ * (R t)⁻¹) * R t * (P t * (C t)ᵀ * (R t)⁻¹)ᵀ)
      (P t₀) t₀ := by
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hRi : Continuous fun t => (R t)⁻¹ := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hinv : ContinuousAt Ring.inverse (R t).det := by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (hRu t).ne_zero
    exact ContinuousAt.comp (f := R) (continuousAt_matrix_inv _ hinv) hR.continuousAt
  have hPC : Continuous fun t => P t * (C t)ᵀ := hPc.matrix_mul hC.matrix_transpose
  have hK : Continuous fun t => P t * (C t)ᵀ * (R t)⁻¹ := hPC.matrix_mul hRi
  have hKC : Continuous fun t => P t * (C t)ᵀ * (R t)⁻¹ * C t := hK.matrix_mul hC
  have hAK : Continuous fun t => A t - P t * (C t)ᵀ * (R t)⁻¹ * C t := hA.sub hKC
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
@[powerlib_foundation] theorem riccati_symm (hA : Continuous A) (hC : Continuous C)
    (hR : Continuous R) (hRs : ∀ t, (R t)ᵀ = R t) (hRu : ∀ t, IsUnit (R t).det)
    (hQs : ∀ t, (Q t)ᵀ = Q t) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P
      (A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t) t)
    {t₀ : ℝ} (h0 : (P t₀)ᵀ = P t₀) (t : ℝ) : (P t)ᵀ = P t := by
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hRi : Continuous fun t => (R t)⁻¹ := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hinv : ContinuousAt Ring.inverse (R t).det := by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (hRu t).ne_zero
    exact ContinuousAt.comp (f := R) (continuousAt_matrix_inv _ hinv) hR.continuousAt
  set M : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => (C t)ᵀ * (R t)⁻¹ * C t with hM
  have hMc : Continuous M := (hC.matrix_transpose.matrix_mul hRi).matrix_mul hC
  have hMs : ∀ t, (M t)ᵀ = M t := fun t => by
    simp only [hM, transpose_mul, transpose_transpose, transpose_nonsing_inv, hRs,
      Matrix.mul_assoc]
  have hT : ∀ t, HasDerivAt (fun z => (P z)ᵀ)
      ((A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t)ᵀ) t := fun t =>
    transposeCLM.hasFDerivAt.comp_hasDerivAt t (hP t)
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
@[powerlib_foundation] theorem riccati_posSemidef (hA : Continuous A) (hC : Continuous C)
    (hQ : Continuous Q) (hR : Continuous R) (hQp : ∀ t, (Q t).PosSemidef)
    (hRp : ∀ t, (R t).PosDef) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P
      (A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t) t)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s)
      ((A t - P t * (C t)ᵀ * (R t)⁻¹ * C t) * Φ t s) t) (hΦ0 : ∀ s, Φ s s = 1)
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
  have hRi : Continuous fun t => (R t)⁻¹ := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hinv : ContinuousAt Ring.inverse (R t).det := by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (hRu t).ne_zero
    exact ContinuousAt.comp (f := R) (continuousAt_matrix_inv _ hinv) hR.continuousAt
  have hK : Continuous fun t => P t * (C t)ᵀ * (R t)⁻¹ :=
    (hPc.matrix_mul hC.matrix_transpose).matrix_mul hRi
  have hAK : Continuous fun t => A t - P t * (C t)ᵀ * (R t)⁻¹ * C t := hA.sub (hK.matrix_mul hC)
  have hQK : Continuous fun t =>
      Q t + (P t * (C t)ᵀ * (R t)⁻¹) * R t * (P t * (C t)ᵀ * (R t)⁻¹)ᵀ :=
    hQ.add ((hK.matrix_mul hR).matrix_mul hK.matrix_transpose)
  rw [hrep]
  refine ltvCov_posSemidef hAK hQK hΦ hΦ0 hP₀ (fun τ => ?_) ht
  refine (hQp τ).add ?_
  simpa [conjTranspose_eq_transpose_of_trivial] using
    (hRp τ).posSemidef.mul_mul_conjTranspose_same (P τ * (C τ)ᵀ * (R τ)⁻¹)

end Riccati

end powerlib.Estimation.LTV
