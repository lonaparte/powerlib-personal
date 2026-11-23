import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Matrix.Normed
import theorem.LinearAlgebra.Frobenius
import theorem.LinearAlgebra.Congruence

/-! # Differential Lyapunov equation `Ṗ = A(t) P + P A(t)ᵀ + Q(t)`: variation of constants

Grönwall uniqueness on the whole line, the laws of a fundamental matrix of `ẋ = A(t) x`, and the
variation-of-constants solution of the differential Lyapunov equation, proved once for the
covariance modules (`Stochastic/LyapunovCovariance`, `Estimation/KalmanLTV`).

Scope.
* Generic linear algebra / matrix ODE; no model. Matrices are real `n × n`, coefficients
  `A(t), Q(t)` are continuous in `t ∈ ℝ`; norms are Frobenius norms (with
  `LinearAlgebra.frobeniusENormedAddMonoid` enabled locally,
  `theorem/LinearAlgebra/Frobenius.lean`).
* Transition matrix. `Φ : ℝ → ℝ → Matrix` is kept abstract through two hypotheses
  (`∂_t Φ(t, s) = A(t) Φ(t, s)` for all `t, s`, `Φ(s, s) = I`) — exactly the content of
  LeanForControl's Peano–Baker theorem for `LinearSystems.stateTransitionMatrix` (Theorem 5.1,
  P5.1). For constant `A` they are discharged by `Φ(t, s) = e^{(t−s)A}` (`expFund_hasDerivAt`,
  `expFund_self`), for continuous time-varying `A` by LeanForControl's state-transition matrix
  (`theorem/Dynamics/VariationOfConstants.lean`, `Dynamics.stm_hasDerivAt` with
  `stateTransitionMatrix_self`).

Source: work-sync theory/T-kalman-filter.md §1.2 (continuous-time prediction between
measurements `Ṗ = A P + P Aᵀ + Q`); work-sync theory/T-sde-systems.md §1.12.2 (differential
Lyapunov equation `Ṗ = A P + P Aᵀ + B Bᵀ`).

Results.
* `eq_zero_of_norm_deriv_le` — Grönwall uniqueness on all of `ℝ` (both time directions), from
  Mathlib's `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`.
* `hasDerivAt_transpose` — `(f')ᵀ` is the derivative of `t ↦ f(t)ᵀ`.
* `expFund_hasDerivAt`, `expFund_self` — `e^{(t−s)A}` is a fundamental matrix for constant `A`.
* `fund_cocycle`, `fund_mul_inv`, `fund_continuous_snd` — `Φ(t, s) Φ(s, τ) = Φ(t, τ)`,
  `Φ(t, s) Φ(s, t) = I`, continuity in the second argument (derived, not assumed).
* `hasDerivAt_ltvCov`, `ltvCov_self`, `ltvCov_unique` — **variation of constants**:
  `P(t) = Φ(t, t₀) P₀ Φ(t, t₀)ᵀ + ∫_{t₀}^t Φ(t, τ) Q(τ) Φ(t, τ)ᵀ dτ` (`ltvCov`) solves
  `Ṗ = A(t) P + P A(t)ᵀ + Q(t)`, `P(t₀) = P₀`, and is its only differentiable solution (with
  `expFund_*`: the constant-`A` case, no Hurwitz assumption).
* `ltvCov_posSemidef` — `P₀ ⪰ 0`, `Q ⪰ 0`, `t ≥ t₀` ⇒ `P(t) ⪰ 0`.
-/

noncomputable section
namespace powerlib.LinearAlgebra

open Matrix Filter Set
open scoped Matrix.Norms.Frobenius Topology

variable {n : ℕ}

attribute [local instance] powerlib.LinearAlgebra.frobeniusENormedAddMonoid

/-! ## Grönwall uniqueness on the whole line -/

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forward half: on `[s, t]`. -/
@[tmio T, powerlib_foundation] private lemma eq_zero_forward {f f' : ℝ → E} {c : ℝ → ℝ}
    (hc : Continuous c) (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, ‖f' t‖ ≤ c t * ‖f t‖)
    {s : ℝ} (hs : f s = 0) {t : ℝ} (hst : s ≤ t) : f t = 0 := by
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
@[tmio T, powerlib_foundation] theorem eq_zero_of_norm_deriv_le {f f' : ℝ → E} {c : ℝ → ℝ}
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

/-- Transposition as a continuous linear map. -/
private def transposeCLM : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := transpose
      map_add' := transpose_add
      map_smul' := fun c M => transpose_smul c M }

/-- Derivative of the transpose: `HasDerivAt f f' t ⇒ HasDerivAt (fun z => (f z)ᵀ) f'ᵀ t`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_transpose {f : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {f' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun z => (f z)ᵀ) f'ᵀ t :=
  transposeCLM.hasFDerivAt.comp_hasDerivAt t hf

/-! ## Fundamental matrices of `ẋ = A(t) x` -/

/-- `Φ(t, s) = e^{(t−s)A}` is a fundamental matrix of `ẋ = A x` for constant `A`:
`∂_t Φ(t, s) = A Φ(t, s)`. -/
@[tmio T, powerlib_foundation] theorem expFund_hasDerivAt (A : Matrix (Fin n) (Fin n) ℝ) (t s : ℝ) :
    HasDerivAt (fun z => NormedSpace.exp ((z - s) • A)) (A * NormedSpace.exp ((t - s) • A)) t :=
  (hasDerivAt_exp_smul_const' A (t - s)).comp_sub_const t s

/-- `Φ(s, s) = e^{0} = I` for `Φ(t, s) = e^{(t−s)A}`. -/
@[tmio T, powerlib_foundation] theorem expFund_self (A : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    NormedSpace.exp ((s - s) • A) = 1 := by
  simp [NormedSpace.exp_zero]

section Fundamental

variable {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}

/-- **Cocycle (semigroup) property** of a fundamental matrix: for continuous `A`,
`Φ(t, s) Φ(s, τ) = Φ(t, τ)` for all `t, s, τ`. -/
@[tmio T, powerlib_foundation] theorem fund_cocycle (hA : Continuous A)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t)
    (hΦ0 : ∀ s, Φ s s = 1) (t s τ : ℝ) : Φ t s * Φ s τ = Φ t τ := by
  have h := eq_zero_of_norm_deriv_le (f := fun z => Φ z s * Φ s τ - Φ z τ)
    (f' := fun z => A z * (Φ z s * Φ s τ - Φ z τ)) (c := fun z => ‖A z‖)
    (continuous_norm.comp hA) (fun z => ?_) (fun z => norm_mul_le _ _) (s := s)
    (by simp [hΦ0]) t
  · exact sub_eq_zero.mp h
  · have := ((hΦ z s).mul_const (Φ s τ)).sub (hΦ z τ)
    convert! this using 1
    rw [Matrix.mul_sub, Matrix.mul_assoc]

/-- `Φ(t, s) Φ(s, t) = I`: every fundamental matrix is invertible. -/
@[tmio T, powerlib_foundation] theorem fund_mul_inv (hA : Continuous A)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t)
    (hΦ0 : ∀ s, Φ s s = 1) (t s : ℝ) : Φ t s * Φ s t = 1 := by
  rw [fund_cocycle hA hΦ hΦ0, hΦ0]

/-- Continuity in the second argument: `τ ↦ Φ(t, τ) = Φ(τ, t)⁻¹`. -/
@[tmio T, powerlib_foundation] theorem fund_continuous_snd (hA : Continuous A)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t)
    (hΦ0 : ∀ s, Φ s s = 1) (t : ℝ) : Continuous fun τ => Φ t τ := by
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

/-! ## Variation of constants for `Ṗ = A(t) P + P A(t)ᵀ + Q(t)` -/

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

@[tmio T, powerlib_foundation] private lemma congrCLM_apply (C M : Matrix (Fin n) (Fin n) ℝ) :
    congrCLM C M = C * M * Cᵀ := rfl

/-- Continuity of the integrand `τ ↦ Φ(t, τ) Q(τ) Φ(t, τ)ᵀ`. -/
@[tmio T, powerlib_foundation] private lemma integrand_continuous (hA : Continuous A)
    (hQ : Continuous Q) (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t)
    (hΦ0 : ∀ s, Φ s s = 1) (t : ℝ) :
    Continuous fun τ => Φ t τ * Q τ * (Φ t τ)ᵀ :=
  ((fund_continuous_snd hA hΦ hΦ0 t).mul hQ).mul
    (fund_continuous_snd hA hΦ hΦ0 t).matrix_transpose

/-- Factorization through the base point:
`P(z) = Φ(z, t₀) [P₀ + ∫_{t₀}^z Φ(t₀, τ) Q(τ) Φ(t₀, τ)ᵀ dτ] Φ(z, t₀)ᵀ`. -/
@[tmio T, powerlib_foundation] private lemma ltvCov_eq (hA : Continuous A) (hQ : Continuous Q)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t)
    (hΦ0 : ∀ s, Φ s s = 1) (P₀ : Matrix (Fin n) (Fin n) ℝ) (t₀ z : ℝ) :
    ltvCov Φ Q P₀ t₀ z =
      Φ z t₀ * (P₀ + ∫ τ in t₀..z, Φ t₀ τ * Q τ * (Φ t₀ τ)ᵀ) * (Φ z t₀)ᵀ := by
  have hcomm := (congrCLM (Φ z t₀)).intervalIntegral_comp_comm
    ((integrand_continuous hA hQ hΦ hΦ0 t₀).intervalIntegrable (μ := MeasureTheory.volume) t₀ z)
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
@[tmio T, powerlib_foundation] theorem ltvCov_self (hΦ0 : ∀ s, Φ s s = 1)
    (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (P₀ : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ) :
    ltvCov Φ Q P₀ t₀ t₀ = P₀ := by
  simp [ltvCov, hΦ0]

/-- **Variation of constants, existence.**  For continuous `A(t)`, `Q(t)` and a fundamental
matrix `Φ` of `ẋ = A(t) x`, the matrix
`P(t) = Φ(t, t₀) P₀ Φ(t, t₀)ᵀ + ∫_{t₀}^t Φ(t, τ) Q(τ) Φ(t, τ)ᵀ dτ` solves
`Ṗ = A(t) P + P A(t)ᵀ + Q(t)` at every `t`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_ltvCov (hA : Continuous A) (hQ : Continuous Q)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t)
    (hΦ0 : ∀ s, Φ s s = 1) (P₀ : Matrix (Fin n) (Fin n) ℝ) (t₀ t : ℝ) :
    HasDerivAt (ltvCov Φ Q P₀ t₀)
      (A t * ltvCov Φ Q P₀ t₀ t + ltvCov Φ Q P₀ t₀ t * (A t)ᵀ + Q t) t := by
  have hW : HasDerivAt (fun z => P₀ + ∫ τ in t₀..z, Φ t₀ τ * Q τ * (Φ t₀ τ)ᵀ)
      (Φ t₀ t * Q t * (Φ t₀ t)ᵀ) t :=
    (((integrand_continuous hA hQ hΦ hΦ0 t₀).integral_hasStrictDerivAt t₀ t).hasDerivAt).const_add
      P₀
  have h := ((hΦ t t₀).mul hW).mul (hasDerivAt_transpose (hΦ t t₀))
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

/-- **Variation of constants, uniqueness.**  Every differentiable solution of
`Ṗ = A(t) P + P A(t)ᵀ + Q(t)` with `P(t₀) = P₀` is the variation-of-constants matrix. -/
@[tmio T, powerlib_foundation] theorem ltvCov_unique (hA : Continuous A) (hQ : Continuous Q)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t)
    (hΦ0 : ∀ s, Φ s s = 1) {P₀ : Matrix (Fin n) (Fin n) ℝ} {t₀ : ℝ}
    {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P (A t * P t + P t * (A t)ᵀ + Q t) t) (h0 : P t₀ = P₀) :
    P = ltvCov Φ Q P₀ t₀ := by
  funext t
  have h := eq_zero_of_norm_deriv_le (f := fun z => P z - ltvCov Φ Q P₀ t₀ z)
    (f' := fun z => A z * (P z - ltvCov Φ Q P₀ t₀ z) + (P z - ltvCov Φ Q P₀ t₀ z) * (A z)ᵀ)
    (c := fun z => ‖A z‖ + ‖(A z)ᵀ‖)
    ((continuous_norm.comp hA).add (continuous_norm.comp hA.matrix_transpose))
    (fun z => ?_) (fun z => ?_) (s := t₀) (by simp [h0, ltvCov_self hΦ0]) t
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

/-- **The variation-of-constants covariance stays positive semidefinite**: for `t ≥ t₀`,
`P₀ ⪰ 0` and `Q(τ) ⪰ 0` give `P(t) ⪰ 0`. -/
@[tmio T, powerlib_foundation] theorem ltvCov_posSemidef (hA : Continuous A) (hQ : Continuous Q)
    (hΦ : ∀ t s, HasDerivAt (fun z => Φ z s) (A t * Φ t s) t)
    (hΦ0 : ∀ s, Φ s s = 1) {P₀ : Matrix (Fin n) (Fin n) ℝ} (hP₀ : P₀.PosSemidef)
    (hQp : ∀ τ, (Q τ).PosSemidef) {t₀ t : ℝ} (ht : t₀ ≤ t) : (ltvCov Φ Q P₀ t₀ t).PosSemidef := by
  have hint := (integrand_continuous hA hQ hΦ hΦ0 t).intervalIntegrable
    (μ := MeasureTheory.volume) t₀ t
  have hpsd : ∀ τ, (Φ t τ * Q τ * (Φ t τ)ᵀ).PosSemidef := fun τ =>
    posSemidef_congr (hQp τ) (Φ t τ)
  refine (posSemidef_congr hP₀ (Φ t t₀)).add ?_
  -- the integral of positive semidefinite matrices is positive semidefinite
  have hsymm : (∫ τ in t₀..t, Φ t τ * Q τ * (Φ t τ)ᵀ)ᵀ =
      ∫ τ in t₀..t, Φ t τ * Q τ * (Φ t τ)ᵀ := by
    have := transposeCLM.intervalIntegral_comp_comm hint
    refine this.symm.trans (intervalIntegral.integral_congr fun τ _ => ?_)
    exact (hpsd τ).isHermitian.isSymm
  refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_iff_isSymm.mpr hsymm) fun x => ?_
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

end Covariance

end powerlib.LinearAlgebra
