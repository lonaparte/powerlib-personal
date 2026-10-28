import dependencies.Mathlib
import theorem.Attributes
import theorem.Estimation.KalmanGaussianVector
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.ConditionalExpectation

/-! # Kalman update = conditional mean in the scalar linear-Gaussian model

In the scalar linear-Gaussian model the Kalman update is the conditional mean and the Kalman
posterior variance is the conditional variance.

Scope.
* Probability theory, not an engineering result. Scalar state and scalar measurement:
  `X ~ N(m, p)`, `V ~ N(0, r)` independent, `Y = h X + V`, gain `k = p h / (h² p + r)`.
* This is the case `n = p = 1` of the vector model (matrix gain, Gaussian vectors) of
  `theorem/Estimation/KalmanGaussianVector.lean`, and the three conditioning results are read from
  it: `(X, Y)` is a Gaussian vector of `ℝ¹ × ℝ¹`, the scalar gain solves `K Σ_YY = Σ_XY`, and the
  σ-algebra of `Y` is that of the vector `(Y)`.

Source: work-sync theory/T-kalman-filter.md §1.1 (measurement update `K = P Hᵀ S⁻¹`,
`x̂⁺ = x̂ + K (y − H x̂)`, `P⁺ = (I − K H) P`; "for linear-Gaussian models the Kalman update is
the exact conditional mean and covariance").

Results.
* `kalman_innovation_indep` — Gaussian conditioning lemma: the estimation error
  `Z = X − m − k (Y − h m)` is independent of `Y` (jointly Gaussian and uncorrelated;
  `gaussian_error_indep`).
* `kalman_condExp_eq` — `E[X | Y] = m + k (Y − h m)` a.s.: the Kalman update is the conditional
  mean (`gaussian_condExp_eq`).
* `kalman_condVar_eq` — `E[(X − E[X|Y])² | Y] = (1 − k h) p` a.s.: the Kalman posterior
  variance is the (deterministic) conditional variance (`gaussian_condCov_eq`).
* `kalman_error_moments` — the error has mean `0` and second moment `(1 − k h) p`; `cov_lin_indep`
  computes covariances of linear combinations of independent variables.
-/

noncomputable section
namespace powerlib.Estimation

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Scalar Kalman gain `k = p h / (h² p + r)`. -/
def kgain (p h r : ℝ) : ℝ := p * h / (h ^ 2 * p + r)

/-- Covariance of two linear combinations of independent square-integrable variables. -/
@[tmio T, powerlib_foundation] theorem cov_lin_indep [IsFiniteMeasure P] {A W : Ω → ℝ}
    (hA : MemLp A 2 P) (hW : MemLp W 2 P) (hAW : IndepFun A W P) (a b c d : ℝ) :
    cov[fun ω => a * A ω + b * W ω, fun ω => c * A ω + d * W ω; P] =
      a * c * Var[A; P] + b * d * Var[W; P] := by
  have e1 : (fun ω => a * A ω + b * W ω) = (fun ω => a * A ω) + fun ω => b * W ω := rfl
  have e2 : (fun ω => c * A ω + d * W ω) = (fun ω => c * A ω) + fun ω => d * W ω := rfl
  rw [e1, e2, covariance_add_left (hA.const_mul a) (hW.const_mul b)
      ((hA.const_mul c).add (hW.const_mul d)),
    covariance_add_right (hA.const_mul a) (hA.const_mul c) (hW.const_mul d),
    covariance_add_right (hW.const_mul b) (hA.const_mul c) (hW.const_mul d)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  rw [covariance_self hA.aemeasurable, covariance_self hW.aemeasurable,
    hAW.covariance_eq_zero hA hW, hAW.symm.covariance_eq_zero hW hA]
  ring

section Model

variable {X V : Ω → ℝ} {m h : ℝ} {p r : ℝ≥0}

omit [MeasurableSpace Ω] in
@[tmio T, powerlib_foundation] theorem kgain_spec (hS : h ^ 2 * (p : ℝ) + r ≠ 0) :
    kgain p h r * (h ^ 2 * p + r) = p * h := by
  unfold kgain; rw [div_mul_cancel₀ _ hS]

/-- The scalar model is the vector model with `n = p = 1`: `(X, Y)` is a Gaussian vector of
`ℝ¹ × ℝ¹`. -/
@[tmio T] private theorem hasGaussianLaw_fin_one (hX : HasLaw X (gaussianReal m p) P)
    (hV : HasLaw V (gaussianReal 0 r) P) (hXV : IndepFun X V P) :
    HasGaussianLaw (fun ω => (fun _ : Fin 1 => X ω, fun _ : Fin 1 => h * X ω + V ω)) P := by
  have hJ : HasGaussianLaw (fun ω => (X ω, V ω)) P :=
    IndepFun.hasGaussianLaw hX.hasGaussianLaw hV.hasGaussianLaw hXV
  let L : ℝ × ℝ →L[ℝ] (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
    (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.pi fun _ =>
        h • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
  convert hJ.map_fun L using 2 with ω
  ext <;> simp [L]

/-- In the one-dimensional vector model the scalar gain solves `K Σ_YY = Σ_XY`. -/
@[tmio T] private theorem gain_fin_one (hX : HasLaw X (gaussianReal m p) P)
    (hV : HasLaw V (gaussianReal 0 r) P) (hXV : IndepFun X V P)
    (hS : h ^ 2 * (p : ℝ) + r ≠ 0) (i _j : Fin 1) :
    ∑ l, (Matrix.of fun _ _ => kgain p h r : Matrix (Fin 1) (Fin 1) ℝ) i l *
        cov[fun ω => h * X ω + V ω, fun ω => h * X ω + V ω; P] =
      cov[X, fun ω => h * X ω + V ω; P] := by
  have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hX2 : MemLp X 2 P := hX.memLp (memLp_id_gaussianReal 2)
  have hV2 : MemLp V 2 P := hV.memLp (memLp_id_gaussianReal 2)
  have hYY := cov_lin_indep hX2 hV2 hXV h 1 h 1
  have hXY := cov_lin_indep hX2 hV2 hXV 1 0 h 1
  simp only [one_mul, zero_mul, add_zero] at hYY hXY
  rw [hX.variance_eq, hV.variance_eq, variance_id_gaussianReal, variance_id_gaussianReal] at hYY
  rw [hX.variance_eq, variance_id_gaussianReal] at hXY
  rw [Fin.sum_univ_one, Matrix.of_apply, hYY, show X = fun ω => X ω from rfl, hXY]
  linear_combination kgain_spec (p := p) (r := r) hS

/-- The σ-algebra of the measurement does not depend on reading it as a vector of `ℝ¹`. -/
@[tmio T] private theorem comap_fin_one (Y : Ω → ℝ) :
    MeasurableSpace.comap (fun ω (_ : Fin 1) => Y ω) inferInstance =
      MeasurableSpace.comap Y inferInstance := by
  apply le_antisymm
  · rw [show (fun ω (_ : Fin 1) => Y ω) = (fun (y : ℝ) (_ : Fin 1) => y) ∘ Y from rfl,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_iff.mpr fun _ => measurable_id).comap_le
  · rw [show Y = (fun z : Fin 1 → ℝ => z 0) ∘ (fun ω (_ : Fin 1) => Y ω) from rfl,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply 0).comap_le

/-- The means of the state and of the measurement. -/
@[tmio T] private theorem integral_state_meas (hX : HasLaw X (gaussianReal m p) P)
    (hV : HasLaw V (gaussianReal 0 r) P) :
    ∫ ω, X ω ∂P = m ∧ ∫ ω, (h * X ω + V ω) ∂P = h * m := by
  have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hXi : Integrable X P := (hX.memLp (memLp_id_gaussianReal 2)).integrable one_le_two
  have hVi : Integrable V P := (hV.memLp (memLp_id_gaussianReal 2)).integrable one_le_two
  have hEX : ∫ ω, X ω ∂P = m := by rw [hX.integral_eq, integral_id_gaussianReal]
  refine ⟨hEX, ?_⟩
  rw [integral_add (hXi.const_mul h) hVi, integral_const_mul, hEX, hV.integral_eq,
    integral_id_gaussianReal, add_zero]

/-- **Gaussian conditioning lemma**: the estimation error `X − m − k (Y − h m)` is independent of
the measurement `Y = h X + V` (`gaussian_error_indep` for `n = p = 1`). -/
@[tmio T, powerlib_foundation] theorem kalman_innovation_indep (hX : HasLaw X (gaussianReal m p) P)
    (hV : HasLaw V (gaussianReal 0 r) P) (hXV : IndepFun X V P)
    (hS : h ^ 2 * (p : ℝ) + r ≠ 0) :
    IndepFun (fun ω => X ω - m - kgain p h r * (h * X ω + V ω - h * m))
      (fun ω => h * X ω + V ω) P := by
  have hind := (gaussian_error_indep (hasGaussianLaw_fin_one hX hV hXV)
    (gain_fin_one hX hV hXV hS)).comp (measurable_pi_apply 0 |>.sub_const
      (m - kgain p h r * (h * m))) (measurable_pi_apply 0)
  convert hind using 1
  · funext ω
    simp only [Function.comp_apply, Fin.sum_univ_one, Matrix.of_apply]
    ring
  · rfl

/-- Decomposition of the estimation error as a linear combination of the centred state and the
noise. -/
@[tmio T, powerlib_foundation] theorem kalman_error_eq :
    (fun ω => X ω - m - kgain p h r * (h * X ω + V ω - h * m)) =
      fun ω => (1 - kgain p h r * h) * (X ω - m) + (-kgain p h r) * V ω := by
  funext ω; ring

/-- The centred state `X − m ~ N(0, p)`. -/
@[tmio T, powerlib_foundation] theorem hasLaw_centred (hX : HasLaw X (gaussianReal m p) P) :
    HasLaw (fun ω => X ω - m) (gaussianReal 0 p) P := by
  have hmap : HasLaw (fun x : ℝ => x - m) (gaussianReal 0 p) (gaussianReal m p) :=
    ⟨by fun_prop, by rw [gaussianReal_map_sub_const, sub_self]⟩
  exact hmap.comp hX

/-- The estimation error has mean `0` and second moment `(1 − k h) p`. -/
@[tmio T, powerlib_foundation] theorem kalman_error_moments (hX : HasLaw X (gaussianReal m p) P)
    (hV : HasLaw V (gaussianReal 0 r) P) (hXV : IndepFun X V P)
    (hS : h ^ 2 * (p : ℝ) + r ≠ 0) :
    MemLp (fun ω => X ω - m - kgain p h r * (h * X ω + V ω - h * m)) 2 P ∧
    ∫ ω, (X ω - m - kgain p h r * (h * X ω + V ω - h * m)) ∂P = 0 ∧
    ∫ ω, (X ω - m - kgain p h r * (h * X ω + V ω - h * m)) ^ 2 ∂P =
      (1 - kgain p h r * h) * p := by
  set k := kgain p h r with hk
  have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hX' := hasLaw_centred hX
  have hX'V : IndepFun (fun ω => X ω - m) V P :=
    hXV.comp (measurable_id.sub_const m) measurable_id
  have hX2 : MemLp (fun ω => X ω - m) 2 P := hX'.memLp (memLp_id_gaussianReal 2)
  have hV2 : MemLp V 2 P := hV.memLp (memLp_id_gaussianReal 2)
  set Z : Ω → ℝ := fun ω => X ω - m - k * (h * X ω + V ω - h * m) with hZ
  have hZlin : Z = fun ω => (1 - k * h) * (X ω - m) + (-k) * V ω := kalman_error_eq
  have hZ2 : MemLp Z 2 P := by rw [hZlin]; exact (hX2.const_mul _).add (hV2.const_mul _)
  have hmean0 : ∫ ω, Z ω ∂P = 0 := by
    rw [hZlin, integral_add ((hX2.integrable one_le_two).const_mul _)
      ((hV2.integrable one_le_two).const_mul _), integral_const_mul, integral_const_mul,
      hX'.integral_eq, hV.integral_eq, integral_id_gaussianReal, integral_id_gaussianReal]
    simp
  refine ⟨hZ2, hmean0, ?_⟩
  have hvar := variance_eq_sub hZ2
  rw [hmean0] at hvar
  have e2 : ∫ ω, Z ω ^ 2 ∂P = Var[Z; P] := by rw [hvar]; simp
  rw [e2, ← covariance_self hZ2.aemeasurable]
  nth_rewrite 1 [hZlin]
  nth_rewrite 1 [hZlin]
  rw [cov_lin_indep hX2 hV2 hX'V, hX'.variance_eq, hV.variance_eq, variance_id_gaussianReal,
    variance_id_gaussianReal]
  have := kgain_spec (p := p) (r := r) hS
  rw [← hk] at this
  linear_combination k * this

/-- **The Kalman update is the conditional mean**: `E[X | Y] = m + k (Y − h m)` a.s.
(`gaussian_condExp_eq` for `n = p = 1`). -/
@[tmio T, powerlib_foundation] theorem kalman_condExp_eq (hX : HasLaw X (gaussianReal m p) P)
    (hV : HasLaw V (gaussianReal 0 r) P) (hXV : IndepFun X V P)
    (hS : h ^ 2 * (p : ℝ) + r ≠ 0) (hXm : Measurable X) (hVm : Measurable V) :
    P[X | MeasurableSpace.comap (fun ω => h * X ω + V ω) inferInstance] =ᵐ[P]
      fun ω => m + kgain p h r * (h * X ω + V ω - h * m) := by
  have hc := gaussian_condExp_eq (hasGaussianLaw_fin_one hX hV hXV) (fun _ => hXm)
    (fun _ => (hXm.const_mul h).add hVm) (gain_fin_one hX hV hXV hS) 0
  obtain ⟨hEX, hEY⟩ := integral_state_meas (h := h) hX hV
  rw [comap_fin_one] at hc
  simpa only [hEX, hEY, Fin.sum_univ_one, Matrix.of_apply] using hc

/-- **The Kalman posterior variance is the conditional variance**:
`E[(X − E[X|Y])² | Y] = (1 − k h) p` a.s. (`gaussian_condCov_eq` for `n = p = 1`). -/
@[tmio T, powerlib_foundation] theorem kalman_condVar_eq (hX : HasLaw X (gaussianReal m p) P)
    (hV : HasLaw V (gaussianReal 0 r) P) (hXV : IndepFun X V P)
    (hS : h ^ 2 * (p : ℝ) + r ≠ 0) (hXm : Measurable X) (hVm : Measurable V) :
    P[fun ω => (X ω - (m + kgain p h r * (h * X ω + V ω - h * m))) ^ 2 |
        MeasurableSpace.comap (fun ω => h * X ω + V ω) inferInstance] =ᵐ[P]
      fun _ => (1 - kgain p h r * h) * p := by
  have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hc := gaussian_condCov_eq (hasGaussianLaw_fin_one hX hV hXV) (fun _ => hXm)
    (fun _ => (hXm.const_mul h).add hVm) (gain_fin_one hX hV hXV hS) 0 0
  obtain ⟨hEX, hEY⟩ := integral_state_meas (h := h) hX hV
  rw [comap_fin_one] at hc
  simp only [hEX, hEY, Fin.sum_univ_one, Matrix.of_apply, ← sq] at hc
  refine hc.trans (Filter.EventuallyEq.of_eq (funext fun _ => ?_))
  have hX2 : MemLp X 2 P := hX.memLp (memLp_id_gaussianReal 2)
  have hV2 : MemLp V 2 P := hV.memLp (memLp_id_gaussianReal 2)
  have hXX := cov_lin_indep hX2 hV2 hXV 1 0 1 0
  have hXY := cov_lin_indep hX2 hV2 hXV 1 0 h 1
  simp only [one_mul, zero_mul, add_zero] at hXX hXY
  rw [hX.variance_eq, variance_id_gaussianReal] at hXX hXY
  rw [hXX, hXY]
  ring

end Model

end powerlib.Estimation
