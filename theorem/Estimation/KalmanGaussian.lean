import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.ConditionalExpectation

/-! # Kalman update = conditional mean in the scalar linear-Gaussian model

Source: work-sync `theory/T-kalman-filter.md` §1.1 (measurement update `K = P Hᵀ S⁻¹`,
`x̂⁺ = x̂ + K (y − H x̂)`, `P⁺ = (I − K H) P`; "for linear-Gaussian models the Kalman update is the
exact conditional mean and covariance").

Foundation (probability), not an engineering result.  Scalar state and scalar measurement:
`X ~ N(m, p)`, `V ~ N(0, r)` independent, `Y = h X + V`, gain `k = p h / (h² p + r)`.
* `kalman_innovation_indep` (Gaussian conditioning lemma): the estimation error
  `Z = X − m − k (Y − h m)` is independent of `Y` (jointly Gaussian and uncorrelated; Mathlib
  `HasGaussianLaw.indepFun_of_covariance_eq_zero`).
* `kalman_condExp_eq`: `E[X | Y] = m + k (Y − h m)` a.s. — the Kalman update is the conditional
  mean.
* `kalman_condVar_eq`: `E[(X − E[X|Y])² | Y] = (1 − k h) p` a.s. — the Kalman posterior variance
  is the (deterministic) conditional variance.

The vector case (matrix gain, Gaussian vectors) is not formalized here.
-/

noncomputable section
namespace powerlib.Estimation

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Scalar Kalman gain `k = p h / (h² p + r)`. -/
def kgain (p h r : ℝ) : ℝ := p * h / (h ^ 2 * p + r)

/-- Covariance of two linear combinations of independent square-integrable variables. -/
@[powerlib_foundation] theorem cov_lin_indep [IsFiniteMeasure P] {A W : Ω → ℝ}
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
@[powerlib_foundation] theorem kgain_spec (hS : h ^ 2 * (p : ℝ) + r ≠ 0) :
    kgain p h r * (h ^ 2 * p + r) = p * h := by
  unfold kgain; rw [div_mul_cancel₀ _ hS]

/-- **Gaussian conditioning lemma**: the estimation error `X − m − k (Y − h m)` is independent of
the measurement `Y = h X + V`. -/
@[powerlib_foundation] theorem kalman_innovation_indep (hX : HasLaw X (gaussianReal m p) P)
    (hV : HasLaw V (gaussianReal 0 r) P) (hXV : IndepFun X V P)
    (hS : h ^ 2 * (p : ℝ) + r ≠ 0) :
    IndepFun (fun ω => X ω - m - kgain p h r * (h * X ω + V ω - h * m))
      (fun ω => h * X ω + V ω) P := by
  set k := kgain p h r with hk
  have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
  -- centred state
  have hX' : HasLaw (fun ω => X ω - m) (gaussianReal 0 p) P := by
    have hmap : HasLaw (fun x : ℝ => x - m) (gaussianReal 0 p) (gaussianReal m p) :=
      ⟨by fun_prop, by rw [gaussianReal_map_sub_const, sub_self]⟩
    exact hmap.comp hX
  have hX'V : IndepFun (fun ω => X ω - m) V P :=
    hXV.comp (measurable_id.sub_const m) measurable_id
  have hJ : HasGaussianLaw (fun ω => (X ω - m, V ω)) P :=
    IndepFun.hasGaussianLaw hX'.hasGaussianLaw hV.hasGaussianLaw hX'V
  set L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    ((1 - k * h) • ContinuousLinearMap.fst ℝ ℝ ℝ - k • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (h • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) with hL
  have hJ2 : HasGaussianLaw (fun ω => ((1 - k * h) * (X ω - m) + (-k) * V ω,
      h * (X ω - m) + 1 * V ω)) P := by
    have := hJ.map_fun L
    convert this using 2 with ω
    ext
    all_goals simp [hL]
    all_goals ring
  have hX2 : MemLp (fun ω => X ω - m) 2 P := hX'.memLp (memLp_id_gaussianReal 2)
  have hV2 : MemLp V 2 P := hV.memLp (memLp_id_gaussianReal 2)
  have hcov : cov[fun ω => (1 - k * h) * (X ω - m) + (-k) * V ω,
      fun ω => h * (X ω - m) + 1 * V ω; P] = 0 := by
    rw [cov_lin_indep hX2 hV2 hX'V, hX'.variance_eq, hV.variance_eq, variance_id_gaussianReal,
      variance_id_gaussianReal]
    have := kgain_spec (p := p) (r := r) hS
    rw [← hk] at this
    linear_combination (-1 : ℝ) * this
  have hind := hJ2.indepFun_of_covariance_eq_zero hcov
  have hcomp := hind.comp measurable_id (measurable_id.add_const (h * m))
  convert hcomp using 1
  · funext ω; simp only [Function.comp_apply, id]; ring
  · funext ω; simp only [Function.comp_apply, id]; ring

/-- Decomposition of the estimation error as a linear combination of the centred state and the
noise. -/
@[powerlib_foundation] theorem kalman_error_eq :
    (fun ω => X ω - m - kgain p h r * (h * X ω + V ω - h * m)) =
      fun ω => (1 - kgain p h r * h) * (X ω - m) + (-kgain p h r) * V ω := by
  funext ω; ring

/-- The centred state `X − m ~ N(0, p)`. -/
@[powerlib_foundation] theorem hasLaw_centred (hX : HasLaw X (gaussianReal m p) P) :
    HasLaw (fun ω => X ω - m) (gaussianReal 0 p) P := by
  have hmap : HasLaw (fun x : ℝ => x - m) (gaussianReal 0 p) (gaussianReal m p) :=
    ⟨by fun_prop, by rw [gaussianReal_map_sub_const, sub_self]⟩
  exact hmap.comp hX

/-- The estimation error has mean `0` and second moment `(1 − k h) p`. -/
@[powerlib_foundation] theorem kalman_error_moments (hX : HasLaw X (gaussianReal m p) P)
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

/-- **The Kalman update is the conditional mean**: `E[X | Y] = m + k (Y − h m)` a.s. -/
@[powerlib_foundation] theorem kalman_condExp_eq (hX : HasLaw X (gaussianReal m p) P)
    (hV : HasLaw V (gaussianReal 0 r) P) (hXV : IndepFun X V P)
    (hS : h ^ 2 * (p : ℝ) + r ≠ 0) (hXm : Measurable X) (hVm : Measurable V) :
    P[X | MeasurableSpace.comap (fun ω => h * X ω + V ω) inferInstance] =ᵐ[P]
      fun ω => m + kgain p h r * (h * X ω + V ω - h * m) := by
  set k := kgain p h r with hk
  have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hind := kalman_innovation_indep hX hV hXV hS
  obtain ⟨hZ2, hZmean, -⟩ := kalman_error_moments hX hV hXV hS
  set Y : Ω → ℝ := fun ω => h * X ω + V ω with hY
  set Z : Ω → ℝ := fun ω => X ω - m - k * (h * X ω + V ω - h * m) with hZ
  have hYm : Measurable Y := (hXm.const_mul h).add hVm
  have hZm : Measurable Z :=
    (hXm.sub_const m).sub (((hXm.const_mul h).add hVm).sub_const (h * m) |>.const_mul k)
  have hZi : Integrable Z P := hZ2.integrable one_le_two
  have hle₂ : MeasurableSpace.comap Y inferInstance ≤ mΩ := hYm.comap_le
  have hle₁ : MeasurableSpace.comap Z inferInstance ≤ mΩ := hZm.comap_le
  have hcZ : P[Z | MeasurableSpace.comap Y inferInstance] =ᵐ[P] fun _ => ∫ ω, Z ω ∂P :=
    condExp_indep_eq hle₁ hle₂ (comap_measurable Z).stronglyMeasurable
      ((IndepFun_iff_Indep _ _ _).mp hind)
  set f : Ω → ℝ := fun ω => m + k * (Y ω - h * m) with hf
  have hfm : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] f :=
    ((measurable_const.add (measurable_const.mul (measurable_id.sub_const (h * m)))).comp
      (comap_measurable Y)).stronglyMeasurable
  have hXi : Integrable X P := hX.integrable (memLp_one_iff_integrable.mp (by
      simpa using memLp_id_gaussianReal (μ := m) (v := p) 1))
  have hfi : Integrable f P := by
    have : f = fun ω => X ω - Z ω := by funext ω; simp only [hf, hZ, hY]; ring
    rw [this]; exact hXi.sub hZi
  have hdec : X = f + Z := by funext ω; simp only [Pi.add_apply, hf, hZ]; ring
  have hadd := condExp_add hfi hZi (MeasurableSpace.comap Y inferInstance) (μ := P)
  rw [condExp_of_stronglyMeasurable hle₂ hfm hfi] at hadd
  rw [hdec]
  filter_upwards [hadd, hcZ] with ω h1 h2
  rw [h1, Pi.add_apply, h2, hZmean, add_zero]

/-- **The Kalman posterior variance is the conditional variance**:
`E[(X − E[X|Y])² | Y] = (1 − k h) p` a.s. -/
@[powerlib_foundation] theorem kalman_condVar_eq (hX : HasLaw X (gaussianReal m p) P)
    (hV : HasLaw V (gaussianReal 0 r) P) (hXV : IndepFun X V P)
    (hS : h ^ 2 * (p : ℝ) + r ≠ 0) (hXm : Measurable X) (hVm : Measurable V) :
    P[fun ω => (X ω - (m + kgain p h r * (h * X ω + V ω - h * m))) ^ 2 |
        MeasurableSpace.comap (fun ω => h * X ω + V ω) inferInstance] =ᵐ[P]
      fun _ => (1 - kgain p h r * h) * p := by
  set k := kgain p h r with hk
  have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hind := kalman_innovation_indep hX hV hXV hS
  obtain ⟨-, -, hsq⟩ := kalman_error_moments hX hV hXV hS
  set Y : Ω → ℝ := fun ω => h * X ω + V ω with hY
  set Z : Ω → ℝ := fun ω => X ω - m - k * (h * X ω + V ω - h * m) with hZ
  have hYm : Measurable Y := (hXm.const_mul h).add hVm
  have hZm : Measurable Z :=
    (hXm.sub_const m).sub (((hXm.const_mul h).add hVm).sub_const (h * m) |>.const_mul k)
  have e : (fun ω => (X ω - (m + k * (h * X ω + V ω - h * m))) ^ 2) = fun ω => Z ω ^ 2 := by
    funext ω; simp only [hZ]; ring
  rw [e]
  have hle₂ : MeasurableSpace.comap Y inferInstance ≤ mΩ := hYm.comap_le
  have hle₁ : MeasurableSpace.comap Z inferInstance ≤ mΩ := hZm.comap_le
  have hc := condExp_indep_eq hle₁ hle₂
    (((comap_measurable Z).pow_const 2).stronglyMeasurable (f := fun ω => Z ω ^ 2))
    ((IndepFun_iff_Indep _ _ _).mp hind) (μ := P)
  refine hc.trans (Filter.EventuallyEq.of_eq ?_)
  funext _
  exact hsq

end Model

end powerlib.Estimation
