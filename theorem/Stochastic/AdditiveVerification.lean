import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.AdditiveNoise
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # The verification theorem for absolutely continuous controlled paths

The Hamilton–Jacobi verification inequality of `theorem/Stochastic/ControlledAction.lean`
(`sub_le_controlAction`) is stated for paths with a right derivative at every point. The paths of
finite Freidlin–Wentzell rate (`fwRate` of `theorem/Stochastic/AdditiveNoise.lean`) are only
absolutely continuous: they are driven by square-integrable controls `u`. This module proves the
inequality `W(φ(T)) − W(φ(0)) ≤ ½ ∫₀ᵀ |u|²` for them, and hence the Hamilton–Jacobi lower bound
of the rate and of its quasi-potential.

Scope.
* Generic: `E` a real Banach space, `b` globally Lipschitz, constant noise columns `σⱼ`,
  `W : E → ℝ` with a continuous derivative `dW` and `H(x, dW(x)) ≤ 0` everywhere
  (`hjHamiltonian`, the Hamilton–Jacobi subsolution property).
* Absolutely continuous calculus is Mathlib's `AbsolutelyContinuousOnInterval`
  (`const_of_ae_hasDerivAt_zero`); derivatives of primitives are Lebesgue's differentiation
  theorem (`IntervalIntegrable.ae_hasDerivAt_integral`).

Source: W. H. Fleming, R. W. Rishel, *Deterministic and Stochastic Optimal Control* (1975),
Ch. IV (verification theorem); M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical
Systems* (1984), Ch. 4 §3 (the quasi-potential bounded below by a subsolution of the
Hamilton–Jacobi equation, for absolutely continuous paths).

Results.
* `absolutelyContinuousOnInterval_of_dist_le`: a path whose increments are dominated by those of
  an absolutely continuous real function is absolutely continuous.
* `sub_le_controlAction_of_primitive` (**verification theorem, absolutely continuous paths**):
  for `w = ∫ u`, `u` integrable and square integrable, the solution `x = solMap w` satisfies
  `W(x(T)) − W(x₀) ≤ ½ ∫₀ᵀ |u|²`.
* `le_fwRate_of_hj`: `W(φ(T)) − W(x₀) ≤ J_T(φ)` for every path; `le_fwQP_of_hj`: the quasi-potential
  of the rate, `inf_T inf {J_T(φ) : φ(T) = x}` from `x_A`, is at least `W(x) − W(x_A)`.
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ≥0} {m : ℕ}

/-- **Comparison for absolute continuity**: if `dist (f x) (f y) ≤ dist (g x) (g y)` on
`[a, b]` and `g` is absolutely continuous there, so is `f`. -/
@[tmio T, powerlib_foundation] theorem absolutelyContinuousOnInterval_of_dist_le {X : Type*}
    [PseudoMetricSpace X] {f : ℝ → X} {g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  unfold AbsolutelyContinuousOnInterval at hg ⊢
  refine squeeze_zero' (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
    ?_ hg
  rw [eventually_inf_principal]
  filter_upwards with E hE
  exact Finset.sum_le_sum fun i hi => h _ (hE.1 i hi).1 _ (hE.1 i hi).2

/-- **Verification theorem for absolutely continuous paths**: if `W` has a continuous derivative
`dW` with `H(x, dW(x)) ≤ 0` everywhere, then along the solution `x = solMap w` driven by
`w = ∫ u` (`u` integrable and square integrable), `W(x(T)) − W(x₀) ≤ ½ ∫₀ᵀ |u|²`. -/
@[tmio T, powerlib_foundation] theorem sub_le_controlAction_of_primitive [CompleteSpace E]
    {K : ℝ≥0} {b : E → E} (hb : LipschitzWith K b) (σ : Fin m → E) (x₀ : E) {W : E → ℝ}
    {dW : E → E →L[ℝ] ℝ} (hW : ∀ x, HasFDerivAt W (dW x) x) (hdW : Continuous dW)
    (hHJ : ∀ x, hjHamiltonian b (fun _ => σ) x (dW x) ≤ 0) {u : ℝ → Fin m → ℝ}
    (hu : IntervalIntegrable u volume 0 T)
    (hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T)
    {w : C(Icc (0 : ℝ) T, Fin m → ℝ)} (hw : ∀ t : Icc (0 : ℝ) T, w t = ∫ s in (0 : ℝ)..t, u s) :
    W (solMap b (columnsCLM σ) x₀ w ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩) - W x₀ ≤
      controlAction u T := by
  set N := columnsCLM σ with hN
  have hspec := solMap_spec hb N x₀ w
  generalize hx : solMap b N x₀ w = x at hspec ⊢
  set φ := pathExt x with hφdef
  have hφc : Continuous φ := continuous_pathExt x
  have hbφ : Continuous fun r => b (φ r) := hb.continuous.comp hφc
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have hIcc : uIcc (0 : ℝ) T = Icc (0 : ℝ) T := uIcc_of_le hT0
  have hsub : ∀ t ∈ Icc (0 : ℝ) T, uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) T := fun t ht => by
    rw [uIcc_of_le ht.1, hIcc]; exact Icc_subset_Icc_right ht.2
  have hNu : IntervalIntegrable (fun r => N (u r)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr
      (N.integrable_comp ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mp hu))
  set v : ℝ → E := fun r => N (u r) + b (φ r) with hv
  have hvi : IntervalIntegrable v volume 0 T := hNu.add (hbφ.intervalIntegrable _ _)
  set F : ℝ → E := fun t => x₀ + ∫ r in (0 : ℝ)..t, v r with hF
  have hφF : ∀ s ∈ Icc (0 : ℝ) T, φ s = F s := by
    intro s hs
    have hus : IntervalIntegrable u volume 0 s := hu.mono_set (hsub s hs)
    have hNus : IntervalIntegrable (fun r => N (u r)) volume 0 s := hNu.mono_set (hsub s hs)
    rw [hφdef, pathExt_of_mem x hs, hspec, hw]
    simp only [hF, hv]
    rw [intervalIntegral.integral_add hNus (hbφ.intervalIntegrable _ _),
      ← N.intervalIntegral_comp_comm hus]
    abel
  -- the integrand `h = dW(φ)(v)` and its integrability
  set h : ℝ → ℝ := fun r => dW (φ r) (v r) with hh
  have hdWφ : Continuous fun r => dW (φ r) := hdW.comp hφc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (T : ℝ))).exists_bound_of_continuousOn
    hdWφ.continuousOn
  have hvI := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mp hvi
  have hhi : IntervalIntegrable h volume 0 T := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr ?_
    have hmeas : AEStronglyMeasurable h (volume.restrict (Ioc 0 T)) :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hdWφ.aestronglyMeasurable.prodMk hvI.aestronglyMeasurable)
    refine (hvI.norm.const_mul C).mono' hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun r hr => ?_
    calc ‖h r‖ ≤ ‖dW (φ r)‖ * ‖v r‖ := (dW (φ r)).le_opNorm _
      _ ≤ C * ‖v r‖ := mul_le_mul_of_nonneg_right (hC r (Ioc_subset_Icc_self hr))
          (norm_nonneg _)
  -- `g = W ∘ F − ∫ h` is absolutely continuous with derivative `0` a.e.
  set g : ℝ → ℝ := fun t => W (F t) - ∫ r in (0 : ℝ)..t, h r with hg
  have hFac : AbsolutelyContinuousOnInterval F 0 T := by
    refine absolutelyContinuousOnInterval_of_dist_le
      (hvi.norm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc) fun s hs t ht => ?_
    rw [dist_eq_norm, Real.dist_eq, hF]
    simp only [add_sub_add_left_eq_sub]
    rw [intervalIntegral.integral_interval_sub_left (hvi.mono_set (hsub s (hIcc ▸ hs)))
        (hvi.mono_set (hsub t (hIcc ▸ ht))),
      intervalIntegral.integral_interval_sub_left
        (hvi.norm.mono_set (hsub s (hIcc ▸ hs))) (hvi.norm.mono_set (hsub t (hIcc ▸ ht)))]
    exact intervalIntegral.norm_integral_le_abs_integral_norm
  have hS : IsCompact (F '' Icc (0 : ℝ) T) := by
    rw [image_congr fun s hs => (hφF s hs).symm]
    exact isCompact_Icc.image hφc
  obtain ⟨KW, hKW⟩ := (((contDiff_one_iff_hasFDerivAt.mpr ⟨dW, hdW, hW⟩).locallyLipschitz
    ).locallyLipschitzOn).exists_lipschitzOnWith_of_compact hS
  have hWF : AbsolutelyContinuousOnInterval (fun t => W (F t)) 0 T :=
    hKW.comp_absolutelyContinuousOnInterval (by rw [hIcc]; exact mapsTo_image F _) hFac
  have hgac : AbsolutelyContinuousOnInterval g 0 T :=
    hWF.sub (hhi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hT : ∀ᵐ s : ℝ, s ≠ (T : ℝ) := by simp [ae_iff, measure_singleton]
  have h0' : ∀ᵐ s : ℝ, s ≠ (0 : ℝ) := by simp [ae_iff, measure_singleton]
  have hgd : ∀ᵐ t, t ∈ uIcc (0 : ℝ) T → HasDerivAt g 0 t := by
    filter_upwards [hvi.ae_hasDerivAt_integral, hhi.ae_hasDerivAt_integral, hT, h0']
      with t h1 h2 htT ht0 ht
    have hFd : HasDerivAt F (v t) t := by
      rw [hF]; exact (h1 ht 0 left_mem_uIcc).const_add x₀
    have hWd := (hW (F t)).comp_hasDerivAt t hFd
    have hd := hWd.sub (h2 ht 0 left_mem_uIcc)
    rw [hIcc] at ht
    have htF : φ t = F t := hφF t ht
    have e : dW (F t) (v t) - h t = 0 := by
      rw [hh]; dsimp only; rw [htF, sub_self]
    rw [e] at hd
    exact hd
  obtain ⟨c, hc⟩ := hgac.const_of_ae_hasDerivAt_zero hgd
  have hgT : g T = g 0 := by
    rw [hc _ right_mem_uIcc, hc _ left_mem_uIcc]
  have hF0 : F 0 = x₀ := by simp [hF]
  have hxT : x ⟨T, right_mem_Icc.mpr hT0⟩ = F T := by
    rw [← hφF T (right_mem_Icc.mpr hT0), hφdef, pathExt_of_mem]
  simp only [hg, hF0, intervalIntegral.integral_same, sub_zero] at hgT
  rw [hxT, show W (F T) - W x₀ = ∫ r in (0 : ℝ)..T, h r by linarith]
  -- pointwise completing the square
  unfold controlAction
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hT0 hhi (hu2.const_mul _) fun r hr => ?_
  have hvr : v r = controlField b (fun _ => σ) (φ r) (u r) := by
    rw [controlField_const, add_comm]
  simp only [hh, hvr]
  rw [apply_controlField]
  have h1 := hHJ (φ r)
  have h2 : 0 ≤ ∑ j, (u r j - dW (φ r) (σ j)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

/-- **Hamilton–Jacobi lower bound of the rate**: `W(φ(T)) − W(x₀) ≤ J_T(φ)` for every path `φ`
on `[0, T]`. -/
@[tmio T, powerlib_foundation] theorem le_fwRate_of_hj [CompleteSpace E] {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (σ : Fin m → E) (x₀ : E) {W : E → ℝ} {dW : E → E →L[ℝ] ℝ}
    (hW : ∀ x, HasFDerivAt W (dW x) x) (hdW : Continuous dW)
    (hHJ : ∀ x, hjHamiltonian b (fun _ => σ) x (dW x) ≤ 0) (φ : C(Icc (0 : ℝ) T, E)) :
    ENNReal.ofReal (W (φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩) - W x₀) ≤ fwRate b σ x₀ T φ := by
  unfold fwRate pushRate
  refine le_iInf₂ fun w hw => le_iInf₂ fun u ⟨hu, hu2, hwu⟩ => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have := sub_le_controlAction_of_primitive hb σ x₀ hW hdW hHJ hu hu2 hwu
  rwa [hw] at this

/-- **Hamilton–Jacobi lower bound of the quasi-potential of the rate**:
`inf_T inf {J_T(φ) : φ(T) = x} ≥ W(x) − W(x_A)` (paths from `x_A`). -/
@[tmio T, powerlib_foundation] theorem le_fwQP_of_hj [CompleteSpace E] {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (σ : Fin m → E) {W : E → ℝ} {dW : E → E →L[ℝ] ℝ}
    (hW : ∀ x, HasFDerivAt W (dW x) x) (hdW : Continuous dW)
    (hHJ : ∀ x, hjHamiltonian b (fun _ => σ) x (dW x) ≤ 0) (xA x : E) :
    ENNReal.ofReal (W x - W xA) ≤
      ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, E)) (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        fwRate b σ xA T φ := by
  refine le_iInf fun T => le_iInf fun φ => le_iInf fun hφ => ?_
  have := le_fwRate_of_hj hb σ xA hW hdW hHJ φ
  rwa [hφ] at this

end powerlib.Stochastic.LDP
