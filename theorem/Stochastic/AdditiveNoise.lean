import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes
import theorem.Stochastic.ControlledAction
import theorem.Stochastic.LDPContraction

/-! # Additive noise: the pathwise solution map and the Freidlin–Wentzell rate

For additive noise the stochastic equation `dx = b(x) dt + N dw` needs no stochastic integral:
it is the integral equation `x(t) = x₀ + N w(t) + ∫₀ᵗ b(x(s)) ds`, solved path by path for every
continuous driving path `w`. This module builds the solution map `w ↦ x` on `C([0, T])`, proves
it continuous (Grönwall), and transports a large-deviation principle of the noise through it; the
rate is read on the admissible pairs of `theorem/Stochastic/ControlledAction.lean`.

Scope.
* Generic: `E`, `F` real normed spaces (`E` complete), `b : E → E` globally Lipschitz, `N` a
  continuous linear noise map, horizon `T ≥ 0` (`T : ℝ≥0`); paths are `C([0, T], ·)` with the
  sup norm; `pathExt` extends a path to `ℝ`, constant outside `[0, T]`.
* The noise process is not constructed here: a large-deviation principle of the laws of the
  noise on `C([0, T])` (for `√ε` times a Brownian motion, Schilder's theorem with the rate
  `schilderRate`) is a hypothesis of the transport theorems; Schilder's theorem itself is
  `theorem/Stochastic/Schilder.lean` (`isLDP_schilder`).
* Rate on `C([0, T], Fin m → ℝ)`: `schilderRate T w = ½ ∫₀ᵀ |u|²` when `w(t) = ∫₀ᵗ u` with `u`
  square integrable (the Cameron–Martin space `H¹₀`), `∞` otherwise; noise map `columnsCLM σ`,
  `v ↦ Σⱼ vⱼ σⱼ` (constant columns `σⱼ`, the additive case of `controlField`).

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984), Ch. 3
§1 (additive noise: the solution is a continuous function of the noise path, and the action
functional follows from that of the Wiener process); A. Dembo, O. Zeitouni, *Large Deviations
Techniques and Applications*, 2nd ed. (1998), Thm 5.2.3 (Schilder) and Thm 5.6.3 (its contraction
to diffusions); H. K. Khalil, *Nonlinear Systems*, 3rd ed., Thm 3.2 and Lemma A.1 (existence and
Grönwall, through LeanForControl `exists_isIntegralCurveOn_Icc`, `gronwall_const`).

Results.
* `pathExt`, `solMap` (the solution of the integral equation, chosen), `schilderRate`,
  `columnsCLM`, `fwRate` (`pushRate` of `schilderRate` through `solMap`).
* `exists_solution`, `solMap_spec` (`solMap` solves the equation), `eq_solMap` (uniqueness),
  `norm_solMap_sub_le` (`‖x − x'‖ ≤ ‖N‖ e^{KT} ‖w − w'‖`), `lipschitzWith_solMap`,
  `continuous_solMap`; `exists_leftInverse_solMap`: with a continuous linear left inverse of `N`
  the noise is recovered continuously from the solution, `w = L(x − x₀ − ∫ b(x))`.
* `IsLDP.map_solMap`, `IsLDP.map_solMap_of_isGoodRate`: an LDP of the noise laws gives an LDP of
  the solution laws with the pushed rate (contraction principle).
* Rate on admissible pairs: `exists_primitive_path`, `controlField_const`, `columnsCLM_apply`;
  `solMap_eq_of_admissible` (an admissible pair `(φ, u)` of `ControlledAction` from `x₀` with
  integrable control is the solution driven by `w = ∫ u`) and `admissible_of_solMap`
  (conversely, the solution driven by `∫ u`, `u` integrable and right-continuous, is an
  admissible pair); `fwRate_le_controlAction` (`J(φ) ≤ ½∫|u|²`), `ae_eq_of_primitive_eq`
  (Lebesgue differentiation), `schilderRate_eq` (`schilderRate (∫ u) = ½∫|u|²`),
  `fwRate_eq_controlAction` (equality when `N` has a left inverse: the control is then unique
  a.e.), `intervalIntegrable_of_admissible` (with such a left inverse every admissible control is
  integrable, so no extra hypothesis is needed).
* Helpers: `continuous_pathExt`, `pathExt_of_mem`, `norm_pathExt_sub_le`,
  `norm_sub_le_of_solution` (Grönwall for two solutions).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {T : ℝ≥0}

/-- A path on `[0, T]` extended to `ℝ`, constant outside the interval. -/
def pathExt (x : C(Icc (0 : ℝ) T, E)) : ℝ → E := IccExtend T.coe_nonneg x

/-- **Pathwise solution map** of `x(t) = x₀ + N w(t) + ∫₀ᵗ b(x(s)) ds` (the additive-noise
equation `dx = b(x) dt + N dw` solved for the driving path `w`; a chosen solution, unique when
`b` is Lipschitz, `eq_solMap`). -/
def solMap (b : E → E) (N : F →L[ℝ] E) (x₀ : E) (w : C(Icc (0 : ℝ) T, F)) :
    C(Icc (0 : ℝ) T, E) :=
  Classical.epsilon fun x : C(Icc (0 : ℝ) T, E) =>
    ∀ t : Icc (0 : ℝ) T, x t = x₀ + N (w t) + ∫ s in (0 : ℝ)..t, b (pathExt x s)

omit [NormedSpace ℝ E] in
@[tmio T, powerlib_foundation] theorem continuous_pathExt (x : C(Icc (0 : ℝ) T, E)) :
    Continuous (pathExt x) :=
  continuous_IccExtend_iff.mpr x.continuous

omit [NormedSpace ℝ E] in
@[tmio T, powerlib_foundation] theorem pathExt_of_mem (x : C(Icc (0 : ℝ) T, E)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) : pathExt x s = x ⟨s, hs⟩ :=
  IccExtend_of_mem _ _ hs

omit [NormedSpace ℝ E] in
@[tmio T, powerlib_foundation] theorem norm_pathExt_sub_le (x y : C(Icc (0 : ℝ) T, E)) (s : ℝ) :
    ‖pathExt x s - pathExt y s‖ ≤ ‖x - y‖ := by
  have := (x - y).norm_coe_le_norm (projIcc (0 : ℝ) (T : ℝ) T.coe_nonneg s)
  simpa [pathExt, IccExtend] using this

/-! ## Existence, uniqueness and continuity of the solution map -/

/-- **Existence** (globally Lipschitz drift): the equation has a continuous solution on `[0, T]`
for every continuous driving path. Through `y = x − N w`, it is the ODE `ẏ = b(y + N w(t))`,
`y(0) = x₀`, with a continuous field Lipschitz in `y` (LeanForControl
`exists_isIntegralCurveOn_Icc`). -/
@[tmio T, powerlib_foundation] theorem exists_solution [CompleteSpace E] {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E) (w : C(Icc (0 : ℝ) T, F)) :
    ∃ x : C(Icc (0 : ℝ) T, E), ∀ t : Icc (0 : ℝ) T,
      x t = x₀ + N (w t) + ∫ s in (0 : ℝ)..t, b (pathExt x s) := by
  set f : ℝ → E → E := fun t y => b (y + N (pathExt w t)) with hf
  have hwc := continuous_pathExt w
  have hf_cont : Continuous (Function.uncurry f) :=
    hb.continuous.comp (continuous_snd.add (N.continuous.comp (hwc.comp continuous_fst)))
  have hf_lip : ∀ t, LipschitzWith K (f t) := fun t =>
    LipschitzWith.of_dist_le_mul fun y z => by
      have := hb.dist_le_mul (y + N (pathExt w t)) (z + N (pathExt w t))
      simpa only [hf, dist_add_right] using this
  obtain ⟨α, hα0, hα⟩ := exists_isIntegralCurveOn_Icc hf_cont hf_lip 0 T x₀
  have hαc : ContinuousOn α (Icc 0 T) := hα.continuousOn
  let x : C(Icc (0 : ℝ) T, E) :=
    ⟨fun t => α t + N (w t), hαc.domRestrict.add (N.continuous.comp w.continuous)⟩
  have hext : ∀ s ∈ Icc (0 : ℝ) T, pathExt x s = α s + N (pathExt w s) := by
    intro s hs
    rw [pathExt_of_mem x hs, pathExt_of_mem w hs]
    rfl
  refine ⟨x, fun t => ?_⟩
  have ht := t.2
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hFc : ContinuousOn (fun s => f s (α s)) (Icc 0 T) :=
    hf_cont.comp_continuousOn (continuousOn_id.prodMk hαc)
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivAt α (f s (α s)) s := fun s hs =>
    (hα s ⟨hs.1.le, hs.2.le.trans ht.2⟩).hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hαc.mono hsub)
    hderiv ((hFc.mono hsub).intervalIntegrable_of_Icc ht.1)
  have hcongr : ∫ s in (0 : ℝ)..t, b (pathExt x s) = ∫ s in (0 : ℝ)..t, f s (α s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [hf, hext s (hsub hs)]
  change α t + N (w t) = _
  rw [hcongr, hftc, hα0]
  abel

/-- **Grönwall estimate** for two solutions: `‖x − x'‖ ≤ ‖N‖ ‖w − w'‖ e^{KT}`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_le_of_solution {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E) {w w' : C(Icc (0 : ℝ) T, F)}
    {x x' : C(Icc (0 : ℝ) T, E)}
    (hx : ∀ t : Icc (0 : ℝ) T, x t = x₀ + N (w t) + ∫ s in (0 : ℝ)..t, b (pathExt x s))
    (hx' : ∀ t : Icc (0 : ℝ) T, x' t = x₀ + N (w' t) + ∫ s in (0 : ℝ)..t, b (pathExt x' s)) :
    ‖x - x'‖ ≤ ‖N‖ * ‖w - w'‖ * Real.exp (K * T) := by
  set C := ‖N‖ * ‖w - w'‖ with hC
  set y : ℝ → ℝ := fun s => ‖pathExt x s - pathExt x' s‖ with hy
  have hyc : Continuous y := ((continuous_pathExt x).sub (continuous_pathExt x')).norm
  have hbx : Continuous fun s => b (pathExt x s) := hb.continuous.comp (continuous_pathExt x)
  have hbx' : Continuous fun s => b (pathExt x' s) := hb.continuous.comp (continuous_pathExt x')
  have hineq : ∀ t ∈ Icc (0 : ℝ) T, y t ≤ C + ∫ s in (0 : ℝ)..t, (K : ℝ) * y s := by
    intro t ht
    have e : pathExt x t - pathExt x' t = N (w ⟨t, ht⟩ - w' ⟨t, ht⟩) +
        ∫ s in (0 : ℝ)..t, (b (pathExt x s) - b (pathExt x' s)) := by
      rw [pathExt_of_mem x ht, pathExt_of_mem x' ht, hx, hx',
        intervalIntegral.integral_sub (hbx.intervalIntegrable _ _) (hbx'.intervalIntegrable _ _),
        map_sub]
      abel
    simp only [hy]
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (N.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      simpa using (w - w').norm_coe_le_norm ⟨t, ht⟩
    · refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
      refine intervalIntegral.integral_mono_on ht.1 ((hbx.sub hbx').norm.intervalIntegrable _ _)
        ((hyc.const_mul _).intervalIntegrable _ _) fun s _ => ?_
      have := hb.dist_le_mul (pathExt x s) (pathExt x' s)
      simpa [dist_eq_norm] using this
  have hg := gronwall_const (a := 0) (b := T) K.coe_nonneg hyc.continuousOn hineq
  have hC0 : 0 ≤ C := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun t => ?_
  have h1 := hg t t.2
  have h2 : y t = ‖(x - x') t‖ := by
    simp only [hy, pathExt_of_mem x t.2, pathExt_of_mem x' t.2, ContinuousMap.sub_apply]
  have h3 : Real.exp (K * (t - 0)) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.mpr (by nlinarith [t.2.2, K.coe_nonneg])
  rw [← h2]
  exact h1.trans (mul_le_mul_of_nonneg_left h3 hC0)

/-- `solMap` solves the equation (globally Lipschitz drift). -/
@[tmio T, powerlib_foundation] theorem solMap_spec [CompleteSpace E] {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E) (w : C(Icc (0 : ℝ) T, F))
    (t : Icc (0 : ℝ) T) :
    solMap b N x₀ w t = x₀ + N (w t) + ∫ s in (0 : ℝ)..t, b (pathExt (solMap b N x₀ w) s) :=
  Classical.epsilon_spec (p := fun x : C(Icc (0 : ℝ) T, E) => ∀ t : Icc (0 : ℝ) T,
    x t = x₀ + N (w t) + ∫ s in (0 : ℝ)..t, b (pathExt x s)) (exists_solution hb N x₀ w) t

/-- **Uniqueness**: every solution is `solMap`. -/
@[tmio T, powerlib_foundation] theorem eq_solMap [CompleteSpace E] {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) {N : F →L[ℝ] E} {x₀ : E} {w : C(Icc (0 : ℝ) T, F)}
    {x : C(Icc (0 : ℝ) T, E)}
    (hx : ∀ t : Icc (0 : ℝ) T, x t = x₀ + N (w t) + ∫ s in (0 : ℝ)..t, b (pathExt x s)) :
    x = solMap b N x₀ w := by
  have h := norm_sub_le_of_solution hb N x₀ hx (solMap_spec hb N x₀ w)
  rw [sub_self, norm_zero, mul_zero, zero_mul] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- **Continuity of the solution map**: `w ↦ x` is Lipschitz with constant `‖N‖ e^{KT}`. -/
@[tmio T, powerlib_foundation] theorem norm_solMap_sub_le [CompleteSpace E] {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E)
    (w w' : C(Icc (0 : ℝ) T, F)) :
    ‖solMap b N x₀ w - solMap b N x₀ w'‖ ≤ ‖N‖ * Real.exp (K * T) * ‖w - w'‖ := by
  have := norm_sub_le_of_solution hb N x₀ (solMap_spec hb N x₀ w) (solMap_spec hb N x₀ w')
  linarith [mul_comm (‖N‖ * ‖w - w'‖) (Real.exp (K * T)),
    mul_right_comm ‖N‖ ‖w - w'‖ (Real.exp (K * T))]

@[tmio T, powerlib_foundation] theorem lipschitzWith_solMap [CompleteSpace E] {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E) :
    LipschitzWith (‖N‖₊ * Real.toNNReal (Real.exp (K * T)))
      (solMap b N x₀ : C(Icc (0 : ℝ) T, F) → C(Icc (0 : ℝ) T, E)) :=
  LipschitzWith.of_dist_le_mul fun w w' => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, coe_nnnorm,
      Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact norm_solMap_sub_le hb N x₀ w w'

@[tmio T, powerlib_foundation] theorem continuous_solMap [CompleteSpace E] {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E) :
    Continuous (solMap b N x₀ : C(Icc (0 : ℝ) T, F) → C(Icc (0 : ℝ) T, E)) :=
  (lipschitzWith_solMap hb N x₀).continuous

/-- **Continuous left inverse**: if `L ∘ N = id`, the driving path is recovered from the
solution by the continuous map `x ↦ L(x − x₀ − ∫₀^· b(x))`. -/
@[tmio T, powerlib_foundation] theorem exists_leftInverse_solMap [CompleteSpace E] {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) {N : F →L[ℝ] E} {L : E →L[ℝ] F}
    (hL : ∀ v, L (N v) = v) (x₀ : E) :
    ∃ G : C(Icc (0 : ℝ) T, E) → C(Icc (0 : ℝ) T, F), Continuous G ∧
      ∀ w, G (solMap b N x₀ w) = w := by
  have hprim : ∀ x : C(Icc (0 : ℝ) T, E),
      Continuous fun t : ℝ => ∫ s in (0 : ℝ)..t, b (pathExt x s) := fun x =>
    intervalIntegral.continuous_primitive
      (fun _ _ => (hb.continuous.comp (continuous_pathExt x)).intervalIntegrable _ _) 0
  let G : C(Icc (0 : ℝ) T, E) → C(Icc (0 : ℝ) T, F) := fun x =>
    ⟨fun t => L (x t - x₀ - ∫ s in (0 : ℝ)..t, b (pathExt x s)),
      L.continuous.comp ((x.continuous.sub continuous_const).sub
        ((hprim x).comp continuous_subtype_val))⟩
  refine ⟨G, ?_, fun w => ?_⟩
  · refine (LipschitzWith.of_dist_le_mul (K := ‖L‖₊ * (1 + K * T)) fun x x' => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm]
    have hd : 0 ≤ ‖x - x'‖ := norm_nonneg _
    push_cast
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun t => ?_
    have hbx : Continuous fun s => b (pathExt x s) := hb.continuous.comp (continuous_pathExt x)
    have hbx' : Continuous fun s => b (pathExt x' s) :=
      hb.continuous.comp (continuous_pathExt x')
    have e : (G x - G x') t = L ((x t - x' t) -
        ∫ s in (0 : ℝ)..t, (b (pathExt x s) - b (pathExt x' s))) := by
      simp only [G, ContinuousMap.sub_apply, ContinuousMap.coe_mk, ← map_sub]
      rw [intervalIntegral.integral_sub (hbx.intervalIntegrable _ _)
        (hbx'.intervalIntegrable _ _)]
      congr 1
      abel
    rw [e]
    refine (L.le_opNorm _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖x t - x' t‖ ≤ ‖x - x'‖ := by simpa using (x - x').norm_coe_le_norm t
    have h2 : ‖∫ s in (0 : ℝ)..t, (b (pathExt x s) - b (pathExt x' s))‖ ≤
        K * ‖x - x'‖ * |(t : ℝ) - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => ?_
      have := hb.dist_le_mul (pathExt x s) (pathExt x' s)
      rw [dist_eq_norm, dist_eq_norm] at this
      exact this.trans (mul_le_mul_of_nonneg_left (norm_pathExt_sub_le x x' s) K.coe_nonneg)
    have h3 : |(t : ℝ) - 0| ≤ T := by
      rw [sub_zero, abs_of_nonneg t.2.1]
      exact t.2.2
    have h4 : K * ‖x - x'‖ * |(t : ℝ) - 0| ≤ K * ‖x - x'‖ * T :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg K.coe_nonneg hd)
    nlinarith
  · ext t
    simp only [G, ContinuousMap.coe_mk]
    rw [solMap_spec hb N x₀ w t]
    simp only [map_add, map_sub, hL]
    abel

/-! ## Transport of a large-deviation principle of the noise -/

/-- **Freidlin–Wentzell transport, additive noise**: if the laws `μ_i` of the driving noise on
`C([0, T], F)` satisfy a large-deviation principle with rate `I`, and the noise map `N` has a
continuous linear left inverse, the laws of the solutions `μ_i ∘ solMap⁻¹` satisfy it with the
rate `pushRate solMap I` (contraction principle with a continuous left inverse; `I` need not be
good). -/
@[tmio T, powerlib_foundation] theorem IsLDP.map_solMap [CompleteSpace E] {ι : Type*}
    [MeasurableSpace C(Icc (0 : ℝ) T, F)] [BorelSpace C(Icc (0 : ℝ) T, F)]
    [MeasurableSpace C(Icc (0 : ℝ) T, E)] [BorelSpace C(Icc (0 : ℝ) T, E)]
    {l : Filter ι} {s : ι → ℝ} {μ : ι → Measure C(Icc (0 : ℝ) T, F)}
    {I : C(Icc (0 : ℝ) T, F) → ℝ≥0∞} (h : IsLDP l s μ I) {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) {N : F →L[ℝ] E} {L : E →L[ℝ] F} (hL : ∀ v, L (N v) = v) (x₀ : E) :
    IsLDP l s (fun i => (μ i).map (solMap b N x₀)) (pushRate (solMap b N x₀) I) := by
  obtain ⟨G, hGc, hG⟩ := exists_leftInverse_solMap (T := T) hb hL x₀
  exact h.map_of_leftInverse (continuous_solMap hb N x₀) hGc hG

/-- The same for a good rate, without a left inverse of `N` (contraction principle). -/
@[tmio T, powerlib_foundation] theorem IsLDP.map_solMap_of_isGoodRate [CompleteSpace E]
    {ι : Type*} [MeasurableSpace C(Icc (0 : ℝ) T, F)] [BorelSpace C(Icc (0 : ℝ) T, F)]
    [MeasurableSpace C(Icc (0 : ℝ) T, E)] [BorelSpace C(Icc (0 : ℝ) T, E)]
    {l : Filter ι} {s : ι → ℝ} {μ : ι → Measure C(Icc (0 : ℝ) T, F)}
    {I : C(Icc (0 : ℝ) T, F) → ℝ≥0∞} (h : IsLDP l s μ I) (hI : IsGoodRate I) {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E) :
    IsLDP l s (fun i => (μ i).map (solMap b N x₀)) (pushRate (solMap b N x₀) I) :=
  h.map hI (continuous_solMap hb N x₀)

/-! ## The Schilder rate and the rate on admissible pairs -/

variable {m : ℕ}

/-- **Schilder (Cameron–Martin) rate** on `C([0, T], ℝᵐ)`: `½ ∫₀ᵀ |u|²` when `w(t) = ∫₀ᵗ u` with
`u` integrable and square integrable, `∞` otherwise. -/
def schilderRate (T : ℝ≥0) (w : C(Icc (0 : ℝ) T, Fin m → ℝ)) : ℝ≥0∞ :=
  ⨅ (u : ℝ → Fin m → ℝ) (_ : IntervalIntegrable u volume 0 T ∧
      IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T ∧
      ∀ t : Icc (0 : ℝ) T, w t = ∫ s in (0 : ℝ)..t, u s),
    ENNReal.ofReal (controlAction u T)

/-- Noise map of constant columns `σⱼ`: `v ↦ Σⱼ vⱼ σⱼ`. -/
def columnsCLM (σ : Fin m → E) : (Fin m → ℝ) →L[ℝ] E :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight (σ j)

/-- **Freidlin–Wentzell rate of the additive-noise model** on `C([0, T], E)`:
`J(φ) = inf {schilderRate w : solMap w = φ}`. -/
def fwRate (b : E → E) (σ : Fin m → E) (x₀ : E) (T : ℝ≥0) :
    C(Icc (0 : ℝ) T, E) → ℝ≥0∞ :=
  pushRate (solMap b (columnsCLM σ) x₀) (schilderRate T)

@[tmio T, powerlib_foundation] theorem columnsCLM_apply (σ : Fin m → E) (v : Fin m → ℝ) :
    columnsCLM σ v = ∑ j, v j • σ j := by
  simp [columnsCLM]

/-- The controlled field with constant columns is the drift plus the noise map. -/
@[tmio T, powerlib_foundation] theorem controlField_const (b : E → E) (σ : Fin m → E) (x : E)
    (v : Fin m → ℝ) : controlField b (fun _ => σ) x v = b x + columnsCLM σ v := by
  simp [controlField, columnsCLM_apply]

/-- The primitive of an integrable control is a continuous path. -/
@[tmio T, powerlib_foundation] theorem exists_primitive_path [CompleteSpace F] {u : ℝ → F}
    (hu : IntervalIntegrable u volume 0 T) :
    ∃ W : C(Icc (0 : ℝ) T, F), ∀ t : Icc (0 : ℝ) T, W t = ∫ s in (0 : ℝ)..t, u s := by
  have h := intervalIntegral.continuousOn_primitive_interval' hu left_mem_uIcc
  rw [uIcc_of_le T.coe_nonneg] at h
  exact ⟨⟨_, h.domRestrict⟩, fun t => rfl⟩

/-- **Admissible pairs are solutions**: an admissible pair `(φ, u)` of `ControlledAction` on
`[0, T]` from `x₀` (constant columns) with an integrable control is the solution driven by the
primitive `w = ∫ u`. -/
@[tmio T, powerlib_foundation] theorem solMap_eq_of_admissible [CompleteSpace E] {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) (σ : Fin m → E) {x₀ : E} {φ : ℝ → E}
    {u : ℝ → Fin m → ℝ} (h0 : φ 0 = x₀) (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt φ (controlField b (fun _ => σ) (φ t) (u t))
      (Ici t) t)
    (hu : IntervalIntegrable u volume 0 T) {W : C(Icc (0 : ℝ) T, Fin m → ℝ)}
    (hW : ∀ t : Icc (0 : ℝ) T, W t = ∫ s in (0 : ℝ)..t, u s) {x : C(Icc (0 : ℝ) T, E)}
    (hx : ∀ t : Icc (0 : ℝ) T, x t = φ t) : solMap b (columnsCLM σ) x₀ W = x := by
  refine (eq_solMap hb fun t => ?_).symm
  have ht := t.2
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hbφ : ContinuousOn (fun s => b (φ s)) (Icc 0 T) := hb.continuous.comp_continuousOn hc
  have hbi : IntervalIntegrable (fun s => b (φ s)) volume 0 t :=
    (hbφ.mono hsub).intervalIntegrable_of_Icc ht.1
  have hut : IntervalIntegrable u volume 0 t :=
    hu.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le T.coe_nonneg]; exact hsub)
  have hNu : IntervalIntegrable (fun s => columnsCLM σ (u s)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr ((columnsCLM σ).integrable_comp hut.1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 (hc.mono hsub)
    (fun s hs => ((hφ s ⟨hs.1.le, hs.2.trans_le ht.2⟩).mono Ioi_subset_Ici_self))
    ((hbi.add hNu).congr fun s _ => (controlField_const b σ (φ s) (u s)).symm)
  have hcongr : ∫ s in (0 : ℝ)..t, b (pathExt x s) = ∫ s in (0 : ℝ)..t, b (φ s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [pathExt_of_mem x (hsub hs), hx]
  rw [hx, hcongr, hW, ← (columnsCLM σ).intervalIntegral_comp_comm hut]
  have e : ∫ s in (0 : ℝ)..t, controlField b (fun _ => σ) (φ s) (u s) =
      (∫ s in (0 : ℝ)..t, b (φ s)) + ∫ s in (0 : ℝ)..t, columnsCLM σ (u s) := by
    rw [← intervalIntegral.integral_add hbi hNu]
    exact intervalIntegral.integral_congr fun s _ => controlField_const b σ (φ s) (u s)
  rw [e, h0] at hftc
  rw [eq_sub_iff_add_eq] at hftc
  rw [← hftc]
  abel

/-- **Converse: solutions driven by primitives of right-continuous controls are admissible**:
for `w = ∫ u` with `u` integrable and right-continuous on `[0, T)`, the solution `φ = solMap w`
(extended by `pathExt`) starts at `x₀`, is continuous on `[0, T]` and has the right derivative
`b(φ) + Σⱼ uⱼ σⱼ` at every point of `[0, T)`: `(φ, u)` is an admissible pair of
`ControlledAction`. -/
@[tmio T, powerlib_foundation] theorem admissible_of_solMap [CompleteSpace E] {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) (σ : Fin m → E) (x₀ : E) {u : ℝ → Fin m → ℝ}
    (hu : IntervalIntegrable u volume 0 T)
    (hrc : ∀ t ∈ Ico (0 : ℝ) T, ContinuousWithinAt u (Ioi t) t)
    {W : C(Icc (0 : ℝ) T, Fin m → ℝ)} (hW : ∀ t : Icc (0 : ℝ) T, W t = ∫ s in (0 : ℝ)..t, u s) :
    pathExt (solMap b (columnsCLM σ) x₀ W) 0 = x₀ ∧
      ContinuousOn (pathExt (solMap b (columnsCLM σ) x₀ W)) (Icc 0 T) ∧
      ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt (pathExt (solMap b (columnsCLM σ) x₀ W))
        (controlField b (fun _ => σ) (pathExt (solMap b (columnsCLM σ) x₀ W) t) (u t))
        (Ici t) t := by
  set x := solMap b (columnsCLM σ) x₀ W with hxdef
  set N := columnsCLM σ with hN
  have hspec := solMap_spec hb N x₀ W
  set F : ℝ → E := fun s => x₀ + N (∫ r in (0 : ℝ)..s, u r) + ∫ r in (0 : ℝ)..s, b (pathExt x r)
    with hF
  have hφF : ∀ s ∈ Icc (0 : ℝ) T, pathExt x s = F s := by
    intro s hs
    rw [pathExt_of_mem x hs, hspec, hW]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, T.coe_nonneg⟩
  refine ⟨?_, (continuous_pathExt x).continuousOn, fun t ht => ?_⟩
  · rw [hφF 0 h0]
    simp [hF]
  have htT : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
  have hut : IntervalIntegrable u volume 0 t :=
    hu.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le T.coe_nonneg]; exact Icc_subset_Icc_right htT.2)
  have hmeas : StronglyMeasurableAtFilter u (𝓝[>] t) := by
    refine ⟨Ioc 0 T, mem_of_superset (Ioo_mem_nhdsGT ht.2)
      fun s hs => ⟨ht.1.trans_lt hs.1, hs.2.le⟩, ?_⟩
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp hu).aestronglyMeasurable
  have h1 := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici t) (t := Ioi t) hut hmeas
    (hrc t ht)
  have h1' := N.hasFDerivAt.comp_hasDerivWithinAt t h1
  have hbx : Continuous fun r => b (pathExt x r) := hb.continuous.comp (continuous_pathExt x)
  have h2 := (hbx.integral_hasStrictDerivAt 0 t).hasDerivAt.hasDerivWithinAt (s := Ici t)
  have hFd := ((hasDerivWithinAt_const t (Ici t) x₀).add h1').add h2
  have hev : pathExt x =ᶠ[𝓝[≥] t] F := by
    filter_upwards [Ico_mem_nhdsGE ht.2] with s hs
    exact hφF s ⟨ht.1.trans hs.1, hs.2.le⟩
  refine (hFd.congr_of_eventuallyEq hev (hφF t htT)).congr_deriv ?_
  rw [controlField_const]
  simp only [zero_add]
  abel

/-- **Rate on admissible pairs, upper bound**: `J(φ) ≤ ½ ∫₀ᵀ |u|²` for an admissible pair with an
integrable control. -/
@[tmio T, powerlib_foundation] theorem fwRate_le_controlAction [CompleteSpace E] {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) (σ : Fin m → E) {x₀ : E} {φ : ℝ → E}
    {u : ℝ → Fin m → ℝ} (h0 : φ 0 = x₀) (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt φ (controlField b (fun _ => σ) (φ t) (u t))
      (Ici t) t)
    (hu : IntervalIntegrable u volume 0 T)
    (hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T) {x : C(Icc (0 : ℝ) T, E)}
    (hx : ∀ t : Icc (0 : ℝ) T, x t = φ t) :
    fwRate b σ x₀ T x ≤ ENNReal.ofReal (controlAction u T) := by
  obtain ⟨W, hW⟩ := exists_primitive_path (T := T) hu
  have hS := solMap_eq_of_admissible hb σ h0 hc hφ hu hW hx
  calc fwRate b σ x₀ T x = pushRate (solMap b (columnsCLM σ) x₀) (schilderRate T)
        (solMap b (columnsCLM σ) x₀ W) := by rw [hS]; rfl
    _ ≤ schilderRate T W := pushRate_le _ _ W
    _ ≤ ENNReal.ofReal (controlAction u T) :=
      iInf₂_le_of_le u ⟨hu, hu2, hW⟩ le_rfl

/-- **Equal primitives give a.e. equal integrands** (Lebesgue differentiation). -/
@[tmio T, powerlib_foundation] theorem ae_eq_of_primitive_eq [CompleteSpace F] {u u' : ℝ → F}
    (hu : IntervalIntegrable u volume 0 T) (hu' : IntervalIntegrable u' volume 0 T)
    (h : ∀ t ∈ Icc (0 : ℝ) T, ∫ s in (0 : ℝ)..t, u s = ∫ s in (0 : ℝ)..t, u' s) :
    ∀ᵐ s, s ∈ Ioo (0 : ℝ) T → u s = u' s := by
  filter_upwards [hu.ae_hasDerivAt_integral, hu'.ae_hasDerivAt_integral] with s h1 h2 hs
  have hsI : s ∈ uIcc (0 : ℝ) T := by rw [uIcc_of_le T.coe_nonneg]; exact Ioo_subset_Icc_self hs
  have d1 := h1 hsI 0 left_mem_uIcc
  have d2 := h2 hsI 0 left_mem_uIcc
  have hev : (fun x => ∫ t in (0 : ℝ)..x, u' t) =ᶠ[𝓝 s] fun x => ∫ t in (0 : ℝ)..x, u t := by
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with x hx
    exact (h x hx).symm
  exact d1.unique (d2.congr_of_eventuallyEq hev.symm)

/-- **Value of the Schilder rate**: if `w(t) = ∫₀ᵗ u` with `u` integrable and square integrable,
then `schilderRate T w = ½ ∫₀ᵀ |u|²` (every other representative equals `u` a.e.). -/
@[tmio T, powerlib_foundation] theorem schilderRate_eq {u : ℝ → Fin m → ℝ}
    (hu : IntervalIntegrable u volume 0 T)
    (hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T)
    {W : C(Icc (0 : ℝ) T, Fin m → ℝ)} (hW : ∀ t : Icc (0 : ℝ) T, W t = ∫ s in (0 : ℝ)..t, u s) :
    schilderRate T W = ENNReal.ofReal (controlAction u T) := by
  refine le_antisymm (iInf₂_le_of_le u ⟨hu, hu2, hW⟩ le_rfl) ?_
  refine le_iInf₂ fun u' ⟨hu', _, hWu'⟩ => ?_
  have hae := ae_eq_of_primitive_eq hu hu' fun t ht => by rw [← hW ⟨t, ht⟩, ← hWu' ⟨t, ht⟩]
  have hT : ∀ᵐ s : ℝ, s ≠ (T : ℝ) := by simp [ae_iff, measure_singleton]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold controlAction
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae, hT] with s hs hsT hsI
  rw [uIoc_of_le T.coe_nonneg] at hsI
  rw [hs ⟨hsI.1, lt_of_le_of_ne hsI.2 hsT⟩]

/-- **Rate on admissible pairs, value**: if the noise map has a left inverse (`L ∘ N = id`), the
control of an admissible pair is unique a.e. and `J(φ) = ½ ∫₀ᵀ |u|²`. -/
@[tmio T, powerlib_foundation] theorem fwRate_eq_controlAction [CompleteSpace E] {K : ℝ≥0}
    {b : E → E} (hb : LipschitzWith K b) (σ : Fin m → E) {L : E →L[ℝ] Fin m → ℝ}
    (hL : ∀ v, L (columnsCLM σ v) = v) {x₀ : E} {φ : ℝ → E}
    {u : ℝ → Fin m → ℝ} (h0 : φ 0 = x₀) (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt φ (controlField b (fun _ => σ) (φ t) (u t))
      (Ici t) t)
    (hu : IntervalIntegrable u volume 0 T)
    (hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T) {x : C(Icc (0 : ℝ) T, E)}
    (hx : ∀ t : Icc (0 : ℝ) T, x t = φ t) :
    fwRate b σ x₀ T x = ENNReal.ofReal (controlAction u T) := by
  refine le_antisymm (fwRate_le_controlAction hb σ h0 hc hφ hu hu2 hx) ?_
  obtain ⟨G, -, hG⟩ := exists_leftInverse_solMap (T := T) hb hL x₀
  obtain ⟨W, hW⟩ := exists_primitive_path (T := T) hu
  have hS := solMap_eq_of_admissible hb σ h0 hc hφ hu hW hx
  rw [← schilderRate_eq hu hu2 hW]
  refine le_iInf₂ fun W' hW' => ?_
  have hWW : W' = W := by rw [← hG W', hW', ← hS, hG]
  rw [hWW]

/-- **Admissible controls are integrable** when the noise map has a left inverse: on `[0, T)`,
`u = L(φ'₊ − b(φ))` with the (measurable) right derivative `φ'₊`, and `|u| ≤ 1 + Σⱼ uⱼ²`. -/
@[tmio T, powerlib_foundation] theorem intervalIntegrable_of_admissible [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] {K : ℝ≥0} {b : E → E} (hb : LipschitzWith K b)
    (σ : Fin m → E) {L : E →L[ℝ] Fin m → ℝ} (hL : ∀ v, L (columnsCLM σ v) = v) {φ : ℝ → E}
    {u : ℝ → Fin m → ℝ} (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt φ (controlField b (fun _ => σ) (φ t) (u t))
      (Ici t) t)
    (hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T) :
    IntervalIntegrable u volume 0 T := by
  set g : ℝ → Fin m → ℝ := fun t => L (derivWithin φ (Ici t) t) - L (b (φ t)) with hg
  have hug : ∀ t ∈ Ico (0 : ℝ) T, u t = g t := by
    intro t ht
    have hd := (hφ t ht).derivWithin (uniqueDiffWithinAt_Ici t)
    rw [controlField_const] at hd
    simp only [hg, hd, map_add, hL, add_sub_cancel_left]
  have hD : Measurable fun t => L (derivWithin φ (Ici t) t) :=
    L.continuous.measurable.comp (measurable_derivWithin_Ici φ)
  have hB : AEStronglyMeasurable (fun t => L (b (φ t))) (volume.restrict (Ioc 0 T)) :=
    ((L.continuous.comp hb.continuous).comp_continuousOn hc).aestronglyMeasurable
      measurableSet_Icc |>.mono_set Ioc_subset_Icc_self
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioc 0 T)) :=
    hD.aestronglyMeasurable.sub hB
  have hT : ∀ᵐ s : ℝ, s ≠ (T : ℝ) := by simp [ae_iff, measure_singleton]
  have hum : AEStronglyMeasurable u (volume.restrict (Ioc 0 T)) := by
    refine hgm.congr ?_
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hT] with s hsT hs
    exact (hug s ⟨hs.1.le, lt_of_le_of_ne hs.2 hsT⟩).symm
  have hint : IntegrableOn (fun t => 1 + ∑ j, u t j ^ 2) (Ioc 0 T) := by
    have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp hu2
    exact (integrableOn_const (by simp)).add h2
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr ?_
  refine hint.mono' hum (Eventually.of_forall fun t => ?_)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  have hj : u t j ^ 2 ≤ ∑ i, u t i ^ 2 :=
    Finset.single_le_sum (f := fun i => u t i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (u t j), sq_abs (u t j)]

end powerlib.Stochastic.LDP
