import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.AdditiveNoise

/-! # Large deviations of the additive-noise model, uniform over compact sets of initial points

The solution map of `x(t) = x₀ + N w(t) + ∫₀ᵗ b(x)` is jointly continuous in the initial point and
the driving path (Grönwall: `‖x − x'‖ ≤ (‖x₀ − x₀'‖ + ‖N‖ ‖w − w'‖) e^{KT}`). Hence a
large-deviation principle for the noise transports to the solutions **uniformly over initial
points in a compact set `K`**:
`limsup s log sup_{x₀ ∈ K} P(x^{x₀} ∈ A) ≤ −inf_{x₀ ∈ K} inf_{cl A} J_{x₀}` and, for open `G`,
`liminf s log inf_{x₀ ∈ K} P(x^{x₀} ∈ G) ≥ −sup_{x₀ ∈ K} inf_G J_{x₀}`, with
`J_{x₀} = pushRate (solMap x₀) I` (the Freidlin–Wentzell rate from `x₀` when `I` is the Schilder
rate). This is the uniform large-deviation principle used in the proof of the exit-time theorem;
no ellipticity of the noise is needed.

Scope.
* Generic: `E`, `F` real Banach spaces, `b` globally Lipschitz, `N : F →L[ℝ] E`, any filter with
  eventually nonnegative speed `s`. The upper bound uses only the upper bound of the noise
  principle on closed sets; the lower bound only its lower bound on open balls.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 3 §3 (Thms 3.3.1–3.3.3: the action functional uniformly in the initial point); A. Dembo,
O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed. (1998), Cor. 5.6.15 (the
uniform principle for diffusions on compacts).

Results.
* `norm_sub_le_of_solution₂` (Grönwall, two initial points), `lipschitzWith_solMap_uncurry`,
  `continuous_solMap_uncurry`, `isClosed_exists_solMap_mem` (`{w : ∃ x₀ ∈ K, S(x₀, w) ∈ C}` is
  closed for `K` compact and `C` closed).
* `IsLDP.limsup_iSup_solMap_le` (**uniform upper bound**), `IsLDP.le_liminf_iInf_solMap`
  (**uniform lower bound**).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {T : ℝ≥0}

omit [CompleteSpace E] in
/-- **Grönwall estimate, two initial points**:
`‖x − x'‖ ≤ (‖x₀ − x₀'‖ + ‖N‖ ‖w − w'‖) e^{KT}`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_le_of_solution₂ {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) {x₀ x₀' : E} {w w' : C(Icc (0 : ℝ) T, F)}
    {x x' : C(Icc (0 : ℝ) T, E)}
    (hx : ∀ t : Icc (0 : ℝ) T, x t = x₀ + N (w t) + ∫ s in (0 : ℝ)..t, b (pathExt x s))
    (hx' : ∀ t : Icc (0 : ℝ) T, x' t = x₀' + N (w' t) + ∫ s in (0 : ℝ)..t, b (pathExt x' s)) :
    ‖x - x'‖ ≤ (‖x₀ - x₀'‖ + ‖N‖ * ‖w - w'‖) * Real.exp (K * T) := by
  set C := ‖x₀ - x₀'‖ + ‖N‖ * ‖w - w'‖ with hC
  set y : ℝ → ℝ := fun s => ‖pathExt x s - pathExt x' s‖ with hy
  have hyc : Continuous y := ((continuous_pathExt x).sub (continuous_pathExt x')).norm
  have hbx : Continuous fun s => b (pathExt x s) := hb.continuous.comp (continuous_pathExt x)
  have hbx' : Continuous fun s => b (pathExt x' s) := hb.continuous.comp (continuous_pathExt x')
  have hineq : ∀ t ∈ Icc (0 : ℝ) T, y t ≤ C + ∫ s in (0 : ℝ)..t, (K : ℝ) * y s := by
    intro t ht
    have e : pathExt x t - pathExt x' t = ((x₀ - x₀') + N (w ⟨t, ht⟩ - w' ⟨t, ht⟩)) +
        ∫ s in (0 : ℝ)..t, (b (pathExt x s) - b (pathExt x' s)) := by
      rw [pathExt_of_mem x ht, pathExt_of_mem x' ht, hx, hx',
        intervalIntegral.integral_sub (hbx.intervalIntegrable _ _) (hbx'.intervalIntegrable _ _),
        map_sub]
      abel
    simp only [hy]
    rw [e]
    have hn1 : ‖(x₀ - x₀') + N (w ⟨t, ht⟩ - w' ⟨t, ht⟩)‖ ≤ C := by
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      refine (N.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      simpa using (w - w').norm_coe_le_norm ⟨t, ht⟩
    have hn2 : ‖∫ s in (0 : ℝ)..t, (b (pathExt x s) - b (pathExt x' s))‖ ≤
        ∫ s in (0 : ℝ)..t, (K : ℝ) * y s := by
      refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
      refine intervalIntegral.integral_mono_on ht.1 ((hbx.sub hbx').norm.intervalIntegrable _ _)
        ((hyc.const_mul _).intervalIntegrable _ _) fun s _ => ?_
      have := hb.dist_le_mul (pathExt x s) (pathExt x' s)
      simpa [dist_eq_norm] using this
    exact (norm_add_le _ _).trans (add_le_add hn1 hn2)
  have hg := gronwall_const (a := 0) (b := T) K.coe_nonneg hyc.continuousOn hineq
  have hC0 : 0 ≤ C := by positivity
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun t => ?_
  have h1 := hg t t.2
  have h2 : y t = ‖(x - x') t‖ := by
    simp only [hy, pathExt_of_mem x t.2, pathExt_of_mem x' t.2, ContinuousMap.sub_apply]
  have h3 : Real.exp (K * (t - 0)) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.mpr (by nlinarith [t.2.2, K.coe_nonneg])
  rw [← h2]
  exact h1.trans (mul_le_mul_of_nonneg_left h3 hC0)

/-- The solution map is jointly Lipschitz in the initial point and the driving path. -/
@[tmio T, powerlib_foundation] theorem lipschitzWith_solMap_uncurry {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) :
    LipschitzWith ((1 + ‖N‖₊) * Real.toNNReal (Real.exp (K * T)))
      (fun p : E × C(Icc (0 : ℝ) T, F) => solMap b N p.1 p.2) :=
  LipschitzWith.of_dist_le_mul fun p q => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, coe_nnnorm,
      Real.coe_toNNReal _ (Real.exp_pos _).le]
    have h := norm_sub_le_of_solution₂ hb N (solMap_spec hb N p.1 p.2) (solMap_spec hb N q.1 q.2)
    have h1 : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
    have h2 : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
    have hN := norm_nonneg N
    have he := (Real.exp_pos (K * T)).le
    calc _ ≤ (‖p.1 - q.1‖ + ‖N‖ * ‖p.2 - q.2‖) * Real.exp (K * T) := h
      _ ≤ (‖p - q‖ + ‖N‖ * ‖p - q‖) * Real.exp (K * T) := by gcongr
      _ = (1 + ‖N‖) * Real.exp (K * T) * ‖p - q‖ := by ring

@[tmio T, powerlib_foundation] theorem continuous_solMap_uncurry {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) :
    Continuous (fun p : E × C(Icc (0 : ℝ) T, F) => solMap b N p.1 p.2) :=
  (lipschitzWith_solMap_uncurry hb N).continuous

/-- For `K` compact and `C` closed, the set of driving paths taking some initial point of `K`
into `C` is closed. -/
@[tmio T, powerlib_foundation] theorem isClosed_exists_solMap_mem {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) {Kc : Set E} (hKc : IsCompact Kc)
    {C : Set C(Icc (0 : ℝ) T, E)} (hC : IsClosed C) :
    IsClosed {w : C(Icc (0 : ℝ) T, F) | ∃ x₀ ∈ Kc, solMap b N x₀ w ∈ C} := by
  have := isCompact_iff_compactSpace.mp hKc
  have hc : Continuous fun p : Kc × C(Icc (0 : ℝ) T, F) => solMap b N (p.1 : E) p.2 :=
    (continuous_solMap_uncurry hb N).comp (continuous_subtype_val.prodMap continuous_id)
  have h := isClosedMap_snd_of_compactSpace _ (hC.preimage hc)
  convert h using 1
  ext w
  constructor
  · rintro ⟨x₀, hx₀, hw⟩
    exact ⟨(⟨x₀, hx₀⟩, w), hw, rfl⟩
  · rintro ⟨⟨x, w'⟩, h', rfl⟩
    exact ⟨x, x.2, h'⟩

variable [MeasurableSpace C(Icc (0 : ℝ) T, F)] [OpensMeasurableSpace C(Icc (0 : ℝ) T, F)]

/-- **Uniform upper bound over a compact set of initial points**: for every set `A` of paths,
`limsup s log sup_{x₀ ∈ K} P(solMap x₀ w ∈ A) ≤ −inf_{x₀ ∈ K} inf_{cl A} J_{x₀}`. -/
@[tmio T, powerlib_foundation] theorem IsLDP.limsup_iSup_solMap_le {ι : Type*} {l : Filter ι}
    {s : ι → ℝ} (hs : ∀ᶠ i in l, 0 ≤ s i) {μ : ι → Measure C(Icc (0 : ℝ) T, F)}
    {I : C(Icc (0 : ℝ) T, F) → ℝ≥0∞} (h : IsLDP l s μ I) {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) {Kc : Set E} (hKc : IsCompact Kc)
    (A : Set C(Icc (0 : ℝ) T, E)) :
    limsup (fun i => (s i : EReal) * ENNReal.log (⨆ x₀ ∈ Kc, μ i (solMap b N x₀ ⁻¹' A))) l ≤
      -(⨅ x₀ ∈ Kc, ⨅ φ ∈ closure A, ((pushRate (solMap b N x₀) I φ : ℝ≥0∞) : EReal)) := by
  set FK := {w : C(Icc (0 : ℝ) T, F) | ∃ x₀ ∈ Kc, solMap b N x₀ w ∈ closure A} with hFK
  have hFKc : IsClosed FK := isClosed_exists_solMap_mem hb N hKc isClosed_closure
  have hbd : ∀ i, ⨆ x₀ ∈ Kc, μ i (solMap b N x₀ ⁻¹' A) ≤ μ i FK := fun i =>
    iSup₂_le fun x₀ hx₀ => measure_mono fun w hw => ⟨x₀, hx₀, subset_closure hw⟩
  have h1 : limsup (fun i => (s i : EReal) * ENNReal.log
        (⨆ x₀ ∈ Kc, μ i (solMap b N x₀ ⁻¹' A))) l ≤
      limsup (fun i => (s i : EReal) * ENNReal.log (μ i FK)) l := by
    refine limsup_le_limsup ?_
    filter_upwards [hs] with i hi
    exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log (hbd i)) (by exact_mod_cast hi)
  refine h1.trans ((h.2.1 FK hFKc.measurableSet).trans (EReal.neg_le_neg_iff.mpr ?_))
  rw [hFKc.closure_eq]
  refine le_iInf₂ fun w hw => ?_
  obtain ⟨x₀, hx₀, hwA⟩ := hw
  exact iInf₂_le_of_le x₀ hx₀ (iInf₂_le_of_le _ hwA
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (pushRate_le _ I w)))

/-- **Uniform lower bound over a compact set of initial points**: for every open set `G` of
paths, `liminf s log inf_{x₀ ∈ K} P(solMap x₀ w ∈ G) ≥ −sup_{x₀ ∈ K} inf_G J_{x₀}` (finitely many
balls of driving paths cover `K` by joint continuity of the solution map). -/
@[tmio T, powerlib_foundation] theorem IsLDP.le_liminf_iInf_solMap {ι : Type*} {l : Filter ι}
    {s : ι → ℝ} (hs : ∀ᶠ i in l, 0 ≤ s i) {μ : ι → Measure C(Icc (0 : ℝ) T, F)}
    {I : C(Icc (0 : ℝ) T, F) → ℝ≥0∞} (h : IsLDP l s μ I) {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) {Kc : Set E} (hKc : IsCompact Kc)
    {G : Set C(Icc (0 : ℝ) T, E)} (hG : IsOpen G) :
    -(((⨆ x₀ ∈ Kc, ⨅ φ ∈ G, pushRate (solMap b N x₀) I φ : ℝ≥0∞)) : EReal) ≤
      liminf (fun i => (s i : EReal) * ENNReal.log (⨅ x₀ ∈ Kc, μ i (solMap b N x₀ ⁻¹' G))) l := by
  set a := ⨆ x₀ ∈ Kc, ⨅ φ ∈ G, pushRate (solMap b N x₀) I φ with ha
  have core : ∀ β : ℝ≥0∞, a < β → -(β : EReal) ≤
      liminf (fun i => (s i : EReal) * ENNReal.log (⨅ x₀ ∈ Kc, μ i (solMap b N x₀ ⁻¹' G))) l := by
    intro β haβ
    rcases Kc.eq_empty_or_nonempty with hK | hK
    · refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hs] with i hi
      have h0 : (0 : EReal) ≤
          (s i : EReal) * ENNReal.log (⨅ x₀ ∈ Kc, μ i (solMap b N x₀ ⁻¹' G)) := by
        rw [hK]
        simp only [mem_empty_iff_false, not_false_eq_true, iInf_neg, iInf_top, ENNReal.log_top]
        exact mul_nonneg (by exact_mod_cast hi) le_top
      have hβ0 : -(β : EReal) ≤ 0 := by
        have := EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_nonneg β)
        rwa [neg_zero] at this
      exact hβ0.trans h0
    -- a driving path of rate `< β` for each initial point
    have hpt : ∀ x ∈ Kc, ∃ w, solMap b N x w ∈ G ∧ I w < β := by
      intro x hx
      have h1 : ⨅ φ ∈ G, pushRate (solMap b N x) I φ < β :=
        lt_of_le_of_lt (le_iSup₂ (f := fun x _ => ⨅ φ ∈ G, pushRate (solMap b N x) I φ) x hx) haβ
      obtain ⟨φ, h2⟩ := iInf_lt_iff.mp h1
      obtain ⟨hφ, h3⟩ := iInf_lt_iff.mp h2
      obtain ⟨w, h4⟩ := iInf_lt_iff.mp h3
      obtain ⟨hw, h5⟩ := iInf_lt_iff.mp h4
      exact ⟨w, hw ▸ hφ, h5⟩
    choose! W hWG hWI using hpt
    have hrad : ∀ x ∈ Kc, ∃ r > 0, ∀ y w', dist y x < r → dist w' (W x) < r →
        solMap b N y w' ∈ G := by
      intro x hx
      have hopen := hG.preimage (continuous_solMap_uncurry hb N)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (x, W x) (hWG x hx)
      refine ⟨r, hr, fun y w' hy hw' => ?_⟩
      have hmem : (y, w') ∈ Metric.ball (x, W x) r := by
        rw [Metric.mem_ball, Prod.dist_eq]
        exact max_lt hy hw'
      exact hball hmem
    choose! R hR hRG using hrad
    obtain ⟨t, htK, htfin, hcover⟩ := hKc.elim_finite_subcover_image
      (b := Kc) (c := fun x => Metric.ball x (R x)) (fun x _ => Metric.isOpen_ball)
      (fun y hy => mem_biUnion hy (Metric.mem_ball_self (hR y hy)))
    have htne : t.Nonempty := by
      obtain ⟨y, hy⟩ := hK
      obtain ⟨x, hx, -⟩ := mem_iUnion₂.mp (hcover hy)
      exact ⟨x, hx⟩
    -- the lower bound on each ball of driving paths
    have hball : ∀ x ∈ Kc, -(β : EReal) <
        liminf (fun i => (s i : EReal) * ENNReal.log (μ i (Metric.ball (W x) (R x)))) l := by
      intro x hx
      have h1 := h.2.2 (Metric.ball (W x) (R x)) measurableSet_ball
      rw [Metric.isOpen_ball.interior_eq] at h1
      refine lt_of_lt_of_le ?_ h1
      have h2 : (⨅ w ∈ Metric.ball (W x) (R x), ((I w : ℝ≥0∞) : EReal)) ≤ (I (W x) : EReal) :=
        iInf₂_le (W x) (Metric.mem_ball_self (hR x hx))
      have h3 : ((I (W x) : ℝ≥0∞) : EReal) < (β : EReal) :=
        EReal.coe_ennreal_lt_coe_ennreal_iff.mpr (hWI x hx)
      exact EReal.neg_lt_neg_iff.mpr (lt_of_le_of_lt h2 h3)
    have hev : ∀ᶠ i in l, ∀ x ∈ t, -(β : EReal) <
        (s i : EReal) * ENNReal.log (μ i (Metric.ball (W x) (R x))) :=
      (eventually_all_finite htfin).mpr fun x hx =>
        eventually_lt_of_lt_liminf (hball x (htK hx))
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hev, hs] with i hi hsi
    obtain ⟨x', hx', hmin⟩ := t.exists_min_image (fun x => μ i (Metric.ball (W x) (R x)))
      htfin htne
    have hle : μ i (Metric.ball (W x') (R x')) ≤ ⨅ y ∈ Kc, μ i (solMap b N y ⁻¹' G) := by
      refine le_iInf₂ fun y hy => ?_
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hcover hy)
      exact (hmin x hx).trans (measure_mono fun w' hw' =>
        hRG x (htK hx) y w' (Metric.mem_ball.mp hyx) (Metric.mem_ball.mp hw'))
    exact (hi x' hx').le.trans
      (mul_le_mul_of_nonneg_left (ENNReal.log_le_log hle) (by exact_mod_cast hsi))
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hLc, hca⟩ := exists_between hcon
  have hc0 : 0 ≤ -c := by
    have h1 : -(a : EReal) ≤ 0 := by
      have := EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_nonneg a)
      rwa [neg_zero] at this
    have h2 : c ≤ 0 := (hca.trans_le h1).le
    exact EReal.neg_nonneg.mpr h2
  have hβ : (((-c).toENNReal : ℝ≥0∞) : EReal) = -c := EReal.coe_toENNReal hc0
  have haβ : a < (-c).toENNReal := by
    rw [← EReal.coe_ennreal_lt_coe_ennreal_iff, hβ]
    exact EReal.lt_neg_comm.mp hca
  have h1 := core _ haβ
  rw [hβ, neg_neg] at h1
  exact lt_irrefl _ (h1.trans_lt hLc)

end powerlib.Stochastic.LDP
