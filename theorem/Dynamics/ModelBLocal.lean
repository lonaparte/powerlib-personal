import theorem.Dynamics.Basin

/-! # Local tools for fields that are singular or only locally regular

Generic foundation, independent of any model, written for GFL model B
(`theorem/GFL/ModelBStability.lean`, `theorem/GFL/ModelBBoundary.lean`), whose field contains
`1 / V_dc`. Model boundary: an arbitrary autonomous field `f : ℝⁿ → ℝⁿ` (continuous time, no
inputs), read through the Flow semantics of `theorem/Flow/Defs.lean` (solution segments, i.e.
Mathlib integral curves on `[t₀, t₁]`). No global regularity of `f` is assumed.

Results.
* `locallyExponentiallyStable_of_collapse`: if the flow collapses onto a coordinate plane
  `y_k = 0` through `x` (`2 y_k f_k(y) ≤ −a` off the plane, `f_k ≠ 0` on it, the other components
  bounded), then `x` satisfies the segment-based local exponential estimate, even when it is not an
  equilibrium: solution segments near `x` cannot cross the plane and last only `O(y_k(t₀)²)`.
  This is the semantics of `LocallyExponentiallyStable` (LeanForControl), which constrains
  existing segments and does not assert existence.
* `unstable_of_repel`: if instead the flow is repelled from the plane (`2 y_k f_k(y) ≥ a` off it)
  and agrees on every half ball `{y_k ≥ s}` with a `C¹` field, `x` is unstable: the solution from
  `x + s e_k` exists while it stays near `x` (globally Lipschitz cutoff of the `C¹` field, first
  exit `forall_lt_of_first_exit`), and there `y_k²` grows linearly.
* `unstable_of_cone`: instability from a cone `{σ y_k > 0, W ≥ 0}` at the plane that the field
  enters through its boundary and in which `σ y_k` grows at a positive rate (the degenerate case of
  the plane where the power term vanishes at `x`); helpers `deriv_nonpos_of_isMinOn_right`,
  `exists_pos_of_hasDerivAt`.
* `locallyExponentiallyStable_of_spiral`: spiral collapse. If off the plane `y_k f_k = q` with a
  `C¹` function `q`, `q(x) = 0`, `dq/dt = g + h q / y_k`, and `h(x)² + 4 g(x) < 0`, while on the
  plane `f_k ≠ 0`, then `x` satisfies the local exponential estimate: in the time `dτ = dt / y_k`
  the pair `(y_k, q)` is a linear focus; the function `spiralLyap` (radius times
  `exp(σ K angle)`) decreases at a uniform rate (`hasDerivWithinAt_spiralLyap`, algebra
  `spiral_ineq`), a segment can touch the plane only where `q = 0` (`q_eq_zero_of_touch`) and
  hence only at its end, and segments last `O(‖y(t₀) − x‖)`.
* `localAsymptoticStable_of_eqOn_ball`: local asymptotic stability depends only on the field on a
  ball (first-exit argument), complementing the ball-locality lemmas of
  `theorem/GFL/ModelBStability.lean`.
* `localAsymptoticStable_of_lie_neg`: a `C¹` function, positive on a punctured ball and strictly
  decreasing along a field continuous on that ball, gives local asymptotic stability. Unlike
  LeanForControl's `lyapunov_local_asymptotic_stable` no global sublevel set has to be compact
  (the Lyapunov stability part is LeanForControl's `lyapunov_stable`; attractivity is the standard
  uniform-decay argument on a compact annulus, through `antitoneOn_V_add_linear`).
* `norm_sub_smul_single_le`, `norm_le_norm_sub_smul_single_add`: norm bounds for the projection
  removing one coordinate.

Source: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.1 (local Lyapunov theorem); the collapse
estimate is new (it answers the `V_dc* = 0` question of `theorem/GFL/ModelBStability.lean`).

## Family and connection conclusions
None: this module defines no family. All results are generic semantic implications (foundation);
model-specific conclusions are drawn in the GFL model-B modules.
-/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology

variable {n : ℕ}

/-- The coordinate projection killing the `k`-th coordinate does not increase the norm. -/
@[powerlib_foundation] theorem norm_sub_smul_single_le (k : Fin n) (v : State n) :
    ‖v - v k • EuclideanSpace.single k (1 : ℝ)‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = k
  · subst hi; simp [sq_nonneg]
  · simp [hi]

/-- A vector is bounded by its part off the `k`-th coordinate plus that coordinate. -/
@[powerlib_foundation] theorem norm_le_norm_sub_smul_single_add (k : Fin n) (v : State n) :
    ‖v‖ ≤ ‖v - v k • EuclideanSpace.single k (1 : ℝ)‖ + |v k| := by
  have h := norm_add_le (v - v k • EuclideanSpace.single k (1 : ℝ))
    (v k • EuclideanSpace.single k (1 : ℝ))
  rw [sub_add_cancel, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs] at h
  exact h

/-- **Collapse onto a coordinate plane.** Let the point `x` lie on the plane `y_k = 0`. If near `x`
the field drives `y_k²` down at a uniform rate off the plane (`2 y_k f_k(y) ≤ −a`), crosses the
plane transversally on it (`f_k(y) ≠ 0` where `y_k = 0`), and has bounded components off `k`, then
`x` satisfies the segment-based local exponential estimate — whether or not `x` is an equilibrium.
Every solution segment starting near `x` stays off the plane except possibly at its end, so it
lasts at most `y_k(t₀)² / a`, and over that time it moves by `O(‖y(t₀) − x‖²)`; the estimate
holds with `C = 4` and rate `1`. The field need not be continuous on the plane. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_collapse
    {f : State n → State n} {x : State n} (k : Fin n) (hxk : x k = 0) {ρ a M : ℝ}
    (hρ : 0 < ρ) (ha : 0 < a)
    (hcol : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → 2 * y k * f y k ≤ -a)
    (hplane : ∀ y : State n, ‖y - x‖ < ρ → y k = 0 → f y k ≠ 0)
    (hbound : ∀ y : State n, ‖y - x‖ < ρ →
      ‖f y - f y k • EuclideanSpace.single k (1 : ℝ)‖ ≤ M) :
    LocallyExponentiallyStable f x := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound x (by simpa using hρ))
  set P : State n →L[ℝ] State n := ContinuousLinearMap.id ℝ (State n) -
    (EuclideanSpace.proj k : State n →L[ℝ] ℝ).smulRight (EuclideanSpace.single k (1 : ℝ))
    with hPdef
  have hP : ∀ v, P v = v - v k • EuclideanSpace.single k (1 : ℝ) := fun v => by
    simp [hPdef]
  set r := min (ρ / 8) (min 1 (2 * a / (M + 4))) with hr
  have hr0 : 0 < r := lt_min (by positivity) (lt_min one_pos (by positivity))
  refine ⟨r, 4, 1, hr0, by norm_num, one_pos, ?_⟩
  intro t₀ t₁ φ hφ h0
  set δ := ‖φ t₀ - x‖ with hδ
  have hδρ : δ < ρ / 8 := lt_of_lt_of_le h0 (min_le_left _ _)
  have hδ1 : δ < 1 := lt_of_lt_of_le h0 ((min_le_right _ _).trans (min_le_left _ _))
  have hδa : δ < 2 * a / (M + 4) := lt_of_lt_of_le h0 ((min_le_right _ _).trans (min_le_right _ _))
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hk0 : |φ t₀ k| ≤ δ := by
    have := PiLp.norm_apply_le (φ t₀ - x) k
    simpa [hxk] using this
  -- analysis of a segment staying in the ball
  have key : ∀ s ∈ Icc t₀ t₁, (∀ u ∈ Icc t₀ s, ‖φ u - x‖ < ρ) →
      a * (s - t₀) ≤ δ ^ 2 ∧ ∀ t ∈ Icc t₀ s, ‖φ t - x‖ ≤ 2 * δ + M * (t - t₀) := by
    intro s hs hin
    have hseg : IsTrajectoryOn φ f t₀ s := hφ.mono (Icc_subset_Icc le_rfl hs.2)
    have hdk : ∀ t ∈ Icc t₀ s, HasDerivWithinAt (fun t => (φ t k : ℝ)) (f (φ t) k : ℝ)
        (Icc t₀ s) t :=
      fun t ht => (EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
        (hseg t ht)
    have hdu : ∀ t ∈ Icc t₀ s, HasDerivWithinAt (fun t => φ t k ^ 2)
        (2 * φ t k * f (φ t) k) (Icc t₀ s) t := fun t ht => by
      have := (hdk t ht).fun_pow 2
      convert this using 1
      push_cast
      ring
    have hint : interior (Icc t₀ s) = Ioo t₀ s := interior_Icc
    have hdu' : ∀ t ∈ interior (Icc t₀ s), HasDerivWithinAt (fun t => φ t k ^ 2)
        (2 * φ t k * f (φ t) k) (interior (Icc t₀ s)) t := fun t ht => by
      rw [hint] at ht ⊢
      exact ((hdu t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt
    have hcont : ContinuousOn (fun t => φ t k ^ 2) (Icc t₀ s) :=
      fun t ht => (hdu t ht).continuousWithinAt
    have hsign : ∀ t ∈ Icc t₀ s, 2 * φ t k * f (φ t) k ≤ 0 := fun t ht => by
      by_cases h : φ t k = 0
      · simp [h]
      · linarith [hcol _ (hin t ht) h]
    have hanti : AntitoneOn (fun t => φ t k ^ 2) (Icc t₀ s) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcont hdu'
        (fun t ht => hsign t (interior_subset ht))
    -- the coordinate does not vanish before `s`
    have hne : ∀ τ ∈ Ico t₀ s, φ τ k ≠ 0 := by
      intro τ hτ hz
      have hzero : ∀ t ∈ Icc τ s, φ t k = 0 := fun t ht => by
        have h1 := hanti ⟨hτ.1, hτ.2.le⟩ ⟨hτ.1.trans ht.1, ht.2⟩ ht.1
        simp only [hz] at h1
        have : φ t k ^ 2 = 0 := le_antisymm (by simpa using h1) (sq_nonneg _)
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      have hd1 : HasDerivWithinAt (fun t => φ t k) (f (φ τ) k) (Icc τ s) τ :=
        (hdk τ (Ico_subset_Icc_self hτ)).mono (Icc_subset_Icc hτ.1 le_rfl)
      have hd2 : HasDerivWithinAt (fun t => φ t k) 0 (Icc τ s) τ :=
        (hasDerivWithinAt_const τ (Icc τ s) (0 : ℝ)).congr (fun t ht => hzero t ht)
          (hzero τ ⟨le_rfl, hτ.2.le⟩)
      have heq := (uniqueDiffOn_Icc hτ.2 τ ⟨le_rfl, hτ.2.le⟩).eq_deriv _ hd1 hd2
      exact hplane _ (hin τ (Ico_subset_Icc_self hτ)) hz heq
    -- the rate along the segment
    have hanti2 : AntitoneOn (fun t => φ t k ^ 2 + a * t) (Icc t₀ s) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => 2 * φ t k * f (φ t) k + a)
        (convex_Icc _ _) (hcont.add (continuous_const.mul continuous_id).continuousOn)
        (fun t ht => (hdu' t ht).add ((hasDerivWithinAt_id t _).const_mul a |>.congr_deriv
          (by ring))) (fun t ht => ?_)
      rw [hint] at ht
      linarith [hcol _ (hin t (Ioo_subset_Icc_self ht))
        (hne t ⟨ht.1.le, ht.2⟩)]
    have hrate : a * (s - t₀) ≤ δ ^ 2 := by
      have h1 := hanti2 ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
      simp only at h1
      have h2 : φ t₀ k ^ 2 ≤ δ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hk0 2
      nlinarith [sq_nonneg (φ s k)]
    refine ⟨hrate, fun t ht => ?_⟩
    -- the coordinates off `k`
    have hdP : ∀ u ∈ Icc t₀ s, HasDerivWithinAt (fun u => P (φ u)) (P (f (φ u))) (Icc t₀ s) u :=
      fun u hu => P.hasFDerivAt.comp_hasDerivWithinAt u (hseg u hu)
    have hPb := norm_image_sub_le_of_norm_deriv_le_segment' hdP (fun u hu => by
      rw [hP]; exact hbound _ (hin u (Ico_subset_Icc_self hu))) t ht
    have hkt : |φ t k| ≤ |φ t₀ k| := by
      have h1 := hanti ⟨le_rfl, hs.1⟩ ht ht.1
      exact sq_le_sq.mp h1
    have hsplit := norm_le_norm_sub_smul_single_add k (φ t - x)
    rw [← hP] at hsplit
    have hPx : P (φ t - x) = (P (φ t) - P (φ t₀)) + P (φ t₀ - x) := by
      simp only [map_sub]; abel
    have hP0 : ‖P (φ t₀ - x)‖ ≤ δ := by rw [hP]; exact norm_sub_smul_single_le k _
    have hkx : (φ t - x) k = φ t k := by simp [hxk]
    rw [hPx, hkx] at hsplit
    have := norm_add_le (P (φ t) - P (φ t₀)) (P (φ t₀ - x))
    linarith
  have hδMa : δ * (M + 4) ≤ 2 * a := by
    rw [lt_div_iff₀ (by positivity)] at hδa; linarith
  have hdrift : ∀ s, t₀ ≤ s → a * (s - t₀) ≤ δ ^ 2 → M * (s - t₀) ≤ 2 * δ := by
    intro s hst hrate
    have hst' : 0 ≤ s - t₀ := by linarith
    have : a * (M * (s - t₀)) ≤ a * (2 * δ) := by nlinarith
    exact le_of_mul_le_mul_left this ha
  intro t ht
  have ht₁ : t₀ ≤ t₁ := ht.1.trans ht.2
  -- the solution stays in the ball of radius `ρ / 2`
  have hstay : ∀ u ∈ Icc t₀ t₁, ‖φ u - x‖ < ρ / 2 := by
    intro u hu
    by_contra hfar
    push Not at hfar
    obtain ⟨τ, hτ, hτeq, hτin⟩ := exists_first_sphere_hit hφ.continuousOn
      (show ‖φ t₀ - x‖ < ρ / 2 by linarith) hu hfar
    obtain ⟨hrate, hb⟩ := key τ hτ (fun v hv => lt_of_le_of_lt (hτin v hv) (by linarith))
    have h1 := hb τ ⟨hτ.1, le_rfl⟩
    have h2 := hdrift τ hτ.1 hrate
    linarith
  obtain ⟨hrate, hb⟩ := key t₁ ⟨ht₁, le_rfl⟩
    (fun u hu => lt_of_lt_of_le (hstay u hu) (by linarith))
  have h1 := hb t ht
  -- `2δ + M τ ≤ 4 e^{-τ} δ` for `τ = t - t₀ ≤ δ² / a`
  have hτ0 : 0 ≤ t - t₀ := by linarith [ht.1]
  have hτrate : a * (t - t₀) ≤ δ ^ 2 := by nlinarith [ht.2]
  have hexp : 1 - (t - t₀) ≤ Real.exp (-1 * (t - t₀)) := by
    have := Real.add_one_le_exp (-1 * (t - t₀)); linarith
  have hkey : (t - t₀) * (M + 4 * δ) ≤ 2 * δ := by
    have : a * ((t - t₀) * (M + 4 * δ)) ≤ a * (2 * δ) := by nlinarith
    exact le_of_mul_le_mul_left this ha
  calc ‖φ t - x‖ ≤ 2 * δ + M * (t - t₀) := h1
    _ ≤ 4 * (1 - (t - t₀)) * δ := by nlinarith
    _ ≤ 4 * Real.exp (-1 * (t - t₀)) * δ := by
        have := mul_le_mul_of_nonneg_right hexp hδ0; nlinarith

/-- Local asymptotic stability only depends on the field on a ball around the point. -/
@[powerlib_foundation] theorem localAsymptoticStable_of_eqOn_ball {f g : State n → State n} {x : State n} {R : ℝ}
    (hR : 0 < R) (hfg : ∀ y, ‖y - x‖ < R → f y = g y) (hg : LocalAsymptoticStable g x) :
    LocalAsymptoticStable f x := by
  obtain ⟨hgs, c, hc, hconv⟩ := hg
  have hfs : LyapunovStable f x := by
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := hgs (min ε (R / 2)) (lt_min hε (by positivity))
    refine ⟨min δ (min ε (R / 2)), lt_min hδ (lt_min hε (by positivity)), ?_⟩
    intro t₀ t₁ φ hφ h0
    have h0' : ‖φ t₀ - x‖ < min ε (R / 2) := lt_of_lt_of_le h0 (min_le_right _ _)
    intro t ht
    by_contra hfar
    push Not at hfar
    have hfar' : min ε (R / 2) ≤ ‖φ t - x‖ := (min_le_left _ _).trans hfar
    obtain ⟨τ, hτ, hτeq, hτin⟩ := exists_first_sphere_hit hφ.continuousOn h0' ht hfar'
    have hseg : IsTrajectoryOn φ g t₀ τ :=
      isIntegralCurveOn_of_eq_on_curve (hφ.mono (Icc_subset_Icc le_rfl hτ.2))
        (fun u hu => hfg _ (lt_of_le_of_lt (hτin u hu)
          (lt_of_le_of_lt (min_le_right _ _) (by linarith))))
    have := hb t₀ τ φ hseg (lt_of_lt_of_le h0 (min_le_left _ _)) τ ⟨hτ.1, le_rfl⟩
    linarith
  refine ⟨hfs, ?_⟩
  obtain ⟨δ, hδ, hb⟩ := hfs (R / 2) (by positivity)
  refine ⟨min c δ, lt_min hc hδ, fun t₀ φ hφ h0 => ?_⟩
  have hin : ∀ t ∈ Ici t₀, ‖φ t - x‖ < R / 2 := fun t ht =>
    hb t₀ t φ (hφ.mono Icc_subset_Ici_self) (lt_of_lt_of_le h0 (min_le_right _ _)) t
      ⟨ht, le_rfl⟩
  refine hconv t₀ φ (isIntegralCurveOn_of_eq_on_curve hφ fun t ht => ?_)
    (lt_of_lt_of_le h0 (min_le_left _ _))
  exact hfg _ (by linarith [hin t ht])

/-- **Local strict Lyapunov function.** A `C¹` function that vanishes at the point, is positive on
a punctured ball around it and strictly decreases along a field continuous on that ball makes the
point locally asymptotically stable. No hypothesis is made on the field outside the ball, and no
global sublevel set needs to be compact. -/
@[powerlib_foundation] theorem localAsymptoticStable_of_lie_neg (hn : 0 < n) {f : State n → State n} {x : State n}
    {V : State n → ℝ} {R : ℝ} (hR : 0 < R) (hV : ContDiff ℝ 1 V)
    (hf : ContinuousOn f (Metric.ball x R)) (hV0 : V x = 0)
    (hpos : ∀ y, ‖y - x‖ < R → y ≠ x → 0 < V y)
    (hLie : ∀ y, ‖y - x‖ < R → y ≠ x → fderiv ℝ V y (f y) < 0) :
    LocalAsymptoticStable f x := by
  have hVd : Differentiable ℝ V := hV.differentiable one_ne_zero
  have hmin : IsLocalMin V x := by
    filter_upwards [Metric.ball_mem_nhds x hR] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    rcases eq_or_ne y x with rfl | hne
    · exact le_rfl
    · rw [hV0]; exact (hpos y hy hne).le
  have hfd0 : fderiv ℝ V x = 0 := hmin.fderiv_eq_zero
  have hLS : LyapunovStable f x := by
    refine lyapunov_stable (D := Metric.ball x R) hn
      ⟨Metric.isOpen_ball, Metric.mem_ball_self hR, hV.continuous, hVd, hV0,
        fun y hy hne => hpos y (by rwa [Metric.mem_ball, dist_eq_norm] at hy) hne,
        fun y hy => ?_⟩
    rcases eq_or_ne y x with rfl | hne
    · rw [hfd0]; simp
    · exact (hLie y (by rwa [Metric.mem_ball, dist_eq_norm] at hy) hne).le
  refine ⟨hLS, ?_⟩
  obtain ⟨δ, hδ, hb⟩ := hLS (R / 2) (by positivity)
  refine ⟨δ, hδ, fun t₀ φ hφ h0 => ?_⟩
  have hin : ∀ t, t₀ ≤ t → ‖φ t - x‖ < R / 2 := fun t ht =>
    hb t₀ t φ (hφ.mono Icc_subset_Ici_self) h0 t ⟨ht, le_rfl⟩
  have hLc : ContinuousOn (fun y => fderiv ℝ V y (f y)) (Metric.ball x R) :=
    ((hV.continuous_fderiv one_ne_zero).continuousOn).clm_apply hf
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δη, hδη, hbη⟩ := hLS η hη
  -- the solution enters the ball of radius `δη`
  have henter : ∃ T, t₀ ≤ T ∧ ‖φ T - x‖ < δη := by
    by_contra hno
    push Not at hno
    set K := {y : State n | δη ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ R / 2} with hK
    have hKc : IsCompact K := by
      refine (isCompact_closedBall x (R / 2)).of_isClosed_subset ?_ fun y hy => ?_
      · exact (isClosed_le continuous_const (continuous_norm.comp (continuous_sub_right x))).inter
          (isClosed_le (continuous_norm.comp (continuous_sub_right x)) continuous_const)
      · rw [Metric.mem_closedBall, dist_eq_norm]; exact hy.2
    have hKR : K ⊆ Metric.ball x R := fun y hy => by
      rw [Metric.mem_ball, dist_eq_norm]; linarith [hy.2]
    have hφK : ∀ t, t₀ ≤ t → φ t ∈ K := fun t ht => ⟨hno t ht, (hin t ht).le⟩
    obtain ⟨ym, hymK, hmax⟩ := hKc.exists_isMaxOn ⟨φ t₀, hφK t₀ le_rfl⟩ (hLc.mono hKR)
    have hym0 : ym ≠ x := fun h => by
      have := hymK.1; rw [h, sub_self, norm_zero] at this; linarith
    have hγ : fderiv ℝ V ym (f ym) < 0 := hLie ym (by linarith [hymK.2]) hym0
    set γ := -fderiv ℝ V ym (f ym) with hγdef
    have hγ0 : 0 < γ := by linarith
    have hanti := antitoneOn_V_add_linear (c := γ) hVd hV.continuous (convex_Ici t₀) hφ
      (fun t ht => by
        have := hmax (hφK t (interior_subset ht))
        simp only [Set.mem_ofPred_eq] at this
        linarith)
    set T := t₀ + V (φ t₀) / γ + 1 with hT
    have hVφ0 : 0 ≤ V (φ t₀) := by
      rcases eq_or_ne (φ t₀) x with h | h
      · rw [h, hV0]
      · exact (hpos _ (by linarith [hin t₀ le_rfl]) h).le
    have hT0 : t₀ ≤ T := by
      have : 0 ≤ V (φ t₀) / γ := div_nonneg hVφ0 hγ0.le
      linarith
    have h1 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT0) hT0
    simp only at h1
    have hVT : 0 ≤ V (φ T) := by
      rcases eq_or_ne (φ T) x with h | h
      · rw [h, hV0]
      · exact (hpos _ (by linarith [hin T hT0]) h).le
    have : γ * T = γ * t₀ + V (φ t₀) + γ := by
      rw [hT, mul_add, mul_add, mul_div_cancel₀ _ hγ0.ne', mul_one]
    linarith
  obtain ⟨T, hT, hTδ⟩ := henter
  refine ⟨T, fun t ht => ?_⟩
  rw [dist_eq_norm]
  exact hbη T t φ (hφ.mono fun u hu => le_trans hT hu.1) hTδ t ⟨ht, le_rfl⟩

/-- First-exit argument for a continuous function of a curve: if `Φ ∘ φ` starts below `c` and is
below `c` at every `s` up to which it has stayed at most `c`, it stays below `c`. -/
@[powerlib_foundation] theorem forall_lt_of_first_exit {E : Type*} [TopologicalSpace E] {φ : ℝ → E} {Φ : E → ℝ}
    {t₀ t₁ c : ℝ} (hΦ : Continuous Φ) (hφ : ContinuousOn φ (Icc t₀ t₁)) (h0 : Φ (φ t₀) < c)
    (hstep : ∀ s ∈ Icc t₀ t₁, (∀ u ∈ Icc t₀ s, Φ (φ u) ≤ c) → Φ (φ s) < c) :
    ∀ u ∈ Icc t₀ t₁, Φ (φ u) < c := by
  have hψ : ContinuousOn (fun t => Φ (φ t)) (Icc t₀ t₁) := hΦ.comp_continuousOn hφ
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu, hu'⟩ := hcon
  set A : Set ℝ := Icc t₀ t₁ ∩ (fun t => Φ (φ t)) ⁻¹' {y | c ≤ y} with hAdef
  have hAne : A.Nonempty := ⟨u, hu, hu'⟩
  have hAclosed : IsClosed A :=
    hψ.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_le continuous_const continuous_id)
  have hAbdd : BddBelow A := ⟨t₀, fun t ht => ht.1.1⟩
  have hτA : sInf A ∈ A := hAclosed.csInf_mem hAne hAbdd
  have hbelow : ∀ t ∈ Ico t₀ (sInf A), Φ (φ t) < c := by
    intro t ht
    by_contra h
    push Not at h
    have : sInf A ≤ t := csInf_le hAbdd ⟨⟨ht.1, ht.2.le.trans hτA.1.2⟩, h⟩
    linarith [ht.2]
  have hle : ∀ t ∈ Icc t₀ (sInf A), Φ (φ t) ≤ c := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rcases eq_or_lt_of_le hτA.1.1 with h' | h'
      · rw [h, ← h']; exact h0.le
      · have hcl : IsClosed (Icc t₀ (sInf A) ∩ (fun t => Φ (φ t)) ⁻¹' {y | y ≤ c}) :=
          (hψ.mono (Icc_subset_Icc le_rfl hτA.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
            (isClosed_le continuous_id continuous_const)
        have hsub : Ico t₀ (sInf A) ⊆ Icc t₀ (sInf A) ∩ (fun t => Φ (φ t)) ⁻¹' {y | y ≤ c} :=
          fun t' ht' => ⟨Ico_subset_Icc_self ht', (hbelow t' ht').le⟩
        have hcl' := hcl.closure_subset_iff.mpr hsub
        rw [closure_Ico h'.ne] at hcl'
        exact (hcl' ht).2
    · exact (hbelow t ⟨ht.1, h⟩).le
  exact absurd hτA.2 (not_le.mpr (hstep _ hτA.1 hle))

/-- **Repulsion from a coordinate plane.** Let `x` lie on the plane `y_k = 0`. If near `x` the
field drives `y_k²` up at a uniform rate off the plane (`2 y_k f_k(y) ≥ a`), and on each half
ball `{y_k ≥ s}` (`s > 0`) it agrees with a `C¹` field, then `x` is unstable: the solution from
`x + s e_k` exists as long as it stays near `x`, and there `y_k²` grows without bound. -/
@[powerlib_foundation] theorem unstable_of_repel {f : State n → State n} {x : State n} (k : Fin n) (hxk : x k = 0)
    {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    (hrep : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → a ≤ 2 * y k * f y k)
    (hext : ∀ s > 0, ∃ g : State n → State n, ContDiff ℝ 1 g ∧
      ∀ y : State n, ‖y - x‖ < ρ → s ≤ y k → g y = f y) :
    Unstable f x := by
  intro hLS
  obtain ⟨δ, hδ, hb⟩ := hLS (ρ / 2) (by positivity)
  set s := min (δ / 2) (ρ / 4) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsρ : s ≤ ρ / 4 := min_le_right _ _
  obtain ⟨g, hg, hgf⟩ := hext (s / 2) (by positivity)
  obtain ⟨G, hG, ⟨K, hGlip⟩, hGg⟩ := exists_contDiff_lipschitz_extension hg (‖x‖ + ρ)
  set y₀ : State n := x + s • EuclideanSpace.single k (1 : ℝ) with hy₀
  obtain ⟨ψ, hψ0, hψ⟩ := Flow.forwardComplete_of_lipschitzWith hGlip 0 y₀
  have hy₀x : ‖y₀ - x‖ = s := by
    rw [hy₀, add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_of_pos hs0]
  have hy₀k : y₀ k = s := by simp [hy₀, hxk]
  -- the region where `G = f`
  have hGf : ∀ y : State n, ‖y - x‖ < ρ → s / 2 ≤ y k → G y = f y := by
    intro y hy hyk
    rw [hGg y (by
      have := norm_le_norm_add_norm_sub' y x
      linarith)]
    exact hgf y hy hyk
  set Φ : State n → ℝ := fun y => max (‖y - x‖ - ρ / 2) (s / 2 - y k) with hΦ
  have hΦc : Continuous Φ :=
    ((continuous_norm.comp (continuous_sub_right x)).sub continuous_const).max
      (continuous_const.sub ((EuclideanSpace.proj k : State n →L[ℝ] ℝ).continuous))
  -- along any stretch in the region, `y_k² − a t` does not decrease
  have hgrow : ∀ T, 0 ≤ T → (∀ u ∈ Icc 0 T, Φ (ψ u) ≤ 0) →
      IsTrajectoryOn ψ f 0 T ∧ ∀ u ∈ Icc 0 T, ψ 0 k ^ 2 + a * u ≤ ψ u k ^ 2 := by
    intro T hT hin
    have hin' : ∀ u ∈ Icc 0 T, ‖ψ u - x‖ < ρ ∧ s / 2 ≤ ψ u k := fun u hu => by
      have h := hin u hu
      simp only [hΦ, max_le_iff, sub_nonpos] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hseg : IsTrajectoryOn ψ f 0 T :=
      isIntegralCurveOn_of_eq_on_curve (hψ.mono Icc_subset_Ici_self)
        (fun u hu => hGf _ (hin' u hu).1 (hin' u hu).2)
    refine ⟨hseg, ?_⟩
    have hdk : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => (ψ t k : ℝ)) (f (ψ t) k : ℝ)
        (Icc 0 T) t :=
      fun t ht => (EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
        (hseg t ht)
    have hmono : MonotoneOn (fun t => ψ t k ^ 2 - a * t) (Icc 0 T) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => 2 * ψ t k * f (ψ t) k - a)
        (convex_Icc _ _) ?_ (fun t ht => ?_) (fun t ht => ?_)
      · exact (fun t ht => ((hdk t ht).fun_pow 2).continuousWithinAt.sub
          (continuous_const.mul continuous_id).continuousWithinAt)
      · rw [interior_Icc] at ht
        have h1 := ((hdk t (Ioo_subset_Icc_self ht)).fun_pow 2).fun_sub
          ((hasDerivWithinAt_id t _).const_mul a)
        have h2 := (h1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt (s := interior (Icc 0 T))
        convert h2 using 1
        simp only [id]
        push_cast
        ring
      · rw [interior_Icc] at ht
        have hk : ψ t k ≠ 0 := by
          have := (hin' t (Ioo_subset_Icc_self ht)).2
          intro h; rw [h] at this; linarith
        linarith [hrep _ (hin' t (Ioo_subset_Icc_self ht)).1 hk]
    intro u hu
    have := hmono ⟨le_rfl, hT⟩ hu hu.1
    simp only [mul_zero, sub_zero] at this
    linarith
  -- the solution stays in the region
  have hstay : ∀ T, 0 ≤ T → ∀ u ∈ Icc 0 T, Φ (ψ u) < 0 := by
    intro T hT
    refine forall_lt_of_first_exit hΦc (hψ.continuousOn.mono Icc_subset_Ici_self) ?_ ?_
    · simp only [hΦ, hψ0, hy₀x, hy₀k, max_lt_iff]
      constructor <;> linarith
    · intro t ht hin
      obtain ⟨hseg, hsq⟩ := hgrow t ht.1 hin
      have h1 : ‖ψ t - x‖ < ρ / 2 :=
        hb 0 t ψ hseg (by rw [hψ0, hy₀x]; exact hsδ) t ⟨ht.1, le_rfl⟩
      have h2 : s ^ 2 ≤ ψ t k ^ 2 := by
        have := hsq t ⟨ht.1, le_rfl⟩
        rw [hψ0, hy₀k] at this
        nlinarith [ht.1]
      have h3 : s / 2 ≤ ψ t k := by
        have := hin t ⟨ht.1, le_rfl⟩
        simp only [hΦ, max_le_iff] at this
        linarith [this.2]
      have h4 : s ≤ ψ t k := by nlinarith
      simp only [hΦ, max_lt_iff]
      constructor <;> linarith
  -- but `y_k²` grows linearly while `|y_k| < ρ / 2`
  set T := ρ ^ 2 / a + 1 with hT
  have hT0 : 0 ≤ T := by positivity
  obtain ⟨-, hsq⟩ := hgrow T hT0 (fun u hu => (hstay T hT0 u hu).le)
  have hfin := hstay T hT0 T ⟨hT0, le_rfl⟩
  simp only [hΦ, max_lt_iff] at hfin
  have hk : |ψ T k| ≤ ‖ψ T - x‖ := by
    have := PiLp.norm_apply_le (ψ T - x) k
    simpa [hxk] using this
  have h1 := hsq T ⟨hT0, le_rfl⟩
  have h2 : ψ T k ^ 2 < ρ ^ 2 / 4 := by
    have h3 : |ψ T k| < ρ / 2 := by linarith [hfin.1]
    have := sq_lt_sq' (by linarith [abs_nonneg (ψ T k), neg_abs_le (ψ T k)]) (lt_of_le_of_lt (le_abs_self _) h3)
    nlinarith [sq_abs (ψ T k), abs_nonneg (ψ T k)]
  have h5 : a * T = ρ ^ 2 + a := by rw [hT]; field_simp
  nlinarith [sq_nonneg (ψ 0 k)]

/-- A function with derivative `d` within `[a, b]` at the right end `b`, where it is minimal on
`[a, b]`, has `d ≤ 0`. -/
@[powerlib_foundation] theorem deriv_nonpos_of_isMinOn_right {φ : ℝ → ℝ} {d a b : ℝ} (hab : a < b)
    (hd : HasDerivWithinAt φ d (Icc a b) b) (hmin : ∀ u ∈ Icc a b, φ b ≤ φ u) : d ≤ 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Icc_sdiff_right, nhdsWithin_Ico_eq_nhdsLT hab] at hd
  refine le_of_tendsto hd ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with u hu
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith [hmin u ⟨hu.1.le, hu.2.le⟩])
    (by linarith [hu.2])

/-- A function vanishing at `0` with positive derivative there is positive at some `t ∈ (0, ε)`. -/
@[powerlib_foundation] theorem exists_pos_of_hasDerivAt {ψ : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt ψ d 0) (h0 : ψ 0 = 0)
    (hpos : 0 < d) {ε : ℝ} (hε : 0 < ε) : ∃ t ∈ Ioo 0 ε, 0 < ψ t := by
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have h1 : Tendsto (slope ψ 0) (𝓝[>] 0) (𝓝 d) :=
    hd.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < slope ψ 0 t ∧ t < ε :=
    (h1.eventually (lt_mem_nhds hpos)).and (Ioo_mem_nhdsGT hε |> fun h =>
      Filter.mem_of_superset h fun t ht => ht.2)
  obtain ⟨t, ht, ht0⟩ := (h2.and self_mem_nhdsWithin).exists
  refine ⟨t, ⟨ht0, ht.2⟩, ?_⟩
  have := ht.1
  rw [slope_def_field, h0, sub_zero, sub_zero] at this
  exact (div_pos_iff_of_pos_right ht0).mp this

/-- **Instability from an invariant cone at a coordinate plane.** Let `x` lie on the plane
`y_k = 0`. Suppose that on one side `σ y_k > 0` (`σ = ±1`), near `x`, the sublevel `W ≥ 0` of a
`C¹` function `W` with `W x = 0` is a cone in which `σ y_k` grows at a rate `μ > 0`, the field
crosses its boundary `W = 0` inwards, some direction `v` points into the cone at `x`, and the field
agrees on every half ball `{σ y_k ≥ s}` with a `C¹` field. Then `x` is unstable: the solution from
a point of the cone close to `x` stays in it and leaves every small ball. -/
@[powerlib_foundation] theorem unstable_of_cone {f : State n → State n} {x : State n} (k : Fin n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) {W : State n → ℝ}
    (hW : ContDiff ℝ 1 W) (hxk : x k = 0) (hW0 : W x = 0)
    (hcone : ∀ y : State n, ‖y - x‖ < ρ → 0 < σ * y k → 0 ≤ W y → μ ≤ σ * f y k)
    (hbar : ∀ y : State n, ‖y - x‖ < ρ → 0 < σ * y k → W y = 0 →
      0 < fderiv ℝ W y (f y))
    (v : State n) (hv : 0 < σ * v k) (hWv : 0 < fderiv ℝ W x v)
    (hext : ∀ s > 0, ∃ g : State n → State n, ContDiff ℝ 1 g ∧
      ∀ y : State n, ‖y - x‖ < ρ → s ≤ σ * y k → g y = f y) :
    Unstable f x := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσa : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hWd : Differentiable ℝ W := hW.differentiable one_ne_zero
  intro hLS
  obtain ⟨δ, hδ, hb⟩ := hLS (ρ / 2) (by positivity)
  -- a seed in the cone
  set ε := min δ (ρ / 2) / (‖v‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hline : HasDerivAt (fun t : ℝ => W (x + t • v)) (fderiv ℝ W x v) 0 := by
    have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have h := (hWd (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [zero_smul, add_zero] at h
    exact h
  obtain ⟨t₀, ht₀, hWt₀⟩ := exists_pos_of_hasDerivAt hline (by simpa using hW0) hWv hε0
  set y₀ : State n := x + t₀ • v with hy₀
  have hy₀x : ‖y₀ - x‖ < min δ (ρ / 2) := by
    rw [hy₀, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht₀.1]
    have h1 : t₀ * ‖v‖ ≤ t₀ * (‖v‖ + 1) := by nlinarith [ht₀.1]
    have h2 : t₀ * (‖v‖ + 1) < ε * (‖v‖ + 1) := by
      have := ht₀.2; nlinarith [norm_nonneg v]
    have h3 : ε * (‖v‖ + 1) = min δ (ρ / 2) := by
      rw [hε]; field_simp
    linarith
  set s₀ := σ * y₀ k with hs₀
  have hs₀0 : 0 < s₀ := by
    simp only [hs₀, hy₀, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hxk, zero_add]
    nlinarith [ht₀.1]
  obtain ⟨g, hg, hgf⟩ := hext (s₀ / 2) (by positivity)
  obtain ⟨G, hG, ⟨K, hGlip⟩, hGg⟩ := exists_contDiff_lipschitz_extension hg (‖x‖ + ρ)
  obtain ⟨ψ, hψ0, hψ⟩ := Flow.forwardComplete_of_lipschitzWith hGlip 0 y₀
  have hGf : ∀ y : State n, ‖y - x‖ < ρ → s₀ / 2 ≤ σ * y k → G y = f y := by
    intro y hy hyk
    rw [hGg y (by
      have := norm_le_norm_add_norm_sub' y x
      linarith)]
    exact hgf y hy hyk
  set Φ : State n → ℝ := fun y => max (max (‖y - x‖ - ρ / 2) (s₀ / 2 - σ * y k)) (-W y)
    with hΦ
  have hΦc : Continuous Φ :=
    (((continuous_norm.comp (continuous_sub_right x)).sub continuous_const).max
      (continuous_const.sub (continuous_const.mul
        ((EuclideanSpace.proj k : State n →L[ℝ] ℝ).continuous)))).max hW.continuous.neg
  have hregion : ∀ y : State n, Φ y ≤ 0 → ‖y - x‖ < ρ ∧ s₀ / 2 ≤ σ * y k ∧ 0 ≤ W y := by
    intro y hy
    simp only [hΦ, max_le_iff, sub_nonpos, neg_nonpos] at hy
    exact ⟨by linarith [hy.1.1], hy.1.2, hy.2⟩
  -- along a stretch in the region, `σ y_k − μ t` does not decrease
  have hgrow : ∀ T, 0 ≤ T → (∀ u ∈ Icc 0 T, Φ (ψ u) ≤ 0) →
      IsTrajectoryOn ψ f 0 T ∧ ∀ u ∈ Icc 0 T, s₀ + μ * u ≤ σ * ψ u k := by
    intro T hT hin
    have hseg : IsTrajectoryOn ψ f 0 T :=
      isIntegralCurveOn_of_eq_on_curve (hψ.mono Icc_subset_Ici_self)
        (fun u hu => hGf _ (hregion _ (hin u hu)).1 (hregion _ (hin u hu)).2.1)
    refine ⟨hseg, ?_⟩
    have hdk : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => (ψ t k : ℝ)) (f (ψ t) k : ℝ)
        (Icc 0 T) t :=
      fun t ht => (EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
        (hseg t ht)
    have hmono : MonotoneOn (fun t => σ * ψ t k - μ * t) (Icc 0 T) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => σ * f (ψ t) k - μ)
        (convex_Icc _ _) ?_ (fun t ht => ?_) (fun t ht => ?_)
      · exact (fun t ht => ((hdk t ht).const_mul σ).continuousWithinAt.sub
          (continuous_const.mul continuous_id).continuousWithinAt)
      · rw [interior_Icc] at ht
        have h1 := ((hdk t (Ioo_subset_Icc_self ht)).const_mul σ).fun_sub
          ((hasDerivWithinAt_id t _).const_mul μ)
        have h2 := (h1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt
          (s := interior (Icc 0 T))
        convert h2 using 1
        all_goals first | rfl | ring
      · rw [interior_Icc] at ht
        obtain ⟨h1, h2, h3⟩ := hregion _ (hin t (Ioo_subset_Icc_self ht))
        linarith [hcone _ h1 (by linarith) h3]
    intro u hu
    have := hmono ⟨le_rfl, hT⟩ hu hu.1
    simp only [mul_zero, sub_zero, hψ0] at this
    linarith
  have hstay : ∀ T, 0 ≤ T → ∀ u ∈ Icc 0 T, Φ (ψ u) < 0 := by
    intro T hT
    refine forall_lt_of_first_exit hΦc (hψ.continuousOn.mono Icc_subset_Ici_self) ?_ ?_
    · simp only [hΦ, hψ0, max_lt_iff]
      refine ⟨⟨by linarith [hy₀x.trans_le (min_le_right _ _)], by linarith⟩, by linarith⟩
    · intro t ht hin
      obtain ⟨hseg, hsq⟩ := hgrow t ht.1 hin
      have h1 : ‖ψ t - x‖ < ρ / 2 :=
        hb 0 t ψ hseg (by rw [hψ0]; exact hy₀x.trans_le (min_le_left _ _)) t ⟨ht.1, le_rfl⟩
      have h2 : s₀ ≤ σ * ψ t k := by nlinarith [hsq t ⟨ht.1, le_rfl⟩, ht.1]
      have h3 : 0 < W (ψ t) := by
        by_contra hW3
        push Not at hW3
        have hWt : W (ψ t) = 0 := le_antisymm hW3 (hregion _ (hin t ⟨ht.1, le_rfl⟩)).2.2
        have htpos : 0 < t := by
          rcases eq_or_lt_of_le ht.1 with h | h
          · rw [← h, hψ0] at hWt; linarith
          · exact h
        have hd : HasDerivWithinAt (fun u => W (ψ u)) (fderiv ℝ W (ψ t) (f (ψ t)))
            (Icc 0 t) t :=
          (hWd (ψ t)).hasFDerivAt.comp_hasDerivWithinAt t (hseg t ⟨ht.1, le_rfl⟩)
        have hle := deriv_nonpos_of_isMinOn_right htpos hd (fun u hu => by
          rw [hWt]; exact (hregion _ (hin u hu)).2.2)
        obtain ⟨r1, r2, -⟩ := hregion _ (hin t ⟨ht.1, le_rfl⟩)
        linarith [hbar _ r1 (by linarith) hWt]
      simp only [hΦ, max_lt_iff]
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  -- but `σ y_k` grows linearly while `|y_k| < ρ / 2`
  set T := ρ / μ with hT
  have hT0 : 0 ≤ T := by positivity
  obtain ⟨-, hsq⟩ := hgrow T hT0 (fun u hu => (hstay T hT0 u hu).le)
  have hfin := hstay T hT0 T ⟨hT0, le_rfl⟩
  simp only [hΦ, max_lt_iff] at hfin
  have hk : |ψ T k| ≤ ‖ψ T - x‖ := by
    have := PiLp.norm_apply_le (ψ T - x) k
    simpa [hxk] using this
  have h1 := hsq T ⟨hT0, le_rfl⟩
  have h2 : σ * ψ T k ≤ |ψ T k| := by
    calc σ * ψ T k ≤ |σ * ψ T k| := le_abs_self _
      _ = |ψ T k| := by rw [abs_mul, hσa, one_mul]
  have h5 : μ * T = ρ := by rw [hT]; field_simp
  linarith [hfin.1.1]

/-- The algebraic core of the spiral estimate. With `Q = ω p + (h*/2) z`,
`ω² = −g* − h*²/4 > 0`, `2Kω = |h*| + 2` and coefficients `g, h` within
`ε = ω / (2 (1 + K)(1 + ω + |h*|/2))` of `g*, h*`, the combination
`σ z V' + 2 K z (p' z − p z')` (with `z' = Q/z`, `z p' = (g z + (h − h*/2) Q)/ω`, `V = z² + p²`)
is at most `−V`. -/
@[powerlib_foundation] theorem spiral_ineq {z p g h gs hs ω K ε σ s : ℝ} (hω : 0 < ω) (hω2 : ω ^ 2 = -gs - hs ^ 2 / 4)
    (hK : 2 * K * ω = |hs| + 2) (hK0 : 0 ≤ K)
    (hε : 2 * ε * (1 + K) * (1 + (ω + |hs| / 2)) = ω)
    (hg : |g - gs| ≤ ε) (hh : |h - hs| ≤ ε) (hσ : σ = 1 ∨ σ = -1)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = z ^ 2 + p ^ 2) :
    σ * (2 * z * (ω * p + hs / 2 * z) + 2 * p * ((g * z + (h - hs / 2) * (ω * p + hs / 2 * z)) / ω))
      + 2 * K * (z * ((g * z + (h - hs / 2) * (ω * p + hs / 2 * z)) / ω) -
        p * (ω * p + hs / 2 * z)) ≤ -(z ^ 2 + p ^ 2) := by
  set Q := ω * p + hs / 2 * z with hQ
  have hid : σ * (2 * z * Q + 2 * p * ((g * z + (h - hs / 2) * Q) / ω)) +
      2 * K * (z * ((g * z + (h - hs / 2) * Q) / ω) - p * Q) =
      (σ * hs - 2 * K * ω) * (z ^ 2 + p ^ 2) +
        (z * (g - gs) + (h - hs) * Q) * (2 * σ * p + 2 * K * z) / ω := by
    field_simp
    rw [hQ]
    linear_combination (2 * z * (K * z + p * σ)) * hω2
  rw [hid]
  have hσs : σ * hs ≤ |hs| := by
    rcases hσ with rfl | rfl
    · simp [le_abs_self]
    · simp [neg_le_abs]
  have hσa : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hz : |z| ≤ s := by
    rw [← Real.sqrt_sq hs0, hs2]; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg p])
  have hp : |p| ≤ s := by
    rw [← Real.sqrt_sq hs0, hs2]; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg z])
  have hQb : |Q| ≤ (ω + |hs| / 2) * s := by
    rw [hQ]
    calc |ω * p + hs / 2 * z| ≤ |ω * p| + |hs / 2 * z| := abs_add_le _ _
      _ = ω * |p| + |hs| / 2 * |z| := by
          rw [abs_mul, abs_mul, abs_div, abs_of_pos hω]; norm_num
      _ ≤ ω * s + |hs| / 2 * s := by gcongr
      _ = (ω + |hs| / 2) * s := by ring
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hg
  have hA : |z * (g - gs) + (h - hs) * Q| ≤ ε * (1 + (ω + |hs| / 2)) * s := by
    calc |z * (g - gs) + (h - hs) * Q| ≤ |z| * |g - gs| + |h - hs| * |Q| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ s * ε + ε * ((ω + |hs| / 2) * s) := by gcongr
      _ = ε * (1 + (ω + |hs| / 2)) * s := by ring
  have hB : |2 * σ * p + 2 * K * z| ≤ 2 * (1 + K) * s := by
    calc |2 * σ * p + 2 * K * z| ≤ |2 * σ * p| + |2 * K * z| := abs_add_le _ _
      _ = 2 * |p| + 2 * K * |z| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, hσa, abs_of_nonneg hK0]; norm_num
      _ ≤ 2 * s + 2 * K * s := by gcongr
      _ = 2 * (1 + K) * s := by ring
  have hE : (z * (g - gs) + (h - hs) * Q) * (2 * σ * p + 2 * K * z) / ω ≤ z ^ 2 + p ^ 2 := by
    rw [div_le_iff₀ hω]
    have h1 := abs_mul (z * (g - gs) + (h - hs) * Q) (2 * σ * p + 2 * K * z)
    have h2 : |(z * (g - gs) + (h - hs) * Q) * (2 * σ * p + 2 * K * z)| ≤
        ε * (1 + (ω + |hs| / 2)) * s * (2 * (1 + K) * s) := by
      rw [h1]; exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
    have h3 : ε * (1 + (ω + |hs| / 2)) * s * (2 * (1 + K) * s) = ω * s ^ 2 := by
      rw [show ε * (1 + (ω + |hs| / 2)) * s * (2 * (1 + K) * s) =
        (2 * ε * (1 + K) * (1 + (ω + |hs| / 2))) * s ^ 2 by ring, hε]
    rw [h3, hs2] at h2
    nlinarith [le_abs_self ((z * (g - gs) + (h - hs) * Q) * (2 * σ * p + 2 * K * z))]
  have hF : (σ * hs - 2 * K * ω) * (z ^ 2 + p ^ 2) ≤ -2 * (z ^ 2 + p ^ 2) := by
    have : σ * hs - 2 * K * ω ≤ -2 := by rw [hK]; linarith
    nlinarith [sq_nonneg z, sq_nonneg p]
  linarith

/-- The Lyapunov function of the spiral estimate in the coordinates `(z, Q)`:
`√(z² + p²) · exp(σ K arctan(p / z))` with `p = (Q − (h*/2) z)/ω`. -/
def spiralLyap (ω hs K σ z Q : ℝ) : ℝ :=
  Real.sqrt (z ^ 2 + ((Q - hs / 2 * z) / ω) ^ 2) *
    Real.exp (σ * K * Real.arctan ((Q - hs / 2 * z) / ω / z))

/-- `exp(σ K arctan a)` lies between `exp(∓Kπ/2)`. -/
@[powerlib_foundation] theorem exp_spiral_bounds {K σ a : ℝ} (hK0 : 0 ≤ K) (hσ : σ = 1 ∨ σ = -1) :
    Real.exp (-(K * (Real.pi / 2))) ≤ Real.exp (σ * K * Real.arctan a) ∧
      Real.exp (σ * K * Real.arctan a) ≤ Real.exp (K * (Real.pi / 2)) := by
  have h1 := Real.arctan_lt_pi_div_two a
  have h2 := Real.neg_pi_div_two_lt_arctan a
  constructor <;> apply Real.exp_le_exp.mpr <;> rcases hσ with rfl | rfl <;> nlinarith

/-- Upper bound of the spiral function by the radius. -/
@[powerlib_foundation] theorem spiralLyap_le {ω hs K σ z Q : ℝ} (hK0 : 0 ≤ K) (hσ : σ = 1 ∨ σ = -1) :
    spiralLyap ω hs K σ z Q ≤
      Real.sqrt (z ^ 2 + ((Q - hs / 2 * z) / ω) ^ 2) * Real.exp (K * (Real.pi / 2)) :=
  mul_le_mul_of_nonneg_left (exp_spiral_bounds hK0 hσ).2 (Real.sqrt_nonneg _)

/-- Lower bound of the spiral function by the radius. -/
@[powerlib_foundation] theorem le_spiralLyap {ω hs K σ z Q : ℝ} (hK0 : 0 ≤ K) (hσ : σ = 1 ∨ σ = -1) :
    Real.sqrt (z ^ 2 + ((Q - hs / 2 * z) / ω) ^ 2) * Real.exp (-(K * (Real.pi / 2))) ≤
      spiralLyap ω hs K σ z Q :=
  mul_le_mul_of_nonneg_left (exp_spiral_bounds hK0 hσ).1 (Real.sqrt_nonneg _)

/-- Along a curve with `z' = Q / z` and `Q' = g + h Q / z` (`g, h` near `g*, h*`, discriminant
`h*² + 4g* < 0`), the spiral function decreases at least at the rate `exp(−Kπ/2) / 2` while
`σ z > 0`. -/
@[powerlib_foundation] theorem hasDerivWithinAt_spiralLyap {z Q : ℝ → ℝ} {S : Set ℝ} {t g h gs hs ω K ε σ : ℝ}
    (hω : 0 < ω) (hω2 : ω ^ 2 = -gs - hs ^ 2 / 4) (hK : 2 * K * ω = |hs| + 2) (hK0 : 0 ≤ K)
    (hε : 2 * ε * (1 + K) * (1 + (ω + |hs| / 2)) = ω) (hσ : σ = 1 ∨ σ = -1)
    (hσz : 0 < σ * z t) (hg : |g - gs| ≤ ε) (hh : |h - hs| ≤ ε)
    (hz : HasDerivWithinAt z (Q t / z t) S t)
    (hQ : HasDerivWithinAt Q (g + h * (Q t / z t)) S t) :
    ∃ d, HasDerivWithinAt (fun u => spiralLyap ω hs K σ (z u) (Q u)) d S t ∧
      d ≤ -Real.exp (-(K * (Real.pi / 2))) / 2 := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hz0 : z t ≠ 0 := by intro h0; rw [h0, mul_zero] at hσz; exact lt_irrefl _ hσz
  set z' := Q t / z t with hz'
  set p' := (g + h * z' - hs / 2 * z') / ω with hp'
  have hp : HasDerivWithinAt (fun u => (Q u - hs / 2 * z u) / ω) p' S t :=
    (hQ.fun_sub (hz.const_mul (hs / 2))).div_const ω
  set pt := (Q t - hs / 2 * z t) / ω with hpt
  have hV : HasDerivWithinAt (fun u => z u ^ 2 + ((Q u - hs / 2 * z u) / ω) ^ 2)
      (2 * z t * z' + 2 * pt * p') S t := by
    have := (hz.fun_pow 2).fun_add (hp.fun_pow 2)
    convert this using 1
    push_cast; ring
  set V := z t ^ 2 + pt ^ 2 with hVdef
  have hVpos : 0 < V := by positivity
  have hsq := hV.sqrt (ne_of_gt hVpos)
  have hr := hp.fun_div hz hz0
  have ha := hr.arctan
  have he := (ha.const_mul (σ * K)).exp
  have hΨ := hsq.fun_mul he
  refine ⟨_, hΨ, ?_⟩
  set sV := Real.sqrt V with hsVdef
  have hsV2 : sV ^ 2 = V := Real.sq_sqrt hVpos.le
  have hsV0 : 0 < sV := Real.sqrt_pos.mpr hVpos
  set e := Real.exp (σ * K * Real.arctan (pt / z t)) with hedef
  have he0 : 0 < e := Real.exp_pos _
  have heb := (exp_spiral_bounds (a := pt / z t) hK0 hσ).1
  -- the derivative in closed form
  set X := 2 * z t * z' + 2 * pt * p' + 2 * σ * K * (p' * z t - pt * z') with hX
  have hd : (2 * z t * z' + 2 * pt * p') / (2 * sV) * e +
      sV * (e * (σ * K * (1 / (1 + (pt / z t) ^ 2) * ((p' * z t - pt * z') / z t ^ 2)))) =
      e / (2 * sV) * X := by
    have hw : 1 / (1 + (pt / z t) ^ 2) * (1 / z t ^ 2) = 1 / sV ^ 2 := by
      rw [hsV2, hVdef]; field_simp
    have h2 : sV * (e * (σ * K * (1 / (1 + (pt / z t) ^ 2) * ((p' * z t - pt * z') / z t ^ 2)))) =
        sV * e * σ * K * (p' * z t - pt * z') * (1 / (1 + (pt / z t) ^ 2) * (1 / z t ^ 2)) := by
      ring
    rw [h2, hw, hX]
    field_simp
  rw [hd]
  -- the spiral inequality
  have hA := spiral_ineq (z := z t) (p := pt) (g := g) (h := h) (s := sV) hω hω2 hK hK0 hε hg hh
    hσ hsV0.le (by rw [hsV2])
  have hQt : Q t = ω * pt + hs / 2 * z t := by rw [hpt]; field_simp; ring
  have hzz' : z t * z' = Q t := by rw [hz']; field_simp
  have hzp' : z t * p' = (g * z t + (h - hs / 2) * Q t) / ω := by
    rw [hp', hz']; field_simp; ring
  have hXz : σ * z t * X ≤ -V := by
    have : σ * z t * X = σ * (2 * z t * Q t + 2 * pt * ((g * z t + (h - hs / 2) * Q t) / ω)) +
        2 * K * (z t * ((g * z t + (h - hs / 2) * Q t) / ω) - pt * Q t) := by
      rw [← hzp', ← hzz', hX]
      linear_combination (2 * K * z t * (p' * z t - pt * z')) * hσ2
    rw [this, hQt]
    exact hA
  -- conclude
  have hσzV : σ * z t ≤ sV := by
    have : |z t| ≤ sV := by
      rw [hsVdef, hVdef]; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg pt])
    rcases hσ with rfl | rfl
    · linarith [le_abs_self (z t)]
    · linarith [neg_abs_le (z t)]
  have hfin : e / (2 * sV) * X * (σ * z t) ≤ -(e / 2) * (σ * z t) := by
    have h1 : e / (2 * sV) * X * (σ * z t) = e / (2 * sV) * (σ * z t * X) := by ring
    rw [h1]
    have h2 : e / (2 * sV) * (σ * z t * X) ≤ e / (2 * sV) * (-V) :=
      mul_le_mul_of_nonneg_left hXz (by positivity)
    have h3 : e / (2 * sV) * (-V) = -(e / 2) * sV := by
      rw [← hsV2]; field_simp
    have h4 := mul_le_mul_of_nonneg_left hσzV (le_of_lt (half_pos he0))
    linarith
  have hfin' : e / (2 * sV) * X ≤ -(e / 2) := le_of_mul_le_mul_right hfin hσz
  linarith

/-- Mean-value lower bound on a subinterval: a function with derivative at least `m` inside
`[c, d] ⊆ [a, b]` increases by at least `m (d − c)`. -/
@[powerlib_foundation] theorem sub_ge_of_deriv_ge {u u' : ℝ → ℝ} {a b c d m : ℝ} (hcd : c ≤ d) (hca : a ≤ c)
    (hdb : d ≤ b) (hu : ∀ s ∈ Icc a b, HasDerivWithinAt u (u' s) (Icc a b) s)
    (hm : ∀ s ∈ Ioo c d, m ≤ u' s) : m * (d - c) ≤ u d - u c := by
  have hmono : MonotoneOn (fun s => u s - m * s) (Icc c d) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun s => u' s - m) (convex_Icc _ _)
      (fun s hs => ((hu s ⟨hca.trans hs.1, hs.2.trans hdb⟩).continuousWithinAt.mono
        (Icc_subset_Icc hca hdb)).sub (continuous_const.mul continuous_id).continuousWithinAt)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs
      have h1 := (hu s ⟨hca.trans hs.1.le, hs.2.le.trans hdb⟩).hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hca hs.1) (lt_of_lt_of_le hs.2 hdb))
      exact (h1.fun_sub ((hasDerivAt_id s).const_mul m)).hasDerivWithinAt.congr_deriv (by simp)
    · rw [interior_Icc] at hs
      linarith [hm s hs]
  have := hmono ⟨le_rfl, hcd⟩ ⟨hcd, le_rfl⟩ hcd
  simp only at this
  linarith

/-- Mean-value upper bound on a subinterval. -/
@[powerlib_foundation] theorem sub_le_of_deriv_le {u u' : ℝ → ℝ} {a b c d m : ℝ} (hcd : c ≤ d) (hca : a ≤ c)
    (hdb : d ≤ b) (hu : ∀ s ∈ Icc a b, HasDerivWithinAt u (u' s) (Icc a b) s)
    (hm : ∀ s ∈ Ioo c d, u' s ≤ m) : u d - u c ≤ m * (d - c) := by
  have h := sub_ge_of_deriv_ge (u := fun s => -u s) (u' := fun s => -u' s) (m := -m) hcd hca hdb
    (fun s hs => (hu s hs).neg) (fun s hs => by linarith [hm s hs])
  linarith

/-- **A solution segment touches the singular plane only where `q = 0`.** Near `x`, off the plane
`y_k f_k(y) = q(y)` and on it `f_k ≠ 0`. If a nontrivial solution segment meets the plane at `τ`,
then `q(φ τ) = 0`: otherwise `y_k²` would be monotone near `τ` with slope bounded away from zero
(`d(y_k²)/dt = 2 q`), which is incompatible with the transversal crossing `y_k ≈ f_k (t − τ)`. -/
@[powerlib_foundation] theorem q_eq_zero_of_touch {f : State n → State n} {x : State n} (k : Fin n) {q : State n → ℝ}
    {ρ : ℝ} (hqc : Continuous q)
    (hrel : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → y k * f y k = q y)
    (hplane : ∀ y : State n, ‖y - x‖ < ρ → y k = 0 → f y k ≠ 0)
    {φ : ℝ → State n} {a b τ : ℝ} (hab : a < b) (hφ : IsTrajectoryOn φ f a b)
    (hin : ∀ t ∈ Icc a b, ‖φ t - x‖ < ρ) (hτ : τ ∈ Icc a b) (hz : φ τ k = 0) :
    q (φ τ) = 0 := by
  set ι := f (φ τ) k with hι
  have hι0 : ι ≠ 0 := hplane _ (hin τ hτ) hz
  have hιp : 0 < |ι| := abs_pos.mpr hι0
  have hd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t => (φ t k : ℝ)) (f (φ t) k : ℝ)
      (Icc a b) t :=
    fun t ht => (EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (hφ t ht)
  -- `u = y_k²` and its derivative `2 y_k f_k`
  have hu : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t => φ t k ^ 2)
      (2 * (φ t k * f (φ t) k)) (Icc a b) t := fun t ht => by
    have := (hd t ht).fun_pow 2
    convert this using 1
    push_cast; ring
  have hu' : ∀ t ∈ Icc a b, φ t k * f (φ t) k = if φ t k = 0 then 0 else q (φ t) := by
    intro t ht
    split_ifs with h
    · rw [h, zero_mul]
    · exact hrel _ (hin t ht) h
  by_contra hq1
  set q1 := q (φ τ) with hq1def
  have hq1p : 0 < |q1| := abs_pos.mpr hq1
  -- continuity of `q ∘ φ` at `τ`
  have hqφ : ContinuousWithinAt (fun t => q (φ t)) (Icc a b) τ :=
    hqc.continuousAt.comp_continuousWithinAt (hφ.continuousOn τ hτ)
  obtain ⟨η₁, hη₁, hq⟩ : ∃ η > 0, ∀ t ∈ Icc a b, |t - τ| < η → |q (φ t) - q1| < |q1| / 2 := by
    have := Metric.continuousWithinAt_iff.mp hqφ (|q1| / 2) (by positivity)
    obtain ⟨η, hη, h⟩ := this
    exact ⟨η, hη, fun t ht htτ => by
      have := h ht (by rw [Real.dist_eq]; exact htτ); rwa [Real.dist_eq] at this⟩
  -- transversal crossing at `τ`
  obtain ⟨η₂, hη₂, hlin⟩ : ∃ η > 0, ∀ t ∈ Icc a b, |t - τ| < η →
      |φ t k - ι * (t - τ)| ≤ |ι| / 2 * |t - τ| := by
    have hsl := (hasDerivWithinAt_iff_tendsto_slope.mp (hd τ hτ))
    have hev := hsl.eventually (Metric.ball_mem_nhds ι (half_pos hιp))
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨η, hη, h⟩ := hev
    refine ⟨η, hη, fun t ht htτ => ?_⟩
    rcases eq_or_ne t τ with rfl | hne
    · simp [hz]
    · have h1 := h (by rw [Real.dist_eq]; exact htτ) ⟨ht, hne⟩
      rw [Real.dist_eq, slope_def_field, hz, sub_zero] at h1
      have hne' : t - τ ≠ 0 := sub_ne_zero.mpr hne
      have h2 : φ t k - ι * (t - τ) = (φ t k / (t - τ) - ι) * (t - τ) := by
        field_simp
      rw [h2, abs_mul]
      exact mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
  set η := min η₁ η₂ with hη
  have hη0 : 0 < η := lt_min hη₁ hη₂
  have hnz : ∀ t ∈ Icc a b, t ≠ τ → |t - τ| < η → φ t k ≠ 0 ∧ φ t k ^ 2 ≤ 9 / 4 * ι ^ 2 * (t - τ) ^ 2 := by
    intro t ht hne htη
    have h1 := hlin t ht (lt_of_lt_of_le htη (min_le_right _ _))
    have hpos : 0 < |t - τ| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have h2 := abs_le.mp h1
    have hιt : |ι * (t - τ)| = |ι| * |t - τ| := abs_mul _ _
    constructor
    · intro h0
      rw [h0, zero_sub, abs_neg, hιt] at h1
      nlinarith
    · have h3 : |φ t k| ≤ 3 / 2 * |ι| * |t - τ| := by
        have := abs_sub_abs_le_abs_sub (φ t k) (ι * (t - τ))
        rw [hιt] at this
        linarith
      have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      rw [sq_abs] at h4
      calc φ t k ^ 2 ≤ (3 / 2 * |ι| * |t - τ|) ^ 2 := h4
        _ = 9 / 4 * ι ^ 2 * (t - τ) ^ 2 := by rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring
  have hqsgn : ∀ t ∈ Icc a b, |t - τ| < η → (0 < q1 → q1 / 2 < q (φ t)) ∧
      (q1 < 0 → q (φ t) < q1 / 2) := by
    intro t ht htη
    have h := abs_lt.mp (hq t ht (lt_of_lt_of_le htη (min_le_left _ _)))
    constructor
    · intro hp; rw [abs_of_pos hp] at h; linarith [h.1]
    · intro hn; rw [abs_of_neg hn] at h; linarith [h.2]
  rcases lt_or_gt_of_ne hq1 with hneg | hpos
  · -- `q1 < 0`: `y_k²` decreases near `τ`
    rcases eq_or_lt_of_le hτ.1 with hτa | hτa
    · -- `τ = a < b`: to the right `y_k²` cannot leave `0`
      set t := min b (τ + η / 2) with ht
      have htτ : τ < t := lt_min (hτa ▸ hab) (by linarith)
      have htb : t ≤ b := min_le_left _ _
      have hle := sub_le_of_deriv_le (m := 0) htτ.le hτ.1 htb hu (fun s hs => by
        rw [hu' s ⟨hτ.1.trans hs.1.le, hs.2.le.trans htb⟩]
        split_ifs with h0
        · simp
        · have hsη : |s - τ| < η := by
            rw [abs_of_pos (by linarith [hs.1])]
            linarith [hs.2, min_le_right b (τ + η / 2)]
          linarith [(hqsgn s ⟨hτ.1.trans hs.1.le, hs.2.le.trans htb⟩ hsη).2 hneg])
      have htη : |t - τ| < η := by
        rw [abs_of_pos (by linarith)]; linarith [min_le_right b (τ + η / 2)]
      obtain ⟨hz0, -⟩ := hnz t ⟨hτ.1.trans htτ.le, htb⟩ (ne_of_gt htτ) htη
      simp only [hz, zero_pow two_ne_zero, sub_zero, zero_mul] at hle
      exact hz0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hle (sq_nonneg _)))
    · -- `τ > a`: to the left `y_k²` would exceed `|q1| (τ − t)`
      set t := max a (τ - min (η / 2) (|q1| / (9 * ι ^ 2))) with ht
      have hδ : 0 < min (η / 2) (|q1| / (9 * ι ^ 2)) := lt_min (by positivity) (by positivity)
      have htτ : t < τ := max_lt hτa (by linarith)
      have hat : a ≤ t := le_max_left _ _
      have htη' : τ - t ≤ min (η / 2) (|q1| / (9 * ι ^ 2)) := by
        have := le_max_right a (τ - min (η / 2) (|q1| / (9 * ι ^ 2))); linarith
      have hle := sub_le_of_deriv_le (m := q1) htτ.le hat hτ.2 hu (fun s hs => by
        have hsI : s ∈ Icc a b := ⟨hat.trans hs.1.le, hs.2.le.trans hτ.2⟩
        have hsη : |s - τ| < η := by
          rw [abs_of_neg (by linarith [hs.2])]
          linarith [hs.1, min_le_left (η / 2) (|q1| / (9 * ι ^ 2))]
        obtain ⟨hs0, -⟩ := hnz s hsI (ne_of_lt hs.2) hsη
        rw [hu' s hsI]; simp only [hs0, ↓reduceIte]
        linarith [(hqsgn s hsI hsη).2 hneg])
      have htη : |t - τ| < η := by
        rw [abs_of_neg (by linarith)]
        linarith [min_le_left (η / 2) (|q1| / (9 * ι ^ 2))]
      obtain ⟨-, hsq⟩ := hnz t ⟨hat, htτ.le.trans hτ.2⟩ (ne_of_lt htτ) htη
      simp only [hz, zero_pow two_ne_zero, zero_sub] at hle
      -- `φ t k ² ≥ |q1| (τ − t)` and `≤ (9/4) ι² (τ − t)²`
      have hq1a : |q1| = -q1 := abs_of_neg hneg
      have h1 : -q1 * (τ - t) ≤ φ t k ^ 2 := by linarith
      have hι2 : 0 < ι ^ 2 := by positivity
      have h2 : (τ - t) * (9 * ι ^ 2) ≤ |q1| := by
        have := htη'.trans (min_le_right _ _)
        rwa [le_div_iff₀ (by positivity)] at this
      have h3 : 0 < τ - t := by linarith
      rw [hq1a] at h2
      nlinarith [sq_nonneg (t - τ)]
  · -- `q1 > 0`: `y_k²` increases near `τ`
    rcases eq_or_lt_of_le hτ.2 with hτb | hτb
    · -- `τ = b > a`: to the left `y_k²` would be below `0`
      set t := max a (τ - η / 2) with ht
      have htτ : t < τ := max_lt (hτb ▸ hab) (by linarith)
      have hat : a ≤ t := le_max_left _ _
      have hge := sub_ge_of_deriv_ge (m := 0) htτ.le hat hτ.2 hu (fun s hs => by
        rw [hu' s ⟨hat.trans hs.1.le, hs.2.le.trans hτ.2⟩]
        split_ifs with h0
        · simp
        · have hsη : |s - τ| < η := by
            rw [abs_of_neg (by linarith [hs.2])]
            linarith [hs.1, le_max_right a (τ - η / 2)]
          linarith [(hqsgn s ⟨hat.trans hs.1.le, hs.2.le.trans hτ.2⟩ hsη).1 hpos])
      have htη : |t - τ| < η := by
        rw [abs_of_neg (by linarith)]; linarith [le_max_right a (τ - η / 2)]
      obtain ⟨hz0, -⟩ := hnz t ⟨hat, htτ.le.trans hτ.2⟩ (ne_of_lt htτ) htη
      simp only [hz, zero_pow two_ne_zero, zero_mul, zero_sub] at hge
      exact hz0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        (le_antisymm (by linarith) (sq_nonneg _)))
    · -- `τ < b`: to the right `y_k²` would exceed `q1 (t − τ)`
      set t := min b (τ + min (η / 2) (q1 / (9 * ι ^ 2))) with ht
      have hδ : 0 < min (η / 2) (q1 / (9 * ι ^ 2)) := lt_min (by positivity) (by positivity)
      have htτ : τ < t := lt_min hτb (by linarith)
      have htb : t ≤ b := min_le_left _ _
      have htη' : t - τ ≤ min (η / 2) (q1 / (9 * ι ^ 2)) := by
        have := min_le_right b (τ + min (η / 2) (q1 / (9 * ι ^ 2))); linarith
      have hge := sub_ge_of_deriv_ge (m := q1) htτ.le hτ.1 htb hu (fun s hs => by
        have hsI : s ∈ Icc a b := ⟨hτ.1.trans hs.1.le, hs.2.le.trans htb⟩
        have hsη : |s - τ| < η := by
          rw [abs_of_pos (by linarith [hs.1])]
          linarith [hs.2, min_le_left (η / 2) (q1 / (9 * ι ^ 2))]
        obtain ⟨hs0, -⟩ := hnz s hsI (ne_of_gt hs.1) hsη
        rw [hu' s hsI]; simp only [hs0, ↓reduceIte]
        linarith [(hqsgn s hsI hsη).1 hpos])
      have htη : |t - τ| < η := by
        rw [abs_of_pos (by linarith)]
        linarith [min_le_left (η / 2) (q1 / (9 * ι ^ 2))]
      obtain ⟨-, hsq⟩ := hnz t ⟨hτ.1.trans htτ.le, htb⟩ (ne_of_gt htτ) htη
      simp only [hz, zero_pow two_ne_zero, sub_zero] at hge
      have hι2 : 0 < ι ^ 2 := by positivity
      have h2 : (t - τ) * (9 * ι ^ 2) ≤ q1 := by
        have := htη'.trans (min_le_right _ _)
        rwa [le_div_iff₀ (by positivity)] at this
      have h3 : 0 < t - τ := by linarith
      nlinarith [sq_nonneg (t - τ)]


/-- A transversal zero: if `z τ = 0` and `z' (τ) = ι ≠ 0` within `S`, then near `τ`,
`|z u − ι (u − τ)| ≤ |ι|/2 |u − τ|` on `S`. -/
@[powerlib_foundation] theorem exists_transversal {z : ℝ → ℝ} {S : Set ℝ} {τ ι : ℝ} (hι : ι ≠ 0)
    (hd : HasDerivWithinAt z ι S τ) (hz : z τ = 0) :
    ∃ η > 0, ∀ u ∈ S, |u - τ| < η → |z u - ι * (u - τ)| ≤ |ι| / 2 * |u - τ| := by
  have hιp : 0 < |ι| := abs_pos.mpr hι
  have hsl := hasDerivWithinAt_iff_tendsto_slope.mp hd
  have hev := hsl.eventually (Metric.ball_mem_nhds ι (half_pos hιp))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, h⟩ := hev
  refine ⟨η, hη, fun u hu huτ => ?_⟩
  rcases eq_or_ne u τ with rfl | hne
  · simp [hz]
  · have h1 := h (by rw [Real.dist_eq]; exact huτ) ⟨hu, hne⟩
    rw [Real.dist_eq, slope_def_field, hz, sub_zero] at h1
    have hne' : u - τ ≠ 0 := sub_ne_zero.mpr hne
    have h2 : z u - ι * (u - τ) = (z u / (u - τ) - ι) * (u - τ) := by field_simp
    rw [h2, abs_mul]
    exact mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)

/-- `√(a² + b²) ≤ |a| + |b|`. -/
@[powerlib_foundation] theorem sqrt_sq_add_sq_le (a b : ℝ) : Real.sqrt (a ^ 2 + b ^ 2) ≤ |a| + |b| := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-- The spiral function is nonnegative. -/
@[powerlib_foundation] theorem spiralLyap_nonneg (ω hs K σ z Q : ℝ) : 0 ≤ spiralLyap ω hs K σ z Q :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

/-- A closed upper bound on `[a, b)` extends to `b`. -/
@[powerlib_foundation] theorem forall_Icc_of_forall_Ico {F : ℝ → ℝ} {a b B : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b)) (h : ∀ t ∈ Ico a b, F t ≤ B) : ∀ t ∈ Icc a b, F t ≤ B := by
  have hcl : IsClosed (Icc a b ∩ F ⁻¹' Iic B) :=
    hF.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : Ico a b ⊆ Icc a b ∩ F ⁻¹' Iic B := fun t ht => ⟨Ico_subset_Icc_self ht, h t ht⟩
  have := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ico hab.ne] at this
  exact fun t ht => (this ht).2

set_option maxHeartbeats 1000000 in
/-- **Spiral collapse onto a coordinate plane.** Let `x` lie on the plane `y_k = 0`, and near `x`
let the field satisfy `y_k f_k(y) = q(y)` off the plane and `f_k ≠ 0` on it, with `q` a `C¹`
function vanishing at `x` whose Lie derivative is `g + h q / y_k` (`g, h` continuous at `x`), and
bounded components off `k`. If `h(x)² + 4 g(x) < 0`, then `x` satisfies the segment-based local
exponential estimate (whether or not it is an equilibrium). In the time `τ` with `dτ = dt / y_k`
the pair `(y_k, q)` follows a linear focus; every solution segment near `x` meets the plane at
most at its end, after a time `O(‖y(t₀) − x‖)`, and stays within `O(‖y(t₀) − x‖)` of `x`
(Lyapunov function `spiralLyap`, decreasing at a uniform rate; `q_eq_zero_of_touch`). -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_spiral {f : State n → State n} {x : State n} (k : Fin n)
    (hxk : x k = 0) {q g h : State n → ℝ} (hq : ContDiff ℝ 1 q) (hq0 : q x = 0)
    (hgc : ContinuousAt g x) (hhc : ContinuousAt h x) {ρ M : ℝ} (hρ : 0 < ρ)
    (hrel : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → y k * f y k = q y)
    (hplane : ∀ y : State n, ‖y - x‖ < ρ → y k = 0 → f y k ≠ 0)
    (hlie : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 →
      fderiv ℝ q y (f y) = g y + h y * (q y / y k))
    (hD : h x ^ 2 + 4 * g x < 0)
    (hbound : ∀ y : State n, ‖y - x‖ < ρ →
      ‖f y - f y k • EuclideanSpace.single k (1 : ℝ)‖ ≤ M) :
    LocallyExponentiallyStable f x := by
  -- constants of the focus
  obtain ⟨gs, hgs⟩ : ∃ v, v = g x := ⟨_, rfl⟩
  obtain ⟨hs, hhs⟩ : ∃ v, v = h x := ⟨_, rfl⟩
  rw [← hgs, ← hhs] at hD
  obtain ⟨ω, hωdef⟩ : ∃ v, v = Real.sqrt (-(hs ^ 2 + 4 * gs)) / 2 := ⟨_, rfl⟩
  have hω : 0 < ω := by
    rw [hωdef]
    have := Real.sqrt_pos.mpr (show 0 < -(hs ^ 2 + 4 * gs) by linarith)
    positivity
  have hω2 : ω ^ 2 = -gs - hs ^ 2 / 4 := by
    rw [hωdef, div_pow, Real.sq_sqrt (by linarith)]; ring
  obtain ⟨K, hKdef⟩ : ∃ v, v = (|hs| + 2) / (2 * ω) := ⟨_, rfl⟩
  have hK : 2 * K * ω = |hs| + 2 := by rw [hKdef]; field_simp
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  obtain ⟨ε, hεdef⟩ : ∃ v, v = ω / (2 * (1 + K) * (1 + (ω + |hs| / 2))) := ⟨_, rfl⟩
  have hε : 2 * ε * (1 + K) * (1 + (ω + |hs| / 2)) = ω := by
    rw [hεdef]; field_simp
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨E, hEdef⟩ : ∃ v, v = Real.exp (K * (Real.pi / 2)) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hEdef]; exact Real.one_le_exp (by positivity)
  obtain ⟨c, hcdef⟩ : ∃ v, v = Real.exp (-(K * (Real.pi / 2))) / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hcE : c * E = 1 / 2 := by
    rw [hcdef, hEdef, div_mul_eq_mul_div, ← Real.exp_add]; simp
  have hEc : Real.exp (-(K * (Real.pi / 2))) * E = 1 := by
    rw [hEdef, ← Real.exp_add]; simp
  -- neighbourhoods
  obtain ⟨ρg, hρg, hg⟩ := Metric.continuousAt_iff.mp hgc ε hε0
  obtain ⟨ρh, hρh, hh⟩ := Metric.continuousAt_iff.mp hhc ε hε0
  -- `q` is Lipschitz on the unit ball
  have hqd : Differentiable ℝ q := hq.differentiable one_ne_zero
  obtain ⟨L, hL⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn
    (hq.continuous_fderiv one_ne_zero).continuousOn
  have hqL : ∀ y : State n, ‖y - x‖ ≤ 1 → |q y| ≤ L * ‖y - x‖ := by
    intro y hy
    have := (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hqd z) (fun z hz => hL z hz) (Metric.mem_closedBall_self zero_le_one)
      (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy)
    rwa [hq0, sub_zero, Real.norm_eq_abs] at this
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL x (Metric.mem_closedBall_self zero_le_one))
  obtain ⟨R, hRdef⟩ : ∃ v, v = min ρ (min ρg (min ρh 1)) := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hRdef]; exact lt_min hρ (lt_min hρg (lt_min hρh one_pos))
  have hRρ : R ≤ ρ := by rw [hRdef]; exact min_le_left _ _
  have hRg : R ≤ ρg := by rw [hRdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hRh : R ≤ ρh := by
    rw [hRdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hR1 : R ≤ 1 := by
    rw [hRdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hgR : ∀ y : State n, ‖y - x‖ < R → |g y - gs| ≤ ε := fun y hy => by
    rw [hgs]; exact (hg (by rw [dist_eq_norm]; linarith)).le
  have hhR : ∀ y : State n, ‖y - x‖ < R → |h y - hs| ≤ ε := fun y hy => by
    rw [hhs]; exact (hh (by rw [dist_eq_norm]; linarith)).le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hbound x (by simpa using hρ))
  obtain ⟨CV, hCV⟩ : ∃ v, v = 1 + (L + |hs| / 2) / ω := ⟨_, rfl⟩
  have hCV1 : 1 ≤ CV := by
    have : 0 ≤ (L + |hs| / 2) / ω := by positivity
    rw [hCV]; linarith
  obtain ⟨C1, hC1⟩ : ∃ v, v = 1 + 2 * M * E ^ 2 * CV + E ^ 2 * CV := ⟨_, rfl⟩
  have hC11 : 1 ≤ C1 := by
    have h1 : 0 ≤ 2 * M * E ^ 2 * CV := by positivity
    have h2 : 0 ≤ E ^ 2 * CV := by positivity
    rw [hC1]; linarith
  obtain ⟨r, hrdef⟩ : ∃ v, v = min (R / (4 * C1)) (c / (2 * E * CV)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; exact lt_min (by positivity) (by positivity)
  refine ⟨r, 2 * C1, 1, hr0, by linarith, one_pos, ?_⟩
  intro t₀ t₁ φ hφ h0
  obtain ⟨δ, hδ⟩ : ∃ v, v = ‖φ t₀ - x‖ := ⟨_, rfl⟩
  rw [← hδ] at h0
  rw [← hδ]
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact norm_nonneg _
  have hδR : δ < R / (4 * C1) := lt_of_lt_of_le h0 (by rw [hrdef]; exact min_le_left _ _)
  have hδc : δ < c / (2 * E * CV) := lt_of_lt_of_le h0 (by rw [hrdef]; exact min_le_right _ _)
  have hδR' : C1 * δ < R / 4 := by
    rw [lt_div_iff₀ (by positivity)] at hδR
    have : C1 * δ = δ * (4 * C1) / 4 := by ring
    rw [this]; linarith
  have hδ1 : δ ≤ 1 := by
    have : δ < R / 4 := by have := le_mul_of_one_le_left hδ0 hC11; linarith
    linarith
  have hz0 : |φ t₀ k| ≤ δ := by
    have := PiLp.norm_apply_le (φ t₀ - x) k
    rw [hδ]; simpa [hxk] using this
  have hq0' : |q (φ t₀)| ≤ L * δ := by rw [hδ]; exact hqL _ (hδ ▸ hδ1)
  have hΨ0 : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      spiralLyap ω hs K σ (φ t₀ k) (q (φ t₀)) ≤ E * (CV * δ) := by
    intro σ hσ
    refine (spiralLyap_le hK0 hσ).trans ?_
    rw [← hEdef, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (sqrt_sq_add_sq_le _ _).trans ?_
    have hp : |(q (φ t₀) - hs / 2 * φ t₀ k) / ω| ≤ (L + |hs| / 2) / ω * δ := by
      rw [abs_div, abs_of_pos hω, div_le_iff₀ hω]
      calc |q (φ t₀) - hs / 2 * φ t₀ k| ≤ |q (φ t₀)| + |hs / 2 * φ t₀ k| := abs_sub _ _
        _ ≤ L * δ + |hs| / 2 * δ := by
            rw [abs_mul, abs_div, abs_two]
            gcongr
        _ = (L + |hs| / 2) / ω * δ * ω := by field_simp
    calc |φ t₀ k| + |(q (φ t₀) - hs / 2 * φ t₀ k) / ω| ≤ δ + (L + |hs| / 2) / ω * δ :=
          add_le_add hz0 hp
      _ = CV * δ := by rw [hCV]; ring
  -- the segment analysis
  have key : ∀ s ∈ Icc t₀ t₁, (∀ u ∈ Icc t₀ s, ‖φ u - x‖ < R) →
      ∀ t ∈ Icc t₀ s, ‖φ t - x‖ ≤ C1 * δ ∧ c * (t - t₀) ≤ E * (CV * δ) := by
    intro s hsI hin
    rcases eq_or_lt_of_le hsI.1 with hst | hst
    · intro t ht
      have htt : t = t₀ := le_antisymm (hst ▸ ht.2) ht.1
      rw [htt, sub_self, mul_zero, ← hδ]
      exact ⟨le_mul_of_one_le_left hδ0 hC11, by positivity⟩
    have hseg : IsTrajectoryOn φ f t₀ s := hφ.mono (Icc_subset_Icc le_rfl hsI.2)
    have hinρ : ∀ u ∈ Icc t₀ s, ‖φ u - x‖ < ρ := fun u hu => lt_of_lt_of_le (hin u hu) hRρ
    have hdk : ∀ u ∈ Icc t₀ s, HasDerivWithinAt (fun u => (φ u k : ℝ)) (f (φ u) k : ℝ)
        (Icc t₀ s) u :=
      fun u hu => (EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt u
        (hseg u hu)
    have hdq : ∀ u ∈ Icc t₀ s, HasDerivWithinAt (fun u => q (φ u))
        (fderiv ℝ q (φ u) (f (φ u))) (Icc t₀ s) u :=
      fun u hu => (hqd (φ u)).hasFDerivAt.comp_hasDerivWithinAt u (hseg u hu)
    -- the spiral function decreases where `σ y_k > 0`
    have hderivW : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ u ∈ Icc t₀ s, 0 < σ * φ u k →
        ∃ d, HasDerivWithinAt (fun v => spiralLyap ω hs K σ (φ v k) (q (φ v))) d
          (Icc t₀ s) u ∧ d ≤ -c := by
      intro σ hσ u hu hσu
      have hu0 : φ u k ≠ 0 := by intro h0; rw [h0, mul_zero] at hσu; exact lt_irrefl _ hσu
      have hfk : f (φ u) k = q (φ u) / φ u k := by
        rw [eq_div_iff hu0, mul_comm]; exact hrel _ (hinρ u hu) hu0
      have hz' := hdk u hu
      rw [hfk] at hz'
      have hQ' := hdq u hu
      rw [hlie _ (hinρ u hu) hu0] at hQ'
      obtain ⟨d, hd, hdle⟩ := hasDerivWithinAt_spiralLyap (z := fun v => (φ v k : ℝ))
        (Q := fun v => q (φ v)) hω hω2 hK hK0 hε hσ hσu
        (hgR _ (hin u hu)) (hhR _ (hin u hu)) hz' hQ'
      exact ⟨d, hd, by rw [hcdef]; linarith⟩
    -- monotonicity on a stretch off the plane
    have hanti : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ a b, t₀ ≤ a → a ≤ b → b ≤ s →
        (∀ u ∈ Ioo a b, 0 < σ * φ u k) →
        ContinuousOn (fun v => spiralLyap ω hs K σ (φ v k) (q (φ v))) (Icc a b) →
        spiralLyap ω hs K σ (φ b k) (q (φ b)) + c * b ≤
          spiralLyap ω hs K σ (φ a k) (q (φ a)) + c * a := by
      intro σ hσ a b hta hab hbs hpos hcont
      have hA : AntitoneOn (fun v => spiralLyap ω hs K σ (φ v k) (q (φ v)) + c * v) (Icc a b) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
          (hcont.add (continuous_const.mul continuous_id).continuousOn) ?_ ?_
        · intro u hu
          rw [interior_Icc] at hu
          have huI : u ∈ Icc t₀ s := ⟨hta.trans hu.1.le, hu.2.le.trans hbs⟩
          obtain ⟨d, hd, -⟩ := hderivW σ hσ u huI (hpos u hu)
          have hd' := hd.hasDerivAt (Icc_mem_nhds (lt_of_le_of_lt hta hu.1)
            (lt_of_lt_of_le hu.2 hbs))
          exact (hd'.fun_add ((hasDerivAt_id' u).const_mul c)).differentiableAt.differentiableWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          have huI : u ∈ Icc t₀ s := ⟨hta.trans hu.1.le, hu.2.le.trans hbs⟩
          obtain ⟨d, hd, hdle⟩ := hderivW σ hσ u huI (hpos u hu)
          have hd' := hd.hasDerivAt (Icc_mem_nhds (lt_of_le_of_lt hta hu.1)
            (lt_of_lt_of_le hu.2 hbs))
          rw [(hd'.fun_add ((hasDerivAt_id' u).const_mul c)).deriv]
          simp only [mul_one]
          linarith
      exact hA ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    -- (i) no contact with the plane before `s`
    have hnt : ∀ τ ∈ Ico t₀ s, φ τ k ≠ 0 := by
      intro τ hτ hz
      have hτI : τ ∈ Icc t₀ s := Ico_subset_Icc_self hτ
      have hqτ : q (φ τ) = 0 := q_eq_zero_of_touch k hq.continuous
        (fun y hy hy0 => hrel y hy hy0) (fun y hy hy0 => hplane y hy hy0) hst hseg hinρ hτI hz
      obtain ⟨ι, hι⟩ : ∃ v, v = f (φ τ) k := ⟨_, rfl⟩
      have hι0 : ι ≠ 0 := by rw [hι]; exact hplane _ (hinρ τ hτI) hz
      obtain ⟨σ, hσ, hσι⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * ι = |ι| := by
        rcases le_or_gt 0 ι with h | h
        · exact ⟨1, Or.inl rfl, by rw [one_mul, abs_of_nonneg h]⟩
        · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h]; ring⟩
      have hσa : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
      have hdτ : HasDerivWithinAt (fun u => (φ u k : ℝ)) ι (Icc t₀ s) τ := by
        rw [hι]; exact hdk τ hτI
      obtain ⟨η, hη, hlin⟩ := exists_transversal hι0 hdτ hz
      obtain ⟨τ', hτ'⟩ : ∃ v, v = min s (τ + η / 2) := ⟨_, rfl⟩
      have hττ' : τ < τ' := by rw [hτ']; exact lt_min hτ.2 (by linarith)
      have hτ's : τ' ≤ s := by rw [hτ']; exact min_le_left _ _
      have hτ'η : τ' ≤ τ + η / 2 := by rw [hτ']; exact min_le_right _ _
      have hpos : ∀ u ∈ Ioc τ τ', 0 < σ * φ u k := by
        intro u hu
        have huI : u ∈ Icc t₀ s := ⟨hτ.1.trans hu.1.le, hu.2.trans hτ's⟩
        have huη : |u - τ| < η := by
          rw [abs_of_pos (by linarith [hu.1])]
          linarith [hu.2]
        have h1 := abs_le.mp (hlin u huI huη)
        have h2 : σ * φ u k ≥ σ * (ι * (u - τ)) - |ι| / 2 * |u - τ| := by
          have h3 : |σ * (φ u k - ι * (u - τ))| ≤ |ι| / 2 * |u - τ| := by
            rw [abs_mul, hσa, one_mul]; exact hlin u huI huη
          have := neg_abs_le (σ * (φ u k - ι * (u - τ)))
          have e : σ * (φ u k - ι * (u - τ)) = σ * φ u k - σ * (ι * (u - τ)) := by ring
          linarith
        have h4 : σ * (ι * (u - τ)) = |ι| * (u - τ) := by rw [← hσι]; ring
        rw [h4, abs_of_pos (by linarith [hu.1] : (0 : ℝ) < u - τ)] at h2
        have : 0 < |ι| * (u - τ) := mul_pos (abs_pos.mpr hι0) (by linarith [hu.1])
        linarith
      -- continuity of the spiral function on `[τ, τ']`, including at the contact point
      have hcont : ContinuousOn (fun v => spiralLyap ω hs K σ (φ v k) (q (φ v))) (Icc τ τ') := by
        intro u hu
        rcases eq_or_lt_of_le hu.1 with hut | hut
        · -- at the contact point the function vanishes and is squeezed by `E √V`
          subst hut
          have hval : spiralLyap ω hs K σ (φ τ k) (q (φ τ)) = 0 := by
            simp [spiralLyap, hz, hqτ]
          have hVc : ContinuousWithinAt (fun v => Real.sqrt (φ v k ^ 2 +
              ((q (φ v) - hs / 2 * φ v k) / ω) ^ 2) * E) (Icc τ τ') τ := by
            have hφc : ContinuousWithinAt φ (Icc τ τ') τ :=
              (hseg.continuousOn τ hτI).mono (Icc_subset_Icc hτ.1 hτ's)
            have hk : ContinuousWithinAt (fun v => φ v k) (Icc τ τ') τ :=
              ((EuclideanSpace.proj k : State n →L[ℝ] ℝ).continuous.continuousAt).comp_continuousWithinAt hφc
            have hqc : ContinuousWithinAt (fun v => q (φ v)) (Icc τ τ') τ :=
              hq.continuous.continuousAt.comp_continuousWithinAt hφc
            exact ((((hk.pow 2).add (((hqc.sub (hk.const_smul (hs / 2))).div_const ω).pow 2)).sqrt).mul
              continuousWithinAt_const)
          rw [ContinuousWithinAt, hval]
          have hlim : Tendsto (fun v => Real.sqrt (φ v k ^ 2 +
              ((q (φ v) - hs / 2 * φ v k) / ω) ^ 2) * E) (𝓝[Icc τ τ'] τ) (𝓝 0) := by
            have := hVc.tendsto
            simpa [hz, hqτ] using this
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
            (fun v => spiralLyap_nonneg _ _ _ _ _ _) (fun v => hEdef ▸ spiralLyap_le hK0 hσ)
        · obtain ⟨d, hd, -⟩ := hderivW σ hσ u ⟨hτ.1.trans hu.1, hu.2.trans hτ's⟩
            (hpos u ⟨hut, hu.2⟩)
          exact hd.continuousWithinAt.mono (Icc_subset_Icc (hτ.1) hτ's)
      have h1 := hanti σ hσ τ τ' hτ.1 hττ'.le hτ's (fun u hu => hpos u ⟨hu.1, hu.2.le⟩) hcont
      have hval : spiralLyap ω hs K σ (φ τ k) (q (φ τ)) = 0 := by
        simp [spiralLyap, hz, hqτ]
      rw [hval] at h1
      have := spiralLyap_nonneg ω hs K σ (φ τ' k) (q (φ τ'))
      have := mul_pos hc0 (sub_pos.mpr hττ')
      have e : c * (τ' - τ) = c * τ' - c * τ := by ring
      linarith
    -- (ii) the side of the plane
    have hz00 : φ t₀ k ≠ 0 := hnt t₀ ⟨le_rfl, hst⟩
    obtain ⟨σ, hσ, hσz0⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * φ t₀ k := by
      rcases lt_or_gt_of_ne hz00 with h | h
      · exact ⟨-1, Or.inr rfl, by linarith⟩
      · exact ⟨1, Or.inl rfl, by linarith⟩
    have hside : ∀ u ∈ Ico t₀ s, 0 < σ * φ u k := by
      intro u hu
      by_contra hneg
      push Not at hneg
      have hcz : ContinuousOn (fun v => σ * φ v k) (Icc t₀ u) :=
        continuous_const.continuousOn.mul
          (((EuclideanSpace.proj k : State n →L[ℝ] ℝ).continuous.comp_continuousOn
            (hseg.continuousOn.mono (Icc_subset_Icc le_rfl hu.2.le))))
      obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc' hu.1 hcz ⟨hneg, hσz0.le⟩
      have : φ τ k = 0 := by
        rcases hσ with rfl | rfl
        · simpa using hτ0
        · simpa using hτ0
      exact hnt τ ⟨hτ.1, lt_of_le_of_lt hτ.2 hu.2⟩ this
    -- (iii) decrease of the spiral function and the bounds on `[t₀, s)`
    have hbd : ∀ t ∈ Ico t₀ s, ‖φ t - x‖ ≤ C1 * δ ∧ c * (t - t₀) ≤ E * (CV * δ) := by
      intro t ht
      have hcont : ContinuousOn (fun v => spiralLyap ω hs K σ (φ v k) (q (φ v))) (Icc t₀ t) := by
        intro u hu
        obtain ⟨d, hd, -⟩ := hderivW σ hσ u ⟨hu.1, hu.2.trans ht.2.le⟩
          (hside u ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩)
        exact hd.continuousWithinAt.mono (Icc_subset_Icc le_rfl ht.2.le)
      have h1 := hanti σ hσ t₀ t le_rfl ht.1 ht.2.le
        (fun u hu => hside u ⟨hu.1.le, lt_trans hu.2 ht.2⟩) hcont
      have hΨt := spiralLyap_nonneg ω hs K σ (φ t k) (q (φ t))
      have hΨ0' := hΨ0 σ hσ
      have hlen : c * (t - t₀) ≤ E * (CV * δ) := by linarith
      -- `|y_k|` through the spiral function
      have hzk : |φ t k| ≤ E ^ 2 * CV * δ := by
        have h2 := le_spiralLyap (ω := ω) (hs := hs) (z := φ t k) (Q := q (φ t)) hK0 hσ
        have h3 : |φ t k| ≤ Real.sqrt (φ t k ^ 2 + ((q (φ t) - hs / 2 * φ t k) / ω) ^ 2) :=
          Real.abs_le_sqrt (by have := sq_nonneg ((q (φ t) - hs / 2 * φ t k) / ω); linarith)
        have h4 : Real.exp (-(K * (Real.pi / 2))) * E = 1 := hEc
        have h5 : Real.sqrt (φ t k ^ 2 + ((q (φ t) - hs / 2 * φ t k) / ω) ^ 2) ≤
            E * spiralLyap ω hs K σ (φ t k) (q (φ t)) := by
          have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ E)
          calc _ = E * (Real.sqrt (φ t k ^ 2 + ((q (φ t) - hs / 2 * φ t k) / ω) ^ 2) *
                Real.exp (-(K * (Real.pi / 2)))) := by
                  rw [show E * (Real.sqrt (φ t k ^ 2 + ((q (φ t) - hs / 2 * φ t k) / ω) ^ 2) *
                    Real.exp (-(K * (Real.pi / 2)))) = Real.sqrt (φ t k ^ 2 +
                      ((q (φ t) - hs / 2 * φ t k) / ω) ^ 2) *
                      (Real.exp (-(K * (Real.pi / 2))) * E) by ring, h4, mul_one]
            _ ≤ _ := this
        have hct : 0 ≤ c * (t - t₀) := mul_nonneg hc0.le (sub_nonneg.mpr ht.1)
        have h6 : spiralLyap ω hs K σ (φ t k) (q (φ t)) ≤ E * (CV * δ) := by linarith
        calc |φ t k| ≤ E * spiralLyap ω hs K σ (φ t k) (q (φ t)) := h3.trans h5
          _ ≤ E * (E * (CV * δ)) := mul_le_mul_of_nonneg_left h6 (by positivity)
          _ = E ^ 2 * CV * δ := by ring
      -- the other coordinates
      set P : State n →L[ℝ] State n := ContinuousLinearMap.id ℝ (State n) -
        (EuclideanSpace.proj k : State n →L[ℝ] ℝ).smulRight (EuclideanSpace.single k (1 : ℝ))
        with hPdef
      have hP : ∀ v, P v = v - v k • EuclideanSpace.single k (1 : ℝ) := fun v => by
        simp [hPdef]
      have htI : t ∈ Icc t₀ s := Ico_subset_Icc_self ht
      have hseg' : IsTrajectoryOn φ f t₀ t := hseg.mono (Icc_subset_Icc le_rfl ht.2.le)
      have hdP : ∀ u ∈ Icc t₀ t, HasDerivWithinAt (fun u => P (φ u)) (P (f (φ u))) (Icc t₀ t) u :=
        fun u hu => P.hasFDerivAt.comp_hasDerivWithinAt u (hseg' u hu)
      have hPb := norm_image_sub_le_of_norm_deriv_le_segment' hdP (fun u hu => by
        rw [hP]; exact hbound _ (hinρ u ⟨hu.1, hu.2.le.trans ht.2.le⟩)) t ⟨ht.1, le_rfl⟩
      have hsplit := norm_le_norm_sub_smul_single_add k (φ t - x)
      rw [← hP] at hsplit
      have hPx : P (φ t - x) = (P (φ t) - P (φ t₀)) + P (φ t₀ - x) := by
        simp only [map_sub]; abel
      have hP0 : ‖P (φ t₀ - x)‖ ≤ δ := by rw [hP, hδ]; exact norm_sub_smul_single_le k _
      have hkx : (φ t - x) k = φ t k := by simp [hxk]
      rw [hPx, hkx] at hsplit
      have h7 := norm_add_le (P (φ t) - P (φ t₀)) (P (φ t₀ - x))
      have hlen' : t - t₀ ≤ 2 * E ^ 2 * CV * δ := by
        have : c * (t - t₀) ≤ c * (2 * E ^ 2 * CV * δ) := by
          have : c * (2 * E ^ 2 * CV * δ) = (2 * (c * E)) * (E * (CV * δ)) := by ring
          rw [this, hcE]; linarith
        exact le_of_mul_le_mul_left this hc0
      have hM' : M * (t - t₀) ≤ M * (2 * E ^ 2 * CV * δ) := mul_le_mul_of_nonneg_left hlen' hM0
      refine ⟨?_, hlen⟩
      rw [hC1]
      linarith
    -- (iv) up to `s`
    intro t ht
    have hc1 : ContinuousOn (fun t => ‖φ t - x‖) (Icc t₀ s) :=
      continuous_norm.comp_continuousOn (hseg.continuousOn.sub continuousOn_const)
    have hc2 : ContinuousOn (fun t => c * (t - t₀)) (Icc t₀ s) :=
      (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
    exact ⟨forall_Icc_of_forall_Ico hst hc1 (fun t ht => (hbd t ht).1) t ht,
      forall_Icc_of_forall_Ico hst hc2 (fun t ht => (hbd t ht).2) t ht⟩
  -- bootstrap: the solution stays in the ball of radius `R / 2`
  intro t ht
  have ht₁ : t₀ ≤ t₁ := ht.1.trans ht.2
  have hstay : ∀ u ∈ Icc t₀ t₁, ‖φ u - x‖ < R / 2 := by
    intro u hu
    by_contra hfar
    push Not at hfar
    obtain ⟨τ, hτ, hτeq, hτin⟩ := exists_first_sphere_hit hφ.continuousOn
      (show ‖φ t₀ - x‖ < R / 2 by
        rw [← hδ]; have := le_mul_of_one_le_left hδ0 hC11; linarith) hu hfar
    have h1 := (key τ hτ (fun v hv => lt_of_le_of_lt (hτin v hv) (by linarith)) τ
      ⟨hτ.1, le_rfl⟩).1
    linarith
  obtain ⟨h1, h2⟩ := key t₁ ⟨ht₁, le_rfl⟩ (fun u hu => lt_of_lt_of_le (hstay u hu) (by linarith))
    t ht
  -- the time is at most `1/2`, so `e^{-(t - t₀)} ≥ 1/2`
  have hT : t - t₀ ≤ 1 / 2 := by
    have h3 : E * (CV * δ) ≤ c / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hδc
      have : E * (CV * δ) = δ * (2 * E * CV) / 2 := by ring
      rw [this]; linarith
    have : c * (t - t₀) ≤ c * (1 / 2) := by linarith
    exact le_of_mul_le_mul_left this hc0
  have hexp : 1 / 2 ≤ Real.exp (-1 * (t - t₀)) := by
    have := Real.add_one_le_exp (-1 * (t - t₀)); linarith
  calc ‖φ t - x‖ ≤ C1 * δ := h1
    _ ≤ 2 * C1 * Real.exp (-1 * (t - t₀)) * δ := by
        have h5 : 1 ≤ 2 * Real.exp (-1 * (t - t₀)) := by linarith
        have h6 := mul_le_mul_of_nonneg_left h5 (mul_nonneg (by linarith : (0 : ℝ) ≤ C1) hδ0)
        have h7 : C1 * δ * (2 * Real.exp (-1 * (t - t₀))) =
            2 * C1 * Real.exp (-1 * (t - t₀)) * δ := by ring
        linarith

end powerlib.Dynamics
