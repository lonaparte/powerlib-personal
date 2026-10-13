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

end powerlib.Dynamics
