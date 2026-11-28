import theorem.Map.AsymptoticPhaseLipschitz
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # The local asymptotic phase is Lipschitz: a smooth cut-off

The Lipschitz estimates of `theorem/Map/AsymptoticPhaseLipschitz.lean` need nonlinearities that
are globally `ε`-Lipschitz **and** differentiable with Lipschitz derivatives. The cut-off of
`exists_local_centreManifold` (`f₀ ∘ ballRetract ρ`, the radial retraction) gives the first
property only: it is not differentiable on the sphere `‖p‖ = ρ`. On finite-dimensional spaces a
smooth bump does both: for `N` of class `C²` near `0` with `N(0) = 0`, `DN(0) = 0`, the map
`Ñ = χ(·/r) N`, with a fixed smooth bump `χ` equal to `1` on the unit ball and `0` outside the
ball of radius `2`, agrees with `N` on `‖p‖ ≤ r`, has `‖DÑ‖ ≤ (1 + 2 sup ‖Dχ‖) sup_{‖x‖ ≤ 2r} ‖DN‖`
(small for small `r`, since `‖N(x)‖ ≤ ‖x‖ sup ‖DN‖` on the ball and `‖D(χ(·/r))‖ ≤ sup ‖Dχ‖/r`),
and is of class `C²` with compact support, so its derivative is globally Lipschitz
(`exists_smooth_cutoff`; the Lipschitz constant of `DÑ` is not made explicit, it may grow as
`r → 0`, which only shrinks the neighbourhood of the fixed point where the estimate applies).

With these cut-offs the local asymptotic phase (`exists_local_asymptoticPhase`) is locally
Lipschitz under the bunching condition `(b + 2ε)(α + ε) < a − ε`
(`exists_local_asymptoticPhase_lipschitz`). For a simple multiplier `−1` (`A = −id`, the setting
of `theorem/Periodic/FlipReduction.lean`) and `ε = (1 − b)/8` the phase of the cut-off map is
`8`-Lipschitz from every point of a ball around the fixed point, and it shadows every orbit of the
original map that stays in the ball `‖p‖ ≤ ρ` with the rate `(1 + 3b)/4`
(`exists_local_flip_asymptoticPhase_lipschitz`): the asymptotic phase of a flip is Lipschitz near
the fixed point.

Scope.
* Finite-dimensional real normed spaces (`X × Y` with the max norm; a smooth bump exists, and
  compactly supported continuous maps are bounded). `f₀`, `g₀` of class `C²` at `0`
  (`ContDiffAt ℝ 2`), with `f₀(0) = g₀(0) = 0` and vanishing derivatives at `0`. The cut-offs and
  the graph are those of the cut-off map; local centre manifolds are not unique.
* The flip statement is about a map already in the split form `(−x + f₀(x, y), B y + g₀(x, y))`
  with `‖B y‖ ≤ b ‖y‖`, `b < 1`. The coordinates of `theorem/Periodic/FlipReduction.lean`
  (`coordMap`, the adapted norm of the stable part) bring a period map with a simple multiplier
  `−1` to this form, but that module cuts off with the radial retraction on `ℝⁿ` and assumes only
  a Taylor expansion at the fixed point; a period map of class `C²` composed with those
  coordinates is not restated here.
* Generic; nothing here describes a physical system (foundation).

Source: the open item of `theorem/Map/AsymptoticPhaseLipschitz.lean` (Scope: the radial cut-off
is not differentiable); smooth bump functions on finite-dimensional spaces (Mathlib
`ContDiffBump`); Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2 (cut-offs of class
`C^k` for local centre manifolds); Pugh, Shub and Wilkinson, "Hölder foliations", Duke Math.
J. 86 (1997) (centre bunching).

Results.
* `exists_smooth_cutoff`: an `ε`-Lipschitz map, differentiable with Lipschitz derivative, equal to
  `N` near `0`.
* `exists_local_asymptoticPhase_lipschitz`: the local asymptotic phase of the smoothly cut-off
  map is locally Lipschitz under bunching, with the shadowing of `exists_local_asymptoticPhase`.
* **The theorem** `exists_local_flip_asymptoticPhase_lipschitz`: near a fixed point with the
  multiplier `−1` the phase is `8`-Lipschitz from a ball `‖p'‖ ≤ δ`, locally Lipschitz, and
  shadows the local orbits with the constant `6/5` and the rate `(1 + 3b)/4`.

Corrections.
None: an extension (the local form of `theorem/Map/AsymptoticPhaseLipschitz.lean`).

Family and connection conclusions.
None: static evidence on maps.
-/

noncomputable section

open Filter Topology Metric

namespace powerlib.Map.CenterManifold

section SmoothCutoff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A smooth cut-off.** A map `N` of class `C²` near `0` with `N(0) = 0` and `DN(0) = 0`, on a
finite-dimensional space, agrees on a closed ball `‖p‖ ≤ ρ` with a globally `ε`-Lipschitz map
`Ñ`, `Ñ(0) = 0`, which is differentiable with a globally Lipschitz derivative, for every `ε > 0`:
`Ñ = χ(·/r) N` with a smooth bump `χ` (`1` on the unit ball, `0` outside the ball of radius `2`),
`‖DÑ‖ ≤ sup_{‖x‖ ≤ 2r} ‖DN‖ (1 + 2 sup ‖Dχ‖)`, and `Ñ` of class `C²` with compact support. -/
@[tmio T, powerlib_foundation] theorem exists_smooth_cutoff {N : E → F} (hN : ContDiffAt ℝ 2 N 0)
    (hN0 : N 0 = 0) (hD0 : fderiv ℝ N 0 = 0) {ε : NNReal} (hε : 0 < ε) :
    ∃ ρ > 0, ∃ Ñ : E → F, LipschitzWith ε Ñ ∧ Ñ 0 = 0 ∧ (∀ p, ‖p‖ ≤ ρ → Ñ p = N p) ∧
      Differentiable ℝ Ñ ∧ ∃ L₂ : NNReal, LipschitzWith L₂ (fderiv ℝ Ñ) := by
  have hεr : (0 : ℝ) < ε := hε
  -- the ball where `N` is of class `C²`
  obtain ⟨u, hu, hNu⟩ := hN.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hNat : ∀ x : E, ‖x‖ < ρ₀ → ContDiffAt ℝ 2 N x := fun x hx =>
    (hNu.mono hball).contDiffAt (isOpen_ball.mem_nhds (by simpa using hx))
  have hNd : ∀ x : E, ‖x‖ < ρ₀ → DifferentiableAt ℝ N x := fun x hx =>
    (hNat x hx).differentiableAt (by norm_num)
  -- a fixed bump and the bound of its derivative
  let φ₁ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hφs : ContDiff ℝ 2 φ₁ := φ₁.contDiff
  obtain ⟨C, hC⟩ := (hφs.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (φ₁.hasCompactSupport.fderiv ℝ)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- smallness of `DN` near `0`
  have hDc : ContinuousAt (fderiv ℝ N) 0 :=
    (hN.fderiv_right (m := 1) (by norm_num)).continuousAt
  set η := (ε : ℝ) / (1 + 2 * C) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨r₁, hr₁, hr₁b⟩ := Metric.continuousAt_iff.mp hDc η hη0
  have hDN : ∀ x : E, ‖x‖ < r₁ → ‖fderiv ℝ N x‖ ≤ η := fun x hx => by
    have := hr₁b (x := x) (by simpa using hx)
    rw [dist_eq_norm, hD0, sub_zero] at this
    exact this.le
  set r := min r₁ ρ₀ / 4 with hr
  have hr0 : 0 < r := by positivity
  have h2r : 2 * r < ρ₀ := by have := min_le_right r₁ ρ₀; linarith
  have h2r' : 2 * r < r₁ := by have := min_le_left r₁ ρ₀; linarith
  -- the scaled bump
  set χ : E → ℝ := fun x => φ₁ (r⁻¹ • x) with hχ
  have hχs : ContDiff ℝ 2 χ := hφs.comp (contDiff_id.const_smul r⁻¹)
  have hnorm : ∀ x : E, ‖r⁻¹ • x‖ = ‖x‖ / r := fun x => by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le), inv_mul_eq_div]
  have hχ1 : ∀ x : E, ‖x‖ ≤ r → χ x = 1 := fun x hx => by
    refine φ₁.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right, hnorm]
    show ‖x‖ / r ≤ 1
    rw [div_le_one hr0]
    exact hx
  have hχ0 : ∀ x : E, 2 * r ≤ ‖x‖ → χ x = 0 := fun x hx => by
    refine φ₁.zero_of_le_dist ?_
    rw [dist_zero_right, hnorm]
    show (2 : ℝ) ≤ ‖x‖ / r
    rw [le_div_iff₀ hr0]
    exact hx
  have hχnn : ∀ x, 0 ≤ χ x := fun x => φ₁.nonneg
  have hχle : ∀ x, χ x ≤ 1 := fun x => φ₁.le_one
  have hχd : ∀ x : E, HasFDerivAt χ
      ((fderiv ℝ φ₁ (r⁻¹ • x)).comp (r⁻¹ • ContinuousLinearMap.id ℝ E)) x := fun x =>
    ((hφs.differentiable (by norm_num)) (r⁻¹ • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul r⁻¹)
  have hχD : ∀ x : E, ‖fderiv ℝ χ x‖ ≤ C / r := fun x => by
    rw [(hχd x).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖r⁻¹ • ContinuousLinearMap.id ℝ E‖ ≤ r⁻¹ := by
      refine (norm_smul_le (r⁻¹ : ℝ) (ContinuousLinearMap.id ℝ E)).trans ?_
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
      exact mul_le_of_le_one_right (inv_nonneg.mpr hr0.le) ContinuousLinearMap.norm_id_le
    calc _ ≤ C * r⁻¹ := mul_le_mul (hC _) h1 (norm_nonneg _) hC0
      _ = C / r := by rw [div_eq_mul_inv]
  have hχD0 : ∀ x : E, 2 * r ≤ ‖x‖ → fderiv ℝ χ x = 0 := fun x hx => by
    have : IsLocalMin χ x := Filter.Eventually.of_forall fun y => by
      rw [hχ0 x hx]; exact hχnn y
    exact this.fderiv_eq_zero
  -- the cut-off
  set Ñ : E → F := fun x => χ x • N x with hÑ
  have hÑ0 : ∀ x : E, 2 * r ≤ ‖x‖ → Ñ x = 0 := fun x hx => by
    simp only [hÑ, hχ0 x hx, zero_smul]
  have hÑev : ∀ x : E, 2 * r < ‖x‖ → Ñ =ᶠ[𝓝 x] fun _ => 0 := fun x hx => by
    have hopen : IsOpen {y : E | 2 * r < ‖y‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hÑ0 y (le_of_lt hy)
  have hbound : ∀ x : E, ∃ D : E →L[ℝ] F, HasFDerivAt Ñ D x ∧ ‖D‖ ≤ ε := by
    intro x
    by_cases hx : ‖x‖ < ρ₀
    · refine ⟨χ x • fderiv ℝ N x + (fderiv ℝ χ x).smulRight (N x),
        ((hχs.differentiable (by norm_num)) x).hasFDerivAt.smul (hNd x hx).hasFDerivAt, ?_⟩
      by_cases hx2 : ‖x‖ < 2 * r
      · have hDx : ‖fderiv ℝ N x‖ ≤ η := hDN x (by linarith)
        -- the mean value inequality on the ball of radius `2r`
        have hNx : ‖N x‖ ≤ η * ‖x‖ := by
          have hsub : ball (0 : E) (2 * r) ⊆ ball 0 ρ₀ := ball_subset_ball h2r.le
          have := (convex_ball (0 : E) (2 * r)).norm_image_sub_le_of_norm_fderiv_le
            (f := N) (C := η) (fun y hy => hNd y (by simpa using hsub hy))
            (fun y hy => hDN y (by have := mem_ball_zero_iff.mp hy; linarith))
            (mem_ball_self (by positivity)) (by simpa using hx2)
          simpa [hN0] using this
        calc ‖χ x • fderiv ℝ N x + (fderiv ℝ χ x).smulRight (N x)‖
            ≤ ‖χ x • fderiv ℝ N x‖ + ‖(fderiv ℝ χ x).smulRight (N x)‖ := norm_add_le _ _
          _ = |χ x| * ‖fderiv ℝ N x‖ + ‖fderiv ℝ χ x‖ * ‖N x‖ := by
              rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
          _ ≤ 1 * η + C / r * (η * (2 * r)) := by
              rw [abs_of_nonneg (hχnn x)]
              refine add_le_add (mul_le_mul (hχle x) hDx (norm_nonneg _) zero_le_one)
                (mul_le_mul (hχD x) (hNx.trans (mul_le_mul_of_nonneg_left hx2.le hη0.le))
                  (norm_nonneg _) (by positivity))
          _ = ε := by
              have h12 : (1 + 2 * C) ≠ 0 := by positivity
              rw [hη]; field_simp
      · push Not at hx2
        rw [hχ0 x hx2, hχD0 x hx2, zero_smul, ContinuousLinearMap.zero_smulRight, add_zero,
          norm_zero]
        exact ε.coe_nonneg
    · push Not at hx
      exact ⟨0, (hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq (hÑev x (by linarith)),
        by rw [norm_zero]; exact ε.coe_nonneg⟩
  choose D hD hDε using hbound
  have hdiff : Differentiable ℝ Ñ := fun x => (hD x).differentiableAt
  -- `Ñ` is of class `C²` with compact support
  have hC2 : ContDiff ℝ 2 Ñ := by
    refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : ‖x‖ < ρ₀
    · exact hχs.contDiffAt.smul (hNat x hx)
    · push Not at hx
      exact contDiffAt_const.congr_of_eventuallyEq (hÑev x (by linarith))
  have hcs : HasCompactSupport Ñ := HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * r))
    fun x hx => hÑ0 x (by rw [mem_closedBall, dist_zero_right] at hx; push Not at hx; exact hx.le)
  have hC1 : ContDiff ℝ 1 (fderiv ℝ Ñ) := hC2.fderiv_right (m := 1) (by norm_num)
  obtain ⟨L, hL⟩ := (hC1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    ((hcs.fderiv ℝ).fderiv ℝ)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  refine ⟨r, hr0, Ñ, lipschitzWith_of_nnnorm_fderiv_le hdiff fun x => ?_, ?_, fun p hp => ?_,
    hdiff, L.toNNReal, lipschitzWith_of_nnnorm_fderiv_le (hC1.differentiable (by norm_num))
      fun x => ?_⟩
  · rw [(hD x).fderiv, ← NNReal.coe_le_coe, coe_nnnorm]; exact hDε x
  · simp only [hÑ, hN0, smul_zero]
  · simp only [hÑ, hχ1 p hp, one_smul]
  · rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL0]; exact hL x

end SmoothCutoff

/-! ## The local phase -/

section Local

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {A : X →L[ℝ] X} {B : Y →L[ℝ] Y} {a b α : ℝ} {ε : NNReal}

/-- **The local asymptotic phase with a smooth cut-off, Lipschitz under bunching.** Let
`F₀(x, y) = (A x + f₀(x, y), B y + g₀(x, y))` on finite-dimensional `X × Y`, with `f₀`, `g₀` of
class `C²` near `0`, vanishing at `0` with vanishing derivative there, `a ‖x‖ ≤ ‖A x‖ ≤ α ‖x‖`,
`‖B y‖ ≤ b ‖y‖`, and `ε > 0` with the gap `b + 3ε < a`, the bunching condition
`(b + 2ε)(α + ε) < a − ε` and `b + 2ε < 1`. There are a radius `ρ > 0` and `ε`-Lipschitz
cut-offs `f`, `g` equal to `f₀`, `g₀` on `‖p‖ ≤ ρ`, differentiable with Lipschitz derivatives
(`exists_smooth_cutoff`), whose invariant `1`-Lipschitz graph `h` through `0` has a **locally
Lipschitz** asymptotic phase `φ`; every orbit of `F₀` that stays in the ball is shadowed by the
reduced orbit of its phase, as in `exists_local_asymptoticPhase`. -/
@[tmio T, powerlib_foundation] theorem exists_local_asymptoticPhase_lipschitz
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hAα : ∀ x, ‖A x‖ ≤ α * ‖x‖)
    (haα : a ≤ α) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) {f₀ : X × Y → X} {g₀ : X × Y → Y}
    (hf : ContDiffAt ℝ 2 f₀ 0) (hg : ContDiffAt ℝ 2 g₀ 0) (hf0 : f₀ 0 = 0) (hg0 : g₀ 0 = 0)
    (hDf : fderiv ℝ f₀ 0 = 0) (hDg : fderiv ℝ g₀ 0 = 0) (hε : 0 < ε) (hgap : b + 3 * ε < a)
    (hbunch : (b + 2 * ε) * (α + ε) < a - ε) (hθ : b + 2 * ε < 1) :
    ∃ ρ > 0, ∃ f : X × Y → X, ∃ g : X × Y → Y,
      LipschitzWith ε f ∧ LipschitzWith ε g ∧ f 0 = 0 ∧ g 0 = 0 ∧
      (∀ p, ‖p‖ ≤ ρ → f p = f₀ p ∧ g p = g₀ p) ∧
      (∃ L₂ : NNReal, Differentiable ℝ f ∧ LipschitzWith L₂ (fderiv ℝ f) ∧
        Differentiable ℝ g ∧ LipschitzWith L₂ (fderiv ℝ g)) ∧
      ∃ h : X → Y, LipschitzWith 1 h ∧ h 0 = 0 ∧
        (∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) ∧
        LocallyLipschitz (asymptoticPhase A B f g h) ∧
        ∀ (p : X × Y) (k : ℕ), (∀ j < k, ‖(splitMap A B f₀ g₀)^[j] p‖ ≤ ρ) →
          ‖(splitMap A B f₀ g₀)^[k] p -
              ((reducedMap A f h)^[k] (asymptoticPhase A B f g h p),
                h ((reducedMap A f h)^[k] (asymptoticPhase A B f g h p)))‖ ≤
            (1 + ε / (a - b - 3 * ε)) * (b + 2 * ε) ^ k * ‖p.2 - h p.1‖ := by
  obtain ⟨ρ₁, hρ₁, f, hfl, hf0', hff, hfd, L₁, hfL⟩ := exists_smooth_cutoff hf hf0 hDf hε
  obtain ⟨ρ₂, hρ₂, g, hgl, hg0', hgg, hgd, L₂, hgL⟩ := exists_smooth_cutoff hg hg0 hDg hε
  set ρ := min ρ₁ ρ₂ with hρ
  have hagree : ∀ p, ‖p‖ ≤ ρ → f p = f₀ p ∧ g p = g₀ p := fun p hp =>
    ⟨hff p (hp.trans (min_le_left _ _)), hgg p (hp.trans (min_le_right _ _))⟩
  have hsplit : ∀ p, ‖p‖ ≤ ρ → splitMap A B f₀ g₀ p = splitMap A B f g p := fun p hp => by
    simp only [splitMap, (hagree p hp).1, (hagree p hp).2]
  obtain ⟨h, ⟨hlip, hh0, hinv⟩, -⟩ :=
    exists_unique_invariantGraph hAs hA hB hb hfl hgl hf0' hg0' hgap
  have hfL' : LipschitzWith (max L₁ L₂) (fderiv ℝ f) := hfL.weaken (le_max_left _ _)
  have hgL' : LipschitzWith (max L₁ L₂) (fderiv ℝ g) := hgL.weaken (le_max_right _ _)
  refine ⟨ρ, lt_min hρ₁ hρ₂, f, g, hfl, hgl, hf0', hg0', hagree, ⟨max L₁ L₂, hfd, hfL', hgd, hgL'⟩,
    h, hlip, hh0, hinv, locallyLipschitz_asymptoticPhase hAs hA hAα haα hB hb hfl hgl hgap hbunch
      hθ hlip hinv hfd hfL' hgd hgL', fun p k hk => ?_⟩
  have heq : ∀ j ≤ k, (splitMap A B f₀ g₀)^[j] p = (splitMap A B f g)^[j] p := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih (Nat.le_of_succ_le hj)]
      exact hsplit _ (hk j hj)
  rw [heq k le_rfl, ← splitMap_iterate_graph hinv]
  exact norm_iterate_sub_asymptoticPhase_le hAs hA hB hb hfl hgl hgap hlip hinv p k

/-- **Near a fixed point with a simple multiplier `−1` the phase is Lipschitz.** For
`F₀(x, y) = (−x + f₀(x, y), B y + g₀(x, y))` on finite-dimensional `X × Y` (the flip setting of
`theorem/Periodic/FlipReduction.lean`: `A = −id`, `a = α = 1`), `‖B y‖ ≤ b ‖y‖` with
`0 ≤ b < 1`, and `f₀`, `g₀` of class `C²` near `0` with vanishing value and derivative at `0`:
with `ε = (1 − b)/8` there are a radius `ρ`, smooth cut-offs `f`, `g` equal to `f₀`, `g₀` on
`‖p‖ ≤ ρ` and their invariant graph `h`, such that the asymptotic phase `φ` is `8`-Lipschitz
from every point `p'` of a ball `‖p'‖ ≤ δ` around the fixed point, locally Lipschitz everywhere,
and shadows the orbits of `F₀` that stay in the ball:
`‖F₀ᵏ p − (rᵏ φ(p), h(rᵏ φ(p)))‖ ≤ (6/5) ((1 + 3b)/4)ᵏ ‖p₂ − h(p₁)‖`. -/
@[tmio T, powerlib_foundation] theorem exists_local_flip_asymptoticPhase_lipschitz {b : ℝ}
    (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hb1 : b < 1) {f₀ : X × Y → X} {g₀ : X × Y → Y}
    (hf : ContDiffAt ℝ 2 f₀ 0) (hg : ContDiffAt ℝ 2 g₀ 0) (hf0 : f₀ 0 = 0) (hg0 : g₀ 0 = 0)
    (hDf : fderiv ℝ f₀ 0 = 0) (hDg : fderiv ℝ g₀ 0 = 0) :
    ∃ ρ > 0, ∃ f : X × Y → X, ∃ g : X × Y → Y, (∀ p, ‖p‖ ≤ ρ → f p = f₀ p ∧ g p = g₀ p) ∧
      ∃ h : X → Y, LipschitzWith 1 h ∧ h 0 = 0 ∧
        (∀ x, h (-x + f (x, h x)) = B (h x) + g (x, h x)) ∧
        (∃ δ > 0, ∀ p p' : X × Y, ‖p'‖ ≤ δ →
          ‖asymptoticPhase (-ContinuousLinearMap.id ℝ X) B f g h p -
            asymptoticPhase (-ContinuousLinearMap.id ℝ X) B f g h p'‖ ≤ 8 * ‖p - p'‖) ∧
        LocallyLipschitz (asymptoticPhase (-ContinuousLinearMap.id ℝ X) B f g h) ∧
        ∀ (p : X × Y) (k : ℕ),
          (∀ j < k, ‖(splitMap (-ContinuousLinearMap.id ℝ X) B f₀ g₀)^[j] p‖ ≤ ρ) →
          ‖(splitMap (-ContinuousLinearMap.id ℝ X) B f₀ g₀)^[k] p -
              ((reducedMap (-ContinuousLinearMap.id ℝ X) f h)^[k]
                  (asymptoticPhase (-ContinuousLinearMap.id ℝ X) B f g h p),
                h ((reducedMap (-ContinuousLinearMap.id ℝ X) f h)^[k]
                  (asymptoticPhase (-ContinuousLinearMap.id ℝ X) B f g h p)))‖ ≤
            6 / 5 * ((1 + 3 * b) / 4) ^ k * ‖p.2 - h p.1‖ := by
  set A := -ContinuousLinearMap.id ℝ X with hAdef
  have hAs : Function.Surjective A := fun x => ⟨-x, by simp [hAdef]⟩
  have hA : ∀ x, 1 * ‖x‖ ≤ ‖A x‖ := fun x => by simp [hAdef]
  have hAα : ∀ x, ‖A x‖ ≤ 1 * ‖x‖ := fun x => by simp [hAdef]
  let ε : NNReal := ⟨(1 - b) / 8, by linarith⟩
  have hεe : (ε : ℝ) = (1 - b) / 8 := rfl
  have hε : 0 < ε := by rw [← NNReal.coe_pos, hεe]; linarith
  have hgap : b + 3 * ε < 1 := by rw [hεe]; linarith
  have hθ : b + 2 * ε < 1 := by rw [hεe]; linarith
  have hbunch : (b + 2 * ε) * (1 + ε) < 1 - ε := by
    rw [hεe]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - b) (by linarith : (0 : ℝ) < 19 - 3 * b)]
  obtain ⟨ρ, hρ, f, g, hfl, hgl, -, -, hagree, ⟨L₂, hfd, hfL, hgd, hgL⟩, h, hlip, hh0, hinv,
    hloc, hsh⟩ := exists_local_asymptoticPhase_lipschitz hAs hA hAα le_rfl hB hb hf hg hf0 hg0
      hDf hDg hε hgap hbunch hθ
  have hinv' : ∀ x, h (-x + f (x, h x)) = B (h x) + g (x, h x) := fun x => by
    simpa [hAdef] using hinv x
  obtain ⟨hflip, -⟩ := flip_asymptoticPhase_lipschitz hB hb hb1 hε hεe.le hfl hgl hfd hfL hgd hgL
    hlip hinv'
  have hL₂ := L₂.coe_nonneg
  set δ := (1 - b) / (40 * (L₂ + 1)) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; apply div_pos <;> linarith
  refine ⟨ρ, hρ, f, g, hagree, h, hlip, hh0, hinv', ⟨δ, hδ0, fun p p' hp' => ?_⟩, hloc,
    fun p k hk => ?_⟩
  · refine hflip (2 * δ) p p' ?_ ?_
    · rw [hδ]
      have h1 : (L₂ : ℝ) * (2 * ((1 - b) / (40 * (L₂ + 1)))) =
          (1 - b) / 20 * (L₂ / (L₂ + 1)) := by field_simp; ring
      rw [h1]
      have h2 : (L₂ : ℝ) / (L₂ + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have h3 : 0 ≤ (1 - b) / 20 := by linarith
      calc _ ≤ (1 - b) / 20 * 1 := mul_le_mul_of_nonneg_left h2 h3
        _ = _ := mul_one _
    · have h1 : ‖h p'.1‖ ≤ ‖p'.1‖ := by simpa [hh0] using hlip.norm_sub_le p'.1 0
      calc ‖p'.2 - h p'.1‖ ≤ ‖p'.2‖ + ‖h p'.1‖ := norm_sub_le _ _
        _ ≤ ‖p'‖ + ‖p'‖ := add_le_add (norm_snd_le p') (h1.trans (norm_fst_le p'))
        _ ≤ 2 * δ := by linarith
  · have e1 : (1 : ℝ) + ε / (1 - b - 3 * ε) = 6 / 5 := by
      rw [hεe]
      have : 1 - b ≠ 0 := by linarith
      field_simp
      ring
    have e2 : b + 2 * (ε : ℝ) = (1 + 3 * b) / 4 := by rw [hεe]; ring
    have := hsh p k hk
    rwa [e1, e2] at this

end Local

end powerlib.Map.CenterManifold
