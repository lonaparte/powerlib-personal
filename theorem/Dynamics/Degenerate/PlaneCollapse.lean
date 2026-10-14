import theorem.Dynamics.Coordinates
import theorem.Dynamics.Calculus
import theorem.Dynamics.Locality

/-! # Local tools for fields that are singular or only locally regular

Generic foundation, independent of any model, written for GFL model B
(`theorem/GFL/DCLink/ModelBStability.lean`, `theorem/GFL/DCLink/ModelBBoundary.lean`), whose field
contains `1 / V_dc`. Model boundary: an arbitrary autonomous field `f : ℝⁿ → ℝⁿ` (continuous time,
no inputs), read through the Flow semantics of `theorem/Flow/Defs.lean` (solution segments, i.e.
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
  exit `Dynamics.forall_lt_of_first_exit`), and there `y_k²` grows linearly.
* `unstable_of_cone`: instability from a cone `{σ y_k > 0, W ≥ 0}` at the plane that the field
  enters through its boundary and in which `σ y_k` grows at a positive rate (the degenerate case of
  the plane where the power term vanishes at `x`); helpers `Dynamics.deriv_nonpos_of_isMinOn_right`,
  `Dynamics.exists_pos_of_hasDerivAt` (`theorem/Dynamics/Calculus.lean`).
* `locallyExponentiallyStable_of_spiral`: spiral collapse. If off the plane `y_k f_k = q` with a
  `C¹` function `q`, `q(x) = 0`, `dq/dt = g + h q / y_k`, and `h(x)² + 4 g(x) < 0`, while on the
  plane `f_k ≠ 0`, then `x` satisfies the local exponential estimate: in the time `dτ = dt / y_k`
  the pair `(y_k, q)` is a linear focus; the function `spiralLyap` (radius times
  `exp(σ K angle)`) decreases at a uniform rate (`hasDerivWithinAt_spiralLyap`, algebra
  `spiral_ineq`), a segment can touch the plane only where `q = 0` (`q_eq_zero_of_touch`) and
  hence only at its end, and segments last `O(‖y(t₀) − x‖)`.
* `unstable_of_barriers`: instability from seeds arbitrarily close to `x`, each with a trapping
  region `{σ y_k ≥ σ y₀_k / 2, W₁, W₂, W₃ ≥ 0}` (three `C¹` barriers crossed inwards) in which
  `σ y_k` does not decrease and a bounded `C¹` function grows at a positive rate; generalizes
  `unstable_of_cone` (helpers `Dynamics.eventually_pos_of_hasDerivAt`, `exists_lipschitz_bound`).
* `unstable_of_degenerate_node`: in the setting of `locallyExponentiallyStable_of_spiral`, a double
  root `h(x)/2 ≠ 0` of `λ² − h(x)λ − g(x)` (`h(x)² + 4g(x) = 0`) with `C¹` coefficients `g, h`
  makes `x` unstable: on the side `σ = sign h(x)` the shrinking cone
  `q ≥ (|h(x)|/2 − √w) w` (`w = σ y_k`), cut down to a horn `‖y − x‖ ≤ (K + 1) w`, is entered by the
  field because its margin `√w` dominates the `O(w)` variation of `g, h`.
* `not_locallyExponentiallyStable_of_nilpotent`: if `g(x) = h(x) = 0` (`C¹`), `∂_k q = h`, and the
  field off the `k`-th coordinate does not vanish at `x`, the local exponential estimate fails:
  under it the solution from `x + s³ e_k` stays `O(s³)`-close, so `q = O(s⁵)` and the solution
  lives for a time `≍ s³`, during which the drift carries it beyond the estimate.

The generic tools these constructions use are in the flat `Dynamics` modules: ball locality
(`Dynamics.localAsymptoticStable_of_eqOn_ball`, `theorem/Dynamics/Locality.lean`), the local strict
Lyapunov theorem (`Dynamics.localAsymptoticStable_of_lie_neg`, `theorem/Dynamics/Lyapunov.lean`),
mean-value and interval bounds (`theorem/Dynamics/Calculus.lean`) and the norm bounds for the
projection removing one coordinate (`Dynamics.norm_sub_smul_single_le`,
`Dynamics.norm_le_norm_sub_smul_single_add`, `theorem/Dynamics/Coordinates.lean`).

Source: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.1 (local Lyapunov theorem); the collapse
estimate is new (it answers the `V_dc* = 0` question of `theorem/GFL/DCLink/ModelBStability.lean`).

## Family and connection conclusions
None: this module defines no family. All results are generic semantic implications (foundation);
model-specific conclusions are drawn in the GFL model-B modules.
-/

noncomputable section
namespace powerlib.Dynamics.Degenerate
open Set Filter Topology

variable {n : ℕ}

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

/-- The spiral function is nonnegative. -/
@[powerlib_foundation] theorem spiralLyap_nonneg (ω hs K σ z Q : ℝ) : 0 ≤ spiralLyap ω hs K σ z Q :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

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

/-! ## Degenerate points of the plane: barriers, degenerate node, nilpotent drift -/

/-- **Instability from a trapping region with three barriers.** Let the field agree near `x` on
every half ball `{σ y_k ≥ s}` (`s > 0`) with a `C¹` field. Suppose that arbitrarily close to `x` there are seeds `y₀` with `σ y₀_k > 0` and a
region `{σ y_k ≥ σ y₀_k / 2, W₁, W₂, W₃ ≥ 0}` (three `C¹` barriers, positive at `y₀`) near `x`
in which `σ y_k` does not decrease, a `C¹` function `V`, bounded near `x`, grows at a rate
`μ > 0`, and the field crosses each barrier `W_i = 0` inwards. Then `x` is unstable. -/
@[powerlib_foundation] theorem unstable_of_barriers {f : State n → State n} {x : State n} (k : Fin n) {σ : ℝ}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hext : ∀ s > 0, ∃ g : State n → State n, ContDiff ℝ 1 g ∧
      ∀ y : State n, ‖y - x‖ < ρ → s ≤ σ * y k → g y = f y)
    (hseed : ∀ δ > 0, ∃ y₀ : State n, ‖y₀ - x‖ < δ ∧ 0 < σ * y₀ k ∧
      ∃ (W₁ W₂ W₃ V : State n → ℝ) (μ b : ℝ), 0 < μ ∧ ContDiff ℝ 1 W₁ ∧ ContDiff ℝ 1 W₂ ∧
        ContDiff ℝ 1 W₃ ∧ ContDiff ℝ 1 V ∧ 0 < W₁ y₀ ∧ 0 < W₂ y₀ ∧ 0 < W₃ y₀ ∧
        (∀ y : State n, ‖y - x‖ < ρ → V y ≤ b) ∧
        ∀ y : State n, ‖y - x‖ < ρ → σ * y₀ k / 2 ≤ σ * y k → 0 ≤ W₁ y → 0 ≤ W₂ y →
          0 ≤ W₃ y → 0 ≤ σ * f y k ∧ μ ≤ fderiv ℝ V y (f y) ∧
          (W₁ y = 0 → 0 < fderiv ℝ W₁ y (f y)) ∧ (W₂ y = 0 → 0 < fderiv ℝ W₂ y (f y)) ∧
          (W₃ y = 0 → 0 < fderiv ℝ W₃ y (f y))) :
    Unstable f x := by
  intro hLS
  obtain ⟨δ, hδ, hb⟩ := hLS (ρ / 2) (by positivity)
  obtain ⟨y₀, hy₀x, hs₀0, W₁, W₂, W₃, V, μ, b, hμ, hW₁, hW₂, hW₃, hV, h1₀, h2₀, h3₀, hVb,
    hreg⟩ := hseed (min δ (ρ / 2)) (lt_min hδ (by positivity))
  obtain ⟨s₀, hs₀⟩ : ∃ s, s = σ * y₀ k := ⟨_, rfl⟩
  rw [← hs₀] at hs₀0 hreg
  obtain ⟨g, hg, hgf⟩ := hext (s₀ / 2) (by positivity)
  obtain ⟨G, hG, ⟨K, hGlip⟩, hGg⟩ := exists_contDiff_lipschitz_extension hg (‖x‖ + ρ)
  obtain ⟨ψ, hψ0, hψ⟩ := Flow.forwardComplete_of_lipschitzWith hGlip 0 y₀
  have hGf : ∀ y : State n, ‖y - x‖ < ρ → s₀ / 2 ≤ σ * y k → G y = f y := by
    intro y hy hyk
    rw [hGg y (by
      have := norm_le_norm_add_norm_sub' y x
      linarith)]
    exact hgf y hy hyk
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : State n → ℝ, Φ = fun y => max (max (max (‖y - x‖ - ρ / 2)
      (s₀ / 2 - σ * y k)) (-W₁ y)) (max (-W₂ y) (-W₃ y)) := ⟨_, rfl⟩
  have hΦc : Continuous Φ := by
    rw [hΦ]
    exact ((((continuous_norm.comp (continuous_sub_right x)).sub continuous_const).max
      (continuous_const.sub (continuous_const.mul
        ((EuclideanSpace.proj k : State n →L[ℝ] ℝ).continuous)))).max hW₁.continuous.neg).max
      (hW₂.continuous.neg.max hW₃.continuous.neg)
  have hregion : ∀ y : State n, Φ y ≤ 0 → ‖y - x‖ < ρ ∧ s₀ / 2 ≤ σ * y k ∧ 0 ≤ W₁ y ∧
      0 ≤ W₂ y ∧ 0 ≤ W₃ y := by
    intro y hy
    simp only [hΦ, max_le_iff, sub_nonpos, neg_nonpos] at hy
    exact ⟨by linarith [hy.1.1.1], hy.1.1.2, hy.1.2, hy.2.1, hy.2.2⟩
  -- along a stretch in the region: a solution of `f`, `σ y_k ≥ s₀`, `V` grows at rate `μ`
  have hgrow : ∀ T, 0 ≤ T → (∀ u ∈ Icc 0 T, Φ (ψ u) ≤ 0) →
      IsTrajectoryOn ψ f 0 T ∧ (∀ u ∈ Icc 0 T, s₀ ≤ σ * ψ u k) ∧
        ∀ u ∈ Icc 0 T, V y₀ + μ * u ≤ V (ψ u) := by
    intro T hT hin
    have hseg : IsTrajectoryOn ψ f 0 T :=
      isIntegralCurveOn_of_eq_on_curve (hψ.mono Icc_subset_Ici_self)
        (fun u hu => hGf _ (hregion _ (hin u hu)).1 (hregion _ (hin u hu)).2.1)
    have hR : ∀ u ∈ Icc 0 T, _ := fun u hu => by
      obtain ⟨r1, r2, r3, r4, r5⟩ := hregion _ (hin u hu)
      exact hreg _ r1 r2 r3 r4 r5
    refine ⟨hseg, ?_, ?_⟩
    · intro u hu
      have hdk : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => σ * ψ t k) (σ * f (ψ t) k)
          (Icc 0 T) t :=
        fun t ht => ((EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
          t (hseg t ht)).const_mul σ
      have := sub_ge_of_deriv_ge (m := 0) hu.1 le_rfl hu.2 hdk
        (fun s hs => (hR s ⟨hs.1.le, hs.2.le.trans hu.2⟩).1)
      simp only [zero_mul, hψ0] at this
      linarith
    · intro u hu
      have hdV : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => V (ψ t)) (fderiv ℝ V (ψ t) (f (ψ t)))
          (Icc 0 T) t :=
        fun t ht => ((hV.differentiable one_ne_zero) (ψ t)).hasFDerivAt.comp_hasDerivWithinAt t
          (hseg t ht)
      have := sub_ge_of_deriv_ge (m := μ) hu.1 le_rfl hu.2 hdV
        (fun s hs => (hR s ⟨hs.1.le, hs.2.le.trans hu.2⟩).2.1)
      simp only [sub_zero, hψ0] at this
      linarith
  -- a barrier positive at the seed stays positive while the solution is in the region
  have hbar : ∀ W : State n → ℝ, ContDiff ℝ 1 W → 0 < W y₀ →
      (∀ y : State n, ‖y - x‖ < ρ → s₀ / 2 ≤ σ * y k → 0 ≤ W₁ y → 0 ≤ W₂ y → 0 ≤ W₃ y →
        W y = 0 → 0 < fderiv ℝ W y (f y)) →
      ∀ t, 0 ≤ t → (∀ u ∈ Icc 0 t, Φ (ψ u) ≤ 0) → (∀ u ∈ Icc 0 t, 0 ≤ W (ψ u)) →
        0 < W (ψ t) := by
    intro W hW hW0 hWb t ht hin hWin
    by_contra hW3
    push Not at hW3
    have hWt : W (ψ t) = 0 := le_antisymm hW3 (hWin t ⟨ht, le_rfl⟩)
    have htpos : 0 < t := by
      rcases eq_or_lt_of_le ht with h | h
      · rw [← h, hψ0] at hWt; linarith
      · exact h
    obtain ⟨hseg, -, -⟩ := hgrow t ht hin
    have hd : HasDerivWithinAt (fun u => W (ψ u)) (fderiv ℝ W (ψ t) (f (ψ t))) (Icc 0 t) t :=
      ((hW.differentiable one_ne_zero) (ψ t)).hasFDerivAt.comp_hasDerivWithinAt t
        (hseg t ⟨ht, le_rfl⟩)
    have hle := deriv_nonpos_of_isMinOn_right htpos hd (fun u hu => by
      rw [hWt]; exact hWin u hu)
    obtain ⟨r1, r2, r3, r4, r5⟩ := hregion _ (hin t ⟨ht, le_rfl⟩)
    linarith [hWb _ r1 r2 r3 r4 r5 hWt]
  have hstay : ∀ T, 0 ≤ T → ∀ u ∈ Icc 0 T, Φ (ψ u) < 0 := by
    intro T hT
    refine forall_lt_of_first_exit hΦc (hψ.continuousOn.mono Icc_subset_Ici_self) ?_ ?_
    · simp only [hΦ, hψ0, max_lt_iff]
      refine ⟨⟨⟨by linarith [hy₀x.trans_le (min_le_right _ _)], by linarith⟩, by linarith⟩,
        by linarith, by linarith⟩
    · intro t ht hin
      obtain ⟨hseg, hsk, -⟩ := hgrow t ht.1 hin
      have h1 : ‖ψ t - x‖ < ρ / 2 :=
        hb 0 t ψ hseg (by rw [hψ0]; exact hy₀x.trans_le (min_le_left _ _)) t ⟨ht.1, le_rfl⟩
      have h2 : s₀ ≤ σ * ψ t k := hsk t ⟨ht.1, le_rfl⟩
      have hWin : ∀ u ∈ Icc 0 t, 0 ≤ W₁ (ψ u) ∧ 0 ≤ W₂ (ψ u) ∧ 0 ≤ W₃ (ψ u) :=
        fun u hu => (hregion _ (hin u hu)).2.2
      have h3 := hbar W₁ hW₁ h1₀ (fun y r1 r2 r3 r4 r5 => (hreg y r1 r2 r3 r4 r5).2.2.1) t ht.1
        hin (fun u hu => (hWin u hu).1)
      have h4 := hbar W₂ hW₂ h2₀ (fun y r1 r2 r3 r4 r5 => (hreg y r1 r2 r3 r4 r5).2.2.2.1) t
        ht.1 hin (fun u hu => (hWin u hu).2.1)
      have h5 := hbar W₃ hW₃ h3₀ (fun y r1 r2 r3 r4 r5 => (hreg y r1 r2 r3 r4 r5).2.2.2.2) t
        ht.1 hin (fun u hu => (hWin u hu).2.2)
      simp only [hΦ, max_lt_iff]
      exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, by linarith, by linarith⟩
  -- but `V` is bounded near `x`
  have hVy₀ : V y₀ ≤ b := hVb y₀ (by linarith [hy₀x.trans_le (min_le_right _ _)])
  obtain ⟨T, hT⟩ : ∃ T, T = (b - V y₀) / μ + 1 := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; have := div_nonneg (sub_nonneg.mpr hVy₀) hμ.le; linarith
  obtain ⟨-, -, hVg⟩ := hgrow T hT0 (fun u hu => (hstay T hT0 u hu).le)
  have hfin := hregion _ (hstay T hT0 T ⟨hT0, le_rfl⟩).le
  have h1 := hVg T ⟨hT0, le_rfl⟩
  have h2 := hVb _ hfin.1
  have h3 : μ * T = b - V y₀ + μ := by rw [hT]; field_simp
  linarith


/-- A `C¹` real function is Lipschitz at a point on a ball. -/
@[powerlib_foundation] theorem exists_lipschitz_bound {g : State n → ℝ} (hg : ContDiff ℝ 1 g) (x : State n) :
    ∃ L ρ : ℝ, 0 ≤ L ∧ 0 < ρ ∧ ∀ y : State n, ‖y - x‖ < ρ → |g y - g x| ≤ L * ‖y - x‖ := by
  obtain ⟨K, t, ht, hK⟩ := hg.contDiffAt.exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨K, ρ, K.2, hρ, fun y hy => ?_⟩
  have := hK.dist_le_mul y (hball (by rwa [Metric.mem_ball, dist_eq_norm]))
    x (hball (Metric.mem_ball_self hρ))
  rwa [Real.dist_eq, dist_eq_norm] at this


set_option maxHeartbeats 1000000 in
/-- **Instability at a degenerate node of the plane.** Let `x` lie on the plane `y_k = 0` and
suppose that near `x`, off the plane, `y_k f_k = q` and `dq/dt = g + h q / y_k` with `C¹`
functions `q, g, h`, `q(x) = 0`, `∂_k q(x) = h(x)`, the remaining components of the field
continuous at `x`, and the field equal on every half ball `{σ y_k ≥ s}` to a `C¹` field. If the
quadratic `λ² − h(x) λ − g(x)` has a double root `h(x)/2 ≠ 0` (`h(x)² + 4 g(x) = 0`), then `x` is
unstable: on the side `σ = sign h(x)`, with `w = σ y_k` and `λ = |h(x)|/2`, the horn
`{q ≥ (λ − √w) w, ‖y − x‖² ≤ (K² + 1) y_k²}` is entered by the field (the margin `√w` of the
shrinking cone dominates the Lipschitz variation `O(w)` of `g, h`), and in it `w' ≥ λ / 2`. -/
@[powerlib_foundation] theorem unstable_of_degenerate_node {f : State n → State n} {x : State n} (k : Fin n)
    (hxk : x k = 0) {q g h : State n → ℝ} (hq : ContDiff ℝ 1 q) (hq0 : q x = 0)
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h) {ρ : ℝ} (hρ : 0 < ρ)
    (hrel : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → y k * f y k = q y)
    (hlie : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 →
      fderiv ℝ q y (f y) = g y + h y * (q y / y k))
    (hqk : fderiv ℝ q x (EuclideanSpace.single k 1) = h x)
    (hD : h x ^ 2 + 4 * g x = 0) (hh0 : h x ≠ 0)
    (hF : ContinuousAt (fun y => f y - f y k • EuclideanSpace.single k (1 : ℝ)) x)
    (hext : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ s > 0, ∃ G : State n → State n, ContDiff ℝ 1 G ∧
      ∀ y : State n, ‖y - x‖ < ρ → s ≤ σ * y k → G y = f y) :
    Unstable f x := by
  obtain ⟨σ, hσ, hσh⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * h x = |h x| := by
    by_cases h0 : 0 ≤ h x
    · exact ⟨1, Or.inl rfl, by rw [one_mul, abs_of_nonneg h0]⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg (not_le.mp h0)]; ring⟩
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσa : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  obtain ⟨l, hl⟩ : ∃ l, l = |h x| / 2 := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hl]; have := abs_pos.mpr hh0; linarith
  have hσh' : σ * h x = 2 * l := by rw [hσh, hl]; ring
  have hgx : g x = -l ^ 2 := by
    have h1 : h x ^ 2 = |h x| ^ 2 := (sq_abs _).symm
    have h2 : |h x| = 2 * l := by rw [hl]; ring
    rw [h2] at h1
    linarith
  obtain ⟨Lg, ρg, hLg, hρg, hgL⟩ := exists_lipschitz_bound hg x
  obtain ⟨Lh, ρh, hLh, hρh, hhL⟩ := exists_lipschitz_bound hh x
  obtain ⟨ρF, hρF, hFb⟩ := Metric.continuousAt_iff.mp hF 1 one_pos
  set e : State n := EuclideanSpace.single k (1 : ℝ) with he
  obtain ⟨M, hM⟩ : ∃ M, M = ‖f x - f x k • e‖ + 1 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hFM : ∀ y : State n, ‖y - x‖ < ρF → ‖f y - f y k • e‖ ≤ M := by
    intro y hy
    have h1 := hFb (by rwa [dist_eq_norm])
    rw [dist_eq_norm] at h1
    have h2 := norm_le_norm_add_norm_sub' (f y - f y k • e) (f x - f x k • e)
    rw [hM]
    have h3 : ‖f x - f x k • e - (f y - f y k • e)‖ = ‖f y - f y k • e - (f x - f x k • e)‖ :=
      norm_sub_rev _ _
    linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Lg + Lh := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = 4 * (M + 1) / l + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 4 * (M + 1) / l := by positivity
    rw [hK]; linarith
  have hKl : K * l = 4 * (M + 1) + l := by rw [hK]; field_simp
  obtain ⟨S, hS⟩ : ∃ S, S = 3 / 2 + L * (1 + l) * (1 + K) := ⟨_, rfl⟩
  have hS1 : 3 / 2 ≤ S := by
    have : 0 ≤ L * (1 + l) * (1 + K) := by positivity
    rw [hS]; linarith
  obtain ⟨c, hc⟩ : ∃ c, c = l / 2 / S := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    have : 0 < S := by linarith
    rw [hc]; positivity
  have hcS : c * S = l / 2 := by rw [hc]; field_simp
  have hcl : c ≤ l / 2 := by
    have : c * (3 / 2) ≤ c * S := mul_le_mul_of_nonneg_left hS1 hc0.le
    linarith
  obtain ⟨r, hr⟩ : ∃ r, r = min (min ρ ρg) (min ρh (min ρF (c ^ 2))) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrρ : r ≤ ρ := by rw [hr]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hrg : r ≤ ρg := by rw [hr]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrh : r ≤ ρh := by rw [hr]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hrF : r ≤ ρF := by
    rw [hr]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrc : r ≤ c ^ 2 := by
    rw [hr]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hqd : Differentiable ℝ q := hq.differentiable one_ne_zero
  -- the coordinate `σ y_k` and its derivative
  have hk : ∀ y : State n, HasFDerivAt (fun y : State n => σ * y k)
      (σ • (EuclideanSpace.proj k : State n →L[ℝ] ℝ)) y :=
    fun y => (EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.const_mul σ
  have hkc : ContDiff ℝ 1 (fun y : State n => σ * y k) :=
    contDiff_const.mul (EuclideanSpace.proj k : State n →L[ℝ] ℝ).contDiff
  -- the barriers
  obtain ⟨W₁, hW₁⟩ : ∃ W : State n → ℝ,
      W = fun y => q y - l * (σ * y k) + (σ * y k) ^ (3 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W : State n → ℝ,
      W = fun y => (K ^ 2 + 1) * (y k) ^ 2 - ‖y - x‖ ^ 2 := ⟨_, rfl⟩
  have hW₁c : ContDiff ℝ 1 W₁ := by
    rw [hW₁]
    exact (hq.sub (contDiff_const.mul hkc)).add
      ((Real.contDiff_rpow_const_of_le (by norm_num)).comp hkc)
  have hW₂c : ContDiff ℝ 1 W₂ := by
    rw [hW₂]
    exact (contDiff_const.mul
      ((EuclideanSpace.proj k : State n →L[ℝ] ℝ).contDiff.pow 2)).sub
      ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  refine unstable_of_barriers k (σ := σ) hr0 ?_ ?_
  · intro s hs
    obtain ⟨G, hG, hGf⟩ := hext σ hσ s hs
    exact ⟨G, hG, fun y hy hys => hGf y (lt_of_lt_of_le hy hrρ) hys⟩
  intro δ hδ
  -- a seed on the line `x + t σ e_k`
  have hline : HasDerivAt (fun t : ℝ => q (x + (t * σ) • e) - l * t) (σ * h x - l) 0 := by
    have hl' : HasDerivAt (fun t : ℝ => x + (t * σ) • e) (σ • e) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const σ).smul_const e).const_add x
      simpa using this
    have h1 := (hqd (x + ((0 : ℝ) * σ) • e)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl'
    simp only [zero_mul, zero_smul, add_zero] at h1
    have h2 := h1.sub ((hasDerivAt_id (0 : ℝ)).const_mul l)
    refine HasDerivAt.congr_deriv (f := fun t : ℝ => q (x + (t * σ) • e) - l * t) h2 ?_
    rw [map_smul, hqk, smul_eq_mul, mul_one]
  have hev := eventually_pos_of_hasDerivAt hline (by simp [hq0]) (by rw [hσh']; linarith)
  obtain ⟨t, ht, htδ⟩ := (hev.and (Ioo_mem_nhdsGT hδ)).exists
  have ht0 : 0 < t := htδ.1
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : State n, y₀ = x + (t * σ) • e := ⟨_, rfl⟩
  have hy₀x : ‖y₀ - x‖ = t := by
    rw [hy₀, add_sub_cancel_left, norm_smul, he, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_mul, hσa, mul_one, abs_of_pos ht0]
  have hy₀k : y₀ k = t * σ := by
    rw [hy₀, he]; simp [hxk]
  have hσy₀ : σ * y₀ k = t := by rw [hy₀k]; linear_combination t * hσ2
  refine ⟨y₀, by rw [hy₀x]; exact htδ.2, by rw [hσy₀]; exact ht0, W₁, W₂, fun _ => 1,
    fun y => σ * y k, l / 2, r, by positivity, hW₁c, hW₂c, contDiff_const, hkc, ?_, ?_,
    one_pos, ?_, ?_⟩
  · rw [hW₁]
    simp only
    rw [hσy₀]
    have h1 : 0 ≤ t ^ (3 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
    have h2 : 0 < q y₀ - l * t := by rw [hy₀]; exact ht
    linarith
  · rw [hW₂]
    simp only
    rw [hy₀x, hy₀k]
    have : 0 < K ^ 2 * t ^ 2 := by positivity
    linear_combination this - (K ^ 2 + 1) * t ^ 2 * hσ2
  · intro y hy
    have h1 : |y k| ≤ ‖y - x‖ := by
      have := PiLp.norm_apply_le (y - x) k
      simpa [hxk] using this
    have h2 : σ * y k ≤ |y k| := by
      calc σ * y k ≤ |σ * y k| := le_abs_self _
        _ = |y k| := by rw [abs_mul, hσa, one_mul]
    linarith
  intro y hy hyk h1 h2 _
  have hyρ : ‖y - x‖ < ρ := lt_of_lt_of_le hy hrρ
  obtain ⟨w, hw⟩ : ∃ w, w = σ * y k := ⟨_, rfl⟩
  rw [hσy₀, ← hw] at hyk
  have hw0 : 0 < w := by linarith
  have hyk' : y k = σ * w := by rw [hw]; linear_combination (-(y k)) * hσ2
  have hyk0 : y k ≠ 0 := by
    rw [hyk']; exact mul_ne_zero (by rcases hσ with h | h <;> rw [h] <;> norm_num) hw0.ne'
  have hwN : w ≤ ‖y - x‖ := by
    have h3 := PiLp.norm_apply_le (y - x) k
    simp only [PiLp.sub_apply, hxk, sub_zero, Real.norm_eq_abs] at h3
    have h4 : |y k| = w := by rw [hyk', abs_mul, hσa, one_mul, abs_of_pos hw0]
    linarith
  obtain ⟨s, hs⟩ : ∃ s, s = w ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.rpow_pos_of_pos hw0 _
  have hss : s * s = w := by
    rw [hs, ← Real.rpow_add hw0]; norm_num
  have h32 : w ^ (3 / 2 : ℝ) = w * s := by
    rw [hs, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hw0, Real.rpow_one]
  have hsc : s < c := by nlinarith
  have hN : ‖y - x‖ ≤ (K + 1) * w := by
    rw [hW₂] at h2
    simp only at h2
    rw [hyk'] at h2
    by_contra hcon
    push Not at hcon
    have h3 : ((K + 1) * w) ^ 2 < ‖y - x‖ ^ 2 :=
      pow_lt_pow_left₀ hcon (by positivity) two_ne_zero
    nlinarith
  have hq1 : l * w - w * s ≤ q y := by
    rw [hW₁] at h1
    simp only at h1
    rw [← hw, h32] at h1
    linarith
  have ha : w * (σ * f y k) = q y := by
    rw [← hrel y hyρ hyk0, hyk']; ring
  have hal : l / 2 ≤ σ * f y k := by
    by_contra hcon
    push Not at hcon
    have : w * (σ * f y k) < w * (l / 2) := mul_lt_mul_of_pos_left hcon hw0
    nlinarith
  refine ⟨by linarith, ?_, ?_, ?_, fun h0 => absurd h0 one_ne_zero⟩
  · rw [(hk y).fderiv]
    simpa using hal
  · intro hW0
    have hW₁d : HasFDerivAt W₁ (fderiv ℝ q y - l • σ • (EuclideanSpace.proj k : State n →L[ℝ] ℝ)
        + ((3 / 2) * (σ * y k) ^ ((3 / 2 : ℝ) - 1)) •
          σ • (EuclideanSpace.proj k : State n →L[ℝ] ℝ)) y := by
      rw [hW₁]
      exact ((hqd y).hasFDerivAt.sub ((hk y).const_mul l)).add
        ((Real.hasDerivAt_rpow_const (Or.inr (by norm_num))).comp_hasFDerivAt y (hk y))
    rw [hW₁d.fderiv]
    simp only [_root_.add_apply, _root_.sub_apply, _root_.smul_apply, smul_eq_mul,
      PiLp.proj_apply]
    rw [hlie y hyρ hyk0, ← hw, show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← hs]
    have hqW : q y = l * w - w * s := by
      rw [hW₁] at hW0
      simp only at hW0
      rw [← hw, h32] at hW0
      linarith
    obtain ⟨a, ha'⟩ : ∃ a, a = σ * f y k := ⟨_, rfl⟩
    rw [← ha'] at ha hal ⊢
    have haval : a = l - s := by
      have h3 : w * a = w * (l - s) := by rw [ha, hqW]; ring
      exact mul_left_cancel₀ hw0.ne' h3
    have hqf : q y / y k = σ * a := by
      rw [← hrel y hyρ hyk0, ha']
      field_simp
      linear_combination (-(f y k)) * hσ2
    rw [hqf]
    obtain ⟨N, hNdef⟩ : ∃ N, N = ‖y - x‖ := ⟨_, rfl⟩
    rw [← hNdef] at hN
    have hgy : -l ^ 2 - Lg * N ≤ g y := by
      have h3 := (abs_le.mp (hgL y (lt_of_lt_of_le hy hrg))).1
      rw [hgx, ← hNdef] at h3
      linarith
    have hhy : 2 * l - Lh * N ≤ σ * h y := by
      have h3 := hhL y (lt_of_lt_of_le hy hrh)
      rw [← hNdef] at h3
      have h4 : |σ * (h y - h x)| = |h y - h x| := by rw [abs_mul, hσa, one_mul]
      have h5 := neg_abs_le (σ * (h y - h x))
      rw [h4] at h5
      have h6 : σ * h y = σ * h x + σ * (h y - h x) := by ring
      rw [h6, hσh']
      linarith
    have ha0 : 0 ≤ a := by linarith
    have hE1 : (2 * l - Lh * N) * a ≤ (σ * h y) * a := mul_le_mul_of_nonneg_right hhy ha0
    have hrw : h y * (σ * a) = (σ * h y) * a := by ring
    have hN' : N ≤ (K + 1) * (s * s) := by rw [hss]; exact hN
    have hLg' : Lg * N ≤ Lg * ((K + 1) * (s * s)) := mul_le_mul_of_nonneg_left hN' hLg
    have hLh' : Lh * N * a ≤ Lh * ((K + 1) * (s * s)) * l := by
      have h6 : a ≤ l := by rw [haval]; linarith
      have h7 : 0 ≤ Lh * N := mul_nonneg hLh (by rw [hNdef]; exact norm_nonneg _)
      calc Lh * N * a ≤ Lh * N * l := mul_le_mul_of_nonneg_left h6 h7
        _ ≤ Lh * ((K + 1) * (s * s)) * l :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN' hLh) hl0.le
    have hsum : Lg * ((K + 1) * (s * s)) + Lh * ((K + 1) * (s * s)) * l ≤
        (S - 3 / 2) * (s * s) := by
      have h3 : (S - 3 / 2) * (s * s) - (Lg * ((K + 1) * (s * s)) +
          Lh * ((K + 1) * (s * s)) * l) = (K + 1) * (s * s) * (Lg * l + Lh) := by
        rw [hS, hL]; ring
      have h4 : 0 ≤ (K + 1) * (s * s) * (Lg * l + Lh) := by positivity
      linarith
    have hfin : 0 < s * (l / 2) - S * (s * s) := by
      have h3 : S * s < S * c := mul_lt_mul_of_pos_left hsc (by linarith)
      have h4 : 0 < l / 2 - S * s := by linarith [hcS]
      have h5 := mul_pos hs0 h4
      linarith [h5]
    have hexp : (2 * l - Lh * N) * a - l * a + 3 / 2 * s * a =
        s * (l / 2) - 3 / 2 * (s * s) + l ^ 2 - Lh * N * a := by
      rw [haval]; ring
    rw [hrw]
    linarith
  · intro hW0
    have hW₂d : HasFDerivAt W₂ ((K ^ 2 + 1) • ((2 • (y k) ^ (2 - 1)) •
        (EuclideanSpace.proj k : State n →L[ℝ] ℝ)) -
        2 • (innerSL ℝ (y - x)).comp (ContinuousLinearMap.id ℝ (State n))) y := by
      rw [hW₂]
      exact (((EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.pow 2).const_mul
        (K ^ 2 + 1)).sub ((hasFDerivAt_id y).sub_const x).norm_sq
    rw [hW₂d.fderiv]
    simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul, PiLp.proj_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply]
    have hsimp : (K ^ 2 + 1) * (2 • y k ^ (2 - 1) * f y k) - 2 • inner ℝ (y - x) (f y) =
        2 * (K ^ 2 + 1) * (y k * f y k) - 2 * inner ℝ (y - x) (f y) := by
      simp only [nsmul_eq_mul, Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
      ring
    have hinner : inner ℝ (y - x) (f y) = inner ℝ (y - x) (f y - f y k • e) + f y k * y k := by
      have h3 : f y = (f y - f y k • e) + f y k • e := by abel
      conv_lhs => rw [h3]
      rw [inner_add_right, inner_smul_right, he, EuclideanSpace.inner_single_right]
      simp [hxk]
    have hFin : inner ℝ (y - x) (f y - f y k • e) ≤ ‖y - x‖ * M :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hFM y (lt_of_lt_of_le hy hrF)) (norm_nonneg _))
    rw [hsimp, hinner, hrel y hyρ hyk0]
    have hqwl : w * (l / 2) ≤ q y := by
      rw [← ha]; exact mul_le_mul_of_nonneg_left hal hw0.le
    have hK2 : K ^ 2 * (w * (l / 2)) ≤ K ^ 2 * q y := mul_le_mul_of_nonneg_left hqwl (sq_nonneg K)
    have hNM : ‖y - x‖ * M ≤ (K + 1) * w * M := mul_le_mul_of_nonneg_right hN hM0
    have hKK : 0 < K ^ 2 * l - 2 * (K + 1) * M := by
      have e1 : K ^ 2 * l - 2 * (K + 1) * M = 2 * M * (K - 1) + K * (4 + l) := by
        have e0 : K ^ 2 * l = K * (K * l) := by ring
        rw [e0, hKl]; ring
      rw [e1]
      have h4 := mul_nonneg (by linarith : 0 ≤ 2 * M) (by linarith : 0 ≤ K - 1)
      have h5 := mul_pos (by linarith : 0 < K) (by linarith : 0 < 4 + l)
      linarith
    have hfk : f y k * y k = q y := by rw [← hrel y hyρ hyk0]; ring
    rw [hfk]
    rw [show 2 * (K ^ 2 + 1) * q y - 2 * (inner ℝ (y - x) (f y - f y k • e) + q y) =
      2 * (K ^ 2 * q y) - 2 * inner ℝ (y - x) (f y - f y k • e) by ring]
    have h3' : 0 < 2 * (K ^ 2 * (w * (l / 2))) - 2 * ((K + 1) * w * M) := by
      have h := mul_pos hw0 hKK
      have e : 2 * (K ^ 2 * (w * (l / 2))) - 2 * ((K + 1) * w * M) =
          w * (K ^ 2 * l - 2 * (K + 1) * M) := by ring
      rw [e]; exact h
    linarith [hFin, hNM, hK2, h3']


/-- **No exponential estimate at a nilpotent point of the plane with drift.** Let `x` lie on the
plane `y_k = 0`, and suppose that near `x`, off the plane, `y_k f_k = q` and
`dq/dt = g + h q / y_k`, with `C¹` functions `q, g, h` vanishing at `x`, `∂_k q = h`, the remaining
components `F = f − f_k e_k` of the field continuous at `x` with `F(x) ≠ 0`, and the field equal
on every half ball `{y_k ≥ s}` to a `C¹` field. Then the local exponential estimate fails. Under
the estimate with overshoot `C`, the solution from `x + s³ e_k` stays within `C s³` of `x`; there
`g, h = O(s³)`, so `q` stays `O(s⁵)` and `y_k ≥ s³/2` for a time `4 C s³ / ‖F(x)‖`, during which
the drift `F ≈ F(x)` carries the solution to distance `2 C s³`. -/
@[powerlib_foundation] theorem not_locallyExponentiallyStable_of_nilpotent {f : State n → State n} {x : State n}
    (k : Fin n) (hxk : x k = 0) {q g h : State n → ℝ} (hq : ContDiff ℝ 1 q) (hq0 : q x = 0)
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h) (hg0 : g x = 0) (hh0 : h x = 0)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hrel : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → y k * f y k = q y)
    (hlie : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 →
      fderiv ℝ q y (f y) = g y + h y * (q y / y k))
    (hqk : ∀ y : State n, fderiv ℝ q y (EuclideanSpace.single k 1) = h y)
    (hF : ContinuousAt (fun y => f y - f y k • EuclideanSpace.single k (1 : ℝ)) x)
    (hF0 : f x - f x k • EuclideanSpace.single k (1 : ℝ) ≠ 0)
    (hext : ∀ s > 0, ∃ G : State n → State n, ContDiff ℝ 1 G ∧
      ∀ y : State n, ‖y - x‖ < ρ → s ≤ y k → G y = f y) :
    ¬ LocallyExponentiallyStable f x := by
  rintro ⟨r, C, a, hr, hC, ha, hles⟩
  set e : State n := EuclideanSpace.single k (1 : ℝ) with he
  obtain ⟨Lg, ρg, hLg, hρg, hgL⟩ := exists_lipschitz_bound hg x
  obtain ⟨Lh, ρh, hLh, hρh, hhL⟩ := exists_lipschitz_bound hh x
  obtain ⟨Fx, hFx⟩ : ∃ v : State n, v = f x - f x k • e := ⟨_, rfl⟩
  obtain ⟨F0, hF0d⟩ : ∃ F0, F0 = ‖Fx‖ := ⟨_, rfl⟩
  have hF0p : 0 < F0 := by rw [hF0d, hFx]; exact norm_pos_iff.mpr hF0
  obtain ⟨ρF, hρF, hFb⟩ := Metric.continuousAt_iff.mp hF (F0 / 2) (by positivity)
  obtain ⟨L, hL⟩ : ∃ L, L = Lg + Lh := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  obtain ⟨ρ', hρ'⟩ : ∃ ρ', ρ' = min (min ρ ρg) (min ρh ρF) := ⟨_, rfl⟩
  have hρ'0 : 0 < ρ' := by rw [hρ']; positivity
  have hρ'ρ : ρ' ≤ ρ := by rw [hρ']; exact (min_le_left _ _).trans (min_le_left _ _)
  have hρ'g : ρ' ≤ ρg := by rw [hρ']; exact (min_le_left _ _).trans (min_le_right _ _)
  have hρ'h : ρ' ≤ ρh := by rw [hρ']; exact (min_le_right _ _).trans (min_le_left _ _)
  have hρ'F : ρ' ≤ ρF := by rw [hρ']; exact (min_le_right _ _).trans (min_le_right _ _)
  have hC0 : 0 < C := by linarith
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = L + 12 * L * C ^ 2 / F0 := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  -- the small parameter
  obtain ⟨m, hm⟩ : ∃ m, m = min (min (min 1 r) (ρ' / (2 * C))) (min (1 / (Λ + 1)) (F0 / (16 * C))) :=
    ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  obtain ⟨s, hs⟩ : ∃ s, s = m / 2 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsm : s < m := by rw [hs]; linarith
  have hs1 : s < 1 := by
    refine lt_of_lt_of_le hsm ?_
    rw [hm]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hsr : s < r := by
    refine lt_of_lt_of_le hsm ?_
    rw [hm]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsρ : s < ρ' / (2 * C) := by
    refine lt_of_lt_of_le hsm ?_
    rw [hm]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hsΛ : s < 1 / (Λ + 1) := by
    refine lt_of_lt_of_le hsm ?_
    rw [hm]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hsF : s < F0 / (16 * C) := by
    refine lt_of_lt_of_le hsm ?_
    rw [hm]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hqd : Differentiable ℝ q := hq.differentiable one_ne_zero
  have hLgL : Lg ≤ L := by rw [hL]; linarith
  have hLhL : Lh ≤ L := by rw [hL]; linarith
  -- derived smallness
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs0.le hs1.le
  have hs2s : s ^ 2 ≤ s := pow_le_of_le_one hs0.le hs1.le two_ne_zero
  have hs3p : 0 < s ^ 3 := by positivity
  have hs3s : s ^ 3 ≤ s := pow_le_of_le_one hs0.le hs1.le (by norm_num)
  have hs3r : s ^ 3 < r := lt_of_le_of_lt hs3s hsr
  have hCs : C * s < ρ' / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hsρ
    linarith only [hsρ]
  have hCs3 : C * s ^ 3 < ρ' / 2 := by
    have := mul_le_mul_of_nonneg_left hs3s hC0.le
    linarith only [this, hCs]
  have hs3C : s ^ 3 ≤ C * s ^ 3 := le_mul_of_one_le_left hs3p.le hC
  have hsΛ' : s * Λ < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hsΛ
    linarith only [hsΛ, hs0]
  have hsF' : 16 * C * s ^ 2 < F0 := by
    rw [lt_div_iff₀ (by positivity)] at hsF
    have := mul_le_mul_of_nonneg_left hs2s (by positivity : (0 : ℝ) ≤ 16 * C)
    linarith only [hsF, this]
  -- the seed
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : State n, y₀ = x + s ^ 3 • e := ⟨_, rfl⟩
  have hy₀x : ‖y₀ - x‖ = s ^ 3 := by
    rw [hy₀, add_sub_cancel_left, norm_smul, he, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_of_pos hs3p]
  have hy₀k : y₀ k = s ^ 3 := by rw [hy₀, he]; simp [hxk]
  have hqy₀ : |q y₀| ≤ Lh * s ^ 6 := by
    have hd : ∀ u ∈ Icc 0 (s ^ 3), HasDerivWithinAt (fun u : ℝ => q (x + u • e))
        (h (x + u • e)) (Icc 0 (s ^ 3)) u := by
      intro u _
      have hl : HasDerivAt (fun u : ℝ => x + u • e) e u := by
        simpa using ((hasDerivAt_id u).smul_const e).const_add x
      have h1 := (hqd (x + u • e)).hasFDerivAt.comp_hasDerivAt u hl
      rw [he, hqk] at h1
      exact h1.hasDerivWithinAt
    have hbd : ∀ u ∈ Ioo 0 (s ^ 3), |h (x + u • e)| ≤ Lh * s ^ 3 := by
      intro u hu
      have hn : ‖x + u • e - x‖ = u := by
        rw [add_sub_cancel_left, norm_smul, he, PiLp.norm_single, norm_one, mul_one,
          Real.norm_eq_abs, abs_of_pos hu.1]
      have h1 := hhL (x + u • e) (by rw [hn]; linarith [hu.2])
      rw [hh0, sub_zero, hn] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hu.2.le hLh)
    have h1 := sub_le_of_deriv_le (m := Lh * s ^ 3) hs3p.le le_rfl le_rfl hd
      (fun u hu => (abs_le.mp (hbd u hu)).2)
    have h2 := sub_ge_of_deriv_ge (m := -(Lh * s ^ 3)) hs3p.le le_rfl le_rfl hd
      (fun u hu => (abs_le.mp (hbd u hu)).1)
    simp only [zero_smul, add_zero, hq0, sub_zero] at h1 h2
    rw [← hy₀] at h1 h2
    rw [abs_le]
    constructor
    · linarith only [h2]
    · linarith only [h1]
  -- the solution from the seed, through a globally Lipschitz `C¹` field
  obtain ⟨G, hG, hGf⟩ := hext (s ^ 3 / 2) (by positivity)
  obtain ⟨Gt, hGt, ⟨K, hGlip⟩, hGg⟩ := exists_contDiff_lipschitz_extension hG (‖x‖ + ρ)
  obtain ⟨ψ, hψ0, hψ⟩ := Flow.forwardComplete_of_lipschitzWith hGlip 0 y₀
  have hGtf : ∀ y : State n, ‖y - x‖ < ρ → s ^ 3 / 2 ≤ y k → Gt y = f y := by
    intro y hy hyk
    rw [hGg y (by
      have := norm_le_norm_add_norm_sub' y x
      linarith)]
    exact hGf y hy hyk
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : State n → ℝ, Φ = fun y =>
      max (max (‖y - x‖ - ρ' / 2) (s ^ 3 / 2 - y k)) (|q y| - s ^ 5) := ⟨_, rfl⟩
  have hΦc : Continuous Φ := by
    rw [hΦ]
    exact (((continuous_norm.comp (continuous_sub_right x)).sub continuous_const).max
      (continuous_const.sub (EuclideanSpace.proj k : State n →L[ℝ] ℝ).continuous)).max
      ((continuous_abs.comp hq.continuous).sub continuous_const)
  have hregion : ∀ y : State n, Φ y ≤ 0 →
      ‖y - x‖ ≤ ρ' / 2 ∧ s ^ 3 / 2 ≤ y k ∧ |q y| ≤ s ^ 5 := by
    intro y hy
    simp only [hΦ, max_le_iff, sub_nonpos] at hy
    exact ⟨hy.1.1, hy.1.2, hy.2⟩
  have hseg : ∀ t, 0 ≤ t → (∀ u ∈ Icc 0 t, Φ (ψ u) ≤ 0) → IsTrajectoryOn ψ f 0 t := by
    intro t _ hin
    exact isIntegralCurveOn_of_eq_on_curve (hψ.mono Icc_subset_Ici_self)
      (fun u hu => hGtf _ (by linarith [(hregion _ (hin u hu)).1]) (hregion _ (hin u hu)).2.1)
  have hnear : ∀ t, IsTrajectoryOn ψ f 0 t → ∀ u ∈ Icc 0 t, ‖ψ u - x‖ ≤ C * s ^ 3 := by
    intro t hst u hu
    have h1 := hles 0 t ψ hst (by rw [hψ0, hy₀x]; exact hs3r) u hu
    rw [hψ0, hy₀x] at h1
    have h2 : Real.exp (-a * (u - 0)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := mul_nonneg ha.le hu.1
      linarith only [this])
    have h3 : C * Real.exp (-a * (u - 0)) * s ^ 3 ≤ C * 1 * s ^ 3 := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC0.le) hs3p.le
    linarith only [h1, h3]
  -- the slope `f_k = q / y_k` is `O(s²)` in the region
  have hslope : ∀ y : State n, ‖y - x‖ ≤ ρ' / 2 → s ^ 3 / 2 ≤ y k → |q y| ≤ s ^ 5 →
      |f y k| ≤ 2 * s ^ 2 ∧ |q y / y k| ≤ 2 * s ^ 2 := by
    intro y hy hyk hqy
    have hyk0 : 0 < y k := lt_of_lt_of_le (by positivity) hyk
    have hfk : f y k = q y / y k := by
      rw [← hrel y (by linarith) hyk0.ne']; field_simp
    have h1 : |q y / y k| ≤ 2 * s ^ 2 := by
      rw [abs_div, abs_of_pos hyk0, div_le_iff₀ hyk0]
      have : 2 * s ^ 2 * (s ^ 3 / 2) ≤ 2 * s ^ 2 * y k :=
        mul_le_mul_of_nonneg_left hyk (by positivity)
      linarith only [this, hqy]
    exact ⟨by rw [hfk]; exact h1, h1⟩
  obtain ⟨T, hT⟩ : ∃ T, T = 4 * C * s ^ 3 / F0 := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hstay : ∀ u ∈ Icc 0 T, Φ (ψ u) < 0 := by
    refine forall_lt_of_first_exit hΦc (hψ.continuousOn.mono Icc_subset_Ici_self) ?_ ?_
    · rw [hψ0]
      simp only [hΦ, max_lt_iff]
      refine ⟨⟨by rw [hy₀x]; linarith only [hs3C, hCs3], by rw [hy₀k]; linarith only [hs3p]⟩, ?_⟩
      have h1 : Lh * s ^ 6 ≤ Λ * s ^ 6 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hΛ]
        have : 0 ≤ 12 * L * C ^ 2 / F0 := by positivity
        linarith only [this, hLhL]
      have h2 : Λ * s ^ 6 < s ^ 5 := by
        have : s ^ 5 * (s * Λ) < s ^ 5 * 1 := mul_lt_mul_of_pos_left hsΛ' (by positivity)
        have e : Λ * s ^ 6 = s ^ 5 * (s * Λ) := by ring
        linarith only [this, e]
      have := abs_le.mp hqy₀
      have h3 : |q y₀| < s ^ 5 := lt_of_le_of_lt hqy₀ (lt_of_le_of_lt h1 h2)
      linarith only [h3]
    intro t ht hin
    have hst := hseg t ht.1 hin
    have hN := hnear t hst
    have hreg : ∀ u ∈ Icc 0 t, ‖ψ u - x‖ ≤ ρ' / 2 ∧ s ^ 3 / 2 ≤ ψ u k ∧ |q (ψ u)| ≤ s ^ 5 :=
      fun u hu => hregion _ (hin u hu)
    -- `q` along the solution
    have hdq : ∀ u ∈ Icc 0 t, HasDerivWithinAt (fun u => q (ψ u))
        (fderiv ℝ q (ψ u) (f (ψ u))) (Icc 0 t) u :=
      fun u hu => (hqd (ψ u)).hasFDerivAt.comp_hasDerivWithinAt u (hst u hu)
    obtain ⟨mq, hmq⟩ : ∃ mq, mq = L * C * s ^ 3 + 2 * L * C * s ^ 5 := ⟨_, rfl⟩
    have hdqb : ∀ u ∈ Ioo 0 t, |fderiv ℝ q (ψ u) (f (ψ u))| ≤ mq := by
      intro u hu
      obtain ⟨r1, r2, r3⟩ := hreg u ⟨hu.1.le, hu.2.le⟩
      have hNu := hN u ⟨hu.1.le, hu.2.le⟩
      have hyk0 : ψ u k ≠ 0 := (lt_of_lt_of_le (by positivity) r2).ne'
      rw [hlie _ (by linarith) hyk0]
      have hg1 := hgL (ψ u) (by linarith)
      have hh1 := hhL (ψ u) (by linarith)
      rw [hg0, sub_zero] at hg1
      rw [hh0, sub_zero] at hh1
      have hsl := (hslope _ r1 r2 r3).2
      have hgb : |g (ψ u)| ≤ L * C * s ^ 3 := by
        calc |g (ψ u)| ≤ Lg * ‖ψ u - x‖ := hg1
          _ ≤ L * (C * s ^ 3) := mul_le_mul hLgL hNu (norm_nonneg _) hL0
          _ = L * C * s ^ 3 := by ring
      have hhb : |h (ψ u) * (q (ψ u) / ψ u k)| ≤ 2 * L * C * s ^ 5 := by
        rw [abs_mul]
        have hh2 : |h (ψ u)| ≤ L * (C * s ^ 3) :=
          hh1.trans (mul_le_mul hLhL hNu (norm_nonneg _) hL0)
        calc |h (ψ u)| * |q (ψ u) / ψ u k| ≤ L * (C * s ^ 3) * (2 * s ^ 2) :=
              mul_le_mul hh2 hsl (abs_nonneg _) (by positivity)
          _ = 2 * L * C * s ^ 5 := by ring
      rw [hmq]
      exact (abs_add_le _ _).trans (add_le_add hgb hhb)
    have hq1 := sub_le_of_deriv_le (m := mq) ht.1 le_rfl le_rfl hdq
      (fun u hu => (abs_le.mp (hdqb u hu)).2)
    have hq2 := sub_ge_of_deriv_ge (m := -mq) ht.1 le_rfl le_rfl hdq
      (fun u hu => (abs_le.mp (hdqb u hu)).1)
    rw [hψ0] at hq1 hq2
    have hmq0 : 0 ≤ mq := by rw [hmq]; positivity
    have hmqT : mq * t ≤ mq * T := mul_le_mul_of_nonneg_left ht.2 hmq0
    have hmqT' : mq * T + Lh * s ^ 6 < s ^ 5 := by
      have e1 : mq * T = 4 * L * C ^ 2 / F0 * s ^ 6 + 8 * L * C ^ 2 / F0 * s ^ 8 := by
        rw [hmq, hT]; field_simp; ring
      have e2 : s ^ 8 ≤ s ^ 6 := by
        have : s ^ 8 = s ^ 6 * s ^ 2 := by ring
        rw [this]; exact mul_le_of_le_one_right (by positivity) hs2
      have e3 : 0 ≤ 8 * L * C ^ 2 / F0 := by positivity
      have e4 : 8 * L * C ^ 2 / F0 * s ^ 8 ≤ 8 * L * C ^ 2 / F0 * s ^ 6 :=
        mul_le_mul_of_nonneg_left e2 e3
      have e5 : Lh * s ^ 6 ≤ L * s ^ 6 := mul_le_mul_of_nonneg_right hLhL (by positivity)
      have e6 : Λ * s ^ 6 = L * s ^ 6 + 4 * L * C ^ 2 / F0 * s ^ 6 +
          8 * L * C ^ 2 / F0 * s ^ 6 := by rw [hΛ]; ring
      have e7 : Λ * s ^ 6 < s ^ 5 := by
        have : s ^ 5 * (s * Λ) < s ^ 5 * 1 := mul_lt_mul_of_pos_left hsΛ' (by positivity)
        have e : Λ * s ^ 6 = s ^ 5 * (s * Λ) := by ring
        linarith only [this, e]
      linarith only [e1, e4, e5, e6, e7]
    have hqt : |q (ψ t)| < s ^ 5 := by
      have := abs_le.mp hqy₀
      rw [abs_lt]
      constructor
      · linarith only [this.1, hq2, hmqT, hmqT']
      · linarith only [this.2, hq1, hmqT, hmqT']
    -- `y_k` along the solution
    have hdk : ∀ u ∈ Icc 0 t, HasDerivWithinAt (fun u => ψ u k) (f (ψ u) k) (Icc 0 t) u :=
      fun u hu => (EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt u
        (hst u hu)
    have hk1 := sub_ge_of_deriv_ge (m := -(2 * s ^ 2)) ht.1 le_rfl le_rfl hdk
      (fun u hu => by
        obtain ⟨r1, r2, r3⟩ := hreg u ⟨hu.1.le, hu.2.le⟩
        exact (abs_le.mp (hslope _ r1 r2 r3).1).1)
    rw [hψ0, hy₀k] at hk1
    have hkT : 2 * s ^ 2 * t ≤ 2 * s ^ 2 * T := mul_le_mul_of_nonneg_left ht.2 (by positivity)
    have hkT' : 2 * s ^ 2 * T < s ^ 3 / 2 := by
      have e1 : 2 * s ^ 2 * T = 8 * C * s ^ 2 / F0 * s ^ 3 := by rw [hT]; field_simp; ring
      have e2 : 8 * C * s ^ 2 / F0 < 1 / 2 := by
        rw [div_lt_iff₀ hF0p]; linarith only [hsF']
      rw [e1]
      have := mul_lt_mul_of_pos_right e2 hs3p
      linarith only [this]
    have hNt := hN t ⟨ht.1, le_rfl⟩
    simp only [hΦ, max_lt_iff]
    exact ⟨⟨by linarith only [hNt, hCs3], by linarith only [hk1, hkT, hkT']⟩,
      by linarith only [hqt]⟩
  -- the drift carries the solution away
  have hsT := hseg T hT0 (fun u hu => (hstay u hu).le)
  have hNT := hnear T hsT T ⟨hT0, le_rfl⟩
  have hFxk : Fx k = 0 := by rw [hFx, he]; simp
  have hin_e : inner ℝ Fx e = 0 := by
    rw [he, EuclideanSpace.inner_single_right]; simp [hFxk]
  have hdi : ∀ u ∈ Icc 0 T, HasDerivWithinAt (fun u => inner ℝ Fx (ψ u - x))
      (inner ℝ Fx (f (ψ u))) (Icc 0 T) u :=
    fun u hu => (innerSL ℝ Fx).hasFDerivAt.comp_hasDerivWithinAt u ((hsT u hu).sub_const x)
  have hdib : ∀ u ∈ Ioo 0 T, F0 ^ 2 / 2 ≤ inner ℝ Fx (f (ψ u)) := by
    intro u hu
    have hNu := hnear T hsT u ⟨hu.1.le, hu.2.le⟩
    have hFu := hFb (x := ψ u) (by rw [dist_eq_norm]; linarith)
    simp only [dist_eq_norm] at hFu
    rw [← hFx] at hFu
    have hsplit : f (ψ u) = Fx + ((f (ψ u) - f (ψ u) k • e) - Fx) + f (ψ u) k • e := by abel
    rw [hsplit, inner_add_right, inner_add_right, inner_smul_right, hin_e, mul_zero, add_zero,
      real_inner_self_eq_norm_sq, ← hF0d]
    have h1 := (abs_le.mp (abs_real_inner_le_norm Fx ((f (ψ u) - f (ψ u) k • e) - Fx))).1
    rw [← hF0d] at h1
    have h2 : F0 * ‖f (ψ u) - f (ψ u) k • e - Fx‖ ≤ F0 * (F0 / 2) :=
      mul_le_mul_of_nonneg_left hFu.le hF0p.le
    linarith only [h1, h2]
  have hgrow := sub_ge_of_deriv_ge (m := F0 ^ 2 / 2) hT0 le_rfl le_rfl hdi hdib
  rw [hψ0, hy₀, add_sub_cancel_left, inner_smul_right, hin_e, mul_zero, sub_zero] at hgrow
  have hup : inner ℝ Fx (ψ T - x) ≤ F0 * (C * s ^ 3) := by
    calc inner ℝ Fx (ψ T - x) ≤ ‖Fx‖ * ‖ψ T - x‖ := real_inner_le_norm _ _
      _ ≤ F0 * (C * s ^ 3) := by rw [← hF0d]; exact mul_le_mul_of_nonneg_left hNT hF0p.le
  have hval : F0 ^ 2 / 2 * (T - 0) = 2 * (F0 * (C * s ^ 3)) := by rw [hT]; field_simp; ring
  have hpos : 0 < F0 * (C * s ^ 3) := by positivity
  linarith only [hgrow, hup, hval, hpos]

end powerlib.Dynamics.Degenerate
