import theorem.Criteria.Hurwitz2
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # Bifurcation hypersurfaces: crossing behaviour of `Σ_SN`, `Σ_WS`, `Σ_DOC`

Foundation layer: generic statements about parameter families, not an engineering model.

1. One-dimensional `Σ_SN` crossing (`fold_crossing`). For a scalar family `ẋ = f(x, μ)` with a
   fold at `(x₀, μ₀)` — on a box `[x₀ − r, x₀ + r] × [μ₀ − ε, μ₀ + ε]` the map `x ↦ f(x, μ)` is
   strictly convex for every `μ` (the local form of `f_xx > 0`), `μ ↦ f(x, μ)` is strictly
   increasing for every `x` (the local form of `f_μ > 0`), `f` is continuous, and
   `f(x₀, μ₀) = 0` is the minimum of `f(·, μ₀)` (`f_x(x₀, μ₀) = 0`) — the number of equilibria in
   `[x₀ − r, x₀ + r]` is `0` for `μ ∈ (μ₀, μ₀ + ε]` and exactly `2` for `μ` in some
   `(μ₀ − ε', μ₀)`: crossing `Σ_SN` changes the count `2 → 0`. (The derivation of the box
   conditions from `f ∈ C²`, `f_xx ≠ 0`, `f_μ ≠ 0` by continuity is not formalized.)
2. `Σ_WS` with transversality (`ws_crossing_trace`, `ws_crossing_det`): for a planar family with
   equilibrium Jacobian `A(μ)` (derived with `fderiv`), if `det A > 0` near `μ₀`, `tr A(μ₀) = 0`
   and `d tr/dμ > 0` at `μ₀` (Hopf type), the equilibrium is locally exponentially stable just
   below `μ₀` and unstable just above; similarly for `det A` crossing zero downwards with
   `tr A < 0` (saddle-node type).
3. `Σ_DOC` is not a stability boundary (`exponentiallyStable_node_and_focus`): for planar LTI
   systems exponential stability is `tr < 0 ∧ det > 0` irrespective of the discriminant sign;
   a stable node and a stable focus are both exponentially stable.
4. Equilibrium continuation (wrapper of Mathlib's implicit function theorem,
   `ContDiffAt.implicitFunction`): if `f(μ₀, x₀) = 0` and the state Jacobian
   `∂ₓf(μ₀, x₀)` is invertible (e.g. a matrix with `det A(μ₀) ≠ 0`), there is a `Cⁿ` branch
   `x = ψ(μ)` with `ψ(μ₀) = x₀`, `f(μ, ψ(μ)) = 0` near `μ₀`, and near `(μ₀, x₀)` these are the only
   equilibria (`equilibrium_branch`, `equilibrium_branch_matrix`).

Correction (T-bifurcation-hypersurfaces.md §1.1–1.2): "多个 `Σ_•` 的并把 `𝒫` 切成拓扑等价的连通
区域" is false as stated when `Σ_DOC` is included: crossing `Σ_DOC` (node ↔ focus) keeps the
equilibrium exponentially stable (item 3), so `Σ_DOC` separates convergence styles, not stability
types; it is not a codimension-one bifurcation boundary in the sense of §1.1.

Source: work-sync theory/T-bifurcation-hypersurfaces.md §1.1–1.2; theory/T-bifurcation.md §1.2
(`det A(μ*) ≠ 0` ⇒ smooth continuation of the equilibrium branch), §1.4.
-/

noncomputable section
namespace powerlib.NormalForm

open Set Filter Topology

/-! ## 1. `Σ_SN` crossing in one dimension -/

/-- Strict convexity at an interior point: `g b < θ g a + (1 − θ) g c`. -/
@[powerlib_foundation] theorem strictConvexOn_lt_secant {s : Set ℝ} {g : ℝ → ℝ}
    (hg : StrictConvexOn ℝ s g) {a b c : ℝ} (ha : a ∈ s) (hc : c ∈ s) (hab : a < b)
    (hbc : b < c) :
    g b < (c - b) / (c - a) * g a + (b - a) / (c - a) * g c := by
  have hca : 0 < c - a := by linarith
  have h := hg.2 ha hc (by linarith : a ≠ c) (div_pos (by linarith : 0 < c - b) hca)
    (div_pos (by linarith : 0 < b - a) hca)
    (by rw [← add_div, div_eq_one_iff_eq hca.ne']; ring)
  have hb : ((c - b) / (c - a)) • a + ((b - a) / (c - a)) • c = b := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [hb] at h
  simpa only [smul_eq_mul] using h

/-- A strictly convex function on `[a, b]` that is positive at both ends and negative at an
interior point `c` has exactly two zeros in `[a, b]`. -/
@[powerlib_foundation] theorem ncard_zeros_strictConvex {g : ℝ → ℝ} {a b c : ℝ}
    (hg : StrictConvexOn ℝ (Icc a b) g) (hcont : ContinuousOn g (Icc a b)) (hac : a < c)
    (hcb : c < b) (ha : 0 < g a) (hb : 0 < g b) (hgc : g c < 0) :
    {x ∈ Icc a b | g x = 0}.ncard = 2 := by
  have haI : a ∈ Icc a b := ⟨le_rfl, by linarith⟩
  have hbI : b ∈ Icc a b := ⟨by linarith, le_rfl⟩
  have hcI : c ∈ Icc a b := ⟨hac.le, hcb.le⟩
  -- one zero on each side of `c`
  obtain ⟨z₁, hz₁, hgz₁⟩ : ∃ z ∈ Icc a c, g z = 0 :=
    intermediate_value_Icc' hac.le (hcont.mono (Icc_subset_Icc_right hcb.le)) ⟨hgc.le, ha.le⟩
  obtain ⟨z₂, hz₂, hgz₂⟩ : ∃ z ∈ Icc c b, g z = 0 :=
    intermediate_value_Icc hcb.le (hcont.mono (Icc_subset_Icc_left hac.le)) ⟨hgc.le, hb.le⟩
  have hz₁c : z₁ < c := lt_of_le_of_ne hz₁.2 (by rintro rfl; linarith)
  have hcz₂ : c < z₂ := lt_of_le_of_ne hz₂.1 (by rintro rfl; linarith)
  have hz₁I : z₁ ∈ Icc a b := ⟨hz₁.1, by linarith⟩
  have hz₂I : z₂ ∈ Icc a b := ⟨by linarith, hz₂.2⟩
  have hset : {x ∈ Icc a b | g x = 0} = {z₁, z₂} := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hxI, hgx⟩
      rcases lt_trichotomy x c with hxc | rfl | hxc
      · left
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have := strictConvexOn_lt_secant hg hxI hcI h hz₁c
          rw [hgx, hgz₁] at this
          have : 0 < (z₁ - x) / (c - x) * g c * (-1) := by
            have : 0 < (z₁ - x) / (c - x) := div_pos (by linarith) (by linarith)
            nlinarith
          nlinarith
        · have := strictConvexOn_lt_secant hg hz₁I hcI h hxc
          rw [hgx, hgz₁] at this
          have : 0 < (x - z₁) / (c - z₁) := div_pos (by linarith) (by linarith)
          nlinarith
      · linarith
      · right
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have := strictConvexOn_lt_secant hg hcI hz₂I hxc h
          rw [hgx, hgz₂] at this
          have : 0 < (z₂ - x) / (z₂ - c) := div_pos (by linarith) (by linarith)
          nlinarith
        · have := strictConvexOn_lt_secant hg hcI hxI hcz₂ h
          rw [hgx, hgz₂] at this
          have : 0 < (x - z₂) / (x - c) := div_pos (by linarith) (by linarith)
          nlinarith
    · rintro (rfl | rfl)
      · exact ⟨hz₁I, hgz₁⟩
      · exact ⟨hz₂I, hgz₂⟩
  rw [hset, ncard_pair (by intro h; linarith)]

/-- One-dimensional `Σ_SN` crossing (local box form of `f_xx > 0`, `f_μ > 0`): no equilibrium
in `[x₀ − r, x₀ + r]` just above `μ₀`, exactly two just below. -/
@[powerlib_foundation] theorem fold_crossing {f : ℝ → ℝ → ℝ} {x₀ μ₀ r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε)
    (hconv : ∀ μ ∈ Icc (μ₀ - ε) (μ₀ + ε), StrictConvexOn ℝ (Icc (x₀ - r) (x₀ + r)) (f · μ))
    (hmono : ∀ x ∈ Icc (x₀ - r) (x₀ + r), StrictMonoOn (f x) (Icc (μ₀ - ε) (μ₀ + ε)))
    (hcont : ContinuousOn (Function.uncurry f) (Icc (x₀ - r) (x₀ + r) ×ˢ Icc (μ₀ - ε) (μ₀ + ε)))
    (h0 : f x₀ μ₀ = 0) (hmin : ∀ x ∈ Icc (x₀ - r) (x₀ + r), 0 ≤ f x μ₀) :
    (∀ μ ∈ Ioc μ₀ (μ₀ + ε), ∀ x ∈ Icc (x₀ - r) (x₀ + r), f x μ ≠ 0) ∧
      ∃ ε' > 0, ∀ μ ∈ Ioo (μ₀ - ε') μ₀, {x ∈ Icc (x₀ - r) (x₀ + r) | f x μ = 0}.ncard = 2 := by
  have hμ₀ : μ₀ ∈ Icc (μ₀ - ε) (μ₀ + ε) := ⟨by linarith, by linarith⟩
  have hx₀ : x₀ ∈ Icc (x₀ - r) (x₀ + r) := ⟨by linarith, by linarith⟩
  refine ⟨fun μ hμ x hx => ?_, ?_⟩
  · have := hmono x hx hμ₀ ⟨by linarith [hμ.1], hμ.2⟩ hμ.1
    linarith [hmin x hx]
  -- endpoint values are positive at `μ₀`
  have hend : ∀ y ∈ ({x₀ - r, x₀ + r} : Set ℝ), 0 < f y μ₀ := by
    intro y hy
    have hyI : y ∈ Icc (x₀ - r) (x₀ + r) := by
      rcases hy with rfl | rfl
      · exact ⟨le_rfl, by linarith⟩
      · exact ⟨by linarith, le_rfl⟩
    rcases lt_or_eq_of_le (hmin y hyI) with h | h
    · exact h
    · exfalso
      rcases hy with rfl | rfl
      · have := strictConvexOn_lt_secant (hconv μ₀ hμ₀) hyI hx₀ (by linarith : x₀ - r < x₀ - r / 2)
          (by linarith)
        rw [← h, h0] at this
        have := hmin (x₀ - r / 2) ⟨by linarith, by linarith⟩
        linarith
      · have := strictConvexOn_lt_secant (hconv μ₀ hμ₀) hx₀ hyI (by linarith : x₀ < x₀ + r / 2)
          (by linarith)
        rw [← h, h0] at this
        have := hmin (x₀ + r / 2) ⟨by linarith, by linarith⟩
        linarith
  -- by continuity in `μ`, they stay positive slightly below `μ₀`
  have hpos : ∀ y ∈ ({x₀ - r, x₀ + r} : Set ℝ),
      ∀ᶠ μ in 𝓝[Icc (μ₀ - ε) (μ₀ + ε)] μ₀, 0 < f y μ := by
    intro y hy
    have hyI : y ∈ Icc (x₀ - r) (x₀ + r) := by
      rcases hy with rfl | rfl
      · exact ⟨le_rfl, by linarith⟩
      · exact ⟨by linarith, le_rfl⟩
    have hc : ContinuousWithinAt (f y) (Icc (μ₀ - ε) (μ₀ + ε)) μ₀ := by
      have := (hcont (y, μ₀) ⟨hyI, hμ₀⟩).comp (continuousWithinAt_const.prodMk continuousWithinAt_id)
        (fun μ hμ => ⟨hyI, hμ⟩)
      exact this
    exact hc.eventually (lt_mem_nhds (hend y hy))
  have hboth := (hpos _ (Or.inl rfl)).and (hpos _ (Or.inr rfl))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hboth
  obtain ⟨δ, hδ, hball⟩ := hboth
  refine ⟨min δ ε, lt_min hδ hε, fun μ hμ => ?_⟩
  have hμI : μ ∈ Icc (μ₀ - ε) (μ₀ + ε) :=
    ⟨by linarith [hμ.1, min_le_right δ ε], by linarith [hμ.2]⟩
  have hdist : dist μ μ₀ < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hμ.1, hμ.2, min_le_left δ ε]
  obtain ⟨hl, hr'⟩ := hball hdist hμI
  have hc : f x₀ μ < 0 := by
    have := hmono x₀ hx₀ hμI hμ₀ hμ.2
    linarith
  apply ncard_zeros_strictConvex (hconv μ hμI) _ (by linarith) (by linarith) hl hr' hc
  exact (hcont.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨hx, hμI⟩))

/-! ## 2. `Σ_WS` crossing with transversality -/

/-- Hopf-type `Σ_WS` crossing: `det A > 0` near `μ₀`, `tr A(μ₀) = 0`, `d tr/dμ (μ₀) > 0`. -/
@[powerlib_foundation] theorem ws_crossing_trace {F : ℝ → Dynamics.State 2 → Dynamics.State 2}
    {xe : ℝ → Dynamics.State 2} {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {μ₀ τ : ℝ}
    (hF : ∀ μ, ContDiff ℝ 1 (F μ)) (heq : ∀ μ, F μ (xe μ) = 0)
    (hJ : ∀ μ, fderiv ℝ (F μ) (xe μ) = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (A μ))
    (hdet : ∀ᶠ μ in 𝓝 μ₀, 0 < (A μ).det) (htr0 : (A μ₀).trace = 0)
    (htr : HasDerivAt (fun μ => (A μ).trace) τ μ₀) (hτ : 0 < τ) :
    (∀ᶠ μ in 𝓝[<] μ₀, Dynamics.LocallyExponentiallyStable (F μ) (xe μ)) ∧
      ∀ᶠ μ in 𝓝[>] μ₀, Dynamics.Unstable (F μ) (xe μ) := by
  have hslope := htr.hasDerivWithinAt (s := Iio μ₀)
  -- sign of the trace on each side, from the derivative
  have hlt : ∀ᶠ μ in 𝓝[<] μ₀, (A μ).trace < 0 := by
    have h := htr.tendsto_slope_zero_left
    have : ∀ᶠ t in 𝓝[<] (0 : ℝ), 0 < t⁻¹ • ((A (μ₀ + t)).trace - (A μ₀).trace) :=
      h.eventually (lt_mem_nhds hτ)
    have h2 : ∀ᶠ t in 𝓝[<] (0 : ℝ), (A (μ₀ + t)).trace < 0 := by
      filter_upwards [this, self_mem_nhdsWithin] with t ht htneg
      rw [htr0, sub_zero, smul_eq_mul] at ht
      have htn : t < 0 := htneg
      nlinarith [inv_lt_zero.mpr htn, mul_pos_iff.mp ht]
    have hmap : Tendsto (fun μ => μ - μ₀) (𝓝[<] μ₀) (𝓝[<] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (continuous_sub_right μ₀).tendsto' μ₀ 0 (by simp) |>.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with μ hμ
        simpa using hμ
    filter_upwards [hmap.eventually h2] with μ hμ
    simpa using hμ
  have hgt : ∀ᶠ μ in 𝓝[>] μ₀, 0 < (A μ).trace := by
    have h := htr.tendsto_slope_zero_right
    have : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • ((A (μ₀ + t)).trace - (A μ₀).trace) :=
      h.eventually (lt_mem_nhds hτ)
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (A (μ₀ + t)).trace := by
      filter_upwards [this, self_mem_nhdsWithin] with t ht htpos
      rw [htr0, sub_zero, smul_eq_mul] at ht
      have htp : 0 < t := htpos
      exact (pos_iff_pos_of_mul_pos ht).mp (inv_pos.mpr htp)
    have hmap : Tendsto (fun μ => μ - μ₀) (𝓝[>] μ₀) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (continuous_sub_right μ₀).tendsto' μ₀ 0 (by simp) |>.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with μ hμ
        simpa using hμ
    filter_upwards [hmap.eventually h2] with μ hμ
    simpa using hμ
  constructor
  · filter_upwards [hlt, nhdsWithin_le_nhds hdet] with μ h1 h2
    exact Criteria.locallyExponentiallyStable_of_jacobian_fin_two (A μ) (hF μ) (heq μ) (hJ μ) h1 h2
  · filter_upwards [hgt] with μ h1
    exact Criteria.unstable_of_jacobian_trace_pos_fin_two (A μ) (hF μ) (heq μ) (hJ μ) h1

/-- Saddle-node-type `Σ_WS` crossing: `tr A < 0` near `μ₀`, `det A(μ₀) = 0`,
`d det/dμ (μ₀) < 0`. -/
@[powerlib_foundation] theorem ws_crossing_det {F : ℝ → Dynamics.State 2 → Dynamics.State 2}
    {xe : ℝ → Dynamics.State 2} {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {μ₀ κ : ℝ}
    (hF : ∀ μ, ContDiff ℝ 1 (F μ)) (heq : ∀ μ, F μ (xe μ) = 0)
    (hJ : ∀ μ, fderiv ℝ (F μ) (xe μ) = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (A μ))
    (htr : ∀ᶠ μ in 𝓝 μ₀, (A μ).trace < 0) (hdet0 : (A μ₀).det = 0)
    (hdet : HasDerivAt (fun μ => (A μ).det) κ μ₀) (hκ : κ < 0) :
    (∀ᶠ μ in 𝓝[<] μ₀, Dynamics.LocallyExponentiallyStable (F μ) (xe μ)) ∧
      ∀ᶠ μ in 𝓝[>] μ₀, Dynamics.Unstable (F μ) (xe μ) := by
  have hneg : HasDerivAt (fun μ => -(A μ).det) (-κ) μ₀ := hdet.neg
  have hlt : ∀ᶠ μ in 𝓝[<] μ₀, 0 < (A μ).det := by
    have h := hneg.tendsto_slope_zero_left
    have : ∀ᶠ t in 𝓝[<] (0 : ℝ), 0 < t⁻¹ • (-(A (μ₀ + t)).det - -(A μ₀).det) :=
      h.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ t in 𝓝[<] (0 : ℝ), 0 < (A (μ₀ + t)).det := by
      filter_upwards [this, self_mem_nhdsWithin] with t ht htneg
      rw [hdet0, neg_zero, sub_zero, smul_eq_mul] at ht
      have htn : t < 0 := htneg
      have := (neg_iff_neg_of_mul_pos ht).mp (inv_lt_zero.mpr htn)
      linarith
    have hmap : Tendsto (fun μ => μ - μ₀) (𝓝[<] μ₀) (𝓝[<] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (continuous_sub_right μ₀).tendsto' μ₀ 0 (by simp) |>.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with μ hμ
        simpa using hμ
    filter_upwards [hmap.eventually h2] with μ hμ
    simpa using hμ
  have hgt : ∀ᶠ μ in 𝓝[>] μ₀, (A μ).det < 0 := by
    have h := hneg.tendsto_slope_zero_right
    have : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (-(A (μ₀ + t)).det - -(A μ₀).det) :=
      h.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (A (μ₀ + t)).det < 0 := by
      filter_upwards [this, self_mem_nhdsWithin] with t ht htpos
      rw [hdet0, neg_zero, sub_zero, smul_eq_mul] at ht
      have htp : 0 < t := htpos
      have := (pos_iff_pos_of_mul_pos ht).mp (inv_pos.mpr htp)
      linarith
    have hmap : Tendsto (fun μ => μ - μ₀) (𝓝[>] μ₀) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (continuous_sub_right μ₀).tendsto' μ₀ 0 (by simp) |>.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with μ hμ
        simpa using hμ
    filter_upwards [hmap.eventually h2] with μ hμ
    simpa using hμ
  constructor
  · filter_upwards [hlt, nhdsWithin_le_nhds htr] with μ h1 h2
    exact Criteria.locallyExponentiallyStable_of_jacobian_fin_two (A μ) (hF μ) (heq μ) (hJ μ) h2 h1
  · filter_upwards [hgt] with μ h1
    exact Criteria.unstable_of_jacobian_det_neg_fin_two (A μ) (hF μ) (heq μ) (hJ μ) h1

/-! ## 3. `Σ_DOC` is not a stability boundary -/

/-- A stable node (`tr² − 4 det > 0`) and a stable focus (`tr² − 4 det < 0`) are both
exponentially stable: crossing `Σ_DOC` does not change stability. -/
@[powerlib_foundation] theorem exponentiallyStable_node_and_focus :
    LTI.ExponentiallyStable ⟨!![-3, 0; 0, -1]⟩ ∧
      (!![-3, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 -
        4 * (!![-3, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).det > 0 ∧
      LTI.ExponentiallyStable ⟨!![-1, -1; 1, -1]⟩ ∧
      (!![-1, -1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 -
        4 * (!![-1, -1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ).det < 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Criteria.exponentiallyStable_fin_two_iff]
    norm_num [Matrix.trace_fin_two, Matrix.det_fin_two]
  · norm_num [Matrix.trace_fin_two, Matrix.det_fin_two]
  · rw [Criteria.exponentiallyStable_fin_two_iff]
    norm_num [Matrix.trace_fin_two, Matrix.det_fin_two]
  · norm_num [Matrix.trace_fin_two, Matrix.det_fin_two]

/-- For a planar LTI model, exponential stability is decided by `tr < 0 ∧ det > 0` alone: the
discriminant (the `Σ_DOC` coordinate) plays no role. -/
@[powerlib_foundation] theorem exponentiallyStable_indep_discriminant
    (m₁ m₂ : LTI.AutonomousModel 2) (htr : m₁.A.trace = m₂.A.trace)
    (hdet : m₁.A.det = m₂.A.det) :
    LTI.ExponentiallyStable m₁ ↔ LTI.ExponentiallyStable m₂ := by
  rw [Criteria.exponentiallyStable_fin_two_iff, Criteria.exponentiallyStable_fin_two_iff, htr,
    hdet]

/-! ## 4. Equilibrium continuation (implicit function theorem wrapper) -/

section Continuation

variable {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- If `f(μ₀, x₀) = 0` and the state Jacobian is invertible, the equilibrium continues to a `Cⁿ`
branch `ψ`, unique near `(μ₀, x₀)`. Wraps Mathlib `ContDiffAt.implicitFunction`,
`ContDiffAt.contDiffAt_implicitFunction`, `ContDiffAt.eventually_apply_implicitFunction` and
`ContDiffAt.eventually_apply_eq_iff_implicitFunction`. -/
@[powerlib_foundation] theorem equilibrium_branch {f : P × X → X} {μ₀ : P} {x₀ : X}
    {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f (μ₀, x₀)) (hn : n ≠ 0) (heq : f (μ₀, x₀) = 0)
    (hinv : (fderiv ℝ f (μ₀, x₀) ∘L ContinuousLinearMap.inr ℝ P X).IsInvertible) :
    ∃ ψ : P → X, ψ μ₀ = x₀ ∧ ContDiffAt ℝ n ψ μ₀ ∧ (∀ᶠ μ in 𝓝 μ₀, f (μ, ψ μ) = 0) ∧
      ∀ᶠ v in 𝓝 (μ₀, x₀), f v = 0 ↔ ψ v.1 = v.2 := by
  refine ⟨hf.implicitFunction hn hinv, hf.implicitFunction_apply_self hn hinv,
    hf.contDiffAt_implicitFunction hn hinv, ?_, ?_⟩
  · simpa [heq] using hf.eventually_apply_implicitFunction hn hinv
  · simpa [heq] using hf.eventually_apply_eq_iff_implicitFunction hn hinv

end Continuation

/-- Matrix form: on `X = ℝⁿ`, a state Jacobian `A` with `det A ≠ 0` is invertible, so the
equilibrium continues smoothly. -/
@[powerlib_foundation] theorem equilibrium_branch_matrix {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [CompleteSpace P] {k : ℕ} {f : P × (Fin k → ℝ) → Fin k → ℝ} {μ₀ : P}
    {x₀ : Fin k → ℝ} {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f (μ₀, x₀)) (hn : n ≠ 0)
    (heq : f (μ₀, x₀) = 0) (A : Matrix (Fin k) (Fin k) ℝ)
    (hJ : fderiv ℝ f (μ₀, x₀) ∘L ContinuousLinearMap.inr ℝ P (Fin k → ℝ) =
      (Matrix.toLin' A).toContinuousLinearMap)
    (hdet : A.det ≠ 0) :
    ∃ ψ : P → Fin k → ℝ, ψ μ₀ = x₀ ∧ ContDiffAt ℝ n ψ μ₀ ∧ (∀ᶠ μ in 𝓝 μ₀, f (μ, ψ μ) = 0) ∧
      ∀ᶠ v in 𝓝 (μ₀, x₀), f v = 0 ↔ ψ v.1 = v.2 := by
  apply equilibrium_branch hf hn heq
  rw [hJ]
  let _ := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hdet)
  exact ⟨(Matrix.toLinearEquiv' A inferInstance).toContinuousLinearEquiv, rfl⟩

end powerlib.NormalForm
