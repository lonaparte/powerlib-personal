import theorem.CurrentControl.SISO
import theorem.DCLink.Locality

/-! # Degenerate equilibria of locally `C¹` fields (foundation)

Generic tools for non-hyperbolic equilibria of autonomous continuous-time fields
`f : ℝⁿ → ℝⁿ` (`ℝⁿ = EuclideanSpace ℝ (Fin n)`, the library's segment semantics) that are `C¹`
only on an open set `U` containing the point — typically power-balance fields with a `1/V_dc`
factor, smooth on `V_dc > 0` only. The degenerate-linearization tools of
`theorem/CurrentControl/SISO.lean` (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`,
`Dynamics.unstable_of_chetaev`, `Dynamics.unstable_of_lie_nonpos_of_lie_pos`) and
`Dynamics.isEquilibrium_of_lyapunovStable` (`theorem/Dynamics/ConverseLinearization.lean`) assume a
globally `C¹` field. Here the field is replaced near the point by a globally `C¹` field
(`DCLink.exists_contDiff_eventuallyEq`, a smooth bump) and the conclusions are transported back
with the locality lemmas of `theorem/DCLink/Locality.lean`:

* `localAsymptoticStable_congr_nhds`: local asymptotic stability depends only on the field near
  the point (Lyapunov stability keeps nearby forward-complete solutions where the fields agree).
* `isEquilibrium_of_lyapunovStable_local`: a Lyapunov stable point of a locally `C¹` field is an
  equilibrium.
* `not_localAsymptoticStable_of_lie_nonpos_local`: a function that does not increase along the
  field near the point (within `U`) and takes values below its value at the point arbitrarily
  close to it rules out local asymptotic stability (conserved energies of centres).
* `unstable_of_chetaev_local`: Chetaev's instability theorem (classical form) for locally `C¹`
  fields.
* `unstable_of_lie_nonpos_of_lie_pos_local`: its variant on the sublevel set of a non-increasing
  energy below the level of the point.
* `fderiv_sq_sub_add_apply`, `fderiv_sq_max_add_apply`: chain rule for the composite energies
  `(V − c)² + E` and `(max g 0)² + E`.
* `abs_apply_le_norm`, `norm_le_abs_add_abs_two`, `norm_le_abs_add_abs_three`: comparison of the
  Euclidean norm with the coordinates (seeds of the theorems above).
* `hasDerivAt_sq_max_zero`, `contDiff_one_sq_max_zero`: `t ↦ (max t 0)²` is `C¹` with derivative
  `2 max t 0` — the building block of the "practical" Lyapunov functions `((g − λ E)⁺)² + E` used
  for cascades of a centre with a contracting state.

These are general facts about autonomous ODEs, not engineering conclusions.

Source: standard (Khalil, *Nonlinear Systems*, 3rd ed., Theorems 4.1 and 4.3, stated for `C¹`
fields on a domain); needed by work-sync `theory/T-vsc-dc-voltage-control.md` §1.4.
-/

noncomputable section

namespace powerlib.Dynamics

open Set Filter Topology Metric

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Local asymptotic stability depends only on the field near the point. -/
@[powerlib_foundation] theorem localAsymptoticStable_congr_nhds {f g : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (hfg : f =ᶠ[𝓝 x] g) (hg : LocalAsymptoticStable g x) : LocalAsymptoticStable f x := by
  obtain ⟨hgLS, c, hc, hconv⟩ := hg
  have hfLS : LyapunovStable f x := DCLink.lyapunovStable_congr_nhds hfg hgLS
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hfg
  obtain ⟨δ, hδ, hb⟩ := hfLS ρ hρ
  refine ⟨hfLS, min c δ, lt_min hc hδ, fun t₀ φ hφ h0 => ?_⟩
  have hin : ∀ t, t₀ ≤ t → ‖φ t - x‖ < ρ := fun t ht =>
    hb t₀ t φ (hφ.mono Icc_subset_Ici_self) (h0.trans_le (min_le_right _ _)) t ⟨ht, le_rfl⟩
  have hφg : IsIntegralCurveOn φ (fun _ y => g y) (Ici t₀) := by
    intro t ht
    have h := hφ t ht
    have hfg' : f (φ t) = g (φ t) := hball (by rw [dist_eq_norm]; exact hin t ht)
    simp only at h ⊢
    rw [← hfg']
    exact h
  exact hconv t₀ φ hφg (h0.trans_le (min_le_left _ _))

/-- A field that is `C¹` on an open neighbourhood `U` of `x` agrees near `x` with a globally `C¹`
field, on a ball contained in `U`. -/
private theorem exists_contDiff_ball {f : ℝⁿ → ℝⁿ} {U : Set ℝⁿ} (hU : IsOpen U) {x : ℝⁿ}
    (hx : x ∈ U) (hf : ContDiffOn ℝ 1 f U) :
    ∃ g : ℝⁿ → ℝⁿ, ContDiff ℝ 1 g ∧ g =ᶠ[𝓝 x] f ∧
      ∃ σ > 0, ∀ y, ‖y - x‖ < σ → g y = f y ∧ y ∈ U := by
  obtain ⟨g, hg, hgf⟩ := DCLink.exists_contDiff_eventuallyEq hU hx hf
  obtain ⟨σ, hσ, hball⟩ := Metric.eventually_nhds_iff.mp (hgf.and (hU.mem_nhds hx))
  exact ⟨g, hg, hgf, σ, hσ, fun y hy => hball (by rw [dist_eq_norm]; exact hy)⟩

/-- A Lyapunov stable point of a field that is `C¹` on an open neighbourhood is an equilibrium. -/
@[powerlib_foundation] theorem isEquilibrium_of_lyapunovStable_local {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    {U : Set ℝⁿ} (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ 1 f U)
    (h : LyapunovStable f x) : f x = 0 := by
  obtain ⟨g, hg, hgf⟩ := DCLink.exists_contDiff_eventuallyEq hU hx hf
  have hgx : g x = 0 := isEquilibrium_of_lyapunovStable hg (DCLink.lyapunovStable_congr_nhds hgf h)
  rw [← hgf.eq_of_nhds]
  exact hgx

/-- A function that does not increase along a locally `C¹` field near a point, and takes values
below its value at the point arbitrarily close to it, rules out local asymptotic stability. -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_lie_nonpos_local {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} {U : Set ℝⁿ} {V : ℝⁿ → ℝ} {ρ : ℝ} (hU : IsOpen U) (hx : x_eq ∈ U)
    (hf : ContDiffOn ℝ 1 f U) (hV : Differentiable ℝ V) (hρ : 0 < ρ)
    (hLie : ∀ x ∈ U, ‖x - x_eq‖ < ρ → fderiv ℝ V x (f x) ≤ 0)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ V x < V x_eq) :
    ¬ LocalAsymptoticStable f x_eq := by
  obtain ⟨g, hg, hgf, σ, hσ, hball⟩ := exists_contDiff_ball hU hx hf
  intro h
  refine not_localAsymptoticStable_of_lie_nonpos (ρ := min ρ σ) hg hV (lt_min hρ hσ)
    (fun y hy => ?_) hseed (localAsymptoticStable_congr_nhds hgf h)
  obtain ⟨hgy, hyU⟩ := hball y (hy.trans_le (min_le_right _ _))
  rw [hgy]
  exact hLie y hyU (hy.trans_le (min_le_left _ _))

/-- **Chetaev's instability theorem** for a field that is `C¹` on an open neighbourhood `U` of the
point: a `C¹` function positive at states arbitrarily close to the point and strictly increasing
along the field wherever it is positive, within `U` and distance `r`. -/
@[powerlib_foundation] theorem unstable_of_chetaev_local {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {U : Set ℝⁿ} {W : ℝⁿ → ℝ} {r : ℝ} (hU : IsOpen U) (hx : x_eq ∈ U)
    (hf : ContDiffOn ℝ 1 f U) (hW : ContDiff ℝ 1 W) (hr : 0 < r)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ 0 < W x)
    (hLie : ∀ x ∈ U, ‖x - x_eq‖ ≤ r → 0 < W x → 0 < fderiv ℝ W x (f x)) :
    Unstable f x_eq := by
  obtain ⟨g, hg, hgf, σ, hσ, hball⟩ := exists_contDiff_ball hU hx hf
  rw [DCLink.unstable_congr_nhds hgf.symm]
  refine unstable_of_chetaev (r := min r (σ / 2)) hg hW (lt_min hr (by positivity)) hseed
    (fun y hy hWy => ?_)
  obtain ⟨hgy, hyU⟩ := hball y (hy.trans_lt ((min_le_right _ _).trans_lt (by linarith)))
  rw [hgy]
  exact hLie y hyU (hy.trans (min_le_left _ _)) hWy

/-- **Chetaev's theorem on a non-increasing level set**, for a field that is `C¹` on an open
neighbourhood `U` of the point: an energy `E` that does not increase along the field near the
point and takes values below `E x*` arbitrarily close to it, and a function `W` that strictly
increases wherever `E < E x*` near the point. -/
@[powerlib_foundation] theorem unstable_of_lie_nonpos_of_lie_pos_local {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} {U : Set ℝⁿ} {E W : ℝⁿ → ℝ} {r : ℝ} (hU : IsOpen U) (hx : x_eq ∈ U)
    (hf : ContDiffOn ℝ 1 f U) (hE : ContDiff ℝ 1 E) (hW : ContDiff ℝ 1 W) (hr : 0 < r)
    (hELie : ∀ x ∈ U, ‖x - x_eq‖ ≤ r → fderiv ℝ E x (f x) ≤ 0)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ E x < E x_eq)
    (hWLie : ∀ x ∈ U, ‖x - x_eq‖ ≤ r → E x < E x_eq → 0 < fderiv ℝ W x (f x)) :
    Unstable f x_eq := by
  obtain ⟨g, hg, hgf, σ, hσ, hball⟩ := exists_contDiff_ball hU hx hf
  rw [DCLink.unstable_congr_nhds hgf.symm]
  have hmem : ∀ y, ‖y - x_eq‖ ≤ min r (σ / 2) → g y = f y ∧ y ∈ U := fun y hy =>
    hball y (hy.trans_lt ((min_le_right _ _).trans_lt (by linarith)))
  refine unstable_of_lie_nonpos_of_lie_pos (r := min r (σ / 2)) hg hE hW
    (lt_min hr (by positivity)) (fun y hy => ?_) hseed (fun y hy hEy => ?_)
  · obtain ⟨hgy, hyU⟩ := hmem y hy
    rw [hgy]
    exact hELie y hyU (hy.trans (min_le_left _ _))
  · obtain ⟨hgy, hyU⟩ := hmem y hy
    rw [hgy]
    exact hWLie y hyU (hy.trans (min_le_left _ _)) hEy

/-! ## The squared positive part -/

/-- `t ↦ (max t 0)²` has derivative `2 max t 0` everywhere. -/
@[powerlib_foundation] theorem hasDerivAt_sq_max_zero (t : ℝ) :
    HasDerivAt (fun s : ℝ => max s 0 ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hev : (fun s : ℝ => max s 0 ^ 2) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [max_eq_right (le_of_lt (mem_Iio.mp hs))]
    rw [max_eq_right ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst ht
    rw [max_self, mul_zero, hasDerivAt_iff_isLittleO]
    simp only [max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      smul_zero]
    refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hc] with s hs
    rw [Metric.mem_ball, dist_zero_right] at hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : max s 0 ^ 2 ≤ s ^ 2 := by
      rcases le_total s 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg s]
      · rw [max_eq_left h]
    have h2 : s ^ 2 = |s| * |s| := by rw [← sq_abs, sq]
    calc max s 0 ^ 2 ≤ |s| * |s| := h2 ▸ h1
      _ ≤ c * |s| := mul_le_mul_of_nonneg_right hs.le (abs_nonneg s)
  · have hev : (fun s : ℝ => max s 0 ^ 2) =ᶠ[𝓝 t] fun s => s ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp [max_eq_left (le_of_lt (mem_Ioi.mp hs))]
    rw [max_eq_left ht.le]
    have h : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
    exact h.congr_of_eventuallyEq hev

/-- `t ↦ (max t 0)²` is `C¹`. -/
@[powerlib_foundation] theorem contDiff_one_sq_max_zero :
    ContDiff ℝ 1 (fun s : ℝ => max s 0 ^ 2) := by
  rw [contDiff_one_iff_deriv]
  have hd : deriv (fun s : ℝ => max s 0 ^ 2) = fun t => 2 * max t 0 :=
    funext fun t => (hasDerivAt_sq_max_zero t).deriv
  refine ⟨fun t => (hasDerivAt_sq_max_zero t).differentiableAt, ?_⟩
  rw [hd]
  fun_prop

/-! ## Lie derivatives of composite energies -/

/-- The derivative of `(V − c)² + E` in the direction `v`. -/
@[powerlib_foundation] theorem fderiv_sq_sub_add_apply {V E : ℝⁿ → ℝ} {x : ℝⁿ}
    (hV : DifferentiableAt ℝ V x) (hE : DifferentiableAt ℝ E x) (c : ℝ) (v : ℝⁿ) :
    fderiv ℝ (fun y => (V y - c) ^ 2 + E y) x v =
      2 * (V x - c) * fderiv ℝ V x v + fderiv ℝ E x v := by
  have h := ((hV.hasFDerivAt.sub_const c).pow 2).add hE.hasFDerivAt
  rw [show (fun y => (V y - c) ^ 2 + E y) = (fun y => (V y - c) ^ 2) + E from rfl, h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The derivative of `(max g 0)² + E` in the direction `v`. -/
@[powerlib_foundation] theorem fderiv_sq_max_add_apply {g E : ℝⁿ → ℝ} {x : ℝⁿ}
    (hg : DifferentiableAt ℝ g x) (hE : DifferentiableAt ℝ E x) (v : ℝⁿ) :
    fderiv ℝ (fun y => max (g y) 0 ^ 2 + E y) x v =
      2 * max (g x) 0 * fderiv ℝ g x v + fderiv ℝ E x v := by
  have h := ((hasDerivAt_sq_max_zero (g x)).comp_hasFDerivAt x hg.hasFDerivAt).add
    hE.hasFDerivAt
  rw [show (fun y => max (g y) 0 ^ 2 + E y) = (fun s : ℝ => max s 0 ^ 2) ∘ g + E from rfl,
    h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]

/-! ## Norms of planar and three-dimensional states -/

/-- A coordinate is bounded by the norm. -/
@[powerlib_foundation] theorem abs_apply_le_norm (x : ℝⁿ) (i : Fin n) : |x i| ≤ ‖x‖ := by
  simpa using PiLp.norm_apply_le x i

/-- The Euclidean norm of a planar state is bounded by the sum of the absolute coordinates. -/
@[powerlib_foundation] theorem norm_le_abs_add_abs_two (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ≤ |x 0| + |x 1| := by
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  have h : ‖x‖ ^ 2 ≤ (|x 0| + |x 1|) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_abs (x 0), sq_abs (x 1), mul_nonneg h0 h1]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- The Euclidean norm of a three-dimensional state is bounded by the sum of the absolute
coordinates. -/
@[powerlib_foundation] theorem norm_le_abs_add_abs_three (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ≤ |x 0| + |x 1| + |x 2| := by
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  have h2 := abs_nonneg (x 2)
  have h : ‖x‖ ^ 2 ≤ (|x 0| + |x 1| + |x 2|) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_abs (x 0), sq_abs (x 1), sq_abs (x 2), mul_nonneg h0 h1, mul_nonneg h0 h2,
      mul_nonneg h1 h2]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

end powerlib.Dynamics
