import theorem.Dynamics.Degenerate.PlaneCollapse

/-! # Collapse onto an invariant coordinate plane

The case of `theorem/Dynamics/Degenerate/PlaneCollapse.lean` where the field is tangent to the
plane it collapses onto: solution segments off the plane are driven into it, and the plane carries
a flow of its own. Written for the open-loop VSM–DC model with a source current that does not
cross the singular plane (`theorem/GridTiedConverter/GFM/DCLink/OpenLoop.lean`).

Scope.
* Generic foundation, independent of any model: it imports no engineering module and defines no
  family. An arbitrary autonomous field `f : ℝⁿ → ℝⁿ` (continuous time, no inputs) and a point
  `x` on the coordinate plane `y_k = 0`, read through the Flow semantics of
  `theorem/Flow/Defs.lean` (solution segments on `[t₀, t₁]`, Mathlib integral curves). No
  regularity of `f` is assumed.
* The flow on the plane is represented by a field `g` on `ℝⁿ` equal to `f` on the plane. For the
  passage from `f` to `g`, `g(y) = f(y − y_k e_k) − y_k e_k` (`f` read at the projection of `y`
  onto the plane, the `k`-th coordinate relaxed at unit rate) and the plane is invariant
  (`f_k = 0` on it): a solution of `g` is then a solution of `f` on the plane, its projection,
  plus a `k`-th coordinate decaying as `e^{−t}`.

Source: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.1 (stability, asymptotic stability)
and Definition 4.5 (exponential stability); the reductions are new (it answers the case left open in
`theorem/GridTiedConverter/GFM/DCLink/OpenLoop.lean`: a source current that does not cross the
singular plane).

Results.
* `lyapunovStable_of_invariantPlane`, `locallyExponentiallyStable_of_invariantPlane`,
  `localAsymptoticStable_of_invariantPlane`: with an invariant plane and `g` as above, Lyapunov
  stability, local exponential stability, or local asymptotic stability, of `x` for `f` passes to
  `g`. So instability of `g` (for instance at a point where `g` does not
  vanish, or from a Jacobian eigenvalue of `g`) is instability of `f`.
* `lyapunovStable_of_invariantPlane_collapse`,
  `locallyExponentiallyStable_of_invariantPlane_collapse`: conversely, if near `x` the field
  collapses onto the plane (`2 y_k f_k(y) ≤ −a` off it, the components off `k` bounded) and `x`
  is Lyapunov stable, or locally exponentially stable, for a field `g` equal to `f` on the plane
  near `x`, then so it is for `f`. A segment of `f` near `x` runs off the plane until it first
  reaches it — that part obeys the collapse estimate (`locallyExponentiallyStable_of_collapse`,
  applied to `f` changed on the plane so that it crosses it) — and then stays on the plane
  (`y_k²` does not increase), where it is a segment of `g`.
* `lyapunovStable_iff_of_invariantPlane`, `locallyExponentiallyStable_iff_of_invariantPlane`: the
  two directions together. Under the collapse the stability of `x` is exactly that of the flow on
  the plane.
* `lyapunovStable_iff_of_invariantPlane_firstIntegral`: without collapse, a first integral off the
  plane. If the components of `f` off `k` do not depend on `y_k` and off the plane
  `y_k f_k = Ġ` for a differentiable `G` independent of `y_k` (`y_k²/2 − G` conserved), Lyapunov
  stability of `x` for `f` is that for `g`: since its last visit to the plane, `y_k²` along a
  segment grows by at most twice the oscillation of `G` along the projection (mean value
  theorem, `sSup` of the closed set of visits).
-/

noncomputable section
namespace powerlib.Dynamics.Degenerate
open Set Filter Topology

variable {n : ℕ}

/-! ## A solution of the plane field splits -/

/-- With `f_k = 0` on the plane, the `k`-th component of `g(y) = f(y − y_k e_k) − y_k e_k` is
`−y_k`. -/
@[tmio T, powerlib_foundation] private theorem plane_apply_k {f g : State n → State n}
    (k : Fin n) (hplane : ∀ y : State n, y k = 0 → f y k = 0)
    (hg : ∀ y : State n, g y = f (y - y k • EuclideanSpace.single k (1 : ℝ)) -
      y k • EuclideanSpace.single k (1 : ℝ)) (y : State n) : g y k = -y k := by
  have hek : EuclideanSpace.single k (1 : ℝ) k = 1 := by simp
  rw [hg, PiLp.sub_apply, hplane _ (by simp), PiLp.smul_apply, hek, smul_eq_mul, mul_one,
    zero_sub]

/-- The projection onto the plane of a solution of `g(y) = f(y − y_k e_k) − y_k e_k`, on any set
of times, is a solution of `f` when `f_k = 0` on the plane. -/
@[tmio T, powerlib_foundation] private theorem isIntegralCurveOn_proj {f g : State n → State n}
    (k : Fin n) (hplane : ∀ y : State n, y k = 0 → f y k = 0)
    (hg : ∀ y : State n, g y = f (y - y k • EuclideanSpace.single k (1 : ℝ)) -
      y k • EuclideanSpace.single k (1 : ℝ))
    {ψ : ℝ → State n} {s : Set ℝ} (hψ : IsIntegralCurveOn ψ (fun _ y => g y) s) :
    IsIntegralCurveOn (fun t => ψ t - ψ t k • EuclideanSpace.single k (1 : ℝ))
      (fun _ y => f y) s := by
  set e := EuclideanSpace.single k (1 : ℝ) with he
  set P : State n →L[ℝ] State n := ContinuousLinearMap.id ℝ (State n) -
    (EuclideanSpace.proj k : State n →L[ℝ] ℝ).smulRight e with hPdef
  have hP : ∀ v, P v = v - v k • e := fun v => by simp [hPdef]
  have hPg : ∀ y : State n, P (g y) = f (y - y k • e) := fun y => by
    rw [hP, plane_apply_k k hplane hg, hg]
    module
  intro t ht
  have h := P.hasFDerivAt.comp_hasDerivWithinAt t (hψ t ht)
  rw [hPg] at h
  convert h using 1
  funext s
  simp only [Function.comp_apply, hP]

/-- A solution segment of `g(y) = f(y − y_k e_k) − y_k e_k` splits, when `f_k = 0` on the plane,
into its projection onto the plane, a solution segment of `f`, and a `k`-th coordinate decaying
as `e^{−t}`. -/
@[tmio T, powerlib_foundation] private theorem isTrajectoryOn_proj {f g : State n → State n}
    (k : Fin n) (hplane : ∀ y : State n, y k = 0 → f y k = 0)
    (hg : ∀ y : State n, g y = f (y - y k • EuclideanSpace.single k (1 : ℝ)) -
      y k • EuclideanSpace.single k (1 : ℝ))
    {ψ : ℝ → State n} {t₀ t₁ : ℝ} (hψ : IsTrajectoryOn ψ g t₀ t₁) :
    IsTrajectoryOn (fun t => ψ t - ψ t k • EuclideanSpace.single k (1 : ℝ)) f t₀ t₁ ∧
      ∀ t ∈ Icc t₀ t₁, ψ t k = ψ t₀ k * Real.exp (-(t - t₀)) := by
  have hgk := plane_apply_k k hplane hg
  refine ⟨isIntegralCurveOn_proj k hplane hg hψ, ?_⟩
  · have hd : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt (fun t => ψ t k) (-ψ t k) (Icc t₀ t₁) t :=
      fun t ht => by
        have h := (EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
          (hψ t ht)
        rw [← hgk]
        exact h
    have hh : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt (fun t => ψ t k * Real.exp (t - t₀)) 0
        (Icc t₀ t₁) t := fun t ht => by
      have h := (hd t ht).mul (((hasDerivWithinAt_id t _).sub_const t₀).exp)
      convert h using 1
      · rfl
      · simp only [id]
        ring
    have hconst := constant_of_has_deriv_right_zero (f := fun t => ψ t k * Real.exp (t - t₀))
      (fun t ht => (hh t ht).continuousWithinAt) (fun t ht =>
        (hh t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)))
    intro t ht
    have h := hconst t ht
    simp only [sub_self, Real.exp_zero, mul_one] at h
    rw [← h, mul_assoc, ← Real.exp_add]
    simp

/-- The distance of the projection to a point of the plane, and the remaining coordinate. -/
@[tmio T, powerlib_foundation] private theorem norm_sub_le_proj {x : State n} (k : Fin n)
    (hxk : x k = 0) (y : State n) :
    ‖(y - y k • EuclideanSpace.single k (1 : ℝ)) - x‖ ≤ ‖y - x‖ ∧
      ‖y - x‖ ≤ ‖(y - y k • EuclideanSpace.single k (1 : ℝ)) - x‖ + |y k| ∧ |y k| ≤ ‖y - x‖ := by
  have hid : (y - y k • EuclideanSpace.single k (1 : ℝ)) - x =
      (y - x) - (y - x) k • EuclideanSpace.single k (1 : ℝ) := by
    rw [PiLp.sub_apply, hxk, sub_zero]
    abel
  have hk : (y - x) k = y k := by rw [PiLp.sub_apply, hxk, sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [hid]
    exact norm_sub_smul_single_le k _
  · rw [hid, ← hk]
    exact norm_le_norm_sub_smul_single_add k _
  · rw [← hk]
    exact abs_apply_le_norm _ k

/-! ## From `f` to the plane field -/

/-- **Lyapunov stability passes to the plane field.** If `f_k = 0` on the plane `y_k = 0`
through `x`, and `g(y) = f(y − y_k e_k) − y_k e_k`, a Lyapunov stable point for `f` is Lyapunov
stable for `g`: a solution of `g` is a solution of `f` on the plane plus a decaying `y_k`. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_of_invariantPlane {f g : State n → State n}
    {x : State n} (k : Fin n) (hxk : x k = 0) (hplane : ∀ y : State n, y k = 0 → f y k = 0)
    (hg : ∀ y : State n, g y = f (y - y k • EuclideanSpace.single k (1 : ℝ)) -
      y k • EuclideanSpace.single k (1 : ℝ))
    (h : LyapunovStable f x) : LyapunovStable g x := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h (ε / 2) (half_pos hε)
  refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), fun t₀ t₁ ψ hψ h0 t ht => ?_⟩
  obtain ⟨hχ, hk⟩ := isTrajectoryOn_proj k hplane hg hψ
  obtain ⟨h1, -, h3⟩ := norm_sub_le_proj k hxk (ψ t₀)
  obtain ⟨-, h5, -⟩ := norm_sub_le_proj k hxk (ψ t)
  have hδ' : ‖ψ t₀ - x‖ < δ := lt_of_lt_of_le h0 (min_le_left _ _)
  have hε' : ‖ψ t₀ - x‖ < ε / 2 := lt_of_lt_of_le h0 (min_le_right _ _)
  have h6 := hb t₀ t₁ _ hχ (lt_of_le_of_lt h1 hδ') t ht
  have h7 : |ψ t k| ≤ |ψ t₀ k| := by
    rw [hk t ht, abs_mul, Real.abs_exp]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr (by linarith [ht.1]))
  simp only at h6
  linarith

/-- **Local exponential stability passes to the plane field** (as
`lyapunovStable_of_invariantPlane`): the estimate of `f` with constants `C, a` gives that of `g`
with `C + 1` and `min a 1`. -/
@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_of_invariantPlane
    {f g : State n → State n} {x : State n} (k : Fin n) (hxk : x k = 0)
    (hplane : ∀ y : State n, y k = 0 → f y k = 0)
    (hg : ∀ y : State n, g y = f (y - y k • EuclideanSpace.single k (1 : ℝ)) -
      y k • EuclideanSpace.single k (1 : ℝ))
    (h : LocallyExponentiallyStable f x) : LocallyExponentiallyStable g x := by
  obtain ⟨r, C, a, hr, hC, ha, hb⟩ := h
  refine ⟨r, C + 1, min a 1, hr, by linarith, lt_min ha one_pos, fun t₀ t₁ ψ hψ h0 t ht => ?_⟩
  obtain ⟨hχ, hk⟩ := isTrajectoryOn_proj k hplane hg hψ
  obtain ⟨h1, -, h3⟩ := norm_sub_le_proj k hxk (ψ t₀)
  obtain ⟨-, h5, -⟩ := norm_sub_le_proj k hxk (ψ t)
  have h6 := hb t₀ t₁ _ hχ (lt_of_le_of_lt h1 h0) t ht
  simp only at h6
  have hτ : 0 ≤ t - t₀ := by linarith [ht.1]
  have he1 : Real.exp (-a * (t - t₀)) ≤ Real.exp (-min a 1 * (t - t₀)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left a 1])
  have he2 : Real.exp (-(t - t₀)) ≤ Real.exp (-min a 1 * (t - t₀)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right a 1])
  have h7 : |ψ t k| ≤ Real.exp (-min a 1 * (t - t₀)) * ‖ψ t₀ - x‖ := by
    rw [hk t ht, abs_mul, Real.abs_exp, mul_comm]
    exact mul_le_mul he2 h3 (abs_nonneg _) (Real.exp_pos _).le
  have h8 : C * Real.exp (-a * (t - t₀)) * ‖(ψ t₀ - ψ t₀ k • EuclideanSpace.single k (1 : ℝ)) - x‖
      ≤ C * Real.exp (-min a 1 * (t - t₀)) * ‖ψ t₀ - x‖ := by
    have hC0 : 0 ≤ C := by linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left he1 hC0) h1 (norm_nonneg _)
      (mul_nonneg hC0 (Real.exp_pos _).le)
  nlinarith

/-- **Local asymptotic stability passes to the plane field** (as
`lyapunovStable_of_invariantPlane`): the projection of a forward-complete solution of `g` is one
of `f`, which converges to `x`, and the `k`-th coordinate decays as `e^{−t}`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_invariantPlane
    {f g : State n → State n} {x : State n} (k : Fin n) (hxk : x k = 0)
    (hplane : ∀ y : State n, y k = 0 → f y k = 0)
    (hg : ∀ y : State n, g y = f (y - y k • EuclideanSpace.single k (1 : ℝ)) -
      y k • EuclideanSpace.single k (1 : ℝ))
    (h : LocalAsymptoticStable f x) : LocalAsymptoticStable g x := by
  obtain ⟨hs, c, hc, hconv⟩ := h
  refine ⟨lyapunovStable_of_invariantPlane k hxk hplane hg hs, c, hc, fun t₀ ψ hψ h0 => ?_⟩
  obtain ⟨h1, -, -⟩ := norm_sub_le_proj k hxk (ψ t₀)
  have hlim := hconv t₀ _ (isIntegralCurveOn_proj k hplane hg hψ) (lt_of_le_of_lt h1 h0)
  have hk : ∀ t, t₀ ≤ t → ψ t k = ψ t₀ k * Real.exp (-(t - t₀)) := fun t ht =>
    (isTrajectoryOn_proj k hplane hg (hψ.mono Icc_subset_Ici_self)).2 t ⟨ht, le_rfl⟩
  have hexp : Tendsto (fun t => ψ t₀ k * Real.exp (-(t - t₀))) atTop (𝓝 0) := by
    have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_atTop_add_const_right _ (-t₀) tendsto_id)).const_mul (ψ t₀ k)
    rw [mul_zero] at h3
    exact h3
  have h2 := hlim.add (hexp.smul_const (EuclideanSpace.single k (1 : ℝ)))
  rw [zero_smul, add_zero] at h2
  refine h2.congr' (eventually_atTop.mpr ⟨t₀, fun t ht => ?_⟩)
  simp only
  rw [← hk t ht, sub_add_cancel]

/-! ## From the plane field to `f`, under the collapse -/

/-- Along a segment of `f` near `x`, where off the plane `2 y_k f_k ≤ −a`, the square `y_k²` does
not increase. -/
@[tmio T, powerlib_foundation] private theorem antitoneOn_sq {f : State n → State n}
    {x : State n} (k : Fin n) {ρ a : ℝ} (ha : 0 < a)
    (hcol : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → 2 * y k * f y k ≤ -a)
    {φ : ℝ → State n} {t₀ s : ℝ} (hφ : IsTrajectoryOn φ f t₀ s)
    (hin : ∀ u ∈ Icc t₀ s, ‖φ u - x‖ < ρ) :
    AntitoneOn (fun t => φ t k ^ 2) (Icc t₀ s) := by
  have hdk : ∀ t ∈ Icc t₀ s, HasDerivWithinAt (fun t => (φ t k : ℝ)) (f (φ t) k : ℝ)
      (Icc t₀ s) t :=
    fun t ht => (EuclideanSpace.proj k : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (hφ t ht)
  have hdu : ∀ t ∈ Icc t₀ s, HasDerivWithinAt (fun t => φ t k ^ 2)
      (2 * φ t k * f (φ t) k) (Icc t₀ s) t := fun t ht => by
    have := (hdk t ht).fun_pow 2
    convert this using 1
    push_cast
    ring
  have hint : interior (Icc t₀ s) = Ioo t₀ s := interior_Icc
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => 2 * φ t k * f (φ t) k)
    (convex_Icc _ _) (fun t ht => (hdu t ht).continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
  · rw [hint] at ht ⊢
    exact ((hdu t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt
  · rw [hint] at ht
    by_cases h : φ t k = 0
    · simp [h]
    · linarith [hcol _ (hin t (Ioo_subset_Icc_self ht)) h]

/-- On a segment along which `y_k²` does not increase, every time `t` has a first time `τ ≤ t`
on the plane, after which (up to `t`) the segment stays on it, unless the segment is off the plane
up to `t` (then `τ = t`). -/
@[tmio T, powerlib_foundation] private theorem exists_first_zero {φ : ℝ → State n} (k : Fin n)
    {t₀ s : ℝ} (hc : ContinuousOn φ (Icc t₀ s)) (hanti : AntitoneOn (fun t => φ t k ^ 2) (Icc t₀ s))
    {t : ℝ} (ht : t ∈ Icc t₀ s) :
    ∃ τ ∈ Icc t₀ t, (∀ v ∈ Ico t₀ τ, φ v k ≠ 0) ∧ (τ = t ∨ ∀ v ∈ Icc τ t, φ v k = 0) := by
  by_cases h : φ t k = 0
  · set Z := Icc t₀ t ∩ (fun v => φ v k) ⁻¹' {0} with hZ
    have hck : ContinuousOn (fun v => φ v k) (Icc t₀ t) :=
      ((EuclideanSpace.proj k : State n →L[ℝ] ℝ).continuous.comp_continuousOn hc).mono
        (Icc_subset_Icc le_rfl ht.2)
    have hZc : IsClosed Z := hck.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hZb : BddBelow Z := ⟨t₀, fun v hv => hv.1.1⟩
    have hτZ := hZc.csInf_mem ⟨t, ⟨ht.1, le_rfl⟩, h⟩ hZb
    refine ⟨sInf Z, hτZ.1, fun v hv hv0 => ?_, Or.inr fun v hv => ?_⟩
    · have : sInf Z ≤ v := csInf_le hZb ⟨⟨hv.1, hv.2.le.trans hτZ.1.2⟩, hv0⟩
      exact absurd hv.2 (not_lt.mpr this)
    · have h1 := hanti ⟨hτZ.1.1, hτZ.1.2.trans ht.2⟩ ⟨hτZ.1.1.trans hv.1, hv.2.trans ht.2⟩ hv.1
      have h0 : φ (sInf Z) k = 0 := hτZ.2
      simp only [h0] at h1
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm (by simpa using h1)
        (sq_nonneg _))
  · refine ⟨t, ⟨ht.1, le_rfl⟩, fun v hv hv0 => h ?_, Or.inl rfl⟩
    have h1 := hanti ⟨hv.1, hv.2.le.trans ht.2⟩ ht hv.2.le
    simp only [hv0] at h1
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm (by simpa using h1)
      (sq_nonneg _))

/-- The collapse estimate up to the first time on the plane: under the collapse conditions there
are `r, C, c` such that a segment of `f` starting within `r` of `x` and off the plane before `τ`
satisfies `‖y(τ) − x‖ ≤ C e^{−c (τ − t₀)} ‖y(t₀) − x‖`
(`locallyExponentiallyStable_of_collapse` for `f` changed on the plane, where it is not used, and
continuity at `τ`). -/
@[tmio T, powerlib_foundation] private theorem exists_collapse_bound {f : State n → State n}
    {x : State n} (k : Fin n) (hxk : x k = 0) {ρ a M : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    (hcol : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → 2 * y k * f y k ≤ -a)
    (hbound : ∀ y : State n, ‖y - x‖ < ρ →
      ‖f y - f y k • EuclideanSpace.single k (1 : ℝ)‖ ≤ M) :
    ∃ r C c : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < c ∧ ∀ (t₀ t₁ τ : ℝ) (φ : ℝ → State n),
      IsTrajectoryOn φ f t₀ t₁ → ‖φ t₀ - x‖ < r → τ ∈ Icc t₀ t₁ →
        (∀ v ∈ Ico t₀ τ, φ v k ≠ 0) →
          ‖φ τ - x‖ ≤ C * Real.exp (-c * (τ - t₀)) * ‖φ t₀ - x‖ := by
  set e := EuclideanSpace.single k (1 : ℝ) with he
  have hek : e k = 1 := by simp [he]
  set f₁ : State n → State n := fun y => if y k = 0 then f y + (1 - f y k) • e else f y with hf₁
  have hoff : ∀ y : State n, y k ≠ 0 → f₁ y = f y := fun y hy => by simp [hf₁, hy]
  have hcol₁ : LocallyExponentiallyStable f₁ x := by
    refine locallyExponentiallyStable_of_collapse (M := M) k hxk hρ ha (fun y hy hyk => ?_)
      (fun y _ hyk => ?_) (fun y hy => ?_)
    · rw [hoff y hyk]
      exact hcol y hy hyk
    · simp [hf₁, hyk, hek]
    · by_cases hyk : y k = 0
      · have h1 : f₁ y - f₁ y k • e = f y - f y k • e := by
          simp only [hf₁, hyk, ↓reduceIte, PiLp.add_apply, PiLp.smul_apply, hek, smul_eq_mul,
            mul_one]
          module
        rw [h1]
        exact hbound y hy
      · rw [hoff y hyk]
        exact hbound y hy
  obtain ⟨r, C, c, hr, hC, hc, hb⟩ := hcol₁
  refine ⟨r, C, c, hr, hC, hc, fun t₀ t₁ τ φ hφ h0 hτ hne => ?_⟩
  rcases eq_or_lt_of_le hτ.1 with heq | hlt
  · subst heq
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    exact le_mul_of_one_le_left (norm_nonneg _) hC
  · have hcl : τ ∈ closure (Ico t₀ τ) := by
      rw [closure_Ico hlt.ne]
      exact right_mem_Icc.mpr hlt.le
    have hcφ : ContinuousWithinAt φ (Ico t₀ τ) τ :=
      (hφ.continuousOn τ hτ).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hτ.2))
    refine ContinuousWithinAt.closure_le (g := fun v => C * Real.exp (-c * (v - t₀)) * ‖φ t₀ - x‖)
      hcl (hcφ.sub continuousWithinAt_const).norm (by fun_prop) fun v hv => ?_
    have hseg : IsTrajectoryOn φ f₁ t₀ v := fun w hw => by
      have hwτ : w < τ := lt_of_le_of_lt hw.2 hv.2
      show HasDerivWithinAt φ (f₁ (φ w)) (Icc t₀ v) w
      rw [show f₁ (φ w) = f (φ w) from hoff _ (hne w ⟨hw.1, hwτ⟩)]
      exact (hφ w ⟨hw.1, hwτ.le.trans hτ.2⟩).mono (Icc_subset_Icc le_rfl (hv.2.le.trans hτ.2))
    exact hb t₀ v φ hseg h0 v ⟨hv.1, le_rfl⟩

/-- **Local exponential stability from the plane field, under the collapse.** Let `x` lie on the
plane `y_k = 0`, let the field collapse onto the plane near `x` (`2 y_k f_k(y) ≤ −a` off it, the
components off `k` bounded) and let `g` equal `f` on the plane near `x`. If `x` is locally
exponentially stable for `g`, it is for `f`: a segment of `f` obeys the collapse estimate until it
first reaches the plane, and the estimate of `g` from then on. -/
@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_of_invariantPlane_collapse
    {f g : State n → State n} {x : State n} (k : Fin n) (hxk : x k = 0) {ρ a M : ℝ}
    (hρ : 0 < ρ) (ha : 0 < a)
    (hcol : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → 2 * y k * f y k ≤ -a)
    (hbound : ∀ y : State n, ‖y - x‖ < ρ →
      ‖f y - f y k • EuclideanSpace.single k (1 : ℝ)‖ ≤ M)
    (hg : ∀ y : State n, ‖y - x‖ < ρ → y k = 0 → g y = f y)
    (h : LocallyExponentiallyStable g x) : LocallyExponentiallyStable f x := by
  obtain ⟨r₁, C₁, a₁, hr₁, hC₁, ha₁, hb₁⟩ := exists_collapse_bound k hxk hρ ha hcol hbound
  obtain ⟨r₂, C₂, a₂, hr₂, hC₂, ha₂, hb₂⟩ := h
  have hC : 1 ≤ C₁ * C₂ := one_le_mul_of_one_le_of_one_le hC₁ hC₂
  have hC0 : 0 < C₁ * C₂ := by linarith
  set b := min a₁ a₂ with hb
  refine ⟨min r₁ (min (r₂ / C₁) (ρ / (2 * (C₁ * C₂)))), C₁ * C₂, b,
    lt_min hr₁ (lt_min (by positivity) (by positivity)), hC, lt_min ha₁ ha₂, ?_⟩
  intro t₀ t₁ φ hφ h0
  set δ := ‖φ t₀ - x‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδ1 : δ < r₁ := lt_of_lt_of_le h0 (min_le_left _ _)
  have hδ2 : C₁ * δ < r₂ := by
    have := lt_of_lt_of_le h0 ((min_le_right _ _).trans (min_le_left _ _))
    rw [lt_div_iff₀ (by linarith)] at this
    linarith
  have hδ3 : C₁ * C₂ * δ < ρ / 2 := by
    have := lt_of_lt_of_le h0 ((min_le_right _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have est : ∀ s ∈ Icc t₀ t₁, (∀ u ∈ Icc t₀ s, ‖φ u - x‖ < ρ) →
      ∀ t ∈ Icc t₀ s, ‖φ t - x‖ ≤ C₁ * C₂ * Real.exp (-b * (t - t₀)) * δ := by
    intro s hs hin t ht
    have hseg : IsTrajectoryOn φ f t₀ s := hφ.mono (Icc_subset_Icc le_rfl hs.2)
    obtain ⟨τ, hτ, hne, hon⟩ := exists_first_zero k hseg.continuousOn
      (antitoneOn_sq k ha hcol hseg hin) ht
    have hτs : τ ∈ Icc t₀ s := ⟨hτ.1, hτ.2.trans ht.2⟩
    have hτb := hb₁ t₀ s τ φ hseg hδ1 hτs hne
    have hτ0 : 0 ≤ τ - t₀ := by linarith [hτ.1]
    have he1 : Real.exp (-a₁ * (τ - t₀)) ≤ Real.exp (-b * (τ - t₀)) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_left a₁ a₂])
    have he1' : Real.exp (-a₁ * (τ - t₀)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    rcases hon with rfl | hon
    · calc ‖φ τ - x‖ ≤ C₁ * Real.exp (-a₁ * (τ - t₀)) * δ := hτb
        _ ≤ C₁ * C₂ * Real.exp (-b * (τ - t₀)) * δ := by
          have h1 : C₁ ≤ C₁ * C₂ := le_mul_of_one_le_right (by linarith) hC₂
          have h2 := mul_le_mul h1 he1 (Real.exp_pos _).le hC0.le
          exact mul_le_mul_of_nonneg_right h2 hδ0
    · have hgseg : IsTrajectoryOn φ g τ t := fun v hv => by
        have hv' : v ∈ Icc t₀ s := ⟨hτ.1.trans hv.1, hv.2.trans ht.2⟩
        show HasDerivWithinAt φ (g (φ v)) (Icc τ t) v
        rw [hg (φ v) (hin v hv') (hon v hv)]
        exact (hseg v hv').mono (Icc_subset_Icc hτ.1 ht.2)
      have hτr : ‖φ τ - x‖ < r₂ := by
        refine lt_of_le_of_lt (hτb.trans ?_) hδ2
        have := mul_le_mul_of_nonneg_left he1' (by linarith : (0 : ℝ) ≤ C₁)
        nlinarith
      have h2 := hb₂ τ t φ hgseg hτr t ⟨hτ.2, le_rfl⟩
      have htτ : 0 ≤ t - τ := by linarith [hτ.2]
      have he2 : Real.exp (-a₂ * (t - τ)) ≤ Real.exp (-b * (t - τ)) :=
        Real.exp_le_exp.mpr (by nlinarith [min_le_right a₁ a₂])
      have hsplit : Real.exp (-b * (t - τ)) * Real.exp (-b * (τ - t₀)) =
          Real.exp (-b * (t - t₀)) := by
        rw [← Real.exp_add]
        ring_nf
      calc ‖φ t - x‖ ≤ C₂ * Real.exp (-a₂ * (t - τ)) * ‖φ τ - x‖ := h2
        _ ≤ C₂ * Real.exp (-b * (t - τ)) * (C₁ * Real.exp (-b * (τ - t₀)) * δ) := by
          have h3 : ‖φ τ - x‖ ≤ C₁ * Real.exp (-b * (τ - t₀)) * δ :=
            hτb.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left he1 (by linarith)) hδ0)
          exact mul_le_mul (mul_le_mul_of_nonneg_left he2 (by linarith)) h3 (norm_nonneg _)
            (mul_nonneg (by linarith) (Real.exp_pos _).le)
        _ = C₁ * C₂ * Real.exp (-b * (t - t₀)) * δ := by
          rw [← hsplit]
          ring
  have hbnd : ∀ t, 0 ≤ t - t₀ → C₁ * C₂ * Real.exp (-b * (t - t₀)) * δ ≤ C₁ * C₂ * δ :=
    fun t ht => by
      have : Real.exp (-b * (t - t₀)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [lt_min ha₁ ha₂])
      have := mul_le_mul_of_nonneg_left this hC0.le
      nlinarith
  have hstay : ∀ u ∈ Icc t₀ t₁, ‖φ u - x‖ < ρ / 2 := by
    refine Dynamics.forall_lt_of_first_exit (Φ := fun y => ‖y - x‖)
      (continuous_id.sub continuous_const).norm hφ.continuousOn (by nlinarith) fun s hs hle => ?_
    have h1 := est s hs (fun u hu => lt_of_le_of_lt (hle u hu) (half_lt_self hρ)) s
      ⟨hs.1, le_rfl⟩
    linarith [hbnd s (by linarith [hs.1])]
  intro t ht
  exact est t₁ ⟨ht.1.trans ht.2, le_rfl⟩
    (fun u hu => (hstay u hu).trans (half_lt_self hρ)) t ht

/-- **Lyapunov stability from the plane field, under the collapse** (the hypotheses of
`locallyExponentiallyStable_of_invariantPlane_collapse`): a segment of `f` stays within `C₁ δ` of
`x` until it first reaches the plane (collapse estimate), and then within the stability bound of
`g`. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_of_invariantPlane_collapse
    {f g : State n → State n} {x : State n} (k : Fin n) (hxk : x k = 0) {ρ a M : ℝ}
    (hρ : 0 < ρ) (ha : 0 < a)
    (hcol : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → 2 * y k * f y k ≤ -a)
    (hbound : ∀ y : State n, ‖y - x‖ < ρ →
      ‖f y - f y k • EuclideanSpace.single k (1 : ℝ)‖ ≤ M)
    (hg : ∀ y : State n, ‖y - x‖ < ρ → y k = 0 → g y = f y)
    (h : LyapunovStable g x) : LyapunovStable f x := by
  obtain ⟨r₁, C₁, a₁, hr₁, hC₁, ha₁, hb₁⟩ := exists_collapse_bound k hxk hρ ha hcol hbound
  intro ε hε
  set ε' := min ε (ρ / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (half_pos hρ)
  obtain ⟨δ₂, hδ₂, hb₂⟩ := h ε' hε'0
  have hC0 : 0 < C₁ := by linarith
  refine ⟨min r₁ (min (δ₂ / C₁) (ε' / C₁)), lt_min hr₁ (lt_min (by positivity) (by positivity)),
    fun t₀ t₁ φ hφ h0 => ?_⟩
  set δ := ‖φ t₀ - x‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδ1 : δ < r₁ := lt_of_lt_of_le h0 (min_le_left _ _)
  have hδ2 : C₁ * δ < δ₂ := by
    have := lt_of_lt_of_le h0 ((min_le_right _ _).trans (min_le_left _ _))
    rw [lt_div_iff₀ hC0] at this
    linarith
  have hδ3 : C₁ * δ < ε' := by
    have := lt_of_lt_of_le h0 ((min_le_right _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ hC0] at this
    linarith
  have est : ∀ s ∈ Icc t₀ t₁, (∀ u ∈ Icc t₀ s, ‖φ u - x‖ < ρ) →
      ∀ t ∈ Icc t₀ s, ‖φ t - x‖ < ε' := by
    intro s hs hin t ht
    have hseg : IsTrajectoryOn φ f t₀ s := hφ.mono (Icc_subset_Icc le_rfl hs.2)
    obtain ⟨τ, hτ, hne, hon⟩ := exists_first_zero k hseg.continuousOn
      (antitoneOn_sq k ha hcol hseg hin) ht
    have hτs : τ ∈ Icc t₀ s := ⟨hτ.1, hτ.2.trans ht.2⟩
    have hτb : ‖φ τ - x‖ ≤ C₁ * δ := by
      refine (hb₁ t₀ s τ φ hseg hδ1 hτs hne).trans ?_
      have : Real.exp (-a₁ * (τ - t₀)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [hτ.1])
      have := mul_le_mul_of_nonneg_left this hC0.le
      nlinarith
    rcases hon with rfl | hon
    · exact lt_of_le_of_lt hτb hδ3
    · have hgseg : IsTrajectoryOn φ g τ t := fun v hv => by
        have hv' : v ∈ Icc t₀ s := ⟨hτ.1.trans hv.1, hv.2.trans ht.2⟩
        show HasDerivWithinAt φ (g (φ v)) (Icc τ t) v
        rw [hg (φ v) (hin v hv') (hon v hv)]
        exact (hseg v hv').mono (Icc_subset_Icc hτ.1 ht.2)
      exact hb₂ τ t φ hgseg (lt_of_le_of_lt hτb hδ2) t ⟨hτ.2, le_rfl⟩
  have hstay : ∀ u ∈ Icc t₀ t₁, ‖φ u - x‖ < ρ / 2 := by
    refine Dynamics.forall_lt_of_first_exit (Φ := fun y => ‖y - x‖)
      (continuous_id.sub continuous_const).norm hφ.continuousOn ?_ fun s hs hle => ?_
    · have : δ ≤ C₁ * δ := le_mul_of_one_le_left hδ0 hC₁
      exact lt_of_le_of_lt this (lt_of_lt_of_le hδ3 (min_le_right _ _))
    · exact lt_of_lt_of_le (est s hs (fun u hu => lt_of_le_of_lt (hle u hu) (half_lt_self hρ))
        s ⟨hs.1, le_rfl⟩) (min_le_right _ _)
  intro t ht
  exact lt_of_lt_of_le (est t₁ ⟨ht.1.trans ht.2, le_rfl⟩
    (fun u hu => (hstay u hu).trans (half_lt_self hρ)) t ht) (min_le_left _ _)

/-! ## The reduction -/

/-- **Under the collapse onto an invariant plane, local exponential stability is that of the flow
on the plane.** With `f_k = 0` on the plane, `2 y_k f_k(y) ≤ −a` off it near `x`, the components
off `k` bounded near `x`, and `g(y) = f(y − y_k e_k) − y_k e_k`:
`x` is locally exponentially stable for `f` iff it is for `g`. -/
@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_iff_of_invariantPlane
    {f g : State n → State n} {x : State n} (k : Fin n) (hxk : x k = 0) {ρ a M : ℝ}
    (hρ : 0 < ρ) (ha : 0 < a)
    (hcol : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → 2 * y k * f y k ≤ -a)
    (hbound : ∀ y : State n, ‖y - x‖ < ρ →
      ‖f y - f y k • EuclideanSpace.single k (1 : ℝ)‖ ≤ M)
    (hplane : ∀ y : State n, y k = 0 → f y k = 0)
    (hg : ∀ y : State n, g y = f (y - y k • EuclideanSpace.single k (1 : ℝ)) -
      y k • EuclideanSpace.single k (1 : ℝ)) :
    LocallyExponentiallyStable f x ↔ LocallyExponentiallyStable g x :=
  ⟨locallyExponentiallyStable_of_invariantPlane k hxk hplane hg,
    locallyExponentiallyStable_of_invariantPlane_collapse k hxk hρ ha hcol hbound
      fun y _ hy => by rw [hg, hy, zero_smul, sub_zero, sub_zero]⟩

/-- **Under the collapse onto an invariant plane, Lyapunov stability is that of the flow on the
plane** (the hypotheses of `locallyExponentiallyStable_iff_of_invariantPlane`). -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_iff_of_invariantPlane
    {f g : State n → State n} {x : State n} (k : Fin n) (hxk : x k = 0) {ρ a M : ℝ}
    (hρ : 0 < ρ) (ha : 0 < a)
    (hcol : ∀ y : State n, ‖y - x‖ < ρ → y k ≠ 0 → 2 * y k * f y k ≤ -a)
    (hbound : ∀ y : State n, ‖y - x‖ < ρ →
      ‖f y - f y k • EuclideanSpace.single k (1 : ℝ)‖ ≤ M)
    (hplane : ∀ y : State n, y k = 0 → f y k = 0)
    (hg : ∀ y : State n, g y = f (y - y k • EuclideanSpace.single k (1 : ℝ)) -
      y k • EuclideanSpace.single k (1 : ℝ)) :
    LyapunovStable f x ↔ LyapunovStable g x :=
  ⟨lyapunovStable_of_invariantPlane k hxk hplane hg,
    lyapunovStable_of_invariantPlane_collapse k hxk hρ ha hcol hbound
      fun y _ hy => by rw [hg, hy, zero_smul, sub_zero, sub_zero]⟩

/-! ## An invariant plane with a first integral off it -/

/-- Along a segment of `f`, on an interval `[a, b]` whose interior stays off the plane, the
quantity `y_k²/2 − G(y)` is conserved when `y_k f_k = Ġ` off the plane (mean value theorem). -/
@[tmio T, powerlib_foundation] private theorem firstIntegral_eq {f : State n → State n}
    (k : Fin n) {G : State n → ℝ} (hG : Differentiable ℝ G)
    (hlie : ∀ y : State n, y k ≠ 0 → y k * f y k = fderiv ℝ G y (f y))
    {φ : ℝ → State n} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ f t₀ t₁) {a b : ℝ} (ha : t₀ ≤ a)
    (hab : a ≤ b) (hb : b ≤ t₁) (hne : ∀ s ∈ Ioo a b, φ s k ≠ 0) :
    φ b k ^ 2 / 2 - G (φ b) = φ a k ^ 2 / 2 - G (φ a) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rfl
  have hc : ContinuousOn φ (Icc a b) := hφ.continuousOn.mono (Icc_subset_Icc ha hb)
  have hFc : ContinuousOn (fun s => φ s k ^ 2 / 2 - G (φ s)) (Icc a b) :=
    ((((EuclideanSpace.proj k : State n →L[ℝ] ℝ).continuous.comp_continuousOn hc).pow 2).div_const
      2).sub (hG.continuous.comp_continuousOn hc)
  obtain ⟨c, hcI, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => φ s k ^ 2 / 2 - G (φ s))
    (fun _ => (0 : ℝ)) hlt hFc fun c hcI => by
      have hct : c ∈ Ioo t₀ t₁ := ⟨lt_of_le_of_lt ha hcI.1, lt_of_lt_of_le hcI.2 hb⟩
      have hd : HasDerivAt φ (f (φ c)) c :=
        (hφ c (Ioo_subset_Icc_self hct)).hasDerivAt (Icc_mem_nhds hct.1 hct.2)
      have hk := (coord k).hasFDerivAt.comp_hasDerivAt c hd
      have hGd := (hG (φ c)).hasFDerivAt.comp_hasDerivAt c hd
      refine (((hk.pow 2).div_const 2).sub hGd).congr_deriv ?_
      simp only [Function.comp_apply, coord_apply]
      rw [← hlie _ (hne c hcI), show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hlt.ne'
  rw [eq_div_iff hba, zero_mul] at hslope
  linarith

/-- Along a segment of `f`, `y_k²` at a time `t` exceeds its initial value by at most twice the
increase of `G` since some earlier time `a` (the last visit to the plane, or `t₀`). -/
@[tmio T, powerlib_foundation] private theorem sq_le_of_firstIntegral {f : State n → State n}
    (k : Fin n) {G : State n → ℝ} (hG : Differentiable ℝ G)
    (hlie : ∀ y : State n, y k ≠ 0 → y k * f y k = fderiv ℝ G y (f y))
    {φ : ℝ → State n} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ f t₀ t₁) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) :
    ∃ a ∈ Icc t₀ t, φ t k ^ 2 ≤ φ t₀ k ^ 2 + 2 * (G (φ t) - G (φ a)) := by
  by_cases htk : φ t k = 0
  · exact ⟨t, ⟨ht.1, le_rfl⟩, by rw [htk, sub_self]; nlinarith [sq_nonneg (φ t₀ k)]⟩
  have hcont : ContinuousOn (fun s => φ s k) (Icc t₀ t) :=
    (EuclideanSpace.proj k : State n →L[ℝ] ℝ).continuous.comp_continuousOn
      (hφ.continuousOn.mono (Icc_subset_Icc le_rfl ht.2))
  set Z := Icc t₀ t ∩ (fun s => φ s k) ⁻¹' {0} with hZ
  by_cases hZn : Z.Nonempty
  · have hZc : IsClosed Z := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hZb : BddAbove Z := ⟨t, fun s hs => hs.1.2⟩
    have haZ : sSup Z ∈ Z := hZc.csSup_mem hZn hZb
    have ha0 : φ (sSup Z) k = 0 := haZ.2
    have hne : ∀ s ∈ Ioo (sSup Z) t, φ s k ≠ 0 := fun s hs h0 =>
      (not_le.mpr hs.1) (le_csSup hZb ⟨⟨haZ.1.1.trans hs.1.le, hs.2.le⟩, h0⟩)
    have h := firstIntegral_eq k hG hlie hφ haZ.1.1 haZ.1.2 ht.2 hne
    rw [ha0] at h
    refine ⟨sSup Z, haZ.1, ?_⟩
    nlinarith [sq_nonneg (φ t₀ k)]
  · have hne : ∀ s ∈ Ioo t₀ t, φ s k ≠ 0 := fun s hs h0 =>
      hZn ⟨s, ⟨hs.1.le, hs.2.le⟩, h0⟩
    have h := firstIntegral_eq k hG hlie hφ le_rfl ht.1 ht.2 hne
    exact ⟨t₀, ⟨le_rfl, ht.1⟩, by linarith⟩

/-- **Lyapunov stability with a first integral off an invariant plane.** Suppose the components
of `f` off `k` do not depend on `y_k`, `f(y − y_k e_k) = f(y) − f_k(y) e_k` (so the plane
`y_k = 0` is invariant), and off the plane `y_k f_k(y) = Ġ(y)` for a differentiable `G` that does
not depend on `y_k` (`y_k²/2 − G` is conserved off the plane). Then a point `x` of the plane is
Lyapunov stable for `f` iff it is for the plane field `g(y) = f(y − y_k e_k) − y_k e_k`: the
projection of a segment of `f` is a segment of `g`, and since its last visit to the plane (or
from `t₀`) `y_k²` has grown by at most twice the oscillation of `G` along that projection. No
collapse onto the plane and no regularity of `f` are needed. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_iff_of_invariantPlane_firstIntegral
    {f g : State n → State n} {x : State n} (k : Fin n) (hxk : x k = 0)
    (hoff : ∀ y : State n, f (y - y k • EuclideanSpace.single k (1 : ℝ)) =
      f y - f y k • EuclideanSpace.single k (1 : ℝ))
    {G : State n → ℝ} (hG : Differentiable ℝ G)
    (hGP : ∀ y : State n, G (y - y k • EuclideanSpace.single k (1 : ℝ)) = G y)
    (hlie : ∀ y : State n, y k ≠ 0 → y k * f y k = fderiv ℝ G y (f y))
    (hg : ∀ y : State n, g y = f (y - y k • EuclideanSpace.single k (1 : ℝ)) -
      y k • EuclideanSpace.single k (1 : ℝ)) :
    LyapunovStable f x ↔ LyapunovStable g x := by
  set e := EuclideanSpace.single k (1 : ℝ) with he
  have hek : e k = 1 := by simp [he]
  have hPk : ∀ v : State n, (v - v k • e) k = 0 := fun v => by simp [hek]
  have hplane : ∀ y : State n, y k = 0 → f y k = 0 := fun y hy => by
    have h := congrArg (fun v : State n => v k) (hoff y)
    simp only [hy, zero_smul, sub_zero, PiLp.sub_apply, PiLp.smul_apply, hek, smul_eq_mul,
      mul_one, sub_self] at h
    exact h
  refine ⟨lyapunovStable_of_invariantPlane k hxk hplane hg, fun h ε hε => ?_⟩
  set P : State n →L[ℝ] State n := ContinuousLinearMap.id ℝ (State n) -
    (EuclideanSpace.proj k : State n →L[ℝ] ℝ).smulRight e with hPdef
  have hP : ∀ v, P v = v - v k • e := fun v => by simp [hPdef]
  obtain ⟨rG, hrG, hGc⟩ := Metric.continuous_iff.mp hG.continuous x (ε ^ 2 / 16) (by positivity)
  obtain ⟨δ, hδ, hb⟩ := h (min (ε / 4) rG) (lt_min (by positivity) hrG)
  refine ⟨min δ (ε / 4), lt_min hδ (by positivity), fun t₀ t₁ φ hφ h0 t ht => ?_⟩
  have hχ : IsTrajectoryOn (fun s => φ s - φ s k • e) g t₀ t₁ := fun s hs => by
    have hd := P.hasFDerivAt.comp_hasDerivWithinAt s (hφ s hs)
    show HasDerivWithinAt _ (g (φ s - φ s k • e)) _ s
    rw [hg, hPk, zero_smul, sub_zero, sub_zero, hoff, ← hP]
    exact hd
  obtain ⟨h1, -, h3⟩ := norm_sub_le_proj k hxk (φ t₀)
  have hstay : ∀ s ∈ Icc t₀ t₁, ‖(φ s - φ s k • e) - x‖ < min (ε / 4) rG := fun s hs =>
    hb t₀ t₁ _ hχ (lt_of_le_of_lt h1 (lt_of_lt_of_le h0 (min_le_left _ _))) s hs
  have hGs : ∀ s ∈ Icc t₀ t₁, |G (φ s) - G x| < ε ^ 2 / 16 := fun s hs => by
    rw [← hGP]
    have h2 := hGc _ (by rw [dist_eq_norm]; exact lt_of_lt_of_le (hstay s hs) (min_le_right _ _))
    rwa [Real.dist_eq] at h2
  obtain ⟨a, ha, hsq⟩ := sq_le_of_firstIntegral k hG hlie hφ ht
  have hGt := abs_lt.mp (hGs t ht)
  have hGa := abs_lt.mp (hGs a ⟨ha.1, ha.2.trans ht.2⟩)
  have h0k : |φ t₀ k| < ε / 4 := lt_of_le_of_lt h3 (lt_of_lt_of_le h0 (min_le_right _ _))
  have h0k2 : φ t₀ k ^ 2 < (ε / 4) ^ 2 := by
    rw [← sq_abs]
    exact pow_lt_pow_left₀ h0k (abs_nonneg _) two_ne_zero
  have hkt : |φ t k| < 3 * ε / 4 := abs_lt_of_sq_lt_sq (by nlinarith) (by positivity)
  obtain ⟨-, h5, -⟩ := norm_sub_le_proj k hxk (φ t)
  have h6 := lt_of_lt_of_le (hstay t ht) (min_le_left _ _)
  linarith

end powerlib.Dynamics.Degenerate
