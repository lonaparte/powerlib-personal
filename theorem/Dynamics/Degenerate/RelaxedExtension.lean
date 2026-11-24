import theorem.Dynamics.Coordinates

/-! # A field extended by complement coordinates that relax at unit rate

A field `h` on `ℝᵐ`, carried into `ℝⁿ` by a linear isometry `ι` with a left inverse `π` that
does not increase norms, and extended off the image of `ι` by letting the complement relax at
unit rate: `g(y) = ι h(π y) − (y − ι π y)`. A solution of `g` is a solution of `h` carried by `ι`
plus a complement `y − ι π y` that decays as `e^{−t}`; so Lyapunov stability, local exponential
stability and local asymptotic stability of the point `ι u` for `g` are those of `u` for `h`.
Written for the flow on the invariant singular plane of the open-loop VSM–DC model
(`theorem/GridTiedConverter/GFM/DCLink/OpenLoop.lean`, `Plant.planeField`): the swing of
`theorem/PowerSystem/Synchronous/Swing.lean` with the DC voltage relaxed.

Scope.
* Generic foundation, independent of any model: it imports no engineering module and defines no
  family. Arbitrary autonomous fields `h : ℝᵐ → ℝᵐ`, `g : ℝⁿ → ℝⁿ` (continuous time, no input)
  and continuous linear maps `ι : ℝᵐ → ℝⁿ`, `π : ℝⁿ → ℝᵐ` with `π ∘ ι = id`, `‖ι u‖ = ‖u‖`,
  `‖π y‖ ≤ ‖y‖` and `‖y − ι π y‖ ≤ ‖y‖` (an orthogonal splitting of coordinates), read through
  LeanForControl's notions (solution segments on `[t₀, t₁]` for Lyapunov and local exponential
  stability, forward-complete solutions for attraction). No regularity of `h` is assumed.
* The splitting of `ℝ³` into the plane of its first two coordinates and the third axis
  (`incl23`, `proj32`).

Source: Khalil, *Nonlinear Systems* (3rd ed.), Definitions 4.1 (stability, asymptotic stability)
and 4.5 (exponential stability); the reduction is elementary (the complement solves `ċ = −c`).

Results.
* `lyapunovStable_relaxed_iff`, `locallyExponentiallyStable_relaxed_iff`,
  `localAsymptoticStable_relaxed_iff`: `ι u` is Lyapunov stable, locally exponentially stable,
  or locally asymptotically stable for `g` iff `u` is for `h`.
* `incl23` (`(a, b) ↦ (a, b, 0)`) and `proj32` (`(a, b, c) ↦ (a, b)`), with `incl23_apply`,
  `proj32_apply_zero`, `proj32_apply_one`, and the hypotheses of the three laws for them:
  `proj32_incl23`, `norm_incl23`, `norm_proj32_le`, `norm_sub_incl23_proj32_le`.
-/

noncomputable section
namespace powerlib.Dynamics.Degenerate
open Set Filter Topology

variable {m n : ℕ} {ι : State m →L[ℝ] State n} {π : State n →L[ℝ] State m}
  {h : State m → State m} {g : State n → State n}

/-! ## Solutions of the extended field -/

/-- The image under `ι` of a solution of `h` is a solution of `g`. -/
@[tmio T, powerlib_foundation] private theorem isIntegralCurveOn_relaxed_incl
    (hπι : ∀ u, π (ι u) = u) (hg : ∀ y, g y = ι (h (π y)) - (y - ι (π y))) {s : Set ℝ}
    {ψ : ℝ → State m} (hψ : IsIntegralCurveOn ψ (fun _ u => h u) s) :
    IsIntegralCurveOn (fun t => ι (ψ t)) (fun _ y => g y) s := fun t ht => by
  have hd := ι.hasFDerivAt.comp_hasDerivWithinAt t (hψ t ht)
  show HasDerivWithinAt (fun t => ι (ψ t)) (g (ι (ψ t))) s t
  rw [hg, hπι, sub_self, sub_zero]
  exact hd

/-- The projection by `π` of a solution of `g` is a solution of `h`. -/
@[tmio T, powerlib_foundation] private theorem isIntegralCurveOn_relaxed_proj
    (hπι : ∀ u, π (ι u) = u) (hg : ∀ y, g y = ι (h (π y)) - (y - ι (π y))) {s : Set ℝ}
    {φ : ℝ → State n} (hφ : IsIntegralCurveOn φ (fun _ y => g y) s) :
    IsIntegralCurveOn (fun t => π (φ t)) (fun _ u => h u) s := fun t ht => by
  have hd := π.hasFDerivAt.comp_hasDerivWithinAt t (hφ t ht)
  have he : π (g (φ t)) = h (π (φ t)) := by
    simp only [hg, map_sub, hπι, sub_self, sub_zero]
  show HasDerivWithinAt (fun t => π (φ t)) (h (π (φ t))) s t
  rw [← he]
  exact hd

/-- Along a solution segment of `g` the complement `y − ι π y` decays as `e^{−(t − t₀)}`. -/
@[tmio T, powerlib_foundation] private theorem relaxed_complement
    (hπι : ∀ u, π (ι u) = u) (hg : ∀ y, g y = ι (h (π y)) - (y - ι (π y)))
    {φ : ℝ → State n} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ g t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, φ t - ι (π (φ t)) = Real.exp (-(t - t₀)) • (φ t₀ - ι (π (φ t₀))) := by
  set Q : State n →L[ℝ] State n := ContinuousLinearMap.id ℝ (State n) - ι.comp π with hQdef
  have hQ : ∀ y, Q y = y - ι (π y) := fun y => by simp [hQdef]
  have hQg : ∀ y, Q (g y) = -Q y := fun y => by
    rw [hQ, hQ, hg]
    simp only [map_sub, hπι, sub_self, sub_zero]
    abel
  have hh : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt (fun t => Real.exp (t - t₀) • Q (φ t)) 0
      (Icc t₀ t₁) t := fun t ht => by
    have hc := Q.hasFDerivAt.comp_hasDerivWithinAt t (hφ t ht)
    have he := ((hasDerivWithinAt_id t (Icc t₀ t₁)).sub_const t₀).exp
    refine (he.smul hc).congr_deriv ?_
    show Real.exp (id t - t₀) • Q (g (φ t)) + (Real.exp (id t - t₀) * 1) • Q (φ t) = 0
    rw [hQg, id, mul_one, smul_neg, neg_add_cancel]
  have hconst := constant_of_has_deriv_right_zero
    (f := fun t => Real.exp (t - t₀) • Q (φ t))
    (fun t ht => (hh t ht).continuousWithinAt) (fun t ht =>
      (hh t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)))
  intro t ht
  have h1 := hconst t ht
  simp only [sub_self, Real.exp_zero, one_smul] at h1
  rw [← hQ, ← hQ, ← h1, smul_smul, ← Real.exp_add]
  simp

/-- Distances to a point `ι u` of the image: the projection and the complement are within the
distance, and the distance is within their sum. -/
@[tmio T, powerlib_foundation] private theorem norm_relaxed (hπι : ∀ u, π (ι u) = u)
    (hι : ∀ u, ‖ι u‖ = ‖u‖) (hπ : ∀ y, ‖π y‖ ≤ ‖y‖) (hQ : ∀ y, ‖y - ι (π y)‖ ≤ ‖y‖)
    (u : State m) (y : State n) :
    ‖π y - u‖ ≤ ‖y - ι u‖ ∧ ‖y - ι (π y)‖ ≤ ‖y - ι u‖ ∧
      ‖y - ι u‖ ≤ ‖π y - u‖ + ‖y - ι (π y)‖ := by
  have e1 : π y - u = π (y - ι u) := by rw [map_sub, hπι]
  have e2 : y - ι (π y) = (y - ι u) - ι (π (y - ι u)) := by
    simp only [map_sub, hπι]
    abel
  have e3 : y - ι u = ι (π y - u) + (y - ι (π y)) := by
    rw [map_sub]
    abel
  refine ⟨by rw [e1]; exact hπ _, by rw [e2]; exact hQ _, ?_⟩
  calc ‖y - ι u‖ = ‖ι (π y - u) + (y - ι (π y))‖ := by rw [← e3]
    _ ≤ ‖ι (π y - u)‖ + ‖y - ι (π y)‖ := norm_add_le _ _
    _ = ‖π y - u‖ + ‖y - ι (π y)‖ := by rw [hι]

/-! ## The three stability notions -/

/-- **Lyapunov stability of the relaxed extension.** With `π ∘ ι = id`, `ι` isometric, `π` and
`1 − ι π` not increasing norms, and `g(y) = ι h(π y) − (y − ι π y)`, the point `ι u` is Lyapunov
stable for `g` iff `u` is for `h`. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_relaxed_iff (hπι : ∀ u, π (ι u) = u)
    (hι : ∀ u, ‖ι u‖ = ‖u‖) (hπ : ∀ y, ‖π y‖ ≤ ‖y‖) (hQ : ∀ y, ‖y - ι (π y)‖ ≤ ‖y‖)
    (hg : ∀ y, g y = ι (h (π y)) - (y - ι (π y))) (u : State m) :
    LyapunovStable g (ι u) ↔ LyapunovStable h u := by
  constructor
  · intro hs ε hε
    obtain ⟨δ, hδ, hb⟩ := hs ε hε
    refine ⟨δ, hδ, fun t₀ t₁ ψ hψ h0 t ht => ?_⟩
    have h1 := hb t₀ t₁ _ (isIntegralCurveOn_relaxed_incl hπι hg hψ)
      (by rwa [← map_sub, hι]) t ht
    rwa [← map_sub, hι] at h1
  · intro hs ε hε
    obtain ⟨δ, hδ, hb⟩ := hs (ε / 2) (half_pos hε)
    refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), fun t₀ t₁ φ hφ h0 t ht => ?_⟩
    obtain ⟨hp0, hc0, -⟩ := norm_relaxed hπι hι hπ hQ u (φ t₀)
    obtain ⟨-, -, hsplit⟩ := norm_relaxed hπι hι hπ hQ u (φ t)
    have h1 := hb t₀ t₁ _ (isIntegralCurveOn_relaxed_proj hπι hg hφ)
      (lt_of_le_of_lt hp0 (lt_of_lt_of_le h0 (min_le_left _ _))) t ht
    have h2 : ‖φ t - ι (π (φ t))‖ ≤ ‖φ t₀ - ι u‖ := by
      rw [relaxed_complement hπι hg hφ t ht, norm_smul, Real.norm_eq_abs, Real.abs_exp]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (by linarith [ht.1]))).trans hc0
    have h3 := lt_of_lt_of_le h0 (min_le_right _ _)
    linarith

/-- **Local exponential stability of the relaxed extension** (the hypotheses of
`lyapunovStable_relaxed_iff`): the estimate of `h` with constants `C, a` gives that of `g` with
`C + 1` and `min a 1`, and conversely with the same constants. -/
@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_relaxed_iff
    (hπι : ∀ u, π (ι u) = u) (hι : ∀ u, ‖ι u‖ = ‖u‖) (hπ : ∀ y, ‖π y‖ ≤ ‖y‖)
    (hQ : ∀ y, ‖y - ι (π y)‖ ≤ ‖y‖) (hg : ∀ y, g y = ι (h (π y)) - (y - ι (π y)))
    (u : State m) :
    LocallyExponentiallyStable g (ι u) ↔ LocallyExponentiallyStable h u := by
  constructor
  · rintro ⟨r, C, a, hr, hC, ha, hb⟩
    refine ⟨r, C, a, hr, hC, ha, fun t₀ t₁ ψ hψ h0 t ht => ?_⟩
    have h1 := hb t₀ t₁ _ (isIntegralCurveOn_relaxed_incl hπι hg hψ)
      (by rwa [← map_sub, hι]) t ht
    simp only [← map_sub, hι] at h1
    exact h1
  · rintro ⟨r, C, a, hr, hC, ha, hb⟩
    refine ⟨r, C + 1, min a 1, hr, by linarith, lt_min ha one_pos,
      fun t₀ t₁ φ hφ h0 t ht => ?_⟩
    obtain ⟨hp0, hc0, -⟩ := norm_relaxed hπι hι hπ hQ u (φ t₀)
    obtain ⟨-, -, hsplit⟩ := norm_relaxed hπι hι hπ hQ u (φ t)
    have h1 := hb t₀ t₁ _ (isIntegralCurveOn_relaxed_proj hπι hg hφ) (lt_of_le_of_lt hp0 h0) t ht
    have hτ : 0 ≤ t - t₀ := by linarith [ht.1]
    have he1 : Real.exp (-a * (t - t₀)) ≤ Real.exp (-min a 1 * (t - t₀)) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_left a 1])
    have he2 : Real.exp (-(t - t₀)) ≤ Real.exp (-min a 1 * (t - t₀)) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_right a 1])
    have h2 : ‖φ t - ι (π (φ t))‖ ≤ Real.exp (-min a 1 * (t - t₀)) * ‖φ t₀ - ι u‖ := by
      rw [relaxed_complement hπι hg hφ t ht, norm_smul, Real.norm_eq_abs, Real.abs_exp]
      exact mul_le_mul he2 hc0 (norm_nonneg _) (Real.exp_pos _).le
    have h3 : C * Real.exp (-a * (t - t₀)) * ‖π (φ t₀) - u‖ ≤
        C * Real.exp (-min a 1 * (t - t₀)) * ‖φ t₀ - ι u‖ := by
      have hC0 : 0 ≤ C := by linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left he1 hC0) hp0 (norm_nonneg _)
        (mul_nonneg hC0 (Real.exp_pos _).le)
    nlinarith

/-- **Local asymptotic stability of the relaxed extension** (the hypotheses of
`lyapunovStable_relaxed_iff`): a forward-complete solution of `g` converges to `ι u` iff its
projection, a solution of `h`, converges to `u`, since the complement tends to zero. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_relaxed_iff
    (hπι : ∀ u, π (ι u) = u) (hι : ∀ u, ‖ι u‖ = ‖u‖) (hπ : ∀ y, ‖π y‖ ≤ ‖y‖)
    (hQ : ∀ y, ‖y - ι (π y)‖ ≤ ‖y‖) (hg : ∀ y, g y = ι (h (π y)) - (y - ι (π y)))
    (u : State m) :
    LocalAsymptoticStable g (ι u) ↔ LocalAsymptoticStable h u := by
  have hls := lyapunovStable_relaxed_iff hπι hι hπ hQ hg u
  constructor
  · rintro ⟨hs, c, hc, hconv⟩
    refine ⟨hls.mp hs, c, hc, fun t₀ ψ hψ h0 => ?_⟩
    have hlim := hconv t₀ _ (isIntegralCurveOn_relaxed_incl hπι hg hψ)
      (by rwa [← map_sub, hι])
    have h1 := (π.continuous.tendsto _).comp hlim
    simpa only [Function.comp_def, hπι] using h1
  · rintro ⟨hs, c, hc, hconv⟩
    refine ⟨hls.mpr hs, c, hc, fun t₀ φ hφ h0 => ?_⟩
    obtain ⟨hp0, -, -⟩ := norm_relaxed hπι hι hπ hQ u (φ t₀)
    have hlim := hconv t₀ _ (isIntegralCurveOn_relaxed_proj hπι hg hφ) (lt_of_le_of_lt hp0 h0)
    set c₀ := φ t₀ - ι (π (φ t₀)) with hc₀
    have hsplit : ∀ t, t₀ ≤ t → φ t = ι (π (φ t)) + Real.exp (-(t - t₀)) • c₀ := fun t ht => by
      rw [← relaxed_complement hπι hg (hφ.mono Icc_subset_Ici_self) t ⟨ht, le_rfl⟩]
      abel
    have hexp : Tendsto (fun t => Real.exp (-(t - t₀))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    have h1 := ((ι.continuous.tendsto u).comp hlim).add (hexp.smul_const c₀)
    rw [zero_smul, add_zero] at h1
    exact h1.congr' (eventually_atTop.mpr ⟨t₀, fun t ht => (hsplit t ht).symm⟩)

/-! ## The plane of the first two coordinates of `ℝ³` -/

/-- The inclusion `(a, b) ↦ (a, b, 0)` of the plane `y₂ = 0` of `ℝ³`. -/
def incl23 : State 2 →L[ℝ] State 3 :=
  (coord 0).smulRight (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) +
    (coord 1).smulRight (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))

/-- The projection `(a, b, c) ↦ (a, b)` onto the plane `y₂ = 0` of `ℝ³`. -/
def proj32 : State 3 →L[ℝ] State 2 :=
  (coord 0).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (coord 1).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

@[tmio T, simp, powerlib_foundation] theorem incl23_apply (u : State 2) :
    incl23 u = mk3 (u 0) (u 1) 0 := by
  apply state3_ext <;> simp [incl23]

@[tmio T, simp, powerlib_foundation] theorem proj32_apply_zero (y : State 3) :
    proj32 y 0 = y 0 := by
  simp [proj32]

@[tmio T, simp, powerlib_foundation] theorem proj32_apply_one (y : State 3) :
    proj32 y 1 = y 1 := by
  simp [proj32]

@[tmio T, powerlib_foundation] theorem proj32_incl23 (u : State 2) : proj32 (incl23 u) = u := by
  ext i
  fin_cases i <;> simp

@[tmio T, powerlib_foundation] theorem norm_incl23 (u : State 2) : ‖incl23 u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  simp

@[tmio T, powerlib_foundation] theorem norm_proj32_le (y : State 3) : ‖proj32 y‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  apply Real.sqrt_le_sqrt
  simp only [proj32_apply_zero, proj32_apply_one]
  nlinarith [sq_nonneg ‖y 2‖]

@[tmio T, powerlib_foundation] theorem norm_sub_incl23_proj32_le (y : State 3) :
    ‖y - incl23 (proj32 y)‖ ≤ ‖y‖ := by
  have e : y - incl23 (proj32 y) = y 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    apply state3_ext <;> simp
  rw [e, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  exact abs_apply_le_norm y 2

end powerlib.Dynamics.Degenerate
