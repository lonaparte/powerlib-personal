import theorem.Averaging.KBMPerturbed

/-! # Periodic orbits from averaging (Bogoliubov's second theorem)

Every averaging estimate of `theorem/Averaging/KBM.lean` and `theorem/Averaging/KBMPerturbed.lean`
holds on the window `[0, L/ε]`. Here a hyperbolic equilibrium `y*` of the averaged field
`f̄ = Averaging.fieldAverage f T` is shown to persist as a genuine `T`-periodic solution of the
original system `ẋ = ε f(x, t) + ε² r(x, t)` for all small `ε > 0`, `O(ε)`-close to `y*` for all
`t ∈ ℝ` and unique near `y*`. The proof uses only Lipschitz (Grönwall) estimates and no
differentiability of the flow: the period map is one Euler step of the averaged field plus a
remainder of order `ε²` with an `ε`-independent Lipschitz constant (the stroboscopic form of the
near-identity averaging transformation, formalized in `theorem/Averaging/NearIdentity.lean`:
`strobGen_sample`, `transformed_le`), and its fixed point is found by the Newton-type
contraction `y ↦ y − (εT Df̄(y*))⁻¹ (P(y) − y)`. Perturbations of order `ε^{1+κ}` are
`theorem/Averaging/PerturbedPeriodicOrbits.lean`.

Scope.
* `ẋ = ε f(x, t) + ε² r(x, t)` on a real Banach space `E`, `0 < ε ≤ 1`. Both `f` and `r` satisfy
  the hypotheses of `Averaging.kbm_first_order` with the same period `T > 0` (continuity,
  `T`-periodicity in `t`, global Lipschitz constants `ℓ`, `ℓ_r` and bounds `M`, `M_r`), written out
  in every statement (behaviour is defined only in the semantic layer). The remainder `r` may
  depend on `ε` (the constants do not); no derivative of `r` is used.
* `f(·, t)` is `C¹` on the closed ball `‖x − y*‖ ≤ ρ` with an `L₂`-Lipschitz derivative `Df(x, t)`,
  and `t ↦ Df(y*, t)` is continuous. Global hypotheses are met by a cut-off of a local field (as
  in `ParametricResonance.DuffingMathieu.cutField`).
* `y*` is an equilibrium of `f̄` and the derivative `A = Df̄(y*)` (a hypothesis `HasFDerivAt`) has a
  two-sided continuous linear inverse `B`. Solutions are global `C¹` curves; they exist and are
  unique (`DuffingMathieu.exists_global_solution`, Mathlib's `ODE_solution_unique_univ`).
* Generic mathematics, no model family.

Source: Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations*
(the justification of the averaging method, the second theorem of Bogoliubov: periodic solutions
near hyperbolic equilibria of the averaged system); Hale, *Ordinary Differential Equations*,
Ch. V (the method of averaging, periodic solutions); Sanders–Verhulst–Murdock, *Averaging Methods
in Nonlinear Dynamical Systems*, Ch. 6 (periodic averaging and hyperbolicity); work-sync
theory/T-averaging-method.md §1.1–1.3
(standard form, averaged field); the one-period estimates are proved here from KBM's
`Averaging.periodIntegral_eq` and Grönwall's inequality (Mathlib `dist_le_of_trajectories_ODE`).

Results.
* `solution_drift_le`, `field_lipschitzWith` — `‖x(b) − x(a)‖ ≤ ε(M + M_r)(b − a)`; the field
  `ε f + ε² r` is `(εℓ + ε²ℓ_r)`-Lipschitz.
* `period_step_le` — one period is one averaged Euler step up to `ε² C_S`:
  `‖x(τ + T) − x(τ) − εT f̄(x(τ))‖ ≤ ε²(ℓ(M + M_r)T² + M_r T)` (`stroboConst`).
* `second_diff_le` — second differences of a field with Lipschitz derivative.
* `fieldAverage_sub_linear_le` — `‖f̄(y) − f̄(z) − Df̄(y*)(y − z)‖ ≤ L₂ ρ' ‖y − z‖` on the ball of
  radius `ρ' ≤ ρ` (`Df̄(y*)` is the period average of `Df(y*, ·)`).
* `period_step_sub_le` — the `O(ε²)` part of the period map is `ε² L_S`-Lipschitz
  (`stroboLip`), for two solutions starting in a ball of radius `r₁`, `r₁ + ε(M + M_r)T ≤ ρ`.
* `full_field_continuous`, `full_solution_unique` — the field `ε f + ε² r` is jointly continuous;
  global solutions are unique.
* `exists_periodic_orbit` — **Bogoliubov's second theorem**: under explicit smallness conditions
  on `ε` and `r₀`, a `T`-periodic solution with `‖x_ε(t) − y*‖ ≤ ε(2‖B‖C_S/T + (M + M_r)T)` for all
  `t`, unique among solutions with `x(T) = x(0)`, `‖x(0) − y*‖ ≤ r₀`. Its stability and the
  validity of averaging on `[0, ∞)` are in `theorem/Averaging/PeriodicOrbitStability.lean`.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology intervalIntegral
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f r : E → ℝ → E} {T ℓ M ℓr Mr : ℝ}

section OnePeriod

/-- **Drift of a solution of `ẋ = ε f(x, t) + ε² r(x, t)`**: `‖x(b) − x(a)‖ ≤ ε(M + M_r)(b − a)`
for `a ≤ b`, `0 ≤ ε ≤ 1`, `‖f‖ ≤ M`, `‖r‖ ≤ M_r`. -/
@[tmio T, powerlib_foundation] theorem solution_drift_le (hfM : ∀ x t, ‖f x t‖ ≤ M)
    (hrM : ∀ x t, ‖r x t‖ ≤ Mr) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {x : ℝ → E} (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t) {a b : ℝ}
    (hab : a ≤ b) : ‖x b - x a‖ ≤ ε * (M + Mr) * (b - a) := by
  refine norm_image_sub_le_of_norm_deriv_le_segment' (f := x)
    (f' := fun t => ε • f (x t) t + ε ^ 2 • r (x t) t)
    (fun t _ => (hx t).hasDerivWithinAt) (fun t _ => ?_) b ⟨hab, le_rfl⟩
  have h1 : ε ^ 2 ≤ ε := by nlinarith
  have h2 : ε ^ 2 * ‖r (x t) t‖ ≤ ε * Mr :=
    (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hrM _ _) hε)
  have h3 : ε * ‖f (x t) t‖ ≤ ε * M := mul_le_mul_of_nonneg_left (hfM _ _) hε
  calc ‖ε • f (x t) t + ε ^ 2 • r (x t) t‖ ≤ ‖ε • f (x t) t‖ + ‖ε ^ 2 • r (x t) t‖ :=
        norm_add_le _ _
    _ = ε * ‖f (x t) t‖ + ε ^ 2 * ‖r (x t) t‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hε, Real.norm_of_nonneg (by positivity)]
    _ ≤ ε * M + ε * Mr := add_le_add h3 h2
    _ = ε * (M + Mr) := by ring

/-- The field `ε f + ε² r` is `(εℓ + ε²ℓ_r)`-Lipschitz in the state. -/
@[tmio T, powerlib_foundation] theorem field_lipschitzWith
    (hfl : ∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖)
    (hrl : ∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) (hℓ : 0 ≤ ℓ) (hℓr : 0 ≤ ℓr) {ε : ℝ}
    (hε : 0 ≤ ε) (t : ℝ) :
    LipschitzWith (Real.toNNReal (ε * ℓ + ε ^ 2 * ℓr)) fun y => ε • f y t + ε ^ 2 • r y t := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  calc ‖ε • f y t + ε ^ 2 • r y t - (ε • f z t + ε ^ 2 • r z t)‖
      = ‖ε • (f y t - f z t) + ε ^ 2 • (r y t - r z t)‖ := by
        congr 1; simp only [smul_sub]; abel
    _ ≤ ε * ‖f y t - f z t‖ + ε ^ 2 * ‖r y t - r z t‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hε, Real.norm_of_nonneg (by positivity)]
    _ ≤ ε * (ℓ * ‖y - z‖) + ε ^ 2 * (ℓr * ‖y - z‖) := by
        gcongr
        · exact hfl _ _ _
        · exact hrl _ _ _
    _ = (ε * ℓ + ε ^ 2 * ℓr) * ‖y - z‖ := by ring

/-- The one-period displacement minus the averaged Euler step, as an integral. -/
@[tmio T, powerlib_foundation] private theorem period_step_eq [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hrc : Continuous (Function.uncurry r)) {ε : ℝ} {x : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t) (τ : ℝ) :
    x (τ + T) - x τ - (ε * T) • fieldAverage f T (x τ) =
      ∫ s in τ..τ + T, (ε • (f (x s) s - f (x τ) s) + ε ^ 2 • r (x s) s) := by
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt
  have hfc : Continuous fun s => f (x s) s := hf.2.2.1.comp (hxc.prodMk continuous_id)
  have hrc' : Continuous fun s => r (x s) s := hrc.comp (hxc.prodMk continuous_id)
  have hfy : Continuous fun s => f (x τ) s := PeriodicField.continuous_snd hf (x τ)
  have hFc : Continuous fun s => ε • f (x s) s + ε ^ 2 • r (x s) s :=
    (hfc.const_smul ε).add (hrc'.const_smul (ε ^ 2))
  have hfy' : Continuous fun s => ε • f (x τ) s := hfy.const_smul ε
  have hFTC : ∫ s in τ..τ + T, (ε • f (x s) s + ε ^ 2 • r (x s) s) = x (τ + T) - x τ :=
    integral_eq_sub_of_hasDerivAt (fun t _ => hx t) (hFc.intervalIntegrable _ _)
  have hav : (ε * T) • fieldAverage f T (x τ) = ∫ s in τ..τ + T, ε • f (x τ) s := by
    rw [intervalIntegral.integral_smul, periodIntegral_eq hf (x τ) τ, smul_smul]
  rw [← hFTC, hav, ← intervalIntegral.integral_sub (hFc.intervalIntegrable _ _)
    (hfy'.intervalIntegrable _ _)]
  congr 1; funext s; simp only [smul_sub]; abel

/-- **One period of `ẋ = ε f(x, t) + ε² r(x, t)` is one Euler step of the averaged field up to
`O(ε²)`**: for a solution `x`, every initial time `τ` and `0 ≤ ε ≤ 1`,
`‖x(τ + T) − x(τ) − εT f̄(x(τ))‖ ≤ ε² (ℓ(M + M_r)T² + M_r T)`. -/
@[tmio T, powerlib_foundation] theorem period_step_le [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hrc : Continuous (Function.uncurry r)) (hrM : ∀ x t, ‖r x t‖ ≤ Mr)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {x : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t) (τ : ℝ) :
    ‖x (τ + T) - x τ - (ε * T) • fieldAverage f T (x τ)‖ ≤
      ε ^ 2 * (ℓ * (M + Mr) * T ^ 2 + Mr * T) := by
  have hT := hf.1
  have hℓ := hf.2.1
  rw [period_step_eq hf hrc hx τ]
  have hbound : ∀ s ∈ Ι τ (τ + T),
      ‖ε • (f (x s) s - f (x τ) s) + ε ^ 2 • r (x s) s‖ ≤ ε ^ 2 * (ℓ * (M + Mr) * T + Mr) := by
    intro s hs
    rw [uIoc_of_le (by linarith)] at hs
    have hd := solution_drift_le hf.2.2.2.2.2 hrM hε hε1 hx hs.1.le
    calc ‖ε • (f (x s) s - f (x τ) s) + ε ^ 2 • r (x s) s‖
        ≤ ε * ‖f (x s) s - f (x τ) s‖ + ε ^ 2 * ‖r (x s) s‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hε, Real.norm_of_nonneg (by positivity)]
      _ ≤ ε * (ℓ * (ε * (M + Mr) * T)) + ε ^ 2 * Mr := by
          gcongr
          · refine (hf.2.2.2.2.1 _ _ _).trans (mul_le_mul_of_nonneg_left (hd.trans ?_) hℓ)
            have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (x τ) 0)
            have hMr : 0 ≤ Mr := (norm_nonneg _).trans (hrM (x τ) 0)
            exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by positivity)
          · exact hrM _ _
      _ = ε ^ 2 * (ℓ * (M + Mr) * T + Mr) := by ring
  have h := norm_integral_le_of_norm_le_const hbound
  rw [show τ + T - τ = T by ring, abs_of_pos hT] at h
  calc _ ≤ ε ^ 2 * (ℓ * (M + Mr) * T + Mr) * T := h
    _ = ε ^ 2 * (ℓ * (M + Mr) * T ^ 2 + Mr * T) := by ring

end OnePeriod

section Smooth

variable {Df : E → ℝ → E →L[ℝ] E} {ystar : E} {ρ L₂ : ℝ}

@[tmio T, powerlib_foundation] private theorem norm_segment_sub_le {a b y : E} {ρ θ : ℝ}
    (ha : ‖a - y‖ ≤ ρ) (hb : ‖b - y‖ ≤ ρ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ‖b + θ • (a - b) - y‖ ≤ ρ := by
  have e : b + θ • (a - b) - y = (1 - θ) • (b - y) + θ • (a - y) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  rw [e]
  calc ‖(1 - θ) • (b - y) + θ • (a - y)‖ ≤ (1 - θ) * ‖b - y‖ + θ * ‖a - y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hθ.2]),
          Real.norm_of_nonneg hθ.1]
    _ ≤ (1 - θ) * ρ + θ * ρ := by
        gcongr
        · linarith [hθ.2]
        · exact hθ.1
    _ = ρ := by ring

@[tmio T, powerlib_foundation] private theorem hasDerivAt_segment (a b : E) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => b + θ • (a - b)) (a - b) θ := by
  have h := ((hasDerivAt_id θ).smul_const (a - b)).const_add b
  simpa using h

/-- **Second differences of a field with Lipschitz derivative.** If `f(·, t)` has the derivative
`Df(x, t)` on the closed ball `‖x − y*‖ ≤ ρ`, `Df` is `L₂`-Lipschitz there and `f(·, t)` is
`ℓ`-Lipschitz, then for `a, b, c, d` in the ball with `‖a − c‖, ‖b − d‖ ≤ m`:
`‖(f(a) − f(b)) − (f(c) − f(d))‖ ≤ L₂ m ‖a − b‖ + ℓ ‖(a − b) − (c − d)‖`. -/
@[tmio T, powerlib_foundation] theorem second_diff_le
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hfl : ∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) (hℓ : 0 ≤ ℓ) (hL₂ : 0 ≤ L₂) {a b c d : E}
    (ha : ‖a - ystar‖ ≤ ρ) (hb : ‖b - ystar‖ ≤ ρ) (hc : ‖c - ystar‖ ≤ ρ)
    (hd : ‖d - ystar‖ ≤ ρ) {m : ℝ} (hac : ‖a - c‖ ≤ m) (hbd : ‖b - d‖ ≤ m) (t : ℝ) :
    ‖(f a t - f b t) - (f c t - f d t)‖ ≤ L₂ * m * ‖a - b‖ + ℓ * ‖(a - b) - (c - d)‖ := by
  set p : ℝ → E := fun θ => b + θ • (a - b) with hp
  set q : ℝ → E := fun θ => d + θ • (c - d) with hq
  have hlip : LipschitzWith (Real.toNNReal ℓ) fun y => f y t := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hℓ]
    exact hfl y z t
  have hderiv : ∀ θ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun θ => f (p θ) t - f (q θ) t)
      (Df (p θ) t (a - b) - Df (q θ) t (c - d)) (Icc 0 1) θ := by
    intro θ hθ
    have h1 := (hD (p θ) (norm_segment_sub_le ha hb hθ) t).comp_hasDerivAt θ
      (hasDerivAt_segment a b θ)
    have h2 := (hD (q θ) (norm_segment_sub_le hc hd hθ) t).comp_hasDerivAt θ
      (hasDerivAt_segment c d θ)
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ θ ∈ Ico (0 : ℝ) 1, ‖Df (p θ) t (a - b) - Df (q θ) t (c - d)‖ ≤
      L₂ * m * ‖a - b‖ + ℓ * ‖(a - b) - (c - d)‖ := by
    intro θ hθ
    have hθ' := Ico_subset_Icc_self hθ
    have hpq : ‖p θ - q θ‖ ≤ m := by
      have e : p θ - q θ = (1 - θ) • (b - d) + θ • (a - c) := by
        simp only [hp, hq, sub_smul, one_smul, smul_sub]; abel
      rw [e]
      calc ‖(1 - θ) • (b - d) + θ • (a - c)‖ ≤ (1 - θ) * ‖b - d‖ + θ * ‖a - c‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hθ'.2]),
              Real.norm_of_nonneg hθ'.1]
        _ ≤ (1 - θ) * m + θ * m := by
            gcongr
            · linarith [hθ'.2]
            · exact hθ'.1
        _ = m := by ring
    have hDq : ‖Df (q θ) t‖ ≤ ℓ := by
      have := (hD (q θ) (norm_segment_sub_le hc hd hθ') t).le_of_lipschitz hlip
      rwa [Real.coe_toNNReal _ hℓ] at this
    have e : Df (p θ) t (a - b) - Df (q θ) t (c - d) =
        (Df (p θ) t - Df (q θ) t) (a - b) + Df (q θ) t ((a - b) - (c - d)) := by
      simp only [sub_apply, map_sub]; abel
    rw [e]
    calc ‖(Df (p θ) t - Df (q θ) t) (a - b) + Df (q θ) t ((a - b) - (c - d))‖
        ≤ ‖Df (p θ) t - Df (q θ) t‖ * ‖a - b‖ + ‖Df (q θ) t‖ * ‖(a - b) - (c - d)‖ :=
          (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.le_opNorm _ _)
            (ContinuousLinearMap.le_opNorm _ _))
      _ ≤ (L₂ * ‖p θ - q θ‖) * ‖a - b‖ + ℓ * ‖(a - b) - (c - d)‖ := by
          gcongr
          exact hDl _ _ (norm_segment_sub_le ha hb hθ') (norm_segment_sub_le hc hd hθ') t
      _ ≤ L₂ * m * ‖a - b‖ + ℓ * ‖(a - b) - (c - d)‖ := by gcongr
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  have e : (f (p 1) t - f (q 1) t) - (f (p 0) t - f (q 0) t) =
      (f a t - f b t) - (f c t - f d t) := by
    simp only [hp, hq, one_smul, zero_smul, add_zero, add_sub_cancel]; abel
  rw [e] at h
  exact h

/-- **The averaged field is linear up to `L₂ρ'` on a ball.** If `f(·, t)` is `C¹` on the ball
`‖x − y*‖ ≤ ρ` with `L₂`-Lipschitz derivative `Df`, `Df(y*, ·)` is continuous and `A` is the
derivative of the averaged field `f̄` at `y*`, then for `y, z` in the smaller ball of radius
`ρ' ≤ ρ`: `‖f̄(y) − f̄(z) − A(y − z)‖ ≤ L₂ ρ' ‖y − z‖`. (The derivative of `f̄` at `y*` is the
period average of `Df(y*, ·)`.) -/
@[tmio T, powerlib_foundation] theorem fieldAverage_sub_linear_le [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {A : E →L[ℝ] E}
    (hA : HasFDerivAt (fieldAverage f T) A ystar) {ρ' : ℝ} (hρ' : ρ' ≤ ρ) {y z : E}
    (hy : ‖y - ystar‖ ≤ ρ') (hz : ‖z - ystar‖ ≤ ρ') :
    ‖fieldAverage f T y - fieldAverage f T z - A (y - z)‖ ≤ L₂ * ρ' * ‖y - z‖ := by
  have hT := hf.1
  have hystar : ‖ystar - ystar‖ ≤ ρ := by rw [sub_self, norm_zero]; exact hρ.le
  -- pointwise: `f(·, s) − Df(y*, s)` is `L₂ρ'`-Lipschitz on the ball of radius `ρ'`
  have hpt : ∀ ρ'' ≤ ρ, ∀ y z : E, ‖y - ystar‖ ≤ ρ'' → ‖z - ystar‖ ≤ ρ'' → ∀ s,
      ‖f y s - f z s - Df ystar s (y - z)‖ ≤ L₂ * ρ'' * ‖y - z‖ := by
    intro ρ'' hρ'' y z hy hz s
    have hderiv : ∀ θ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
        (fun θ => f (z + θ • (y - z)) s - θ • Df ystar s (y - z))
        (Df (z + θ • (y - z)) s (y - z) - Df ystar s (y - z)) (Icc 0 1) θ := by
      intro θ hθ
      have h1 := (hD _ ((norm_segment_sub_le hy hz hθ).trans hρ'') s).comp_hasDerivAt θ
        (hasDerivAt_segment y z θ)
      have h2 := (hasDerivAt_id θ).smul_const (Df ystar s (y - z))
      simp only [id, one_smul] at h2
      exact (h1.sub h2).hasDerivWithinAt
    have hbound : ∀ θ ∈ Ico (0 : ℝ) 1,
        ‖Df (z + θ • (y - z)) s (y - z) - Df ystar s (y - z)‖ ≤ L₂ * ρ'' * ‖y - z‖ := by
      intro θ hθ
      have hθ' := Ico_subset_Icc_self hθ
      have hseg := norm_segment_sub_le hy hz hθ'
      rw [← sub_apply]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      gcongr
      exact (hDl _ _ (hseg.trans hρ'') hystar s).trans (mul_le_mul_of_nonneg_left hseg hL₂)
    have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
    have e : (f (z + (1 : ℝ) • (y - z)) s - (1 : ℝ) • Df ystar s (y - z)) -
        (f (z + (0 : ℝ) • (y - z)) s - (0 : ℝ) • Df ystar s (y - z)) =
        f y s - f z s - Df ystar s (y - z) := by
      simp only [one_smul, zero_smul, add_zero, add_sub_cancel, sub_zero]; abel
    rw [e] at h
    exact h
  -- the average of `Df(y*, ·)`
  set Abar : E →L[ℝ] E := T⁻¹ • ∫ s in (0 : ℝ)..T, Df ystar s with hAbar
  have hAbar_apply : ∀ v, Abar v = T⁻¹ • ∫ s in (0 : ℝ)..T, Df ystar s v := by
    intro v
    rw [hAbar, smul_apply,
      ContinuousLinearMap.intervalIntegral_apply (hDc.intervalIntegrable _ _)]
  have hbar : ∀ ρ'' ≤ ρ, ∀ y z : E, ‖y - ystar‖ ≤ ρ'' → ‖z - ystar‖ ≤ ρ'' →
      ‖fieldAverage f T y - fieldAverage f T z - Abar (y - z)‖ ≤ L₂ * ρ'' * ‖y - z‖ := by
    intro ρ'' hρ'' y z hy hz
    have hcy := PeriodicField.continuous_snd hf y
    have hcz := PeriodicField.continuous_snd hf z
    have hcD : Continuous fun s => Df ystar s (y - z) :=
      (ContinuousLinearMap.apply ℝ E (y - z)).continuous.comp hDc
    have e : fieldAverage f T y - fieldAverage f T z - Abar (y - z) =
        T⁻¹ • ∫ s in (0 : ℝ)..T, (f y s - f z s - Df ystar s (y - z)) := by
      have hcyz : Continuous fun s => f y s - f z s := hcy.sub hcz
      rw [hAbar_apply, fieldAverage, fieldAverage, ← smul_sub, ← smul_sub,
        intervalIntegral.integral_sub (hcyz.intervalIntegrable _ _) (hcD.intervalIntegrable _ _),
        intervalIntegral.integral_sub (hcy.intervalIntegrable _ _) (hcz.intervalIntegrable _ _)]
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hT.le)]
    have h := norm_integral_le_of_norm_le_const (a := 0) (b := T)
      (f := fun s => f y s - f z s - Df ystar s (y - z)) (C := L₂ * ρ'' * ‖y - z‖)
      (fun s _ => hpt ρ'' hρ'' y z hy hz s)
    rw [sub_zero, abs_of_pos hT] at h
    calc T⁻¹ * ‖∫ s in (0 : ℝ)..T, (f y s - f z s - Df ystar s (y - z))‖
        ≤ T⁻¹ * (L₂ * ρ'' * ‖y - z‖ * T) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hT.le)
      _ = L₂ * ρ'' * ‖y - z‖ := by field_simp
  -- `Abar` is the derivative of `f̄` at `y*`, hence equals `A`
  have hAbarD : HasFDerivAt (fieldAverage f T) Abar ystar := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hO : (fun h => fieldAverage f T (ystar + h) - fieldAverage f T ystar - Abar h) =O[𝓝 0]
        fun h => ‖h‖ ^ 2 := by
      refine Asymptotics.IsBigO.of_bound L₂ ?_
      filter_upwards [Metric.closedBall_mem_nhds (0 : E) hρ] with h hh
      rw [Metric.mem_closedBall, dist_zero_right] at hh
      have hb := hbar ‖h‖ hh (ystar + h) ystar (by rw [add_sub_cancel_left])
        (by rw [sub_self, norm_zero]; exact norm_nonneg _)
      rw [add_sub_cancel_left] at hb
      rw [Real.norm_of_nonneg (by positivity)]
      calc _ ≤ L₂ * ‖h‖ * ‖h‖ := hb
        _ = L₂ * ‖h‖ ^ 2 := by ring
    exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  have hAeq : A = Abar := hA.unique hAbarD
  rw [hAeq]
  exact hbar ρ' hρ' y z hy hz

/-- The Lipschitz constant `L_S = e^{(ℓ + ℓ_r)T}(T²(L₂(M + M_r) + ℓ(ℓ + ℓ_r)) + Tℓ_r)` of the
`O(ε²)` part of the period map (`period_step_sub_le`). -/
def stroboLip (ℓ ℓr L₂ M Mr T : ℝ) : ℝ :=
  Real.exp ((ℓ + ℓr) * T) * (T ^ 2 * (L₂ * (M + Mr) + ℓ * (ℓ + ℓr)) + T * ℓr)

/-- The bound `C_S = ℓ(M + M_r)T² + M_r T` of the `O(ε²)` part of the period map
(`period_step_le`). -/
def stroboConst (ℓ M Mr T : ℝ) : ℝ := ℓ * (M + Mr) * T ^ 2 + Mr * T

/-- **The `O(ε²)` part of the period map is Lipschitz with an `ε`-independent constant.** For two
solutions `x`, `z` of `ẋ = ε f(x, t) + ε² r(x, t)` (`0 ≤ ε ≤ 1`) starting at time `τ` in the ball
`‖· − y*‖ ≤ r₁` with `r₁ + ε(M + M_r)T ≤ ρ`, where `f(·, t)` has an `L₂`-Lipschitz derivative:
`‖(x(τ + T) − x(τ) − εT f̄(x(τ))) − (z(τ + T) − z(τ) − εT f̄(z(τ)))‖ ≤ ε² L_S ‖x(τ) − z(τ)‖`,
`L_S = stroboLip ℓ ℓ_r L₂ M M_r T` (Grönwall for `x − z`, second differences of `f`). -/
@[tmio T, powerlib_foundation] theorem period_step_sub_le [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hr : 0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
      (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr)
    (hL₂ : 0 ≤ L₂) (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {x z : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t)
    (hz : ∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) {τ r₁ : ℝ}
    (hxτ : ‖x τ - ystar‖ ≤ r₁) (hzτ : ‖z τ - ystar‖ ≤ r₁) (hr₁ : r₁ + ε * (M + Mr) * T ≤ ρ) :
    ‖(x (τ + T) - x τ - (ε * T) • fieldAverage f T (x τ)) -
        (z (τ + T) - z τ - (ε * T) • fieldAverage f T (z τ))‖ ≤
      ε ^ 2 * stroboLip ℓ ℓr L₂ M Mr T * ‖x τ - z τ‖ := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hℓr := hr.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (x τ) 0)
  have hMr : 0 ≤ Mr := (norm_nonneg _).trans (hr.2.2.2.2.2 (x τ) 0)
  set e₀ := ‖x τ - z τ‖ with he₀
  set G := Real.exp ((ℓ + ℓr) * T) with hG
  have hG1 : 1 ≤ G := Real.one_le_exp (by positivity)
  set v : ℝ → E → E := fun t y => ε • f y t + ε ^ 2 • r y t with hv
  set K := ε * ℓ + ε ^ 2 * ℓr with hK
  have hK0 : 0 ≤ K := by positivity
  have hKle : K ≤ ε * (ℓ + ℓr) := by
    have : ε ^ 2 ≤ ε := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hℓr]
  have hlip : ∀ t, LipschitzWith (Real.toNNReal K) (v t) := fun t =>
    field_lipschitzWith hf.2.2.2.2.1 hr.2.2.2.2.1 hℓ hℓr hε t
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt
  have hzc : Continuous z := continuous_iff_continuousAt.mpr fun t => (hz t).continuousAt
  -- Grönwall: `‖x(s) − z(s)‖ ≤ G e₀` on `[τ, τ + T]`
  have hgr : ∀ s ∈ Icc τ (τ + T), ‖x s - z s‖ ≤ G * e₀ := by
    intro s hs
    have h := dist_le_of_trajectories_ODE (v := v) hlip hxc.continuousOn
      (fun t _ => (hx t).hasDerivWithinAt) hzc.continuousOn
      (fun t _ => (hz t).hasDerivWithinAt) (le_of_eq rfl) s hs
    rw [dist_eq_norm, Real.coe_toNNReal _ hK0, ← dist_eq_norm] at h
    rw [← dist_eq_norm]
    refine h.trans ?_
    rw [dist_eq_norm, mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 : s - τ ≤ T := by linarith [hs.2]
    have h2 : 0 ≤ s - τ := by linarith [hs.1]
    refine mul_le_mul (hKle.trans ?_) h1 h2 (by positivity)
    nlinarith
  -- the deviation of `x − z` from its initial value
  have hdev : ∀ s ∈ Icc τ (τ + T),
      ‖(x s - x τ) - (z s - z τ)‖ ≤ ε * (ℓ + ℓr) * (G * e₀) * T := by
    intro s hs
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u => x u - z u)
      (f' := fun u => v u (x u) - v u (z u)) (C := ε * (ℓ + ℓr) * (G * e₀))
      (fun u _ => ((hx u).sub (hz u)).hasDerivWithinAt)
      (fun u hu => by
        have hu' : u ∈ Icc τ (τ + T) := ⟨hu.1, hu.2.le.trans hs.2⟩
        have := (hlip u).dist_le_mul (x u) (z u)
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK0] at this
        refine this.trans ?_
        exact mul_le_mul hKle (hgr u hu') (norm_nonneg _) (by positivity)) s ⟨hs.1, le_rfl⟩
    have e : (x s - z s) - (x τ - z τ) = (x s - x τ) - (z s - z τ) := by abel
    rw [e] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by positivity)
  -- the drifts
  have hdx : ∀ s ∈ Icc τ (τ + T), ‖x s - x τ‖ ≤ ε * (M + Mr) * T := fun s hs =>
    (solution_drift_le hf.2.2.2.2.2 hr.2.2.2.2.2 hε hε1 hx hs.1).trans
      (mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by positivity))
  have hdz : ∀ s ∈ Icc τ (τ + T), ‖z s - z τ‖ ≤ ε * (M + Mr) * T := fun s hs =>
    (solution_drift_le hf.2.2.2.2.2 hr.2.2.2.2.2 hε hε1 hz hs.1).trans
      (mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by positivity))
  have hball : ∀ w : ℝ → E, ‖w τ - ystar‖ ≤ r₁ → ∀ s, ‖w s - w τ‖ ≤ ε * (M + Mr) * T →
      ‖w s - ystar‖ ≤ ρ := by
    intro w hw s hs
    calc ‖w s - ystar‖ = ‖(w s - w τ) + (w τ - ystar)‖ := by congr 1; abel
      _ ≤ ‖w s - w τ‖ + ‖w τ - ystar‖ := norm_add_le _ _
      _ ≤ ρ := by linarith
  have hdrift0 : 0 ≤ ε * (M + Mr) * T := by positivity
  have hxτ' : ‖x τ - ystar‖ ≤ ρ := by linarith
  have hzτ' : ‖z τ - ystar‖ ≤ ρ := by linarith
  -- the integrand
  rw [period_step_eq hf hr.2.2.1 hx τ, period_step_eq hf hr.2.2.1 hz τ,
    ← intervalIntegral.integral_sub]
  rotate_left
  · exact (Continuous.intervalIntegrable (by
      have hfc : Continuous fun s => f (x s) s := hf.2.2.1.comp (hxc.prodMk continuous_id)
      have hrc : Continuous fun s => r (x s) s := hr.2.2.1.comp (hxc.prodMk continuous_id)
      exact ((hfc.sub (PeriodicField.continuous_snd hf (x τ))).const_smul ε).add
        (hrc.const_smul (ε ^ 2))) _ _)
  · exact (Continuous.intervalIntegrable (by
      have hfc : Continuous fun s => f (z s) s := hf.2.2.1.comp (hzc.prodMk continuous_id)
      have hrc : Continuous fun s => r (z s) s := hr.2.2.1.comp (hzc.prodMk continuous_id)
      exact ((hfc.sub (PeriodicField.continuous_snd hf (z τ))).const_smul ε).add
        (hrc.const_smul (ε ^ 2))) _ _)
  have hbound : ∀ s ∈ Ι τ (τ + T),
      ‖(ε • (f (x s) s - f (x τ) s) + ε ^ 2 • r (x s) s) -
          (ε • (f (z s) s - f (z τ) s) + ε ^ 2 • r (z s) s)‖ ≤
        ε ^ 2 * (G * e₀) * (T * (L₂ * (M + Mr) + ℓ * (ℓ + ℓr)) + ℓr) := by
    intro s hs
    rw [uIoc_of_le (by linarith)] at hs
    have hs' : s ∈ Icc τ (τ + T) := ⟨hs.1.le, hs.2⟩
    have he0G : ‖x τ - z τ‖ ≤ G * e₀ := by
      rw [← he₀]; nlinarith [norm_nonneg (x τ - z τ)]
    have hsd := second_diff_le hD hDl hf.2.2.2.2.1 hℓ hL₂ (hball x hxτ s (hdx s hs')) hxτ'
      (hball z hzτ s (hdz s hs')) hzτ' (hgr s hs') he0G s
    have hrd := hr.2.2.2.2.1 (x s) (z s) s
    have e : (ε • (f (x s) s - f (x τ) s) + ε ^ 2 • r (x s) s) -
        (ε • (f (z s) s - f (z τ) s) + ε ^ 2 • r (z s) s) =
        ε • ((f (x s) s - f (x τ) s) - (f (z s) s - f (z τ) s)) +
          ε ^ 2 • (r (x s) s - r (z s) s) := by
      simp only [smul_sub]; abel
    rw [e]
    calc ‖ε • ((f (x s) s - f (x τ) s) - (f (z s) s - f (z τ) s)) +
          ε ^ 2 • (r (x s) s - r (z s) s)‖
        ≤ ε * ‖(f (x s) s - f (x τ) s) - (f (z s) s - f (z τ) s)‖ +
            ε ^ 2 * ‖r (x s) s - r (z s) s‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hε, Real.norm_of_nonneg (by positivity)]
      _ ≤ ε * (L₂ * (G * e₀) * (ε * (M + Mr) * T) +
              ℓ * (ε * (ℓ + ℓr) * (G * e₀) * T)) + ε ^ 2 * (ℓr * (G * e₀)) := by
          gcongr
          · refine hsd.trans ?_
            gcongr
            · exact hdx s hs'
            · exact hdev s hs'
          · exact hrd.trans (mul_le_mul_of_nonneg_left (hgr s hs') hℓr)
      _ = ε ^ 2 * (G * e₀) * (T * (L₂ * (M + Mr) + ℓ * (ℓ + ℓr)) + ℓr) := by ring
  have h := norm_integral_le_of_norm_le_const hbound
  rw [show τ + T - τ = T by ring, abs_of_pos hT] at h
  refine h.trans (le_of_eq ?_)
  simp only [stroboLip, ← hG]
  ring

end Smooth

section Orbit

variable {Df : E → ℝ → E →L[ℝ] E} {ystar : E} {ρ L₂ : ℝ}

/-- The field `ε f + ε² r` of the full system is continuous and `T`-periodic in `t`. -/
@[tmio T, powerlib_foundation] theorem full_field_continuous
    (hfc : Continuous (Function.uncurry f)) (hrc : Continuous (Function.uncurry r)) (ε : ℝ) :
    Continuous (Function.uncurry fun (t : ℝ) (y : E) => ε • f y t + ε ^ 2 • r y t) := by
  have h1 : Continuous fun q : ℝ × E => f q.2 q.1 := hfc.comp (continuous_snd.prodMk continuous_fst)
  have h2 : Continuous fun q : ℝ × E => r q.2 q.1 := hrc.comp (continuous_snd.prodMk continuous_fst)
  exact (h1.const_smul ε).add (h2.const_smul (ε ^ 2))

/-- Global solutions of the full system are unique. -/
@[tmio T, powerlib_foundation] theorem full_solution_unique
    (hfl : ∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖)
    (hrl : ∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) (hℓ : 0 ≤ ℓ) (hℓr : 0 ≤ ℓr) {ε : ℝ}
    (hε : 0 ≤ ε) {x z : ℝ → E} (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t)
    (hz : ∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) {t₀ : ℝ} (h : x t₀ = z t₀) :
    x = z :=
  ODE_solution_unique_univ (v := fun t y => ε • f y t + ε ^ 2 • r y t) (s := fun _ => univ)
    (fun t => (field_lipschitzWith hfl hrl hℓ hℓr hε t).lipschitzOnWith)
    (fun t => ⟨hx t, mem_univ _⟩) (fun t => ⟨hz t, mem_univ _⟩) h

/-- **Bogoliubov's second theorem (existence and uniqueness of the periodic solution).** Let `f`
and `r` satisfy the hypotheses of `Averaging.kbm_first_order` (period `T`, Lipschitz constants
`ℓ`, `ℓ_r`, bounds `M`, `M_r`), let `f(·, t)` be `C¹` on the ball `‖x − y*‖ ≤ ρ` with
`L₂`-Lipschitz derivative `Df` (`Df(y*, ·)` continuous), and let `y*` be an equilibrium of the
averaged field, `f̄(y*) = 0`, whose derivative `A = Df̄(y*)` is invertible with inverse `B`. Then
for every `ε` with `0 < ε ≤ 1`, `2ε(M + M_r)T ≤ ρ`, `4ε‖B‖L_S ≤ T` and `2ε‖B‖C_S ≤ r₀T`
(`L_S = stroboLip …`, `C_S = stroboConst …`, `r₀ > 0` with `2r₀ ≤ ρ`, `4‖B‖L₂r₀ ≤ 1`), the system
`ẋ = ε f(x, t) + ε² r(x, t)` has a `T`-periodic solution `x_ε` with
`‖x_ε(t) − y*‖ ≤ ε (2‖B‖C_S/T + (M + M_r)T)` for all `t`, and it is the only solution with
`x(T) = x(0)` and `‖x(0) − y*‖ ≤ r₀`. (The period map `P(y) = y + εT f̄(y) + ε² S(y)` with
`‖S‖ ≤ C_S`, `Lip S ≤ L_S` (`period_step_le`, `period_step_sub_le`), and the Newton-type
contraction `y ↦ y − (εT A)⁻¹ (P(y) − y)` on the ball of radius `r₀`.) -/
@[tmio T, powerlib_foundation] theorem exists_periodic_orbit [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hr : 0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
      (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) (h0 : fieldAverage f T ystar = 0) {A B : E →L[ℝ] E}
    (hA : HasFDerivAt (fieldAverage f T) A ystar) (hAB : ∀ v, A (B v) = v)
    (hBA : ∀ v, B (A v) = v) {r₀ ε : ℝ} (hr₀ : 0 < r₀) (hr₀ρ : 2 * r₀ ≤ ρ)
    (hr₀L : 4 * ‖B‖ * L₂ * r₀ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hερ : 2 * ε * (M + Mr) * T ≤ ρ) (hεL : 4 * ε * ‖B‖ * stroboLip ℓ ℓr L₂ M Mr T ≤ T)
    (hεC : 2 * ε * ‖B‖ * stroboConst ℓ M Mr T ≤ r₀ * T) :
    ∃ x : ℝ → E, (∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t) ∧
      (∀ t, x (t + T) = x t) ∧
      (∀ t, ‖x t - ystar‖ ≤ ε * (2 * ‖B‖ * stroboConst ℓ M Mr T / T + (M + Mr) * T)) ∧
      ∀ z : ℝ → E, (∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) →
        z T = z 0 → ‖z 0 - ystar‖ ≤ r₀ → z = x := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hℓr := hr.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  have hMr : 0 ≤ Mr := (norm_nonneg _).trans (hr.2.2.2.2.2 ystar 0)
  have hεT : 0 < ε * T := mul_pos hε hT
  set CS := stroboConst ℓ M Mr T with hCS
  set LS := stroboLip ℓ ℓr L₂ M Mr T with hLS
  -- the solutions from time `0`
  have hsol : ∀ y : E, ∃ x : ℝ → E, x 0 = y ∧
      ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t := fun y =>
    ParametricResonance.DuffingMathieu.exists_global_solution
      (full_field_continuous hf.2.2.1 hr.2.2.1 ε)
      (fun t => field_lipschitzWith hf.2.2.2.2.1 hr.2.2.2.2.1 hℓ hℓr hε.le t) y
  choose X hX0 hX using hsol
  -- the `O(ε²)` part of the period map
  set Ψ : E → E := fun y => X y T - y - (ε * T) • fieldAverage f T y with hΨ
  have hΨb : ∀ y, ‖Ψ y‖ ≤ ε ^ 2 * CS := by
    intro y
    have h := period_step_le hf hr.2.2.1 hr.2.2.2.2.2 hε.le hε1 (hX y) 0
    rw [zero_add, hX0] at h
    exact h
  have hΨl : ∀ y z, ‖y - ystar‖ ≤ r₀ → ‖z - ystar‖ ≤ r₀ → ‖Ψ y - Ψ z‖ ≤ ε ^ 2 * LS * ‖y - z‖ := by
    intro y z hy hz
    have h := period_step_sub_le hf hr hL₂ hD hDl hε.le hε1 (hX y) (hX z) (τ := 0) (r₁ := r₀)
      (by rw [hX0]; exact hy) (by rw [hX0]; exact hz) (by linarith)
    simp only [zero_add, hX0] at h
    exact h
  -- the Newton-type map
  set N : E → E := fun y => y - B (fieldAverage f T y + (ε * T)⁻¹ • Ψ y) with hN
  have hNlip : ∀ y z, ‖y - ystar‖ ≤ r₀ → ‖z - ystar‖ ≤ r₀ → ‖N y - N z‖ ≤ 2⁻¹ * ‖y - z‖ := by
    intro y z hy hz
    have e : N y - N z = -(B (fieldAverage f T y - fieldAverage f T z - A (y - z)) +
        (ε * T)⁻¹ • B (Ψ y - Ψ z)) := by
      simp only [hN, map_sub, map_add, map_smul, hBA]
      simp only [smul_sub]; abel
    rw [e, norm_neg]
    have h1 := fieldAverage_sub_linear_le hf hρ hL₂ hD hDl hDc hA (by linarith) hy hz
    have h2 := hΨl y z hy hz
    calc ‖B (fieldAverage f T y - fieldAverage f T z - A (y - z)) +
          (ε * T)⁻¹ • B (Ψ y - Ψ z)‖
        ≤ ‖B‖ * (L₂ * r₀ * ‖y - z‖) + (ε * T)⁻¹ * (‖B‖ * (ε ^ 2 * LS * ‖y - z‖)) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
          · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hεT.le)]
            exact mul_le_mul_of_nonneg_left
              ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
              (inv_nonneg.mpr hεT.le)
      _ = (‖B‖ * L₂ * r₀ + ε * ‖B‖ * LS / T) * ‖y - z‖ := by field_simp
      _ ≤ (4⁻¹ + 4⁻¹) * ‖y - z‖ := by
          gcongr
          · linarith
          · rw [div_le_iff₀ hT]; linarith
      _ = 2⁻¹ * ‖y - z‖ := by norm_num
  have hN0 : ‖N ystar - ystar‖ ≤ ε * ‖B‖ * CS / T := by
    have e : N ystar - ystar = -((ε * T)⁻¹ • B (Ψ ystar)) := by
      simp only [hN, h0, zero_add, map_smul]; abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hεT.le)]
    calc (ε * T)⁻¹ * ‖B (Ψ ystar)‖ ≤ (ε * T)⁻¹ * (‖B‖ * (ε ^ 2 * CS)) :=
          mul_le_mul_of_nonneg_left ((B.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (hΨb _) (norm_nonneg _))) (inv_nonneg.mpr hεT.le)
      _ = ε * ‖B‖ * CS / T := by field_simp
  have hN0' : ε * ‖B‖ * CS / T ≤ r₀ / 2 := by
    rw [div_le_iff₀ hT]; linarith
  have hball : ∀ y, ‖y - ystar‖ ≤ r₀ → ‖N y - ystar‖ ≤ r₀ := by
    intro y hy
    calc ‖N y - ystar‖ = ‖(N y - N ystar) + (N ystar - ystar)‖ := by congr 1; abel
      _ ≤ 2⁻¹ * ‖y - ystar‖ + ε * ‖B‖ * CS / T :=
          (norm_add_le _ _).trans (add_le_add (hNlip y ystar hy (by simp [hr₀.le])) hN0)
      _ ≤ r₀ := by linarith
  -- the fixed point
  have hmaps : MapsTo N (Metric.closedBall ystar r₀) (Metric.closedBall ystar r₀) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    exact hball y hy
  have hcontr : ContractingWith 2⁻¹ (hmaps.restrict N _ _) := by
    refine ⟨by rw [inv_lt_one₀ (by norm_num)]; norm_num, ?_⟩
    apply LipschitzOnWith.mapsToRestrict
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    rw [Metric.mem_closedBall, dist_eq_norm] at hy hz
    rw [dist_eq_norm, dist_eq_norm]
    have : ((2⁻¹ : NNReal) : ℝ) = 2⁻¹ := by norm_num
    rw [this]
    exact hNlip y z hy hz
  obtain ⟨yε, hyε, hfix, -, -⟩ := hcontr.exists_fixedPoint' Metric.isClosed_closedBall.isComplete
    hmaps (Metric.mem_closedBall_self hr₀.le) (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_eq_norm] at hyε
  have hfix' : N yε = yε := hfix
  -- the fixed point is a periodic initial state
  have hper0 : X yε T = yε := by
    have h1 : B (fieldAverage f T yε + (ε * T)⁻¹ • Ψ yε) = 0 := by
      have := hfix'; simp only [hN] at this; exact sub_eq_self.mp this
    have h2 : fieldAverage f T yε + (ε * T)⁻¹ • Ψ yε = 0 := by
      rw [← hAB (fieldAverage f T yε + (ε * T)⁻¹ • Ψ yε), h1, map_zero]
    have h3 : Ψ yε = -((ε * T) • fieldAverage f T yε) := by
      have := congrArg (fun v => (ε * T) • v) h2
      simp only [smul_add, smul_smul, mul_inv_cancel₀ hεT.ne', one_smul, smul_zero] at this
      exact eq_neg_of_add_eq_zero_right this
    have h4 : X yε T - yε - (ε * T) • fieldAverage f T yε =
        -((ε * T) • fieldAverage f T yε) := h3
    have := congrArg (fun v => v + yε + (ε * T) • fieldAverage f T yε) h4
    rw [show X yε T - yε - (ε * T) • fieldAverage f T yε + yε + (ε * T) • fieldAverage f T yε =
      X yε T by abel, show -((ε * T) • fieldAverage f T yε) + yε + (ε * T) • fieldAverage f T yε =
      yε by abel] at this
    exact this
  have hyεb : ‖yε - ystar‖ ≤ 2 * (ε * ‖B‖ * CS / T) := by
    have h := hNlip yε ystar hyε (by simp [hr₀.le])
    rw [hfix'] at h
    have : ‖yε - ystar‖ ≤ 2⁻¹ * ‖yε - ystar‖ + ε * ‖B‖ * CS / T :=
      calc ‖yε - ystar‖ = ‖(yε - N ystar) + (N ystar - ystar)‖ := by congr 1; abel
        _ ≤ ‖yε - N ystar‖ + ‖N ystar - ystar‖ := norm_add_le _ _
        _ ≤ 2⁻¹ * ‖yε - ystar‖ + ε * ‖B‖ * CS / T := add_le_add h hN0
    linarith
  -- the periodic solution
  have hx := hX yε
  have hxper : ∀ t, X yε (t + T) = X yε t := by
    have hshift : ∀ t, HasDerivAt (fun t => X yε (t + T))
        (ε • f (X yε (t + T)) t + ε ^ 2 • r (X yε (t + T)) t) t := by
      intro t
      have h := (hx (t + T)).comp_add_const t T
      rw [hf.2.2.2.1, hr.2.2.2.1] at h
      exact h
    have := full_solution_unique hf.2.2.2.2.1 hr.2.2.2.2.1 hℓ hℓr hε.le hshift hx (t₀ := 0)
      (by show X yε (0 + T) = X yε 0; rw [zero_add, hper0, hX0])
    exact fun t => congrFun this t
  refine ⟨X yε, hx, hxper, fun t => ?_, fun z hz hzT hz0 => ?_⟩
  · obtain ⟨t', ht', hxt⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) (f := X yε) hxper hT t
    rw [hxt]
    have hd := solution_drift_le hf.2.2.2.2.2 hr.2.2.2.2.2 hε.le hε1 hx ht'.1
    rw [sub_zero, hX0] at hd
    calc ‖X yε t' - ystar‖ = ‖(X yε t' - yε) + (yε - ystar)‖ := by congr 1; abel
      _ ≤ ε * (M + Mr) * t' + 2 * (ε * ‖B‖ * CS / T) := (norm_add_le _ _).trans (add_le_add hd hyεb)
      _ ≤ ε * (M + Mr) * T + 2 * (ε * ‖B‖ * CS / T) := by
          gcongr
          exact ht'.2.le
      _ = ε * (2 * ‖B‖ * CS / T + (M + Mr) * T) := by ring
  · have hzX : z = X (z 0) := full_solution_unique hf.2.2.2.2.1 hr.2.2.2.2.1 hℓ hℓr hε.le hz
      (hX (z 0)) (t₀ := 0) (by rw [hX0])
    have hNz : N (z 0) = z 0 := by
      have hΨz : Ψ (z 0) = -((ε * T) • fieldAverage f T (z 0)) := by
        simp only [hΨ]
        rw [← hzX, hzT]; abel
      simp only [hN, hΨz, smul_neg, smul_smul, inv_mul_cancel₀ hεT.ne', one_smul, add_neg_cancel,
        map_zero, sub_zero]
    have hz0' : z 0 = yε := by
      have h := hNlip (z 0) yε hz0 hyε
      rw [hNz, hfix'] at h
      have : ‖z 0 - yε‖ = 0 := by linarith [norm_nonneg (z 0 - yε)]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    rw [hzX, hz0']

end Orbit

end powerlib.Averaging
