import theorem.Averaging.PeriodicOrbits
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! # The near-identity transformation of first-order averaging

`theorem/Averaging/PeriodicOrbits.lean` works with the period map of `ẋ = ε f(x, t)` and never
changes coordinates. Here the classical near-identity transformation of the averaging method is
constructed explicitly: `x = y + ε u(y, t)` with the generator
`u(y, t) = ∫₀ᵗ (f(y, s) − f̄(y)) ds`, the `t`-primitive of the oscillating part of the field. It is
`T`-periodic in `t`, vanishes at the sampling times `kT` (so the stroboscopic samples of `x` and
`y` coincide, `strobGen_sample`: this is why the period map of `PeriodicOrbits` carries the
averaged field directly, `Averaging.period_step_le`), bounded by `2MT`, `2ℓT`-Lipschitz, and
differentiable in `y` with the derivative `∫₀ᵗ Df(y, s) ds − (t/T) ∫₀ᵀ Df(y, s) ds` (differentiation
under the integral sign), of norm at most `2ℓT`; `I + ε D_y u` is invertible for `2εℓT < 1`. The
generator is jointly differentiable along curves (continuous partial derivatives, Mathlib
`hasStrictFDerivAt_uncurry_coprod`), and in the new coordinates the equation reads
`(I + ε D_y u) ẏ = ε f̄(y) + ε (f(y + εu, t) − f(y, t))`, so that
`‖ẏ − ε f̄(y)‖ ≤ ε² R_ε` with the explicit `R_ε = 2ℓMT + 2ℓT(M + 2εℓMT)/(1 − 2εℓT)`. The
zero-mean generator `u − ⟨u⟩` (`zeroMeanGen`) differs from `u` by a function of `y` alone.

Scope.
* `ẋ = ε f(x, t)` on a real Banach space `E`, `f` with the hypotheses of
  `Averaging.kbm_first_order` (period `T > 0`, continuity, `T`-periodicity, global Lipschitz
  constant `ℓ`, bound `M`), written out in every statement.
* For the derivative in the state: `f(·, t)` has the derivative `Df(x, t)` everywhere and `Df` is
  jointly continuous.
* The transformed equation is stated for a differentiable curve `y` whose transform
  `x = y + ε u(y, t)` solves `ẋ = ε f(x, t)`; the remainder is bounded, its Lipschitz constant in
  `y` is not derived here. The transformed curve of every solution, its derivative, the
  remainder field and its Lipschitz constant are `theorem/Averaging/NearIdentityInverse.lean`
  (`transformed_solution`, `hasDerivAt_transformed_solution`, `norm_nearIdRemainder_sub_le`).
* Generic mathematics, no model family.

Source: Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations*
(the averaging change of variables); Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear
Dynamical Systems*, Ch. 2.8–2.9 (the near-identity transformation `x = y + εu(y, t)` with the
periodic generator); Hale, *Ordinary Differential Equations*, Ch. V; work-sync
theory/T-averaging-method.md §1.2; Mathlib `hasFDerivAt_integral_of_dominated_of_fderiv_le`,
`continuous_parametric_primitive_of_continuous`, `hasStrictFDerivAt_uncurry_coprod`.

Results.
* `strobGen`, `strobGen_eq`, `hasDerivAt_strobGen_time`, `strobGen_periodic`, `strobGen_sample` —
  the generator, its `t`-derivative `f − f̄`, periodicity, `u(y, kT) = 0`.
* `zeroMeanGen`, `zeroMeanGen_periodic`, `hasDerivAt_zeroMeanGen_time`, `fieldAverage_zeroMeanGen`
  — the zero-mean generator.
* `norm_strobGen_le`, `norm_strobGen_sub_le` — `‖u‖ ≤ 2MT`, `u` is `2ℓT`-Lipschitz.
* `strobGenD`, `hasFDerivAt_strobGen`, `strobGenD_periodic`, `norm_strobGenD_le` — the derivative
  in the state and `‖D_y u‖ ≤ 2ℓT`.
* `isUnit_one_add_strobGenD` — `I + ε D_y u` is invertible for `2εℓT < 1`.
* `hasDerivAt_strobGen_comp` — the chain rule along a curve.
* `transformed_eq`, `transformed_le` — the transformed equation and `‖ẏ − ε f̄(y)‖ ≤ ε² R_ε`.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology intervalIntegral MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ → E} {T ℓ M : ℝ}

/-- The generator `u(y, t) = ∫₀ᵗ (f(y, s) − f̄(y)) ds` of the near-identity transformation. -/
def strobGen (f : E → ℝ → E) (T : ℝ) (y : E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, (f y s - fieldAverage f T y)

@[tmio T, powerlib_foundation] theorem strobGen_eq
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y : E) (t : ℝ) :
    strobGen f T y t = (∫ s in (0 : ℝ)..t, f y s) - t • fieldAverage f T y := by
  rw [strobGen, intervalIntegral.integral_sub
    ((PeriodicField.continuous_snd hf y).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero]

/-- The `t`-derivative of the generator is the oscillating part `f(y, t) − f̄(y)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_strobGen_time
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y : E) (t : ℝ) :
    HasDerivAt (strobGen f T y) (f y t - fieldAverage f T y) t :=
  (((PeriodicField.continuous_snd hf y).sub continuous_const).integral_hasStrictDerivAt 0
    t).hasDerivAt

/-- The generator is `T`-periodic in time. -/
@[tmio T, powerlib_foundation] theorem strobGen_periodic
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y : E) (t : ℝ) :
    strobGen f T y (t + T) = strobGen f T y t := by
  have hc : Continuous fun s => f y s - fieldAverage f T y :=
    (PeriodicField.continuous_snd hf y).sub continuous_const
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 t) (hc.intervalIntegrable (μ := volume) t (t + T))
  have hzero : ∫ s in t..t + T, (f y s - fieldAverage f T y) = 0 := by
    rw [intervalIntegral.integral_sub ((PeriodicField.continuous_snd hf y).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), periodIntegral_eq hf y t,
      intervalIntegral.integral_const, show t + T - t = T by ring, sub_self]
  simp only [strobGen]
  rw [← hsplit, hzero, add_zero]

/-- **The generator vanishes at the sampling times**: `u(y, kT) = 0`, so the stroboscopic samples
of `x = y + ε u(y, t)` and `y` coincide. -/
@[tmio T, powerlib_foundation] theorem strobGen_sample
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y : E) (k : ℕ) :
    strobGen f T y (k * T) = 0 := by
  induction k with
  | zero => simp [strobGen]
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℝ) * T = k * T + T by push_cast; ring, strobGen_periodic hf, ih]

/-- The zero-mean generator `u(y, t) − ⟨u(y, ·)⟩`. -/
def zeroMeanGen (f : E → ℝ → E) (T : ℝ) (y : E) (t : ℝ) : E :=
  strobGen f T y t - fieldAverage (strobGen f T) T y

@[tmio T, powerlib_foundation] theorem zeroMeanGen_periodic
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y : E) (t : ℝ) :
    zeroMeanGen f T y (t + T) = zeroMeanGen f T y t := by
  rw [zeroMeanGen, zeroMeanGen, strobGen_periodic hf]

@[tmio T, powerlib_foundation] theorem hasDerivAt_zeroMeanGen_time
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y : E) (t : ℝ) :
    HasDerivAt (zeroMeanGen f T y) (f y t - fieldAverage f T y) t := by
  have h := (hasDerivAt_strobGen_time hf y t).sub_const (fieldAverage (strobGen f T) T y)
  exact h

/-- The zero-mean generator has period average zero. -/
@[tmio T, powerlib_foundation] theorem fieldAverage_zeroMeanGen
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y : E) :
    fieldAverage (zeroMeanGen f T) T y = 0 := by
  have hc : Continuous (strobGen f T y) := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_strobGen_time hf y t).continuousAt
  simp only [fieldAverage, zeroMeanGen]
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_sub, smul_smul, inv_mul_cancel₀ hf.1.ne',
    one_smul, sub_self]

/-- **The generator is bounded**: `‖u(y, t)‖ ≤ 2MT` for all `t`. -/
@[tmio T, powerlib_foundation] theorem norm_strobGen_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y : E) (t : ℝ) :
    ‖strobGen f T y t‖ ≤ 2 * M * T := by
  have hP : Function.Periodic (strobGen f T y) T := fun t => strobGen_periodic hf y t
  obtain ⟨t', ht', hxt⟩ := hP.exists_mem_Ico₀ hf.1 t
  rw [hxt, strobGen]
  have hb : ∀ s ∈ Ι (0 : ℝ) t', ‖f y s - fieldAverage f T y‖ ≤ 2 * M := fun s _ =>
    (norm_sub_le _ _).trans (by linarith [hf.2.2.2.2.2 y s, norm_fieldAverage_le hf y])
  have h := norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht'.1] at h
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 y 0)
  exact h.trans (by nlinarith [ht'.2])

/-- **The generator is `2ℓT`-Lipschitz in the state.** -/
@[tmio T, powerlib_foundation] theorem norm_strobGen_sub_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y z : E) (t : ℝ) :
    ‖strobGen f T y t - strobGen f T z t‖ ≤ 2 * ℓ * T * ‖y - z‖ := by
  have hP : Function.Periodic (fun t => strobGen f T y t - strobGen f T z t) T := fun t => by
    simp only [strobGen_periodic hf]
  obtain ⟨t', ht', hxt⟩ := hP.exists_mem_Ico₀ hf.1 t
  have hcy : Continuous fun s => f y s - fieldAverage f T y :=
    (PeriodicField.continuous_snd hf y).sub continuous_const
  have hcz : Continuous fun s => f z s - fieldAverage f T z :=
    (PeriodicField.continuous_snd hf z).sub continuous_const
  rw [hxt, strobGen, strobGen, ← intervalIntegral.integral_sub (hcy.intervalIntegrable 0 t')
    (hcz.intervalIntegrable 0 t')]
  have hb : ∀ s ∈ Ι (0 : ℝ) t', ‖(f y s - fieldAverage f T y) - (f z s - fieldAverage f T z)‖ ≤
      2 * ℓ * ‖y - z‖ := fun s _ => by
    have e : (f y s - fieldAverage f T y) - (f z s - fieldAverage f T z) =
        (f y s - f z s) - (fieldAverage f T y - fieldAverage f T z) := by abel
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith [hf.2.2.2.2.1 y z s, fieldAverage_lipschitz hf y z])
  have h := norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht'.1] at h
  have : 0 ≤ 2 * ℓ * ‖y - z‖ := by have := hf.2.1; positivity
  exact h.trans (by nlinarith [ht'.2])

variable {Df : E → ℝ → E →L[ℝ] E}

/-- The derivative of the generator in the state:
`∫₀ᵗ Df(y, s) ds − (t/T) ∫₀ᵀ Df(y, s) ds`. -/
def strobGenD (Df : E → ℝ → E →L[ℝ] E) (T : ℝ) (y : E) (t : ℝ) : E →L[ℝ] E :=
  (∫ s in (0 : ℝ)..t, Df y s) - (t / T) • ∫ s in (0 : ℝ)..T, Df y s

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] private theorem hasFDerivAt_primitive
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    (y : E) (b : ℝ) :
    HasFDerivAt (fun y => ∫ s in (0 : ℝ)..b, f y s) (∫ s in (0 : ℝ)..b, Df y s) y := by
  have hlip : ∀ s, LipschitzWith (Real.toNNReal ℓ) fun y => f y s := fun s =>
    LipschitzWith.of_dist_le_mul fun x z => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hf.2.1]; exact hf.2.2.2.2.1 x z s
  have hbound : ∀ x s, ‖Df x s‖ ≤ ℓ := fun x s => by
    have := (hD x s).le_of_lipschitz (hlip s)
    rwa [Real.coe_toNNReal _ hf.2.1] at this
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => ℓ)
    (s := univ) univ_mem ?_ ((PeriodicField.continuous_snd hf y).intervalIntegrable _ _) ?_
    (Eventually.of_forall fun s _ x _ => hbound x s) intervalIntegrable_const
    (Eventually.of_forall fun s _ x _ => hD x s)
  · exact Eventually.of_forall fun x => (PeriodicField.continuous_snd hf x).aestronglyMeasurable
  · exact (hDc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

/-- **Differentiation under the integral sign**: the generator is differentiable in the state with
derivative `strobGenD`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_strobGen
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    (y : E) (t : ℝ) : HasFDerivAt (fun y => strobGen f T y t) (strobGenD Df T y t) y := by
  have e : (fun y => strobGen f T y t) =
      fun y => (∫ s in (0 : ℝ)..t, f y s) - (t / T) • ∫ s in (0 : ℝ)..T, f y s := by
    funext z
    rw [strobGen_eq hf, fieldAverage, smul_smul, div_eq_mul_inv]
  rw [e]
  exact (hasFDerivAt_primitive hf hD hDc y t).sub
    ((hasFDerivAt_primitive hf hD hDc y T).const_smul (t / T))

omit [CompleteSpace E] in
/-- The derivative of the state is `T`-periodic in `s` (uniqueness of derivatives). -/
@[tmio T, powerlib_foundation] private theorem Df_periodic
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (x : E) (s : ℝ) :
    Df x (s + T) = Df x s := by
  have h := hD x (s + T)
  simp only [hf.2.2.2.1] at h
  exact h.unique (hD x s)

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem strobGenD_periodic
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    (y : E) (t : ℝ) : strobGenD Df T y (t + T) = strobGenD Df T y t := by
  have hc : Continuous (Df y) := hDc.comp (continuous_const.prodMk continuous_id)
  have hP : Function.Periodic (Df y) T := fun s => Df_periodic hf hD y s
  rw [strobGenD, strobGenD, ← intervalIntegral.integral_add_adjacent_intervals (b := t)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), hP.intervalIntegral_add_eq t 0,
    zero_add, add_div, div_self hf.1.ne', add_smul, one_smul]
  abel

omit [CompleteSpace E] in
/-- **`‖D_y u(y, t)‖ ≤ 2ℓT`** for all `t`. -/
@[tmio T, powerlib_foundation] theorem norm_strobGenD_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    (y : E) (t : ℝ) : ‖strobGenD Df T y t‖ ≤ 2 * ℓ * T := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hlip : ∀ s, LipschitzWith (Real.toNNReal ℓ) fun y => f y s := fun s =>
    LipschitzWith.of_dist_le_mul fun x z => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hℓ]; exact hf.2.2.2.2.1 x z s
  have hbound : ∀ x s, ‖Df x s‖ ≤ ℓ := fun x s => by
    have := (hD x s).le_of_lipschitz (hlip s)
    rwa [Real.coe_toNNReal _ hℓ] at this
  have hP : Function.Periodic (strobGenD Df T y) T := fun t => strobGenD_periodic hf hD hDc y t
  obtain ⟨t', ht', hxt⟩ := hP.exists_mem_Ico₀ hT t
  rw [hxt, strobGenD]
  have h1 := norm_integral_le_of_norm_le_const (a := 0) (b := t') (f := Df y) (C := ℓ)
    (fun s _ => hbound y s)
  have h2 := norm_integral_le_of_norm_le_const (a := 0) (b := T) (f := Df y) (C := ℓ)
    (fun s _ => hbound y s)
  rw [sub_zero, abs_of_nonneg ht'.1] at h1
  rw [sub_zero, abs_of_pos hT] at h2
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg ht'.1 hT.le)]
  have h3 : t' / T * ‖∫ s in (0 : ℝ)..T, Df y s‖ ≤ t' / T * (ℓ * T) :=
    mul_le_mul_of_nonneg_left h2 (div_nonneg ht'.1 hT.le)
  have h4 : t' / T * (ℓ * T) = ℓ * t' := by field_simp
  nlinarith [ht'.2]

/-- **`I + ε D_y u` is invertible** for `2εℓT < 1` (Neumann series in `E →L[ℝ] E`). -/
@[tmio T, powerlib_foundation] theorem isUnit_one_add_strobGenD
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {ε : ℝ} (hε : 0 ≤ ε) (hεℓ : 2 * ε * ℓ * T < 1) (y : E) (t : ℝ) :
    IsUnit (1 + ε • strobGenD Df T y t) := by
  have h : ‖-(ε • strobGenD Df T y t)‖ < 1 := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hε]
    calc ε * ‖strobGenD Df T y t‖ ≤ ε * (2 * ℓ * T) :=
          mul_le_mul_of_nonneg_left (norm_strobGenD_le hf hD hDc y t) hε
      _ < 1 := by linarith
  have hu := (Units.oneSub _ h).isUnit
  rwa [Units.val_oneSub, sub_neg_eq_add] at hu

/-- **The chain rule for the generator along a curve** (continuous partial derivatives,
`hasStrictFDerivAt_uncurry_coprod`): `d/dt u(y(t), t) = D_y u(y, t)[ẏ] + f(y, t) − f̄(y)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_strobGen_comp
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {y : ℝ → E} {y' : E} {t : ℝ} (hy : HasDerivAt y y' t) :
    HasDerivAt (fun t => strobGen f T (y t) t)
      (strobGenD Df T (y t) t y' + (f (y t) t - fieldAverage f T (y t))) t := by
  set f₂ : E → ℝ → ℝ →L[ℝ] E := fun x s =>
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f x s - fieldAverage f T x) with hf₂
  have hcD : Continuous (Function.uncurry (strobGenD Df T)) := by
    have h1 : Continuous fun p : E × ℝ => ∫ s in (0 : ℝ)..p.2, Df p.1 s :=
      continuous_parametric_primitive_of_continuous hDc
    have h2 : Continuous fun p : E × ℝ => ∫ s in (0 : ℝ)..T, Df p.1 s :=
      continuous_parametric_intervalIntegral_of_continuous' hDc 0 T |>.comp continuous_fst
    exact h1.sub ((continuous_snd.div_const T).smul h2)
  have hcf : Continuous fun p : E × ℝ => f p.1 p.2 - fieldAverage f T p.1 :=
    hf.2.2.1.sub ((fieldAverage_continuous hf).comp continuous_fst)
  have hc₂ : Continuous (Function.uncurry f₂) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).continuous.comp hcf
  have hS := hasStrictFDerivAt_uncurry_coprod (f := strobGen f T) (f₁ := strobGenD Df T)
    (f₂ := f₂) (u := (y t, t))
    (Eventually.of_forall fun v => hasFDerivAt_strobGen hf hD hDc v.1 v.2)
    (Eventually.of_forall fun v => (hasDerivAt_strobGen_time hf v.1 v.2).hasFDerivAt)
    hcD.continuousAt hc₂.continuousAt
  have hcurve : HasDerivAt (fun t => (y t, t)) (y', (1 : ℝ)) t := hy.prodMk (hasDerivAt_id t)
  have h := HasFDerivAt.comp_hasDerivAt (f := fun s => (y s, s)) t hS.hasFDerivAt hcurve
  have h' : HasDerivAt (fun t => strobGen f T (y t) t)
      (((strobGenD Df T (y t) t).coprod (f₂ (y t) t)) (y', 1)) t := h
  refine h'.congr_deriv ?_
  rw [ContinuousLinearMap.coprod_apply]
  simp [hf₂]

/-- **The transformed equation.** If `y` is differentiable and its transform
`x = y + ε u(y, t)` solves `ẋ = ε f(x, t)`, then
`ẏ + ε D_y u(y, t)[ẏ] = ε f̄(y) + ε (f(y + εu, t) − f(y, t))`. -/
@[tmio T, powerlib_foundation] theorem transformed_eq
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {ε : ℝ} {y y' : ℝ → E} (hy : ∀ t, HasDerivAt y (y' t) t)
    (hx : ∀ t, HasDerivAt (fun t => y t + ε • strobGen f T (y t) t)
      (ε • f (y t + ε • strobGen f T (y t) t) t) t) (t : ℝ) :
    y' t + ε • strobGenD Df T (y t) t (y' t) = ε • fieldAverage f T (y t) +
      ε • (f (y t + ε • strobGen f T (y t) t) t - f (y t) t) := by
  have h := (hy t).add ((hasDerivAt_strobGen_comp hf hD hDc (hy t)).const_smul ε)
  have heq := h.unique (hx t)
  calc y' t + ε • strobGenD Df T (y t) t (y' t) =
      (y' t + ε • (strobGenD Df T (y t) t (y' t) + (f (y t) t - fieldAverage f T (y t)))) -
        ε • (f (y t) t - fieldAverage f T (y t)) := by simp only [smul_add]; abel
    _ = ε • f (y t + ε • strobGen f T (y t) t) t - ε • (f (y t) t - fieldAverage f T (y t)) := by
        rw [heq]
    _ = _ := by simp only [smul_sub]; abel

/-- **The transformed equation is the averaged equation up to `ε²`**: under `2εℓT < 1`,
`0 ≤ ε`, `‖ẏ − ε f̄(y)‖ ≤ ε² (2ℓMT + 2ℓT (M + 2εℓMT)/(1 − 2εℓT))`. -/
@[tmio T, powerlib_foundation] theorem transformed_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {ε : ℝ} (hε : 0 ≤ ε) (hεℓ : 2 * ε * ℓ * T < 1) {y y' : ℝ → E}
    (hy : ∀ t, HasDerivAt y (y' t) t)
    (hx : ∀ t, HasDerivAt (fun t => y t + ε • strobGen f T (y t) t)
      (ε • f (y t + ε • strobGen f T (y t) t) t) t) (t : ℝ) :
    ‖y' t - ε • fieldAverage f T (y t)‖ ≤
      ε ^ 2 * (2 * ℓ * M * T + 2 * ℓ * T * (M + 2 * ε * ℓ * M * T) / (1 - 2 * ε * ℓ * T)) := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (y t) 0)
  have he := transformed_eq hf hD hDc hy hx t
  set D := strobGenD Df T (y t) t with hDdef
  set Δ := f (y t + ε • strobGen f T (y t) t) t - f (y t) t with hΔ
  have hDn : ‖D‖ ≤ 2 * ℓ * T := norm_strobGenD_le hf hD hDc (y t) t
  have hΔn : ‖Δ‖ ≤ ε * (2 * ℓ * M * T) := by
    refine (hf.2.2.2.2.1 _ _ t).trans ?_
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε]
    have := norm_strobGen_le hf (y t) t
    calc ℓ * (ε * ‖strobGen f T (y t) t‖) ≤ ℓ * (ε * (2 * M * T)) := by gcongr
      _ = ε * (2 * ℓ * M * T) := by ring
  have hfb := norm_fieldAverage_le hf (y t)
  have hpos : 0 < 1 - 2 * ε * ℓ * T := by linarith
  -- an a-priori bound on `ẏ`
  have hy' : ‖y' t‖ ≤ ε * (M + 2 * ε * ℓ * M * T) / (1 - 2 * ε * ℓ * T) := by
    have e : y' t = ε • fieldAverage f T (y t) + ε • Δ - ε • D (y' t) := by
      rw [← he]; abel
    have h1 : ‖y' t‖ ≤ ε * M + ε * (ε * (2 * ℓ * M * T)) + ε * (2 * ℓ * T) * ‖y' t‖ := by
      conv_lhs => rw [e]
      refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left hfb hε
      · rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left hΔn hε
      · rw [norm_smul, Real.norm_of_nonneg hε, mul_assoc]
        exact mul_le_mul_of_nonneg_left ((D.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hDn (norm_nonneg _))) hε
    rw [le_div_iff₀ hpos]
    nlinarith
  have e2 : y' t - ε • fieldAverage f T (y t) = ε • Δ - ε • D (y' t) := by
    calc y' t - ε • fieldAverage f T (y t) =
        (y' t + ε • D (y' t)) - ε • D (y' t) - ε • fieldAverage f T (y t) := by abel
      _ = (ε • fieldAverage f T (y t) + ε • Δ) - ε • D (y' t) - ε • fieldAverage f T (y t) := by
          rw [he]
      _ = ε • Δ - ε • D (y' t) := by abel
  rw [e2]
  calc ‖ε • Δ - ε • D (y' t)‖ ≤ ε * (ε * (2 * ℓ * M * T)) +
        ε * (2 * ℓ * T * (ε * (M + 2 * ε * ℓ * M * T) / (1 - 2 * ε * ℓ * T))) := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left hΔn hε
        · rw [norm_smul, Real.norm_of_nonneg hε]
          refine mul_le_mul_of_nonneg_left ((D.le_opNorm _).trans ?_) hε
          exact mul_le_mul hDn hy' (norm_nonneg _) (by positivity)
    _ = ε ^ 2 * (2 * ℓ * M * T + 2 * ℓ * T * (M + 2 * ε * ℓ * M * T) / (1 - 2 * ε * ℓ * T)) := by
        field_simp

end powerlib.Averaging
