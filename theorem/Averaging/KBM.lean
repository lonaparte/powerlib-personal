import dependencies.Mathlib
import theorem.Attributes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.ODE.Gronwall

/-! # First-order periodic averaging (Krylov–Bogoliubov–Mitropolsky)

Foundation layer: the first-order averaging theorem for a fast periodic forcing, with an explicit
error constant. No engineering model is fixed here.

Setting. `ẋ = ε f(x, t)` on a real Banach space `E`, with `f` jointly continuous, `T`-periodic in
`t` (`T > 0`), globally Lipschitz in `x` (constant `ℓ ≥ 0`, uniformly in `t`) and bounded by `M`.
These hypotheses on the fast-periodic field are written out in every statement as the single
hypothesis `hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
(∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M` (the former structure
`PeriodicField` with fields `hT`, `hℓ`, `cont`, `per`, `lip`, `bound` is removed: its fields
quantify over time, and behaviour is defined only in the semantic layer; the namespace lemmas
`PeriodicField.continuous_snd`, `PeriodicField.M_nonneg` keep their names). The averaged field
is `f̄(x) = (1/T) ∫₀ᵀ f(x, s) ds` (`fieldAverage`) and the averaged system is `x̄̇ = ε f̄(x̄)`.
Solutions are global solutions (they exist under the global Lipschitz bound); only the window
`[0, L/ε]` is used.

Results.
* `periodIntegral_eq`: `∫ₐ^{a+T} f(y, s) ds = T f̄(y)` for every `a` (periodicity);
  `norm_fieldAverage_le`, `fieldAverage_lipschitz`: `‖f̄‖ ≤ M`, `f̄` is `ℓ`-Lipschitz.
* `norm_integral_osc_le`: the oscillating part `g(s) = f(x̄(s), s) − f̄(x̄(s))` has
  `‖∫₀ᵗ g‖ ≤ 2ℓMLT + 2MT` whenever `0 ≤ t` and `εt ≤ L` (period-by-period cancellation plus the
  slow drift `‖x̄(s) − x̄(r)‖ ≤ εM|s − r|`).
* `kbm_first_order`: if `x(0) = x̄(0)`, then for every `t ∈ [0, L/ε]`
  `‖x(t) − x̄(t)‖ ≤ (2ℓMLT + 2MT) e^{ℓL} ε` — the `O(ε)` error on the `O(1/ε)` time window
  (Grönwall applied to `x − x̄ − ε∫₀ᵗ g`).

Not formalized: the almost-periodic case, higher-order averaging, and the domain-restricted
(local Lipschitz, `x̄` staying in a compact set with margin) version; here the bounds are global.

Correction (T-averaging-method.md §1.9 / §1.7, recorded only): in the almost-periodic case the
error is in general only `O(δ(ε))` with `δ(ε) → 0` (not `O(ε)`); the second-order averaged field
of §1.7 omits the `∂_ε f` contribution.

Source: work-sync theory/T-averaging-method.md §1.1–1.3 (standard form, averaged field, KBM
first-order theorem `‖x(t) − x̄(t)‖ ≤ Cε` on `[0, L/ε]`), §1.8.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology intervalIntegral
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The averaged field `f̄(x) = (1/T) ∫₀ᵀ f(x, s) ds`. -/
def fieldAverage (f : E → ℝ → E) (T : ℝ) (x : E) : E := T⁻¹ • ∫ s in (0 : ℝ)..T, f x s

variable {f : E → ℝ → E} {T ℓ M : ℝ}

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[powerlib_foundation] theorem PeriodicField.continuous_snd
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (x : E) :
    Continuous (f x) :=
  hf.2.2.1.comp (continuous_const.prodMk continuous_id)

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[powerlib_foundation] theorem PeriodicField.M_nonneg
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) [Nonempty E] :
    0 ≤ M :=
  (norm_nonneg _).trans (hf.2.2.2.2.2 (Classical.arbitrary E) 0)

omit [CompleteSpace E] in
/-- Periodicity: the integral over any period equals `T f̄(y)`. -/
@[powerlib_foundation] theorem periodIntegral_eq
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y : E) (a : ℝ) :
    ∫ s in a..a + T, f y s = T • fieldAverage f T y := by
  have hP : Function.Periodic (f y) T := fun t => hf.2.2.2.1 y t
  rw [hP.intervalIntegral_add_eq a 0, zero_add, fieldAverage, smul_smul,
    mul_inv_cancel₀ hf.1.ne', one_smul]

omit [CompleteSpace E] in
@[powerlib_foundation] theorem norm_fieldAverage_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (x : E) :
    ‖fieldAverage f T x‖ ≤ M := by
  rw [fieldAverage, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hf.1.le)]
  have h := norm_integral_le_of_norm_le_const (a := 0) (b := T) (f := f x) (C := M)
    (fun s _ => hf.2.2.2.2.2 x s)
  rw [sub_zero, abs_of_pos hf.1] at h
  calc T⁻¹ * ‖∫ s in (0 : ℝ)..T, f x s‖ ≤ T⁻¹ * (M * T) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hf.1.le)
    _ = M := by field_simp [hf.1.ne']

omit [CompleteSpace E] in
@[powerlib_foundation] theorem fieldAverage_lipschitz
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (x y : E) :
    ‖fieldAverage f T x - fieldAverage f T y‖ ≤ ℓ * ‖x - y‖ := by
  rw [fieldAverage, fieldAverage, ← smul_sub,
    ← integral_sub ((PeriodicField.continuous_snd hf x).intervalIntegrable _ _)
      ((PeriodicField.continuous_snd hf y).intervalIntegrable _ _),
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hf.1.le)]
  have h := norm_integral_le_of_norm_le_const (a := 0) (b := T) (f := fun s => f x s - f y s)
    (C := ℓ * ‖x - y‖) (fun s _ => hf.2.2.2.2.1 x y s)
  rw [sub_zero, abs_of_pos hf.1] at h
  calc T⁻¹ * ‖∫ s in (0 : ℝ)..T, f x s - f y s‖ ≤ T⁻¹ * (ℓ * ‖x - y‖ * T) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hf.1.le)
    _ = ℓ * ‖x - y‖ := by field_simp [hf.1.ne']

omit [CompleteSpace E] in
@[powerlib_foundation] theorem fieldAverage_continuous
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) :
    Continuous (fieldAverage f T) := by
  have : LipschitzWith (Real.toNNReal ℓ) (fieldAverage f T) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hf.2.1]
    exact fieldAverage_lipschitz hf x y
  exact this.continuous

omit [CompleteSpace E] in
/-- Slow drift of the averaged solution: `‖x̄(s) − x̄(r)‖ ≤ εM(s − r)` for `r ≤ s`. -/
@[powerlib_foundation] theorem averaged_drift
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) {ε : ℝ} (hε : 0 ≤ ε)
    {xbar : ℝ → E} (hxbar : ∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t) {r s : ℝ}
    (hrs : r ≤ s) : ‖xbar s - xbar r‖ ≤ ε * M * (s - r) := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := r) (b := s) (f := xbar)
    (f' := fun t => ε • fieldAverage f T (xbar t)) (C := ε * M)
    (fun t _ => (hxbar t).hasDerivWithinAt)
    (fun t _ => by
      rw [norm_smul, Real.norm_of_nonneg hε]
      exact mul_le_mul_of_nonneg_left (norm_fieldAverage_le hf _) hε)
    s ⟨hrs, le_rfl⟩
  exact h

/-- The oscillating part `g(s) = f(x̄(s), s) − f̄(x̄(s))`. -/
def oscPart (f : E → ℝ → E) (T : ℝ) (xbar : ℝ → E) (s : ℝ) : E :=
  f (xbar s) s - fieldAverage f T (xbar s)

omit [CompleteSpace E] in
@[powerlib_foundation] theorem oscPart_continuous
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) {xbar : ℝ → E}
    (hc : Continuous xbar) : Continuous (oscPart f T xbar) := by
  unfold oscPart
  exact (hf.2.2.1.comp (hc.prodMk continuous_id)).sub ((fieldAverage_continuous hf).comp hc)

omit [CompleteSpace E] in
@[powerlib_foundation] theorem norm_oscPart_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (xbar : ℝ → E)
    (s : ℝ) : ‖oscPart f T xbar s‖ ≤ 2 * M := by
  unfold oscPart
  calc ‖f (xbar s) s - fieldAverage f T (xbar s)‖
      ≤ ‖f (xbar s) s‖ + ‖fieldAverage f T (xbar s)‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hf.2.2.2.2.2 _ _) (norm_fieldAverage_le hf _)
    _ = 2 * M := by ring

/-- One period: `‖∫ₐ^{a+T} g‖ ≤ 2ℓεMT²`. -/
@[powerlib_foundation] theorem norm_period_osc_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) {ε : ℝ}
    (hε : 0 ≤ ε) {xbar : ℝ → E} (hxbar : ∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t)
    (a : ℝ) : ‖∫ s in a..a + T, oscPart f T xbar s‖ ≤ 2 * ℓ * ε * M * T ^ 2 := by
  have hc : Continuous xbar := continuous_iff_continuousAt.mpr fun t => (hxbar t).continuousAt
  set y := xbar a
  have hsplit : ∫ s in a..a + T, oscPart f T xbar s =
      (∫ s in a..a + T, (oscPart f T xbar s - (f y s - fieldAverage f T y))) +
        ∫ s in a..a + T, (f y s - fieldAverage f T y) := by
    rw [← integral_add]
    · congr 1; funext s; abel
    · exact ((oscPart_continuous hf hc).sub
        ((PeriodicField.continuous_snd hf y).sub continuous_const))
        |>.intervalIntegrable _ _
    · exact ((PeriodicField.continuous_snd hf y).sub continuous_const).intervalIntegrable _ _
  have hzero : ∫ s in a..a + T, (f y s - fieldAverage f T y) = 0 := by
    rw [integral_sub ((PeriodicField.continuous_snd hf y).intervalIntegrable _ _)
      intervalIntegrable_const,
      periodIntegral_eq hf y a, integral_const, add_sub_cancel_left, sub_self]
  rw [hsplit, hzero, add_zero]
  have hbound : ∀ s ∈ Ι a (a + T),
      ‖oscPart f T xbar s - (f y s - fieldAverage f T y)‖ ≤ 2 * ℓ * ε * M * T := by
    intro s hs
    rw [uIoc_of_le (by linarith [hf.1])] at hs
    have hdrift : ‖xbar s - y‖ ≤ ε * M * T := by
      have := averaged_drift hf hε hxbar hs.1.le
      calc ‖xbar s - y‖ ≤ ε * M * (s - a) := this
        _ ≤ ε * M * T := by
          apply mul_le_mul_of_nonneg_left (by linarith [hs.2])
          have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 y 0)
          positivity
    unfold oscPart
    calc ‖f (xbar s) s - fieldAverage f T (xbar s) - (f y s - fieldAverage f T y)‖
        = ‖(f (xbar s) s - f y s) - (fieldAverage f T (xbar s) - fieldAverage f T y)‖ := by
          congr 1; abel
      _ ≤ ‖f (xbar s) s - f y s‖ + ‖fieldAverage f T (xbar s) - fieldAverage f T y‖ :=
          norm_sub_le _ _
      _ ≤ ℓ * ‖xbar s - y‖ + ℓ * ‖xbar s - y‖ :=
          add_le_add (hf.2.2.2.2.1 _ _ _) (fieldAverage_lipschitz hf _ _)
      _ ≤ ℓ * (ε * M * T) + ℓ * (ε * M * T) := by
          gcongr <;> exact hf.2.1
      _ = 2 * ℓ * ε * M * T := by ring
  have h := norm_integral_le_of_norm_le_const hbound
  rw [show a + T - a = T by ring, abs_of_pos hf.1] at h
  calc _ ≤ 2 * ℓ * ε * M * T * T := h
    _ = 2 * ℓ * ε * M * T ^ 2 := by ring

/-- Accumulated oscillation: `‖∫₀ᵗ g‖ ≤ 2ℓMLT + 2MT` for `0 ≤ t`, `εt ≤ L`. -/
@[powerlib_foundation] theorem norm_integral_osc_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) {ε L : ℝ}
    (hε : 0 < ε) {xbar : ℝ → E}
    (hxbar : ∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t) {t : ℝ} (ht : 0 ≤ t)
    (htL : ε * t ≤ L) :
    ‖∫ s in (0 : ℝ)..t, oscPart f T xbar s‖ ≤ 2 * ℓ * M * L * T + 2 * M * T := by
  have hc : Continuous xbar := continuous_iff_continuousAt.mpr fun t => (hxbar t).continuousAt
  have hg := oscPart_continuous hf hc
  have hT := hf.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (xbar 0) 0)
  set N := ⌊t / T⌋₊
  have hNT : (N : ℝ) * T ≤ t := by
    have := Nat.floor_le (div_nonneg ht hT.le)
    calc (N : ℝ) * T ≤ t / T * T := mul_le_mul_of_nonneg_right this hT.le
      _ = t := by field_simp
  have hNT' : t - N * T ≤ T := by
    have := Nat.lt_floor_add_one (t / T)
    have : t < ((N : ℝ) + 1) * T := by
      calc t = t / T * T := by field_simp
        _ < ((N : ℝ) + 1) * T := mul_lt_mul_of_pos_right this hT
    linarith
  -- split at `N T`
  have hsplit : ∫ s in (0 : ℝ)..t, oscPart f T xbar s =
      (∫ s in (0 : ℝ)..(N * T), oscPart f T xbar s) + ∫ s in (N * T : ℝ)..t, oscPart f T xbar s :=
    (integral_add_adjacent_intervals (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)).symm
  have hsum : ∫ s in (0 : ℝ)..(N * T), oscPart f T xbar s =
      ∑ k ∈ Finset.range N, ∫ s in (k * T : ℝ)..((k + 1 : ℕ) * T), oscPart f T xbar s := by
    rw [sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) * T)
      (fun k _ => hg.intervalIntegrable _ _)]
    simp
  have hper : ∀ k ∈ Finset.range N,
      ‖∫ s in (k * T : ℝ)..((k + 1 : ℕ) * T), oscPart f T xbar s‖ ≤ 2 * ℓ * ε * M * T ^ 2 := by
    intro k _
    rw [show ((k + 1 : ℕ) : ℝ) * T = k * T + T by push_cast; ring]
    exact norm_period_osc_le hf hε.le hxbar _
  have h1 : ‖∫ s in (0 : ℝ)..(N * T), oscPart f T xbar s‖ ≤ N * (2 * ℓ * ε * M * T ^ 2) := by
    rw [hsum]
    calc ‖∑ k ∈ Finset.range N, ∫ s in (k * T : ℝ)..((k + 1 : ℕ) * T), oscPart f T xbar s‖
        ≤ ∑ k ∈ Finset.range N, ‖∫ s in (k * T : ℝ)..((k + 1 : ℕ) * T), oscPart f T xbar s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, 2 * ℓ * ε * M * T ^ 2 := Finset.sum_le_sum hper
      _ = N * (2 * ℓ * ε * M * T ^ 2) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h2 : ‖∫ s in (N * T : ℝ)..t, oscPart f T xbar s‖ ≤ 2 * M * T := by
    have := norm_integral_le_of_norm_le_const (a := N * T) (b := t)
      (fun s _ => norm_oscPart_le hf xbar s)
    rw [abs_of_nonneg (by linarith)] at this
    calc _ ≤ 2 * M * (t - N * T) := this
      _ ≤ 2 * M * T := mul_le_mul_of_nonneg_left hNT' (by positivity)
  have h3 : (N : ℝ) * (2 * ℓ * ε * M * T ^ 2) ≤ 2 * ℓ * M * L * T := by
    have hℓ := hf.2.1
    calc (N : ℝ) * (2 * ℓ * ε * M * T ^ 2) = 2 * ℓ * M * T * (ε * (N * T)) := by ring
      _ ≤ 2 * ℓ * M * T * (ε * t) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNT hε.le)
          positivity
      _ ≤ 2 * ℓ * M * T * L := mul_le_mul_of_nonneg_left htL (by positivity)
      _ = 2 * ℓ * M * L * T := by ring
  rw [hsplit]
  calc _ ≤ ‖∫ s in (0 : ℝ)..(N * T), oscPart f T xbar s‖ +
        ‖∫ s in (N * T : ℝ)..t, oscPart f T xbar s‖ := norm_add_le _ _
    _ ≤ 2 * ℓ * M * L * T + 2 * M * T := by linarith

/-- **First-order periodic averaging.** With `x(0) = x̄(0)`, for every `t ∈ [0, L/ε]`:
`‖x(t) − x̄(t)‖ ≤ (2ℓMLT + 2MT) e^{ℓL} ε`. -/
@[powerlib_foundation] theorem kbm_first_order
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) {ε L : ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L) {x xbar : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ε • f (x t) t) t)
    (hxbar : ∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t) (h0 : x 0 = xbar 0) :
    ∀ t ∈ Icc 0 (L / ε),
      ‖x t - xbar t‖ ≤ (2 * ℓ * M * L * T + 2 * M * T) * Real.exp (ℓ * L) * ε := by
  have hcbar : Continuous xbar := continuous_iff_continuousAt.mpr fun t => (hxbar t).continuousAt
  have hcx : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt
  have hg := oscPart_continuous hf hcbar
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (xbar 0) 0)
  have hℓ := hf.2.1
  set C₁ := 2 * ℓ * M * L * T + 2 * M * T
  have hC₁ : 0 ≤ C₁ := by have := hf.1; positivity
  set R : ℝ → E := fun t => ε • ∫ s in (0 : ℝ)..t, oscPart f T xbar s
  have hR : ∀ t, HasDerivAt R (ε • oscPart f T xbar t) t :=
    fun t => (hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_smul ε
  have hRb : ∀ t ∈ Icc 0 (L / ε), ‖R t‖ ≤ ε * C₁ := by
    intro t ht
    have htL : ε * t ≤ L := by
      have := ht.2; rw [le_div_iff₀ hε] at this; linarith
    simp only [R, norm_smul, Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left (norm_integral_osc_le hf hε hxbar ht.1 htL) hε.le
  set w : ℝ → E := fun t => (x t - xbar t) - R t
  have hw : ∀ t, HasDerivAt w (ε • (f (x t) t - f (xbar t) t)) t := by
    intro t
    have h := ((hx t).sub (hxbar t)).sub (hR t)
    convert h using 1
    simp only [oscPart, smul_sub]; abel
  have hw0 : w 0 = 0 := by simp [w, R, h0]
  have hwb : ∀ t ∈ Icc 0 (L / ε), ‖w t‖ ≤ ε * C₁ * (Real.exp (ℓ * L) - 1) := by
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := w)
      (f' := fun t => ε • (f (x t) t - f (xbar t) t)) (δ := 0) (K := ε * ℓ)
      (ε := ε * ℓ * (ε * C₁)) (a := 0) (b := L / ε)
      (fun t _ => (hw t).continuousAt.continuousWithinAt)
      (fun t _ => (hw t).hasDerivWithinAt) (by simp [hw0])
      (fun t ht => by
        rw [norm_smul, Real.norm_of_nonneg hε.le]
        have h1 := hf.2.2.2.2.1 (x t) (xbar t) t
        have h2 : ‖x t - xbar t‖ ≤ ‖w t‖ + ‖R t‖ := by
          have : x t - xbar t = w t + R t := by simp [w]
          rw [this]; exact norm_add_le _ _
        have h3 := hRb t ⟨ht.1, ht.2.le⟩
        calc ε * ‖f (x t) t - f (xbar t) t‖ ≤ ε * (ℓ * ‖x t - xbar t‖) :=
              mul_le_mul_of_nonneg_left h1 hε.le
          _ ≤ ε * (ℓ * (‖w t‖ + ε * C₁)) := by gcongr; linarith
          _ = ε * ℓ * ‖w t‖ + ε * ℓ * (ε * C₁) := by ring)
    intro t ht
    have h := hgr t ht
    rw [sub_zero] at h
    rcases eq_or_lt_of_le hℓ with hℓ0 | hℓpos
    · rw [← hℓ0] at h ⊢
      simp only [mul_zero, zero_mul, gronwallBound_K0, zero_add] at h
      simpa using h
    · rw [gronwallBound_of_K_ne_0 (by positivity)] at h
      simp only [zero_mul, zero_add] at h
      have hratio : ε * ℓ * (ε * C₁) / (ε * ℓ) = ε * C₁ := by field_simp
      rw [hratio] at h
      have hexp : Real.exp (ε * ℓ * t) ≤ Real.exp (ℓ * L) := by
        apply Real.exp_le_exp.mpr
        have := ht.2; rw [le_div_iff₀ hε] at this
        nlinarith
      calc ‖w t‖ ≤ ε * C₁ * (Real.exp (ε * ℓ * t) - 1) := h
        _ ≤ ε * C₁ * (Real.exp (ℓ * L) - 1) := by
            apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  intro t ht
  have : x t - xbar t = w t + R t := by simp [w]
  rw [this]
  calc ‖w t + R t‖ ≤ ‖w t‖ + ‖R t‖ := norm_add_le _ _
    _ ≤ ε * C₁ * (Real.exp (ℓ * L) - 1) + ε * C₁ := add_le_add (hwb t ht) (hRb t ht)
    _ = C₁ * Real.exp (ℓ * L) * ε := by ring

end powerlib.Averaging
