import theorem.Attributes
import dependencies.Mathlib

/-! # The symmetric clamp (foundation)

Clamping a real number to the interval `[−r, r]`, `clampSym r x = max (−r) (min x r)`: the
saturation of a command `x` at the limit `r`, stated once for every limiter of the library.

Scope.
* Static real analysis of one piecewise-linear function of two real arguments; nothing here
  describes a physical system and no model family is defined.

Source: elementary analysis; used by the d-axis-priority current limiter
(`theorem/GridTiedConverter/GFM/Limiting/DAxisPriority.lean`) and the PI current loop under the
inverter's modulation voltage limit (`theorem/GridTiedConverter/CurrentControl/VoltageLimit.lean`).

Results.
* `clampSym_of_abs_le`: a value in range passes unchanged.
* `abs_clampSym_le`: the clamped value is bounded by the limit, `|clampSym r x| ≤ |r|` (squared:
  `sq_le_sq.mpr`).
* `clampSym_nonneg`, `clampSym_nonpos`: with `r ≥ 0` the sign is kept.
* `clampSym_eventually_eq`: beyond the limit the clamp is constant near the value.
* `clampSym_ne_of_lt_abs`: with `r ≥ 0`, a value beyond the limit is changed.
-/

noncomputable section
namespace powerlib.SpecialFunctions

open Filter
open scoped Topology

/-- Clamp to `[−r, r]`. -/
def clampSym (r x : ℝ) : ℝ := max (-r) (min x r)

/-- A value in range passes unchanged. -/
@[tmio T, powerlib_foundation] theorem clampSym_of_abs_le {r x : ℝ} (h : |x| ≤ r) :
    clampSym r x = x := by
  rw [abs_le] at h
  rw [clampSym, min_eq_left h.2, max_eq_right h.1]

/-- The clamped value is bounded by the limit. -/
@[tmio T, powerlib_foundation] theorem abs_clampSym_le (r x : ℝ) : |clampSym r x| ≤ |r| := by
  unfold clampSym
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  · rw [max_eq_left ((min_le_right _ _).trans (by linarith)), abs_neg]

@[tmio T, powerlib_foundation] theorem clampSym_nonneg {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    0 ≤ clampSym r x :=
  le_max_of_le_right (le_min hx hr)

@[tmio T, powerlib_foundation] theorem clampSym_nonpos {r x : ℝ} (hr : 0 ≤ r) (hx : x ≤ 0) :
    clampSym r x ≤ 0 :=
  max_le (by linarith) ((min_le_left _ _).trans hx)

/-- Beyond the limit the clamp is constant near the value. -/
@[tmio T, powerlib_foundation] theorem clampSym_eventually_eq {r x₀ : ℝ} (h : r < |x₀|) :
    ∀ᶠ x in 𝓝 x₀, clampSym r x = clampSym r x₀ := by
  rcases lt_abs.mp h with h | h
  · filter_upwards [eventually_gt_nhds h] with x hx
    simp [clampSym, min_eq_right hx.le, min_eq_right h.le]
  · have h' : x₀ < -r := by linarith
    have e : ∀ w, w < -r → clampSym r w = -r := fun w hw =>
      max_eq_left ((min_le_left _ _).trans hw.le)
    filter_upwards [eventually_lt_nhds h'] with x hx
    rw [e x hx, e x₀ h']

/-- With a nonnegative limit, a value beyond it is changed by the clamp. -/
@[tmio T, powerlib_foundation] theorem clampSym_ne_of_lt_abs {r x : ℝ} (hr : 0 ≤ r)
    (h : r < |x|) : clampSym r x ≠ x := by
  rcases lt_abs.mp h with h | h
  · rw [show clampSym r x = r by
      rw [clampSym, min_eq_right h.le, max_eq_right (by linarith : -r ≤ r)]]
    exact h.ne
  · rw [show clampSym r x = -r from max_eq_left ((min_le_left _ _).trans (by linarith))]
    intro e
    linarith

end powerlib.SpecialFunctions
