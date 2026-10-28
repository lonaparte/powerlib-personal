import theorem.Attributes
import dependencies.Mathlib

/-! # d-axis-priority current limiting

Static current-reference limiter (foundation), with a Correction of the note's rule.

Model boundary.
Current reference `(i_d, i_q)` in the dq frame, limit `I ≥ 0`; a static map, no converter
dynamics. The note's rule (T-current-limiting §1.2 table): `i_d ← min(i_d, I)`,
`i_q ← sgn(i_q) √(I² − i_d²)` (`dPriorityNote`). The corrected rule (`dPriority`) clamps `i_d`
to `[−I, I]` and then clamps `i_q` to `[−r, r]`, `r = √(I² − i_d'²)`.

Source: work-sync `theory/T-current-limiting.md` §1.1, §1.2.

Results.
* `dPriority_norm_le`: `i_d'² + i_q'² ≤ I²` always;
* `dPriority_of_within`: the limiter is the identity inside the disc `i_d² + i_q² ≤ I²`;
* `dPriority_fst_of_abs_le`: the d-axis current is kept whenever `|i_d| ≤ I` (priority);
* `dPriority_snd_sign`: the sign of `i_q` is kept.
* `clamp_not_rotation_invariant`: component-wise clipping in dq does not commute with a frame
  rotation (unlike the circular limiter, `radialLimit_isometry`), which is the formal content of
  "dq 系按分量硬截断会引入波形畸变" (T-current-limiting §1.1).

Correction. As written the rule (a) always overwrites `i_q` with the remaining capacity, even
when the reference is already inside the limit (`dPriorityNote_overwrites`: `(0, 1/2)` with
`I = 1` becomes `(0, 1)`), and (b) does not limit a negative `i_d` — exporting active power is
`i_d < 0` in the IN-positive convention (`dPriorityNote_exceeds`: `(−2, 0)` with `I = 1` stays
at magnitude `2`). In the corrected rule `dPriority`, `i_q` takes the *minimum* of its magnitude
and the remaining capacity.
-/

noncomputable section
namespace powerlib.Limiting

/-- Clamp to `[-r, r]`. -/
def clampSym (r x : ℝ) : ℝ := max (-r) (min x r)

@[tmio T, powerlib_foundation] theorem clampSym_sq_le {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    clampSym r x ^ 2 ≤ r ^ 2 := by
  have h1 : -r ≤ clampSym r x := le_max_left _ _
  have h2 : clampSym r x ≤ r := max_le (by linarith) (min_le_right _ _)
  nlinarith

@[tmio T, powerlib_foundation] theorem clampSym_of_abs_le {r x : ℝ} (h : |x| ≤ r) : clampSym r x = x := by
  have := abs_le.mp h
  simp only [clampSym]
  rw [min_eq_left this.2, max_eq_right this.1]

/-- Corrected d-axis-priority limiter. -/
def dPriority (I id iq : ℝ) : ℝ × ℝ :=
  (clampSym I id, clampSym (Real.sqrt (I ^ 2 - clampSym I id ^ 2)) iq)

/-- Sign function `sgn` (`sgn 0 = 0`). -/
def sgn (x : ℝ) : ℝ := if 0 < x then 1 else if x < 0 then -1 else 0

/-- The note's d-axis-priority rule, literally. -/
def dPriorityNote (I id iq : ℝ) : ℝ × ℝ :=
  (min id I, sgn iq * Real.sqrt (I ^ 2 - (min id I) ^ 2))

/-- The corrected limiter never exceeds the limit. -/
@[powerlib_foundation] theorem dPriority_norm_le {I : ℝ} (hI : 0 ≤ I) (id iq : ℝ) :
    (dPriority I id iq).1 ^ 2 + (dPriority I id iq).2 ^ 2 ≤ I ^ 2 := by
  simp only [dPriority]
  have h1 := clampSym_sq_le hI id
  have h2 := clampSym_sq_le (Real.sqrt_nonneg (I ^ 2 - clampSym I id ^ 2)) iq
  rw [Real.sq_sqrt (by linarith)] at h2
  linarith

/-- No action inside the limit disc. -/
@[powerlib_foundation] theorem dPriority_of_within {I id iq : ℝ} (hI : 0 ≤ I)
    (h : id ^ 2 + iq ^ 2 ≤ I ^ 2) : dPriority I id iq = (id, iq) := by
  have hd : |id| ≤ I :=
    abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg iq]) hI |> fun h => abs_le.mpr h
  have hcd : clampSym I id = id := clampSym_of_abs_le hd
  have hq : |iq| ≤ Real.sqrt (I ^ 2 - id ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  simp only [dPriority, hcd, clampSym_of_abs_le hq]

/-- d-axis priority: `i_d` is kept whenever `|i_d| ≤ I`. -/
@[powerlib_foundation] theorem dPriority_fst_of_abs_le {I id : ℝ} (h : |id| ≤ I) (iq : ℝ) :
    (dPriority I id iq).1 = id :=
  clampSym_of_abs_le h

@[powerlib_foundation] theorem clampSym_nonneg {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    0 ≤ clampSym r x :=
  le_max_of_le_right (le_min hx hr)

@[powerlib_foundation] theorem clampSym_nonpos {r x : ℝ} (hr : 0 ≤ r) (hx : x ≤ 0) :
    clampSym r x ≤ 0 :=
  max_le (by linarith) ((min_le_left _ _).trans hx)

/-- The sign of `i_q` is preserved. -/
@[powerlib_foundation] theorem dPriority_snd_sign (I id iq : ℝ) :
    (0 ≤ iq → 0 ≤ (dPriority I id iq).2) ∧ (iq ≤ 0 → (dPriority I id iq).2 ≤ 0) :=
  ⟨fun h => clampSym_nonneg (Real.sqrt_nonneg _) h,
    fun h => clampSym_nonpos (Real.sqrt_nonneg _) h⟩

/-- Correction (a): the note's rule changes a reference that is inside the limit. -/
@[powerlib_foundation] theorem dPriorityNote_overwrites :
    (0 : ℝ) ^ 2 + (1 / 2) ^ 2 ≤ 1 ^ 2 ∧ dPriorityNote 1 0 (1 / 2) ≠ (0, 1 / 2) := by
  refine ⟨by norm_num, ?_⟩
  intro h
  have h2 := congrArg Prod.snd h
  simp [dPriorityNote, sgn] at h2

/-- Correction (b): the note's rule does not limit a negative `i_d` (exported power). -/
@[powerlib_foundation] theorem dPriorityNote_exceeds :
    1 ^ 2 < (dPriorityNote 1 (-2) 0).1 ^ 2 + (dPriorityNote 1 (-2) 0).2 ^ 2 := by
  simp [dPriorityNote]
  norm_num

/-- Component-wise clipping does not commute with a frame rotation: rotating `(1, 1)` by
`π/4` and clipping to `I = 1` differs from clipping and then rotating. -/
@[powerlib_foundation] theorem clamp_not_rotation_invariant :
    let rotQ : ℝ → ℝ → ℝ := fun a b => Real.sin (Real.pi / 4) * a + Real.cos (Real.pi / 4) * b
    clampSym 1 (rotQ 1 1) ≠ rotQ (clampSym 1 1) (clampSym 1 1) := by
  intro rotQ
  have h1 : clampSym 1 1 = 1 := clampSym_of_abs_le (by norm_num)
  have h2 : rotQ 1 1 = Real.sqrt 2 := by
    simp only [rotQ, Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hs : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [h1, h2]
  have h3 : clampSym 1 (Real.sqrt 2) = 1 := by
    simp only [clampSym]
    rw [min_eq_right hs.le, max_eq_right (by norm_num)]
  rw [h3]
  exact hs.ne

end powerlib.Limiting
