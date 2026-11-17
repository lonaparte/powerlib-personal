import theorem.SpecialFunctions.Clamp
import Mathlib.Basic.Real.Sign

/-! # d-axis-priority current limiting

Static current-reference limiter (domain), with a Correction of the note's rule.

Model boundary.
Current reference `(i_d, i_q)` in the dq frame, limit `I ≥ 0`; a static map, no converter
dynamics. The note's rule (T-current-limiting §1.2 table): `i_d ← min(i_d, I)`,
`i_q ← sgn(i_q) √(I² − i_d²)` (`dPriorityNote`). The corrected rule (`dPriority`) clamps `i_d`
to `[−I, I]` and then clamps `i_q` to `[−r, r]`, `r = √(I² − i_d'²)`.

Source: work-sync `theory/T-current-limiting.md` §1.1, §1.2; the symmetric clamp
`SpecialFunctions.clampSym` (`theorem/SpecialFunctions/Clamp.lean`).

Results.
* `dPriority_norm_le`: `i_d'² + i_q'² ≤ I²` always;
* `dPriority_of_within`: the limiter is the identity inside the disc `i_d² + i_q² ≤ I²`;
* d-axis priority: `(dPriority I i_d i_q).1 = clampSym I i_d = i_d` whenever `|i_d| ≤ I`
  (`SpecialFunctions.clampSym_of_abs_le`);
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

open powerlib.SpecialFunctions

/-- Corrected d-axis-priority limiter. -/
def dPriority (I id iq : ℝ) : ℝ × ℝ :=
  (clampSym I id, clampSym (Real.sqrt (I ^ 2 - clampSym I id ^ 2)) iq)

/-- The note's d-axis-priority rule, literally (`sgn` is `Real.sign`, `sgn 0 = 0`). -/
def dPriorityNote (I id iq : ℝ) : ℝ × ℝ :=
  (min id I, Real.sign iq * Real.sqrt (I ^ 2 - (min id I) ^ 2))

/-- The corrected limiter never exceeds the limit. -/
@[tmio M, powerlib_domain] theorem dPriority_norm_le (I id iq : ℝ) :
    (dPriority I id iq).1 ^ 2 + (dPriority I id iq).2 ^ 2 ≤ I ^ 2 := by
  simp only [dPriority]
  have h1 : clampSym I id ^ 2 ≤ I ^ 2 := sq_le_sq.mpr (abs_clampSym_le I id)
  have h2 := sq_le_sq.mpr (abs_clampSym_le (Real.sqrt (I ^ 2 - clampSym I id ^ 2)) iq)
  rw [Real.sq_sqrt (by linarith)] at h2
  linarith

/-- No action inside the limit disc. -/
@[tmio M, powerlib_domain] theorem dPriority_of_within {I id iq : ℝ} (hI : 0 ≤ I)
    (h : id ^ 2 + iq ^ 2 ≤ I ^ 2) : dPriority I id iq = (id, iq) := by
  have hd : |id| ≤ I :=
    abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg iq]) hI |> fun h => abs_le.mpr h
  have hcd : clampSym I id = id := clampSym_of_abs_le hd
  have hq : |iq| ≤ Real.sqrt (I ^ 2 - id ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  simp only [dPriority, hcd, clampSym_of_abs_le hq]

/-- The sign of `i_q` is preserved. -/
@[tmio M, powerlib_domain] theorem dPriority_snd_sign (I id iq : ℝ) :
    (0 ≤ iq → 0 ≤ (dPriority I id iq).2) ∧ (iq ≤ 0 → (dPriority I id iq).2 ≤ 0) :=
  ⟨fun h => clampSym_nonneg (Real.sqrt_nonneg _) h,
    fun h => clampSym_nonpos (Real.sqrt_nonneg _) h⟩

/-- Correction (a): the note's rule changes a reference that is inside the limit. -/
@[tmio M, powerlib_domain] theorem dPriorityNote_overwrites :
    (0 : ℝ) ^ 2 + (1 / 2) ^ 2 ≤ 1 ^ 2 ∧ dPriorityNote 1 0 (1 / 2) ≠ (0, 1 / 2) := by
  refine ⟨by norm_num, ?_⟩
  intro h
  have h2 := congrArg Prod.snd h
  simp [dPriorityNote, Real.sign_of_pos (two_pos : (0 : ℝ) < 2)] at h2

/-- Correction (b): the note's rule does not limit a negative `i_d` (exported power). -/
@[tmio M, powerlib_domain] theorem dPriorityNote_exceeds :
    1 ^ 2 < (dPriorityNote 1 (-2) 0).1 ^ 2 + (dPriorityNote 1 (-2) 0).2 ^ 2 := by
  simp [dPriorityNote]
  norm_num

/-- Component-wise clipping does not commute with a frame rotation: rotating `(1, 1)` by
`π/4` and clipping to `I = 1` differs from clipping and then rotating. -/
@[tmio T, powerlib_foundation] theorem clamp_not_rotation_invariant :
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
