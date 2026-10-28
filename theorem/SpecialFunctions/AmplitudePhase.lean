import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Amplitude-phase form of a pair of reals (foundation)

A pair `(W, f)` with amplitude `B = √(W² + f²)` and phase `a = arcsin (f / B)` in `[−π/2, π/2]`
is `(±B cos a, B sin a)`: the cosine part is `B cos a = |W|`, so the phase reproduces `W` up to its
sign (the sine part `B sin a = f` is `SpecialFunctions.mul_sin_arcsin_div`).

Scope.
* Pure trigonometry of real numbers; no model family. No hypothesis on `(W, f)`: for `B = 0` both
  sides vanish.

Source: the amplitude-phase form `W cos x + f sin x = B sin(x + a)` of a sinusoid (elementary
trigonometry, `Real.cos_arcsin`); used by the line potentials of a lossless cycle
(`theorem/Network/Swing/CycleMinimum.lean`, `cos_base_pos`) and the representatives in
`(−π/2, π/2)` of angles with positive cosine (`theorem/Network/Swing/Four.lean`,
`exists_rep_of_cos_pos`).

Results.
* `sqrt_mul_cos_arcsin`: `√(W² + f²) cos (arcsin (f / √(W² + f²))) = |W|`.
* `cos_arcsin_sin`: `cos (arcsin (sin x)) = |cos x|` (the case `(W, f) = (cos x, sin x)`, `B = 1`).

Family and connection conclusions.
* None: foundation only.
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Real

/-- The cosine part of the amplitude-phase form: with `B = √(W² + f²)`,
`B cos (arcsin (f / B)) = |W|`. -/
@[tmio T, powerlib_foundation] theorem sqrt_mul_cos_arcsin (W f : ℝ) :
    √(W ^ 2 + f ^ 2) * cos (arcsin (f / √(W ^ 2 + f ^ 2))) = |W| := by
  obtain ⟨B, hBdef⟩ : ∃ B, B = √(W ^ 2 + f ^ 2) := ⟨_, rfl⟩
  rw [← hBdef]
  have hB2 : B ^ 2 = W ^ 2 + f ^ 2 := by rw [hBdef, sq_sqrt (by positivity)]
  rcases (hBdef ▸ sqrt_nonneg _ : 0 ≤ B).eq_or_lt with h0 | hB
  · have hW : W = 0 := by nlinarith [sq_nonneg W, sq_nonneg f]
    rw [← h0, hW, zero_mul, abs_zero]
  rw [cos_arcsin]
  have : 1 - (f / B) ^ 2 = W ^ 2 / B ^ 2 := by
    rw [eq_div_iff (by positivity), sub_mul, div_pow, div_mul_cancel₀ _ (by positivity)]
    linarith
  rw [this, sqrt_div' _ (sq_nonneg _), sqrt_sq hB.le, sqrt_sq_eq_abs]
  field_simp

/-- An angle and its arcsine-of-sine representative have cosines of the same magnitude. -/
@[powerlib_foundation] theorem cos_arcsin_sin (x : ℝ) : cos (arcsin (sin x)) = |cos x| := by
  have h := sqrt_mul_cos_arcsin (cos x) (sin x)
  rwa [cos_sq_add_sin_sq, sqrt_one, div_one, one_mul] at h

end powerlib.SpecialFunctions
