import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Zeros of a shifted sinusoid `c − A sin(θ + φ)` in one period (foundation)

The number and position of the zeros of `c − A sin(θ + φ)` in a period window `[a, a + 2π)`, for
`A > 0`.

Scope.
* Pure trigonometry; no model family. It is used for the reduced GFL-PLL model whose
  phase-detector characteristic is exactly of this form (`theorem/GFL/LCLine/Reduction.lean`,
  `h_eq_polar`).

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/equilibria-and-bifurcation.md`
§2 (number of equilibria per period).

Results.
* `|c| < A`: exactly two zeros (`ncard_sinusoidZeros_of_lt`), `stableRoot` (where the derivative
  `−A cos(θ + φ)` is negative) and `saddleRoot` (where it is positive), and they differ
  (`stableRoot_ne_saddleRoot`).
* `|c| = A`: exactly one zero, where the derivative vanishes (`ncard_sinusoidZeros_of_eq`).
* `|c| > A`: no zero (`sinusoidZeros_eq_empty`).
* Explicitly `stableRoot ≡ arcsin(c/A) − φ` and `saddleRoot ≡ π − arcsin(c/A) − φ (mod 2π)`.
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Real Set

/-- Zeros of `θ ↦ c − A sin(θ + φ)` in the window `[a, a + 2π)`. -/
def sinusoidZeros (c A φ a : ℝ) : Set ℝ :=
  {θ | θ ∈ Ico a (a + 2 * π) ∧ c - A * sin (θ + φ) = 0}

/-- The zero with `cos(θ + φ) ≥ 0`, reduced into the window. -/
def stableRoot (c A φ a : ℝ) : ℝ := toIcoMod two_pi_pos a (arcsin (c / A) - φ)

/-- The zero with `cos(θ + φ) ≤ 0`, reduced into the window. -/
def saddleRoot (c A φ a : ℝ) : ℝ := toIcoMod two_pi_pos a (π - arcsin (c / A) - φ)

section
variable {c A φ a : ℝ}

@[tmio T, powerlib_foundation] theorem stableRoot_mem : stableRoot c A φ a ∈ Ico a (a + 2 * π) :=
  toIcoMod_mem_Ico _ _ _

@[powerlib_foundation] theorem saddleRoot_mem : saddleRoot c A φ a ∈ Ico a (a + 2 * π) :=
  toIcoMod_mem_Ico _ _ _

@[powerlib_foundation] private lemma toIcoMod_add_phase (a b : ℝ) :
    ∃ n : ℤ, toIcoMod two_pi_pos a b = b - n * (2 * π) := by
  refine ⟨toIcoDiv two_pi_pos a b, ?_⟩
  have := self_sub_toIcoMod two_pi_pos a b
  rw [zsmul_eq_mul] at this
  linarith

@[powerlib_foundation] theorem sin_stableRoot (hc : |c| ≤ A) (hA : 0 < A) :
    sin (stableRoot c A φ a + φ) = c / A := by
  obtain ⟨n, hn⟩ := toIcoMod_add_phase a (arcsin (c / A) - φ)
  have hs : |c / A| ≤ 1 := by rw [abs_div, abs_of_pos hA, div_le_one hA]; exact hc
  rw [stableRoot, hn, show arcsin (c / A) - φ - n * (2 * π) + φ =
    arcsin (c / A) - n * (2 * π) by ring, sin_sub_int_mul_two_pi,
    sin_arcsin (abs_le.mp hs).1 (abs_le.mp hs).2]

@[powerlib_foundation] theorem cos_stableRoot :
    cos (stableRoot c A φ a + φ) = √(1 - (c / A) ^ 2) := by
  obtain ⟨n, hn⟩ := toIcoMod_add_phase a (arcsin (c / A) - φ)
  rw [stableRoot, hn, show arcsin (c / A) - φ - n * (2 * π) + φ =
    arcsin (c / A) - n * (2 * π) by ring, cos_sub_int_mul_two_pi, cos_arcsin]

@[powerlib_foundation] theorem sin_saddleRoot (hc : |c| ≤ A) (hA : 0 < A) :
    sin (saddleRoot c A φ a + φ) = c / A := by
  obtain ⟨n, hn⟩ := toIcoMod_add_phase a (π - arcsin (c / A) - φ)
  have hs : |c / A| ≤ 1 := by rw [abs_div, abs_of_pos hA, div_le_one hA]; exact hc
  rw [saddleRoot, hn, show π - arcsin (c / A) - φ - n * (2 * π) + φ =
    (π - arcsin (c / A)) - n * (2 * π) by ring, sin_sub_int_mul_two_pi, sin_pi_sub,
    sin_arcsin (abs_le.mp hs).1 (abs_le.mp hs).2]

@[powerlib_foundation] theorem cos_saddleRoot :
    cos (saddleRoot c A φ a + φ) = -√(1 - (c / A) ^ 2) := by
  obtain ⟨n, hn⟩ := toIcoMod_add_phase a (π - arcsin (c / A) - φ)
  rw [saddleRoot, hn, show π - arcsin (c / A) - φ - n * (2 * π) + φ =
    (π - arcsin (c / A)) - n * (2 * π) by ring, cos_sub_int_mul_two_pi, cos_pi_sub, cos_arcsin]

@[powerlib_foundation] theorem sqrt_one_sub_sq_pos (hc : |c| < A) (hA : 0 < A) :
    0 < √(1 - (c / A) ^ 2) := by
  apply Real.sqrt_pos.mpr
  have hs : |c / A| < 1 := by rw [abs_div, abs_of_pos hA, div_lt_one hA]; exact hc
  have : (c / A) ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (c / A)]
  linarith

@[powerlib_foundation] theorem sqrt_one_sub_sq_eq_zero (hc : |c| = A) (hA : 0 < A) :
    √(1 - (c / A) ^ 2) = 0 := by
  have : (c / A) ^ 2 = 1 := by
    rw [div_pow, ← sq_abs, hc, div_self (pow_ne_zero 2 hA.ne')]
  rw [this, sub_self, Real.sqrt_zero]

/-- The loading angle `arcsin (c / A)` solves `A sin δ = c`. -/
@[powerlib_foundation] theorem mul_sin_arcsin_div (hc : |c| ≤ A) (hA : 0 < A) :
    A * sin (arcsin (c / A)) = c := by
  have hs : |c / A| ≤ 1 := by rw [abs_div, abs_of_pos hA, div_le_one hA]; exact hc
  rw [sin_arcsin (abs_le.mp hs).1 (abs_le.mp hs).2]
  field_simp

/-- The second angle `π − arcsin (c / A)` solves `A sin δ = c` too. -/
@[powerlib_foundation] theorem mul_sin_pi_sub_arcsin_div (hc : |c| ≤ A) (hA : 0 < A) :
    A * sin (π - arcsin (c / A)) = c := by
  rw [sin_pi_sub]
  exact mul_sin_arcsin_div hc hA

/-- Below the peak, `A cos δ > 0` at the loading angle. -/
@[powerlib_foundation] theorem cos_arcsin_div_pos (hc : |c| < A) (hA : 0 < A) :
    0 < cos (arcsin (c / A)) := by
  rw [cos_arcsin]
  exact sqrt_one_sub_sq_pos hc hA

/-- Below the peak, `A cos δ < 0` at the second angle. -/
@[powerlib_foundation] theorem cos_pi_sub_arcsin_div_neg (hc : |c| < A) (hA : 0 < A) :
    cos (π - arcsin (c / A)) < 0 := by
  rw [cos_pi_sub, neg_lt_zero]
  exact cos_arcsin_div_pos hc hA

@[powerlib_foundation] theorem stableRoot_zero (hc : |c| ≤ A) (hA : 0 < A) :
    c - A * sin (stableRoot c A φ a + φ) = 0 := by
  rw [sin_stableRoot hc hA]; field_simp; ring

@[powerlib_foundation] theorem saddleRoot_zero (hc : |c| ≤ A) (hA : 0 < A) :
    c - A * sin (saddleRoot c A φ a + φ) = 0 := by
  rw [sin_saddleRoot hc hA]; field_simp; ring

/-- Every zero in the window is `stableRoot` or `saddleRoot`. -/
@[powerlib_foundation] theorem sinusoidZeros_subset (hA : 0 < A) :
    sinusoidZeros c A φ a ⊆ {stableRoot c A φ a, saddleRoot c A φ a} := by
  rintro θ ⟨hθ, hz⟩
  have hsin : sin (θ + φ) = c / A := by field_simp; linarith
  have hs : |c / A| ≤ 1 := by rw [← hsin]; exact abs_sin_le_one _
  have harc : sin (θ + φ) = sin (arcsin (c / A)) := by
    rw [hsin, sin_arcsin (abs_le.mp hs).1 (abs_le.mp hs).2]
  obtain ⟨k, hk | hk⟩ := Real.sin_eq_sin_iff.mp harc
  · left
    have e : θ = (arcsin (c / A) - φ) - k • (2 * π) := by rw [zsmul_eq_mul]; linarith
    rw [stableRoot, ← toIcoMod_sub_zsmul two_pi_pos a _ k, ← e]
    exact ((toIcoMod_eq_self two_pi_pos).mpr hθ).symm
  · right
    have e : θ = (π - arcsin (c / A) - φ) + k • (2 * π) := by rw [zsmul_eq_mul]; linarith
    rw [saddleRoot, ← toIcoMod_add_zsmul two_pi_pos a _ k, ← e]
    exact ((toIcoMod_eq_self two_pi_pos).mpr hθ).symm

/-- `|c| < A`: the two zeros are distinct. -/
@[powerlib_foundation] theorem stableRoot_ne_saddleRoot (hc : |c| < A) (hA : 0 < A) :
    stableRoot c A φ a ≠ saddleRoot c A φ a := by
  intro h
  obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod two_pi_pos).mp h
  rw [zsmul_eq_mul] at hn
  have hs : |c / A| < 1 := by rw [abs_div, abs_of_pos hA, div_lt_one hA]; exact hc
  have h1 : arcsin (c / A) < π / 2 := arcsin_lt_pi_div_two.mpr (abs_lt.mp hs).2
  have h2 : -(π / 2) < arcsin (c / A) := neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp hs).1
  have hpi := pi_pos
  have hlo : (0 : ℝ) < n := by
    by_contra hneg; rw [not_lt] at hneg
    nlinarith
  have hhi : (n : ℝ) < 1 := by
    by_contra hneg; rw [not_lt] at hneg
    nlinarith
  have : (0 : ℤ) < n := by exact_mod_cast hlo
  have : n < (1 : ℤ) := by exact_mod_cast hhi
  omega

/-- `|c| = A`: the two zeros coincide. -/
@[powerlib_foundation] theorem stableRoot_eq_saddleRoot (hc : |c| = A) (hA : 0 < A) :
    stableRoot c A φ a = saddleRoot c A φ a := by
  rw [stableRoot, saddleRoot, toIcoMod_eq_toIcoMod]
  rcases abs_eq hA.le |>.mp hc with h | h
  · refine ⟨0, ?_⟩
    rw [h, div_self hA.ne', arcsin_one]; simp; ring
  · refine ⟨1, ?_⟩
    rw [h, neg_div, div_self hA.ne', arcsin_neg, arcsin_one]; simp; ring

/-- `|c| ≤ A`: the zero set in a window is exactly `{stableRoot, saddleRoot}`. -/
@[powerlib_foundation] theorem sinusoidZeros_eq (hc : |c| ≤ A) (hA : 0 < A) :
    sinusoidZeros c A φ a = {stableRoot c A φ a, saddleRoot c A φ a} := by
  refine (sinusoidZeros_subset hA).antisymm ?_
  rintro θ (rfl | rfl)
  · exact ⟨stableRoot_mem, stableRoot_zero hc hA⟩
  · exact ⟨saddleRoot_mem, saddleRoot_zero hc hA⟩

/-- `|c| < A`: exactly two zeros per period. -/
@[powerlib_foundation] theorem ncard_sinusoidZeros_of_lt (hc : |c| < A) (hA : 0 < A) :
    (sinusoidZeros c A φ a).ncard = 2 := by
  rw [sinusoidZeros_eq hc.le hA, Set.ncard_pair (stableRoot_ne_saddleRoot hc hA)]

/-- `|c| = A`: exactly one zero per period. -/
@[powerlib_foundation] theorem ncard_sinusoidZeros_of_eq (hc : |c| = A) (hA : 0 < A) :
    (sinusoidZeros c A φ a).ncard = 1 := by
  rw [sinusoidZeros_eq hc.le hA, stableRoot_eq_saddleRoot hc hA, Set.pair_eq_singleton,
    Set.ncard_singleton]

/-- `|c| > A`: no zero at all. -/
@[powerlib_foundation] theorem sinusoid_ne_zero_of_lt (hA : 0 ≤ A) (hc : A < |c|) (θ : ℝ) :
    c - A * sin (θ + φ) ≠ 0 := by
  intro h
  have : |c| = |A * sin (θ + φ)| := by rw [show c = A * sin (θ + φ) by linarith]
  rw [abs_mul, abs_of_nonneg hA] at this
  have hs := abs_sin_le_one (θ + φ)
  nlinarith [abs_nonneg (sin (θ + φ))]

@[powerlib_foundation] theorem sinusoidZeros_eq_empty (hA : 0 ≤ A) (hc : A < |c|) :
    sinusoidZeros c A φ a = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun θ hθ => sinusoid_ne_zero_of_lt hA hc θ hθ.2

/-- Existence of a zero: `(∃ θ, c − A sin(θ + φ) = 0) ↔ |c| ≤ A` (for `A > 0`). -/
@[powerlib_foundation] theorem exists_sinusoid_zero_iff (hA : 0 < A) :
    (∃ θ, c - A * sin (θ + φ) = 0) ↔ |c| ≤ A := by
  constructor
  · rintro ⟨θ, hθ⟩
    by_contra h; rw [not_le] at h
    exact sinusoid_ne_zero_of_lt hA.le h θ hθ
  · intro hc
    exact ⟨stableRoot c A φ 0, stableRoot_zero hc hA⟩

end

end powerlib.SpecialFunctions
