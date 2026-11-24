import theorem.Attributes
import dependencies.Mathlib
import Mathlib.NumberTheory.ZetaValues

/-! # Two sums over the odd harmonics `n ≥ 3` (foundation)

For the odd integers `n = 2k + 3` (`k = 0, 1, 2, …`, that is `n = 3, 5, 7, …`),
`n² − 1 = 4(k + 1)(k + 2)` and `n = (k + 2)² − (k + 1)²`, so

* `n/(n² − 1)² = (1/16)(1/(k + 1)² − 1/(k + 2)²)`, a telescoping series:
  `Σ_{n odd ≥ 3} n/(n² − 1)² = 1/16`;
* `1/(n² − 1)² = (1/16)(1/(k + 1) − 1/(k + 2))²
  = (1/16)(1/(k + 1)² + 1/(k + 2)² − 2/((k + 1)(k + 2)))`, which with Basel's sum
  `Σ_{k ≥ 1} 1/k² = π²/6` and the telescoping `Σ_{k ≥ 1} 1/(k(k + 1)) = 1` gives
  `Σ_{n odd ≥ 3} 1/(n² − 1)² = (1/16)(π²/3 − 3) = (π² − 9)/48`.

These are the sums of the factors `n/(n² − 1)²` and `1/(n² − 1)²` that the harmonic power and the
squared harmonic currents of a resonant link tuned at the fundamental carry
(`theorem/WPT/HarmonicTotals.lean`).

Scope.
* Exact sums of two real series indexed by `k : ℕ`, with the odd harmonic number written
  `((2 * k + 3 : ℕ) : ℝ)`; no model family and no engineering object.

Source: partial fractions and telescoping; Basel's sum `ζ(2) = π²/6` is Mathlib's
`hasSum_zeta_two` (`Mathlib/NumberTheory/ZetaValues.lean`).

Results.
* `hasSum_odd_div_sq_sub_one_sq`: `Σ_{k ≥ 0} n/(n² − 1)² = 1/16` with `n = 2k + 3`.
* `hasSum_one_div_sq_sub_one_sq`: `Σ_{k ≥ 0} 1/(n² − 1)² = (π² − 9)/48` with `n = 2k + 3`.
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Real Filter Finset
open scoped Topology

/-- Basel's sum from `k = 1`, and from `k = 2`. -/
@[tmio T, powerlib_foundation] private lemma hasSum_one_div_add_sq (j : ℕ) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + (j + 1 : ℕ)) ^ 2)
      (π ^ 2 / 6 - ∑ i ∈ range (j + 1), 1 / ((i : ℝ)) ^ 2) := by
  have h := (hasSum_nat_add_iff' (j + 1)).mpr hasSum_zeta_two
  simpa only [Nat.cast_add] using h

/-- The telescoping sum `Σ_{k ≥ 0} (1/(k + 1) − 1/(k + 2)) = 1`. -/
@[tmio T, powerlib_foundation] private lemma hasSum_telescope :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) 1 := by
  have hnn : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := fun k => by
    rw [sub_nonneg]
    gcongr
    norm_num
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hpart : ∀ m : ℕ, ∑ i ∈ range m, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) =
      1 - 1 / ((m : ℝ) + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  simp_rw [hpart]
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub (1 : ℝ)
  simpa using h

/-- `Σ_{k ≥ 0} n/(n² − 1)² = 1/16` over the odd harmonics `n = 2k + 3 ≥ 3`. -/
@[tmio T, powerlib_foundation] theorem hasSum_odd_div_sq_sub_one_sq :
    HasSum (fun k : ℕ => ((2 * k + 3 : ℕ) : ℝ) / (((2 * k + 3 : ℕ) : ℝ) ^ 2 - 1) ^ 2)
      (1 / 16) := by
  have h := ((hasSum_one_div_add_sq 0).sub (hasSum_one_div_add_sq 1)).mul_left (1 / 16)
  convert h using 1
  · funext k
    push_cast
    have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
    have h3 : ((2 * k + 3 : ℝ)) ^ 2 - 1 ≠ 0 := by
      rw [show ((2 * k + 3 : ℝ)) ^ 2 - 1 = 4 * ((k + 1) * (k + 2)) by ring]
      positivity
    field_simp
    ring
  · simp [sum_range_succ]

/-- `Σ_{k ≥ 0} 1/(n² − 1)² = (π² − 9)/48` over the odd harmonics `n = 2k + 3 ≥ 3`. -/
@[tmio T, powerlib_foundation] theorem hasSum_one_div_sq_sub_one_sq :
    HasSum (fun k : ℕ => 1 / (((2 * k + 3 : ℕ) : ℝ) ^ 2 - 1) ^ 2) ((π ^ 2 - 9) / 48) := by
  have h := ((((hasSum_one_div_add_sq 0).add (hasSum_one_div_add_sq 1)).sub
    (hasSum_telescope.mul_left 2))).mul_left (1 / 16)
  convert h using 1
  · funext k
    push_cast
    have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
    have h3 : ((2 * k + 3 : ℝ)) ^ 2 - 1 ≠ 0 := by
      rw [show ((2 * k + 3 : ℝ)) ^ 2 - 1 = 4 * ((k + 1) * (k + 2)) by ring]
      positivity
    field_simp
    ring
  · simp [sum_range_succ]
    ring

end powerlib.SpecialFunctions
