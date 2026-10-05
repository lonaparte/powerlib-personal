import theorem.LibrarySearch
import dependencies.LeanForControl

open scoped Matrix.Norms.Frobenius

namespace powerlib.Upstream

@[powerlib_foundation]
theorem complexification_exp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (NormedSpace.exp A).map (algebraMap ℝ ℂ) =
      NormedSpace.exp (A.map (algebraMap ℝ ℂ)) := by
  powerlib_search

@[powerlib_foundation]
theorem exp_const_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t s : ℝ) :
    NormedSpace.exp (t • A) * NormedSpace.exp (s • A) =
      NormedSpace.exp ((t + s) • A) := by
  powerlib_search

@[powerlib_foundation]
theorem contractive_block {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : LinearSystems.IsHurwitz A) :
    ∃ m : ℕ, 0 < m ∧ ‖NormedSpace.exp ((m : ℝ) • A)‖ < 1 := by
  powerlib_search

end powerlib.Upstream
