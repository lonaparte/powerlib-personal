import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Nondegeneracy of a stable diagonal linear period map

For a positive period and modal exponents in the open left half-plane,
the modal multipliers have modulus less than one. Consequently the diagonal
period map minus the identity is invertible.

This is the spectral part of the return-map implicit-function argument. It
does not construct a nonlinear return map or identify its derivative.
-/

noncomputable section

namespace Powerlib.Parametric

/-- A stable scalar mode contracts over every positive period. -/
theorem stable_modal_multiplier_norm_lt_one {λ : ℂ} {T : ℝ}
    (hλ : λ.re < 0) (hT : 0 < T) :
    ‖Complex.exp ((T : ℂ) * λ)‖ < 1 := by
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  simpa using mul_neg_of_pos_of_neg hT hλ

/-- A stable scalar mode cannot have period multiplier one. -/
theorem stable_modal_multiplier_ne_one {λ : ℂ} {T : ℝ}
    (hλ : λ.re < 0) (hT : 0 < T) :
    Complex.exp ((T : ℂ) * λ) ≠ 1 := by
  intro h
  have hn := stable_modal_multiplier_norm_lt_one hλ hT
  rw [h, norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

/-- The diagonal linear return map minus identity has nonzero determinant. -/
theorem stable_diagonal_returnMap_sub_one_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (λ : ι → ℂ) {T : ℝ}
    (hλ : ∀ j, (λ j).re < 0) (hT : 0 < T) :
    (Matrix.diagonal (fun j ↦ Complex.exp ((T : ℂ) * λ j)) - 1).det ≠ 0 := by
  have hd : Matrix.diagonal (fun j ↦ Complex.exp ((T : ℂ) * λ j)) - 1 =
      Matrix.diagonal (fun j ↦ Complex.exp ((T : ℂ) * λ j) - 1) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  rw [hd, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact sub_ne_zero.mpr (stable_modal_multiplier_ne_one (hλ j) hT)

/-- This is the diagonal spectral nondegeneracy needed by the fixed-point IFT. -/
theorem stable_diagonal_returnMap_sub_one_isUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι] (λ : ι → ℂ) {T : ℝ}
    (hλ : ∀ j, (λ j).re < 0) (hT : 0 < T) :
    IsUnit (Matrix.diagonal (fun j ↦ Complex.exp ((T : ℂ) * λ j)) - 1) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr
    (stable_diagonal_returnMap_sub_one_det_ne_zero λ hλ hT)

end Powerlib.Parametric
