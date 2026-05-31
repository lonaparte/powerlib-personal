/-
  Theorem A (§7): zero eigenvalue of the unanchored Jacobian `J_U` (Variant U).

  Variant U sets `F9_U := 0`, so by §6 its Jacobian has a zero bottom row
  (`ρᵀ = 0ᵀ`, `j99 = 0`).  We take this §6 structural fact as the hypothesis on the
  Jacobian and prove the two assertions of Theorem A:

    * `e₉ᵀ J_U = 0ᵀ`  (the last standard basis covector is a left eigenvector for 0);
    * `det J_U = 0`   (so `0 ∈ spec(J_U)`),

  together with `e₉ ≠ 0` (the eigenvector is genuine).
-/
import GFL.Model

namespace GFL

open Matrix

/-- **Theorem A — zero eigenvalue, Variant U (§7).**
If the Jacobian has a zero last row (Variant U, §6: `ρᵀ = 0ᵀ`, `j99 = 0`), then `e₉` is
a nonzero left eigenvector for eigenvalue `0` and `det J = 0`, i.e. `0 ∈ spec(J)`. -/
theorem variantU_zero_eigenvalue (J : Matrix (Fin 9) (Fin 9) ℝ)
    (hbot : ∀ j, J 8 j = 0) :
    (Pi.single (8 : Fin 9) (1 : ℝ) : Fin 9 → ℝ) ᵥ* J = 0 ∧
    J.det = 0 ∧
    (Pi.single (8 : Fin 9) (1 : ℝ) : Fin 9 → ℝ) ≠ 0 := by
  refine ⟨?_, det_eq_zero_of_row_eq_zero 8 hbot, ?_⟩
  · -- e₉ᵀ J = 0ᵀ  : compute the j-th entry, `vecMul` reduces to a `dotProduct`
    funext j
    show (Pi.single (8 : Fin 9) (1 : ℝ) : Fin 9 → ℝ) ⬝ᵥ (fun i => J i j) = (0 : Fin 9 → ℝ) j
    rw [single_dotProduct]
    simp [hbot j]
  · -- e₉ ≠ 0 since its 8-component is 1
    intro h
    have h8 : (Pi.single (8 : Fin 9) (1 : ℝ) : Fin 9 → ℝ) 8 = 0 := by rw [h]; rfl
    rw [Pi.single_eq_same] at h8
    exact one_ne_zero h8

end GFL
