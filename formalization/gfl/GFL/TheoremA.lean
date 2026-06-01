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
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

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

/-! ### Theorem A strengthened: the zero eigenvalue is simple (exactly one) -/

/-- The Variant-U Jacobian as a block matrix (§6): `[[A, c], [0, 0]]` over `Fin 8 ⊕ Unit`. -/
def JUblock (A : Matrix (Fin 8) (Fin 8) ℝ) (c : Fin 8 → ℝ) :
    Matrix (Fin 8 ⊕ Unit) (Fin 8 ⊕ Unit) ℝ :=
  Matrix.fromBlocks A (fun i _ => c i) 0 0

/-- **Theorem A, strengthened (§7 + §9 anchor "exactly one zero eigenvalue").**
The characteristic determinant factorises as

    `det(J_U − μ·I) = (−μ) · det(A − μ·I)`.

The factor `(−μ)` is a *simple* zero, and `det(A − 0·I) = det A ≠ 0` whenever `A` is
invertible (W2), so `μ = 0` is a root of multiplicity exactly one: the unanchored
Jacobian has **exactly one** zero eigenvalue. -/
theorem variantU_charpoly_factor
    (A : Matrix (Fin 8) (Fin 8) ℝ) (c : Fin 8 → ℝ) (μ : ℝ) :
    (JUblock A c - μ • 1).det = (-μ) * (A - μ • 1).det := by
  have hM : JUblock A c - μ • (1 : Matrix (Fin 8 ⊕ Unit) (Fin 8 ⊕ Unit) ℝ)
      = Matrix.fromBlocks (A - μ • 1) (fun i _ => c i) 0 (-(μ • 1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [JUblock, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.neg_apply]
  rw [hM, Matrix.det_fromBlocks_zero₂₁]
  have hu : (-(μ • (1 : Matrix Unit Unit ℝ))).det = -μ := by
    rw [Matrix.det_unique]; simp
  rw [hu]; ring

/-- At `μ = 0` the cofactor `det(A − 0·I) = det A`, which is nonzero exactly when `A`
is invertible — confirming the zero eigenvalue of `J_U` is simple (multiplicity one). -/
theorem variantU_zero_cofactor_ne (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : IsUnit A.det) :
    (A - (0 : ℝ) • 1).det ≠ 0 := by
  simpa using hA.ne_zero

/-- **Theorem A — explicit right eigenvector.**  From `det J_U = 0` there is a *nonzero*
`v` with `J_U · v = 0`: a genuine right eigenvector for eigenvalue `0` (the standard
"`0 ∈ spec`" via a nontrivial kernel, complementing the left eigenvector `e₉`). -/
theorem variantU_zero_right_eigenvector (J : Matrix (Fin 9) (Fin 9) ℝ)
    (hbot : ∀ j, J 8 j = 0) : ∃ v : Fin 9 → ℝ, v ≠ 0 ∧ J *ᵥ v = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.mpr (det_eq_zero_of_row_eq_zero 8 hbot)

end GFL
