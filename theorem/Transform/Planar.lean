import dependencies.Mathlib
import theorem.Attributes

/-! # Planar vectors: the rotation generator and the complex form

Generic algebra of planar vectors `Fin 2 → ℝ`: the rotation generator `J` and the identification
of the plane with `ℂ`. No electrical frame is chosen here; the Clarke and Park transforms built
on them are in `theorem/Transform/Park.lean`.

Scope.
* Generic: planar vectors `Fin 2 → ℝ` (components `0`, `1`) and real 2 × 2 matrices, and the
  dot-product invariance of orthogonal coordinate changes in any dimension; no model, no axis,
  sign or normalization convention of an electrical transform.

Source: work-sync `theory/T-park-transformation.md` §1.2 (complex form of a planar vector, the
rotation generator as multiplication by `j`).

Results.
* `J = [[0, -1], [1, 0]]`, the rotation generator (counter-clockwise quarter turn): `J_mulVec`,
  `J_mul_J` (`J² = −1`), `J_transpose` (`Jᵀ = −J`: `J` is skew; it is the interconnection of
  the lossless `LC` loop of `theorem/PH/Observability.lean`).
* Complex form `toComplex x = x₀ + j x₁` and its inverse `ofComplex` (`toComplex_ofComplex`,
  `ofComplex_toComplex`, `toComplex_eq`), the real linear equivalence `complexEquiv`
  (`toComplex_add`, `toComplex_sub`, `toComplex_smul`), and `toComplex_J_mulVec` (`J` is
  multiplication by `j`).
* `orthogonal_dotProduct`: a coordinate change `A` with `Aᵀ A = 1` preserves the dot product,
  `(A v)·(A w) = v·w` (power invariance of the orthogonal Park, Clarke and frame rotations).
-/

noncomputable section
namespace powerlib.Transform
open Matrix

/-- Rotation generator `J = [[0, -1], [1, 0]]`. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- Complex form `x₀ + j x₁` of a planar vector. -/
def toComplex (x : Fin 2 → ℝ) : ℂ := ⟨x 0, x 1⟩

/-- Planar vector `(Re z, Im z)` of a complex number. -/
def ofComplex (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

/-! ## The rotation generator -/

@[tmio T, simp, powerlib_foundation] theorem J_mulVec (x : Fin 2 → ℝ) :
    J *ᵥ x = ![-x 1, x 0] := by
  ext i; fin_cases i <;> simp [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[tmio T, powerlib_foundation] theorem J_mul_J : J * J = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J]

@[tmio T, powerlib_foundation] theorem J_transpose : Jᵀ = -J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J]

/-! ## Complex form -/

@[tmio T, simp, powerlib_foundation] theorem toComplex_re (x : Fin 2 → ℝ) :
    (toComplex x).re = x 0 := rfl

@[tmio T, simp, powerlib_foundation] theorem toComplex_im (x : Fin 2 → ℝ) :
    (toComplex x).im = x 1 := rfl

@[tmio T, simp, powerlib_foundation] theorem toComplex_ofComplex (z : ℂ) :
    toComplex (ofComplex z) = z := by
  apply Complex.ext <;> simp [toComplex, ofComplex]

@[tmio T, simp, powerlib_foundation] theorem ofComplex_toComplex (x : Fin 2 → ℝ) :
    ofComplex (toComplex x) = x := by
  ext i; fin_cases i <;> simp [toComplex, ofComplex]

@[tmio T, powerlib_foundation] theorem toComplex_eq (x : Fin 2 → ℝ) :
    toComplex x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [toComplex]

/-- The complex-form coordinate map as a real linear equivalence. -/
def complexEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ where
  toFun := toComplex
  invFun := ofComplex
  map_add' x y := by apply Complex.ext <;> simp [toComplex]
  map_smul' c x := by apply Complex.ext <;> simp [toComplex]
  left_inv := ofComplex_toComplex
  right_inv := toComplex_ofComplex

@[tmio T, simp, powerlib_foundation] theorem complexEquiv_apply (x : Fin 2 → ℝ) :
    complexEquiv x = toComplex x := rfl

@[tmio T, simp, powerlib_foundation] theorem toComplex_add (x y : Fin 2 → ℝ) :
    toComplex (x + y) = toComplex x + toComplex y := complexEquiv.map_add x y

@[tmio T, simp, powerlib_foundation] theorem toComplex_sub (x y : Fin 2 → ℝ) :
    toComplex (x - y) = toComplex x - toComplex y := complexEquiv.map_sub x y

@[tmio T, simp, powerlib_foundation] theorem toComplex_smul (c : ℝ) (x : Fin 2 → ℝ) :
    toComplex (c • x) = (c : ℂ) * toComplex x := by
  apply Complex.ext <;> simp [toComplex]

/-- `J` is complex multiplication by `j`. -/
@[tmio T, powerlib_foundation] theorem toComplex_J_mulVec (x : Fin 2 → ℝ) :
    toComplex (J *ᵥ x) = Complex.I * toComplex x := by
  apply Complex.ext <;> simp [toComplex]

/-! ## Orthogonal coordinate changes -/

/-- A coordinate change with `Aᵀ A = 1` preserves the dot product: `(A v)·(A w) = v·w`. -/
@[tmio T, powerlib_foundation] theorem orthogonal_dotProduct {m n R : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] [CommSemiring R] {A : Matrix m n R} (hA : Aᵀ * A = 1)
    (v w : n → R) : (A *ᵥ v) ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hA, vecMul_one]

end powerlib.Transform
