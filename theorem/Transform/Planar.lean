import dependencies.Mathlib
import theorem.Attributes

/-! # Planar vectors: the rotation generator, the complex form and complex-symmetric matrices

Generic algebra of planar vectors `Fin 2 → ℝ`: the rotation generator `J`, the identification
of the plane with `ℂ` and the complex-symmetric 2 × 2 matrices (multiplication by a complex
number). No electrical frame is chosen here; the Clarke and Park transforms built on them are in
`theorem/Transform/Park.lean`.

Scope.
* Generic: planar vectors `Fin 2 → ℝ` (components `0`, `1`), 2 × 2 matrices over a commutative
  ring, and the dot-product invariance of orthogonal coordinate changes in any dimension; no
  model, no axis, sign or normalization convention of an electrical transform.

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
* Complex-symmetric matrices `complexSymm a b = [[a, −b], [b, a]]` over any commutative ring:
  the matrix of multiplication by `a + jb` (`toComplex_complexSymm_mulVec`); closed under sum,
  difference and product (`complexSymm_add`, `complexSymm_sub`, `complexSymm_mul`, `a + jb`
  arithmetic), scalars `s • 1 = complexSymm s 0`, ring maps (`complexSymm_map`), determinant
  `a² + b²` (`det_complexSymm`) and, over a field, inverse
  `complexSymm (a/(a² + b²)) (−b/(a² + b²))` (`complexSymm_inv`). The rotation `rot θ` is
  `complexSymm (cos θ) (sin θ)` (`rot_eq_complexSymm`, `theorem/Transform/Park.lean`); dq
  impedances, transfer functions and the line matrices of the GFL models are instances.
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

/-! ## Complex-symmetric 2 × 2 matrices -/

/-- Complex-symmetric 2 × 2 matrix `[[a, −b], [b, a]]`. -/
def complexSymm {R : Type*} [CommRing R] (a b : R) : Matrix (Fin 2) (Fin 2) R := !![a, -b; b, a]

section complexSymm
variable {R : Type*} [CommRing R]

@[tmio T, powerlib_foundation] theorem complexSymm_mul (a b c d : R) :
    complexSymm a b * complexSymm c d = complexSymm (a * c - b * d) (a * d + b * c) := by
  simp only [complexSymm, mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

@[tmio T, powerlib_foundation] theorem complexSymm_add (a b c d : R) :
    complexSymm a b + complexSymm c d = complexSymm (a + c) (b + d) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexSymm]; ring

@[tmio T, powerlib_foundation] theorem complexSymm_sub (a b c d : R) :
    complexSymm a b - complexSymm c d = complexSymm (a - c) (b - d) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexSymm]; ring

@[tmio T, powerlib_foundation] theorem smul_one_eq_complexSymm (s : R) :
    s • (1 : Matrix (Fin 2) (Fin 2) R) = complexSymm s 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexSymm]

@[tmio T, powerlib_foundation] theorem det_complexSymm (a b : R) :
    (complexSymm a b).det = a ^ 2 + b ^ 2 := by
  rw [complexSymm, det_fin_two_of]; ring

@[tmio T, powerlib_foundation] theorem complexSymm_map {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) : (complexSymm a b).map f = complexSymm (f a) (f b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexSymm]

end complexSymm

/-- Inverse of a nonsingular complex-symmetric matrix over any field. -/
@[tmio T, powerlib_foundation] theorem complexSymm_inv {K : Type*} [Field K] {a b : K}
    (h : a ^ 2 + b ^ 2 ≠ 0) :
    (complexSymm a b)⁻¹ = complexSymm (a / (a ^ 2 + b ^ 2)) (-b / (a ^ 2 + b ^ 2)) := by
  apply Matrix.inv_eq_right_inv
  rw [complexSymm_mul, show (1 : Matrix (Fin 2) (Fin 2) K) = complexSymm 1 0 by
    simpa using smul_one_eq_complexSymm (1 : K)]
  congr 1
  · field_simp; ring
  · field_simp; ring

/-- Real action: `[[a, −b], [b, a]] x` is `(a + jb) (x₀ + j x₁)` in complex form. -/
@[tmio T, powerlib_foundation] theorem toComplex_complexSymm_mulVec (a b : ℝ) (x : Fin 2 → ℝ) :
    toComplex (complexSymm a b *ᵥ x) = (⟨a, b⟩ : ℂ) * toComplex x := by
  apply Complex.ext <;>
    simp [toComplex, complexSymm, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-! ## Orthogonal coordinate changes -/

/-- A coordinate change with `Aᵀ A = 1` preserves the dot product: `(A v)·(A w) = v·w`. -/
@[tmio T, powerlib_foundation] theorem orthogonal_dotProduct {m n R : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] [CommSemiring R] {A : Matrix m n R} (hA : Aᵀ * A = 1)
    (v w : n → R) : (A *ᵥ v) ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hA, vecMul_one]

end powerlib.Transform
