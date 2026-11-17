import dependencies.Mathlib
import theorem.Attributes
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Real congruence preserves positive semidefiniteness

`A ⪰ 0 ⇒ B A Bᵀ ⪰ 0` for real matrices, stated once with the transpose for the covariance,
estimation and matrix-ODE modules (Mathlib states it with `conjTranspose`).

Scope.
* Generic linear algebra; real matrices over finite index types; no model.

Source: Mathlib's `Matrix.PosSemidef.mul_mul_conjTranspose_same` (`ᴴ = ᵀ` over `ℝ`).

Results.
* `posSemidef_congr` — `A ⪰ 0 ⇒ B A Bᵀ ⪰ 0`.
-/

namespace powerlib.LinearAlgebra
open Matrix

/-- **Real congruence preserves semidefiniteness**: `A ⪰ 0 ⇒ B A Bᵀ ⪰ 0`. -/
@[tmio T, powerlib_foundation] theorem posSemidef_congr {m k : Type*} [Fintype m] [Fintype k]
    {A : Matrix m m ℝ} (hA : A.PosSemidef) (B : Matrix k m ℝ) : (B * A * Bᵀ).PosSemidef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hA.mul_mul_conjTranspose_same B

end powerlib.LinearAlgebra
