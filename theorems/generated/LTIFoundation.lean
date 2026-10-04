-- Generated from the scoped syntax executed by Agda's field operation.
-- Agda source SHA-256: bfeda8eaf62ea856ac1e0302642f912f065f2a7b89c3abc28cb54905b16ff669
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import theorems.Attributes

namespace powerlib.generated
open scoped BigOperators

def linearField {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) : ℝ := (∑ j0, (A i j0 * x j0))

@[simp, powerlib_foundation] theorem linearField_spec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    linearField A x = A.mulVec x := rfl

end powerlib.generated
