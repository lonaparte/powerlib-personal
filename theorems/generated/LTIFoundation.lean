-- Generated from the normalized Agda executable field operation.
-- Agda source SHA-256: 89a92146a14721e9c76faace5197d5e29c97aa0286e3c62eae882447959628d0
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import theorems.Attributes

namespace powerlib.generated
open scoped BigOperators

def linearField {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) : ℝ := ∑ j, (A i j * x j)

@[simp, powerlib_foundation] theorem linearField_spec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    linearField A x = A.mulVec x := rfl

end powerlib.generated
