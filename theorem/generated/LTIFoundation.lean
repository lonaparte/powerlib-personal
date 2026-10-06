-- Generated from the Agda-normalized executable conversion.
-- Agda source SHA-256: 9697800c1f6ee455dac7af1fcaebca45c88fdbd043f0bbd67167ccb6fd5ba573
import dependencies.Mathlib
import theorem.Attributes

namespace powerlib.generated
open scoped BigOperators

def linearField {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) : ℝ := (∑ j0, (A i j0 * x j0))

@[simp, powerlib_foundation] theorem linearField_spec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    linearField A x = A.mulVec x := rfl

end powerlib.generated
