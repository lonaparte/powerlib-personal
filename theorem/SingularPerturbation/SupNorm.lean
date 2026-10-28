import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Linarith
import theorem.Attributes

/-! # Dot product and sup norm on `Fin m → ℝ` (foundation)

The Euclidean square `|v|² = v ⬝ᵥ v` of a real vector is at most `m` times the square of its sup
norm.

Scope.
* Real vectors `v : Fin m → ℝ`, any `m`; `‖·‖` is the default sup norm of the product space.
* No definitions, models or dynamics: an inequality between two norms on `ℝᵐ`, kept in a module
  with no library imports so that low modules can use it.

Source: comparison of the Euclidean and sup norms on `ℝᵐ` (`|v|₂² ≤ m ‖v‖∞²`), needed by the
uniform linearization of the boundary layer (`theorem/SingularPerturbation/BoundaryLayer.lean`,
work-sync theory/T-tikhonov.md §1.2) and by the action bound of the gradient-path construction
of `theorem/Stochastic/LargeDeviations.lean` (theory/T-large-deviations.md).

Results.
* `dotProduct_self_le_card_mul_norm_sq` — `v ⬝ᵥ v ≤ m ‖v‖²` (moved here from
  `theorem/SingularPerturbation/BoundaryLayer.lean`, which imports this module, under its name).

Family and connection conclusions.
* None: a generic inequality, used inside the proofs of other modules.
-/

namespace powerlib.SingularPerturbation
open Matrix

variable {m : ℕ}

/-- `|v|² ≤ m ‖v‖²` (sup norm). -/
@[tmio T, powerlib_foundation] theorem dotProduct_self_le_card_mul_norm_sq (v : Fin m → ℝ) :
    v ⬝ᵥ v ≤ m * ‖v‖ ^ 2 := by
  have h : ∀ i, v i * v i ≤ ‖v‖ ^ 2 := fun i => by
    have h1 : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
    have h2 := abs_nonneg (v i)
    nlinarith [abs_mul_abs_self (v i)]
  calc v ⬝ᵥ v = ∑ i, v i * v i := rfl
    _ ≤ ∑ _i : Fin m, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = m * ‖v‖ ^ 2 := by simp

end powerlib.SingularPerturbation
