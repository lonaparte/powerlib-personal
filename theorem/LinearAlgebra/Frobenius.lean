import dependencies.Mathlib
import Mathlib.Analysis.Matrix.Normed

/-! # The Frobenius norm on square real matrices: the extended-norm monoid structure

The extended-norm monoid structure of square real matrices under the Frobenius norm, defined
once for the modules that read matrix-valued limits and integrals in that norm.

Scope.
* Generic: square real matrices `Matrix (Fin n) (Fin n) ℝ` with Mathlib's Frobenius norm
  (`Matrix.Norms.Frobenius`, a scoped instance); no model.

Source: Mathlib's Frobenius matrix norm (`Mathlib.Analysis.Matrix.Normed`); the pinned Mathlib
does not derive this structure from the scoped norm, and the LeanForControl module
`LinearSystems.Stability.Continuous.LyapunovEquation` supplies it as a local instance in the
same way.

Results.
* `frobeniusENormedAddMonoid`: the `ENormedAddMonoid` structure of the Frobenius
  `NormedAddCommGroup`. It is not a global instance, since the Frobenius norm is itself scoped:
  a module enables it with `open scoped Matrix.Norms.Frobenius` and
  `attribute [local instance] powerlib.LinearAlgebra.frobeniusENormedAddMonoid`
  (`Stochastic/LyapunovCovariance`, `Estimation/KalmanPredict`, `Estimation/KalmanLTV`,
  `PowerSystem/Frequency/StochasticCOI`).
-/

noncomputable section
namespace powerlib.LinearAlgebra

open scoped Matrix.Norms.Frobenius

/-- The extended-norm monoid structure of the Frobenius norm on square real matrices; enable it
with `attribute [local instance]`. -/
abbrev frobeniusENormedAddMonoid {n : ℕ} : ENormedAddMonoid (Matrix (Fin n) (Fin n) ℝ) :=
  (NormedAddCommGroup.toENormedAddCommMonoid :
    ENormedAddCommMonoid (Matrix (Fin n) (Fin n) ℝ)).toENormedAddMonoid

end powerlib.LinearAlgebra
