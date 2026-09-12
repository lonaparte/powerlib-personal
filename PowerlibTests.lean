import Powerlib
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

/-! Exact examples and a transitive axiom audit, checked by `lake build`. -/

namespace Powerlib.Tests

/-- The one-dimensional family `x' = a x`. -/
def scalar (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => a

/-- This calculation uses only Mathlib, not the stability axiom. -/
theorem scalar_eigenvalue_iff (a : ℝ) (z : ℂ) :
    HasEigenvalue (scalar a) z ↔ z = (a : ℂ) := by
  simp [HasEigenvalue, Matrix.eval_charpoly, Matrix.det_fin_one, scalar,
    Matrix.scalar, Matrix.diagonal, Matrix.map, sub_eq_zero]

/-- A parameterized decision: the scalar system is stable exactly when `a < 0`. -/
theorem scalar_stable_iff (a : ℝ) : SmallSignalStable (scalar a) ↔ a < 0 := by
  rw [linear_spectral_criterion]
  constructor
  · intro h
    simpa using h (a : ℂ) ((scalar_eigenvalue_iff a (a : ℂ)).mpr rfl)
  · intro ha z hz
    rw [(scalar_eigenvalue_iff a z).mp hz]
    simpa using ha

theorem negative_mode_stable : SmallSignalStable (scalar (-1)) :=
  (scalar_stable_iff (-1)).mpr (by norm_num)

theorem positive_mode_not_stable : ¬ SmallSignalStable (scalar 1) := by
  rw [scalar_stable_iff]
  norm_num

theorem zero_mode_not_stable : ¬ SmallSignalStable (scalar 0) := by
  rw [scalar_stable_iff]
  norm_num

/-- A genuinely complex boundary case: the undamped oscillator has eigenvalue `i`.
It is not exponentially stable; no nonlinear instability claim is made. -/
theorem oscillator_not_stable :
    ¬ SmallSignalStable (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  apply not_smallSignalStable_of_eigenvalue_nonneg (z := Complex.I)
  · norm_num [HasEigenvalue, Matrix.eval_charpoly, Matrix.det_fin_two,
      Matrix.scalar, Matrix.diagonal, Matrix.map, Complex.I_mul_I]
  · simp

end Powerlib.Tests

/- Fail the build on any additional axiom, including transitive `sorryAx` or
native evaluation axioms. A subset of the allowed logical axioms is sufficient. -/
run_cmd do
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound, ``Powerlib.linear_spectral_criterion]
  let env ← Lean.getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    if (`Powerlib).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
      count := count + 1
  unless count > 0 do
    throwError "No Powerlib declarations were audited"
  logInfo m!"Axiom audit passed for {count} Powerlib declarations; one domain axiom is allowed."
