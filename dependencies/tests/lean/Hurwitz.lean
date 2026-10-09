import powerlib

open powerlib

namespace HurwitzConsumers

variable {n : ℕ}
@[powerlib_domain] theorem linear_stable_of_hurwitz (m : LTI.AutonomousModel n)
    (h : LinearSystems.IsHurwitz m.A) : LTI.ExponentiallyStable m := by aesop

@[powerlib_domain] theorem linear_hurwitz_of_stable (m : LTI.AutonomousModel n)
    (h : LTI.ExponentiallyStable m) : LinearSystems.IsHurwitz m.A := by aesop

@[powerlib_foundation] theorem spectral_of_hurwitz (A : Matrix (Fin n) (Fin n) ℝ)
    (h : LinearSystems.IsHurwitz A) : LTI.SpectrallyStable A := by powerlib_search

@[powerlib_domain] theorem linear_stable_of_spectral (m : LTI.AutonomousModel n)
    (h : LTI.SpectrallyStable m.A) : LTI.ExponentiallyStable m := by powerlib_search

@[powerlib_domain] theorem certificate_of_hurwitz (m : LTI.AutonomousModel n)
    (h : LinearSystems.IsHurwitz m.A) : Nonempty (LTI.Accepted m) := by powerlib_search

@[powerlib_domain] theorem nonlinear_small_signal_stable
    (f : Dynamics.State n → Dynamics.State n) (x_eq : Dynamics.State n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : LTI.SpectrallyStable A) : Dynamics.LocallyExponentiallyStable f x_eq := by
  powerlib_search

@[powerlib_domain] theorem nonlinear_unstable
    (f : Dynamics.State n → Dynamics.State n) (x_eq : Dynamics.State n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (s : ℂ) (hroot : (LTI.characteristicMatrix A s).det = 0) (hs : 0 < s.re) :
    Dynamics.Unstable f x_eq := by
  powerlib_search
def damped : LTI.AutonomousModel 2 := ⟨!![-1, 0; 0, -1]⟩

@[powerlib_domain] theorem damped_hurwitz : LinearSystems.IsHurwitz damped.A := by
  intro μ v hv heig
  have hcomp (j : Fin 2) : -v j = μ * v j := by
    have := congrFun heig j
    fin_cases j <;> simpa [damped, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have hμ : μ = -1 := by
    have h0 : (μ + 1) * v j = 0 := by linear_combination -(hcomp j)
    exact eq_neg_iff_add_eq_zero.mpr ((mul_eq_zero.mp h0).resolve_right hj)
  rw [hμ]
  norm_num

@[powerlib_domain] theorem damped_stable : LTI.ExponentiallyStable damped := by
  have h := damped_hurwitz
  aesop

end HurwitzConsumers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (consumer, source) in #[
      (`powerlib.LTI.accepted_nonempty_of_isHurwitz,
        `LinearSystems.IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov),
      (`powerlib.Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian,
        `hurwitz_linearization_locally_exponentially_stable),
      (`powerlib.Dynamics.unstable_of_jacobian_eigenvalue_re_pos,
        `unstable_of_exists_complex_eigenvalue_re_pos)] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) |
      throwError "Missing Hurwitz adapter proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "Adapter did not directly reuse {source}: {consumer}"
    let some entry := powerlib.Search.describe env source |
      throwError "Upstream theorem absent from discovery: {source}"
    unless entry.moduleName.getRoot == `LeanForControl && entry.kind.isNone &&
        powerlib.Search.eligible env source do
      throwError "Upstream theorem failed provenance or axiom checks: {source}"
  let mut count : Nat := 0
  for name in powerlib.Registry.theoremNames env do
    let some entry := powerlib.Search.describe env name |
      throwError "Registered theorem absent from discovery: {name}"
    if entry.moduleName == `theorem.Hurwitz then
      count := count + 1
  unless count == 13 do
    throwError "Expected 13 registered Hurwitz theorems, found {count}"
  for name in #[`powerlib.LTI.exponentiallyStable_iff_spectrallyStable,
      `powerlib.LTI.accepted_nonempty_iff_isHurwitz,
      `powerlib.Dynamics.locallyExponentiallyStable_of_spectrallyStable_jacobian,
      `powerlib.Dynamics.unstable_of_characteristic_root_re_pos] do
    unless powerlib.Registry.kindOf? env name == some .domain do
      throwError "Hurwitz domain theorem lost its classification: {name}"
  unless powerlib.Registry.kindOf? env `powerlib.LTI.spectrallyStable_iff_isHurwitz ==
      some .foundation do
    throwError "The spectral equivalence must stay a foundation result"
  logInfo "POWERLIB_HURWITZ_OK: three layers; 3 direct upstream adapters"
