import powerlib

namespace DynamicsAutomation
open powerlib.Dynamics

@[powerlib_domain] theorem nonlinear_exponential (n : ℕ) :
    GloballyExponentiallyStable (@Nonlinear.field n) 0 := by aesop

@[powerlib_domain] theorem nonlinear_asymptotic {n : ℕ} (hn : 0 < n) :
    GloballyAsymptoticallyStable (@Nonlinear.field n) 0 := by aesop

@[powerlib_domain] theorem nonlinear_segment_bound {n : ℕ} {φ : ℝ → State n} {a b t : ℝ}
    (hφ : powerlib.Dynamics.IsTrajectoryOn φ (@Nonlinear.field n) a b) (ht : t ∈ Set.Icc a b) :
    ‖φ t‖ ≤ Real.exp (-(t - a)) * ‖φ a‖ := by aesop

@[powerlib_domain] theorem polynomial_complete {model : Polynomial2.Model} (c : Polynomial2.Accepted model) :
    ForwardComplete model.field := by aesop

@[powerlib_domain] theorem polynomial_exponential {model : Polynomial2.Model} (c : Polynomial2.Accepted model) :
    GloballyExponentiallyStable model.field 0 := by aesop

@[powerlib_domain] theorem polynomial_asymptotic {model : Polynomial2.Model} (c : Polynomial2.Accepted model) :
    GloballyAsymptoticallyStable model.field 0 := by aesop

@[powerlib_domain] theorem polynomial_complete_semantics {model : Polynomial2.Model}
    (c : Polynomial2.Accepted model) :
    ForwardComplete model.field ∧ GloballyExponentiallyStable model.field 0 ∧
      GloballyAsymptoticallyStable model.field 0 := by aesop

end DynamicsAutomation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants do
    if name.getRoot == `DynamicsAutomation && info.isTheorem then
      count := count + 1
      for ax in powerlib.Search.declarationAxioms env name do
        unless powerlib.Search.allowedAxiom ax do
          throwError "Native dynamics automation used an unapproved axiom: {name}: {ax}"
  unless count == 7 do throwError "Missing native nonlinear or polynomial consumer"
  logInfo "POWERLIB_DYNAMICS_AUTOMATION_OK: 7 native consumers"
