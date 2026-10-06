import powerlib

noncomputable section
namespace powerlib.Tests.RLLargeSignal
open powerlib

@[powerlib_domain] theorem component_only (m : Impedance) (hR : 0 < m.resistance) (voltage : ℝ) :
    GloballyExponentiallyStable m voltage (voltage / m.resistance) := by aesop

def submittedModel : Impedance := ⟨2, ⟨1, by norm_num⟩⟩

@[powerlib_domain] theorem concrete_component_only (voltage : ℝ) :
    GloballyExponentiallyStable submittedModel voltage
      (voltage / submittedModel.resistance) := by
  have hR : 0 < submittedModel.resistance := by norm_num [submittedModel]
  aesop

@[powerlib_domain] theorem all_trajectories_decay (m : Impedance) (hR : 0 < m.resistance)
    (voltage : ℝ) (i : ℝ → ℝ) (hi : IsTrajectory m voltage i)
    (t : ℝ) (ht : 0 ≤ t) :
    (i t - voltage / m.resistance) ^ 2 =
      (i 0 - voltage / m.resistance) ^ 2 * Real.exp (-(2 * (toStateSpace m).decay * t)) := by
  let certificate := synthesize m hR
  have he : IsEquilibrium m voltage (voltage / m.resistance) :=
    equilibrium_of_resistance_ne_zero (ne_of_gt hR) voltage
  change _ = _ * Real.exp (-(certificate.rate * t))
  aesop

end powerlib.Tests.RLLargeSignal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless powerlib.Registry.kindOf? env `powerlib.rl_globally_exponentially_stable == some .domain do
    throwError "Component-only RL theorem missing from public discovery"
  for name in #[`powerlib.Tests.RLLargeSignal.component_only,
      `powerlib.Tests.RLLargeSignal.concrete_component_only,
      `powerlib.Tests.RLLargeSignal.all_trajectories_decay] do
    for axiomName in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom axiomName do
        throwError "Unapproved RL large-signal consumer axiom: {name}: {axiomName}"
  logInfo "POWERLIB_RL_LARGE_SIGNAL_OK"
