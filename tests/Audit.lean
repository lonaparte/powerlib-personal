import powerlib

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut state : Lean.CollectAxioms.State := {}
  for root in [`powerlib.reciprocal_involutive, `powerlib.scale_cancel, `powerlib.state_roundtrip, `powerlib.impedance_roundtrip, `powerlib.modelEquiv, `powerlib.same_dynamics, `powerlib.same_port_relation, `powerlib.frequency_zero_iff, `powerlib.impedance_stable_iff, `powerlib.stability_agrees, `powerlib.Accepted.stable, `powerlib.Accepted.dissipation, `powerlib.response_initial, `powerlib.response_solves, `powerlib.Accepted.decay_bound, `powerlib.generated.convert_spec] do
    let (_, next) := ((Lean.CollectAxioms.collect root).run env).run state
    state := next
  for ax in state.axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom {ax}"
  logInfo "POWERLIB_KERNEL_OK"
