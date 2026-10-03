import Powerlib

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut state : Lean.CollectAxioms.State := {}
  for root in [`Powerlib.reciprocal_involutive, `Powerlib.scale_cancel, `Powerlib.state_roundtrip, `Powerlib.impedance_roundtrip, `Powerlib.modelEquiv, `Powerlib.same_dynamics, `Powerlib.same_port_relation, `Powerlib.frequency_zero_iff, `Powerlib.impedance_stable_iff, `Powerlib.stability_agrees, `Powerlib.Accepted.stable, `Powerlib.Accepted.dissipation, `Powerlib.response_initial, `Powerlib.response_solves, `Powerlib.Accepted.decay_bound, `Powerlib.Generated.convert_spec] do
    let (_, next) := ((Lean.CollectAxioms.collect root).run env).run state
    state := next
  for ax in state.axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom {ax}"
  logInfo "POWERLIB_KERNEL_OK"
