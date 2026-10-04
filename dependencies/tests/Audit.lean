import powerlib

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut state : Lean.CollectAxioms.State := {}
  let roots := ([`powerlib.reciprocal_involutive, `powerlib.scale_cancel, `powerlib.state_roundtrip, `powerlib.impedance_roundtrip, `powerlib.modelEquiv, `powerlib.same_dynamics, `powerlib.same_port_relation, `powerlib.frequency_zero_iff, `powerlib.impedance_stable_iff, `powerlib.stability_agrees, `powerlib.Accepted.stable, `powerlib.Accepted.dissipation, `powerlib.response_initial, `powerlib.response_solves, `powerlib.Accepted.decay_bound, `powerlib.generated.convert_spec, `powerlib.LCL.circuit_roundtrip, `powerlib.LCL.state_roundtrip, `powerlib.LCL.modelEquiv, `powerlib.LCL.same_dynamics, `powerlib.LCL.StateSpace.matrix_mulVec, `powerlib.LCL.StateSpace.perturbation, `powerlib.LCL.characteristic_identity, `powerlib.LCL.same_characteristic, `powerlib.lcl_stable_iff, `powerlib.LCL.stability_agrees, `powerlib.LCL.hurwitz_gap, `powerlib.LCL.cubic_hurwitz, `powerlib.LCL.stable_of_hurwitz, `powerlib.LCL.passive_hurwitz, `powerlib.LCL.passive_stable_iff, `powerlib.LCL.energy_positive, `powerlib.LCL.Accepted.stable, `powerlib.LCL.Accepted.positive, `powerlib.LCL.Accepted.dissipation, `powerlib.generated.convertLCL_spec] : List Name) ++ (powerlib.Registry.theoremNames env).toList
  for root in roots do
    let (_, next) := ((Lean.CollectAxioms.collect root).run env).run state
    state := next
  for ax in state.axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom {ax}"
  logInfo "POWERLIB_KERNEL_OK"
