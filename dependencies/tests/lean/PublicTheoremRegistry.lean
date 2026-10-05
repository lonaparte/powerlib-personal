import powerlib

open powerlib

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let domains := Registry.theoremNames env (some .domain)
  let foundations := Registry.theoremNames env (some .foundation)
  for name in #[`powerlib.lcl_stable_iff, `powerlib.impedance_stable_iff,
      `powerlib.Accepted.stable, `powerlib.LCL.Accepted.stable,
      `powerlib.asymptoticallyStable_iff_resistance_pos,
      `powerlib.Accepted.globallyExponentiallyStable,
      `powerlib.Accepted.energy_derivative, `powerlib.LCL.Accepted.globallyExponentiallyStable,
      `powerlib.LCL.Accepted.globallyAsymptoticallyStable,
      `powerlib.LCL.Accepted.energy_derivative, `powerlib.LCL.trajectory_exists,
      `powerlib.LCL.trajectory_unique, `powerlib.LCL.passive_lyapunovStable,
      `powerlib.LCL.lossless_not_asymptoticallyStable,
      `powerlib.LCL.lossless_energy_conserved] do
    unless domains.contains name do
      throwError "Public domain theorem missing from public registry: {name}"
  for name in #[`powerlib.Passivity.QuadraticStorage.passiveWithStorage,
      `powerlib.Passivity.PassiveWithStorage.lyapunovStable_of_bounds,
      `powerlib.Passivity.QuadraticStorage.lyapunovStable,
      `powerlib.StateSpacePassivity.Certificate.passiveWithStorage,
      `powerlib.StateSpacePassivity.Certificate.integral_passivity,
      `powerlib.StateSpacePassivity.Certificate.lyapunovStable,
      `powerlib.StateSpacePassivity.MatrixCertificate.passiveWithStorage,
      `powerlib.StateSpacePassivity.MatrixCertificate.lyapunovStable,
      `powerlib.StateSpacePassivity.trajectory_exists,
      `powerlib.StateSpacePassivity.trajectory_unique,
      `powerlib.StateSpacePassivity.Certificate.lyapunovStableAt,
      `powerlib.RLPort.passiveWithStorage,
      `powerlib.RLPort.integral_passivity,
      `powerlib.RLPort.zeroInput_stable,
      `powerlib.RLPort.lyapunovStable,
      `powerlib.RLPort.trajectory_exists,
      `powerlib.RLPort.trajectory_unique,
      `powerlib.LCL.physical_passiveWithStorage,
      `powerlib.LCL.passive_lyapunovStable_via_ports,
      `powerlib.LCL.StorageAccepted.integral_passivity,
      `powerlib.LCL.StorageAccepted.zeroInput_stable,
      `powerlib.PortHamiltonian.passiveWithStorage,
      `powerlib.PortHamiltonian.lyapunovStable,
      `powerlib.PortHamiltonian.trajectory_exists,
      `powerlib.PortHamiltonian.trajectory_unique] do
    unless domains.contains name do
      throwError "Public passivity theorem missing from public registry: {name}"
  for name in #[`powerlib.lcl_asymptotically_stable_iff,
      `powerlib.lcl_globally_exponentially_stable_iff,
      `powerlib.LCL.passive_asymptoticallyStable, `powerlib.LCL.passive_globallyExponentiallyStable] do
    unless domains.contains name do
      throwError "Public semantic theorem missing from public registry: {name}"
  for name in #[`powerlib.state_roundtrip, `powerlib.LCL.circuit_roundtrip,
      `powerlib.generated.convert_spec, `powerlib.generated.convertLCL_spec,
      `powerlib.trajectory_iff_circuit] do
    unless foundations.contains name do
      throwError "Imported foundation theorem missing from public registry: {name}"
  unless (Registry.kindOf? env `powerlib.response).isNone do
    throwError "A definition was classified as a theorem"
  let all := Registry.theoremNames env
  unless all.size == domains.size + foundations.size do
    throwError "The public registry classification partition is incomplete"
  unless all == all.qsort Name.quickLt && all.toList.eraseDups.length == all.size do
    throwError "The public registry is not unique and deterministic"
  for name in all do
    for axiomName in Search.declarationAxioms env name do
      unless Search.allowedAxiom axiomName do
        throwError "Unapproved registered theorem axiom: {name}: {axiomName}"
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Public registry returned a non-theorem: {name}"
  logInfo "POWERLIB_PUBLIC_THEOREM_REGISTRY_OK"
