import powerlib

open powerlib Filter
open scoped Topology

namespace NativeConsumers
@[powerlib_foundation] theorem rl_roundtrip (m : Impedance) : toImpedance (toStateSpace m) = m := by simp

@[powerlib_domain] theorem rl_stability_sign (m : Impedance) : m.Stable ↔ 0 < m.resistance := by simp

@[powerlib_foundation] theorem rl_stability_transport (m : Impedance) :
    (toStateSpace m).Stable ↔ m.Stable := by simp

@[powerlib_foundation] theorem rl_zero_equilibrium (m : Impedance) : IsEquilibrium m 0 0 := by simp

@[powerlib_domain] theorem rl_certificate_stable (m : Impedance) (c : Accepted m) : m.Stable := by aesop

@[powerlib_domain] theorem rl_certificate_asymptotic (m : Impedance) (c : Accepted m) :
    AsymptoticallyStable m 0 0 := by
  have he : IsEquilibrium m 0 0 := by simp
  aesop

@[powerlib_domain] theorem rl_certificate_lyapunov (m : Impedance) (c : Accepted m) (v e : ℝ) (he : IsEquilibrium m v e) :
    LyapunovStable m v e := by aesop

@[powerlib_domain] theorem rl_certificate_global_asymptotic (m : Impedance) (c : Accepted m) (v e : ℝ) (he : IsEquilibrium m v e) :
    GloballyAsymptoticallyStable m v e := by aesop

@[powerlib_domain] theorem rl_certificate_exponential (m : Impedance) (c : Accepted m) (v e : ℝ) (he : IsEquilibrium m v e) :
    GloballyExponentiallyStable m v e := by aesop

@[powerlib_domain] theorem rl_asymptotic_characterization (m : Impedance) (v e : ℝ) (he : IsEquilibrium m v e) :
    AsymptoticallyStable m v e ↔ 0 < m.resistance := by aesop

@[powerlib_domain] theorem rl_forward_existence (m : Impedance) (v e initial : ℝ) (he : IsEquilibrium m v e) :
    ∃ i, IsTrajectory m v i ∧ i 0 = initial := by aesop

@[powerlib_domain] theorem rl_trajectory_convergence (m : Impedance) (hm : m.Stable) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) :
    Tendsto i atTop (𝓝 e) := by aesop

@[powerlib_domain] theorem rl_trajectory_decay (m : Impedance) (c : Accepted m) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) (t : ℝ) (ht : 0 ≤ t) :
    (i t - e) ^ 2 = (i 0 - e) ^ 2 * Real.exp (-(c.rate * t)) := by aesop

@[powerlib_domain] theorem rl_energy_derivative (m : Impedance) (c : Accepted m) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => energy c.p (i s - e)) (-(i t - e) ^ 2) (Set.Ici 0) t := by
  aesop

@[powerlib_foundation] theorem lcl_roundtrip (m : LCL.Circuit) : LCL.toCircuit (LCL.toStateSpace m) = m := by simp
@[powerlib_domain] theorem lcl_certificate_pole_stable (m : LCL.Circuit) (c : LCL.Accepted m) :
    (LCL.toStateSpace m).Stable := by aesop
@[powerlib_domain] theorem lcl_certificate_energy_positive (m : LCL.Circuit) (c : LCL.Accepted m) (x y z : ℝ)
    (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : 0 < LCL.energy c.p x y z := by aesop
@[powerlib_domain] theorem lcl_certificate_energy_derivative (m : LCL.Circuit) (c : LCL.Accepted m) (x y z : ℝ) :
    let f := (LCL.toStateSpace m).field x y z 0 0
    LCL.energyDerivative c.p x y z f.1 f.2.1 f.2.2 = -(x^2+y^2+z^2) := by aesop

@[powerlib_domain] theorem lcl_certificate_exponential (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.GloballyExponentiallyStable m u vg e := by aesop

@[powerlib_domain] theorem lcl_certificate_global_asymptotic (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.GloballyAsymptoticallyStable m u vg e := by aesop

@[powerlib_domain] theorem lcl_certificate_asymptotic (m : LCL.Circuit) (c : LCL.Accepted m) :
    LCL.AsymptoticallyStable m 0 0 0 := by
  have he : LCL.IsEquilibrium m 0 0 0 := by simp
  aesop

@[powerlib_domain] theorem lcl_forward_existence (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (initial : LCL.State) :
    ∃ x, LCL.IsTrajectory m u vg x ∧ x 0 = initial := by aesop

@[powerlib_domain] theorem lcl_trajectory_convergence (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (x : ℝ → LCL.State) (he : LCL.IsEquilibrium m u vg e) (hx : LCL.IsTrajectory m u vg x) :
    Tendsto x atTop (𝓝 e) := by aesop

@[powerlib_domain] theorem lcl_shifted_energy_derivative (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (x : ℝ → LCL.State) (he : LCL.IsEquilibrium m u vg e) (hx : LCL.IsTrajectory m u vg x)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => LCL.quadraticEnergy c.p (x s - e))
      (-LCL.squaredSize (x t - e)) (Set.Ici 0) t := by aesop

@[powerlib_domain] theorem lcl_passive_lyapunov (m : LCL.Circuit) (hp : m.Passive) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) : LCL.LyapunovStable m u vg e := by
  let gc := (LCL.physicalStateSpaceCertificate m hp).toCertificate
  have hg : StateSpacePassivity.IsEquilibrium (LCL.terminalStateSpace m) ![u, vg] e := by
    simpa only [LCL.terminalStateSpace_equilibrium_iff] using he
  clear_value gc
  clear hp
  have hs : StateSpacePassivity.LyapunovStableAt (LCL.terminalStateSpace m) ![u, vg] e := by
    aesop (config := { enableSimp := false })
  simpa only [LCL.terminalStateSpace_stability_iff] using hs

@[powerlib_domain] theorem lcl_lossless_not_asymptotic (m : LCL.Circuit) (h1 : m.first.resistance = 0) (h2 : m.second.resistance = 0)
    (u vg : ℝ) (e : LCL.State) (he : LCL.IsEquilibrium m u vg e) :
    ¬ LCL.AsymptoticallyStable m u vg e := by aesop

@[powerlib_domain] theorem lcl_damped_asymptotic (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) :
    LCL.AsymptoticallyStable m 0 0 0 := by
  have he : LCL.IsEquilibrium m 0 0 0 := by simp
  aesop

@[powerlib_domain] theorem lcl_damped_exponential (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.GloballyExponentiallyStable m u vg e := by aesop

@[powerlib_domain] theorem lcl_asymptotic_characterization (m : LCL.Circuit) (hp : m.Passive) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.AsymptoticallyStable m u vg e ↔ m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0 := by
  aesop

@[powerlib_domain] theorem lcl_storage_zero_stable (m : LCL.Circuit) (c : LCL.StorageAccepted m) :
    LCL.LyapunovStable m 0 0 0 := by
  let gc := c.stateSpaceCertificate
  have hs : Passivity.LyapunovStable
      (StateSpacePassivity.system (LCL.terminalStateSpace m)) := by aesop
  apply LCL.lyapunovStable_of_portSystem
    (by simpa only [LCL.terminalStateSpace_system] using hs)
  simp

@[powerlib_domain] theorem lcl_storage_passive (m : LCL.Circuit) (c : LCL.StorageAccepted m) :
    Passivity.PassiveWithStorage (LCL.portSystem m) (LCL.portEnergy m) := by
  let gc := c.stateSpaceCertificate
  have hp : Passivity.PassiveWithStorage
      (StateSpacePassivity.system (LCL.terminalStateSpace m))
      (StateSpacePassivity.energy gc.P) := by aesop
  simpa only [gc, LCL.terminalStateSpace_system, LCL.StorageAccepted.stateSpaceCertificate_matrix,
    LCL.terminalStateSpace_energy_function] using hp

@[powerlib_domain] theorem rl_port_state_space_passive (m : Impedance) (hR : 0 ≤ m.resistance) :
    Passivity.PassiveWithStorage (StateSpacePassivity.system (RLPort.stateSpace m))
      (StateSpacePassivity.energy (RLPort.synthesizePassivityCertificate m hR).P) := by
  let gc := RLPort.synthesizePassivityCertificate m hR
  aesop

@[powerlib_domain] theorem rl_port_state_space_stable (m : Impedance) (hR : 0 ≤ m.resistance) :
    Passivity.LyapunovStable (StateSpacePassivity.system (RLPort.stateSpace m)) := by
  let gc := RLPort.synthesizePassivityCertificate m hR
  aesop

@[powerlib_domain] theorem rl_port_lyapunov (m : Impedance) (hR : 0 ≤ m.resistance) (v e : ℝ)
    (he : IsEquilibrium m v e) : LyapunovStable m v e := by
  let gc := RLPort.synthesizePassivityCertificate m hR
  have hg := RLPort.equilibrium_to_generic he
  have hs : StateSpacePassivity.LyapunovStableAt
      (RLPort.stateSpace m) (RLPort.toState v) (RLPort.toState e) := by aesop
  exact RLPort.lyapunovStable_of_genericAt hs

@[powerlib_domain] theorem ph_lyapunov {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty ι]
    (m : PortHamiltonian.Model ι κ) :
    Passivity.LyapunovStable (PortHamiltonian.system m) := by
  let gc := PortHamiltonian.certificate m
  have hs : Passivity.LyapunovStable
      (StateSpacePassivity.system (PortHamiltonian.linearModel m)) := by aesop
  simpa only [PortHamiltonian.system_eq] using hs

@[powerlib_domain] theorem ph_passive {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (m : PortHamiltonian.Model ι κ) :
    Passivity.PassiveWithStorage (PortHamiltonian.system m) (PortHamiltonian.energy m) := by
  let gc := PortHamiltonian.certificate m
  have hp : Passivity.PassiveWithStorage
      (StateSpacePassivity.system (PortHamiltonian.linearModel m))
      (StateSpacePassivity.energy gc.P) := by aesop
  simpa only [gc, PortHamiltonian.system_eq, PortHamiltonian.certificate_P,
    PortHamiltonian.energy_fun_eq] using hp


@[powerlib_domain] theorem ph_model_semantic_contract {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty ι] (m : PortHamiltonian.Model ι κ) :
    Passivity.PassiveWithStorage (PortHamiltonian.system m) (PortHamiltonian.energy m) ∧
      Passivity.LyapunovStable (PortHamiltonian.system m) := by aesop

@[powerlib_domain] theorem ph_constructed_response_contract {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : PortHamiltonian.Model ι κ) (initial : ι → ℝ) (t : ℝ) :
    HasDerivAt (PortHamiltonian.response m initial)
      (PortHamiltonian.operator m (PortHamiltonian.response m initial t)) t ∧
      Passivity.IsTrajectory (PortHamiltonian.system m) (fun _ => 0)
        (PortHamiltonian.response m initial) ∧
      PortHamiltonian.response m initial 0 = initial := by aesop

@[powerlib_foundation] theorem ph_energy_and_damping {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : PortHamiltonian.Model ι κ) (x : ι → ℝ) (hx : x ≠ 0) :
    0 < PortHamiltonian.energy m x ∧ 0 ≤ PortHamiltonian.dampingPower m x := by aesop

noncomputable def losslessPHModel : PortHamiltonian.Model (Fin 1) (Fin 1) where
  J := 0
  d := fun _ => 0
  w := fun _ => 1
  B := fun _ _ => 1
  skew := by simp
  damping_nonneg := by intro i; norm_num
  weights_pos := by intro i; norm_num

@[powerlib_domain] theorem concrete_lossless_ph_semantics :
    Passivity.PassiveWithStorage (PortHamiltonian.system losslessPHModel)
      (PortHamiltonian.energy losslessPHModel) ∧
      Passivity.LyapunovStable (PortHamiltonian.system losslessPHModel) := by aesop

@[powerlib_domain] theorem concrete_lossless_ph_forward_solution (initial : Fin 1 → ℝ) :
    ∃ x, Passivity.IsTrajectory (PortHamiltonian.system losslessPHModel)
      (fun _ => 0) x ∧ x 0 = initial := by aesop

end NativeConsumers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants do
    if name.getRoot == `NativeConsumers && info.isTheorem then
      for axiomName in powerlib.Search.declarationAxioms env name do
        unless powerlib.Search.allowedAxiom axiomName do
          throwError "Unexpected native consumer axiom: {name}: {axiomName}"
  for (consumer, source) in #[
      (`NativeConsumers.rl_port_state_space_passive,
        `powerlib.StateSpacePassivity.Certificate.passiveWithStorage),
      (`NativeConsumers.rl_port_state_space_stable,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable),
      (`NativeConsumers.lcl_storage_passive,
        `powerlib.StateSpacePassivity.Certificate.passiveWithStorage),
      (`NativeConsumers.lcl_storage_zero_stable,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable),
      (`NativeConsumers.ph_passive,
        `powerlib.StateSpacePassivity.Certificate.passiveWithStorage),
      (`NativeConsumers.ph_lyapunov,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable)] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing case consumer proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "Case consumer did not directly use the general state-space theorem {source}"
  for consumer in #[`NativeConsumers.rl_port_lyapunov, `NativeConsumers.lcl_passive_lyapunov] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing equilibrium case proof: {consumer}"
    unless #[`powerlib.StateSpacePassivity.Certificate.lyapunovStableAt,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable].any
        proof.getUsedConstants.contains do
      throwError "Equilibrium case did not use general certificate stability: {consumer}"
  logInfo "POWERLIB_NATIVE_THEOREM_USE_OK"
