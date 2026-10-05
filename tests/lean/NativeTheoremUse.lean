import powerlib

open powerlib Filter
open scoped Topology

namespace NativeConsumers
theorem rl_roundtrip (m : Impedance) : toImpedance (toStateSpace m) = m := by simp

theorem rl_stability_sign (m : Impedance) : m.Stable ↔ 0 < m.resistance := by simp

theorem rl_stability_transport (m : Impedance) :
    (toStateSpace m).Stable ↔ m.Stable := by simp

theorem rl_zero_equilibrium (m : Impedance) : IsEquilibrium m 0 0 := by simp

theorem rl_certificate_stable (m : Impedance) (c : Accepted m) : m.Stable := by aesop

theorem rl_certificate_asymptotic (m : Impedance) (c : Accepted m) :
    AsymptoticallyStable m 0 0 := by
  have he : IsEquilibrium m 0 0 := by simp
  exact?

theorem rl_certificate_lyapunov (m : Impedance) (c : Accepted m) (v e : ℝ) (he : IsEquilibrium m v e) :
    LyapunovStable m v e := by exact?

theorem rl_certificate_global_asymptotic (m : Impedance) (c : Accepted m) (v e : ℝ) (he : IsEquilibrium m v e) :
    GloballyAsymptoticallyStable m v e := by exact?

theorem rl_certificate_exponential (m : Impedance) (c : Accepted m) (v e : ℝ) (he : IsEquilibrium m v e) :
    GloballyExponentiallyStable m v e := by exact?

theorem rl_asymptotic_characterization (m : Impedance) (v e : ℝ) (he : IsEquilibrium m v e) :
    AsymptoticallyStable m v e ↔ 0 < m.resistance := by exact?

theorem rl_forward_existence (m : Impedance) (v e initial : ℝ) (he : IsEquilibrium m v e) :
    ∃ i, IsTrajectory m v i ∧ i 0 = initial := by exact?

theorem rl_trajectory_convergence (m : Impedance) (hm : m.Stable) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) :
    Tendsto i atTop (𝓝 e) := by exact?

theorem rl_trajectory_decay (m : Impedance) (c : Accepted m) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) (t : ℝ) (ht : 0 ≤ t) :
    (i t - e) ^ 2 = (i 0 - e) ^ 2 * Real.exp (-(c.rate * t)) := by exact?

theorem rl_energy_derivative (m : Impedance) (c : Accepted m) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => energy c.p (i s - e)) (-(i t - e) ^ 2) (Set.Ici 0) t := by
  exact?

theorem lcl_roundtrip (m : LCL.Circuit) : LCL.toCircuit (LCL.toStateSpace m) = m := by simp
theorem lcl_certificate_pole_stable (m : LCL.Circuit) (c : LCL.Accepted m) :
    (LCL.toStateSpace m).Stable := by aesop
theorem lcl_certificate_energy_positive (m : LCL.Circuit) (c : LCL.Accepted m) (x y z : ℝ)
    (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : 0 < LCL.energy c.p x y z := by exact?
theorem lcl_certificate_energy_derivative (m : LCL.Circuit) (c : LCL.Accepted m) (x y z : ℝ) :
    let f := (LCL.toStateSpace m).field x y z 0 0
    LCL.energyDerivative c.p x y z f.1 f.2.1 f.2.2 = -(x^2+y^2+z^2) := by exact?

theorem lcl_certificate_exponential (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.GloballyExponentiallyStable m u vg e := by exact?

theorem lcl_certificate_global_asymptotic (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.GloballyAsymptoticallyStable m u vg e := by exact?

theorem lcl_certificate_asymptotic (m : LCL.Circuit) (c : LCL.Accepted m) :
    LCL.AsymptoticallyStable m 0 0 0 := by
  have he : LCL.IsEquilibrium m 0 0 0 := by simp
  exact?

theorem lcl_forward_existence (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (initial : LCL.State) :
    ∃ x, LCL.IsTrajectory m u vg x ∧ x 0 = initial := by exact?

theorem lcl_trajectory_convergence (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (x : ℝ → LCL.State) (he : LCL.IsEquilibrium m u vg e) (hx : LCL.IsTrajectory m u vg x) :
    Tendsto x atTop (𝓝 e) := by exact?

theorem lcl_shifted_energy_derivative (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (x : ℝ → LCL.State) (he : LCL.IsEquilibrium m u vg e) (hx : LCL.IsTrajectory m u vg x)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => LCL.quadraticEnergy c.p (x s - e))
      (-LCL.squaredSize (x t - e)) (Set.Ici 0) t := by exact?

theorem lcl_passive_lyapunov (m : LCL.Circuit) (hp : m.Passive) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) : LCL.LyapunovStable m u vg e := by
  let gc := (LCL.physicalStateSpaceCertificate m hp).toCertificate
  have hg : StateSpacePassivity.IsEquilibrium (LCL.terminalStateSpace m) ![u, vg] e := by
    simpa only [LCL.terminalStateSpace_equilibrium_iff] using he
  have hs : StateSpacePassivity.LyapunovStableAt (LCL.terminalStateSpace m) ![u, vg] e := by
    exact?
  simpa only [LCL.terminalStateSpace_stability_iff] using hs

theorem lcl_lossless_not_asymptotic (m : LCL.Circuit) (h1 : m.first.resistance = 0) (h2 : m.second.resistance = 0)
    (u vg : ℝ) (e : LCL.State) (he : LCL.IsEquilibrium m u vg e) :
    ¬ LCL.AsymptoticallyStable m u vg e := by exact?

theorem lcl_damped_asymptotic (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) :
    LCL.AsymptoticallyStable m 0 0 0 := by
  have he : LCL.IsEquilibrium m 0 0 0 := by simp
  exact?

theorem lcl_damped_exponential (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.GloballyExponentiallyStable m u vg e := by exact?

theorem lcl_asymptotic_characterization (m : LCL.Circuit) (hp : m.Passive) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.AsymptoticallyStable m u vg e ↔ m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0 := by
  exact?

theorem lcl_storage_zero_stable (m : LCL.Circuit) (c : LCL.StorageAccepted m) :
    LCL.LyapunovStable m 0 0 0 := by
  let gc := c.stateSpaceCertificate
  have hs : Passivity.LyapunovStable
      (StateSpacePassivity.system (LCL.terminalStateSpace m)) := by aesop
  apply LCL.lyapunovStable_of_portSystem
    (by simpa only [LCL.terminalStateSpace_system] using hs)
  simp

theorem lcl_storage_passive (m : LCL.Circuit) (c : LCL.StorageAccepted m) :
    Passivity.PassiveWithStorage (LCL.portSystem m) (LCL.portEnergy m) := by
  let gc := c.stateSpaceCertificate
  have hp : Passivity.PassiveWithStorage
      (StateSpacePassivity.system (LCL.terminalStateSpace m))
      (StateSpacePassivity.energy gc.P) := by exact?
  simpa only [gc, LCL.terminalStateSpace_system, LCL.StorageAccepted.stateSpaceCertificate_matrix,
    LCL.terminalStateSpace_energy_function] using hp

theorem rl_port_state_space_passive (m : Impedance) (hR : 0 ≤ m.resistance) :
    Passivity.PassiveWithStorage (StateSpacePassivity.system (RLPort.stateSpace m))
      (StateSpacePassivity.energy (RLPort.synthesizePassivityCertificate m hR).P) := by
  let gc := RLPort.synthesizePassivityCertificate m hR
  aesop

theorem rl_port_state_space_stable (m : Impedance) (hR : 0 ≤ m.resistance) :
    Passivity.LyapunovStable (StateSpacePassivity.system (RLPort.stateSpace m)) := by
  let gc := RLPort.synthesizePassivityCertificate m hR
  aesop

theorem rl_port_lyapunov (m : Impedance) (hR : 0 ≤ m.resistance) (v e : ℝ)
    (he : IsEquilibrium m v e) : LyapunovStable m v e := by
  let gc := RLPort.synthesizePassivityCertificate m hR
  have hg := RLPort.equilibrium_to_generic he
  have hs : StateSpacePassivity.LyapunovStableAt
      (RLPort.stateSpace m) (RLPort.toState v) (RLPort.toState e) := by aesop
  exact RLPort.lyapunovStable_of_genericAt hs

theorem ph_lyapunov {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty ι]
    (m : PortHamiltonian.Model ι κ) :
    Passivity.LyapunovStable (PortHamiltonian.system m) := by
  let gc := PortHamiltonian.certificate m
  have hs : Passivity.LyapunovStable
      (StateSpacePassivity.system (PortHamiltonian.linearModel m)) := by exact?
  simpa only [PortHamiltonian.system_eq] using hs

theorem ph_passive {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (m : PortHamiltonian.Model ι κ) :
    Passivity.PassiveWithStorage (PortHamiltonian.system m) (PortHamiltonian.energy m) := by
  let gc := PortHamiltonian.certificate m
  have hp : Passivity.PassiveWithStorage
      (StateSpacePassivity.system (PortHamiltonian.linearModel m))
      (StateSpacePassivity.energy gc.P) := by exact?
  simpa only [gc, PortHamiltonian.system_eq, PortHamiltonian.certificate_P,
    PortHamiltonian.energy_fun_eq] using hp

end NativeConsumers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut state : Lean.CollectAxioms.State := {}
  for (name, info) in env.constants do
    if name.getRoot == `NativeConsumers && info.isTheorem then
      let (_, next) := ((Lean.CollectAxioms.collect name).run env).run state
      state := next
  for ax in state.axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected native consumer axiom: {ax}"
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
    let some proof := info.value? | throwError "Missing case consumer proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "Case consumer did not directly use the general state-space theorem {source}"
  for consumer in #[`NativeConsumers.rl_port_lyapunov, `NativeConsumers.lcl_passive_lyapunov] do
    let info ← getConstInfo consumer
    let some proof := info.value? | throwError "Missing equilibrium case proof: {consumer}"
    unless #[`powerlib.StateSpacePassivity.Certificate.lyapunovStableAt,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable].any
        proof.getUsedConstants.contains do
      throwError "Equilibrium case did not use general certificate stability: {consumer}"
  logInfo "POWERLIB_NATIVE_THEOREM_USE_OK"
