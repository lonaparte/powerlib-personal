import powerlib

example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty ι]
    (m : powerlib.StateSpacePassivity.Model ι κ)
    (c : powerlib.StateSpacePassivity.Certificate m) :
    powerlib.Passivity.LyapunovStable (powerlib.StateSpacePassivity.system m) := by
  aesop

example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (m : powerlib.StateSpacePassivity.Model ι κ)
    (c : powerlib.StateSpacePassivity.Certificate m) :
    powerlib.Passivity.PassiveWithStorage (powerlib.StateSpacePassivity.system m)
      (powerlib.StateSpacePassivity.energy c.P) := by
  aesop

#check powerlib.lcl_stable_iff
#print axioms powerlib.lcl_stable_iff
#print axioms powerlib.LCL.Accepted.stable

-- Internal pole stability for the passive canonical three-state LCL plant.
example (m : powerlib.LCL.Circuit) (hp : m.Passive) :
    (powerlib.LCL.toStateSpace m).Stable ↔
      m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0 :=
  powerlib.lcl_stable_iff m hp

example (m : powerlib.LCL.Circuit) (certificate : powerlib.LCL.Accepted m) :
    (powerlib.LCL.toStateSpace m).Stable := certificate.stable

-- Reuse stability through the equivalence between the two model descriptions.
example (m : powerlib.Impedance) :
    (powerlib.toStateSpace m).Stable ↔ m.Stable :=
  powerlib.stability_agrees m

-- A verified synthesized certificate provides a theorem about its exact model.
example (m : powerlib.Impedance) (certificate : powerlib.Accepted m) : m.Stable :=
  certificate.stable

-- The frequency-domain equations have the same voltage/current interpretation.
example (m : powerlib.Impedance) (s current voltage : ℂ) :
    (s + ((powerlib.toStateSpace m).decay : ℂ)) * current =
        ((powerlib.toStateSpace m).inputGain.val : ℂ) * voltage ↔
      voltage = m.frequency s * current :=
  powerlib.same_port_relation m s current voltage

example (m : powerlib.LCL.Circuit) (hp : m.Passive) (u vg : ℝ)
    (e : powerlib.LCL.State) (he : powerlib.LCL.IsEquilibrium m u vg e) :
    powerlib.LCL.LyapunovStable m u vg e :=
  powerlib.LCL.passive_lyapunovStable_via_ports hp he

example (m : powerlib.LCL.Circuit) (hp : m.Passive) :
    powerlib.LCL.LyapunovStable m 0 0 0 :=
  (powerlib.LCL.synthesizeStorage m hp).zeroInput_stable

example (m : powerlib.LCL.Circuit) (c : powerlib.LCL.StorageAccepted m)
    (u : ℝ → powerlib.LCL.PortInput) (x : ℝ → powerlib.LCL.State)
    (hx : powerlib.LCL.IsPortTrajectory m u x) (t : ℝ) (ht : 0 ≤ t)
    (hpower : IntervalIntegrable
      (fun s => u s 0 * x s 0 - u s 1 * x s 2) MeasureTheory.volume 0 t) :
    powerlib.LCL.portEnergy m (x t) - powerlib.LCL.portEnergy m (x 0) ≤
      ∫ s in (0 : ℝ)..t, u s 0 * x s 0 - u s 1 * x s 2 :=
  c.integral_passivity hx ht hpower

example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty ι]
    (m : powerlib.PortHamiltonian.Model ι κ) :
    powerlib.Passivity.LyapunovStable (powerlib.PortHamiltonian.system m) :=
  powerlib.PortHamiltonian.lyapunovStable m

example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (m : powerlib.PortHamiltonian.Model ι κ) (initial : powerlib.PortHamiltonian.State ι) :
    ∃ x, powerlib.Passivity.IsTrajectory (powerlib.PortHamiltonian.system m)
      (fun _ => 0) x ∧ x 0 = initial :=
  powerlib.PortHamiltonian.trajectory_exists m initial
