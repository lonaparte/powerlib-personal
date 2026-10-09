import dependencies.Mathlib
import theorem.LCLPassivity
import theorem.Passivity
import theorem.StateSpaceTrajectories

noncomputable section
namespace powerlib.LCL
open Set Filter
open MeasureTheory
open scoped Topology

abbrev PortInput := Fin 2 → ℝ

def terminalStateSpace (m : Circuit) :
    powerlib.LTI.Model (Fin 3) (Fin 2) where
  A := (toStateSpace m).matrix
  B := ![![(toStateSpace m).first.inputGain.val, 0],
    ![0, 0], ![0, -(toStateSpace m).second.inputGain.val]]
  C := ![![1, 0, 0], ![0, 0, -1]]
  D := 0

def physicalStorageMatrix (m : Circuit) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![m.first.inductance.val, m.capacitance.val,
    m.second.inductance.val]

@[powerlib_foundation] theorem terminalStateSpace_field (m : Circuit)
    (x : State) (u : PortInput) :
    powerlib.LTI.Model.field (terminalStateSpace m) x u =
      (toStateSpace m).vectorField (u 0) (u 1) x := by
  ext i
  fin_cases i <;>
    simp [powerlib.LTI.Model.field, terminalStateSpace,
      StateSpace.matrix, StateSpace.vectorField, StateSpace.field,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

@[simp, powerlib_foundation] theorem terminalStateSpace_output (m : Circuit)
    (x : State) (u : PortInput) :
    powerlib.LTI.Model.output (terminalStateSpace m) x u = ![x 0, -x 2] := by
  ext i
  fin_cases i <;>
    simp [powerlib.LTI.Model.output, terminalStateSpace,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def portSystem (m : Circuit) : powerlib.Passivity.System State (Fin 2) where
  field x u := (toStateSpace m).vectorField (u 0) (u 1) x
  output x _ := ![x 0, -x 2]

@[powerlib_foundation] theorem terminalStateSpace_system (m : Circuit) :
    powerlib.StateSpacePassivity.system (terminalStateSpace m) = portSystem m := by
  unfold powerlib.StateSpacePassivity.system portSystem
  congr 1
  · funext x u
    exact terminalStateSpace_field m x u
  · funext x u
    exact terminalStateSpace_output m x u

@[powerlib_foundation] theorem physicalStorageMatrix_posDef (m : Circuit) :
    (physicalStorageMatrix m).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i
  · exact m.first.inductance.property
  · exact m.capacitance.property
  · exact m.second.inductance.property

@[powerlib_foundation] theorem physicalStorageMatrix_dissipation (m : Circuit) :
    -(physicalStorageMatrix m * (terminalStateSpace m).A +
      (terminalStateSpace m).A.transpose * physicalStorageMatrix m) =
      Matrix.diagonal ![2 * m.first.resistance, 0, 2 * m.second.resistance] := by
  ext i j
  simp only [physicalStorageMatrix, Matrix.neg_apply, Matrix.add_apply]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [terminalStateSpace, StateSpace.matrix, toStateSpace,
      generated.convertLCL, powerlib.reciprocal] <;>
    field_simp [ne_of_gt m.first.inductance.property,
      ne_of_gt m.second.inductance.property, ne_of_gt m.capacitance.property] <;> ring

@[powerlib_foundation] theorem physicalStorageMatrix_collocated (m : Circuit) :
    physicalStorageMatrix m * (terminalStateSpace m).B =
      (terminalStateSpace m).C.transpose := by
  ext i j
  rw [physicalStorageMatrix, Matrix.diagonal_mul, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [terminalStateSpace, toStateSpace, generated.convertLCL,
      powerlib.reciprocal] <;>
    field_simp [ne_of_gt m.first.inductance.property,
      ne_of_gt m.second.inductance.property, ne_of_gt m.capacitance.property]

def physicalStateSpaceCertificate (m : Circuit) (hp : m.Passive) :
    powerlib.StateSpacePassivity.CollocatedCertificate (terminalStateSpace m) where
  P := physicalStorageMatrix m
  positive := physicalStorageMatrix_posDef m
  dissipation := by
    rw [physicalStorageMatrix_dissipation]
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> simp <;> linarith [hp.1, hp.2]
  collocated := physicalStorageMatrix_collocated m
  feedthrough := Matrix.PosSemidef.zero

def IsPortTrajectory (m : Circuit) (u : ℝ → PortInput) (x : ℝ → State) : Prop :=
  ∀ t ∈ Ici (0 : ℝ),
    HasDerivWithinAt x ((toStateSpace m).vectorField (u t 0) (u t 1) (x t)) (Ici 0) t

@[powerlib_foundation] theorem portTrajectory_iff_generic (m : Circuit)
    (u : ℝ → PortInput) (x : ℝ → State) :
    IsPortTrajectory m u x ↔ powerlib.Passivity.IsTrajectory (portSystem m) u x :=
  Iff.rfl

@[powerlib_foundation] theorem portTrajectory_iff_circuit (m : Circuit)
    (u : ℝ → PortInput) (x : ℝ → State) :
    IsPortTrajectory m u x ↔ ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ![(u t 0 - m.first.resistance * x t 0 - x t 1) / m.first.inductance.val,
        (x t 0 - x t 2) / m.capacitance.val,
        (x t 1 - m.second.resistance * x t 2 - u t 1) / m.second.inductance.val]
      (Ici 0) t := by
  simp only [IsPortTrajectory, StateSpace.vectorField, same_dynamics]

@[powerlib_foundation] theorem portTrajectory_constant_iff (m : Circuit)
    (u vg : ℝ) (x : ℝ → State) :
    powerlib.Passivity.IsTrajectory (portSystem m) (fun _ => ![u, vg]) x ↔
      IsTrajectory m u vg x :=
  Iff.rfl

@[simp, powerlib_foundation] theorem terminalStateSpace_trajectory_iff (m : Circuit)
    (u vg : ℝ) (x : ℝ → State) :
    powerlib.Passivity.IsTrajectory (powerlib.StateSpacePassivity.system (terminalStateSpace m))
      (fun _ => ![u, vg]) x ↔ IsTrajectory m u vg x := by
  rw [terminalStateSpace_system]
  exact portTrajectory_constant_iff m u vg x

@[simp, powerlib_foundation] theorem terminalStateSpace_equilibrium_iff (m : Circuit)
    (u vg : ℝ) (e : State) :
    (terminalStateSpace m).IsEquilibrium ![u, vg] e ↔
      IsEquilibrium m u vg e := by
  simp [powerlib.LTI.Model.IsEquilibrium, terminalStateSpace_field,
    IsEquilibrium]

@[simp, powerlib_foundation] theorem terminalStateSpace_stability_iff (m : Circuit)
    (u vg : ℝ) (e : State) :
    powerlib.StateSpacePassivity.LyapunovStableAt (terminalStateSpace m) ![u, vg] e ↔
      LyapunovStable m u vg e := by
  simp only [powerlib.StateSpacePassivity.LyapunovStableAt, LyapunovStable,
    terminalStateSpace_trajectory_iff]

def portEnergy (m : Circuit) (x : State) : ℝ :=
  quadraticEnergy (physicalWeights m) x / 2

def portEnergyRate (m : Circuit) (x : State) (u : PortInput) : ℝ :=
  u 0 * x 0 - u 1 * x 2 - m.first.resistance * (x 0) ^ 2 -
    m.second.resistance * (x 2) ^ 2

@[simp, powerlib_foundation] theorem terminalStateSpace_energy (m : Circuit) (x : State) :
    powerlib.StateSpacePassivity.energy (physicalStorageMatrix m) x = portEnergy m x := by
  simp [powerlib.StateSpacePassivity.energy, powerlib.LTI.energy, physicalStorageMatrix,
    portEnergy, quadraticEnergy, energy, physicalWeights,
    Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ]
  ring

@[simp, powerlib_foundation] theorem terminalStateSpace_energy_function (m : Circuit) :
    powerlib.StateSpacePassivity.energy (physicalStorageMatrix m) = portEnergy m :=
  funext (terminalStateSpace_energy m)

@[powerlib_foundation] theorem terminalStateSpace_energyRate (m : Circuit)
    (x : State) (u : PortInput) :
    dotProduct ((physicalStorageMatrix m).mulVec x)
      (powerlib.LTI.Model.field (terminalStateSpace m) x u) =
      portEnergyRate m x u := by
  rw [terminalStateSpace_field]
  simp [physicalStorageMatrix, Matrix.mulVec_diagonal, dotProduct,
    Fin.sum_univ_succ, StateSpace.vectorField, StateSpace.field,
    toStateSpace, generated.convertLCL, powerlib.reciprocal, portEnergyRate]
  field_simp [ne_of_gt m.first.inductance.property,
    ne_of_gt m.second.inductance.property, ne_of_gt m.capacitance.property]
  ring

@[simp, powerlib_foundation] theorem port_supply (m : Circuit) (x : State) (u : PortInput) :
    powerlib.Passivity.supply (portSystem m) x u = u 0 * x 0 - u 1 * x 2 := by
  simp [powerlib.Passivity.supply, portSystem, Fin.sum_univ_two]
  ring

@[powerlib_domain] theorem portEnergy_derivative {m : Circuit}
    {u : ℝ → PortInput} {x : ℝ → State} (hx : IsPortTrajectory m u x)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => portEnergy m (x s))
      (portEnergyRate m (x t) (u t)) (Ici 0) t := by
  have hsym : (physicalStorageMatrix m).transpose = physicalStorageMatrix m := by
    simp [physicalStorageMatrix]
  have hx' : HasDerivWithinAt x
      (powerlib.LTI.Model.field (terminalStateSpace m) (x t) (u t)) (Ici 0) t := by
    simpa only [terminalStateSpace_field] using hx t ht
  simpa only [terminalStateSpace_energy, terminalStateSpace_energyRate] using
    powerlib.StateSpacePassivity.energy_derivative (physicalStorageMatrix m) hsym hx'

def certifiedPortStorage {m : Circuit} (p : SymmetricMatrix)
    (hweights : p = physicalWeights m) (hp : m.Passive) :
    powerlib.Passivity.QuadraticStorage (portSystem m) := by
  let V := (physicalStateSpaceCertificate m hp).toCertificate.storage
  have he : (fun x => quadraticEnergy p x / 2) = V.energy := by
    rw [hweights]
    exact (terminalStateSpace_energy_function m).symm
  exact {
    energy := fun x => quadraticEnergy p x / 2
    rate := V.rate
    energyDerivative := by
      intro u x hx t ht
      change HasDerivWithinAt (fun s => (fun y => quadraticEnergy p y / 2) (x s)) _ _ _
      rw [he]
      apply V.energyDerivative (t := t) _ ht
      simpa only [terminalStateSpace_system] using hx
    dissipation := by
      intro x u
      simpa only [terminalStateSpace_system] using V.dissipation x u
    continuous := by rw [he]; exact V.continuous
    homogeneous := by
      change ∀ a x, (fun y => quadraticEnergy p y / 2) (a • x) =
        a ^ 2 * (fun y => quadraticEnergy p y / 2) x
      rw [he]
      exact V.homogeneous
    positive := by
      change ∀ x ≠ 0, 0 < (fun y => quadraticEnergy p y / 2) x
      rw [he]
      exact V.positive }

def physicalPortStorage (m : Circuit) (hp : m.Passive) :
    powerlib.Passivity.QuadraticStorage (portSystem m) :=
  certifiedPortStorage (physicalWeights m) rfl hp

structure StorageAccepted (m : Circuit) where
  p : SymmetricMatrix
  weights_exact : p = physicalWeights m
  passive : m.Passive

def synthesizeStorage (m : Circuit) (hp : m.Passive) : StorageAccepted m where
  p := physicalWeights m
  weights_exact := rfl
  passive := hp

def StorageAccepted.portStorage {m : Circuit} (c : StorageAccepted m) :
    powerlib.Passivity.QuadraticStorage (portSystem m) :=
  certifiedPortStorage c.p c.weights_exact c.passive

def StorageAccepted.stateSpaceCertificate {m : Circuit} (c : StorageAccepted m) :
    powerlib.StateSpacePassivity.Certificate (terminalStateSpace m) :=
  (physicalStateSpaceCertificate m c.passive).toCertificate

@[simp, powerlib_foundation] theorem StorageAccepted.stateSpaceCertificate_matrix {m : Circuit}
    (c : StorageAccepted m) : c.stateSpaceCertificate.P = physicalStorageMatrix m := rfl

@[simp, powerlib_foundation] theorem StorageAccepted.portStorage_energy {m : Circuit}
    (c : StorageAccepted m) (x : State) :
    c.portStorage.energy x = portEnergy m x := by
  simp [StorageAccepted.portStorage, certifiedPortStorage, portEnergy, c.weights_exact]

@[powerlib_domain] theorem StorageAccepted.passiveWithStorage {m : Circuit}
    (c : StorageAccepted m) :
    powerlib.Passivity.PassiveWithStorage (portSystem m) (portEnergy m) := by
  simpa only [terminalStateSpace_system, StorageAccepted.stateSpaceCertificate_matrix,
    terminalStateSpace_energy_function] using c.stateSpaceCertificate.passiveWithStorage

@[powerlib_domain] theorem physical_passiveWithStorage {m : Circuit} (hp : m.Passive) :
    powerlib.Passivity.PassiveWithStorage (portSystem m) (portEnergy m) :=
  (synthesizeStorage m hp).passiveWithStorage

@[simp, powerlib_foundation] theorem port_zero_equilibrium (m : Circuit) :
    powerlib.Passivity.IsEquilibrium (portSystem m) 0 :=
  zero_equilibrium m

@[powerlib_foundation] theorem lyapunovStable_of_portSystem {m : Circuit}
    (hs : powerlib.Passivity.LyapunovStable (portSystem m))
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    LyapunovStable m u vg e := by
  apply (terminalStateSpace_stability_iff m u vg e).mp
  apply powerlib.StateSpacePassivity.lyapunovStableAt_of_zeroInput
    ((terminalStateSpace_equilibrium_iff m u vg e).mpr he)
  simpa only [terminalStateSpace_system] using hs

@[powerlib_domain] theorem passive_lyapunovStable_via_ports {m : Circuit}
    (hp : m.Passive) {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    LyapunovStable m u vg e :=
  lyapunovStable_of_portSystem (by
    simpa only [terminalStateSpace_system] using
      (physicalStateSpaceCertificate m hp).toCertificate.lyapunovStable) he

@[powerlib_domain] theorem StorageAccepted.lyapunovStable {m : Circuit}
    (c : StorageAccepted m) {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    LyapunovStable m u vg e :=
  lyapunovStable_of_portSystem (by
    simpa only [terminalStateSpace_system] using c.stateSpaceCertificate.lyapunovStable) he

@[powerlib_domain] theorem StorageAccepted.zeroInput_stable {m : Circuit}
    (c : StorageAccepted m) : LyapunovStable m 0 0 0 :=
  c.lyapunovStable (zero_equilibrium m)

@[powerlib_domain] theorem StorageAccepted.integral_passivity {m : Circuit}
    (c : StorageAccepted m) {u : ℝ → PortInput} {x : ℝ → State}
    (hx : IsPortTrajectory m u x) {t : ℝ} (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun s => u s 0 * x s 0 - u s 1 * x s 2) volume 0 t) :
    portEnergy m (x t) - portEnergy m (x 0) ≤
      ∫ s in (0 : ℝ)..t, u s 0 * x s 0 - u s 1 * x s 2 := by
  have hsupply' : IntervalIntegrable
      (fun s => powerlib.Passivity.supply
        (powerlib.StateSpacePassivity.system (terminalStateSpace m)) (x s) (u s)) volume 0 t := by
    simpa only [terminalStateSpace_system, port_supply] using hsupply
  have hx' : powerlib.Passivity.IsTrajectory
      (powerlib.StateSpacePassivity.system (terminalStateSpace m)) u x := by
    rw [terminalStateSpace_system]
    exact (portTrajectory_iff_generic m u x).mp hx
  simpa only [StorageAccepted.stateSpaceCertificate_matrix, terminalStateSpace_energy,
    terminalStateSpace_system, port_supply] using
    c.stateSpaceCertificate.integral_passivity hx' ht hsupply'

@[powerlib_domain] theorem physical_integral_passivity {m : Circuit}
    (hp : m.Passive) {u : ℝ → PortInput} {x : ℝ → State}
    (hx : IsPortTrajectory m u x) {t : ℝ} (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun s => u s 0 * x s 0 - u s 1 * x s 2) volume 0 t) :
    portEnergy m (x t) - portEnergy m (x 0) ≤
      ∫ s in (0 : ℝ)..t, u s 0 * x s 0 - u s 1 * x s 2 :=
  (synthesizeStorage m hp).integral_passivity hx ht hsupply

@[powerlib_domain] theorem StorageAccepted.zeroInput_energy_nonincreasing {m : Circuit}
    (c : StorageAccepted m) {x : ℝ → State} (hx : IsTrajectory m 0 0 x) :
    AntitoneOn (fun t => portEnergy m (x t)) (Ici 0) := by
  have hx' : powerlib.Passivity.IsTrajectory
      (powerlib.StateSpacePassivity.system (terminalStateSpace m)) (fun _ => 0) x := by
    rw [terminalStateSpace_system]
    exact hx
  simpa only [StorageAccepted.stateSpaceCertificate_matrix, terminalStateSpace_energy] using
    c.stateSpaceCertificate.zeroInput_energy_antitone hx'

@[powerlib_domain] theorem StorageAccepted.trajectory_exists {m : Circuit}
    (_c : StorageAccepted m) {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e)
    (initial : State) : ∃ x, IsTrajectory m u vg x ∧ x 0 = initial := by
  simpa only [terminalStateSpace_trajectory_iff] using
    powerlib.StateSpacePassivity.equilibrium_trajectory_exists
      ((terminalStateSpace_equilibrium_iff m u vg e).mpr he) initial

@[powerlib_domain] theorem StorageAccepted.trajectory_unique {m : Circuit}
    (_c : StorageAccepted m) {u vg : ℝ} {e : State} {x y : ℝ → State}
    (_he : IsEquilibrium m u vg e) (hx : IsTrajectory m u vg x)
    (hy : IsTrajectory m u vg y) (h0 : x 0 = y 0) : EqOn x y (Ici 0) :=
  powerlib.StateSpacePassivity.trajectory_unique (terminalStateSpace m)
    ((terminalStateSpace_trajectory_iff m u vg x).mpr hx)
    ((terminalStateSpace_trajectory_iff m u vg y).mpr hy) h0

end powerlib.LCL
