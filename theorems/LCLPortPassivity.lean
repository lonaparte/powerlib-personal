import theorems.LCLPassivity
import theorems.Passivity

/-!
Physical terminal-port passivity of the Agda-derived ideal LCL plant.
The state order is converter current, capacitor voltage, grid current. Inputs
are the two terminal voltages; outputs are converter current and negative grid
current, so both port powers are counted into the plant. Inputs may vary with
continuous time. This model has no controller, PLL, PWM, delay, or sampling.
The stability conclusion is Lyapunov stability about a constant-input
equilibrium, including the lossless case; it does not assert attraction.
-/
noncomputable section
namespace powerlib.LCL
open Set Filter
open MeasureTheory
open scoped Topology

abbrev PortInput := Fin 2 → ℝ

def portSystem (m : Circuit) : powerlib.Passivity.System State (Fin 2) where
  field x u := (toStateSpace m).vectorField (u 0) (u 1) x
  output x := ![x 0, -x 2]

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

def portEnergy (m : Circuit) (x : State) : ℝ :=
  quadraticEnergy (physicalWeights m) x / 2

def portEnergyRate (m : Circuit) (x : State) (u : PortInput) : ℝ :=
  u 0 * x 0 - u 1 * x 2 - m.first.resistance * (x 0) ^ 2 -
    m.second.resistance * (x 2) ^ 2

@[simp, powerlib_foundation] theorem port_supply (m : Circuit) (x : State) (u : PortInput) :
    powerlib.Passivity.supply (portSystem m) x u = u 0 * x 0 - u 1 * x 2 := by
  simp [powerlib.Passivity.supply, portSystem, Fin.sum_univ_two]
  ring

@[powerlib_domain] theorem portEnergy_derivative {m : Circuit}
    {u : ℝ → PortInput} {x : ℝ → State} (hx : IsPortTrajectory m u x)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => portEnergy m (x s))
      (portEnergyRate m (x t) (u t)) (Ici 0) t := by
  have h := (quadraticEnergy_derivative (physicalWeights m) (hx t ht)).div_const 2
  convert h using 1
  dsimp [portEnergyRate, StateSpace.vectorField]
  rw [same_dynamics]
  dsimp [energyDerivative, physicalWeights]
  field_simp [ne_of_gt m.first.inductance.property, ne_of_gt m.second.inductance.property,
    ne_of_gt m.capacitance.property]
  ring

def certifiedPortStorage {m : Circuit} (p : SymmetricMatrix)
    (hweights : p = physicalWeights m) (hp : m.Passive) :
    powerlib.Passivity.QuadraticStorage (portSystem m) where
  energy x := quadraticEnergy p x / 2
  rate := portEnergyRate m
  energyDerivative := by
    subst p
    intro u x hx t ht
    exact portEnergy_derivative hx ht
  dissipation := by
    intro x u
    rw [port_supply]
    dsimp [portEnergyRate]
    nlinarith [mul_nonneg hp.1 (sq_nonneg (x 0)),
      mul_nonneg hp.2 (sq_nonneg (x 2))]
  continuous := (quadraticEnergy_continuous p).div_const 2
  homogeneous := by
    intro a x
    rw [quadraticEnergy_smul]
    ring
  positive := by
    subst p
    intro x hx
    exact div_pos (physicalEnergy_positive m x hx) (by norm_num)

def physicalPortStorage (m : Circuit) (hp : m.Passive) :
    powerlib.Passivity.QuadraticStorage (portSystem m) :=
  certifiedPortStorage (physicalWeights m) rfl hp

/-- Model-indexed physical-storage certificate. The physical weights are
reconstructed from the submitted circuit, and passivity is checked anew. -/
structure StorageAccepted (m : Circuit) where
  p : SymmetricMatrix
  weights_exact : p = physicalWeights m
  passive : m.Passive

/-- Witness-free construction: only the plant and checked resistance signs
are supplied; the physical storage matrix is computed from the plant. -/
def synthesizeStorage (m : Circuit) (hp : m.Passive) : StorageAccepted m where
  p := physicalWeights m
  weights_exact := rfl
  passive := hp

def StorageAccepted.portStorage {m : Circuit} (c : StorageAccepted m) :
    powerlib.Passivity.QuadraticStorage (portSystem m) :=
  certifiedPortStorage c.p c.weights_exact c.passive

@[simp, powerlib_foundation] theorem StorageAccepted.portStorage_energy {m : Circuit}
    (c : StorageAccepted m) (x : State) :
    c.portStorage.energy x = portEnergy m x := by
  simp [StorageAccepted.portStorage, certifiedPortStorage, portEnergy, c.weights_exact]

@[powerlib_domain, aesop unsafe apply] theorem StorageAccepted.passiveWithStorage {m : Circuit}
    (c : StorageAccepted m) :
    powerlib.Passivity.PassiveWithStorage (portSystem m) (portEnergy m) := by
  have h := c.portStorage.passiveWithStorage
  have he : c.portStorage.energy = portEnergy m :=
    funext (fun x => c.portStorage_energy x)
  rw [he] at h
  exact h

@[powerlib_domain, aesop unsafe apply] theorem physical_passiveWithStorage {m : Circuit} (hp : m.Passive) :
    powerlib.Passivity.PassiveWithStorage (portSystem m) (portEnergy m) :=
  (synthesizeStorage m hp).passiveWithStorage

@[simp, powerlib_foundation] theorem port_zero_equilibrium (m : Circuit) :
    powerlib.Passivity.IsEquilibrium (portSystem m) 0 :=
  zero_equilibrium m

/-- Transport origin stability of the terminal-port system through the
equilibrium-shift conversion checked for the original circuit. -/
@[powerlib_foundation] theorem lyapunovStable_of_portSystem {m : Circuit}
    (hs : powerlib.Passivity.LyapunovStable (portSystem m))
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    LyapunovStable m u vg e := by
  intro ε hε
  obtain ⟨δ, hδ, hstable⟩ := hs ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx h0 t ht
  have hshift : powerlib.Passivity.IsTrajectory (portSystem m) (fun _ => 0)
      (fun s => x s - e) := trajectory_shift he hx
  exact hstable (fun s => x s - e) hshift h0 t ht

/-- Differential physical passivity implies Lyapunov stability after the
checked equilibrium shift. No strictly negative energy rate is required. -/
@[powerlib_domain, aesop unsafe apply] theorem passive_lyapunovStable_via_ports {m : Circuit}
    (hp : m.Passive) {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    LyapunovStable m u vg e :=
  lyapunovStable_of_portSystem
    ((physicalPortStorage m hp).lyapunovStable (port_zero_equilibrium m)) he

@[powerlib_domain, aesop unsafe apply] theorem StorageAccepted.lyapunovStable {m : Circuit}
    (c : StorageAccepted m) {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    LyapunovStable m u vg e :=
  lyapunovStable_of_portSystem
    (c.portStorage.lyapunovStable (port_zero_equilibrium m)) he

@[powerlib_domain, aesop unsafe apply] theorem StorageAccepted.zeroInput_stable {m : Circuit}
    (c : StorageAccepted m) : LyapunovStable m 0 0 0 :=
  c.lyapunovStable (zero_equilibrium m)

/-- Integral physical terminal-port passivity for actual varying-input
trajectories. Only the input-output power needs to be integrable. -/
@[powerlib_domain] theorem StorageAccepted.integral_passivity {m : Circuit}
    (c : StorageAccepted m) {u : ℝ → PortInput} {x : ℝ → State}
    (hx : IsPortTrajectory m u x) {t : ℝ} (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun s => u s 0 * x s 0 - u s 1 * x s 2) volume 0 t) :
    portEnergy m (x t) - portEnergy m (x 0) ≤
      ∫ s in (0 : ℝ)..t, u s 0 * x s 0 - u s 1 * x s 2 := by
  have hsupply' : IntervalIntegrable
      (fun s => powerlib.Passivity.supply (portSystem m) (x s) (u s)) volume 0 t := by
    simpa only [port_supply] using hsupply
  have h := c.portStorage.integral_passivity hx ht hsupply'
  change c.portStorage.energy (x t) - c.portStorage.energy (x 0) ≤ _ at h
  simpa only [StorageAccepted.portStorage_energy, port_supply] using h

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
  have h := c.portStorage.toDissipativeStorage.zeroInput_energy_antitone hx
  change AntitoneOn (fun t => c.portStorage.energy (x t)) (Ici 0) at h
  simpa only [StorageAccepted.portStorage_energy] using h

/-- Forward existence is supplied by the matrix-exponential solution of the
original plant, including lossless plants and nonunique equilibria. -/
@[powerlib_domain] theorem StorageAccepted.trajectory_exists {m : Circuit}
    (_c : StorageAccepted m) {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e)
    (initial : State) : ∃ x, IsTrajectory m u vg x ∧ x 0 = initial :=
  powerlib.LCL.trajectory_exists he initial

@[powerlib_domain] theorem StorageAccepted.trajectory_unique {m : Circuit}
    (_c : StorageAccepted m) {u vg : ℝ} {e : State} {x y : ℝ → State}
    (he : IsEquilibrium m u vg e) (hx : IsTrajectory m u vg x)
    (hy : IsTrajectory m u vg y) (h0 : x 0 = y 0) : EqOn x y (Ici 0) :=
  powerlib.LCL.trajectory_unique he hx hy h0

end powerlib.LCL
