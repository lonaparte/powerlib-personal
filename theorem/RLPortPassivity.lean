import dependencies.Mathlib
import theorem.RLStability
import theorem.StateSpaceTrajectories

noncomputable section
namespace powerlib.RLPort
open Set Matrix
open MeasureTheory

abbrev State := Fin 1 → ℝ
abbrev Input := Fin 1 → ℝ

def toState (current : ℝ) : State := fun _ => current

def stateSpace (m : Impedance) : LTI.Model (Fin 1) (Fin 1) where
  A := fun _ _ => -(toStateSpace m).decay
  B := fun _ _ => (toStateSpace m).inputGain.val
  C := fun _ _ => 1
  D := 0

def portSystem (m : Impedance) : Passivity.System State (Fin 1) :=
  StateSpacePassivity.system (stateSpace m)

@[simp, powerlib_foundation] theorem stateSpace_field (m : Impedance)
    (x : State) (u : Input) :
    LTI.Model.field (stateSpace m) x u = toState ((toStateSpace m).field (x 0) (u 0)) := by
  ext j
  fin_cases j
  simp [LTI.Model.field, stateSpace, Matrix.mulVec, dotProduct,
    toState, StateSpace.field]

@[simp, powerlib_foundation] theorem stateSpace_output (m : Impedance)
    (x : State) (u : Input) : LTI.Model.output (stateSpace m) x u = x := by
  ext j
  fin_cases j
  simp [LTI.Model.output, stateSpace, Matrix.mulVec, dotProduct]

@[simp, powerlib_foundation] theorem port_supply (m : Impedance)
    (x : State) (u : Input) : Passivity.supply (portSystem m) x u = u 0 * x 0 := by
  simp [Passivity.supply, portSystem, StateSpacePassivity.system]

def storageMatrix (m : Impedance) : Matrix (Fin 1) (Fin 1) ℝ :=
  diagonal (fun _ => m.inductance.val)

def portEnergy (m : Impedance) (x : State) : ℝ :=
  m.inductance.val * (x 0) ^ 2 / 2

@[simp, powerlib_foundation] theorem storage_energy (m : Impedance) (x : State) :
    StateSpacePassivity.energy (storageMatrix m) x = portEnergy m x := by
  simp [StateSpacePassivity.energy, LTI.energy, storageMatrix, portEnergy, dotProduct]
  ring

def synthesizePassivityCertificate (m : Impedance) (hR : 0 ≤ m.resistance) :
    StateSpacePassivity.Certificate (stateSpace m) where
  P := storageMatrix m
  positive := Matrix.PosDef.diagonal (fun _ => m.inductance.property)
  kyp := by
    intro x u
    have hbalance : dotProduct ((storageMatrix m).mulVec x)
        (LTI.Model.field (stateSpace m) x u) = u 0 * x 0 - m.resistance * (x 0) ^ 2 := by
      rw [stateSpace_field]
      simp only [storageMatrix, Matrix.mulVec_diagonal, dotProduct,
        Fin.sum_univ_one, toState]
      rw [same_dynamics]
      field_simp [ne_of_gt m.inductance.property]
    rw [hbalance]
    change _ ≤ Passivity.supply (portSystem m) x u
    rw [port_supply]
    nlinarith [mul_nonneg hR (sq_nonneg (x 0))]

@[powerlib_domain] theorem passiveWithStorage
    {m : Impedance} (hR : 0 ≤ m.resistance) :
    Passivity.PassiveWithStorage (portSystem m) (portEnergy m) := by
  have h := (synthesizePassivityCertificate m hR).passiveWithStorage
  change Passivity.PassiveWithStorage (portSystem m)
    (StateSpacePassivity.energy (storageMatrix m)) at h
  have he : StateSpacePassivity.energy (storageMatrix m) = portEnergy m :=
    funext (storage_energy m)
  rw [he] at h
  exact h

@[powerlib_domain] theorem zeroInput_stable
    {m : Impedance} (hR : 0 ≤ m.resistance) :
    Passivity.LyapunovStable (portSystem m) := by
  exact (synthesizePassivityCertificate m hR).lyapunovStable

def IsPortTrajectory (m : Impedance) (voltage : ℝ → ℝ) (current : ℝ → ℝ) : Prop :=
  ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt current
    ((toStateSpace m).field (current t) (voltage t)) (Ici 0) t

@[powerlib_foundation] theorem portTrajectory_iff_generic (m : Impedance)
    (voltage current : ℝ → ℝ) :
    IsPortTrajectory m voltage current ↔ Passivity.IsTrajectory (portSystem m)
      (fun t => toState (voltage t)) (fun t => toState (current t)) := by
  constructor
  · intro h t ht
    change HasDerivWithinAt _ (LTI.Model.field (stateSpace m)
      (toState (current t)) (toState (voltage t))) _ _
    rw [stateSpace_field]
    apply hasDerivWithinAt_pi.mpr
    intro j
    exact h t ht
  · intro h t ht
    have hd := h t ht
    change HasDerivWithinAt _ (LTI.Model.field (stateSpace m)
      (toState (current t)) (toState (voltage t))) _ _ at hd
    rw [stateSpace_field] at hd
    exact (hasDerivWithinAt_pi.mp hd) 0

@[powerlib_foundation] theorem portTrajectory_iff_circuit (m : Impedance)
    (voltage current : ℝ → ℝ) :
    IsPortTrajectory m voltage current ↔ ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt current
      ((voltage t - m.resistance * current t) / m.inductance.val) (Ici 0) t := by
  simp only [IsPortTrajectory, same_dynamics]

@[powerlib_foundation] theorem portTrajectory_constant_iff (m : Impedance)
    (v : ℝ) (current : ℝ → ℝ) :
    IsPortTrajectory m (fun _ => v) current ↔ powerlib.IsTrajectory m v current :=
  Iff.rfl

@[powerlib_foundation] theorem scalarTrajectory_of_generic {m : Impedance}
    {u : ℝ → Input} {x : ℝ → State}
    (hx : Passivity.IsTrajectory (portSystem m) u x) :
    IsPortTrajectory m (fun t => u t 0) (fun t => x t 0) := by
  intro t ht
  have hd := hx t ht
  change HasDerivWithinAt _ (LTI.Model.field (stateSpace m)
    (x t) (u t)) _ _ at hd
  rw [stateSpace_field] at hd
  exact (hasDerivWithinAt_pi.mp hd) 0

@[powerlib_domain] theorem zeroInput_trajectory_exists (m : Impedance) (initial : ℝ) :
    ∃ current, powerlib.IsTrajectory m 0 current ∧ current 0 = initial := by
  obtain ⟨x, hx, h0⟩ := StateSpacePassivity.trajectory_exists (stateSpace m) (toState initial)
  refine ⟨fun t => x t 0, scalarTrajectory_of_generic hx, ?_⟩
  exact congrArg (fun z : State => z 0) h0

@[powerlib_domain] theorem port_trajectory_unique {m : Impedance}
    {voltage current₁ current₂ : ℝ → ℝ}
    (h₁ : IsPortTrajectory m voltage current₁)
    (h₂ : IsPortTrajectory m voltage current₂) (h0 : current₁ 0 = current₂ 0) :
    EqOn current₁ current₂ (Ici 0) := by
  have heq := StateSpacePassivity.trajectory_unique (stateSpace m)
    ((portTrajectory_iff_generic m voltage current₁).mp h₁)
    ((portTrajectory_iff_generic m voltage current₂).mp h₂)
    (congrArg toState h0)
  intro t ht
  exact congrArg (fun z : State => z 0) (heq ht)

@[powerlib_domain] theorem integral_passivity {m : Impedance}
    (hR : 0 ≤ m.resistance) {voltage current : ℝ → ℝ}
    (hx : IsPortTrajectory m voltage current) {t : ℝ} (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun s => voltage s * current s) volume 0 t) :
    m.inductance.val * (current t) ^ 2 / 2 -
        m.inductance.val * (current 0) ^ 2 / 2 ≤
      ∫ s in (0 : ℝ)..t, voltage s * current s := by
  have hpower : IntervalIntegrable (fun s => Passivity.supply (portSystem m)
      (toState (current s)) (toState (voltage s))) volume 0 t := by
    simpa only [port_supply, toState] using hsupply
  have h := (passiveWithStorage hR).2
    ((portTrajectory_iff_generic m voltage current).mp hx) ht hpower
  simpa only [port_supply, toState, portEnergy] using h

@[powerlib_foundation] theorem equilibrium_to_generic
    {m : Impedance} {v e : ℝ} (he : powerlib.IsEquilibrium m v e) :
    (stateSpace m).IsEquilibrium (toState v) (toState e) := by
  change LTI.Model.field (stateSpace m) (toState e) (toState v) = 0
  rw [stateSpace_field]
  change toState ((toStateSpace m).field e v) = 0
  rw [powerlib.equilibrium_field he]
  rfl

@[powerlib_foundation] theorem lyapunovStable_of_genericAt
    {m : Impedance} {v e : ℝ}
    (hs : StateSpacePassivity.LyapunovStableAt (stateSpace m) (toState v) (toState e)) :
    powerlib.LyapunovStable m v e := by
  intro ε hε
  obtain ⟨δ, hδ, hstable⟩ := hs ε hε
  refine ⟨δ, hδ, ?_⟩
  intro current hx h0 t ht
  have hgeneric := (portTrajectory_iff_generic m (fun _ => v) current).mp hx
  have hnorm : ‖toState (current 0) - toState e‖ < δ := by
    simpa [toState, Pi.sub_def, Real.norm_eq_abs] using h0
  simpa [toState, Pi.sub_def, Real.norm_eq_abs] using hstable _ hgeneric hnorm t ht

@[powerlib_domain] theorem lyapunovStable
    {m : Impedance} (hR : 0 ≤ m.resistance) {v e : ℝ}
    (he : powerlib.IsEquilibrium m v e) : powerlib.LyapunovStable m v e := by
  apply lyapunovStable_of_genericAt
  exact StateSpacePassivity.lyapunovStableAt_of_zeroInput
    (equilibrium_to_generic he) (zeroInput_stable hR)

@[powerlib_domain] theorem trajectory_exists {m : Impedance} {v e : ℝ}
    (he : powerlib.IsEquilibrium m v e) (initial : ℝ) :
    ∃ current, powerlib.IsTrajectory m v current ∧ current 0 = initial := by
  obtain ⟨x, hx, h0⟩ := StateSpacePassivity.equilibrium_trajectory_exists
    (equilibrium_to_generic he) (toState initial)
  refine ⟨fun t => x t 0, scalarTrajectory_of_generic hx, ?_⟩
  exact congrArg (fun z : State => z 0) h0

@[powerlib_domain] theorem trajectory_unique {m : Impedance} {v : ℝ}
    {current₁ current₂ : ℝ → ℝ}
    (h₁ : powerlib.IsTrajectory m v current₁)
    (h₂ : powerlib.IsTrajectory m v current₂) (h0 : current₁ 0 = current₂ 0) :
    EqOn current₁ current₂ (Ici 0) :=
  port_trajectory_unique h₁ h₂ h0

end powerlib.RLPort
