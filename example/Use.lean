import powerlib

/-! Public consumers of the library. -/

open powerlib LinearSystems

-- One semantics: every attractive sentence about a linear plant is the Hurwitz property.
#check powerlib.Linear.holds_iff_isHurwitz
#check powerlib.Linear.den
#print axioms powerlib.Linear.holds_iff_isHurwitz

-- RL: every sentence has an exact translation into parameter requirements.
example (P : Flow.Property) :
    TMIO.realize Circuits.RL.Meets (Circuits.RL.translate P) =
      Linear.den Circuits.RL.Impedance.plant P :=
  Circuits.RL.realize_translate P

-- LCL: pole stability is exact for every circuit, passive or not.
example (m : Circuits.LCL.Circuit) : IsHurwitz m.plant.A ↔ m.Stable :=
  Circuits.LCL.isHurwitz_iff_stable m

-- Synthesis: the certificate is computed from the submitted parameters.
example (m : Circuits.RL.Impedance) (hR : 0 < m.resistance) {P : Flow.Property}
    (hP : P.Attractive) : m ∈ Linear.den Circuits.RL.Impedance.plant P :=
  (Circuits.RL.synthesize m hR).mem_den hP

example (m : Circuits.LCL.Circuit) (hp : m.Passive) (hd : m.Damped) {P : Flow.Property}
    (hP : P.Attractive) : m ∈ Linear.den Circuits.LCL.Circuit.plant P :=
  (Circuits.LCL.synthesize m hp hd).mem_den hP

-- Passivity from stored energy, for every port-Hamiltonian plant.
example {n p : ℕ} (H : Port.PortHamiltonian n p) : H.plant.system.Passive :=
  ⟨_, H.passiveWith⟩

-- Interconnection: the impedance criterion is exact relative to component stability, port data
-- alone cannot certify the closed loop, and on minimal plants the transfer function decides
-- stability.
#check powerlib.Circuits.Interconnection.exactUnder_impedanceStable
#check powerlib.Circuits.Interconnection.portData_not_certified
#check powerlib.Circuits.Interconnection.closedLoop_not_separable
#check powerlib.Linear.similar_iff_transfer_eq
#check powerlib.Linear.isHurwitz_iff_of_transfer_eq
#check powerlib.Linear.exists_minimal_realization
#print axioms powerlib.Linear.similar_iff_transfer_eq

-- Nonlinear: a quadratic-decay certificate proves global exponential stability, including a
-- solution through every state.
example (n : ℕ) : Flow.GloballyExponentiallyStable (Nonlinear.Cubic.field (n := n)) 0 :=
  Nonlinear.Cubic.globallyExponentiallyStable n
