import powerlib

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

#check powerlib.LTI.Accepted.exponentially_stable
#check powerlib.LTI.trajectory_exists
#print axioms powerlib.LTI.Accepted.exponentially_stable

-- Small-signal stability: the Hurwitz spectrum is exactly exponential decay of the linear
-- model, and a Hurwitz Jacobian makes a nonlinear equilibrium locally exponentially stable.
#check powerlib.LTI.exponentiallyStable_iff_spectrallyStable
#check powerlib.LTI.accepted_nonempty_iff_isHurwitz
#check powerlib.Dynamics.locallyExponentiallyStable_of_spectrallyStable_jacobian
#check powerlib.Dynamics.unstable_of_characteristic_root_re_pos
#print axioms powerlib.LTI.exponentiallyStable_iff_isHurwitz

-- Impedance-based stability of a source–load interconnection: the closed loop is computed by
-- the Agda-normalized conversion, and with both subsystems stable on their own the
-- interconnected small-signal model is exponentially stable exactly when det(I + Z_s Y_L)
-- has no zero in the closed right half-plane.
#check powerlib.ImpedanceCriterion.Interconnection.exponentiallyStable_iff_impedanceStable
#check powerlib.ImpedanceCriterion.Interconnection.det_characteristicMatrix_closedLoop
#check powerlib.ImpedanceCriterion.impedanceStable_without_premises_insufficient
#print axioms powerlib.ImpedanceCriterion.Interconnection.exponentiallyStable_iff_impedanceStable
