import theorems.RLStability

/-!
# Large-signal stability of the ideal scalar RL circuit

The state is physical branch current `[i]` in a stationary frame. The exact,
continuous-time model is `L*i' = v - R*i`, with fixed `L > 0`, fixed `R`, and
constant voltage `v`. The equilibrium is constructed from the model as `v/R`.
No linearization, small-error assumption, or bound on initial current is used.
There are no hidden controller, PLL, PWM, delay, saturation or switching states.
This result does not describe a fault-on trajectory, a switching event, or
compliance with current/voltage safety limits.

`LargeSignalStable` includes existence and uniqueness for every initial current,
not only decay conditional on a solution. It also includes both global
exponential stability and Lyapunov stability with global attraction.
The certificate constructor and the Agda-generated model conversion are reused;
the model-bound ATP admission must derive this predicate before claiming success.
-/
noncomputable section
namespace powerlib
open Set

def LargeSignalStable (m : Impedance) (voltage : ℝ) : Prop :=
  IsEquilibrium m voltage (voltage / m.resistance) ∧
  (∀ initial : ℝ, ∃ i : ℝ → ℝ, IsTrajectory m voltage i ∧ i 0 = initial) ∧
  (∀ i j : ℝ → ℝ, IsTrajectory m voltage i → IsTrajectory m voltage j →
    i 0 = j 0 → EqOn i j (Ici 0)) ∧
  GloballyExponentiallyStable m voltage (voltage / m.resistance) ∧
  GloballyAsymptoticallyStable m voltage (voltage / m.resistance)

@[powerlib_domain] theorem Accepted.largeSignalStable {m : Impedance}
    (c : Accepted m) (voltage : ℝ) : LargeSignalStable m voltage := by
  have hR : 0 < m.resistance := (impedance_stable_iff m).mp c.stable
  have he := equilibrium_of_resistance_ne_zero (ne_of_gt hR) voltage
  refine ⟨he, ?_, ?_, c.globallyExponentiallyStable he,
    c.globallyAsymptoticallyStable he⟩
  · exact fun initial => trajectory_exists he initial
  · exact fun i j hi hj h0 => trajectory_unique_at_equilibrium he hi hj h0

/-- Witness-free symbolic synthesis: resistance positivity is an input condition,
not a supplied Lyapunov coefficient, equilibrium, or convergence rate. -/
@[powerlib_domain] theorem largeSignalStable_of_resistance_pos {m : Impedance}
    (hR : 0 < m.resistance) (voltage : ℝ) : LargeSignalStable m voltage :=
  (synthesize m hR).largeSignalStable voltage

/-- Exact characterization, including rejection of zero and negative resistance. -/
@[powerlib_domain] theorem largeSignalStable_iff_resistance_pos
    (m : Impedance) (voltage : ℝ) : LargeSignalStable m voltage ↔ 0 < m.resistance := by
  constructor
  · intro h
    exact (impedance_stable_iff m).mp
      ((globallyAsymptoticallyStable_iff_stable h.1).mp h.2.2.2.2)
  · intro hR
    exact largeSignalStable_of_resistance_pos hR voltage

/-- The exact physical-current estimate holds at every amplitude. Its rate is
`R/L`; the existing certificate's squared-error rate is `2*R/L`. -/
@[powerlib_domain] theorem large_signal_error_exact {m : Impedance}
    (hR : 0 < m.resistance) {voltage : ℝ} {i : ℝ → ℝ}
    (hi : IsTrajectory m voltage i) {t : ℝ} (ht : 0 ≤ t) :
    |i t - voltage / m.resistance| =
      |i 0 - voltage / m.resistance| *
        Real.exp (-(m.resistance / m.inductance.val) * t) := by
  have he := equilibrium_of_resistance_ne_zero (ne_of_gt hR) voltage
  simpa [toStateSpace, generated.convert, reciprocal, div_eq_mul_inv] using
    trajectory_error_exact he hi ht

/-- The equilibrium need not be supplied to the certificate consumer. -/
@[powerlib_domain] theorem Accepted.large_signal_error_exact {m : Impedance}
    (c : Accepted m) {voltage : ℝ} {i : ℝ → ℝ}
    (hi : IsTrajectory m voltage i) {t : ℝ} (ht : 0 ≤ t) :
    |i t - voltage / m.resistance| =
      |i 0 - voltage / m.resistance| *
        Real.exp (-(m.resistance / m.inductance.val) * t) :=
  powerlib.large_signal_error_exact ((impedance_stable_iff m).mp c.stable) hi ht

end powerlib
