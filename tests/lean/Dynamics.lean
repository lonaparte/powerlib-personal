import powerlib

/-! Regression checks on the public API: global existence, estimates for every
finite solution segment, attraction of every complete trajectory, and rejection
of a locally stable field whose energy increases far from the equilibrium. -/

noncomputable section
namespace powerlib.Tests.Dynamics

open powerlib.Dynamics Set Filter Topology

-- There is a full forward trajectory through every initial state, including n = 0.
theorem nonlinear_every_initial_state_has_global_solution (n : ℕ) (a : ℝ) (x₀ : State n) :
    ∃ φ : ℝ → State n, φ a = x₀ ∧
      IsIntegralCurveOn φ (fun _ x => Nonlinear.field x) (Ici a) :=
  (Nonlinear.globallyExponentiallyStable n).2.1 a x₀

-- This estimate applies to an arbitrary solution, time anchor, and amplitude.
theorem nonlinear_every_finite_segment_decays {n : ℕ} {φ : ℝ → State n}
    {a b t : ℝ} (hφ : IsTrajectoryOn φ (@Nonlinear.field n) a b) (ht : t ∈ Icc a b) :
    ‖φ t‖ ≤ Real.exp (-(t - a)) * ‖φ a‖ :=
  Nonlinear.norm_bound hφ ht

-- The public GAS theorem supplies universal attraction, not a selected response.
theorem nonlinear_every_global_trajectory_converges {n : ℕ} (hn : 0 < n)
    (a : ℝ) (φ : ℝ → State n)
    (hφ : IsIntegralCurveOn φ (fun _ x => Nonlinear.field x) (Ici a)) :
    Tendsto φ atTop (𝓝 (0 : State n)) :=
  (Nonlinear.globallyAsymptoticallyStable hn).2.2.2 a φ hφ

-- Accepted LCL witnesses remain indexed by the exact original zero-input plant.
theorem lcl_every_initial_state_has_global_solution {m : powerlib.LCL.Circuit}
    (c : powerlib.LCL.Accepted m) (a : ℝ) (x₀ : powerlib.LCL.State3) :
    ∃ φ : ℝ → powerlib.LCL.State3, φ a = x₀ ∧
      IsIntegralCurveOn φ (fun _ x => m.autonomousField x) (Ici a) :=
  c.autonomousGloballyExponentiallyStable.2.1 a x₀

theorem lcl_uniform_decay_of_every_finite_segment {m : powerlib.LCL.Circuit}
    (c : powerlib.LCL.Accepted m) :
    ∃ C rate : ℝ, 1 ≤ C ∧ 0 < rate ∧
      ∀ (a b : ℝ) (φ : ℝ → powerlib.LCL.State3),
        IsTrajectoryOn φ m.autonomousField a b →
        ∀ t ∈ Icc a b,
          ‖φ t‖ ≤ C * Real.exp (-(rate * (t - a))) * ‖φ a‖ := by
  simpa only [sub_zero] using c.autonomousGloballyExponentiallyStable.2.2

theorem lcl_every_global_trajectory_converges {m : powerlib.LCL.Circuit}
    (c : powerlib.LCL.Accepted m) (a : ℝ) (φ : ℝ → powerlib.LCL.State3)
    (hφ : IsIntegralCurveOn φ (fun _ x => m.autonomousField x) (Ici a)) :
    Tendsto φ atTop (𝓝 (0 : powerlib.LCL.State3)) :=
  c.autonomousGloballyAsymptoticallyStable.2.2.2 a φ hφ

-- A negative Jacobian at zero must not be mistaken for global stability.
def locallyStableField (x : ℝ) : ℝ := -x + x ^ 3

def squareEnergy (x : ℝ) : ℝ := x ^ 2

theorem locallyStableField_has_negative_linearization :
    HasDerivAt locallyStableField (-1) 0 := by
  simpa [locallyStableField] using
    (hasDerivAt_id (0 : ℝ)).neg.add ((hasDerivAt_id (0 : ℝ)).pow 3)

theorem squareEnergy_lie_derivative (x : ℝ) :
    fderiv ℝ squareEnergy x (locallyStableField x) =
      2 * x * locallyStableField x := by
  have hd := ((hasDerivAt_id x).pow 2).hasFDerivAt
  change fderiv ℝ (fun y : ℝ => id y ^ 2) x (locallyStableField x) = _
  rw [hd.fderiv]
  simp [ContinuousLinearMap.smulRight_apply]
  ring

-- At x = 2 the Lie derivative is 24; no positive global decay rate can fit.
theorem locallyStableField_rejects_global_decay_certificate :
    ¬ Nonempty (QuadraticDecayCertificate locallyStableField squareEnergy 0) := by
  rintro ⟨c⟩
  have hdecay := c.dissipation 2
  rw [squareEnergy_lie_derivative] at hdecay
  norm_num [locallyStableField, squareEnergy] at hdecay
  nlinarith [c.rate_pos]

-- The complete field has a nonzero constant trajectory. Thus global exponential
-- stability itself is false, independently of the choice of energy certificate.
theorem locallyStableField_not_globallyExponentiallyStable :
    ¬ powerlib.Dynamics.GloballyExponentiallyStable locallyStableField (0 : ℝ) := by
  intro hstable
  obtain ⟨C, rate, hC, hrate, hdecay⟩ := hstable.2.2
  have hCpos : 0 < C + 1 := by linarith
  let t := Real.log (C + 1) / rate
  have ht : 0 ≤ t := by
    apply le_of_lt
    exact div_pos (Real.log_pos (by linarith : 1 < C + 1)) hrate
  have hφ : IsTrajectoryOn (fun _ : ℝ => (1 : ℝ)) locallyStableField 0 t := by
    intro s hs
    simpa [locallyStableField] using (hasDerivAt_const s (1 : ℝ)).hasDerivWithinAt
  have hbound := hdecay 0 t (fun _ => 1) hφ t ⟨ht, le_refl t⟩
  simp only [sub_zero, norm_one, mul_one] at hbound
  have hrt : rate * t = Real.log (C + 1) := by
    dsimp [t]
    field_simp
  rw [hrt, Real.exp_neg, Real.exp_log hCpos] at hbound
  have hlt : C * (C + 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hCpos]
    linarith
  exact (not_lt_of_ge hbound) hlt

end powerlib.Tests.Dynamics

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots := #[
    `powerlib.Tests.Dynamics.nonlinear_every_initial_state_has_global_solution,
    `powerlib.Tests.Dynamics.nonlinear_every_finite_segment_decays,
    `powerlib.Tests.Dynamics.nonlinear_every_global_trajectory_converges,
    `powerlib.Tests.Dynamics.lcl_every_initial_state_has_global_solution,
    `powerlib.Tests.Dynamics.lcl_uniform_decay_of_every_finite_segment,
    `powerlib.Tests.Dynamics.lcl_every_global_trajectory_converges,
    `powerlib.Tests.Dynamics.locallyStableField_has_negative_linearization,
    `powerlib.Tests.Dynamics.squareEnergy_lie_derivative,
    `powerlib.Tests.Dynamics.locallyStableField_rejects_global_decay_certificate,
    `powerlib.Tests.Dynamics.locallyStableField_not_globallyExponentiallyStable]
  let mut auditedAxioms : Array Name := #[]
  for root in roots do
    match env.find? root with
    | some (.thmInfo _) => pure ()
    | some _ => throwError "Dynamics regression audit root {root} is not a theorem"
    | none => throwError "Dynamics regression audit root {root} was not found"
    auditedAxioms := auditedAxioms ++ powerlib.Search.declarationAxioms env root
  for ax in auditedAxioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected Dynamics regression axiom {ax}"
  logInfo "POWERLIB_DYNAMICS_OK"
