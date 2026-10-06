import dependencies.Mathlib
import theorem.Dynamics.Stability
import theorem.Dynamics.LyapunovDefs
import theorem.LCLStability
import theorem.Lyapunov

/-! Full zero-input trajectory certificates for the canonical RL and ideal LCL
plants. Coordinates are physical current for RL and `(i₁, vC, i₂)` for LCL.
The fields below are exactly the original continuous-time plant fields.
-/

noncomputable section
open Metric Set

namespace powerlib

def Impedance.autonomousField (m : Impedance) : ℝ → ℝ :=
  fun i => (toStateSpace m).field i 0

@[powerlib_foundation] theorem Impedance.autonomousField_smooth (m : Impedance) :
    ContDiff ℝ 1 m.autonomousField := by
  unfold Impedance.autonomousField StateSpace.field
  fun_prop

@[powerlib_foundation] theorem rl_energy_derivative (p i di : ℝ) :
    fderiv ℝ (energy p) i di = 2 * p * i * di := by
  have h := (((hasDerivAt_id i).pow 2).const_mul p).hasFDerivAt
  change fderiv ℝ (fun y => p * id y ^ 2) i di = _
  erw [h.fderiv]
  simp
  ring

/-- An admitted scalar certificate yields a global nonlinear-trajectory energy
certificate for the exact submitted RL model. -/
def Accepted.quadraticDecayCertificate {m : Impedance} (c : Accepted m) :
    Dynamics.QuadraticDecayCertificate m.autonomousField (energy c.p) 0 where
  lower := c.p
  upper := c.p
  rate := c.rate
  lower_pos := c.p_pos
  upper_pos := c.p_pos
  rate_pos := c.rate_pos
  smooth := by unfold energy; fun_prop
  equilibrium_field := by simp [Impedance.autonomousField, StateSpace.field]
  equilibrium_value := by simp [energy]
  lower_bound := by intro i; simp [energy, sq_abs]
  upper_bound := by intro i; simp [energy, sq_abs]
  dissipation := by
    intro i
    rw [rl_energy_derivative]
    have hid := c.dissipation i
    change 2 * c.p * i * (toStateSpace m).field i 0 ≤ -c.rate * energy c.p i
    rw [hid]
    have hrate : c.rate * c.p = 1 := by
      rw [c.rate_exact]
      nlinarith [c.lyapunov_identity]
    simp only [energy]
    nlinarith [hrate]

@[powerlib_domain, aesop safe apply] theorem Impedance.autonomousField_forwardComplete (m : Impedance) :
    Dynamics.ForwardComplete m.autonomousField := by
  intro a i₀
  refine ⟨fun t => response m i₀ (t - a), ?_, ?_⟩
  · simp
  · intro t ht
    have h := (response_solves m i₀ (t - a)).comp t ((hasDerivAt_id t).sub_const a)
    simpa [Impedance.autonomousField, Function.comp_def] using! h.hasDerivWithinAt

/-- Accepted RL certificates prove decay of every solution from every current,
including existence for the entire forward time ray. -/
@[powerlib_domain, aesop norm forward (immediate := [c])] theorem Accepted.autonomousGloballyExponentiallyStable {m : Impedance}
    (c : Accepted m) : Dynamics.GloballyExponentiallyStable m.autonomousField 0 :=
  c.quadraticDecayCertificate.globallyExponentiallyStable m.autonomousField_smooth

end powerlib

namespace powerlib.LCL

abbrev State3 := Dynamics.State 3

def Circuit.autonomousField (m : Circuit) (x : State3) : State3 :=
  let f := (toStateSpace m).field (x 0) (x 1) (x 2) 0 0
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![f.1, f.2.1, f.2.2]

def stateEnergy (p : SymmetricMatrix) (x : State3) : ℝ :=
  energy p (x 0) (x 1) (x 2)

@[fun_prop, powerlib_foundation] theorem coordinate_smooth (j : Fin 3) :
    ContDiff ℝ 1 (fun x : State3 => x j) :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : State3 →L[ℝ] ℝ).contDiff

@[powerlib_foundation] theorem Circuit.autonomousField_smooth (m : Circuit) :
    ContDiff ℝ 1 m.autonomousField := by
  have hs : ContDiff ℝ 1 (fun x : State3 =>
      ![-(toStateSpace m).first.decay * x 0 - (toStateSpace m).first.inputGain.val * x 1,
        (toStateSpace m).capacitorGain.val * (x 0 - x 2),
        (toStateSpace m).second.inputGain.val * x 1 - (toStateSpace m).second.decay * x 2]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> simp <;> fun_prop
  convert! (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp hs using 1
  funext x
  ext j
  fin_cases j <;> simp [Circuit.autonomousField, StateSpace.field]

@[powerlib_foundation] theorem stateEnergy_smooth (p : SymmetricMatrix) :
    ContDiff ℝ 1 (stateEnergy p) := by
  unfold stateEnergy energy
  fun_prop

@[powerlib_foundation] theorem stateEnergy_zero (p : SymmetricMatrix) :
    stateEnergy p 0 = 0 := by
  simpa [stateEnergy, quadraticEnergy] using quadraticEnergy_zero p

@[powerlib_foundation] theorem stateEnergy_homogeneous (p : SymmetricMatrix)
    (r : ℝ) (x : State3) : stateEnergy p (r • x) = r ^ 2 * stateEnergy p x := by
  simpa [stateEnergy, quadraticEnergy] using
    quadraticEnergy_smul p r ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)) x)

@[powerlib_domain] theorem Accepted.stateEnergy_positive {m : Circuit} (c : Accepted m)
    (x : State3) (hx : x ≠ 0) : 0 < stateEnergy c.p x := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hnonzero : e x ≠ 0 := by
    intro h
    exact hx (e.injective (by simpa using h))
  exact c.positive _ _ _ ((state_ne_zero_iff (e x)).mp hnonzero)

@[powerlib_foundation] theorem stateEnergy_derivative (p : SymmetricMatrix)
    (x dx : State3) :
    fderiv ℝ (stateEnergy p) x dx =
      energyDerivative p (x 0) (x 1) (x 2) (dx 0) (dx 1) (dx 2) := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State3 →L[ℝ] ℝ).hasFDerivAt
    (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State3 →L[ℝ] ℝ).hasFDerivAt
    (x := x)
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) : State3 →L[ℝ] ℝ).hasFDerivAt
    (x := x)
  have h := ((((((h0.mul h0).const_mul p.p11).add
    ((h0.const_mul (2 * p.p12)).mul h1)).add
    ((h0.const_mul (2 * p.p13)).mul h2)).add
    ((h1.mul h1).const_mul p.p22)).add
    ((h1.const_mul (2 * p.p23)).mul h2)).add
    ((h2.mul h2).const_mul p.p33)
  simp only [PiLp.proj_apply] at h
  unfold stateEnergy energy
  simp only [pow_two]
  erw [h.fderiv]
  simp [energyDerivative]
  ring

@[powerlib_foundation] theorem state3_norm_sq (x : State3) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_succ, sq_abs]
  ring

@[powerlib_domain] theorem Accepted.stateEnergy_dissipation {m : Circuit}
    (c : Accepted m) (x : State3) :
    fderiv ℝ (stateEnergy c.p) x (m.autonomousField x) = -‖x‖ ^ 2 := by
  rw [stateEnergy_derivative, state3_norm_sq]
  simpa [Circuit.autonomousField] using c.dissipation (x 0) (x 1) (x 2)

@[powerlib_foundation] theorem Circuit.autonomousField_zero (m : Circuit) :
    m.autonomousField 0 = 0 := by
  ext j
  fin_cases j <;> simp [Circuit.autonomousField, StateSpace.field]

/-- Every accepted LCL matrix supplies its own global norm bounds. -/
@[powerlib_domain] theorem Accepted.stateEnergy_bounds {m : Circuit} (c : Accepted m) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ x : State3, lo * ‖x‖ ^ 2 ≤ stateEnergy c.p x ∧
        stateEnergy c.p x ≤ hi * ‖x‖ ^ 2 := by
  obtain ⟨lo, hlo, hi, hhilo, hb⟩ := powerlib.quadratic_bounds
    (stateEnergy c.p) (stateEnergy_smooth c.p).continuous
    (stateEnergy_homogeneous c.p) c.stateEnergy_positive
  exact ⟨lo, hi, hlo, hlo.trans_le hhilo, hb⟩

/-- The original model-indexed LCL certificate implies a global trajectory
certificate, with bounds and decay rate derived inside Lean. -/
def Accepted.quadraticDecayCertificate {m : Circuit} (c : Accepted m) :
    Dynamics.QuadraticDecayCertificate m.autonomousField (stateEnergy c.p) 0 := by
  let lo := c.stateEnergy_bounds.choose
  let hi := c.stateEnergy_bounds.choose_spec.choose
  have hproperties : 0 < lo ∧ 0 < hi ∧
      ∀ x : State3, lo * ‖x‖ ^ 2 ≤ stateEnergy c.p x ∧
        stateEnergy c.p x ≤ hi * ‖x‖ ^ 2 :=
    c.stateEnergy_bounds.choose_spec.choose_spec
  have hlo := hproperties.1
  have hhi := hproperties.2.1
  have hb := hproperties.2.2
  refine
    { lower := lo
      upper := hi
      rate := hi⁻¹
      lower_pos := hlo
      upper_pos := hhi
      rate_pos := inv_pos.mpr hhi
      smooth := stateEnergy_smooth c.p
      equilibrium_field := m.autonomousField_zero
      equilibrium_value := stateEnergy_zero c.p
      lower_bound := ?_
      upper_bound := ?_
      dissipation := ?_ }
  · intro x
    simpa using (hb x).1
  · intro x
    simpa using (hb x).2
  · intro x
    rw [c.stateEnergy_dissipation]
    have h := mul_le_mul_of_nonneg_left (hb x).2 (le_of_lt (inv_pos.mpr hhi))
    have hh : hi⁻¹ * (hi * ‖x‖ ^ 2) = ‖x‖ ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hhi), one_mul]
    rw [hh] at h
    linarith

/-- The admitted ideal LCL plant is globally exponentially stable for arbitrary
initial `(i₁, vC, i₂)`, with both terminal input perturbations held at zero. -/
@[powerlib_domain, aesop norm forward (immediate := [c])] theorem Accepted.autonomousGloballyExponentiallyStable {m : Circuit}
    (c : Accepted m) : Dynamics.GloballyExponentiallyStable m.autonomousField 0 :=
  c.quadraticDecayCertificate.globallyExponentiallyStable m.autonomousField_smooth

/-- Global asymptotic stability of the same original three-state LCL field. -/
@[powerlib_domain, aesop norm forward (immediate := [c])] theorem Accepted.autonomousGloballyAsymptoticallyStable {m : Circuit}
    (c : Accepted m) : Dynamics.GloballyAsymptoticallyStable m.autonomousField 0 :=
  c.quadraticDecayCertificate.globallyAsymptoticallyStable (by norm_num)
    m.autonomousField_smooth

end powerlib.LCL
