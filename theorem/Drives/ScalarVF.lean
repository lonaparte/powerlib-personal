import dependencies.Mathlib
import theorem.Attributes

/-! # Scalar V/f control of the induction machine: steady-state torque algebra

Static foundation for scalar V/f control: the frequency-ramp limit, the pull-out torque, and its
dependence on frequency in the constant-V/f and field-weakening regions.

Model boundary.
* Induction machine in sinusoidal steady state, Steinmetz single-phase equivalent circuit with
  stator resistance `r_s ≥ 0`, rotor resistance referred to the stator `r_r > 0`, total leakage
  reactance `X = X_ls + X_lr'` at the supply frequency, magnetising branch neglected for the
  torque expression (as in the note's §1.6 formula), three phases, phase voltage `V`,
  synchronous electrical speed `ω_s = 2πf`, slip `s > 0`:
  `T_e(s) = (3V²/ω_s) (r_r/s) / ((r_s + r_r/s)² + X²)`.
* `np` pole pairs (`P/2` in the note), rigid shaft with inertia `J`.
* These are algebraic steady-state statements; the open-loop V/f drive dynamics (e.g.
  sub-harmonic oscillation) are not modelled.

Source: work-sync `theory/T-scalar-vf-control.md` §1.5–§1.7.

Results.
* `rampRate_eq`, `rampRate_le`: if the rotor follows the synchronous speed,
  `Ω = 2πf/np` and `J Ω̇ = T`, then `ḟ = np T /(2πJ)`; the admissible ramp is
  `ḟ ≤ np T_avail/(2πJ)`.
* `torque_le_max`, `torque_at_pullout`: `T_e(s) ≤ T_max = 3V²/(2ω_s (r_s + √(r_s² + X²)))` for
  every `s > 0`, with equality at the pull-out slip `s_p = r_r/√(r_s² + X²)`.
* Constant-V/f region (`V = k f`, `X = x f`): `T_max` is independent of `f` when `r_s = 0`
  (`maxTorque_vf_rs_zero`) and strictly increasing in `f` when `r_s > 0`
  (`maxTorque_vf_strictMono`) — the low-frequency loss of pull-out torque that boost
  compensates.
* Field weakening (`V = V_n`, `r_s = 0`): `T_max(f) = T_max(f_n)(f_n/f)²`
  (`maxTorque_fieldWeakening`) and `T_max(f)·Ω(f)` is strictly decreasing
  (`fieldWeakening_power_strictAnti`).

Corrections.
* §1.5: the ramp limit `ḟ_max = T_avail/(2πJ_eq) · (P/2)/f_n` has an extra `1/f_n`; the
  dimensionally consistent limit is `ḟ ≤ (P/2) T_avail/(2πJ_eq)` (`rampRate_le`,
  `noteRamp_ne`).
* §1.7: "constant-power region `T_max·Ω_r ≈ const`" contradicts the stated `T_max ∝ 1/f²`;
  under the note's own model `T_max·Ω ∝ 1/f` strictly decreases
  (`fieldWeakening_power_strictAnti`). Constant power is only reachable below `T_max`
  (operating torque `∝ 1/f`), not along the pull-out curve.
-/

noncomputable section
namespace powerlib.Drives.ScalarVF

/-! ## Frequency ramp -/

/-- With `Ω = 2πf/np` and `J Ω̇ = T`, the frequency slope is `ḟ = np T/(2πJ)`. -/
@[powerlib_foundation] theorem rampRate_eq (np J T df : ℝ) (hnp : np ≠ 0) (hJ : J ≠ 0)
    (h : J * (2 * Real.pi / np * df) = T) : df = np * T / (2 * Real.pi * J) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [← h]
  field_simp

/-- Ramp limit: the available accelerating torque bounds `ḟ` by `np T_avail/(2πJ)`. -/
@[powerlib_foundation] theorem rampRate_le (np J T Tavail df : ℝ) (hnp : 0 < np) (hJ : 0 < J)
    (h : J * (2 * Real.pi / np * df) = T) (hT : T ≤ Tavail) :
    df ≤ np * Tavail / (2 * Real.pi * J) := by
  rw [rampRate_eq np J T df hnp.ne' hJ.ne' h]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left hT hnp.le

/-- The note's formula differs from the correct one by the factor `1/f_n`. -/
@[powerlib_foundation] theorem noteRamp_ne (np J Tavail fn : ℝ) (hnp : np ≠ 0) (hJ : J ≠ 0)
    (hT : Tavail ≠ 0) (hfn : fn ≠ 1) (hfn0 : fn ≠ 0) :
    Tavail / (2 * Real.pi * J) * (np / fn) ≠ np * Tavail / (2 * Real.pi * J) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  intro h
  field_simp at h
  exact hfn h.symm

/-! ## Torque–slip curve and pull-out torque -/

/-- Steady-state electromagnetic torque at slip `s`. -/
def torque (V ω rs rr X s : ℝ) : ℝ :=
  3 * V ^ 2 / ω * (rr / s) / ((rs + rr / s) ^ 2 + X ^ 2)

/-- Pull-out (maximum) torque. -/
def maxTorque (V ω rs X : ℝ) : ℝ :=
  3 * V ^ 2 / (2 * ω * (rs + Real.sqrt (rs ^ 2 + X ^ 2)))

/-- Pull-out slip `s_p = r_r / √(r_s² + X²)`. -/
def pulloutSlip (rs rr X : ℝ) : ℝ := rr / Real.sqrt (rs ^ 2 + X ^ 2)

@[powerlib_foundation] theorem torque_le_max (V ω rs rr X s : ℝ) (hω : 0 < ω) (hrs : 0 ≤ rs)
    (hrr : 0 < rr) (hX : X ≠ 0) (hs : 0 < s) :
    torque V ω rs rr X s ≤ maxTorque V ω rs X := by
  unfold torque maxTorque
  set Z := Real.sqrt (rs ^ 2 + X ^ 2)
  have hZ2 : Z ^ 2 = rs ^ 2 + X ^ 2 := Real.sq_sqrt (by positivity)
  have hZ : 0 < Z := Real.sqrt_pos.mpr (by positivity)
  set a := rr / s
  have ha : 0 < a := div_pos hrr hs
  have hden : 0 < (rs + a) ^ 2 + X ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hV : 0 ≤ 3 * V ^ 2 := by positivity
  have key : a * (2 * ω * (rs + Z)) ≤ ω * ((rs + a) ^ 2 + X ^ 2) := by
    nlinarith [sq_nonneg (a - Z)]
  nlinarith

@[powerlib_foundation] theorem torque_at_pullout (V ω rs rr X : ℝ) (hω : 0 < ω) (hrs : 0 ≤ rs)
    (hrr : 0 < rr) (hX : X ≠ 0) :
    torque V ω rs rr X (pulloutSlip rs rr X) = maxTorque V ω rs X := by
  unfold torque maxTorque pulloutSlip
  set Z := Real.sqrt (rs ^ 2 + X ^ 2)
  have hZ2 : Z ^ 2 = rs ^ 2 + X ^ 2 := Real.sq_sqrt (by positivity)
  have hZ : 0 < Z := Real.sqrt_pos.mpr (by positivity)
  have ha : rr / (rr / Z) = Z := by field_simp
  rw [ha]
  have hden : (rs + Z) ^ 2 + X ^ 2 = 2 * Z * (rs + Z) := by nlinarith
  rw [hden]
  field_simp

/-! ## Constant V/f region and field weakening -/

/-- Pull-out torque on the V/f line `V = k f`, `ω_s = 2πf`, `X = x f`. -/
def maxTorqueVF (k x rs f : ℝ) : ℝ := maxTorque (k * f) (2 * Real.pi * f) rs (x * f)

/-- With `r_s = 0` the pull-out torque on the V/f line is `3k²/(4πx)` for every `f > 0`. -/
@[powerlib_foundation] theorem maxTorque_vf_rs_zero (k x f : ℝ) (hx : 0 < x) (hf : 0 < f) :
    maxTorqueVF k x 0 f = 3 * k ^ 2 / (4 * Real.pi * x) := by
  unfold maxTorqueVF maxTorque
  have hs : Real.sqrt ((0 : ℝ) ^ 2 + (x * f) ^ 2) = x * f := by
    rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq (by positivity)]
  rw [hs]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- With `r_s > 0` the pull-out torque on the V/f line strictly increases with frequency. -/
@[powerlib_foundation] theorem maxTorque_vf_strictMono (k x rs : ℝ) (hk : k ≠ 0) (hx : 0 < x)
    (hrs : 0 < rs) : StrictMonoOn (maxTorqueVF k x rs) (Set.Ioi 0) := by
  intro f1 hf1 f2 hf2 h12
  simp only [Set.mem_Ioi] at hf1 hf2
  unfold maxTorqueVF maxTorque
  set S1 := Real.sqrt (rs ^ 2 + (x * f1) ^ 2)
  set S2 := Real.sqrt (rs ^ 2 + (x * f2) ^ 2)
  have hS1 : 0 ≤ S1 := Real.sqrt_nonneg _
  have hS2 : 0 ≤ S2 := Real.sqrt_nonneg _
  have hpi := Real.pi_pos
  -- f1 S2 < f2 S1
  have hkey : f1 * S2 < f2 * S1 := by
    have e1 : f1 * S2 = Real.sqrt ((f1 * rs) ^ 2 + (x * f1 * f2) ^ 2) := by
      rw [show (f1 * rs) ^ 2 + (x * f1 * f2) ^ 2 = f1 ^ 2 * (rs ^ 2 + (x * f2) ^ 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hf1.le]
    have e2 : f2 * S1 = Real.sqrt ((f2 * rs) ^ 2 + (x * f1 * f2) ^ 2) := by
      rw [show (f2 * rs) ^ 2 + (x * f1 * f2) ^ 2 = f2 ^ 2 * (rs ^ 2 + (x * f1) ^ 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hf2.le]
    rw [e1, e2]
    apply Real.sqrt_lt_sqrt (by positivity)
    have : f1 * rs < f2 * rs := mul_lt_mul_of_pos_right h12 hrs
    nlinarith [mul_pos hf1 hrs]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hk2 : 0 < 3 * k ^ 2 := by positivity
  have : f1 * (rs + S2) < f2 * (rs + S1) := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left this (show 0 < 3 * k ^ 2 * (2 * Real.pi) * (f1 * f2) by positivity)]

/-- Field weakening (`V = V_n`, `r_s = 0`): `T_max(f) = T_max(f_n) (f_n/f)²`. -/
@[powerlib_foundation] theorem maxTorque_fieldWeakening (Vn x fn f : ℝ) (hx : 0 < x) (hfn : 0 < fn)
    (hf : 0 < f) :
    maxTorque Vn (2 * Real.pi * f) 0 (x * f) =
      maxTorque Vn (2 * Real.pi * fn) 0 (x * fn) * (fn / f) ^ 2 := by
  unfold maxTorque
  have hs : ∀ y : ℝ, 0 < y → Real.sqrt ((0 : ℝ) ^ 2 + (x * y) ^ 2) = x * y := by
    intro y hy
    rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq (by positivity)]
  rw [hs f hf, hs fn hfn]
  simp only [zero_add]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Correction witness**: along the field-weakening pull-out curve the product
`T_max(f) · Ω(f)` with `Ω = 2πf/np` strictly decreases, so it is not a constant-power curve. -/
@[powerlib_foundation] theorem fieldWeakening_power_strictAnti (Vn x np : ℝ) (hV : Vn ≠ 0)
    (hx : 0 < x) (hnp : 0 < np) :
    StrictAntiOn (fun f => maxTorque Vn (2 * Real.pi * f) 0 (x * f) * (2 * Real.pi * f / np))
      (Set.Ioi 0) := by
  intro f1 hf1 f2 hf2 h12
  simp only [Set.mem_Ioi] at hf1 hf2
  have hs : ∀ y : ℝ, 0 < y → Real.sqrt ((0 : ℝ) ^ 2 + (x * y) ^ 2) = x * y := by
    intro y hy
    rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq (by positivity)]
  have e : ∀ y : ℝ, 0 < y →
      maxTorque Vn (2 * Real.pi * y) 0 (x * y) * (2 * Real.pi * y / np) =
        3 * Vn ^ 2 / (2 * x * np) / y := by
    intro y hy
    unfold maxTorque
    rw [hs y hy]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  simp only
  rw [e f1 hf1, e f2 hf2]
  apply div_lt_div_of_pos_left (by positivity) hf1 h12

end powerlib.Drives.ScalarVF
