import theorem.Criteria.Hurwitz2
import theorem.Transform.Park
import theorem.Linear.Family
import theorem.Linear.Jordan
import theorem.TMIO.ClaimElab
import theorem.Spectral.Local

/-! # Linearized SRF-PLL: state-space models, transfer functions and tuning

Model boundary.
* System (every model of this module): three-phase SRF-PLL (Park projection on the PLL frame + PI
  loop filter + VCO) on an ideal balanced sinusoidal grid of constant amplitude `V`, **linearized**
  at the locked operating point `θ̃ = θ̂ − θ_g = 0` (phase-detector slope `∂V_q/∂θ̃ = −V`). No
  pre-filter (SOGI/DDSRF/MAF), sampling, delay, PWM, current loop, LCL filter, saturation or
  anti-windup. Continuous time. Parameters `V, K_p, K_i` are real numbers; every hypothesis is
  stated in each theorem.
* State order `(θ, η)`: `θ` = PLL angle deviation (phase model, port model) or phase error
  `θ̃` (frequency model); `η = ∫ V_q dt` = raw PI integrator state (V·s).
  All three models share the state matrix `linA = [[−V K_p, K_i], [−V, 0]]`, which is the
  Jacobian of the nonlinear SRF-PLL error field at its in-phase equilibrium
  (`theorem/PLL/Model.lean`, `srf_fderiv_inPhase`).
* `phaseModel`: input grid angle deviation `Δθ_g`, output `Δθ̂`
  (`θ̂̇ = K_p V (θ_g − θ̂) + K_i η`, `η̇ = V (θ_g − θ̂)`); transfer
  `H_pll(s) = V (K_p s + K_i) / (s² + V K_p s + V K_i)` (T-pll-dynamics §1.3).
* `frequencyModel`: input grid frequency deviation `Δω_g`, output estimated frequency
  deviation `Δω̂ = −V K_p θ̃ + K_i η`; same transfer `H_pll` (T-pll-dynamics §1.4,
  T-frequency-measurement §1.1 with `V = 1`).
* `portModel`: input external q-axis voltage perturbation `ΔV_q^sys`, output `Δθ̂`, with the
  PLL-frame voltage `V_q^pll = ΔV_q^sys − V Δθ̂` (self-rotation feedback); transfer
  `G_pll(s) = (K_p s + K_i) / (s² + V K_p s + V K_i) = H_pll / V` (T-pll-dynamics §1.11).
* `admittanceModel I_d0`: same input, output `ΔI_q^sys = I_d0 Δθ̂`: the PLL contribution
  to the q-axis port admittance of a current-controlled converter whose current is held at
  its PLL-frame reference `(I_d0, I_q0)` (IN-positive current, work-sync `conventions.md`
  §D1; only the PLL term, ideal current loop, no outer loops). `rot_linearization` derives the
  output gain `I_d0` from the frame rotation `I^sys = rot(Δθ̂) I^pll`.

Source: work-sync `theory/T-pll-dynamics.md` §1.3, §1.4, §1.5, §1.11;
`theory/T-invariant-coordinates.md` §1.2 (ζ algebra, raw-voltage tuning);
`theory/T-gfl-impedance.md` §1.3 (`G_i^pll`), §1.6; `theory/T-frequency-measurement.md` §1.1.

Results.
* `det(sI − linA) = s² + V K_p s + V K_i`; `linA` Hurwitz iff `V K_p > 0 ∧ V K_i > 0`; the
  same condition is necessary and sufficient for global exponential stability of the linear PLL
  (`LinearPLL.mem_den_globallyExponentiallyStable_iff`).
* Transfer functions above; `H_pll(0) = 1`; `G_pll = H_pll / V`.
* `ω_n = √(V K_i)`, `ζ = V K_p / (2 ω_n)`; standard form `s² + 2ζω_n s + ω_n²`;
  `ζ = (K_p/2)√(V/K_i)`, `4ζ² = V K_p²/K_i`; raw-voltage tuning `K_p = 2ζ₀ω_b/V`,
  `K_i = ω_b²/V` gives `ω_n = ω_b`, `ζ = ζ₀` (`ζ₀ = 1/√2`: `K_p = √2 ω_b / V`);
  `ω_n(V) = ω_n(V₀)√(V/V₀)`; normalized-input gains applied to raw `V_q` give
  `ζ_eff = ζ √V`.
* `Re G_pll(jω) = (V K_i² + ω²(V K_p² − K_i)) / |den|²`; for `V, K_p, K_i > 0`,
  `Re G_pll(jω) > 0 ∀ω ⇔ K_i ≤ V K_p² ⇔ ζ ≥ 1/2`; with `I_d0 < 0` (exporting active power)
  this gives `Re Y_qq^pll(jω) < 0 ∀ω` (negative conductance).

Family and connection conclusions.
`LinearPLL.family` reads a complete system `LinearPLL.Model` — amplitude `V`, PI gains `K_p`,
`K_i` and the input-output channel (phase, frequency, port, or admittance with current `I_d0`) —
as the port system (`Linear.Plant.system`) of the corresponding plant of this module; every
channel has the state matrix `linA`, so the flow sentences (about the origin, the locked point)
depend only on `V K_p` and `V K_i`. Requirements are static: positive proportional loop gain
`V K_p > 0`, positive integral loop gain `V K_i > 0`, or a negative loop gain. Connection
conclusions: soundness of every translation (`chain_le_semantics`), exactness for the attractive
sentences and sampled contraction (`exact_hurwitz`), the global exponential stability
equivalence (`mem_den_globallyExponentiallyStable_iff`, for every channel), and the boundaries
`not_exact_lyapunovStable`, `not_exact_unstable`, `not_exact_conservative` (zero-gain and
Jordan-block witnesses). Decay rates, conservation and passivity have no available translation (the
inconsistent whole language). The frequency-domain results (transfer functions, `Re G_pll`,
`admittanceModel_re_neg`) are static evidence on the plants, not connection conclusions.

Correction (T-pll-dynamics §1.11 / T-gfl-impedance §1.3, "phase near 0° ⇒ real part > 0"):
`Re G_pll(jω) > 0` at **every** frequency holds exactly when `K_i ≤ V K_p²` (`ζ ≥ 1/2`); for
`ζ < 1/2` it becomes negative at high frequency (`re_transfer_portModel_pos_iff`), so the
sign of `Re Y_qq^pll` is guaranteed only under that tuning condition.
-/

noncomputable section
namespace powerlib.PLL
open Matrix

/-! ## State matrix and models -/

/-- Linearized SRF-PLL state matrix in state order `(θ, η)`: `[[−V K_p, K_i], [−V, 0]]`. -/
def linA (V Kp Ki : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-(V * Kp), Ki; -V, 0]

/-- Closed-loop phase tracking model: input `Δθ_g`, output `Δθ̂`. -/
def phaseModel (V Kp Ki : ℝ) : Linear.Plant 2 1 :=
  ⟨linA V Kp Ki, !![V * Kp; V], !![1, 0], 0⟩

/-- Frequency tracking model: input `Δω_g`, output `Δω̂ = −V K_p θ̃ + K_i η`. -/
def frequencyModel (V Kp Ki : ℝ) : Linear.Plant 2 1 :=
  ⟨linA V Kp Ki, !![-1; 0], !![-(V * Kp), Ki], 0⟩

/-- Port model: input `ΔV_q^sys`, output `Δθ̂` (`G_pll`). -/
def portModel (V Kp Ki : ℝ) : Linear.Plant 2 1 :=
  ⟨linA V Kp Ki, !![Kp; 1], !![1, 0], 0⟩

/-- PLL admittance model: input `ΔV_q^sys`, output `ΔI_q^sys = I_d0 Δθ̂` (`Y_qq^pll`). -/
def admittanceModel (V Kp Ki Id0 : ℝ) : Linear.Plant 2 1 :=
  ⟨linA V Kp Ki, !![Kp; 1], !![Id0, 0], 0⟩

/-- Loop polynomial `s² + V K_p s + V K_i`. -/
def loopPoly (V Kp Ki : ℝ) (s : ℂ) : ℂ := s ^ 2 + (V : ℂ) * Kp * s + (V : ℂ) * Ki

/-- `H_pll(s) = V (K_p s + K_i) / (s² + V K_p s + V K_i)`. -/
def closedLoopTF (V Kp Ki : ℝ) (s : ℂ) : ℂ :=
  ((V : ℂ) * Kp * s + (V : ℂ) * Ki) / loopPoly V Kp Ki s

/-- `G_pll(s) = (K_p s + K_i) / (s² + V K_p s + V K_i)`. -/
def portTF (V Kp Ki : ℝ) (s : ℂ) : ℂ := ((Kp : ℂ) * s + Ki) / loopPoly V Kp Ki s

@[powerlib_foundation] theorem characteristicMatrix_linA (V Kp Ki : ℝ) (s : ℂ) :
    Linear.characteristicMatrix (linA V Kp Ki) s = !![s + V * Kp, -(Ki : ℂ); V, s] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Linear.characteristicMatrix, linA]

/-- Characteristic polynomial of the linearized PLL: `det(sI − A) = s² + V K_p s + V K_i`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_linA (V Kp Ki : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (linA V Kp Ki) s).det = loopPoly V Kp Ki s := by
  rw [characteristicMatrix_linA, det_fin_two_of, loopPoly]; ring

@[simp, powerlib_foundation] theorem trace_linA (V Kp Ki : ℝ) : (linA V Kp Ki).trace = -(V * Kp) := by
  simp [linA, Matrix.trace_fin_two]

@[simp, powerlib_foundation] theorem det_linA (V Kp Ki : ℝ) : (linA V Kp Ki).det = V * Ki := by
  simp [linA, Matrix.det_fin_two]; ring

/-- Hurwitz test: `linA` is Hurwitz iff `V K_p > 0 ∧ V K_i > 0`. -/
@[powerlib_foundation] theorem isHurwitz_linA_iff (V Kp Ki : ℝ) :
    LinearSystems.IsHurwitz (linA V Kp Ki) ↔ 0 < V * Kp ∧ 0 < V * Ki := by
  rw [Criteria.isHurwitz_fin_two_iff, trace_linA, det_linA, neg_lt_zero]

/-- Every root of the loop polynomial lies in the open left half-plane iff
`V K_p > 0 ∧ V K_i > 0`. -/
@[powerlib_foundation] theorem loopPoly_roots_re_neg_iff (V Kp Ki : ℝ) :
    (∀ s : ℂ, loopPoly V Kp Ki s = 0 → s.re < 0) ↔ 0 < V * Kp ∧ 0 < V * Ki := by
  have h := Criteria.quadratic_roots_re_neg_iff (V * Kp) (V * Ki)
  push_cast at h
  simpa only [loopPoly] using h

/-! ## Transfer functions -/

@[powerlib_foundation] private lemma transfer_linA_model (V Kp Ki : ℝ) (B : Matrix (Fin 2) (Fin 1) ℝ)
    (C : Matrix (Fin 1) (Fin 2) ℝ) (s : ℂ) :
    Linear.transfer (⟨linA V Kp Ki, B, C, 0⟩ : Linear.Plant 2 1) s =
      (loopPoly V Kp Ki s)⁻¹ •
        (Linear.complexify C * !![s, (Ki : ℂ); -(V : ℂ), s + V * Kp] * Linear.complexify B) := by
  rw [Linear.transfer_eq_adjugate]
  simp only
  rw [det_characteristicMatrix_linA, characteristicMatrix_linA, adjugate_fin_two_of]
  simp [Linear.complexify]

/-- `θ̂(s)/θ_g(s) = V (K_p s + K_i) / (s² + V K_p s + V K_i)` (division by zero is `0` on both
sides, so the identity holds for every `s`). -/
@[powerlib_foundation] theorem transfer_phaseModel (V Kp Ki : ℝ) (s : ℂ) :
    Linear.transfer (phaseModel V Kp Ki) s = !![closedLoopTF V Kp Ki s] := by
  rw [phaseModel, transfer_linA_model]
  ext i j; fin_cases i; fin_cases j
  simp [closedLoopTF, Linear.complexify, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `ω̂(s)/ω_g(s) = H_pll(s)`: the frequency estimate has the same transfer function. -/
@[powerlib_foundation] theorem transfer_frequencyModel (V Kp Ki : ℝ) (s : ℂ) :
    Linear.transfer (frequencyModel V Kp Ki) s = !![closedLoopTF V Kp Ki s] := by
  rw [frequencyModel, transfer_linA_model]
  ext i j; fin_cases i; fin_cases j
  simp [closedLoopTF, Linear.complexify, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `Δθ̂(s)/ΔV_q^sys(s) = G_pll(s) = (K_p s + K_i)/(s² + V K_p s + V K_i)`. -/
@[powerlib_foundation] theorem transfer_portModel (V Kp Ki : ℝ) (s : ℂ) :
    Linear.transfer (portModel V Kp Ki) s = !![portTF V Kp Ki s] := by
  rw [portModel, transfer_linA_model]
  ext i j; fin_cases i; fin_cases j
  simp [portTF, Linear.complexify, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `Y_qq^pll(s) = I_d0 G_pll(s)`. -/
@[powerlib_foundation] theorem transfer_admittanceModel (V Kp Ki Id0 : ℝ) (s : ℂ) :
    Linear.transfer (admittanceModel V Kp Ki Id0) s = !![(Id0 : ℂ) * portTF V Kp Ki s] := by
  rw [admittanceModel, transfer_linA_model]
  ext i j; fin_cases i; fin_cases j
  simp [portTF, Linear.complexify, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `G_pll = H_pll / V` (`V ≠ 0`). -/
@[powerlib_foundation] theorem portTF_eq_closedLoopTF_div {V : ℝ} (hV : V ≠ 0) (Kp Ki : ℝ)
    (s : ℂ) : portTF V Kp Ki s = closedLoopTF V Kp Ki s / V := by
  have hV' : (V : ℂ) ≠ 0 := by exact_mod_cast hV
  rw [portTF, closedLoopTF]
  field_simp

/-- Transfer-matrix form of `G_pll = H_pll / V`. -/
@[powerlib_foundation] theorem transfer_portModel_eq_smul {V : ℝ} (hV : V ≠ 0) (Kp Ki : ℝ)
    (s : ℂ) : Linear.transfer (portModel V Kp Ki) s =
      (V : ℂ)⁻¹ • Linear.transfer (phaseModel V Kp Ki) s := by
  rw [transfer_portModel, transfer_phaseModel, portTF_eq_closedLoopTF_div hV]
  ext i j; fin_cases i; fin_cases j
  simp [div_eq_inv_mul]

/-- Unit DC gain `H_pll(0) = 1`: zero steady-state phase error for a phase step and zero
steady-state frequency error for a frequency step (final-value form). -/
@[powerlib_foundation] theorem closedLoopTF_zero {V Ki : ℝ} (h : V * Ki ≠ 0) (Kp : ℝ) :
    closedLoopTF V Kp Ki 0 = 1 := by
  have h' : (V : ℂ) * Ki ≠ 0 := by exact_mod_cast h
  simp [closedLoopTF, loopPoly, h']

@[powerlib_foundation] theorem transfer_phaseModel_zero {V Ki : ℝ} (h : V * Ki ≠ 0) (Kp : ℝ) :
    Linear.transfer (phaseModel V Kp Ki) 0 = 1 := by
  rw [transfer_phaseModel, closedLoopTF_zero h]
  ext i j; fin_cases i; fin_cases j; rfl

@[powerlib_foundation] theorem transfer_frequencyModel_zero {V Ki : ℝ} (h : V * Ki ≠ 0) (Kp : ℝ) :
    Linear.transfer (frequencyModel V Kp Ki) 0 = 1 := by
  rw [transfer_frequencyModel, closedLoopTF_zero h]
  ext i j; fin_cases i; fin_cases j; rfl

/-! ## Natural frequency and damping ratio -/

/-- `ω_n = √(V K_i)`. -/
def omegaN (V Ki : ℝ) : ℝ := Real.sqrt (V * Ki)

/-- `ζ = V K_p / (2 ω_n)`. -/
def zeta (V Kp Ki : ℝ) : ℝ := V * Kp / (2 * omegaN V Ki)

/-- Standard second-order form `s² + 2ζω_n s + ω_n²` of the loop polynomial (`V K_i > 0`). -/
@[powerlib_foundation] theorem loopPoly_eq_standard {V Kp Ki : ℝ} (h : 0 < V * Ki) (s : ℂ) :
    loopPoly V Kp Ki s = s ^ 2 + 2 * (zeta V Kp Ki : ℂ) * (omegaN V Ki : ℂ) * s +
      (omegaN V Ki : ℂ) ^ 2 := by
  have hω : 0 < omegaN V Ki := Real.sqrt_pos.mpr h
  have hsq : omegaN V Ki ^ 2 = V * Ki := Real.sq_sqrt h.le
  have h2 : 2 * zeta V Kp Ki * omegaN V Ki = V * Kp := by
    rw [zeta]; field_simp
  have h2' : 2 * (zeta V Kp Ki : ℂ) * (omegaN V Ki : ℂ) = (V : ℂ) * Kp := by exact_mod_cast h2
  have hsq' : (omegaN V Ki : ℂ) ^ 2 = (V : ℂ) * Ki := by exact_mod_cast hsq
  rw [loopPoly, h2', hsq']

/-- `ζ = (K_p/2) √(V/K_i)` for `V, K_i > 0` (T-pll-dynamics §1.3 boxed). -/
@[powerlib_foundation] theorem zeta_eq {V Kp Ki : ℝ} (hV : 0 < V) (hKi : 0 < Ki) :
    zeta V Kp Ki = Kp / 2 * Real.sqrt (V / Ki) := by
  rw [zeta, omegaN, Real.sqrt_mul hV.le, Real.sqrt_div hV.le]
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hsK : 0 < Real.sqrt Ki := Real.sqrt_pos.mpr hKi
  have hV' : V = Real.sqrt V * Real.sqrt V := (Real.mul_self_sqrt hV.le).symm
  field_simp
  nth_rewrite 1 [hV']
  ring

/-- `4ζ² = V K_p² / K_i` (T-invariant-coordinates §1.2). -/
@[powerlib_foundation] theorem four_mul_zeta_sq {V Kp Ki : ℝ} (hV : V ≠ 0) (h : 0 < V * Ki) :
    4 * zeta V Kp Ki ^ 2 = V * Kp ^ 2 / Ki := by
  have hsq : omegaN V Ki ^ 2 = V * Ki := Real.sq_sqrt h.le
  have hω : omegaN V Ki ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  have hKi : Ki ≠ 0 := by rintro rfl; simp at h
  rw [zeta, div_pow, mul_pow, mul_pow, hsq]
  field_simp
  ring

/-- Raw-voltage PI tuning `K_p = 2ζ₀ω_b/V`, `K_i = ω_b²/V` gives `ω_n = ω_b` and `ζ = ζ₀`
independently of `V` (T-invariant-coordinates §1.2). -/
@[powerlib_foundation] theorem rawVoltageTuning {V ωb : ℝ} (hV : V ≠ 0) (hω : 0 < ωb)
    (ζ₀ : ℝ) :
    omegaN V (ωb ^ 2 / V) = ωb ∧ zeta V (2 * ζ₀ * ωb / V) (ωb ^ 2 / V) = ζ₀ := by
  have hn : omegaN V (ωb ^ 2 / V) = ωb := by
    rw [omegaN, show V * (ωb ^ 2 / V) = ωb ^ 2 by field_simp, Real.sqrt_sq hω.le]
  refine ⟨hn, ?_⟩
  rw [zeta, hn]
  field_simp

/-- Typical tuning (T-pll-dynamics §1.3): `K_p = √2 ω_b / V`, `K_i = ω_b² / V` gives
`ω_n = ω_b` and `ζ = 1/√2`. -/
@[powerlib_foundation] theorem standardTuning {V ωb : ℝ} (hV : V ≠ 0) (hω : 0 < ωb) :
    omegaN V (ωb ^ 2 / V) = ωb ∧
      zeta V (Real.sqrt 2 * ωb / V) (ωb ^ 2 / V) = 1 / Real.sqrt 2 := by
  have h2 : Real.sqrt 2 = 2 * (1 / Real.sqrt 2) := by
    have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    field_simp; linarith
  have h := rawVoltageTuning hV hω (1 / Real.sqrt 2)
  rw [← h2] at h
  exact h

/-- Operating-point dependence (T-pll-dynamics §1.5): `ω_n(V) = ω_n(V₀) √(V/V₀)`. -/
@[powerlib_foundation] theorem omegaN_scale {V V₀ Ki : ℝ} (hV₀ : 0 < V₀) (hKi : 0 ≤ Ki) : omegaN V Ki = omegaN V₀ Ki * Real.sqrt (V / V₀) := by
  rw [omegaN, omegaN, ← Real.sqrt_mul (mul_nonneg hV₀.le hKi)]
  congr 1
  field_simp

/-- Applying gains designed for the normalized input `V_q/V` (design `ζ = zeta 1 K_p K_i`) to
the raw signal `V_q` gives `ζ_eff = ζ √V` (T-invariant-coordinates §1.2). -/
@[powerlib_foundation] theorem zeta_raw_eq {V Kp Ki : ℝ} (hV : 0 < V) (hKi : 0 < Ki) :
    zeta V Kp Ki = zeta 1 Kp Ki * Real.sqrt V := by
  rw [zeta_eq hV hKi, zeta_eq one_pos hKi, Real.sqrt_div hV.le, Real.sqrt_div zero_le_one,
    Real.sqrt_one]
  ring

/-- `ζ ≥ 1/2 ⇔ K_i ≤ V K_p²` (`V, K_i > 0`, `K_p ≥ 0`). -/
@[powerlib_foundation] theorem half_le_zeta_iff {V Kp Ki : ℝ} (hV : 0 < V) (hKp : 0 ≤ Kp)
    (hKi : 0 < Ki) : 1 / 2 ≤ zeta V Kp Ki ↔ Ki ≤ V * Kp ^ 2 := by
  have h4 := four_mul_zeta_sq (Kp := Kp) hV.ne' (mul_pos hV hKi)
  have hz : 0 ≤ zeta V Kp Ki := by
    rw [zeta]; exact div_nonneg (mul_nonneg hV.le hKp) (by unfold omegaN; positivity)
  constructor
  · intro h
    have : 1 ≤ 4 * zeta V Kp Ki ^ 2 := by nlinarith
    rw [h4, le_div_iff₀ hKi] at this
    linarith
  · intro h
    have : 1 ≤ 4 * zeta V Kp Ki ^ 2 := by
      rw [h4, le_div_iff₀ hKi]; linarith
    nlinarith

/-! ## Real part of `G_pll(jω)` and the PLL negative conductance -/

/-- `Re G_pll(jω) = (V K_i² + ω²(V K_p² − K_i)) / ((V K_i − ω²)² + (V K_p ω)²)`. -/
@[powerlib_foundation] theorem re_portTF (V Kp Ki ω : ℝ) :
    (portTF V Kp Ki ((ω : ℂ) * Complex.I)).re =
      (V * Ki ^ 2 + ω ^ 2 * (V * Kp ^ 2 - Ki)) / ((V * Ki - ω ^ 2) ^ 2 + (V * Kp * ω) ^ 2) := by
  have hden : loopPoly V Kp Ki ((ω : ℂ) * Complex.I) =
      ⟨V * Ki - ω ^ 2, V * Kp * ω⟩ := by
    apply Complex.ext <;> simp [loopPoly, pow_two]
    ring
  have hnum : (Kp : ℂ) * ((ω : ℂ) * Complex.I) + Ki = ⟨Ki, Kp * ω⟩ := by
    apply Complex.ext <;> simp
  rw [portTF, hden, hnum, Complex.div_re, Complex.normSq_mk, ← add_div]
  congr 1 <;> ring

@[powerlib_foundation] private lemma portTF_den_pos {V Kp Ki : ℝ} (hVKp : V * Kp ≠ 0)
    (hVKi : V * Ki ≠ 0) (ω : ℝ) : 0 < (V * Ki - ω ^ 2) ^ 2 + (V * Kp * ω) ^ 2 := by
  rcases eq_or_ne ω 0 with rfl | hω
  · simp; positivity
  · have : 0 < (V * Kp * ω) ^ 2 := by positivity
    positivity

/-- For `V, K_p, K_i > 0`: `Re G_pll(jω) > 0` for every real `ω` iff `K_i ≤ V K_p²`. -/
@[powerlib_foundation] theorem re_portTF_pos_iff {V Kp Ki : ℝ} (hV : 0 < V) (hKp : 0 < Kp)
    (hKi : 0 < Ki) :
    (∀ ω : ℝ, 0 < (portTF V Kp Ki ((ω : ℂ) * Complex.I)).re) ↔ Ki ≤ V * Kp ^ 2 := by
  have hden := portTF_den_pos (mul_pos hV hKp).ne' (mul_pos hV hKi).ne'
  constructor
  · intro h
    by_contra hc
    push Not at hc
    set c := Ki - V * Kp ^ 2 with hcdef
    have hc' : 0 < c := by linarith
    set ω := Real.sqrt (V * Ki ^ 2 / c + 1) with hω
    have hω2 : ω ^ 2 = V * Ki ^ 2 / c + 1 := Real.sq_sqrt (by positivity)
    have hneg : V * Ki ^ 2 + ω ^ 2 * (V * Kp ^ 2 - Ki) < 0 := by
      rw [hω2, show V * Kp ^ 2 - Ki = -c by rw [hcdef]; ring]
      field_simp
      nlinarith
    have := h ω
    rw [re_portTF] at this
    exact absurd this (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hneg.le (hden ω).le))
  · intro h ω
    rw [re_portTF]
    apply div_pos _ (hden ω)
    have : 0 ≤ ω ^ 2 * (V * Kp ^ 2 - Ki) := mul_nonneg (sq_nonneg _) (by linarith)
    have : 0 < V * Ki ^ 2 := by positivity
    linarith

/-- The same statement for the port model's transfer function: `Re G_pll(jω) > 0 ∀ω ⇔
ζ ≥ 1/2` (`V, K_p, K_i > 0`). -/
@[powerlib_foundation] theorem re_transfer_portModel_pos_iff {V Kp Ki : ℝ} (hV : 0 < V)
    (hKp : 0 < Kp) (hKi : 0 < Ki) :
    (∀ ω : ℝ, 0 < (Linear.transfer (portModel V Kp Ki) ((ω : ℂ) * Complex.I) 0 0).re) ↔
      1 / 2 ≤ zeta V Kp Ki := by
  rw [half_le_zeta_iff hV hKp.le hKi, ← re_portTF_pos_iff hV hKp hKi]
  simp [transfer_portModel]

/-- Frame-rotation linearization of a constant PLL-frame current (`T-gfl-impedance` §1.3):
`d/dθ̂ (rot θ̂ · I₀)|₀ = J I₀ = (−I_q0, I_d0)`; its q component is the output gain `I_d0` of
`admittanceModel`. -/
@[powerlib_foundation] theorem rot_linearization (I0 : Fin 2 → ℝ) :
    HasDerivAt (fun θ : ℝ => Transform.rot θ *ᵥ I0) ![-(I0 1), I0 0] 0 := by
  have h := Transform.hasDerivAt_rot_mulVec (θ := fun θ => θ) (x := fun _ => I0) (t := 0)
    (hasDerivAt_id 0) (hasDerivAt_const 0 I0)
  convert h using 1
  simp

/-- PLL negative conductance (T-pll-dynamics §1.11, T-gfl-impedance §1.6): for
`V, K_p, K_i > 0` with `ζ ≥ 1/2` (`K_i ≤ V K_p²`) and an exporting converter
(`I_d0 < 0`, IN-positive), the PLL contribution to the q-axis admittance has negative real
part at every frequency. Static evidence on the model (a transfer-function inequality), not a
connection conclusion. -/
@[powerlib_foundation] theorem admittanceModel_re_neg {V Kp Ki Id0 : ℝ} (hV : 0 < V) (hKp : 0 < Kp)
    (hKi : 0 < Ki) (hζ : 1 / 2 ≤ zeta V Kp Ki) (hId : Id0 < 0) (ω : ℝ) :
    (Linear.transfer (admittanceModel V Kp Ki Id0) ((ω : ℂ) * Complex.I) 0 0).re < 0 := by
  have hpos := ((re_portTF_pos_iff hV hKp hKi).mpr
    ((half_le_zeta_iff hV hKp.le hKi).mp hζ)) ω
  rw [transfer_admittanceModel]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  exact mul_neg_of_neg_of_pos hId hpos


/-! ## The linearized SRF-PLL family -/

namespace LinearPLL

/-- The input-output channel through which the linearized PLL is read; every channel has the state
matrix `linA`. -/
inductive Channel
  /-- Grid-angle deviation to estimated-angle deviation (`phaseModel`). -/
  | phase
  /-- Grid-frequency deviation to estimated-frequency deviation (`frequencyModel`). -/
  | frequency
  /-- External q-axis voltage to estimated-angle deviation (`portModel`). -/
  | port
  /-- External q-axis voltage to q-axis current, PLL-frame d current `I_d0`
  (`admittanceModel`). -/
  | admittance (Id0 : ℝ)

/-- A linearized SRF-PLL: grid voltage amplitude, PI gains and the channel it is read through. -/
structure Model where
  /-- Grid voltage amplitude (phase-detector slope `−V`). -/
  V : ℝ
  /-- Proportional gain. -/
  Kp : ℝ
  /-- Integral gain. -/
  Ki : ℝ
  /-- Input-output channel. -/
  channel : Channel

/-- The plant of a model: the state-space model of its channel. -/
def Model.plant (m : Model) : Linear.Plant 2 1 :=
  match m.channel with
  | .phase => phaseModel m.V m.Kp m.Ki
  | .frequency => frequencyModel m.V m.Kp m.Ki
  | .port => portModel m.V m.Kp m.Ki
  | .admittance Id0 => admittanceModel m.V m.Kp m.Ki Id0

/-- Every channel has the state matrix `linA`. -/
@[powerlib_foundation] theorem Model.plant_A (m : Model) : m.plant.A = linA m.V m.Kp m.Ki := by
  rcases m with ⟨V, Kp, Ki, c⟩
  cases c <;> rfl

/-- Requirements on the linearized PLL, all static. -/
inductive Requirement
  /-- Positive proportional loop gain `V K_p > 0` (state-matrix trace `< 0`). -/
  | proportional
  /-- Positive integral loop gain `V K_i > 0` (state-matrix determinant `> 0`). -/
  | integral
  /-- A negative loop gain: `V K_p < 0` or `V K_i < 0`. -/
  | negativeGain

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .proportional => 0 < m.V * m.Kp
  | .integral => 0 < m.V * m.Ki
  | .negativeGain => m.V * m.Kp < 0 ∨ m.V * m.Ki < 0

/-- The translation of the sentences: the attractive sentences, sampled contraction and Lyapunov
stability into both positive loop gains, instability into a negative loop gain. Decay rates,
conservation and passivity are translated into the whole (inconsistent) language: unavailable
translation coverage, not a usable translation. -/
def translate : Sentence → Set Requirement
  | .flow .unstable => {.negativeGain}
  | .flow (.decay _) | .flow .conservative => Set.univ
  | .flow _ => {.proportional, .integral}
  | .passive => Set.univ

/-- The linearized SRF-PLL family: every model read as the port system of its channel's plant. -/
def family : Family Model Requirement 2 1 := ⟨fun m => m.plant.system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear : family.IsLinear Model.plant := fun _ => rfl

/-- No model has both positive loop gains and a negative one: the whole requirement language is
inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  have h1 : 0 < m.V * m.Kp := h .proportional
  have h2 : 0 < m.V * m.Ki := h .integral
  rcases (h .negativeGain : m.V * m.Kp < 0 ∨ m.V * m.Ki < 0) with h3 | h3 <;> linarith

private theorem isHurwitz_plant_iff (m : Model) :
    LinearSystems.IsHurwitz m.plant.A ↔ 0 < m.V * m.Kp ∧ 0 < m.V * m.Ki := by
  rw [Model.plant_A, isHurwitz_linA_iff]

/-- A negative loop gain gives a characteristic root in the open right half plane. -/
private theorem unstable_of_negativeGain {m : Model} (h : m.V * m.Kp < 0 ∨ m.V * m.Ki < 0) :
    m ∈ family.den (.flow .unstable) := by
  refine family_isLinear.mem_den_flow.mpr ?_
  rw [Model.plant_A]
  obtain ⟨s, hs, hre⟩ : ∃ s : ℂ, (Linear.characteristicMatrix (linA m.V m.Kp m.Ki) s).det = 0 ∧
      0 < s.re := by
    rcases h with h | h
    · exact Criteria.exists_characteristic_root_re_pos_of_trace_pos _ (by rw [trace_linA]; linarith)
    · exact Criteria.exists_characteristic_root_re_pos_of_det_neg _ (by rw [det_linA]; exact h)
  exact Linear.unstable_of_root 0 hs hre

/-- Every translation of the linearized PLL family is sound: its translation chain lies below its
semantics connection. Both positive loop gains make the state matrix Hurwitz (the linear hub), a
negative loop gain gives a right-half-plane root (LeanForControl's eigenvalue instability). -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  have hhur : (∀ q ∈ ({.proportional, .integral} : Set Requirement), Meets m q) →
      LinearSystems.IsHurwitz m.plant.A := fun h =>
    (isHurwitz_plant_iff m).mpr ⟨h .proportional (by simp), h .integral (by simp)⟩
  rcases s with P | _
  · have hden : P.Attractive ∨ P = .contractive →
        translate (.flow P) = {.proportional, .integral} → m ∈ family.den (.flow P) := by
      intro hP ht
      rw [family_isLinear.den_hurwitz hP, Set.mem_ofPred_eq]
      exact hhur (ht ▸ hm)
    cases P
    case lyapunovStable =>
      exact family_isLinear.mem_den_flow.mpr (Linear.lyapunovStable_of_isHurwitz 0 (hhur hm))
    case unstable => exact unstable_of_negativeGain (hm .negativeGain rfl)
    case decay a => exact (hnone fun q => hm q trivial).elim
    case conservative => exact (hnone fun q => hm q trivial).elim
    case contractive => exact hden (Or.inr rfl) rfl
    all_goals exact hden (Or.inl trivial) rfl
  · exact (hnone fun q => hm q trivial).elim

/-- On the attractive sentences and sampled contraction the chain agrees with the semantics: both
positive loop gains are their exact translation, for every channel. -/
@[powerlib_domain] theorem exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have ht : translate (.flow P) = {.proportional, .integral} := by
    rcases hP with hP | rfl
    · cases P <;> first | rfl | exact absurd hP id
    · rfl
  unfold Family.Exact
  change TMIO.realize Meets (translate (.flow P)) = _
  rw [ht, family_isLinear.den_hurwitz hP]
  ext m
  simp only [TMIO.mem_realize, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, Set.mem_ofPred_eq, isHurwitz_plant_iff]
  rfl

/-- Linear SRF-PLL (every channel; they share the state matrix): global exponential stability of
the locked point iff `V K_p > 0 ∧ V K_i > 0`. -/
@[powerlib_domain] theorem mem_den_globallyExponentiallyStable_iff (m : Model) :
    connection% (m ∈ family.den (.flow .globallyExponentiallyStable) ↔
      m ∈ {m : Model | 0 < m.V * m.Kp ∧ 0 < m.V * m.Ki}) := by
  unfold powerlib.TMIO.Statement
  rw [family_isLinear.den_hurwitz
    (Or.inl Flow.Property.attractive_globallyExponentiallyStable), Set.mem_ofPred_eq,
    Set.mem_ofPred_eq, isHurwitz_plant_iff]

/-- The phase channel without loop gains (`V = 0`, `K_i = 0`): the state matrix is zero. -/
def frozen : Model := ⟨0, 0, 0, .phase⟩

@[powerlib_foundation] theorem frozen_plant_A : frozen.plant.A = 0 := by
  rw [Model.plant_A]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frozen, linA]

/-- The frozen loop conserves the energy `|x|²`. -/
@[powerlib_domain] theorem frozen_mem_den_conservative :
    connection% (frozen ∈ family.den (.flow .conservative)) := by
  unfold powerlib.TMIO.Statement
  refine family_isLinear.mem_den_conservative (P := 1) (by simp) (fun v hv => ?_)
    (by simp [frozen_plant_A])
  simpa using Matrix.dotProduct_self_star_pos_iff.mpr hv

/-- Conservation has no available translation, and none is exact: the frozen loop conserves an
energy while no model meets the whole language. -/
@[powerlib_domain] theorem not_exact_conservative :
    connection% (¬ family.Exact (.flow .conservative)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := frozen_mem_den_conservative
  unfold powerlib.TMIO.Statement at hmem
  rw [← h] at hmem
  change frozen ∈ TMIO.realize Meets Set.univ at hmem
  rw [realize_univ] at hmem
  exact hmem

/-- Both positive loop gains are a sound but not exact translation of Lyapunov stability: the
frozen loop is Lyapunov stable (conserved energy) with zero loop gains. -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have hmem : frozen ∈ family.den (.flow .lyapunovStable) := by
    have hc := frozen_mem_den_conservative
    unfold powerlib.TMIO.Statement at hc
    rw [family_isLinear.mem_den_flow] at hc ⊢
    exact Flow.Conservative.lyapunovStable hc
  refine Spectral.not_exact_of_witness hmem (q := .proportional) (by simp [family, translate])
    fun h' => ?_
  have h'' : 0 < frozen.V * frozen.Kp := h'
  simp [frozen] at h''

/-- The phase channel with `V = 0`, `K_i = 1`: the state matrix is the Jordan block
`[[0, 1], [0, 0]]`. -/
def jordan : Model := ⟨0, 0, 1, .phase⟩

/-- A negative loop gain is a sound but not exact translation of instability: with zero amplitude
and a nonzero integral gain the integrator drifts linearly (a zero Jordan chain), although no loop
gain is negative. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
  let w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
  have hv : v ≠ 0 := by intro h; have := congrArg (fun x => x 0) h; norm_num [v] at this
  have hAv : Linear.op jordan.plant.A v = 0 := by
    rw [Model.plant_A]
    ext i
    fin_cases i <;> norm_num [v, Linear.op, jordan, linA, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  have hAw : Linear.op jordan.plant.A w = v := by
    rw [Model.plant_A]
    ext i
    fin_cases i <;> norm_num [v, w, Linear.op, jordan, linA, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  have hmem : jordan ∈ family.den (.flow .unstable) :=
    family_isLinear.mem_den_flow.mpr (Linear.unstable_of_zero_jordan_chain hv hAv hAw)
  refine Spectral.not_exact_of_witness hmem (q := .negativeGain) rfl fun h => ?_
  rcases (h : jordan.V * jordan.Kp < 0 ∨ jordan.V * jordan.Ki < 0) with h | h <;>
    simp [jordan] at h

end LinearPLL

end powerlib.PLL
