import dependencies.Mathlib
import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import theorem.Machine.InductionMachine
import theorem.Machine.CascadeControl

/-! # Sensorless machine control: observer algebra (foundation)

Foundation layer; no closed-loop observer convergence is claimed.

Models and conventions: PMSM / IM space vectors, motor convention, amplitude-invariant
transform, electrical angles. Surface PMSM in the stationary frame:
`v = r i + L di/dt + e`, back-EMF `e = ωψ_f (−sin θ, cos θ)`. IPMSM in the rotor frame:
`ψ_dq = diag(L_d, L_q) i_dq`; an estimated frame lagging by `Δθ = θ − θ̂` sees
`x̂ = R(Δθ) x_dq`. High-frequency injection neglects resistance and rotation (`ω_h ≫ ω_r`),
the "LPF" is the average over one carrier period.

Contents.
* `backEMF_estimate`, `angle_of_backEMF` (atan2 / `Complex.arg` recovers `θ` on `(−π, π]`
  for `ωψ_f > 0`), `norm_backEMF` (`‖e‖/ψ_f = |ω|`), `arctan_formula_wrong`.
* SMO: error dynamics of the observer `dî/dt = (v − r î)/L + K sgn(i − î)`
  (`smo_error_dynamics`), the Lyapunov inequality
  `Σ s ṡ ≤ −(K − max|e|/L) Σ|s|` (`smo_lyapunov_bound`), and the equivalent control
  `K sgn_eq = −e/L` (`smo_equivalentControl`).
* HF injection: estimated-frame inverse inductance
  `R(Δθ) diag(1/L_d, 1/L_q) R(−Δθ) = [[Σ + Δ' cos 2Δθ, Δ' sin 2Δθ], [Δ' sin 2Δθ, Σ − Δ' cos 2Δθ]]`
  (`Σ = (1/L_d + 1/L_q)/2`, `Δ' = (1/L_d − 1/L_q)/2`), the HF currents
  `î_d = (V_h/ω_h)(Σ + Δ' cos 2Δθ) sin ω_h t` (`= V_h/(ω_h L_d)` at `Δθ = 0`),
  `î_q = (V_h/ω_h) Δ' sin 2Δθ sin ω_h t`, and the demodulated error
  `(V_h/(4ω_h))(1/L_d − 1/L_q) sin 2Δθ` (`hf_demodulation`).
* IM: voltage model (`InductionMachine.rotorFlux_voltageModel`), stationary-frame current model
  `dψ_r/dt = (L_m/T_r) i_s − (1/T_r − jω_r) ψ_r` (`currentModel_stationary`).
* Angle-tracking PI with a demodulation gain `k_ε`:
  `θ̂/θ = k_ε (K_p s + K_i)/(s² + k_ε K_p s + k_ε K_i)` (`trackingLoop_transfer`), and the
  small-signal gain of `K sin 2Δθ` is `2K` (`demod_smallSignal_gain`).

Source: work-sync theory/T-sensorless-machine-control.md §1.1, §1.4, §1.5, §1.9, §2.7.

Corrections.
* §1.1: `θ̂ = arctan(−ê_α/ê_β)` loses the quadrant whenever `cos θ < 0`
  (`arctan_formula_wrong`); use `atan2(−ê_α, ê_β)`; `‖ê‖/ψ_f` gives only `|ω|`.
* §1.4: with the attractive observer the equivalent control is `K sgn_eq = −e/L`, i.e.
  `ê = −L · LPF[K sgn(i − î)]`; the note's `+` sign (and the `−ê` term inside its observer) is
  inconsistent with its own `V̇` derivation, which uses the observer without `ê`.
* §1.5: the note's `î_d` has `−Δ' cos 2Δθ` (giving `1/L_q` at `Δθ = 0`, `hf_note_d_axis_wrong`)
  and the demodulated amplitude `V_h/(2ω_h)(…)` is too large by a factor 2 (and has the
  opposite sign for `Δθ = θ − θ̂`).
* §2.7: the tracking-loop transfer function omits the demodulation gain; with
  `ε = k_ε Δθ` it is `k_ε(K_p s + K_i)/(s² + k_ε K_p s + k_ε K_i)`.
-/

noncomputable section
namespace powerlib.Machine.Sensorless

open Complex ComplexConjugate Matrix

/-! ## Back-EMF methods -/

/-- Back-EMF estimate from the stator voltage equation `v = r i + L di/dt + e`. -/
@[powerlib_foundation] theorem backEMF_estimate (r L : ℝ) (v i di e : ℂ)
    (h : v = r * i + L * di + e) : e = v - r * i - L * di := by
  rw [h]; ring

/-- Surface-PMSM back-EMF `e = ωψ_f (−sin θ, cos θ)`. -/
def backEMF (ω ψf θ : ℝ) : ℂ := ⟨-(ω * ψf * Real.sin θ), ω * ψf * Real.cos θ⟩

/-- `atan2(−e_α, e_β) = arg(e_β − j e_α)` recovers the rotor angle for `ωψ_f > 0`. -/
@[powerlib_foundation] theorem angle_of_backEMF (ω ψf θ : ℝ) (hpos : 0 < ω * ψf)
    (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg ⟨(backEMF ω ψf θ).im, -(backEMF ω ψf θ).re⟩ = θ := by
  have h : (⟨(backEMF ω ψf θ).im, -(backEMF ω ψf θ).re⟩ : ℂ) =
      ((ω * ψf : ℝ) : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    apply Complex.ext <;> simp [backEMF, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [h, Complex.arg_real_mul _ hpos, Complex.arg_cos_add_sin_mul_I hθ]

/-- `‖e‖ = |ω| |ψ_f|`: the back-EMF magnitude gives the speed magnitude only. -/
@[powerlib_foundation] theorem norm_backEMF (ω ψf θ : ℝ) :
    ‖backEMF ω ψf θ‖ = |ω| * |ψf| := by
  have h : ‖backEMF ω ψf θ‖ ^ 2 = (|ω| * |ψf|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [backEMF]
    rw [mul_pow, sq_abs, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h

/-- The note's `arctan(−e_α/e_β)` misses the angle whenever `cos θ < 0`. -/
@[powerlib_foundation] theorem arctan_formula_wrong (ω ψf θ : ℝ) (hcos : Real.cos θ < 0) :
    Real.arctan (-(backEMF ω ψf θ).re / (backEMF ω ψf θ).im) ≠ θ := by
  intro h
  have h1 := Real.neg_pi_div_two_lt_arctan (-(backEMF ω ψf θ).re / (backEMF ω ψf θ).im)
  have h2 := Real.arctan_lt_pi_div_two (-(backEMF ω ψf θ).re / (backEMF ω ψf θ).im)
  rw [h] at h1 h2
  have : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨h1.le, h2.le⟩
  linarith

/-! ## Sliding-mode observer -/

/-- Error dynamics: plant `L di/dt = v − r i − e`, observer
`dî/dt = (v − r î)/L + K sgn(i − î)`, `s = i − î`. -/
@[powerlib_foundation] theorem smo_error_dynamics (r L K v i ih e : ℝ) (hL : L ≠ 0) :
    (v - r * i - e) / L - ((v - r * ih) / L + K * Real.sign (i - ih)) =
      -(r / L) * (i - ih) - e / L - K * Real.sign (i - ih) := by
  field_simp
  ring

@[powerlib_foundation] theorem mul_sign_eq_abs (x : ℝ) : x * Real.sign x = |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · rw [h, Real.sign_zero]; simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

/-- **SMO Lyapunov inequality.** For `V = ½ Σ s_i²` and
`ṡ_i = −(r/L) s_i − e_i/L − K sgn(s_i)` with `r ≥ 0`, `L > 0`, `|e_i| ≤ M`:
`Σ s_i ṡ_i ≤ −(K − M/L) Σ |s_i|`. -/
@[powerlib_foundation] theorem smo_lyapunov_bound {n : ℕ} (r L K M : ℝ) (hr : 0 ≤ r) (hL : 0 < L)
    (s e : Fin n → ℝ) (he : ∀ j, |e j| ≤ M) :
    ∑ j, s j * (-(r / L) * s j - e j / L - K * Real.sign (s j)) ≤ -(K - M / L) * ∑ j, |s j| := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hrl : 0 ≤ r / L := div_nonneg hr hL.le
  have h1 : s j * (-(r / L) * s j - e j / L - K * Real.sign (s j)) =
      -(r / L) * s j ^ 2 - s j * e j / L - K * |s j| := by
    rw [← mul_sign_eq_abs]; ring
  rw [h1]
  have h2 : -(s j * e j) ≤ |s j| * M := by
    have := neg_abs_le (s j * e j)
    rw [abs_mul] at this
    nlinarith [abs_nonneg (s j), he j]
  have h3 : -(s j * e j) / L ≤ |s j| * M / L := div_le_div_of_nonneg_right h2 hL.le
  have h4 : 0 ≤ r / L * s j ^ 2 := mul_nonneg hrl (sq_nonneg _)
  have h5 : -(s j * e j / L) ≤ |s j| * M / L := by rw [← neg_div]; exact h3
  have h6 : -(K - M / L) * |s j| = -(K * |s j|) + |s j| * M / L := by ring
  have h7 : -(r / L) * s j ^ 2 = -(r / L * s j ^ 2) := by ring
  rw [h6, h7]
  linarith

/-- Reaching condition: with `K > M/L`, `V̇ < 0` off the sliding surface. -/
@[powerlib_foundation] theorem smo_reaching {n : ℕ} (r L K M : ℝ) (hr : 0 ≤ r) (hL : 0 < L)
    (hK : M / L < K) (s e : Fin n → ℝ) (he : ∀ j, |e j| ≤ M) (hs : s ≠ 0) :
    ∑ j, s j * (-(r / L) * s j - e j / L - K * Real.sign (s j)) < 0 := by
  have hb := smo_lyapunov_bound r L K M hr hL s e he
  have hpos : 0 < ∑ j, |s j| := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hs
    exact lt_of_lt_of_le (abs_pos.mpr hj)
      (Finset.single_le_sum (fun i _ => abs_nonneg (s i)) (Finset.mem_univ j))
  have : -(K - M / L) * ∑ j, |s j| < 0 := mul_neg_of_neg_of_pos (by linarith) hpos
  linarith

/-- Equivalent control: if the error and its rate vanish at an instant
(`s = 0`, `ṡ = −(r/L)s − e/L − u = 0`), the switching injection equals `u = −e/L`. -/
@[powerlib_foundation] theorem smo_equivalentControl (r L e u : ℝ) (hL : L ≠ 0)
    (h : -(r / L) * 0 - e / L - u = 0) : u = -e / L := by
  field_simp at h ⊢
  linarith

/-! ## High-frequency injection -/

/-- Rotation matrix `R(a)`. -/
def rot (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos a, -Real.sin a; Real.sin a, Real.cos a]

@[powerlib_foundation] theorem rot_neg_mul_rot (a : ℝ) : rot (-a) * rot a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq a]

/-- Inverse inductance seen in the estimated frame. -/
def estInvInductance (Δ Ld Lq : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rot Δ * !![1 / Ld, 0; 0, 1 / Lq] * rot (-Δ)

@[powerlib_foundation] theorem estInvInductance_eq (Δ Ld Lq : ℝ) :
    estInvInductance Δ Ld Lq =
      !![(1 / Ld + 1 / Lq) / 2 + (1 / Ld - 1 / Lq) / 2 * Real.cos (2 * Δ),
          (1 / Ld - 1 / Lq) / 2 * Real.sin (2 * Δ);
        (1 / Ld - 1 / Lq) / 2 * Real.sin (2 * Δ),
          (1 / Ld + 1 / Lq) / 2 - (1 / Ld - 1 / Lq) / 2 * Real.cos (2 * Δ)] := by
  have hs := Real.sin_sq_add_cos_sq Δ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [estInvInductance, rot, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_two_mul,
      Real.sin_two_mul] <;>
    first
      | ring1
      | linear_combination (1 / Ld) * hs
      | linear_combination (1 / Lq) * hs

/-- Frame relation: `ψ_dq = diag(L_d, L_q) i_dq`, `ψ̂ = R(Δθ) ψ_dq`, `î = R(Δθ) i_dq` give
`î = Γ̂ ψ̂` with `Γ̂ = estInvInductance`. -/
@[powerlib_foundation] theorem estCurrent_eq (Δ Ld Lq : ℝ) (hd : Ld ≠ 0) (hq : Lq ≠ 0)
    (i : Fin 2 → ℝ) :
    rot Δ *ᵥ i = estInvInductance Δ Ld Lq *ᵥ (rot Δ *ᵥ (!![Ld, 0; 0, Lq] *ᵥ i)) := by
  have hdiag : !![1 / Ld, 0; 0, 1 / Lq] * !![Ld, 0; 0, Lq] = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd, hq]
  have key : estInvInductance Δ Ld Lq * (rot Δ * !![Ld, 0; 0, Lq]) = rot Δ := by
    unfold estInvInductance
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (rot (-Δ)), rot_neg_mul_rot, Matrix.one_mul, hdiag, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, key]

/-- The injected flux `ψ̂_d(t) = (V_h/ω_h) sin ω_h t` solves `dψ̂_d/dt = V_h cos ω_h t`,
`ψ̂_d(0) = 0` (resistance and rotation neglected). -/
@[powerlib_foundation] theorem hf_flux_hasDerivAt (Vh ωh t : ℝ) (hω : ωh ≠ 0) :
    HasDerivAt (fun s => Vh / ωh * Real.sin (ωh * s)) (Vh * Real.cos (ωh * t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => ωh * s) ωh t := by
    simpa using (hasDerivAt_id t).const_mul ωh
  have h2 := h1.sin.const_mul (Vh / ωh)
  convert h2 using 1
  field_simp

/-- HF current response in the estimated frame: `î = Γ̂ (ψ̂_d, 0)`. -/
@[powerlib_foundation] theorem hf_current (Δ Ld Lq Vh ωh t : ℝ) :
    estInvInductance Δ Ld Lq *ᵥ ![Vh / ωh * Real.sin (ωh * t), 0] =
      ![Vh / ωh * ((1 / Ld + 1 / Lq) / 2 + (1 / Ld - 1 / Lq) / 2 * Real.cos (2 * Δ)) *
          Real.sin (ωh * t),
        Vh / ωh * ((1 / Ld - 1 / Lq) / 2 * Real.sin (2 * Δ)) * Real.sin (ωh * t)] := by
  rw [estInvInductance_eq]
  ext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- At `Δθ = 0` the d-axis HF current amplitude is `V_h/(ω_h L_d)`. -/
@[powerlib_foundation] theorem hf_current_aligned (Ld Lq Vh ωh : ℝ) :
    Vh / ωh * ((1 / Ld + 1 / Lq) / 2 + (1 / Ld - 1 / Lq) / 2 * Real.cos (2 * 0)) =
      Vh / (ωh * Ld) := by
  simp
  field_simp
  ring

/-- **Correction witness**: the note's d-axis coefficient `Σ − Δ' cos 2Δθ` equals `1/L_q` at
`Δθ = 0`. -/
@[powerlib_foundation] theorem hf_note_d_axis_wrong (Ld Lq : ℝ) (hd : Ld ≠ 0) (hq : Lq ≠ 0)
    (hne : Ld ≠ Lq) :
    (1 / Ld + 1 / Lq) / 2 - (1 / Ld - 1 / Lq) / 2 * Real.cos (2 * 0) = 1 / Lq ∧ 1 / Lq ≠ 1 / Ld := by
  refine ⟨by simp; ring, ?_⟩
  intro h
  exact hne (by field_simp at h; linarith)

/-- Mean of `A sin²(ω t)` over one carrier period is `A/2`. -/
@[powerlib_foundation] theorem carrier_mean_sin_sq (A ω : ℝ) (hω : 0 < ω) :
    ω / (2 * Real.pi) * ∫ t in (0 : ℝ)..(2 * Real.pi / ω), A * Real.sin (ω * t) * Real.sin (ω * t) =
      A / 2 := by
  have hpi := Real.pi_pos
  have h1 : (∫ t in (0 : ℝ)..(2 * Real.pi / ω), A * Real.sin (ω * t) * Real.sin (ω * t)) =
      A * ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (ω * t) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  have h2 : (∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (ω * t) ^ 2) = Real.pi / ω := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hω.ne', integral_sin_sq]
    simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_mul, smul_eq_mul]
    rw [show ω * (2 * Real.pi / ω) = 2 * Real.pi by field_simp, Real.sin_two_pi]
    field_simp
    ring
  rw [h1, h2]
  field_simp

/-- **HF demodulation.** Multiplying `î_q` by the carrier and averaging over one period gives
`(V_h/(4ω_h))(1/L_d − 1/L_q) sin 2Δθ`. -/
@[powerlib_foundation] theorem hf_demodulation (Δ Ld Lq Vh ωh : ℝ) (hω : 0 < ωh) :
    ωh / (2 * Real.pi) * ∫ t in (0 : ℝ)..(2 * Real.pi / ωh),
        Vh / ωh * ((1 / Ld - 1 / Lq) / 2 * Real.sin (2 * Δ)) * Real.sin (ωh * t) *
          Real.sin (ωh * t) =
      Vh / (4 * ωh) * (1 / Ld - 1 / Lq) * Real.sin (2 * Δ) := by
  rw [carrier_mean_sin_sq _ ωh hω]
  field_simp
  ring

/-! ## Induction-machine observers -/

/-- Stationary-frame current model (`ω_e = 0`):
`dψ_r/dt = (L_m/T_r) i_s − (1/T_r − jω_r) ψ_r`. -/
@[powerlib_foundation] theorem currentModel_stationary (p : InductionMachine.Params)
    (hrr : p.rr ≠ 0) (hLr : p.Lr ≠ 0) (ωr : ℝ) (is ir dψr : ℂ)
    (h : InductionMachine.RotorVoltageEquation p 0 ωr ir (InductionMachine.rotorFlux p is ir) dψr) :
    dψr = (p.Lm / p.Tr : ℝ) * is -
      ((1 / p.Tr : ℝ) - Complex.I * ωr) * InductionMachine.rotorFlux p is ir := by
  have hc := InductionMachine.currentModel p hrr hLr 0 ωr is ir dψr h
  have hTr : p.Tr ≠ 0 := div_ne_zero hLr hrr
  have hTr' : (p.Tr : ℂ) ≠ 0 := by exact_mod_cast hTr
  push_cast at hc ⊢
  field_simp
  linear_combination hc

/-! ## Angle-tracking loop -/

/-- Small-signal gain of the demodulated error `K sin 2Δθ` is `2K`. -/
@[powerlib_foundation] theorem demod_smallSignal_gain (K : ℝ) :
    HasDerivAt (fun Δ => K * Real.sin (2 * Δ)) (2 * K) 0 := by
  have h1 : HasDerivAt (fun Δ : ℝ => 2 * Δ) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
  have h2 := h1.sin.const_mul K
  convert h2 using 1
  rw [mul_zero, Real.cos_zero]
  ring

/-- Linearised angle-tracking loop `θ̂' = K_p ε + K_i ξ`, `ξ' = ε`, `ε = k_ε (θ − θ̂)`;
state `(θ̂, ξ)`, input `θ`, output `θ̂`. -/
def trackingLoopModel (kε Kp Ki : ℝ) : Linear.Plant 2 1 :=
  CascadeControl.siso2 (-(Kp * kε)) Ki (-kε) 0 (Kp * kε) kε 1 0

@[powerlib_foundation] theorem trackingLoop_transfer (kε Kp Ki : ℝ) (s : ℂ)
    (hden : s ^ 2 + kε * Kp * s + kε * Ki ≠ 0) :
    Linear.transfer (trackingLoopModel kε Kp Ki) s 0 0 =
      kε * (Kp * s + Ki) / (s ^ 2 + kε * Kp * s + kε * Ki) := by
  have hdet : ((s - ((-(Kp * kε)) : ℝ)) * (s - ((0 : ℝ) : ℂ)) - (Ki : ℂ) * ((-kε : ℝ) : ℂ)) =
      s ^ 2 + kε * Kp * s + kε * Ki := by
    push_cast; ring
  unfold trackingLoopModel
  rw [CascadeControl.siso2_transfer _ _ _ _ _ _ _ _ s (by rw [hdet]; exact hden), hdet]
  push_cast
  ring

end powerlib.Machine.Sensorless
