import theorem.Transform.Park
import theorem.Criteria.Hurwitz2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # SRF-PLL phase detector and pre-filters: signal-level identities

All results here are coordinate / signal identities (foundation layer). They describe what
the SRF-PLL phase detector and its pre-filters compute from a *given* voltage signal; they
make no stability claim about any closed loop.

Model boundary.
Continuous time, ideal signals (no sampling, quantization, PWM, noise model, or measurement
delay). The PLL frame angle `θ̂` is an arbitrary real number here.

Conventions (shared by every `powerlib.PLL` module).
* A planar vector `Fin 2 → ℝ` has component `0` = α (resp. d) and `1` = β (resp. q).
* Park matrix `park θ = [[cos θ, sin θ], [−sin θ, cos θ]]` (αβ → dq) and
  `rot θ = park (−θ)` (dq → αβ) are those of `theorem/Transform/Park.lean`
  (work-sync `conventions.md` §4 / §D4). Amplitude-invariant Clarke `clarke`.
* Grid voltage: ideal balanced sinusoid of amplitude `V`, angle `θ_g`; phase voltages
  `v_x = V cos(θ_g + φ_x)`, `φ = (0, −2π/3, 2π/3)`. The PLL frame angle is `θ̂`.
  Phase error `θ̃ = θ̂ − θ_g` (swing sign, `conventions.md` §D5).
* Negative-sequence component of amplitude `A` and angle `α`: `A (cos α, −sin α)` in αβ.

Source: work-sync `theory/T-pll-dynamics.md` §1.2, §1.6, §1.7, §1.8, §1.9.

Results.
* Clarke of the balanced three-phase voltage, Park projection
  `V_dq = V (cos(θ_g − θ̂), sin(θ_g − θ̂))`, phase-detector characteristic `V_q = −V sin θ̃`,
  and the perturbation projection `V_q^p = −V sin θ_e + (−sin θ_e, cos θ_e)·(δv_d, δv_q)`
  (T-pll-dynamics §1.2), with `‖(−sin θ_e, cos θ_e)‖ = 1`.
* Unbalanced / harmonic voltage in the PLL frame (T-pll-dynamics §1.6), with a Correction.
* DDSRF cross-coupling (T-pll-dynamics §1.8, Rodríguez et al. 2007) and exact decoupling,
  with a Correction.
* SOGI quadrature generator (T-pll-dynamics §1.7) as a `Linear.Plant`: transfer functions,
  `H_d(jω′) = 1`, `H_q(jω′) = −j`, Hurwitz iff `k ω′ > 0 ∧ ω′ ≠ 0`; exact positive-sequence
  extraction of the DSOGI in the phasor domain.
* MAF (T-pll-dynamics §1.9): one-window moving average of a complex exponential is
  `H_maf(jω) e^{jωt}`; with window `T_w = 2π/ω_s` it annihilates every nonzero integer
  multiple of `ω_s`.

Family and connection conclusions.
None. This module defines no family and states no behaviour; every result is a signal identity,
a transfer function or a static matrix test.

Correction (§1.6): the note writes the negative-sequence contribution to `V_q` as
`V⁻ sin(2θ_g − θ̂_g + φ⁻)`; locked (`θ̂ = θ_g`) this has the fundamental frequency, which
contradicts the stated `2ω_s` ripple. The correct term is `−V⁻ sin(θ_g + θ̂_g + φ⁻)`
(`park_unbalanced_q`), which is `−V⁻ sin(2θ_g + φ⁻)` when locked; the note's formula is
refuted by `not_note_negSeq_formula`.

Correction (§1.8): the second (q) row of the note's undecoupled DDSRF equation has both
negative-sequence signs reversed. The correct relation is
`V^{++} = V⁺ + park(2θ̂) V⁻`, i.e. `V_q^{++} = V_q⁺ + cos(2θ̂) V_q⁻ − sin(2θ̂) V_d⁻`
(Rodríguez et al., IEEE TPEL 22(2), 2007, eq. (3)); the note's version is refuted by
`not_note_ddsrf_q_row`. The decoupling equation must be corrected in the same way.
-/

noncomputable section
namespace powerlib.PLL
open Matrix
open powerlib.Transform (park rot clarke)

/-! ## Balanced grid voltage and the SRF phase detector -/

/-- Balanced positive-sequence phase voltages `V cos(θ_g + φ_x)`, `φ = (0, −2π/3, 2π/3)`. -/
def balancedAbc (V θg : ℝ) : Fin 3 → ℝ :=
  ![V * Real.cos θg, V * Real.cos (θg - 2 * Real.pi / 3), V * Real.cos (θg + 2 * Real.pi / 3)]

/-- Grid voltage space vector `V (cos θ_g, sin θ_g)` in the stationary αβ frame. -/
def gridAlphaBeta (V θg : ℝ) : Fin 2 → ℝ := ![V * Real.cos θg, V * Real.sin θg]

/-- Amplitude-invariant Clarke maps the balanced phase voltages to `V (cos θ_g, sin θ_g)`. -/
@[powerlib_foundation] theorem clarke_balancedAbc (V θg : ℝ) :
    clarke *ᵥ balancedAbc V θg = gridAlphaBeta V θg := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]; ring
  have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_three]
  ext i; fin_cases i <;>
    simp [clarke, balancedAbc, gridAlphaBeta, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Real.cos_sub, Real.cos_add, hc, hs]
  · ring
  · linear_combination (1 / 3 : ℝ) * V * Real.sin θg * h3

/-- Park projection of the grid voltage onto the PLL frame `θ̂`:
`V_dq = V (cos(θ_g − θ̂), sin(θ_g − θ̂))` (T-pll-dynamics §1.2). -/
@[powerlib_foundation] theorem park_gridAlphaBeta (V θg θh : ℝ) :
    park θh *ᵥ gridAlphaBeta V θg =
      ![V * Real.cos (θg - θh), V * Real.sin (θg - θh)] := by
  ext i; fin_cases i <;> simp [gridAlphaBeta, Real.cos_sub, Real.sin_sub] <;> ring

/-- The SRF-PLL phase detector: the q-axis grid voltage in the PLL frame. -/
def phaseDetector (V θg θh : ℝ) : ℝ := (park θh *ᵥ gridAlphaBeta V θg) 1

/-- Phase-detector characteristic `V_q = −V sin θ̃`, `θ̃ = θ̂ − θ_g`. -/
@[simp, powerlib_foundation] theorem phaseDetector_eq (V θg θh : ℝ) :
    phaseDetector V θg θh = -(V * Real.sin (θh - θg)) := by
  rw [phaseDetector, park_gridAlphaBeta]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [show θg - θh = -(θh - θg) by ring, Real.sin_neg]; ring

/-- Projecting a grid-frame vector into the PLL frame: `park θ̂ · rot θ_g = park(θ̂ − θ_g)`. -/
@[powerlib_foundation] theorem park_rot_mulVec (θh θg : ℝ) (vg : Fin 2 → ℝ) :
    park θh *ᵥ (rot θg *ᵥ vg) = park (θh - θg) *ᵥ vg := by
  rw [Matrix.mulVec_mulVec, Transform.park_eq_rot_neg, Transform.park_eq_rot_neg,
    ← Transform.rot_add]
  congr 2; ring

/-- Perturbation projection (T-pll-dynamics §1.2, boxed): grid-frame voltage
`(V + δv_d, δv_q)` seen on the q axis of a PLL frame advanced by `θ_e`. -/
@[powerlib_foundation] theorem perturbed_q (V θe δd δq : ℝ) :
    (park θe *ᵥ ![V + δd, δq]) 1 =
      -(V * Real.sin θe) + (-(Real.sin θe) * δd + Real.cos θe * δq) := by
  simp; ring

/-- The bare noise-projection row `(−sin θ_e, cos θ_e)` has unit length. -/
@[powerlib_foundation] theorem noiseProjection_sq_sum (θe : ℝ) :
    (-(Real.sin θe)) ^ 2 + Real.cos θe ^ 2 = 1 := by
  rw [neg_sq]; exact Real.sin_sq_add_cos_sq θe

/-! ## Unbalanced and harmonic voltages in the PLL frame (T-pll-dynamics §1.6) -/

/-- Positive-sequence component `A (cos α, sin α)` (counter-clockwise rotation). -/
def posSeq (A α : ℝ) : Fin 2 → ℝ := ![A * Real.cos α, A * Real.sin α]

/-- Negative-sequence component `A (cos α, −sin α)` (clockwise rotation). -/
def negSeq (A α : ℝ) : Fin 2 → ℝ := ![A * Real.cos α, -(A * Real.sin α)]

@[powerlib_foundation] theorem park_posSeq_q (A α θh : ℝ) :
    (park θh *ᵥ posSeq A α) 1 = A * Real.sin (α - θh) := by
  simp [posSeq, Real.sin_sub]; ring

@[powerlib_foundation] theorem park_negSeq_q (A α θh : ℝ) :
    (park θh *ᵥ negSeq A α) 1 = -(A * Real.sin (α + θh)) := by
  simp [negSeq, Real.sin_add]; ring

/-- q-axis PLL-frame voltage of `V⁺` positive sequence at `θ_g` plus `V⁻` negative sequence
at `θ_g + φ⁻`: `V_q = −V⁺ sin θ̃ − V⁻ sin(θ_g + θ̂ + φ⁻)` (corrected §1.6). -/
@[powerlib_foundation] theorem park_unbalanced_q (Vp Vn θg θh φn : ℝ) :
    (park θh *ᵥ (posSeq Vp θg + negSeq Vn (θg + φn))) 1 =
      -(Vp * Real.sin (θh - θg)) - Vn * Real.sin (θg + θh + φn) := by
  rw [Matrix.mulVec_add, Pi.add_apply, park_posSeq_q, park_negSeq_q,
    show θg - θh = -(θh - θg) by ring, Real.sin_neg, show θg + φn + θh = θg + θh + φn by ring]
  ring

/-- Locked PLL (`θ̂ = θ_g`): the negative sequence produces a double-frequency `V_q` term. -/
@[powerlib_foundation] theorem park_unbalanced_q_locked (Vp Vn θg φn : ℝ) :
    (park θg *ᵥ (posSeq Vp θg + negSeq Vn (θg + φn))) 1 =
      -(Vn * Real.sin (2 * θg + φn)) := by
  rw [park_unbalanced_q]; ring_nf; simp

/-- Locked PLL: an `h`-th harmonic positive-sequence component gives a `(h − 1)θ_g` term. -/
@[powerlib_foundation] theorem park_posSeq_harmonic_locked (A h φ θg : ℝ) :
    (park θg *ᵥ posSeq A (h * θg + φ)) 1 = A * Real.sin ((h - 1) * θg + φ) := by
  rw [park_posSeq_q]; ring_nf

/-- Locked PLL: an `h`-th harmonic negative-sequence component gives a `(h + 1)θ_g` term. -/
@[powerlib_foundation] theorem park_negSeq_harmonic_locked (A h φ θg : ℝ) :
    (park θg *ᵥ negSeq A (h * θg + φ)) 1 = -(A * Real.sin ((h + 1) * θg + φ)) := by
  rw [park_negSeq_q]; ring_nf

/-- The note's negative-sequence term `V⁻ sin(2θ_g − θ̂ + φ⁻)` is not the q-axis voltage. -/
@[powerlib_foundation] theorem not_note_negSeq_formula {Vn : ℝ} (hVn : Vn ≠ 0) :
    ¬ ∀ θg θh φn : ℝ, (park θh *ᵥ negSeq Vn (θg + φn)) 1 =
      Vn * Real.sin (2 * θg - θh + φn) := by
  intro h
  have h0 := h 0 0 (Real.pi / 2)
  rw [park_negSeq_q] at h0
  simp at h0
  exact hVn (by linarith)

/-! ## DDSRF cross-coupling (T-pll-dynamics §1.8) -/

/-- Unbalanced αβ voltage: positive-sequence `V⁺_dq` in the `+θ̂` frame and
negative-sequence `V⁻_dq` in the `−θ̂` frame. -/
def unbalancedAlphaBeta (θh : ℝ) (Vp Vn : Fin 2 → ℝ) : Fin 2 → ℝ :=
  rot θh *ᵥ Vp + rot (-θh) *ᵥ Vn

/-- Positive-frame (`dq^{+1}`) components: `V^{++} = V⁺ + park(2θ̂) V⁻`
(Rodríguez et al. 2007, eq. (3)). -/
@[powerlib_foundation] theorem ddsrf_positiveFrame (θh : ℝ) (Vp Vn : Fin 2 → ℝ) :
    park θh *ᵥ unbalancedAlphaBeta θh Vp Vn = Vp + park (2 * θh) *ᵥ Vn := by
  rw [unbalancedAlphaBeta, Matrix.mulVec_add, Transform.park_mulVec_rot_mulVec,
    Matrix.mulVec_mulVec, Transform.park_eq_rot_neg θh, ← Transform.rot_add,
    Transform.park_eq_rot_neg (2 * θh)]
  congr 3; ring

/-- Componentwise form of `ddsrf_positiveFrame`. -/
@[powerlib_foundation] theorem ddsrf_positiveFrame_apply (θh : ℝ) (Vp Vn : Fin 2 → ℝ) :
    park θh *ᵥ unbalancedAlphaBeta θh Vp Vn =
      ![Vp 0 + Real.cos (2 * θh) * Vn 0 + Real.sin (2 * θh) * Vn 1,
        Vp 1 + Real.cos (2 * θh) * Vn 1 - Real.sin (2 * θh) * Vn 0] := by
  rw [ddsrf_positiveFrame]
  ext i; fin_cases i <;> simp <;> ring

/-- Negative-frame (`dq^{−1}`) components: `V^{−−} = V⁻ + rot(2θ̂) V⁺`. -/
@[powerlib_foundation] theorem ddsrf_negativeFrame (θh : ℝ) (Vp Vn : Fin 2 → ℝ) :
    park (-θh) *ᵥ unbalancedAlphaBeta θh Vp Vn = Vn + rot (2 * θh) *ᵥ Vp := by
  rw [unbalancedAlphaBeta, Matrix.mulVec_add, Transform.park_mulVec_rot_mulVec,
    Matrix.mulVec_mulVec, Transform.park_eq_rot_neg (-θh), ← Transform.rot_add, add_comm]
  congr 3; ring

/-- Exact DDSRF decoupling: subtracting `park(2θ̂)` of the negative-sequence estimate from the
positive-frame voltage leaves the true positive sequence when the estimate is exact. -/
@[powerlib_foundation] theorem ddsrf_decoupled (θh : ℝ) (Vp Vn : Fin 2 → ℝ) :
    park θh *ᵥ unbalancedAlphaBeta θh Vp Vn - park (2 * θh) *ᵥ Vn = Vp := by
  rw [ddsrf_positiveFrame, add_sub_cancel_right]

/-- Decoupling error with an estimate `V̄⁻`: the residual is `park(2θ̂)(V⁻ − V̄⁻)`. -/
@[powerlib_foundation] theorem ddsrf_decoupling_error (θh : ℝ) (Vp Vn Vnbar : Fin 2 → ℝ) :
    park θh *ᵥ unbalancedAlphaBeta θh Vp Vn - park (2 * θh) *ᵥ Vnbar =
      Vp + park (2 * θh) *ᵥ (Vn - Vnbar) := by
  rw [ddsrf_positiveFrame, Matrix.mulVec_sub]; abel

/-- The note's q row `V_q^{++} = V_q⁺ − cos(2θ̂) V_q⁻ + sin(2θ̂) V_d⁻` is false. -/
@[powerlib_foundation] theorem not_note_ddsrf_q_row :
    ¬ ∀ (θh : ℝ) (Vp Vn : Fin 2 → ℝ), (park θh *ᵥ unbalancedAlphaBeta θh Vp Vn) 1 =
      Vp 1 - Real.cos (2 * θh) * Vn 1 + Real.sin (2 * θh) * Vn 0 := by
  intro h
  have h0 := h 0 0 ![0, 1]
  rw [ddsrf_positiveFrame_apply] at h0
  norm_num at h0

/-! ## SOGI quadrature signal generator (T-pll-dynamics §1.7) -/

/-- SOGI state matrix, states `(v′, qv′)`:
`v̇′ = k ω′ (v − v′) − ω′ qv′`, `q̇v′ = ω′ v′`. -/
def sogiA (k ω' : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-(k * ω'), -ω'; ω', 0]

/-- SOGI with output `v′` (in-phase, band-pass). -/
def sogiD (k ω' : ℝ) : Linear.Plant 2 1 :=
  ⟨sogiA k ω', !![k * ω'; 0], !![1, 0], 0⟩

/-- SOGI with output `qv′` (quadrature, low-pass). -/
def sogiQ (k ω' : ℝ) : Linear.Plant 2 1 :=
  ⟨sogiA k ω', !![k * ω'; 0], !![0, 1], 0⟩

/-- SOGI denominator `s² + k ω′ s + ω′²`. -/
def sogiDen (k ω' : ℝ) (s : ℂ) : ℂ := s ^ 2 + (k : ℂ) * ω' * s + (ω' : ℂ) ^ 2

@[powerlib_foundation] theorem characteristicMatrix_sogiA (k ω' : ℝ) (s : ℂ) :
    Linear.characteristicMatrix (sogiA k ω') s = !![s + k * ω', (ω' : ℂ); -(ω' : ℂ), s] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Linear.characteristicMatrix, sogiA]

@[powerlib_foundation] theorem det_characteristicMatrix_sogiA (k ω' : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (sogiA k ω') s).det = sogiDen k ω' s := by
  rw [characteristicMatrix_sogiA, det_fin_two_of, sogiDen]; ring

/-- `H_d(s) = k ω′ s / (s² + k ω′ s + ω′²)` (division by zero gives `0` on both sides). -/
@[powerlib_foundation] theorem transfer_sogiD (k ω' : ℝ) (s : ℂ) :
    Linear.transfer (sogiD k ω') s = !![(k : ℂ) * ω' * s / sogiDen k ω' s] := by
  rw [Linear.transfer_eq_adjugate, show (sogiD k ω').A = sogiA k ω' from rfl,
    det_characteristicMatrix_sogiA, characteristicMatrix_sogiA, adjugate_fin_two_of]
  ext i j; fin_cases i; fin_cases j
  simp [sogiD, Linear.complexify, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `H_q(s) = k ω′² / (s² + k ω′ s + ω′²)`. -/
@[powerlib_foundation] theorem transfer_sogiQ (k ω' : ℝ) (s : ℂ) :
    Linear.transfer (sogiQ k ω') s = !![(k : ℂ) * (ω' : ℂ) ^ 2 / sogiDen k ω' s] := by
  rw [Linear.transfer_eq_adjugate, show (sogiQ k ω').A = sogiA k ω' from rfl,
    det_characteristicMatrix_sogiA, characteristicMatrix_sogiA, adjugate_fin_two_of]
  ext i j; fin_cases i; fin_cases j
  simp [sogiQ, Linear.complexify, Matrix.mul_apply, Fin.sum_univ_two]
  ring

@[powerlib_foundation] private lemma sogiDen_center {k ω' : ℝ} :
    sogiDen k ω' ((ω' : ℂ) * Complex.I) = Complex.I * k * (ω' : ℂ) ^ 2 := by
  rw [sogiDen]; ring_nf; rw [Complex.I_sq]; ring

/-- Sinusoidal steady state at the centre frequency: `H_d(jω′) = 1` (unit gain, zero phase). -/
@[powerlib_foundation] theorem transfer_sogiD_center {k ω' : ℝ} (hk : k ≠ 0) (hω : ω' ≠ 0) :
    Linear.transfer (sogiD k ω') ((ω' : ℂ) * Complex.I) = !![1] := by
  rw [transfer_sogiD, sogiDen_center]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hω' : (ω' : ℂ) ≠ 0 := by exact_mod_cast hω
  congr 1
  field_simp

/-- Sinusoidal steady state at the centre frequency: `H_q(jω′) = −j` (90° lag). -/
@[powerlib_foundation] theorem transfer_sogiQ_center {k ω' : ℝ} (hk : k ≠ 0) (hω : ω' ≠ 0) :
    Linear.transfer (sogiQ k ω') ((ω' : ℂ) * Complex.I) = !![-Complex.I] := by
  rw [transfer_sogiQ, sogiDen_center]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hω' : (ω' : ℂ) ≠ 0 := by exact_mod_cast hω
  congr 1
  field_simp
  rw [one_div, Complex.inv_I]

/-- The SOGI internal dynamics are Hurwitz iff `k ω′ > 0` and `ω′ ≠ 0`. -/
@[powerlib_foundation] theorem isHurwitz_sogiA_iff (k ω' : ℝ) :
    LinearSystems.IsHurwitz (sogiA k ω') ↔ 0 < k * ω' ∧ ω' ≠ 0 := by
  rw [sogiA, Criteria.isHurwitz_fin_two_of_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, fun h => ?_⟩
    rw [h] at h2; simp at h2
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by nlinarith [sq_pos_of_ne_zero h2]⟩

/-- DSOGI positive-sequence extraction in the phasor domain at the centre frequency:
with `qv′ = −j v′`, `v_α⁺ = ½(v′_α − q v′_β)` recovers the positive-sequence phasor `P`
exactly and rejects the negative-sequence phasor `N`
(`V_α = P + N`, `V_β = −jP + jN`). -/
@[powerlib_foundation] theorem dsogi_positive_extraction (P N : ℂ) :
    (1 / 2 : ℂ) * ((P + N) - (-Complex.I) * (-Complex.I * P + Complex.I * N)) = P ∧
      (1 / 2 : ℂ) * ((-Complex.I) * (P + N) + (-Complex.I * P + Complex.I * N)) =
        -Complex.I * P := by
  constructor
  · ring_nf; rw [Complex.I_sq]; ring
  · ring

/-! ## MAF: one-window moving average (T-pll-dynamics §1.9) -/

/-- `H_maf(s) = (1 − e^{−T_w s}) / (T_w s)`. -/
def mafTF (Tw : ℝ) (s : ℂ) : ℂ := (1 - Complex.exp (-((Tw : ℂ) * s))) / ((Tw : ℂ) * s)

/-- The window average of a complex exponential input `e^{jωτ}` over `[t − T_w, t]` is
`H_maf(jω) e^{jωt}`: the moving-average operator acts on this signal as `H_maf`. -/
@[powerlib_foundation] theorem movingAverage_exp {Tw ω : ℝ} (hT : Tw ≠ 0) (hω : ω ≠ 0) (t : ℝ) :
    (1 / (Tw : ℂ)) * ∫ τ in (t - Tw)..t, Complex.exp (((ω : ℂ) * Complex.I) * τ) =
      mafTF Tw ((ω : ℂ) * Complex.I) * Complex.exp (((ω : ℂ) * Complex.I) * t) := by
  have hc : (ω : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hω) Complex.I_ne_zero
  have hT' : (Tw : ℂ) ≠ 0 := by exact_mod_cast hT
  rw [integral_exp_mul_complex hc, mafTF]
  have hsplit : Complex.exp ((ω : ℂ) * Complex.I * ((t - Tw : ℝ) : ℂ)) =
      Complex.exp ((ω : ℂ) * Complex.I * t) *
        Complex.exp (-((Tw : ℂ) * ((ω : ℂ) * Complex.I))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hsplit]
  field_simp

/-- With window `T_w = 2π/ω_s` the MAF gain vanishes at every nonzero integer multiple
`n ω_s` (`T-pll-dynamics` §1.9). -/
@[powerlib_foundation] theorem mafTF_harmonic_eq_zero {ωs : ℝ} (hω : ωs ≠ 0) {n : ℤ}
    (hn : n ≠ 0) : mafTF (2 * Real.pi / ωs) ((n : ℂ) * ωs * Complex.I) = 0 := by
  rw [mafTF]
  have h1 : Complex.exp (-(((2 * Real.pi / ωs : ℝ) : ℂ) * ((n : ℂ) * ωs * Complex.I))) = 1 := by
    have hω' : (ωs : ℂ) ≠ 0 := by exact_mod_cast hω
    have : -(((2 * Real.pi / ωs : ℝ) : ℂ) * ((n : ℂ) * ωs * Complex.I)) =
        ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [h1, sub_self, zero_div]

/-- Semantic form: the one-period moving average of the harmonic `e^{j n ω_s τ}` is zero. -/
@[powerlib_foundation] theorem movingAverage_harmonic_eq_zero {ωs : ℝ} (hω : ωs ≠ 0) {n : ℤ}
    (hn : n ≠ 0) (t : ℝ) :
    ∫ τ in (t - 2 * Real.pi / ωs)..t,
      Complex.exp (((n * ωs : ℝ) : ℂ) * Complex.I * τ) = 0 := by
  have hT : 2 * Real.pi / ωs ≠ 0 := div_ne_zero (by positivity) hω
  have hnω : (n : ℝ) * ωs ≠ 0 := mul_ne_zero (by exact_mod_cast hn) hω
  have h := movingAverage_exp hT hnω t
  have hz : mafTF (2 * Real.pi / ωs) (((n * ωs : ℝ) : ℂ) * Complex.I) = 0 := by
    have := mafTF_harmonic_eq_zero hω hn
    simpa [mul_assoc] using this
  rw [hz, zero_mul] at h
  have hT' : (1 / ((2 * Real.pi / ωs : ℝ) : ℂ)) ≠ 0 := by
    simp only [one_div, ne_eq, inv_eq_zero]; exact_mod_cast hT
  exact (mul_eq_zero.mp h).resolve_left hT'

end powerlib.PLL
