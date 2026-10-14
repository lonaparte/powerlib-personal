import theorem.PLL.Linear
import theorem.LTI.Plant

/-! # Frequency measurement by SRF-PLL: bandwidth, phase, ROCOF

Exact frequency-response identities of the linearized SRF-PLL used as a frequency meter. The PMU
window estimator and the ROCOF trip probability are in `theorem/Frequency/Measurement.lean`.

Model boundary.
* System: the formalized linearized SRF-PLL of `theorem/PLL/Linear.lean` (`frequencyModel`,
  transfer `H(s) = (a s + b)/(s² + a s + b)`, `a = V K_p`, `b = V K_i`; with `V = 1` this is
  T-frequency-measurement §1.1's `(K_p s + K_i)/(s² + K_p s + K_i)`), with the boundary stated
  there (locked operating point, no pre-filter, sampling, delay or PWM; continuous time).

Source: work-sync `theory/T-frequency-measurement.md` §1.1–§1.5.

Results.
* −3 dB bandwidth: for `V K_i > 0`, on `ω ≥ 0`, `|H(jω)|² = 1/2` holds exactly at
  `ω_b = ω_n √(1 + 2ζ² + √((1 + 2ζ²)² + 1))` (`ω_n = √(V K_i)`, `ζ = V K_p/(2ω_n)`), with
  `|H|² > 1/2` below and `< 1/2` above (`V K_p ≠ 0`).
* Phase: `arg H(jω) = −arctan(a ω³ / (ω_n²(ω_n² − ω²) + a² ω²))` whenever the denominator is
  positive, in particular for every `ω` when `ζ ≥ 1/2`.
* ROCOF: the derivative-output realization `LTI.derivModel` `(A, B, C A, C B)` of a strictly
  proper model has transfer `s H(s)` and its output is the time derivative of the original
  output (`theorem/LTI/Plant.lean`); for the PLL `rocofModel` has transfer `s H(s)` and
  `|s H(jω)|² = ω² |H(jω)|²` (noise PSD amplified by `ω²`).

Family and connection conclusions.
No family and no connection conclusion: every result is a frequency-response identity, not a
behaviour of a family's models. The stability of these models is in `theorem/PLL/Linear.lean`
(`LinearPLL.family`).

Correction (§1.1 bandwidth): the note gives `ω_b ≈ 2ω_n √(1 − 2ζ² + √(4ζ⁴ − 4ζ² + 2))`
(the formula of a pure second-order low-pass `ω_n²/(s² + 2ζω_n s + ω_n²)`, with an extra
factor 2). For the PLL closed loop `H = (2ζω_n s + ω_n²)/(s² + 2ζω_n s + ω_n²)` the exact
−3 dB frequency is `ω_n √(1 + 2ζ² + √((1 + 2ζ²)² + 1))`; at `ζ = 1/√2` the note's formula
gives `2ω_n`, which is not a −3 dB point (`not_note_bandwidth`).

Correction (§1.2 phase): the note's `∠H(jω) = arctan(ω(ω_n² − ω²)/(K_p ω_n²))` is wrong; the
correct phase is `−arctan(K_p ω³/(ω_n²(ω_n² − ω²) + K_p² ω²))` (`V = 1`). E.g. the note's
formula vanishes at `ω = ω_n`, while the true phase there is `−arctan(ω_n/K_p) ≠ 0`
(`arg_closedLoopTF_omegaN_ne_zero`). The note's numerical values (7° lag and 25 ms group delay
at 1 Hz for `ω_n = 30`, `ζ = 0.7`) are therefore not reproduced; the corrected formula gives
about 0.71° (computed outside Lean, not a kernel-checked claim).
-/

noncomputable section
namespace powerlib.PLL
open Matrix Complex
open powerlib.LTI (derivModel)

/-! ## Magnitude and the −3 dB bandwidth -/

/-- `|H(jω)|² = (b² + a²ω²)/((b − ω²)² + a²ω²)`, `a = V K_p`, `b = V K_i`. -/
@[powerlib_foundation] theorem normSq_closedLoopTF (V Kp Ki ω : ℝ) :
    normSq (closedLoopTF V Kp Ki ((ω : ℂ) * I)) =
      ((V * Ki) ^ 2 + (V * Kp * ω) ^ 2) / ((V * Ki - ω ^ 2) ^ 2 + (V * Kp * ω) ^ 2) := by
  have hden : loopPoly V Kp Ki ((ω : ℂ) * I) = ⟨V * Ki - ω ^ 2, V * Kp * ω⟩ := by
    apply Complex.ext <;> simp [loopPoly, pow_two]
    ring
  have hnum : (V : ℂ) * Kp * ((ω : ℂ) * I) + (V : ℂ) * Ki = ⟨V * Ki, V * Kp * ω⟩ := by
    apply Complex.ext <;> simp
  rw [closedLoopTF, hden, hnum, Complex.normSq_div, Complex.normSq_mk, Complex.normSq_mk]
  ring

/-- The exact −3 dB bandwidth `ω_n √(1 + 2ζ² + √((1 + 2ζ²)² + 1))`. -/
def bandwidth (ωn ζ : ℝ) : ℝ :=
  ωn * Real.sqrt (1 + 2 * ζ ^ 2 + Real.sqrt ((1 + 2 * ζ ^ 2) ^ 2 + 1))

@[powerlib_foundation] private lemma bandwidth_sq_root {V Kp Ki : ℝ} (h : 0 < V * Ki) :
    0 < bandwidth (omegaN V Ki) (zeta V Kp Ki) ^ 2 ∧
      (bandwidth (omegaN V Ki) (zeta V Kp Ki) ^ 2) ^ 2 -
        (2 * (V * Ki) + (V * Kp) ^ 2) * bandwidth (omegaN V Ki) (zeta V Kp Ki) ^ 2 -
        (V * Ki) ^ 2 = 0 := by
  set X := bandwidth (omegaN V Ki) (zeta V Kp Ki) ^ 2 with hXdef
  have hω : 0 < omegaN V Ki := Real.sqrt_pos.mpr h
  have hsq : omegaN V Ki ^ 2 = V * Ki := Real.sq_sqrt h.le
  have ha : V * Kp = 2 * zeta V Kp Ki * omegaN V Ki := by rw [zeta]; field_simp
  set ζ := zeta V Kp Ki
  set ωn := omegaN V Ki
  set r := Real.sqrt ((1 + 2 * ζ ^ 2) ^ 2 + 1) with hr
  have hr2 : r ^ 2 = (1 + 2 * ζ ^ 2) ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hin : 0 < 1 + 2 * ζ ^ 2 + r := by positivity
  have hX : X = ωn ^ 2 * (1 + 2 * ζ ^ 2 + r) := by
    rw [hXdef, bandwidth, mul_pow, Real.sq_sqrt hin.le]
  refine ⟨by rw [hX]; positivity, ?_⟩
  rw [hX, ← hsq, ha]
  linear_combination ωn ^ 4 * hr2

/-- Factorization of the −3 dB condition: `2|N|² − |D|² = −(ω² − X)(ω² + b²/X)`. -/
@[powerlib_foundation] private lemma bandwidth_factor {V Kp Ki : ℝ} (h : 0 < V * Ki) (ω : ℝ) :
    2 * ((V * Ki) ^ 2 + (V * Kp * ω) ^ 2) - ((V * Ki - ω ^ 2) ^ 2 + (V * Kp * ω) ^ 2) =
      -((ω ^ 2 - bandwidth (omegaN V Ki) (zeta V Kp Ki) ^ 2) *
        (ω ^ 2 + (V * Ki) ^ 2 / bandwidth (omegaN V Ki) (zeta V Kp Ki) ^ 2)) := by
  obtain ⟨hX, hroot⟩ := bandwidth_sq_root (Kp := Kp) h
  generalize bandwidth (omegaN V Ki) (zeta V Kp Ki) ^ 2 = X at hX hroot ⊢
  have hdiv : (V * Ki) ^ 2 / X = X - (2 * (V * Ki) + (V * Kp) ^ 2) := by
    rw [div_eq_iff hX.ne']; linear_combination (-1 : ℝ) * hroot
  rw [hdiv]
  linear_combination (-1 : ℝ) * hroot

@[powerlib_foundation] private lemma closedLoop_den_pos_or {V Kp Ki : ℝ} (h : 0 < V * Ki) (ω : ℝ) :
    0 < (V * Ki - ω ^ 2) ^ 2 + (V * Kp * ω) ^ 2 ∨
      ((V * Ki - ω ^ 2) ^ 2 + (V * Kp * ω) ^ 2 = 0 ∧ ω ^ 2 = V * Ki ∧ V * Kp = 0) := by
  rcases (add_nonneg (sq_nonneg (V * Ki - ω ^ 2)) (sq_nonneg (V * Kp * ω))).lt_or_eq with hp | h0
  · exact Or.inl hp
  · right
    have h1 : (V * Ki - ω ^ 2) ^ 2 = 0 := by nlinarith [sq_nonneg (V * Ki - ω ^ 2), sq_nonneg (V * Kp * ω)]
    have h2 : (V * Kp * ω) ^ 2 = 0 := by nlinarith [sq_nonneg (V * Ki - ω ^ 2), sq_nonneg (V * Kp * ω)]
    have h1' : V * Ki - ω ^ 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h1
    have hω2 : ω ^ 2 = V * Ki := by linarith
    have hω : ω ≠ 0 := by
      rintro rfl
      have : (0 : ℝ) ^ 2 = 0 := by norm_num
      linarith
    have : V * Kp * ω = 0 := pow_eq_zero_iff two_ne_zero |>.mp h2
    exact ⟨h0.symm, hω2, (mul_eq_zero.mp this).resolve_right hω⟩

/-- −3 dB bandwidth: for `V K_i > 0` and `ω ≥ 0`, `|H(jω)|² = 1/2 ⇔ ω = ω_b`. -/
@[powerlib_foundation] theorem normSq_closedLoopTF_eq_half_iff {V Kp Ki : ℝ} (h : 0 < V * Ki)
    {ω : ℝ} (hω : 0 ≤ ω) :
    normSq (closedLoopTF V Kp Ki ((ω : ℂ) * I)) = 1 / 2 ↔
      ω = bandwidth (omegaN V Ki) (zeta V Kp Ki) := by
  obtain ⟨hX, hroot⟩ := bandwidth_sq_root (Kp := Kp) h
  have hb0 : 0 ≤ bandwidth (omegaN V Ki) (zeta V Kp Ki) := by
    unfold bandwidth omegaN; positivity
  have hfac := bandwidth_factor (Kp := Kp) h ω
  set X := bandwidth (omegaN V Ki) (zeta V Kp Ki) ^ 2
  have hpos : 0 < ω ^ 2 + (V * Ki) ^ 2 / X := by positivity
  rw [normSq_closedLoopTF]
  rcases closedLoop_den_pos_or (Kp := Kp) h ω with hD | ⟨hD, hω2, ha⟩
  · rw [div_eq_iff hD.ne']
    constructor
    · intro he
      have : (ω ^ 2 - X) * (ω ^ 2 + (V * Ki) ^ 2 / X) = 0 := by linarith
      have hx : ω ^ 2 = X := by
        have := (mul_eq_zero.mp this).resolve_right hpos.ne'
        linarith
      exact (pow_left_inj₀ hω hb0 two_ne_zero).mp hx
    · intro he
      have hx : ω ^ 2 = X := by rw [he]
      have h0 : 2 * ((V * Ki) ^ 2 + (V * Kp * ω) ^ 2) -
          ((V * Ki - ω ^ 2) ^ 2 + (V * Kp * ω) ^ 2) = 0 := by
        rw [hfac, hx, sub_self, zero_mul, neg_zero]
      linarith
  · rw [hD, div_zero]
    constructor
    · intro h0; norm_num at h0
    · intro he
      exfalso
      have hx : ω ^ 2 = X := by rw [he]
      have hXb : X = V * Ki := by rw [← hx, hω2]
      rw [hXb, ha] at hroot
      nlinarith

/-- Inside the bandwidth `|H(jω)|² > 1/2`; outside `|H(jω)|² < 1/2` (`V K_i > 0`, `V K_p ≠ 0`). -/
@[powerlib_foundation] theorem normSq_closedLoopTF_cmp_half {V Kp Ki : ℝ} (h : 0 < V * Ki)
    (ha : V * Kp ≠ 0) {ω : ℝ} (hω : 0 ≤ ω) :
    (ω < bandwidth (omegaN V Ki) (zeta V Kp Ki) →
      1 / 2 < normSq (closedLoopTF V Kp Ki ((ω : ℂ) * I))) ∧
    (bandwidth (omegaN V Ki) (zeta V Kp Ki) < ω →
      normSq (closedLoopTF V Kp Ki ((ω : ℂ) * I)) < 1 / 2) := by
  obtain ⟨hX, -⟩ := bandwidth_sq_root (Kp := Kp) h
  have hfac := bandwidth_factor (Kp := Kp) h ω
  set X := bandwidth (omegaN V Ki) (zeta V Kp Ki) ^ 2
  have hpos : 0 < ω ^ 2 + (V * Ki) ^ 2 / X := by positivity
  have hD : 0 < (V * Ki - ω ^ 2) ^ 2 + (V * Kp * ω) ^ 2 := by
    rcases closedLoop_den_pos_or (Kp := Kp) h ω with hD | ⟨-, -, h0⟩
    · exact hD
    · exact absurd h0 ha
  rw [normSq_closedLoopTF]
  constructor
  · intro hlt
    rw [lt_div_iff₀ hD]
    have : ω ^ 2 < X := by
      have := pow_lt_pow_left₀ hlt hω two_ne_zero
      simpa [X] using this
    nlinarith
  · intro hlt
    rw [div_lt_iff₀ hD]
    have : X < ω ^ 2 := by
      have hb0 : 0 ≤ bandwidth (omegaN V Ki) (zeta V Kp Ki) := by
        unfold bandwidth omegaN; positivity
      have := pow_lt_pow_left₀ hlt hb0 two_ne_zero
      simpa [X] using this
    nlinarith

/-- The same −3 dB characterization for the transfer function of `frequencyModel`, in
amplitude form `|H(jω)| = 1/√2`. -/
@[powerlib_foundation] theorem frequencyModel_bandwidth {V Kp Ki : ℝ} (h : 0 < V * Ki) {ω : ℝ}
    (hω : 0 ≤ ω) :
    ‖Linear.transfer (frequencyModel V Kp Ki) ((ω : ℂ) * I) 0 0‖ = 1 / Real.sqrt 2 ↔
      ω = bandwidth (omegaN V Ki) (zeta V Kp Ki) := by
  rw [← normSq_closedLoopTF_eq_half_iff h hω, transfer_frequencyModel]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro he; rw [he, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  · intro he
    have h2 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    rw [← h2] at he
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp he

/-- The note's bandwidth `2ω_n √(1 − 2ζ² + √(4ζ⁴ − 4ζ² + 2))` equals `2ω_n` at `ζ = 1/√2`, and
`2ω_n` is not a −3 dB frequency of the PLL closed loop with `ζ = 1/√2`. -/
@[powerlib_foundation] theorem not_note_bandwidth {V Kp Ki : ℝ} (h : 0 < V * Ki)
    (hζ : zeta V Kp Ki = 1 / Real.sqrt 2) :
    2 * omegaN V Ki * Real.sqrt (1 - 2 * zeta V Kp Ki ^ 2 +
        Real.sqrt (4 * zeta V Kp Ki ^ 4 - 4 * zeta V Kp Ki ^ 2 + 2)) = 2 * omegaN V Ki ∧
      normSq (closedLoopTF V Kp Ki (((2 * omegaN V Ki : ℝ) : ℂ) * I)) ≠ 1 / 2 := by
  have hω : 0 < omegaN V Ki := Real.sqrt_pos.mpr h
  have hz2 : zeta V Kp Ki ^ 2 = 1 / 2 := by
    rw [hζ, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hz4 : zeta V Kp Ki ^ 4 = 1 / 4 := by
    rw [show zeta V Kp Ki ^ 4 = (zeta V Kp Ki ^ 2) ^ 2 by ring, hz2]; norm_num
  refine ⟨?_, ?_⟩
  · rw [hz2, hz4]; norm_num
  · rw [ne_eq, normSq_closedLoopTF_eq_half_iff h (by positivity), bandwidth, hz2]
    intro he
    have h1 : Real.sqrt (1 + 2 * (1 / 2) + Real.sqrt ((1 + 2 * (1 / 2)) ^ 2 + 1)) = 2 :=
      (mul_left_cancel₀ hω.ne' (by linarith :
        omegaN V Ki * Real.sqrt (1 + 2 * (1 / 2) + Real.sqrt ((1 + 2 * (1 / 2)) ^ 2 + 1)) =
          omegaN V Ki * 2))
    have h2 : (1 : ℝ) + 2 * (1 / 2) + Real.sqrt ((1 + 2 * (1 / 2)) ^ 2 + 1) =
        2 + Real.sqrt 5 := by norm_num
    rw [h2] at h1
    have h3 : Real.sqrt (2 + Real.sqrt 5) ^ 2 = 2 ^ 2 := by rw [h1]
    rw [Real.sq_sqrt (by positivity)] at h3
    have h5 : Real.sqrt 5 = 2 := by linarith
    have h6 : Real.sqrt 5 ^ 2 = 2 ^ 2 := by rw [h5]
    rw [Real.sq_sqrt (by norm_num)] at h6
    norm_num at h6

/-! ## Phase -/

/-- `H(jω) = |den|⁻² (D(ω) − j a ω³)` with `D(ω) = b(b − ω²) + a²ω²`. -/
@[powerlib_foundation] theorem closedLoopTF_eq (V Kp Ki ω : ℝ) :
    closedLoopTF V Kp Ki ((ω : ℂ) * I) =
      (((V * Ki - ω ^ 2) ^ 2 + (V * Kp * ω) ^ 2)⁻¹ : ℝ) *
        ⟨V * Ki * (V * Ki - ω ^ 2) + (V * Kp) ^ 2 * ω ^ 2, -(V * Kp * ω ^ 3)⟩ := by
  have hden : loopPoly V Kp Ki ((ω : ℂ) * I) = ⟨V * Ki - ω ^ 2, V * Kp * ω⟩ := by
    apply Complex.ext <;> simp [loopPoly, pow_two]
    ring
  have hnum : (V : ℂ) * Kp * ((ω : ℂ) * I) + (V : ℂ) * Ki = ⟨V * Ki, V * Kp * ω⟩ := by
    apply Complex.ext <;> simp
  rw [closedLoopTF, hden, hnum]
  apply Complex.ext
  · rw [Complex.div_re, Complex.normSq_mk]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← add_div]
    field_simp
  · rw [Complex.div_im, Complex.normSq_mk]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [← sub_div]
    field_simp
    ring

@[powerlib_foundation] private lemma arg_of_re_pos_eq_arctan {z : ℂ} (hz : 0 < z.re) :
    arg z = Real.arctan (z.im / z.re) := by
  have habs : |arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [← Complex.tan_arg, Real.arctan_tan (by linarith [neg_abs_le (arg z)]) (lt_of_abs_lt habs)]

/-- Phase of the PLL closed loop: `arg H(jω) = −arctan(a ω³/(b(b − ω²) + a²ω²))` whenever the
denominator is positive (`a = V K_p`, `b = ω_n² = V K_i`). -/
@[powerlib_foundation] theorem arg_closedLoopTF {V Kp Ki ω : ℝ}
    (hD : 0 < V * Ki * (V * Ki - ω ^ 2) + (V * Kp) ^ 2 * ω ^ 2) :
    arg (closedLoopTF V Kp Ki ((ω : ℂ) * I)) =
      -Real.arctan (V * Kp * ω ^ 3 / (V * Ki * (V * Ki - ω ^ 2) + (V * Kp) ^ 2 * ω ^ 2)) := by
  have hden : 0 < (V * Ki - ω ^ 2) ^ 2 + (V * Kp * ω) ^ 2 := by
    rcases (add_nonneg (sq_nonneg (V * Ki - ω ^ 2)) (sq_nonneg (V * Kp * ω))).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 : V * Ki - ω ^ 2 = 0 := by nlinarith [sq_nonneg (V * Ki - ω ^ 2), sq_nonneg (V * Kp * ω)]
      have h2 : V * Kp * ω = 0 := by nlinarith [sq_nonneg (V * Ki - ω ^ 2), sq_nonneg (V * Kp * ω)]
      have : V * Ki * (V * Ki - ω ^ 2) + (V * Kp) ^ 2 * ω ^ 2 = 0 := by
        rw [h1, show (V * Kp) ^ 2 * ω ^ 2 = (V * Kp * ω) ^ 2 by ring, h2]; ring
      linarith
  rw [closedLoopTF_eq, Complex.arg_real_mul _ (inv_pos.mpr hden), arg_of_re_pos_eq_arctan hD]
  rw [neg_div, Real.arctan_neg]

/-- With `ζ ≥ 1/2` (`K_i ≤ V K_p²`, `V, K_i > 0`) the phase formula holds at every `ω`. -/
@[powerlib_foundation] theorem arg_closedLoopTF_of_half_le_zeta {V Kp Ki : ℝ} (hV : 0 < V)
    (hKi : 0 < Ki) (hK : Ki ≤ V * Kp ^ 2) (ω : ℝ) :
    arg (closedLoopTF V Kp Ki ((ω : ℂ) * I)) =
      -Real.arctan (V * Kp * ω ^ 3 / (V * Ki * (V * Ki - ω ^ 2) + (V * Kp) ^ 2 * ω ^ 2)) := by
  apply arg_closedLoopTF
  have h1 : 0 < (V * Ki) ^ 2 := by positivity
  have h2 : 0 ≤ ω ^ 2 * (V * (V * Kp ^ 2 - Ki)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg hV.le (by linarith))
  nlinarith

/-- At `ω = ω_n` the phase is `−arctan(ω_n / (V K_p)) ≠ 0` (`V K_p > 0`, `V K_i > 0`), whereas
the note's formula `arctan(ω(ω_n² − ω²)/(K_p ω_n²))` vanishes there. -/
@[powerlib_foundation] theorem arg_closedLoopTF_omegaN_ne_zero {V Kp Ki : ℝ} (ha : 0 < V * Kp)
    (h : 0 < V * Ki) : arg (closedLoopTF V Kp Ki ((omegaN V Ki : ℂ) * I)) ≠ 0 := by
  have hω : 0 < omegaN V Ki := Real.sqrt_pos.mpr h
  have hsq : omegaN V Ki ^ 2 = V * Ki := Real.sq_sqrt h.le
  have hD : 0 < V * Ki * (V * Ki - omegaN V Ki ^ 2) + (V * Kp) ^ 2 * omegaN V Ki ^ 2 := by
    rw [hsq, sub_self, mul_zero, zero_add]; positivity
  rw [arg_closedLoopTF hD, neg_ne_zero]
  apply ne_of_gt
  rw [Real.arctan_pos]
  positivity

/-! ## ROCOF estimation: derivative output -/

/-- ROCOF estimate of the PLL: output `d/dt Δω̂`. -/
def rocofModel (V Kp Ki : ℝ) : Linear.Plant 2 1 := derivModel (frequencyModel V Kp Ki)

/-- `ROCOF(s)/ω_g(s) = s H_pll(s)`. -/
@[powerlib_foundation] theorem transfer_rocofModel {V Kp Ki : ℝ} {s : ℂ}
    (hs : loopPoly V Kp Ki s ≠ 0) :
    Linear.transfer (rocofModel V Kp Ki) s = !![s * closedLoopTF V Kp Ki s] := by
  rw [rocofModel, LTI.transfer_derivModel rfl (by rwa [show (frequencyModel V Kp Ki).A =
    linA V Kp Ki from rfl, det_characteristicMatrix_linA]), transfer_frequencyModel]
  ext i j; fin_cases i; fin_cases j; simp

/-- Noise amplification of differentiation: `|jω H(jω)|² = ω² |H(jω)|²`. -/
@[powerlib_foundation] theorem normSq_rocof (V Kp Ki ω : ℝ) :
    normSq (((ω : ℂ) * I) * closedLoopTF V Kp Ki ((ω : ℂ) * I)) =
      ω ^ 2 * normSq (closedLoopTF V Kp Ki ((ω : ℂ) * I)) := by
  rw [Complex.normSq_mul]
  congr 1
  simp [Complex.normSq_apply]; ring

end powerlib.PLL
