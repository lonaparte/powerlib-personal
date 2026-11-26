import theorem.Criteria.Hurwitz2

/-! # Natural frequency, damping ratio and damped frequency of an eigenvalue

The modal frequency data of a complex eigenvalue `λ = −α + jω_d`: natural frequency
`ω_n = |λ|`, damping ratio `ζ = −Re λ / |λ|`, damped frequency `ω_d = Im λ`, their Hz versions,
the standard quadratic `(s − λ)(s − λ̄) = s² + 2ζω_n s + ω_n²`, the polar forms
`λ = ω_n(−ζ + j√(1 − ζ²)) = ω_n e^{j(π/2 + arcsin ζ)}`, and the bridge to the damping ratio and
natural frequency of a real `2 × 2` matrix.

Scope.
* An arbitrary complex number `λ` (in applications an eigenvalue of a complexified real state
  matrix). No hypothesis is built into the definitions: at `λ = 0` the damping ratio is `0`
  (Lean's `x / 0 = 0`), and every statement says which hypotheses it needs (`λ ≠ 0`,
  `0 ≤ Im λ`, …).
* The damping ratio is signed: `ζ < 0` for an eigenvalue in the open right half-plane. It is a
  fraction, not a percentage; the report's percentage is `100 ζ`.
* The bridge statements concern a real `2 × 2` matrix `A` and a non-real root of
  `det(sI − A)` (`Linear.characteristicMatrix`); `Criteria.dampingRatio A` and
  `Criteria.naturalFrequency A` are those of `theorem/Criteria/Hurwitz2.lean`. No model family.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §2.1.1, eqs. (2-4)–(2-6)
(`λ_r = −α_r + jω_dr`, `ω_nr = |λ_r|`, `f_dr = ω_dr/2π`, `f_nr = √(α_r² + ω_dr²)/2π`,
`ζ_r = α_r/√(α_r² + ω_dr²)`), and §2.2.1–§2.2.2 (the denominator `(ω_nr² − ω²) + j2ζ_rω_nrω` of
(2-19) and the polar form `λ̃_r = ω_nr e^{jφ_r}` of (2-26), with `φ_r ≈ π/2` for a poorly damped
mode).

Results.
* `naturalFreqHz_mk`, `dampedFreqHz_mk`, `dampingRatio_mk` — eqs. (2-5), (2-6) for
  `λ = −α + jω_d`.
* `dampingRatio_mul_naturalFreq` — `ζ ω_n = −Re λ` (every `λ`); `naturalFreq_sq`,
  `naturalFreq_eq_sqrt` — `ω_n² = (Re λ)² + (Im λ)²`, `ω_n = √((Re λ)² + (Im λ)²)`.
* `sub_mul_sub_conj` — `(s − λ)(s − λ̄) = s² + 2ζω_n s + ω_n²` for every `s, λ ∈ ℂ`; at `s = jω`
  it is `(ω_n² − ω²) + j 2ζω_n ω` (`I_mul_sub_mul_I_mul_sub_conj`), the denominator of (2-19).
* `abs_dampingRatio_le_one`, `dampingRatio_sq_add_sq` (`ζ² + (ω_d/ω_n)² = 1`, `λ ≠ 0`),
  `abs_dampingRatio_lt_one_iff` (`|ζ| < 1 ↔ Im λ ≠ 0`, `λ ≠ 0`), `dampingRatio_pos_iff`
  (`0 < ζ ↔ Re λ < 0`), `dampingRatio_eq_zero_iff` (`ζ = 0 ↔ Re λ = 0`),
  `dampingRatio_conj`, `naturalFreq_conj`.
* `abs_dampedFreq_eq`, `dampedFreq_eq` — `|ω_d| = ω_n √(1 − ζ²)`, and `ω_d = ω_n √(1 − ζ²)` when
  `Im λ ≥ 0`.
* `eq_polar`, `eq_exp_arcsin` — for `Im λ ≥ 0`: `λ = ω_n(−ζ + j√(1 − ζ²))` and
  `λ = ω_n e^{j(π/2 + arcsin ζ)}` (the report's `φ_r = π/2 + arcsin ζ_r`); conversely
  `naturalFreq_polar`, `dampingRatio_polar`: `ω_n(−ζ + j√(1 − ζ²))` has natural frequency `ω_n`
  and damping ratio `ζ` (`ω_n > 0`, `|ζ| ≤ 1`);
  `arcsin_le_pi_div_two_mul` — `0 ≤ arcsin ζ ≤ (π/2) ζ` for `0 ≤ ζ ≤ 1`, so
  `|φ_r − π/2| ≤ (π/2) ζ_r` quantifies "`φ_r ≈ π/2` for a poorly damped mode".
* `criteria_dampingRatio_eq`, `criteria_naturalFrequency_eq` — for a real `2 × 2` matrix `A`
  with a non-real characteristic root `λ`, `Criteria.dampingRatio A = ζ(λ)` and
  `Criteria.naturalFrequency A = |λ|`: the matrix-level and the eigenvalue-level definitions
  agree.
-/

noncomputable section
namespace powerlib.Modal
open Complex
open scoped ComplexConjugate

/-- Natural frequency `ω_n = |λ|` of an eigenvalue (rad/s). -/
def naturalFreq (lam : ℂ) : ℝ := ‖lam‖

/-- Damped frequency `ω_d = Im λ` of an eigenvalue (rad/s). -/
def dampedFreq (lam : ℂ) : ℝ := lam.im

/-- Damping ratio `ζ = −Re λ / |λ|` of an eigenvalue (a fraction; `0` at `λ = 0`). -/
def dampingRatio (lam : ℂ) : ℝ := -lam.re / ‖lam‖

/-- Natural frequency in Hz, `f_n = ω_n / 2π`. -/
def naturalFreqHz (lam : ℂ) : ℝ := naturalFreq lam / (2 * Real.pi)

/-- Damped frequency in Hz, `f_d = ω_d / 2π`. -/
def dampedFreqHz (lam : ℂ) : ℝ := dampedFreq lam / (2 * Real.pi)

/-! ## The report's formulas (2-5), (2-6) -/

@[tmio T, powerlib_foundation] theorem naturalFreq_sq (lam : ℂ) :
    naturalFreq lam ^ 2 = lam.re ^ 2 + lam.im ^ 2 := by
  rw [naturalFreq, Complex.sq_norm, Complex.normSq_apply]
  ring

@[tmio T, powerlib_foundation] theorem naturalFreq_eq_sqrt (lam : ℂ) :
    naturalFreq lam = Real.sqrt (lam.re ^ 2 + lam.im ^ 2) := by
  rw [← naturalFreq_sq, Real.sqrt_sq (show 0 ≤ naturalFreq lam from norm_nonneg lam)]

/-- Eq. (2-5), natural frequency: `f_n = √(α² + ω_d²) / 2π` for `λ = −α + jω_d`. -/
@[tmio T, powerlib_foundation] theorem naturalFreqHz_mk (α ωd : ℝ) :
    naturalFreqHz (-(α : ℂ) + ωd * I) = Real.sqrt (α ^ 2 + ωd ^ 2) / (2 * Real.pi) := by
  rw [naturalFreqHz, naturalFreq_eq_sqrt]
  simp

/-- Eq. (2-5), damped frequency: `f_d = ω_d / 2π` for `λ = −α + jω_d`. -/
@[tmio T, powerlib_foundation] theorem dampedFreqHz_mk (α ωd : ℝ) :
    dampedFreqHz (-(α : ℂ) + ωd * I) = ωd / (2 * Real.pi) := by
  simp [dampedFreqHz, dampedFreq]

/-- Eq. (2-6): `ζ = α / √(α² + ω_d²)` for `λ = −α + jω_d`. -/
@[tmio T, powerlib_foundation] theorem dampingRatio_mk (α ωd : ℝ) :
    dampingRatio (-(α : ℂ) + ωd * I) = α / Real.sqrt (α ^ 2 + ωd ^ 2) := by
  rw [dampingRatio, ← naturalFreq, naturalFreq_eq_sqrt]
  simp

/-! ## Basic identities -/

/-- `ζ ω_n = −Re λ` for every `λ` (both sides vanish at `λ = 0`). -/
@[tmio T, powerlib_foundation] theorem dampingRatio_mul_naturalFreq (lam : ℂ) :
    dampingRatio lam * naturalFreq lam = -lam.re := by
  rw [dampingRatio, naturalFreq]
  rcases eq_or_ne lam 0 with rfl | h
  · simp
  · field_simp [norm_ne_zero_iff.mpr h]

@[tmio T, powerlib_foundation] theorem naturalFreq_conj (lam : ℂ) :
    naturalFreq (conj lam) = naturalFreq lam := by
  simp [naturalFreq]

@[tmio T, powerlib_foundation] theorem dampingRatio_conj (lam : ℂ) :
    dampingRatio (conj lam) = dampingRatio lam := by
  simp [dampingRatio]

/-- The standard quadratic: `(s − λ)(s − λ̄) = s² + 2ζω_n s + ω_n²`. -/
@[tmio T, powerlib_foundation] theorem sub_mul_sub_conj (s lam : ℂ) :
    (s - lam) * (s - conj lam) =
      s ^ 2 + 2 * (dampingRatio lam : ℂ) * (naturalFreq lam : ℂ) * s +
        (naturalFreq lam : ℂ) ^ 2 := by
  have h1 : ((dampingRatio lam * naturalFreq lam : ℝ) : ℂ) = ((-lam.re : ℝ) : ℂ) := by
    rw [dampingRatio_mul_naturalFreq]
  push_cast at h1
  have e1 := Complex.add_conj lam
  have e2 := Complex.mul_conj lam
  have e3 : (naturalFreq lam : ℂ) ^ 2 = (Complex.normSq lam : ℂ) := by
    rw [naturalFreq, ← Complex.ofReal_pow, Complex.sq_norm]
  push_cast at e1
  linear_combination (-s) * e1 + e2 - e3 - 2 * s * h1

/-- At `s = jω`: `(jω − λ)(jω − λ̄) = (ω_n² − ω²) + j 2ζω_n ω`, the denominator of (2-19). -/
@[tmio T, powerlib_foundation] theorem I_mul_sub_mul_I_mul_sub_conj (ω : ℝ) (lam : ℂ) :
    ((ω : ℂ) * I - lam) * ((ω : ℂ) * I - conj lam) =
      ((naturalFreq lam ^ 2 - ω ^ 2 : ℝ) : ℂ) +
        ((2 * dampingRatio lam * naturalFreq lam * ω : ℝ) : ℂ) * I := by
  rw [sub_mul_sub_conj]
  push_cast
  linear_combination (ω : ℂ) ^ 2 * Complex.I_sq

/-! ## Range of the damping ratio -/

@[tmio T, powerlib_foundation] theorem abs_dampingRatio_le_one (lam : ℂ) : |dampingRatio lam| ≤ 1 := by
  rw [dampingRatio, abs_div, abs_neg, abs_norm]
  exact div_le_one_of_le₀ (Complex.abs_re_le_norm lam) (norm_nonneg _)

/-- `ζ² + (ω_d / ω_n)² = 1` for `λ ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem dampingRatio_sq_add_sq {lam : ℂ} (h : lam ≠ 0) :
    dampingRatio lam ^ 2 + (dampedFreq lam / naturalFreq lam) ^ 2 = 1 := by
  have hn : naturalFreq lam ≠ 0 := norm_ne_zero_iff.mpr h
  have hsq := naturalFreq_sq lam
  rw [dampingRatio, ← naturalFreq, dampedFreq, div_pow, div_pow, neg_sq, ← add_div, ← hsq,
    div_self (pow_ne_zero 2 hn)]

/-- `|ζ| < 1` exactly for a non-real eigenvalue (`λ ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem abs_dampingRatio_lt_one_iff {lam : ℂ} (h : lam ≠ 0) :
    |dampingRatio lam| < 1 ↔ lam.im ≠ 0 := by
  have hn : 0 < naturalFreq lam := norm_pos_iff.mpr h
  have hsq := dampingRatio_sq_add_sq h
  rw [dampedFreq, div_pow] at hsq
  have hn2 : 0 < naturalFreq lam ^ 2 := by positivity
  constructor
  · intro hlt him
    rw [him] at hsq
    have : dampingRatio lam ^ 2 = 1 := by simpa using hsq
    have h1 : |dampingRatio lam| ^ 2 = 1 := by rw [sq_abs, this]
    nlinarith [abs_nonneg (dampingRatio lam)]
  · intro him
    have hpos : 0 < lam.im ^ 2 / naturalFreq lam ^ 2 := div_pos (by positivity) hn2
    have hz : dampingRatio lam ^ 2 < 1 := by linarith
    rw [← sq_abs] at hz
    nlinarith [abs_nonneg (dampingRatio lam)]

/-- `0 < ζ ↔ Re λ < 0`: positive damping is an eigenvalue in the open left half-plane. -/
@[tmio T, powerlib_foundation] theorem dampingRatio_pos_iff (lam : ℂ) : 0 < dampingRatio lam ↔ lam.re < 0 := by
  rw [dampingRatio]
  constructor
  · intro h
    rcases div_pos_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · exact absurd h2 (not_lt.mpr (norm_nonneg _))
  · intro h
    have hne : lam ≠ 0 := fun h0 => by simp [h0] at h
    exact div_pos (by linarith) (norm_pos_iff.mpr hne)

@[tmio T, powerlib_foundation] theorem dampingRatio_eq_zero_iff (lam : ℂ) :
    dampingRatio lam = 0 ↔ lam.re = 0 := by
  rw [dampingRatio, div_eq_zero_iff, neg_eq_zero, norm_eq_zero]
  constructor
  · rintro (h | rfl)
    · exact h
    · rfl
  · exact Or.inl

/-! ## Damped frequency and polar forms -/

/-- `|ω_d| = ω_n √(1 − ζ²)`. -/
@[tmio T, powerlib_foundation] theorem abs_dampedFreq_eq (lam : ℂ) :
    |dampedFreq lam| = naturalFreq lam * Real.sqrt (1 - dampingRatio lam ^ 2) := by
  rcases eq_or_ne lam 0 with rfl | h
  · simp [dampedFreq, naturalFreq]
  have hn : 0 < naturalFreq lam := norm_pos_iff.mpr h
  have hsq := dampingRatio_sq_add_sq h
  have h1 : 1 - dampingRatio lam ^ 2 = (dampedFreq lam / naturalFreq lam) ^ 2 := by linarith
  rw [h1, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hn]
  field_simp

/-- `ω_d = ω_n √(1 − ζ²)` for `Im λ ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem dampedFreq_eq {lam : ℂ} (h : 0 ≤ lam.im) :
    dampedFreq lam = naturalFreq lam * Real.sqrt (1 - dampingRatio lam ^ 2) := by
  rw [← abs_dampedFreq_eq, abs_of_nonneg (show 0 ≤ dampedFreq lam from h)]

/-- Polar form `λ = ω_n(−ζ + j√(1 − ζ²))` for `Im λ ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem eq_polar {lam : ℂ} (h : 0 ≤ lam.im) :
    lam = (naturalFreq lam : ℂ) *
      (-(dampingRatio lam : ℂ) + (Real.sqrt (1 - dampingRatio lam ^ 2) : ℂ) * I) := by
  have hre := dampingRatio_mul_naturalFreq lam
  have him := dampedFreq_eq h
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.neg_re, Complex.I_re, Complex.I_im, Complex.add_im, Complex.neg_im,
      Complex.mul_im]
    linarith
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.neg_re, Complex.I_re, Complex.I_im, Complex.add_im, Complex.neg_im,
      Complex.mul_re]
    rw [dampedFreq] at him
    linarith

/-- Exponential polar form `λ = ω_n e^{j(π/2 + arcsin ζ)}` for `Im λ ≥ 0`: the report's
`λ̃_r = ω_nr e^{jφ_r}` with `φ_r = π/2 + arcsin ζ_r`. -/
@[tmio T, powerlib_foundation] theorem eq_exp_arcsin {lam : ℂ} (h : 0 ≤ lam.im) :
    lam = (naturalFreq lam : ℂ) *
      Complex.exp (((Real.pi / 2 + Real.arcsin (dampingRatio lam) : ℝ) : ℂ) * I) := by
  have hz := abs_le.mp (abs_dampingRatio_le_one lam)
  have hexp : Complex.exp (((Real.pi / 2 + Real.arcsin (dampingRatio lam) : ℝ) : ℂ) * I) =
      -(dampingRatio lam : ℂ) + (Real.sqrt (1 - dampingRatio lam ^ 2) : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, Real.sin_arcsin hz.1 hz.2, Real.cos_arcsin]
    push_cast
    ring
  rw [hexp]
  exact eq_polar h

/-- Conversely, `ω_n(−ζ + j√(1 − ζ²))` has natural frequency `ω_n` (`ω_n ≥ 0`, `|ζ| ≤ 1`). -/
@[tmio T, powerlib_foundation] theorem naturalFreq_polar {ωn ζ : ℝ} (hωn : 0 ≤ ωn) (hζ : |ζ| ≤ 1) :
    naturalFreq ((ωn : ℂ) * (-(ζ : ℂ) + (Real.sqrt (1 - ζ ^ 2) : ℂ) * I)) = ωn := by
  have hz : 0 ≤ 1 - ζ ^ 2 := by nlinarith [abs_le.mp hζ]
  rw [naturalFreq_eq_sqrt]
  have : ((ωn : ℂ) * (-(ζ : ℂ) + (Real.sqrt (1 - ζ ^ 2) : ℂ) * I)).re ^ 2 +
      ((ωn : ℂ) * (-(ζ : ℂ) + (Real.sqrt (1 - ζ ^ 2) : ℂ) * I)).im ^ 2 = ωn ^ 2 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im]
    have := Real.sq_sqrt hz
    nlinarith
  rw [this, Real.sqrt_sq hωn]

/-- Conversely, `ω_n(−ζ + j√(1 − ζ²))` has damping ratio `ζ` (`ω_n > 0`, `|ζ| ≤ 1`). -/
@[tmio T, powerlib_foundation] theorem dampingRatio_polar {ωn ζ : ℝ} (hωn : 0 < ωn) (hζ : |ζ| ≤ 1) :
    dampingRatio ((ωn : ℂ) * (-(ζ : ℂ) + (Real.sqrt (1 - ζ ^ 2) : ℂ) * I)) = ζ := by
  rw [dampingRatio, ← naturalFreq, naturalFreq_polar hωn.le hζ]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.neg_re, Complex.I_re, Complex.add_im, Complex.neg_im, Complex.I_im, Complex.mul_im]
  field_simp
  ring

/-- `0 ≤ arcsin ζ ≤ (π/2) ζ` for `0 ≤ ζ ≤ 1` (Jordan's inequality `sin x ≥ (2/π) x`). -/
@[tmio T, powerlib_foundation] theorem arcsin_le_pi_div_two_mul {ζ : ℝ} (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) :
    0 ≤ Real.arcsin ζ ∧ Real.arcsin ζ ≤ Real.pi / 2 * ζ := by
  have ha : 0 ≤ Real.arcsin ζ := Real.arcsin_nonneg.mpr h0
  refine ⟨ha, ?_⟩
  have hj := Real.mul_le_sin ha (Real.arcsin_le_pi_div_two ζ)
  rw [Real.sin_arcsin (by linarith) h1] at hj
  have hpi := Real.pi_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at hj
  nlinarith

/-! ## Bridge to real 2×2 matrices -/

@[tmio T, powerlib_foundation] private theorem fin_two_root_trace_det {A : Matrix (Fin 2) (Fin 2) ℝ} {lam : ℂ}
    (hroot : (Linear.characteristicMatrix A lam).det = 0) (him : lam.im ≠ 0) :
    A.trace = 2 * lam.re ∧ A.det = lam.re ^ 2 + lam.im ^ 2 := by
  rw [Criteria.det_characteristicMatrix_fin_two] at hroot
  have hq : lam ^ 2 + ((-A.trace : ℝ) : ℂ) * lam + ((A.det : ℝ) : ℂ) = 0 := by
    rw [← hroot]; push_cast; ring
  have hr := Criteria.quadratic_root_re hq
  have hi := Criteria.quadratic_root_im hq
  have htr : A.trace = 2 * lam.re := by
    rcases mul_eq_zero.mp hi with h | h
    · exact absurd h him
    · linarith
  refine ⟨htr, ?_⟩
  rw [htr] at hr
  linarith

/-- For a real `2 × 2` matrix with a non-real characteristic root `λ`,
`Criteria.naturalFrequency A = |λ|`. -/
@[tmio T, powerlib_foundation] theorem criteria_naturalFrequency_eq {A : Matrix (Fin 2) (Fin 2) ℝ}
    {lam : ℂ} (hroot : (Linear.characteristicMatrix A lam).det = 0) (him : lam.im ≠ 0) :
    Criteria.naturalFrequency A = naturalFreq lam := by
  obtain ⟨-, hdet⟩ := fin_two_root_trace_det hroot him
  rw [Criteria.naturalFrequency, hdet, naturalFreq_eq_sqrt]

/-- For a real `2 × 2` matrix with a non-real characteristic root `λ`,
`Criteria.dampingRatio A = ζ(λ) = −Re λ / |λ|`. -/
@[tmio T, powerlib_foundation] theorem criteria_dampingRatio_eq {A : Matrix (Fin 2) (Fin 2) ℝ}
    {lam : ℂ} (hroot : (Linear.characteristicMatrix A lam).det = 0) (him : lam.im ≠ 0) :
    Criteria.dampingRatio A = dampingRatio lam := by
  obtain ⟨htr, hdet⟩ := fin_two_root_trace_det hroot him
  have hn : Real.sqrt A.det = naturalFreq lam := by rw [hdet, naturalFreq_eq_sqrt]
  rw [Criteria.dampingRatio, hn, htr, dampingRatio, ← naturalFreq]
  have hpos : naturalFreq lam ≠ 0 := by
    rw [naturalFreq, norm_ne_zero_iff]
    rintro rfl
    exact him rfl
  field_simp

end powerlib.Modal
