import theorem.WPT.Compensation

/-! # Bifurcation of the zero-phase-angle frequencies of the series–series link

The input reactance of the series–series compensated link away from its design frequency, and the
frequencies at which it vanishes. With both coils tuned to `ω₀` the input impedance is real at
`ω₀` for every load (`ssLink_inputImpedance`); this module decides when it is also real at other
frequencies, the bifurcation (frequency splitting) of the zero-phase-angle frequencies, and in which
direction the input reactance crosses zero at `ω₀`. In the normalized frequency `u = ω/ω₀`, with the
squared coupling coefficient `c = k² = M²/(L₁L₂)` and `x = 1/Q²`, `Q = ω₀L₂/(R₂ + R_L)` the loaded
quality factor of the secondary, the input reactance vanishes exactly at `u = 1` and at the positive
roots `u²` of `(1 − c) w² − (2 − x) w + 1`. A second zero-phase-angle frequency exists **iff**
`x < 2` and `c ≥ x − x²/4`, i.e. `Q² > 1/2` and `k ≥ k_c = (1/Q)√(1 − 1/(4Q²))`, the critical
coupling. The reactance numerator `N(ω) = ω³((R₂ + R_L)² + X₂²) Im Z_in` is a polynomial with the
sign of the input reactance at every positive frequency; its slope at `ω₀` is
`2ω₀³((R₂ + R_L)² L₁ − ω₀² M² L₂) = 2ω₀³(R₂ + R_L)² L₁ (1 − k² Q²)`, so the input turns from
capacitive to inductive through `ω₀` when `kQ < 1` and from inductive to capacitive when `kQ > 1`.

Model boundary.
* The coil pair `tunedCoils w ω₀` (`theorem/WPT/Compensation.lean`: series capacitors
  `S_k = ω₀² L_k`, both coils resonant at the one design frequency `ω₀ > 0`), the secondary
  terminated by the load resistance `R_L`, operated at the angular frequency `ω > 0`, in sinusoidal
  steady state (RMS phasors). The primary winding resistance does not enter the input reactance.
* Positive inductances, a positive secondary resistance `R₂ + R_L > 0`, a coupling `0 < M² < L₁L₂`.
  An ideal sinusoidal voltage source; no inverter harmonics, rectifier, control or transients
  (the frequency tracking loop is `theorem/WPT/Tracking.lean`).

Source: the bifurcation of the zero-phase-angle frequencies of loosely coupled inductive power
transfer (Wang, Covic and Stielau, *IEEE Trans. Ind. Electron.* 51 (2004) 148–157); frequency
splitting and the critical coupling of two resonant coils (Hui, Zhong and Lee, *IEEE Trans. Power
Electron.* 29 (2014) 4500–4511); the input impedance of `theorem/Passive/Coupled.lean`.

Results.
* `inputImpedance_im` (every coupled pair: `Im Z_in(jω) = X₁ − (ωM)² X₂/((R₂ + R_L)² + X₂²)`).
* `reactanceNumerator` (`N`), `inputImpedance_im_mul` (`Im Z_in · ω³((R₂ + R_L)² + X₂²) = N` for the
  tuned pair), `inputImpedance_im_pos_iff`, `inputImpedance_im_eq_zero_iff` (at a positive
  frequency the input reactance has the sign of `N`).
* `reactanceNumerator_normalized` (`N(u ω₀) = ω₀⁶ L₁ L₂² (u² − 1)((1 − c) u⁴ − (2 − x) u² + 1)`),
  `exists_root_iff` (the quadratic `(1 − c) w² − (2 − x) w + 1`, `0 < c < 1`, has a positive root
  `w ≠ 1` iff `x < 2` and `x − x²/4 ≤ c`), `exists_split_iff` (the tuned link has a
  zero-phase-angle frequency `ω ≠ ω₀` iff `x < 2` and `x − x²/4 ≤ c`).
* `hasDerivAt_reactanceNumerator` (the slope `2ω₀³((R₂ + R_L)² L₁ − ω₀² M² L₂)` of `N` at `ω₀`).
-/

noncomputable section

namespace powerlib.WPT

open Complex

/-- The input reactance of every coupled pair with the secondary terminated by `R_L`:
`Im Z_in(jω) = X₁ − (ωM)² X₂/((R₂ + R_L)² + X₂²)`. -/
@[tmio M, powerlib_domain] theorem inputImpedance_im (w : Passive.Coupled) (RL ω : ℝ) :
    (w.inputImpedance RL (ω * I)).im = w.primary.reactance ω -
      (ω * w.M) ^ 2 * w.secondary.reactance ω /
        ((w.secondary.R + RL) ^ 2 + w.secondary.reactance ω ^ 2) := by
  rw [Passive.Coupled.inputImpedance_jω, Passive.SeriesRLC.impedance_jω,
    Passive.SeriesRLC.impedance_jω]
  rw [show ((w.secondary.R : ℂ) + (w.secondary.reactance ω : ℂ) * I + (RL : ℂ)) =
      (((w.secondary.R + RL : ℝ) : ℂ) + (w.secondary.reactance ω : ℂ) * I) by push_cast; ring]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, Complex.div_im, Complex.add_re, Complex.mul_re, Complex.normSq_apply,
    ← Complex.ofReal_pow]
  ring

/-- The reactance numerator `N(ω) = ((R₂ + R_L)² ω² + P₂²) P₁ − ω⁴ M² P₂` of the pair tuned at
`ω₀`, with `P_k = L_k (ω² − ω₀²) = ω X_k(ω)`. -/
def reactanceNumerator (w : Passive.Coupled) (RL ω₀ ω : ℝ) : ℝ :=
  (ω ^ 2 * (w.secondary.R + RL) ^ 2 + (w.secondary.L * (ω ^ 2 - ω₀ ^ 2)) ^ 2) *
      (w.primary.L * (ω ^ 2 - ω₀ ^ 2)) -
    ω ^ 4 * w.M ^ 2 * (w.secondary.L * (ω ^ 2 - ω₀ ^ 2))

/-- The reactance of a coil tuned at `ω₀`, at `ω ≠ 0`: `X(ω) = L (ω² − ω₀²)/ω`. -/
@[tmio M, powerlib_domain] private theorem tuned_reactance_eq (R L ω₀ : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    (⟨R, L, tunedElastance L ω₀⟩ : Passive.SeriesRLC).reactance ω = L * (ω ^ 2 - ω₀ ^ 2) / ω := by
  simp only [Passive.SeriesRLC.reactance, tunedElastance]
  field_simp

/-- `(A − B/D)(c D) = A c D − B c` for `D ≠ 0`. -/
@[tmio T, powerlib_foundation] private theorem sub_div_mul_cancel {A B D c : ℝ} (hD : D ≠ 0) :
    (A - B / D) * (c * D) = A * c * D - B * c := by
  field_simp

/-- For the tuned pair at `ω ≠ 0`, `Im Z_in · ω³((R₂ + R_L)² + X₂²) = N(ω)`. -/
@[tmio M, powerlib_domain] theorem inputImpedance_im_mul (w : Passive.Coupled) (RL ω₀ : ℝ)
    {ω : ℝ} (hω : ω ≠ 0) :
    ((tunedCoils w ω₀).inputImpedance RL (ω * I)).im *
        (ω ^ 3 * ((w.secondary.R + RL) ^ 2 + (tunedCoils w ω₀).secondary.reactance ω ^ 2)) =
      reactanceNumerator w RL ω₀ ω := by
  have him := inputImpedance_im (tunedCoils w ω₀) RL ω
  have hX₁ : (tunedCoils w ω₀).primary.reactance ω = w.primary.L * (ω ^ 2 - ω₀ ^ 2) / ω :=
    tuned_reactance_eq _ _ _ hω
  have hX₂ : (tunedCoils w ω₀).secondary.reactance ω = w.secondary.L * (ω ^ 2 - ω₀ ^ 2) / ω :=
    tuned_reactance_eq _ _ _ hω
  have hR : (tunedCoils w ω₀).secondary.R = w.secondary.R := rfl
  have hM : (tunedCoils w ω₀).M = w.M := rfl
  rw [him, hX₁, hX₂, hR, hM]
  rcases ne_or_eq ((w.secondary.R + RL) ^ 2 + (w.secondary.L * (ω ^ 2 - ω₀ ^ 2) / ω) ^ 2) 0 with
    hpos | hpos
  · rw [sub_div_mul_cancel hpos]
    unfold reactanceNumerator
    field_simp
  · -- a vanishing denominator: then `R₂ + R_L = 0` and `P₂ = 0`, and both sides vanish
    have h1 : w.secondary.R + RL = 0 := by
      nlinarith [sq_nonneg (w.secondary.R + RL), sq_nonneg (w.secondary.L * (ω ^ 2 - ω₀ ^ 2) / ω)]
    have h2 : w.secondary.L * (ω ^ 2 - ω₀ ^ 2) / ω = 0 := by
      nlinarith [sq_nonneg (w.secondary.R + RL), sq_nonneg (w.secondary.L * (ω ^ 2 - ω₀ ^ 2) / ω)]
    have h3 : w.secondary.L * (ω ^ 2 - ω₀ ^ 2) = 0 := by
      rwa [div_eq_zero_iff, or_iff_left hω] at h2
    rw [hpos, mul_zero, mul_zero]
    unfold reactanceNumerator
    rw [h1, h3]
    ring

/-- At a positive frequency, with a positive secondary resistance, the input is inductive exactly
where `N > 0`. -/
@[tmio M, powerlib_domain] theorem inputImpedance_im_pos_iff (w : Passive.Coupled) {RL ω₀ ω : ℝ}
    (hω : 0 < ω) (hR : 0 < w.secondary.R + RL) :
    0 < ((tunedCoils w ω₀).inputImpedance RL (ω * I)).im ↔ 0 < reactanceNumerator w RL ω₀ ω := by
  rw [← inputImpedance_im_mul w RL ω₀ hω.ne']
  have : 0 < ω ^ 3 * ((w.secondary.R + RL) ^ 2 + (tunedCoils w ω₀).secondary.reactance ω ^ 2) := by
    positivity
  exact (mul_pos_iff_of_pos_right this).symm

/-- At a positive frequency, with a positive secondary resistance, the input reactance vanishes
exactly where `N` does. -/
@[tmio M, powerlib_domain] theorem inputImpedance_im_eq_zero_iff (w : Passive.Coupled)
    {RL ω₀ ω : ℝ} (hω : 0 < ω) (hR : 0 < w.secondary.R + RL) :
    ((tunedCoils w ω₀).inputImpedance RL (ω * I)).im = 0 ↔ reactanceNumerator w RL ω₀ ω = 0 := by
  rw [← inputImpedance_im_mul w RL ω₀ hω.ne']
  have : 0 < ω ^ 3 * ((w.secondary.R + RL) ^ 2 + (tunedCoils w ω₀).secondary.reactance ω ^ 2) := by
    positivity
  rw [mul_eq_zero, or_iff_left this.ne']

/-- In the normalized frequency `u = ω/ω₀`, with `c = M²/(L₁L₂)` and
`x = ((R₂ + R_L)/(ω₀L₂))²`: `N(u ω₀) = ω₀⁶ L₁ L₂² (u² − 1)((1 − c) u⁴ − (2 − x) u² + 1)`. -/
@[tmio M, powerlib_domain] theorem reactanceNumerator_normalized (w : Passive.Coupled) (RL : ℝ)
    {ω₀ : ℝ} (hω₀ : ω₀ ≠ 0) (hL₁ : w.primary.L ≠ 0) (hL₂ : w.secondary.L ≠ 0) (u : ℝ) :
    reactanceNumerator w RL ω₀ (u * ω₀) =
      ω₀ ^ 6 * w.primary.L * w.secondary.L ^ 2 * (u ^ 2 - 1) *
        ((1 - w.M ^ 2 / (w.primary.L * w.secondary.L)) * (u ^ 2) ^ 2 -
          (2 - ((w.secondary.R + RL) / (ω₀ * w.secondary.L)) ^ 2) * u ^ 2 + 1) := by
  unfold reactanceNumerator
  field_simp
  ring

/-- The quadratic `(1 − c) w² − (2 − x) w + 1` with `0 < c < 1` has a positive root `w ≠ 1` **iff**
`x < 2` and `x − x²/4 ≤ c`. -/
@[tmio T, powerlib_foundation] theorem exists_root_iff {c x : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    (∃ w : ℝ, 0 < w ∧ w ≠ 1 ∧ (1 - c) * w ^ 2 - (2 - x) * w + 1 = 0) ↔
      x < 2 ∧ x - x ^ 2 / 4 ≤ c := by
  have ha : 0 < 1 - c := by linarith
  have hiff : x - x ^ 2 / 4 ≤ c ↔ 4 * (1 - c) ≤ (2 - x) ^ 2 := by
    constructor <;> intro h <;> nlinarith
  rw [hiff]
  constructor
  · rintro ⟨w, hw, -, hf⟩
    refine ⟨?_, ?_⟩
    · nlinarith [sq_nonneg w, mul_pos ha (pow_pos hw 2)]
    · nlinarith [sq_nonneg (2 * (1 - c) * w - (2 - x))]
  · rintro ⟨hx, hd⟩
    have hd0 : 0 ≤ (2 - x) ^ 2 - 4 * (1 - c) := by linarith
    have hq0 : 0 ≤ Real.sqrt ((2 - x) ^ 2 - 4 * (1 - c)) := Real.sqrt_nonneg _
    have hqq : Real.sqrt ((2 - x) ^ 2 - 4 * (1 - c)) ^ 2 = (2 - x) ^ 2 - 4 * (1 - c) :=
      Real.sq_sqrt hd0
    have hq_lt : Real.sqrt ((2 - x) ^ 2 - 4 * (1 - c)) < 2 - x := by
      have h := Real.sqrt_lt_sqrt hd0 (by linarith : (2 - x) ^ 2 - 4 * (1 - c) < (2 - x) ^ 2)
      rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 2 - x)] at h
    set q := Real.sqrt ((2 - x) ^ 2 - 4 * (1 - c))
    have hw₁ : 0 < ((2 - x) + q) / (2 * (1 - c)) := by positivity
    have hw₂ : 0 < ((2 - x) - q) / (2 * (1 - c)) := div_pos (by linarith) (by positivity)
    have hf₁ : (1 - c) * (((2 - x) + q) / (2 * (1 - c))) ^ 2 - (2 - x) *
        (((2 - x) + q) / (2 * (1 - c))) + 1 = 0 := by
      field_simp
      nlinarith [hqq]
    have hf₂ : (1 - c) * (((2 - x) - q) / (2 * (1 - c))) ^ 2 - (2 - x) *
        (((2 - x) - q) / (2 * (1 - c))) + 1 = 0 := by
      field_simp
      nlinarith [hqq]
    by_cases h1 : ((2 - x) + q) / (2 * (1 - c)) = 1
    · refine ⟨_, hw₂, fun h2 => ?_, hf₂⟩
      -- the product of the two roots is `1/(1 − c) ≠ 1`
      have hprod : ((2 - x) + q) / (2 * (1 - c)) * (((2 - x) - q) / (2 * (1 - c))) * (1 - c) =
          1 := by
        field_simp
        nlinarith [hqq]
      rw [h1, h2] at hprod
      linarith
    · exact ⟨_, hw₁, h1, hf₁⟩

/-- Bifurcation: the link tuned at `ω₀` has a zero-phase-angle frequency `ω ≠ ω₀` **iff**
`x < 2` and `x − x²/4 ≤ c`, with `c = M²/(L₁L₂) = k²` and `x = ((R₂ + R_L)/(ω₀L₂))² = 1/Q²`:
`Q² > 1/2` and `k² ≥ (1/Q²)(1 − 1/(4Q²))`, the critical coupling. -/
@[tmio M, powerlib_domain] theorem exists_split_iff (w : Passive.Coupled) {RL ω₀ : ℝ}
    (hω₀ : 0 < ω₀) (hL₁ : 0 < w.primary.L) (hL₂ : 0 < w.secondary.L)
    (hR : 0 < w.secondary.R + RL) (hM : w.M ≠ 0)
    (hk : w.M ^ 2 < w.primary.L * w.secondary.L) :
    (∃ ω, 0 < ω ∧ ω ≠ ω₀ ∧ ((tunedCoils w ω₀).inputImpedance RL (ω * I)).im = 0) ↔
      ((w.secondary.R + RL) / (ω₀ * w.secondary.L)) ^ 2 < 2 ∧
        ((w.secondary.R + RL) / (ω₀ * w.secondary.L)) ^ 2 -
            (((w.secondary.R + RL) / (ω₀ * w.secondary.L)) ^ 2) ^ 2 / 4 ≤
          w.M ^ 2 / (w.primary.L * w.secondary.L) := by
  have hLL : 0 < w.primary.L * w.secondary.L := mul_pos hL₁ hL₂
  have hc0 : 0 < w.M ^ 2 / (w.primary.L * w.secondary.L) := div_pos (by positivity) hLL
  have hc1 : w.M ^ 2 / (w.primary.L * w.secondary.L) < 1 := (div_lt_one hLL).mpr hk
  rw [← exists_root_iff hc0 hc1]
  have hK : 0 < ω₀ ^ 6 * w.primary.L * w.secondary.L ^ 2 := by positivity
  constructor
  · rintro ⟨ω, hω, hne, h0⟩
    rw [inputImpedance_im_eq_zero_iff w hω hR] at h0
    have hu : ω = ω / ω₀ * ω₀ := by field_simp
    rw [hu, reactanceNumerator_normalized w RL hω₀.ne' hL₁.ne' hL₂.ne'] at h0
    have hu0 : 0 < ω / ω₀ := div_pos hω hω₀
    have hu1 : (ω / ω₀) ^ 2 - 1 ≠ 0 := by
      intro h
      have : ω / ω₀ = 1 := by nlinarith
      exact hne (by field_simp at this; linarith)
    refine ⟨(ω / ω₀) ^ 2, by positivity, fun h => hu1 (by rw [h]; ring), ?_⟩
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (mul_ne_zero hK.ne' hu1)
    · exact h
  · rintro ⟨v, hv, hv1, hf⟩
    refine ⟨Real.sqrt v * ω₀, by positivity, fun h => hv1 ?_, ?_⟩
    · have : Real.sqrt v = 1 := by
        have := mul_right_cancel₀ hω₀.ne' (h.trans (one_mul ω₀).symm)
        exact this
      rw [← Real.sq_sqrt hv.le, this, one_pow]
    · rw [inputImpedance_im_eq_zero_iff w (by positivity) hR,
        reactanceNumerator_normalized w RL hω₀.ne' hL₁.ne' hL₂.ne', Real.sq_sqrt hv.le, hf,
        mul_zero]

/-- The slope of the reactance numerator at `ω₀`: `N'(ω₀) = 2ω₀³((R₂ + R_L)² L₁ − ω₀² M² L₂)`,
positive exactly when `k² Q² < 1` (`ω₀² M² L₂ < (R₂ + R_L)² L₁`). -/
@[tmio M, powerlib_domain] theorem hasDerivAt_reactanceNumerator (w : Passive.Coupled) (RL ω₀ : ℝ) :
    HasDerivAt (reactanceNumerator w RL ω₀)
      (2 * ω₀ ^ 3 * ((w.secondary.R + RL) ^ 2 * w.primary.L - ω₀ ^ 2 * w.M ^ 2 * w.secondary.L))
      ω₀ := by
  have he : HasDerivAt (fun ω : ℝ => ω ^ 2 - ω₀ ^ 2) (2 * ω₀) ω₀ := by
    simpa using (hasDerivAt_pow 2 ω₀).sub_const (ω₀ ^ 2)
  have h2 : HasDerivAt (fun ω : ℝ => ω ^ 2) (2 * ω₀) ω₀ := by simpa using hasDerivAt_pow 2 ω₀
  have h4 : HasDerivAt (fun ω : ℝ => ω ^ 4) (4 * ω₀ ^ 3) ω₀ := by simpa using hasDerivAt_pow 4 ω₀
  have h := (((h2.mul_const ((w.secondary.R + RL) ^ 2)).add
    ((he.const_mul w.secondary.L).pow 2)).mul (he.const_mul w.primary.L)).sub
    ((h4.mul_const (w.M ^ 2)).mul (he.const_mul w.secondary.L))
  convert h using 1
  · funext ω
    simp only [reactanceNumerator, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
  · simp
    ring

end powerlib.WPT
