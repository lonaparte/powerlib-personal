import theorem.Delay.SampleHold
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Moving-average smoothing: frequency response and attenuation

The `L`-point moving average of a sampled record and the continuous window average: closed form
of the discrete response (Dirichlet kernel), no amplification, strict attenuation of every
oscillation and the exact nulls, and the magnitude `|sinc|` of the continuous window average.

Scope.
* Discrete time with unit sample spacing (`ω` in radians per sample; at the sampling rate `f_s`,
  `ω = 2π f / f_s`), the causal average `y[n] = (1/L) Σ_{k<L} x[n − k]` acting on complex
  exponentials (hence, by linearity and conjugation, on real sinusoids); no windowing other than
  the rectangular one, no transients at the record ends.
* The continuous window average over `T` is the normalized sample-and-hold of
  `theorem/Delay/SampleHold.lean` (`(1/T) ∫₀ᵀ e^{−s t} dt`); it is only read here, not redefined.

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026) §3.1 ("the
data can be smoothed using a moving average filter … this is not recommended, as it attenuates
possible existing forced oscillations at the high end of the frequency range"), Tables 3–10
("Span = 5").

Results.
* `maResp` (`H(ω) = (1/L) Σ_{k<L} e^{−jωk}`), `movingAverage_cexp` (the average of `e^{jωn}` is
  `H(ω) e^{jωn}`), `maResp_zero` (unit DC gain).
* `maResp_eq` (closed form `e^{−jω(L−1)/2} sin(Lω/2)/(L sin(ω/2))` for `ω ∉ 2πℤ`),
  `norm_maResp_le` (`|H| ≤ 1`), `norm_maResp_lt` (`|H| < 1` for `L ≥ 2`, `ω ∉ 2πℤ`: every
  oscillation component is strictly attenuated), `maResp_eq_zero_iff` (nulls exactly at
  `sin(Lω/2) = 0`, i.e. `f = j f_s / L`).
* `sin_mul_div_sin_antitoneOn`, `norm_maResp_antitoneOn` (`|H|` decreases on the main lobe
  `(0, 2π/L]`: the higher the frequency, the stronger the attenuation).
* `maResp_top_of_band` (at `f_s = 10 Hz`: the 5-point average removes `2 Hz` completely, the
  3-point average keeps `(1 + √5)/6 ≈ 0.54` of it).
* `norm_sampleHold_jω_lt_one` (continuous window average: `|H(jω)| = |sinc(ωT/2)| < 1` for
  `ω ≠ 0`).

Sharpening (§3.1). The attenuation is strict at every nonzero frequency and total at
`f = j f_s / L`. If the tables' "Span = 5" denotes a 5-point moving average of the 10 Hz data
(the report does not define it), that smoothing annihilates the 2 Hz top of the assessed band.

Family and connection conclusions.
* None: this module defines no family; every result is an identity or inequality of explicit
  frequency responses.
-/

noncomputable section
namespace powerlib.Signal
open Complex Finset

/-! ## The discrete moving average -/

/-- Frequency response `H(ω) = (1/L) Σ_{k<L} e^{−jωk}` of the `L`-point moving average
`y[n] = (1/L) Σ_{k<L} x[n − k]` (`ω` in radians per sample). -/
def maResp (L : ℕ) (ω : ℝ) : ℂ := (1 / (L : ℂ)) * ∑ k ∈ range L, exp ((-(ω * k) : ℝ) * I)

/-- The moving average of a sampled complex exponential `e^{jωn}` is `H(ω) e^{jωn}`. -/
@[tmio T, powerlib_foundation] theorem movingAverage_cexp (L : ℕ) (ω : ℝ) (n : ℤ) :
    (1 / (L : ℂ)) * ∑ k ∈ range L, exp (((ω * (n - k) : ℝ)) * I) =
      maResp L ω * exp ((ω * n : ℝ) * I) := by
  rw [maResp, mul_assoc, sum_mul]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Unit DC gain. -/
@[tmio T, powerlib_foundation] theorem maResp_zero {L : ℕ} (hL : L ≠ 0) : maResp L 0 = 1 := by
  simp [maResp, hL]

/-- `e^{−2jx} − 1 = e^{−jx} (−2j sin x)`. -/
@[tmio T, powerlib_foundation] private theorem exp_sub_one_half (x : ℝ) :
    exp ((-(2 * x) : ℝ) * I) - 1 = exp ((-x : ℝ) * I) * (-2 * I * (Real.sin x : ℂ)) := by
  rw [ofReal_sin, Complex.sin]
  have h1 : exp ((-x : ℝ) * I) * exp ((x : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
  have h2 : exp ((-(2 * x) : ℝ) * I) = exp ((-x : ℝ) * I) * exp ((-x : ℝ) * I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  have h3 : exp (-(x : ℂ) * I) = exp ((-x : ℝ) * I) := by push_cast; ring_nf
  rw [h2, h3]
  linear_combination h1 + (exp ((-x : ℝ) * I) * (exp ((-x : ℝ) * I) - exp (↑x * I))) * I_sq

/-- Closed form (Dirichlet kernel): for `ω ∉ 2πℤ` (`sin(ω/2) ≠ 0`),
`H(ω) = e^{−jω(L−1)/2} sin(Lω/2) / (L sin(ω/2))`. -/
@[tmio T, powerlib_foundation] theorem maResp_eq {L : ℕ} (hL : L ≠ 0) {ω : ℝ}
    (hs : Real.sin (ω / 2) ≠ 0) :
    maResp L ω = exp ((-(ω * (L - 1) / 2) : ℝ) * I) *
      ((Real.sin (L * ω / 2) / (L * Real.sin (ω / 2)) : ℝ) : ℂ) := by
  set z := exp ((-ω : ℝ) * I)
  have hzk : ∀ k : ℕ, exp ((-(ω * k) : ℝ) * I) = z ^ k := fun k => by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  have hz : z - 1 = exp ((-(ω / 2) : ℝ) * I) * (-2 * I * (Real.sin (ω / 2) : ℂ)) := by
    rw [← exp_sub_one_half]; simp only [z]; push_cast; ring_nf
  have hzL : z ^ L - 1 = exp ((-(L * ω / 2) : ℝ) * I) * (-2 * I * (Real.sin (L * ω / 2) : ℂ)) := by
    rw [← exp_sub_one_half, ← hzk]; push_cast; ring_nf
  have hs' : (Real.sin (ω / 2) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hz1 : z - 1 ≠ 0 := by
    rw [hz]; exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (by simp) hs')
  have hgeom : ∑ k ∈ range L, z ^ k = (z ^ L - 1) / (z - 1) :=
    geom_sum_eq (sub_ne_zero.mp hz1) L
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [maResp, sum_congr rfl fun k _ => hzk k, hgeom, hzL, hz]
  have hexp : exp ((-(L * ω / 2) : ℝ) * I) =
      exp ((-(ω * (L - 1) / 2) : ℝ) * I) * exp ((-(ω / 2) : ℝ) * I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [hexp]
  have he : exp ((-(ω / 2) : ℝ) * I) ≠ 0 := Complex.exp_ne_zero _
  push_cast
  field_simp

/-- Smoothing never amplifies: `|H(ω)| ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem norm_maResp_le (L : ℕ) (ω : ℝ) : ‖maResp L ω‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [maResp]
  rw [maResp, norm_mul]
  calc ‖1 / (L : ℂ)‖ * ‖∑ k ∈ range L, exp ((-(ω * k) : ℝ) * I)‖
      ≤ ‖1 / (L : ℂ)‖ * ∑ k ∈ range L, ‖exp ((-(ω * k) : ℝ) * I)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = 1 := by
        simp only [norm_exp_ofReal_mul_I, sum_const, card_range, nsmul_eq_mul, mul_one,
          norm_div, norm_one, Complex.norm_natCast]
        field_simp

/-- Smoothing strictly attenuates every oscillation: for `L ≥ 2` and `ω ∉ 2πℤ`,
`|H(ω)| < 1`. -/
@[tmio T, powerlib_foundation] theorem norm_maResp_lt {L : ℕ} (hL : 2 ≤ L) {ω : ℝ}
    (hs : Real.sin (ω / 2) ≠ 0) : ‖maResp L ω‖ < 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have h12 : ‖(1 : ℂ) + exp ((-ω : ℝ) * I)‖ < 2 := by
    have hcos : Real.cos ω < 1 := by
      have h2 : Real.cos ω = 1 - 2 * Real.sin (ω / 2) ^ 2 := by
        have := Real.cos_sq_add_sin_sq (ω / 2)
        rw [show ω = 2 * (ω / 2) by ring, Real.cos_two_mul]
        rw [show 2 * (ω / 2) / 2 = ω / 2 by ring] at *
        linarith
      have : 0 < Real.sin (ω / 2) ^ 2 := by positivity
      linarith
    have hsq : ‖(1 : ℂ) + exp ((-ω : ℝ) * I)‖ ^ 2 = 2 + 2 * Real.cos ω := by
      rw [← normSq_eq_norm_sq, normSq_apply]
      simp only [add_re, one_re, exp_ofReal_mul_I_re, add_im, one_im, exp_ofReal_mul_I_im,
        zero_add, Real.cos_neg, Real.sin_neg]
      nlinarith [Real.sin_sq_add_cos_sq ω]
    nlinarith [norm_nonneg ((1 : ℂ) + exp ((-ω : ℝ) * I))]
  have hsum : ∑ k ∈ range (m + 2), exp ((-(ω * k) : ℝ) * I) =
      ((1 : ℂ) + exp ((-ω : ℝ) * I)) +
        ∑ k ∈ range m, exp ((-(ω * ((k + 1 + 1 : ℕ) : ℝ)) : ℝ) * I) := by
    rw [sum_range_succ', sum_range_succ']
    simp only [zero_add, Nat.cast_one, mul_one, Nat.cast_zero, mul_zero, neg_zero, ofReal_zero,
      zero_mul, Complex.exp_zero]
    ring
  rw [maResp, norm_mul, hsum]
  have hb : ‖((1 : ℂ) + exp ((-ω : ℝ) * I)) +
      ∑ k ∈ range m, exp ((-(ω * ((k + 1 + 1 : ℕ) : ℝ)) : ℝ) * I)‖ < 2 + m := by
    calc _ ≤ ‖(1 : ℂ) + exp ((-ω : ℝ) * I)‖ +
          ‖∑ k ∈ range m, exp ((-(ω * ((k + 1 + 1 : ℕ) : ℝ)) : ℝ) * I)‖ := norm_add_le _ _
      _ ≤ ‖(1 : ℂ) + exp ((-ω : ℝ) * I)‖ +
          ∑ k ∈ range m, ‖exp ((-(ω * ((k + 1 + 1 : ℕ) : ℝ)) : ℝ) * I)‖ := by
            gcongr; exact norm_sum_le _ _
      _ < 2 + m := by
          simp only [norm_exp_ofReal_mul_I, sum_const, card_range, nsmul_eq_mul, mul_one]
          linarith
  have hpos : (0 : ℝ) < (m + 2 : ℕ) := by positivity
  rw [norm_div, norm_one, Complex.norm_natCast]
  calc 1 / ((m + 2 : ℕ) : ℝ) * _ < 1 / ((m + 2 : ℕ) : ℝ) * (2 + m) :=
        mul_lt_mul_of_pos_left hb (by positivity)
    _ = 1 := by push_cast; field_simp; ring

/-- The moving average annihilates exactly the frequencies with `sin(Lω/2) = 0`, `ω ∉ 2πℤ`:
`f = j f_s / L` at the sampling rate `f_s`. -/
@[tmio T, powerlib_foundation] theorem maResp_eq_zero_iff {L : ℕ} (hL : L ≠ 0) {ω : ℝ}
    (hs : Real.sin (ω / 2) ≠ 0) : maResp L ω = 0 ↔ Real.sin (L * ω / 2) = 0 := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  rw [maResp_eq hL hs, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _), ofReal_eq_zero,
    div_eq_zero_iff, or_iff_left (mul_ne_zero hL' hs)]

/-- §3.1 at `10 Hz` sampling (`ω = 2π f / 10` per sample): the 5-point average removes the
`2 Hz` top of the band completely, the 3-point average keeps only `(1 + √5)/6 ≈ 0.54` of it. -/
@[tmio T, powerlib_foundation] theorem maResp_top_of_band :
    maResp 5 (2 * Real.pi * 2 / 10) = 0 ∧
      ‖maResp 3 (2 * Real.pi * 2 / 10)‖ = (1 + √5) / 6 := by
  have hs : Real.sin (2 * Real.pi * 2 / 10 / 2) ≠ 0 := by
    rw [show 2 * Real.pi * 2 / 10 / 2 = Real.pi / 5 by ring]
    exact (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
  refine ⟨(maResp_eq_zero_iff (by norm_num) hs).mpr ?_, ?_⟩
  · rw [show ((5 : ℕ) : ℝ) * (2 * Real.pi * 2 / 10) / 2 = (1 : ℕ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi 1
  · rw [maResp_eq (by norm_num) hs, norm_mul, norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    rw [show 2 * Real.pi * 2 / 10 / 2 = Real.pi / 5 by ring,
      show ((3 : ℕ) : ℝ) * (2 * Real.pi * 2 / 10) / 2 = Real.pi - 2 * (Real.pi / 5) by
        push_cast; ring, Real.sin_pi_sub, Real.sin_two_mul]
    have hs5 : 0 < Real.sin (Real.pi / 5) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    rw [show 2 * Real.sin (Real.pi / 5) * Real.cos (Real.pi / 5) /
        (((3 : ℕ) : ℝ) * Real.sin (Real.pi / 5)) = 2 * Real.cos (Real.pi / 5) / 3 by
      push_cast; field_simp, Real.cos_pi_div_five]
    rw [abs_of_pos (by positivity)]
    ring

/-- `sin(L x)/sin x` decreases on `(0, π/L]` for real `L ≥ 2` (its derivative has the numerator
`L cos(Lx) sin x − sin(Lx) cos x`, which vanishes at `0` and has derivative
`(1 − L²) sin(Lx) sin x ≤ 0`). -/
@[tmio T, powerlib_foundation] theorem sin_mul_div_sin_antitoneOn {L : ℝ} (hL2 : 2 ≤ L) :
    AntitoneOn (fun x => Real.sin (L * x) / Real.sin x) (Set.Ioc 0 (Real.pi / L)) := by
  have hL : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hπL : Real.pi / L < Real.pi := div_lt_self Real.pi_pos (by linarith)
  have hsin : ∀ x ∈ Set.Ioc 0 (Real.pi / L), 0 < Real.sin x := fun x hx =>
    Real.sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans_lt hπL)
  -- numerator of the derivative
  set N : ℝ → ℝ := fun x => L * Real.cos (L * x) * Real.sin x - Real.sin (L * x) * Real.cos x
  have hN' : ∀ x, HasDerivAt N ((1 - L ^ 2) * Real.sin (L * x) * Real.sin x) x := fun x => by
    have h1 : HasDerivAt (fun x => Real.cos (L * x)) (-Real.sin (L * x) * L) x := by
      simpa using ((hasDerivAt_id' x).const_mul L).cos
    have h2 : HasDerivAt (fun x => Real.sin (L * x)) (Real.cos (L * x) * L) x := by
      simpa using ((hasDerivAt_id' x).const_mul L).sin
    have := ((h1.const_mul L).mul (Real.hasDerivAt_sin x)).sub (h2.mul (Real.hasDerivAt_cos x))
    convert this using 1
    ring
  have hNle : ∀ x ∈ Set.Icc 0 (Real.pi / L), N x ≤ 0 := by
    have hanti : AntitoneOn N (Set.Icc 0 (Real.pi / L)) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (fun x _ => (hN' x).continuousAt.continuousWithinAt)
        (fun x _ => (hN' x).hasDerivWithinAt) fun x hx => ?_
      rw [interior_Icc] at hx
      have hs1 : 0 ≤ Real.sin (L * x) := Real.sin_nonneg_of_nonneg_of_le_pi (by
        nlinarith [hx.1]) (by have := hx.2; rw [lt_div_iff₀ hL0] at this; linarith)
      have hs2 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le (by
        have := hx.2; have : Real.pi / L ≤ Real.pi := div_le_self Real.pi_pos.le hL; linarith)
      have : 1 - L ^ 2 ≤ 0 := by nlinarith
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg this hs1) hs2
    intro x hx
    have h0 : N 0 = 0 := by simp [N]
    have := hanti ⟨le_rfl, by positivity⟩ hx hx.1
    linarith
  have hg : ∀ x ∈ Set.Ioc 0 (Real.pi / L), HasDerivAt (fun x => Real.sin (L * x) / Real.sin x)
      (N x / Real.sin x ^ 2) x := fun x hx => by
    have h2 : HasDerivAt (fun x => Real.sin (L * x)) (Real.cos (L * x) * L) x := by
      simpa using ((hasDerivAt_id' x).const_mul L).sin
    have := h2.div (Real.hasDerivAt_sin x) (hsin x hx).ne'
    convert this using 1
    simp only [N]
    ring
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc _ _)
    (f' := fun x => N x / Real.sin x ^ 2)
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hg x (interior_subset hx)).hasDerivWithinAt) fun x hx => ?_
  have hx' := interior_subset hx
  exact div_nonpos_of_nonpos_of_nonneg (hNle x ⟨hx'.1.le, hx'.2⟩) (sq_nonneg _)

/-- Smoothing attenuates more the higher the frequency over the main lobe: `|H(ω)|` decreases on
`(0, 2π/L]` (`L ≥ 2`), from `1` at `ω → 0` to `0` at the first null `ω = 2π/L`. -/
@[tmio T, powerlib_foundation] theorem norm_maResp_antitoneOn {L : ℕ} (hL : 2 ≤ L) :
    AntitoneOn (fun ω => ‖maResp L ω‖) (Set.Ioc 0 (2 * Real.pi / L)) := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hmap : ∀ ω ∈ Set.Ioc 0 (2 * Real.pi / L), ω / 2 ∈ Set.Ioc 0 (Real.pi / L) := fun ω hω =>
    ⟨by linarith [hω.1], by
      have := hω.2
      rw [le_div_iff₀ hL0] at this ⊢
      linarith⟩
  have hform : ∀ ω ∈ Set.Ioc 0 (2 * Real.pi / L),
      ‖maResp L ω‖ = Real.sin (L * (ω / 2)) / Real.sin (ω / 2) / L := by
    intro ω hω
    have hx := hmap ω hω
    have hπL : Real.pi / L < Real.pi := div_lt_self Real.pi_pos (by linarith)
    have hs : 0 < Real.sin (ω / 2) := Real.sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans_lt hπL)
    have hsL : 0 ≤ Real.sin (L * (ω / 2)) := Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [hx.1]) (by have := hx.2; rw [le_div_iff₀ hL0] at this; linarith)
    rw [maResp_eq (by omega) hs.ne', norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, show (L : ℝ) * ω / 2 = L * (ω / 2) by ring,
      abs_of_nonneg (div_nonneg hsL (by positivity))]
    field_simp
  intro a ha b hb hab
  simp only
  rw [hform a ha, hform b hb]
  exact div_le_div_of_nonneg_right (sin_mul_div_sin_antitoneOn hL' (hmap a ha) (hmap b hb)
    (by linarith)) hL0.le

/-! ## The continuous window average -/

/-- The continuous window average over `T ≠ 0` (the normalized sample-and-hold
`Delay.sampleHold`) has magnitude `|sinc(ωT/2)|` (`Delay.sampleHold_jω`), strictly below `1` at
every `ω ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem norm_sampleHold_jω_lt_one {T ω : ℝ} (hT : T ≠ 0)
    (hω : ω ≠ 0) :
    ‖Delay.sampleHold T (ω * I)‖ = |Real.sinc (ω * T / 2)| ∧
      ‖Delay.sampleHold T (ω * I)‖ < 1 := by
  have hn : ‖Delay.sampleHold T (ω * I)‖ = |Real.sinc (ω * T / 2)| := by
    rw [Delay.sampleHold_jω hT, norm_mul, Delay.norm_pureDelay_jω, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  refine ⟨hn, ?_⟩
  have hx : ω * T / 2 ≠ 0 := by
    have := mul_ne_zero hω hT; intro h; apply this; linarith
  rw [hn, Real.sinc_of_ne_zero hx, abs_div, div_lt_one (abs_pos.mpr hx)]
  exact Real.abs_sin_lt_abs hx

end powerlib.Signal
