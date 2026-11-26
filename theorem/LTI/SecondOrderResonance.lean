import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Resonance of the normalized second-order frequency response

The normalized second-order phasor `H(ν) = (a + jνb) / ((1 − ν²) + j2ζν)` (frequency ratio
`ν = ω/ω_n`) of a lightly damped mode: its squared amplitude, the frequency of maximum amplitude
(resonance) and its limit `ν² → 1` as `ζ → 0`, the low-pass channel (`b = 0`, unit-gain iff
`ζ² ≥ 1/2`, peak `1/(2ζ√(1 − ζ²))`), the band-pass channel (`a = 0`, peak `1/(2ζ)` at `ν = 1`),
and the growth of the peak as `ζ → 0⁺`.

Scope.
* Real parameters `a, b, ζ` and a real frequency ratio `ν`; pure algebra and real analysis of
  the explicit rational function `H`. No model family. The modal origin of `H` (one conjugate
  pair of a linear system, `a = A_r/ω_n²`, `b = B_r/ω_n`) is `theorem/Modal/ForcedPhasor.lean`.
* Resonance is the maximum over `ν` of the amplitude `|H(ν)|` (eq. (2-22)), written in the
  variable `u = ν² ≥ 0` as `|H|² = b² f(u)`, `f(u) = (c² + u) / ((1 − u)² + 4ζ²u)`, `c = a/b`.
  It needs `ζ ≠ 0` (for `ζ = 0` the amplitude is unbounded at `ν = 1`) and `b ≠ 0` (the case
  `b = 0` is the low-pass channel, treated separately).

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §2.2.1–§2.2.2,
eqs. (2-21), (2-22), (2-24). The report says "differentiate (2-23) with respect to `v_r`"; (2-23)
is the phase. The quantity maximized at (2-24) is the amplitude (2-22); this module proves that
(2-24) is its exact maximizer: `ν_r² = √(1 + 2(1 − 2ζ_r²)c² + c⁴) − c²`, `c = a/(bω_nr)`, is the
global maximum of the amplitude over `ν ≥ 0` whenever it is positive, it is a stationary point,
it equals `1` at `ζ_r = 0` and tends to `1` as `ζ_r → 0` (the report's "`ζ_r ≈ 0` ⇒ `v_r ≈ 1`").

Results.
* `resonanceDen`, `resonanceResp` — `D(ν) = (1 − ν²) + j2ζν` and `H(ν) = (a + jνb)/D(ν)`;
  `normSq_resonanceDen`, `resonanceDen_eq_zero_iff` (`D = 0 ↔ ν² = 1 ∧ ζ = 0`),
  `sq_norm_resonanceResp` (eq. (2-22): `|H|² = (a² + (νb)²)/((1 − ν²)² + (2ζν)²)`),
  `sq_norm_resonanceResp_eq` (`|H(ν)|² = b² f(ν²)`, `c = a/b`).
* `peakSq` — `u* = √(1 + 2(1 − 2ζ²)c² + c⁴) − c²` (eq. (2-24)); `ampSq_le_peak` (for `ζ ≠ 0`,
  `u* > 0`: `f(u) ≤ f(u*)` for every `u ≥ 0`), `hasDerivAt_ampSq_peak` (`f'(u*) = 0`),
  `ampSq_peak` (peak value `f(u*) = 1/(2u* − 2 + 4ζ²)`), `norm_resonanceResp_le_peak`
  (amplitude form: `|H(ν)| ≤ |H(√u*)|` for every `ν`).
* `peakSq_zero` (`u* = 1` at `ζ = 0`), `tendsto_peakSq` (`u* → 1` as `ζ → 0`).
* Auxiliary: `resonance_q_pos` (`(1 − u)² + 4ζ²u > 0` for `u ≥ 0`, `ζ ≠ 0`), `peakSq_eq` (the
  stationarity equation `u*² + 2c²u* = 1 + 2c²(1 − 2ζ²)`), `peak_identity`
  (`(c² + u*)q(u) − (c² + u)q(u*) = (c² + u*)(u − u*)²`), `norm_resonanceDen_eq`
  (`|D| = √((1 − ν²)² + (2ζν)²)`), `lowpass_lower_bound` (`|D(ν)| ≥ 2ζ√(1 − ζ²)`).
* Low-pass channel `1/D`: `norm_inv_resonanceDen_le_one_iff` (`|1/D(ν)| ≤ 1` for all `ν` iff
  `ζ² ≥ 1/2`), `norm_inv_resonanceDen_le` (`|1/D(ν)| ≤ 1/(2ζ√(1 − ζ²))` for `0 < ζ < 1`),
  `norm_inv_resonanceDen_peak` (equality at `ν = √(1 − 2ζ²)` when `ζ² ≤ 1/2`).
* Band-pass channel `jν/D`: `norm_bandpass_le` (`|jν/D(ν)| ≤ 1/(2ζ)`, `ζ > 0`),
  `norm_bandpass_one` (equality at `ν = 1`).
* Unbounded peaks: `tendsto_lowpass_peak`, `tendsto_bandpass_peak` — both peak values tend to
  `+∞` as `ζ → 0⁺` (the report's "the smaller the damping ratio the larger the amplitude").
-/

noncomputable section
namespace powerlib.LTI
open Complex Filter Topology Set

/-- Normalized second-order denominator `D(ν) = (1 − ν²) + j 2ζν`. -/
def resonanceDen (ζ ν : ℝ) : ℂ := ((1 - ν ^ 2 : ℝ) : ℂ) + ((2 * ζ * ν : ℝ) : ℂ) * I

/-- Normalized single-mode response `H(ν) = (a + jνb) / D(ν)`. -/
def resonanceResp (a b ζ ν : ℝ) : ℂ := ((a : ℂ) + ((ν * b : ℝ) : ℂ) * I) / resonanceDen ζ ν

/-- Normalized squared amplitude in `u = ν²`: `f(u) = (c² + u) / ((1 − u)² + 4ζ²u)`. -/
def ampSq (c ζ u : ℝ) : ℝ := (c ^ 2 + u) / ((1 - u) ^ 2 + 4 * ζ ^ 2 * u)

/-- The report's resonance frequency ratio squared (2-24):
`u* = √(1 + 2(1 − 2ζ²)c² + c⁴) − c²`. -/
def peakSq (c ζ : ℝ) : ℝ := Real.sqrt (1 + 2 * (1 - 2 * ζ ^ 2) * c ^ 2 + c ^ 4) - c ^ 2

/-! ## Amplitude of the normalized response -/

@[tmio T, powerlib_foundation] theorem normSq_resonanceDen (ζ ν : ℝ) :
    normSq (resonanceDen ζ ν) = (1 - ν ^ 2) ^ 2 + (2 * ζ * ν) ^ 2 := by
  rw [resonanceDen, Complex.normSq_add_mul_I]

@[tmio T, powerlib_foundation] theorem resonanceDen_eq_zero_iff (ζ ν : ℝ) :
    resonanceDen ζ ν = 0 ↔ ν ^ 2 = 1 ∧ ζ = 0 := by
  rw [← Complex.normSq_eq_zero, normSq_resonanceDen]
  constructor
  · intro h
    have h1 : (1 - ν ^ 2) ^ 2 = 0 := by nlinarith [sq_nonneg (1 - ν ^ 2), sq_nonneg (2 * ζ * ν)]
    have h2 : (2 * ζ * ν) ^ 2 = 0 := by nlinarith [sq_nonneg (1 - ν ^ 2), sq_nonneg (2 * ζ * ν)]
    have hν : ν ^ 2 = 1 := by nlinarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h1]
    have hν0 : ν ≠ 0 := by rintro rfl; norm_num at hν
    refine ⟨hν, ?_⟩
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h2
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact h
    · exact absurd h hν0
  · rintro ⟨hν, rfl⟩
    rw [hν]; ring

/-- Eq. (2-22), squared: `|H|² = (a² + (νb)²) / ((1 − ν²)² + (2ζν)²)`. -/
@[tmio T, powerlib_foundation] theorem sq_norm_resonanceResp (a b ζ ν : ℝ) :
    ‖resonanceResp a b ζ ν‖ ^ 2 = (a ^ 2 + (ν * b) ^ 2) / ((1 - ν ^ 2) ^ 2 + (2 * ζ * ν) ^ 2) := by
  rw [resonanceResp, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, normSq_resonanceDen,
    Complex.normSq_add_mul_I]

/-- In the variable `u = ν²`: `|H(ν)|² = b² f(ν²)` with `c = a/b`. -/
@[tmio T, powerlib_foundation] theorem sq_norm_resonanceResp_eq {b : ℝ} (hb : b ≠ 0) (a ζ ν : ℝ) :
    ‖resonanceResp a b ζ ν‖ ^ 2 = b ^ 2 * ampSq (a / b) ζ (ν ^ 2) := by
  rw [sq_norm_resonanceResp, ampSq, ← mul_div_assoc]
  congr 1
  · field_simp
  · ring

/-! ## The resonance frequency (2-24) -/

/-- The denominator `q(u) = (1 − u)² + 4ζ²u` is positive for `u ≥ 0` and `ζ ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem resonance_q_pos {ζ u : ℝ} (hζ : ζ ≠ 0) (hu : 0 ≤ u) :
    0 < (1 - u) ^ 2 + 4 * ζ ^ 2 * u := by
  have hz : 0 < ζ ^ 2 := by positivity
  rcases eq_or_lt_of_le hu with rfl | hu'
  · norm_num
  · nlinarith [sq_nonneg (1 - u)]

/-- The stationarity equation of (2-24): `u*² + 2c²u* = 1 + 2c²(1 − 2ζ²)` when `u* > 0`. -/
@[tmio T, powerlib_foundation] theorem peakSq_eq {c ζ : ℝ} (hpos : 0 < peakSq c ζ) :
    peakSq c ζ ^ 2 + 2 * c ^ 2 * peakSq c ζ - 1 - 2 * c ^ 2 + 4 * c ^ 2 * ζ ^ 2 = 0 := by
  set S := Real.sqrt (1 + 2 * (1 - 2 * ζ ^ 2) * c ^ 2 + c ^ 4) with hS
  have hp : peakSq c ζ = S - c ^ 2 := rfl
  have hS0 : 0 < S := by rw [hp] at hpos; nlinarith [sq_nonneg c]
  have hrad : 0 < 1 + 2 * (1 - 2 * ζ ^ 2) * c ^ 2 + c ^ 4 := Real.sqrt_pos.mp hS0
  have hS2 : S ^ 2 = 1 + 2 * (1 - 2 * ζ ^ 2) * c ^ 2 + c ^ 4 := Real.sq_sqrt hrad.le
  rw [hp]
  linear_combination hS2

/-- Key identity: with `q(u) = (1 − u)² + 4ζ²u` and `u*` of (2-24),
`(c² + u*) q(u) − (c² + u) q(u*) = (c² + u*)(u − u*)²`. -/
@[tmio T, powerlib_foundation] theorem peak_identity {c ζ : ℝ} (hpos : 0 < peakSq c ζ) (u : ℝ) :
    (c ^ 2 + peakSq c ζ) * ((1 - u) ^ 2 + 4 * ζ ^ 2 * u) -
        (c ^ 2 + u) * ((1 - peakSq c ζ) ^ 2 + 4 * ζ ^ 2 * peakSq c ζ) =
      (c ^ 2 + peakSq c ζ) * (u - peakSq c ζ) ^ 2 := by
  linear_combination (u - peakSq c ζ) * peakSq_eq hpos

/-- Eq. (2-24) is the maximizer: for `ζ ≠ 0` and `u* > 0`, `f(u) ≤ f(u*)` for every `u ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem ampSq_le_peak {c ζ : ℝ} (hζ : ζ ≠ 0) (hpos : 0 < peakSq c ζ)
    {u : ℝ} (hu : 0 ≤ u) : ampSq c ζ u ≤ ampSq c ζ (peakSq c ζ) := by
  have hq := resonance_q_pos hζ hu
  have hq' := resonance_q_pos hζ hpos.le
  rw [ampSq, ampSq, div_le_div_iff₀ hq hq']
  have hid := peak_identity hpos u
  have hc : 0 ≤ c ^ 2 + peakSq c ζ := by positivity
  nlinarith [mul_nonneg hc (sq_nonneg (u - peakSq c ζ))]

/-- Peak value `f(u*) = 1/(2u* − 2 + 4ζ²)`. -/
@[tmio T, powerlib_foundation] theorem ampSq_peak {c ζ : ℝ} (hζ : ζ ≠ 0) (hpos : 0 < peakSq c ζ) :
    ampSq c ζ (peakSq c ζ) = 1 / (2 * peakSq c ζ - 2 + 4 * ζ ^ 2) := by
  have hq := resonance_q_pos hζ hpos.le
  have hE := peakSq_eq hpos
  have hkey : (1 - peakSq c ζ) ^ 2 + 4 * ζ ^ 2 * peakSq c ζ =
      (c ^ 2 + peakSq c ζ) * (2 * peakSq c ζ - 2 + 4 * ζ ^ 2) := by
    linear_combination -hE
  have hc : 0 < c ^ 2 + peakSq c ζ := by positivity
  have hd : 2 * peakSq c ζ - 2 + 4 * ζ ^ 2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hkey
    linarith
  rw [ampSq, hkey]
  field_simp

/-- Stationarity at (2-24): `f'(u*) = 0`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_ampSq_peak {c ζ : ℝ} (hζ : ζ ≠ 0)
    (hpos : 0 < peakSq c ζ) : HasDerivAt (ampSq c ζ) 0 (peakSq c ζ) := by
  have hq := resonance_q_pos hζ hpos.le
  have hE := peakSq_eq hpos
  set p := peakSq c ζ
  have hn : HasDerivAt (fun u : ℝ => c ^ 2 + u) 1 p := (hasDerivAt_id p).const_add _
  have hd : HasDerivAt (fun u : ℝ => (1 - u) ^ 2 + 4 * ζ ^ 2 * u)
      (2 * (1 - p) * (-1) + 4 * ζ ^ 2) p := by
    have h1 : HasDerivAt (fun u : ℝ => (1 - u) ^ 2) (2 * (1 - p) * (-1)) p := by
      have h := (hasDerivAt_pow 2 (1 - p)).comp p ((hasDerivAt_id p).const_sub 1)
      exact h.congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun u : ℝ => 4 * ζ ^ 2 * u) (4 * ζ ^ 2) p := by
      simpa using (hasDerivAt_id p).const_mul (4 * ζ ^ 2)
    exact h1.add h2
  have h := hn.div hd hq.ne'
  have hzero : (1 * ((1 - p) ^ 2 + 4 * ζ ^ 2 * p) - (c ^ 2 + p) * (2 * (1 - p) * (-1) +
      4 * ζ ^ 2)) / ((1 - p) ^ 2 + 4 * ζ ^ 2 * p) ^ 2 = 0 := by
    rw [div_eq_zero_iff]
    left
    linear_combination -hE
  rw [hzero] at h
  exact h

/-- Amplitude form of (2-24): for `b ≠ 0`, `ζ ≠ 0` and `u* = peakSq (a/b) ζ > 0`, the amplitude
`|H(ν)|` is maximal at `ν = √u*`. -/
@[tmio T, powerlib_foundation] theorem norm_resonanceResp_le_peak {a b ζ : ℝ} (hb : b ≠ 0) (hζ : ζ ≠ 0)
    (hpos : 0 < peakSq (a / b) ζ) (ν : ℝ) :
    ‖resonanceResp a b ζ ν‖ ≤ ‖resonanceResp a b ζ (Real.sqrt (peakSq (a / b) ζ))‖ := by
  have h1 := sq_norm_resonanceResp_eq hb a ζ ν
  have h2 := sq_norm_resonanceResp_eq hb a ζ (Real.sqrt (peakSq (a / b) ζ))
  rw [Real.sq_sqrt hpos.le] at h2
  have hle := ampSq_le_peak hζ hpos (sq_nonneg ν)
  have : ‖resonanceResp a b ζ ν‖ ^ 2 ≤ ‖resonanceResp a b ζ (Real.sqrt (peakSq (a / b) ζ))‖ ^ 2 := by
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hle (sq_nonneg b)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

/-- At `ζ = 0` the resonance frequency ratio is exactly `1`. -/
@[tmio T, powerlib_foundation] theorem peakSq_zero (c : ℝ) : peakSq c 0 = 1 := by
  have h : 1 + 2 * (1 - 2 * (0 : ℝ) ^ 2) * c ^ 2 + c ^ 4 = (c ^ 2 + 1) ^ 2 := by ring
  rw [peakSq, h, Real.sqrt_sq (by positivity)]
  ring

/-- `u* → 1` as `ζ → 0`: a poorly damped mode resonates near its natural frequency. -/
@[tmio T, powerlib_foundation] theorem tendsto_peakSq (c : ℝ) : Tendsto (peakSq c) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (peakSq c) := by
    unfold peakSq
    fun_prop
  rw [← peakSq_zero c]
  exact hc.tendsto 0

/-! ## Low-pass channel (`b = 0`) -/

@[tmio T, powerlib_foundation] theorem norm_resonanceDen_eq (ζ ν : ℝ) :
    ‖resonanceDen ζ ν‖ = Real.sqrt ((1 - ν ^ 2) ^ 2 + (2 * ζ * ν) ^ 2) := by
  rw [Complex.norm_def, normSq_resonanceDen]

/-- Unit gain of the low-pass channel: `|1/D(ν)| ≤ 1` for every `ν` iff `ζ² ≥ 1/2`. -/
@[tmio T, powerlib_foundation] theorem norm_inv_resonanceDen_le_one_iff (ζ : ℝ) :
    (∀ ν : ℝ, ‖(resonanceDen ζ ν)⁻¹‖ ≤ 1) ↔ 1 / 2 ≤ ζ ^ 2 := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    set s := (1 - 2 * ζ ^ 2) / 2 with hs
    have hs0 : 0 < s := by rw [hs]; linarith
    have hs1 : s ≤ 1 / 2 := by rw [hs]; nlinarith [sq_nonneg ζ]
    set ν := Real.sqrt s
    have hν : ν ^ 2 = s := Real.sq_sqrt hs0.le
    have hD : normSq (resonanceDen ζ ν) = 1 - 3 * s ^ 2 := by
      rw [normSq_resonanceDen]
      have : (2 * ζ * ν) ^ 2 = 4 * ζ ^ 2 * ν ^ 2 := by ring
      rw [this, hν, hs]
      ring
    have hlt1 : ‖resonanceDen ζ ν‖ < 1 := by
      rw [Complex.norm_def, hD, Real.sqrt_lt' one_pos]
      nlinarith
    have hpos : 0 < ‖resonanceDen ζ ν‖ := by
      rw [Complex.norm_def, hD]
      apply Real.sqrt_pos.mpr
      nlinarith
    have := h ν
    rw [norm_inv] at this
    have h2 := (one_lt_inv₀ hpos).mpr hlt1
    linarith
  · intro hζ ν
    have hD : 1 ≤ ‖resonanceDen ζ ν‖ := by
      rw [norm_resonanceDen_eq, Real.le_sqrt' one_pos]
      nlinarith [sq_nonneg (ν ^ 2), sq_nonneg ν, mul_nonneg (sq_nonneg ν) (sq_nonneg ν)]
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hD

/-- `|D(ν)| ≥ 2ζ√(1 − ζ²)` for `0 ≤ ζ ≤ 1`: `|D|² = (ν² − (1 − 2ζ²))² + 4ζ²(1 − ζ²)`. -/
@[tmio T, powerlib_foundation] theorem lowpass_lower_bound {ζ : ℝ} (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (ν : ℝ) :
    2 * ζ * Real.sqrt (1 - ζ ^ 2) ≤ ‖resonanceDen ζ ν‖ := by
  have hz : 0 ≤ 1 - ζ ^ 2 := by nlinarith
  have hrw : 2 * ζ * Real.sqrt (1 - ζ ^ 2) = Real.sqrt (4 * ζ ^ 2 * (1 - ζ ^ 2)) := by
    rw [Real.sqrt_mul' _ hz, Real.sqrt_mul' _ (sq_nonneg ζ), Real.sqrt_sq h0,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hrw, norm_resonanceDen_eq]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (ν ^ 2 - (1 - 2 * ζ ^ 2))]

/-- Low-pass peak bound: `|1/D(ν)| ≤ 1/(2ζ√(1 − ζ²))` for `0 < ζ < 1`. -/
@[tmio T, powerlib_foundation] theorem norm_inv_resonanceDen_le {ζ : ℝ} (h0 : 0 < ζ) (h1 : ζ < 1) (ν : ℝ) :
    ‖(resonanceDen ζ ν)⁻¹‖ ≤ 1 / (2 * ζ * Real.sqrt (1 - ζ ^ 2)) := by
  have hz : 0 < 1 - ζ ^ 2 := by nlinarith
  have hpos : 0 < 2 * ζ * Real.sqrt (1 - ζ ^ 2) := by
    have := Real.sqrt_pos.mpr hz
    positivity
  rw [norm_inv, one_div]
  exact inv_anti₀ hpos (lowpass_lower_bound h0.le h1.le ν)

/-- The low-pass peak is attained at `ν = √(1 − 2ζ²)` when `0 < ζ`, `ζ² ≤ 1/2`. -/
@[tmio T, powerlib_foundation] theorem norm_inv_resonanceDen_peak {ζ : ℝ} (h0 : 0 < ζ)
    (h1 : ζ ^ 2 ≤ 1 / 2) :
    ‖(resonanceDen ζ (Real.sqrt (1 - 2 * ζ ^ 2)))⁻¹‖ = 1 / (2 * ζ * Real.sqrt (1 - ζ ^ 2)) := by
  have hs : 0 ≤ 1 - 2 * ζ ^ 2 := by linarith
  have hz : 0 ≤ 1 - ζ ^ 2 := by linarith
  have hν : Real.sqrt (1 - 2 * ζ ^ 2) ^ 2 = 1 - 2 * ζ ^ 2 := Real.sq_sqrt hs
  have hD : ‖resonanceDen ζ (Real.sqrt (1 - 2 * ζ ^ 2))‖ = 2 * ζ * Real.sqrt (1 - ζ ^ 2) := by
    rw [norm_resonanceDen_eq]
    have e1 : (2 * ζ * Real.sqrt (1 - 2 * ζ ^ 2)) ^ 2 = 4 * ζ ^ 2 * (1 - 2 * ζ ^ 2) := by
      rw [mul_pow, hν]; ring
    have e2 : (2 * ζ * Real.sqrt (1 - ζ ^ 2)) ^ 2 = 4 * ζ ^ 2 * (1 - ζ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hz]; ring
    have : (1 - Real.sqrt (1 - 2 * ζ ^ 2) ^ 2) ^ 2 + (2 * ζ * Real.sqrt (1 - 2 * ζ ^ 2)) ^ 2 =
        (2 * ζ * Real.sqrt (1 - ζ ^ 2)) ^ 2 := by
      rw [e1, e2, hν]; ring
    rw [this, Real.sqrt_sq (by positivity)]
  rw [norm_inv, hD, one_div]

/-! ## Band-pass channel (`a = 0`) -/

/-- Band-pass bound: `|jν/D(ν)| ≤ 1/(2ζ)` for `ζ > 0`. -/
@[tmio T, powerlib_foundation] theorem norm_bandpass_le {ζ : ℝ} (h0 : 0 < ζ) (ν : ℝ) :
    ‖(ν : ℂ) * I / resonanceDen ζ ν‖ ≤ 1 / (2 * ζ) := by
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_ne (resonanceDen ζ ν) 0 with hD | hD
  · rw [hD, norm_zero, div_zero]
    positivity
  have hDpos : 0 < ‖resonanceDen ζ ν‖ := norm_pos_iff.mpr hD
  rw [div_le_div_iff₀ hDpos (by positivity), one_mul]
  have him : |(resonanceDen ζ ν).im| ≤ ‖resonanceDen ζ ν‖ := Complex.abs_im_le_norm _
  have : (resonanceDen ζ ν).im = 2 * ζ * ν := by
    simp only [resonanceDen, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ζ)] at him
  linarith

/-- The band-pass peak `1/(2ζ)` is attained at `ν = 1`. -/
@[tmio T, powerlib_foundation] theorem norm_bandpass_one {ζ : ℝ} (h0 : 0 < ζ) :
    ‖((1 : ℝ) : ℂ) * I / resonanceDen ζ 1‖ = 1 / (2 * ζ) := by
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, norm_one,
    norm_resonanceDen_eq]
  have : (1 - (1 : ℝ) ^ 2) ^ 2 + (2 * ζ * 1) ^ 2 = (2 * ζ) ^ 2 := by ring
  rw [this, Real.sqrt_sq (by positivity)]

/-! ## Unbounded peaks as `ζ → 0⁺` -/

/-- The band-pass peak `1/(2ζ)` tends to `+∞` as `ζ → 0⁺`. -/
@[tmio T, powerlib_foundation] theorem tendsto_bandpass_peak :
    Tendsto (fun ζ : ℝ => 1 / (2 * ζ)) (𝓝[>] 0) atTop := by
  have h : Tendsto (fun ζ : ℝ => 2 * ζ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using tendsto_nhdsWithin_of_tendsto_nhds ((continuous_const_mul (2 : ℝ)).tendsto 0)
    · filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact mul_pos two_pos (mem_Ioi.mp hζ)
  exact (tendsto_inv_nhdsGT_zero.comp h).congr fun ζ => by rw [Function.comp_apply, one_div]

/-- The low-pass peak `1/(2ζ√(1 − ζ²))` tends to `+∞` as `ζ → 0⁺`. -/
@[tmio T, powerlib_foundation] theorem tendsto_lowpass_peak :
    Tendsto (fun ζ : ℝ => 1 / (2 * ζ * Real.sqrt (1 - ζ ^ 2))) (𝓝[>] 0) atTop := by
  have h : Tendsto (fun ζ : ℝ => 2 * ζ * Real.sqrt (1 - ζ ^ 2)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun ζ : ℝ => 2 * ζ * Real.sqrt (1 - ζ ^ 2)) := by fun_prop
      simpa using tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto 0)
    · have hlt : ∀ᶠ ζ in 𝓝[>] (0 : ℝ), ζ < 1 :=
        nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
      filter_upwards [self_mem_nhdsWithin, hlt] with ζ hζ hζ1
      have hz : 0 < 1 - ζ ^ 2 := by
        have : ζ ^ 2 < 1 := by nlinarith [mem_Ioi.mp hζ]
        linarith
      have := Real.sqrt_pos.mpr hz
      exact mul_pos (mul_pos two_pos (mem_Ioi.mp hζ)) this
  exact (tendsto_inv_nhdsGT_zero.comp h).congr fun ζ => by rw [Function.comp_apply, one_div]

end powerlib.LTI
