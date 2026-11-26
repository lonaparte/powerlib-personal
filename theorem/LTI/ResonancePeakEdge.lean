import theorem.LTI.SecondOrderResonance

/-! # The resonance maximizer when TR-110's (2-24) gives no positive frequency

The frequency of maximum amplitude of the normalized second-order phasor
`H(ν) = (a + jνb)/((1 − ν²) + j2ζν)` is (2-24), `ν_r² = u* = √(1 + 2(1 − 2ζ²)c² + c⁴) − c²`,
`c = a/b`, whenever `u* > 0` (`LTI.ampSq_le_peak`). This module closes the remaining case
`u* ≤ 0`: there is no interior resonance, the squared amplitude `f(u) = (c² + u)/q(u)` is
non-increasing on `u ≥ 0` and its maximum is at `u = 0` (`ν = 0`, the static gain `|a|`).
Together, the maximizer of the amplitude over `ν ≥ 0` is `ν = √(max(u*, 0))` for every `c` and
every `ζ ≠ 0`.

Scope.
* Real parameters `a, b, c, ζ` and `u = ν² ≥ 0`; pure algebra of the explicit rational function
  `LTI.ampSq` of `theorem/LTI/SecondOrderResonance.lean` (`q(u) = (1 − u)² + 4ζ²u`). The case
  `b = 0` (low-pass channel) is treated there separately. No model family.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §2.2.2, eqs. (2-22) and
(2-24) (the resonance frequency ratio, defined by the report only when the radicand expression
is positive).

Corrections and sharpenings.
* (2-24) is a resonance only when `u* > 0`, i.e. exactly when `1 + 2(1 − 2ζ²)c² > 0`
  (`peakSq_nonpos_iff`); otherwise the amplitude decreases from `ν = 0` and the "resonance
  frequency" of the report does not exist (`ampSq_antitoneOn`, `norm_resonanceResp_antitoneOn`).

Results.
* `peakSq_nonpos_iff` — `u* ≤ 0 ↔ 1 + 2(1 − 2ζ²)c² ≤ 0`; `ne_zero_of_peakSq_nonpos` — then
  `ζ ≠ 0` (since `u* = 1` at `ζ = 0`).
* `ampSq_cross` — `(c² + u) q(v) − (c² + v) q(u) = (v − u)(uv + c²(u + v) − (1 + 2(1 − 2ζ²)c²))`.
* `ampSq_antitoneOn`, `ampSq_zero`, `ampSq_le_zero` — for `u* ≤ 0`: `f` is non-increasing on
  `[0, ∞)`, `f(0) = c²` and `f(u) ≤ f(0)` for all `u ≥ 0`.
* `ampSq_le_max` — for every `c` and `ζ ≠ 0`: `f(u) ≤ f(max(u*, 0))` for all `u ≥ 0`
  (with `LTI.ampSq_le_peak` for `u* > 0`).
* `norm_resonanceResp_antitoneOn`, `norm_resonanceResp_le_max` — amplitude form: for `b ≠ 0` and
  `u* ≤ 0` the amplitude `|H(ν)|` is non-increasing on `ν ≥ 0`; for `b ≠ 0`, `ζ ≠ 0` it is
  maximal at `ν = √(max(u*, 0))`.
-/

noncomputable section
namespace powerlib.LTI
open Set

/-- `u* ≤ 0` exactly when `1 + 2(1 − 2ζ²)c² ≤ 0`. -/
@[tmio T, powerlib_foundation] theorem peakSq_nonpos_iff (c ζ : ℝ) :
    peakSq c ζ ≤ 0 ↔ 1 + 2 * (1 - 2 * ζ ^ 2) * c ^ 2 ≤ 0 := by
  rw [peakSq, sub_nonpos, Real.sqrt_le_left (sq_nonneg c)]
  constructor <;> intro h <;> nlinarith

/-- With `u* ≤ 0` the damping ratio is nonzero (at `ζ = 0`, `u* = 1`). -/
@[tmio T, powerlib_foundation] theorem ne_zero_of_peakSq_nonpos {c ζ : ℝ}
    (h : peakSq c ζ ≤ 0) : ζ ≠ 0 := by
  rintro rfl
  rw [peakSq_zero] at h
  norm_num at h

/-- The cross-multiplied difference of two amplitude values:
`(c² + u) q(v) − (c² + v) q(u) = (v − u)(uv + c²(u + v) − (1 + 2(1 − 2ζ²)c²))`. -/
@[tmio T, powerlib_foundation] theorem ampSq_cross (c ζ u v : ℝ) :
    (c ^ 2 + u) * ((1 - v) ^ 2 + 4 * ζ ^ 2 * v) - (c ^ 2 + v) * ((1 - u) ^ 2 + 4 * ζ ^ 2 * u) =
      (v - u) * (u * v + c ^ 2 * (u + v) - (1 + 2 * (1 - 2 * ζ ^ 2) * c ^ 2)) := by
  ring

/-- For `u* ≤ 0` the squared amplitude is non-increasing on `u ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem ampSq_antitoneOn {c ζ : ℝ} (h : peakSq c ζ ≤ 0) :
    AntitoneOn (ampSq c ζ) (Ici 0) := by
  have hζ := ne_zero_of_peakSq_nonpos h
  have hK := (peakSq_nonpos_iff c ζ).mp h
  intro u hu v hv huv
  have hu' : 0 ≤ u := hu
  have hv' : 0 ≤ v := hv
  have hqu := resonance_q_pos hζ hu'
  have hqv := resonance_q_pos hζ hv'
  rw [ampSq, ampSq, div_le_div_iff₀ hqv hqu]
  have hid := ampSq_cross c ζ u v
  have hE : 0 ≤ u * v + c ^ 2 * (u + v) - (1 + 2 * (1 - 2 * ζ ^ 2) * c ^ 2) := by
    have : 0 ≤ u * v := mul_nonneg hu' hv'
    have : 0 ≤ c ^ 2 * (u + v) := mul_nonneg (sq_nonneg c) (by linarith)
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr huv) hE]

/-- `f(0) = c²` (the static gain squared over `b²`). -/
@[tmio T, powerlib_foundation] theorem ampSq_zero (c ζ : ℝ) : ampSq c ζ 0 = c ^ 2 := by
  simp [ampSq]

/-- For `u* ≤ 0` the maximum of the squared amplitude over `u ≥ 0` is at `u = 0`. -/
@[tmio T, powerlib_foundation] theorem ampSq_le_zero {c ζ : ℝ} (h : peakSq c ζ ≤ 0) {u : ℝ}
    (hu : 0 ≤ u) : ampSq c ζ u ≤ ampSq c ζ 0 :=
  ampSq_antitoneOn h (Set.mem_Ici.mpr le_rfl) hu hu

/-- The maximizer for every `c` and `ζ ≠ 0`: `f(u) ≤ f(max(u*, 0))` for all `u ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem ampSq_le_max {c ζ : ℝ} (hζ : ζ ≠ 0) {u : ℝ}
    (hu : 0 ≤ u) : ampSq c ζ u ≤ ampSq c ζ (max (peakSq c ζ) 0) := by
  rcases lt_or_ge 0 (peakSq c ζ) with hpos | hneg
  · rw [max_eq_left hpos.le]
    exact ampSq_le_peak hζ hpos hu
  · rw [max_eq_right hneg]
    exact ampSq_le_zero hneg hu

/-- Amplitude form of the edge case: for `b ≠ 0` and `u* = peakSq (a/b) ζ ≤ 0` the amplitude
`|H(ν)|` is non-increasing on `ν ≥ 0` (maximal at `ν = 0`, where `|H(0)| = |a|`). -/
@[tmio T, powerlib_foundation] theorem norm_resonanceResp_antitoneOn {a b ζ : ℝ} (hb : b ≠ 0)
    (h : peakSq (a / b) ζ ≤ 0) :
    AntitoneOn (fun ν => ‖resonanceResp a b ζ ν‖) (Ici 0) := by
  intro μ hμ ν hν hμν
  have hμ' : 0 ≤ μ := hμ
  have hsq : μ ^ 2 ≤ ν ^ 2 := pow_le_pow_left₀ hμ' hμν 2
  have hle := ampSq_antitoneOn h (sq_nonneg μ) (sq_nonneg ν) hsq
  have h2 : ‖resonanceResp a b ζ ν‖ ^ 2 ≤ ‖resonanceResp a b ζ μ‖ ^ 2 := by
    rw [sq_norm_resonanceResp_eq hb, sq_norm_resonanceResp_eq hb]
    exact mul_le_mul_of_nonneg_left hle (sq_nonneg b)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- The amplitude maximizer for every `a`, `b ≠ 0` and `ζ ≠ 0`: `|H(ν)| ≤ |H(√(max(u*, 0)))|`
for every `ν`, `u* = peakSq (a/b) ζ`. -/
@[tmio T, powerlib_foundation] theorem norm_resonanceResp_le_max {a b ζ : ℝ} (hb : b ≠ 0)
    (hζ : ζ ≠ 0) (ν : ℝ) :
    ‖resonanceResp a b ζ ν‖ ≤
      ‖resonanceResp a b ζ (Real.sqrt (max (peakSq (a / b) ζ) 0))‖ := by
  have h1 := sq_norm_resonanceResp_eq hb a ζ ν
  have h2 := sq_norm_resonanceResp_eq hb a ζ (Real.sqrt (max (peakSq (a / b) ζ) 0))
  rw [Real.sq_sqrt (le_max_right _ _)] at h2
  have hle := ampSq_le_max (c := a / b) hζ (sq_nonneg ν)
  have : ‖resonanceResp a b ζ ν‖ ^ 2 ≤
      ‖resonanceResp a b ζ (Real.sqrt (max (peakSq (a / b) ζ) 0))‖ ^ 2 := by
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hle (sq_nonneg b)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

end powerlib.LTI
