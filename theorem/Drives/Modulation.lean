import dependencies.Mathlib
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import theorem.Transform.SpaceVector

/-! # Two-level inverter modulation limits (foundation)

Model: ideal two-level three-phase inverter, DC link `V_dc > 0`; each leg voltage (with respect to
the negative rail, averaged over a switching period) lies in `[0, V_dc]`; the output space vector is
the amplitude-invariant Clarke vector of the three leg voltages (`Transform.SpaceVector.clarke`).
Dead time, device drops, ripple and DC-link variation are excluded.

Contents.
* `linearRange_projection_le`: for **any** leg voltages in `[0, V_dc]` (any PWM pattern, any
  zero-sequence injection) the projection of the output vector on the hexagon apothem
  direction `e^{jπ/6}` is at most `V_dc/√3`.
* `svpwm_linearRange`: conversely every vector with `|u| ≤ V_dc/√3` is produced by some leg
  voltages in `[0, V_dc]` (min–max zero-sequence injection). Together:
  `V_max = V_dc/√3` is the largest circle (`maxCircle_radius_le`), the bound used for
  `|u| ≤ V_dc/√3` in the FOC voltage ellipse and CCS-MPC.
* SPWM (sinusoidal legs without zero-sequence injection): the legs stay in `[0, V_dc]` iff the
  phase peak is `≤ V_dc/2` (`spwm_legs_mem_iff`).
* Six-step: the fundamental Fourier coefficient of a leg switching between `0` and `V_dc` with
  50 % duty is `2V_dc/π` (`sixStep_fundamental`), and the line-to-line fundamental is `√3`
  times a leg fundamental (`sin_sub_sin_two_pi_div_three`).
* Utilisation (line-to-line rms / `V_dc`): SPWM `√6/4 ≈ 0.612`, SVPWM `1/√2 ≈ 0.707`, six-step
  `√6/π ≈ 0.780` (`utilisation_bounds`).

Source: work-sync theory/T-scalar-vf-control.md §1.8 (modulation utilisation),
theory/T-field-oriented-control.md §1.7 (`V_max = V_dc/√3`),
theory/T-predictive-machine-control.md §1.5 (`|u| ≤ V_dc/√3`).
-/

noncomputable section
namespace powerlib.Drives.Modulation

open Complex
open powerlib.Transform.SpaceVector

/-- Projection of a space vector on the unit vector `e^{jπ/6} = (√3/2, 1/2)`. -/
def apothemProjection (u : ℂ) : ℝ := Real.sqrt 3 / 2 * u.re + 1 / 2 * u.im

@[powerlib_foundation] theorem apothemProjection_clarke (xa xb xc : ℝ) :
    apothemProjection (clarke xa xb xc) = Real.sqrt 3 / 3 * (xa - xc) := by
  simp only [apothemProjection, clarke_re, clarke_im]
  ring

/-- No leg pattern in `[0, V_dc]` produces a vector beyond `V_dc/√3` in the apothem
direction. -/
@[powerlib_foundation] theorem linearRange_projection_le (V xa xb xc : ℝ)
    (ha : xa ∈ Set.Icc 0 V) (hc : xc ∈ Set.Icc 0 V) :
    apothemProjection (clarke xa xb xc) ≤ V / Real.sqrt 3 := by
  rw [apothemProjection_clarke]
  have h3 : 0 < Real.sqrt 3 := by positivity
  have hs : Real.sqrt 3 / 3 = 1 / Real.sqrt 3 := by
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [hs, div_mul_eq_mul_div, one_mul]
  apply div_le_div_of_nonneg_right _ h3.le
  linarith [ha.2, hc.1]

/-- Inverse Clarke transform (zero-sequence free phase voltages of a space vector). -/
def invClarke (u : ℂ) : ℝ × ℝ × ℝ :=
  (u.re, -u.re / 2 + Real.sqrt 3 / 2 * u.im, -u.re / 2 - Real.sqrt 3 / 2 * u.im)

@[powerlib_foundation] theorem clarke_invClarke (u : ℂ) :
    clarke (invClarke u).1 (invClarke u).2.1 (invClarke u).2.2 = u := by
  have h3 := Transform.sqrt3_sq
  apply Complex.ext
  · simp only [clarke_re, invClarke]; ring
  · simp only [clarke_im, invClarke]
    linear_combination (u.im / 3) * h3

/-- Pairwise phase differences are bounded by `√3 |u|` (line-to-line peak). -/
@[powerlib_foundation] theorem invClarke_diff_le (u : ℂ) :
    |(invClarke u).1 - (invClarke u).2.1| ≤ Real.sqrt 3 * ‖u‖ ∧
      |(invClarke u).2.1 - (invClarke u).2.2| ≤ Real.sqrt 3 * ‖u‖ ∧
      |(invClarke u).2.2 - (invClarke u).1| ≤ Real.sqrt 3 * ‖u‖ := by
  have h3 := Transform.sqrt3_sq
  have h3p : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hn : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have key : ∀ p : ℝ, p ^ 2 ≤ 3 * (u.re ^ 2 + u.im ^ 2) → |p| ≤ Real.sqrt 3 * ‖u‖ := by
    intro p hp
    rw [← hn] at hp
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hp
  simp only [invClarke]
  refine ⟨key _ ?_, key _ ?_, key _ ?_⟩
  · have e : 3 * (u.re ^ 2 + u.im ^ 2) - (u.re - (-u.re / 2 + Real.sqrt 3 / 2 * u.im)) ^ 2 =
        3 / 4 * (u.re + Real.sqrt 3 * u.im) ^ 2 := by
      linear_combination (-u.im ^ 2) * h3
    nlinarith [sq_nonneg (u.re + Real.sqrt 3 * u.im)]
  · have e : 3 * (u.re ^ 2 + u.im ^ 2) -
        (-u.re / 2 + Real.sqrt 3 / 2 * u.im - (-u.re / 2 - Real.sqrt 3 / 2 * u.im)) ^ 2 =
        3 * u.re ^ 2 := by
      linear_combination (-u.im ^ 2) * h3
    nlinarith [sq_nonneg u.re]
  · have e : 3 * (u.re ^ 2 + u.im ^ 2) - (-u.re / 2 - Real.sqrt 3 / 2 * u.im - u.re) ^ 2 =
        3 / 4 * (u.re - Real.sqrt 3 * u.im) ^ 2 := by
      linear_combination (-u.im ^ 2) * h3
    nlinarith [sq_nonneg (u.re - Real.sqrt 3 * u.im)]

/-- **SVPWM linear range.** Every vector with `|u| ≤ V_dc/√3` is the space vector of some
leg voltages in `[0, V_dc]`. -/
@[powerlib_foundation] theorem svpwm_linearRange (V : ℝ) (u : ℂ) (hu : ‖u‖ ≤ V / Real.sqrt 3) :
    ∃ xa xb xc : ℝ, xa ∈ Set.Icc 0 V ∧ xb ∈ Set.Icc 0 V ∧ xc ∈ Set.Icc 0 V ∧
      clarke xa xb xc = u := by
  obtain ⟨d1, d2, d3⟩ := invClarke_diff_le u
  set a := (invClarke u).1
  set b := (invClarke u).2.1
  set c := (invClarke u).2.2
  have h3 : 0 < Real.sqrt 3 := by positivity
  have hV : Real.sqrt 3 * ‖u‖ ≤ V := by
    rw [le_div_iff₀ h3] at hu; linarith
  set m := min (min a b) c
  have hm : m = a ∨ m = b ∨ m = c := by
    rcases min_choice (min a b) c with h | h
    · rcases min_choice a b with h' | h'
      · left; rw [show m = min (min a b) c from rfl, h, h']
      · right; left; rw [show m = min (min a b) c from rfl, h, h']
    · right; right; exact h
  have hma : m ≤ a := (min_le_left _ _).trans (min_le_left _ _)
  have hmb : m ≤ b := (min_le_left _ _).trans (min_le_right _ _)
  have hmc : m ≤ c := min_le_right _ _
  have hab := abs_le.mp d1
  have hbc := abs_le.mp d2
  have hca := abs_le.mp d3
  refine ⟨a - m, b - m, c - m, ⟨by linarith, ?_⟩, ⟨by linarith, ?_⟩, ⟨by linarith, ?_⟩, ?_⟩
  · rcases hm with h | h | h <;> rw [h] <;> linarith
  · rcases hm with h | h | h <;> rw [h] <;> linarith
  · rcases hm with h | h | h <;> rw [h] <;> linarith
  · have := clarke_add_const a b c (-m)
    simp only [← sub_eq_add_neg] at this
    rw [this]
    exact clarke_invClarke u

/-- `V_dc/√3` is the largest synthesizable circle: if every vector of modulus `ρ ≥ 0` can be
produced by leg voltages in `[0, V_dc]`, then `ρ ≤ V_dc/√3`. -/
@[powerlib_foundation] theorem maxCircle_radius_le (V ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ u : ℂ, ‖u‖ = ρ → ∃ xa xb xc : ℝ, xa ∈ Set.Icc 0 V ∧ xb ∈ Set.Icc 0 V ∧
      xc ∈ Set.Icc 0 V ∧ clarke xa xb xc = u) :
    ρ ≤ V / Real.sqrt 3 := by
  set u : ℂ := ⟨ρ * (Real.sqrt 3 / 2), ρ * (1 / 2)⟩
  have h3 := Transform.sqrt3_sq
  have hu : ‖u‖ = ρ := by
    have hsq : ‖u‖ ^ 2 = ρ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [u]
      linear_combination (ρ ^ 2 / 4) * h3
    have := (pow_left_inj₀ (norm_nonneg u) hρ (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
    exact this
  obtain ⟨xa, xb, xc, ha, _, hc, hcl⟩ := h u hu
  have hb := linearRange_projection_le V xa xb xc ha hc
  rw [hcl] at hb
  have : apothemProjection u = ρ := by
    simp only [apothemProjection, u]
    linear_combination (ρ / 4) * h3
  linarith

/-- SPWM: sinusoidal legs `V/2 + M cos(θ − 2πk/3)` stay in `[0, V]` for every angle iff
`M ≤ V/2` (for `0 ≤ M`); their space vector is `M e^{jθ}`. -/
@[powerlib_foundation] theorem spwm_legs_mem_iff (V M : ℝ) (hM : 0 ≤ M) :
    (∀ θ : ℝ, V / 2 + M * Real.cos θ ∈ Set.Icc 0 V) ↔ M ≤ V / 2 := by
  constructor
  · intro h
    have := (h 0).2
    rw [Real.cos_zero] at this
    linarith
  · intro h θ
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    constructor <;> nlinarith

@[powerlib_foundation] theorem spwm_spaceVector (V M θ : ℝ) :
    clarke (V / 2 + M * Real.cos θ) (V / 2 + M * Real.cos (θ - 2 * Real.pi / 3))
      (V / 2 + M * Real.cos (θ + 2 * Real.pi / 3)) = ⟨M * Real.cos θ, M * Real.sin θ⟩ := by
  have := clarke_add_const (M * Real.cos θ) (M * Real.cos (θ - 2 * Real.pi / 3))
    (M * Real.cos (θ + 2 * Real.pi / 3)) (V / 2)
  rw [show V / 2 + M * Real.cos θ = M * Real.cos θ + V / 2 by ring,
    show V / 2 + M * Real.cos (θ - 2 * Real.pi / 3) = M * Real.cos (θ - 2 * Real.pi / 3) + V / 2 by ring,
    show V / 2 + M * Real.cos (θ + 2 * Real.pi / 3) = M * Real.cos (θ + 2 * Real.pi / 3) + V / 2 by ring,
    this, clarke_balanced]

/-- Six-step leg: `V_dc` on `[0, π)`, `0` on `[π, 2π)`. Its fundamental sine coefficient
`(1/π) ∫₀^{2π} v(θ) sin θ dθ` equals `2V_dc/π`. -/
@[powerlib_foundation] theorem sixStep_fundamental (V : ℝ) :
    (1 / Real.pi) * ((∫ θ in (0 : ℝ)..Real.pi, V * Real.sin θ) +
      ∫ θ in Real.pi..(2 * Real.pi), (0 : ℝ) * Real.sin θ) = 2 * V / Real.pi := by
  rw [intervalIntegral.integral_const_mul, integral_sin]
  simp only [Real.cos_zero, Real.cos_pi, zero_mul, intervalIntegral.integral_zero]
  ring

/-- Line-to-line fundamental = `√3` × leg fundamental: `sin θ − sin(θ − 2π/3) = √3 cos(θ − π/3)`. -/
@[powerlib_foundation] theorem sin_sub_sin_two_pi_div_three (θ : ℝ) :
    Real.sin θ - Real.sin (θ - 2 * Real.pi / 3) = Real.sqrt 3 * Real.cos (θ - Real.pi / 3) := by
  have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; ring
  have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [Real.sin_sub, Real.cos_sub, hc, hs, Real.cos_pi_div_three, Real.sin_pi_div_three]
  have h3 := Transform.sqrt3_sq
  linear_combination (-Real.sin θ / 2) * h3

/-- Utilisation factors `V_LL,rms / V_dc`: SPWM `√(3/2)·(1/2) = √6/4 ∈ (0.612, 0.613)`,
SVPWM `√(3/2)·(1/√3) = 1/√2 ∈ (0.707, 0.708)`, six-step `√3·(2/π)/√2 = √6/π ∈ (0.779, 0.780)`. -/
@[powerlib_foundation] theorem utilisation_bounds :
    (0.612 < Real.sqrt 6 / 4 ∧ Real.sqrt 6 / 4 < 0.613) ∧
      (0.707 < 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 0.708) ∧
      (0.779 < Real.sqrt 6 / Real.pi ∧ Real.sqrt 6 / Real.pi < 0.780) := by
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h6p : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2p : 0 < Real.sqrt 2 := by positivity
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hs6a : 2.4494 < Real.sqrt 6 := by nlinarith
  have hs6b : Real.sqrt 6 < 2.4495 := by nlinarith
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ h2p]; nlinarith
  · rw [div_lt_iff₀ h2p]; nlinarith
  · rw [lt_div_iff₀ (by linarith)]; nlinarith
  · rw [div_lt_iff₀ (by linarith)]; nlinarith

/-- The three utilisation constants are the stated combinations. -/
@[powerlib_foundation] theorem utilisation_values :
    Real.sqrt (3 / 2) * (1 / 2) = Real.sqrt 6 / 4 ∧
      Real.sqrt (3 / 2) * (1 / Real.sqrt 3) = 1 / Real.sqrt 2 ∧
      Real.sqrt 3 * (2 / Real.pi) / Real.sqrt 2 = Real.sqrt 6 / Real.pi := by
  have e1 : Real.sqrt (3 / 2) = Real.sqrt 6 / 2 := by
    rw [show (3 / 2 : ℝ) = 6 / 4 by norm_num, Real.sqrt_div' 6 (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2p : 0 < Real.sqrt 2 := by positivity
  have h3p : 0 < Real.sqrt 3 := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨by rw [e1]; ring, ?_, ?_⟩
  · rw [e1, e6]
    field_simp
    nlinarith
  · rw [e6]
    field_simp
    nlinarith

end powerlib.Drives.Modulation
