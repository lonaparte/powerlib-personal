import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import theorem.SpecialFunctions.BesselI

/-! # Bessel surface impedance of a solid conductor: low- and high-frequency limits

Static special-function analysis of Schelkunoff's surface impedance of a solid round conductor:
the DC resistance plus internal inductance at low frequency and the skin-effect surface impedance
at high frequency.

Model boundary.
* A straight solid round conductor of radius `r > 0` and resistivity `ρ ≥ 0`, axially symmetric
  current, quasi-static field inside the conductor (displacement current neglected), sinusoidal
  steady state at angular frequency `ω`; the propagation constant of the diffusion equation is
  `m = √(jωμ/ρ)` (any complex `m`; the physical one is `m = (1 + j)√(ωμ/(2ρ))`, argument
  `π/4`).
* The per-unit-length surface (internal) impedance is Schelkunoff's
  `Z(m) = (ρ m/(2π r)) I₀(m r)/I₁(m r)` (`coreImpedance`). No proximity effect, no earth
  return, no insulation or screen.
* Modified Bessel functions: the power series `SpecialFunctions.besselI0`,
  `SpecialFunctions.besselI1` (through `besselSeries0`, `besselSeries1` at `w = z²/4`), their
  small-argument bounds, integral representation, Laplace estimates and the large-argument
  limit `I₀(z)/I₁(z) → 1` in a sector are in `theorem/SpecialFunctions/BesselI.lean`.

Source: work-sync `theory/T-cable.md` §1.2.1 ("严格解是 Bessel 比值
`ρ m/(2π r_c) · I₀(m r_c)/I₁(m r_c)` … 低频退化为直流电阻 `ρ_c/(π r_c²)` + 内电感 `μ₀/(8π)`；
高频退化为趋肤表面阻抗 `ρ_c m/(2π r_c)`"), §1.2.2 (tubular conductors).

Results (foundation).
* `coreImpedance_eq`: `Z(m) = (ρ/(π r²)) f₀(w)/f₁(w)`, `w = (m r)²/4` (`m ≠ 0`).
* **Low-frequency limit**: `coreImpedance_lowFrequency_le`
  (`‖Z − ρ/(π r²) − ρ m²/(8π)‖ ≤ (3ρ r²/(8π)) ‖m‖⁴` for `‖m‖ r ≤ 1`), `coreImpedance_isBigO`
  (`Z = ρ/(π r²) + ρ m²/(8π) + O(m⁴)` as `m → 0`), `coreImpedance_tendsto_dc`
  (`Z → ρ/(π r²)`), and `internalInductance`: with `m² = jωμ/ρ` the second-order term is
  `jω μ/(8π)` — the note's DC resistance plus internal inductance `μ/(8π)` per unit length,
  exactly.
* **High-frequency (skin-effect) limit**: `coreImpedance_div_surface`
  (`Z(m)/(ρ m/(2π r)) = I₀(mr)/I₁(mr)`), `coreImpedance_tendsto_surface` (along
  `m = (1 + i)s`, `s → ∞`: `Z/(ρ m/(2π r)) → 1`), `coreImpedance_sub_surface_isBigO`
  (`Z(m) = ρ m/(2π r) + O(1)` along the same ray), `coreImpedance_tendsto_surface_omega` (the
  same limit as `ω → ∞` for `m(ω) = (1 + i)√(ωμ/(2ρ))`, with `m² = jωμ/ρ` by
  `one_add_I_mul_sqrt_sq`).
* Tubular conductors (§1.2.2): the exact (Schelkunoff) tubular-conductor impedances need the
  second-kind functions `K₀`, `K₁` in addition to `I₀`, `I₁`; they are defined (integral
  representation), with their small/large-argument behaviour, derivatives and the Wronskian
  `I₀K₁ + I₁K₀ = 1/z`, in `theorem/SpecialFunctions/BesselK.lean`. The exact inner, outer and
  transfer impedances, their low-frequency (DC resistance) and high-frequency (surface
  impedance, complete screening) limits and their comparison with the Wedepohl–Wilcox
  `coth`/`csch` formulas of `theorem/Line/Cable.lean` are in `theorem/Line/CableSchelkunoff.lean`.

Family and connection conclusions.
* None: static special-function analysis; no model family.
-/

noncomputable section
namespace powerlib.Line.CableBessel
open Filter Topology Asymptotics
open scoped Nat
open powerlib.SpecialFunctions (besselI0 besselI1 besselSeries0 besselSeries1 besselRatio_sub_le
  besselI0_div_besselI1_sub_one_le tendsto_besselI0_div_besselI1 one_add_I_mul_re
  norm_one_add_I_mul_le)

/-- Schelkunoff surface impedance of a solid round conductor of radius `r` and resistivity `ρ`,
per unit length: `Z = (ρ m/(2π r)) I₀(m r)/I₁(m r)` with `m = √(jωμ/ρ)` (T-cable §1.2.1). -/
def coreImpedance (ρ r : ℝ) (m : ℂ) : ℂ :=
  (ρ : ℂ) * m / (2 * Real.pi * r) * (besselI0 (m * r) / besselI1 (m * r))

/-- With `w = (m r)²/4`: `Z = (ρ/(π r²)) · I₀-series(w)/I₁-series(w)`. -/
@[tmio M, powerlib_foundation] theorem coreImpedance_eq {ρ r : ℝ} (hr : r ≠ 0) {m : ℂ} (hm : m ≠ 0) :
    coreImpedance ρ r m = ((ρ / (Real.pi * r ^ 2) : ℝ) : ℂ) *
      (besselSeries0 ((m * r) ^ 2 / 4) / besselSeries1 ((m * r) ^ 2 / 4)) := by
  unfold coreImpedance besselI0 besselI1
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h1 : besselSeries1 ((m * r) ^ 2 / 4) = 0
  · simp [h1]
  · push_cast
    field_simp

/-- **Low-frequency expansion of the Bessel surface impedance**, explicit remainder: for `ρ ≥ 0`,
`r > 0`, `m ≠ 0` with `‖m‖ r ≤ 1`,
`‖Z(m) − ρ/(π r²) − ρ m²/(8π)‖ ≤ (3 ρ r²/(8π)) ‖m‖⁴`. -/
@[powerlib_foundation] theorem coreImpedance_lowFrequency_le {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : 0 < r)
    {m : ℂ} (hm : m ≠ 0) (hmr : ‖m‖ * r ≤ 1) :
    ‖coreImpedance ρ r m - ((ρ / (Real.pi * r ^ 2) : ℝ) : ℂ) - (ρ : ℂ) * m ^ 2 / (8 * Real.pi)‖ ≤
      3 * ρ * r ^ 2 / (8 * Real.pi) * ‖m‖ ^ 4 := by
  rw [coreImpedance_eq hr.ne' hm]
  set w : ℂ := (m * r) ^ 2 / 4 with hwdef
  have hnw : ‖w‖ = (‖m‖ * r) ^ 2 / 4 := by
    rw [hwdef, norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      show ‖(4 : ℂ)‖ = 4 by simp]
  have hw : ‖w‖ ≤ 1 / 4 := by
    rw [hnw]
    have : 0 ≤ ‖m‖ * r := by positivity
    nlinarith
  have hR : 0 ≤ ρ / (Real.pi * r ^ 2) := by positivity
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e : ((ρ / (Real.pi * r ^ 2) : ℝ) : ℂ) * (besselSeries0 w / besselSeries1 w) -
      ((ρ / (Real.pi * r ^ 2) : ℝ) : ℂ) - (ρ : ℂ) * m ^ 2 / (8 * Real.pi) =
      ((ρ / (Real.pi * r ^ 2) : ℝ) : ℂ) * (besselSeries0 w / besselSeries1 w - 1 - w / 2) := by
    rw [hwdef]; push_cast; field_simp; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  calc ρ / (Real.pi * r ^ 2) * ‖besselSeries0 w / besselSeries1 w - 1 - w / 2‖ ≤
        ρ / (Real.pi * r ^ 2) * (6 * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (besselRatio_sub_le hw) hR
    _ = 3 * ρ * r ^ 2 / (8 * Real.pi) * ‖m‖ ^ 4 := by
        rw [hnw]; field_simp; ring

/-- **Low-frequency limit (Bessel)**: `Z(m) − ρ/(π r²) − ρ m²/(8π) = O(m⁴)` as `m → 0`. -/
@[powerlib_foundation] theorem coreImpedance_isBigO {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : 0 < r) :
    (fun m => coreImpedance ρ r m - ((ρ / (Real.pi * r ^ 2) : ℝ) : ℂ) -
      (ρ : ℂ) * m ^ 2 / (8 * Real.pi)) =O[𝓝[≠] 0] (fun m : ℂ => m ^ 4) := by
  refine IsBigO.of_bound (3 * ρ * r ^ 2 / (8 * Real.pi)) ?_
  have hball : ∀ᶠ m in 𝓝[≠] (0 : ℂ), ‖m‖ * r ≤ 1 := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (inv_pos.mpr hr)] with m hm
    rw [Metric.mem_closedBall, dist_zero_right] at hm
    rw [← le_div_iff₀ hr, one_div]
    exact hm
  filter_upwards [self_mem_nhdsWithin, hball] with m (hm : m ≠ 0) hmr
  rw [norm_pow]
  exact coreImpedance_lowFrequency_le hρ hr hm hmr

/-- **DC limit (Bessel)**: `Z(m) → ρ/(π r²)` (the DC resistance) as `m → 0`. -/
@[powerlib_foundation] theorem coreImpedance_tendsto_dc {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : 0 < r) :
    Tendsto (coreImpedance ρ r) (𝓝[≠] 0) (𝓝 ((ρ / (Real.pi * r ^ 2) : ℝ) : ℂ)) := by
  have h4 : Tendsto (fun m : ℂ => m ^ 4) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun m : ℂ => m ^ 4) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_pow 4).tendsto (0 : ℂ)
    exact this.mono_left nhdsWithin_le_nhds
  have hrem := (coreImpedance_isBigO hρ hr).trans_tendsto h4
  have hsq : Tendsto (fun m : ℂ => (ρ : ℂ) * m ^ 2 / (8 * Real.pi)) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun m : ℂ => (ρ : ℂ) * m ^ 2 / (8 * Real.pi)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun m : ℂ => (ρ : ℂ) * m ^ 2 / (8 * Real.pi) := by fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  have := (hrem.add hsq).add_const (((ρ / (Real.pi * r ^ 2) : ℝ) : ℂ))
  simp only [zero_add] at this
  refine this.congr fun m => ?_
  ring

/-- With `m² = jωμ/ρ` the second-order term is `jω μ/(8π)`: the internal inductance per unit
length of a solid round conductor, independent of its radius and resistivity. -/
@[powerlib_foundation] theorem internalInductance {ρ ω μ : ℝ} (hρ : ρ ≠ 0) {m : ℂ}
    (hm : m ^ 2 = Complex.I * ω * μ / ρ) :
    (ρ : ℂ) * m ^ 2 / (8 * Real.pi) = Complex.I * ω * ((μ / (8 * Real.pi) : ℝ) : ℂ) := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hm]; push_cast; field_simp


open MeasureTheory Set intervalIntegral

/-! ## High frequency: the skin-effect limit -/

/-- With `m = (1 + i)s` (`s = 1/δ`, `δ` the skin depth) the surface impedance factorizes:
`Z(m) = (ρ m/(2π r)) · I₀(m r)/I₁(m r)`; the ratio `Z/(ρ m/(2π r))` is `I₀(mr)/I₁(mr)`. -/
@[powerlib_foundation] theorem coreImpedance_div_surface {ρ r : ℝ} (hρ : ρ ≠ 0) (hr : 0 < r)
    {m : ℂ} (hm : m ≠ 0) :
    coreImpedance ρ r m / ((ρ : ℂ) * m / (2 * Real.pi * r)) =
      besselI0 (m * r) / besselI1 (m * r) := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold coreImpedance
  rw [mul_div_cancel_left₀]
  exact div_ne_zero (mul_ne_zero hρ' hm) (by simp [hπ, hr'])

/-- **High-frequency (skin-effect) limit (Bessel)**: along the physical ray `m = (1 + i)s`,
`s → ∞`, `Z(m)/(ρ m/(2π r)) → 1` — the surface impedance of the note. -/
@[powerlib_foundation] theorem coreImpedance_tendsto_surface {ρ r : ℝ} (hρ : ρ ≠ 0) (hr : 0 < r) :
    Tendsto (fun s : ℝ => coreImpedance ρ r ((1 + Complex.I) * s) /
      ((ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * r))) atTop (𝓝 1) := by
  have h := tendsto_besselI0_div_besselI1 (l := atTop)
    (f := fun s : ℝ => (1 + Complex.I) * ((s * r : ℝ) : ℂ)) (K := 2) two_pos
    (by simpa [one_add_I_mul_re] using tendsto_id.atTop_mul_const hr)
    (by filter_upwards [eventually_ge_atTop 0] with s hs
        exact norm_one_add_I_mul_le (by positivity))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [coreImpedance_div_surface hρ hr (by
    refine mul_ne_zero (by intro h; simpa using congrArg Complex.re h) ?_
    exact_mod_cast hs.ne')]
  push_cast; ring_nf

/-- **High-frequency expansion with bounded remainder**: along `m = (1 + i)s`,
`Z(m) = ρ m/(2π r) + O(1)` as `s → ∞` (the surface term itself grows like `s`). -/
@[powerlib_foundation] theorem coreImpedance_sub_surface_isBigO {ρ r : ℝ} (hρ : ρ ≠ 0)
    (hr : 0 < r) :
    (fun s : ℝ => coreImpedance ρ r ((1 + Complex.I) * s) -
      (ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * r)) =O[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨C, x₀, hx₀, hC⟩ := besselI0_div_besselI1_sub_one_le (K := 2) two_pos
  refine IsBigO.of_bound (|ρ| * 2 / (2 * Real.pi * r) * (C / r)) ?_
  filter_upwards [eventually_ge_atTop (x₀ / r), eventually_gt_atTop 0] with s hs hs0
  have hsr : x₀ ≤ s * r := by rwa [div_le_iff₀ hr] at hs
  set w : ℂ := (1 + Complex.I) * ((s * r : ℝ) : ℂ) with hw
  have hwre : w.re = s * r := by rw [hw, one_add_I_mul_re]
  obtain ⟨-, hI1, hb⟩ := hC w (by rw [hwre]; exact hsr)
    (by rw [hwre, ← one_add_I_mul_re (s * r)]; exact norm_one_add_I_mul_le (by positivity))
  have hm : (1 + Complex.I) * (s : ℂ) * r = w := by rw [hw]; push_cast; ring
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e : coreImpedance ρ r ((1 + Complex.I) * s) -
      (ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * r) =
      (ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * r) * (besselI0 w / besselI1 w - 1) := by
    unfold coreImpedance; rw [hm]; ring
  rw [e, norm_mul, norm_one, mul_one]
  rw [hwre] at hb
  have h1I : ‖(1 + Complex.I)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    simp; norm_num
  have hZs : ‖(ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * r)‖ ≤
      |ρ| * 2 * s / (2 * Real.pi * r) := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hs0, show ‖(2 * (Real.pi : ℂ) * r)‖ = 2 * Real.pi * r by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hr]; simp, ← mul_assoc]
    gcongr
  calc ‖(ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * r)‖ * ‖besselI0 w / besselI1 w - 1‖ ≤
        |ρ| * 2 * s / (2 * Real.pi * r) * (C / (s * r)) :=
        mul_le_mul hZs hb (norm_nonneg _) (by positivity)
    _ = |ρ| * 2 / (2 * Real.pi * r) * (C / r) := by field_simp

/-- The physical propagation constant `m = (1 + i)√(ωμ/(2ρ))` satisfies `m² = jωμ/ρ`. -/
@[powerlib_foundation] theorem one_add_I_mul_sqrt_sq {ω μ ρ : ℝ} (hρ : ρ ≠ 0)
    (h : 0 ≤ ω * μ / (2 * ρ)) :
    ((1 + Complex.I) * (Real.sqrt (ω * μ / (2 * ρ)) : ℂ)) ^ 2 = Complex.I * ω * μ / ρ := by
  have hs : ((Real.sqrt (ω * μ / (2 * ρ)) : ℂ)) ^ 2 = ((ω * μ / (2 * ρ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt h]
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  rw [mul_pow, hs, add_sq, Complex.I_sq]
  push_cast
  field_simp
  ring

/-- **Skin-effect limit in angular frequency**: with `m(ω) = (1 + i)√(ωμ/(2ρ)) = √(jωμ/ρ)`
(`ρ, μ, r > 0`), `Z(m(ω)) / (ρ m(ω)/(2π r)) → 1` as `ω → ∞`. -/
@[powerlib_foundation] theorem coreImpedance_tendsto_surface_omega {ρ r μ : ℝ} (hρ : 0 < ρ)
    (hr : 0 < r) (hμ : 0 < μ) :
    Tendsto (fun ω : ℝ =>
      coreImpedance ρ r ((1 + Complex.I) * (Real.sqrt (ω * μ / (2 * ρ)) : ℂ)) /
        ((ρ : ℂ) * ((1 + Complex.I) * (Real.sqrt (ω * μ / (2 * ρ)) : ℂ)) / (2 * Real.pi * r)))
      atTop (𝓝 1) := by
  have hs : Tendsto (fun ω : ℝ => Real.sqrt (ω * μ / (2 * ρ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_id.atTop_mul_const hμ).atTop_div_const (by positivity))
  exact (coreImpedance_tendsto_surface hρ.ne' hr).comp hs

end powerlib.Line.CableBessel
