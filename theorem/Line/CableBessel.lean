import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Bessel surface impedance of a solid conductor: low-frequency limit

Source: work-sync `theory/T-cable.md` §1.2.1 ("严格解是 Bessel 比值
`ρ m/(2π r_c) · I₀(m r_c)/I₁(m r_c)` … 低频退化为直流电阻 `ρ_c/(π r_c²)` + 内电感 `μ₀/(8π)`；
高频退化为趋肤表面阻抗 `ρ_c m/(2π r_c)`"), §1.2.2 (tubular conductors).

Model boundary. A straight solid round conductor of radius `r > 0` and resistivity `ρ ≥ 0`,
axially symmetric current, quasi-static field inside the conductor (displacement current
neglected), sinusoidal steady state at angular frequency `ω`; the propagation constant of the
diffusion equation is `m = √(jωμ/ρ)` (any complex `m`; the physical one has argument `π/4`). The
per-unit-length surface (internal) impedance is Schelkunoff's
`Z(m) = (ρ m/(2π r)) I₀(m r)/I₁(m r)` (`coreImpedance`). No proximity effect, no earth return,
no insulation or screen.

Modified Bessel functions. Mathlib has no modified Bessel functions; they are defined here by
their power series: `besselI0 z = Σ_k (z/2)^{2k}/(k!)²`, `besselI1 z = Σ_k (z/2)^{2k+1}/(k!(k+1)!)`
(`besselI0_eq`, `besselI1_eq`), through the entire series `besselSeries0 w = Σ w^k/(k!)²` and
`besselSeries1 w = Σ w^k/(k!(k+1)!)` at `w = z²/4`.

Results (foundation).
* `hasSum_exp_tail`, `norm_tsum_sub_two_le`: a series dominated termwise by the exponential series
  differs from its first two terms by at most `‖w‖²` (`‖w‖ ≤ 1`).
* `besselSeries0_sub_le`, `besselSeries1_sub_le`: `‖f₀(w) − 1 − w‖, ‖f₁(w) − 1 − w/2‖ ≤ ‖w‖²`;
  `besselRatio_sub_le`: `‖f₀(w)/f₁(w) − 1 − w/2‖ ≤ 6‖w‖²` for `‖w‖ ≤ 1/4`.
* `coreImpedance_eq`: `Z(m) = (ρ/(π r²)) f₀(w)/f₁(w)`, `w = (m r)²/4` (`m ≠ 0`).
* **Low-frequency limit**: `coreImpedance_lowFrequency_le`
  (`‖Z − ρ/(π r²) − ρ m²/(8π)‖ ≤ (3ρ r²/(8π)) ‖m‖⁴` for `‖m‖ r ≤ 1`), `coreImpedance_isBigO`
  (`Z = ρ/(π r²) + ρ m²/(8π) + O(m⁴)` as `m → 0`), `coreImpedance_tendsto_dc` (`Z → ρ/(π r²)`),
  and `internalInductance`: with `m² = jωμ/ρ` the second-order term is `jω μ/(8π)` — the note's
  DC resistance plus internal inductance `μ/(8π)` per unit length, exactly.

UNPROVED.
* High-frequency (skin-effect) limit `Z(m)/(ρ m/(2π r)) → 1` as `|m| → ∞` with `arg m = π/4`
  (equivalently `I₀(z)/I₁(z) → 1` in the sector `|arg z| < π/2`): the power series does not give
  large-argument behaviour; it needs the integral representation
  `I_n(z) = (1/π)∫₀^π e^{z cos θ} cos nθ dθ` (not in Mathlib) and a Laplace/Watson estimate with a
  complex large parameter, including a lower bound `|I₁(z)| ≳ |e^z|/√|2πz|`.
* The exact (Schelkunoff) tubular-conductor impedances of §1.2.2 need `K₀`, `K₁` (with their
  logarithmic singularity) in addition; the note itself only states the Wedepohl–Wilcox
  `coth`/`csch` approximations, which are engineering formulas, not consequences proved here.

Family and connection conclusions: none (static special-function analysis; no model family).
-/

noncomputable section
namespace powerlib.Line.CableBessel
open Filter Topology Asymptotics
open scoped Nat

/-- Even series `I₀`: `besselSeries0 w = Σ_k w^k/(k!)²`, so `I₀(z) = besselSeries0 (z²/4)`. -/
def besselSeries0 (w : ℂ) : ℂ := ∑' k : ℕ, w ^ k / ((k ! : ℂ) ^ 2)

/-- Odd series `I₁`: `besselSeries1 w = Σ_k w^k/(k!(k+1)!)`, so
`I₁(z) = (z/2) besselSeries1 (z²/4)`. -/
def besselSeries1 (w : ℂ) : ℂ := ∑' k : ℕ, w ^ k / ((k ! : ℂ) * ((k + 1) ! : ℂ))

/-- The exponential tail `Σ_{k ≥ 2} x^k/k! = eˣ − 1 − x`. -/
@[powerlib_foundation] theorem hasSum_exp_tail (x : ℝ) :
    HasSum (fun k : ℕ => x ^ (k + 2) / ((k + 2) ! : ℝ)) (Real.exp x - 1 - x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := (hasSum_nat_add_iff' (f := fun n : ℕ => x ^ n / (n ! : ℝ)) 2).mpr h
  simpa [Finset.sum_range_succ, sub_sub] using h2

/-- A series dominated termwise by `‖w‖^k/k!` from `k = 2` on: its value minus the first two
terms is at most `‖w‖²` for `‖w‖ ≤ 1`. -/
@[powerlib_foundation] theorem norm_tsum_sub_two_le {g : ℕ → ℂ} {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hg : ∀ k, ‖g k‖ ≤ ‖w‖ ^ k / (k ! : ℝ)) :
    ‖(∑' k, g k) - g 0 - g 1‖ ≤ ‖w‖ ^ 2 := by
  have hsum : Summable g :=
    Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖w‖) hg
  have hsplit := hsum.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsplit
  have htail : (∑' k, g k) - g 0 - g 1 = ∑' k, g (k + 2) := by
    rw [← hsplit]; ring
  rw [htail]
  have hs2 : Summable fun k => ‖g (k + 2)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hg (k + 2))
      (hasSum_exp_tail ‖w‖).summable
  calc ‖∑' k, g (k + 2)‖ ≤ ∑' k, ‖g (k + 2)‖ := norm_tsum_le_tsum_norm hs2
    _ ≤ ∑' k : ℕ, ‖w‖ ^ (k + 2) / ((k + 2) ! : ℝ) :=
        hs2.tsum_le_tsum (fun k => hg (k + 2)) (hasSum_exp_tail ‖w‖).summable
    _ = Real.exp ‖w‖ - 1 - ‖w‖ := (hasSum_exp_tail ‖w‖).tsum_eq
    _ ≤ ‖w‖ ^ 2 := by
        have := Real.abs_exp_sub_one_sub_id_le (x := ‖w‖) (by rw [abs_norm]; exact hw)
        exact (le_abs_self _).trans this

/-- `‖I₀-series(w) − 1 − w‖ ≤ ‖w‖²` for `‖w‖ ≤ 1`. -/
@[powerlib_foundation] theorem besselSeries0_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖besselSeries0 w - 1 - w‖ ≤ ‖w‖ ^ 2 := by
  have h := norm_tsum_sub_two_le (g := fun k : ℕ => w ^ k / ((k ! : ℂ) ^ 2)) hw (fun k => by
    rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
    have hk : (1 : ℝ) ≤ (k ! : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hk0 : (0 : ℝ) < (k ! : ℝ) := by positivity
    rw [div_le_div_iff₀ (by positivity) hk0]
    have : (k ! : ℝ) ≤ (k ! : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity))
  simpa [besselSeries0] using h

/-- `‖I₁-series(w) − 1 − w/2‖ ≤ ‖w‖²` for `‖w‖ ≤ 1`. -/
@[powerlib_foundation] theorem besselSeries1_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖besselSeries1 w - 1 - w / 2‖ ≤ ‖w‖ ^ 2 := by
  have h := norm_tsum_sub_two_le (g := fun k : ℕ => w ^ k / ((k ! : ℂ) * ((k + 1) ! : ℂ))) hw
    (fun k => by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
      have hk0 : (0 : ℝ) < (k ! : ℝ) := by positivity
      have hk1 : (1 : ℝ) ≤ ((k + 1) ! : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))
      rw [div_le_div_iff₀ (by positivity) hk0]
      have : (k ! : ℝ) ≤ (k ! : ℝ) * ((k + 1) ! : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity))
  have e : (∑' k : ℕ, w ^ k / ((k ! : ℂ) * ((k + 1) ! : ℂ))) - w ^ 0 / ((0 ! : ℂ) * ((0 + 1) ! : ℂ)) -
      w ^ 1 / ((1 ! : ℂ) * ((1 + 1) ! : ℂ)) = besselSeries1 w - 1 - w / 2 := by
    simp [besselSeries1, Nat.factorial]
  rw [e] at h
  exact h

/-- Modified Bessel function of the first kind, order zero: `I₀(z) = Σ_k (z/2)^{2k}/(k!)²`. -/
def besselI0 (z : ℂ) : ℂ := besselSeries0 (z ^ 2 / 4)

/-- Modified Bessel function of the first kind, order one: `I₁(z) = Σ_k (z/2)^{2k+1}/(k!(k+1)!)`. -/
def besselI1 (z : ℂ) : ℂ := z / 2 * besselSeries1 (z ^ 2 / 4)

/-- `I₀` is the standard power series. -/
@[powerlib_foundation] theorem besselI0_eq (z : ℂ) :
    besselI0 z = ∑' k : ℕ, (z / 2) ^ (2 * k) / ((k ! : ℂ) ^ 2) := by
  unfold besselI0 besselSeries0
  congr 1; funext k
  rw [pow_mul]; ring

/-- `I₁` is the standard power series. -/
@[powerlib_foundation] theorem besselI1_eq (z : ℂ) :
    besselI1 z = ∑' k : ℕ, (z / 2) ^ (2 * k + 1) / ((k ! : ℂ) * ((k + 1) ! : ℂ)) := by
  unfold besselI1 besselSeries1
  rw [← tsum_mul_left]
  congr 1; funext k
  rw [pow_add, pow_mul]; ring

/-- Schelkunoff surface impedance of a solid round conductor of radius `r` and resistivity `ρ`,
per unit length: `Z = (ρ m/(2π r)) I₀(m r)/I₁(m r)` with `m = √(jωμ/ρ)` (T-cable §1.2.1). -/
def coreImpedance (ρ r : ℝ) (m : ℂ) : ℂ :=
  (ρ : ℂ) * m / (2 * Real.pi * r) * (besselI0 (m * r) / besselI1 (m * r))

/-- With `w = (m r)²/4`: `Z = (ρ/(π r²)) · I₀-series(w)/I₁-series(w)`. -/
@[powerlib_foundation] theorem coreImpedance_eq {ρ r : ℝ} (hr : r ≠ 0) {m : ℂ} (hm : m ≠ 0) :
    coreImpedance ρ r m = ((ρ / (Real.pi * r ^ 2) : ℝ) : ℂ) *
      (besselSeries0 ((m * r) ^ 2 / 4) / besselSeries1 ((m * r) ^ 2 / 4)) := by
  unfold coreImpedance besselI0 besselI1
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h1 : besselSeries1 ((m * r) ^ 2 / 4) = 0
  · simp [h1]
  · push_cast
    field_simp

/-- `I₀/I₁` series ratio: `‖f₀(w)/f₁(w) − 1 − w/2‖ ≤ 6 ‖w‖²` for `‖w‖ ≤ 1/4`. -/
@[powerlib_foundation] theorem besselRatio_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) :
    ‖besselSeries0 w / besselSeries1 w - 1 - w / 2‖ ≤ 6 * ‖w‖ ^ 2 := by
  have hw1 : ‖w‖ ≤ 1 := by linarith
  have h0 := besselSeries0_sub_le hw1
  have h1 := besselSeries1_sub_le hw1
  set f0 := besselSeries0 w
  set f1 := besselSeries1 w
  have hn := norm_nonneg w
  have hf1 : 1 / 2 ≤ ‖f1‖ := by
    have : ‖(1 : ℂ) + w / 2‖ ≥ 1 - ‖w‖ / 2 := by
      have := norm_sub_norm_le (1 : ℂ) (-(w / 2))
      rw [sub_neg_eq_add, norm_neg, norm_div, Complex.norm_two, norm_one] at this
      linarith
    have := norm_sub_norm_le ((1 : ℂ) + w / 2) (-(f1 - 1 - w / 2))
    rw [norm_neg, sub_neg_eq_add, show (1 : ℂ) + w / 2 + (f1 - 1 - w / 2) = f1 by ring] at this
    nlinarith
  have hf1' : f1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hf1; linarith
  have hnum : ‖f0 - (1 + w / 2) * f1‖ ≤ 3 * ‖w‖ ^ 2 := by
    have e : f0 - (1 + w / 2) * f1 = (f0 - 1 - w) - w ^ 2 / 4 - (1 + w / 2) * (f1 - 1 - w / 2) := by
      ring
    rw [e]
    have hq : ‖(1 : ℂ) + w / 2‖ ≤ 1 + ‖w‖ / 2 := by
      have := norm_add_le (1 : ℂ) (w / 2)
      rwa [norm_one, norm_div, Complex.norm_two] at this
    calc ‖(f0 - 1 - w) - w ^ 2 / 4 - (1 + w / 2) * (f1 - 1 - w / 2)‖ ≤
          ‖f0 - 1 - w‖ + ‖w ^ 2 / 4‖ + ‖(1 + w / 2) * (f1 - 1 - w / 2)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 / 4 + (1 + ‖w‖ / 2) * ‖w‖ ^ 2 := by
          rw [norm_mul, norm_div, norm_pow, show ‖(4 : ℂ)‖ = 4 by simp]
          gcongr
      _ ≤ 3 * ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]
  have e2 : f0 / f1 - 1 - w / 2 = (f0 - (1 + w / 2) * f1) / f1 := by
    field_simp
    ring
  rw [e2, norm_div, div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg ‖w‖]

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

end powerlib.Line.CableBessel
