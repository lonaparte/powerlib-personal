import theorem.SpecialFunctions.BesselK
import theorem.Line.Cable

/-! # Exact (Schelkunoff) tubular-conductor impedances: frequency limits and Wedepohl–Wilcox

Source: work-sync `theory/T-cable.md` §1.2.2 ("管状导体（屏蔽层）的三个阻抗" — the note states
the Wedepohl–Wilcox `coth`/`csch` forms and their limits: "低频 → 管的直流电阻（无屏蔽），高频
`csch(mt) ∼ e^{−mt} → 0`（完全屏蔽）"); §1.2 heading "Schelkunoff / Wedepohl–Wilcox"; ref. 1
(Schelkunoff 1934, the exact Bessel-function solution).

Model boundary. A straight homogeneous tubular conductor (inner radius `a > 0`, outer radius
`b > a`, thickness `t = b − a`, resistivity `ρ`), axially symmetric current, quasi-static field
in the metal (displacement current neglected), sinusoidal steady state; `m = √(jωμ/ρ)` is the
propagation constant of the diffusion equation, any complex `m` with `Re m > 0` (the physical
one is `m = (1 + j)s`, `s = √(ωμ/(2ρ)) = 1/δ`). Per unit length, with
`D(m) = I₁(mb)K₁(ma) − I₁(ma)K₁(mb)` (`tubeDet`):
* `exactZin  = (ρm/(2πa)) (I₀(ma)K₁(mb) + K₀(ma)I₁(mb))/D` — inner-surface impedance (return
  current inside the tube),
* `exactZout = (ρm/(2πb)) (I₀(mb)K₁(ma) + K₀(mb)I₁(ma))/D` — outer-surface impedance,
* `exactZmut = ρ/(2πab D)` — transfer (screening) impedance.
`I₀`, `I₁` are the power series of `theorem/SpecialFunctions/BesselI.lean`; `K₀`, `K₁` the
integrals `∫₀^∞ e^{−z cosh t}(1, cosh t) dt` of `theorem/SpecialFunctions/BesselK.lean`. The
formulas are the definitions here (the field solution behind them is not derived). No proximity effect, no
earth return, no insulation; the Wedepohl–Wilcox comparisons use `Cable.tubeZin`, `tubeZout`,
`tubeZmut` of `theorem/Line/Cable.lean`.

Results (foundation; static special-function analysis, no model family). Limits are proved
along any filter (`m → 0` with `Re m > 0`, in a sector `‖m‖ ≤ K Re m` where needed; or
`Re m → ∞` in a sector), then specialized to the physical ray `m = (1 + j)s` and to `ω`.
* Low frequency, DC resistance `ρ/(π(b² − a²))`: `tendsto_tubeDet_zero`
  (`D → (b² − a²)/(2ab)`), `tendsto_exactZmut_dc`, `tendsto_exactZin_dc`, `tendsto_exactZout_dc`;
  ray `s → 0⁺`: `exactZmut_tendsto_dc`, `exactZin_tendsto_dc`, `exactZout_tendsto_dc`.
* High frequency: normalized forms `tubeDet_eq_norm`, `numIn_eq_norm`, `numOut_eq_norm`,
  `exactZin_div_surface_eq`, `exactZout_div_surface_eq`, `exactZmut_eq_norm` (from
  `I_ν(z) = e^z G(z) Î_ν(z)/π`, `K_ν(z) = e^{−z} G(z) K̂_ν(z)`, `Î, K̂ → 1`,
  `G(ma)G(mb) = π/(2m√(ab))`, `gaussHalf_mul_gaussHalf`); `tendsto_exactZin_surface`,
  `tendsto_exactZout_surface` (`Z_in/(ρm/(2πa)) → 1`, `Z_out/(ρm/(2πb)) → 1`: surface
  impedances), `tendsto_exactZmut_zero` (`Z_mut → 0`: complete screening, `Z_mut ∼
  (ρ m/(π√(ab))) e^{−m t}`); ray `s → ∞`: `exactZin_tendsto_surface`,
  `exactZout_tendsto_surface`, `exactZmut_tendsto_zero`.
* High-frequency rates: `besselNorm_sub_one_isBigO` (`Î_ν − 1`, `K̂_ν − 1` are `O(1/Re m)`),
  `innerRatio_sub_one_isBigO`, `outerRatio_sub_one_isBigO`; `exactZin_sub_surface_isBigO_of`,
  `exactZout_sub_surface_isBigO_of` and along the ray `exactZin_sub_surface_isBigO`,
  `exactZout_sub_surface_isBigO` (`Z_in = ρm/(2πa) + O(1)`, `Z_out = ρm/(2πb) + O(1)`);
  `tendsto_exactZmut_div_asymptotic`, `exactZmut_div_asymptotic_tendsto`
  (`Z_mut ∼ (ρ m/(π√(ab))) e^{−m(b−a)}`).
* Angular frequency `m(ω) = (1 + j)√(ωμ/(2ρ))`: `exactZ_tendsto_omega` (all six limits).
* Relation with the Wedepohl–Wilcox formulas: low frequency, all three ratios `→ 1`
  (`tendsto_exactZin_div_tubeZin_dc`, `tendsto_exactZout_div_tubeZout_dc`,
  `tendsto_exactZmut_div_tubeZmut_dc`); high frequency along the ray,
  `exactZin_div_tubeZin_tendsto_hf`, `exactZout_div_tubeZout_tendsto_hf` (`→ 1`), but
  `tendsto_exactZmut_div_tubeZmut`, `exactZmut_div_tubeZmut_tendsto_hf`:
  `Z_mut/Z_mut^{WW} → (a + b)/(2√(ab))`, with `one_lt_wwMutFactor` (`> 1` for `a < b`).

Correction (to reading the §1.2.2 boxed formulas as the tube's impedances).
* The Wedepohl–Wilcox transfer impedance `(ρ m/(π(a + b))) csch(mt)` is not asymptotically
  equivalent to the exact one at high frequency: both decay like `e^{−mt}` (so the note's
  "→ 0, 完全屏蔽" holds for both), but their ratio tends to `(a + b)/(2√(ab)) > 1`
  (`exactZmut_div_tubeZmut_tendsto_hf`, `one_lt_wwMutFactor`); the `csch` formula replaces the
  geometric mean `√(ab)` of the radii by the arithmetic mean `(a + b)/2` and is asymptotically
  exact only in the thin-wall limit. The inner and outer impedances are asymptotically
  equivalent at both ends (ratios `→ 1`).

Family and connection conclusions: none (static special-function analysis; no model family).
-/

noncomputable section
namespace powerlib.Line.CableSchelkunoff
open Filter Topology
open powerlib.SpecialFunctions powerlib.Line.Cable

/-- Schelkunoff's determinant of a tube (inner radius `a`, outer radius `b`):
`D(m) = I₁(mb) K₁(ma) − I₁(ma) K₁(mb)`. -/
def tubeDet (a b : ℝ) (m : ℂ) : ℂ :=
  besselI1 (m * b) * besselK1 (m * a) - besselI1 (m * a) * besselK1 (m * b)

/-- Exact inner-surface impedance of a tube (return current inside):
`Z_in(m) = (ρ m/(2π a)) (I₀(ma) K₁(mb) + K₀(ma) I₁(mb))/D(m)`. -/
def exactZin (ρ a b : ℝ) (m : ℂ) : ℂ :=
  (ρ : ℂ) * m / (2 * Real.pi * a) *
    ((besselI0 (m * a) * besselK1 (m * b) + besselK0 (m * a) * besselI1 (m * b)) / tubeDet a b m)

/-- Exact outer-surface impedance of a tube (return current outside):
`Z_out(m) = (ρ m/(2π b)) (I₀(mb) K₁(ma) + K₀(mb) I₁(ma))/D(m)`. -/
def exactZout (ρ a b : ℝ) (m : ℂ) : ℂ :=
  (ρ : ℂ) * m / (2 * Real.pi * b) *
    ((besselI0 (m * b) * besselK1 (m * a) + besselK0 (m * b) * besselI1 (m * a)) / tubeDet a b m)

/-- Exact transfer (mutual) impedance of a tube: `Z_mut(m) = ρ/(2π a b D(m))`. -/
def exactZmut (ρ a b : ℝ) (m : ℂ) : ℂ :=
  (ρ : ℂ) / (2 * Real.pi * a * b * tubeDet a b m)

/-! ## Low frequency -/

section LowFrequency

variable {ι : Type*} {l : Filter ι} {f : ι → ℂ}

@[powerlib_foundation] theorem tendsto_mul_ofReal {r : ℝ} (hf : Tendsto f l (𝓝 0)) :
    Tendsto (fun i => f i * r) l (𝓝 0) := by
  simpa using hf.mul_const (r : ℂ)

@[powerlib_foundation]
theorem re_mul_ofReal_pos {r : ℝ} (hr : 0 < r) (hre : ∀ᶠ i in l, 0 < (f i).re) :
    ∀ᶠ i in l, 0 < (f i * r).re := by
  filter_upwards [hre] with i hi
  rw [Complex.re_mul_ofReal]; positivity

@[powerlib_foundation]
theorem sector_mul_ofReal {r K : ℝ} (hr : 0 < r) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    ∀ᶠ i in l, ‖f i * r‖ ≤ K * (f i * r).re := by
  filter_upwards [hsec] with i hi
  rw [Complex.re_mul_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  nlinarith

/-- `I₁(mb) K₁(ma) = (b/(2a)) f₁((mb)²/4) · (ma) K₁(ma)`. -/
@[powerlib_foundation] theorem besselI1_mul_besselK1_eq {a b : ℝ} (ha : a ≠ 0) (m : ℂ) :
    besselI1 (m * b) * besselK1 (m * a) =
      ((b / (2 * a) : ℝ) : ℂ) * besselSeries1 ((m * b) ^ 2 / 4) * (m * a * besselK1 (m * a)) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  unfold besselI1
  push_cast
  field_simp

/-- **Low-frequency limit of the determinant**: `D(m) → (b² − a²)/(2ab)` as `m → 0`, `Re m > 0`. -/
@[powerlib_foundation]
theorem tendsto_tubeDet_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hf : Tendsto f l (𝓝 0))
    (hre : ∀ᶠ i in l, 0 < (f i).re) :
    Tendsto (fun i => tubeDet a b (f i)) l (𝓝 (((b ^ 2 - a ^ 2) / (2 * a * b) : ℝ) : ℂ)) := by
  have h1 := ((tendsto_besselSeries1_sq_zero (tendsto_mul_ofReal (r := b) hf)).const_mul
    ((b / (2 * a) : ℝ) : ℂ)).mul (tendsto_mul_besselK1_zero (tendsto_mul_ofReal (r := a) hf)
    (re_mul_ofReal_pos ha hre))
  have h2 := ((tendsto_besselSeries1_sq_zero (tendsto_mul_ofReal (r := a) hf)).const_mul
    ((a / (2 * b) : ℝ) : ℂ)).mul (tendsto_mul_besselK1_zero (tendsto_mul_ofReal (r := b) hf)
    (re_mul_ofReal_pos hb hre))
  have h := h1.sub h2
  have e : ((b / (2 * a) : ℝ) : ℂ) * 1 * 1 - ((a / (2 * b) : ℝ) : ℂ) * 1 * 1 =
      (((b ^ 2 - a ^ 2) / (2 * a * b) : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [e] at h
  refine h.congr fun i => ?_
  simp only [tubeDet]
  rw [besselI1_mul_besselK1_eq ha.ne', besselI1_mul_besselK1_eq hb.ne']

/-- The tube's DC resistance as a quotient: `ρ/(2π a b ((b² − a²)/(2ab))) = ρ/(π(b² − a²))`. -/
@[powerlib_foundation] theorem dc_eq {ρ a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ρ / (2 * Real.pi * a * b * ((b ^ 2 - a ^ 2) / (2 * a * b))) =
      ρ / (Real.pi * (b ^ 2 - a ^ 2)) := by
  have hb : 0 < b := ha.trans hab
  have h3 : b ^ 2 - a ^ 2 ≠ 0 := by nlinarith
  field_simp

/-- **Low-frequency limit of the exact transfer impedance**: `Z_mut(m) → ρ/(π(b² − a²))` (the
tube's DC resistance) as `m → 0` in the open right half-plane. -/
@[powerlib_foundation]
theorem tendsto_exactZmut_dc {ρ a b : ℝ} (ha : 0 < a) (hab : a < b) (hf : Tendsto f l (𝓝 0))
    (hre : ∀ᶠ i in l, 0 < (f i).re) :
    Tendsto (fun i => exactZmut ρ a b (f i)) l (𝓝 ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ)) := by
  have hb : 0 < b := ha.trans hab
  have hD := tendsto_tubeDet_zero ha hb hf hre
  have hne : (2 * Real.pi * a * b : ℂ) * (((b ^ 2 - a ^ 2) / (2 * a * b) : ℝ) : ℂ) ≠ 0 := by
    have h3 : b ^ 2 - a ^ 2 ≠ 0 := by nlinarith
    have : (2 * Real.pi * a * b * ((b ^ 2 - a ^ 2) / (2 * a * b)) : ℝ) ≠ 0 := by
      have := Real.pi_pos; positivity
    exact_mod_cast this
  have h := (tendsto_const_nhds (x := (ρ : ℂ))).div (hD.const_mul (2 * Real.pi * a * b : ℂ)) hne
  have e : (ρ : ℂ) / ((2 * Real.pi * a * b : ℂ) * (((b ^ 2 - a ^ 2) / (2 * a * b) : ℝ) : ℂ)) =
      ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ) := by
    rw [← dc_eq (ρ := ρ) ha hab]; push_cast; ring
  rw [e] at h
  refine h.congr fun i => ?_
  simp only [Pi.div_apply, exactZmut]

/-- **Low-frequency limit of the exact inner-surface impedance**: `Z_in(m) → ρ/(π(b² − a²))` as
`m → 0` in a sector `‖m‖ ≤ K Re m`. -/
@[powerlib_foundation]
theorem tendsto_exactZin_dc {ρ a b K : ℝ} (ha : 0 < a) (hab : a < b) (hf : Tendsto f l (𝓝 0))
    (hre : ∀ᶠ i in l, 0 < (f i).re) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => exactZin ρ a b (f i)) l (𝓝 ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ)) := by
  have hb : 0 < b := ha.trans hab
  have hD := tendsto_tubeDet_zero ha hb hf hre
  -- `m I₀(ma) K₁(mb) → 1/b`
  have hN1 := ((tendsto_besselI0_zero (tendsto_mul_ofReal (r := a) hf)).mul
    (tendsto_mul_besselK1_zero (tendsto_mul_ofReal (r := b) hf) (re_mul_ofReal_pos hb hre))).const_mul
    ((1 / b : ℝ) : ℂ)
  -- `m K₀(ma) I₁(mb) → 0`
  have hN2 := ((tendsto_mul_besselK0_zero (tendsto_mul_ofReal (r := a) hf) (re_mul_ofReal_pos ha hre)
    (sector_mul_ofReal ha hsec)).mul ((tendsto_mul_ofReal (r := b) hf).mul
    (tendsto_besselSeries1_sq_zero (tendsto_mul_ofReal (r := b) hf)))).const_mul
    ((1 / (2 * a) : ℝ) : ℂ)
  have hN := hN1.add hN2
  have hden : (((b ^ 2 - a ^ 2) / (2 * a * b) : ℝ) : ℂ) ≠ 0 := by
    have h3 : b ^ 2 - a ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast div_ne_zero h3 (by positivity)
  have h := ((hN.div hD hden).const_mul ((ρ / (2 * Real.pi * a) : ℝ) : ℂ))
  have e : ((ρ / (2 * Real.pi * a) : ℝ) : ℂ) * ((((1 / b : ℝ) : ℂ) * (1 * 1) +
      ((1 / (2 * a) : ℝ) : ℂ) * (0 * (0 * 1))) / (((b ^ 2 - a ^ 2) / (2 * a * b) : ℝ) : ℂ)) =
      ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ) := by
    have h3 : b ^ 2 - a ^ 2 ≠ 0 := by nlinarith
    have hR : ρ / (2 * Real.pi * a) * (1 / b / ((b ^ 2 - a ^ 2) / (2 * a * b))) =
        ρ / (Real.pi * (b ^ 2 - a ^ 2)) := by
      field_simp
    rw [← hR]; push_cast; ring
  rw [e] at h
  refine h.congr fun i => ?_
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [Pi.div_apply, exactZin, besselI1]
  generalize besselI0 (f i * a) = A0
  generalize besselK1 (f i * b) = B1
  generalize besselK0 (f i * a) = A1
  generalize besselSeries1 ((f i * b) ^ 2 / 4) = S
  generalize tubeDet a b (f i) = D
  push_cast
  field_simp

/-- **Low-frequency limit of the exact outer-surface impedance**: `Z_out(m) → ρ/(π(b² − a²))` as
`m → 0` in a sector `‖m‖ ≤ K Re m`. -/
@[powerlib_foundation]
theorem tendsto_exactZout_dc {ρ a b K : ℝ} (ha : 0 < a) (hab : a < b) (hf : Tendsto f l (𝓝 0))
    (hre : ∀ᶠ i in l, 0 < (f i).re) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => exactZout ρ a b (f i)) l (𝓝 ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ)) := by
  have hb : 0 < b := ha.trans hab
  have hD := tendsto_tubeDet_zero ha hb hf hre
  -- `m I₀(mb) K₁(ma) → 1/a`
  have hN1 := ((tendsto_besselI0_zero (tendsto_mul_ofReal (r := b) hf)).mul
    (tendsto_mul_besselK1_zero (tendsto_mul_ofReal (r := a) hf) (re_mul_ofReal_pos ha hre))).const_mul
    ((1 / a : ℝ) : ℂ)
  -- `m K₀(mb) I₁(ma) → 0`
  have hN2 := ((tendsto_mul_besselK0_zero (tendsto_mul_ofReal (r := b) hf) (re_mul_ofReal_pos hb hre)
    (sector_mul_ofReal hb hsec)).mul ((tendsto_mul_ofReal (r := a) hf).mul
    (tendsto_besselSeries1_sq_zero (tendsto_mul_ofReal (r := a) hf)))).const_mul
    ((1 / (2 * b) : ℝ) : ℂ)
  have hN := hN1.add hN2
  have hden : (((b ^ 2 - a ^ 2) / (2 * a * b) : ℝ) : ℂ) ≠ 0 := by
    have h3 : b ^ 2 - a ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast div_ne_zero h3 (by positivity)
  have h := ((hN.div hD hden).const_mul ((ρ / (2 * Real.pi * b) : ℝ) : ℂ))
  have e : ((ρ / (2 * Real.pi * b) : ℝ) : ℂ) * ((((1 / a : ℝ) : ℂ) * (1 * 1) +
      ((1 / (2 * b) : ℝ) : ℂ) * (0 * (0 * 1))) / (((b ^ 2 - a ^ 2) / (2 * a * b) : ℝ) : ℂ)) =
      ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ) := by
    have h3 : b ^ 2 - a ^ 2 ≠ 0 := by nlinarith
    have hR : ρ / (2 * Real.pi * b) * (1 / a / ((b ^ 2 - a ^ 2) / (2 * a * b))) =
        ρ / (Real.pi * (b ^ 2 - a ^ 2)) := by
      field_simp
    rw [← hR]; push_cast; ring
  rw [e] at h
  refine h.congr fun i => ?_
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [Pi.div_apply, exactZout, besselI1]
  generalize besselI0 (f i * b) = A0
  generalize besselK1 (f i * a) = B1
  generalize besselK0 (f i * b) = A1
  generalize besselSeries1 ((f i * a) ^ 2 / 4) = S
  generalize tubeDet a b (f i) = D
  push_cast
  field_simp

end LowFrequency

/-! ## High frequency -/

section HighFrequency

variable {ι : Type*} {l : Filter ι} {f : ι → ℂ}

/-- `e^{−2w} = (e^w)^{−2}`. -/
@[powerlib_foundation]
theorem cexp_neg_two_mul (w : ℂ) : Complex.exp (-(2 * w)) = (Complex.exp w ^ 2)⁻¹ := by
  rw [Complex.exp_neg, ← Complex.exp_nat_mul]; norm_num

/-- `e^{mb} = e^{ma} e^{m(b − a)}`. -/
@[powerlib_foundation] theorem cexp_mul_eq (a b : ℝ) (m : ℂ) :
    Complex.exp (m * b) = Complex.exp (m * a) * Complex.exp (m * ((b - a : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]; push_cast; ring_nf

@[powerlib_foundation]
theorem re_mul_ofReal_pos' {r : ℝ} (hr : 0 < r) {m : ℂ} (hm : 0 < m.re) : 0 < (m * r).re := by
  rw [Complex.re_mul_ofReal]; positivity

/-- Normalized determinant (`Re m > 0`, `a, b > 0`):
`D(m) = (G(ma)G(mb)/π) e^{m(b−a)} (Î₁(mb)K̂₁(ma) − Î₁(ma)K̂₁(mb) e^{−2m(b−a)})`. -/
@[powerlib_foundation]
theorem tubeDet_eq_norm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m : ℂ} (hm : 0 < m.re) :
    tubeDet a b m = gaussHalf (m * a) * gaussHalf (m * b) / Real.pi *
      Complex.exp (m * ((b - a : ℝ) : ℂ)) *
      (besselI1Norm (m * b) * besselK1Norm (m * a) - besselI1Norm (m * a) * besselK1Norm (m * b) *
        Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ))))) := by
  have hGa : gaussHalf (m * a) ≠ 0 := gaussHalf_ne_zero (re_mul_ofReal_pos' ha hm)
  have hGb : gaussHalf (m * b) ≠ 0 := gaussHalf_ne_zero (re_mul_ofReal_pos' hb hm)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold tubeDet
  rw [besselI1_eq_norm hGb, besselK1_eq_norm hGa, besselI1_eq_norm hGa, besselK1_eq_norm hGb,
    cexp_mul_eq a b m, cexp_neg_two_mul]
  have hu := Complex.exp_ne_zero (m * a)
  have hE := Complex.exp_ne_zero (m * ((b - a : ℝ) : ℂ))
  generalize Complex.exp (m * a) = u at hu ⊢
  generalize Complex.exp (m * ((b - a : ℝ) : ℂ)) = E at hE ⊢
  field_simp

/-- Normalized inner numerator: `I₀(ma)K₁(mb) + K₀(ma)I₁(mb) =
(G(ma)G(mb)/π) e^{m(b−a)} (Î₀(ma)K̂₁(mb) e^{−2m(b−a)} + K̂₀(ma)Î₁(mb))`. -/
@[powerlib_foundation]
theorem numIn_eq_norm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m : ℂ} (hm : 0 < m.re) :
    besselI0 (m * a) * besselK1 (m * b) + besselK0 (m * a) * besselI1 (m * b) =
      gaussHalf (m * a) * gaussHalf (m * b) / Real.pi * Complex.exp (m * ((b - a : ℝ) : ℂ)) *
      (besselI0Norm (m * a) * besselK1Norm (m * b) * Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ)))) +
        besselK0Norm (m * a) * besselI1Norm (m * b)) := by
  have hGa : gaussHalf (m * a) ≠ 0 := gaussHalf_ne_zero (re_mul_ofReal_pos' ha hm)
  have hGb : gaussHalf (m * b) ≠ 0 := gaussHalf_ne_zero (re_mul_ofReal_pos' hb hm)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [besselI0_eq_norm hGa, besselK1_eq_norm hGb, besselK0_eq_norm hGa, besselI1_eq_norm hGb,
    cexp_mul_eq a b m, cexp_neg_two_mul]
  have hu := Complex.exp_ne_zero (m * a)
  have hE := Complex.exp_ne_zero (m * ((b - a : ℝ) : ℂ))
  generalize Complex.exp (m * a) = u at hu ⊢
  generalize Complex.exp (m * ((b - a : ℝ) : ℂ)) = E at hE ⊢
  field_simp

/-- Normalized outer numerator: `I₀(mb)K₁(ma) + K₀(mb)I₁(ma) =
(G(ma)G(mb)/π) e^{m(b−a)} (Î₀(mb)K̂₁(ma) + K̂₀(mb)Î₁(ma) e^{−2m(b−a)})`. -/
@[powerlib_foundation]
theorem numOut_eq_norm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m : ℂ} (hm : 0 < m.re) :
    besselI0 (m * b) * besselK1 (m * a) + besselK0 (m * b) * besselI1 (m * a) =
      gaussHalf (m * a) * gaussHalf (m * b) / Real.pi * Complex.exp (m * ((b - a : ℝ) : ℂ)) *
      (besselI0Norm (m * b) * besselK1Norm (m * a) + besselK0Norm (m * b) * besselI1Norm (m * a) *
        Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ))))) := by
  have hGa : gaussHalf (m * a) ≠ 0 := gaussHalf_ne_zero (re_mul_ofReal_pos' ha hm)
  have hGb : gaussHalf (m * b) ≠ 0 := gaussHalf_ne_zero (re_mul_ofReal_pos' hb hm)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [besselI0_eq_norm hGb, besselK1_eq_norm hGa, besselK0_eq_norm hGb, besselI1_eq_norm hGa,
    cexp_mul_eq a b m, cexp_neg_two_mul]
  have hu := Complex.exp_ne_zero (m * a)
  have hE := Complex.exp_ne_zero (m * ((b - a : ℝ) : ℂ))
  generalize Complex.exp (m * a) = u at hu ⊢
  generalize Complex.exp (m * ((b - a : ℝ) : ℂ)) = E at hE ⊢
  field_simp

/-- The common factor `(G(ma)G(mb)/π) e^{m(b−a)}` is nonzero (`Re m > 0`). -/
@[powerlib_foundation]
theorem commonFactor_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m : ℂ} (hm : 0 < m.re) :
    gaussHalf (m * a) * gaussHalf (m * b) / Real.pi * Complex.exp (m * ((b - a : ℝ) : ℂ)) ≠ 0 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (gaussHalf_ne_zero (re_mul_ofReal_pos' ha hm))
    (gaussHalf_ne_zero (re_mul_ofReal_pos' hb hm))) hπ) (Complex.exp_ne_zero _)

/-- `Z_in(m)/(ρ m/(2π a))` in normalized form. -/
@[powerlib_foundation]
theorem exactZin_div_surface_eq {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hb : 0 < b) {m : ℂ}
    (hm : 0 < m.re) :
    exactZin ρ a b m / ((ρ : ℂ) * m / (2 * Real.pi * a)) =
      (besselI0Norm (m * a) * besselK1Norm (m * b) * Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ)))) +
        besselK0Norm (m * a) * besselI1Norm (m * b)) /
      (besselI1Norm (m * b) * besselK1Norm (m * a) - besselI1Norm (m * a) * besselK1Norm (m * b) *
        Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ))))) := by
  have hm0 : m ≠ 0 := by intro h; rw [h] at hm; simp at hm
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold exactZin
  rw [mul_div_cancel_left₀ _ (div_ne_zero (mul_ne_zero hρ' hm0) (by simp [hπ, ha'])),
    numIn_eq_norm ha hb hm, tubeDet_eq_norm ha hb hm,
    mul_div_mul_left _ _ (commonFactor_ne_zero ha hb hm)]

/-- `Z_out(m)/(ρ m/(2π b))` in normalized form. -/
@[powerlib_foundation]
theorem exactZout_div_surface_eq {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hb : 0 < b) {m : ℂ}
    (hm : 0 < m.re) :
    exactZout ρ a b m / ((ρ : ℂ) * m / (2 * Real.pi * b)) =
      (besselI0Norm (m * b) * besselK1Norm (m * a) +
        besselK0Norm (m * b) * besselI1Norm (m * a) * Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ))))) /
      (besselI1Norm (m * b) * besselK1Norm (m * a) - besselI1Norm (m * a) * besselK1Norm (m * b) *
        Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ))))) := by
  have hm0 : m ≠ 0 := by intro h; rw [h] at hm; simp at hm
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold exactZout
  rw [mul_div_cancel_left₀ _ (div_ne_zero (mul_ne_zero hρ' hm0) (by simp [hπ, hb'])),
    numOut_eq_norm ha hb hm, tubeDet_eq_norm ha hb hm,
    mul_div_mul_left _ _ (commonFactor_ne_zero ha hb hm)]

/-- The limits of the eight normalized quantities and of `e^{−2m(b−a)}` along a sector filter. -/
@[powerlib_foundation] theorem tendsto_norms {a b K : ℝ} (ha : 0 < a) (hab : a < b) (hK : 0 < K)
    (hre : Tendsto (fun i => (f i).re) l atTop) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    (Tendsto (fun i => besselI0Norm (f i * a)) l (𝓝 1) ∧
      Tendsto (fun i => besselI1Norm (f i * a)) l (𝓝 1) ∧
      Tendsto (fun i => besselK0Norm (f i * a)) l (𝓝 1) ∧
      Tendsto (fun i => besselK1Norm (f i * a)) l (𝓝 1)) ∧
    (Tendsto (fun i => besselI0Norm (f i * b)) l (𝓝 1) ∧
      Tendsto (fun i => besselI1Norm (f i * b)) l (𝓝 1) ∧
      Tendsto (fun i => besselK0Norm (f i * b)) l (𝓝 1) ∧
      Tendsto (fun i => besselK1Norm (f i * b)) l (𝓝 1)) ∧
    Tendsto (fun i => Complex.exp (-(2 * (f i * ((b - a : ℝ) : ℂ))))) l (𝓝 0) := by
  have hb : 0 < b := ha.trans hab
  have hrer : ∀ {r : ℝ}, 0 < r → Tendsto (fun i => (f i * r).re) l atTop := fun hr => by
    simpa [Complex.re_mul_ofReal] using hre.atTop_mul_const hr
  exact ⟨tendsto_besselNorm hK (hrer ha) (sector_mul_ofReal ha hsec),
    tendsto_besselNorm hK (hrer hb) (sector_mul_ofReal hb hsec),
    tendsto_cexp_neg_two_mul (hrer (by linarith))⟩

/-- **High-frequency limit of the exact inner-surface impedance**: along any `m → ∞` in a sector
(`Re m → ∞`, `‖m‖ ≤ K Re m`), `Z_in(m)/(ρ m/(2π a)) → 1` (the inner surface impedance). -/
@[powerlib_foundation]
theorem tendsto_exactZin_surface {ρ a b K : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b) (hK : 0 < K)
    (hre : Tendsto (fun i => (f i).re) l atTop) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => exactZin ρ a b (f i) / ((ρ : ℂ) * f i / (2 * Real.pi * a))) l (𝓝 1) := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨⟨hI0a, hI1a, hK0a, hK1a⟩, ⟨hI0b, hI1b, hK0b, hK1b⟩, hE⟩ := tendsto_norms ha hab hK hre hsec
  have h := (((hI0a.mul hK1b).mul hE).add (hK0a.mul hI1b)).div
    ((hI1b.mul hK1a).sub ((hI1a.mul hK1b).mul hE)) (by norm_num)
  rw [show ((1 : ℂ) * 1 * 0 + 1 * 1) / (1 * 1 - 1 * 1 * 0) = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [hre.eventually_gt_atTop 0] with i hi
  rw [Pi.div_apply, exactZin_div_surface_eq hρ ha hb hi]

/-- **High-frequency limit of the exact outer-surface impedance**: `Z_out(m)/(ρ m/(2π b)) → 1`. -/
@[powerlib_foundation]
theorem tendsto_exactZout_surface {ρ a b K : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b) (hK : 0 < K)
    (hre : Tendsto (fun i => (f i).re) l atTop) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => exactZout ρ a b (f i) / ((ρ : ℂ) * f i / (2 * Real.pi * b))) l (𝓝 1) := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨⟨hI0a, hI1a, hK0a, hK1a⟩, ⟨hI0b, hI1b, hK0b, hK1b⟩, hE⟩ := tendsto_norms ha hab hK hre hsec
  have h := (((hI0b.mul hK1a)).add ((hK0b.mul hI1a).mul hE)).div
    ((hI1b.mul hK1a).sub ((hI1a.mul hK1b).mul hE)) (by norm_num)
  rw [show ((1 : ℂ) * 1 + 1 * 1 * 0) / (1 * 1 - 1 * 1 * 0) = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [hre.eventually_gt_atTop 0] with i hi
  rw [Pi.div_apply, exactZout_div_surface_eq hρ ha hb hi]

/-- `G(ma) G(mb) = π/(2m √a √b)` (`Re m > 0`, `a, b > 0`). -/
@[powerlib_foundation]
theorem gaussHalf_mul_gaussHalf {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m : ℂ} (hm : 0 < m.re) :
    gaussHalf (m * a) * gaussHalf (m * b) =
      Real.pi / (2 * m) / ((Real.sqrt a : ℂ) * (Real.sqrt b : ℂ)) := by
  rw [mul_comm m, mul_comm m, gaussHalf_ofReal_mul ha, gaussHalf_ofReal_mul hb, ← gaussHalf_sq hm]
  ring

/-- Normalized transfer impedance (`Re m > 0`):
`Z_mut(m) = (ρ/(π √a √b)) · m e^{−m(b−a)} / (Î₁(mb)K̂₁(ma) − Î₁(ma)K̂₁(mb) e^{−2m(b−a)})`. -/
@[powerlib_foundation]
theorem exactZmut_eq_norm {ρ a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m : ℂ} (hm : 0 < m.re) :
    exactZmut ρ a b m = ((ρ / (Real.pi * (Real.sqrt a * Real.sqrt b)) : ℝ) : ℂ) *
      (m * Complex.exp (-(m * ((b - a : ℝ) : ℂ)))) /
      (besselI1Norm (m * b) * besselK1Norm (m * a) - besselI1Norm (m * a) * besselK1Norm (m * b) *
        Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ))))) := by
  have hm0 : m ≠ 0 := by intro h; rw [h] at hm; simp at hm
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsa : (Real.sqrt a : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ha).ne'
  have hsb : (Real.sqrt b : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hb).ne'
  have ha2 : (a : ℂ) = (Real.sqrt a : ℂ) ^ 2 := by rw [← Complex.ofReal_pow, Real.sq_sqrt ha.le]
  have hb2 : (b : ℂ) = (Real.sqrt b : ℂ) ^ 2 := by rw [← Complex.ofReal_pow, Real.sq_sqrt hb.le]
  unfold exactZmut
  rw [tubeDet_eq_norm ha hb hm, gaussHalf_mul_gaussHalf ha hb hm]
  generalize besselI1Norm (m * b) * besselK1Norm (m * a) - besselI1Norm (m * a) *
    besselK1Norm (m * b) * Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ)))) = D
  rw [Complex.exp_neg]
  have hE := Complex.exp_ne_zero (m * ((b - a : ℝ) : ℂ))
  generalize Complex.exp (m * ((b - a : ℝ) : ℂ)) = E at hE ⊢
  by_cases hD : D = 0
  · simp [hD]
  · rw [ha2, hb2]
    push_cast
    field_simp

/-- `m e^{−m t} → 0` as `m → ∞` in a sector (`t > 0`). -/
@[powerlib_foundation]
theorem tendsto_mul_cexp_neg {t K : ℝ} (ht : 0 < t) (hre : Tendsto (fun i => (f i).re) l atTop)
    (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => f i * Complex.exp (-(f i * t))) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun x : ℝ => K / t * ((x * t) ^ 1 * Real.exp (-(x * t)))) atTop (𝓝 (K / t * 0)) :=
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.atTop_mul_const ht)).const_mul _
  rw [mul_zero] at h1
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ (h1.comp hre)
  filter_upwards [hsec, hre.eventually_gt_atTop 0] with i hs hi
  rw [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.re_mul_ofReal]
  simp only [Function.comp_apply, pow_one]
  have hE := (Real.exp_pos (-((f i).re * t))).le
  calc ‖f i‖ * Real.exp (-((f i).re * t)) ≤ K * (f i).re * Real.exp (-((f i).re * t)) := by gcongr
    _ = K / t * ((f i).re * t * Real.exp (-((f i).re * t))) := by field_simp

/-- **High-frequency limit of the exact transfer impedance**: `Z_mut(m) → 0` as `m → ∞` in a sector
(complete screening). -/
@[powerlib_foundation]
theorem tendsto_exactZmut_zero {ρ a b K : ℝ} (ha : 0 < a) (hab : a < b) (hK : 0 < K)
    (hre : Tendsto (fun i => (f i).re) l atTop) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => exactZmut ρ a b (f i)) l (𝓝 0) := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨⟨-, hI1a, -, hK1a⟩, ⟨-, hI1b, -, hK1b⟩, hE⟩ := tendsto_norms ha hab hK hre hsec
  have hm := tendsto_mul_cexp_neg (t := b - a) (by linarith) hre hsec
  have h := (hm.const_mul ((ρ / (Real.pi * (Real.sqrt a * Real.sqrt b)) : ℝ) : ℂ)).div
    ((hI1b.mul hK1a).sub ((hI1a.mul hK1b).mul hE)) (by norm_num)
  rw [mul_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards [hre.eventually_gt_atTop 0] with i hi
  rw [Pi.div_apply, exactZmut_eq_norm ha hb hi]

/-- `‖e^w‖ > 1` gives `e^{2w} ≠ 1`. -/
@[powerlib_foundation] theorem cexp_sq_ne_one {w : ℂ} (hw : 0 < w.re) : Complex.exp w ^ 2 ≠ 1 := by
  intro h
  have := congrArg norm h
  rw [norm_pow, Complex.norm_exp, norm_one] at this
  have h1 : 1 < Real.exp w.re := Real.one_lt_exp_iff.mpr hw
  nlinarith

/-- Ratio of the exact and the Wedepohl–Wilcox transfer impedances (`Re m > 0`, `ρ ≠ 0`):
`Z_mut/Z_mut^{WW} = ((a + b)/(√a √b)) ((1 − e^{−2m(b−a)})/2) /
(Î₁(mb)K̂₁(ma) − Î₁(ma)K̂₁(mb) e^{−2m(b−a)})`. -/
@[powerlib_foundation]
theorem exactZmut_div_tubeZmut_eq {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b) {m : ℂ}
    (hm : 0 < m.re) :
    exactZmut ρ a b m / tubeZmut ρ a b m =
      (((a + b) / (Real.sqrt a * Real.sqrt b) : ℝ) : ℂ) *
        ((1 - Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ))))) / 2) /
      (besselI1Norm (m * b) * besselK1Norm (m * a) - besselI1Norm (m * a) * besselK1Norm (m * b) *
        Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ))))) := by
  have hb : 0 < b := ha.trans hab
  have hm0 : m ≠ 0 := by intro h; rw [h] at hm; simp at hm
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsa : (Real.sqrt a : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ha).ne'
  have hsb : (Real.sqrt b : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hb).ne'
  have hab' : ((a : ℂ) + b) ≠ 0 := by exact_mod_cast (by linarith : a + b ≠ 0)
  have hw : 0 < (m * ((b - a : ℝ) : ℂ)).re := re_mul_ofReal_pos' (by linarith) hm
  have hE2 := cexp_sq_ne_one hw
  rw [exactZmut_eq_norm ha hb hm]
  unfold tubeZmut
  have hs : Complex.sinh (m * (b - a)) =
      (Complex.exp (m * ((b - a : ℝ) : ℂ)) - (Complex.exp (m * ((b - a : ℝ) : ℂ)))⁻¹) / 2 := by
    rw [← Complex.exp_neg, ← Complex.two_sinh]; push_cast; ring
  rw [hs, cexp_neg_two_mul, Complex.exp_neg]
  generalize besselI1Norm (m * b) * besselK1Norm (m * a) - besselI1Norm (m * a) *
    besselK1Norm (m * b) * (Complex.exp (m * ((b - a : ℝ) : ℂ)) ^ 2)⁻¹ = D
  have hE := Complex.exp_ne_zero (m * ((b - a : ℝ) : ℂ))
  generalize Complex.exp (m * ((b - a : ℝ) : ℂ)) = E at hE hE2 ⊢
  have hE' : E - E⁻¹ ≠ 0 := by
    intro h; apply hE2
    have : E * (E - E⁻¹) = 0 := by rw [h, mul_zero]
    field_simp at this
    linear_combination this
  have hE'' : E ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hE2
  by_cases hD : D = 0
  · simp [hD]
  · push_cast
    field_simp

/-- **High-frequency ratio of the exact and the Wedepohl–Wilcox transfer impedances**: as `m → ∞`
in a sector, `Z_mut/Z_mut^{WW} → (a + b)/(2√(ab))`. Both tend to `0` with the same exponential
`e^{−m(b−a)}`, but the Wedepohl–Wilcox prefactor `2/(a + b)` replaces the exact `1/√(ab)`. -/
@[powerlib_foundation]
theorem tendsto_exactZmut_div_tubeZmut {ρ a b K : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b)
    (hK : 0 < K) (hre : Tendsto (fun i => (f i).re) l atTop)
    (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => exactZmut ρ a b (f i) / tubeZmut ρ a b (f i)) l
      (𝓝 (((a + b) / (2 * Real.sqrt (a * b)) : ℝ) : ℂ)) := by
  obtain ⟨⟨-, hI1a, -, hK1a⟩, ⟨-, hI1b, -, hK1b⟩, hE⟩ := tendsto_norms ha hab hK hre hsec
  have h := ((((tendsto_const_nhds (x := (1 : ℂ))).sub hE).div_const 2).const_mul
    (((a + b) / (Real.sqrt a * Real.sqrt b) : ℝ) : ℂ)).div
    ((hI1b.mul hK1a).sub ((hI1a.mul hK1b).mul hE)) (by norm_num)
  have e : (((a + b) / (Real.sqrt a * Real.sqrt b) : ℝ) : ℂ) * ((1 - 0) / 2) / (1 * 1 - 1 * 1 * 0) =
      (((a + b) / (2 * Real.sqrt (a * b)) : ℝ) : ℂ) := by
    rw [Real.sqrt_mul ha.le]; push_cast; ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [hre.eventually_gt_atTop 0] with i hi
  rw [Pi.div_apply, exactZmut_div_tubeZmut_eq hρ ha hab hi]

/-- **Correction (Wedepohl–Wilcox transfer impedance)**: the high-frequency ratio
`(a + b)/(2√(ab))` exceeds `1` for every tube of positive thickness (`0 < a < b`): the
`csch` formula has the exact decay rate but overestimates the screening impedance by the
arithmetic/geometric-mean ratio of the radii; the factor is `1` only in the thin-wall limit. -/
@[powerlib_foundation] theorem one_lt_wwMutFactor {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    1 < (a + b) / (2 * Real.sqrt (a * b)) := by
  have hb : 0 < b := ha.trans hab
  have hs : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr (by positivity)
  rw [one_lt_div (by positivity)]
  have h2 : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (by positivity)
  nlinarith [sq_nonneg (a + b - 2 * Real.sqrt (a * b)), sq_pos_of_pos (sub_pos.mpr hab)]

end HighFrequency

/-! ## Comparison with the Wedepohl–Wilcox formulas at low frequency -/

section LowFrequencyWW

variable {ι : Type*} {l : Filter ι} {f : ι → ℂ}

@[powerlib_foundation]
theorem tendsto_nhdsNE_of_re_pos (hf : Tendsto f l (𝓝 0)) (hre : ∀ᶠ i in l, 0 < (f i).re) :
    Tendsto f l (𝓝[≠] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨hf, hre.mono fun i hi h => by
    rw [Set.mem_singleton_iff] at h; rw [h] at hi; simp at hi⟩

@[powerlib_foundation] theorem dc_ne_zero {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b) :
    ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ) ≠ 0 := by
  have h3 : 0 < b ^ 2 - a ^ 2 := by nlinarith
  exact_mod_cast div_ne_zero hρ (by positivity)

/-- At low frequency the exact and the Wedepohl–Wilcox inner impedances agree to first order:
`Z_in/Z_in^{WW} → 1` (both tend to the DC resistance). -/
@[powerlib_foundation]
theorem tendsto_exactZin_div_tubeZin_dc {ρ a b K : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b)
    (hf : Tendsto f l (𝓝 0)) (hre : ∀ᶠ i in l, 0 < (f i).re)
    (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => exactZin ρ a b (f i) / tubeZin ρ a b (f i)) l (𝓝 1) := by
  have h := (tendsto_exactZin_dc (ρ := ρ) ha hab hf hre hsec).div
    ((tubeZin_tendsto_dc ha hab).comp (tendsto_nhdsNE_of_re_pos hf hre)) (dc_ne_zero hρ ha hab)
  rwa [div_self (dc_ne_zero hρ ha hab)] at h

/-- `Z_out/Z_out^{WW} → 1` at low frequency. -/
@[powerlib_foundation]
theorem tendsto_exactZout_div_tubeZout_dc {ρ a b K : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b)
    (hf : Tendsto f l (𝓝 0)) (hre : ∀ᶠ i in l, 0 < (f i).re)
    (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => exactZout ρ a b (f i) / tubeZout ρ a b (f i)) l (𝓝 1) := by
  have h := (tendsto_exactZout_dc (ρ := ρ) ha hab hf hre hsec).div
    ((tubeZout_tendsto_dc ha hab).comp (tendsto_nhdsNE_of_re_pos hf hre)) (dc_ne_zero hρ ha hab)
  rwa [div_self (dc_ne_zero hρ ha hab)] at h

/-- `Z_mut/Z_mut^{WW} → 1` at low frequency. -/
@[powerlib_foundation]
theorem tendsto_exactZmut_div_tubeZmut_dc {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b)
    (hf : Tendsto f l (𝓝 0)) (hre : ∀ᶠ i in l, 0 < (f i).re) :
    Tendsto (fun i => exactZmut ρ a b (f i) / tubeZmut ρ a b (f i)) l (𝓝 1) := by
  have h := (tendsto_exactZmut_dc (ρ := ρ) ha hab hf hre).div
    ((tubeZmut_tendsto_dc ha hab).comp (tendsto_nhdsNE_of_re_pos hf hre)) (dc_ne_zero hρ ha hab)
  rwa [div_self (dc_ne_zero hρ ha hab)] at h

end LowFrequencyWW

/-! ## The physical ray `m = (1 + j)s` (`s = 1/δ`) and angular frequency -/

/-- Along the ray, `Re((1 + j)s) = s → ∞`. -/
@[powerlib_foundation]
theorem ray_re_tendsto : Tendsto (fun s : ℝ => ((1 + Complex.I) * (s : ℂ)).re) atTop atTop := by
  exact tendsto_id.congr fun s => (one_add_I_mul_re s).symm

/-- The ray lies in the sector `‖m‖ ≤ 2 Re m` (`s ≥ 0`). -/
@[powerlib_foundation] theorem ray_sector {l : Filter ℝ} (hl : ∀ᶠ s in l, 0 ≤ s) :
    ∀ᶠ s : ℝ in l, ‖(1 + Complex.I) * (s : ℂ)‖ ≤ 2 * ((1 + Complex.I) * (s : ℂ)).re :=
  hl.mono fun _ hs => norm_one_add_I_mul_le hs

/-- `(1 + j)s → 0` as `s → 0⁺`. -/
@[powerlib_foundation]
theorem ray_tendsto_zero : Tendsto (fun s : ℝ => (1 + Complex.I) * (s : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => (1 + Complex.I) * (s : ℂ)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun s : ℝ => (1 + Complex.I) * (s : ℂ) := by fun_prop
    simpa using hc.tendsto 0
  exact h.mono_left nhdsWithin_le_nhds

/-- `Re((1 + j)s) > 0` for `s > 0`. -/
@[powerlib_foundation]
theorem ray_re_pos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < ((1 + Complex.I) * (s : ℂ)).re := by
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [one_add_I_mul_re]; exact hs

/-- **Exact inner impedance, skin-effect limit** along `m = (1 + j)s`, `s → ∞`:
`Z_in/(ρ m/(2π a)) → 1`. -/
@[powerlib_foundation]
theorem exactZin_tendsto_surface {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℝ => exactZin ρ a b ((1 + Complex.I) * s) /
      ((ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * a))) atTop (𝓝 1) :=
  tendsto_exactZin_surface hρ ha hab two_pos ray_re_tendsto (ray_sector (eventually_ge_atTop 0))

/-- **Exact outer impedance, skin-effect limit**: `Z_out/(ρ m/(2π b)) → 1` along `m = (1 + j)s`. -/
@[powerlib_foundation]
theorem exactZout_tendsto_surface {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℝ => exactZout ρ a b ((1 + Complex.I) * s) /
      ((ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * b))) atTop (𝓝 1) :=
  tendsto_exactZout_surface hρ ha hab two_pos ray_re_tendsto (ray_sector (eventually_ge_atTop 0))

/-- **Exact transfer impedance, complete screening**: `Z_mut → 0` along `m = (1 + j)s`, `s → ∞`. -/
@[powerlib_foundation] theorem exactZmut_tendsto_zero {ρ a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℝ => exactZmut ρ a b ((1 + Complex.I) * s)) atTop (𝓝 0) :=
  tendsto_exactZmut_zero ha hab two_pos ray_re_tendsto (ray_sector (eventually_ge_atTop 0))

/-- **Exact vs Wedepohl–Wilcox inner impedance at high frequency**: `Z_in/Z_in^{WW} → 1`. -/
@[powerlib_foundation]
theorem exactZin_div_tubeZin_tendsto_hf {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℝ => exactZin ρ a b ((1 + Complex.I) * s) /
      tubeZin ρ a b ((1 + Complex.I) * s)) atTop (𝓝 1) := by
  have h := (exactZin_tendsto_surface hρ ha hab).div (tubeZin_tendsto_surface hρ ha hab) one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have hS : (ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * a) ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
    exact div_ne_zero (mul_ne_zero hρ' (mul_ne_zero one_add_I_ne_zero hs')) (by simp [hπ, ha'])
  rw [Pi.div_apply, div_div_div_cancel_right₀ hS]

/-- **Exact vs Wedepohl–Wilcox outer impedance at high frequency**: `Z_out/Z_out^{WW} → 1`. -/
@[powerlib_foundation]
theorem exactZout_div_tubeZout_tendsto_hf {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℝ => exactZout ρ a b ((1 + Complex.I) * s) /
      tubeZout ρ a b ((1 + Complex.I) * s)) atTop (𝓝 1) := by
  have h := (exactZout_tendsto_surface hρ ha hab).div (tubeZout_tendsto_surface hρ ha hab) one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have hS : (ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * b) ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast (ha.trans hab).ne'
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
    exact div_ne_zero (mul_ne_zero hρ' (mul_ne_zero one_add_I_ne_zero hs')) (by simp [hπ, hb'])
  rw [Pi.div_apply, div_div_div_cancel_right₀ hS]

/-- **Exact vs Wedepohl–Wilcox transfer impedance at high frequency** along `m = (1 + j)s`:
`Z_mut/Z_mut^{WW} → (a + b)/(2√(ab))` (`> 1` by `one_lt_wwMutFactor`). -/
@[powerlib_foundation]
theorem exactZmut_div_tubeZmut_tendsto_hf {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℝ => exactZmut ρ a b ((1 + Complex.I) * s) /
      tubeZmut ρ a b ((1 + Complex.I) * s)) atTop
      (𝓝 (((a + b) / (2 * Real.sqrt (a * b)) : ℝ) : ℂ)) :=
  tendsto_exactZmut_div_tubeZmut hρ ha hab two_pos ray_re_tendsto
    (ray_sector (eventually_ge_atTop 0))

/-- **Exact inner impedance, DC limit** along `m = (1 + j)s`, `s → 0⁺`. -/
@[powerlib_foundation] theorem exactZin_tendsto_dc {ρ a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℝ => exactZin ρ a b ((1 + Complex.I) * s)) (𝓝[>] 0)
      (𝓝 ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ)) :=
  tendsto_exactZin_dc ha hab ray_tendsto_zero ray_re_pos
    (ray_sector (eventually_mem_nhdsWithin.mono fun _ hs => le_of_lt hs))

/-- **Exact outer impedance, DC limit** along `m = (1 + j)s`, `s → 0⁺`. -/
@[powerlib_foundation] theorem exactZout_tendsto_dc {ρ a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℝ => exactZout ρ a b ((1 + Complex.I) * s)) (𝓝[>] 0)
      (𝓝 ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ)) :=
  tendsto_exactZout_dc ha hab ray_tendsto_zero ray_re_pos
    (ray_sector (eventually_mem_nhdsWithin.mono fun _ hs => le_of_lt hs))

/-- **Exact transfer impedance, DC limit** along `m = (1 + j)s`, `s → 0⁺` (no screening at DC). -/
@[powerlib_foundation] theorem exactZmut_tendsto_dc {ρ a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℝ => exactZmut ρ a b ((1 + Complex.I) * s)) (𝓝[>] 0)
      (𝓝 ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ)) :=
  tendsto_exactZmut_dc ha hab ray_tendsto_zero ray_re_pos

/-- The physical propagation constant `m(ω) = (1 + j)√(ωμ/(2ρ))` moves along the ray:
`√(ωμ/(2ρ)) → ∞` as `ω → ∞` (`μ, ρ > 0`). -/
@[powerlib_foundation] theorem sqrt_omega_tendsto_atTop {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) :
    Tendsto (fun ω : ℝ => Real.sqrt (ω * μ / (2 * ρ))) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp ((tendsto_id.atTop_mul_const hμ).atTop_div_const (by positivity))

/-- `√(ωμ/(2ρ)) → 0⁺` as `ω → 0⁺`. -/
@[powerlib_foundation] theorem sqrt_omega_tendsto_zero {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) :
    Tendsto (fun ω : ℝ => Real.sqrt (ω * μ / (2 * ρ))) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have hc : Continuous fun ω : ℝ => Real.sqrt (ω * μ / (2 * ρ)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with ω (hω : 0 < ω)
    exact Real.sqrt_pos.mpr (by positivity)

/-- **Exact tube impedances in angular frequency**, `m(ω) = (1 + j)√(ωμ/(2ρ)) = √(jωμ/ρ)`:
`ω → 0⁺` gives the DC resistance for all three impedances, `ω → ∞` the inner surface
impedance, the outer surface impedance and complete screening. -/
@[powerlib_foundation]
theorem exactZ_tendsto_omega {ρ a b μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (ha : 0 < a) (hab : a < b) :
    let m : ℝ → ℂ := fun ω => (1 + Complex.I) * (Real.sqrt (ω * μ / (2 * ρ)) : ℂ)
    Tendsto (fun ω => exactZin ρ a b (m ω)) (𝓝[>] 0)
        (𝓝 ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ)) ∧
      Tendsto (fun ω => exactZout ρ a b (m ω)) (𝓝[>] 0)
        (𝓝 ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ)) ∧
      Tendsto (fun ω => exactZmut ρ a b (m ω)) (𝓝[>] 0)
        (𝓝 ((ρ / (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : ℂ)) ∧
      Tendsto (fun ω => exactZin ρ a b (m ω) / ((ρ : ℂ) * m ω / (2 * Real.pi * a))) atTop (𝓝 1) ∧
      Tendsto (fun ω => exactZout ρ a b (m ω) / ((ρ : ℂ) * m ω / (2 * Real.pi * b))) atTop (𝓝 1) ∧
      Tendsto (fun ω => exactZmut ρ a b (m ω)) atTop (𝓝 0) := by
  intro m
  have h0 := sqrt_omega_tendsto_zero hμ hρ
  have hinf := sqrt_omega_tendsto_atTop hμ hρ
  exact ⟨(exactZin_tendsto_dc ha hab).comp h0, (exactZout_tendsto_dc ha hab).comp h0,
    (exactZmut_tendsto_dc ha hab).comp h0, (exactZin_tendsto_surface hρ.ne' ha hab).comp hinf,
    (exactZout_tendsto_surface hρ.ne' ha hab).comp hinf, (exactZmut_tendsto_zero ha hab).comp hinf⟩

/-! ## High-frequency rates -/

open Asymptotics

section Rates

variable {ι : Type*} {l : Filter ι} {f : ι → ℂ}

/-- Rate of the normalized functions: in a sector, `Î_ν(f) − 1` and `K̂_ν(f) − 1` are
`O(1/Re f)`. -/
@[powerlib_foundation]
theorem besselNorm_sub_one_isBigO {K : ℝ} (hK : 0 < K) (hre : Tendsto (fun i => (f i).re) l atTop)
    (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    (fun i => besselI0Norm (f i) - 1) =O[l] (fun i => 1 / (f i).re) ∧
    (fun i => besselI1Norm (f i) - 1) =O[l] (fun i => 1 / (f i).re) ∧
    (fun i => besselK0Norm (f i) - 1) =O[l] (fun i => 1 / (f i).re) ∧
    (fun i => besselK1Norm (f i) - 1) =O[l] (fun i => 1 / (f i).re) := by
  obtain ⟨C, hC0, hC⟩ := besselI_laplace_le' hK
  have hpos := hre.eventually_gt_atTop 0
  have key : ∀ {X : ℂ → ℂ} {C' : ℝ}, 0 ≤ C' →
      (∀ z : ℂ, 0 < z.re → ‖z‖ ≤ K * z.re → ‖X z - gaussHalf z‖ ≤ C' / z.re * ‖gaussHalf z‖) →
      (fun i => X (f i) / gaussHalf (f i) - 1) =O[l] (fun i => 1 / (f i).re) := by
    intro X C' hC' hb
    refine IsBigO.of_bound C' ?_
    filter_upwards [hpos, hsec] with i hi hs
    have hG := gaussHalf_ne_zero hi
    have hGn : 0 < ‖gaussHalf (f i)‖ := norm_pos_iff.mpr hG
    rw [show X (f i) / gaussHalf (f i) - 1 = (X (f i) - gaussHalf (f i)) / gaussHalf (f i) by
      field_simp, norm_div, div_le_iff₀ hGn, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine (hb _ hi hs).trans_eq ?_
    ring
  exact ⟨key hC0 fun z hz hzK => (hC z hz hzK).1, key hC0 fun z hz hzK => (hC z hz hzK).2,
    key (by positivity) fun z hz hzK => (besselK_laplace_le hz hzK).1,
    key (by positivity) fun z hz hzK => (besselK_laplace_le hz hzK).2⟩

/-- `1/Re(f r) = O(1/Re f)` (`r > 0`). -/
@[powerlib_foundation] theorem inv_re_mul_isBigO {r : ℝ} (hr : 0 < r) :
    (fun i => 1 / (f i * r).re) =O[l] (fun i => 1 / (f i).re) := by
  refine IsBigO.of_bound (1 / r) (Eventually.of_forall fun i => ?_)
  rw [Complex.re_mul_ofReal, Real.norm_eq_abs, Real.norm_eq_abs, show 1 / ((f i).re * r) =
    1 / r * (1 / (f i).re) by field_simp, abs_mul, abs_of_pos (by positivity : 0 < 1 / r)]

/-- `e^{−2w} = O(1/Re f)` for `w = f t`, `t > 0`. -/
@[powerlib_foundation]
theorem cexp_neg_two_mul_isBigO {t : ℝ} (ht : 0 < t) (hre : Tendsto (fun i => (f i).re) l atTop) :
    (fun i => Complex.exp (-(2 * (f i * t)))) =O[l] (fun i => 1 / (f i).re) := by
  refine IsBigO.of_bound (1 / (2 * t)) ?_
  filter_upwards [hre.eventually_gt_atTop 0] with i hi
  rw [Complex.norm_exp, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hre' : (-(2 * (f i * t))).re = -(2 * t * (f i).re) := by
    simp [Complex.mul_re]; ring
  rw [hre', Real.exp_neg]
  have hy : 0 < 2 * t * (f i).re := by positivity
  have h1 : 2 * t * (f i).re ≤ Real.exp (2 * t * (f i).re) := by
    linarith [Real.add_one_le_exp (2 * t * (f i).re)]
  rw [inv_le_comm₀ (Real.exp_pos _) (by positivity)]
  calc (1 / (2 * t) * (1 / (f i).re))⁻¹ = 2 * t * (f i).re := by field_simp
    _ ≤ _ := h1

/-- Algebra of the inner ratio: `N'/D' − 1 = ((K̂₀ − 1 − (K̂₁ − 1))Î₁ + E(Î₀K̂₁ + Î₁K̂₁))/D'`. -/
@[powerlib_foundation]
theorem innerRatio_sub_one_eq {p0 p1 q0 q1 r1 s1 E : ℂ} (hD : r1 * q1 - p1 * s1 * E ≠ 0) :
    (p0 * s1 * E + q0 * r1) / (r1 * q1 - p1 * s1 * E) - 1 =
      ((q0 - 1 - (q1 - 1)) * r1 + E * (p0 * s1 + p1 * s1)) * (r1 * q1 - p1 * s1 * E)⁻¹ := by
  rw [div_sub_one hD, div_eq_mul_inv]
  congr 1
  ring

/-- The normalized ratio `N'/D'` of the inner impedance is `1 + O(1/Re m)`. -/
@[powerlib_foundation]
theorem innerRatio_sub_one_isBigO {a b K : ℝ} (ha : 0 < a) (hab : a < b) (hK : 0 < K)
    (hre : Tendsto (fun i => (f i).re) l atTop) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    (fun i => (besselI0Norm (f i * a) * besselK1Norm (f i * b) *
        Complex.exp (-(2 * (f i * ((b - a : ℝ) : ℂ)))) +
        besselK0Norm (f i * a) * besselI1Norm (f i * b)) /
      (besselI1Norm (f i * b) * besselK1Norm (f i * a) - besselI1Norm (f i * a) *
        besselK1Norm (f i * b) * Complex.exp (-(2 * (f i * ((b - a : ℝ) : ℂ))))) - 1)
      =O[l] (fun i => 1 / (f i).re) := by
  have hb : 0 < b := ha.trans hab
  have hrer : ∀ {r : ℝ}, 0 < r → Tendsto (fun i => (f i * r).re) l atTop := fun hr => by
    simpa [Complex.re_mul_ofReal] using hre.atTop_mul_const hr
  obtain ⟨⟨hI0a, hI1a, hK0a, hK1a⟩, ⟨hI0b, hI1b, hK0b, hK1b⟩, hE⟩ := tendsto_norms ha hab hK hre hsec
  obtain ⟨-, -, rK0a, rK1a⟩ := besselNorm_sub_one_isBigO hK (hrer ha) (sector_mul_ofReal ha hsec)
  have rK0a' := rK0a.trans (inv_re_mul_isBigO ha)
  have rK1a' := rK1a.trans (inv_re_mul_isBigO ha)
  have rE := cexp_neg_two_mul_isBigO (t := b - a) (by linarith) hre
  set E := fun i => Complex.exp (-(2 * (f i * ((b - a : ℝ) : ℂ))))
  set D := fun i => besselI1Norm (f i * b) * besselK1Norm (f i * a) - besselI1Norm (f i * a) *
    besselK1Norm (f i * b) * E i with hDdef
  have hD : Tendsto D l (𝓝 1) := by
    have := (hI1b.mul hK1a).sub ((hI1a.mul hK1b).mul hE)
    rw [show (1 : ℂ) * 1 - 1 * 1 * 0 = 1 by norm_num] at this
    exact this
  -- `N' − D' = (K̂₀(ma) − K̂₁(ma)) Î₁(mb) + e^{−2w}(Î₀(ma)K̂₁(mb) + Î₁(ma)K̂₁(mb))`
  have hdiff : (fun i => (besselK0Norm (f i * a) - 1 - (besselK1Norm (f i * a) - 1)) *
      besselI1Norm (f i * b) + E i * (besselI0Norm (f i * a) * besselK1Norm (f i * b) +
        besselI1Norm (f i * a) * besselK1Norm (f i * b))) =O[l] (fun i => 1 / (f i).re) := by
    have h1 := ((rK0a'.sub rK1a').mul (hI1b.isBigO_one (F := ℝ))).congr_right
      (fun i => mul_one _)
    have h2 := (rE.mul (((hI0a.mul hK1b).add (hI1a.mul hK1b)).isBigO_one (F := ℝ))).congr_right
      (fun i => mul_one _)
    exact h1.add h2
  have hinv : (fun i => (D i)⁻¹) =O[l] (fun _ => (1 : ℝ)) :=
    (hD.inv₀ one_ne_zero).isBigO_one (F := ℝ)
  refine ((hdiff.mul hinv).congr_right (fun i => mul_one _)).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [hD.eventually_ne one_ne_zero] with i hi
  exact (innerRatio_sub_one_eq hi).symm

/-- Algebra of the outer ratio. -/
@[powerlib_foundation]
theorem outerRatio_sub_one_eq {p1 q1 r0 r1 s0 s1 E : ℂ} (hD : r1 * q1 - p1 * s1 * E ≠ 0) :
    (r0 * q1 + s0 * p1 * E) / (r1 * q1 - p1 * s1 * E) - 1 =
      ((r0 - 1 - (r1 - 1)) * q1 + E * (s0 * p1 + p1 * s1)) * (r1 * q1 - p1 * s1 * E)⁻¹ := by
  rw [div_sub_one hD, div_eq_mul_inv]
  congr 1
  ring

/-- The normalized ratio of the outer impedance is `1 + O(1/Re m)`. -/
@[powerlib_foundation]
theorem outerRatio_sub_one_isBigO {a b K : ℝ} (ha : 0 < a) (hab : a < b) (hK : 0 < K)
    (hre : Tendsto (fun i => (f i).re) l atTop) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    (fun i => (besselI0Norm (f i * b) * besselK1Norm (f i * a) +
        besselK0Norm (f i * b) * besselI1Norm (f i * a) *
          Complex.exp (-(2 * (f i * ((b - a : ℝ) : ℂ))))) /
      (besselI1Norm (f i * b) * besselK1Norm (f i * a) - besselI1Norm (f i * a) *
        besselK1Norm (f i * b) * Complex.exp (-(2 * (f i * ((b - a : ℝ) : ℂ))))) - 1)
      =O[l] (fun i => 1 / (f i).re) := by
  have hb : 0 < b := ha.trans hab
  have hrer : ∀ {r : ℝ}, 0 < r → Tendsto (fun i => (f i * r).re) l atTop := fun hr => by
    simpa [Complex.re_mul_ofReal] using hre.atTop_mul_const hr
  obtain ⟨⟨hI0a, hI1a, hK0a, hK1a⟩, ⟨hI0b, hI1b, hK0b, hK1b⟩, hE⟩ := tendsto_norms ha hab hK hre hsec
  obtain ⟨rI0b, rI1b, -, -⟩ := besselNorm_sub_one_isBigO hK (hrer hb) (sector_mul_ofReal hb hsec)
  have rI0b' := rI0b.trans (inv_re_mul_isBigO hb)
  have rI1b' := rI1b.trans (inv_re_mul_isBigO hb)
  have rE := cexp_neg_two_mul_isBigO (t := b - a) (by linarith) hre
  have hD : Tendsto (fun i => besselI1Norm (f i * b) * besselK1Norm (f i * a) -
      besselI1Norm (f i * a) * besselK1Norm (f i * b) *
        Complex.exp (-(2 * (f i * ((b - a : ℝ) : ℂ))))) l (𝓝 1) := by
    have := (hI1b.mul hK1a).sub ((hI1a.mul hK1b).mul hE)
    rw [show (1 : ℂ) * 1 - 1 * 1 * 0 = 1 by norm_num] at this
    exact this
  have h1 := ((rI0b'.sub rI1b').mul (hK1a.isBigO_one (F := ℝ))).congr_right (fun i => mul_one _)
  have h2 := (rE.mul (((hK0b.mul hI1a).add (hI1a.mul hK1b)).isBigO_one (F := ℝ))).congr_right
    (fun i => mul_one _)
  have hinv := (hD.inv₀ one_ne_zero).isBigO_one (F := ℝ)
  refine (((h1.add h2).mul hinv).congr_right (fun i => mul_one _)).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [hD.eventually_ne one_ne_zero] with i hi
  exact (outerRatio_sub_one_eq hi).symm

/-- `Z_in(m) = (ρ m/(2π a)) · N'/D'` in normalized form (`Re m > 0`). -/
@[powerlib_foundation]
theorem exactZin_eq_norm {ρ a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m : ℂ} (hm : 0 < m.re) :
    exactZin ρ a b m = (ρ : ℂ) * m / (2 * Real.pi * a) *
      ((besselI0Norm (m * a) * besselK1Norm (m * b) * Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ)))) +
        besselK0Norm (m * a) * besselI1Norm (m * b)) /
      (besselI1Norm (m * b) * besselK1Norm (m * a) - besselI1Norm (m * a) * besselK1Norm (m * b) *
        Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ)))))) := by
  unfold exactZin
  rw [numIn_eq_norm ha hb hm, tubeDet_eq_norm ha hb hm,
    mul_div_mul_left _ _ (commonFactor_ne_zero ha hb hm)]

/-- `Z_out(m) = (ρ m/(2π b)) · N'_out/D'` in normalized form (`Re m > 0`). -/
@[powerlib_foundation]
theorem exactZout_eq_norm {ρ a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m : ℂ} (hm : 0 < m.re) :
    exactZout ρ a b m = (ρ : ℂ) * m / (2 * Real.pi * b) *
      ((besselI0Norm (m * b) * besselK1Norm (m * a) +
        besselK0Norm (m * b) * besselI1Norm (m * a) * Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ))))) /
      (besselI1Norm (m * b) * besselK1Norm (m * a) - besselI1Norm (m * a) * besselK1Norm (m * b) *
        Complex.exp (-(2 * (m * ((b - a : ℝ) : ℂ)))))) := by
  unfold exactZout
  rw [numOut_eq_norm ha hb hm, tubeDet_eq_norm ha hb hm,
    mul_div_mul_left _ _ (commonFactor_ne_zero ha hb hm)]

/-- The surface term `ρ m/(2π r)` is `O(Re m)` in a sector. -/
@[powerlib_foundation] theorem surface_isBigO {ρ r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    (fun i => (ρ : ℂ) * f i / (2 * Real.pi * r)) =O[l] (fun i => (f i).re) := by
  refine IsBigO.of_bound (|ρ| * K / (2 * Real.pi * r)) ?_
  filter_upwards [hsec] with i hs
  have hπr : ‖(2 * (Real.pi : ℂ) * r)‖ = 2 * Real.pi * r := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hr]; simp
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, hπr, Real.norm_eq_abs]
  have hc : 0 ≤ |ρ| * K / (2 * Real.pi * r) := by have := Real.pi_pos; positivity
  calc |ρ| * ‖f i‖ / (2 * Real.pi * r) ≤ |ρ| * (K * (f i).re) / (2 * Real.pi * r) := by gcongr
    _ = |ρ| * K / (2 * Real.pi * r) * (f i).re := by ring
    _ ≤ |ρ| * K / (2 * Real.pi * r) * |(f i).re| := mul_le_mul_of_nonneg_left (le_abs_self _) hc

/-- **High-frequency expansion of the exact inner impedance**: in a sector,
`Z_in(m) = ρ m/(2π a) + O(1)` (the surface term itself grows like `‖m‖`). -/
@[powerlib_foundation]
theorem exactZin_sub_surface_isBigO_of {ρ a b K : ℝ} (ha : 0 < a) (hab : a < b) (hK : 0 < K)
    (hre : Tendsto (fun i => (f i).re) l atTop) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    (fun i => exactZin ρ a b (f i) - (ρ : ℂ) * f i / (2 * Real.pi * a)) =O[l] (fun _ => (1 : ℝ)) := by
  have hb : 0 < b := ha.trans hab
  have h := (surface_isBigO (ρ := ρ) ha hK.le hsec).mul (innerRatio_sub_one_isBigO ha hab hK hre hsec)
  refine h.congr' ?_ ?_
  · filter_upwards [hre.eventually_gt_atTop 0] with i hi
    rw [exactZin_eq_norm ha hb hi]; ring
  · filter_upwards [hre.eventually_gt_atTop 0] with i hi
    field_simp

/-- **High-frequency expansion of the exact outer impedance**: `Z_out(m) = ρ m/(2π b) + O(1)`. -/
@[powerlib_foundation]
theorem exactZout_sub_surface_isBigO_of {ρ a b K : ℝ} (ha : 0 < a) (hab : a < b) (hK : 0 < K)
    (hre : Tendsto (fun i => (f i).re) l atTop) (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    (fun i => exactZout ρ a b (f i) - (ρ : ℂ) * f i / (2 * Real.pi * b)) =O[l]
      (fun _ => (1 : ℝ)) := by
  have hb : 0 < b := ha.trans hab
  have h := (surface_isBigO (ρ := ρ) hb hK.le hsec).mul (outerRatio_sub_one_isBigO ha hab hK hre hsec)
  refine h.congr' ?_ ?_
  · filter_upwards [hre.eventually_gt_atTop 0] with i hi
    rw [exactZout_eq_norm ha hb hi]; ring
  · filter_upwards [hre.eventually_gt_atTop 0] with i hi
    field_simp

/-- **Asymptotic equivalent of the exact transfer impedance**: in a sector,
`Z_mut(m) ∼ (ρ m/(π √(ab))) e^{−m(b−a)}`, i.e. the ratio tends to `1` (`ρ ≠ 0`). -/
@[powerlib_foundation]
theorem tendsto_exactZmut_div_asymptotic {ρ a b K : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b)
    (hK : 0 < K) (hre : Tendsto (fun i => (f i).re) l atTop)
    (hsec : ∀ᶠ i in l, ‖f i‖ ≤ K * (f i).re) :
    Tendsto (fun i => exactZmut ρ a b (f i) /
      ((ρ / (Real.pi * Real.sqrt (a * b)) : ℝ) * (f i * Complex.exp (-(f i * ((b - a : ℝ) : ℂ))))))
      l (𝓝 1) := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨⟨-, hI1a, -, hK1a⟩, ⟨-, hI1b, -, hK1b⟩, hE⟩ := tendsto_norms ha hab hK hre hsec
  have hD := ((hI1b.mul hK1a).sub ((hI1a.mul hK1b).mul hE)).inv₀ (by norm_num)
  rw [show ((1 : ℂ) * 1 - 1 * 1 * 0)⁻¹ = 1 by norm_num] at hD
  refine hD.congr' ?_
  filter_upwards [hre.eventually_gt_atTop 0] with i hi
  have hf0 : f i ≠ 0 := by intro h; rw [h] at hi; simp at hi
  have hc : ((ρ / (Real.pi * Real.sqrt (a * b)) : ℝ) : ℂ) ≠ 0 := by
    have : Real.pi * Real.sqrt (a * b) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne'
    exact_mod_cast div_ne_zero hρ this
  have hX : f i * Complex.exp (-(f i * ((b - a : ℝ) : ℂ))) ≠ 0 :=
    mul_ne_zero hf0 (Complex.exp_ne_zero _)
  rw [exactZmut_eq_norm ha hb hi, ← Real.sqrt_mul ha.le]
  rw [mul_div_assoc, mul_div_mul_left _ _ hc]
  field_simp

end Rates

/-- **Exact inner impedance, high-frequency expansion** along `m = (1 + j)s`:
`Z_in(m) = ρ m/(2π a) + O(1)` as `s → ∞`. -/
@[powerlib_foundation] theorem exactZin_sub_surface_isBigO {ρ a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (fun s : ℝ => exactZin ρ a b ((1 + Complex.I) * s) -
      (ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * a)) =O[atTop] (fun _ => (1 : ℝ)) :=
  exactZin_sub_surface_isBigO_of ha hab two_pos ray_re_tendsto (ray_sector (eventually_ge_atTop 0))

/-- **Exact outer impedance, high-frequency expansion** along `m = (1 + j)s`:
`Z_out(m) = ρ m/(2π b) + O(1)` as `s → ∞`. -/
@[powerlib_foundation] theorem exactZout_sub_surface_isBigO {ρ a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (fun s : ℝ => exactZout ρ a b ((1 + Complex.I) * s) -
      (ρ : ℂ) * ((1 + Complex.I) * s) / (2 * Real.pi * b)) =O[atTop] (fun _ => (1 : ℝ)) :=
  exactZout_sub_surface_isBigO_of ha hab two_pos ray_re_tendsto (ray_sector (eventually_ge_atTop 0))

/-- **Exact transfer impedance, asymptotic equivalent** along `m = (1 + j)s`:
`Z_mut(m) ∼ (ρ m/(π √(ab))) e^{−m(b−a)}` as `s → ∞`. -/
@[powerlib_foundation]
theorem exactZmut_div_asymptotic_tendsto {ρ a b : ℝ} (hρ : ρ ≠ 0) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun s : ℝ => exactZmut ρ a b ((1 + Complex.I) * s) /
      ((ρ / (Real.pi * Real.sqrt (a * b)) : ℝ) * (((1 + Complex.I) * s) *
        Complex.exp (-(((1 + Complex.I) * s) * ((b - a : ℝ) : ℂ)))))) atTop (𝓝 1) :=
  tendsto_exactZmut_div_asymptotic hρ ha hab two_pos ray_re_tendsto
    (ray_sector (eventually_ge_atTop 0))

end powerlib.Line.CableSchelkunoff
