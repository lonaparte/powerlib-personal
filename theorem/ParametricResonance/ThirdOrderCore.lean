import theorem.Criteria.Routh3

/-! # The third-order synchronization core: damping, Hopf margin and the 2:1 kinematic factor

Exact identities and explicit error bounds for the first-order formulas of a monic real cubic
`s³ + d₂ s² + d₁ s + d₀` with a real root `−p` and a complex pair `−σ ± jΩ` — the common
synchronization core of droop, VSG and dVOC in the source — together with the network-lag
correction of its Hopf boundary and the 2:1 kinematic factor at the Hopf point.

Scope.
* Real cubics and complex rational functions only; no converter model is fixed here. The
  readings of droop, VSG and dVOC as such cubics are stated with the converter models in
  `theorem/GridTiedConverter/GFM/` (`DroopPump.charPoly`, `DroopTwoFilter` for VSG,
  `DVOCPump.charPoly_hopf`), and the first-order network expansion behind the lag
  `p ≈ K_s δ − K_d δ̇` (`d₁ ↦ d₁ − d₀ τ`, source §4.4) in `NetworkLag.lean` and
  `DroopSideband.charPoly` there.
* Root parametrization: `(s + p)((s + σ)² + Ω²) = s³ + d₂ s² + d₁ s + d₀` with
  `d₂ = p + 2σ`, `d₁ = σ² + Ω² + 2σp`, `d₀ = p (σ² + Ω²)` (`coeff2`, `coeff1`, `coeff0`).
  Hopf margin `κ_H = 1 − d₀/(d₂ d₁)` (`hopfMargin`), bandwidth ratio `β_L = Ω/d₂`, and the
  first-order damping formula `β_L κ_H / (2 (1 + β_L²))` (`dampingApprox`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §4.1 ((12) and the identity `d₂d₁ − d₀ = 2σ_m[(p_r + σ_m)² + Ω_m²]`),
§4.4 ((16), (17)), §5.2 (Table 6, kinematic factors), §8 (Table 12).

Results.
* `cubic_factor`, `coeffs_of_root` (Vieta: a cubic with real coefficients and the root
  `−σ + jΩ`, `Ω ≠ 0`, has `d₁ = coeff1`, `d₀ = coeff0` with `p = d₂ − 2σ`), `hopf_gap`
  (`d₂d₁ − d₀ = 2σ((p + σ)² + Ω²)`), `hopfMargin_eq`.
* (12) with an explicit remainder (`dampingApprox_bounds`): for `p > 0`, `σ ≥ 0`, `Ω > 0`,
  `0 ≤ σ/Ω − β_L κ_H/(2(1 + β_L²)) ≤ (σ/Ω)(σ/Ω + 2κ_H)`: the first-order formula never
  overestimates the damping, and its error is second order in `(σ/Ω, κ_H)`.
* `Ω² ≈ d₁` with an explicit remainder (`freq_bounds`): `Ω² ≤ d₁` and `(1 − 2κ_H) d₁ ≤ Ω²`.
* Network lag (§4.4): the cubic `s³ + d₂ s² + (d₁ − d₀τ) s + d₀` has all roots in the open left
  half plane iff `(1 − κ_H) d₂ τ < κ_H` (`lagged_roots_re_neg_iff`, Routh–Hurwitz
  `Criteria.cubic_roots_re_neg_iff`); its Hopf boundary is exactly
  `κ_H = d₂τ/(1 + d₂τ)` (`lagged_boundary_iff`). The source's first-order boundary
  `β_L κ_H = Ω τ` is `κ_H = d₂ τ`.
* Boundary shift of the two-lag loop `s (s + a)(s + w) + d₀ (1 − τ s)` (VSG: `a = D/2H`,
  `w = ω_c`, (17)): with `a_q`, `a_f` the boundary values without and with the lag,
  `a_f/a_q = (1 + (w + a_f)τ)(w + a_q)/(w + a_f)`, `a_q ≤ a_f`, and
  `(1 + wτ)(1 − a_f/w) ≤ a_f/a_q ≤ (1 + wτ)(1 + a_f/w)` (`boundary_shift`).
* 2:1 kinematic factor at the Hopf point (`d₁ = Ω²`, `d₀ = d₂Ω²`): the sensitivity
  `S(s) = s(s² + d₂s + d₁)/(s³ + d₂s² + d₁s + d₀) = 1/(1 + L(s))`, `L = d₀/(s(s² + d₂s + d₁))`
  (`loopSensitivity_eq`), equals `(4 + 6jβ)/(3 + 6jβ)` at `s = 2jΩ` (`loopSensitivity_hopf`), with
  `|S|² = 1 + 7/(9 + 36β²)` (`normSq_hopfFactor`), hence `1 < |S|² ≤ 16/9` for every real `β`
  (`hopfFactor_bounds`), strictly decreasing in `β ≥ 0` (`normSq_hopfFactor_strictAntiOn`),
  and `25/18 ≤ |S|² ≤ 16/9` on `0 ≤ β ≤ 1/2` (`hopfFactor_bounds_half`). The double integrator
  `L = Ω²/s²` gives `S(2jΩ) = 4/3` (`doubleIntegrator_sensitivity`).
* The constant-power-pole/PI-zero factor (dVOC row of Table 6):
  `s²(s − a)/((s + d₂)(s² + Ω²))` at `s = 2jΩ` equals `(4/3)(2jΩ − a)/(2jΩ + d₂)`
  (`poleZeroFactor_hopf`), of squared modulus `(16/9)(4Ω² + a²)/(4Ω² + d₂²)`
  (`normSq_poleZeroFactor`).

Corrections.
* §4.1 writes `σ_m/Ω_m ≈ β_L κ_H/[2(1 + β_L²)]` "to first order in `κ_H`"; the exact relation
  gives a one-sided error: the formula is a lower bound for `σ_m/Ω_m`.
* §4.4 gives the Hopf condition `β_L κ_H = Ω_m τ_net`; the exact boundary of the lagged cubic is
  `κ_H = d₂τ/(1 + d₂τ)`, smaller by the factor `1/(1 + d₂τ)`.
-/

noncomputable section
namespace powerlib.ParametricResonance.ThirdOrder

open Complex

/-! ## Root parametrization -/

/-- `d₂ = p + 2σ`. -/
def coeff2 (p σ : ℝ) : ℝ := p + 2 * σ

/-- `d₁ = σ² + Ω² + 2σp`. -/
def coeff1 (p σ Ω : ℝ) : ℝ := σ ^ 2 + Ω ^ 2 + 2 * σ * p

/-- `d₀ = p (σ² + Ω²)`. -/
def coeff0 (p σ Ω : ℝ) : ℝ := p * (σ ^ 2 + Ω ^ 2)

/-- Hopf margin `κ_H = 1 − d₀/(d₂ d₁)`. -/
def hopfMargin (d2 d1 d0 : ℝ) : ℝ := 1 - d0 / (d2 * d1)

/-- The first-order damping formula `β κ_H / (2 (1 + β²))`, `β = Ω/d₂` (source (12)). -/
def dampingApprox (d2 d1 d0 Ω : ℝ) : ℝ :=
  Ω / d2 * hopfMargin d2 d1 d0 / (2 * (1 + (Ω / d2) ^ 2))

@[tmio T, powerlib_foundation] theorem cubic_factor (p σ Ω : ℝ) (s : ℂ) :
    s ^ 3 + (coeff2 p σ : ℂ) * s ^ 2 + (coeff1 p σ Ω : ℂ) * s + (coeff0 p σ Ω : ℂ) =
      (s + p) * ((s + σ) ^ 2 + (Ω : ℂ) ^ 2) := by
  simp only [coeff2, coeff1, coeff0]
  push_cast
  ring

/-- Vieta: a real cubic with the root `−σ + jΩ` (`Ω ≠ 0`) has `d₁ = coeff1`, `d₀ = coeff0` for
the real root `−p`, `p = d₂ − 2σ`. -/
@[tmio T, powerlib_foundation] theorem coeffs_of_root {d2 d1 d0 σ Ω : ℝ} (hΩ : Ω ≠ 0)
    (hroot : (-(σ : ℂ) + Ω * I) ^ 3 + (d2 : ℂ) * (-(σ : ℂ) + Ω * I) ^ 2 +
      (d1 : ℂ) * (-(σ : ℂ) + Ω * I) + (d0 : ℂ) = 0) :
    d2 = coeff2 (d2 - 2 * σ) σ ∧ d1 = coeff1 (d2 - 2 * σ) σ Ω ∧ d0 = coeff0 (d2 - 2 * σ) σ Ω := by
  have key : (Complex.mk (-σ ^ 3 + 3 * σ * Ω ^ 2 + d2 * (σ ^ 2 - Ω ^ 2) - d1 * σ + d0)
      (3 * σ ^ 2 * Ω - Ω ^ 3 - 2 * d2 * σ * Ω + d1 * Ω)) = 0 := by
    rw [Complex.mk_eq_add_mul_I]
    push_cast
    linear_combination hroot - ((-3 * (σ : ℂ) * Ω ^ 2 + d2 * Ω ^ 2) + (Ω : ℂ) ^ 3 * I) * I_sq
  have hre : -σ ^ 3 + 3 * σ * Ω ^ 2 + d2 * (σ ^ 2 - Ω ^ 2) - d1 * σ + d0 = 0 :=
    congrArg Complex.re key
  have him : 3 * σ ^ 2 * Ω - Ω ^ 3 - 2 * d2 * σ * Ω + d1 * Ω = 0 := congrArg Complex.im key
  have h1 : d1 = Ω ^ 2 - 3 * σ ^ 2 + 2 * d2 * σ := by
    have : Ω * (3 * σ ^ 2 - Ω ^ 2 - 2 * d2 * σ + d1) = 0 := by linear_combination him
    have := (mul_eq_zero.mp this).resolve_left hΩ
    linarith
  refine ⟨by simp [coeff2], ?_, ?_⟩
  · simp only [coeff1]; rw [h1]; ring
  · simp only [coeff0]
    have : d0 = σ ^ 3 - 3 * σ * Ω ^ 2 - d2 * (σ ^ 2 - Ω ^ 2) + d1 * σ := by linarith
    rw [this, h1]; ring

/-- The identity behind (12): `d₂d₁ − d₀ = 2σ((p + σ)² + Ω²)`. -/
@[tmio T, powerlib_foundation] theorem hopf_gap (p σ Ω : ℝ) :
    coeff2 p σ * coeff1 p σ Ω - coeff0 p σ Ω = 2 * σ * ((p + σ) ^ 2 + Ω ^ 2) := by
  simp only [coeff2, coeff1, coeff0]
  ring

@[tmio T, powerlib_foundation] private theorem coeff1_pos {p σ Ω : ℝ} (hp : 0 ≤ p) (hσ : 0 ≤ σ) (hΩ : 0 < Ω) :
    0 < coeff1 p σ Ω := by
  unfold coeff1; positivity

@[tmio T, powerlib_foundation] private theorem coeff2_pos {p σ : ℝ} (hp : 0 < p) (hσ : 0 ≤ σ) : 0 < coeff2 p σ := by
  unfold coeff2; positivity

@[tmio T, powerlib_foundation] theorem hopfMargin_eq {p σ Ω : ℝ} (hp : 0 < p) (hσ : 0 ≤ σ)
    (hΩ : 0 < Ω) :
    hopfMargin (coeff2 p σ) (coeff1 p σ Ω) (coeff0 p σ Ω) =
      2 * σ * ((p + σ) ^ 2 + Ω ^ 2) / (coeff2 p σ * coeff1 p σ Ω) := by
  have h2 := coeff2_pos hp hσ
  have h1 := coeff1_pos hp.le hσ hΩ
  rw [hopfMargin, ← hopf_gap]
  field_simp

/-! ## The damping formula (12) with an explicit remainder -/

/-- (12) with a one-sided second-order remainder:
`0 ≤ σ/Ω − β κ_H/(2(1 + β²)) ≤ (σ/Ω)(σ/Ω + 2 κ_H)`. -/
@[tmio T, powerlib_foundation] theorem dampingApprox_bounds {p σ Ω : ℝ} (hp : 0 < p)
    (hσ : 0 ≤ σ) (hΩ : 0 < Ω) :
    0 ≤ σ / Ω - dampingApprox (coeff2 p σ) (coeff1 p σ Ω) (coeff0 p σ Ω) Ω ∧
      σ / Ω - dampingApprox (coeff2 p σ) (coeff1 p σ Ω) (coeff0 p σ Ω) Ω ≤
        σ / Ω * (σ / Ω + 2 * hopfMargin (coeff2 p σ) (coeff1 p σ Ω) (coeff0 p σ Ω)) := by
  have h2 := coeff2_pos hp hσ
  have h1 := coeff1_pos hp.le hσ hΩ
  set d2 := coeff2 p σ with hd2
  set d1 := coeff1 p σ Ω with hd1
  have hκ := hopfMargin_eq hp hσ hΩ
  rw [← hd2, ← hd1] at hκ
  set κ := hopfMargin d2 d1 (coeff0 p σ Ω) with hκdef
  set T1 := σ * Ω ^ 2 * (2 * p + 3 * σ) / (d1 * (d2 ^ 2 + Ω ^ 2)) with hT1
  set T2 := σ * (σ + 2 * p) / d1 with hT2
  have hsplit : σ / Ω - dampingApprox d2 d1 (coeff0 p σ Ω) Ω = σ / Ω * (T1 + T2) := by
    rw [dampingApprox, ← hκdef, hκ, hT1, hT2, hd2, hd1]
    simp only [coeff2, coeff1]
    field_simp
    ring
  have hT1nn : 0 ≤ T1 := by rw [hT1]; positivity
  have hT2nn : 0 ≤ T2 := by rw [hT2]; positivity
  have hT1le : T1 ≤ σ / Ω := by
    rw [hT1, div_le_div_iff₀ (by positivity) hΩ]
    have hd1' : Ω ^ 2 ≤ d1 := by rw [hd1]; unfold coeff1; nlinarith
    have hlin : 2 * p + 3 * σ ≤ 2 * d2 := by rw [hd2]; unfold coeff2; linarith
    have hamgm : 2 * d2 * Ω ≤ d2 ^ 2 + Ω ^ 2 := by nlinarith [sq_nonneg (d2 - Ω)]
    calc σ * Ω ^ 2 * (2 * p + 3 * σ) * Ω
        ≤ σ * Ω ^ 2 * (2 * d2) * Ω := by gcongr
      _ = σ * Ω ^ 2 * (2 * d2 * Ω) := by ring
      _ ≤ σ * Ω ^ 2 * (d2 ^ 2 + Ω ^ 2) := by gcongr
      _ ≤ σ * (d1 * (d2 ^ 2 + Ω ^ 2)) := by
          rw [← mul_assoc σ]; gcongr
  have hT2le : T2 ≤ 2 * κ := by
    rw [hT2, hκ, div_le_iff₀ h1]
    rw [show 2 * (2 * σ * ((p + σ) ^ 2 + Ω ^ 2) / (d2 * d1)) * d1 =
      4 * σ * ((p + σ) ^ 2 + Ω ^ 2) / d2 by field_simp; ring]
    rw [le_div_iff₀ h2, hd2]
    unfold coeff2
    have : (σ + 2 * p) * (p + 2 * σ) ≤ 4 * ((p + σ) ^ 2 + Ω ^ 2) := by nlinarith
    nlinarith
  have hsΩ : 0 ≤ σ / Ω := by positivity
  refine ⟨by rw [hsplit]; positivity, ?_⟩
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left (by linarith) hsΩ

/-- `Ω² ≈ d₁` with an explicit remainder: `Ω² ≤ d₁` and `(1 − 2κ_H) d₁ ≤ Ω²`. -/
@[tmio T, powerlib_foundation] theorem freq_bounds {p σ Ω : ℝ} (hp : 0 < p) (hσ : 0 ≤ σ)
    (hΩ : 0 < Ω) :
    Ω ^ 2 ≤ coeff1 p σ Ω ∧
      (1 - 2 * hopfMargin (coeff2 p σ) (coeff1 p σ Ω) (coeff0 p σ Ω)) * coeff1 p σ Ω ≤ Ω ^ 2 := by
  have h2 := coeff2_pos hp hσ
  have h1 := coeff1_pos hp.le hσ hΩ
  refine ⟨by unfold coeff1; nlinarith, ?_⟩
  rw [hopfMargin_eq hp hσ hΩ]
  have e : (1 - 2 * (2 * σ * ((p + σ) ^ 2 + Ω ^ 2) / (coeff2 p σ * coeff1 p σ Ω))) *
      coeff1 p σ Ω = coeff1 p σ Ω - 4 * σ * ((p + σ) ^ 2 + Ω ^ 2) / coeff2 p σ := by
    field_simp
    ring
  rw [e, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ h2]
  simp only [coeff1, coeff2]
  have : (σ + 2 * p) * (p + 2 * σ) ≤ 4 * ((p + σ) ^ 2 + Ω ^ 2) := by nlinarith
  nlinarith

/-! ## The network-lag correction of the Hopf boundary (§4.4) -/

/-- Routh–Hurwitz for the lagged cubic `s³ + d₂s² + (d₁ − d₀τ)s + d₀`: all roots have negative
real part iff `(1 − κ_H) d₂ τ < κ_H`. -/
@[tmio T, powerlib_foundation] theorem lagged_roots_re_neg_iff {d2 d1 d0 τ : ℝ} (h2 : 0 < d2)
    (h1 : 0 < d1) (h0 : 0 < d0) :
    (∀ s : ℂ, s ^ 3 + (d2 : ℂ) * s ^ 2 + ((d1 - d0 * τ : ℝ) : ℂ) * s + (d0 : ℂ) = 0 → s.re < 0) ↔
      (1 - hopfMargin d2 d1 d0) * (d2 * τ) < hopfMargin d2 d1 d0 := by
  rw [Criteria.cubic_roots_re_neg_iff]
  have e : (1 - hopfMargin d2 d1 d0) * (d2 * τ) = d0 * τ / d1 := by
    rw [hopfMargin]; field_simp; ring
  have key : d0 * τ / d1 < 1 - d0 / (d2 * d1) ↔ d0 < d2 * (d1 - d0 * τ) := by
    rw [← sub_pos, show 1 - d0 / (d2 * d1) - d0 * τ / d1 = (d2 * (d1 - d0 * τ) - d0) / (d2 * d1) by
      field_simp; ring, div_pos_iff_of_pos_right (by positivity), sub_pos]
  rw [e, hopfMargin, key]
  exact ⟨fun h => h.2.2, fun h => ⟨h2, h0, h⟩⟩

/-- The exact Hopf boundary of the lagged cubic: `d₂(d₁ − d₀τ) = d₀ ↔ κ_H = d₂τ/(1 + d₂τ)`. -/
@[tmio T, powerlib_foundation] theorem lagged_boundary_iff {d2 d1 d0 τ : ℝ} (h2 : 0 < d2)
    (h1 : 0 < d1) (hτ : 0 ≤ τ) :
    d2 * (d1 - d0 * τ) = d0 ↔ hopfMargin d2 d1 d0 = d2 * τ / (1 + d2 * τ) := by
  have hden : 0 < 1 + d2 * τ := by positivity
  rw [hopfMargin, eq_div_iff hden.ne']
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-- Boundary shift of the two-lag loop `s(s + a)(s + w) + d₀(1 − τ s)` (VSG under the
droop–VSG map: `a = D/2H`, `w = ω_c`, (17)). `a_q`, `a_f` are boundary values without and with
the lag: `(w + a_q) w a_q = d₀` and `(w + a_f)(w a_f − d₀τ) = d₀`. -/
@[tmio T, powerlib_foundation] theorem boundary_shift {w d0 τ aq af : ℝ} (hw : 0 < w)
    (hτ : 0 ≤ τ) (haq : 0 < aq) (haf : 0 < af)
    (hq : (w + aq) * (w * aq) = d0) (hf : (w + af) * (w * af - d0 * τ) = d0) :
    af / aq = (1 + (w + af) * τ) * (w + aq) / (w + af) ∧ aq ≤ af ∧
      (1 + w * τ) * (1 - af / w) ≤ af / aq ∧ af / aq ≤ (1 + w * τ) * (1 + af / w) := by
  have e1 : w * (af * (w + af)) = w * (aq * (w + aq) * (1 + (w + af) * τ)) := by
    linear_combination hf - (1 + (w + af) * τ) * hq
  have e2 : af * (w + af) = aq * (w + aq) * (1 + (w + af) * τ) :=
    mul_left_cancel₀ hw.ne' e1
  have hratio : af / aq = (1 + (w + af) * τ) * (w + aq) / (w + af) := by
    rw [div_eq_div_iff haq.ne' (by positivity)]
    linear_combination e2
  have hle : aq ≤ af := by
    by_contra hlt
    push Not at hlt
    have : af * (w + af) < aq * (w + aq) := by nlinarith
    have : aq * (w + aq) ≤ aq * (w + aq) * (1 + (w + af) * τ) := by
      have : 0 ≤ aq * (w + aq) * ((w + af) * τ) := by positivity
      nlinarith
    linarith
  refine ⟨hratio, hle, ?_, ?_⟩
  · rw [hratio, le_div_iff₀ (by positivity)]
    have h1 : (1 + w * τ) * (1 - af / w) * (w + af) ≤ (1 + w * τ) * w := by
      have : (1 - af / w) * (w + af) = w - af ^ 2 / w := by field_simp; ring
      rw [mul_assoc, this]
      have : 0 ≤ af ^ 2 / w := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (1 + w * τ) * w ≤ (1 + (w + af) * τ) * (w + aq) :=
      mul_le_mul (by nlinarith) (by linarith) hw.le (by positivity)
    linarith
  · rw [hratio, div_le_iff₀ (by positivity)]
    have : (1 + w * τ) * (1 + af / w) = 1 + (w + af) * τ + af / w := by field_simp; ring
    rw [this]
    have : 0 ≤ af / w := by positivity
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

/-! ## The 2:1 kinematic factor at the Hopf point (§5.2) -/

/-- Sensitivity `S(s) = 1/(1 + L(s))` of the third-order loop `L = d₀/(s(s² + d₂s + d₁))`. -/
def loopSensitivity (d2 d1 d0 : ℝ) (s : ℂ) : ℂ :=
  s * (s ^ 2 + (d2 : ℂ) * s + (d1 : ℂ)) / (s ^ 3 + (d2 : ℂ) * s ^ 2 + (d1 : ℂ) * s + (d0 : ℂ))

/-- The Hopf-point factor `(4 + 6jβ)/(3 + 6jβ)`. -/
def hopfFactor (β : ℝ) : ℂ := (4 + 6 * (β : ℂ) * I) / (3 + 6 * (β : ℂ) * I)

@[tmio T, powerlib_foundation] theorem loopSensitivity_eq {d2 d1 d0 : ℝ} {s : ℂ}
    (hD : s * (s ^ 2 + (d2 : ℂ) * s + (d1 : ℂ)) ≠ 0) :
    loopSensitivity d2 d1 d0 s = 1 / (1 + (d0 : ℂ) / (s * (s ^ 2 + (d2 : ℂ) * s + (d1 : ℂ)))) := by
  have hD' : s ^ 3 + (d2 : ℂ) * s ^ 2 + (d1 : ℂ) * s =
      s * (s ^ 2 + (d2 : ℂ) * s + (d1 : ℂ)) := by ring
  rw [loopSensitivity, hD', one_add_div hD, one_div_div]

/-- At the Hopf point (`d₁ = Ω²`, `d₀ = d₂Ω²`, roots `±jΩ`, `−d₂`), the 2:1 kinematic factor is
`S(2jΩ) = (4 + 6jβ)/(3 + 6jβ)`, `β = Ω/d₂` (Table 6, droop row). -/
@[tmio T, powerlib_foundation] theorem loopSensitivity_hopf {d2 Ω : ℝ} (h2 : 0 < d2)
    (hΩ : 0 < Ω) :
    loopSensitivity d2 (Ω ^ 2) (d2 * Ω ^ 2) (2 * (Ω : ℂ) * I) = hopfFactor (Ω / d2) := by
  have hd2 : (d2 : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hden : (2 * (Ω : ℂ) * I) ^ 3 + (d2 : ℂ) * (2 * (Ω : ℂ) * I) ^ 2 +
      ((Ω ^ 2 : ℝ) : ℂ) * (2 * (Ω : ℂ) * I) + ((d2 * Ω ^ 2 : ℝ) : ℂ) =
      -3 * (Ω : ℂ) ^ 2 * (d2 + 2 * (Ω : ℂ) * I) := by
    push_cast
    linear_combination (8 * (Ω : ℂ) ^ 3 * I + 4 * d2 * Ω ^ 2) * I_sq
  have hnum : (2 * (Ω : ℂ) * I) * ((2 * (Ω : ℂ) * I) ^ 2 + (d2 : ℂ) * (2 * (Ω : ℂ) * I) +
      ((Ω ^ 2 : ℝ) : ℂ)) = -2 * (Ω : ℂ) ^ 2 * (2 * d2 + 3 * (Ω : ℂ) * I) := by
    push_cast
    linear_combination (8 * (Ω : ℂ) ^ 3 * I + 4 * d2 * Ω ^ 2) * I_sq
  have hne : (d2 : ℂ) + 2 * (Ω : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne' : (3 : ℂ) + 6 * ((Ω / d2 : ℝ) : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [loopSensitivity, hden, hnum, hopfFactor, div_eq_div_iff (by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hΩc)) hne) hne']
  push_cast
  field_simp
  ring

@[tmio T, powerlib_foundation] theorem normSq_hopfFactor (β : ℝ) :
    Complex.normSq (hopfFactor β) = 1 + 7 / (9 + 36 * β ^ 2) := by
  rw [hopfFactor, Complex.normSq_div]
  simp [Complex.normSq_apply]
  have : 0 < 9 + 36 * β ^ 2 := by positivity
  field_simp
  ring

@[tmio T, powerlib_foundation] theorem hopfFactor_bounds (β : ℝ) :
    1 < Complex.normSq (hopfFactor β) ∧ Complex.normSq (hopfFactor β) ≤ 16 / 9 := by
  rw [normSq_hopfFactor]
  have h : 0 < 9 + 36 * β ^ 2 := by positivity
  have hpos : 0 < 7 / (9 + 36 * β ^ 2) := by positivity
  refine ⟨by linarith, ?_⟩
  have : 7 / (9 + 36 * β ^ 2) ≤ 7 / 9 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  linarith

@[tmio T, powerlib_foundation] theorem normSq_hopfFactor_strictAntiOn :
    StrictAntiOn (fun β => Complex.normSq (hopfFactor β)) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [normSq_hopfFactor]
  have ha' : (0 : ℝ) ≤ a := ha
  have : 9 + 36 * a ^ 2 < 9 + 36 * b ^ 2 := by nlinarith
  have := div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 7) (by positivity) this
  linarith

/-- On `0 ≤ β ≤ 1/2`: `25/18 ≤ |S|² ≤ 16/9`, i.e. `|S| ∈ [1.178…, 4/3]` (Table 6, droop range). -/
@[tmio T, powerlib_foundation] theorem hopfFactor_bounds_half {β : ℝ} (hβ : 0 ≤ β)
    (hβ' : β ≤ 1 / 2) :
    25 / 18 ≤ Complex.normSq (hopfFactor β) ∧ Complex.normSq (hopfFactor β) ≤ 16 / 9 := by
  refine ⟨?_, (hopfFactor_bounds β).2⟩
  rw [normSq_hopfFactor]
  have h : 9 + 36 * β ^ 2 ≤ 18 := by nlinarith
  have : 7 / 18 ≤ 7 / (9 + 36 * β ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) h
  linarith

/-- The double integrator `L = Ω²/s²`: `1/(1 + L(2jΩ)) = 4/3`. -/
@[tmio T, powerlib_foundation] theorem doubleIntegrator_sensitivity {Ω : ℝ} (hΩ : Ω ≠ 0) :
    1 / (1 + (Ω : ℂ) ^ 2 / (2 * (Ω : ℂ) * I) ^ 2) = 4 / 3 := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have : (2 * (Ω : ℂ) * I) ^ 2 = -4 * (Ω : ℂ) ^ 2 := by
    linear_combination (4 * (Ω : ℂ) ^ 2) * I_sq
  rw [this]
  field_simp
  norm_num

/-- The pole–zero factor `s²(s − a)/((s + d₂)(s² + Ω²))` at `s = 2jΩ`. -/
def poleZeroFactor (d2 Ω a : ℝ) (s : ℂ) : ℂ :=
  s ^ 2 * (s - a) / ((s + d2) * (s ^ 2 + (Ω : ℂ) ^ 2))

/-- dVOC row of Table 6: `s²(s − a)/((s + d₂)(s² + Ω²))` at `2jΩ` is `(4/3)(2jΩ − a)/(2jΩ + d₂)`. -/
@[tmio T, powerlib_foundation] theorem poleZeroFactor_hopf {d2 Ω a : ℝ} (hΩ : Ω ≠ 0) :
    poleZeroFactor d2 Ω a (2 * (Ω : ℂ) * I) =
      4 / 3 * ((2 * (Ω : ℂ) * I - a) / (2 * (Ω : ℂ) * I + d2)) := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hsq : (2 * (Ω : ℂ) * I) ^ 2 = -4 * (Ω : ℂ) ^ 2 := by
    linear_combination (4 * (Ω : ℂ) ^ 2) * I_sq
  rw [poleZeroFactor, hsq]
  field_simp
  ring

@[tmio T, powerlib_foundation] theorem normSq_poleZeroFactor {d2 Ω a : ℝ} (hΩ : Ω ≠ 0) :
    Complex.normSq (poleZeroFactor d2 Ω a (2 * (Ω : ℂ) * I)) =
      16 / 9 * ((4 * Ω ^ 2 + a ^ 2) / (4 * Ω ^ 2 + d2 ^ 2)) := by
  rw [poleZeroFactor_hopf hΩ, Complex.normSq_mul, Complex.normSq_div]
  simp [Complex.normSq_apply]
  ring

end powerlib.ParametricResonance.ThirdOrder
