import theorem.GridTiedConverter.GFM.DroopSideband

/-! # The network lag of the synchronizing power: `p ≈ K δ − K_d δ̇` and `τ_net` (16)

The first-order network expansion behind the lag `p ≈ K_s δ − K_d δ̇` of §4.4: for a series R–L
link the quasi-static current plus its first-order correction gives the port power
`P₀(δ) − K_d δ̇` with an exact `K_d`, and the lag ratio `τ = K_d/K` that enters the lagged cubic
`s³ + d₂s² + (d₁ − d₀τ)s + d₀` of `theorem/ParametricResonance/ThirdOrderCore.lean`.

Model boundary.
* Series link `Z = R + jX` (base frequency `ω_b`, inductance `X/ω_b`) between the EMF
  `E e^{jδ(t)}` (constant amplitude) and the grid voltage `V` (constant angle), in the frame rotating
  at `ω_b`: `(X/ω_b) i' + Z i = E e^{jδ} − V`. Quasi-static current `i₀ = (E e^{jδ} − V)/Z`
  (`current0`), first-order correction `i₁ = −(X/ω_b) i₀'/Z` (`current1`); terms of second order in
  `d/dt ÷ ω_b` (the residual `(X/ω_b) i₁'`) are excluded. Port power `p = Re(E e^{jδ} ī)`
  (`portPower`).
* The PCC (measurement behind `x_up`) case is covered only for a lossless link
  (`lagRatio_lossless`); the resistive PCC terms of (16) are not formalized.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §4.4 (`p ≈ K_s δ − K_d δ̇`, `d₁ ↦ d₁ − d₀ τ_net`, (16)
`Ω_m τ_net = (μ/X)[x_up tan δ₀ + 2r_f + (2E/V) r_g/cos δ₀]`), Appendix B (the first-order current).

Results.
* `hasDerivAt_current0`, `firstOrder_step` — `i₀' = jE e^{jδ} δ̇/Z` and `Z i₁ + (X/ω_b) i₀' = 0`:
  `i₀ + i₁` solves the link equation up to `(X/ω_b) i₁'`.
* `portPower_current1` — the first-order current contributes exactly `−K_d δ̇` to the port power,
  `K_d = 2 R X² E²/(ω_b |Z|⁴)` (`lagCoeff`); the static part is
  `Grid.MeasurementPoint.measuredPower_eq` at the port.
* `hasDerivAt_lagRatio` — the port lag ratio `τ = K_d/K`, `K = E V (X cos δ₀ + R sin δ₀)/|Z|²`
  (`lagRatio`), has `dτ/dR = 2E/(ω_b V X cos δ₀)` at `R = 0`: `Ω τ = (μ/X)(2E/V) R/cos δ₀ + O(R²)`,
  the `r_g` term of (16) for port measurement (all resistance downstream).
* `lagRatio_lossless` — lossless link, measurement behind `x_up`: `τ = (x_up/X) tan Ψ/ω_b`, the
  `x_up tan δ₀` term of (16).

Corrections.
* At the port the exact first-order lag is `τ = 2RX²E/(ω_b V |Z|² (X cos δ₀ + R sin δ₀))`; (16)
  gives its first-order term in `R/X`.

Family and connection conclusions.
None: static evidence (first-order network expansion of the port power).
-/

noncomputable section
namespace powerlib.GFM
namespace NetworkLag
open Complex ComplexConjugate

/-- Series impedance `Z = R + jX`. -/
def imp (R X : ℝ) : ℂ := (R : ℂ) + (X : ℂ) * I

/-- Quasi-static current `i₀ = (E e^{jδ} − V)/Z`. -/
def current0 (E V R X δ : ℝ) : ℂ := ((E : ℂ) * exp ((δ : ℂ) * I) - V) / imp R X

/-- First-order correction `i₁ = −(X/ω_b) i₀'/Z` along an angle with rate `δ̇`. -/
def current1 (E R X ωb δ δd : ℝ) : ℂ :=
  -((X / ωb : ℝ) : ℂ) * (I * E * exp ((δ : ℂ) * I) * δd / imp R X) / imp R X

/-- Port power `Re(E e^{jδ} conj i)`. -/
def portPower (E δ : ℝ) (i : ℂ) : ℝ := ((E : ℂ) * exp ((δ : ℂ) * I) * conj i).re

@[tmio M, powerlib_domain] theorem imp_ne_zero {R X : ℝ} (hX : X ≠ 0) : imp R X ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp [imp] at this; exact hX this

/-- `i₀` along a differentiable angle: `i₀' = jE e^{jδ} δ̇/Z`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_current0 (E V R X : ℝ) {δ : ℝ → ℝ} {δd t : ℝ}
    (hδ : HasDerivAt δ δd t) :
    HasDerivAt (fun t => current0 E V R X (δ t))
      (I * E * exp ((δ t : ℂ) * I) * δd / imp R X) t := by
  have h1 : HasDerivAt (fun t => ((δ t : ℝ) : ℂ) * I) ((δd : ℂ) * I) t :=
    hδ.ofReal_comp.mul_const I
  have h2 := ((h1.cexp.const_mul (E : ℂ)).sub_const (V : ℂ)).div_const (imp R X)
  convert h2 using 1
  · funext t; simp [current0]
  · ring

/-- The first-order step is exact: `Z i₁ + (X/ω_b) i₀' = 0`, so `i₀ + i₁` solves
`(X/ω_b) i' + Z i = E e^{jδ} − V` up to `(X/ω_b) i₁'`, which is second order in `d/dt ÷ ω_b`. -/
@[tmio M, powerlib_domain] theorem firstOrder_step {E R X ωb δ δd : ℝ} (hX : X ≠ 0) :
    imp R X * current1 E R X ωb δ δd +
      ((X / ωb : ℝ) : ℂ) * (I * E * exp ((δ : ℂ) * I) * δd / imp R X) = 0 := by
  have hZ := imp_ne_zero (R := R) hX
  simp only [current1]
  field_simp
  ring

/-- The lag coefficient of the port power, `K_d = 2 R X² E²/(ω_b |Z|⁴)`. -/
def lagCoeff (E R X ωb : ℝ) : ℝ := 2 * R * X ^ 2 * E ^ 2 / (ωb * (R ^ 2 + X ^ 2) ^ 2)

/-- The first-order current contributes `−K_d δ̇` to the port power: `p = P₀(δ) − K_d δ̇`. -/
@[tmio M, powerlib_domain] theorem portPower_current1 (E R X ωb δ δd : ℝ) (hX : X ≠ 0) :
    portPower E δ (current1 E R X ωb δ δd) = -(lagCoeff E R X ωb * δd) := by
  have hZ := imp_ne_zero (R := R) hX
  have hRX : R ^ 2 + X ^ 2 ≠ 0 := by positivity
  have hw : exp ((δ : ℂ) * I) * conj (exp ((δ : ℂ) * I)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; simp
  have hZc : conj (imp R X) = (R : ℂ) - X * I := by
    simp [imp, map_add, map_mul, conj_ofReal, conj_I]; ring
  have hZc0 : (R : ℂ) - X * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX this
  have e : (E : ℂ) * exp ((δ : ℂ) * I) * conj (current1 E R X ωb δ δd) =
      ((X / ωb * E ^ 2 * δd : ℝ) : ℂ) * I / ((R : ℂ) - X * I) ^ 2 := by
    simp only [current1, map_div₀, map_mul, map_neg, conj_ofReal, conj_I, hZc]
    rw [show (E : ℂ) * exp ((δ : ℂ) * I) *
        (-((X / ωb : ℝ) : ℂ) * (-I * E * conj (exp ((δ : ℂ) * I)) * δd / ((R : ℂ) - X * I)) /
          ((R : ℂ) - X * I)) =
        ((X / ωb : ℝ) : ℂ) * I * E ^ 2 * δd * (exp ((δ : ℂ) * I) * conj (exp ((δ : ℂ) * I))) /
          ((R : ℂ) - X * I) ^ 2 by field_simp, hw]
    push_cast
    field_simp
  have hsq : ((R : ℂ) - X * I) ^ 2 = ((R ^ 2 - X ^ 2 : ℝ) : ℂ) + ((-2 * R * X : ℝ) : ℂ) * I := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [portPower, e, hsq, Complex.div_re]
  have hn : Complex.normSq (((R ^ 2 - X ^ 2 : ℝ) : ℂ) + ((-2 * R * X : ℝ) : ℂ) * I) =
      (R ^ 2 + X ^ 2) ^ 2 := by
    rw [Complex.normSq_add_mul_I]; ring
  rw [hn]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.add_re, Complex.add_im]
  rw [lagCoeff]
  rcases eq_or_ne ωb 0 with h0 | h0
  · simp [h0]
  field_simp
  ring

/-- The lag ratio `τ = K_d/K` of the port power, with `K = E V (X cos δ₀ + R sin δ₀)/|Z|²` the
static synchronizing coefficient (`Grid.MeasurementPoint.deriv_measuredPower` at the port):
`τ = 2 R X² E/(ω_b V |Z|² (X cos δ₀ + R sin δ₀))`. -/
def lagRatio (E V X ωb δ0 R : ℝ) : ℝ :=
  lagCoeff E R X ωb / (E * V * (X * Real.cos δ0 + R * Real.sin δ0) / (R ^ 2 + X ^ 2))

/-- First order in `R`: `dτ/dR = 2E/(ω_b V X cos δ₀)` at `R = 0`, i.e.
`Ω τ = (μ/X)(2E/V) R/cos δ₀ + O(R²)`: the resistive term of (16) for port measurement. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_lagRatio {E V X ωb δ0 : ℝ} (hE : E ≠ 0) (hV : V ≠ 0) (hX : X ≠ 0)
    (hωb : ωb ≠ 0) (hc : Real.cos δ0 ≠ 0) :
    HasDerivAt (lagRatio E V X ωb δ0) (2 * E / (ωb * V * X * Real.cos δ0)) 0 := by
  have hform : lagRatio E V X ωb δ0 = fun R =>
      2 * X ^ 2 * E / (ωb * V) * (R / ((R ^ 2 + X ^ 2) * (X * Real.cos δ0 + R * Real.sin δ0))) := by
    funext R
    simp only [lagRatio, lagCoeff]
    rcases eq_or_ne (X * Real.cos δ0 + R * Real.sin δ0) 0 with h | h
    · simp [h]
    have hRX : R ^ 2 + X ^ 2 ≠ 0 := by positivity
    field_simp
  rw [hform]
  have hden : HasDerivAt (fun R : ℝ => (R ^ 2 + X ^ 2) * (X * Real.cos δ0 + R * Real.sin δ0))
      ((2 * 0 * 1) * (X * Real.cos δ0 + 0 * Real.sin δ0) +
        (0 ^ 2 + X ^ 2) * (1 * Real.sin δ0)) 0 := by
    have h1 : HasDerivAt (fun R : ℝ => R ^ 2 + X ^ 2) (2 * 0 * 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).add_const (X ^ 2)
    have h2 : HasDerivAt (fun R : ℝ => X * Real.cos δ0 + R * Real.sin δ0) (1 * Real.sin δ0) 0 :=
      ((hasDerivAt_id (0 : ℝ)).mul_const (Real.sin δ0)).const_add _
    exact h1.mul h2
  have hd0 : (0 ^ 2 + X ^ 2) * (X * Real.cos δ0 + 0 * Real.sin δ0) ≠ 0 := by
    simp [hX, hc]
  have h := ((hasDerivAt_id (0 : ℝ)).div hden (by simpa using hd0)).const_mul
    (2 * X ^ 2 * E / (ωb * V))
  convert h using 1
  · funext R; rfl
  · have hid : (id (0 : ℝ)) = 0 := rfl
    rw [hid]
    norm_num
    field_simp

/-- Lossless link measured behind `x_up` (`K_d = x_up E V sin Ψ/(ω_b X²)`,
`DroopSideband.hasDerivAt_shortcut`; `K = E V cos Ψ/X`): `τ = K_d/K = (x_up/X) tan Ψ/ω_b`, the first
term of (16), `Ω τ = μ (x_up/X) tan δ₀`. -/
@[tmio M, powerlib_domain] theorem lagRatio_lossless {E V X xup ωb Ψ : ℝ} (hE : E ≠ 0) (hV : V ≠ 0) (hX : X ≠ 0)
    (hc : Real.cos Ψ ≠ 0) :
    (xup * E * V * Real.sin Ψ / (ωb * X ^ 2)) / (E * V * Real.cos Ψ / X) =
      xup / X * Real.tan Ψ / ωb := by
  rw [Real.tan_eq_sin_div_cos]
  rcases eq_or_ne ωb 0 with h0 | h0
  · simp [h0]
  field_simp

end NetworkLag
end powerlib.GFM
