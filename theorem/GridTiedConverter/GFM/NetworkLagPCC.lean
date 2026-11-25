import theorem.GridTiedConverter.GFM.NetworkLag

/-! # The network lag at the PCC: the resistive terms of (16)

The first-order network lag `p ≈ K δ − K_d δ̇` of `NetworkLag` for power measured at the PCC, with
a resistive filter `Z_f = r_f + j x_f` upstream of the measurement and a resistive grid link
`Z_g = r_g + j x_g` downstream. The lag coefficient `K_d` is derived exactly from the first-order
current, the lag ratio `τ = K_d/K` is closed in form, and its first-order coefficients in the
resistances are computed along every direction `(r_f, r_g) = t (a_f, a_g)`.

Model boundary.
* EMF `E e^{jδ(t)}` (constant amplitude), link `Z = Z_f + Z_g` with total reactance
  `X = x_f + x_g` in the frame of `ω_b`, grid voltage `V` (constant angle); the first-order current
  `i₀ + i₁` of `NetworkLag` (`current0`, `current1`, `firstOrder_step`).
* PCC power `p_M = Re((E e^{jδ} − Z_f i − (x_f/ω_b) i') ī)` (`pccPower`, the voltage behind the
  filter); along `i₀ + i₁` with `i' ≈ i₀'` the terms of second order in `d/dt ÷ ω_b` are identified
  (`pccPower_expand`) and excluded.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §4.4, (16):
`Ω_m τ_net = (μ/X)[x_up tan δ₀ + 2r_f + (2E/V) r_g/cos δ₀]`, `x_up = x_f` for PCC measurement,
and (17) `D_ss^full ≈ D_ss^qs (1 + ω_c τ_net)`.

Results.
* `re_current0_conj_current1` (`Re(i₀ ī₁)`), `re_dcurrent0_conj_current0` (`Re(i₀' ī₀)`).
* `pccPower_expand` — quasi-static part + `pccFirst` + second-order terms.
* `pccFirst_eq` — `pccFirst = −K_d δ̇`,
  `K_d = E[2E r_g X² + 2V cos δ r_f X² + V sin δ (x_f r² + x_f X² − 2 r_f r X)]/(ω_b |Z|⁴)`.
* `pccPower_static`, `hasDerivAt_pccPower_static` — `K = E V (X cos δ − (r_f − r_g) sin δ)/|Z|²`.
* `pccLagRatio_eq` (closed form of `ω_b X τ`), `pccLagRatio_lossless` (`ω_b X τ = x_f tan δ`).
* `hasDerivAt_pccLagRatio` — `d(ω_b X τ)/dt = 2a_f + (2E/V) a_g/cos δ + (x_f/X) tan² δ (a_f − a_g)`.

Corrections.
* To first order in the resistances,
  `Ω τ = (μ/X)[x_f tan δ₀ + 2r_f + (2E/V) r_g/cos δ₀ + (x_f/X) tan² δ₀ (r_f − r_g)]`:
  (16) omits the last term, `O(δ₀²)` relative to the `r_f` and `r_g` coefficients (about 2% at
  `x_f/X = 0.3`, `δ₀ = 20°`). With no filter upstream (`x_f = 0`, port measurement) (16) is exact
  to first order (`NetworkLag.hasDerivAt_lagRatio`).

Family and connection conclusions.
None: static evidence (first-order network expansion of the PCC power).
-/

noncomputable section
namespace powerlib.GFM
namespace NetworkLag
open Complex ComplexConjugate

@[tmio M, powerlib_domain] theorem exp_conj_split (δ : ℝ) :
    exp ((δ : ℂ) * I) = (Real.cos δ : ℂ) + Real.sin δ * I ∧
      conj (exp ((δ : ℂ) * I)) = (Real.cos δ : ℂ) - Real.sin δ * I := by
  have h : exp ((δ : ℂ) * I) = (Real.cos δ : ℂ) + Real.sin δ * I := by
    rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  refine ⟨h, ?_⟩
  rw [h, map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  ring

/-- The cross term of the first-order current:
`Re(i₀ ī₁) = −(X/ω_b) E δ̇ ((E − V cos δ) X + V sin δ R)/|Z|⁴`. -/
@[tmio M, powerlib_domain] theorem re_current0_conj_current1 (E V R X ωb δ δd : ℝ) (hX : X ≠ 0) :
    (current0 E V R X δ * conj (current1 E R X ωb δ δd)).re =
      -(X / ωb * E * δd * ((E - V * Real.cos δ) * X + V * Real.sin δ * R) / (R ^ 2 + X ^ 2) ^ 2) := by
  obtain ⟨h1, h2⟩ := exp_conj_split δ
  have hZ := imp_ne_zero (R := R) hX
  have hZc : (R : ℂ) - X * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX this
  have hsc := Real.cos_sq_add_sin_sq δ
  simp only [current0, current1, imp, map_div₀, map_mul, map_neg, map_add, conj_ofReal,
    conj_I, h1]
  simp only [imp] at hZ
  generalize Real.cos δ = c at hsc ⊢
  generalize Real.sin δ = s at hsc ⊢
  have hsc' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hsc
  have hZc' : (R : ℂ) + X * -I ≠ 0 := by rw [show (R : ℂ) + X * -I = R - X * I by ring]; exact hZc
  have hN : ((R : ℂ) ^ 2 + (X : ℂ) ^ 2) ≠ 0 := by
    have : R ^ 2 + X ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  rcases eq_or_ne ωb 0 with h0 | h0
  · simp [h0]
  have hωc : (ωb : ℂ) ≠ 0 := by exact_mod_cast h0
  have key : (((E : ℂ) * ((c : ℂ) + (s : ℂ) * I) - V) / ((R : ℂ) + X * I) *
        (-((X / ωb : ℝ) : ℂ) * (-I * E * ((c : ℂ) + s * -I) * δd / ((R : ℂ) + X * -I)) /
          ((R : ℂ) + X * -I))) =
      ((-(X / ωb * E * δd * ((E - V * c) * X + V * s * R) / (R ^ 2 + X ^ 2) ^ 2) : ℝ) : ℂ) +
        (((X / ωb * E * δd * ((E - V * c) * R - V * s * X) / (R ^ 2 + X ^ 2) ^ 2) : ℝ) : ℂ) * I := by
    have hA : (R : ℂ) + I * X ≠ 0 := by rw [mul_comm]; exact hZ
    have hB : (R : ℂ) + -(I * X) ≠ 0 := by
      rw [show (R : ℂ) + -(I * X) = R - X * I by ring]; exact hZc
    push_cast
    field_simp
    linear_combination (-(E : ℂ)*(X : ℂ)*(δd : ℂ)*((E : ℂ)*I^2*(R : ℂ)*(X : ℂ)^3 + (E : ℂ)*I*(R : ℂ)^4*(s : ℂ)^2 + 2*(E : ℂ)*I*(R : ℂ)^2*(X : ℂ)^2*(s : ℂ)^2 - (E : ℂ)*I*(R : ℂ)^2*(X : ℂ)^2 + (E : ℂ)*I*(X : ℂ)^4*(s : ℂ)^2 - (E : ℂ)*I*(X : ℂ)^4 - (E : ℂ)*(R : ℂ)^3*(X : ℂ) - I^2*(R : ℂ)*(V : ℂ)*(X : ℂ)^3*(c : ℂ) - I^2*(V : ℂ)*(X : ℂ)^4*(s : ℂ) + I*(R : ℂ)^2*(V : ℂ)*(X : ℂ)^2*(c : ℂ) + I*(V : ℂ)*(X : ℂ)^4*(c : ℂ) - (R : ℂ)^4*(V : ℂ)*(s : ℂ) + (R : ℂ)^3*(V : ℂ)*(X : ℂ)*(c : ℂ))) * I_sq + ((E : ℂ)^2*I*(X : ℂ)*(δd : ℂ)*((R : ℂ)^2 + (X : ℂ)^2)^2) * hsc'
  rw [key]
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
  ring

/-- The reactive-energy term: `Re(i₀' ī₀) = V E sin δ δ̇/|Z|²`, `i₀' = jE e^{jδ} δ̇/Z`. -/
@[tmio M, powerlib_domain] theorem re_dcurrent0_conj_current0 (E V R X δ δd : ℝ) (hX : X ≠ 0) :
    (I * E * exp ((δ : ℂ) * I) * δd / imp R X * conj (current0 E V R X δ)).re =
      V * E * Real.sin δ * δd / (R ^ 2 + X ^ 2) := by
  obtain ⟨h1, h2⟩ := exp_conj_split δ
  have hZ := imp_ne_zero (R := R) hX
  have hZc : (R : ℂ) - X * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX this
  have hsc := Real.cos_sq_add_sin_sq δ
  simp only [current0, imp, map_div₀, map_mul, map_sub, map_add, conj_ofReal, conj_I, h1]
  simp only [imp] at hZ
  generalize Real.cos δ = c at hsc ⊢
  generalize Real.sin δ = s at hsc ⊢
  have hsc' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hsc
  have hN : ((R : ℂ) ^ 2 + (X : ℂ) ^ 2) ≠ 0 := by
    have : R ^ 2 + X ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  have key : I * E * ((c : ℂ) + s * I) * δd / ((R : ℂ) + X * I) *
        (((E : ℂ) * ((c : ℂ) + s * -I) - V) / ((R : ℂ) + X * -I)) =
      (((V * E * s * δd / (R ^ 2 + X ^ 2)) : ℝ) : ℂ) +
        (((E * δd * (E - V * c) / (R ^ 2 + X ^ 2)) : ℝ) : ℂ) * I := by
    have hA : (R : ℂ) + I * X ≠ 0 := by rw [mul_comm]; exact hZ
    have hB : (R : ℂ) + -(I * X) ≠ 0 := by
      rw [show (R : ℂ) + -(I * X) = R - X * I by ring]; exact hZc
    push_cast
    field_simp
    linear_combination (-(E : ℂ)*(δd : ℂ)*((E : ℂ)*I*(R : ℂ)^2*(s : ℂ)^2 + (E : ℂ)*I*(X : ℂ)^2*(s : ℂ)^2 - (E : ℂ)*I*(X : ℂ)^2 + I*(V : ℂ)*(X : ℂ)^2*(c : ℂ) + (R : ℂ)^2*(V : ℂ)*(s : ℂ))) * I_sq + ((E : ℂ)^2*I*(δd : ℂ)*((R : ℂ)^2 + (X : ℂ)^2)) * hsc'
  rw [key]
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
  ring

/-! ### Measurement at the PCC -/

/-- Power measured at the PCC behind the filter `Z_f = r_f + j x_f`:
`p_M = Re((E e^{jδ} − Z_f i − (x_f/ω_b) i') ī)`. -/
def pccPower (E rf xf ωb δ : ℝ) (i di : ℂ) : ℝ :=
  (((E : ℂ) * exp ((δ : ℂ) * I) - ((rf : ℂ) + xf * I) * i - ((xf / ωb : ℝ) : ℂ) * di) * conj i).re

/-- The part of the PCC power linear in `δ̇` for the first-order current of the link
`Z = (r_f + r_g) + j(x_f + x_g)`. -/
def pccFirst (E V rf rg xf xg ωb δ δd : ℝ) : ℝ :=
  portPower E δ (current1 E (rf + rg) (xf + xg) ωb δ δd) -
    (((rf : ℂ) + xf * I) * (current0 E V (rf + rg) (xf + xg) δ *
        conj (current1 E (rf + rg) (xf + xg) ωb δ δd) +
      current1 E (rf + rg) (xf + xg) ωb δ δd * conj (current0 E V (rf + rg) (xf + xg) δ))).re -
    xf / ωb * (I * E * exp ((δ : ℂ) * I) * δd / imp (rf + rg) (xf + xg) *
      conj (current0 E V (rf + rg) (xf + xg) δ)).re

/-- The PCC power along the first-order current `i₀ + i₁` (with `i' ≈ i₀'`) is the quasi-static
power, the first-order part `pccFirst`, and terms of second order in `d/dt ÷ ω_b`. -/
@[tmio M, powerlib_domain] theorem pccPower_expand (E V rf rg xf xg ωb δ δd : ℝ) :
    pccPower E rf xf ωb δ
        (current0 E V (rf + rg) (xf + xg) δ + current1 E (rf + rg) (xf + xg) ωb δ δd)
        (I * E * exp ((δ : ℂ) * I) * δd / imp (rf + rg) (xf + xg)) =
      pccPower E rf xf ωb δ (current0 E V (rf + rg) (xf + xg) δ) 0 +
        pccFirst E V rf rg xf xg ωb δ δd -
        ((((rf : ℂ) + xf * I) * current1 E (rf + rg) (xf + xg) ωb δ δd *
            conj (current1 E (rf + rg) (xf + xg) ωb δ δd)).re +
          xf / ωb * (I * E * exp ((δ : ℂ) * I) * δd / imp (rf + rg) (xf + xg) *
            conj (current1 E (rf + rg) (xf + xg) ωb δ δd)).re) := by
  simp only [pccPower, pccFirst, portPower, map_add, mul_zero, sub_zero]
  simp only [← re_ofReal_mul, ← add_re, ← sub_re]
  congr 1
  ring

/-- The lag coefficient at the PCC:
`K_d = E[2E r_g X² + 2V cos δ r_f X² + V sin δ (x_f r² + x_f X² − 2 r_f r X)]/(ω_b |Z|⁴)`,
`r = r_f + r_g`, `X = x_f + x_g`. -/
def pccLagCoeff (E V rf rg xf xg ωb δ : ℝ) : ℝ :=
  E * (2 * E * rg * (xf + xg) ^ 2 + 2 * V * Real.cos δ * rf * (xf + xg) ^ 2 +
      V * Real.sin δ * (xf * (rf + rg) ^ 2 + xf * (xf + xg) ^ 2 - 2 * rf * (rf + rg) * (xf + xg))) /
    (ωb * ((rf + rg) ^ 2 + (xf + xg) ^ 2) ^ 2)

/-- The first-order current contributes exactly `−K_d δ̇` to the PCC power. -/
@[tmio M, powerlib_domain] theorem pccFirst_eq (E V rf rg xf xg ωb δ δd : ℝ) (hX : xf + xg ≠ 0) :
    pccFirst E V rf rg xf xg ωb δ δd = -(pccLagCoeff E V rf rg xf xg ωb δ * δd) := by
  have hcross : current1 E (rf + rg) (xf + xg) ωb δ δd * conj (current0 E V (rf + rg) (xf + xg) δ) =
      conj (current0 E V (rf + rg) (xf + xg) δ * conj (current1 E (rf + rg) (xf + xg) ωb δ δd)) := by
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [pccFirst, portPower_current1 _ _ _ _ _ _ hX, re_dcurrent0_conj_current0 _ _ _ _ _ _ hX,
    hcross, Complex.add_conj, Complex.re_mul_ofReal, re_current0_conj_current1 _ _ _ _ _ _ _ hX]
  have hre : ((rf : ℂ) + xf * I).re = rf := by simp
  rw [hre]
  simp only [lagCoeff, pccLagCoeff]
  have hN : (rf + rg) ^ 2 + (xf + xg) ^ 2 ≠ 0 := by positivity
  rcases eq_or_ne ωb 0 with h0 | h0
  · simp [h0]
  field_simp
  ring

/-- The quasi-static PCC power `P₀(δ) = [E V (X sin δ + (r_f − r_g) cos δ) + r_g E² − r_f V²]/|Z|²`
(`Grid.MeasurementPoint.measuredPower_eq` with `Z_u = Z_f`, `Z_d = Z_g`). -/
@[tmio M, powerlib_domain] theorem pccPower_static (E V rf rg xf xg ωb δ : ℝ) (hX : xf + xg ≠ 0) :
    pccPower E rf xf ωb δ (current0 E V (rf + rg) (xf + xg) δ) 0 =
      (E * V * ((xf + xg) * Real.sin δ + (rf - rg) * Real.cos δ) + rg * E ^ 2 - rf * V ^ 2) /
        ((rf + rg) ^ 2 + (xf + xg) ^ 2) := by
  obtain ⟨h1, h2⟩ := exp_conj_split δ
  have hZ := imp_ne_zero (R := rf + rg) hX
  have hZc : ((rf : ℂ) + rg) - ((xf : ℂ) + xg) * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX (by linarith)
  have hsc := Real.cos_sq_add_sin_sq δ
  simp only [pccPower, current0, imp, map_div₀, map_mul, map_sub, map_add, conj_ofReal, conj_I, h1,
    mul_zero, sub_zero]
  simp only [imp] at hZ
  generalize Real.cos δ = c at hsc ⊢
  generalize Real.sin δ = s at hsc ⊢
  push_cast at hZ ⊢
  have hsc' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hsc
  have hN : (((rf : ℂ) + rg) ^ 2 + ((xf : ℂ) + xg) ^ 2) ≠ 0 := by
    have : (rf + rg) ^ 2 + (xf + xg) ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  have hA : (rf : ℂ) + rg + I * (xf + xg) ≠ 0 := by
    rw [show (rf : ℂ) + rg + I * (xf + xg) = (rf + rg) + (xf + xg) * I by ring]; exact hZ
  have hB : (rf : ℂ) + rg + -(I * (xf + xg)) ≠ 0 := by
    rw [show (rf : ℂ) + rg + -(I * (xf + xg)) = (rf + rg) - (xf + xg) * I by ring]; exact hZc
  have key : ((E : ℂ) * ((c : ℂ) + s * I) - ((rf : ℂ) + xf * I) *
        (((E : ℂ) * ((c : ℂ) + s * I) - V) / ((rf : ℂ) + rg + (xf + xg) * I))) *
        (((E : ℂ) * ((c : ℂ) + s * -I) - V) / ((rf : ℂ) + rg + (xf + xg) * -I)) =
      (((E * V * ((xf + xg) * s + (rf - rg) * c) + rg * E ^ 2 - rf * V ^ 2) /
        ((rf + rg) ^ 2 + (xf + xg) ^ 2) : ℝ) : ℂ) +
      (((E ^ 2 * xg + E * V * c * xf - E * V * c * xg - E * V * s * (rf + rg) - V ^ 2 * xf) /
        ((rf + rg) ^ 2 + (xf + xg) ^ 2) : ℝ) : ℂ) * I := by
    push_cast
    field_simp
    linear_combination (-(E : ℂ)^2*I*(rf : ℂ)^2*(s : ℂ)^2*(xg : ℂ) - 2*(E : ℂ)^2*I*(rf : ℂ)*(rg : ℂ)*(s : ℂ)^2*(xg : ℂ) - (E : ℂ)^2*I*(rg : ℂ)^2*(s : ℂ)^2*(xg : ℂ) - (E : ℂ)^2*I*(s : ℂ)^2*(xf : ℂ)^2*(xg : ℂ) - 2*(E : ℂ)^2*I*(s : ℂ)^2*(xf : ℂ)*(xg : ℂ)^2 - (E : ℂ)^2*I*(s : ℂ)^2*(xg : ℂ)^3 + (E : ℂ)^2*I*(xf : ℂ)^2*(xg : ℂ) + 2*(E : ℂ)^2*I*(xf : ℂ)*(xg : ℂ)^2 + (E : ℂ)^2*I*(xg : ℂ)^3 - (E : ℂ)^2*(rf : ℂ)^2*(rg : ℂ)*(s : ℂ)^2 - 2*(E : ℂ)^2*(rf : ℂ)*(rg : ℂ)^2*(s : ℂ)^2 - (E : ℂ)^2*(rg : ℂ)^3*(s : ℂ)^2 - (E : ℂ)^2*(rg : ℂ)*(s : ℂ)^2*(xf : ℂ)^2 - 2*(E : ℂ)^2*(rg : ℂ)*(s : ℂ)^2*(xf : ℂ)*(xg : ℂ) - (E : ℂ)^2*(rg : ℂ)*(s : ℂ)^2*(xg : ℂ)^2 + (E : ℂ)^2*(rg : ℂ)*(xf : ℂ)^2 + 2*(E : ℂ)^2*(rg : ℂ)*(xf : ℂ)*(xg : ℂ) + (E : ℂ)^2*(rg : ℂ)*(xg : ℂ)^2 + (E : ℂ)*I*(V : ℂ)*(c : ℂ)*(xf : ℂ)^3 + (E : ℂ)*I*(V : ℂ)*(c : ℂ)*(xf : ℂ)^2*(xg : ℂ) - (E : ℂ)*I*(V : ℂ)*(c : ℂ)*(xf : ℂ)*(xg : ℂ)^2 - (E : ℂ)*I*(V : ℂ)*(c : ℂ)*(xg : ℂ)^3 - (E : ℂ)*I*(V : ℂ)*(rf : ℂ)*(s : ℂ)*(xf : ℂ)^2 - 2*(E : ℂ)*I*(V : ℂ)*(rf : ℂ)*(s : ℂ)*(xf : ℂ)*(xg : ℂ) - (E : ℂ)*I*(V : ℂ)*(rf : ℂ)*(s : ℂ)*(xg : ℂ)^2 - (E : ℂ)*I*(V : ℂ)*(rg : ℂ)*(s : ℂ)*(xf : ℂ)^2 - 2*(E : ℂ)*I*(V : ℂ)*(rg : ℂ)*(s : ℂ)*(xf : ℂ)*(xg : ℂ) - (E : ℂ)*I*(V : ℂ)*(rg : ℂ)*(s : ℂ)*(xg : ℂ)^2 + (E : ℂ)*(V : ℂ)*(c : ℂ)*(rf : ℂ)*(xf : ℂ)^2 + 2*(E : ℂ)*(V : ℂ)*(c : ℂ)*(rf : ℂ)*(xf : ℂ)*(xg : ℂ) + (E : ℂ)*(V : ℂ)*(c : ℂ)*(rf : ℂ)*(xg : ℂ)^2 - (E : ℂ)*(V : ℂ)*(c : ℂ)*(rg : ℂ)*(xf : ℂ)^2 - 2*(E : ℂ)*(V : ℂ)*(c : ℂ)*(rg : ℂ)*(xf : ℂ)*(xg : ℂ) - (E : ℂ)*(V : ℂ)*(c : ℂ)*(rg : ℂ)*(xg : ℂ)^2 - (E : ℂ)*(V : ℂ)*(rf : ℂ)^2*(s : ℂ)*(xf : ℂ) - (E : ℂ)*(V : ℂ)*(rf : ℂ)^2*(s : ℂ)*(xg : ℂ) - 2*(E : ℂ)*(V : ℂ)*(rf : ℂ)*(rg : ℂ)*(s : ℂ)*(xf : ℂ) - 2*(E : ℂ)*(V : ℂ)*(rf : ℂ)*(rg : ℂ)*(s : ℂ)*(xg : ℂ) - (E : ℂ)*(V : ℂ)*(rg : ℂ)^2*(s : ℂ)*(xf : ℂ) - (E : ℂ)*(V : ℂ)*(rg : ℂ)^2*(s : ℂ)*(xg : ℂ) - I*(V : ℂ)^2*(xf : ℂ)^3 - 2*I*(V : ℂ)^2*(xf : ℂ)^2*(xg : ℂ) - I*(V : ℂ)^2*(xf : ℂ)*(xg : ℂ)^2 - (V : ℂ)^2*(rf : ℂ)*(xf : ℂ)^2 - 2*(V : ℂ)^2*(rf : ℂ)*(xf : ℂ)*(xg : ℂ) - (V : ℂ)^2*(rf : ℂ)*(xg : ℂ)^2) * I_sq + ((E : ℂ)^2*(I*(xg : ℂ) + (rg : ℂ))*((rf : ℂ)^2 + 2*(rf : ℂ)*(rg : ℂ) + (rg : ℂ)^2 + (xf : ℂ)^2 + 2*(xf : ℂ)*(xg : ℂ) + (xg : ℂ)^2)) * hsc'
  rw [key]
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
  ring

/-- The synchronizing coefficient at the PCC: `K = dP₀/dδ = E V (X cos δ − (r_f − r_g) sin δ)/|Z|²`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_pccPower_static (E V rf rg xf xg ωb δ : ℝ)
    (hX : xf + xg ≠ 0) :
    HasDerivAt (fun δ => pccPower E rf xf ωb δ (current0 E V (rf + rg) (xf + xg) δ) 0)
      (E * V * ((xf + xg) * Real.cos δ - (rf - rg) * Real.sin δ) / ((rf + rg) ^ 2 + (xf + xg) ^ 2))
      δ := by
  have hfun : (fun δ => pccPower E rf xf ωb δ (current0 E V (rf + rg) (xf + xg) δ) 0) = fun δ =>
      (E * V * ((xf + xg) * Real.sin δ + (rf - rg) * Real.cos δ) + rg * E ^ 2 - rf * V ^ 2) /
        ((rf + rg) ^ 2 + (xf + xg) ^ 2) :=
    funext fun δ => pccPower_static E V rf rg xf xg ωb δ hX
  rw [hfun]
  have h := (((((Real.hasDerivAt_sin δ).const_mul (xf + xg)).add
    ((Real.hasDerivAt_cos δ).const_mul (rf - rg))).const_mul (E * V)).add_const (rg * E ^ 2)).sub_const
    (rf * V ^ 2) |>.div_const ((rf + rg) ^ 2 + (xf + xg) ^ 2)
  convert h using 2
  ring

/-- The PCC lag ratio `τ = K_d/K`. -/
def pccLagRatio (E V xf xg ωb δ rf rg : ℝ) : ℝ :=
  pccLagCoeff E V rf rg xf xg ωb δ /
    (E * V * ((xf + xg) * Real.cos δ - (rf - rg) * Real.sin δ) / ((rf + rg) ^ 2 + (xf + xg) ^ 2))

/-- Lossless link at the PCC: `ω_b X τ = x_f tan δ`, the `x_up tan δ₀` term of (16). -/
@[tmio M, powerlib_domain] theorem pccLagRatio_lossless (E V xf xg ωb δ : ℝ) (hE : E ≠ 0)
    (hV : V ≠ 0) (hX : xf + xg ≠ 0) (hωb : ωb ≠ 0) (hc : Real.cos δ ≠ 0) :
    ωb * (xf + xg) * pccLagRatio E V xf xg ωb δ 0 0 = xf * Real.tan δ := by
  rw [Real.tan_eq_sin_div_cos]
  simp only [pccLagRatio, pccLagCoeff]
  field_simp
  ring

@[tmio M, powerlib_domain] theorem pccLagRatio_eq (E V xf xg ωb δ rf rg : ℝ) (hE : E ≠ 0)
    (hV : V ≠ 0) (hX : xf + xg ≠ 0) (hωb : ωb ≠ 0) :
    ωb * (xf + xg) * pccLagRatio E V xf xg ωb δ rf rg =
      (xf + xg) * (2 * E * rg * (xf + xg) ^ 2 + 2 * V * Real.cos δ * rf * (xf + xg) ^ 2 +
        V * Real.sin δ * (xf * (rf + rg) ^ 2 + xf * (xf + xg) ^ 2 - 2 * rf * (rf + rg) * (xf + xg))) /
      (V * ((rf + rg) ^ 2 + (xf + xg) ^ 2) *
        ((xf + xg) * Real.cos δ - (rf - rg) * Real.sin δ)) := by
  have hN : (rf + rg) ^ 2 + (xf + xg) ^ 2 ≠ 0 := by positivity
  simp only [pccLagRatio, pccLagCoeff]
  rcases eq_or_ne ((xf + xg) * Real.cos δ - (rf - rg) * Real.sin δ) 0 with h | h
  · rw [h]; simp
  field_simp

@[tmio T, powerlib_foundation] theorem hasDerivAt_quad (c0 c1 c2 : ℝ) :
    HasDerivAt (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2) c1 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).const_mul c1).const_add c0).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul c2)
  convert h using 1
  · funext t; simp
  · simp

/-- The resistive terms of (16) at the PCC, exactly to first order: along every direction
`(r_f, r_g) = t (a_f, a_g)`,
`d(ω_b X τ)/dt = 2 a_f + (2E/V) a_g/cos δ + (x_f/X) tan² δ (a_f − a_g)` at `t = 0`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_pccLagRatio (E V xf xg ωb δ af ag : ℝ) (hE : E ≠ 0)
    (hV : V ≠ 0) (hX : xf + xg ≠ 0) (hωb : ωb ≠ 0) (hc : Real.cos δ ≠ 0) :
    HasDerivAt (fun t => ωb * (xf + xg) * pccLagRatio E V xf xg ωb δ (t * af) (t * ag))
      (2 * af + 2 * E / V * ag / Real.cos δ + xf / (xf + xg) * Real.tan δ ^ 2 * (af - ag)) 0 := by
  have hfun : (fun t => ωb * (xf + xg) * pccLagRatio E V xf xg ωb δ (t * af) (t * ag)) = fun t =>
      ((xf + xg) * (V * Real.sin δ * xf * (xf + xg) ^ 2) +
          (xf + xg) * (2 * E * ag * (xf + xg) ^ 2 + 2 * V * Real.cos δ * af * (xf + xg) ^ 2) * t +
          (xf + xg) * (V * Real.sin δ * (xf * (af + ag) ^ 2 - 2 * af * (af + ag) * (xf + xg))) * t ^ 2) /
        ((V * (xf + xg) ^ 2 + 0 * t + V * (af + ag) ^ 2 * t ^ 2) *
          (Real.cos δ * (xf + xg) + (-(af - ag) * Real.sin δ) * t + 0 * t ^ 2)) := by
    funext t
    rw [pccLagRatio_eq E V xf xg ωb δ _ _ hE hV hX hωb]
    congr 1
    · ring
    · ring
  rw [hfun]
  have hn := hasDerivAt_quad ((xf + xg) * (V * Real.sin δ * xf * (xf + xg) ^ 2))
    ((xf + xg) * (2 * E * ag * (xf + xg) ^ 2 + 2 * V * Real.cos δ * af * (xf + xg) ^ 2))
    ((xf + xg) * (V * Real.sin δ * (xf * (af + ag) ^ 2 - 2 * af * (af + ag) * (xf + xg))))
  have hm := (hasDerivAt_quad (V * (xf + xg) ^ 2) 0 (V * (af + ag) ^ 2)).mul
    (hasDerivAt_quad (Real.cos δ * (xf + xg)) (-(af - ag) * Real.sin δ) 0)
  have hm0 : (V * (xf + xg) ^ 2 + 0 * 0 + V * (af + ag) ^ 2 * 0 ^ 2) *
      (Real.cos δ * (xf + xg) + (-(af - ag) * Real.sin δ) * 0 + 0 * 0 ^ 2) ≠ 0 := by
    simp [hV, hX, hc]
  have h := hn.div hm hm0
  convert h using 1
  simp only [Pi.mul_apply]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

end NetworkLag
end powerlib.GFM
