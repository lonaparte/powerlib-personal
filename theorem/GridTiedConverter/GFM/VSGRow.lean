import theorem.ParametricResonance.ThirdOrderCore
import theorem.Modal.Sensitivity

/-! # VSG: the 2:1 kinematic factor off the Hopf point and the damping slope

The VSG row of Table 6 and the VSG threshold of Table 12 on the VSG loop
`s(s + a)(s + ω_c) + d₀` (`a = D/2H`, `d₀ = ω₀ω_c K_s/2H`). The 2:1 kinematic factor of every
third-order loop is derived exactly off the Hopf point (`loopSensitivity_root`); on the VSG loop
it is a function of `ε = Ω/ω_c` and `s = σ/Ω` only (`vsg_root`), whose first-order expansion is
proved as a Fréchet derivative (`vsg_row_firstOrder`). The damping slope `dσ/dD` at the Hopf point
is derived from the root branch of the mode (`vsg_slope`, `vsg_decay_slope`).

Scope.
* Real cubics `s³ + d₂s² + d₁s + d₀` with roots `−p`, `−σ ± jΩ`
  (`ThirdOrder.coeff2`, `coeff1`, `coeff0`) and their sensitivity
  `S(s) = s(s² + d₂s + d₁)/(s³ + d₂s² + d₁s + d₀)` (`ThirdOrder.loopSensitivity`) at `s = 2jΩ`.
* The VSG loop: `d₂ = a + ω_c`, `d₁ = a ω_c` (the core `(θ, Δω, P_f)` of §3 with a quasi-static
  network; `DroopTwoFilter` relates it to droop).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (VSG core), Table 3 (droop `β_L ≈ √χ/(1 + χ) ∈ [0.15, 0.5]`,
VSG `κ_H ≈ 1 − D_ss/D`), Table 6 (VSG row `4/3 − (2j/3)Ω_m/ω_c + (4j/9)σ_m/Ω_m`), Table 12 (VSG
threshold `≈ (3/(2P)) √(K_s/(2Hω₀)) (D − D_ss)`), and the VSG single report's
`σ_m ≈ D/4H − Ω_m²/(2ω_c) − (D/2H)²/(2ω_c)` quoted in §4.1.

Results.
* `hasFDerivAt_of_partials` — a function of two real variables differentiable at `0` with
  partial derivatives `a`, `b` has the Fréchet derivative `v ↦ v₁ a + v₂ b`.
* `loopSensitivity_root` — exact: `S(2jΩ) = 1 − (1 + s²)/((1 + 2jβ)(s² + 4js − 3))`,
  `β = Ω/p`, `s = σ/Ω` (`kinFactor`), for every third-order loop.
* `vsg_root` — on the VSG loop `a/Ω = (ε(1 − 3s²) + 2s)/(1 − 2sε)` (`vsgX`),
  `β = ε/(1 + ε(x − 2s))` (`vsgBeta`), and `S(2jΩ) = kinFactor(β(ε, s), s)`.
* `kinFactor_zero`, `hasDerivAt_kin_eps`, `hasDerivAt_kin_sigma`, `vsg_row_firstOrder` —
  `S = 4/3 − (2j/3) ε + (4j/9) s + o(|ε| + |s|)`: the VSG row of Table 6.
* `vsg_slope` — at the Hopf point `Ω² = a₀ω_c` the mode continues to a differentiable branch
  `λ(a)` with `λ'(a₀) = −(jΩ + ω_c)/(2(jΩ + a₀ + ω_c))` (`Modal.exists_root_branch` on
  `Q(s) + a = 0`, `Q(s) = s + d₀/(s(s + ω_c))`).
* `vsg_decay_slope` — `dσ/da = (ω_c(a₀ + ω_c) + Ω²)/(2((a₀ + ω_c)² + Ω²))` and
  `0 ≤ 1/2 − dσ/da ≤ a₀/(2(a₀ + ω_c))`: `dσ/dD = (1 − θ)/(4H)`, `0 ≤ θ ≤ a₀/(a₀ + ω_c)`, the slope
  of `σ_m ≈ (D − D_ss)/(4H)`.
* `vsg_threshold_chain` — `4(σ/Ω)/((4/3) tan δ₀)` with `σ = (D − D_ss)/(4H)`,
  `Ω = √(ω₀K_s/(2H))`, `tan δ₀ = P/K_s` is exactly `(3/(2P)) √(K_s/(2Hω₀)) (D − D_ss)`.
* `droop_beta_le` — `β_L = √(ω₁ω_m)/(ω₁ + ω_m) = √χ/(1 + χ) ≤ 1/2`.

Corrections.
None: the VSG row of Table 6, the threshold chain of Table 12 and the droop bound `β_L ≤ 1/2` are
confirmed; the slope `1/(4H)` of `σ_m` in `D` holds to first order in `a₀/ω_c` (`vsg_decay_slope`).

Family and connection conclusions.
None: static evidence on the third-order loop (sensitivity, root branch).
-/

noncomputable section
namespace powerlib.GFM
namespace VSGRow
open Complex Filter Topology
open powerlib.ParametricResonance.ThirdOrder

/-! ### A first-order expansion in two real variables from its partial derivatives -/

/-- A function of two real variables, differentiable at `0`, with partial derivatives `a` and
`b` there, has the Fréchet derivative `v ↦ v₁ a + v₂ b`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_of_partials {f : ℝ × ℝ → ℂ} {a b : ℂ}
    (hd : DifferentiableAt ℝ f 0) (ha : HasDerivAt (fun t : ℝ => f (t, 0)) a 0)
    (hb : HasDerivAt (fun t : ℝ => f (0, t)) b 0) :
    HasFDerivAt f ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b) 0 := by
  have h := hd.hasFDerivAt
  have l1 : HasDerivAt (fun t : ℝ => ((t, 0) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const _ _)
  have l2 : HasDerivAt (fun t : ℝ => ((0, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) 0 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id (0 : ℝ))
  have h' : HasFDerivAt f (fderiv ℝ f 0) ((0 : ℝ), (0 : ℝ)) := by
    rw [Prod.mk_zero_zero]; exact h
  have c1 := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((t, 0) : ℝ × ℝ)) (0 : ℝ) h' l1
  have c2 := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((0, t) : ℝ × ℝ)) (0 : ℝ) h' l2
  have e1 : fderiv ℝ f 0 (1, 0) = a := c1.unique ha
  have e2 : fderiv ℝ f 0 (0, 1) = b := c2.unique hb
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = v.1 • ((1, 0) : ℝ × ℝ) + v.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  rw [hv]
  simp only [map_add, map_smul, e1, e2]
  simp

/-! ### The 2:1 kinematic factor off the Hopf point -/

/-- `S(2jΩ)` of a third-order loop with roots `−p`, `−σ ± jΩ`, in `β = Ω/p` and `s = σ/Ω`. -/
def kinFactor (β s : ℝ) : ℂ :=
  1 - (1 + (s : ℂ) ^ 2) / ((1 + 2 * (β : ℂ) * I) * ((s : ℂ) ^ 2 + 4 * (s : ℂ) * I - 3))

@[tmio T, powerlib_foundation] theorem kin_den_ne (s : ℝ) : (s : ℂ) ^ 2 + 4 * (s : ℂ) * I - 3 ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  have : s = 0 := by linarith
  subst this
  norm_num at h1

@[tmio T, powerlib_foundation] theorem one_add_two_mul_I_ne (β : ℝ) : 1 + 2 * (β : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- Exact: for every third-order loop with roots `−p`, `−σ ± jΩ` the 2:1 kinematic factor is
`S(2jΩ) = 1 − (1 + s²)/((1 + 2jβ)(s² + 4js − 3))`, `β = Ω/p`, `s = σ/Ω`; at `s = 0` this is
`(4 + 6jβ)/(3 + 6jβ)` (`loopSensitivity_hopf`). -/
@[tmio T, powerlib_foundation] theorem loopSensitivity_root (p σ Ω : ℝ) (hp : p ≠ 0) (hΩ : Ω ≠ 0) :
    loopSensitivity (coeff2 p σ) (coeff1 p σ Ω) (coeff0 p σ Ω) (2 * (Ω : ℂ) * I) =
      kinFactor (Ω / p) (σ / Ω) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hk1 := one_add_two_mul_I_ne (Ω / p)
  have hk2 := kin_den_ne (σ / Ω)
  have hD : (2 * (Ω : ℂ) * I) ^ 3 + (coeff2 p σ : ℂ) * (2 * (Ω : ℂ) * I) ^ 2 +
      (coeff1 p σ Ω : ℂ) * (2 * (Ω : ℂ) * I) + (coeff0 p σ Ω : ℂ) =
      (p * Ω ^ 2 : ℂ) * (1 + 2 * ((Ω / p : ℝ) : ℂ) * I) *
        (((σ / Ω : ℝ) : ℂ) ^ 2 + 4 * ((σ / Ω : ℝ) : ℂ) * I - 3) := by
    rw [cubic_factor]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    linear_combination (8 * (Ω : ℂ) ^ 3 * I) * I_sq
  have hD0 : (p * Ω ^ 2 : ℂ) * (1 + 2 * ((Ω / p : ℝ) : ℂ) * I) *
      (((σ / Ω : ℝ) : ℂ) ^ 2 + 4 * ((σ / Ω : ℝ) : ℂ) * I - 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hpc (pow_ne_zero 2 hΩc)) hk1) hk2
  rw [loopSensitivity, show (2 * (Ω : ℂ) * I) * ((2 * (Ω : ℂ) * I) ^ 2 + (coeff2 p σ : ℂ) *
      (2 * (Ω : ℂ) * I) + (coeff1 p σ Ω : ℂ)) =
      ((2 * (Ω : ℂ) * I) ^ 3 + (coeff2 p σ : ℂ) * (2 * (Ω : ℂ) * I) ^ 2 +
      (coeff1 p σ Ω : ℂ) * (2 * (Ω : ℂ) * I) + (coeff0 p σ Ω : ℂ)) - (coeff0 p σ Ω : ℂ) by ring,
    hD, kinFactor, sub_div, div_self hD0]
  congr 1
  rw [div_eq_div_iff hD0 (mul_ne_zero hk1 hk2)]
  simp only [coeff0]
  push_cast
  field_simp
  ring

/-! ### The VSG loop `s(s + a)(s + ω_c) + d₀` -/

/-- `a/Ω` of the VSG loop in `ε = Ω/ω_c` and `s = σ/Ω` (the imaginary part of the root equation). -/
def vsgX (ε s : ℝ) : ℝ := (ε * (1 - 3 * s ^ 2) + 2 * s) / (1 - 2 * s * ε)
/-- `β = Ω/p` of the VSG loop, `p = ω_c + a − 2σ` the real root. -/
def vsgBeta (ε s : ℝ) : ℝ := ε / (1 + ε * (vsgX ε s - 2 * s))

/-- The VSG loop with the root `−σ + jΩ`: `a/Ω = x(ε, s)`, `β = Ω/p = ε/(1 + ε(x − 2s))`, and the
2:1 kinematic factor is `S(2jΩ) = kinFactor(β(ε, s), s)`, `ε = Ω/ω_c`, `s = σ/Ω`. -/
@[tmio T, powerlib_foundation] theorem vsg_root {a w d0 σ Ω : ℝ} (hΩ : Ω ≠ 0) (hw : w ≠ 0)
    (hw2 : w - 2 * σ ≠ 0) (hp : a + w - 2 * σ ≠ 0)
    (hroot : (-(σ : ℂ) + Ω * I) ^ 3 + ((a + w : ℝ) : ℂ) * (-(σ : ℂ) + Ω * I) ^ 2 +
      ((a * w : ℝ) : ℂ) * (-(σ : ℂ) + Ω * I) + (d0 : ℂ) = 0) :
    a / Ω = vsgX (Ω / w) (σ / Ω) ∧ Ω / (a + w - 2 * σ) = vsgBeta (Ω / w) (σ / Ω) ∧
      loopSensitivity (a + w) (a * w) d0 (2 * (Ω : ℂ) * I) =
        kinFactor (vsgBeta (Ω / w) (σ / Ω)) (σ / Ω) := by
  obtain ⟨h2, h1, h0⟩ := coeffs_of_root hΩ hroot
  have hrel : a * (w - 2 * σ) = Ω ^ 2 - 3 * σ ^ 2 + 2 * σ * w := by
    simp only [coeff1] at h1; nlinarith [h1]
  have hx : a / Ω = vsgX (Ω / w) (σ / Ω) := by
    have hd : 1 - 2 * (σ / Ω) * (Ω / w) ≠ 0 := by
      rw [show 1 - 2 * (σ / Ω) * (Ω / w) = (w - 2 * σ) / w by field_simp]
      exact div_ne_zero hw2 hw
    rw [vsgX, eq_div_iff hd]
    field_simp
    linear_combination hrel
  have hβ : Ω / (a + w - 2 * σ) = vsgBeta (Ω / w) (σ / Ω) := by
    rw [vsgBeta, ← hx]
    have hd : 1 + Ω / w * (a / Ω - 2 * (σ / Ω)) ≠ 0 := by
      rw [show 1 + Ω / w * (a / Ω - 2 * (σ / Ω)) = (a + w - 2 * σ) / w by field_simp; ring]
      exact div_ne_zero hp hw
    rw [div_div, show w * (1 + Ω / w * (a / Ω - 2 * (σ / Ω))) = a + w - 2 * σ by field_simp; ring]
  refine ⟨hx, hβ, ?_⟩
  have e := loopSensitivity_root (a + w - 2 * σ) σ Ω hp hΩ
  rw [← h2, ← h1, ← h0, hβ] at e
  exact e

/-- At `ε = s = 0` the factor is `4/3`. -/
@[tmio T, powerlib_foundation] theorem kinFactor_zero : kinFactor (vsgBeta 0 0) 0 = 4 / 3 := by
  simp only [kinFactor, vsgBeta, vsgX]
  norm_num

@[tmio T, powerlib_foundation] theorem differentiableAt_kin :
    DifferentiableAt ℝ (fun v : ℝ × ℝ => kinFactor (vsgBeta v.1 v.2) v.2) 0 := by
  have hb : DifferentiableAt ℝ (fun v : ℝ × ℝ => vsgBeta v.1 v.2) 0 := by
    simp only [vsgBeta, vsgX]
    fun_prop (disch := simp)
  have hbc : DifferentiableAt ℝ (fun v : ℝ × ℝ => ((vsgBeta v.1 v.2 : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.differentiableAt.comp _ hb
  have hsc : DifferentiableAt ℝ (fun v : ℝ × ℝ => ((v.2 : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.differentiableAt.comp _ (by fun_prop)
  simp only [kinFactor]
  have hk := kin_den_ne ((0 : ℝ × ℝ).2)
  have hk1 := one_add_two_mul_I_ne (vsgBeta (0 : ℝ × ℝ).1 (0 : ℝ × ℝ).2)
  have hnum : DifferentiableAt ℝ (fun v : ℝ × ℝ => 1 + ((v.2 : ℝ) : ℂ) ^ 2) 0 :=
    (hsc.pow 2).const_add 1
  have hden1 : DifferentiableAt ℝ (fun v : ℝ × ℝ => 1 + 2 * ((vsgBeta v.1 v.2 : ℝ) : ℂ) * I) 0 :=
    ((hbc.const_mul (2 : ℂ)).mul_const I).const_add 1
  have hden2 : DifferentiableAt ℝ
      (fun v : ℝ × ℝ => ((v.2 : ℝ) : ℂ) ^ 2 + 4 * ((v.2 : ℝ) : ℂ) * I - 3) 0 :=
    ((hsc.pow 2).add ((hsc.const_mul (4 : ℂ)).mul_const I)).sub_const 3
  have h := (hnum.mul ((hden1.mul hden2).inv (mul_ne_zero hk1 hk))).const_sub 1
  convert h using 1
  funext v
  simp only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]

@[tmio T, powerlib_foundation] theorem vsgBeta_eps (t : ℝ) : vsgBeta t 0 = t / (1 + t ^ 2) := by
  simp only [vsgBeta, vsgX]
  ring_nf

@[tmio T, powerlib_foundation] theorem vsgBeta_zero (t : ℝ) : vsgBeta 0 t = 0 := by
  simp [vsgBeta]

/-- `∂S/∂ε = −2j/3` at `ε = s = 0`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_kin_eps :
    HasDerivAt (fun t : ℝ => kinFactor (vsgBeta t 0) 0) (-(2 / 3 : ℂ) * I) 0 := by
  have hβ : HasDerivAt (fun t : ℝ => vsgBeta t 0) 1 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).div (((hasDerivAt_id (0 : ℝ)).pow 2).const_add 1)
      (by norm_num)
    convert h using 1
    · funext t; rw [vsgBeta_eps]; rfl
    · simp
  have hc : HasDerivAt (fun t : ℝ => ((vsgBeta t 0 : ℝ) : ℂ)) 1 0 := by
    simpa using hβ.ofReal_comp
  set K : ℂ := ((0 : ℝ) : ℂ) ^ 2 + 4 * ((0 : ℝ) : ℂ) * I - 3 with hK
  have hK3 : K = -3 := by simp [hK]
  have hden := (((hc.const_mul (2 : ℂ)).mul_const I).const_add 1).mul_const K
  have h0 : vsgBeta 0 0 = 0 := vsgBeta_zero 0
  have hne : (1 + 2 * ((vsgBeta 0 0 : ℝ) : ℂ) * I) * K ≠ 0 := by
    rw [h0, hK3]; norm_num
  have h := ((hasDerivAt_const (0 : ℝ) (1 + ((0 : ℝ) : ℂ) ^ 2)).div hden hne).const_sub 1
  convert h using 1
  · funext t; simp only [kinFactor, hK, Pi.div_apply]
  · rw [h0, hK3]
    push_cast
    ring_nf

/-- `∂S/∂s = 4j/9` at `ε = s = 0`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_kin_sigma :
    HasDerivAt (fun t : ℝ => kinFactor (vsgBeta 0 t) t) ((4 / 9 : ℂ) * I) 0 := by
  have hT : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hN := (hT.pow 2).const_add (1 : ℂ)
  have hD := (((hT.pow 2).add ((hT.const_mul (4 : ℂ)).mul_const I)).sub_const (3 : ℂ)).const_mul
    (1 + 2 * ((0 : ℝ) : ℂ) * I)
  have hne : (1 + 2 * ((0 : ℝ) : ℂ) * I) * (((0 : ℝ) : ℂ) ^ 2 + 4 * ((0 : ℝ) : ℂ) * I - 3) ≠ 0 := by
    norm_num
  have h := (hN.div hD hne).const_sub 1
  convert h using 1
  · funext t; simp only [kinFactor, vsgBeta_zero, Pi.div_apply, Pi.add_apply, Pi.pow_apply]
  · simp only [Pi.add_apply, Pi.pow_apply]
    push_cast
    ring_nf

/-- Table 6, VSG row, to first order: with `ε = Ω/ω_c` and `s = σ/Ω`,
`S(2jΩ) = 4/3 − (2j/3) ε + (4j/9) s + o(|ε| + |s|)` — the Fréchet derivative of
`(ε, s) ↦ kinFactor(β(ε, s), s)` (`vsg_root`) at `0`. -/
@[tmio T, powerlib_foundation] theorem vsg_row_firstOrder :
    HasFDerivAt (fun v : ℝ × ℝ => kinFactor (vsgBeta v.1 v.2) v.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (-(2 / 3 : ℂ) * I) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight ((4 / 9 : ℂ) * I)) 0 :=
  hasFDerivAt_of_partials differentiableAt_kin hasDerivAt_kin_eps hasDerivAt_kin_sigma

/-! ### The damping slope at the Hopf point -/

/-- `Q(s) = s + d₀/(s(s + ω_c))`: the VSG cubic `s(s + a)(s + ω_c) + d₀` is `s(s + ω_c)(Q(s) + a)`,
affine in `a = D/2H`. -/
def vsgQ (w d0 : ℝ) (s : ℂ) : ℂ := s + d0 / (s * (s + w))

@[tmio T, powerlib_foundation] theorem hopf_point_ne (w Ω : ℝ) (hΩ : Ω ≠ 0) :
    (Ω : ℂ) * I * ((Ω : ℂ) * I + w) ≠ 0 := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  refine mul_ne_zero (mul_ne_zero hΩc I_ne_zero) ?_
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hΩ this

/-- The damping slope of the VSG mode at its Hopf point (`Ω² = a₀ ω_c`,
`d₀ = (a₀ + ω_c) a₀ ω_c`): the mode continues to a differentiable branch `λ(a)`, `a = D/2H`, with
`λ'(a₀) = −(jΩ + ω_c)/(2(jΩ + a₀ + ω_c))`. -/
@[tmio T, powerlib_foundation] theorem vsg_slope {a0 w Ω : ℝ} (hw : 0 < w) (hΩ : 0 < Ω)
    (hH : Ω ^ 2 = a0 * w) :
    ∃ lam : ℝ → ℂ, lam a0 = Ω * I ∧
      (∀ᶠ a in 𝓝 a0, lam a * (lam a + a) * (lam a + w) + (((a0 + w) * a0 * w : ℝ) : ℂ) = 0) ∧
      HasDerivAt lam (-((Ω : ℂ) * I + w) / (2 * ((Ω : ℂ) * I + a0 + w))) a0 := by
  set d0 : ℝ := (a0 + w) * a0 * w with hd0
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hHc : (Ω : ℂ) ^ 2 = a0 * w := by exact_mod_cast hH
  have hne := hopf_point_ne w Ω hΩ.ne'
  have hwc : (w : ℂ) + Ω * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hden2 : (Ω : ℂ) * I + a0 + w ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  -- strict derivative of `Q`
  set Q' : ℂ := 1 - (d0 : ℂ) * (2 * (Ω * I) + w) / ((Ω : ℂ) * I * ((Ω : ℂ) * I + w)) ^ 2 with hQ'
  have hQ : HasStrictDerivAt (vsgQ w d0) Q' ((Ω : ℂ) * I) := by
    have hd : HasStrictDerivAt (fun s : ℂ => s * (s + w)) (1 * ((Ω : ℂ) * I + w) + (Ω : ℂ) * I * 1)
        ((Ω : ℂ) * I) := (hasStrictDerivAt_id _).mul ((hasStrictDerivAt_id _).add_const _)
    have h := (hasStrictDerivAt_id ((Ω : ℂ) * I)).add
      ((hasStrictDerivAt_const ((Ω : ℂ) * I) (d0 : ℂ)).div hd hne)
    convert h using 1
    · funext s; simp [vsgQ, Pi.div_apply]
    · rw [hQ']; ring
  have hQ'eq : Q' = 2 * ((Ω : ℂ) * I + a0 + w) / ((Ω : ℂ) * I + w) := by
    have hw' : (Ω : ℂ) * I + w ≠ 0 := by rw [add_comm]; exact hwc
    have hI : (Ω : ℂ) * I ≠ 0 := mul_ne_zero hΩc I_ne_zero
    simp only [hQ', hd0]
    push_cast
    field_simp
    linear_combination (-(Ω : ℂ)^2*(I^2*(Ω : ℂ)^2 + 2*I*(Ω : ℂ)*(a0 : ℂ) + 2*I*(Ω : ℂ)*(w : ℂ) - (Ω : ℂ)^2 + 2*(a0 : ℂ)*(w : ℂ) + (w : ℂ)^2)) * I_sq + (2*I*(Ω : ℂ)*(a0 : ℂ) + 2*I*(Ω : ℂ)*(w : ℂ) - (Ω : ℂ)^2 + (a0 : ℂ)*(w : ℂ) + (w : ℂ)^2) * hHc
  have hw' : (Ω : ℂ) * I + w ≠ 0 := by rw [add_comm]; exact hwc
  have hQ'ne : Q' ≠ 0 := by
    rw [hQ'eq]; exact div_ne_zero (mul_ne_zero two_ne_zero hden2) hw'
  have hQ'val : -1 / Q' = -((Ω : ℂ) * I + w) / (2 * ((Ω : ℂ) * I + a0 + w)) := by
    rw [hQ'eq]
    field_simp
  have hroot0 : vsgQ w d0 ((Ω : ℂ) * I) + 1 * (a0 : ℂ) = 0 := by
    simp only [vsgQ, hd0]
    push_cast
    field_simp
    linear_combination ((Ω : ℂ)^2*(I*(Ω : ℂ) + (a0 : ℂ) + (w : ℂ))) * I_sq + (-I*(Ω : ℂ) - (a0 : ℂ) - (w : ℂ)) * hHc
  obtain ⟨lam, h0, hev, hd⟩ := Modal.exists_root_branch hQ hQ'ne hroot0
  refine ⟨lam, h0, ?_, by rw [← hQ'val]; exact hd⟩
  have hcont : ContinuousAt (fun a => lam a * (lam a + w)) a0 :=
    hd.continuousAt.mul (hd.continuousAt.add continuousAt_const)
  have hne0 : lam a0 * (lam a0 + w) ≠ 0 := by rw [h0]; exact hne
  filter_upwards [hev, hcont.eventually_ne hne0] with a ha hna
  have h1 : lam a ≠ 0 := left_ne_zero_of_mul hna
  have h2 : lam a + w ≠ 0 := right_ne_zero_of_mul hna
  simp only [vsgQ] at ha
  field_simp at ha
  linear_combination ha

/-- The decay-rate slope `dσ/da = −Re λ'(a₀) = (ω_c(a₀ + ω_c) + Ω²)/(2((a₀ + ω_c)² + Ω²))`, and
`0 ≤ 1/2 − dσ/da ≤ a₀/(2(a₀ + ω_c))`: with `a = D/2H`, `dσ/dD = (1 − θ)/(4H)`,
`0 ≤ θ ≤ a₀/(a₀ + ω_c)`. -/
@[tmio T, powerlib_foundation] theorem vsg_decay_slope {a0 w Ω : ℝ} (ha : 0 ≤ a0) (hw : 0 < w)
    (hΩ : 0 < Ω) :
    -(-((Ω : ℂ) * I + w) / (2 * ((Ω : ℂ) * I + a0 + w))).re =
        (w * (a0 + w) + Ω ^ 2) / (2 * ((a0 + w) ^ 2 + Ω ^ 2)) ∧
      0 ≤ 1 / 2 - (w * (a0 + w) + Ω ^ 2) / (2 * ((a0 + w) ^ 2 + Ω ^ 2)) ∧
      1 / 2 - (w * (a0 + w) + Ω ^ 2) / (2 * ((a0 + w) ^ 2 + Ω ^ 2)) ≤ a0 / (2 * (a0 + w)) := by
  have hN : 0 < (a0 + w) ^ 2 + Ω ^ 2 := by positivity
  have hden2 : (Ω : ℂ) * I + a0 + w ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have key : -((Ω : ℂ) * I + w) / (2 * ((Ω : ℂ) * I + a0 + w)) =
      ((-(w * (a0 + w) + Ω ^ 2) / (2 * ((a0 + w) ^ 2 + Ω ^ 2)) : ℝ) : ℂ) +
        ((-(Ω * a0) / (2 * ((a0 + w) ^ 2 + Ω ^ 2)) : ℝ) : ℂ) * I := by
    have hNc : ((a0 : ℂ) + w) ^ 2 + (Ω : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hN.ne'
    rw [div_eq_iff (mul_ne_zero two_ne_zero hden2)]
    push_cast
    field_simp
    linear_combination ((Ω : ℂ)^2*(a0 : ℂ)) * I_sq
  refine ⟨?_, ?_, ?_⟩
  · rw [key]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
    ring
  · rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [sub_le_iff_le_add, div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg Ω, mul_nonneg ha hw.le, sq_nonneg a0]

/-- The threshold chain of Table 12 (VSG): with `σ = (D − D_ss)/(4H)`, `Ω² = ω₀K_s/(2H)`,
`ĝ = (4/3) tan δ₀` and `tan δ₀ = P/K_s`, `ε_crit = 4(σ/Ω)/ĝ` is exactly
`(3/(2P)) √(K_s/(2Hω₀)) (D − D_ss)`. -/
@[tmio T, powerlib_foundation] theorem vsg_threshold_chain {H ω0 Ks P D Dss : ℝ} (hH : 0 < H)
    (hω0 : 0 < ω0) (hKs : 0 < Ks) (hP : P ≠ 0) :
    4 * ((D - Dss) / (4 * H) / Real.sqrt (ω0 * Ks / (2 * H))) / (4 / 3 * (P / Ks)) =
      3 / (2 * P) * Real.sqrt (Ks / (2 * H * ω0)) * (D - Dss) := by
  have hA : 0 < ω0 * Ks / (2 * H) := by positivity
  have hsA : 0 < Real.sqrt (ω0 * Ks / (2 * H)) := Real.sqrt_pos.mpr hA
  have hAB : Real.sqrt (ω0 * Ks / (2 * H)) * Real.sqrt (Ks / (2 * H * ω0)) = Ks / (2 * H) := by
    rw [← Real.sqrt_mul hA.le, show ω0 * Ks / (2 * H) * (Ks / (2 * H * ω0)) = (Ks / (2 * H)) ^ 2 by
      field_simp]
    exact Real.sqrt_sq (by positivity)
  have hB : Real.sqrt (Ks / (2 * H * ω0)) = Ks / (2 * H) / Real.sqrt (ω0 * Ks / (2 * H)) := by
    rw [eq_div_iff hsA.ne', mul_comm, hAB]
  rw [hB]
  field_simp
  ring

/-- Droop (Table 3): at the Hopf point `β_L = Ω/d₂ = √(ω₁ω_m)/(ω₁ + ω_m) = √χ/(1 + χ)`,
`χ = ω₁/ω_m`, and `β_L ≤ 1/2`. -/
@[tmio T, powerlib_foundation] theorem droop_beta_le {ω1 ωm : ℝ} (h1 : 0 < ω1) (hm : 0 < ωm) :
    Real.sqrt (ω1 * ωm) / (ω1 + ωm) = Real.sqrt (ω1 / ωm) / (1 + ω1 / ωm) ∧
      Real.sqrt (ω1 * ωm) / (ω1 + ωm) ≤ 1 / 2 := by
  constructor
  · have hsm : 0 < Real.sqrt ωm := Real.sqrt_pos.mpr hm
    rw [Real.sqrt_mul h1.le, Real.sqrt_div h1.le]
    have ht : ωm = Real.sqrt ωm ^ 2 := (Real.sq_sqrt hm.le).symm
    set t := Real.sqrt ωm
    rw [ht]
    field_simp
    ring
  · rw [div_le_iff₀ (by positivity)]
    have h := Real.sqrt_le_sqrt (show ω1 * ωm ≤ ((ω1 + ωm) / 2) ^ 2 by nlinarith [sq_nonneg (ω1 - ωm)])
    rw [Real.sqrt_sq (by positivity)] at h
    linarith

end VSGRow
end powerlib.GFM
