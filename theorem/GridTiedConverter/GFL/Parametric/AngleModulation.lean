import theorem.ParametricResonance.HurwitzForcedOrbit
import theorem.ParametricResonance.ElementDecomposition
import theorem.GridTiedConverter.GFL.DCLink.FourState

/-! # GFL converter under small grid-angle variations: forced response, `A₁`, modal contributions

The grid-following converter of the slides "Hidden Instability of Grid-Following Converters Under
Small Grid Angle Variations" (KTH, 2026-11-27): PLL and dc-voltage loop, ideal inner current loop,
`i_q = 0`, source voltage `V₀∠θ_g` behind `X_g`. The source angle is prescribed,
`θ_g = θ_{g0} + ε cos ω_p t`. Every equation, matrix and coefficient of the slides is stated and
proved here for the exact nonlinear model.

Model boundary.
* States `(δ, ξ_PLL, v_dc, ξ_DVC)`, `δ = θ_PLL − θ_g`, `v_dc` normalized (nominal `1`):
  * `i_d = i_{d0} + k_pv(v_dc − 1) + k_iv ξ_DVC`, `v_d = V₀ cos δ`, `v_q = −V₀ sin δ + X_g i_d`;
  * `δ̇ = k_{p,PLL} v_q + k_{i,PLL} ξ_PLL − θ̇_g`, `ξ̇_PLL = v_q`;
  * `v̇_dc = (3/2C)(v_{d0} i_{d0} − v_d i_d/v_dc)`, `ξ̇_DVC = v_dc − 1` (`field`).
* In the absolute PLL angle `φ = δ + (θ_g − θ_{g0})` the grid angle is a parameter (`afield`),
  and the forced-orbit and Floquet machinery of `SmoothForcedOrbit` applies. `shift_solution`
  carries solutions back to the source's coordinates; `matX_afield` identifies the Jacobians.
* The model is the library's four-state model `DCLink.FourState` with the IN-positive current
  `−i_{d0}` (`toFourState`, `field_eq_fourState`, `isEq_fourState`).
* The orbit statements assume `A₀` Hurwitz (`LinearSystems.IsHurwitz`); the drive frequency is
  arbitrary.

Source: slides "Hidden Instability of Grid-Following Converters Under Small Grid Angle
Variations" (KTH, 2026-11-27), pp. 2–25, 28–30.

Results.
* `field`, `afield`, `xs`, `field_eq_afield`, `shift_solution`, `toFourState`,
  `field_eq_fourState`, `isEq_fourState` — the model (pp. 2–3).
* `field_xs`, `eq_char`, `arcsin_branch` — the operating point (p. 4).
* `A31`, `A0`, `jac`, `jac_xs`, `contDiffAt_afield`, `matX_afield`, `matX_afield_xs`,
  `R2`, `R3`, `R`, `field_decomp`, `R_isBigO`, `dR`, `jac_eq_A0_add`, `hasDerivAt_R`:
  * the deviation equations, `A₀` and the exact remainder `R = O(‖η‖²)` (pp. 5–9);
  * `J_p = A₀ + ∂R/∂η` with `∂R/∂η` in closed form (pp. 11–14).
* `Ldc`, `Gam`, `Dg`, `da3`, …, `da0`, `Dg_eq`, `det_sub_A0`, `zc`, `e0c`, `zc_eq`, `zc_eq_inv`,
  `zc_three`, `zc_two` — the forced response `z⁽¹⁾ = −jω_p(jω_pI − A₀)⁻¹e₁` in closed form
  (pp. 10, 29).
* `fderivW_afield`, `hz_afield`, `Dg_ne_of_hurwitz`, `harm_add_e0`, `orbit_angle` — the periodic
  response `η_p = ε Re{z⁽¹⁾e^{jω_pt}} + O(ε²)`: existence, uniqueness in a ball of radius `cε`,
  and the expansion (pp. 10, 28).
* `kdc`, `dJ`, `ih`, `vh`, `b1`, `b3`, `b4`, `gA1`, `smDx_afield`, `smM1_afield`, `smA1_afield`,
  `jac_angle_expansion` — `A₁(ω_p)` with `b₁, b₃, b₄`, and
  `J_p = A₀ + ε Re{A₁e^{jω_pt}} + O(ε²)` along the forced trajectory (pp. 15–19).
* `ratio11`, `ratio21`, `ratio31`, `ratio33`, `ratio34` — the relative modulations (p. 22).
* `pump_eq_sum`, `contribution31` — `g_m = Γ₁₁ + Γ₂₁ + Γ₃₁ + Γ₃₃ + Γ₃₄` and `Γ₃₁` (pp. 21, 25).
* `det_neg_A0_eq`, `det_neg_A0`, `cos_two_pos_of_hurwitz`, `angle_lt_pi_div_four`,
  `tan_cot_bounds`, `cot_tan_asymp` — `det(−A₀) = (3k_{i,PLL}k_iv V₀²/2C) cos 2δ₀`, nominal
  stability forces `|δ₀| < π/4`, `0 < |tan δ₀| < 1 < |cot δ₀|`, `|cot δ₀|² ∼ δ₀⁻²` (p. 23).
* `delta_ratio` — `|Γ^{(δ)}₃₁|/|Γ^{(δ)}_{ik}| = |cot δ₀|²|w₃₁|/|w_ik|` (p. 24).
* `continuous_Ldc`, `continuous_Dg`, `zc_small`, `zc_small_isBigO`, `zc_large`, `zc_large_isBigO`
  — the response component table as `ω_p → 0` and `ω_p → ∞` (p. 29).
* The generic statements used for pp. 20–21 and 26–27 are `Element.sum_weight`,
  `Element.contribution_eq`, `ForcedOrbit.slow_det`, `ForcedOrbit.slow_re_max`,
  `ForcedOrbit.slow_growth_iff` and `ForcedOrbit.slow_crit_tuned`. The Floquet statements at a
  2:1 resonance are in `GFL.Parametric.AngleModulationHopf`.

Corrections.
None: every formula of the slides checks.

Family and connection conclusions.
None: static evidence on the GFL model; its link to the four-state model `DCLink.FourState` is
`field_eq_fourState`.
-/

noncomputable section
namespace powerlib.GFL.Parametric.AngleModulation
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 harm)
open scoped Matrix.Norms.Operator

/-- Parameters of the grid-following converter with PLL and dc-voltage loop. -/
structure Params where
  /-- PLL proportional gain `k_{p,PLL}` -/
  kp : ℝ
  /-- PLL integral gain `k_{i,PLL}` -/
  ki : ℝ
  /-- dc-voltage loop proportional gain `k_pv` -/
  kpv : ℝ
  /-- dc-voltage loop integral gain `k_iv` -/
  kiv : ℝ
  /-- normalized dc-capacitance coefficient `C` -/
  C : ℝ
  /-- source-voltage magnitude `V₀` -/
  V0 : ℝ
  /-- grid reactance `X_g` -/
  Xg : ℝ
  /-- d-axis current reference `i_{d0}` -/
  id0 : ℝ
  /-- operating angle `δ₀` -/
  δ0 : ℝ

namespace Params
variable (p : Params)

/-- `v_{d0} = V₀ cos δ₀`. -/
def vd0 : ℝ := p.V0 * Real.cos p.δ0

/-- The d-axis current of the dc controller, `i_d = i_{d0} + k_pv(v_dc − 1) + k_iv ξ_DVC`. -/
def idv (x : Fin 4 → ℝ) : ℝ := p.id0 + p.kpv * (x 2 - 1) + p.kiv * x 3

/-- The GFL field in the states `(δ, ξ_PLL, v_dc, ξ_DVC)`, `δ = θ_PLL − θ_g`, with the grid-angle
rate `θ̇_g = d` as input. -/
def field (x : Fin 4 → ℝ) (d : ℝ) : Fin 4 → ℝ :=
  ![p.kp * (-p.V0 * Real.sin (x 0) + p.Xg * p.idv x) + p.ki * x 1 - d,
    -p.V0 * Real.sin (x 0) + p.Xg * p.idv x,
    3 / (2 * p.C) * (p.vd0 * p.id0 - p.V0 * Real.cos (x 0) * p.idv x / x 2),
    x 2 - 1]

/-- The same field in the absolute PLL angle `φ = θ_PLL − θ_{g0} = δ + w`, `w = θ_g − θ_{g0}`: the
grid angle enters as a parameter. -/
def afield (q : (Fin 4 → ℝ) × ℝ) : Fin 4 → ℝ :=
  ![p.kp * (-p.V0 * Real.sin (q.1 0 - q.2) + p.Xg * p.idv q.1) + p.ki * q.1 1,
    -p.V0 * Real.sin (q.1 0 - q.2) + p.Xg * p.idv q.1,
    3 / (2 * p.C) * (p.vd0 * p.id0 - p.V0 * Real.cos (q.1 0 - q.2) * p.idv q.1 / q.1 2),
    q.1 2 - 1]

/-- The operating point `(δ₀, 0, 1, 0)`. -/
def xs : Fin 4 → ℝ := ![p.δ0, 0, 1, 0]

end Params

/-- The angle direction `e₁ = (1, 0, 0, 0)`. -/
def e0 : Fin 4 → ℝ := ![1, 0, 0, 0]

namespace Params
variable (p : Params)

@[tmio M, powerlib_domain] theorem field_eq_afield (x : Fin 4 → ℝ) (w d : ℝ) :
    p.field x d = p.afield (x + w • e0, w) - d • e0 := by
  funext i
  fin_cases i <;> simp [field, afield, idv, e0]

/-- A solution of the absolute-angle system with the grid angle `w(t)` is, after subtracting
`w(t) e₁`, a solution of the source's system with `θ̇_g = ẇ`. -/
@[tmio M, powerlib_domain] theorem shift_solution {y : ℝ → Fin 4 → ℝ} {w w' : ℝ → ℝ}
    (hw : ∀ t, HasDerivAt w (w' t) t) (hy : ∀ t, HasDerivAt y (p.afield (p.xs + y t, w t)) t)
    (t : ℝ) :
    HasDerivAt (fun t => y t - w t • e0) (p.field (p.xs + (y t - w t • e0)) (w' t)) t := by
  have h := (hy t).sub ((hw t).smul_const e0)
  rw [p.field_eq_afield _ (w t)]
  convert h using 2
  abel_nf

/-- The model is the library's four-state GFL model (`DCLink.FourState`) with the IN-positive
current `−i_{d0}`, the same integrator `ξ_DVC = η`, and the dc source current
`I_dc0 = (3/2) v_{d0} i_{d0}`. -/
def toFourState : DCLink.FourState.Params where
  V0 := p.V0
  line := ⟨0, p.Xg, 0⟩
  id0 := -p.id0
  kp := p.kp
  ki := p.ki
  kpv := p.kpv
  kiv := p.kiv
  dcLink := ⟨0, p.C, 0⟩
  Idc0 := 3 / 2 * p.vd0 * p.id0
  dcLink_lossless := rfl
  line_lossless := rfl
  dcLink_noInd := rfl

@[tmio M, powerlib_domain] theorem field_eq_fourState (x : Fin 4 → ℝ) :
    p.field x 0 = DCLink.FourState.coordField p.toFourState x := by
  funext i
  fin_cases i <;>
    simp [field, DCLink.FourState.coordField, DCLink.FourState.vq, DCLink.FourState.idc, idv,
      toFourState, DCLink.FourState.Params.γ, Passive.SeriesRLC.reactance,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

@[tmio M, powerlib_domain] theorem isEq_fourState :
    DCLink.FourState.IsEq p.toFourState p.δ0 ↔ p.V0 * Real.sin p.δ0 = p.Xg * p.id0 := by
  simp [DCLink.FourState.IsEq, toFourState, Passive.SeriesRLC.reactance, vd0]

/-! ### The operating point -/

/-- The operating point is an equilibrium of the unforced model when `V₀ sin δ₀ = X_g i_{d0}`. -/
@[tmio M, powerlib_domain] theorem field_xs (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    p.field p.xs 0 = 0 := by
  funext i
  fin_cases i <;> simp [field, xs, idv, vd0, hs]

/-- Conversely, an equilibrium with `i_d = i_{d0}` (and `k_i, k_iv ≠ 0`) is `(δ, 0, 1, 0)` with
`V₀ sin δ = X_g i_{d0}`. -/
@[tmio M, powerlib_domain] theorem eq_char (hki : p.ki ≠ 0) (hkiv : p.kiv ≠ 0) {x : Fin 4 → ℝ}
    (hx : p.field x 0 = 0) (hid : p.idv x = p.id0) :
    x 1 = 0 ∧ x 2 = 1 ∧ x 3 = 0 ∧ p.V0 * Real.sin (x 0) = p.Xg * p.id0 := by
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h3 := congrFun hx 3
  simp [field] at h0 h1 h3
  have hx2 : x 2 = 1 := by linarith
  have hx3 : x 3 = 0 := by
    simp only [idv, hx2, sub_self, mul_zero, add_zero] at hid
    exact (mul_eq_zero.1 (by linarith : p.kiv * x 3 = 0)).resolve_left hkiv
  have hq : -p.V0 * Real.sin (x 0) + p.Xg * p.idv x = 0 := by linarith
  rw [hid] at hq h0
  refine ⟨?_, hx2, hx3, by linarith⟩
  have e : -(p.V0 * Real.sin (x 0)) + p.Xg * p.id0 = 0 := by linarith
  rw [e, mul_zero, zero_add] at h0
  exact (mul_eq_zero.1 h0).resolve_left hki

/-- The principal branch `δ₀ = arcsin(X_g i_{d0}/V₀)` satisfies the equilibrium relation, with
`v_{d0} ≥ 0`. -/
@[tmio M, powerlib_domain] theorem arcsin_branch (hV : 0 < p.V0) (hX : |p.Xg * p.id0| ≤ p.V0)
    (hδ : p.δ0 = Real.arcsin (p.Xg * p.id0 / p.V0)) :
    p.V0 * Real.sin p.δ0 = p.Xg * p.id0 ∧ 0 ≤ p.vd0 := by
  have h1 : -1 ≤ p.Xg * p.id0 / p.V0 := by
    rw [le_div_iff₀ hV]; linarith [neg_abs_le (p.Xg * p.id0)]
  have h2 : p.Xg * p.id0 / p.V0 ≤ 1 := by
    rw [div_le_iff₀ hV]; linarith [le_abs_self (p.Xg * p.id0)]
  refine ⟨?_, ?_⟩
  · rw [hδ, Real.sin_arcsin h1 h2]; field_simp
  · rw [vd0, hδ]; exact mul_nonneg hV.le (Real.cos_arcsin_nonneg _)


/-! ### The Jacobian -/

/-- The nominal `(3, 1)` entry `3 X_g i_{d0}²/(2C)`. -/
def A31 : ℝ := 3 * p.Xg * p.id0 ^ 2 / (2 * p.C)

/-- The nominal GFL matrix `A₀`, columns in the order `(η₁, η₂, η₃, η₄)`. -/
def A0 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-p.kp * p.vd0, p.ki, p.kp * p.Xg * p.kpv, p.kp * p.Xg * p.kiv;
    -p.vd0, 0, p.Xg * p.kpv, p.Xg * p.kiv;
    p.A31, 0, -(3 * p.vd0 * (p.kpv - p.id0)) / (2 * p.C), -(3 * p.vd0 * p.kiv) / (2 * p.C);
    0, 0, 1, 0]

/-- The GFL Jacobian at the state `x` (`v_dc = x₃ ≠ 0`): the matrix `J_p` of the source along
any trajectory. -/
def jac (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-p.kp * (p.V0 * Real.cos (x 0)), p.ki, p.kp * p.Xg * p.kpv, p.kp * p.Xg * p.kiv;
    -(p.V0 * Real.cos (x 0)), 0, p.Xg * p.kpv, p.Xg * p.kiv;
    3 * p.V0 * Real.sin (x 0) * p.idv x / (2 * p.C) / x 2, 0,
      -(3 * (p.V0 * Real.cos (x 0)) / (2 * p.C) * (p.kpv / x 2 - p.idv x / x 2 ^ 2)),
      -(3 * (p.V0 * Real.cos (x 0)) * p.kiv / (2 * p.C) / x 2);
    0, 0, 1, 0]

@[tmio M, powerlib_domain] theorem jac_xs (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    p.jac p.xs = p.A0 := by
  have hA : p.A31 = 3 * p.V0 * Real.sin p.δ0 * p.id0 / (2 * p.C) := by
    rw [A31]; linear_combination (-(3 * p.id0 / (2 * p.C))) * hs
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jac, A0, xs, idv, vd0, hA] <;> ring

@[tmio M, powerlib_domain] theorem contDiffAt_afield {n : WithTop ℕ∞} {q : (Fin 4 → ℝ) × ℝ}
    (hq : q.1 2 ≠ 0) : ContDiffAt ℝ n p.afield q := by
  have hx : ∀ i : Fin 4, ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => q.1 i := fun i =>
    (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have ha : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => q.1 0 - q.2 := (hx 0).sub contDiff_snd
  have hid : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => p.idv q.1 := by
    unfold idv
    exact (contDiff_const.add (contDiff_const.mul ((hx 2).sub contDiff_const))).add
      (contDiff_const.mul (hx 3))
  have hvq : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ =>
      -p.V0 * Real.sin (q.1 0 - q.2) + p.Xg * p.idv q.1 :=
    (contDiff_const.mul (Real.contDiff_sin.comp ha)).add (contDiff_const.mul hid)
  refine contDiffAt_pi.2 fun i => ?_
  fin_cases i
  · exact ((contDiff_const.mul hvq).add (contDiff_const.mul (hx 1))).contDiffAt
  · exact hvq.contDiffAt
  · exact contDiffAt_const.mul (contDiffAt_const.sub
      (((contDiff_const.mul (Real.contDiff_cos.comp ha)).mul hid).contDiffAt.div
        (hx 2).contDiffAt hq))
  · exact ((hx 2).sub contDiff_const).contDiffAt

/-- The Jacobian of the absolute-angle field is the GFL Jacobian at the shifted state
`(φ − w, ξ_PLL, v_dc, ξ_DVC)`. -/
@[tmio M, powerlib_domain] theorem matX_afield {q : (Fin 4 → ℝ) × ℝ} (hq : q.1 2 ≠ 0) :
    matX p.afield q = p.jac (q.1 - q.2 • e0) := by
  refine ParametricResonance.ForcedOrbit.matX_of_line
    ((p.contDiffAt_afield (n := 1) hq).differentiableAt (by norm_num)) fun y => ?_
  have hl : ∀ i, HasDerivAt (fun s : ℝ => (q.1 + s • y) i) (y i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y i)).const_add (q.1 i)
  have ha : HasDerivAt (fun s : ℝ => (q.1 + s • y) 0 - q.2) (y 0) 0 := (hl 0).sub_const _
  have hc : HasDerivAt (fun s : ℝ => Real.cos ((q.1 + s • y) 0 - q.2))
      (-Real.sin (q.1 0 - q.2) * y 0) 0 := by simpa using ha.cos
  have hs : HasDerivAt (fun s : ℝ => Real.sin ((q.1 + s • y) 0 - q.2))
      (Real.cos (q.1 0 - q.2) * y 0) 0 := by simpa using ha.sin
  have hid : HasDerivAt (fun s : ℝ => p.idv (q.1 + s • y)) (p.kpv * y 2 + p.kiv * y 3) 0 := by
    have := ((((hl 2).sub_const 1).const_mul p.kpv).const_add p.id0).add ((hl 3).const_mul p.kiv)
    exact this
  have e2 : (q.1 - q.2 • e0) 2 = q.1 2 := by simp [e0]
  have e3 : p.idv (q.1 - q.2 • e0) = p.idv q.1 := by simp [idv, e0]
  have e0' : (q.1 - q.2 • e0) 0 = q.1 0 - q.2 := by simp [e0]
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · refine (((((hs.const_mul (-p.V0)).add (hid.const_mul p.Xg)).const_mul p.kp).add
      ((hl 1).const_mul p.ki))).congr_deriv ?_
    show _ = (p.jac (q.1 - q.2 • e0) *ᵥ y) 0
    simp only [jac, e0', e2, e3]
    simp [mulVec, dotProduct, Fin.sum_univ_four]; ring
  · refine ((hs.const_mul (-p.V0)).add (hid.const_mul p.Xg)).congr_deriv ?_
    show _ = (p.jac (q.1 - q.2 • e0) *ᵥ y) 1
    simp only [jac, e0', e2, e3]
    simp [mulVec, dotProduct, Fin.sum_univ_four]; ring
  · have hd := ((hc.const_mul p.V0).mul hid).div (hl 2) (by simpa using hq)
    refine ((hd.const_sub (p.vd0 * p.id0)).const_mul (3 / (2 * p.C))).congr_deriv ?_
    show _ = (p.jac (q.1 - q.2 • e0) *ᵥ y) 2
    simp only [jac, e0', e2, e3]
    simp [mulVec, dotProduct, Fin.sum_univ_four]
    field_simp
    ring
  · refine ((hl 2).sub_const 1).congr_deriv ?_
    show _ = (p.jac (q.1 - q.2 • e0) *ᵥ y) 3
    simp [jac, mulVec, dotProduct, Fin.sum_univ_four]

/-- At the operating point the Jacobian of the absolute-angle field is `A₀`. -/
@[tmio M, powerlib_domain] theorem matX_afield_xs (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    matX p.afield (p.xs, 0) = p.A0 := by
  rw [p.matX_afield (by simp [xs]), zero_smul, sub_zero, p.jac_xs hs]

/-! ### The exact nonlinear remainder -/

/-- The PLL remainder `R₂(η) = −V₀[sin(δ₀ + η₁) − sin δ₀ − cos δ₀ η₁]`. -/
def R2 (η : Fin 4 → ℝ) : ℝ :=
  -p.V0 * (Real.sin (p.δ0 + η 0) - Real.sin p.δ0 - Real.cos p.δ0 * η 0)

/-- The dc-voltage remainder `R₃(η)`. -/
def R3 (η : Fin 4 → ℝ) : ℝ :=
  3 / (2 * p.C) * (p.vd0 * p.id0 - p.V0 * Real.cos (p.δ0 + η 0) *
    (p.id0 + p.kpv * η 2 + p.kiv * η 3) / (1 + η 2) - p.Xg * p.id0 ^ 2 * η 0 +
    p.vd0 * (p.kpv - p.id0) * η 2 + p.vd0 * p.kiv * η 3)

/-- The remainder `R(η) = (k_{p,PLL} R₂, R₂, R₃, 0)`. -/
def R (η : Fin 4 → ℝ) : Fin 4 → ℝ := ![p.kp * p.R2 η, p.R2 η, p.R3 η, 0]

/-- The local GFL equations: `η̇ = A₀η − (1, 0, 0, 0)θ̇_g + R(η)`, exactly. -/
@[tmio M, powerlib_domain] theorem field_decomp (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (η : Fin 4 → ℝ) (d : ℝ) : p.field (p.xs + η) d = p.A0 *ᵥ η - d • e0 + p.R η := by
  funext i
  fin_cases i
  · simp [field, A0, R, R2, xs, idv, vd0, e0, dotProduct, Fin.sum_univ_four]
    linear_combination (-p.kp) * hs
  · simp [field, A0, R, R2, xs, idv, vd0, e0, dotProduct, Fin.sum_univ_four]
    linear_combination (-1 : ℝ) * hs
  · simp [field, A0, R, R3, xs, idv, vd0, A31, e0, dotProduct, Fin.sum_univ_four]
    ring
  · simp [field, A0, R, xs, e0, dotProduct, Fin.sum_univ_four]


/-- `R(η) = O(‖η‖²)`: the constant and linear terms cancel. -/
@[tmio M, powerlib_domain] theorem R_isBigO (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    p.R =O[𝓝 0] fun η => ‖η‖ ^ 2 := by
  set G : (Fin 4 → ℝ) → Fin 4 → ℝ := fun η => p.afield (p.xs + η, 0) - p.A0 *ᵥ η with hG
  have hRG : ∀ η, p.R η = G η := fun η => by
    have h := p.field_decomp hs η 0
    rw [p.field_eq_afield _ 0] at h
    simp only [zero_smul, add_zero, sub_zero] at h
    simp only [hG, h]
    abel
  have hq : (p.xs, (0 : ℝ)).1 2 ≠ 0 := by simp [xs]
  have hf : HasFDerivAt (fun η : Fin 4 → ℝ => (p.xs + η, (0 : ℝ)))
      (ContinuousLinearMap.inl ℝ (Fin 4 → ℝ) ℝ) 0 := by
    have := ((ContinuousLinearMap.inl ℝ (Fin 4 → ℝ) ℝ).hasFDerivAt (x := (0 : Fin 4 → ℝ))).const_add
      ((p.xs, (0 : ℝ)) : (Fin 4 → ℝ) × ℝ)
    convert this using 1
    funext η
    simp
  set L := LinearMap.toContinuousLinearMap (Matrix.mulVecLin p.A0) with hL
  have hLd : HasFDerivAt (fun η : Fin 4 → ℝ => p.A0 *ᵥ η) L 0 := L.hasFDerivAt
  have hLc : ContDiff ℝ 2 (fun η : Fin 4 → ℝ => p.A0 *ᵥ η) := L.contDiff
  have hA : HasFDerivAt p.afield (fderiv ℝ p.afield (p.xs, 0)) (p.xs + 0, (0 : ℝ)) := by
    rw [add_zero]
    exact ((p.contDiffAt_afield (n := 1) hq).differentiableAt (by norm_num)).hasFDerivAt
  have hd0 : HasFDerivAt G (0 : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) 0 := by
    have h := (hA.comp (0 : Fin 4 → ℝ) hf).sub hLd
    refine h.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    have hm := ParametricResonance.ForcedOrbit.matX_mulVec p.afield (p.xs, 0) v
    rw [p.matX_afield_xs hs] at hm
    simp [hL, ← hm]
  have hG2 : ContDiffAt ℝ 2 G 0 := by
    have h1 : ContDiffAt ℝ 2 (fun η : Fin 4 → ℝ => p.afield (p.xs + η, 0)) 0 := by
      have hc : ContDiffAt ℝ 2 p.afield ((fun η : Fin 4 → ℝ => (p.xs + η, (0 : ℝ))) 0) := by
        simpa using p.contDiffAt_afield (n := 2) hq
      exact hc.comp (0 : Fin 4 → ℝ) ((contDiffAt_const.add contDiffAt_id).prodMk contDiffAt_const)
    exact h1.sub hLc.contDiffAt
  obtain ⟨r, K, hr, hK, hd, hl⟩ := ParametricResonance.ForcedOrbit.exists_taylor_ball hG2
  have hG0 : G 0 = 0 := by
    have := p.field_xs hs
    rw [p.field_eq_afield _ 0] at this
    simpa [hG] using this
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : Fin 4 → ℝ) hr] with η hη
  have hη' : ‖η‖ ≤ r := by simpa using hη
  have ht := ParametricResonance.ForcedOrbit.taylor_sub hK hd hl hη'
    (q1 := η) (q2 := 0) (by simp) (by simp)
  rw [hRG, norm_pow, norm_norm]
  calc ‖G η‖ ≤ K * ‖η‖ * ‖η‖ := by simpa [hG0, hd0.fderiv] using ht
    _ = K * ‖η‖ ^ 2 := by ring

/-- `∂R/∂η` at `η`, in closed form: the PLL rows `k_{p,PLL}·(V₀[cos δ₀ − cos(δ₀ + η₁)], 0, 0, 0)`,
`(V₀[cos δ₀ − cos(δ₀ + η₁)], 0, 0, 0)` and the dc row. -/
def dR (η : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![p.kp * (p.V0 * (Real.cos p.δ0 - Real.cos (p.δ0 + η 0))), 0, 0, 0;
    p.V0 * (Real.cos p.δ0 - Real.cos (p.δ0 + η 0)), 0, 0, 0;
    3 / (2 * p.C) * (p.V0 * Real.sin (p.δ0 + η 0) * (p.id0 + p.kpv * η 2 + p.kiv * η 3) /
      (1 + η 2) - p.Xg * p.id0 ^ 2), 0,
      3 / (2 * p.C) * (-(p.V0 * Real.cos (p.δ0 + η 0)) * (p.kpv / (1 + η 2) -
        (p.id0 + p.kpv * η 2 + p.kiv * η 3) / (1 + η 2) ^ 2) + p.vd0 * (p.kpv - p.id0)),
      3 / (2 * p.C) * (-(p.V0 * Real.cos (p.δ0 + η 0)) * p.kiv / (1 + η 2) + p.vd0 * p.kiv);
    0, 0, 0, 0]

/-- The Jacobian along a trajectory is `A₀ + ∂R/∂η`. -/
@[tmio M, powerlib_domain] theorem jac_eq_A0_add (η : Fin 4 → ℝ) :
    p.jac (p.xs + η) = p.A0 + p.dR η := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jac, A0, dR, xs, idv, vd0, A31] <;> ring

/-- `dR` is the derivative of `R`, along every direction. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_R (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (η y : Fin 4 → ℝ) (hη : 1 + η 2 ≠ 0) :
    HasDerivAt (fun s : ℝ => p.R (η + s • y)) (p.dR η *ᵥ y) 0 := by
  have hq : (p.xs + η, (0 : ℝ)).1 2 ≠ 0 := by simpa [xs, add_comm] using hη
  have hA := ((p.contDiffAt_afield (n := 1) hq).differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => (p.xs + (η + s • y), (0 : ℝ))) (y, 0) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => p.xs + (η + s • y)) y 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add (p.xs + η)
    exact h1.prodMk (hasDerivAt_const _ _)
  have hlin : HasDerivAt (fun s : ℝ => p.A0 *ᵥ (η + s • y)) (p.A0 *ᵥ y) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (p.A0 *ᵥ y)).const_add (p.A0 *ᵥ η)
    convert this using 1
    · funext s; simp [Matrix.mulVec_add, Matrix.mulVec_smul]
    · simp
  have h := (hA.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)).sub hlin
  have hRf : (fun s : ℝ => p.R (η + s • y)) =
      fun s => p.afield (p.xs + (η + s • y), 0) - p.A0 *ᵥ (η + s • y) := by
    funext s
    have h := p.field_decomp hs (η + s • y) 0
    rw [p.field_eq_afield _ 0] at h
    simp only [zero_smul, add_zero, sub_zero] at h
    rw [h]; abel
  rw [hRf]
  have hm := ParametricResonance.ForcedOrbit.matX_mulVec p.afield (p.xs + η, 0) y
  rw [p.matX_afield hq, zero_smul, sub_zero, p.jac_eq_A0_add η, Matrix.add_mulVec] at hm
  refine h.congr_deriv ?_
  rw [← hm]
  abel

/-! ### The characteristic polynomial and the first-order forced response -/

/-- `L_dc(s) = s² + (3v_{d0}/2C)[(k_pv − i_{d0})s + k_iv]`. -/
def Ldc (s : ℂ) : ℂ := s ^ 2 + 3 * p.vd0 / (2 * p.C) * ((p.kpv - p.id0) * s + p.kiv)

/-- The PLL–dc coupling `Γ = X_g A₃₁ = 3X_g² i_{d0}²/(2C)`. -/
def Gam : ℝ := p.Xg * p.A31

/-- `D_GFL(s) = (s² + k_p v_{d0} s + k_i v_{d0}) L_dc(s) − Γ(k_p s + k_i)(k_pv s + k_iv)`. -/
def Dg (s : ℂ) : ℂ :=
  (s ^ 2 + p.kp * p.vd0 * s + p.ki * p.vd0) * p.Ldc s -
    p.Gam * (p.kp * s + p.ki) * (p.kpv * s + p.kiv)

/-- Its coefficients. -/
def da3 : ℝ := p.kp * p.vd0 + 3 * p.vd0 * (p.kpv - p.id0) / (2 * p.C)
/-- `s²` coefficient. -/
def da2 : ℝ := p.ki * p.vd0 + 3 * p.vd0 * p.kiv / (2 * p.C) +
  p.kp * p.vd0 * (3 * p.vd0 * (p.kpv - p.id0) / (2 * p.C)) - p.Gam * p.kp * p.kpv
/-- `s` coefficient. -/
def da1 : ℝ := p.ki * p.vd0 * (3 * p.vd0 * (p.kpv - p.id0) / (2 * p.C)) +
  p.kp * p.vd0 * (3 * p.vd0 * p.kiv / (2 * p.C)) - p.Gam * (p.ki * p.kpv + p.kp * p.kiv)
/-- Constant coefficient. -/
def da0 : ℝ := p.ki * p.vd0 * (3 * p.vd0 * p.kiv / (2 * p.C)) - p.Gam * p.ki * p.kiv

@[tmio M, powerlib_domain] theorem Dg_eq (s : ℂ) :
    p.Dg s = s ^ 4 + p.da3 * s ^ 3 + p.da2 * s ^ 2 + p.da1 * s + p.da0 := by
  simp only [Dg, Ldc, da3, da2, da1, da0]
  push_cast
  ring

@[tmio M, powerlib_domain] theorem det_sub_A0 (s : ℂ) :
    (s • (1 : Matrix (Fin 4) (Fin 4) ℂ) - p.A0.map (algebraMap ℝ ℂ)).det = p.Dg s := by
  have a1 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := rfl
  have a2 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := rfl
  have a3 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := rfl
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, A0, Matrix.submatrix, Matrix.one_apply, a1, a2,
    a3]
  simp only [Dg, Ldc, Gam, A31]
  push_cast
  ring

/-- The first-order response coefficient `z⁽¹⁾(s)` at `s = jω_p`, in closed form:
`z₁ = −s²L_dc/D`, `z₂ = s(v_{d0}L_dc − Γ(k_pv s + k_iv))/D`, `z₃ = −A₃₁s³/D`, `z₄ = −A₃₁s²/D`. -/
def zc (s : ℂ) : Fin 4 → ℂ :=
  ![-(s ^ 2 * p.Ldc s) / p.Dg s, s * (p.vd0 * p.Ldc s - p.Gam * (p.kpv * s + p.kiv)) / p.Dg s,
    -(p.A31 * s ^ 3) / p.Dg s, -(p.A31 * s ^ 2) / p.Dg s]

end Params

/-- `e₁` as a complex vector. -/
def e0c : Fin 4 → ℂ := ![1, 0, 0, 0]

namespace Params
variable (p : Params)

/-- `s z⁽¹⁾ = A₀ z⁽¹⁾ − s e₁`. -/
@[tmio M, powerlib_domain] theorem zc_eq {s : ℂ} (hD : p.Dg s ≠ 0) :
    s • p.zc s - p.A0.map (algebraMap ℝ ℂ) *ᵥ p.zc s = -s • e0c := by
  funext i
  fin_cases i <;> simp [zc, A0, e0c, mulVec, dotProduct, Fin.sum_univ_four] <;> field_simp <;>
    simp only [Dg, Ldc, Gam, A31] <;> push_cast <;> ring

/-- `z⁽¹⁾ = −s (sI − A₀)⁻¹ e₁`. -/
@[tmio M, powerlib_domain] theorem zc_eq_inv {s : ℂ} (hD : p.Dg s ≠ 0) :
    p.zc s = -s • ((s • (1 : Matrix (Fin 4) (Fin 4) ℂ) - p.A0.map (algebraMap ℝ ℂ))⁻¹ *ᵥ e0c) := by
  have hu : IsUnit (s • (1 : Matrix (Fin 4) (Fin 4) ℂ) - p.A0.map (algebraMap ℝ ℂ)).det := by
    rw [p.det_sub_A0]; exact isUnit_iff_ne_zero.2 hD
  have hM : (s • (1 : Matrix (Fin 4) (Fin 4) ℂ) - p.A0.map (algebraMap ℝ ℂ)) *ᵥ p.zc s =
      -s • e0c := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]; exact p.zc_eq hD
  calc p.zc s = ((s • (1 : Matrix (Fin 4) (Fin 4) ℂ) - p.A0.map (algebraMap ℝ ℂ))⁻¹ *
        (s • (1 : Matrix (Fin 4) (Fin 4) ℂ) - p.A0.map (algebraMap ℝ ℂ))) *ᵥ p.zc s := by
        rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    _ = _ := by rw [← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul]

/-- `z₃⁽¹⁾ = s z₄⁽¹⁾`. -/
@[tmio M, powerlib_domain] theorem zc_three (s : ℂ) : p.zc s 2 = s * p.zc s 3 := by
  simp [zc]; ring

/-- `z₂⁽¹⁾ = s(1 + z₁⁽¹⁾)/(k_{p,PLL} s + k_{i,PLL})`. -/
@[tmio M, powerlib_domain] theorem zc_two {s : ℂ} (hD : p.Dg s ≠ 0)
    (hk : (p.kp : ℂ) * s + p.ki ≠ 0) : p.zc s 1 = s * (1 + p.zc s 0) / (p.kp * s + p.ki) := by
  rw [eq_div_iff hk]
  simp only [zc]
  simp
  field_simp
  simp only [Dg]
  ring


/-! ### The forced orbit -/

/-- The input direction in the absolute angle: `∂_w F = (k_p v_{d0}, v_{d0}, −A₃₁, 0) = −A₀ e₁`. -/
@[tmio M, powerlib_domain] theorem fderivW_afield (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    fderiv ℝ p.afield (p.xs, 0) (0, 1) = ![p.kp * p.vd0, p.vd0, -p.A31, 0] := by
  refine ParametricResonance.ForcedOrbit.fderivW_of_line
    ((p.contDiffAt_afield (n := 1) (by simp [xs])).differentiableAt (by norm_num))
    (hasDerivAt_pi.2 fun i => ?_)
  have ha : HasDerivAt (fun s : ℝ => p.δ0 - (0 + s)) (-1) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_add 0).const_sub p.δ0
  fin_cases i
  · have h := ((ha.sin.const_mul (-p.V0)).add_const (p.Xg * p.id0)).const_mul p.kp
    refine (h.add_const 0).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      |>.congr_deriv ?_
    · simp [afield, xs, idv]
    · simp [vd0]
  · refine ((ha.sin.const_mul (-p.V0)).add_const (p.Xg * p.id0)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => ?_) |>.congr_deriv ?_
    · simp [afield, xs, idv]
    · simp [vd0]
  · have h := (((ha.cos.const_mul p.V0).mul_const p.id0).div_const 1).const_sub (p.vd0 * p.id0)
      |>.const_mul (3 / (2 * p.C))
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_) |>.congr_deriv ?_
    · simp [afield, xs, idv]
    · simp [A31]
      linear_combination (3 * p.id0 / (2 * p.C)) * hs
  · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp [afield, xs])

/-- In the absolute angle the forced response is `z⁽¹⁾ + e₁`. -/
@[tmio M, powerlib_domain] theorem hz_afield (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) {ω : ℝ}
    (hD : p.Dg (ω * I) ≠ 0) :
    ((ω : ℂ) * I) • (p.zc (ω * I) + e0c) -
        (matX p.afield (p.xs, 0)).map (algebraMap ℝ ℂ) *ᵥ (p.zc (ω * I) + e0c) =
      ((1 : ℝ) : ℂ) • fun i => ((fderiv ℝ p.afield (p.xs, 0) (0, 1) i : ℝ) : ℂ) := by
  rw [p.matX_afield_xs hs, p.fderivW_afield hs, smul_add, Matrix.mulVec_add, add_sub_add_comm,
    p.zc_eq hD]
  funext i
  fin_cases i <;> simp [A0, e0c, mulVec, dotProduct, Fin.sum_univ_four, Matrix.vecHead,
    Matrix.vecTail]

/-- A Hurwitz `A₀` has no eigenvalue `jω`: `D_GFL(jω) ≠ 0`. -/
@[tmio M, powerlib_domain] theorem Dg_ne_of_hurwitz (hA : LinearSystems.IsHurwitz p.A0) (ω : ℝ) :
    p.Dg (ω * I) ≠ 0 := by
  intro h
  rw [← p.det_sub_A0] at h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have he : p.A0.map (algebraMap ℝ ℂ) *ᵥ v = ((ω : ℂ) * I) • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMv
    exact hMv.symm
  have := hA _ v hv he
  simp at this

@[tmio M, powerlib_domain] theorem harm_add_e0 (z : Fin 4 → ℂ) (ω t : ℝ) :
    harm (z + e0c) ω t = harm z ω t + Real.cos (ω * t) • e0 := by
  funext i
  fin_cases i
  · simp [harm, e0c, e0]; ring
  all_goals simp [harm, e0c, e0]

/-- The periodic GFL response to the grid-angle variation `θ_g = θ_{g0} + ε cos ω_p t`, for a Hurwitz
`A₀` and any `ω_p > 0`: for all small `ε > 0` there is a `2π/ω_p`-periodic solution `y` of the
absolute-angle system in the ball of radius `cε`, unique there; its deviation
`η = y − ε cos(ω_p t) e₁` solves the source's equations with `θ̇_g = −εω_p sin ω_p t`, and
`η = ε Re{z⁽¹⁾ e^{jω_p t}} + O(ε²)`. -/
@[tmio M, powerlib_domain] theorem orbit_angle (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (hA : LinearSystems.IsHurwitz p.A0) {ω : ℝ} (hω : 0 < ω) :
    ∃ c C ε1, 0 ≤ c ∧ 0 ≤ C ∧ 0 < ε1 ∧ ∀ ε, 0 < ε → ε ≤ ε1 →
      (∃ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (p.afield (p.xs + y t, ε * Real.cos (ω * t))) t) ∧
      (∀ y1 y2 : ℝ → Fin 4 → ℝ, (∀ t, y1 (t + 2 * Real.pi / ω) = y1 t) →
        (∀ t, ‖y1 t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y1 (p.afield (p.xs + y1 t, ε * Real.cos (ω * t))) t) →
        (∀ t, y2 (t + 2 * Real.pi / ω) = y2 t) → (∀ t, ‖y2 t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y2 (p.afield (p.xs + y2 t, ε * Real.cos (ω * t))) t) → y1 = y2) ∧
      ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (p.afield (p.xs + y t, ε * Real.cos (ω * t))) t) →
        (∀ t, HasDerivAt (fun t => y t - (ε * Real.cos (ω * t)) • e0)
          (p.field (p.xs + (y t - (ε * Real.cos (ω * t)) • e0))
            (-(ε * ω * Real.sin (ω * t)))) t) ∧
        ∀ t, ‖(y t - (ε * Real.cos (ω * t)) • e0) - ε • harm (p.zc (ω * I)) ω t‖ ≤ C * ε ^ 2 := by
  have hq : (p.xs, (0 : ℝ)).1 2 ≠ 0 := by simp [xs]
  have hA' : LinearSystems.IsHurwitz (matX p.afield (p.xs, 0)) := by
    rw [p.matX_afield_xs hs]; exact hA
  have hF0 : p.afield (p.xs, 0) = 0 := by
    have := p.field_xs hs
    rw [p.field_eq_afield _ 0] at this
    simpa using this
  obtain ⟨c, C, ε1, hc, hC, hε1, H⟩ := ParametricResonance.ForcedOrbit.smooth_forced_orbit_hurwitz
    (p.contDiffAt_afield hq) hF0 hA' hω (p.hz_afield hs (p.Dg_ne_of_hurwitz hA ω))
  have e : ∀ ε t (v : Fin 4 → ℝ), p.afield ((p.xs, (0 : ℝ)).1 + v,
      (p.xs, (0 : ℝ)).2 + ε * (1 * Real.cos (ω * t))) = p.afield (p.xs + v, ε * Real.cos (ω * t)) :=
    fun ε t v => by simp
  refine ⟨c, C, ε1, hc, hC, hε1, fun ε hε hε' => ?_⟩
  obtain ⟨⟨y, hy1, hy2, hy3⟩, huniq, hexp⟩ := H ε hε hε'
  refine ⟨⟨y, hy1, hy2, fun t => by rw [← e]; exact hy3 t⟩,
    fun y1 y2 h1 h2 h3 h4 h5 h6 => huniq y1 y2 h1 h2 (fun t => by rw [e]; exact h3 t) h4 h5
      (fun t => by rw [e]; exact h6 t), fun y hy1 hy2 hy3 => ⟨fun t => ?_, fun t => ?_⟩⟩
  · have hw : ∀ t, HasDerivAt (fun t => ε * Real.cos (ω * t)) (-(ε * ω * Real.sin (ω * t))) t :=
      fun t => by
        have := (((hasDerivAt_id' t).const_mul ω).cos).const_mul ε
        exact this.congr_deriv (by ring)
    exact p.shift_solution hw hy3 t
  · have h := hexp y hy1 hy2 (fun t => by rw [e]; exact hy3 t) t
    rw [harm_add_e0, smul_add, smul_smul] at h
    convert h using 2
    abel

/-! ### The first-order periodic coefficient `A₁` -/

/-- `3/(2C)`. -/
def kdc : ℝ := 3 / (2 * p.C)

/-- The derivative of the Jacobian at the operating point along `y`. -/
def dJ (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![p.kp * (p.V0 * Real.sin p.δ0 * y 0), 0, 0, 0;
    p.V0 * Real.sin p.δ0 * y 0, 0, 0, 0;
    p.kdc * (p.vd0 * y 0 * p.id0 +
      p.V0 * Real.sin p.δ0 * (p.kpv * y 2 + p.kiv * y 3) - p.V0 * Real.sin p.δ0 * p.id0 * y 2), 0,
      p.kdc * (p.V0 * Real.sin p.δ0 * y 0 * (p.kpv - p.id0) -
        p.vd0 * (2 * (p.id0 - p.kpv) * y 2 - p.kiv * y 3)),
      p.kdc * (p.kiv * (p.V0 * Real.sin p.δ0 * y 0 + p.vd0 * y 2));
    0, 0, 0, 0]

/-- The complex current coefficient `î_d = k_pv z₃ + k_iv z₄`. -/
def ih (z : Fin 4 → ℂ) : ℂ := p.kpv * z 2 + p.kiv * z 3
/-- The d-axis voltage coefficient `v̂_d = −X_g i_{d0} z₁`. -/
def vh (z : Fin 4 → ℂ) : ℂ := -(p.Xg * p.id0 * z 0)
/-- `b₁ = v_{d0} i_{d0} z₁ + X_g i_{d0}(î_d − i_{d0} z₃)`. -/
def b1 (z : Fin 4 → ℂ) : ℂ := p.vd0 * p.id0 * z 0 + p.Xg * p.id0 * (p.ih z - p.id0 * z 2)
/-- `b₃ = −(k_pv − i_{d0}) v̂_d − v_{d0}[(2i_{d0} − k_pv) z₃ − î_d]`. -/
def b3 (z : Fin 4 → ℂ) : ℂ :=
  -((p.kpv - p.id0) * p.vh z) - p.vd0 * ((2 * p.id0 - p.kpv) * z 2 - p.ih z)
/-- `b₄ = −k_iv(v̂_d − v_{d0} z₃)`. -/
def b4 (z : Fin 4 → ℂ) : ℂ := -(p.kiv * (p.vh z - p.vd0 * z 2))

/-- The GFL periodic coefficient matrix `A₁(ω_p)` in terms of the response `z = z⁽¹⁾`. -/
def gA1 (z : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![p.kp * p.Xg * p.id0 * z 0, 0, 0, 0;
    p.Xg * p.id0 * z 0, 0, 0, 0;
    (p.kdc : ℂ) * p.b1 z, 0, (p.kdc : ℂ) * p.b3 z, (p.kdc : ℂ) * p.b4 z;
    0, 0, 0, 0]

@[tmio M, powerlib_domain] theorem smDx_afield (y : Fin 4 → ℝ) :
    smDx p.afield (p.xs, 0) y = p.dJ y := by
  have hq : (p.xs, (0 : ℝ)).1 2 ≠ 0 := by simp [xs]
  have hF2 : ContDiffAt ℝ 2 p.afield (p.xs, 0) := p.contDiffAt_afield hq
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (p.xs + t • y) 2 ≠ 0 := by
    have hc : Continuous fun t : ℝ => (p.xs + t • y) 2 := by fun_prop
    exact (hc.tendsto 0).eventually_ne (by simp [xs])
  have hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matX p.afield ((p.xs, (0 : ℝ)).1 + t • y, (p.xs, (0 : ℝ)).2) =
      p.jac (p.xs + t • y) := hev.mono fun t ht => by
    rw [p.matX_afield (by simpa using ht)]; simp
  refine ParametricResonance.ForcedOrbit.smDx_of_line hF2 y hJ fun i j => ?_
  have hl : ∀ k, HasDerivAt (fun t : ℝ => (p.xs + t • y) k) (y k) 0 := fun k => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y k)).const_add (p.xs k)
  have hc : HasDerivAt (fun t : ℝ => Real.cos ((p.xs + t • y) 0)) (-Real.sin p.δ0 * y 0) 0 := by
    simpa [xs] using (hl 0).cos
  have hs : HasDerivAt (fun t : ℝ => Real.sin ((p.xs + t • y) 0)) (Real.cos p.δ0 * y 0) 0 := by
    simpa [xs] using (hl 0).sin
  have hid : HasDerivAt (fun t : ℝ => p.idv (p.xs + t • y)) (p.kpv * y 2 + p.kiv * y 3) 0 :=
    ((((hl 2).sub_const 1).const_mul p.kpv).const_add p.id0).add ((hl 3).const_mul p.kiv)
  have h2 : (p.xs + (0 : ℝ) • y) 2 = 1 := by simp [xs]
  have hid0 : p.idv (p.xs + (0 : ℝ) • y) = p.id0 := by simp [idv, xs]
  fin_cases i <;> fin_cases j
  · exact ((hc.const_mul p.V0).const_mul (-p.kp)).congr_deriv
      (by show _ = p.kp * (p.V0 * Real.sin p.δ0 * y 0); ring)
  · exact hasDerivAt_const (0 : ℝ) p.ki
  · exact hasDerivAt_const (0 : ℝ) (p.kp * p.Xg * p.kpv)
  · exact hasDerivAt_const (0 : ℝ) (p.kp * p.Xg * p.kiv)
  · exact ((hc.const_mul p.V0).neg).congr_deriv
      (by show _ = p.V0 * Real.sin p.δ0 * y 0; ring)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (p.Xg * p.kpv)
  · exact hasDerivAt_const (0 : ℝ) (p.Xg * p.kiv)
  · have h := ((((hs.const_mul (3 * p.V0)).mul hid).div_const (2 * p.C)).div (hl 2)
      (by simp [xs]))
    refine h.congr_deriv ?_
    simp [dJ, kdc, xs, idv, vd0]
    ring
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · have h := (((hc.const_mul p.V0).const_mul 3).div_const (2 * p.C)).mul
      (((hasDerivAt_const (0 : ℝ) p.kpv).div (hl 2) (by simp [xs])).sub
        (hid.div ((hl 2).pow 2) (by simp [xs])))
    refine h.neg.congr_deriv ?_
    simp [dJ, kdc, xs, idv, vd0]
    ring
  · have h := ((((hc.const_mul p.V0).const_mul 3).mul_const p.kiv).div_const (2 * p.C)).div (hl 2)
      (by simp [xs])
    refine h.neg.congr_deriv ?_
    simp [dJ, kdc, xs, vd0]
    ring
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (1 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)


@[tmio M, powerlib_domain] theorem smM1_afield : smM1 p.afield (p.xs, 0) = -p.dJ e0 := by
  have hF2 : ContDiffAt ℝ 2 p.afield (p.xs, 0) := p.contDiffAt_afield (by simp [xs])
  ext i j
  have h1 := ParametricResonance.ForcedOrbit.hasDerivAt_matX_line hF2 ((0 : Fin 4 → ℝ), (1 : ℝ)) i j
  have h2 := ParametricResonance.ForcedOrbit.hasDerivAt_matX_line hF2 (-e0, (0 : ℝ)) i j
  have heq : (fun t : ℝ => ((matX p.afield ((p.xs, (0 : ℝ)) + t • ((0 : Fin 4 → ℝ), (1 : ℝ))) i j :
      ℝ) : ℂ)) = fun t => ((matX p.afield ((p.xs, (0 : ℝ)) + t • (-e0, (0 : ℝ))) i j : ℝ) : ℂ) := by
    funext t
    have e1 : ((p.xs, (0 : ℝ)) + t • ((0 : Fin 4 → ℝ), (1 : ℝ))) = (p.xs, t) := by
      ext <;> simp
    have e2 : ((p.xs, (0 : ℝ)) + t • (-e0, (0 : ℝ))) = (p.xs - t • e0, 0) := by
      ext <;> simp [sub_eq_add_neg]
    rw [e1, e2, p.matX_afield (by simp [xs]), p.matX_afield (by simp [xs, e0])]
    simp
  rw [heq] at h1
  have h := Complex.ofReal_injective (h1.unique h2)
  have e1 : smM1 p.afield (p.xs, 0) i j = LinearMap.toMatrix'
      ((fderiv ℝ (ParametricResonance.ForcedOrbit.jacX p.afield) (p.xs, 0) ((0 : Fin 4 → ℝ), (1 : ℝ)) :
        (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) i j := rfl
  have e2 : LinearMap.toMatrix'
      ((fderiv ℝ (ParametricResonance.ForcedOrbit.jacX p.afield) (p.xs, 0) (-e0, (0 : ℝ)) :
        (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) i j =
      smDx p.afield (p.xs, 0) (-e0) i j := rfl
  rw [e1, h, e2, p.smDx_afield]
  fin_cases i <;> fin_cases j <;> simp [dJ, e0]

/-- `A₁ = D_x(∂ₓF)[z⁽¹⁾ + e₁] + D_w(∂ₓF)` of the absolute-angle field is the source's `A₁(ω_p)`. -/
@[tmio M, powerlib_domain] theorem smA1_afield (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (z : Fin 4 → ℂ) : smA1 p.afield (p.xs, 0) 1 (z + e0c) = p.gA1 z := by
  ext i j
  simp only [ParametricResonance.ForcedOrbit.smA1, ParametricResonance.ForcedOrbit.DxC,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, p.smM1_afield, p.smDx_afield]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [dJ, gA1, e0c, e0, b1, b3, b4, ih, vh, hs, Complex.mul_re, Complex.mul_im,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-- Along the forced GFL trajectory `J_p(t; ε) = A₀ + ε Re{A₁(ω_p) e^{jω_p t}} + O(ε²)`, with
`A₁ = gA1 z⁽¹⁾(jω_p)`. -/
@[tmio M, powerlib_domain] theorem jac_angle_expansion
    (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hA : LinearSystems.IsHurwitz p.A0) {ω : ℝ}
    (hω : 0 < ω) :
    ∃ c K ε2, 0 ≤ c ∧ 0 ≤ K ∧ 0 < ε2 ∧ ∀ ε, 0 < ε → ε ≤ ε2 →
      (∃ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (p.afield (p.xs + y t, ε * Real.cos (ω * t))) t) ∧
      ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (p.afield (p.xs + y t, ε * Real.cos (ω * t))) t) →
        ∀ t, ‖p.jac (p.xs + (y t - (ε * Real.cos (ω * t)) • e0)) - p.A0 -
          ε • BlockAveraging.modX (p.gA1 (p.zc (ω * I))) ω t‖ ≤ K * ε ^ 2 := by
  obtain ⟨c, C, ε1, hc, hC, hε1, H⟩ := p.orbit_angle hs hA hω
  have hq : (p.xs, (0 : ℝ)).1 2 ≠ 0 := by simp [xs]
  have hF0 : p.afield (p.xs, 0) = 0 := by
    have := p.field_xs hs
    rw [p.field_eq_afield _ 0] at this
    simpa using this
  obtain ⟨K, ε2, hK, hε2, HJ⟩ := ParametricResonance.ForcedOrbit.jac_orbit_expansion
    (p.contDiffAt_afield hq) hF0 hω.ne' (p.hz_afield hs (p.Dg_ne_of_hurwitz hA ω)) (C := C) hc
  refine ⟨c, K, min ε1 (min ε2 (1 / (2 * (c + 1)))), hc, hK,
    lt_min hε1 (lt_min hε2 (by positivity)), fun ε hε hε' => ?_⟩
  have hε1' : ε ≤ ε1 := hε'.trans (min_le_left _ _)
  have hε2' : ε ≤ ε2 := hε'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε ≤ 1 / (2 * (c + 1)) := hε'.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hex, -, hexp⟩ := H ε hε hε1'
  refine ⟨hex, fun y hy1 hy2 hy3 t => ?_⟩
  have hy2' : |y t 2| < 1 := by
    have h1 : |y t 2| ≤ ‖y t‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm (y t) 2
    have h2 : c * ε < 1 := by
      calc c * ε ≤ c * (1 / (2 * (c + 1))) := by gcongr
        _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; linarith
    linarith [hy2 t]
  have hne : (p.xs + y t, ε * Real.cos (ω * t)).1 2 ≠ 0 := by
    have hx2 : p.xs 2 = 1 := rfl
    show p.xs 2 + y t 2 ≠ 0
    rw [hx2]
    intro h
    have : y t 2 = -1 := by linarith
    rw [this] at hy2'
    norm_num at hy2'
  have hexp' : ‖y t - ε • harm (p.zc (ω * I) + e0c) ω t‖ ≤ C * ε ^ 2 := by
    have h := (hexp y hy1 hy2 hy3).2 t
    rw [harm_add_e0, smul_add, smul_smul]
    convert h using 2
    abel
  have hj := HJ ε hε.le hε2' t (y t) (hy2 t) hexp'
  rw [p.matX_afield (by simpa using hne), p.matX_afield_xs hs, p.smA1_afield hs] at hj
  convert hj using 3
  simp [add_sub_assoc]

/-! ### Relative modulation of the GFL entries -/

@[tmio M, powerlib_domain] theorem ratio11 (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (hkp : p.kp ≠ 0) (hv : p.vd0 ≠ 0) (z : Fin 4 → ℂ) :
    p.gA1 z 0 0 / (p.A0 0 0 : ℂ) = -(Real.tan p.δ0 : ℂ) * z 0 := by
  have hc : Real.cos p.δ0 ≠ 0 := fun h => hv (by simp [vd0, h])
  have hden : (p.A0 0 0 : ℂ) ≠ 0 := by
    show ((-p.kp * p.vd0 : ℝ) : ℂ) ≠ 0
    exact_mod_cast mul_ne_zero (neg_ne_zero.2 hkp) hv
  have hsc : (p.V0 : ℂ) * Complex.sin p.δ0 = p.Xg * p.id0 := by
    rw [← Complex.ofReal_sin]; exact_mod_cast hs
  have hc1 : Complex.cos p.δ0 * (Complex.cos p.δ0)⁻¹ = 1 :=
    mul_inv_cancel₀ (by rw [← Complex.ofReal_cos]; exact_mod_cast hc)
  rw [div_eq_iff hden]
  show (p.kp : ℂ) * p.Xg * p.id0 * z 0 = -(Real.tan p.δ0 : ℂ) * z 0 * ((-p.kp * p.vd0 : ℝ) : ℂ)
  rw [Real.tan_eq_sin_div_cos, vd0]
  push_cast
  linear_combination (-(p.kp : ℂ) * z 0) * hsc - (p.kp * p.V0 * Complex.sin p.δ0 * z 0) * hc1

@[tmio M, powerlib_domain] theorem ratio21 (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (hv : p.vd0 ≠ 0) (z : Fin 4 → ℂ) :
    p.gA1 z 1 0 / (p.A0 1 0 : ℂ) = -(Real.tan p.δ0 : ℂ) * z 0 := by
  have hc : Real.cos p.δ0 ≠ 0 := fun h => hv (by simp [vd0, h])
  have hden : (p.A0 1 0 : ℂ) ≠ 0 := by
    show ((-p.vd0 : ℝ) : ℂ) ≠ 0
    exact_mod_cast neg_ne_zero.2 hv
  have hsc : (p.V0 : ℂ) * Complex.sin p.δ0 = p.Xg * p.id0 := by
    rw [← Complex.ofReal_sin]; exact_mod_cast hs
  have hc1 : Complex.cos p.δ0 * (Complex.cos p.δ0)⁻¹ = 1 :=
    mul_inv_cancel₀ (by rw [← Complex.ofReal_cos]; exact_mod_cast hc)
  rw [div_eq_iff hden]
  show (p.Xg : ℂ) * p.id0 * z 0 = -(Real.tan p.δ0 : ℂ) * z 0 * ((-p.vd0 : ℝ) : ℂ)
  rw [Real.tan_eq_sin_div_cos, vd0]
  push_cast
  linear_combination (-(z 0)) * hsc - (p.V0 * Complex.sin p.δ0 * z 0) * hc1

@[tmio M, powerlib_domain] theorem ratio31 (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (hX : p.Xg ≠ 0) (hi : p.id0 ≠ 0) (hC : p.C ≠ 0) (z : Fin 4 → ℂ) :
    p.gA1 z 2 0 / (p.A0 2 0 : ℂ) = (Real.cot p.δ0 : ℂ) * z 0 + p.ih z / p.id0 - z 2 := by
  have hsn : Real.sin p.δ0 ≠ 0 := fun h => by
    have : p.Xg * p.id0 = 0 := by rw [← hs, h, mul_zero]
    exact mul_ne_zero hX hi this
  have hden : (p.A0 2 0 : ℂ) ≠ 0 := by
    show ((p.A31 : ℝ) : ℂ) ≠ 0
    simp only [A31]
    exact_mod_cast div_ne_zero (mul_ne_zero (mul_ne_zero three_ne_zero hX) (pow_ne_zero 2 hi))
      (mul_ne_zero two_ne_zero hC)
  have hsc : (p.V0 : ℂ) * Complex.sin p.δ0 = p.Xg * p.id0 := by
    rw [← Complex.ofReal_sin]; exact_mod_cast hs
  have hs1 : Complex.sin p.δ0 * (Complex.sin p.δ0)⁻¹ = 1 :=
    mul_inv_cancel₀ (by rw [← Complex.ofReal_sin]; exact_mod_cast hsn)
  have hi1 : (p.id0 : ℂ) * (p.id0 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hi)
  rw [div_eq_iff hden]
  show (p.kdc : ℂ) * p.b1 z = ((Real.cot p.δ0 : ℂ) * z 0 + p.ih z / p.id0 - z 2) * ((p.A31 : ℝ) : ℂ)
  rw [Real.cot_eq_cos_div_sin]
  simp only [kdc, b1, A31, vd0]
  push_cast
  linear_combination (3 / (2 * (p.C : ℂ)) * (p.id0 * Complex.cos p.δ0 *
    (Complex.sin p.δ0)⁻¹ * z 0)) * hsc - (3 / (2 * (p.C : ℂ)) * (p.V0 * Complex.cos p.δ0 * p.id0 *
    z 0)) * hs1 - (3 / (2 * (p.C : ℂ)) * (p.Xg * p.id0 * p.ih z)) * hi1

@[tmio M, powerlib_domain] theorem ratio33 (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (hv : p.vd0 ≠ 0) (hk : p.kpv - p.id0 ≠ 0) (hC : p.C ≠ 0) (z : Fin 4 → ℂ) :
    p.gA1 z 2 2 / (p.A0 2 2 : ℂ) =
      -(Real.tan p.δ0 : ℂ) * z 0 - 2 * z 2 - p.kiv / (p.kpv - p.id0) * z 3 := by
  have hc : Real.cos p.δ0 ≠ 0 := fun h => hv (by simp [vd0, h])
  have hden : (p.A0 2 2 : ℂ) ≠ 0 := by
    show ((-(3 * p.vd0 * (p.kpv - p.id0)) / (2 * p.C) : ℝ) : ℂ) ≠ 0
    exact_mod_cast div_ne_zero (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero three_ne_zero hv) hk))
      (mul_ne_zero two_ne_zero hC)
  have hsc : (p.V0 : ℂ) * Complex.sin p.δ0 = p.Xg * p.id0 := by
    rw [← Complex.ofReal_sin]; exact_mod_cast hs
  have hc1 : Complex.cos p.δ0 * (Complex.cos p.δ0)⁻¹ = 1 :=
    mul_inv_cancel₀ (by rw [← Complex.ofReal_cos]; exact_mod_cast hc)
  have hk1 : ((p.kpv : ℂ) - p.id0) * ((p.kpv : ℂ) - p.id0)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast hk)
  rw [div_eq_iff hden]
  show (p.kdc : ℂ) * p.b3 z = (-(Real.tan p.δ0 : ℂ) * z 0 - 2 * z 2 - p.kiv / (p.kpv - p.id0) * z 3) *
    ((-(3 * p.vd0 * (p.kpv - p.id0)) / (2 * p.C) : ℝ) : ℂ)
  rw [Real.tan_eq_sin_div_cos]
  simp only [kdc, b3, vh, ih, vd0]
  push_cast
  linear_combination (-(3 / (2 * (p.C : ℂ))) * (p.kpv - p.id0) * z 0) * hsc -
    (3 / (2 * (p.C : ℂ)) * (p.kpv - p.id0) * z 0 * p.V0 * Complex.sin p.δ0) * hc1 -
    (3 / (2 * (p.C : ℂ)) * (p.V0 * Complex.cos p.δ0) * p.kiv * z 3) * hk1

@[tmio M, powerlib_domain] theorem ratio34 (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (hv : p.vd0 ≠ 0) (hkiv : p.kiv ≠ 0) (hC : p.C ≠ 0) (z : Fin 4 → ℂ) :
    p.gA1 z 2 3 / (p.A0 2 3 : ℂ) = -(Real.tan p.δ0 : ℂ) * z 0 - z 2 := by
  have hc : Real.cos p.δ0 ≠ 0 := fun h => hv (by simp [vd0, h])
  have hden : (p.A0 2 3 : ℂ) ≠ 0 := by
    show ((-(3 * p.vd0 * p.kiv) / (2 * p.C) : ℝ) : ℂ) ≠ 0
    exact_mod_cast div_ne_zero (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero three_ne_zero hv) hkiv))
      (mul_ne_zero two_ne_zero hC)
  have hsc : (p.V0 : ℂ) * Complex.sin p.δ0 = p.Xg * p.id0 := by
    rw [← Complex.ofReal_sin]; exact_mod_cast hs
  have hc1 : Complex.cos p.δ0 * (Complex.cos p.δ0)⁻¹ = 1 :=
    mul_inv_cancel₀ (by rw [← Complex.ofReal_cos]; exact_mod_cast hc)
  rw [div_eq_iff hden]
  show (p.kdc : ℂ) * p.b4 z = (-(Real.tan p.δ0 : ℂ) * z 0 - z 2) *
    ((-(3 * p.vd0 * p.kiv) / (2 * p.C) : ℝ) : ℂ)
  rw [Real.tan_eq_sin_div_cos]
  simp only [kdc, b4, vh, vd0]
  push_cast
  linear_combination (-(3 / (2 * (p.C : ℂ))) * p.kiv * z 0) * hsc -
    (3 / (2 * (p.C : ℂ)) * p.kiv * z 0 * p.V0 * Complex.sin p.δ0) * hc1

/-! ### Modal contributions -/

/-- `g_m = Γ₁₁ + Γ₂₁ + Γ₃₁ + Γ₃₃ + Γ₃₄`: only five entries of `A₁` are modulated. -/
@[tmio M, powerlib_domain] theorem pump_eq_sum (z u r : Fin 4 → ℂ) :
    ParametricResonance.Element.pump (p.gA1 z) u r =
      ParametricResonance.Element.contribution (p.gA1 z) u r 0 0 +
      ParametricResonance.Element.contribution (p.gA1 z) u r 1 0 +
      ParametricResonance.Element.contribution (p.gA1 z) u r 2 0 +
      ParametricResonance.Element.contribution (p.gA1 z) u r 2 2 +
      ParametricResonance.Element.contribution (p.gA1 z) u r 2 3 := by
  simp [ParametricResonance.Element.pump, ParametricResonance.Element.contribution, gA1,
    dotProduct, mulVec, Fin.sum_univ_four]
  ring

/-- The PLL–DVC contribution
`Γ₃₁ = (3 l*_{m,3} r*_{m,1}/2C)[v_{d0} i_{d0} z₁ + X_g i_{d0}(î_d − i_{d0} z₃)]`. -/
@[tmio M, powerlib_domain] theorem contribution31 (z u r : Fin 4 → ℂ) :
    ParametricResonance.Element.contribution (p.gA1 z) u r 2 0 =
      3 * u 2 * star (r 0) / (2 * p.C) *
        (p.vd0 * p.id0 * z 0 + p.Xg * p.id0 * (p.ih z - p.id0 * z 2)) := by
  simp [ParametricResonance.Element.contribution, gA1, b1, kdc]
  ring

/-! ### Nominal stability restricts the equilibrium angle -/

@[tmio M, powerlib_domain] theorem det_neg_A0_eq : (-p.A0).det = p.da0 := by
  have h := p.det_sub_A0 0
  rw [p.Dg_eq] at h
  have hm : (0 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - p.A0.map (algebraMap ℝ ℂ) =
      (-p.A0).map (algebraMap ℝ ℂ) := by
    ext i j; simp
  rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  simp at h
  exact_mod_cast h

/-- `det(−A₀) = (3k_{i,PLL}k_iv V₀²/2C) cos 2δ₀`. -/
@[tmio M, powerlib_domain] theorem det_neg_A0 (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    (-p.A0).det = 3 * p.ki * p.kiv * p.V0 ^ 2 * Real.cos (2 * p.δ0) / (2 * p.C) := by
  rw [p.det_neg_A0_eq, Real.cos_two_mul]
  simp only [da0, Gam, A31, vd0]
  have h := Real.sin_sq_add_cos_sq p.δ0
  linear_combination (3 * p.ki * p.kiv / (2 * p.C) * (p.V0 * Real.sin p.δ0 + p.Xg * p.id0)) *
    hs - (3 * p.ki * p.kiv * p.V0 ^ 2 / (2 * p.C)) * h

/-- A stable fourth-order matrix has `det(−A₀) > 0`; with `C, k_{i,PLL}, k_iv > 0` this forces
`cos 2δ₀ > 0`. -/
@[tmio M, powerlib_domain] theorem cos_two_pos_of_hurwitz
    (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hA : LinearSystems.IsHurwitz p.A0)
    (hC : 0 < p.C) (hki : 0 < p.ki) (hkiv : 0 < p.kiv) : 0 < Real.cos (2 * p.δ0) := by
  have H : ∀ s : ℂ, s ^ 4 + (p.da3 : ℂ) * s ^ 3 + (p.da2 : ℂ) * s ^ 2 + (p.da1 : ℂ) * s +
      (p.da0 : ℂ) = 0 → s.re < 0 := by
    intro s hs0
    rw [← p.Dg_eq, ← p.det_sub_A0] at hs0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hs0
    have he : p.A0.map (algebraMap ℝ ℂ) *ᵥ v = s • v := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMv
      exact hMv.symm
    simpa using hA s v hv he
  obtain ⟨-, -, h0, -⟩ := Criteria.quartic_routh_of_roots_re_neg H
  rw [← p.det_neg_A0_eq, p.det_neg_A0 hs] at h0
  by_contra hneg
  rw [not_lt] at hneg
  have hK : 0 ≤ 3 * p.ki * p.kiv * p.V0 ^ 2 / (2 * p.C) := by positivity
  have : 3 * p.ki * p.kiv * p.V0 ^ 2 * Real.cos (2 * p.δ0) / (2 * p.C) ≤ 0 := by
    rw [show 3 * p.ki * p.kiv * p.V0 ^ 2 * Real.cos (2 * p.δ0) / (2 * p.C) =
      3 * p.ki * p.kiv * p.V0 ^ 2 / (2 * p.C) * Real.cos (2 * p.δ0) by ring]
    exact mul_nonpos_of_nonneg_of_nonpos hK hneg
  linarith

end Params

/-- On the branch `|δ₀| < π/2`, `cos 2δ₀ > 0` gives `|δ₀| < π/4`. -/
@[tmio M, powerlib_domain] theorem angle_lt_pi_div_four {δ0 : ℝ} (hc : 0 < Real.cos (2 * δ0))
    (hb : |δ0| < Real.pi / 2) : |δ0| < Real.pi / 4 := by
  by_contra h
  rw [not_lt] at h
  have h1 : Real.pi / 2 ≤ |2 * δ0| := by rw [abs_mul, abs_two]; linarith
  have h2 : |2 * δ0| ≤ Real.pi + Real.pi / 2 := by
    rw [abs_mul, abs_two]; linarith [Real.pi_pos]
  have := Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
  rw [Real.cos_abs] at this
  linarith

/-- For a nonzero operating angle in the stable range, `0 < |tan δ₀| < 1 < |cot δ₀|`. -/
@[tmio M, powerlib_domain] theorem tan_cot_bounds {δ0 : ℝ} (hc : 0 < Real.cos (2 * δ0))
    (hb : |δ0| < Real.pi / 2) (h0 : δ0 ≠ 0) :
    0 < |Real.tan δ0| ∧ |Real.tan δ0| < 1 ∧ 1 < |Real.cot δ0| := by
  have hcos : 0 < Real.cos δ0 := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le δ0],
    by linarith [le_abs_self δ0]⟩
  have hsin : Real.sin δ0 ≠ 0 := by
    intro h
    rw [Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le δ0, Real.pi_pos])
      (by linarith [le_abs_self δ0, Real.pi_pos])] at h
    exact h0 h
  have hsq : Real.sin δ0 ^ 2 < Real.cos δ0 ^ 2 := by
    rw [Real.cos_two_mul] at hc
    nlinarith [Real.sin_sq_add_cos_sq δ0]
  have ht : |Real.tan δ0| = |Real.sin δ0| / Real.cos δ0 := by
    rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcos]
  have hct : |Real.cot δ0| = Real.cos δ0 / |Real.sin δ0| := by
    rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hcos]
  have hsa : 0 < |Real.sin δ0| := abs_pos.2 hsin
  have hlt : |Real.sin δ0| < Real.cos δ0 :=
    lt_of_pow_lt_pow_left₀ 2 hcos.le (by rw [sq_abs]; exact hsq)
  refine ⟨by rw [ht]; positivity, by rw [ht, div_lt_one hcos]; exact hlt, ?_⟩
  rw [hct, one_lt_div hsa]
  exact hlt

/-- `|cot δ₀|² ∼ δ₀⁻²` and `|tan δ₀| ∼ |δ₀|` as `δ₀ → 0`. -/
@[tmio M, powerlib_domain] theorem cot_tan_asymp :
    Tendsto (fun δ : ℝ => δ ^ 2 * Real.cot δ ^ 2) (𝓝[≠] 0) (𝓝 1) ∧
      Tendsto (fun δ : ℝ => Real.tan δ ^ 2 / δ ^ 2) (𝓝[≠] 0) (𝓝 1) := by
  have hs : Tendsto Real.sinc (𝓝[≠] 0) (𝓝 1) := by
    rw [← Real.sinc_zero]; exact Real.continuous_sinc.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hc : Tendsto Real.cos (𝓝[≠] 0) (𝓝 1) := by
    rw [← Real.cos_zero]; exact Real.continuous_cos.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have ev : ∀ᶠ δ in 𝓝[≠] (0 : ℝ), δ ≠ 0 := self_mem_nhdsWithin
  constructor
  · have h := (hc.pow 2).div (hs.pow 2) (by norm_num)
    rw [one_pow, div_one] at h
    refine h.congr' ?_
    filter_upwards [ev] with δ hδ
    simp only [Pi.div_apply]
    rw [Real.sinc_of_ne_zero hδ, Real.cot_eq_cos_div_sin]
    by_cases hsn : Real.sin δ = 0
    · simp [hsn]
    · field_simp
  · have h := (hs.pow 2).div (hc.pow 2) (by norm_num)
    rw [one_pow, div_one] at h
    refine h.congr' ?_
    filter_upwards [ev] with δ hδ
    simp only [Pi.div_apply]
    rw [Real.sinc_of_ne_zero hδ, Real.tan_eq_sin_div_cos]
    by_cases hcs : Real.cos δ = 0
    · simp [hcs]
    · field_simp

/-- The angle-response parts `Γ^{(δ)}_{ik} = ρ^{(δ)}_{ik}(r̄_k/r_k)w_ik` with `ρ^{(δ)}_{31} = cot δ₀ z₁`
and `ρ^{(δ)}_{ik} = −tan δ₀ z₁` otherwise: `|Γ^{(δ)}_{31}|/|Γ^{(δ)}_{ik}| = |cot δ₀|²|w₃₁|/|w_ik|`. -/
@[tmio M, powerlib_domain] theorem delta_ratio {δ0 : ℝ} (hsn : Real.sin δ0 ≠ 0)
    (hcs : Real.cos δ0 ≠ 0) {z1 w31 w r1 rk : ℂ} (hz : z1 ≠ 0) (hw : w ≠ 0) (hr1 : r1 ≠ 0)
    (hrk : rk ≠ 0) :
    ‖(Real.cot δ0 : ℂ) * z1 * (star r1 / r1) * w31‖ /
        ‖(-(Real.tan δ0 : ℂ)) * z1 * (star rk / rk) * w‖ =
      |Real.cot δ0| ^ 2 * ‖w31‖ / ‖w‖ := by
  have hn : ∀ r : ℂ, r ≠ 0 → ‖star r / r‖ = 1 := fun r hr => by
    rw [norm_div, norm_star, div_self (norm_ne_zero_iff.2 hr)]
  have ht : |Real.tan δ0| = (|Real.cot δ0|)⁻¹ := by
    rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin, abs_div, abs_div, inv_div]
  have hct : 0 < |Real.cot δ0| := by
    rw [Real.cot_eq_cos_div_sin]; exact abs_pos.2 (div_ne_zero hcs hsn)
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, hn r1 hr1, hn rk hrk,
    mul_one]
  rw [ht]
  have : ‖z1‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  field_simp

/-- From a finite limit of `f·g` and `‖g⁻¹‖ = |h|` eventually, `f = O(h)`. -/
@[tmio T, powerlib_foundation] private theorem isBigO_of_tendsto_mul {l : Filter ℝ}
    {f g : ℝ → ℂ} {h : ℝ → ℝ} {c : ℂ} (H : Tendsto (fun ω => f ω * g ω) l (𝓝 c))
    (hg : ∀ᶠ ω in l, g ω ≠ 0 ∧ ‖(g ω)⁻¹‖ = |h ω|) : f =O[l] h := by
  have h1 : (fun ω => f ω * g ω) =O[l] (fun _ => (1 : ℝ)) := H.isBigO_one ℝ
  have h2 : (fun ω => (g ω)⁻¹) =O[l] h :=
    Asymptotics.IsBigO.of_bound 1 (hg.mono fun ω hω => by rw [hω.2, one_mul, Real.norm_eq_abs])
  refine (h1.mul h2).congr' ?_ ?_
  · filter_upwards [hg] with ω hω
    field_simp [hω.1]
  · filter_upwards with ω
    simp

namespace Params
variable (p : Params)

/-! ### Response component estimates -/

@[tmio M, powerlib_domain] theorem continuous_Ldc : Continuous p.Ldc := by
  unfold Ldc; fun_prop

@[tmio M, powerlib_domain] theorem continuous_Dg : Continuous p.Dg := by
  unfold Dg Ldc; fun_prop

/-- As `ω_p → 0`: `z₁/s² → −L_dc(0)/D(0)`, `z₂/s → (v_{d0}L_dc(0) − Γk_iv)/D(0)`,
`z₃/s³ → −A₃₁/D(0)`, `z₄/s² → −A₃₁/D(0)` (`s = jω_p`, `D(0) = det(−A₀) ≠ 0`). -/
@[tmio M, powerlib_domain] theorem zc_small (hD0 : p.Dg 0 ≠ 0) :
    Tendsto (fun ω : ℝ => p.zc (ω * I) 0 / (ω * I) ^ 2) (𝓝[>] 0)
        (𝓝 (-(p.Ldc 0) / p.Dg 0)) ∧
      Tendsto (fun ω : ℝ => p.zc (ω * I) 1 / (ω * I)) (𝓝[>] 0)
        (𝓝 ((p.vd0 * p.Ldc 0 - p.Gam * p.kiv) / p.Dg 0)) ∧
      Tendsto (fun ω : ℝ => p.zc (ω * I) 2 / (ω * I) ^ 3) (𝓝[>] 0)
        (𝓝 (-(p.A31 : ℂ) / p.Dg 0)) ∧
      Tendsto (fun ω : ℝ => p.zc (ω * I) 3 / (ω * I) ^ 2) (𝓝[>] 0)
        (𝓝 (-(p.A31 : ℂ) / p.Dg 0)) := by
  have hs : Tendsto (fun ω : ℝ => (ω : ℂ) * I) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous fun ω : ℝ => (ω : ℂ) * I := by fun_prop
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hL := (p.continuous_Ldc.tendsto 0).comp hs
  have hD := (p.continuous_Dg.tendsto 0).comp hs
  have ev : ∀ᶠ ω : ℝ in 𝓝[>] (0 : ℝ), (ω : ℂ) * I ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ω hω
    exact mul_ne_zero (by exact_mod_cast (ne_of_gt hω)) I_ne_zero
  refine ⟨(hL.neg.div hD hD0).congr' ?_, ?_, ?_, ?_⟩
  · filter_upwards [ev] with ω hω
    have hω0 : (ω : ℂ) ≠ 0 := left_ne_zero_of_mul hω
    simp only [Function.comp_apply, zc]
    simp
    field_simp
  · have h := (((hL.const_mul (p.vd0 : ℂ)).sub
      (((hs.const_mul (p.kpv : ℂ)).add_const (p.kiv : ℂ)).const_mul (p.Gam : ℂ))).div hD hD0)
    simp only [mul_zero, zero_add] at h
    refine h.congr' ?_
    filter_upwards [ev] with ω hω
    have hω0 : (ω : ℂ) ≠ 0 := left_ne_zero_of_mul hω
    simp only [Function.comp_apply, zc]
    simp
    field_simp
  · refine ((tendsto_const_nhds (x := -(p.A31 : ℂ))).div hD hD0).congr' ?_
    filter_upwards [ev] with ω hω
    have hω0 : (ω : ℂ) ≠ 0 := left_ne_zero_of_mul hω
    simp only [zc]
    simp
    field_simp
  · refine ((tendsto_const_nhds (x := -(p.A31 : ℂ))).div hD hD0).congr' ?_
    filter_upwards [ev] with ω hω
    have hω0 : (ω : ℂ) ≠ 0 := left_ne_zero_of_mul hω
    simp only [zc]
    simp
    field_simp

/-- The rows `ω_p → 0` of the table: `z₁ = O(ω_p²)`, `z₂ = O(ω_p)`, `z₃ = O(ω_p³)`,
`z₄ = O(ω_p²)`. -/
@[tmio M, powerlib_domain] theorem zc_small_isBigO (hD0 : p.Dg 0 ≠ 0) :
    (fun ω : ℝ => p.zc (ω * I) 0) =O[𝓝[>] 0] (fun ω => ω ^ 2) ∧
      (fun ω : ℝ => p.zc (ω * I) 1) =O[𝓝[>] 0] (fun ω => ω) ∧
      (fun ω : ℝ => p.zc (ω * I) 2) =O[𝓝[>] 0] (fun ω => ω ^ 3) ∧
      (fun ω : ℝ => p.zc (ω * I) 3) =O[𝓝[>] 0] (fun ω => ω ^ 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := p.zc_small hD0
  have ev : ∀ n : ℕ, ∀ᶠ ω : ℝ in 𝓝[>] (0 : ℝ), (((ω : ℂ) * I) ^ n)⁻¹ ≠ 0 ∧
      ‖((((ω : ℂ) * I) ^ n)⁻¹)⁻¹‖ = |ω ^ n| := fun n => by
    filter_upwards [self_mem_nhdsWithin] with ω hω
    have hne : (ω : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast (ne_of_gt hω)) I_ne_zero
    refine ⟨inv_ne_zero (pow_ne_zero n hne), ?_⟩
    rw [inv_inv, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_pow]
  refine ⟨isBigO_of_tendsto_mul (g := fun ω : ℝ => (((ω : ℂ) * I) ^ 2)⁻¹)
      (c := -(p.Ldc 0) / p.Dg 0) ?_ (ev 2),
    isBigO_of_tendsto_mul (g := fun ω : ℝ => (((ω : ℂ) * I) ^ 1)⁻¹)
      (c := (p.vd0 * p.Ldc 0 - p.Gam * p.kiv) / p.Dg 0) ?_
      ((ev 1).mono fun ω h => by simpa using h),
    isBigO_of_tendsto_mul (g := fun ω : ℝ => (((ω : ℂ) * I) ^ 3)⁻¹)
      (c := -(p.A31 : ℂ) / p.Dg 0) ?_ (ev 3),
    isBigO_of_tendsto_mul (g := fun ω : ℝ => (((ω : ℂ) * I) ^ 2)⁻¹)
      (c := -(p.A31 : ℂ) / p.Dg 0) ?_ (ev 2)⟩
  · simpa [div_eq_mul_inv] using h1
  · simpa [div_eq_mul_inv] using h2
  · simpa [div_eq_mul_inv] using h3
  · simpa [div_eq_mul_inv] using h4


/-- As `ω_p → ∞`: `(z₁ + 1)s → k_{p,PLL}v_{d0}`, `z₂ s → v_{d0}`, `z₃ s → −A₃₁`, `z₄ s² → −A₃₁`
(`s = jω_p`). -/
@[tmio M, powerlib_domain] theorem zc_large :
    Tendsto (fun ω : ℝ => (p.zc (ω * I) 0 + 1) * (ω * I)) atTop (𝓝 (p.kp * p.vd0)) ∧
      Tendsto (fun ω : ℝ => p.zc (ω * I) 1 * (ω * I)) atTop (𝓝 p.vd0) ∧
      Tendsto (fun ω : ℝ => p.zc (ω * I) 2 * (ω * I)) atTop (𝓝 (-(p.A31 : ℂ))) ∧
      Tendsto (fun ω : ℝ => p.zc (ω * I) 3 * (ω * I) ^ 2) atTop (𝓝 (-(p.A31 : ℂ))) := by
  have hu : Tendsto (fun ω : ℝ => ((ω : ℂ) * I)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun ω : ℝ => (ω : ℂ)⁻¹) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
      simpa [Function.comp_def] using this
    have h2 := h.const_mul (-I)
    rw [mul_zero] at h2
    refine h2.congr' (Filter.Eventually.of_forall fun ω => ?_)
    show -I * (ω : ℂ)⁻¹ = ((ω : ℂ) * I)⁻¹
    rw [mul_inv, Complex.inv_I]
    ring
  set α : ℂ := 3 * p.vd0 / (2 * p.C) with hα
  have hDn : Continuous fun u : ℂ => 1 + (p.da3 : ℂ) * u + p.da2 * u ^ 2 + p.da1 * u ^ 3 +
      p.da0 * u ^ 4 := by fun_prop
  have hDn0 := (hDn.tendsto 0).comp hu
  simp only [Function.comp_def, mul_zero, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_pow (by norm_num : (4 : ℕ) ≠ 0)] at hDn0
  have ev : ∀ᶠ ω : ℝ in atTop, (ω : ℂ) ≠ 0 ∧ 1 + (p.da3 : ℂ) * ((ω : ℂ) * I)⁻¹ +
      p.da2 * ((ω : ℂ) * I)⁻¹ ^ 2 + p.da1 * ((ω : ℂ) * I)⁻¹ ^ 3 + p.da0 * ((ω : ℂ) * I)⁻¹ ^ 4 ≠ 0 := by
    filter_upwards [eventually_ne_atTop 0, hDn0.eventually_ne one_ne_zero] with ω h1 h2
    exact ⟨by exact_mod_cast h1, h2⟩
  have hDg : ∀ ω : ℝ, (ω : ℂ) ≠ 0 → p.Dg (ω * I) = ((ω : ℂ) * I) ^ 4 * (1 + (p.da3 : ℂ) *
      ((ω : ℂ) * I)⁻¹ + p.da2 * ((ω : ℂ) * I)⁻¹ ^ 2 + p.da1 * ((ω : ℂ) * I)⁻¹ ^ 3 +
      p.da0 * ((ω : ℂ) * I)⁻¹ ^ 4) := fun ω hω => by
    have hs : (ω : ℂ) * I ≠ 0 := mul_ne_zero hω I_ne_zero
    rw [p.Dg_eq]
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hP : Continuous fun u : ℂ => (p.kp * p.vd0 : ℂ) + (p.da2 - α * p.kiv) * u +
        p.da1 * u ^ 2 + p.da0 * u ^ 3 := by fun_prop
    have h := ((hP.tendsto 0).comp hu).div hDn0 one_ne_zero
    simp only [Function.comp_def, mul_zero, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_pow (by norm_num : (3 : ℕ) ≠ 0), div_one] at h
    refine h.congr' ?_
    filter_upwards [ev] with ω hω
    obtain ⟨hω0, hDn⟩ := hω
    have hs : (ω : ℂ) * I ≠ 0 := mul_ne_zero hω0 I_ne_zero
    simp only [Pi.div_apply, zc, Matrix.cons_val_zero]
    rw [hDg ω hω0]
    simp only [Ldc, hα]
    generalize (ω : ℂ) * I = s at hs hDn ⊢
    generalize hD : 1 + (p.da3 : ℂ) * s⁻¹ + p.da2 * s⁻¹ ^ 2 + p.da1 * s⁻¹ ^ 3 +
      p.da0 * s⁻¹ ^ 4 = Dn at hDn ⊢
    linear_combination (norm := skip) (s / Dn) * hD
    simp only [da3]
    push_cast
    field_simp
    ring
  · have hP : Continuous fun u : ℂ => (p.vd0 : ℂ) * (1 + α * ((p.kpv - p.id0) * u + p.kiv * u ^ 2)) -
        p.Gam * (p.kpv * u + p.kiv * u ^ 2) := by fun_prop
    have h := ((hP.tendsto 0).comp hu).div hDn0 one_ne_zero
    simp only [Function.comp_def, mul_zero, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      sub_zero, mul_one, div_one] at h
    refine h.congr' ?_
    filter_upwards [ev] with ω hω
    obtain ⟨hω0, hDn⟩ := hω
    have hs : (ω : ℂ) * I ≠ 0 := mul_ne_zero hω0 I_ne_zero
    simp only [Pi.div_apply, zc]
    simp only [Matrix.cons_val]
    rw [hDg ω hω0]
    simp only [Ldc, hα]
    generalize (ω : ℂ) * I = s at hs hDn ⊢
    generalize 1 + (p.da3 : ℂ) * s⁻¹ + p.da2 * s⁻¹ ^ 2 + p.da1 * s⁻¹ ^ 3 +
      p.da0 * s⁻¹ ^ 4 = Dn at hDn ⊢
    field_simp
  · refine ((tendsto_const_nhds (x := -(p.A31 : ℂ))).div hDn0 one_ne_zero |>.congr' ?_).trans ?_
    · filter_upwards [ev] with ω hω
      obtain ⟨hω0, hDn⟩ := hω
      have hs : (ω : ℂ) * I ≠ 0 := mul_ne_zero hω0 I_ne_zero
      simp only [Pi.div_apply, zc]
      simp only [Matrix.cons_val]
      rw [hDg ω hω0]
      generalize (ω : ℂ) * I = s at hs hDn ⊢
      field_simp
    · simp
  · refine ((tendsto_const_nhds (x := -(p.A31 : ℂ))).div hDn0 one_ne_zero |>.congr' ?_).trans ?_
    · filter_upwards [ev] with ω hω
      obtain ⟨hω0, hDn⟩ := hω
      have hs : (ω : ℂ) * I ≠ 0 := mul_ne_zero hω0 I_ne_zero
      simp only [Pi.div_apply, zc]
      simp only [Matrix.cons_val]
      rw [hDg ω hω0]
      generalize (ω : ℂ) * I = s at hs hDn ⊢
      field_simp
    · simp

/-- The rows `ω_p → ∞` of the table: `z₁ = −1 + O(ω_p⁻¹)`, `z₂ = O(ω_p⁻¹)`, `z₃ = O(ω_p⁻¹)`,
`z₄ = O(ω_p⁻²)`. -/
@[tmio M, powerlib_domain] theorem zc_large_isBigO :
    (fun ω : ℝ => p.zc (ω * I) 0 + 1) =O[atTop] (fun ω => ω⁻¹) ∧
      (fun ω : ℝ => p.zc (ω * I) 1) =O[atTop] (fun ω => ω⁻¹) ∧
      (fun ω : ℝ => p.zc (ω * I) 2) =O[atTop] (fun ω => ω⁻¹) ∧
      (fun ω : ℝ => p.zc (ω * I) 3) =O[atTop] (fun ω => (ω ^ 2)⁻¹) := by
  obtain ⟨h1, h2, h3, h4⟩ := p.zc_large
  have ev : ∀ n : ℕ, ∀ᶠ ω : ℝ in atTop, ((ω : ℂ) * I) ^ n ≠ 0 ∧
      ‖(((ω : ℂ) * I) ^ n)⁻¹‖ = |(ω ^ n)⁻¹| := fun n => by
    filter_upwards [eventually_ne_atTop 0] with ω hω
    have hne : (ω : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) I_ne_zero
    refine ⟨pow_ne_zero n hne, ?_⟩
    rw [norm_inv, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_pow]
  refine ⟨isBigO_of_tendsto_mul (g := fun ω : ℝ => ((ω : ℂ) * I) ^ 1) (c := p.kp * p.vd0) ?_
      ((ev 1).mono fun ω h => by simpa using h),
    isBigO_of_tendsto_mul (g := fun ω : ℝ => ((ω : ℂ) * I) ^ 1) (c := p.vd0) ?_
      ((ev 1).mono fun ω h => by simpa using h),
    isBigO_of_tendsto_mul (g := fun ω : ℝ => ((ω : ℂ) * I) ^ 1) (c := -(p.A31 : ℂ)) ?_
      ((ev 1).mono fun ω h => by simpa using h),
    isBigO_of_tendsto_mul (g := fun ω : ℝ => ((ω : ℂ) * I) ^ 2) (c := -(p.A31 : ℂ)) ?_ (ev 2)⟩
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4

end Params
end powerlib.GFL.Parametric.AngleModulation
