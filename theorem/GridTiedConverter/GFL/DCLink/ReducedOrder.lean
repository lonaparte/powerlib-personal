import dependencies.Mathlib
import theorem.Passive.Series
import theorem.Passive.Parallel
import theorem.Dynamics.State
import theorem.SpecialFunctions.Sinusoid

/-! # GFL reduced-order models with DC link: algebra and model-B equilibria

Algebraic identities of the GFL reduced-order models and the equilibrium set of
model B.

Model boundary.
* L-filter closed loop in the PLL frame (§1.2.6): the frame rotates at the PLL speed `ω̂`, so the
  KVL cross-coupling is `ω̂ L_f i` and the decoupling uses `ω̂ L̂_f i`.
* Model B (§1.6–§1.7): continuous-time autonomous model on `State 4`, state order
  `x = (Δθ, x_pll, V_dc, ξ_v)`: PLL phase error `Δθ = θ̂ − θ_g` (swing sign, `conventions.md`
  §D5), PLL integrator, DC-link voltage, DC-voltage-loop integrator. Inner current loop eliminated
  (`i = i*`), reactive loop frozen (`i_q* = i_q0` constant), feed-forward LPF and decoupling
  mismatch removed (assumptions (S1)–(S3) of §1.2.9), `P_bridge` replaced by the PCC power,
  constant grid frequency `ω_g`, infinite bus `V_g` behind `Z_g = R_g + j X_g`, IN-positive
  currents. No saturation, no PWM, no delay. The field contains `1 / V_dc`; at `V_dc = 0` Lean's
  convention `1/0 = 0` applies, and only equilibrium-level statements are made here (no
  linearization, so global smoothness is not needed).

Source: work-sync `theory/T-gfl-reduced-order-dynamics.md` §1.1 (complex power), §1.2.6
(closed loop with feed-forward LPF and decoupling mismatch), §1.2.8 (d–q cancellation in
`P_bridge`, DAE → ODE), §1.6–§1.7 (model B and its steady state).

Results.
* Complex power from `S̄ = V̄ Ī*` (`conventions.md` §D0, IN-positive / absorb-positive):
  `P = (3/2)(v_d i_d + v_q i_q)`, `Q = (3/2)(v_q i_d − v_d i_q)` is
  `Transform.complexPower_expand` (`theorem/Transform/ComplexPower.lean`).
* `closedLoop_d`, `closedLoop_q`: in the PLL-frame model the residual of the decoupling is
  exactly `ω̂ ΔL_f i_q`, `ΔL_f = L_f − L̂_f`, with no locking assumption (Correction below).
* d–q duality: the decoupling terms of `bridgeVoltageD`, `bridgeVoltageQ` cancel exactly in the
  bridge power (`CurrentControl.bridgePower_decoupling`,
  `theorem/GridTiedConverter/CurrentControl/Decoupling.lean`).
* An explicit algebraic layer (index-1 DAE whose algebraic variables are given by a DAG of
  explicit formulas) has the same solutions as the ODE obtained by substitution: the generic
  statement is `DAE.isIntegralCurveOn_dae_iff` (`theorem/DAE/Elimination.lean`).
* Model B, necessary equilibrium conditions: `v_q = 0` (`equilibrium_vgq`),
  `ω_s − ω_g + k_i x_pll = 0` (`equilibrium_ki_xpll`), so `x_pll = (ω_g − ω_s)/k_i` for `k_i ≠ 0`
  (`equilibrium_xpll`); `V_dc = V_dc*` is `equilibrium_Vdc`
  (`theorem/GridTiedConverter/GFL/DCLink/ModelBStability.lean`).
* Model B with `R_g = 0`, `i_q0 = 0`: at an equilibrium `X_g i_d = −V_g sin Δθ`
  (`equilibrium_idRef`) and `I₀ V_dc* = (3 V_g² / (4 X_g)) sin 2Δθ`
  (`equilibrium_powerAngle`), so an equilibrium exists iff `|I₀| V_dc* ≤ 3 V_g² / (4 X_g)`
  (`ModelBParams.exists_equilibrium_iff`), and at the fold `|I₀| V_dc* = 3 V_g²/(4 X_g)` one has
  `|X_g i_d| = V_g / √2` (`fold_current`).

Family and connection conclusions.
This module states no behaviour and defines no family. The equilibrium results of model B
(`equilibrium_vgq`, `equilibrium_ki_xpll`, `equilibrium_xpll`, `equilibrium_idRef`,
`equilibrium_powerAngle`, `exists_equilibrium_iff`, `fold_current`) are
algebraic facts about the zero set of `ModelBParams.field`; they are static evidence on the model,
domain identities that do not require connection wrappers. The model-B family and its connection
conclusions (local stability through the Jacobian, 4×4 Routh–Hurwitz) are in
`theorem/GridTiedConverter/GFL/DCLink/ModelBStability.lean`.

Correction (§1.2.6): the note writes the residual as `(ω L_f − ω̂ L̂_f) i_q` and says it reduces
to `ω̂ ΔL_f i_q` only "when the PLL is locked (`ω̂ ≈ ω`)". In the PLL-frame model of §1.2.2
(whose cross term is `L_f ω̂ i_q`) the residual is exactly `ω̂ ΔL_f i_q`, `ΔL_f = L_f − L̂_f`,
with no locking assumption (`closedLoop_d`, `closedLoop_q`).

Correction (§1.7): the note's boundary `|X_g i_d*| ≤ V_g` is only the solvability of
`sin Δθ = −X_g i_d / V_g` for a *given* `i_d`; in model B `i_d` is fixed by the DC power balance,
the existence boundary is `|I₀| V_dc* = 3 V_g² / (4 X_g)`, and the fold sits at
`|X_g i_d| = V_g / √2`, not at `|X_g i_d| = V_g`.

Not formalized: model A (§1.4) contains the implicit loop `Q ↔ i_q* ↔ |v_g|` (a DAE) and is
excluded.
-/

noncomputable section
namespace powerlib.GFL.DCLink
open powerlib.Dynamics (State)

/-! ## Closed loop of the L filter (§1.2.6) -/

/-- d-axis bridge voltage command: PI + feed-forward + decoupling (IN-positive). -/
def bridgeVoltageD (kp ki ξd id idRef vffd ωhat Lhat iq : ℝ) : ℝ :=
  kp * (id - idRef) + ki * ξd + vffd + ωhat * Lhat * iq

/-- q-axis bridge voltage command. -/
def bridgeVoltageQ (kp ki ξq iq iqRef vffq ωhat Lhat id : ℝ) : ℝ :=
  kp * (iq - iqRef) + ki * ξq + vffq - ωhat * Lhat * id

/-- d-axis closed loop:
`L_f i̇_d = k_p(i_d* − i_d) − k_i ξ_d + (v_gd − ṽ_gd) + ω̂ ΔL_f i_q − R_f i_d` when the PLL-frame
KVL is `L_f i̇_d = v_gd − V_d^conv − R_f i_d + ω̂ L_f i_q`. -/
@[tmio M, powerlib_domain] theorem closedLoop_d (kp ki ξd id iq idRef vgd vffd ωhat Lf Lhat Rf : ℝ) :
    vgd - bridgeVoltageD kp ki ξd id idRef vffd ωhat Lhat iq - Rf * id + ωhat * Lf * iq =
      kp * (idRef - id) - ki * ξd + (vgd - vffd) + ωhat * (Lf - Lhat) * iq - Rf * id := by
  unfold bridgeVoltageD
  ring

/-- q-axis closed loop: residual `−ω̂ ΔL_f i_d`. -/
@[tmio M, powerlib_domain] theorem closedLoop_q (kp ki ξq id iq iqRef vgq vffq ωhat Lf Lhat Rf : ℝ) :
    vgq - bridgeVoltageQ kp ki ξq iq iqRef vffq ωhat Lhat id - Rf * iq - ωhat * Lf * id =
      kp * (iqRef - iq) - ki * ξq + (vgq - vffq) - ωhat * (Lf - Lhat) * id - Rf * iq := by
  unfold bridgeVoltageQ
  ring

/-! ## Model B (§1.6) -/

/-- Parameters of model B. -/
structure ModelBParams where
  /-- PLL nominal frequency `ω_s` and constant grid frequency `ω_g`. -/
  ωs : ℝ
  ωg : ℝ
  /-- PLL PI gains. -/
  kp : ℝ
  ki : ℝ
  /-- DC link (lossless shunt), upstream current injection, DC-voltage reference. -/
  dcLink : Passive.ParallelRLC
  I0 : ℝ
  VdcRef : ℝ
  /-- DC-voltage-loop PI gains. -/
  kpv : ℝ
  kiv : ℝ
  /-- Grid voltage and the grid line, a series RLC branch whose phasor impedance
  `Z_g = R_g + j X_g` is taken at the grid frequency `ω_g`. -/
  Vg : ℝ
  line : Passive.SeriesRLC
  /-- Frozen reactive current reference. -/
  iq0 : ℝ
  /-- The DC link is lossless. -/
  dcLink_lossless : dcLink.G = 0
  /-- The DC link has no shunt inductor. -/
  dcLink_noInd : dcLink.Γ = 0

/-- The DC-link capacitance. -/
abbrev ModelBParams.Cdc (p : ModelBParams) : ℝ := p.dcLink.C

/-- The line resistance `R_g`. -/
abbrev ModelBParams.Rg (p : ModelBParams) : ℝ := p.line.R

/-- The line reactance `X_g`. -/
abbrev ModelBParams.Xg (p : ModelBParams) : ℝ := p.line.reactance p.ωg

namespace ModelBParams

variable (p : ModelBParams)

/-- d-axis current reference `i_d* = k_pv (V_dc* − V_dc) + k_iv ξ_v`. -/
def idRef (Vdc ξv : ℝ) : ℝ := p.kpv * (p.VdcRef - Vdc) + p.kiv * ξv

/-- PCC voltage in the PLL frame, d component: `V_g cos Δθ − (R_g i_d − X_g i_q)`. -/
def vgd (Δθ id : ℝ) : ℝ := p.Vg * Real.cos Δθ - (p.Rg * id - p.Xg * p.iq0)

/-- PCC voltage in the PLL frame, q component: `−V_g sin Δθ − (X_g i_d + R_g i_q)`. -/
def vgq (Δθ id : ℝ) : ℝ := -p.Vg * Real.sin Δθ - (p.Xg * id + p.Rg * p.iq0)

/-- Model-B vector field on `x = (Δθ, x_pll, V_dc, ξ_v)`. -/
def field (x : State 4) : State 4 :=
  let id := p.idRef (x 2) (x 3)
  WithLp.toLp 2 ![p.ωs - p.ωg + p.kp * p.vgq (x 0) id + p.ki * x 1,
    p.vgq (x 0) id,
    (p.I0 + 3 * (p.vgd (x 0) id * id + p.vgq (x 0) id * p.iq0) / (2 * x 2)) / p.Cdc,
    p.VdcRef - x 2]

@[tmio M, powerlib_domain] theorem field_eq_zero_iff (x : State 4) :
    p.field x = 0 ↔
      p.ωs - p.ωg + p.kp * p.vgq (x 0) (p.idRef (x 2) (x 3)) + p.ki * x 1 = 0 ∧
      p.vgq (x 0) (p.idRef (x 2) (x 3)) = 0 ∧
      (p.I0 + 3 * (p.vgd (x 0) (p.idRef (x 2) (x 3)) * p.idRef (x 2) (x 3) +
          p.vgq (x 0) (p.idRef (x 2) (x 3)) * p.iq0) / (2 * x 2)) / p.Cdc = 0 ∧
      p.VdcRef - x 2 = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun y : State 4 => y 0) h
    have h1 := congrArg (fun y : State 4 => y 1) h
    have h2 := congrArg (fun y : State 4 => y 2) h
    have h3 := congrArg (fun y : State 4 => y 3) h
    simp [field] at h0 h1 h2 h3
    exact ⟨h0, h1, by simpa using h2, h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    ext i
    fin_cases i
    · simpa [field] using h0
    · simpa [field] using h1
    · simpa [field] using h2
    · simpa [field] using h3

/-- At an equilibrium the q-axis PCC voltage vanishes: `v_q = 0`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibrium_vgq {x : State 4} (hx : p.field x = 0) :
    p.vgq (x 0) (p.idRef (x 2) (x 3)) = 0 :=
  ((p.field_eq_zero_iff x).mp hx).2.1

/-- At an equilibrium the PLL integrator balances the frequency offset:
`ω_s − ω_g + k_i x_pll = 0` (any `k_i`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibrium_ki_xpll {x : State 4} (hx : p.field x = 0) :
    p.ωs - p.ωg + p.ki * x 1 = 0 := by
  obtain ⟨h0, h1, -, -⟩ := (p.field_eq_zero_iff x).mp hx
  rwa [h1, mul_zero, add_zero] at h0

/-- At an equilibrium (`k_i ≠ 0`) the PLL integrator state is `x_pll = (ω_g − ω_s)/k_i`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibrium_xpll (hki : p.ki ≠ 0) {x : State 4}
    (hx : p.field x = 0) : x 1 = (p.ωg - p.ωs) / p.ki := by
  have h0 := p.equilibrium_ki_xpll hx
  field_simp
  linarith

/-- With `R_g = 0` and `i_q0 = 0`, every equilibrium satisfies `X_g i_d = −V_g sin Δθ`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibrium_idRef (hR : p.Rg = 0) (hq : p.iq0 = 0)
    {x : State 4} (hx : p.field x = 0) :
    p.Xg * p.idRef (x 2) (x 3) = -p.Vg * Real.sin (x 0) := by
  have hvq := p.equilibrium_vgq hx
  simp only [vgq, hR, hq, mul_zero, add_zero] at hvq
  linarith

/-- With `R_g = 0` and `i_q0 = 0`, every equilibrium satisfies the power-angle relation
`I₀ V_dc* = (3 V_g² / (4 X_g)) sin 2Δθ` (`C_dc ≠ 0`, `V_dc* ≠ 0`, `X_g ≠ 0`;
`SpecialFunctions.mul_cos_mul_eq_neg_sin_two_mul`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibrium_powerAngle (hC : p.Cdc ≠ 0)
    (hV : p.VdcRef ≠ 0) (hX : p.Xg ≠ 0) (hR : p.Rg = 0) (hq : p.iq0 = 0) {x : State 4}
    (hx : p.field x = 0) :
    p.I0 * p.VdcRef = 3 * p.Vg ^ 2 / (4 * p.Xg) * Real.sin (2 * x 0) := by
  obtain ⟨-, -, h2, h3⟩ := (p.field_eq_zero_iff x).mp hx
  have hVdc : x 2 = p.VdcRef := by linarith
  have hid := p.equilibrium_idRef hR hq hx
  have h2' := (div_eq_zero_iff.mp h2).resolve_right hC
  simp only [vgd, hR, hq, zero_mul, mul_zero, sub_zero, add_zero] at h2'
  have hP := SpecialFunctions.mul_cos_mul_eq_neg_sin_two_mul (V := p.Vg) (θ := x 0)
    (i := p.idRef (x 2) (x 3)) hX (by rw [hid]; ring)
  have hV2 : x 2 ≠ 0 := by rw [hVdc]; exact hV
  have h2'' : p.I0 * x 2 + 3 / 2 * (p.Vg * Real.cos (x 0) * p.idRef (x 2) (x 3)) = 0 := by
    field_simp at h2'
    linarith
  rw [← hVdc]
  linear_combination h2'' - 3 / 2 * hP

/-- Existence of an equilibrium of model B (`R_g = 0`, `i_q0 = 0`, `X_g > 0`, `V_dc* > 0`,
`V_g ≠ 0`, nonzero `C_dc`, `k_i`, `k_iv`): iff `|I₀| V_dc* ≤ 3 V_g² / (4 X_g)` (the power-angle
law `SpecialFunctions.exists_mul_sin_two_mul_eq_iff`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem exists_equilibrium_iff (hki : p.ki ≠ 0) (hkiv : p.kiv ≠ 0)
    (hC : p.Cdc ≠ 0) (hV : 0 < p.VdcRef) (hX : 0 < p.Xg) (hVg : p.Vg ≠ 0) (hR : p.Rg = 0)
    (hq : p.iq0 = 0) :
    (∃ x, p.field x = 0) ↔ |p.I0| * p.VdcRef ≤ 3 * p.Vg ^ 2 / (4 * p.Xg) := by
  have hK : 0 < 3 * p.Vg ^ 2 / (4 * p.Xg) := by positivity
  rw [← abs_of_pos hV, ← abs_mul, ← SpecialFunctions.exists_mul_sin_two_mul_eq_iff hK]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x 0, (p.equilibrium_powerAngle hC hV.ne' hX.ne' hR hq hx).symm⟩
  · rintro ⟨Δθ, hK2⟩
    set K := 3 * p.Vg ^ 2 / (4 * p.Xg) with hKdef
    set s := p.I0 * p.VdcRef / K with hs
    have hsin2 : Real.sin (2 * Δθ) = s := by
      rw [hs, eq_div_iff hK.ne']
      linarith
    set id := -p.Vg * Real.sin Δθ / p.Xg with hid
    refine ⟨WithLp.toLp 2 ![Δθ, (p.ωg - p.ωs) / p.ki, p.VdcRef, id / p.kiv], ?_⟩
    have hidRef : p.idRef p.VdcRef (id / p.kiv) = id := by
      simp only [idRef, sub_self, mul_zero, zero_add]
      field_simp
    have hvq : p.vgq Δθ id = 0 := by
      simp only [vgq, hR, hq, mul_zero, add_zero, hid]
      field_simp
      ring
    rw [field_eq_zero_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    rw [hidRef, hvq]
    refine ⟨?_, rfl, ?_, sub_self _⟩
    · field_simp
      ring
    · simp only [vgd, hR, hq, zero_mul, mul_zero, sub_zero, add_zero]
      have hsin2' := hsin2
      rw [Real.sin_two_mul, hs, hKdef] at hsin2'
      rw [div_eq_zero_iff]
      left
      rw [hid]
      field_simp at hsin2' ⊢
      linear_combination (-1 / 2 : ℝ) * hsin2'

/-- Fold of model B (`R_g = 0`, `i_q0 = 0`): at an equilibrium on the existence boundary
`|I₀| V_dc* = 3 V_g² / (4 X_g)` the d-axis current satisfies `|X_g i_d| = |V_g| / √2`
(`|sin 2Δθ| = 1`, `SpecialFunctions.sin_sq_eq_half_of_abs_sin_two_mul`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fold_current (hC : p.Cdc ≠ 0) (hV : 0 < p.VdcRef)
    (hX : 0 < p.Xg) (hVg : p.Vg ≠ 0) (hR : p.Rg = 0) (hq : p.iq0 = 0) {x : State 4}
    (hx : p.field x = 0) (hfold : |p.I0| * p.VdcRef = 3 * p.Vg ^ 2 / (4 * p.Xg)) :
    |p.Xg * p.idRef (x 2) (x 3)| = |p.Vg| / Real.sqrt 2 := by
  have hpa := p.equilibrium_powerAngle hC hV.ne' hX.ne' hR hq hx
  have hid := p.equilibrium_idRef hR hq hx
  have hK : 0 < 3 * p.Vg ^ 2 / (4 * p.Xg) := by positivity
  have habs : |Real.sin (2 * x 0)| = 1 := by
    have h1 : |p.I0 * p.VdcRef| = 3 * p.Vg ^ 2 / (4 * p.Xg) * |Real.sin (2 * x 0)| := by
      rw [hpa, abs_mul, abs_of_pos hK]
    rw [abs_mul, abs_of_pos hV, hfold] at h1
    have h3 : 3 * p.Vg ^ 2 / (4 * p.Xg) * (|Real.sin (2 * x 0)| - 1) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hK.ne'
    · linarith
  have hsin := SpecialFunctions.sin_sq_eq_half_of_abs_sin_two_mul habs
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  rw [hid]
  have e1 : |-p.Vg * Real.sin (x 0)| ^ 2 = (|p.Vg| / Real.sqrt 2) ^ 2 := by
    rw [sq_abs, div_pow, sq_abs, hs2]
    rw [mul_pow, hsin]
    ring
  exact (sq_eq_sq₀ (abs_nonneg _) (by positivity)).mp e1

end ModelBParams

end powerlib.GFL.DCLink
