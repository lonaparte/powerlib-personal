import theorem.GFL.RatePLL
import theorem.GFL.DCLink.FourState
import theorem.Transform.ComplexPower

/-! # Model layers of the GFL carrier: algebraic loops, exact cancellations, convention invariance

Foundation module: algebraic identities about the model layers of the GFL side of
`gfl-gfm-stability-tree`. Each layer is written as its defining relations (KVL of filter and line
in the PLL frame, current loop, PLL, dc balance); the statements solve those relations exactly.
No time-scale (Tikhonov) or convergence statement is made: the note's numerical claims
("`ω_cc → ∞` second-order convergence", "8 states collapse to 4 to `10⁻⁵ %`") are not formalized.

Model boundary.
Common to every layer: single GFL converter, infinite bus `v_g = (V_g cos θ, −V_g sin θ)` in the PLL
frame (`θ` = PLL error angle), frame speed `ω₁ = ω₀ + u`, SRF-PLL `u = k_p v_q + k_i x`,
`J i = (−i_q, i_d)`, averaged model, continuous time, no PWM / delay / limiter.

Source: work-sync `projects/gfl-gfm-stability-tree/notes/concepts/model-layers.md`
(I1 放开一级: 6 态与 `L_g u I_d` 的真身, 性质 3; `R_g` 在 GFL 侧 (2 态载体); 目标载体的推导:
两个代数环与 `i_q ≠ 0` 的补项; `D₁` 的方向约定); `projects/vsc-parametric-oscillation/references/
gfm-driven-gfl-parametric-resonance/notes/concepts/gfl-four-state-parametric-resonance.md`
(`P_abs`, `Q_abs`); code reference `simulation/src/.../models_extended.py`.

Results.
* Six-state carrier (`CCParams`, `GFLRateCC` with `R_f = R_g = 0`; states
  `(θ, x, i_d, i_q, ξ_d, ξ_q)`, OUT-positive current): L filter `L_f i̇ = e − v − ω₁ L_f J i`,
  line `v = v_g + ω₁ L_g J i + L_g i̇`, current loop with ideal PCC feed-forward and nominal
  decoupling `e = v + PI + ω₀ L_f J i`. `speedEMF_cancel`, `loopRel_iff`: the speed EMF
  `(ω₀ + u) L_g i_d` and the part `−u L_g i_d` of `L_g i̇_q` cancel exactly, so
  `v_q = −V_g sin θ + X_g i_d + (L_g/L_f) PI_q` (`X_g = ω₀ L_g`) and the algebraic loop has a
  unique explicit solution. `ccField_bwTuned_indep_Lf`: with `k_p^cc = 2ζ_c ω_cc L_f`,
  `k_i^cc = ω_cc² L_f` the closed-loop six-state field does not depend on `L_f`.
* Two-state rate carrier with line resistance (`RateRel`, extends `GFL.RatePLL`,
  frozen `I_d`, constant `i_q`): `rateRel_iff` — the `D₀` loop factor `1 − k_p L_g I_d` contains
  neither `R_g` nor `i_q`; `rateRel_iq_zero_iff` — at `i_q = 0` the solution is exactly that of
  the `R_g`-free model for every `R_g` (exact insensitivity, not small sensitivity).
* Four-state dc carrier (`DCParams`, `GFLDCFormC`; states `(θ, x, V_dc, η)`, ideal current loop
  `i = i*`, `i_d* = i_{d0} + s_K (k_pv (V − 1) + k_iv η)`, constant `i_q`, constant-current dc
  source `C V̇ = I_src + s_P P / V`, `P = (3/2)(v_d i_d + v_q i_q)` from `S̄ = V̄ Ī*`). The line
  keeps `L_g i̇_d` and the speed EMF. `rel_iff`: the relations are solved sequentially — first the
  PLL loop `D₀ = 1 − k_p s_L L_g i_d`, then the dc loop
  `D₁ = 1 − s_K s_P s_L (3/2) k_pv L_g i_d/(C V)`; `i_q` enters neither loop factor (`D1_indep_iq`).
  `coordField` / `field` is the resulting four-state field.
* Direction convention: OUT-positive writing `s_L = 1, s_P = −1, s_K = 1` (`outConv`); the
  complete §D8 translation negates both currents and all three flags (`inConv`).
  `loopFactor_flip_all`, `D1_inConv`: `D₁` is invariant; `field_inConv`, `fderiv_field_inConv`:
  the reduced four-state field — none of whose states is a current — is the same function in
  both conventions, so the Jacobians agree entry by entry; `D1_currentOnly`: translating only
  the current gives `2 − D₁`.
* Four-state model of `theorem/GFL/DCLink/FourState.lean`: `fourState_power`: `P_abs`, `Q_abs` are
  `(3/2) Re / Im (V̄ Ī*)` with `V̄ = v_d + j v_q`, `Ī = i_d + j 0` (IN-positive).

Family and connection conclusions.
No family and no connection conclusion: the module solves
algebraic loop relations and proves field identities; it states no behaviour. The behavioural
conclusions about the rate-coupled carrier and the four-state model are made through
`RatePLL.family` and `FourState.family`.
-/

noncomputable section
namespace powerlib.GFL.ModelLayers
open powerlib.GFL.DCLink
open Real

/-! ## Six-state carrier: L filter + current loop + PLL (`R_f = R_g = 0`) -/

/-- Parameters of the six-state carrier (`GFLRateCC` with `R_f = R_g = 0`). -/
structure CCParams where
  /-- grid amplitude -/
  Vg : ℝ
  /-- nominal angular frequency -/
  ω0 : ℝ
  /-- filter inductance -/
  Lf : ℝ
  /-- line inductance -/
  Lg : ℝ
  /-- current-loop proportional gain -/
  kpcc : ℝ
  /-- current-loop integral gain -/
  kicc : ℝ
  /-- PLL proportional gain -/
  kp : ℝ
  /-- PLL integral gain -/
  ki : ℝ
  /-- d-axis current reference -/
  idRef : ℝ
  /-- q-axis current reference -/
  iqRef : ℝ

namespace CCParams
variable (q : CCParams)

/-- PI part of the d-axis current-loop output. -/
def piD (id ξd : ℝ) : ℝ := q.kpcc * (q.idRef - id) + q.kicc * ξd

/-- PI part of the q-axis current-loop output. -/
def piQ (iq ξq : ℝ) : ℝ := q.kpcc * (q.iqRef - iq) + q.kicc * ξq

/-- Algebraic relations of the six-state carrier at the state `(θ, x, i_d, i_q, ξ_d, ξ_q)`, with
unknowns `v` (PCC voltage), `e` (converter voltage), `i̇` and the PLL output `u`:
filter `L_f i̇ = e − v − ω₁ L_f J i`, line `v = v_g + ω₁ L_g J i + L_g i̇`, current loop
`e = v + PI + ω₀ L_f J i`, PLL `u = k_p v_q + k_i x`, `ω₁ = ω₀ + u`, `J i = (−i_q, i_d)`,
`v_g = (V_g cos θ, −V_g sin θ)`. -/
def LoopRel (θ x id iq ξd ξq vd vq ed eq did diq u : ℝ) : Prop :=
  q.Lf * did = ed - vd + (q.ω0 + u) * q.Lf * iq ∧
  q.Lf * diq = eq - vq - (q.ω0 + u) * q.Lf * id ∧
  vd = q.Vg * cos θ - (q.ω0 + u) * q.Lg * iq + q.Lg * did ∧
  vq = -q.Vg * sin θ + (q.ω0 + u) * q.Lg * id + q.Lg * diq ∧
  ed = vd + q.piD id ξd - q.ω0 * q.Lf * iq ∧
  eq = vq + q.piQ iq ξq + q.ω0 * q.Lf * id ∧
  u = q.kp * vq + q.ki * x

/-- Explicit q-axis PCC voltage `−V_g sin θ + X_g i_d + (L_g/L_f) PI_q`, `X_g = ω₀ L_g`. -/
def vqSol (θ id iq ξq : ℝ) : ℝ := -q.Vg * sin θ + q.ω0 * q.Lg * id + q.Lg / q.Lf * q.piQ iq ξq

/-- Explicit d-axis PCC voltage `V_g cos θ − X_g i_q + (L_g/L_f) PI_d`. -/
def vdSol (θ id iq ξd : ℝ) : ℝ := q.Vg * cos θ - q.ω0 * q.Lg * iq + q.Lg / q.Lf * q.piD id ξd

/-- Explicit PLL output. -/
def uSol (θ x id iq ξq : ℝ) : ℝ := q.kp * q.vqSol θ id iq ξq + q.ki * x

/-- The speed EMF `(ω₀ + u) L_g i_d` and the slip part `−u L_g i_d` of `L_g i̇_q` cancel. -/
@[powerlib_foundation] theorem speedEMF_cancel (hLf : q.Lf ≠ 0) (θ id iq ξq u : ℝ) :
    -q.Vg * sin θ + (q.ω0 + u) * q.Lg * id + q.Lg * (q.piQ iq ξq / q.Lf - u * id) =
      q.vqSol θ id iq ξq := by
  unfold vqSol
  field_simp
  ring

/-- The algebraic loop of the six-state carrier has the unique explicit solution: `v_q` does
not contain `u` (speed-EMF cancellation), so `u` follows without any `D₀` factor. -/
@[powerlib_foundation] theorem loopRel_iff (hLf : q.Lf ≠ 0)
    (θ x id iq ξd ξq vd vq ed eq did diq u : ℝ) :
    q.LoopRel θ x id iq ξd ξq vd vq ed eq did diq u ↔
      u = q.uSol θ x id iq ξq ∧ vq = q.vqSol θ id iq ξq ∧ vd = q.vdSol θ id iq ξd ∧
      did = q.piD id ξd / q.Lf + u * iq ∧ diq = q.piQ iq ξq / q.Lf - u * id ∧
      ed = vd + q.piD id ξd - q.ω0 * q.Lf * iq ∧ eq = vq + q.piQ iq ξq + q.ω0 * q.Lf * id := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have hdid : did = q.piD id ξd / q.Lf + u * iq := by
      field_simp
      rw [h5] at h1
      linear_combination h1
    have hdiq : diq = q.piQ iq ξq / q.Lf - u * id := by
      field_simp
      rw [h6] at h2
      linear_combination h2
    have hvq : vq = q.vqSol θ id iq ξq := by
      rw [h4, hdiq, q.speedEMF_cancel hLf]
    have hvd : vd = q.vdSol θ id iq ξd := by
      rw [h3, hdid]
      unfold vdSol
      field_simp
      ring
    refine ⟨?_, hvq, hvd, hdid, hdiq, h5, h6⟩
    rw [h7, hvq]
    rfl
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨?_, ?_, ?_, ?_, h6, h7, ?_⟩
    · rw [h4, h6]; field_simp; ring
    · rw [h5, h7]; field_simp; ring
    · rw [h3, h4]; unfold vdSol; field_simp; ring
    · rw [h2, h5, q.speedEMF_cancel hLf]
    · rw [h1, h2]; rfl

/-- Six-state field, coordinates `(θ, x, i_d, i_q, ξ_d, ξ_q)`, from the explicit loop solution. -/
def ccField (y : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![q.uSol (y 0) (y 1) (y 2) (y 3) (y 5), q.vqSol (y 0) (y 2) (y 3) (y 5),
    q.piD (y 2) (y 4) / q.Lf + q.uSol (y 0) (y 1) (y 2) (y 3) (y 5) * y 3,
    q.piQ (y 3) (y 5) / q.Lf - q.uSol (y 0) (y 1) (y 2) (y 3) (y 5) * y 2,
    q.idRef - y 2, q.iqRef - y 3]

/-- The field rows are the derivatives determined by the loop relations. -/
@[powerlib_foundation] theorem ccField_spec (hLf : q.Lf ≠ 0) (y : Fin 6 → ℝ) :
    ∃ vd ed eq, q.LoopRel (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) vd (q.ccField y 1) ed eq
      (q.ccField y 2) (q.ccField y 3) (q.ccField y 0) := by
  refine ⟨q.vdSol (y 0) (y 2) (y 3) (y 4),
    q.vdSol (y 0) (y 2) (y 3) (y 4) + q.piD (y 2) (y 4) - q.ω0 * q.Lf * y 3,
    q.vqSol (y 0) (y 2) (y 3) (y 5) + q.piQ (y 3) (y 5) + q.ω0 * q.Lf * y 2, ?_⟩
  rw [q.loopRel_iff hLf]
  simp [ccField]

/-- Bandwidth-normalized current-loop tuning `k_p^cc = 2ζ_c ω_cc L_f`, `k_i^cc = ω_cc² L_f`. -/
def bwTuned (ζc ωcc : ℝ) : CCParams :=
  { q with kpcc := 2 * ζc * ωcc * q.Lf, kicc := ωcc ^ 2 * q.Lf }

/-- Under bandwidth-normalized tuning the closed-loop six-state field does not depend on `L_f`
(`L_f ≠ 0`): the stability parameters are `ω_cc, ζ_c`, not `L_f`. -/
@[powerlib_foundation] theorem ccField_bwTuned_indep_Lf (ζc ωcc L L' : ℝ) (hL : L ≠ 0)
    (hL' : L' ≠ 0) :
    (({ q with Lf := L } : CCParams).bwTuned ζc ωcc).ccField =
      (({ q with Lf := L' } : CCParams).bwTuned ζc ωcc).ccField := by
  funext y
  simp only [ccField, bwTuned, uSol, vqSol, piD, piQ]
  have e1 : ∀ a b : ℝ, (2 * ζc * ωcc * L * a + ωcc ^ 2 * L * b) / L =
      (2 * ζc * ωcc * L' * a + ωcc ^ 2 * L' * b) / L' := fun a b => by
    field_simp
  have e2 : ∀ a b : ℝ, q.Lg / L * (2 * ζc * ωcc * L * a + ωcc ^ 2 * L * b) =
      q.Lg / L' * (2 * ζc * ωcc * L' * a + ωcc ^ 2 * L' * b) := fun a b => by
    field_simp
  rw [e1, e1, e2]

end CCParams

/-! ## Two-state rate carrier with line resistance -/

/-- Loop relation of the rate-coupled two-state carrier with line resistance `R_g` and a constant
q-axis current `i_q` (`L_g i̇_q = 0`): `v_q = −V sin θ + R_g i_q + X_g I_d + L_g u I_d`,
`u = k_p v_q + k_i x` (OUT-positive, as `GFL.RatePLL`). -/
def RateRel (p : RatePLL.Params) (Rg iq θ x vq u : ℝ) : Prop :=
  vq = -p.V * sin θ + Rg * iq + p.Xg * p.Id + p.Lg * u * p.Id ∧ u = p.kp * vq + p.ki * x

/-- Solution of the `D₀` loop with `R_g`, `i_q`: `D₀ u = k_p(−V sin θ + R_g i_q + X_g I_d) + k_i x`;
`D₀ = 1 − k_p L_g I_d` contains neither `R_g` nor `i_q`. -/
@[powerlib_foundation] theorem rateRel_iff (p : RatePLL.Params) (hD0 : p.D0 ≠ 0)
    (Rg iq θ x vq u : ℝ) :
    RateRel p Rg iq θ x vq u ↔
      u = (p.kp * (RatePLL.gridQ p θ + Rg * iq) + p.ki * x) / p.D0 ∧
        vq = RatePLL.gridQ p θ + Rg * iq + p.Lg * u * p.Id := by
  have hD : p.D0 = 1 - p.kp * p.Lg * p.Id := rfl
  unfold RateRel RatePLL.gridQ
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by rw [h1]; ring⟩
    rw [eq_div_iff hD0, hD]
    rw [h1] at h2
    linear_combination h2
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h2]; ring, ?_⟩
    rw [h2]
    field_simp at h1
    rw [hD] at h1
    linear_combination h1

/-- At `i_q = 0` the carrier is exactly insensitive to `R_g`: for every `R_g` the loop solution is
the one of the `R_g`-free model `RatePLL` (`θ̇ = pllOut`, `v_q = RatePLL.vq`). -/
@[powerlib_foundation] theorem rateRel_iq_zero_iff (p : RatePLL.Params) (hD0 : p.D0 ≠ 0)
    (Rg θ x vq u : ℝ) :
    RateRel p Rg 0 θ x vq u ↔ u = RatePLL.pllOut p θ x ∧ vq = RatePLL.vq p θ x := by
  rw [rateRel_iff p hD0]
  simp only [mul_zero, add_zero, RatePLL.pllOut, RatePLL.vq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2, h1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2, h1]⟩

/-! ## Four-state dc carrier with ideal current loop: the `D₀` and `D₁` loops -/

/-- The general sign-flag form of the dc loop factor,
`D₁ = 1 − s_K s_P s_L (3/2) k_pv L_g i_d / (C V)`. -/
def loopFactor (sL sP sK kpv Lg C V id : ℝ) : ℝ := 1 - sK * sP * sL * (3 / 2 * kpv * Lg * id) / (C * V)

/-- Flipping all four signs (`i_d`, `s_L`, `s_P`, `s_K`) leaves `D₁` unchanged. -/
@[powerlib_foundation] theorem loopFactor_flip_all (sL sP sK kpv Lg C V id : ℝ) :
    loopFactor (-sL) (-sP) (-sK) kpv Lg C V (-id) = loopFactor sL sP sK kpv Lg C V id := by
  unfold loopFactor; ring

/-- Flipping only the current gives `2 − D₁`. -/
@[powerlib_foundation] theorem loopFactor_flip_current (sL sP sK kpv Lg C V id : ℝ) :
    loopFactor sL sP sK kpv Lg C V (-id) = 2 - loopFactor sL sP sK kpv Lg C V id := by
  unfold loopFactor; ring

/-- Parameters of the four-state dc carrier (`GFLDCFormC`), written in a direction convention
given by three sign flags: `s_L` (sign of the line-impedance drop in `v`), `s_P` (sign of the
port power in the dc balance), `s_K` (sign of `∂i_d*/∂V_dc`). Currents are in the same
convention. -/
structure DCParams where
  /-- grid amplitude -/
  Vg : ℝ
  /-- nominal angular frequency -/
  ω0 : ℝ
  /-- line inductance -/
  Lg : ℝ
  /-- line resistance -/
  Rg : ℝ
  /-- dc capacitance -/
  C : ℝ
  /-- dc source current -/
  Isrc : ℝ
  /-- PLL gains -/
  kp : ℝ
  ki : ℝ
  /-- dc-voltage PI gains -/
  kpv : ℝ
  kiv : ℝ
  /-- d-axis current offset and constant q-axis current (in the convention's direction) -/
  id0 : ℝ
  iq : ℝ
  /-- sign flags -/
  sL : ℝ
  sP : ℝ
  sK : ℝ

namespace DCParams
variable (d : DCParams)

/-- d-axis current command `i_d = i_{d0} + s_K (k_pv (V − 1) + k_iv η)` (ideal current loop). -/
def idRef (V η : ℝ) : ℝ := d.id0 + d.sK * (d.kpv * (V - 1) + d.kiv * η)

/-- Algebraic relations at the state `(θ, x, V, η)`; unknowns `u, v_d, v_q, P, V̇, i̇_d`:
`u = k_p v_q + k_i x`, `v_q = −V_g sin θ + s_L (R_g i_q + (ω₀ + u) L_g i_d)` (`i̇_q = 0`),
`v_d = V_g cos θ + s_L (R_g i_d − (ω₀ + u) L_g i_q + L_g i̇_d)`, `P = (3/2)(v_d i_d + v_q i_q)`,
`C V̇ = I_src + s_P P / V`, `i̇_d = s_K (k_pv V̇ + k_iv (V − 1))`. -/
def Rel (θ x V η u vd vq P Vd did : ℝ) : Prop :=
  u = d.kp * vq + d.ki * x ∧
  vq = -d.Vg * sin θ + d.sL * (d.Rg * d.iq + (d.ω0 + u) * d.Lg * d.idRef V η) ∧
  vd = d.Vg * cos θ + d.sL * (d.Rg * d.idRef V η - (d.ω0 + u) * d.Lg * d.iq + d.Lg * did) ∧
  P = 3 / 2 * (vd * d.idRef V η + vq * d.iq) ∧
  d.C * Vd = d.Isrc + d.sP * P / V ∧
  did = d.sK * (d.kpv * Vd + d.kiv * (V - 1))

/-- PLL loop factor `D₀ = 1 − k_p s_L L_g i_d`. -/
def D0 (V η : ℝ) : ℝ := 1 - d.kp * d.sL * d.Lg * d.idRef V η

/-- dc loop factor `D₁ = 1 − s_K s_P s_L (3/2) k_pv L_g i_d / (C V)`. -/
def D1 (V η : ℝ) : ℝ := loopFactor d.sL d.sP d.sK d.kpv d.Lg d.C V (d.idRef V η)

/-- Loop 1: PLL output. -/
def uSol (θ x V η : ℝ) : ℝ :=
  (d.kp * (-d.Vg * sin θ + d.sL * (d.Rg * d.iq + d.ω0 * d.Lg * d.idRef V η)) + d.ki * x) /
    d.D0 V η

/-- q-axis PCC voltage. -/
def vqSol (θ x V η : ℝ) : ℝ :=
  -d.Vg * sin θ + d.sL * (d.Rg * d.iq + (d.ω0 + d.uSol θ x V η) * d.Lg * d.idRef V η)

/-- Static part of `v_d` (without `L_g i̇_d`). -/
def vdStat (θ x V η : ℝ) : ℝ :=
  d.Vg * cos θ + d.sL * (d.Rg * d.idRef V η - (d.ω0 + d.uSol θ x V η) * d.Lg * d.iq)

/-- Static part of the port power. -/
def PStat (θ x V η : ℝ) : ℝ := 3 / 2 * (d.vdStat θ x V η * d.idRef V η + d.vqSol θ x V η * d.iq)

/-- Loop 2: `i̇_d`. -/
def didSol (θ x V η : ℝ) : ℝ :=
  d.sK * (d.kpv * (d.Isrc + d.sP * d.PStat θ x V η / V) / d.C + d.kiv * (V - 1)) / d.D1 V η

/-- `V̇`. -/
def VdSol (θ x V η : ℝ) : ℝ :=
  (d.Isrc + d.sP * (d.PStat θ x V η + 3 / 2 * d.sL * d.Lg * d.didSol θ x V η * d.idRef V η) / V) /
    d.C

/-- The two algebraic loops are solved sequentially: first `D₀` gives `u`, then `D₁` gives
`i̇_d`; `i_q` enters neither loop factor. -/
@[powerlib_foundation] theorem rel_iff (θ x V η : ℝ) (hD0 : d.D0 V η ≠ 0) (hD1 : d.D1 V η ≠ 0)
    (hV : V ≠ 0) (hC : d.C ≠ 0) (u vd vq P Vd did : ℝ) :
    d.Rel θ x V η u vd vq P Vd did ↔
      u = d.uSol θ x V η ∧ vq = d.vqSol θ x V η ∧ did = d.didSol θ x V η ∧
        vd = d.vdStat θ x V η + d.sL * d.Lg * did ∧
        P = d.PStat θ x V η + 3 / 2 * d.sL * d.Lg * did * d.idRef V η ∧ Vd = d.VdSol θ x V η := by
  have hD0' : d.D0 V η = 1 - d.kp * d.sL * d.Lg * d.idRef V η := rfl
  have hD1' : d.D1 V η = 1 - d.sK * d.sP * d.sL * (3 / 2 * d.kpv * d.Lg * d.idRef V η) / (d.C * V) :=
    rfl
  have hu_iff : ∀ vq', (u = d.kp * vq' + d.ki * x ∧ vq' = -d.Vg * sin θ +
      d.sL * (d.Rg * d.iq + (d.ω0 + u) * d.Lg * d.idRef V η)) ↔
      (u = d.uSol θ x V η ∧ vq' = d.vqSol θ x V η) := by
    intro vq'
    constructor
    · rintro ⟨h1, h2⟩
      have hu : u = d.uSol θ x V η := by
        unfold uSol
        rw [eq_div_iff hD0, hD0']
        rw [h2] at h1
        linear_combination h1
      exact ⟨hu, by rw [h2, hu]; rfl⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, by rw [h2, h1]; rfl⟩
      rw [h2, h1]
      unfold vqSol uSol
      field_simp
      rw [hD0']
      ring
  have hX : d.didSol θ x V η * d.D1 V η =
      d.sK * (d.kpv * (d.Isrc + d.sP * d.PStat θ x V η / V) / d.C + d.kiv * (V - 1)) := by
    unfold didSol
    exact div_mul_cancel₀ _ hD1
  rw [hD1'] at hX
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    obtain ⟨hu, hvq⟩ := (hu_iff vq).1 ⟨h1, h2⟩
    have hvd : vd = d.vdStat θ x V η + d.sL * d.Lg * did := by
      rw [h3, hu]; unfold vdStat; ring
    have hP : P = d.PStat θ x V η + 3 / 2 * d.sL * d.Lg * did * d.idRef V η := by
      rw [h4, hvd, hvq]; unfold PStat; ring
    have hVd : Vd = (d.Isrc + d.sP * P / V) / d.C := by
      rw [eq_div_iff hC]; linear_combination h5
    have hdid : did = d.didSol θ x V η := by
      unfold didSol
      rw [eq_div_iff hD1, hD1']
      rw [hVd, hP] at h6
      field_simp at h6 ⊢
      linear_combination h6
    refine ⟨hu, hvq, hdid, hvd, hP, ?_⟩
    rw [hVd, hP, hdid]
    rfl
  · rintro ⟨hu, hvq, hdid, hvd, hP, hVd⟩
    obtain ⟨h1, h2⟩ := (hu_iff vq).2 ⟨hu, hvq⟩
    refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
    · rw [hvd, hu]; unfold vdStat; ring
    · rw [hP, hvd, hvq]; unfold PStat; ring
    · rw [hVd, hP, hdid]; unfold VdSol; field_simp
    · rw [hVd, hdid]
      unfold VdSol
      field_simp at hX ⊢
      linear_combination hX

/-- Four-state coordinate field `(θ, x, V, η) ↦ (u, v_q, V̇, V − 1)` from the sequential solution
of the two loops (ideal current loop, constant `i_q`). -/
def coordField (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![d.uSol (y 0) (y 1) (y 2) (y 3), d.vqSol (y 0) (y 1) (y 2) (y 3),
    d.VdSol (y 0) (y 1) (y 2) (y 3), y 2 - 1]

/-- The four-state field on `Dynamics.State 4`. -/
def field : Dynamics.State 4 → Dynamics.State 4 := Dynamics.lift d.coordField

/-- The rows of `coordField` solve the loop relations (where `D₀, D₁, V, C ≠ 0`). -/
@[powerlib_foundation] theorem coordField_spec (y : Fin 4 → ℝ) (hD0 : d.D0 (y 2) (y 3) ≠ 0)
    (hD1 : d.D1 (y 2) (y 3) ≠ 0) (hV : y 2 ≠ 0) (hC : d.C ≠ 0) :
    ∃ vd P did, d.Rel (y 0) (y 1) (y 2) (y 3) (d.coordField y 0) vd (d.coordField y 1) P
      (d.coordField y 2) did := by
  refine ⟨d.vdStat (y 0) (y 1) (y 2) (y 3) + d.sL * d.Lg * d.didSol (y 0) (y 1) (y 2) (y 3),
    d.PStat (y 0) (y 1) (y 2) (y 3) +
      3 / 2 * d.sL * d.Lg * d.didSol (y 0) (y 1) (y 2) (y 3) * d.idRef (y 2) (y 3),
    d.didSol (y 0) (y 1) (y 2) (y 3), ?_⟩
  rw [d.rel_iff _ _ _ _ hD0 hD1 hV hC]
  simp [coordField]

/-! ### Direction convention: `D₁` is invariant -/

/-- OUT-positive writing (the source project): `s_L = 1`, `s_P = −1`, `s_K = 1`. -/
def outConv : DCParams := { d with sL := 1, sP := -1, sK := 1 }

/-- Complete translation to IN-positive (`conventions.md` §D8): both currents negated and all
three flags flipped, `s_L = −1`, `s_P = 1`, `s_K = −1`. -/
def inConv : DCParams := { d with id0 := -d.id0, iq := -d.iq, sL := -1, sP := 1, sK := -1 }


@[powerlib_foundation] theorem idRef_inConv (V η : ℝ) :
    d.inConv.idRef V η = -d.outConv.idRef V η := by
  simp [idRef, inConv, outConv]; ring

@[powerlib_foundation] theorem D0_inConv (V η : ℝ) : d.inConv.D0 V η = d.outConv.D0 V η := by
  simp only [D0, idRef_inConv]; simp [inConv, outConv]

/-- `D₁` is a direction-convention invariant: the complete translation gives the same `D₁`. -/
@[powerlib_foundation] theorem D1_inConv (V η : ℝ) : d.inConv.D1 V η = d.outConv.D1 V η := by
  simp only [D1, idRef_inConv]
  rw [← loopFactor_flip_all]
  simp [inConv, outConv]

/-- With the OUT-positive flags, evaluating `D₁` at the negated current (translating only the
current) gives `2 − D₁`, which is `< 1` whenever the true `D₁ > 1`. -/
@[powerlib_foundation] theorem D1_currentOnly (V id : ℝ) :
    loopFactor 1 (-1) 1 d.kpv d.Lg d.C V (-id) = 2 - loopFactor 1 (-1) 1 d.kpv d.Lg d.C V id :=
  loopFactor_flip_current _ _ _ _ _ _ _ _

/-- `D₁` does not depend on the q-axis current. -/
@[powerlib_foundation] theorem D1_indep_iq (a b V η : ℝ) :
    ({ d with iq := a } : DCParams).D1 V η = ({ d with iq := b } : DCParams).D1 V η := rfl

@[powerlib_foundation] theorem uSol_inConv (θ x V η : ℝ) :
    d.inConv.uSol θ x V η = d.outConv.uSol θ x V η := by
  simp only [uSol, D0_inConv, idRef_inConv]; simp [inConv, outConv]; ring

@[powerlib_foundation] theorem vqSol_inConv (θ x V η : ℝ) :
    d.inConv.vqSol θ x V η = d.outConv.vqSol θ x V η := by
  simp only [vqSol, uSol_inConv, idRef_inConv]; simp [inConv, outConv]; ring

@[powerlib_foundation] theorem vdStat_inConv (θ x V η : ℝ) :
    d.inConv.vdStat θ x V η = d.outConv.vdStat θ x V η := by
  simp only [vdStat, uSol_inConv, idRef_inConv]; simp [inConv, outConv]; ring

@[powerlib_foundation] theorem PStat_inConv (θ x V η : ℝ) :
    d.inConv.PStat θ x V η = -d.outConv.PStat θ x V η := by
  simp only [PStat, vdStat_inConv, vqSol_inConv, idRef_inConv]; simp [inConv, outConv]; ring

@[powerlib_foundation] theorem didSol_inConv (θ x V η : ℝ) :
    d.inConv.didSol θ x V η = -d.outConv.didSol θ x V η := by
  simp only [didSol, PStat_inConv, D1_inConv]; simp [inConv, outConv]; ring

@[powerlib_foundation] theorem VdSol_inConv (θ x V η : ℝ) :
    d.inConv.VdSol θ x V η = d.outConv.VdSol θ x V η := by
  simp only [VdSol, PStat_inConv, didSol_inConv, idRef_inConv]; simp [inConv, outConv]; ring

/-- The reduced four-state field is literally the same in both conventions (no state is a
current), so its Jacobian agrees entry by entry at every point. -/
@[powerlib_foundation] theorem field_inConv : d.inConv.field = d.outConv.field := by
  have : d.inConv.coordField = d.outConv.coordField := by
    funext y
    simp only [coordField, uSol_inConv, vqSol_inConv, VdSol_inConv]
  simp only [field, this]

@[powerlib_foundation] theorem fderiv_field_inConv (z : Dynamics.State 4) :
    fderiv ℝ d.inConv.field z = fderiv ℝ d.outConv.field z := by
  rw [field_inConv]

end DCParams

/-! ## Four-state model: absorbed powers from the complex power -/

/-- Absorbed reactive power of the four-state model (`i_q = 0`): `Q_abs = (3/2) v_q i_d`. -/
def qAbs (p : FourState.Params) (θ V η : ℝ) : ℝ := 3 / 2 * (FourState.vq p θ V η * FourState.idc p V η)

/-- `P_abs = (3/2) Re(V̄ Ī*)`, `Q_abs = (3/2) Im(V̄ Ī*)` with `V̄ = V₀ cos θ + j v_q`,
`Ī = i_d + j 0` (`conventions.md` §D0, IN-positive). -/
@[powerlib_foundation] theorem fourState_power (p : FourState.Params) (θ V η : ℝ) :
    FourState.Pabs p θ V η = (3 / 2 : ℝ) * (((⟨p.V0 * cos θ, FourState.vq p θ V η⟩ : ℂ) *
      (starRingEnd ℂ) ⟨FourState.idc p V η, 0⟩).re) ∧
    qAbs p θ V η = (3 / 2 : ℝ) * (((⟨p.V0 * cos θ, FourState.vq p θ V η⟩ : ℂ) *
      (starRingEnd ℂ) ⟨FourState.idc p V η, 0⟩).im) := by
  rw [Transform.complexPower_expand]
  simp only [FourState.Pabs, qAbs]
  constructor <;> ring

end powerlib.GFL.ModelLayers
