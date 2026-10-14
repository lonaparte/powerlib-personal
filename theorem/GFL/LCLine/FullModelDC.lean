import theorem.GFL.LCLine.FullModel
import theorem.PLL.PIPLL

/-! # The 13-state GFL-VSC with DC-link dynamics: constant-power equilibria

Domain module (`vsc-stochastic-stability`, main-line "M1dc").

Model boundary.
* State `x : State 13`: coordinates `0 … 9` exactly as in `theorem/GFL/LCLine/FullModel.lean`
  (`i_d, i_q, v_cd, v_cq, i_gd, i_gq, ξ_d, ξ_q, η, θ_e`), then `x 10 = v_dc` (DC-link voltage),
  `x 11 = ξ_dc` (DC-voltage PI integrator), `x 12 = v_f` (filtered DC-voltage measurement).
* The d-axis current reference is endogenous: `i_d*(x) = K_p^dc (v_f − v_dc^ref) + K_i^dc ξ_dc`
  (inverter convention, `v_dc` high ⇒ more export); `i_q*` frozen.
  Rows `0 … 9` are the 10-state field of `FullModel.lean` with `i_d* := i_d*(x)`
  (`field13_apply_lt`); DC side:
  `C_dc v_dc v̇_dc = P_dc − P_br` (written `v̇_dc = (P_dc − P_br)/(C_dc v_dc)`),
  `ξ̇_dc = v_f − v_dc^ref`, `v̇_f = ω_f (v_dc − v_f)`, bridge power `P_br = (3/2) u^c · i^c`.
* Direction: OUT-positive converter current and `P_br > 0` = bridge output, `P_dc > 0` = DC
  source injection (`decisions.md` §D1.6; opposite to `conventions.md` §D1:
  `I^IN = −i`, `P^absorb = −P_br`). Text-convention PLL angle (`decisions.md` §D1.1–§D1.3).
* Constant `P_dc`, no modulation limit, no switching or sampling delay, continuous time,
  `δω_g = 0`. Level: equilibrium set, plus algebraic identities of the bridge power.

Nondegeneracy: `L_f, C_f, L_g ≠ 0`, `ω_g C_f ≠ 0`, `Δ ≠ 0`, `K_i^cc ≠ 0`, `K_i ≠ 0`,
`K_i^dc ≠ 0`, `ω_f ≠ 0`, `C_dc ≠ 0`, `v_dc^ref ≠ 0`.

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/dc-link-dynamics.md` §1, §2,
§7.2; code reference `simulation/src/.../models_dc.py` (`full_dynamics_dc`, `_alg_chain`,
`_idref_const_power`).

Results.
* `bridge_power_invariant` : `u = v_c + (R_f + jω L_f) i ⇒ u·i = v_c·i + R_f |i|²`.
* `bridgePower_qss` / `PbrAlg_eq` : on the quasi-steady set
  `P_br = (3/2)[(R_f + R_g/Δ)(i_d*² + i_q*²) +
  (V_g/Δ)(i_d*((1 − b)cos θ − a sin θ) − i_q*((1 − b) sin θ + a cos θ))]`, a polynomial of degree
  exactly two in `i_d*` when `R_f + R_g/Δ ≠ 0` (`PbrAlg_quadratic`).
* `field13_eq_zero_iff` : `x` is an equilibrium iff `x = qss13 θ i` with `h(θ, i) = 0`,
  `P_br(θ, i) = P_dc` (constant-power equilibrium; `v_dc = v_f = v_dc^ref`, `ξ_dc = i/K_i^dc`).
* `PbrAlg_eq_Pdc_iff` : for fixed `θ` the power balance has no real `i_d*` when the
  discriminant is negative, and otherwise exactly the two roots `r₊(θ), r₋(θ)`;
  `field13_exists_equilibrium_iff` : an equilibrium exists iff for some `θ` the discriminant is
  `≥ 0` and `h(θ, r₊(θ)) = 0` or `h(θ, r₋(θ)) = 0` (union of the two branches).
* `cp_energy_rate` : on the 2D constant-power layer, wherever a local potential `V` with
  `V′ = −h_cp` exists, `Ḣ_cp = −K_p h_cp² ≤ 0` (no claim where `h_cp` is undefined).

Family and connection conclusions.
The module states no behaviour of the 13-state field: it has
no Family, and every result is static. The equilibrium characterizations `field13_eq_zero_iff`
and `field13_exists_equilibrium_iff` are static evidence on the model,
not connection conclusions. `cp_energy_rate` is a pointwise derivative identity for an arbitrary
phase-detector signal.
-/

noncomputable section
namespace powerlib.GFL.LCLine
open Real Matrix
open powerlib.Dynamics (State)
open powerlib.PLL
open powerlib.Transform (park_dot iparkD iparkQ)

/-- DC-side parameters. -/
structure DCParams where
  /-- DC-link capacitance `C_dc`. -/
  Cdc : ℝ
  /-- DC-voltage reference `v_dc^ref`. -/
  vref : ℝ
  /-- DC-voltage PI proportional gain `K_p^dc`. -/
  Kpdc : ℝ
  /-- DC-voltage PI integral gain `K_i^dc`. -/
  Kidc : ℝ
  /-- Constant DC injection `P_dc`. -/
  Pdc : ℝ
  /-- Measurement filter bandwidth `ω_f`. -/
  wf : ℝ

/-- Bridge-power invariant: with `u = v_c + R_f i + ω L_f J i`, `u·i = v_c·i + R_f |i|²`
(the `ω L_f` cross terms cancel in the dot product). -/
@[powerlib_foundation] theorem bridge_power_invariant (vd vq id iq Rf ωL : ℝ) :
    (vd + Rf * id - ωL * iq) * id + (vq + Rf * iq + ωL * id) * iq =
      (vd * id + vq * iq) + Rf * (id ^ 2 + iq ^ 2) := by
  ring

namespace Params

variable (p : Params) (d : DCParams)

/-- The same converter with the d-axis current reference replaced by `i`. -/
def withId (i : ℝ) : Params := { p with idRef := i }

@[simp, powerlib_foundation] theorem withId_a (i : ℝ) : (p.withId i).a = p.a := rfl
@[simp, powerlib_foundation] theorem withId_b (i : ℝ) : (p.withId i).b = p.b := rfl
@[simp, powerlib_foundation] theorem withId_Δ (i : ℝ) : (p.withId i).Δ = p.Δ := rfl
@[simp, powerlib_foundation] theorem withId_wC (i : ℝ) : (p.withId i).wC = p.wC := rfl
@[simp, powerlib_foundation] theorem withId_Vg (i : ℝ) : (p.withId i).Vg = p.Vg := rfl
@[simp, powerlib_foundation] theorem withId_idRef (i : ℝ) : (p.withId i).idRef = i := rfl
@[simp, powerlib_foundation] theorem withId_iqRef (i : ℝ) : (p.withId i).iqRef = p.iqRef := rfl
@[simp, powerlib_foundation] theorem withId_Rf (i : ℝ) : (p.withId i).Rf = p.Rf := rfl
@[simp, powerlib_foundation] theorem withId_Rg (i : ℝ) : (p.withId i).Rg = p.Rg := rfl

/-- The first ten coordinates. -/
def proj10 (x : State 13) : State 10 :=
  WithLp.toLp 2 (fun i : Fin 10 => x (Fin.castLE (by norm_num) i))

/-- Endogenous d-axis current reference `i_d*(x) = K_p^dc (v_f − v_dc^ref) + K_i^dc ξ_dc`. -/
def idStar (x : State 13) : ℝ := d.Kpdc * (x 12 - d.vref) + d.Kidc * x 11

/-- Bridge power `P_br = (3/2) u^c · i^c`. -/
def Pbr (x : State 13) : ℝ :=
  3 / 2 * ((p.withId (idStar d x)).ucD (proj10 x) * icD (proj10 x) +
    (p.withId (idStar d x)).ucQ (proj10 x) * icQ (proj10 x))

/-- The 13-state field: rows `0 … 9` are the 10-state field with `i_d* := i_d*(x)`. -/
def field13 (x : State 13) : State 13 :=
  WithLp.toLp 2 fun j : Fin 13 =>
    if h : (j : ℕ) < 10 then (p.withId (idStar d x)).field10 (proj10 x) ⟨j, h⟩
    else if (j : ℕ) = 10 then (d.Pdc - p.Pbr d x) / (d.Cdc * x 10)
    else if (j : ℕ) = 11 then x 12 - d.vref
    else d.wf * (x 10 - x 12)

/-- Rows `0 … 9` of the 13-state field are the 10-state field with `i_d* := i_d*(x)`. -/
@[powerlib_foundation] theorem field13_apply_lt (x : State 13) (i : Fin 10) :
    p.field13 d x (Fin.castLE (by norm_num) i) = (p.withId (idStar d x)).field10 (proj10 x) i := by
  simp [field13, i.isLt]

@[simp, powerlib_foundation] theorem field13_10 (x : State 13) :
    p.field13 d x 10 = (d.Pdc - p.Pbr d x) / (d.Cdc * x 10) := by
  simp [field13]
@[simp, powerlib_foundation] theorem field13_11 (x : State 13) :
    p.field13 d x 11 = x 12 - d.vref := by
  simp [field13]
@[simp, powerlib_foundation] theorem field13_12 (x : State 13) :
    p.field13 d x 12 = d.wf * (x 10 - x 12) := by
  simp [field13]

/-! ### Bridge power on the quasi-steady set -/

/-- Bridge power of the quasi-steady algebra with reference `i_d* = p.idRef`. -/
def PbrAlg (θ : ℝ) : ℝ :=
  3 / 2 * ((p.vcD θ p.Vg 0 * p.iD θ + p.vcQ θ p.Vg 0 * p.iQ θ) +
    p.Rf * (p.idRef ^ 2 + p.iqRef ^ 2))

@[powerlib_foundation] theorem icD_qssState (θ η : ℝ) : icD (p.qssState θ η) = p.idRef := by
  simp [icD, qssState, iD, iQ]

@[powerlib_foundation] theorem icQ_qssState (θ η : ℝ) : icQ (p.qssState θ η) = p.iqRef := by
  simp [icQ, qssState, iD, iQ]

/-- `P_br = (3/2) u^c · i^c` evaluated on the quasi-steady set (`K_i^cc ≠ 0`). -/
@[powerlib_foundation] theorem bridgePower_qss (hKicc : p.Kicc ≠ 0) (θ η : ℝ) :
    3 / 2 * (p.ucD (p.qssState θ η) * icD (p.qssState θ η) +
      p.ucQ (p.qssState θ η) * icQ (p.qssState θ η)) = p.PbrAlg θ := by
  have h6 : p.Kicc * p.qssState θ η 6 = p.Rf * p.idRef := by
    show p.Kicc * (p.Rf * p.idRef / p.Kicc) = _; field_simp
  have h7 : p.Kicc * p.qssState θ η 7 = p.Rf * p.iqRef := by
    show p.Kicc * (p.Rf * p.iqRef / p.Kicc) = _; field_simp
  have hdot : vccD (p.qssState θ η) * p.idRef + vccQ (p.qssState θ η) * p.iqRef =
      p.vcD θ p.Vg 0 * p.iD θ + p.vcQ θ p.Vg 0 * p.iQ θ := by
    rw [← p.icD_qssState θ η, ← p.icQ_qssState θ η]
    exact park_dot θ _ _ _ _
  simp only [ucD, ucQ, p.icD_qssState, p.icQ_qssState, h6, h7, PbrAlg]
  rw [← hdot]
  ring

/-- Closed form of the quasi-steady bridge power. -/
@[powerlib_foundation] theorem PbrAlg_eq (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    p.PbrAlg θ = 3 / 2 * ((p.Rf + p.Rg / p.Δ) * (p.idRef ^ 2 + p.iqRef ^ 2) +
      p.Vg / p.Δ * (p.idRef * ((1 - p.b) * cos θ - p.a * sin θ) -
        p.iqRef * ((1 - p.b) * sin θ + p.a * cos θ))) := by
  have s1 : p.vcD θ p.Vg 0 * p.iD θ + p.vcQ θ p.Vg 0 * p.iQ θ =
      (p.igD θ p.Vg 0 * p.iQ θ - p.igQ θ p.Vg 0 * p.iD θ) / p.wC := by
    simp only [vcD, vcQ]; field_simp; ring
  have s2 : p.igD θ p.Vg 0 * p.iQ θ - p.igQ θ p.Vg 0 * p.iD θ =
      (p.a * (p.iD θ ^ 2 + p.iQ θ ^ 2) + p.wC * p.Vg * ((1 - p.b) * p.iD θ - p.a * p.iQ θ)) /
        p.Δ := by
    simp only [igD, igQ, solD, solQ]; field_simp; ring
  have s3 : p.iD θ ^ 2 + p.iQ θ ^ 2 = p.idRef ^ 2 + p.iqRef ^ 2 := by
    simp only [iD, iQ, iparkD, iparkQ]
    linear_combination (p.idRef ^ 2 + p.iqRef ^ 2) * sin_sq_add_cos_sq θ
  have s4 : (1 - p.b) * p.iD θ - p.a * p.iQ θ =
      p.idRef * ((1 - p.b) * cos θ - p.a * sin θ) - p.iqRef * ((1 - p.b) * sin θ + p.a * cos θ) := by
    simp only [iD, iQ, iparkD, iparkQ]; ring
  have ha : p.a = p.wC * p.Rg := rfl
  rw [PbrAlg, s1, s2, s3, s4, ha]
  field_simp
  ring

/-- Coefficients of the bridge power as a polynomial in `i_d*`. -/
def pbrA : ℝ := 3 / 2 * (p.Rf + p.Rg / p.Δ)
/-- Linear coefficient in `i_d*`. -/
def pbrB (θ : ℝ) : ℝ := 3 / 2 * (p.Vg / p.Δ * ((1 - p.b) * cos θ - p.a * sin θ))
/-- Constant term. -/
def pbrC (θ : ℝ) : ℝ :=
  3 / 2 * ((p.Rf + p.Rg / p.Δ) * p.iqRef ^ 2 - p.Vg / p.Δ * (p.iqRef * ((1 - p.b) * sin θ +
    p.a * cos θ)))

/-- The bridge power is a quadratic polynomial in `i_d*` (degree exactly two iff
`R_f + R_g/Δ ≠ 0`). -/
@[powerlib_foundation] theorem PbrAlg_quadratic (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ i : ℝ) :
    (p.withId i).PbrAlg θ = p.pbrA * (i * i) + p.pbrB θ * i + p.pbrC θ := by
  rw [(p.withId i).PbrAlg_eq hwC hΔ]
  simp only [withId_a, withId_b, withId_Δ, withId_Vg, withId_idRef, withId_iqRef, withId_Rf,
    withId_Rg, pbrA, pbrB, pbrC]
  ring

/-- Discriminant of the power balance `P_br(θ, i) = P_dc` in `i`. -/
def pbrDisc (θ : ℝ) : ℝ := discrim p.pbrA (p.pbrB θ) (p.pbrC θ - d.Pdc)

/-- The two branches `r_±(θ) = (−β ± √disc)/(2α)`. -/
def rootPlus (θ : ℝ) : ℝ := (-p.pbrB θ + √(p.pbrDisc d θ)) / (2 * p.pbrA)
/-- Second branch. -/
def rootMinus (θ : ℝ) : ℝ := (-p.pbrB θ - √(p.pbrDisc d θ)) / (2 * p.pbrA)

/-- Power balance in `i_d*` at fixed `θ`: no real solution if the discriminant is negative,
otherwise exactly the two branches. -/
@[powerlib_foundation] theorem PbrAlg_eq_Pdc_iff (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hA : p.pbrA ≠ 0) (θ i : ℝ) :
    (p.withId i).PbrAlg θ = d.Pdc ↔
      0 ≤ p.pbrDisc d θ ∧ (i = p.rootPlus d θ ∨ i = p.rootMinus d θ) := by
  rw [p.PbrAlg_quadratic hwC hΔ, ← sub_eq_zero,
    show p.pbrA * (i * i) + p.pbrB θ * i + p.pbrC θ - d.Pdc =
      p.pbrA * (i * i) + p.pbrB θ * i + (p.pbrC θ - d.Pdc) by ring]
  by_cases hd : 0 ≤ p.pbrDisc d θ
  · have hs : discrim p.pbrA (p.pbrB θ) (p.pbrC θ - d.Pdc) = √(p.pbrDisc d θ) * √(p.pbrDisc d θ) :=
      (Real.mul_self_sqrt hd).symm
    rw [quadratic_eq_zero_iff hA hs]
    simp [hd, rootPlus, rootMinus]
  · simp only [hd, false_and, iff_false]
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ i
    intro s hs
    exact hd (by rw [pbrDisc, hs]; exact sq_nonneg s)

/-! ### Equilibria of the 13-state field -/

/-- The explicit constant-power equilibrium candidate with PLL angle `θ` and current `i`. -/
def qss13 (θ i : ℝ) : State 13 :=
  WithLp.toLp 2 fun j : Fin 13 =>
    if h : (j : ℕ) < 10 then (p.withId i).qssState θ 0 ⟨j, h⟩
    else if (j : ℕ) = 11 then i / d.Kidc else d.vref

@[powerlib_foundation] theorem proj10_qss13 (θ i : ℝ) :
    proj10 (p.qss13 d θ i) = (p.withId i).qssState θ 0 := by
  rw [state10_ext_iff]; intro j
  simp [proj10, qss13]

@[powerlib_foundation] theorem qss13_10 (θ i : ℝ) : p.qss13 d θ i 10 = d.vref := by
  simp [qss13]
@[powerlib_foundation] theorem qss13_11 (θ i : ℝ) : p.qss13 d θ i 11 = i / d.Kidc := by
  simp [qss13]
@[powerlib_foundation] theorem qss13_12 (θ i : ℝ) : p.qss13 d θ i 12 = d.vref := by
  simp [qss13]

@[powerlib_foundation] theorem idStar_qss13 (hKidc : d.Kidc ≠ 0) (θ i : ℝ) :
    idStar d (p.qss13 d θ i) = i := by
  rw [idStar, p.qss13_11, p.qss13_12]
  field_simp; ring

@[powerlib_foundation] private lemma state13_ext_iff {x y : State 13} :
    x = y ↔ ∀ i, x i = y i := by
  constructor
  · rintro rfl i; rfl
  · intro h; ext i; exact h i

/-- Coordinates `0 … 9` of a 13-state vector are those of its projection. -/
@[powerlib_foundation] private lemma apply_eq_proj10 (x : State 13) (j : Fin 13)
    (hj : (j : ℕ) < 10) : x j = proj10 x ⟨j, hj⟩ := by
  simp [proj10]

/-- A (`dc-link-dynamics.md` §2): the equilibria of the 13-state field are exactly the
constant-power quasi-steady states: `h(θ, i) = 0` and `P_br(θ, i) = P_dc`, with
`v_dc = v_f = v_dc^ref` and `ξ_dc = i/K_i^dc`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field13_eq_zero_iff (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKicc : p.Kicc ≠ 0) (hKi : p.Ki ≠ 0)
    (hKidc : d.Kidc ≠ 0) (hwf : d.wf ≠ 0) (hCdc : d.Cdc ≠ 0) (hvref : d.vref ≠ 0)
    (x : State 13) :
    p.field13 d x = 0 ↔ ∃ θ i, (p.withId i).h θ = 0 ∧ (p.withId i).PbrAlg θ = d.Pdc ∧
      x = p.qss13 d θ i := by
  constructor
  · intro hx
    set q := p.withId (idStar d x)
    have h10 : q.field10 (proj10 x) = 0 := by
      rw [state10_ext_iff]; intro j
      rw [← p.field13_apply_lt d x j, hx]; rfl
    obtain ⟨θ, hθ, hy⟩ := (q.field10_eq_zero_iff hLf hCf hLg hwC hΔ hKicc hKi _).mp h10
    have e11 : x 12 - d.vref = 0 := by rw [← p.field13_11 d x, hx]; rfl
    have e12 : d.wf * (x 10 - x 12) = 0 := by rw [← p.field13_12 d x, hx]; rfl
    have e10 : (d.Pdc - p.Pbr d x) / (d.Cdc * x 10) = 0 := by rw [← p.field13_10 d x, hx]; rfl
    have hvf : x 12 = d.vref := by linarith
    have hvdc : x 10 = d.vref := by
      rcases mul_eq_zero.mp e12 with h | h
      · exact absurd h hwf
      · linarith
    have hP : p.Pbr d x = d.Pdc := by
      rw [div_eq_zero_iff, or_iff_left (mul_ne_zero hCdc (by rw [hvdc]; exact hvref))] at e10
      linarith
    have hid : idStar d x = d.Kidc * x 11 := by simp [idStar, hvf]
    refine ⟨θ, idStar d x, hθ, ?_, ?_⟩
    · rw [← hP, Pbr, ← q.bridgePower_qss hKicc θ 0, ← hy]
    · rw [state13_ext_iff]; intro j
      by_cases hj : (j : ℕ) < 10
      · rw [apply_eq_proj10 x j hj, hy]
        simp [qss13, hj, q]
      · rcases j with ⟨k, hk⟩
        simp only at hj
        interval_cases k
        · rw [show (⟨10, hk⟩ : Fin 13) = 10 from rfl, qss13_10]; exact hvdc
        · rw [show (⟨11, hk⟩ : Fin 13) = 11 from rfl, qss13_11, hid]; field_simp
        · rw [show (⟨12, hk⟩ : Fin 13) = 12 from rfl, qss13_12]; exact hvf
  · rintro ⟨θ, i, hθ, hP, rfl⟩
    have hq := p.proj10_qss13 d θ i
    have hid := p.idStar_qss13 d hKidc θ i
    have h10 : (p.withId i).field10 ((p.withId i).qssState θ 0) = 0 :=
      ((p.withId i).field10_eq_zero_iff hLf hCf hLg hwC hΔ hKicc hKi _).mpr ⟨θ, hθ, rfl⟩
    rw [state13_ext_iff]; intro j
    by_cases hj : (j : ℕ) < 10
    · have := p.field13_apply_lt d (p.qss13 d θ i) ⟨j, hj⟩
      rw [show Fin.castLE (by norm_num) (⟨j, hj⟩ : Fin 10) = j from Fin.ext rfl, hid, hq, h10]
        at this
      rw [this]; rfl
    · rcases j with ⟨k, hk⟩
      simp only at hj
      interval_cases k
      · rw [show (⟨10, hk⟩ : Fin 13) = 10 from rfl, p.field13_10, Pbr, hid, hq,
          (p.withId i).bridgePower_qss hKicc θ 0, hP, sub_self, zero_div]; rfl
      · rw [show (⟨11, hk⟩ : Fin 13) = 11 from rfl, p.field13_11, p.qss13_12, sub_self]; rfl
      · rw [show (⟨12, hk⟩ : Fin 13) = 12 from rfl, p.field13_12, p.qss13_10, p.qss13_12,
          sub_self, mul_zero]; rfl

/-- Existence of a constant-power equilibrium, as the union of the two branches of the power
balance (the domain where the discriminant is negative contributes nothing).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field13_exists_equilibrium_iff (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKicc : p.Kicc ≠ 0) (hKi : p.Ki ≠ 0)
    (hKidc : d.Kidc ≠ 0) (hwf : d.wf ≠ 0) (hCdc : d.Cdc ≠ 0) (hvref : d.vref ≠ 0)
    (hA : p.pbrA ≠ 0) :
    (∃ x, p.field13 d x = 0) ↔ ∃ θ, 0 ≤ p.pbrDisc d θ ∧
      ((p.withId (p.rootPlus d θ)).h θ = 0 ∨ (p.withId (p.rootMinus d θ)).h θ = 0) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨θ, i, hθ, hP, -⟩ :=
      (p.field13_eq_zero_iff d hLf hCf hLg hwC hΔ hKicc hKi hKidc hwf hCdc hvref x).mp hx
    obtain ⟨hdisc, hi | hi⟩ := (p.PbrAlg_eq_Pdc_iff d hwC hΔ hA θ i).mp hP
    · exact ⟨θ, hdisc, Or.inl (hi ▸ hθ)⟩
    · exact ⟨θ, hdisc, Or.inr (hi ▸ hθ)⟩
  · rintro ⟨θ, hdisc, hθ | hθ⟩
    · exact ⟨_, (p.field13_eq_zero_iff d hLf hCf hLg hwC hΔ hKicc hKi hKidc hwf hCdc hvref _).mpr
        ⟨θ, _, hθ, (p.PbrAlg_eq_Pdc_iff d hwC hΔ hA θ _).mpr ⟨hdisc, Or.inl rfl⟩, rfl⟩⟩
    · exact ⟨_, (p.field13_eq_zero_iff d hLf hCf hLg hwC hΔ hKicc hKi hKidc hwf hCdc hvref _).mpr
        ⟨θ, _, hθ, (p.PbrAlg_eq_Pdc_iff d hwC hΔ hA θ _).mpr ⟨hdisc, Or.inr rfl⟩, rfl⟩⟩

end Params

/-! ### Energy identity of the 2D constant-power layer -/

/-- For the PI-PLL field with any phase-detector signal `h_cp` (for the constant-power layer,
`h_cp(θ) = h(θ, r_±(θ))`, defined where the discriminant is `≥ 0`): at every point where a local
potential `V` has `V′ = −h_cp`, the energy `H = ½ K_i η² + V(θ)` satisfies `Ḣ = −K_p h_cp² ≤ 0`. -/
@[powerlib_foundation] theorem cp_energy_rate {hcp V : ℝ → ℝ} (Kp Ki : ℝ) {y : State 2}
    (hV : HasDerivAt V (-hcp (y 0)) (y 0)) :
    fderiv ℝ (fun z : State 2 => Ki / 2 * z 1 ^ 2 + V (z 0)) y (piPLLField hcp Kp Ki 0 y) =
      -(Kp * hcp (y 0) ^ 2) := by
  set π0 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  set π1 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have h0 : HasFDerivAt (fun z : State 2 => z 0) π0 y := π0.hasFDerivAt
  have h1 : HasFDerivAt (fun z : State 2 => z 1) π1 y := π1.hasFDerivAt
  have hH : HasFDerivAt (fun z : State 2 => Ki / 2 * z 1 ^ 2 + V (z 0))
      ((Ki / 2) • (2 • y 1 ^ (2 - 1)) • π1 + -hcp (y 0) • π0) y :=
    ((h1.pow 2).const_mul (Ki / 2)).add (hV.comp_hasFDerivAt y h0)
  rw [hH.fderiv]
  simp [π0, π1, piPLLField]
  ring

@[powerlib_foundation] theorem cp_energy_rate_nonpos {hcp V : ℝ → ℝ} {Kp : ℝ} (Ki : ℝ)
    (hKp : 0 ≤ Kp) {y : State 2} (hV : HasDerivAt V (-hcp (y 0)) (y 0)) :
    fderiv ℝ (fun z : State 2 => Ki / 2 * z 1 ^ 2 + V (z 0)) y (piPLLField hcp Kp Ki 0 y) ≤ 0 := by
  rw [cp_energy_rate Kp Ki hV]
  have := mul_nonneg hKp (sq_nonneg (hcp (y 0)))
  linarith

end powerlib.GFL.LCLine
