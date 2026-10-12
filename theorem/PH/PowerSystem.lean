import theorem.PH.Linear
import theorem.TMIO.ClaimElab

/-! # Single machine, node capacitor, RL link and infinite bus: an 11-state pH system

Model boundary (T-power-system-ph §1.5.1).
* One seven-state dq synchronous machine (the `syncMachine7` model of
  `theorem/PH/SyncMachine.lean`: linear magnetics, inverse inductance `Γ ≻ 0`, IN-positive
  stator currents, damping `D` on `ω_r`), one network node with shunt capacitance `C > 0`
  (common DQ frame), one series RL link `L_l > 0`, `r_l ≥ 0` (common DQ frame), and an
  infinite bus with prescribed voltage `(V_D^∞, V_Q^∞)`.
* State order `x = (Ψ_d, Ψ_q, Ψ_f, Ψ_kd, Ψ_kq, p, δ, q_D, q_Q, φ_D, φ_Q) ∈ ℝ¹¹`.
  `∇H = (i_d, i_q, i_f, i_kd, i_kq, ω_r, 0, V_D, V_Q, I_D, I_Q)` with `V = q / C`, `I = φ / L_l`.
* The common DQ frame rotates at a constant `ω_s`; the machine frame is related to it by the
  rotation `R(δ)`; node and link carry the frame-rotation terms `± ω_s C`, `± ω_s L_l`.
* Inputs `u = (v_f, T_m^ext, V_D^∞, V_Q^∞)`; outputs `y = (i_f, ω_r, −I_D, −I_Q)`; port power
  `v_f i_f + T_m ω_r − V^∞·I` (IN-positive for the machine; the power delivered to the
  infinite bus counts negative).
* `J^tot(x)` is the explicit 11 × 11 matrix of the note (depends on `Ψ_d, Ψ_q, cos δ, sin δ`),
  `R^tot = diag(r_s, r_s, r_f, r_kd, r_kq, D, 0, 0, 0, r_l, r_l)`.
  The kernel checks `J^tot = −(J^tot)ᵀ` and that `(J − R)∇H + B u` reproduces every one of the
  eleven state equations of §1.5.1 (replacing the note's sympy check).
* Not modelled: AVR, governor, loads, more machines or nodes, saturation, zero sequence.
* `H` does not depend on `δ`; it is nonnegative but **not** positive definite
  (`smib11_no_quadraticStorage`, formerly stated as the absence of a quadratic storage of the
  removed `Passivity` interface), while passivity with storage `H` holds.

Correction (hard obstruction). The parent model T-sync-machine §1.13 uses the **absolute**
rotor angle, `δ̇ = ω_r`, and §1.5.1 keeps `δ̇ = ω_r` while using `δ` as the angle between the
rotor frame and the DQ frame rotating at `ω_s`. These are inconsistent: the angle between the
two frames obeys `δ̇ = ω_r − ω_s`. With the note's equation every equilibrium has `ω_r = 0`
(`smib11_speed_eq_zero_of_equilibrium`), so synchronous operation `ω_r = ω_s ≠ 0` is never an
equilibrium. We formalize
* `smib11`: the note's ODE verbatim (`δ̇ = ω_r`); its energy balance and passivity still hold;
* `smib11Rel`: the corrected relative-angle ODE `δ̇ = ω_r − ω_s`, obtained by adding the drift
  `−ω_s e_δ`. Since `∂H/∂δ = 0` this drift does no work, so the same energy balance and the
  same passivity statement hold, and every equilibrium now has `ω_r = ω_s`.

Families and connection conclusions. Two families on the parameters `SMIB11Params`, both read
at the origin (the unforced state; for the note's model an equilibrium):
* `SMIB11.family`: the note's model, system map the pH port system `(smib11 p).system`;
* `SMIB11Rel.family`: the corrected model, system map `smib11Rel_system p` (field
  `smib11Rel_field`, the same output and supplied power).
Passivity is translated into no requirement and is exact for both (`H ≥ 0`); flow sentences have
no translation (the whole, inconsistent, language), since no operating point is selected here
and the corrected model's origin is not an equilibrium when `ω_s ≠ 0`. Connection conclusions:
`SMIB11.mem_den_passive` and `SMIB11Rel.mem_den_passive` (formerly `smib11_passiveWithStorage`
and `smib11Rel_passiveWithStorage`), exactness and chain soundness of both families. The state
equations, damping power, supply, power balances, `H` identities and the equilibrium
corrections are static evidence. The former `smib11Rel_storage` (a storage structure of the
removed `Passivity` interface) is replaced by the passivity proof through
`Port.System.passiveWith_of_rate`.

Source: work-sync `theory/T-power-system-ph.md` §1.5.1 (11-state `J^tot`, `R^tot`, `B`,
state equations, energy balance), §1.4 (block-sum Hamiltonian); parent
`theory/T-sync-machine.md` §1.13.
-/

noncomputable section
namespace powerlib.PH
open Matrix Set Filter
open powerlib.Dynamics (State)

/-- Parameters of the 11-state test system. -/
structure SMIB11Params where
  Γ : Matrix (Fin 5) (Fin 5) ℝ
  M : ℝ
  rs : ℝ
  rf : ℝ
  rkd : ℝ
  rkq : ℝ
  D : ℝ
  C : ℝ
  Ll : ℝ
  rl : ℝ
  ωs : ℝ
  Γ_posDef : Γ.PosDef
  M_pos : 0 < M
  rs_nonneg : 0 ≤ rs
  rf_nonneg : 0 ≤ rf
  rkd_nonneg : 0 ≤ rkd
  rkq_nonneg : 0 ≤ rkq
  D_nonneg : 0 ≤ D
  C_pos : 0 < C
  Ll_pos : 0 < Ll
  rl_nonneg : 0 ≤ rl

/-- Diagonal storage weights outside the magnetic block. -/
def smib11_w (p : SMIB11Params) : Fin 11 → ℝ :=
  ![0, 0, 0, 0, 0, 1 / p.M, 0, 1 / p.C, 1 / p.C, 1 / p.Ll, 1 / p.Ll]

/-- Storage matrix `blkdiag(Γ, 1/M, 0, 1/C, 1/C, 1/L_l, 1/L_l)`. -/
def smib11_Q (p : SMIB11Params) : Matrix (Fin 11) (Fin 11) ℝ :=
  Matrix.of fun i j =>
    if h : i.val < 5 ∧ j.val < 5 then p.Γ ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
    else if i = j then smib11_w p i else 0

@[powerlib_foundation] theorem smib11_Q_symm (p : SMIB11Params) :
    (smib11_Q p)ᵀ = smib11_Q p := by
  have hs : ∀ a b : Fin 5, p.Γ b a = p.Γ a b := fun a b => by
    simpa using congrFun (congrFun p.Γ_posDef.isHermitian.eq a) b
  ext i j
  simp only [transpose_apply, smib11_Q, of_apply]
  by_cases h : i.val < 5 ∧ j.val < 5
  · simp only [h.1, h.2, and_self, dite_true]
    exact hs _ _
  · have h' : ¬(j.val < 5 ∧ i.val < 5) := fun h' => h ⟨h'.2, h'.1⟩
    simp only [h, h', dite_false]
    by_cases hij : i = j
    · subst hij
      rfl
    · simp [hij, Ne.symm hij]

/-- Flux linkages of the machine windings. -/
def smib11_flux (x : State 11) : Fin 5 → ℝ := ![x 0, x 1, x 2, x 3, x 4]

/-- Winding currents `i = Γ Ψ` (IN-positive stator currents). -/
def smib11_current (p : SMIB11Params) (x : State 11) : Fin 5 → ℝ := p.Γ *ᵥ smib11_flux x

/-- Rotor speed `ω_r = p / M`. -/
def smib11_speed (p : SMIB11Params) (x : State 11) : ℝ := x 5 / p.M

/-- `Q x = ∇H = (i, ω_r, 0, q_D/C, q_Q/C, φ_D/L_l, φ_Q/L_l)`. -/
@[powerlib_foundation] theorem smib11_Q_mulVec (p : SMIB11Params) (x : State 11) :
    smib11_Q p *ᵥ WithLp.ofLp x =
      ![smib11_current p x 0, smib11_current p x 1, smib11_current p x 2,
        smib11_current p x 3, smib11_current p x 4, smib11_speed p x, 0,
        x 7 / p.C, x 8 / p.C, x 9 / p.Ll, x 10 / p.Ll] := by
  ext i
  fin_cases i <;>
    simp [smib11_Q, smib11_w, smib11_current, smib11_flux, smib11_speed, mulVec, dotProduct,
      Fin.sum_univ_succ]
  all_goals ring

/-- `J^tot(x)` of §1.5.1. -/
def smib11_J (p : SMIB11Params) (x : State 11) : Matrix (Fin 11) (Fin 11) ℝ :=
  !![0, 0, 0, 0, 0, x 1, 0, Real.cos (x 6), Real.sin (x 6), 0, 0;
     0, 0, 0, 0, 0, -x 0, 0, -Real.sin (x 6), Real.cos (x 6), 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     -x 1, x 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     -Real.cos (x 6), Real.sin (x 6), 0, 0, 0, 0, 0, 0, p.ωs * p.C, -1, 0;
     -Real.sin (x 6), -Real.cos (x 6), 0, 0, 0, 0, 0, -(p.ωs * p.C), 0, 0, -1;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, p.ωs * p.Ll;
     0, 0, 0, 0, 0, 0, 0, 0, 1, -(p.ωs * p.Ll), 0]

/-- `R^tot = diag(r_s, r_s, r_f, r_kd, r_kq, D, 0, 0, 0, r_l, r_l)`. -/
def smib11_R (p : SMIB11Params) : Matrix (Fin 11) (Fin 11) ℝ :=
  diagonal ![p.rs, p.rs, p.rf, p.rkd, p.rkq, p.D, 0, 0, 0, p.rl, p.rl]

/-- Port matrix for `u = (v_f, T_m^ext, V_D^∞, V_Q^∞)`. -/
def smib11_g : Matrix (Fin 11) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if i = 2 ∧ j = 0 then 1 else if i = 5 ∧ j = 1 then 1
    else if i = 9 ∧ j = 2 then -1 else if i = 10 ∧ j = 3 then -1 else 0

/-- The 11-state SMIB test system of §1.5.1 as a nonlinear pH model (note's ODE, `δ̇ = ω_r`). -/
def smib11 (p : SMIB11Params) : NonlinearModel 11 4 where
  J := smib11_J p
  R _ := smib11_R p
  g _ := smib11_g
  H := quadraticEnergy (smib11_Q p)
  dH x := WithLp.toLp 2 (smib11_Q p *ᵥ WithLp.ofLp x)
  skew x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smib11_J]
  dissipation_posSemidef _ := PosSemidef.diagonal (fun i => by
    fin_cases i <;>
      simp [p.rs_nonneg, p.rf_nonneg, p.rkd_nonneg, p.rkq_nonneg, p.D_nonneg, p.rl_nonneg])
  hasGradient := hasGradientAt_quadraticEnergy (smib11_Q_symm p)

@[powerlib_foundation] theorem smib11_dH (p : SMIB11Params) (x : State 11) :
    WithLp.ofLp ((smib11 p).dH x) =
      ![smib11_current p x 0, smib11_current p x 1, smib11_current p x 2,
        smib11_current p x 3, smib11_current p x 4, smib11_speed p x, 0,
        x 7 / p.C, x 8 / p.C, x 9 / p.Ll, x 10 / p.Ll] :=
  smib11_Q_mulVec p x

/-- The pH field reproduces the eleven state equations of §1.5.1 (with `δ̇ = ω_r` as in the
note). Notation: `i = Γ Ψ`, `ω_r = p/M`, `V = q/C`, `I = φ/L_l`. -/
@[powerlib_foundation] theorem smib11_field (p : SMIB11Params) (x : State 11) (u : Fin 4 → ℝ) :
    WithLp.ofLp ((smib11 p).field x u) =
      ![-p.rs * smib11_current p x 0 + smib11_speed p x * x 1 +
          (Real.cos (x 6) * (x 7 / p.C) + Real.sin (x 6) * (x 8 / p.C)),
        -p.rs * smib11_current p x 1 - smib11_speed p x * x 0 +
          (-Real.sin (x 6) * (x 7 / p.C) + Real.cos (x 6) * (x 8 / p.C)),
        -p.rf * smib11_current p x 2 + u 0,
        -p.rkd * smib11_current p x 3,
        -p.rkq * smib11_current p x 4,
        (smib11_current p x 1 * x 0 - smib11_current p x 0 * x 1) + u 1 - p.D * smib11_speed p x,
        smib11_speed p x,
        -(Real.cos (x 6) * smib11_current p x 0 - Real.sin (x 6) * smib11_current p x 1) -
          x 9 / p.Ll + p.ωs * x 8,
        -(Real.sin (x 6) * smib11_current p x 0 + Real.cos (x 6) * smib11_current p x 1) -
          x 10 / p.Ll - p.ωs * x 7,
        -p.rl * (x 9 / p.Ll) + p.ωs * x 10 + x 7 / p.C - u 2,
        -p.rl * (x 10 / p.Ll) - p.ωs * x 9 + x 8 / p.C - u 3] := by
  have hC := p.C_pos.ne'
  have hL := p.Ll_pos.ne'
  rw [NonlinearModel.ofLp_field, smib11_dH]
  ext i
  fin_cases i <;>
    simp [smib11, smib11_J, smib11_R, smib11_g, mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.diagonal_apply]
  all_goals field_simp
  all_goals ring

@[powerlib_foundation] theorem smib11_dampingPower (p : SMIB11Params) (x : State 11) :
    (smib11 p).dampingPower x =
      p.rs * (smib11_current p x 0 ^ 2 + smib11_current p x 1 ^ 2) +
        p.rf * smib11_current p x 2 ^ 2 + p.rkd * smib11_current p x 3 ^ 2 +
        p.rkq * smib11_current p x 4 ^ 2 + p.D * smib11_speed p x ^ 2 +
        p.rl * ((x 9 / p.Ll) ^ 2 + (x 10 / p.Ll) ^ 2) := by
  rw [NonlinearModel.dampingPower, smib11_dH]
  simp [smib11, smib11_R, mulVec, dotProduct, Fin.sum_univ_succ, Matrix.diagonal_apply]
  ring

@[powerlib_foundation] theorem smib11_supply (p : SMIB11Params) (x : State 11) (u : Fin 4 → ℝ) :
    (smib11 p).supply x u =
      u 0 * smib11_current p x 2 + u 1 * smib11_speed p x -
        u 2 * (x 9 / p.Ll) - u 3 * (x 10 / p.Ll) := by
  rw [NonlinearModel.supply, NonlinearModel.output, smib11_dH]
  simp [smib11, smib11_g, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Energy balance of §1.5.1: `Ḣ = (v_f i_f + T_m ω_r − V_D^∞ I_D − V_Q^∞ I_Q) −
(r_s(i_d²+i_q²) + r_f i_f² + r_kd i_kd² + r_kq i_kq² + D ω_r² + r_l(I_D² + I_Q²))`. -/
@[powerlib_foundation] theorem smib11_power_balance (p : SMIB11Params) (x : State 11)
    (u : Fin 4 → ℝ) :
    fderiv ℝ (smib11 p).H x ((smib11 p).field x u) =
      (u 0 * smib11_current p x 2 + u 1 * smib11_speed p x -
        u 2 * (x 9 / p.Ll) - u 3 * (x 10 / p.Ll)) -
      (p.rs * (smib11_current p x 0 ^ 2 + smib11_current p x 1 ^ 2) +
        p.rf * smib11_current p x 2 ^ 2 + p.rkd * smib11_current p x 3 ^ 2 +
        p.rkq * smib11_current p x 4 ^ 2 + p.D * smib11_speed p x ^ 2 +
        p.rl * ((x 9 / p.Ll) ^ 2 + (x 10 / p.Ll) ^ 2)) := by
  rw [NonlinearModel.power_balance, smib11_supply, smib11_dampingPower]

/-- `H^tot` is the block sum of the machine, node-capacitor and link energies (§1.4). -/
@[powerlib_foundation] theorem smib11_H (p : SMIB11Params) (x : State 11) :
    (smib11 p).H x =
      ((1 / 2 : ℝ) * (smib11_flux x ⬝ᵥ (p.Γ *ᵥ smib11_flux x)) + x 5 ^ 2 / (2 * p.M)) +
        (x 7 ^ 2 + x 8 ^ 2) / (2 * p.C) + (x 9 ^ 2 + x 10 ^ 2) / (2 * p.Ll) := by
  have hQ := smib11_Q_mulVec p x
  simp only [smib11, quadraticEnergy]
  rw [hQ]
  simp [smib11_current, smib11_flux, smib11_speed, dotProduct, Fin.sum_univ_succ]
  ring

@[powerlib_foundation] theorem smib11_H_nonneg (p : SMIB11Params) (x : State 11) :
    0 ≤ (smib11 p).H x := by
  rw [smib11_H]
  have h := p.Γ_posDef.posSemidef.dotProduct_mulVec_nonneg (smib11_flux x)
  rw [star_trivial] at h
  have hM := p.M_pos
  have hC := p.C_pos
  have hL := p.Ll_pos
  positivity

/-- The unit vector along the rotor-angle coordinate. -/
def smib11_angleAxis (θ : ℝ) : State 11 := WithLp.toLp 2 (Pi.single 6 θ)

/-- `H` vanishes along the rotor-angle axis: it does not depend on `δ`. -/
@[powerlib_foundation] theorem smib11_H_angleAxis (p : SMIB11Params) (θ : ℝ) :
    (smib11 p).H (smib11_angleAxis θ) = 0 := by
  have hflux : smib11_flux (smib11_angleAxis θ) = 0 := by
    ext i
    fin_cases i <;> simp [smib11_flux, smib11_angleAxis]
  rw [smib11_H, hflux]
  simp [smib11_angleAxis]

/-- `H^tot` is not positive definite (it vanishes along the rotor-angle axis), hence it is no
quadratic storage. -/
@[powerlib_foundation] theorem smib11_no_quadraticStorage (p : SMIB11Params) :
    ¬ ∀ x : State 11, x ≠ 0 → 0 < (smib11 p).H x := by
  intro hpos
  have hne : smib11_angleAxis 1 ≠ 0 := by
    intro h
    have := congrArg (fun z : State 11 => z 6) h
    simp [smib11_angleAxis] at this
  have h := hpos _ hne
  rw [smib11_H_angleAxis] at h
  exact lt_irrefl _ h

/-- Correction: with the note's `δ̇ = ω_r`, every equilibrium (for any constant input) has
`ω_r = 0`. -/
@[powerlib_foundation] theorem smib11_speed_eq_zero_of_equilibrium (p : SMIB11Params)
    (x : State 11) (u : Fin 4 → ℝ) (h : (smib11 p).field x u = 0) : smib11_speed p x = 0 := by
  have h' := congrFun (congrArg WithLp.ofLp h) 6
  rw [smib11_field] at h'
  simpa using h'

/-- Correction: synchronous operation `ω_r = ω_s ≠ 0` is never an equilibrium of the
note's ODE. -/
@[powerlib_foundation] theorem smib11_not_equilibrium_of_synchronous (p : SMIB11Params)
    (hωs : p.ωs ≠ 0) (x : State 11) (hx : smib11_speed p x = p.ωs) (u : Fin 4 → ℝ) :
    (smib11 p).field x u ≠ 0 := fun h =>
  hωs (hx ▸ smib11_speed_eq_zero_of_equilibrium p x u h)

/-! ### Corrected relative-angle model `δ̇ = ω_r − ω_s` -/

/-- Field of the corrected model: the note's field plus the frame drift `−ω_s e_δ`. -/
def smib11Rel_field (p : SMIB11Params) (x : State 11) (u : Fin 4 → ℝ) : State 11 :=
  (smib11 p).field x u - smib11_angleAxis p.ωs

@[powerlib_foundation] theorem smib11Rel_field_angle (p : SMIB11Params) (x : State 11)
    (u : Fin 4 → ℝ) : smib11Rel_field p x u 6 = smib11_speed p x - p.ωs := by
  have h := congrFun (smib11_field p x u) 6
  simp only [smib11Rel_field, PiLp.sub_apply]
  rw [show (smib11 p).field x u 6 = WithLp.ofLp ((smib11 p).field x u) 6 from rfl, h]
  simp [smib11_angleAxis]

@[powerlib_foundation] theorem smib11Rel_field_other (p : SMIB11Params) (x : State 11)
    (u : Fin 4 → ℝ) (i : Fin 11) (hi : i ≠ 6) :
    smib11Rel_field p x u i = (smib11 p).field x u i := by
  simp [smib11Rel_field, smib11_angleAxis, hi]

/-- The frame drift does no work: `∂H/∂δ = 0`. -/
@[powerlib_foundation] theorem smib11_fderiv_H_angleAxis (p : SMIB11Params) (x : State 11)
    (θ : ℝ) : fderiv ℝ (smib11 p).H x (smib11_angleAxis θ) = 0 := by
  rw [NonlinearModel.fderiv_H_apply, smib11_dH]
  simp [smib11_angleAxis, dotProduct]

/-- Energy balance of the corrected model: identical to `smib11_power_balance`. -/
@[powerlib_foundation] theorem smib11Rel_power_balance (p : SMIB11Params) (x : State 11)
    (u : Fin 4 → ℝ) :
    fderiv ℝ (smib11 p).H x (smib11Rel_field p x u) =
      (smib11 p).supply x u - (smib11 p).dampingPower x := by
  rw [smib11Rel_field, map_sub, smib11_fderiv_H_angleAxis, sub_zero,
    NonlinearModel.power_balance]

/-- The corrected model as a port system (same output as the note's model). -/
def smib11Rel_system (p : SMIB11Params) : Port.System 11 4 :=
  ⟨smib11Rel_field p, fun x _ => (smib11 p).output x⟩

@[powerlib_foundation] theorem smib11Rel_system_supply (p : SMIB11Params) (x : State 11)
    (u : Fin 4 → ℝ) : (smib11Rel_system p).supply x u = (smib11 p).supply x u := rfl

/-- In the corrected model every equilibrium runs at synchronous speed `ω_r = ω_s`. -/
@[powerlib_foundation] theorem smib11Rel_speed_eq_of_equilibrium (p : SMIB11Params)
    (x : State 11) (u : Fin 4 → ℝ) (h : smib11Rel_field p x u = 0) :
    smib11_speed p x = p.ωs := by
  have h' := congrArg (fun z : State 11 => z 6) h
  simp only at h'
  rw [smib11Rel_field_angle] at h'
  simp only [PiLp.zero_apply] at h'
  linarith

/-! ### Families -/

namespace SMIB11

/-- Requirements: none is available beyond passivity. -/
inductive Requirement
  | impossible

/-- Satisfaction of a requirement. -/
def Meets (_ : SMIB11Params) : Requirement → Prop
  | .impossible => False

/-- Passivity needs no requirement; the flow sentences have no translation. -/
def translate : Sentence → Set Requirement
  | .passive => ∅
  | .flow _ => Set.univ

/-- The note's 11-state system, read as its pH port system at the origin. -/
def family : Family SMIB11Params Requirement 11 4 :=
  ⟨fun p => (smib11 p).system, Meets, translate⟩

@[powerlib_foundation] theorem family_isNonlinearPH : family.IsNonlinearPH smib11 :=
  fun _ => rfl

@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext p
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  exact fun h => h .impossible

/-- Passivity of the note's 11-state system with storage `H^tot`. -/
@[powerlib_domain] theorem mem_den_passive (p : SMIB11Params) :
    connection% (p ∈ family.den .passive) :=
  family_isNonlinearPH.mem_den_passive_of_lowerBound 0 (smib11_H_nonneg p)

/-- Passivity is translated exactly. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  refine Family.exact_of_translate_eq_empty rfl ?_
  ext p
  simp only [Set.mem_univ, iff_true]
  exact mem_den_passive p

/-- Every translation of the family is sound. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s p hp => ?_
  rw [TMIO.mem_realize] at hp
  change ∀ q ∈ translate s, Meets p q at hp
  rcases s with P | _
  · exact (hp .impossible trivial).elim
  · exact mem_den_passive p

end SMIB11

namespace SMIB11Rel

/-- The corrected relative-angle model, read as its port system at the origin. -/
def family : Family SMIB11Params SMIB11.Requirement 11 4 :=
  ⟨smib11Rel_system, SMIB11.Meets, SMIB11.translate⟩

/-- The corrected model is passive with storage `H^tot`: the frame drift does no work.
Implementation evidence for `mem_den_passive`. -/
private theorem passiveWith (p : SMIB11Params) :
    (smib11Rel_system p).PassiveWith (smib11 p).H :=
  (smib11Rel_system p).passiveWith_of_rate _ (smib11_H_nonneg p)
    (fun x u => fderiv ℝ (smib11 p).H x (smib11Rel_field p x u))
    (fun _ x _ _ t hx ht =>
      ((smib11 p).differentiable_H (x t)).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht))
    (fun x u => by
      rw [smib11Rel_power_balance, smib11Rel_system_supply]
      linarith [(smib11 p).dampingPower_nonneg x])

/-- Passivity of the corrected relative-angle model with storage `H^tot`. -/
@[powerlib_domain] theorem mem_den_passive (p : SMIB11Params) :
    connection% (p ∈ family.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [Family.mem_den]
  exact ⟨_, passiveWith p⟩

/-- Passivity is translated exactly. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  refine Family.exact_of_translate_eq_empty rfl ?_
  ext p
  simp only [Set.mem_univ, iff_true]
  exact mem_den_passive p

/-- Every translation of the family is sound. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s p hp => ?_
  rw [TMIO.mem_realize] at hp
  change ∀ q ∈ SMIB11.translate s, SMIB11.Meets p q at hp
  rcases s with P | _
  · exact (hp .impossible trivial).elim
  · exact mem_den_passive p

end SMIB11Rel

end powerlib.PH
