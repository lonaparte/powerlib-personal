/-
  Slow Frequency Mode of a Power-Locked GFL-VSC — formal model + Power Lock (§1–§5).

  This file fixes the parameters (§1), the state coordinates and the active-power
  algebra (§3), an abstract carrier for the inner vector field `F_inner` (§4) that
  records the one structural fact used by the crux — namely `F7 = e_P` — and proves:

    * Lemma 0  (Power Lock, §5)     : at any inner equilibrium `e_P = 0`,
                                       hence `P_meas = P_ref` and `i_d = P_ref/(1.5·Vg)`.
    * Corollary 0a (§5)            : along any C¹ equilibrium branch `z*(d)` the active
                                       power is identically `P_ref`; i.e. `i_d*` is
                                       pinned, so the synchronising coefficient `K = 0`.

  We deliberately carry `F_inner` abstractly (only the component `F7 = e_P` is needed
  for §5 and §7).  The remaining components `F1..F6, F8` of §3–§4 never enter the
  proofs of Theorems A/B/C; modelling them explicitly would force `Real.cos/Real.sin`
  and the analysis tower without adding logical content.  See `README.md`.
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

namespace GFL

open Matrix

/-- §1 (P1–P4).  Parameters of the power-locked GFL-VSC actually used by the
frequency-mode theorems.  The swing constants `H, D, Sn, wn` define `κ, b, β`
(§1/§4/§7); the controller/PLL/line constants enter only through the abstract
inner field and are not needed as separate fields. -/
structure Params where
  Vg     : ℝ
  P_ref  : ℝ
  Q_ref  : ℝ
  wn     : ℝ
  H      : ℝ
  D      : ℝ
  Sn     : ℝ
  Kp_pll : ℝ
  Ki_pll : ℝ
  Vg_pos     : 0 < Vg
  wn_pos     : 0 < wn
  H_pos      : 0 < H
  D_pos      : 0 < D
  Sn_pos     : 0 < Sn
  Pref_pos   : 0 < P_ref
  Ki_pll_pos : 0 < Ki_pll

namespace Params

variable (p : Params)

/-- `κ := wn / (2·H·Sn)` (§1, §4). -/
noncomputable def kappa : ℝ := p.wn / (2 * p.H * p.Sn)
/-- `b := D / (2·H)` (§1, §4). -/
noncomputable def b : ℝ := p.D / (2 * p.H)
/-- `β := wn / (2·H)` (§7, Theorem C). -/
noncomputable def beta : ℝ := p.wn / (2 * p.H)

lemma kappa_pos : 0 < p.kappa :=
  div_pos p.wn_pos (mul_pos (mul_pos two_pos p.H_pos) p.Sn_pos)

lemma b_pos : 0 < p.b :=
  div_pos p.D_pos (mul_pos two_pos p.H_pos)

lemma beta_pos : 0 < p.beta :=
  div_pos p.wn_pos (mul_pos two_pos p.H_pos)

end Params

/-! ### State and active-power algebra (§2–§3)

The state is `y : Fin 9 → ℝ` with the coordinate map (0-based)

  0 ↦ i_d, 1 ↦ i_q, 2 ↦ ξ_dc, 3 ↦ ξ_qc, 4 ↦ η, 5 ↦ θ_e, 6 ↦ ξ_P, 7 ↦ ξ_Q, 8 ↦ dw.

The inner block `z` is coordinates `0..7`; the frequency offset `dw` is coordinate `8`. -/

/-- §3: `P_meas := 1.5·Vg·i_d`  (`i_d` is coordinate `0`). -/
noncomputable def Pmeas (p : Params) (y : Fin 9 → ℝ) : ℝ := (3 / 2) * p.Vg * y 0

/-- §3: active-power error `e_P := P_ref − P_meas`.  By §4 this equals the seventh
inner-field component `F7`. -/
noncomputable def eP (p : Params) (y : Fin 9 → ℝ) : ℝ := p.P_ref - Pmeas p y

/-- §3: `Q_meas := −1.5·Vg·i_q`  (`i_q` is coordinate `1`). -/
noncomputable def Qmeas (p : Params) (y : Fin 9 → ℝ) : ℝ := -(3 / 2) * p.Vg * y 1

/-- §3: reactive-power error `e_Q := Q_ref − Q_meas`.  By §4 this equals the eighth
inner-field component `F8`. -/
noncomputable def eQ (p : Params) (y : Fin 9 → ℝ) : ℝ := p.Q_ref - Qmeas p y

/-- §4: the inner vector field `F_inner : ℝ⁹ → ℝ⁸`.  We carry it abstractly together
with the structural identities of §3–§4 used by the Power Lock and Corollary 0b: the
named components `F3 = e_d`, `F4 = e_q`, `F5 = v_cqc`, `F6 = −Kp_pll·v_cqc − Ki_pll·η − dw`,
`F7 = e_P`, `F8 = e_Q`.  The current-loop errors `e_d, e_q` and the PLL projection `v_cqc`
are carried as named quantities (their explicit §3 form is the rotation algebra, not
needed here). -/
structure InnerField (p : Params) where
  /-- The inner field `F_inner`. -/
  F : (Fin 9 → ℝ) → (Fin 8 → ℝ)
  /-- §3 current-loop d-axis error `e_d`. -/
  errD : (Fin 9 → ℝ) → ℝ
  /-- §3 current-loop q-axis error `e_q`. -/
  errQ : (Fin 9 → ℝ) → ℝ
  /-- §3 PLL projection `v_cqc`. -/
  vcqc : (Fin 9 → ℝ) → ℝ
  /-- §4: `F3 = e_d`. -/
  comp3 : ∀ y, F y 2 = errD y
  /-- §4: `F4 = e_q`. -/
  comp4 : ∀ y, F y 3 = errQ y
  /-- §4: `F5 = v_cqc`. -/
  comp5 : ∀ y, F y 4 = vcqc y
  /-- §4: `F6 = −Kp_pll·v_cqc − Ki_pll·η − dw`  (η = coordinate 4, dw = coordinate 8). -/
  comp6 : ∀ y, F y 5 = -p.Kp_pll * vcqc y - p.Ki_pll * y 4 - y 8
  /-- §4: `F7 = e_P`. -/
  comp7 : ∀ y, F y 6 = eP p y
  /-- §4: `F8 = e_Q`. -/
  comp8 : ∀ y, F y 7 = eQ p y

/-- An inner equilibrium: `F_inner y = 0` (§4; the frequency coordinate `dw = y 8`
is treated as a parameter of the inner block). -/
def IsInnerEquilibrium (p : Params) (S : InnerField p) (y : Fin 9 → ℝ) : Prop :=
  ∀ i, S.F y i = 0

/-- **Lemma 0 (Power Lock, §5) — the crux.**
At any inner equilibrium `e_P = 0`; hence `P_meas = P_ref` and `i_d = P_ref/(1.5·Vg)`.
Pure algebra: the seventh equilibrium equation is `F7 = e_P = 0`. -/
theorem powerLock (p : Params) (S : InnerField p) (y : Fin 9 → ℝ)
    (h : IsInnerEquilibrium p S y) :
    eP p y = 0 ∧ Pmeas p y = p.P_ref ∧ y 0 = p.P_ref / ((3 / 2) * p.Vg) := by
  -- F7 = e_P = 0 at equilibrium
  have h7 : eP p y = 0 := by rw [← S.comp7 y]; exact h 6
  -- P_meas = P_ref
  have hP : Pmeas p y = p.P_ref := by
    have h7' := h7; unfold eP at h7'; linarith
  -- i_d = P_ref / (1.5·Vg)
  have hVg : (3 / 2 : ℝ) * p.Vg ≠ 0 := ne_of_gt (by have := p.Vg_pos; positivity)
  refine ⟨h7, hP, ?_⟩
  have hmul : (3 / 2 : ℝ) * p.Vg * y 0 = p.P_ref := by
    have hP' := hP; unfold Pmeas at hP'; linarith
  rw [eq_div_iff hVg]; linear_combination hmul

/-- §5 / hypothesis W3.  A C¹ branch of inner equilibria parametrised by the grid
frequency offset `d = dw`.  `z d` is an inner equilibrium for every `d`. -/
structure EquilibriumBranch (p : Params) (S : InnerField p) where
  /-- The branch `d ↦ z*(d)`. -/
  z : ℝ → (Fin 9 → ℝ)
  /-- W3: every point of the branch is an inner equilibrium. -/
  isEq : ∀ d, IsInnerEquilibrium p S (z d)

/-- **Corollary 0a (§5).**  Along any equilibrium branch the `i_d` coordinate is pinned
to `P_ref/(1.5·Vg)` independently of `d`, and the active-power measurement is
identically `P_ref`.  Consequently the synchronising coefficient

    `K := d/dd [ P_meas(z*(d)) ] = 1.5·Vg · d(i_d*)/dd = 0`

is exactly zero (it is the derivative of a constant function). -/
theorem syncCoeff_zero (p : Params) (S : InnerField p) (B : EquilibriumBranch p S) :
    (∀ d, B.z d 0 = p.P_ref / ((3 / 2) * p.Vg)) ∧ (∀ d, Pmeas p (B.z d) = p.P_ref) :=
  ⟨fun d => (powerLock p S (B.z d) (B.isEq d)).2.2,
   fun d => (powerLock p S (B.z d) (B.isEq d)).2.1⟩

/-- **Corollary 0b (§5) — remaining equilibrium relations.**
At any inner equilibrium: the reactive Power Lock gives `i_q = −Q_ref/(1.5·Vg)`; the
current-loop errors and PLL projection vanish (`e_d = e_q = 0`, `v_cqc = 0`); and the
integrator state satisfies `η = −dw/Ki_pll` (from `F6 = 0` with `v_cqc = 0`). -/
theorem equilib_relations (p : Params) (S : InnerField p) (y : Fin 9 → ℝ)
    (h : IsInnerEquilibrium p S y) :
    y 1 = -p.Q_ref / ((3 / 2) * p.Vg) ∧
    S.errD y = 0 ∧ S.errQ y = 0 ∧ S.vcqc y = 0 ∧
    y 4 = -(y 8) / p.Ki_pll := by
  -- e_Q = 0 ⟹ i_q = −Q_ref/(1.5·Vg)
  have hQ : eQ p y = 0 := by rw [← S.comp8 y]; exact h 7
  have hVg : (3 / 2 : ℝ) * p.Vg ≠ 0 := ne_of_gt (by have := p.Vg_pos; positivity)
  have hiq : y 1 = -p.Q_ref / ((3 / 2) * p.Vg) := by
    have hQ' := hQ; unfold eQ Qmeas at hQ'
    rw [eq_div_iff hVg]; linear_combination hQ'
  -- e_d = e_q = v_cqc = 0  (they are the vanishing field components F3, F4, F5)
  have hed : S.errD y = 0 := by rw [← S.comp3 y]; exact h 2
  have heq : S.errQ y = 0 := by rw [← S.comp4 y]; exact h 3
  have hv  : S.vcqc y = 0 := by rw [← S.comp5 y]; exact h 4
  -- η = −dw/Ki_pll  (from F6 = 0 and v_cqc = 0)
  have h6 : -p.Kp_pll * S.vcqc y - p.Ki_pll * y 4 - y 8 = 0 := by rw [← S.comp6 y]; exact h 5
  have hKi : p.Ki_pll ≠ 0 := ne_of_gt p.Ki_pll_pos
  have hη : y 4 = -(y 8) / p.Ki_pll := by
    rw [eq_div_iff hKi]; rw [hv] at h6; linear_combination -h6
  exact ⟨hiq, hed, heq, hv, hη⟩

/-- §4: swing-anchored extra component `F9_S := κ·e_P − b·dw` (Variant S). -/
noncomputable def F9S (p : Params) (y : Fin 9 → ℝ) : ℝ := p.kappa * eP p y - p.b * y 8

/-- A Variant-S equilibrium: an inner equilibrium that additionally zeroes `F9_S`. -/
def IsVariantSEquilibrium (p : Params) (S : InnerField p) (y : Fin 9 → ℝ) : Prop :=
  IsInnerEquilibrium p S y ∧ F9S p y = 0

/-- **Corollary 0b (§5), Variant S.**  At a swing-anchored equilibrium `dw* = 0`:
`F9_S = 0` with `e_P = 0` gives `b·dw = 0`, and `b = D/(2H) > 0`. -/
theorem variantS_dw_zero (p : Params) (S : InnerField p) (y : Fin 9 → ℝ)
    (h : IsVariantSEquilibrium p S y) : y 8 = 0 := by
  have hP : eP p y = 0 := (powerLock p S y h.1).1
  have h9 := h.2
  rw [F9S, hP] at h9              -- κ·0 − b·dw = 0
  have hbdw : p.b * y 8 = 0 := by linarith
  exact (mul_eq_zero.mp hbdw).resolve_left (ne_of_gt p.b_pos)

end GFL
