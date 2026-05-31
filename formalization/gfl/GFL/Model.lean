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
  Vg    : ℝ
  P_ref : ℝ
  wn    : ℝ
  H     : ℝ
  D     : ℝ
  Sn    : ℝ
  Vg_pos   : 0 < Vg
  wn_pos   : 0 < wn
  H_pos    : 0 < H
  D_pos    : 0 < D
  Sn_pos   : 0 < Sn
  Pref_pos : 0 < P_ref

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

/-- §4: the inner vector field `F_inner : ℝ⁹ → ℝ⁸`.  We carry it abstractly together
with the single structural identity used by the Power Lock: its seventh component
(0-based index `6`) is `e_P` (this is the definition `F7 = e_P` of §3–§4). -/
structure InnerField (p : Params) where
  /-- The inner field `F_inner`. -/
  F : (Fin 9 → ℝ) → (Fin 8 → ℝ)
  /-- §4: `F7 = e_P`. -/
  comp7 : ∀ y, F y 6 = eP p y

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

end GFL
