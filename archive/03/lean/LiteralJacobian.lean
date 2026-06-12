/-
  P1-inv — a GENUINE reduction of "∂F/∂z is invertible" (W2 for the literal model).

  STATUS: PARTIAL, honest.  Not a proof of invertibility — a *rigorous reduction*.

  The `e_P` and `e_Q` rows of the literal inner field are sparse (machine-checked):
  `F7 = e_P` depends only on `i_d`, `F8 = e_Q` only on `i_q`.  So the corresponding rows of the
  inner Jacobian `∂F/∂z` each have a single nonzero entry `∓1.5·Vg`.  This file proves those two
  rows exactly (`innerJac_eP_row`, `innerJac_eQ_row`).

  Consequence (documented, not yet glued): cofactor/Schur reduction on these two rows gives
  `det(∂F/∂z) = ±(1.5·Vg)² · det(M₆)`, where `M₆` is the 6×6 controller/PLL block.  So W2 reduces to
  `det(M₆) ≠ 0` — the densely-coupled controller block, which is the remaining (un-done) work.  No
  `sorry`; nothing here claims invertibility.
-/
import GFL.LiteralModel
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace GFL

open Matrix

/-- The literal inner field as a function of the inner state `z : Fin 8 → ℝ` alone, with the grid
frequency offset `dw` fixed (it is coordinate 8).  `∂F/∂z` (W2) is the derivative of this map. -/
noncomputable def innerFieldZ (p : Params) (q : LitParams) (dw : ℝ) (z : Fin 8 → ℝ) : Fin 8 → ℝ :=
  F_inner_literal p q (Fin.snoc z dw)

/-- `F7 = e_P` as a function of `z`: `P_ref − 1.5·Vg·i_d` (depends on `z 0` only). -/
theorem innerFieldZ_eP (p : Params) (q : LitParams) (dw : ℝ) (z : Fin 8 → ℝ) :
    innerFieldZ p q dw z 6 = p.P_ref - (3 / 2) * p.Vg * z 0 := by
  have h0 : (Fin.snoc z dw : Fin 9 → ℝ) 0 = z 0 := by
    rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
  rw [innerFieldZ, litF_eP_eq, h0]

/-- `F8 = e_Q` as a function of `z`: `Q_ref − (−1.5·Vg·i_q)` (depends on `z 1` only). -/
theorem innerFieldZ_eQ (p : Params) (q : LitParams) (dw : ℝ) (z : Fin 8 → ℝ) :
    innerFieldZ p q dw z 7 = p.Q_ref - -(3 / 2) * p.Vg * z 1 := by
  have h1 : (Fin.snoc z dw : Fin 9 → ℝ) 1 = z 1 := by
    rw [show (1 : Fin 9) = Fin.castSucc (1 : Fin 8) from rfl, Fin.snoc_castSucc]
  rw [innerFieldZ, litF_eQ_eq, h1]

/-- The literal inner Jacobian `∂F/∂z` at `z₀`: entry `(i,j)` is the partial `∂Fᵢ/∂zⱼ`. -/
noncomputable def innerJac (p : Params) (q : LitParams) (dw : ℝ) (z₀ : Fin 8 → ℝ) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => fderiv ℝ (fun z => innerFieldZ p q dw z i) z₀ (Pi.single j 1)

/-- **`e_P` row of `∂F/∂z` (exact).**  `∂(e_P)/∂zⱼ = −1.5·Vg` if `j = 0`, else `0`. -/
theorem innerJac_eP_row (p : Params) (q : LitParams) (dw : ℝ) (z₀ : Fin 8 → ℝ) (j : Fin 8) :
    innerJac p q dw z₀ 6 j = -((3 / 2) * p.Vg) * (Pi.single (0 : Fin 8) (1 : ℝ) : Fin 8 → ℝ) j := by
  have hfun : (fun z => innerFieldZ p q dw z 6) = fun z => p.P_ref - (3 / 2) * p.Vg * z 0 :=
    funext (innerFieldZ_eP p q dw)
  have hp : HasFDerivAt (fun z : Fin 8 → ℝ => z 0)
      (ContinuousLinearMap.proj (0 : Fin 8) : (Fin 8 → ℝ) →L[ℝ] ℝ) z₀ :=
    (ContinuousLinearMap.proj (0 : Fin 8) : (Fin 8 → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have hd := (hp.const_mul ((3 / 2) * p.Vg)).const_sub p.P_ref
  rw [innerJac, hfun, hd.fderiv]
  by_cases h : j = 0
  · subst h; simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply]
  · simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_of_ne h, Pi.single_eq_of_ne (Ne.symm h)]

/-- **`e_Q` row of `∂F/∂z` (exact).**  `∂(e_Q)/∂zⱼ = 1.5·Vg` if `j = 1`, else `0`. -/
theorem innerJac_eQ_row (p : Params) (q : LitParams) (dw : ℝ) (z₀ : Fin 8 → ℝ) (j : Fin 8) :
    innerJac p q dw z₀ 7 j = -(-(3 / 2) * p.Vg) * (Pi.single (1 : Fin 8) (1 : ℝ) : Fin 8 → ℝ) j := by
  have hfun : (fun z => innerFieldZ p q dw z 7) = fun z => p.Q_ref - -(3 / 2) * p.Vg * z 1 :=
    funext (innerFieldZ_eQ p q dw)
  have hp : HasFDerivAt (fun z : Fin 8 → ℝ => z 1)
      (ContinuousLinearMap.proj (1 : Fin 8) : (Fin 8 → ℝ) →L[ℝ] ℝ) z₀ :=
    (ContinuousLinearMap.proj (1 : Fin 8) : (Fin 8 → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have hd := (hp.const_mul (-(3 / 2) * p.Vg)).const_sub p.Q_ref
  rw [innerJac, hfun, hd.fderiv]
  by_cases h : j = 1
  · subst h; simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply]
  · simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_of_ne h, Pi.single_eq_of_ne (Ne.symm h)]

end GFL
