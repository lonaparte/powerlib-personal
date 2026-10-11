import theorem.ImpedanceStability
import theorem.CurrentControl.ImpedanceAlgebra

/-! # State-space realization of the grid-side impedance `Z_ext` (foundation)

Model: the network seen from the PCC of a grid-following converter (work-sync
T-gfl-impedance §1.7): series line `L_g, R_g` to a stiff grid (voltage perturbation zero) in
parallel with a shunt `R_l ∥ C` load at the PCC, dq frame rotating at `ω`, small-signal,
continuous time. State order `(w_d, w_q, i_line,d, i_line,q)` (index `Fin 2 ⊕ Fin 2`) with
`w = −v_PCC` and `i_line` flowing from the grid into the PCC; input `u` = current drawn by the
converter (IN-positive), output `w = −v_PCC`:
`C w' = u − i_line − w/R_l − ωC J w`, `L_g i_line' = w − R_g i_line − ωL_g J i_line`.
The capacitor carries the dq cross term `ωC J` (`capacitor_dq`), which the note omits.

* `networkModel_D`: the realization has no feedthrough (strictly proper).
* `networkModel_transfer`: off the characteristic roots and with `det Z_line ≠ 0`, its transfer
  matrix is exactly the corrected `Z_ext = (Z_line⁻¹ + Y_load)⁻¹` of `ImpedanceAlgebra.lean`.
* `withNetwork`, `withNetwork_sourceImpedance`: so the network is an admissible `source` of
  `ImpedanceCriterion.Interconnection`, with any strictly proper converter admittance
  realization (`D = 0`, e.g. a GFL admittance) as `load`; the interconnection's source
  impedance is `Z_ext` and its return difference is `det(I + Z_ext Y)`.

Source: work-sync `theory/T-gfl-impedance.md` §1.7; `theory/T-gfl-control.md` §1.7.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix

/-- State index: `(w_d, w_q)` then `(i_line,d, i_line,q)`. -/
abbrev NetIdx := Fin 2 ⊕ Fin 2

/-- Realization of the network impedance seen from the PCC. -/
def networkModel (Lg Rg Rl C ω : ℝ) : LTI.Model NetIdx (Fin 2) :=
  ⟨fromBlocks (-(1 / (Rl * C)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ω • Transform.J)
      (-(1 / C) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ((1 / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (-(Rg / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ω • Transform.J),
    fromRows ((1 / C) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0,
    fromCols (1 : Matrix (Fin 2) (Fin 2) ℝ) 0, 0⟩

@[powerlib_foundation] theorem networkModel_D (Lg Rg Rl C ω : ℝ) :
    (networkModel Lg Rg Rl C ω).D = 0 := rfl

/-- The realization is the PCC KCL and the line KVL. -/
@[powerlib_foundation] theorem networkModel_field {Lg Rg Rl C ω : ℝ} (hC : C ≠ 0)
    (hL : Lg ≠ 0) (w l u : Fin 2 → ℝ) :
    (networkModel Lg Rg Rl C ω).field (Sum.elim w l) u =
      Sum.elim (C⁻¹ • (u - l - Rl⁻¹ • w - (ω * C) • (Transform.J *ᵥ w)))
        (Lg⁻¹ • (w - Rg • l - (ω * Lg) • (Transform.J *ᵥ l))) := by
  ext (k | k) <;> fin_cases k <;>
    simp [networkModel, LTI.Model.field, fromBlocks_mulVec, fromRows_mulVec, Transform.J,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply, Matrix.vecHead,
      Matrix.vecTail] <;>
    field_simp <;> ring

@[powerlib_foundation] private lemma charMatrix_blocks (Lg Rg Rl C ω : ℝ) (s : ℂ) :
    LTI.characteristicMatrix (networkModel Lg Rg Rl C ω).A s =
      fromBlocks (s • 1 - LTI.complexify (-(1 / (Rl * C)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
          ω • Transform.J))
        (-LTI.complexify (-(1 / C) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
        (-LTI.complexify ((1 / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
        (s • 1 - LTI.complexify (-(Rg / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
          ω • Transform.J)) := by
  have hone : (s • (1 : Matrix NetIdx NetIdx ℂ)) = fromBlocks (s • 1) 0 0 (s • 1) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    simp only [smul_zero]
  rw [LTI.characteristicMatrix, hone]
  change fromBlocks (s • 1) 0 0 (s • 1) - LTI.complexify (fromBlocks _ _ _ _) = _
  rw [LTI.complexify_fromBlocks, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

@[powerlib_foundation] private lemma block11 {Rl C ω : ℝ} (hC : C ≠ 0) (s : ℂ) :
    (C : ℂ) • (s • 1 - LTI.complexify (-(1 / (Rl * C)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
      ω • Transform.J)) = Yload Rl C ω s := by
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Yload, Jc, Transform.J] <;> field_simp <;> ring

@[powerlib_foundation] private lemma block22 {Lg Rg ω : ℝ} (hL : Lg ≠ 0) (s : ℂ) :
    (Lg : ℂ) • (s • 1 - LTI.complexify (-(Rg / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
      ω • Transform.J)) = Zoc Lg Rg ω s := by
  have hL' : (Lg : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [Zoc_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Transform.J] <;> field_simp

/-- The realization's transfer matrix is the corrected `Z_ext`. -/
@[powerlib_foundation] theorem networkModel_transfer {Lg Rg Rl C ω : ℝ} (hC : C ≠ 0)
    (hL : Lg ≠ 0) {s : ℂ}
    (hM : (LTI.characteristicMatrix (networkModel Lg Rg Rl C ω).A s).det ≠ 0)
    (hZ : (Zoc Lg Rg ω s).det ≠ 0) :
    LTI.transfer (networkModel Lg Rg Rl C ω) s = Zext Lg Rg Rl C ω s := by
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hL' : (Lg : ℂ) ≠ 0 := by exact_mod_cast hL
  set M := LTI.characteristicMatrix (networkModel Lg Rg Rl C ω).A s with hMdef
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hMX := Matrix.mul_nonsing_inv_cancel_left M
    (LTI.complexify (networkModel Lg Rg Rl C ω).B) hMu
  generalize hX : M⁻¹ * LTI.complexify (networkModel Lg Rg Rl C ω).B = X at hMX
  obtain ⟨X₁, X₂, rfl⟩ : ∃ X₁ X₂, X = fromRows X₁ X₂ :=
    ⟨X.toRows₁, X.toRows₂, (fromRows_toRows X).symm⟩
  rw [hMdef, charMatrix_blocks, fromBlocks_mul_fromRows] at hMX
  have hB : LTI.complexify (networkModel Lg Rg Rl C ω).B =
      fromRows ((1 / C : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 := by
    simp only [networkModel, LTI.complexify_fromRows, LTI.complexify_zero]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hB] at hMX
  obtain ⟨E₁, E₂⟩ := fromRows_inj hMX
  -- the transfer matrix is the first block row of `X`
  have htr : LTI.transfer (networkModel Lg Rg Rl C ω) s = X₁ := by
    rw [LTI.transfer, Matrix.mul_assoc, ← hMdef, hX]
    simp only [networkModel, LTI.complexify_fromCols, LTI.complexify_zero, add_zero]
    have : LTI.complexify (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero]
  rw [htr]
  -- second block row: `Z_line X₂ = X₁`
  have hcL : LTI.complexify ((1 / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      (1 / Lg : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hcC : LTI.complexify (-(1 / C) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      (-(1 / C) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hcL] at E₂
  rw [hcC] at E₁
  have hZX : Zoc Lg Rg ω s * X₂ = X₁ := by
    rw [← block22 hL s, Matrix.smul_mul]
    rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul, neg_add_eq_zero] at E₂
    rw [← E₂, smul_smul, mul_one_div_cancel hL', one_smul]
  have hX2 : X₂ = (Zoc Lg Rg ω s)⁻¹ * X₁ := by
    rw [← hZX, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hZ),
      Matrix.one_mul]
  -- first block row: `Y_load X₁ + X₂ = 1`
  have hYX : Yload Rl C ω s * X₁ + X₂ = 1 := by
    rw [← block11 hC s, Matrix.smul_mul]
    have h2 : -(-(1 / (C : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * X₂ = (1 / (C : ℂ)) • X₂ := by
      rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul, neg_smul, neg_neg]
    rw [h2] at E₁
    have := congrArg (fun Y => (C : ℂ) • Y) E₁
    simp only [smul_add, smul_smul, mul_one_div_cancel hC', one_smul] at this
    exact this
  rw [Zext]
  symm
  apply Matrix.inv_eq_right_inv
  rw [Matrix.add_mul, ← hX2, add_comm]
  exact hYX

/-- The network as the source of an impedance interconnection with a strictly proper
converter admittance as the load. -/
def withNetwork {ι : Type*} (Lg Rg Rl C ω : ℝ) (load : LTI.Model ι (Fin 2))
    (hD : load.D = 0) : ImpedanceCriterion.Interconnection NetIdx ι (Fin 2) :=
  ⟨networkModel Lg Rg Rl C ω, load, hD⟩

@[powerlib_foundation] theorem withNetwork_sourceImpedance {ι : Type*} [Fintype ι]
    [DecidableEq ι] {Lg Rg Rl C ω : ℝ} (hC : C ≠ 0) (hL : Lg ≠ 0)
    (load : LTI.Model ι (Fin 2)) (hD : load.D = 0) {s : ℂ}
    (hM : (LTI.characteristicMatrix (networkModel Lg Rg Rl C ω).A s).det ≠ 0)
    (hZ : (Zoc Lg Rg ω s).det ≠ 0) :
    (withNetwork Lg Rg Rl C ω load hD).sourceImpedance s = Zext Lg Rg Rl C ω s :=
  networkModel_transfer hC hL hM hZ

@[powerlib_foundation] theorem withNetwork_returnDifference {ι : Type*} [Fintype ι]
    [DecidableEq ι] {Lg Rg Rl C ω : ℝ} (hC : C ≠ 0) (hL : Lg ≠ 0)
    (load : LTI.Model ι (Fin 2)) (hD : load.D = 0) {s : ℂ}
    (hM : (LTI.characteristicMatrix (networkModel Lg Rg Rl C ω).A s).det ≠ 0)
    (hZ : (Zoc Lg Rg ω s).det ≠ 0) :
    (withNetwork Lg Rg Rl C ω load hD).returnDifference s =
      (1 + Zext Lg Rg Rl C ω s * LTI.transfer load s).det := by
  rw [ImpedanceCriterion.Interconnection.returnDifference,
    withNetwork_sourceImpedance hC hL load hD hM hZ]
  rfl

end powerlib.CurrentControl
