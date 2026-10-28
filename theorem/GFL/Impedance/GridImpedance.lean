import theorem.Circuits.Interconnection
import theorem.GFL.Impedance.Algebra
import theorem.Transform.Park

/-! # State-space realization of the grid-side impedance `Z_ext`

Model boundary.
The network seen from the PCC of a grid-following converter (work-sync
T-gfl-impedance §1.7): series line `L_g, R_g` to a stiff grid (voltage perturbation zero) in
parallel with a shunt `R_l ∥ C` load at the PCC, dq frame rotating at `ω`, small-signal,
continuous time. State order `(w_d, w_q, i_line,d, i_line,q)` (block index `Fin 2 ⊕ Fin 2`, read
on `Fin 4` through `finSumFinEquiv` by the plant `networkModel`) with
`w = −v_PCC` and `i_line` flowing from the grid into the PCC; input `u` = current drawn by the
converter (IN-positive), output `w = −v_PCC`:
`C w' = u − i_line − w/R_l − ωC J w`, `L_g i_line' = w − R_g i_line − ωL_g J i_line`.
The capacitor carries the dq cross term `ωC J` (`Transform.capacitor_dq`), which the note omits.

Source: work-sync `theory/T-gfl-impedance.md` §1.7; `theory/T-gfl-control.md` §1.7.

Results.
* `networkModel_D`: the realization has no feedthrough (strictly proper).
* `networkBlocks_field`: the block equations are the PCC KCL and the line KVL.
* `networkModel_transfer`: off the characteristic roots and with `det Z_line ≠ 0`, its transfer
  matrix is exactly the corrected `Z_ext = (Z_line⁻¹ + Y_load)⁻¹` of `Algebra.lean`.
* `withNetwork`, `withNetwork_sourceImpedance`: so the network is an admissible `source` of
  `Circuits.Interconnection`, with any strictly proper converter admittance realization
  (`D = 0`, e.g. a GFL admittance) as `load`; the interconnection's source impedance is `Z_ext`
  and its return difference is `det(I + Z_ext Y)`.

These are realization identities (static evidence); the behaviour of the interconnection is
that of the family `Circuits.Interconnection.family`, not restated here.
-/

noncomputable section
namespace powerlib.GFL.Impedance
open Matrix Linear

/-- State index of the blocks: `(w_d, w_q)` then `(i_line,d, i_line,q)`. -/
abbrev NetIdx := Fin 2 ⊕ Fin 2

/-- Block state matrix of the network. -/
def networkA (Lg Rg Rl C ω : ℝ) : Matrix NetIdx NetIdx ℝ :=
  fromBlocks (-(1 / (Rl * C)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ω • Transform.J)
    (-(1 / C) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ((1 / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (-(Rg / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ω • Transform.J)

/-- Block input matrix: the converter current enters the PCC capacitor. -/
def networkB (C : ℝ) : Matrix NetIdx (Fin 2) ℝ :=
  fromRows ((1 / C) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0

/-- Block output matrix: the output is `w = −v_PCC`. -/
def networkC : Matrix (Fin 2) NetIdx ℝ := fromCols (1 : Matrix (Fin 2) (Fin 2) ℝ) 0

/-- Realization of the network impedance seen from the PCC, on `Fin 4` states. -/
def networkModel (Lg Rg Rl C ω : ℝ) : Plant 4 2 :=
  ⟨(networkA Lg Rg Rl C ω).reindex finSumFinEquiv finSumFinEquiv,
    (networkB C).reindex finSumFinEquiv (Equiv.refl _),
    networkC.reindex (Equiv.refl _) finSumFinEquiv, 0⟩

@[tmio M, powerlib_foundation] theorem networkModel_D (Lg Rg Rl C ω : ℝ) :
    (networkModel Lg Rg Rl C ω).D = 0 := rfl

/-- The block equations are the PCC KCL and the line KVL. -/
@[powerlib_foundation] theorem networkBlocks_field {Lg Rg Rl C ω : ℝ} (hC : C ≠ 0)
    (hL : Lg ≠ 0) (w l u : Fin 2 → ℝ) :
    networkA Lg Rg Rl C ω *ᵥ Sum.elim w l + networkB C *ᵥ u =
      Sum.elim (C⁻¹ • (u - l - Rl⁻¹ • w - (ω * C) • (Transform.J *ᵥ w)))
        (Lg⁻¹ • (w - Rg • l - (ω * Lg) • (Transform.J *ᵥ l))) := by
  ext (k | k) <;> fin_cases k <;>
    simp [networkA, networkB, fromBlocks_mulVec, fromRows_mulVec, Transform.J,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply, Matrix.vecHead,
      Matrix.vecTail] <;>
    field_simp <;> ring

/-- The plant's characteristic determinant is the block one. -/
@[powerlib_foundation] theorem det_characteristicMatrix_networkModel (Lg Rg Rl C ω : ℝ)
    (s : ℂ) : (characteristicMatrix (networkModel Lg Rg Rl C ω).A s).det =
      (characteristicMatrix (networkA Lg Rg Rl C ω) s).det := by
  change (characteristicMatrix ((networkA Lg Rg Rl C ω).reindex _ _) s).det = _
  rw [characteristicMatrix_reindex, Matrix.det_reindex_self]

private lemma charMatrix_blocks (Lg Rg Rl C ω : ℝ) (s : ℂ) :
    characteristicMatrix (networkA Lg Rg Rl C ω) s =
      fromBlocks (s • 1 - complexify (-(1 / (Rl * C)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
          ω • Transform.J))
        (-complexify (-(1 / C) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
        (-complexify ((1 / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
        (s • 1 - complexify (-(Rg / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
          ω • Transform.J)) := by
  have hone : (s • (1 : Matrix NetIdx NetIdx ℂ)) = fromBlocks (s • 1) 0 0 (s • 1) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    simp only [smul_zero]
  rw [characteristicMatrix, hone]
  change fromBlocks (s • 1) 0 0 (s • 1) - complexify (fromBlocks _ _ _ _) = _
  rw [complexify_fromBlocks, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

private lemma block11 {Rl C ω : ℝ} (hC : C ≠ 0) (s : ℂ) :
    (C : ℂ) • (s • 1 - complexify (-(1 / (Rl * C)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
      ω • Transform.J)) = Yload Rl C ω s := by
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Yload, Jc, Transform.J] <;> field_simp <;> ring

private lemma block22 {Lg Rg ω : ℝ} (hL : Lg ≠ 0) (s : ℂ) :
    (Lg : ℂ) • (s • 1 - complexify (-(Rg / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
      ω • Transform.J)) = Zoc Lg Rg ω s := by
  have hL' : (Lg : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [Zoc_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Transform.J] <;> field_simp

/-- The realization's transfer matrix is the corrected `Z_ext`. -/
@[powerlib_foundation] theorem networkModel_transfer {Lg Rg Rl C ω : ℝ} (hC : C ≠ 0)
    (hL : Lg ≠ 0) {s : ℂ}
    (hM : (characteristicMatrix (networkModel Lg Rg Rl C ω).A s).det ≠ 0)
    (hZ : (Zoc Lg Rg ω s).det ≠ 0) :
    transfer (networkModel Lg Rg Rl C ω) s = Zext Lg Rg Rl C ω s := by
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hL' : (Lg : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [det_characteristicMatrix_networkModel] at hM
  rw [transfer_eq_transferOf]
  change transferOf ((networkA Lg Rg Rl C ω).reindex finSumFinEquiv finSumFinEquiv)
    ((networkB C).reindex finSumFinEquiv (Equiv.refl _))
    (networkC.reindex (Equiv.refl _) finSumFinEquiv) 0 s = _
  rw [transferOf_reindex]
  set M := characteristicMatrix (networkA Lg Rg Rl C ω) s with hMdef
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hMX := Matrix.mul_nonsing_inv_cancel_left M (complexify (networkB C)) hMu
  generalize hX : M⁻¹ * complexify (networkB C) = X at hMX
  obtain ⟨X₁, X₂, rfl⟩ : ∃ X₁ X₂, X = fromRows X₁ X₂ :=
    ⟨X.toRows₁, X.toRows₂, (fromRows_toRows X).symm⟩
  rw [hMdef, charMatrix_blocks, fromBlocks_mul_fromRows] at hMX
  have hB : complexify (networkB C) =
      fromRows ((1 / C : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 := by
    simp only [networkB, complexify_fromRows, complexify_zero]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hB] at hMX
  obtain ⟨E₁, E₂⟩ := fromRows_inj hMX
  -- the transfer matrix is the first block row of `X`
  have htr : transferOf (networkA Lg Rg Rl C ω) (networkB C) networkC 0 s = X₁ := by
    rw [transferOf, Matrix.mul_assoc, ← hMdef, hX]
    simp only [networkC, complexify_fromCols, complexify_zero, add_zero]
    have : complexify (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero]
  rw [htr]
  -- second block row: `Z_line X₂ = X₁`
  have hcL : complexify ((1 / Lg) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      (1 / Lg : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hcC : complexify (-(1 / C) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
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
def withNetwork {n₂ : ℕ} (Lg Rg Rl C ω : ℝ) (load : Plant n₂ 2) (hD : load.D = 0) :
    Circuits.Interconnection 4 n₂ 2 :=
  ⟨networkModel Lg Rg Rl C ω, load, hD⟩

@[powerlib_foundation] theorem withNetwork_sourceImpedance {n₂ : ℕ} {Lg Rg Rl C ω : ℝ}
    (hC : C ≠ 0) (hL : Lg ≠ 0) (load : Plant n₂ 2) (hD : load.D = 0) {s : ℂ}
    (hM : (characteristicMatrix (networkModel Lg Rg Rl C ω).A s).det ≠ 0)
    (hZ : (Zoc Lg Rg ω s).det ≠ 0) :
    (withNetwork Lg Rg Rl C ω load hD).sourceImpedance s = Zext Lg Rg Rl C ω s :=
  networkModel_transfer hC hL hM hZ

@[powerlib_foundation] theorem withNetwork_returnDifference {n₂ : ℕ} {Lg Rg Rl C ω : ℝ}
    (hC : C ≠ 0) (hL : Lg ≠ 0) (load : Plant n₂ 2) (hD : load.D = 0) {s : ℂ}
    (hM : (characteristicMatrix (networkModel Lg Rg Rl C ω).A s).det ≠ 0)
    (hZ : (Zoc Lg Rg ω s).det ≠ 0) :
    (withNetwork Lg Rg Rl C ω load hD).returnDifference s =
      (1 + Zext Lg Rg Rl C ω s * transfer load s).det := by
  rw [Circuits.Interconnection.returnDifference,
    withNetwork_sourceImpedance hC hL load hD hM hZ]
  rfl

end powerlib.GFL.Impedance
