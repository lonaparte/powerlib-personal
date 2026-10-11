import theorem.PortHamiltonian
import theorem.Transform.Park

/-! # Composition of port-Hamiltonian systems (foundation layer)

* Power-preserving interconnection (T-ph §1.5, (1.9)–(1.10)), linear diagonal version.
  Two `PortHamiltonian.Model`s `m₁ : Model ι₁ κ₁`, `m₂ : Model ι₂ κ₂` are coupled by
  `u₁ = −Mᵀ y₂ + g₁ u`, `u₂ = M y₁ + g₂ u` (`M : κ₂ × κ₁`, external input `u : κ → ℝ`).
  The composite is again a `PortHamiltonian.Model (ι₁ ⊕ ι₂) κ` with
  `J = [[J₁, −B₁ Mᵀ B₂ᵀ], [B₂ M B₁ᵀ, J₂]]`, `R = blkdiag(R₁, R₂)`, `H = H₁ + H₂`,
  `B = [B₁ g₁; B₂ g₂]`; its field restricts to the two subsystem fields under the coupling law,
  its trajectories project to subsystem trajectories, and it is passive (compositionality).
* Block structure (T-power-system-ph §1.4–§1.5.2): block-diagonal PSD dissipation, adding
  skew pairs keeps `J` skew, adding a nonnegative diagonal (constant-impedance loads) keeps
  `R ⪰ 0`.
* Frame rotation (T-power-system-ph §1.2): `R(δ)` is orthogonal, so `v·i` is frame invariant.
* Kron reduction (T-power-system-ph §1.7): eliminating internal nodes with zero injection
  from a linear resistive network `Y` gives `i_b = (Y_bb − Y_bi Y_ii⁻¹ Y_ib) v_b`, conserves
  the port power, and (Mathlib Schur complement) keeps a PSD network PSD.
* State dimension (T-power-system-ph §1.8): `7N + ℓ + n_C`.

These are algebraic statements; they carry no claim about a particular grid.

Source: work-sync `theory/T-ph.md` §1.5 (1.9)–(1.10);
`theory/T-power-system-ph.md` §1.2, §1.4, §1.5, §1.5.2, §1.7, §1.8.
-/

noncomputable section
namespace powerlib.PH
open Matrix Set

/-! ## Power-preserving interconnection -/

section Interconnection

variable {ι₁ ι₂ κ₁ κ₂ κ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Fintype κ₁] [Fintype κ₂] [Fintype κ]

/-- The power-preserving interconnection (1.9) of two linear pH models, written as one pH
model (1.10). -/
def interconnect (m₁ : PortHamiltonian.Model ι₁ κ₁) (m₂ : PortHamiltonian.Model ι₂ κ₂)
    (Mc : Matrix κ₂ κ₁ ℝ) (g₁ : Matrix κ₁ κ ℝ) (g₂ : Matrix κ₂ κ ℝ) :
    PortHamiltonian.Model (ι₁ ⊕ ι₂) κ where
  J := fromBlocks m₁.J (-(m₁.B * Mcᵀ * m₂.Bᵀ)) (m₂.B * Mc * m₁.Bᵀ) m₂.J
  d := Sum.elim m₁.d m₂.d
  w := Sum.elim m₁.w m₂.w
  B := fromRows (m₁.B * g₁) (m₂.B * g₂)
  skew := by
    rw [fromBlocks_transpose, fromBlocks_neg, m₁.skew, m₂.skew]
    congr 1 <;> simp [transpose_mul, Matrix.mul_assoc]
  damping_nonneg := by
    rintro (i | i)
    · exact m₁.damping_nonneg i
    · exact m₂.damping_nonneg i
  weights_pos := by
    rintro (i | i)
    · exact m₁.weights_pos i
    · exact m₂.weights_pos i

variable (m₁ : PortHamiltonian.Model ι₁ κ₁) (m₂ : PortHamiltonian.Model ι₂ κ₂)
  (Mc : Matrix κ₂ κ₁ ℝ) (g₁ : Matrix κ₁ κ ℝ) (g₂ : Matrix κ₂ κ ℝ)

omit [DecidableEq ι₁] [DecidableEq ι₂] [Fintype ι₁] [Fintype ι₂] [Fintype κ] in
@[powerlib_foundation] theorem interconnect_gradient (x : ι₁ ⊕ ι₂ → ℝ) :
    PortHamiltonian.gradient (interconnect m₁ m₂ Mc g₁ g₂) x =
      Sum.elim (PortHamiltonian.gradient m₁ (x ∘ Sum.inl))
        (PortHamiltonian.gradient m₂ (x ∘ Sum.inr)) := by
  ext (i | i) <;> rfl

omit [Fintype ι₁] [Fintype ι₂] [Fintype κ] in
@[powerlib_foundation] theorem interconnect_stateMatrix_sub :
    (interconnect m₁ m₂ Mc g₁ g₂).J - diagonal (interconnect m₁ m₂ Mc g₁ g₂).d =
      fromBlocks (m₁.J - diagonal m₁.d) (-(m₁.B * Mcᵀ * m₂.Bᵀ)) (m₂.B * Mc * m₁.Bᵀ)
        (m₂.J - diagonal m₂.d) := by
  ext (i | i) (j | j) <;> simp [interconnect, diagonal_apply]

/-- (1.10) restricted to the first block is the first subsystem driven by
`u₁ = −Mᵀ y₂ + g₁ u`. -/
@[powerlib_foundation] theorem interconnect_field_inl (x : ι₁ ⊕ ι₂ → ℝ) (u : κ → ℝ) :
    (PortHamiltonian.field (interconnect m₁ m₂ Mc g₁ g₂) x u) ∘ Sum.inl =
      PortHamiltonian.field m₁ (x ∘ Sum.inl)
        (-(Mcᵀ *ᵥ PortHamiltonian.output m₂ (x ∘ Sum.inr)) + g₁ *ᵥ u) := by
  have hB : (interconnect m₁ m₂ Mc g₁ g₂).B = fromRows (m₁.B * g₁) (m₂.B * g₂) := rfl
  rw [PortHamiltonian.field, interconnect_stateMatrix_sub, interconnect_gradient, hB,
    fromBlocks_mulVec, fromRows_mulVec]
  simp only [Function.comp_def, Pi.add_apply, Sum.elim_inl, Sum.elim_inr, PortHamiltonian.field,
    PortHamiltonian.output]
  ext i
  simp only [Pi.add_apply, neg_mulVec, mulVec_add, mulVec_neg, ← mulVec_mulVec]
  abel

/-- (1.10) restricted to the second block is the second subsystem driven by
`u₂ = M y₁ + g₂ u`. -/
@[powerlib_foundation] theorem interconnect_field_inr (x : ι₁ ⊕ ι₂ → ℝ) (u : κ → ℝ) :
    (PortHamiltonian.field (interconnect m₁ m₂ Mc g₁ g₂) x u) ∘ Sum.inr =
      PortHamiltonian.field m₂ (x ∘ Sum.inr)
        (Mc *ᵥ PortHamiltonian.output m₁ (x ∘ Sum.inl) + g₂ *ᵥ u) := by
  have hB : (interconnect m₁ m₂ Mc g₁ g₂).B = fromRows (m₁.B * g₁) (m₂.B * g₂) := rfl
  rw [PortHamiltonian.field, interconnect_stateMatrix_sub, interconnect_gradient, hB,
    fromBlocks_mulVec, fromRows_mulVec]
  simp only [Function.comp_def, Pi.add_apply, Sum.elim_inl, Sum.elim_inr, PortHamiltonian.field,
    PortHamiltonian.output]
  ext i
  simp only [Pi.add_apply, mulVec_add, ← mulVec_mulVec]
  abel

omit [DecidableEq ι₁] [DecidableEq ι₂] [Fintype κ] in
/-- `H^tot = H₁ + H₂`. -/
@[powerlib_foundation] theorem interconnect_energy (x : ι₁ ⊕ ι₂ → ℝ) :
    PortHamiltonian.energy (interconnect m₁ m₂ Mc g₁ g₂) x =
      PortHamiltonian.energy m₁ (x ∘ Sum.inl) + PortHamiltonian.energy m₂ (x ∘ Sum.inr) := by
  simp [PortHamiltonian.energy, interconnect, Fintype.sum_sum_type]

omit [DecidableEq ι₁] [DecidableEq ι₂] [Fintype κ] in
/-- The external output is `g₁ᵀ y₁ + g₂ᵀ y₂`. -/
@[powerlib_foundation] theorem interconnect_output (x : ι₁ ⊕ ι₂ → ℝ) :
    PortHamiltonian.output (interconnect m₁ m₂ Mc g₁ g₂) x =
      g₁ᵀ *ᵥ PortHamiltonian.output m₁ (x ∘ Sum.inl) +
        g₂ᵀ *ᵥ PortHamiltonian.output m₂ (x ∘ Sum.inr) := by
  have hB : (interconnect m₁ m₂ Mc g₁ g₂).B = fromRows (m₁.B * g₁) (m₂.B * g₂) := rfl
  rw [PortHamiltonian.output, hB, interconnect_gradient, transpose_fromRows,
    fromCols_mulVec]
  simp [PortHamiltonian.output, transpose_mul, mulVec_mulVec, Function.comp_def]

/-- Compositionality (T-ph §1.5): the interconnected system is passive with storage
`H₁ + H₂`, with no new Lyapunov analysis. -/
@[powerlib_foundation] theorem interconnect_passiveWithStorage :
    Passivity.PassiveWithStorage (PortHamiltonian.system (interconnect m₁ m₂ Mc g₁ g₂))
      (PortHamiltonian.energy (interconnect m₁ m₂ Mc g₁ g₂)) :=
  PortHamiltonian.passiveWithStorage _

/-- Trajectories of the composite project to trajectories of the first subsystem under the
coupling input `u₁ = −Mᵀ y₂ + g₁ u`. -/
@[powerlib_foundation] theorem interconnect_trajectory_inl {u : ℝ → (κ → ℝ)}
    {x : ℝ → (ι₁ ⊕ ι₂ → ℝ)}
    (hx : Passivity.IsTrajectory (PortHamiltonian.system (interconnect m₁ m₂ Mc g₁ g₂)) u x) :
    Passivity.IsTrajectory (PortHamiltonian.system m₁)
      (fun t => -(Mcᵀ *ᵥ PortHamiltonian.output m₂ (x t ∘ Sum.inr)) + g₁ *ᵥ u t)
      (fun t => x t ∘ Sum.inl) := by
  intro t ht
  have h := hasDerivWithinAt_pi.mp (hx t ht)
  apply hasDerivWithinAt_pi.mpr
  intro i
  have := h (Sum.inl i)
  simp only [PortHamiltonian.system] at this ⊢
  rw [← interconnect_field_inl]
  exact this

/-- Trajectories of the composite project to trajectories of the second subsystem under the
coupling input `u₂ = M y₁ + g₂ u`. -/
@[powerlib_foundation] theorem interconnect_trajectory_inr {u : ℝ → (κ → ℝ)}
    {x : ℝ → (ι₁ ⊕ ι₂ → ℝ)}
    (hx : Passivity.IsTrajectory (PortHamiltonian.system (interconnect m₁ m₂ Mc g₁ g₂)) u x) :
    Passivity.IsTrajectory (PortHamiltonian.system m₂)
      (fun t => Mc *ᵥ PortHamiltonian.output m₁ (x t ∘ Sum.inl) + g₂ *ᵥ u t)
      (fun t => x t ∘ Sum.inr) := by
  intro t ht
  have h := hasDerivWithinAt_pi.mp (hx t ht)
  apply hasDerivWithinAt_pi.mpr
  intro i
  have := h (Sum.inr i)
  simp only [PortHamiltonian.system] at this ⊢
  rw [← interconnect_field_inr]
  exact this

end Interconnection

/-! ## Block structure of `J^tot` and `R^tot` -/

section Blocks

variable {ι ι₁ ι₂ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι₁] [Fintype ι₂]

/-- Block-diagonal dissipation of independent components is positive semidefinite. -/
@[powerlib_foundation] theorem blockDiag_posSemidef {R₁ : Matrix ι₁ ι₁ ℝ} {R₂ : Matrix ι₂ ι₂ ℝ}
    (h₁ : R₁.PosSemidef) (h₂ : R₂.PosSemidef) : (fromBlocks R₁ 0 0 R₂).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec] at h₁ h₂ ⊢
  refine ⟨h₁.1.fromBlocks (by simp) h₂.1, fun x => ?_⟩
  rw [fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero, zero_add, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Pi.star_apply]
  have a := h₁.2 (x ∘ Sum.inl)
  have b := h₂.2 (x ∘ Sum.inr)
  simp only [dotProduct, Pi.star_apply, Function.comp_apply] at a b
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- §1.5.2: adding skew-symmetric interconnection blocks keeps `J` skew. -/
@[powerlib_foundation] theorem skew_add {J K : Matrix ι ι ℝ} (hJ : Jᵀ = -J) (hK : Kᵀ = -K) :
    (J + K)ᵀ = -(J + K) := by
  rw [transpose_add, hJ, hK, neg_add]

/-- An elementary interconnection pair `a (eᵢ eⱼᵀ − eⱼ eᵢᵀ)` is skew-symmetric. -/
def skewPair (i j : ι) (a : ℝ) : Matrix ι ι ℝ :=
  a • (single i j 1 - single j i 1)

omit [Fintype ι] in
@[powerlib_foundation] theorem skewPair_skew (i j : ι) (a : ℝ) :
    (skewPair i j a)ᵀ = -skewPair i j a := by
  simp [skewPair, transpose_sub, transpose_single, smul_sub, neg_sub]

omit [Fintype ι] in
/-- §1.5.2 recursion: any finite sum of elementary pairs added to a skew `J` stays skew. -/
@[powerlib_foundation] theorem skew_add_sum_skewPair {J : Matrix ι ι ℝ} (hJ : Jᵀ = -J)
    (s : Finset (ι × ι × ℝ)) :
    (J + ∑ p ∈ s, skewPair p.1 p.2.1 p.2.2)ᵀ = -(J + ∑ p ∈ s, skewPair p.1 p.2.1 p.2.2) := by
  apply skew_add hJ
  rw [transpose_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => skewPair_skew _ _ _

omit [Fintype ι] in
/-- §1.7: a constant-impedance load adds a nonnegative diagonal term to `R`, keeping `R ⪰ 0`. -/
@[powerlib_foundation] theorem posSemidef_add_diagonal {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {G : ι → ℝ} (hG : ∀ i, 0 ≤ G i) : (R + diagonal G).PosSemidef :=
  hR.add (PosSemidef.diagonal hG)

end Blocks

/-! ## Frame rotation -/

/-- T-power-system-ph §1.2: the rotation `R(δ)` is orthogonal, so the port power
`v_d i_d + v_q i_q` is the same in the machine frame and in the common DQ frame. -/
@[powerlib_foundation] theorem frameRotation_power_invariant (δ : ℝ) (v i : Fin 2 → ℝ) :
    (Transform.rot δ *ᵥ v) ⬝ᵥ (Transform.rot δ *ᵥ i) = v ⬝ᵥ i := by
  simp only [Transform.rot_apply_mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have h := Real.sin_sq_add_cos_sq δ
  linear_combination (v 0 * i 0 + v 1 * i 1) * h

/-! ## Kron reduction -/

section Kron

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
/-- Kron reduction: if the internal nodes inject no current (`Y_ii v_i + Y_ib v_b = 0`) and
`Y_ii` is invertible, the boundary injections are `(Y_bb − Y_bi Y_ii⁻¹ Y_ib) v_b`. -/
@[powerlib_foundation] theorem kron_current {Yii : Matrix ι ι ℝ} {Yib : Matrix ι β ℝ}
    {Ybi : Matrix β ι ℝ} {Ybb : Matrix β β ℝ} (hinv : IsUnit Yii.det) {vi : ι → ℝ}
    {vb : β → ℝ} (hint : Yii *ᵥ vi + Yib *ᵥ vb = 0) :
    Ybi *ᵥ vi + Ybb *ᵥ vb = (Ybb - Ybi * Yii⁻¹ * Yib) *ᵥ vb := by
  have hvi : vi = -((Yii⁻¹ * Yib) *ᵥ vb) := by
    have h1 : Yii *ᵥ vi = -(Yib *ᵥ vb) := eq_neg_of_add_eq_zero_left hint
    have h2 := congrArg (fun z => Yii⁻¹ *ᵥ z) h1
    simp only [mulVec_mulVec, nonsing_inv_mul _ hinv, one_mulVec, mulVec_neg] at h2
    exact h2
  rw [hvi, sub_mulVec, mulVec_neg, mulVec_mulVec, Matrix.mul_assoc]
  abel

omit [DecidableEq ι] [DecidableEq β] in
/-- Kron reduction conserves port power: with zero internal injection, the network power
`vᵀ Y v` equals the boundary port power `v_bᵀ i_b`. -/
@[powerlib_foundation] theorem kron_power (Yii : Matrix ι ι ℝ) (Yib : Matrix ι β ℝ)
    (Ybi : Matrix β ι ℝ) (Ybb : Matrix β β ℝ) {vi : ι → ℝ} {vb : β → ℝ}
    (hint : Yii *ᵥ vi + Yib *ᵥ vb = 0) :
    Sum.elim vi vb ⬝ᵥ (fromBlocks Yii Yib Ybi Ybb *ᵥ Sum.elim vi vb) =
      vb ⬝ᵥ (Ybi *ᵥ vi + Ybb *ᵥ vb) := by
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, hint, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]

omit [DecidableEq β] in
/-- Kron reduction of a positive semidefinite network with positive definite internal block is
positive semidefinite (passivity is preserved). Wrapper of Mathlib
`Matrix.PosDef.fromBlocks₁₁` (Schur complement). -/
@[powerlib_foundation] theorem kron_posSemidef {Yii : Matrix ι ι ℝ} {Yib : Matrix ι β ℝ}
    {Ybb : Matrix β β ℝ} (hY : (fromBlocks Yii Yib Yibᵀ Ybb).PosSemidef) (hii : Yii.PosDef) :
    (Ybb - Yibᵀ * Yii⁻¹ * Yib).PosSemidef := by
  have := hii.isUnit.invertible
  have h := (PosDef.fromBlocks₁₁ Yib Ybb hii).mp
  simp only [conjTranspose_eq_transpose_of_trivial] at h
  exact h hY

end Kron

/-! ## State dimension -/

/-- T-power-system-ph §1.8: `N` seven-state machines, `ℓ` branch fluxes and `n_C` node charges
give a state of dimension `7N + ℓ + n_C` (ZIP loads add no state). -/
@[powerlib_foundation] theorem powerSystem_state_dim (N : ℕ) (β ν : Type*) [Fintype β]
    [Fintype ν] :
    Fintype.card ((Fin N × Fin 7) ⊕ β ⊕ ν) = 7 * N + Fintype.card β + Fintype.card ν := by
  simp [Fintype.card_sum, Fintype.card_prod, mul_comm, add_assoc]

end powerlib.PH
