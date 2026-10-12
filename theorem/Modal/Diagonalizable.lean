import theorem.Modal.Spectral
import theorem.Modal.Eigen
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Algebra.DirectSum.Module

/-! # Diagonalizability ⇔ geometric multiplicity = algebraic multiplicity

Foundation layer (category B).

Source: work-sync `theory/T-eigenvalue-analysis.md` §1.1 ("若对所有 `λ` 都有 `m_g = m_a`，`A` 可对角化
… 否则称 `A` defective").

Setting: complex square matrices. "Diagonalizable" means that modal data exist: a
`ModalBasis A` (`theorem/Modal/Participation.lean`: `A V = V diag(λ)`, `Wᵀ V = I`), i.e. an
invertible matrix of right eigenvectors.

Result (`nonempty_modalBasis_iff`): `A` has a modal basis iff for every `μ ∈ ℂ`,
`dim ker(A − μI) = rootMultiplicity μ (charpoly A)`.
* (⇒) the eigenvector columns with eigenvalue `μ` are linearly independent and lie in the
  eigenspace, and their number is the algebraic multiplicity (`ModalBasis.rootMultiplicity_eq_card`).
* (⇐) `m_g = m_a` forces each eigenspace to equal the generalized eigenspace (same dimension,
  Mathlib `finrank_maxGenEigenspace_eq`), generalized eigenspaces span `ℂⁿ`
  (`iSup_maxGenEigenspace_eq_top`), eigenspaces are independent, so collecting bases of the
  eigenspaces gives an eigenvector basis, hence `V`.
-/

noncomputable section
namespace powerlib.Modal
open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The linear operator of `A` on `ℂⁿ`. -/
abbrev op (A : Matrix n n ℂ) : Module.End ℂ (n → ℂ) := Matrix.toLin' A

/-- (⇒) for a diagonalizable matrix, `m_g(μ) = m_a(μ)` for every `μ`. -/
@[powerlib_foundation] theorem ModalBasis.geom_eq_alg {A : Matrix n n ℂ} (mb : ModalBasis A)
    (μ : ℂ) : finrank ℂ ((op A).eigenspace μ) = A.charpoly.rootMultiplicity μ := by
  refine le_antisymm (geom_le_alg A μ) ?_
  rw [mb.rootMultiplicity_eq_card]
  -- the columns `vᵢ` with `λᵢ = μ` are independent vectors of the eigenspace
  set S := Finset.univ.filter (fun i => mb.eig i = μ)
  have hVunit : IsUnit mb.V := ⟨⟨mb.V, mb.Wᵀ, mb.V_mul_Wt, mb.biorth⟩, rfl⟩
  have hli : LinearIndependent ℂ mb.V.col := linearIndependent_cols_iff_isUnit.mpr hVunit
  have hmem : ∀ i : S, mb.v i ∈ (op A).eigenspace μ := by
    intro i
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, mb.mulVec_v,
      (Finset.mem_filter.mp i.2).2]
  let f : S → (op A).eigenspace μ := fun i => ⟨mb.v i, hmem i⟩
  have hf : LinearIndependent ℂ f := by
    apply LinearIndependent.of_comp ((op A).eigenspace μ).subtype
    have : ((op A).eigenspace μ).subtype ∘ f = mb.V.col ∘ (fun i : S => (i : n)) := by
      funext i; rfl
    rw [this]
    exact hli.comp _ Subtype.val_injective
  have := hf.fintype_card_le_finrank
  simp only [S] at this
  rwa [Fintype.card_coe] at this

/-- (⇐) `m_g = m_a` for all eigenvalues gives a modal basis. -/
@[powerlib_foundation] theorem nonempty_modalBasis_of_geom_eq_alg {A : Matrix n n ℂ}
    (h : ∀ μ, finrank ℂ ((op A).eigenspace μ) = A.charpoly.rootMultiplicity μ) :
    Nonempty (ModalBasis A) := by
  -- eigenspaces = generalized eigenspaces
  have hE : ∀ μ, (op A).eigenspace μ = (op A).maxGenEigenspace μ := by
    intro μ
    apply Submodule.eq_of_le_of_finrank_eq Module.End.eigenspace_le_maxGenEigenspace
    rw [h μ, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']
  have htop : ⨆ μ, (op A).eigenspace μ = ⊤ := by
    simp_rw [hE]
    exact Module.End.iSup_maxGenEigenspace_eq_top (op A)
  have hint : DirectSum.IsInternal (fun μ => (op A).eigenspace μ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (op A).eigenspaces_iSupIndep htop
  let b := hint.collectedBasis (fun μ => Module.finBasis ℂ ((op A).eigenspace μ))
  -- the index type is finite with `card = n`
  have : Finite (Σ μ : ℂ, Fin (finrank ℂ ((op A).eigenspace μ))) := Module.Finite.finite_basis b
  let := Fintype.ofFinite (Σ μ : ℂ, Fin (finrank ℂ ((op A).eigenspace μ)))
  have hcard : Fintype.card n = Fintype.card (Σ μ : ℂ, Fin (finrank ℂ ((op A).eigenspace μ))) := by
    rw [← Module.finrank_eq_card_basis b]
    simp
  let e := Fintype.equivOfCardEq hcard
  let V : Matrix n n ℂ := Matrix.of fun r i => b (e i) r
  let eig : n → ℂ := fun i => (e i).1
  have hcol : V.col = b ∘ e := by funext i r; rfl
  have hVunit : IsUnit V := by
    rw [← linearIndependent_cols_iff_isUnit, hcol]
    exact b.linearIndependent.comp e e.injective
  have hright : A * V = V * diagonal eig := by
    ext r i
    have hmem := hint.collectedBasis_mem (fun μ => Module.finBasis ℂ ((op A).eigenspace μ)) (e i)
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hmem
    have := congrFun hmem r
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [mul_apply, mul_diagonal]
    simp only [V, eig, Matrix.of_apply]
    rw [this, mul_comm]
  have hdet : IsUnit V.det := (isUnit_iff_isUnit_det V).mp hVunit
  have hbi : ((V⁻¹)ᵀ)ᵀ * V = 1 := by rw [transpose_transpose, nonsing_inv_mul _ hdet]
  exact ⟨⟨V, (V⁻¹)ᵀ, eig, hright, hbi⟩⟩

/-- **Diagonalizable ⇔ `m_g = m_a`** for every eigenvalue. -/
@[powerlib_foundation] theorem nonempty_modalBasis_iff (A : Matrix n n ℂ) :
    Nonempty (ModalBasis A) ↔
      ∀ μ, finrank ℂ ((op A).eigenspace μ) = A.charpoly.rootMultiplicity μ :=
  ⟨fun ⟨mb⟩ => mb.geom_eq_alg, nonempty_modalBasis_of_geom_eq_alg⟩

end powerlib.Modal
