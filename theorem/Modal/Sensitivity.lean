import theorem.Modal.Spectral

/-! # Sensitivity of a simple eigenpair: eigenvalue and eigenvector derivatives

Foundation layer (category B).

Sources: work-sync `theory/T-participation-factor.md` (eigenvector sensitivity, simple
eigenvalue premise), `theory/T-eigenvalue-analysis.md` §1.9 and
`theory/T-small-signal-stability.md` §1.8 (`dλ/dα = ψᵀ (∂A/∂α) v`).

Setting: a parameter-dependent complex matrix `A(α)` (entrywise differentiable at `α₀`), the
modal data `mb : ModalBasis (A α₀)` (diagonalisable at `α₀`, biorthonormal `ψⱼᵀ vₖ = δⱼₖ`) and a
**simple** eigenvalue `λᵢ` (`λⱼ ≠ λᵢ` for `j ≠ i`). The theorems are conditional on a
differentiable eigen-branch `A(α) v(α) = λ(α) v(α)` through `(λᵢ, vᵢ)`; its existence (implicit
function theorem for simple eigenvalues) is not proved here.

Results.
* `eigen_branch_deriv`: `A' vᵢ + A v' = λ' vᵢ + λᵢ v'` (derivative of the eigen-equation).
* `eigenvalue_deriv`: `λ'(α₀) = ψᵢᵀ A' vᵢ`.
* `eigenvector_deriv_coeff`: for `j ≠ i`, `ψⱼᵀ v' = ψⱼᵀ A' vᵢ / (λᵢ − λⱼ)`.
* `eigenvector_deriv`: `v' = Σ_{j≠i} (ψⱼᵀ A' vᵢ)/(λᵢ − λⱼ) vⱼ + (ψᵢᵀ v') vᵢ`; the component along
  `vᵢ` is fixed by the normalisation of the branch (e.g. `ψᵢᵀ v(α) ≡ 1` gives `ψᵢᵀ v' = 0`).
-/

noncomputable section
namespace powerlib.Modal
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Derivative of the eigen-equation along a differentiable branch. -/
@[powerlib_foundation] theorem eigen_branch_deriv {A : ℝ → Matrix n n ℂ} {A' : Matrix n n ℂ}
    {v : ℝ → n → ℂ} {v' : n → ℂ} {lam : ℝ → ℂ} {lam' : ℂ} {α₀ : ℝ}
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ α, A α *ᵥ v α = lam α • v α) :
    A' *ᵥ v α₀ + A α₀ *ᵥ v' = lam' • v α₀ + lam α₀ • v' := by
  funext i
  have hL : HasDerivAt (fun α => (A α *ᵥ v α) i) (∑ j, (A' i j * v α₀ j + A α₀ i j * v' j)) α₀ := by
    simp only [mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hA i j).mul (hv j)
  have hR : HasDerivAt (fun α => (lam α • v α) i) (lam' * v α₀ i + lam α₀ * v' i) α₀ := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hlam.mul (hv i)
  have heq : (fun α => (A α *ᵥ v α) i) = fun α => (lam α • v α) i := by
    funext α; rw [heig α]
  rw [heq] at hL
  have := hL.unique hR
  simp only [Pi.add_apply, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  exact this

variable {A : ℝ → Matrix n n ℂ} {A' : Matrix n n ℂ} {α₀ : ℝ} (mb : ModalBasis (A α₀))
  {i : n} {v : ℝ → n → ℂ} {v' : n → ℂ} {lam : ℝ → ℂ} {lam' : ℂ}

/-- `λ'(α₀) = ψᵢᵀ A' vᵢ` along the branch through `(λᵢ, vᵢ)`. -/
@[powerlib_foundation] theorem eigenvalue_deriv
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ α, A α *ᵥ v α = lam α • v α) (hv0 : v α₀ = mb.v i) (hl0 : lam α₀ = mb.eig i) :
    lam' = mb.ψ i ⬝ᵥ (A' *ᵥ mb.v i) := by
  have h := congrArg (fun w => mb.ψ i ⬝ᵥ w) (eigen_branch_deriv hA hv hlam heig)
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hv0, hl0] at h
  rw [dotProduct_mulVec (mb.ψ i) (A α₀) v', mb.vecMul_ψ, smul_dotProduct, smul_eq_mul,
    mb.ψ_dot_v] at h
  simp only [↓reduceIte] at h
  linear_combination -h

/-- Off-diagonal modal coordinates of the eigenvector derivative. -/
@[powerlib_foundation] theorem eigenvector_deriv_coeff
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ α, A α *ᵥ v α = lam α • v α) (hv0 : v α₀ = mb.v i) (hl0 : lam α₀ = mb.eig i)
    {j : n} (hj : j ≠ i) (hsimple : mb.eig j ≠ mb.eig i) :
    mb.ψ j ⬝ᵥ v' = mb.ψ j ⬝ᵥ (A' *ᵥ mb.v i) / (mb.eig i - mb.eig j) := by
  have h := congrArg (fun w => mb.ψ j ⬝ᵥ w) (eigen_branch_deriv hA hv hlam heig)
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hv0, hl0] at h
  rw [dotProduct_mulVec (mb.ψ j) (A α₀) v', mb.vecMul_ψ, smul_dotProduct, smul_eq_mul,
    mb.ψ_dot_v] at h
  simp only [hj, ↓reduceIte] at h
  have hne : mb.eig i - mb.eig j ≠ 0 := sub_ne_zero.mpr (Ne.symm hsimple)
  field_simp
  linear_combination -h

/-- **Eigenvector derivative** of a simple eigenpair. -/
@[powerlib_foundation] theorem eigenvector_deriv
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ α, A α *ᵥ v α = lam α • v α) (hv0 : v α₀ = mb.v i) (hl0 : lam α₀ = mb.eig i)
    (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i) :
    v' = ∑ j ∈ Finset.univ.erase i,
        (mb.ψ j ⬝ᵥ (A' *ᵥ mb.v i) / (mb.eig i - mb.eig j)) • mb.v j +
      (mb.ψ i ⬝ᵥ v') • mb.v i := by
  conv_lhs => rw [mb.eq_sum_modal v']
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji := Finset.ne_of_mem_erase hj
  rw [eigenvector_deriv_coeff mb hA hv hlam heig hv0 hl0 hji (hsimple j hji)]

end powerlib.Modal
