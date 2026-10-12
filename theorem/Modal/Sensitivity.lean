import theorem.Modal.Spectral
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # Sensitivity of a simple eigenpair: eigenvalue and eigenvector derivatives

Foundation layer (category B).

Sources: work-sync `theory/T-participation-factor.md` (eigenvector sensitivity, simple
eigenvalue premise), `theory/T-eigenvalue-analysis.md` §1.9 and
`theory/T-small-signal-stability.md` §1.8 (`dλ/dα = ψᵀ (∂A/∂α) v`).

Setting: a parameter-dependent complex matrix `A(α)` (entrywise differentiable at `α₀`), the
modal data `mb : ModalBasis (A α₀)` (diagonalisable at `α₀`, biorthonormal `ψⱼᵀ vₖ = δⱼₖ`) and a
**simple** eigenvalue `λᵢ` (`λⱼ ≠ λᵢ` for `j ≠ i`). The derivative formulas below are conditional
on a differentiable eigen-branch `A(α) v(α) = λ(α) v(α)` through `(λᵢ, vᵢ)`. The existence of a
differentiable **eigenvalue** branch is proved separately (`exists_eigenvalue_branch`).

Results.
* `eigen_branch_deriv`: `A' vᵢ + A v' = λ' vᵢ + λᵢ v'` (derivative of the eigen-equation).
* `eigenvalue_deriv`: `λ'(α₀) = ψᵢᵀ A' vᵢ`.
* `eigenvector_deriv_coeff`: for `j ≠ i`, `ψⱼᵀ v' = ψⱼᵀ A' vᵢ / (λᵢ − λⱼ)`.
* `eigenvector_deriv`: `v' = Σ_{j≠i} (ψⱼᵀ A' vᵢ)/(λᵢ − λⱼ) vⱼ + (ψᵢᵀ v') vᵢ`; the component along
  `vᵢ` is fixed by the normalisation of the branch (e.g. `ψᵢᵀ v(α) ≡ 1` gives `ψᵢᵀ v' = 0`).
* `contDiffAt_charpoly_eval`: `(p, z) ↦ det(zI − A(p))` is `C¹` when the entries of `A` are.
* `exists_eigenvalue_branch`: **existence of a differentiable eigenvalue branch** — for a parameter
  `p` in a real Banach space `E`, entries of `A(p)` `C¹` at `p₀`, and `λ₀` a simple eigenvalue of
  `A(p₀)` (root multiplicity one in `charpoly`), there is `λ : E → ℂ`, `C¹` at `p₀`, with
  `λ(p₀) = λ₀`, `λ(p)` an eigenvalue of `A(p)` (with an eigenvector) for `p` near `p₀`, and locally
  the only eigenvalue near `λ₀`. Proof: Mathlib's implicit function theorem
  (`ContDiffAt.implicitFunction`) on `F(p, z) = det(zI − A(p))` over `ℝ`, whose `z`-partial
  derivative is multiplication by `χ'(λ₀) ≠ 0` (simple root). A differentiable eigen**vector**
  branch is not constructed here; the formulas above still assume one.
-/

noncomputable section
namespace powerlib.Modal
open Matrix Polynomial Filter Topology

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

/-! ## Existence of a differentiable branch (implicit function theorem) -/

/-- The characteristic polynomial `(p, z) ↦ det(zI − A(p))` is `C¹` jointly in the parameter and
the spectral variable when the entries of `A` are `C¹` at `p₀`. -/
@[powerlib_foundation] theorem contDiffAt_charpoly_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix n n ℂ} {p₀ : E} (hA : ∀ i j, ContDiffAt ℝ 1 (fun p => A p i j) p₀) (z₀ : ℂ) :
    ContDiffAt ℝ 1 (fun q : E × ℂ => (A q.1).charpoly.eval q.2) (p₀, z₀) := by
  have e : (fun q : E × ℂ => (A q.1).charpoly.eval q.2) = fun q =>
      ∑ σ : Equiv.Perm n, (((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, ((if σ i = i then q.2 else 0) - A q.1 (σ i) i)) := by
    funext q
    rw [Matrix.eval_charpoly, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
  rw [e]
  refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => ?_)
  refine ContDiffAt.sub ?_ ((hA (σ i) i).comp (p₀, z₀) contDiffAt_fst)
  split_ifs
  · exact contDiffAt_snd
  · exact contDiffAt_const

/-- **Differentiable eigenvalue branch through a simple eigenvalue** (implicit function theorem on
the characteristic polynomial, Mathlib `ContDiffAt.implicitFunction`): if the entries of `A(p)`
are `C¹` at `p₀` and `λ₀` is a simple eigenvalue of `A(p₀)` (algebraic multiplicity one), there is
a function `λ(p)`, `C¹` at `p₀`, with `λ(p₀) = λ₀`, such that near `p₀` every `λ(p)` is an
eigenvalue of `A(p)` and, near `(p₀, λ₀)`, it is the only one. -/
@[powerlib_foundation] theorem exists_eigenvalue_branch {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {A : E → Matrix n n ℂ} {p₀ : E} {lam₀ : ℂ}
    (hA : ∀ i j, ContDiffAt ℝ 1 (fun p => A p i j) p₀)
    (hsimple : (A p₀).charpoly.rootMultiplicity lam₀ = 1) :
    ∃ lam : E → ℂ, lam p₀ = lam₀ ∧ ContDiffAt ℝ 1 lam p₀ ∧
      (∀ᶠ p in 𝓝 p₀, ∃ v : n → ℂ, v ≠ 0 ∧ A p *ᵥ v = lam p • v) ∧
      (∀ᶠ q in 𝓝 (p₀, lam₀), (A q.1).charpoly.IsRoot q.2 ↔ lam q.1 = q.2) := by
  set f : E × ℂ → ℂ := fun q => (A q.1).charpoly.eval q.2 with hfdef
  set χ := (A p₀).charpoly with hχ
  have hχ0 : χ ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hroot : χ.IsRoot lam₀ := (rootMultiplicity_pos hχ0).mp (by rw [hsimple]; exact one_pos)
  have hder : χ.derivative.eval lam₀ ≠ 0 := by
    intro h
    have := (one_lt_rootMultiplicity_iff_isRoot hχ0).mpr ⟨hroot, h⟩
    omega
  set c := χ.derivative.eval lam₀
  have hf : ContDiffAt ℝ 1 f (p₀, lam₀) := contDiffAt_charpoly_eval hA lam₀
  have hpn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  -- the partial derivative in the spectral variable is multiplication by `χ'(λ₀) ≠ 0`
  have hpart : fderiv ℝ f (p₀, lam₀) ∘L ContinuousLinearMap.inr ℝ E ℂ =
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ) := by
    have h1 : HasFDerivAt (fun z : ℂ => f (p₀, z))
        (fderiv ℝ f (p₀, lam₀) ∘L ContinuousLinearMap.inr ℝ E ℂ) lam₀ := by
      have hin : HasFDerivAt (fun z : ℂ => (p₀, z)) (ContinuousLinearMap.inr ℝ E ℂ) lam₀ :=
        (hasFDerivAt_const p₀ lam₀).prodMk (hasFDerivAt_id lam₀)
      exact (hf.differentiableAt hpn).hasFDerivAt.comp lam₀ hin
    have h2 : HasFDerivAt (fun z : ℂ => f (p₀, z))
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ) lam₀ :=
      (χ.hasDerivAt lam₀).hasFDerivAt.restrictScalars ℝ
    exact h1.unique h2
  have hinv : (fderiv ℝ f (p₀, lam₀) ∘L ContinuousLinearMap.inr ℝ E ℂ).IsInvertible := by
    rw [hpart]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c⁻¹).restrictScalars ℝ) ?_ ?_
    · ext z
      simp
      field_simp
    · ext z
      simp
      field_simp
  set lam := hf.implicitFunction hpn hinv
  have hf0 : f (p₀, lam₀) = 0 := hroot
  refine ⟨lam, hf.implicitFunction_apply_self hpn hinv, hf.contDiffAt_implicitFunction hpn hinv,
    ?_, ?_⟩
  · filter_upwards [hf.eventually_apply_implicitFunction hpn hinv] with p hp
    have hz : (A p).charpoly.eval (lam p) = 0 := by rw [← hf0]; exact hp
    rw [Matrix.eval_charpoly] at hz
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hAv
    exact hAv.symm
  · filter_upwards [hf.eventually_apply_eq_iff_implicitFunction hpn hinv] with q hq
    rw [← hq, hf0]
    rfl

end powerlib.Modal
