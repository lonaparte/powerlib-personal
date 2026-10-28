import theorem.Modal.Spectral
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-! # Sensitivity of a simple eigenpair: eigenvalue and eigenvector derivatives

Derivatives of a simple eigenvalue and of its eigenvector along a parameter, and the existence
of differentiable eigenpair branches (implicit function theorem); scalar root branches.

Scope.
* Finite-dimensional complex matrices, real (Banach-space) parameters, local (germ) statements
  at a simple eigenvalue only; no claim for repeated eigenvalues (where branches need not be
  differentiable), and no global continuation of the branch.
* A parameter-dependent complex matrix `A(α)` (entrywise differentiable at `α₀`), the modal data
  `mb : ModalBasis (A α₀)` (diagonalisable at `α₀`, biorthonormal `ψⱼᵀ vₖ = δⱼₖ`) and a
  **simple** eigenvalue `λᵢ` (`λⱼ ≠ λᵢ` for `j ≠ i`). The first group of formulas is stated
  along a given differentiable eigen-branch `A(α) v(α) = λ(α) v(α)` through `(λᵢ, vᵢ)`
  (globally, or only near `α₀`: the `…_of_eventually` versions). The second group proves that
  such a branch **exists** (implicit function theorem), so the formulas hold unconditionally for
  `C¹` matrix families.

Source: work-sync theory/T-participation-factor.md (eigenvector sensitivity, simple
eigenvalue premise), theory/T-eigenvalue-analysis.md §1.9 and
theory/T-small-signal-stability.md §1.8 (`dλ/dα = ψᵀ (∂A/∂α) v`); scalar root branches:
projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/gfl-gfm-parametric-contrast.md
§17.

Results.

Along a given branch:
* `eigen_branch_deriv`, `eigen_branch_deriv_of_eventually` — `A' vᵢ + A v' = λ' vᵢ + λᵢ v'`.
* `eigenvalue_deriv`, `eigenvalue_deriv_of_eventually` — `λ'(α₀) = ψᵢᵀ A' vᵢ`.
* `eigenvector_deriv_coeff`, `eigenvector_deriv_coeff_of_eventually` — for `j ≠ i`,
  `ψⱼᵀ v' = ψⱼᵀ A' vᵢ / (λᵢ − λⱼ)`.
* `eigenvector_deriv`, `eigenvector_deriv_of_eventually` —
  `v' = Σ_{j≠i} (ψⱼᵀ A' vᵢ)/(λᵢ − λⱼ) vⱼ + (ψᵢᵀ v') vᵢ`; the component along `vᵢ` is fixed by
  the normalisation of the branch (e.g. `ψᵢᵀ v(α) ≡ 1` gives `ψᵢᵀ v' = 0`).

Existence of branches:
* `contDiffAt_charpoly_eval` — `(p, z) ↦ det(zI − A(p))` is `C¹` when the entries of `A` are.
* `exists_eigenvalue_branch` — a `C¹` **eigenvalue** branch through a simple eigenvalue (IFT on
  `det(zI − A(p))`, whose `z`-derivative is `χ'(λ₀) ≠ 0`), locally the only eigenvalue near
  `λ₀`.
* `eq_smul_of_mulVec_sub_eq_smul` — at an eigenvalue of algebraic multiplicity one there is no
  Jordan chain of length two: `(A₀ − λ₀) x ∈ span v₀ ⇒ x ∈ span v₀` (via Mathlib's
  `LinearMap.finrank_genEigenspace_le`: `dim ker (A₀ − λ₀)² ≤ rootMultiplicity = 1`).
* `bordered_injective` — hence the bordered matrix `[[A₀ − λ₀ I, −v₀], [wᵀ, 0]]` is injective
  whenever `wᵀ v₀ ≠ 0`.
* `exists_eigenvector_branch` — **differentiable eigenvector branch**: for a parameter `p` in a
  real Banach space `E`, entries of `A(p)` `C¹` at `p₀`, `λ₀` a simple eigenvalue of `A(p₀)`
  (root multiplicity one in `charpoly`), `A(p₀) v₀ = λ₀ v₀` and any `w` with `wᵀ v₀ ≠ 0`, there
  are `v(p)`, `λ(p)`, `C¹` at `p₀`, with `v(p₀) = v₀`, `λ(p₀) = λ₀`, and near `p₀`
  `A(p) v(p) = λ(p) v(p)`, `wᵀ v(p) = wᵀ v₀`, `v(p) ≠ 0`; near `(p₀, v₀, λ₀)` these are the only
  normalised eigenpairs. Proof: Mathlib's implicit function theorem
  (`ContDiffAt.implicitFunction`) on `F(p, v, λ) = ((A(p) − λ I) v, wᵀ v − wᵀ v₀)`, whose
  `(v, λ)`-derivative is the bordered matrix (invertible by `bordered_injective`; this replaces
  the adjugate route, which needs `adj(λ₀ I − A₀) ≠ 0`). The normalisation is the bilinear
  `wᵀ v` (not `wᴴ v`), so the map is complex-polynomial. `exists_eigenvector_branch_of_ne_zero`
  chooses `w = e_k` with `v₀ k ≠ 0`.
* `exists_eigenpair_branch_deriv` — one real parameter, no diagonalisability: the branch has
  derivatives `v'`, `λ'` with `A' v₀ + A₀ v' = λ' v₀ + λ₀ v'`, `wᵀ v' = 0`, and
  `λ' (uᵀ v₀) = uᵀ A' v₀` for **every** left eigenvector `uᵀ A₀ = λ₀ uᵀ`.
* `eigenpair_deriv_of_simple`, `eigenvalue_deriv_of_simple` — **unconditional** versions of
  `eigenvalue_deriv` / `eigenvector_deriv`: for `A(α)` with `C¹` entries, a modal basis at `α₀`
  and a simple `λᵢ`, there is a branch with `ψᵢᵀ v(α) ≡ 1`, `λ'(α₀) = ψᵢᵀ A' vᵢ` and
  `v'(α₀) = Σ_{j≠i} (ψⱼᵀ A' vᵢ)/(λᵢ − λⱼ) vⱼ`; no branch is assumed.

Scalar root branches:
* `root_branch_deriv`, `exists_root_branch` — a simple root `λ₀` of `P(s) + c K₀ = 0`
  (`P : ℂ → ℂ`, `P'(λ₀) ≠ 0`) continues to a differentiable root branch `λ(K)` of one real
  parameter (inverse function theorem), and every differentiable branch through it has
  `dλ/dK = −c / P'(λ)` (used for the VSM cubic of `theorem/GFM/ContrastAlgebra.lean`).
-/

noncomputable section
namespace powerlib.Modal
open Matrix Polynomial Filter Topology Module

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Derivative of the eigen-equation along a differentiable branch defined near `α₀`. -/
@[tmio T, powerlib_foundation] theorem eigen_branch_deriv_of_eventually {A : ℝ → Matrix n n ℂ}
    {A' : Matrix n n ℂ} {v : ℝ → n → ℂ} {v' : n → ℂ} {lam : ℝ → ℂ} {lam' : ℂ} {α₀ : ℝ}
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ᶠ α in 𝓝 α₀, A α *ᵥ v α = lam α • v α) :
    A' *ᵥ v α₀ + A α₀ *ᵥ v' = lam' • v α₀ + lam α₀ • v' := by
  funext i
  have hL : HasDerivAt (fun α => (A α *ᵥ v α) i) (∑ j, (A' i j * v α₀ j + A α₀ i j * v' j)) α₀ := by
    simp only [mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hA i j).mul (hv j)
  have hR : HasDerivAt (fun α => (lam α • v α) i) (lam' * v α₀ i + lam α₀ * v' i) α₀ := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hlam.mul (hv i)
  have hR' : HasDerivAt (fun α => (A α *ᵥ v α) i) (lam' * v α₀ i + lam α₀ * v' i) α₀ :=
    hR.congr_of_eventuallyEq (heig.mono fun α h => congrFun h i)
  have := hL.unique hR'
  simp only [Pi.add_apply, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  exact this

omit [DecidableEq n] in
/-- Derivative of the eigen-equation along a differentiable branch. -/
@[powerlib_foundation] theorem eigen_branch_deriv {A : ℝ → Matrix n n ℂ} {A' : Matrix n n ℂ}
    {v : ℝ → n → ℂ} {v' : n → ℂ} {lam : ℝ → ℂ} {lam' : ℂ} {α₀ : ℝ}
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ α, A α *ᵥ v α = lam α • v α) :
    A' *ᵥ v α₀ + A α₀ *ᵥ v' = lam' • v α₀ + lam α₀ • v' :=
  eigen_branch_deriv_of_eventually hA hv hlam (Eventually.of_forall heig)

section GivenBranch

variable {A : ℝ → Matrix n n ℂ} {A' : Matrix n n ℂ} {α₀ : ℝ} (mb : ModalBasis (A α₀))
  {i : n} {v : ℝ → n → ℂ} {v' : n → ℂ} {lam : ℝ → ℂ} {lam' : ℂ}

/-- `λ'(α₀) = ψᵢᵀ A' vᵢ` along a branch through `(λᵢ, vᵢ)` defined near `α₀`. -/
@[powerlib_foundation] theorem eigenvalue_deriv_of_eventually
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ᶠ α in 𝓝 α₀, A α *ᵥ v α = lam α • v α) (hv0 : v α₀ = mb.v i)
    (hl0 : lam α₀ = mb.eig i) :
    lam' = mb.ψ i ⬝ᵥ (A' *ᵥ mb.v i) := by
  have h := congrArg (fun w => mb.ψ i ⬝ᵥ w) (eigen_branch_deriv_of_eventually hA hv hlam heig)
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hv0, hl0] at h
  rw [dotProduct_mulVec (mb.ψ i) (A α₀) v', mb.vecMul_ψ, smul_dotProduct, smul_eq_mul,
    mb.ψ_dot_v] at h
  simp only [↓reduceIte] at h
  linear_combination -h

/-- `λ'(α₀) = ψᵢᵀ A' vᵢ` along the branch through `(λᵢ, vᵢ)`. -/
@[powerlib_foundation] theorem eigenvalue_deriv
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ α, A α *ᵥ v α = lam α • v α) (hv0 : v α₀ = mb.v i) (hl0 : lam α₀ = mb.eig i) :
    lam' = mb.ψ i ⬝ᵥ (A' *ᵥ mb.v i) :=
  eigenvalue_deriv_of_eventually mb hA hv hlam (Eventually.of_forall heig) hv0 hl0

/-- Off-diagonal modal coordinates of the eigenvector derivative, along a branch defined near
`α₀`. -/
@[powerlib_foundation] theorem eigenvector_deriv_coeff_of_eventually
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ᶠ α in 𝓝 α₀, A α *ᵥ v α = lam α • v α) (hv0 : v α₀ = mb.v i)
    (hl0 : lam α₀ = mb.eig i) {j : n} (hj : j ≠ i) (hsimple : mb.eig j ≠ mb.eig i) :
    mb.ψ j ⬝ᵥ v' = mb.ψ j ⬝ᵥ (A' *ᵥ mb.v i) / (mb.eig i - mb.eig j) := by
  have h := congrArg (fun w => mb.ψ j ⬝ᵥ w) (eigen_branch_deriv_of_eventually hA hv hlam heig)
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hv0, hl0] at h
  rw [dotProduct_mulVec (mb.ψ j) (A α₀) v', mb.vecMul_ψ, smul_dotProduct, smul_eq_mul,
    mb.ψ_dot_v] at h
  simp only [hj, ↓reduceIte] at h
  have hne : mb.eig i - mb.eig j ≠ 0 := sub_ne_zero.mpr (Ne.symm hsimple)
  field_simp
  linear_combination -h

/-- Off-diagonal modal coordinates of the eigenvector derivative. -/
@[powerlib_foundation] theorem eigenvector_deriv_coeff
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ α, A α *ᵥ v α = lam α • v α) (hv0 : v α₀ = mb.v i) (hl0 : lam α₀ = mb.eig i)
    {j : n} (hj : j ≠ i) (hsimple : mb.eig j ≠ mb.eig i) :
    mb.ψ j ⬝ᵥ v' = mb.ψ j ⬝ᵥ (A' *ᵥ mb.v i) / (mb.eig i - mb.eig j) :=
  eigenvector_deriv_coeff_of_eventually mb hA hv hlam (Eventually.of_forall heig) hv0 hl0 hj
    hsimple

/-- **Eigenvector derivative** of a simple eigenpair, along a branch defined near `α₀`. -/
@[powerlib_foundation] theorem eigenvector_deriv_of_eventually
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ᶠ α in 𝓝 α₀, A α *ᵥ v α = lam α • v α) (hv0 : v α₀ = mb.v i)
    (hl0 : lam α₀ = mb.eig i) (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i) :
    v' = ∑ j ∈ Finset.univ.erase i,
        (mb.ψ j ⬝ᵥ (A' *ᵥ mb.v i) / (mb.eig i - mb.eig j)) • mb.v j +
      (mb.ψ i ⬝ᵥ v') • mb.v i := by
  conv_lhs => rw [mb.eq_sum_modal v']
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji := Finset.ne_of_mem_erase hj
  rw [eigenvector_deriv_coeff_of_eventually mb hA hv hlam heig hv0 hl0 hji (hsimple j hji)]

/-- **Eigenvector derivative** of a simple eigenpair. -/
@[powerlib_foundation] theorem eigenvector_deriv
    (hA : ∀ i j, HasDerivAt (fun α => A α i j) (A' i j) α₀)
    (hv : ∀ j, HasDerivAt (fun α => v α j) (v' j) α₀) (hlam : HasDerivAt lam lam' α₀)
    (heig : ∀ α, A α *ᵥ v α = lam α • v α) (hv0 : v α₀ = mb.v i) (hl0 : lam α₀ = mb.eig i)
    (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i) :
    v' = ∑ j ∈ Finset.univ.erase i,
        (mb.ψ j ⬝ᵥ (A' *ᵥ mb.v i) / (mb.eig i - mb.eig j)) • mb.v j +
      (mb.ψ i ⬝ᵥ v') • mb.v i :=
  eigenvector_deriv_of_eventually mb hA hv hlam (Eventually.of_forall heig) hv0 hl0 hsimple

end GivenBranch

/-! ## Existence of a differentiable branch (implicit function theorem) -/

/-- The characteristic polynomial `(p, z) ↦ det(zI − A(p))` is `C¹` jointly in the parameter and
the spectral variable when the entries of `A` are `C¹` at `p₀`. -/
@[powerlib_foundation] theorem contDiffAt_charpoly_eval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
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
@[powerlib_foundation] theorem exists_eigenvalue_branch {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {A : E → Matrix n n ℂ} {p₀ : E} {lam₀ : ℂ}
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

/-! ## Differentiable eigenvector branch (implicit function theorem on the bordered system) -/

/-- **No Jordan chain of length two at a simple eigenvalue.** If `λ₀` has algebraic multiplicity
one in `charpoly M`, `M v₀ = λ₀ v₀` with `v₀ ≠ 0`, and `(M − λ₀) x = c v₀`, then `x` is a multiple
of `v₀`. Indeed `x` lies in the generalized eigenspace `ker (M − λ₀)²`, whose dimension is at most
the root multiplicity (Mathlib `LinearMap.finrank_genEigenspace_le`), hence is the line
`span v₀`. -/
@[powerlib_foundation] theorem eq_smul_of_mulVec_sub_eq_smul {M : Matrix n n ℂ} {lam₀ : ℂ}
    {v₀ x : n → ℂ}
    (hsimple : M.charpoly.rootMultiplicity lam₀ = 1) (hv₀ : v₀ ≠ 0)
    (hMv : M *ᵥ v₀ = lam₀ • v₀) {c : ℂ} (hx : M *ᵥ x - lam₀ • x = c • v₀) :
    ∃ a : ℂ, x = a • v₀ := by
  set φ : Module.End ℂ (n → ℂ) := Matrix.toLin' M with hφdef
  have hφ : ∀ y, (φ - lam₀ • 1) y = M *ᵥ y - lam₀ • y := fun y => by
    simp [φ, Matrix.toLin'_apply]
  have hfin : finrank ℂ (φ.genEigenspace lam₀ (2 : ℕ)) ≤ 1 := by
    have := LinearMap.finrank_genEigenspace_le φ lam₀ 2
    rwa [hφdef, Matrix.charpoly_toLin', hsimple] at this
  have hmem : ∀ y, M *ᵥ (M *ᵥ y - lam₀ • y) - lam₀ • (M *ᵥ y - lam₀ • y) = 0 →
      y ∈ φ.genEigenspace lam₀ (2 : ℕ) := by
    intro y hy
    rw [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker, sq, Module.End.mul_apply, hφ, hφ]
    exact hy
  have hv₀m := hmem v₀ (by rw [hMv, sub_self, mulVec_zero, smul_zero, sub_zero])
  have hxm := hmem x (by rw [hx, mulVec_smul, hMv, smul_comm, sub_self])
  have hne : (⟨v₀, hv₀m⟩ : φ.genEigenspace lam₀ (2 : ℕ)) ≠ 0 := by
    intro h; exact hv₀ (congrArg Subtype.val h)
  have h1 : finrank ℂ (φ.genEigenspace lam₀ (2 : ℕ)) = 1 :=
    le_antisymm hfin (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp h1 ⟨x, hxm⟩
  exact ⟨a, (congrArg Subtype.val ha).symm⟩

/-- **The bordered matrix of a simple eigenpair is injective**: if `λ₀` is a simple eigenvalue of
`M` with eigenvector `v₀` and `wᵀ v₀ ≠ 0`, then `(M − λ₀) x − c v₀ = 0` and `wᵀ x = 0` force
`x = 0` and `c = 0`; i.e. `[[M − λ₀ I, −v₀], [wᵀ, 0]]` is nonsingular. -/
@[powerlib_foundation] theorem bordered_injective {M : Matrix n n ℂ} {lam₀ : ℂ} {v₀ w : n → ℂ}
    (hsimple : M.charpoly.rootMultiplicity lam₀ = 1) (hMv : M *ᵥ v₀ = lam₀ • v₀)
    (hw : w ⬝ᵥ v₀ ≠ 0) {x : n → ℂ} {c : ℂ} (h1 : M *ᵥ x - lam₀ • x - c • v₀ = 0)
    (h2 : w ⬝ᵥ x = 0) : x = 0 ∧ c = 0 := by
  have hv₀ : v₀ ≠ 0 := fun h => hw (by rw [h, dotProduct_zero])
  obtain ⟨a, rfl⟩ := eq_smul_of_mulVec_sub_eq_smul hsimple hv₀ hMv (sub_eq_zero.mp h1)
  rw [dotProduct_smul, smul_eq_mul, mul_eq_zero] at h2
  have ha : a = 0 := h2.resolve_right hw
  subst ha
  refine ⟨zero_smul _ _, ?_⟩
  simp only [zero_smul, mulVec_zero, smul_zero, sub_zero, zero_sub, neg_eq_zero,
    smul_eq_zero] at h1
  exact h1.resolve_right hv₀

section Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Differentiable eigenvector branch through a simple eigenvalue** (implicit function theorem
on the bordered eigen-system). For a parameter `p` in a real Banach space, entries of `A(p)`
`C¹` at `p₀`, `λ₀` a simple eigenvalue of `A(p₀)` (root multiplicity one in `charpoly`) with
eigenvector `v₀`, and a normalising vector `w` with `wᵀ v₀ ≠ 0`, there are `v(p)` and `λ(p)`,
`C¹` at `p₀`, with `v(p₀) = v₀`, `λ(p₀) = λ₀`, and for `p` near `p₀`
`A(p) v(p) = λ(p) v(p)`, `wᵀ v(p) = wᵀ v₀` and `v(p) ≠ 0`; near `(p₀, v₀, λ₀)` every normalised
eigenpair `(A(p) v = λ v, wᵀ v = wᵀ v₀)` is `(v(p), λ(p))`. -/
@[powerlib_foundation] theorem exists_eigenvector_branch {A : E → Matrix n n ℂ} {p₀ : E} {lam₀ : ℂ}
    {v₀ w : n → ℂ}
    (hA : ∀ i j, ContDiffAt ℝ 1 (fun p => A p i j) p₀)
    (hsimple : (A p₀).charpoly.rootMultiplicity lam₀ = 1) (hv₀ : A p₀ *ᵥ v₀ = lam₀ • v₀)
    (hw : w ⬝ᵥ v₀ ≠ 0) :
    ∃ (v : E → n → ℂ) (lam : E → ℂ), v p₀ = v₀ ∧ lam p₀ = lam₀ ∧
      ContDiffAt ℝ 1 v p₀ ∧ ContDiffAt ℝ 1 lam p₀ ∧
      (∀ᶠ p in 𝓝 p₀, A p *ᵥ v p = lam p • v p ∧ w ⬝ᵥ v p = w ⬝ᵥ v₀ ∧ v p ≠ 0) ∧
      (∀ᶠ q in 𝓝 (p₀, (v₀, lam₀)), (A q.1 *ᵥ q.2.1 = q.2.2 • q.2.1 ∧ w ⬝ᵥ q.2.1 = w ⬝ᵥ v₀) ↔
        (v q.1 = q.2.1 ∧ lam q.1 = q.2.2)) := by
  set F : E × ((n → ℂ) × ℂ) → (n → ℂ) × ℂ :=
    fun q => (A q.1 *ᵥ q.2.1 - q.2.2 • q.2.1, w ⬝ᵥ q.2.1 - w ⬝ᵥ v₀) with hFdef
  set u : E × ((n → ℂ) × ℂ) := (p₀, (v₀, lam₀)) with hu
  have hFu : F u = 0 := by simp [F, u, hv₀]
  have hpn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hF : ContDiffAt ℝ 1 F u := by
    have hcoord : ∀ j, ContDiffAt ℝ 1 (fun q : E × ((n → ℂ) × ℂ) => q.2.1 j) u := fun j =>
      (contDiff_apply ℝ ℂ j).contDiffAt.comp u contDiffAt_snd.fst
    have hlam : ContDiffAt ℝ 1 (fun q : E × ((n → ℂ) × ℂ) => q.2.2) u := contDiffAt_snd.snd
    refine ContDiffAt.prodMk ?_ ?_
    · refine contDiffAt_pi.mpr fun i => ?_
      simp only [Pi.sub_apply, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      exact (ContDiffAt.sum fun j _ => ((hA i j).comp u contDiffAt_fst).mul (hcoord j)).sub
        (hlam.mul (hcoord i))
    · simp only [dotProduct]
      exact (ContDiffAt.sum fun j _ => contDiffAt_const.mul (hcoord j)).sub contDiffAt_const
  -- the bordered linear map
  set Llin : ((n → ℂ) × ℂ) →ₗ[ℝ] (n → ℂ) × ℂ :=
    { toFun := fun y => (A p₀ *ᵥ y.1 - lam₀ • y.1 - y.2 • v₀, w ⬝ᵥ y.1)
      map_add' := fun y z => by
        ext <;> simp [mulVec_add, dotProduct_add, add_smul, smul_add]
        ring
      map_smul' := fun r y => by
        ext <;> simp [mulVec_smul, dotProduct_smul, smul_sub, smul_comm r]
        ring } with hLlin
  set L : ((n → ℂ) × ℂ) →L[ℝ] (n → ℂ) × ℂ := LinearMap.toContinuousLinearMap Llin with hL
  set g : (n → ℂ) × ℂ → (n → ℂ) × ℂ := fun y => F (p₀, y) with hgdef
  have hg : HasFDerivAt g L (v₀, lam₀) := by
    set M₁ : (n → ℂ) →L[ℝ] (n → ℂ) := LinearMap.toContinuousLinearMap
      { toFun := fun x => A p₀ *ᵥ x, map_add' := mulVec_add _,
        map_smul' := fun r x => mulVec_smul _ r x }
    set W₁ : (n → ℂ) →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
      { toFun := fun x => w ⬝ᵥ x, map_add' := dotProduct_add w,
        map_smul' := fun r x => dotProduct_smul r w x }
    have h1 := (M₁.comp (ContinuousLinearMap.fst ℝ (n → ℂ) ℂ)).hasFDerivAt
      (x := ((v₀, lam₀) : (n → ℂ) × ℂ))
    have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := ((v₀, lam₀) : (n → ℂ) × ℂ))).smul
      (hasFDerivAt_fst (𝕜 := ℝ) (p := ((v₀, lam₀) : (n → ℂ) × ℂ)))
    have h3 := (W₁.comp (ContinuousLinearMap.fst ℝ (n → ℂ) ℂ)).hasFDerivAt
      (x := ((v₀, lam₀) : (n → ℂ) × ℂ))
    have h4 := (h1.sub h2).prodMk (h3.sub_const (w ⬝ᵥ v₀))
    refine (h4.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · refine ContinuousLinearMap.ext fun y => ?_
      simp [L, Llin, M₁, W₁, sub_sub]
    · simp [g, F, M₁, W₁]
  have hD : fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ E ((n → ℂ) × ℂ) = L := by
    have h1 : HasFDerivAt g (fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ E ((n → ℂ) × ℂ))
        (v₀, lam₀) := by
      have hin : HasFDerivAt (fun y : (n → ℂ) × ℂ => (p₀, y))
          (ContinuousLinearMap.inr ℝ E ((n → ℂ) × ℂ)) (v₀, lam₀) :=
        (hasFDerivAt_const p₀ _).prodMk (hasFDerivAt_id _)
      exact (hF.differentiableAt hpn).hasFDerivAt.comp (v₀, lam₀) hin
    exact h1.unique hg
  have hLinj : Function.Injective Llin := by
    refine (injective_iff_map_eq_zero Llin).mpr fun y hy => ?_
    have h1 := congrArg Prod.fst hy
    have h2 := congrArg Prod.snd hy
    simp only [Llin, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_zero, Prod.snd_zero] at h1 h2
    obtain ⟨hy1, hy2⟩ := bordered_injective hsimple hv₀ hw h1 h2
    exact Prod.ext hy1 hy2
  have hinv : (fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ E ((n → ℂ) × ℂ)).IsInvertible := by
    rw [hD]
    exact ⟨(LinearEquiv.ofInjectiveEndo Llin hLinj).toContinuousLinearEquiv,
      ContinuousLinearMap.ext fun y => rfl⟩
  set φ := hF.implicitFunction hpn hinv with hφ
  have hφ0 : φ p₀ = (v₀, lam₀) := hF.implicitFunction_apply_self hpn hinv
  have hφC : ContDiffAt ℝ 1 φ p₀ := hF.contDiffAt_implicitFunction hpn hinv
  refine ⟨fun p => (φ p).1, fun p => (φ p).2, congrArg Prod.fst hφ0, congrArg Prod.snd hφ0,
    hφC.fst, hφC.snd, ?_, ?_⟩
  · filter_upwards [hF.eventually_apply_implicitFunction hpn hinv] with p hp
    rw [hFu] at hp
    have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    simp only [F, Prod.fst_zero, Prod.snd_zero] at h1 h2
    refine ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2, fun h => hw ?_⟩
    rw [← sub_eq_zero.mp h2, h, dotProduct_zero]
  · filter_upwards [hF.eventually_apply_eq_iff_implicitFunction hpn hinv] with q hq
    rw [hFu] at hq
    have e : F q = 0 ↔ (A q.1 *ᵥ q.2.1 = q.2.2 • q.2.1 ∧ w ⬝ᵥ q.2.1 = w ⬝ᵥ v₀) := by
      simp only [F, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, sub_eq_zero]
    rw [← e, hq, Prod.ext_iff]

/-- Eigenvector branch through any eigenvector `v₀ ≠ 0` of a simple eigenvalue, normalised by
the coordinate `v(p)_k = v₀ k` for some `k` with `v₀ k ≠ 0`. -/
@[powerlib_foundation] theorem exists_eigenvector_branch_of_ne_zero {A : E → Matrix n n ℂ}
    {p₀ : E} {lam₀ : ℂ} {v₀ : n → ℂ} (hA : ∀ i j, ContDiffAt ℝ 1 (fun p => A p i j) p₀)
    (hsimple : (A p₀).charpoly.rootMultiplicity lam₀ = 1) (hv₀ : A p₀ *ᵥ v₀ = lam₀ • v₀)
    (hne : v₀ ≠ 0) :
    ∃ (v : E → n → ℂ) (lam : E → ℂ), v p₀ = v₀ ∧ lam p₀ = lam₀ ∧
      ContDiffAt ℝ 1 v p₀ ∧ ContDiffAt ℝ 1 lam p₀ ∧
      ∀ᶠ p in 𝓝 p₀, A p *ᵥ v p = lam p • v p ∧ v p ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
  have hw : Pi.single k (1 : ℂ) ⬝ᵥ v₀ ≠ 0 := by
    rw [single_dotProduct, one_mul]; exact hk
  obtain ⟨v, lam, h0, h1, h2, h3, h4, -⟩ := exists_eigenvector_branch hA hsimple hv₀ hw
  exact ⟨v, lam, h0, h1, h2, h3, h4.mono fun p hp => ⟨hp.1, hp.2.2⟩⟩

end Branch

section OneParameter

variable {A : ℝ → Matrix n n ℂ} {A' : Matrix n n ℂ} {α₀ : ℝ}

/-- **Derivatives of a simple eigenpair, one real parameter, no diagonalisability.** For `A(α)`
with entries `C¹` at `α₀` and derivative `A'`, a simple eigenvalue `λ₀` of `A(α₀)` with
eigenvector `v₀`, and `wᵀ v₀ ≠ 0`, the branch of `exists_eigenvector_branch` has derivatives
`v'`, `λ'` at `α₀` with `A' v₀ + A(α₀) v' = λ' v₀ + λ₀ v'`, `wᵀ v' = 0`, and
`λ' (uᵀ v₀) = uᵀ A' v₀` for every left eigenvector `uᵀ A(α₀) = λ₀ uᵀ`. -/
@[powerlib_foundation] theorem exists_eigenpair_branch_deriv {lam₀ : ℂ} {v₀ w : n → ℂ}
    (hA : ∀ k l, ContDiffAt ℝ 1 (fun α => A α k l) α₀)
    (hA' : ∀ k l, HasDerivAt (fun α => A α k l) (A' k l) α₀)
    (hsimple : (A α₀).charpoly.rootMultiplicity lam₀ = 1) (hv₀ : A α₀ *ᵥ v₀ = lam₀ • v₀)
    (hw : w ⬝ᵥ v₀ ≠ 0) :
    ∃ (v : ℝ → n → ℂ) (lam : ℝ → ℂ) (v' : n → ℂ) (lam' : ℂ), v α₀ = v₀ ∧ lam α₀ = lam₀ ∧
      (∀ᶠ α in 𝓝 α₀, A α *ᵥ v α = lam α • v α ∧ w ⬝ᵥ v α = w ⬝ᵥ v₀) ∧
      (∀ k, HasDerivAt (fun α => v α k) (v' k) α₀) ∧ HasDerivAt lam lam' α₀ ∧
      A' *ᵥ v₀ + A α₀ *ᵥ v' = lam' • v₀ + lam₀ • v' ∧ w ⬝ᵥ v' = 0 ∧
      ∀ u : n → ℂ, vecMul u (A α₀) = lam₀ • u → lam' * (u ⬝ᵥ v₀) = u ⬝ᵥ (A' *ᵥ v₀) := by
  obtain ⟨v, lam, hv0, hl0, hvC, hlC, hev, -⟩ :=
    exists_eigenvector_branch (E := ℝ) hA hsimple hv₀ hw
  have hpn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hvk : ∀ k, HasDerivAt (fun α => v α k) (deriv (fun α => v α k) α₀) α₀ := fun k =>
    ((contDiffAt_pi.mp hvC k).differentiableAt hpn).hasDerivAt
  have hlam : HasDerivAt lam (deriv lam α₀) α₀ := (hlC.differentiableAt hpn).hasDerivAt
  set v' : n → ℂ := fun k => deriv (fun α => v α k) α₀ with hv'def
  set lam' := deriv lam α₀ with hlam'def
  have heig : ∀ᶠ α in 𝓝 α₀, A α *ᵥ v α = lam α • v α := hev.mono fun α h => h.1
  have hbr := eigen_branch_deriv_of_eventually hA' hvk hlam heig
  rw [hv0, hl0] at hbr
  have hnorm : w ⬝ᵥ v' = 0 := by
    have h1 : HasDerivAt (fun α => w ⬝ᵥ v α) (w ⬝ᵥ v') α₀ := by
      simp only [dotProduct]
      exact HasDerivAt.fun_sum fun k _ => (hvk k).const_mul (w k)
    have h2 : HasDerivAt (fun α => w ⬝ᵥ v α) 0 α₀ :=
      (hasDerivAt_const α₀ (w ⬝ᵥ v₀)).congr_of_eventuallyEq (hev.mono fun α h => h.2.1)
    exact h1.unique h2
  refine ⟨v, lam, v', lam', hv0, hl0, hev.mono fun α h => ⟨h.1, h.2.1⟩, hvk, hlam, hbr, hnorm,
    fun u hu => ?_⟩
  have h := congrArg (fun z => u ⬝ᵥ z) hbr
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at h
  rw [dotProduct_mulVec u (A α₀) v', hu, smul_dotProduct, smul_eq_mul] at h
  linear_combination -h

/-- **Unconditional eigenvalue and eigenvector derivatives of a simple eigenpair** (removes the
branch premise of `eigenvalue_deriv` / `eigenvector_deriv`). For `A(α)` with entries `C¹` at
`α₀` and derivative `A'`, a modal basis of `A(α₀)` and a simple eigenvalue `λᵢ`
(`λⱼ ≠ λᵢ` for `j ≠ i`), there is an eigen-branch `A(α) v(α) = λ(α) v(α)` near `α₀`, normalised
by `ψᵢᵀ v(α) = 1`, through `(λᵢ, vᵢ)`, with `λ'(α₀) = ψᵢᵀ A' vᵢ` and
`v'(α₀) = Σ_{j≠i} (ψⱼᵀ A' vᵢ)/(λᵢ − λⱼ) vⱼ`. -/
@[powerlib_foundation] theorem eigenpair_deriv_of_simple (mb : ModalBasis (A α₀)) {i : n}
    (hA : ∀ k l, ContDiffAt ℝ 1 (fun α => A α k l) α₀)
    (hA' : ∀ k l, HasDerivAt (fun α => A α k l) (A' k l) α₀)
    (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i) :
    ∃ (v : ℝ → n → ℂ) (lam : ℝ → ℂ), v α₀ = mb.v i ∧ lam α₀ = mb.eig i ∧
      (∀ᶠ α in 𝓝 α₀, A α *ᵥ v α = lam α • v α ∧ mb.ψ i ⬝ᵥ v α = 1) ∧
      HasDerivAt lam (mb.ψ i ⬝ᵥ (A' *ᵥ mb.v i)) α₀ ∧
      ∀ k, HasDerivAt (fun α => v α k)
        ((∑ j ∈ Finset.univ.erase i,
          (mb.ψ j ⬝ᵥ (A' *ᵥ mb.v i) / (mb.eig i - mb.eig j)) • mb.v j) k) α₀ := by
  have hroot : (A α₀).charpoly.rootMultiplicity (mb.eig i) = 1 := by
    rw [mb.rootMultiplicity_eq_card, Finset.card_eq_one]
    refine ⟨i, Finset.ext fun j => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => by_contra fun hj => hsimple j hj h, fun h => h ▸ rfl⟩
  have hψv : mb.ψ i ⬝ᵥ mb.v i = 1 := by rw [mb.ψ_dot_v]; simp
  obtain ⟨v, lam, v', lam', hv0, hl0, hev, hvk, hlam, -, hnorm, -⟩ :=
    exists_eigenpair_branch_deriv hA hA' hroot (mb.mulVec_v i) (by rw [hψv]; exact one_ne_zero)
  have heig : ∀ᶠ α in 𝓝 α₀, A α *ᵥ v α = lam α • v α := hev.mono fun α h => h.1
  have hl' := eigenvalue_deriv_of_eventually mb hA' hvk hlam heig hv0 hl0
  have hv' := eigenvector_deriv_of_eventually mb hA' hvk hlam heig hv0 hl0 hsimple
  rw [hnorm, zero_smul, add_zero] at hv'
  refine ⟨v, lam, hv0, hl0, hev.mono fun α h => ⟨h.1, h.2.trans hψv⟩, hl' ▸ hlam, fun k => ?_⟩
  rw [← hv']
  exact hvk k

/-- **Unconditional `eigenvalue_deriv`**: for `A(α)` with entries `C¹` at `α₀`, a modal basis of
`A(α₀)` and a simple eigenvalue `λᵢ`, there is an eigenvalue branch `λ(α)` of `A(α)` near `α₀`
(with eigenvectors `v(α) ≠ 0`) through `λᵢ` whose derivative is `λ'(α₀) = ψᵢᵀ A' vᵢ`. -/
@[powerlib_foundation] theorem eigenvalue_deriv_of_simple (mb : ModalBasis (A α₀)) {i : n}
    (hA : ∀ k l, ContDiffAt ℝ 1 (fun α => A α k l) α₀)
    (hA' : ∀ k l, HasDerivAt (fun α => A α k l) (A' k l) α₀)
    (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i) :
    ∃ lam : ℝ → ℂ, lam α₀ = mb.eig i ∧
      (∀ᶠ α in 𝓝 α₀, ∃ x : n → ℂ, x ≠ 0 ∧ A α *ᵥ x = lam α • x) ∧
      HasDerivAt lam (mb.ψ i ⬝ᵥ (A' *ᵥ mb.v i)) α₀ := by
  obtain ⟨v, lam, -, hl0, hev, hlam, -⟩ := eigenpair_deriv_of_simple mb hA hA' hsimple
  refine ⟨lam, hl0, hev.mono fun α h => ⟨v α, fun h0 => ?_, h.1⟩, hlam⟩
  have := h.2
  rw [h0, dotProduct_zero] at this
  exact zero_ne_one this

end OneParameter

/-! ## Root branches of a scalar equation: `dλ/dK = −c / P'(λ)` -/

section RootBranch

/-- Any differentiable root branch of `P(λ) + cK = 0` through a simple root has
`dλ/dK = −c / P'(λ)`. -/
@[powerlib_foundation] theorem root_branch_deriv {P : ℂ → ℂ} {P' c lam' : ℂ} {lam : ℝ → ℂ}
    {K0 : ℝ} (hP : HasDerivAt P P' (lam K0)) (hlam : HasDerivAt lam lam' K0)
    (hroot : ∀ᶠ K in 𝓝 K0, P (lam K) + c * K = 0) (hP' : P' ≠ 0) :
    lam' = -c / P' := by
  have h1 : HasDerivAt (fun K : ℝ => P (lam K) + c * K) (P' * lam' + c) K0 := by
    have := (hP.comp K0 hlam).add ((hasDerivAt_id K0).ofReal_comp.const_mul c)
    convert this using 1
    · funext K; simp
    · simp
  have h2 : HasDerivAt (fun K : ℝ => P (lam K) + c * K) 0 K0 :=
    (hasDerivAt_const K0 (0 : ℂ)).congr_of_eventuallyEq hroot
  have := h1.unique h2
  field_simp
  linear_combination this

/-- A simple root continues to a differentiable root branch (inverse function theorem), with
`dλ/dK = −c / P'(λ₀)`. -/
@[powerlib_foundation] theorem exists_root_branch {P : ℂ → ℂ} {P' lam0 c : ℂ} {K0 : ℝ}
    (hP : HasStrictDerivAt P P' lam0) (hP' : P' ≠ 0) (hroot : P lam0 + c * K0 = 0) :
    ∃ lam : ℝ → ℂ, lam K0 = lam0 ∧ (∀ᶠ K in 𝓝 K0, P (lam K) + c * K = 0) ∧
      HasDerivAt lam (-c / P') K0 := by
  set g : ℝ → ℂ := fun K => -c * K
  have hg0 : g K0 = P lam0 := by simp only [g]; linear_combination -hroot
  have hgd : HasDerivAt g (-c) K0 := by
    simpa [g] using (hasDerivAt_id K0).ofReal_comp.const_mul (-c)
  set L := hP.localInverse P P' lam0 hP'
  refine ⟨fun K => L (g K), ?_, ?_, ?_⟩
  · show L (g K0) = lam0
    rw [hg0]
    exact (hP.eventually_left_inverse hP').self_of_nhds
  · have hcont : Tendsto g (𝓝 K0) (𝓝 (P lam0)) := by
      rw [← hg0]; exact hgd.continuousAt.tendsto
    filter_upwards [hcont.eventually (hP.eventually_right_inverse hP')] with K hK
    rw [hK]
    simp only [g]
    ring
  · have hL := (hP.to_localInverse hP').hasDerivAt
    rw [← hg0] at hL
    have := hL.comp K0 hgd
    convert this using 1
    · rfl
    · rw [div_eq_inv_mul]

end RootBranch

end powerlib.Modal
