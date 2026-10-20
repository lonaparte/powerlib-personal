import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Multi-parameter Cramér–Rao bound: `Cov_θ(T) ⪰ J 𝓘(θ)⁻¹ Jᵀ`

The multi-parameter Cramér–Rao inequality on finite sample spaces (complete proof) and on
general probability spaces and density families (with the regularity premises stated
explicitly).

Scope.
* Probability / statistics, not an engineering result.
* The parameter is `θ ∈ ℝ^p` (`Fin p → ℝ`), the statistic `T` takes values in `ℝ^k`,
  `ψ(θ) = E_θ[T]` has Jacobian `J` (`k × p`, `LinearMap.toMatrix'`); for an unbiased estimator
  `k = p`, `ψ = id`, `J = I`.
* Finite sample space (sums in place of integrals, so differentiation under the sum is
  automatic): `pmf θ ω` are probability vectors, differentiable in `θ` at the true parameter,
  nonnegative and normalized for `θ'` near `θ` (zero probabilities are allowed: there the
  derivative vanishes because `θ` is a local minimum). Definitions: `scoreFin`
  (`s_i = ∂_i p_θ / p_θ`, equal to `∂_i log p_θ` where `p_θ > 0`, `scoreFin_eq_fderiv_log`),
  `fisherFin` (`𝓘_ij = E_θ[s_i s_j]`), `meanFin`, `covFin`.
* The scalar Gaussian-location bound and the discrete Gaussian Fisher matrix are in
  `theorem/Estimation/CramerRao.lean`; the block (nuisance) inequality is in
  `theorem/Estimation/FisherAlgebra.lean`.

Source: work-sync theory/T-cramer-rao-bound.md §1.1 (`Cov(θ̂) ⪰ 𝓘⁻¹` for unbiased estimators of
a finite-dimensional parameter, Fisher matrix `𝓘_ij = E[∂_iℓ ∂_jℓ]`), §1.5 (vector parameters
with nuisance components); projects/basin-guard/notes/concepts/detection-tolerance.md §2.

Results.
* `crb_fin` — finite sample space: if `E_θ'[T] = ψ(θ')` near `θ` and `𝓘(θ) ≻ 0`, then
  `Cov_θ(T) − J 𝓘(θ)⁻¹ Jᵀ ⪰ 0`.
* `crb_fin_unbiased` — unbiased near `θ` ⇒ `Cov_θ(T) − 𝓘(θ)⁻¹ ⪰ 0`.
* `gramMatrix_posSemidef` — general probability space: the second-moment matrix of
  square-integrable variables is `⪰ 0`.
* `crb_of_regular` — the covariance-inequality form. With the regularity conditions taken as
  explicit premises in integrated form, `E[S_i] = 0` and `E[T_j S_i] = J_ji`, a positive
  definite `𝓘 = E[S Sᵀ]` gives `Cov(T) ⪰ J 𝓘⁻¹ Jᵀ`.
* `crb_density` — densities `p_θ` with respect to any measure `μ`. The regularity premise is the
  differentiation of `θ' ↦ ∫ p_θ' dμ` and `θ' ↦ ∫ p_θ' T_j dμ` under the integral sign, stated
  explicitly as `HasFDerivAt` hypotheses with derivatives `∫ ∂_θ p_θ dμ` and `∫ T_j ∂_θ p_θ dμ`
  (together with integrability of those derivatives and square integrability of `T` and the
  score under `P_θ = p_θ μ`); the conclusion is `Cov_θ(T) ⪰ J 𝓘(θ)⁻¹ Jᵀ`.

Proof (all versions). The joint Gram matrix of `(T − E T, S)` is the positive semidefinite block
matrix `[[Cov, J], [Jᵀ, 𝓘]]`; Mathlib's Schur-complement criterion
`Matrix.PosDef.fromBlocks₂₂` gives `Cov − J 𝓘⁻¹ Jᵀ ⪰ 0`. The cross block is `J` because
`Σ_ω ∂p_θ(ω) = 0` and `Σ_ω T(ω) ∂p_θ(ω) = ∂ψ` (derivatives of the normalization and of the
mean; uniqueness of Fréchet derivatives).

Not formalized.
* Sufficient conditions (domination) that discharge the interchange premise of `crb_density`
  for concrete continuous families such as the multi-parameter Gaussian model.
-/

noncomputable section
namespace powerlib.Estimation

open Matrix Filter
open scoped Topology

/-! ## Finite sample space -/

section Finite

variable {Ω : Type*} [Fintype Ω] {p k : ℕ}

/-- Score `s_i(θ, ω) = ∂_i p_θ(ω) / p_θ(ω)`, i.e. `∂_i log p_θ(ω)` where `p_θ(ω) > 0` (and `0` on
the null set `p_θ(ω) = 0`, which carries no probability). -/
def scoreFin (pmf : (Fin p → ℝ) → Ω → ℝ) (θ : Fin p → ℝ) (ω : Ω) (i : Fin p) : ℝ :=
  fderiv ℝ (fun θ' => pmf θ' ω) θ (Pi.single i 1) / pmf θ ω

/-- Fisher information matrix `𝓘(θ)_ij = E_θ[s_i s_j]` of a family of probability vectors. -/
def fisherFin (pmf : (Fin p → ℝ) → Ω → ℝ) (θ : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => ∑ ω, pmf θ ω * (scoreFin pmf θ ω i * scoreFin pmf θ ω j)

/-- Mean `E_θ[T]` of a vector statistic. -/
def meanFin (pmf : (Fin p → ℝ) → Ω → ℝ) (θ : Fin p → ℝ) (T : Ω → Fin k → ℝ) : Fin k → ℝ :=
  fun j => ∑ ω, pmf θ ω * T ω j

/-- Covariance matrix `Cov_θ(T)`. -/
def covFin (pmf : (Fin p → ℝ) → Ω → ℝ) (θ : Fin p → ℝ) (T : Ω → Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => ∑ ω, pmf θ ω *
    ((T ω i - meanFin pmf θ T i) * (T ω j - meanFin pmf θ T j))

/-- Gram form `X diag(q) Yᵀ`. -/
private lemma mul_diagonal_mul_transpose_apply {a b : Type*} (X : Matrix a Ω ℝ)
    (Y : Matrix b Ω ℝ) (q : Ω → ℝ) (i : a) (j : b) [DecidableEq Ω] :
    (X * diagonal q * Yᵀ) i j = ∑ ω, q ω * (X i ω * Y j ω) := by
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- **Cramér–Rao bound, finite sample space, biased form.**  Let `p_θ` be probability vectors on a
finite set, differentiable in `θ ∈ ℝ^p` at `θ`, and let the statistic `T` have mean `ψ(θ')` for
all `θ'` near `θ`, with `ψ` differentiable at `θ` (Jacobian `J`).  If the Fisher matrix `𝓘(θ)` is
positive definite, then `Cov_θ(T) ⪰ J 𝓘(θ)⁻¹ Jᵀ`.  The probability vectors only need to be
nonnegative near `θ`: zeros are allowed (their derivative vanishes, a local minimum). -/
@[powerlib_foundation] theorem crb_fin {pmf : (Fin p → ℝ) → Ω → ℝ} {θ : Fin p → ℝ}
    {T : Ω → Fin k → ℝ} {ψ : (Fin p → ℝ) → Fin k → ℝ} {J : (Fin p → ℝ) →L[ℝ] (Fin k → ℝ)}
    (hdiff : ∀ ω, DifferentiableAt ℝ (fun θ' => pmf θ' ω) θ)
    (hnn : ∀ᶠ θ' in 𝓝 θ, ∀ ω, 0 ≤ pmf θ' ω)
    (hsum : ∀ᶠ θ' in 𝓝 θ, ∑ ω, pmf θ' ω = 1)
    (hmean : ∀ᶠ θ' in 𝓝 θ, meanFin pmf θ' T = ψ θ')
    (hψ : HasFDerivAt ψ J θ) (hI : (fisherFin pmf θ).PosDef) :
    (covFin pmf θ T - LinearMap.toMatrix' (J : (Fin p → ℝ) →ₗ[ℝ] (Fin k → ℝ)) *
      (fisherFin pmf θ)⁻¹ *
      (LinearMap.toMatrix' (J : (Fin p → ℝ) →ₗ[ℝ] (Fin k → ℝ)))ᵀ).PosSemidef := by
  classical
  set D : Ω → (Fin p → ℝ) →L[ℝ] ℝ := fun ω => fderiv ℝ (fun θ' => pmf θ' ω) θ
  have hD : ∀ ω, HasFDerivAt (fun θ' => pmf θ' ω) (D ω) θ := fun ω => (hdiff ω).hasFDerivAt
  set q : Ω → ℝ := fun ω => pmf θ ω
  have hq : ∀ ω, 0 ≤ q ω := hnn.self_of_nhds
  -- (a) the derivative vanishes on the null set (local minimum)
  have hD0 : ∀ ω, q ω = 0 → D ω = 0 := by
    intro ω h0
    refine IsLocalMin.hasFDerivAt_eq_zero ?_ (hD ω)
    filter_upwards [hnn] with θ' h'
    simp only [q] at h0
    rw [h0]; exact h' ω
  -- (b) differentiating `Σ p = 1`
  have hsumD : ∑ ω, D ω = 0 := by
    have h1 : HasFDerivAt (fun θ' => ∑ ω, pmf θ' ω) (∑ ω, D ω) θ :=
      HasFDerivAt.fun_sum fun ω _ => hD ω
    have h2 : HasFDerivAt (fun θ' => ∑ ω, pmf θ' ω) (0 : (Fin p → ℝ) →L[ℝ] ℝ) θ :=
      (hasFDerivAt_const (1 : ℝ) θ).congr_of_eventuallyEq hsum
    exact h1.unique h2
  -- (c) differentiating `E_θ[T_j] = ψ_j`
  have hmeanD : ∀ j, ∑ ω, T ω j • D ω = (ContinuousLinearMap.proj j).comp J := by
    intro j
    have h1 : HasFDerivAt (fun θ' => ∑ ω, pmf θ' ω * T ω j) (∑ ω, T ω j • D ω) θ :=
      HasFDerivAt.fun_sum fun ω _ => (hD ω).mul_const (T ω j)
    have h2 : HasFDerivAt (fun θ' => ∑ ω, pmf θ' ω * T ω j)
        ((ContinuousLinearMap.proj j).comp J) θ := by
      refine ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j).hasFDerivAt.comp θ
        hψ).congr_of_eventuallyEq ?_
      filter_upwards [hmean] with θ' h'
      show _ = ψ θ' j
      rw [← h']; rfl
    exact h1.unique h2
  -- matrices
  set m := meanFin pmf θ T
  have hm : m = ψ θ := hmean.self_of_nhds
  set X : Matrix (Fin k) Ω ℝ := Matrix.of fun j ω => T ω j - m j
  set S : Matrix (Fin p) Ω ℝ := Matrix.of fun i ω => scoreFin pmf θ ω i
  set W : Matrix Ω Ω ℝ := diagonal q
  set Jm := LinearMap.toMatrix' (J : (Fin p → ℝ) →ₗ[ℝ] (Fin k → ℝ))
  have hcov : X * W * Xᵀ = covFin pmf θ T := by
    ext i j; rw [mul_diagonal_mul_transpose_apply]; rfl
  have hfis : S * W * Sᵀ = fisherFin pmf θ := by
    ext i j; rw [mul_diagonal_mul_transpose_apply]; rfl
  have hcross : X * W * Sᵀ = Jm := by
    ext j i
    rw [mul_diagonal_mul_transpose_apply]
    have e : ∀ ω, q ω * (X j ω * S i ω) =
        T ω j * D ω (Pi.single i 1) - m j * D ω (Pi.single i 1) := by
      intro ω
      simp only [X, S, scoreFin, of_apply]
      by_cases h0 : q ω = 0
      · rw [hD0 ω h0]
        simp [h0]
      · simp only [q] at h0
        field_simp
        ring
    rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h1 := congrArg (fun L : (Fin p → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) (hmeanD j)
    have h2 := congrArg (fun L : (Fin p → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hsumD
    simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, _root_.zero_apply] at h1 h2
    rw [h1, h2, mul_zero, sub_zero]
    show _ = LinearMap.toMatrix' _ j i
    rw [LinearMap.toMatrix'_apply]
    rfl
  -- the joint Gram matrix is positive semidefinite
  have hW : W.PosSemidef := PosSemidef.diagonal fun ω => hq ω
  have hG : (fromRows X S * W * (fromRows X S)ᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hW.mul_mul_conjTranspose_same (fromRows X S)
  have hWt : Wᵀ = W := diagonal_transpose q
  have hblocks : fromRows X S * W * (fromRows X S)ᵀ =
      fromBlocks (covFin pmf θ T) Jm Jmᴴ (fisherFin pmf θ) := by
    rw [fromRows_mul, transpose_fromRows, fromRows_mul_fromCols, hcov, hfis, hcross,
      conjTranspose_eq_transpose_of_trivial, ← hcross]
    congr 1
    rw [transpose_mul, transpose_mul, transpose_transpose, hWt, Matrix.mul_assoc]
  rw [hblocks] at hG
  have hdet : IsUnit (fisherFin pmf θ).det := hI.isUnit.map Matrix.detMonoidHom
  let := invertibleOfIsUnitDet _ hdet
  have := (PosDef.fromBlocks₂₂ (covFin pmf θ T) Jm hI).mp hG
  simpa [conjTranspose_eq_transpose_of_trivial] using this

/-- **Cramér–Rao bound, finite sample space, unbiased form**: `Cov_θ(T) ⪰ 𝓘(θ)⁻¹` for every
statistic that is unbiased for all parameters near `θ`. -/
@[powerlib_foundation] theorem crb_fin_unbiased {pmf : (Fin p → ℝ) → Ω → ℝ} {θ : Fin p → ℝ}
    {T : Ω → Fin p → ℝ}
    (hdiff : ∀ ω, DifferentiableAt ℝ (fun θ' => pmf θ' ω) θ)
    (hnn : ∀ᶠ θ' in 𝓝 θ, ∀ ω, 0 ≤ pmf θ' ω)
    (hsum : ∀ᶠ θ' in 𝓝 θ, ∑ ω, pmf θ' ω = 1)
    (hunb : ∀ᶠ θ' in 𝓝 θ, meanFin pmf θ' T = θ') (hI : (fisherFin pmf θ).PosDef) :
    (covFin pmf θ T - (fisherFin pmf θ)⁻¹).PosSemidef := by
  have := crb_fin hdiff hnn hsum hunb (hasFDerivAt_id θ) hI
  simpa [LinearMap.toMatrix'_id] using this

omit [Fintype Ω] in
/-- Where `p_θ(ω) > 0`, the score is the derivative of the log-likelihood:
`s_i(θ, ω) = ∂_i log p_θ(ω)`. -/
@[powerlib_foundation] theorem scoreFin_eq_fderiv_log {pmf : (Fin p → ℝ) → Ω → ℝ}
    {θ : Fin p → ℝ} {ω : Ω} (hd : DifferentiableAt ℝ (fun θ' => pmf θ' ω) θ)
    (hpos : 0 < pmf θ ω) (i : Fin p) :
    scoreFin pmf θ ω i = fderiv ℝ (fun θ' => Real.log (pmf θ' ω)) θ (Pi.single i 1) := by
  rw [(hd.hasFDerivAt.log hpos.ne').fderiv, scoreFin]
  simp [div_eq_inv_mul]


end Finite

/-! ## General probability space, regularity as explicit premises -/

section Measure

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {p k : ℕ}

/-- Second-moment (Gram) matrix `E[V_u V_v]` of a finite family of random variables. -/
def gramMatrix {ι : Type*} (P : Measure Ω) (V : ι → Ω → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun u v => ∫ ω, V u ω * V v ω ∂P

/-- The Gram matrix of square-integrable random variables is positive semidefinite:
`cᵀ G c = E[(Σ c_u V_u)²] ≥ 0`. -/
@[powerlib_foundation] theorem gramMatrix_posSemidef {ι : Type*} [Fintype ι] {V : ι → Ω → ℝ}
    (hV : ∀ u, MemLp (V u) 2 P) : (gramMatrix P V).PosSemidef := by
  classical
  have hint : ∀ u v, Integrable (fun ω => V u ω * V v ω) P := fun u v =>
    (hV u).integrable_mul (hV v)
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
  · ext u v
    simp only [conjTranspose_apply, star_trivial, gramMatrix, of_apply]
    exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  · simp only [star_trivial]
    have e : c ⬝ᵥ (gramMatrix P V *ᵥ c) = ∫ ω, (∑ u, c u * V u ω) ^ 2 ∂P := by
      have h1 : (fun ω => (∑ u, c u * V u ω) ^ 2) =
          fun ω => ∑ u, ∑ v, c u * c v * (V u ω * V v ω) := by
        funext ω
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
      rw [h1, integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ =>
        (hint u v).const_mul _]
      simp only [dotProduct, mulVec, gramMatrix, of_apply]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [integral_finsetSum _ fun v _ => (hint u v).const_mul _, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [integral_const_mul]; ring
    rw [e]
    exact integral_nonneg fun ω => sq_nonneg _

/-- Covariance matrix `Cov(T)_ij = E[(T_i − E T_i)(T_j − E T_j)]`. -/
def covMatrix (P : Measure Ω) (T : Ω → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => ∫ ω, (T ω i - ∫ ω', T ω' i ∂P) * (T ω j - ∫ ω', T ω' j ∂P) ∂P

/-- Fisher matrix of a score vector `S`: `𝓘_ij = E[S_i S_j]`. -/
def fisherMatrix (P : Measure Ω) (S : Ω → Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => ∫ ω, S ω i * S ω j ∂P

/-- **Cramér–Rao bound (covariance-inequality form).**  On a probability space, let `T` be a
square-integrable statistic in `ℝ^k` and `S` a square-integrable score in `ℝ^p`.  The regularity
conditions — differentiation under the integral sign, `∂_i ∫ p_θ = ∫ ∂_i p_θ` and
`∂_i E_θ[T_j] = E_θ[T_j S_i]` — are taken as explicit premises in their integrated form:
`E[S_i] = 0` and `E[T_j S_i] = J_ji` (`J` = Jacobian of `θ ↦ E_θ[T]`).  If the Fisher matrix
`𝓘 = E[S Sᵀ]` is positive definite, then `Cov(T) ⪰ J 𝓘⁻¹ Jᵀ`; for an unbiased estimator
(`J = I`), `Cov(T) ⪰ 𝓘⁻¹`. -/
@[powerlib_foundation] theorem crb_of_regular [IsProbabilityMeasure P] {T : Ω → Fin k → ℝ}
    {S : Ω → Fin p → ℝ} {J : Matrix (Fin k) (Fin p) ℝ}
    (hT : ∀ j, MemLp (fun ω => T ω j) 2 P) (hS : ∀ i, MemLp (fun ω => S ω i) 2 P)
    (hS0 : ∀ i, ∫ ω, S ω i ∂P = 0) (hTS : ∀ j i, ∫ ω, T ω j * S ω i ∂P = J j i)
    (hI : (fisherMatrix P S).PosDef) :
    (covMatrix P T - J * (fisherMatrix P S)⁻¹ * Jᵀ).PosSemidef := by
  classical
  set m : Fin k → ℝ := fun j => ∫ ω, T ω j ∂P
  set V : Fin k ⊕ Fin p → Ω → ℝ :=
    Sum.elim (fun j ω => T ω j - m j) (fun i ω => S ω i)
  have hV : ∀ u, MemLp (V u) 2 P := by
    rintro (j | i)
    · exact (hT j).sub (memLp_const _)
    · exact hS i
  have hG := gramMatrix_posSemidef hV
  have hcross : ∀ j i, ∫ ω, (T ω j - m j) * S ω i ∂P = J j i := by
    intro j i
    have h1 : Integrable (fun ω => T ω j * S ω i) P := (hT j).integrable_mul (hS i)
    have h2 : Integrable (fun ω => m j * S ω i) P :=
      ((hS i).integrable one_le_two).const_mul _
    simp_rw [sub_mul]
    rw [integral_sub h1 h2, integral_const_mul, hS0, mul_zero, sub_zero, hTS]
  have hblocks : gramMatrix P V = fromBlocks (covMatrix P T) J Jᴴ (fisherMatrix P S) := by
    ext (j | i) (j' | i')
    · rfl
    · simp only [gramMatrix, of_apply, fromBlocks_apply₁₂, V, Sum.elim_inl, Sum.elim_inr]
      exact hcross j i'
    · simp only [gramMatrix, of_apply, fromBlocks_apply₂₁, V, Sum.elim_inl, Sum.elim_inr,
        conjTranspose_apply, star_trivial]
      rw [← hcross j' i]
      exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    · rfl
  rw [hblocks] at hG
  have hdet : IsUnit (fisherMatrix P S).det := hI.isUnit.map Matrix.detMonoidHom
  let := invertibleOfIsUnitDet _ hdet
  have := (PosDef.fromBlocks₂₂ (covMatrix P T) J hI).mp hG
  simpa [conjTranspose_eq_transpose_of_trivial] using this


/-- The law `P_θ = p_θ · μ` of a density family. -/
def densityLaw (μ : Measure Ω) (f : (Fin p → ℝ) → Ω → ℝ) (θ : Fin p → ℝ) : Measure Ω :=
  μ.withDensity fun ω => ENNReal.ofReal (f θ ω)

/-- Score of a density family with parameter derivative `D ω = ∂_θ p_θ(ω)`:
`s_i = ∂_i p_θ / p_θ` (`0` where `p_θ = 0`). -/
def densityScore (f : (Fin p → ℝ) → Ω → ℝ) (D : Ω → (Fin p → ℝ) →L[ℝ] ℝ) (θ : Fin p → ℝ)
    (ω : Ω) (i : Fin p) : ℝ :=
  D ω (Pi.single i 1) / f θ ω

/-- **Cramér–Rao bound for a density family.**  Let `p_θ` be densities with respect to `μ`,
nonnegative near `θ`, normalized near `θ`, differentiable at `θ` with derivative `D ω`, and let the
statistic `T` have mean `ψ(θ')` near `θ` (`ψ` differentiable, Jacobian `J`).  **Regularity premise**
(differentiation under the integral sign, stated explicitly): `θ' ↦ ∫ p_θ'` and
`θ' ↦ ∫ p_θ' T_j` have derivatives `∫ D` and `∫ T_j D` at `θ`.  If `T` and the score are square
integrable under `P_θ` and the Fisher matrix is positive definite, then
`Cov_θ(T) ⪰ J 𝓘(θ)⁻¹ Jᵀ`. -/
@[powerlib_foundation] theorem crb_density {μ : Measure Ω} {f : (Fin p → ℝ) → Ω → ℝ}
    {θ : Fin p → ℝ} {D : Ω → (Fin p → ℝ) →L[ℝ] ℝ} {T : Ω → Fin k → ℝ}
    {ψ : (Fin p → ℝ) → Fin k → ℝ} {J : (Fin p → ℝ) →L[ℝ] (Fin k → ℝ)}
    (hf : ∀ ω, HasFDerivAt (fun θ' => f θ' ω) (D ω) θ)
    (hnn : ∀ ω, ∀ᶠ θ' in 𝓝 θ, 0 ≤ f θ' ω) (hfm : Measurable (f θ))
    (hnorm : ∀ᶠ θ' in 𝓝 θ, ∫ ω, f θ' ω ∂μ = 1)
    (hmean : ∀ j, ∀ᶠ θ' in 𝓝 θ, ∫ ω, f θ' ω * T ω j ∂μ = ψ θ' j) (hψ : HasFDerivAt ψ J θ)
    (hDi : Integrable D μ) (hTDi : ∀ j, Integrable (fun ω => T ω j • D ω) μ)
    (hswap : HasFDerivAt (fun θ' => ∫ ω, f θ' ω ∂μ) (∫ ω, D ω ∂μ) θ)
    (hswapT : ∀ j, HasFDerivAt (fun θ' => ∫ ω, f θ' ω * T ω j ∂μ) (∫ ω, T ω j • D ω ∂μ) θ)
    (hT2 : ∀ j, MemLp (fun ω => T ω j) 2 (densityLaw μ f θ))
    (hS2 : ∀ i, MemLp (fun ω => densityScore f D θ ω i) 2 (densityLaw μ f θ))
    (hI : (fisherMatrix (densityLaw μ f θ) (densityScore f D θ)).PosDef) :
    (covMatrix (densityLaw μ f θ) T - LinearMap.toMatrix' (J : (Fin p → ℝ) →ₗ[ℝ] (Fin k → ℝ)) *
      (fisherMatrix (densityLaw μ f θ) (densityScore f D θ))⁻¹ *
      (LinearMap.toMatrix' (J : (Fin p → ℝ) →ₗ[ℝ] (Fin k → ℝ)))ᵀ).PosSemidef := by
  have hf0 : ∀ ω, 0 ≤ f θ ω := fun ω => (hnn ω).self_of_nhds
  have hD0 : ∀ ω, f θ ω = 0 → D ω = 0 := by
    intro ω h0
    refine IsLocalMin.hasFDerivAt_eq_zero ?_ (hf ω)
    filter_upwards [hnn ω] with θ' h'
    rw [h0]; exact h'
  -- the two integrated identities
  have hsumD : ∫ ω, D ω ∂μ = 0 :=
    hswap.unique ((hasFDerivAt_const (1 : ℝ) θ).congr_of_eventuallyEq hnorm)
  have hmeanD : ∀ j, ∫ ω, T ω j • D ω ∂μ = (ContinuousLinearMap.proj j).comp J := by
    intro j
    refine (hswapT j).unique (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ)
      j).hasFDerivAt.comp θ hψ).congr_of_eventuallyEq ?_)
    filter_upwards [hmean j] with θ' h'
    exact h'
  -- `P_θ` is a probability measure
  have hfi : Integrable (f θ) μ :=
    Integrable.of_integral_ne_zero (by rw [hnorm.self_of_nhds]; exact one_ne_zero)
  have : IsProbabilityMeasure (densityLaw μ f θ) := by
    constructor
    rw [densityLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0), hnorm.self_of_nhds,
      ENNReal.ofReal_one]
  have hE : ∀ g : Ω → ℝ, ∫ ω, g ω ∂(densityLaw μ f θ) = ∫ ω, f θ ω * g ω ∂μ := by
    intro g
    rw [densityLaw, integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact integral_congr_ae (ae_of_all _ fun ω => by
      simp [ENNReal.toReal_ofReal (hf0 ω)])
  have hcancel : ∀ ω (c : ℝ) i, f θ ω * (c * densityScore f D θ ω i) = c * D ω (Pi.single i 1) := by
    intro ω c i
    by_cases h0 : f θ ω = 0
    · simp [densityScore, h0, hD0 ω h0]
    · simp only [densityScore]; field_simp
  refine crb_of_regular hT2 hS2 (fun i => ?_) (fun j i => ?_) hI
  · rw [hE]
    have := fun ω => hcancel ω 1 i
    simp only [one_mul] at this
    simp only [this]
    rw [← ContinuousLinearMap.integral_apply hDi, hsumD]
    rfl
  · rw [hE]
    simp only [hcancel]
    have h1 := ContinuousLinearMap.integral_apply (hTDi j) (Pi.single i 1)
    rw [hmeanD j] at h1
    simp only [_root_.smul_apply, smul_eq_mul] at h1
    rw [← h1, LinearMap.toMatrix'_apply]
    rfl


end Measure

end powerlib.Estimation
