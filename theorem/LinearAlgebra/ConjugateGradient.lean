import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! # Conjugate gradients: Galerkin optimality and the polynomial (min–max) error bound

Foundation layer (category B; general numerical linear algebra).

Source: work-sync `theory/T-linear-algebra.md` §1.5–§1.6 (CG minimizes `‖x − x*‖_A` over
`x₀ + K_m`), §2.4 (polynomial characterization of the CG error).

Setting: real symmetric positive semidefinite `A` (indexed by `Fin k`), `‖u‖_A² = uᵀAu`, a
solution `x*` of `Ax* = b`, the Krylov space `K_m(A, r₀) = span{r₀, Ar₀, …, A^{m−1}r₀}` with
`r₀ = b − Ax₀`. The CG recursion itself is not formalized; its iterate is characterized by the
Galerkin condition `x_m ∈ x₀ + K_m`, `b − A x_m ⊥ K_m`, which is what CG computes.

Results.
* `galerkin_optimal`: any `x_m ∈ x₀ + S` whose residual is orthogonal to the subspace `S`
  minimizes `‖x − x*‖_A` over `x₀ + S` (A-norm optimality of CG).
* `polyIterate_mem`: for a polynomial `p` with `p(0) = 1`, `deg p ≤ m`, the point
  `x* + p(A)(x₀ − x*)` lies in `x₀ + K_m(A, r₀)`.
* `aeval_conj`: `p(U diag(λ) Uᵀ) = U diag(p(λ)) Uᵀ` for orthogonal `U`.
* `anorm_poly_le`: `‖p(A) e‖_A ≤ maxᵢ |p(λᵢ)| ‖e‖_A` (spectral theorem, Mathlib
  `Matrix.IsHermitian.spectral_theorem`).
* `cg_minmax`: the Galerkin iterate satisfies `‖x_m − x*‖_A² ≤ M² ‖x₀ − x*‖_A²` for every
  `p(0) = 1`, `deg p ≤ m` with `|p(λᵢ)| ≤ M` on the spectrum.

Correction (`T-linear-algebra` §2.4): the note states "CG 第 `m` 步残差 `≤ 2 · min_p max_λ |p(λ)| ‖r₀‖_A`".
The correct statement is for the **error** in the `A`-norm and has **no factor 2**:
`‖x_m − x*‖_A ≤ min_{p(0)=1, deg p ≤ m} max_{λ∈σ(A)} |p(λ)| · ‖x₀ − x*‖_A` (`cg_minmax`); the factor
2 appears only after inserting the Chebyshev bound
`min_p max |p| ≤ 2((√κ−1)/(√κ+1))^m` (§1.6), which is not formalized here (UNPROVED: Chebyshev
extremal bound).
-/

noncomputable section
namespace powerlib.LinearAlgebra
open Matrix Polynomial

variable {k : ℕ}

/-- `‖u‖_A² = uᵀ A u`. -/
def anorm2 (A : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) : ℝ := u ⬝ᵥ (A *ᵥ u)

/-- Krylov space `K_m(A, r) = span{r, Ar, …, A^{m−1} r}`. -/
def krylov (A : Matrix (Fin k) (Fin k) ℝ) (r : Fin k → ℝ) (m : ℕ) : Submodule ℝ (Fin k → ℝ) :=
  Submodule.span ℝ (Set.range fun j : Fin m => (A ^ (j : ℕ)) *ᵥ r)

/-! ## Galerkin optimality -/

/-- **A-norm optimality**: residual orthogonal to `S` ⇒ minimal `A`-norm error over `x₀ + S`. -/
@[powerlib_foundation] theorem galerkin_optimal {A : Matrix (Fin k) (Fin k) ℝ} (hsym : Aᵀ = A)
    (hpsd : ∀ u, 0 ≤ anorm2 A u) {S : Submodule ℝ (Fin k → ℝ)} {x₀ xm xs b : Fin k → ℝ}
    (hxs : A *ᵥ xs = b) (hxm : xm - x₀ ∈ S) (horth : ∀ s ∈ S, s ⬝ᵥ (b - A *ᵥ xm) = 0)
    (x : Fin k → ℝ) (hx : x - x₀ ∈ S) : anorm2 A (xm - xs) ≤ anorm2 A (x - xs) := by
  set d := x - xm
  have hd : d ∈ S := by
    have := S.sub_mem hx hxm
    simpa [d, sub_sub_sub_cancel_right] using this
  have hres : A *ᵥ (xm - xs) = -(b - A *ᵥ xm) := by rw [mulVec_sub, hxs]; abel
  have hcross : d ⬝ᵥ (A *ᵥ (xm - xs)) = 0 := by
    rw [hres, dotProduct_neg, horth d hd, neg_zero]
  have hcross' : (xm - xs) ⬝ᵥ (A *ᵥ d) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]; exact hcross
  have hsplit : x - xs = (xm - xs) + d := by simp [d]
  rw [hsplit]
  unfold anorm2
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hcross, hcross']
  have := hpsd d
  unfold anorm2 at this
  linarith

/-! ## Polynomial iterates lie in the Krylov space -/

@[powerlib_foundation] theorem aeval_mulVec_mem_krylov {A : Matrix (Fin k) (Fin k) ℝ}
    (r : Fin k → ℝ) {m : ℕ} (q : ℝ[X]) (hq : q.natDegree < m) :
    aeval A q *ᵥ r ∈ krylov A r m := by
  rw [aeval_eq_sum_range, sum_mulVec]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [smul_mulVec]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, ?_⟩, rfl⟩)
  have := Finset.mem_range.mp hj
  omega

/-- `x* + p(A)(x₀ − x*) ∈ x₀ + K_m(A, r₀)` for `p(0) = 1`, `deg p ≤ m`. -/
@[powerlib_foundation] theorem polyIterate_mem {A : Matrix (Fin k) (Fin k) ℝ} {x₀ xs b : Fin k → ℝ}
    (hxs : A *ᵥ xs = b) {m : ℕ} (p : ℝ[X]) (hp0 : p.eval 0 = 1) (hpm : p.natDegree ≤ m) :
    (xs + aeval A p *ᵥ (x₀ - xs)) - x₀ ∈ krylov A (b - A *ᵥ x₀) m := by
  -- `p = 1 + X q`
  set q := (p - 1).divX
  have hdecomp : p = 1 + X * q := by
    have h := X_mul_divX_add (p - 1)
    have hc : (p - 1).coeff 0 = 0 := by
      rw [coeff_sub, coeff_zero_eq_eval_zero, hp0, coeff_one_zero, sub_self]
    rw [hc, C_0, add_zero] at h
    rw [h]; ring
  have hcomm : A * aeval A q = aeval A q * A := by
    have : aeval A (X * q) = aeval A (q * X) := by rw [mul_comm]
    simpa [map_mul, aeval_X] using this
  have hp : aeval A p = 1 + A * aeval A q := by
    rw [hdecomp]; simp [map_add, map_mul]
  have hb : b - A *ᵥ x₀ = -(A *ᵥ (x₀ - xs)) := by rw [← hxs, mulVec_sub]; abel
  have hval : (xs + aeval A p *ᵥ (x₀ - xs)) - x₀ = -(aeval A q *ᵥ (b - A *ᵥ x₀)) := by
    rw [hp, hb, mulVec_neg, neg_neg, add_mulVec, one_mulVec, mulVec_mulVec, hcomm]
    abel
  rw [hval]
  refine Submodule.neg_mem _ ?_
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `m = 0`: `p` is the constant `1`, so `q = 0`
    have hp' : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
    have hc1 : p.coeff 0 = 1 := by rw [coeff_zero_eq_eval_zero, hp0]
    have : p - 1 = 0 := by rw [hp', hc1, C_1, sub_self]
    have hq0 : q = 0 := by simp only [q, this, divX_zero]
    rw [hq0, map_zero, zero_mulVec]
    exact Submodule.zero_mem _
  · refine aeval_mulVec_mem_krylov _ q ?_
    have : q.natDegree ≤ m - 1 := by
      simp only [q, natDegree_divX_eq_natDegree_tsub_one]
      have : (p - 1).natDegree ≤ m := (natDegree_sub_le _ _).trans (by simp [hpm])
      omega
    omega

/-! ## Spectral bound -/

@[powerlib_foundation] theorem aeval_diagonal (d : Fin k → ℝ) (p : ℝ[X]) :
    aeval (diagonal d) p = diagonal fun i => p.eval (d i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, diagonal_add]
  | monomial j a =>
    rw [aeval_monomial, diagonal_pow, Matrix.algebraMap_eq_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    simp [eval_monomial]

@[powerlib_foundation] theorem anorm2_conj {A U D : Matrix (Fin k) (Fin k) ℝ} (hU : Uᵀ * U = 1)
    (hA : A = U * D * Uᵀ) (z : Fin k → ℝ) : anorm2 A (U *ᵥ z) = z ⬝ᵥ (D *ᵥ z) := by
  unfold anorm2
  have h1 : A *ᵥ (U *ᵥ z) = U *ᵥ (D *ᵥ z) := by
    rw [hA, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one, ← mulVec_mulVec]
  rw [h1, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hU, one_mulVec]

/-- `p(A) = U diag(p(λ)) Uᵀ` for an orthogonal diagonalization `A = U diag(λ) Uᵀ`. -/
@[powerlib_foundation] theorem aeval_conj {A U : Matrix (Fin k) (Fin k) ℝ} {lam : Fin k → ℝ}
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hA : A = U * diagonal lam * Uᵀ) (p : ℝ[X]) :
    aeval A p = U * diagonal (fun i => p.eval (lam i)) * Uᵀ := by
  have hpow : ∀ j : ℕ, A ^ j = U * diagonal lam ^ j * Uᵀ := by
    intro j
    induction j with
    | zero => simp [hU']
    | succ j ih =>
      rw [pow_succ, ih, hA, pow_succ]
      simp only [Matrix.mul_assoc]
      congr 2
      rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
  rw [← aeval_diagonal]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial j a =>
    rw [aeval_monomial, aeval_monomial, hpow, Algebra.algebraMap_eq_smul_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]

/-- **Spectral bound** `‖p(A) e‖_A² ≤ M² ‖e‖_A²` with `M ≥ maxᵢ |p(λᵢ)|` (`A ⪰ 0`). -/
@[powerlib_foundation] theorem anorm_poly_le {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosSemidef)
    (p : ℝ[X]) {M : ℝ} (hM : ∀ i, |p.eval (hA.1.eigenvalues i)| ≤ M) (e : Fin k → ℝ) :
    anorm2 A (aeval A p *ᵥ e) ≤ M ^ 2 * anorm2 A e := by
  set U : Matrix (Fin k) (Fin k) ℝ := (hA.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)
  set lam := hA.1.eigenvalues
  have hstar : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hUU : Uᵀ * U = 1 := by
    rw [← hstar]; exact Unitary.coe_star_mul_self hA.1.eigenvectorUnitary
  have hUU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hUU
  have hdec : A = U * diagonal lam * Uᵀ := by
    conv_lhs => rw [hA.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    change U * _ * star U = _
    rw [hstar]
    congr 2
  have hpA := aeval_conj hUU hUU' hdec p
  set w := Uᵀ *ᵥ e
  have he : e = U *ᵥ w := by rw [mulVec_mulVec, hUU', one_mulVec]
  have hpe : aeval A p *ᵥ e = U *ᵥ (diagonal (fun i => p.eval (lam i)) *ᵥ w) := by
    rw [hpA]; simp only [w, mulVec_mulVec, Matrix.mul_assoc]
  rw [hpe, anorm2_conj hUU hdec, he, anorm2_conj hUU hdec]
  simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hl : 0 ≤ lam i := hA.eigenvalues_nonneg i
  have hp2 : (p.eval (lam i)) ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM i) 2
  have hw : 0 ≤ lam i * w i ^ 2 := mul_nonneg hl (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hp2 hw]

/-- **CG min–max bound**: the Galerkin iterate `x_m ∈ x₀ + K_m`, `b − A x_m ⊥ K_m`, satisfies
`‖x_m − x*‖_A² ≤ M² ‖x₀ − x*‖_A²` for every `p(0) = 1`, `deg p ≤ m` with `|p(λᵢ)| ≤ M`. -/
@[powerlib_foundation] theorem cg_minmax {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosSemidef)
    {x₀ xm xs b : Fin k → ℝ} (hxs : A *ᵥ xs = b) {m : ℕ}
    (hxm : xm - x₀ ∈ krylov A (b - A *ᵥ x₀) m)
    (horth : ∀ s ∈ krylov A (b - A *ᵥ x₀) m, s ⬝ᵥ (b - A *ᵥ xm) = 0)
    (p : ℝ[X]) (hp0 : p.eval 0 = 1) (hpm : p.natDegree ≤ m) {M : ℝ}
    (hM : ∀ i, |p.eval (hA.1.eigenvalues i)| ≤ M) :
    anorm2 A (xm - xs) ≤ M ^ 2 * anorm2 A (x₀ - xs) := by
  have hsym : Aᵀ = A := by
    have := hA.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hpsd : ∀ u, 0 ≤ anorm2 A u := fun u => by
    have := hA.dotProduct_mulVec_nonneg u
    simpa [anorm2] using this
  have hopt := galerkin_optimal hsym hpsd hxs hxm horth _ (polyIterate_mem hxs p hp0 hpm)
  have hdiff : (xs + aeval A p *ᵥ (x₀ - xs)) - xs = aeval A p *ᵥ (x₀ - xs) := by abel
  rw [hdiff] at hopt
  exact hopt.trans (anorm_poly_le hA p hM _)

end powerlib.LinearAlgebra
