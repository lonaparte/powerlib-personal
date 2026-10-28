import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! # Conjugate gradients: Galerkin optimality and the polynomial (min–max) error bound

The Galerkin iterate of conjugate gradients minimises the `A`-norm error, satisfies the
polynomial min–max bound, and hence the Chebyshev bound in the condition number.

Scope.
* General numerical linear algebra: real symmetric positive semidefinite `A` (indexed by
  `Fin k`), `‖u‖_A² = uᵀAu`, a solution `x*` of `Ax* = b`, the Krylov space
  `K_m(A, r₀) = span{r₀, Ar₀, …, A^{m−1}r₀}` with `r₀ = b − Ax₀`.
* The CG recursion itself is not formalized; its iterate is characterized by the Galerkin
  condition `x_m ∈ x₀ + K_m`, `b − A x_m ⊥ K_m`, which is what CG computes.

Source: work-sync theory/T-linear-algebra.md §1.5–§1.6 (CG minimizes `‖x − x*‖_A` over
`x₀ + K_m`), §2.4 (polynomial characterization of the CG error).

Results.
* `galerkin_optimal` — any `x_m ∈ x₀ + S` whose residual is orthogonal to the subspace `S`
  minimizes `‖x − x*‖_A` over `x₀ + S` (A-norm optimality of CG).
* `polyIterate_mem` — for a polynomial `p` with `p(0) = 1`, `deg p ≤ m`, the point
  `x* + p(A)(x₀ − x*)` lies in `x₀ + K_m(A, r₀)`.
* `aeval_conj` — `p(U diag(λ) Uᵀ) = U diag(p(λ)) Uᵀ` for orthogonal `U`.
* `anorm_poly_le` — `‖p(A) e‖_A ≤ maxᵢ |p(λᵢ)| ‖e‖_A` (spectral theorem, Mathlib
  `Matrix.IsHermitian.spectral_theorem`).
* `cg_minmax` — the Galerkin iterate satisfies `‖x_m − x*‖_A² ≤ M² ‖x₀ − x*‖_A²` for every
  `p(0) = 1`, `deg p ≤ m` with `|p(λᵢ)| ≤ M` on the spectrum.
* `chebyshev_T_ge` — `T_m((u + u⁻¹)/2) ≥ uᵐ/2` for `u > 0` (Mathlib `Chebyshev.T_real_cosh`).
* `exists_chebyshev_poly` — for `0 < lo` there is `p(0) = 1`, `deg p ≤ m`, with
  `|p(x)| ≤ 2((√κ−1)/(√κ+1))^m` on `[lo, hi]`, `κ = hi/lo` (shifted normalised Chebyshev
  polynomial; `|T_m| ≤ 1` on `[−1, 1]` is Mathlib `Chebyshev.abs_eval_T_real_le_one`).
* `cg_chebyshev`, `cg_chebyshev_sqrt` — **CG Chebyshev bound**: if the spectrum of `A` lies in
  `[lo, hi]`, `0 < lo`, then `‖x_m − x*‖_A ≤ 2((√κ−1)/(√κ+1))^m ‖x₀ − x*‖_A`, `κ = hi/lo`.
* `cg_chebyshev_cond` — the same with `κ = λ_max/λ_min` the spectral condition number of a
  positive definite `A` (`k > 0`).

Corrections.
* `T-linear-algebra` §2.4: the note states "CG 第 `m` 步残差
  `≤ 2 · min_p max_λ |p(λ)| ‖r₀‖_A`". The correct statement is for the **error** in the
  `A`-norm and has **no factor 2**:
  `‖x_m − x*‖_A ≤ min_{p(0)=1, deg p ≤ m} max_{λ∈σ(A)} |p(λ)| · ‖x₀ − x*‖_A` (`cg_minmax`); the
  factor 2 appears only after inserting the Chebyshev bound
  `min_p max |p| ≤ 2((√κ−1)/(√κ+1))^m` (§1.6), which gives `cg_chebyshev`.
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
@[tmio T, powerlib_foundation] theorem galerkin_optimal {A : Matrix (Fin k) (Fin k) ℝ} (hsym : Aᵀ = A)
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

/-! ## Chebyshev bound (§1.6) -/

/-- `T_m((u + u⁻¹)/2) ≥ uᵐ / 2` for `u > 0`: with `u = e^θ`, `T_m(cosh θ) = cosh(mθ)`. -/
@[powerlib_foundation] theorem chebyshev_T_ge {u : ℝ} (hu : 0 < u) (m : ℕ) :
    u ^ m / 2 ≤ (Chebyshev.T ℝ (m : ℤ)).eval ((u + u⁻¹) / 2) := by
  have hcosh : Real.cosh (Real.log u) = (u + u⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hu]
  rw [← hcosh, Chebyshev.T_real_cosh, Real.cosh_eq]
  have h1 : Real.exp (((m : ℤ) : ℝ) * Real.log u) = u ^ m := by
    rw [Int.cast_natCast, Real.exp_nat_mul, Real.exp_log hu]
  rw [h1]
  have h2 : 0 < Real.exp (-(((m : ℤ) : ℝ) * Real.log u)) := Real.exp_pos _
  linarith

/-- **Chebyshev polynomial bound**: for `0 < lo` there is a polynomial `p` with `p(0) = 1`,
`deg p ≤ m` and `|p(x)| ≤ 2((√κ − 1)/(√κ + 1))ᵐ` on `[lo, hi]`, `κ = hi / lo`: the shifted,
normalised Chebyshev polynomial `T_m((hi+lo−2x)/(hi−lo)) / T_m((hi+lo)/(hi−lo))` (for `lo < hi`;
`1 − x/lo` or `1` in the degenerate cases). -/
@[powerlib_foundation] theorem exists_chebyshev_poly {lo hi : ℝ} (hlo : 0 < lo) (m : ℕ) :
    ∃ p : ℝ[X], p.eval 0 = 1 ∧ p.natDegree ≤ m ∧
      ∀ x ∈ Set.Icc lo hi, |p.eval x| ≤ 2 * ((√(hi / lo) - 1) / (√(hi / lo) + 1)) ^ m := by
  rcases lt_trichotomy lo hi with hlt | heq | hgt
  · -- the Chebyshev construction
    set q := √(hi / lo) with hq
    have hκ : 1 < hi / lo := (one_lt_div hlo).mpr hlt
    have hq1 : 1 < q := by
      rw [hq, show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt zero_le_one hκ
    have hqq : q ^ 2 = hi / lo := Real.sq_sqrt (by linarith)
    set u := (q + 1) / (q - 1) with hu
    have hqm : 0 < q - 1 := by linarith
    have hupos : 0 < u := div_pos (by linarith) hqm
    have hσ : (u + u⁻¹) / 2 = (hi + lo) / (hi - lo) := by
      have hhl : 0 < hi - lo := by linarith
      rw [hu, inv_div]
      have hhi : hi = q ^ 2 * lo := by rw [hqq]; field_simp
      have h1 : q + 1 ≠ 0 := by linarith
      have h2 : q - 1 ≠ 0 := hqm.ne'
      have h3 : q ^ 2 * lo - lo ≠ 0 := by nlinarith
      rw [hhi, div_add_div _ _ h2 h1, div_div,
        div_eq_div_iff (mul_ne_zero (mul_ne_zero h2 h1) two_ne_zero) h3]
      ring
    set σ := (hi + lo) / (hi - lo)
    set Tσ := (Chebyshev.T ℝ (m : ℤ)).eval σ
    have hTσ : u ^ m / 2 ≤ Tσ := by
      have := chebyshev_T_ge hupos m
      rwa [hσ] at this
    have hTpos : 0 < Tσ := lt_of_lt_of_le (by positivity) hTσ
    refine ⟨C Tσ⁻¹ * (Chebyshev.T ℝ (m : ℤ)).comp (C σ - C (2 / (hi - lo)) * X), ?_, ?_, ?_⟩
    · simp [eval_comp, Tσ, inv_mul_cancel₀ hTpos.ne']
    · refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_comp_le.trans ?_
      rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
      have : (C σ - C (2 / (hi - lo)) * X).natDegree ≤ 1 := by
        refine (natDegree_sub_le _ _).trans ?_
        simp only [natDegree_C, zero_le, max_le_iff, true_and]
        exact (natDegree_C_mul_le _ _).trans natDegree_X_le
      calc m * (C σ - C (2 / (hi - lo)) * X).natDegree ≤ m * 1 := Nat.mul_le_mul_left _ this
        _ = m := mul_one m
    · intro x hx
      have hhl : 0 < hi - lo := by linarith
      have hℓ : |σ - 2 / (hi - lo) * x| ≤ 1 := by
        rw [abs_le]
        have e : σ - 2 / (hi - lo) * x = (hi + lo - 2 * x) / (hi - lo) := by
          simp only [σ]; field_simp
        rw [e, le_div_iff₀ hhl, div_le_iff₀ hhl]
        constructor <;> linarith [hx.1, hx.2]
      have hT := Chebyshev.abs_eval_T_real_le_one (m : ℤ) hℓ
      simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hTpos)]
      have hρ : (q - 1) / (q + 1) = u⁻¹ := by rw [hu, inv_div]
      rw [hρ, inv_pow]
      calc Tσ⁻¹ * |(Chebyshev.T ℝ (m : ℤ)).eval (σ - 2 / (hi - lo) * x)| ≤ Tσ⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hT (inv_pos.mpr hTpos).le
        _ = Tσ⁻¹ := mul_one _
        _ ≤ (u ^ m / 2)⁻¹ := inv_anti₀ (by positivity) hTσ
        _ = 2 * (u ^ m)⁻¹ := by rw [inv_div, div_eq_mul_inv]
  · -- `lo = hi`: the single point `lo` is killed by `1 − x/lo`
    subst heq
    rcases Nat.eq_zero_or_pos m with hm | hm
    · refine ⟨1, by simp, by simp, fun x _ => ?_⟩
      simp [hm]
    · refine ⟨1 - C lo⁻¹ * X, by simp, ?_, fun x hx => ?_⟩
      · refine (natDegree_sub_le _ _).trans ?_
        simp only [natDegree_one, zero_le, max_le_iff, true_and]
        exact ((natDegree_C_mul_le _ _).trans natDegree_X_le).trans hm
      · have hx' : x = lo := le_antisymm hx.2 hx.1
        subst hx'
        simp [inv_mul_cancel₀ hlo.ne', div_self hlo.ne', zero_pow hm.ne']
  · -- `hi < lo`: the interval is empty
    refine ⟨1, by simp, by simp, fun x hx => absurd (hx.1.trans hx.2) (not_le.mpr hgt)⟩

/-- **CG Chebyshev bound** (squared `A`-norm form): if the spectrum of `A ⪰ 0` lies in `[lo, hi]`
with `0 < lo`, the Galerkin (CG) iterate satisfies
`‖x_m − x*‖_A² ≤ (2((√κ−1)/(√κ+1))^m)² ‖x₀ − x*‖_A²`, `κ = hi / lo`. -/
@[powerlib_foundation] theorem cg_chebyshev {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosSemidef)
    {x₀ xm xs b : Fin k → ℝ} (hxs : A *ᵥ xs = b) {m : ℕ}
    (hxm : xm - x₀ ∈ krylov A (b - A *ᵥ x₀) m)
    (horth : ∀ s ∈ krylov A (b - A *ᵥ x₀) m, s ⬝ᵥ (b - A *ᵥ xm) = 0)
    {lo hi : ℝ} (hlo : 0 < lo) (hspec : ∀ i, hA.1.eigenvalues i ∈ Set.Icc lo hi) :
    anorm2 A (xm - xs) ≤
      (2 * ((√(hi / lo) - 1) / (√(hi / lo) + 1)) ^ m) ^ 2 * anorm2 A (x₀ - xs) := by
  obtain ⟨p, hp0, hpm, hp⟩ := exists_chebyshev_poly (hi := hi) hlo m
  exact cg_minmax hA hxs hxm horth p hp0 hpm fun i => hp _ (hspec i)

/-- **CG Chebyshev bound** `‖x_m − x*‖_A ≤ 2((√κ−1)/(√κ+1))^m ‖x₀ − x*‖_A`, `κ = hi / lo`, for a
spectrum in `[lo, hi]`, `0 < lo ≤ hi` (`‖u‖_A = √(uᵀAu)`). -/
@[powerlib_foundation] theorem cg_chebyshev_sqrt {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosSemidef) {x₀ xm xs b : Fin k → ℝ} (hxs : A *ᵥ xs = b) {m : ℕ}
    (hxm : xm - x₀ ∈ krylov A (b - A *ᵥ x₀) m)
    (horth : ∀ s ∈ krylov A (b - A *ᵥ x₀) m, s ⬝ᵥ (b - A *ᵥ xm) = 0)
    {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi) (hspec : ∀ i, hA.1.eigenvalues i ∈ Set.Icc lo hi) :
    √(anorm2 A (xm - xs)) ≤
      2 * ((√(hi / lo) - 1) / (√(hi / lo) + 1)) ^ m * √(anorm2 A (x₀ - xs)) := by
  have h := cg_chebyshev hA hxs hxm horth hlo hspec
  have hq : 1 ≤ √(hi / lo) := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt ((one_le_div hlo).mpr hlh)
  have hc : 0 ≤ 2 * ((√(hi / lo) - 1) / (√(hi / lo) + 1)) ^ m :=
    mul_nonneg zero_le_two (pow_nonneg (div_nonneg (by linarith) (by linarith)) m)
  calc √(anorm2 A (xm - xs))
      ≤ √((2 * ((√(hi / lo) - 1) / (√(hi / lo) + 1)) ^ m) ^ 2 * anorm2 A (x₀ - xs)) :=
        Real.sqrt_le_sqrt h
    _ = 2 * ((√(hi / lo) - 1) / (√(hi / lo) + 1)) ^ m * √(anorm2 A (x₀ - xs)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

/-- **CG Chebyshev bound with the spectral condition number** `κ = λ_max / λ_min` of a positive
definite `A` (`k > 0`): `‖x_m − x*‖_A ≤ 2((√κ−1)/(√κ+1))^m ‖x₀ − x*‖_A`. -/
@[powerlib_foundation] theorem cg_chebyshev_cond {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosDef)
    (hk : 0 < k) {x₀ xm xs b : Fin k → ℝ} (hxs : A *ᵥ xs = b) {m : ℕ}
    (hxm : xm - x₀ ∈ krylov A (b - A *ᵥ x₀) m)
    (horth : ∀ s ∈ krylov A (b - A *ᵥ x₀) m, s ⬝ᵥ (b - A *ᵥ xm) = 0) :
    √(anorm2 A (xm - xs)) ≤
      2 * ((√(Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ hA.1.eigenvalues /
          Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ hA.1.eigenvalues) - 1) /
        (√(Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ hA.1.eigenvalues /
          Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ hA.1.eigenvalues) + 1)) ^ m *
        √(anorm2 A (x₀ - xs)) := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' hne hA.1.eigenvalues
  have hlo : 0 < Finset.univ.inf' hne hA.1.eigenvalues := by
    rw [hi₀]; exact hA.eigenvalues_pos i₀
  have hlh : Finset.univ.inf' hne hA.1.eigenvalues ≤ Finset.univ.sup' hne hA.1.eigenvalues :=
    (Finset.inf'_le _ (Finset.mem_univ i₀)).trans (Finset.le_sup' _ (Finset.mem_univ i₀))
  exact cg_chebyshev_sqrt hA.posSemidef hxs hxm horth hlo hlh fun i =>
    ⟨Finset.inf'_le _ (Finset.mem_univ i), Finset.le_sup' _ (Finset.mem_univ i)⟩

end powerlib.LinearAlgebra
