import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # The Schur determinant identity and the Jacobian on a quasi-steady graph (foundation)

The determinant of a two-by-two block matrix whose off-diagonal block is cancelled by a solution
`H` of `A H + B = 0`, and its calculus reading: at a point of a quasi-steady graph (a surface on
which the fast rows of a field vanish identically) the Jacobian determinant of the field is the
determinant of its fast block times the Jacobian determinant of the reduced field (the slow rows
on the graph).

Scope.
* Pure linear algebra over a commutative ring (`det_fromBlocks_of_mul_add_eq_zero`) and
  differential calculus of an arbitrary field `f` on `EuclideanSpace ℝ ι` whose coordinates are
  split by an equivalence `ι ≃ F ⊕ S` into fast and slow ones (`det_eq_det_fast_mul_det_reduced`).
  No model: the converter instances only supply the obligations.
* Nothing is assumed about invertibility of the fast block: `H` (the derivative of the graph) is
  part of the data, so the identity holds also when the fast block is singular.

Source: Schur determinant identity, R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed.,
§0.8.5; its use for singularly perturbed (fast–slow) systems, P. Kokotović, H. K. Khalil and
J. O'Reilly, *Singular Perturbation Methods in Control*, §2.1 (the reduced Jacobian
`A₂₂ − A₂₁ A₁₁⁻¹ A₁₂`); GFM counterpart study, full-order model note (t5, "reduced Jacobian = Schur
complement; det J = det J_ff · det J_red").

Results.
* `det_fromBlocks_of_mul_add_eq_zero`: `A H + B = 0` ⇒
  `det [[A, B], [C, D]] = det A · det (C H + D)` (with `H = −A⁻¹ B` this is the Schur identity
  `det A · det (D − C A⁻¹ B)`).
* `det_eq_det_fast_mul_det_reduced`: let `Φ` be a differentiable graph over the slow coordinates
  (`Φ s` has slow part `s`) on which the fast rows of `f` vanish; at `Φ s₀`, if `J` is the
  Jacobian of `f`, `A` its fast–fast partial derivatives and `R` the Jacobian of the reduced field
  `s ↦ (slow rows of f)(Φ s)`, then `det J = det A · det R`.
-/

noncomputable section
namespace powerlib.LinearAlgebra
open Matrix

/-- The Schur determinant identity: if `H` solves `A H + B = 0`, the block matrix
`[[A, B], [C, D]]` has determinant `det A · det (C H + D)` (right multiplication by the unipotent
`[[1, H], [0, 1]]` makes it block lower triangular). -/
@[tmio T, powerlib_foundation] theorem det_fromBlocks_of_mul_add_eq_zero {m n R : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R) (D : Matrix n n R)
    (H : Matrix m n R) (hH : A * H + B = 0) :
    (fromBlocks A B C D).det = A.det * (C * H + D).det := by
  have h : fromBlocks A B C D * fromBlocks 1 H 0 1 = fromBlocks A 0 C (C * H + D) := by
    simp [fromBlocks_multiply, hH]
  have h1 : (fromBlocks (1 : Matrix m m R) H 0 1).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  calc (fromBlocks A B C D).det = (fromBlocks A B C D * fromBlocks 1 H 0 1).det := by
        rw [det_mul, h1, mul_one]
    _ = A.det * (C * H + D).det := by rw [h, det_fromBlocks_zero₁₂]

section Graph

variable {ι F S : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype S]
  [DecidableEq S]

omit [DecidableEq ι] in
/-- The derivative of a coordinate of a curve in `EuclideanSpace ℝ ι`. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_coord {c : ℝ → EuclideanSpace ℝ ι}
    {v : EuclideanSpace ℝ ι} (hc : HasDerivAt c v 0) (i : ι) :
    HasDerivAt (fun t => c t i) (v i) 0 :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt 0 hc

/-- The derivative of `f` along a curve through the point, read through its Jacobian matrix. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_comp_coord
    {f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {J : Matrix ι ι ℝ} {x : EuclideanSpace ℝ ι}
    (hJ : HasFDerivAt f (Matrix.toEuclideanCLM (𝕜 := ℝ) J) x) {c : ℝ → EuclideanSpace ℝ ι}
    {v : EuclideanSpace ℝ ι} (hc : HasDerivAt c v 0) (hc0 : c 0 = x) (i : ι) :
    HasDerivAt (fun t => f (c t) i) (∑ j, J i j * v j) 0 := by
  have h := hasDerivAt_coord (HasFDerivAt.comp_hasDerivAt_of_eq 0 hJ hc hc0.symm) i
  simpa [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct] using h

/-- The line `t ↦ s₀ + t eₖ` through `s₀` in the direction of a basis vector. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_line {E : Type*} [Fintype E]
    [DecidableEq E] (s₀ : EuclideanSpace ℝ E) (k : E) :
    HasDerivAt (fun t : ℝ => s₀ + t • EuclideanSpace.single k 1) (EuclideanSpace.single k 1) 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single k (1 : ℝ))).const_add s₀

/-- The Jacobian determinant on a quasi-steady graph. The coordinates of `ι` are split into fast
(`F`) and slow (`S`) ones by `e`; `Φ s` is a point with slow part `s` on which the fast rows of `f`
vanish. At `Φ s₀`, with `J` the Jacobian of `f`, `A` the fast–fast partial derivatives of the fast
rows and `R` the Jacobian of the reduced field `s ↦ (slow rows of f)(Φ s)`,
`det J = det A · det R`: the reduced Jacobian is the Schur complement of the fast block. -/
@[tmio T, powerlib_foundation] theorem det_eq_det_fast_mul_det_reduced (e : ι ≃ F ⊕ S)
    {f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {Φ : EuclideanSpace ℝ S → EuclideanSpace ℝ ι}
    {s₀ : EuclideanSpace ℝ S} {J : Matrix ι ι ℝ} {A : Matrix F F ℝ} {R : Matrix S S ℝ}
    (hJ : HasFDerivAt f (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (Φ s₀))
    (hΦ : DifferentiableAt ℝ Φ s₀) (hslow : ∀ s k, Φ s (e.symm (.inr k)) = s k)
    (hfast : ∀ s i, f (Φ s) (e.symm (.inl i)) = 0)
    (hA : ∀ i j, HasDerivAt
      (fun t : ℝ => f (Φ s₀ + t • EuclideanSpace.single (e.symm (.inl j)) 1) (e.symm (.inl i)))
      (A i j) 0)
    (hR : HasFDerivAt (fun s => (WithLp.toLp 2 fun k => f (Φ s) (e.symm (.inr k)) :
      EuclideanSpace ℝ S)) (Matrix.toEuclideanCLM (𝕜 := ℝ) R) s₀) :
    J.det = A.det * R.det := by
  -- the derivative of the graph in the slow direction `k`
  set w : S → EuclideanSpace ℝ ι := fun k => fderiv ℝ Φ s₀ (EuclideanSpace.single k 1) with hw
  have hc : ∀ k, HasDerivAt (fun t : ℝ => Φ (s₀ + t • EuclideanSpace.single k 1)) (w k) 0 :=
    fun k => hΦ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line s₀ k) (by simp)
  have hc0 : ∀ k, (fun t : ℝ => Φ (s₀ + t • EuclideanSpace.single k 1)) 0 = Φ s₀ := by simp
  -- its slow coordinates are those of `eₖ`
  have hws : ∀ k l, w k (e.symm (.inr l)) = if l = k then 1 else 0 := by
    intro k l
    have h1 := hasDerivAt_coord (hc k) (e.symm (.inr l))
    simp only [hslow] at h1
    have h2 := hasDerivAt_coord (hasDerivAt_line s₀ k) l
    rw [h1.unique h2]
    simp [PiLp.single_apply]
  -- the block form of the Jacobian
  set Jb := J.reindex e e with hJb
  have hJbe : ∀ a b, Jb a b = J (e.symm a) (e.symm b) := fun a b => rfl
  set H : Matrix F S ℝ := fun j k => w k (e.symm (.inl j)) with hH
  have hsum : ∀ a k, ∑ b, J (e.symm a) b * w k b =
      ∑ j, Jb a (.inl j) * H j k + Jb a (.inr k) := by
    intro a k
    rw [← e.symm.sum_comp, Fintype.sum_sum_type]
    congr 1
    simp only [hJbe, hws, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  -- fast rows: `A H + B = 0`
  have hAb : ∀ i j, Jb (.inl i) (.inl j) = A i j := by
    intro i j
    have h1 := hasDerivAt_comp_coord hJ (hasDerivAt_line (Φ s₀) (e.symm (.inl j))) (by simp)
      (e.symm (.inl i))
    rw [(hA i j).unique h1]
    simp [hJbe, PiLp.single_apply]
  have hfastRow : ∀ i k, ∑ j, Jb (.inl i) (.inl j) * H j k + Jb (.inl i) (.inr k) = 0 := by
    intro i k
    have h1 := hasDerivAt_comp_coord hJ (hc k) (hc0 k) (e.symm (.inl i))
    have h0 : HasDerivAt (fun t : ℝ => f (Φ (s₀ + t • EuclideanSpace.single k 1))
        (e.symm (.inl i))) 0 0 := by
      simp only [hfast]
      exact hasDerivAt_const _ _
    rw [← hsum, h1.unique h0]
  -- slow rows: `C H + D = R`
  have hslowRow : ∀ l k, ∑ j, Jb (.inr l) (.inl j) * H j k + Jb (.inr l) (.inr k) = R l k := by
    intro l k
    have h1 := hasDerivAt_comp_coord hJ (hc k) (hc0 k) (e.symm (.inr l))
    have h2 := hasDerivAt_coord (hR.comp_hasDerivAt_of_eq 0 (hasDerivAt_line s₀ k) (by simp)) l
    rw [← hsum, h1.unique h2]
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, PiLp.single_apply]
  have hblock : Jb = fromBlocks A (Jb.toBlocks₁₂) (Jb.toBlocks₂₁) (Jb.toBlocks₂₂) := by
    rw [← fromBlocks_toBlocks Jb]
    congr 1
    ext i j
    exact hAb i j
  have hAH : A * H + Jb.toBlocks₁₂ = 0 := by
    ext i k
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply]
    simpa only [hAb, toBlocks₁₂, of_apply] using hfastRow i k
  have hCH : Jb.toBlocks₂₁ * H + Jb.toBlocks₂₂ = R := by
    ext l k
    rw [Matrix.add_apply, Matrix.mul_apply]
    simpa only [toBlocks₂₁, toBlocks₂₂, of_apply] using hslowRow l k
  rw [← det_reindex_self e J, ← hJb, hblock, det_fromBlocks_of_mul_add_eq_zero _ _ _ _ H hAH, hCH]

end Graph

end powerlib.LinearAlgebra
