import theorem.SingularPerturbation.Linear
import theorem.LinearAlgebra.SchurDeterminant
import theorem.Dynamics.Locality

/-! # Singular perturbation on a quasi-steady graph: Jacobian blocks, stability, instability

A field whose fast rows vanish on an explicit graph over the slow coordinates has a Jacobian whose
Schur complement is the Jacobian of the reduced field. Hence: a Hurwitz fast block and a Hurwitz
reduced Jacobian give local exponential stability of the field with its fast rows accelerated by
`1/ε`, for every small `ε > 0`; the determinant sign gives instability; and the characteristic
determinant at a positive real frequency decides a positive real eigenvalue.

Scope.
* Generic statements about an arbitrary field `f` on `EuclideanSpace ℝ ι` (on `Dynamics.State N`
  for the semantic conclusions) whose coordinates are split by an equivalence `e : ι ≃ F ⊕ S`
  into fast (`F`) and slow (`S`) ones, and a graph `Φ` over the slow coordinates on which the fast
  rows of `f` vanish identically (the data of `LinearAlgebra.det_eq_det_fast_mul_det_reduced`).
  The field is `C¹` on an open neighbourhood `U` of the point only (local versions).
* `splitScaledField e ε f` is the `ε`-system `ε ż = f_fast`, `ẋ = f_slow` written as one field:
  the fast rows are multiplied by `ε⁻¹`, the slow rows are unchanged (the field
  `SingularPerturbation.scaledField` of `theorem/SingularPerturbation/Nonlinear.lean` for an
  arbitrary coordinate order). Equilibrium-level (local) statements; no claim here about the
  basin or finite-horizon approximation (a basin uniform in `ε` with an explicit `ε*` is
  `theorem/SingularPerturbation/UniformBasin.lean`).

Source: Kokotović–Khalil–O'Reilly, *Singular Perturbation Methods in Control* (1986), Ch. 2
(two-time-scale stability with Hurwitz boundary-layer and reduced matrices) and §2.1 (the reduced
Jacobian is the Schur complement `A₀ = A₁₁ − A₁₂ A₂₂⁻¹ A₂₁`); Horn–Johnson, *Matrix Analysis*,
§0.8.5 (Schur complement); work-sync theory/T-singular-perturbation.md §1.3–§1.4,
theory/T-tikhonov.md §1.2; GFM counterpart study, full-order model note (t5: "reduced Jacobian
= Schur complement") and equilibria note (t6 §c: "δs stability does NOT carry over").

Results.
* The Jacobian on a quasi-steady graph in block form, `[[A, B], [C, D]]` with `A H + B = 0`,
  `C H + D = R` and `R = D − C A⁻¹ B` (`LinearAlgebra.exists_blocks_of_graph`,
  `LinearAlgebra.reducedJacobian_eq_schur` of `theorem/LinearAlgebra/SchurDeterminant.lean`), is
  the input of the laws below; `isUnit_det_of_spectrallyStable`: a spectrally stable matrix on any
  finite index is invertible.
* `locallyExponentiallyStable_of_lt_graphEpsStar`: with positive definite Lyapunov matrices
  `P₀ R + Rᵀ P₀ = −1` of the reduced Jacobian and `P₂ A + Aᵀ P₂ = −1` of the fast block, the
  field with its fast rows multiplied by `ε⁻¹` is locally exponentially stable at the point for
  every `ε ∈ (0, graphEpsStar e J P₀ P₂)`, an explicit bound computed from the blocks of the
  Jacobian `J` (Kokotović's composite Lyapunov bound `LinearSP.isHurwitz_of_lt_epsStar` and the
  local indirect method `Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local`);
  `graphEpsStar_pos`. Its matrix core, on any finite index:
  `spectrallyStable_splitScale_mul_of_lt_graphEpsStar` (a matrix whose blocks admit `H` with
  `A H + B = 0`, `C H + D = R` is spectrally stable with its fast rows times `ε⁻¹` for every
  `ε ∈ (0, graphEpsStar …)`) and `exists_epsStar_spectrallyStable_splitScale_mul`.
  `graphEpsStar_eq_of_blocks`: the bound in the original index types,
  `1/(2c + 1)`, `c = S (2S + 1)/2 + |P₂ H C|₁`, `S = |P₀ C|₁ + |P₂ H R|₁` (`absSum_reindex`,
  `absSum_neg`). `exists_posDef_lyapunov_of_spectrallyStable`: such `P` exist for spectrally
  stable matrices on any finite index, and `posDef_of_lyapunov_of_spectrallyStable`: every
  solution of `P A + Aᵀ P = −1` is then positive definite (uniqueness); hence
  `exists_epsStar_locallyExponentiallyStable_of_graph`: if the fast block and the reduced
  Jacobian are spectrally stable, there is `ε* > 0` with the same conclusion.
* `unstable_of_det_fast_mul_det_reduced`: `(−1)^N det A · det R < 0` gives instability (a
  positive real eigenvalue, `Criteria.exists_pos_real_eigenvalue_of_det`), for a field `C¹` near
  the point only.
* `exists_real_eigenvalue_ge_of_det_sub_nonpos`: a real matrix with `det (r • 1 − A) ≤ 0` at
  some real `r` has a real eigenvalue `μ ≥ r` (the characteristic polynomial is monic);
  `unstable_of_det_sub_nonpos`: the semantic corollary for a `C¹` field. Unlike the determinant
  sign, this frequency test detects the instabilities of odd-dimensional fields whose fast block
  and reduced Jacobian are both stable.
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Matrix

/-! ## Spectral stability on an arbitrary finite index -/

section Index

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- A spectrally stable matrix on any finite index is invertible. -/
@[tmio T, powerlib_foundation] theorem isUnit_det_of_spectrallyStable {A : Matrix F F ℝ}
    (hA : Linear.SpectrallyStable A) : IsUnit A.det := by
  set e := Fintype.equivFin F
  have h := Criteria.isUnit_det_of_isHurwitz
    ((Linear.spectrallyStable_iff_isHurwitz _).mp ((Linear.spectrallyStable_reindex e A).mpr hA))
  rwa [Matrix.det_reindex_self] at h

end Index

/-! ## Two-time-scale stability on a quasi-steady graph -/

section Scaled

variable {ι F S : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype S]
  [DecidableEq S]

/-- `diag(ε⁻¹ on the fast coordinates, 1 on the slow ones)` for the split `e`. -/
def splitScale (e : ι ≃ F ⊕ S) (ε : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i => Sum.elim (fun _ => ε⁻¹) (fun _ => 1) (e i)

/-- The `ε`-system of a split field: the fast rows multiplied by `ε⁻¹` (`ε ż = f_fast`), the
slow rows unchanged (`ẋ = f_slow`). -/
def splitScaledField (e : ι ≃ F ⊕ S) (ε : ℝ) (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (splitScale e ε) (f x)

omit [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem splitScaledField_fast (e : ι ≃ F ⊕ S) (ε : ℝ)
    (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) (i : F) :
    splitScaledField e ε f x (e.symm (.inl i)) = ε⁻¹ * f x (e.symm (.inl i)) := by
  simp [splitScaledField, splitScale, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]

omit [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem splitScaledField_slow (e : ι ≃ F ⊕ S) (ε : ℝ)
    (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι) (k : S) :
    splitScaledField e ε f x (e.symm (.inr k)) = f x (e.symm (.inr k)) := by
  simp [splitScaledField, splitScale, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]

/-- The blocks of a split matrix as a linear singularly perturbed system (slow first). -/
def splitSP (e : ι ≃ F ⊕ S) (J : Matrix ι ι ℝ) :
    LinearSP (Fintype.card S) (Fintype.card F) :=
  ⟨((J.reindex e e).toBlocks₂₂).reindex (Fintype.equivFin S) (Fintype.equivFin S),
    ((J.reindex e e).toBlocks₂₁).reindex (Fintype.equivFin S) (Fintype.equivFin F),
    ((J.reindex e e).toBlocks₁₂).reindex (Fintype.equivFin F) (Fintype.equivFin S),
    ((J.reindex e e).toBlocks₁₁).reindex (Fintype.equivFin F) (Fintype.equivFin F)⟩

/-- The relabelling of the coordinates that puts the slow ones first. -/
def splitOrder (e : ι ≃ F ⊕ S) : ι ≃ Fin (Fintype.card S) ⊕ Fin (Fintype.card F) :=
  e.trans ((Equiv.sumComm F S).trans
    (Equiv.sumCongr (Fintype.equivFin S) (Fintype.equivFin F)))

omit [DecidableEq F] [DecidableEq S] in
/-- The scaled Jacobian, relabelled slow first, is the block matrix of `splitSP`. -/
@[tmio T, powerlib_foundation] theorem reindex_splitScale_mul (e : ι ≃ F ⊕ S) (J : Matrix ι ι ℝ)
    (ε : ℝ) : (splitScale e ε * J).reindex (splitOrder e) (splitOrder e) =
      (splitSP e J).blockMatrix ε := by
  ext (a | a) (b | b) <;>
    simp [splitOrder, splitSP, splitScale, LinearSP.blockMatrix, Matrix.diagonal_mul,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

omit [Fintype ι] [DecidableEq ι] [DecidableEq S] in
/-- The reduced matrix of `splitSP` is the relabelled Schur complement. -/
@[tmio T, powerlib_foundation] theorem reducedMatrix_splitSP (e : ι ≃ F ⊕ S) (J : Matrix ι ι ℝ) :
    (splitSP e J).reducedMatrix = ((J.reindex e e).toBlocks₂₂ - (J.reindex e e).toBlocks₂₁ *
      ((J.reindex e e).toBlocks₁₁)⁻¹ * (J.reindex e e).toBlocks₁₂).reindex
        (Fintype.equivFin S) (Fintype.equivFin S) := by
  simp only [LinearSP.reducedMatrix, splitSP, Matrix.reindex_apply, Matrix.inv_submatrix_equiv,
    Matrix.submatrix_mul_equiv]
  rfl

/-- **The explicit `ε*` of a split Jacobian.** Kokotović's bound `ε* = 1/(2c + 1)`
(`LinearSP.epsStar`) for the blocks of `J` split by `e` (`splitSP`, slow coordinates first), with
a Lyapunov matrix `P₀` of the reduced (slow) block and `P₂` of the fast block, both on their own
index types (relabelled by `Fintype.equivFin`). Written out: `c = S (2S + 1)/2 + |P₂ L B'|₁`,
`S = |P₀ B'|₁ + |P₂ L R|₁`, where `B'` is the slow-from-fast block of `J`, `L = A⁻¹ C'` the
quasi-steady gain (`A` the fast block, `C'` the fast-from-slow block), `R` the reduced matrix and
`|N|₁ = Σᵢⱼ |Nᵢⱼ|`. -/
def graphEpsStar (e : ι ≃ F ⊕ S) (J : Matrix ι ι ℝ) (P0 : Matrix S S ℝ) (P2 : Matrix F F ℝ) : ℝ :=
  (splitSP e J).epsStar (P0.reindex (Fintype.equivFin S) (Fintype.equivFin S))
    (P2.reindex (Fintype.equivFin F) (Fintype.equivFin F))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem graphEpsStar_pos (e : ι ≃ F ⊕ S) (J : Matrix ι ι ℝ)
    (P0 : Matrix S S ℝ) (P2 : Matrix F F ℝ) : 0 < graphEpsStar e J P0 P2 := by
  set sp := splitSP e J
  set P0' := P0.reindex (Fintype.equivFin S) (Fintype.equivFin S)
  set P2' := P2.reindex (Fintype.equivFin F) (Fintype.equivFin F)
  have hc : 0 ≤ sp.couplingConst P0' P2' := by
    simp only [LinearSP.couplingConst]
    have := absSum_nonneg (P0' * sp.A12)
    have := absSum_nonneg (P2' * sp.gain * sp.reducedMatrix)
    have := absSum_nonneg (P2' * sp.gain * sp.A12)
    positivity
  simp only [graphEpsStar, LinearSP.epsStar]
  positivity

omit [Fintype ι] [DecidableEq ι] in
/-- A Lyapunov equation `P M + Mᵀ P = −1` survives a relabelling of the index. -/
@[tmio T, powerlib_foundation] private theorem lyapunov_reindex {k k' : Type*} [Fintype k]
    [DecidableEq k] [Fintype k'] [DecidableEq k'] (σ : k ≃ k') {P M : Matrix k k ℝ}
    (h : P * M + Mᵀ * P = -1) :
    P.reindex σ σ * M.reindex σ σ + (M.reindex σ σ)ᵀ * P.reindex σ σ = -1 := by
  have h' := congrArg (fun X : Matrix k k ℝ => X.reindex σ σ) h
  ext i j
  have hij := congrFun (congrFun h' i) j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.neg_apply,
    Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq] at hij ⊢
  rw [← hij, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← σ.symm.sum_comp, ← σ.symm.sum_comp]
  simp [Matrix.transpose_apply]

omit [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S] in
/-- A spectrally stable matrix on any finite index has a positive definite Lyapunov matrix,
`P A + Aᵀ P = −1` (LeanForControl's continuous Lyapunov theorem, after relabelling). -/
@[tmio T, powerlib_foundation] theorem exists_posDef_lyapunov_of_spectrallyStable
    {A : Matrix F F ℝ} (hA : Linear.SpectrallyStable A) :
    ∃ P : Matrix F F ℝ, P.PosDef ∧ P * A + Aᵀ * P = -1 := by
  set σ := Fintype.equivFin F
  have hH : LinearSystems.IsHurwitz (A.reindex σ σ) :=
    (Linear.spectrallyStable_iff_isHurwitz _).mp ((Linear.spectrallyStable_reindex σ A).mpr hA)
  obtain ⟨P, hP, hL, -⟩ :=
    hH.exists_posDef_unique_solution_continuous_lyapunov 1 Matrix.PosDef.one
  refine ⟨P.reindex σ.symm σ.symm, hP.submatrix σ.injective, ?_⟩
  have h := lyapunov_reindex σ.symm hL
  simpa using h

omit [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S] in
/-- For a spectrally stable matrix, every solution of `P A + Aᵀ P = −1` is positive definite (it
is the unique solution of LeanForControl's continuous Lyapunov theorem). -/
@[tmio T, powerlib_foundation] theorem posDef_of_lyapunov_of_spectrallyStable
    {A P : Matrix F F ℝ} (hA : Linear.SpectrallyStable A) (hL : P * A + Aᵀ * P = -1) :
    P.PosDef := by
  set σ := Fintype.equivFin F
  have hH : LinearSystems.IsHurwitz (A.reindex σ σ) :=
    (Linear.spectrallyStable_iff_isHurwitz _).mp ((Linear.spectrallyStable_reindex σ A).mpr hA)
  obtain ⟨P', hP', -, huniq⟩ :=
    hH.exists_posDef_unique_solution_continuous_lyapunov 1 Matrix.PosDef.one
  have hPe : P.reindex σ σ = P' := huniq _ (lyapunov_reindex σ hL)
  have := hP'.submatrix σ.injective
  rw [← hPe] at this
  simpa using this

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] [DecidableEq S] in
/-- `Σᵢⱼ |Nᵢⱼ|` does not depend on the labelling. -/
@[tmio T, powerlib_foundation] theorem absSum_reindex {k l k' l' : Type*} [Fintype k] [Fintype l]
    [Fintype k'] [Fintype l'] (e₁ : k ≃ k') (e₂ : l ≃ l') (N : Matrix k l ℝ) :
    absSum (N.reindex e₁ e₂) = absSum N := by
  simp only [absSum, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [← e₁.symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e₂.symm.sum_comp]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem absSum_neg {k l : Type*} [Fintype k] [Fintype l]
    (N : Matrix k l ℝ) : absSum (-N) = absSum N := by
  simp [absSum]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] [DecidableEq S] in
@[tmio T, powerlib_foundation] private theorem reindex_mul_reindex {k l m k' l' m' : Type*}
    [Fintype l] [Fintype l'] (e₁ : k ≃ k') (e₂ : l ≃ l') (e₃ : m ≃ m') (X : Matrix k l ℝ)
    (Y : Matrix l m ℝ) : X.reindex e₁ e₂ * Y.reindex e₂ e₃ = (X * Y).reindex e₁ e₃ := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

omit [Fintype ι] [DecidableEq ι] [DecidableEq S] in
/-- **The explicit `ε*` from the blocks.** For `J` split by `e` with blocks `[[A, B], [C, D]]`
(fast first), invertible `A`, `A H + B = 0` and `C H + D = R`:
`graphEpsStar e J P₀ P₂ = 1/(2c + 1)` with `c = S (2S + 1)/2 + |P₂ H C|₁` and
`S = |P₀ C|₁ + |P₂ H R|₁` (`|N|₁ = Σᵢⱼ |Nᵢⱼ|`), all in the original index types. -/
@[tmio T, powerlib_foundation] theorem graphEpsStar_eq_of_blocks (e : ι ≃ F ⊕ S)
    {J : Matrix ι ι ℝ} {A : Matrix F F ℝ} {R : Matrix S S ℝ} {H : Matrix F S ℝ}
    (hA11 : (J.reindex e e).toBlocks₁₁ = A) (hAu : IsUnit A.det)
    (hH : A * H + (J.reindex e e).toBlocks₁₂ = 0)
    (hHR : (J.reindex e e).toBlocks₂₁ * H + (J.reindex e e).toBlocks₂₂ = R)
    (P0 : Matrix S S ℝ) (P2 : Matrix F F ℝ) :
    graphEpsStar e J P0 P2 =
      1 / (2 * ((absSum (P0 * (J.reindex e e).toBlocks₂₁) + absSum (P2 * H * R)) *
        (2 * (absSum (P0 * (J.reindex e e).toBlocks₂₁) + absSum (P2 * H * R)) + 1) / 2 +
          absSum (P2 * H * (J.reindex e e).toBlocks₂₁)) + 1) := by
  set σF := Fintype.equivFin F with hσF
  set σS := Fintype.equivFin S with hσS
  set sp := splitSP e J
  have hRS := LinearAlgebra.reducedJacobian_eq_schur hAu hH hHR
  have h0 : sp.reducedMatrix = R.reindex σS σS := by
    rw [reducedMatrix_splitSP, hA11, ← hRS]
  have hAinvB : A⁻¹ * (J.reindex e e).toBlocks₁₂ = -H := by
    have : (J.reindex e e).toBlocks₁₂ = -(A * H) := eq_neg_of_add_eq_zero_right hH
    rw [this, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mul]
  have hgain : sp.gain = (-H).reindex σF σS := by
    show (((J.reindex e e).toBlocks₁₁).reindex σF σF)⁻¹ *
      ((J.reindex e e).toBlocks₁₂).reindex σF σS = _
    rw [hA11, Matrix.inv_reindex, ← hAinvB, reindex_mul_reindex]
  have hA12 : sp.A12 = ((J.reindex e e).toBlocks₂₁).reindex σS σF := rfl
  simp only [graphEpsStar, LinearSP.epsStar, LinearSP.couplingConst]
  rw [hgain, h0, hA12, ← hσF, ← hσS]
  simp only [reindex_mul_reindex, absSum_reindex, Matrix.neg_mul, Matrix.mul_neg, absSum_neg]

/-- **Matrix form, explicit `ε*`.** A real matrix `J` on any finite index, split by `e`, whose
blocks `[[A, B], [C, D]]` (fast first) admit `H` with `A H + B = 0` and `C H + D = R` (the
quasi-steady gain and the reduced matrix `R = D − C A⁻¹ B`): with positive definite Lyapunov
matrices `P₀ R + Rᵀ P₀ = −1`, `P₂ A + Aᵀ P₂ = −1`, the matrix with its fast rows multiplied by
`ε⁻¹` is spectrally stable for every `ε ∈ (0, graphEpsStar e J P₀ P₂)`
(`LinearSP.isHurwitz_of_lt_epsStar`). -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_splitScale_mul_of_lt_graphEpsStar
    (e : ι ≃ F ⊕ S) {J : Matrix ι ι ℝ} {A : Matrix F F ℝ} {R : Matrix S S ℝ} {H : Matrix F S ℝ}
    (hA11 : (J.reindex e e).toBlocks₁₁ = A) (hH : A * H + (J.reindex e e).toBlocks₁₂ = 0)
    (hHR : (J.reindex e e).toBlocks₂₁ * H + (J.reindex e e).toBlocks₂₂ = R)
    {P0 : Matrix S S ℝ} {P2 : Matrix F F ℝ} (hP0 : P0.PosDef) (hP2 : P2.PosDef)
    (hL0 : P0 * R + Rᵀ * P0 = -1) (hL2 : P2 * A + Aᵀ * P2 = -1) {ε : ℝ} (hε : 0 < ε)
    (hεs : ε < graphEpsStar e J P0 P2) :
    Linear.SpectrallyStable (splitScale e ε * J) := by
  set σF := Fintype.equivFin F
  set σS := Fintype.equivFin S
  set sp := splitSP e J
  have h22 : sp.A22 = A.reindex σF σF := by
    show ((J.reindex e e).toBlocks₁₁).reindex σF σF = _
    rw [hA11]
  have hP2' : (P2.reindex σF σF).PosDef := hP2.submatrix σF.symm.injective
  have hP0' : (P0.reindex σS σS).PosDef := hP0.submatrix σS.symm.injective
  have hcert : Linear.Certificate (A.reindex σF σF) :=
    ⟨P2.reindex σF σF, hP2'.isHermitian.isSymm, fun x hx => by
      simpa using hP2'.dotProduct_mulVec_pos hx, by
      rw [add_comm]; exact lyapunov_reindex σF hL2⟩
  have hAu' : IsUnit (A.reindex σF σF).det := Criteria.isUnit_det_of_isHurwitz hcert.isHurwitz
  have hAu : IsUnit A.det := by rwa [Matrix.det_reindex_self] at hAu'
  have hRS := LinearAlgebra.reducedJacobian_eq_schur hAu hH hHR
  have h0 : sp.reducedMatrix = R.reindex σS σS := by
    rw [reducedMatrix_splitSP, hA11, ← hRS]
  have h := sp.isHurwitz_of_lt_epsStar (by rw [h22]; exact hAu') hP0' hP2'
    (by rw [h0]; exact lyapunov_reindex σS hL0) (by rw [h22]; exact lyapunov_reindex σF hL2)
    hε hεs
  rw [← Linear.spectrallyStable_iff_isHurwitz, LinearSP.stateMatrix,
    Linear.spectrallyStable_reindex, ← reindex_splitScale_mul,
    Linear.spectrallyStable_reindex] at h
  exact h

/-- **Matrix form.** With the block data of `spectrallyStable_splitScale_mul_of_lt_graphEpsStar`
and spectrally stable `A` and `R`, there is `ε* > 0` such that the matrix with its fast rows
multiplied by `ε⁻¹` is spectrally stable for every `ε ∈ (0, ε*)`. -/
@[tmio T, powerlib_foundation] theorem exists_epsStar_spectrallyStable_splitScale_mul
    (e : ι ≃ F ⊕ S) {J : Matrix ι ι ℝ} {A : Matrix F F ℝ} {R : Matrix S S ℝ} {H : Matrix F S ℝ}
    (hA11 : (J.reindex e e).toBlocks₁₁ = A) (hH : A * H + (J.reindex e e).toBlocks₁₂ = 0)
    (hHR : (J.reindex e e).toBlocks₂₁ * H + (J.reindex e e).toBlocks₂₂ = R)
    (hAs : Linear.SpectrallyStable A) (hRs : Linear.SpectrallyStable R) :
    ∃ εs > 0, ∀ ε, 0 < ε → ε < εs → Linear.SpectrallyStable (splitScale e ε * J) := by
  obtain ⟨P0, hP0, hL0⟩ := exists_posDef_lyapunov_of_spectrallyStable hRs
  obtain ⟨P2, hP2, hL2⟩ := exists_posDef_lyapunov_of_spectrallyStable hAs
  exact ⟨graphEpsStar e J P0 P2, graphEpsStar_pos e J P0 P2, fun ε hε hεs =>
    spectrallyStable_splitScale_mul_of_lt_graphEpsStar e hA11 hH hHR hP0 hP2 hL0 hL2 hε hεs⟩

/-- **Two-time-scale stability on a quasi-steady graph with an explicit `ε*`.** With the data of
`exists_epsStar_locallyExponentiallyStable_of_graph` (a field `C¹` near the point whose fast rows
vanish on the graph `Φ`, fast block `A`, reduced Jacobian `R`), the Jacobian `J` of the field at
`Φ s₀`, and positive definite Lyapunov matrices `P₀ R + Rᵀ P₀ = −1`, `P₂ A + Aᵀ P₂ = −1`: for every
`ε ∈ (0, graphEpsStar e J P₀ P₂)` the `ε`-system is locally exponentially stable at `Φ s₀`
(Kokotović's composite Lyapunov bound `LinearSP.isHurwitz_of_lt_epsStar`). -/
@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_of_lt_graphEpsStar {N : ℕ}
    (e : Fin N ≃ F ⊕ S) {f : Dynamics.State N → Dynamics.State N} {U : Set (Dynamics.State N)}
    (hU : IsOpen U) {Φ : EuclideanSpace ℝ S → Dynamics.State N} {s₀ : EuclideanSpace ℝ S}
    (hx : Φ s₀ ∈ U) (hf : ContDiffOn ℝ 1 f U) (heq : f (Φ s₀) = 0) {J : Matrix (Fin N) (Fin N) ℝ}
    (hJ : HasFDerivAt f (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (Φ s₀)) {A : Matrix F F ℝ}
    {R : Matrix S S ℝ} (hΦ : DifferentiableAt ℝ Φ s₀)
    (hslow : ∀ s k, Φ s (e.symm (.inr k)) = s k) (hfast : ∀ s i, f (Φ s) (e.symm (.inl i)) = 0)
    (hA : ∀ i j, HasDerivAt
      (fun t : ℝ => f (Φ s₀ + t • EuclideanSpace.single (e.symm (.inl j)) 1) (e.symm (.inl i)))
      (A i j) 0)
    (hR : HasFDerivAt (fun s => (WithLp.toLp 2 fun k => f (Φ s) (e.symm (.inr k)) :
      EuclideanSpace ℝ S)) (Matrix.toEuclideanCLM (𝕜 := ℝ) R) s₀)
    {P0 : Matrix S S ℝ} {P2 : Matrix F F ℝ} (hP0 : P0.PosDef) (hP2 : P2.PosDef)
    (hL0 : P0 * R + Rᵀ * P0 = -1) (hL2 : P2 * A + Aᵀ * P2 = -1) {ε : ℝ} (hε : 0 < ε)
    (hεs : ε < graphEpsStar e J P0 P2) :
    LocallyExponentiallyStable (splitScaledField e ε f) (Φ s₀) := by
  obtain ⟨hA11, H, hH, hHR⟩ := LinearAlgebra.exists_blocks_of_graph e hJ hΦ hslow hfast hA hR
  have hHur : LinearSystems.IsHurwitz (splitScale e ε * J) :=
    (Linear.spectrallyStable_iff_isHurwitz _).mp
      (spectrallyStable_splitScale_mul_of_lt_graphEpsStar e hA11 hH hHR hP0 hP2 hL0 hL2 hε hεs)
  set L := Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (splitScale e ε)
  have hderiv : fderiv ℝ (splitScaledField e ε f) (Φ s₀) =
      Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (splitScale e ε * J) := by
    have h := (L.hasFDerivAt.comp (Φ s₀) hJ).fderiv
    rw [← ContinuousLinearMap.mul_def, ← map_mul] at h
    exact h
  refine Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local hU hx _
    (L.contDiff.comp_contDiffOn hf) ?_ hderiv hHur
  simp [splitScaledField, heq]

/-- **Two-time-scale stability on a quasi-steady graph.** Let the fast rows of `f` (`C¹` on an
open neighbourhood `U` of the point) vanish on a graph `Φ` over the slow coordinates, with
equilibrium `Φ s₀`, fast block `A` and reduced Jacobian `R`. If `A` and `R` are spectrally stable
(all eigenvalues in the open left half-plane), there is `ε* > 0` such that for every
`ε ∈ (0, ε*)` the `ε`-system — the fast rows multiplied by `ε⁻¹` — is locally exponentially
stable at `Φ s₀`. -/
@[tmio T, powerlib_foundation] theorem exists_epsStar_locallyExponentiallyStable_of_graph {N : ℕ}
    (e : Fin N ≃ F ⊕ S) {f : Dynamics.State N → Dynamics.State N} {U : Set (Dynamics.State N)}
    (hU : IsOpen U) {Φ : EuclideanSpace ℝ S → Dynamics.State N} {s₀ : EuclideanSpace ℝ S}
    (hx : Φ s₀ ∈ U) (hf : ContDiffOn ℝ 1 f U) (heq : f (Φ s₀) = 0) {A : Matrix F F ℝ}
    {R : Matrix S S ℝ} (hΦ : DifferentiableAt ℝ Φ s₀)
    (hslow : ∀ s k, Φ s (e.symm (.inr k)) = s k) (hfast : ∀ s i, f (Φ s) (e.symm (.inl i)) = 0)
    (hA : ∀ i j, HasDerivAt
      (fun t : ℝ => f (Φ s₀ + t • EuclideanSpace.single (e.symm (.inl j)) 1) (e.symm (.inl i)))
      (A i j) 0)
    (hR : HasFDerivAt (fun s => (WithLp.toLp 2 fun k => f (Φ s) (e.symm (.inr k)) :
      EuclideanSpace ℝ S)) (Matrix.toEuclideanCLM (𝕜 := ℝ) R) s₀)
    (hAs : Linear.SpectrallyStable A) (hRs : Linear.SpectrallyStable R) :
    ∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      LocallyExponentiallyStable (splitScaledField e ε f) (Φ s₀) := by
  have hdiff : DifferentiableAt ℝ f (Φ s₀) :=
    (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  set J := (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).symm (fderiv ℝ f (Φ s₀)) with hJdef
  have hJ : HasFDerivAt f (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (Φ s₀) := by
    simpa [J] using hdiff.hasFDerivAt
  obtain ⟨P0, hP0, hL0⟩ := exists_posDef_lyapunov_of_spectrallyStable hRs
  obtain ⟨P2, hP2, hL2⟩ := exists_posDef_lyapunov_of_spectrallyStable hAs
  exact ⟨graphEpsStar e J P0 P2, graphEpsStar_pos e J P0 P2, fun ε hε hεs =>
    locallyExponentiallyStable_of_lt_graphEpsStar e hU hx hf heq hJ hΦ hslow hfast hA hR hP0 hP2
      hL0 hL2 hε hεs⟩

end Scaled

/-! ## Instability on a quasi-steady graph -/

section Unstable

variable {F S : Type*} [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S]

/-- **Determinant-sign instability on a quasi-steady graph**, for a field `C¹` near the point
only: with the data of `LinearAlgebra.exists_blocks_of_graph` at an equilibrium `Φ s₀`, a fast
block `A` and a reduced Jacobian `R` with `(−1)^N det A · det R < 0` give a positive real
eigenvalue of the Jacobian (`LinearAlgebra.det_eq_det_fast_mul_det_reduced`,
`Criteria.exists_pos_real_eigenvalue_of_det`), hence instability. -/
@[tmio T, powerlib_foundation] theorem unstable_of_det_fast_mul_det_reduced {N : ℕ}
    (e : Fin N ≃ F ⊕ S) {f : Dynamics.State N → Dynamics.State N} {U : Set (Dynamics.State N)}
    (hU : IsOpen U) {Φ : EuclideanSpace ℝ S → Dynamics.State N} {s₀ : EuclideanSpace ℝ S}
    (hx : Φ s₀ ∈ U) (hf : ContDiffOn ℝ 1 f U) (heq : f (Φ s₀) = 0) {A : Matrix F F ℝ}
    {R : Matrix S S ℝ} (hΦ : DifferentiableAt ℝ Φ s₀)
    (hslow : ∀ s k, Φ s (e.symm (.inr k)) = s k) (hfast : ∀ s i, f (Φ s) (e.symm (.inl i)) = 0)
    (hA : ∀ i j, HasDerivAt
      (fun t : ℝ => f (Φ s₀ + t • EuclideanSpace.single (e.symm (.inl j)) 1) (e.symm (.inl i)))
      (A i j) 0)
    (hR : HasFDerivAt (fun s => (WithLp.toLp 2 fun k => f (Φ s) (e.symm (.inr k)) :
      EuclideanSpace ℝ S)) (Matrix.toEuclideanCLM (𝕜 := ℝ) R) s₀)
    (hdet : (-1) ^ N * (A.det * R.det) < 0) : Unstable f (Φ s₀) := by
  have hdiff : DifferentiableAt ℝ f (Φ s₀) :=
    (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  set J := (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).symm (fderiv ℝ f (Φ s₀)) with hJdef
  have hJac : fderiv ℝ f (Φ s₀) = Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) J := by simp [J]
  have hJ : HasFDerivAt f (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (Φ s₀) := by
    rw [← hJac]; exact hdiff.hasFDerivAt
  have hdetJ := LinearAlgebra.det_eq_det_fast_mul_det_reduced e hJ hΦ hslow hfast hA hR
  obtain ⟨r, hr, v, hv, heig⟩ := Criteria.exists_pos_real_eigenvalue_of_det J (by rwa [hdetJ])
  exact Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local hU hx J hf heq hJac
    ⟨r, v, hv, heig, by rwa [Complex.ofReal_re]⟩

end Unstable

/-! ## The characteristic determinant at a positive real frequency -/

section Frequency

variable {n : ℕ}

/-- If `det (r • 1 − A) ≤ 0` at some real `r`, the real matrix `A` has a real eigenvalue `μ ≥ r`:
`r` itself when the determinant vanishes, otherwise a positive eigenvalue of `A − r • 1`
(`Criteria.exists_pos_real_eigenvalue_of_det`), shifted by `r`. -/
@[tmio T, powerlib_foundation] theorem exists_real_eigenvalue_ge_of_det_sub_nonpos
    (A : Matrix (Fin n) (Fin n) ℝ) {r : ℝ} (h : (r • (1 : Matrix _ _ ℝ) - A).det ≤ 0) :
    ∃ μ : ℝ, r ≤ μ ∧ ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = (μ : ℂ) • v := by
  rcases h.lt_or_eq with hlt | h0
  · have hdet : (-1) ^ n * (A - r • (1 : Matrix _ _ ℝ)).det < 0 := by
      have : A - r • (1 : Matrix _ _ ℝ) = -(r • (1 : Matrix _ _ ℝ) - A) := by abel
      rw [this, Matrix.det_neg, Fintype.card_fin, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
        neg_one_sq, one_pow, one_mul]
      exact hlt
    obtain ⟨μ, hμ, v, hv, heig⟩ := Criteria.exists_pos_real_eigenvalue_of_det _ hdet
    refine ⟨μ + r, by linarith, v, hv, ?_⟩
    have hmap : (A - r • (1 : Matrix _ _ ℝ)).map (algebraMap ℝ ℂ) =
        A.map (algebraMap ℝ ℂ) - (r : ℂ) • 1 := by
      ext i j
      simp [Matrix.one_apply, Complex.coe_algebraMap]
      split_ifs <;> simp
    rw [hmap, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add] at heig
    rw [heig, Complex.ofReal_add, add_smul]
  · obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨r, le_rfl, fun i => (v i : ℂ), fun h => hv (funext fun i => by
      simpa using congrFun h i), ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
    have key : A.map (algebraMap ℝ ℂ) *ᵥ (fun i => (v i : ℂ)) = fun i => ((A *ᵥ v) i : ℂ) := by
      ext i; simp [Matrix.mulVec, dotProduct, Complex.coe_algebraMap]
    rw [key, ← hz]
    ext i
    simp

/-- The frequency test for instability: at an equilibrium of a `C¹` field whose Jacobian `A`
satisfies `det (r • 1 − A) ≤ 0` at some `r > 0`, the equilibrium is unstable. -/
@[tmio T, powerlib_foundation] theorem unstable_of_det_sub_nonpos
    {f : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x = 0)
    (hJac : fderiv ℝ f x = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) {r : ℝ} (hr : 0 < r)
    (h : (r • (1 : Matrix _ _ ℝ) - A).det ≤ 0) : Unstable f x := by
  obtain ⟨μ, hμ, v, hv, heig⟩ := exists_real_eigenvalue_ge_of_det_sub_nonpos A h
  exact unstable_of_exists_complex_eigenvalue_re_pos A hf heq hJac
    ⟨μ, v, hv, heig, by rw [Complex.ofReal_re]; linarith⟩

end Frequency

end powerlib.SingularPerturbation
