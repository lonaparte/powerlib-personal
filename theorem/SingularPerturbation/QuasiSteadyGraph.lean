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
  arbitrary coordinate order). Equilibrium-level (local) statements; no claim about the basin,
  its uniformity in `ε` or finite-horizon approximation.

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
* `exists_epsStar_locallyExponentiallyStable_of_graph`: if the fast block and the reduced
  Jacobian are spectrally stable, there is `ε* > 0` such that for every `ε ∈ (0, ε*)` the field
  with its fast rows multiplied by `ε⁻¹` is locally exponentially stable at the point (Kokotović's
  theorem `LinearSP.exists_epsStar_isHurwitz` and the local indirect method
  `Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local`).
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
  have hJac : fderiv ℝ f (Φ s₀) = Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) J := by simp [J]
  have hJ : HasFDerivAt f (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (Φ s₀) := by
    rw [← hJac]; exact hdiff.hasFDerivAt
  obtain ⟨hA11, H, hH, hHR⟩ := LinearAlgebra.exists_blocks_of_graph e hJ hΦ hslow hfast hA hR
  have hAu : IsUnit A.det := isUnit_det_of_spectrallyStable hAs
  have hRS := LinearAlgebra.reducedJacobian_eq_schur hAu hH hHR
  set sp := splitSP e J
  have h22 : LinearSystems.IsHurwitz sp.A22 := by
    rw [← Linear.spectrallyStable_iff_isHurwitz]
    show Linear.SpectrallyStable (((J.reindex e e).toBlocks₁₁).reindex _ _)
    rw [Linear.spectrallyStable_reindex, hA11]
    exact hAs
  have h0 : LinearSystems.IsHurwitz sp.reducedMatrix := by
    rw [← Linear.spectrallyStable_iff_isHurwitz, reducedMatrix_splitSP, hA11, ← hRS,
      Linear.spectrallyStable_reindex]
    exact hRs
  obtain ⟨εs, hεs, hε⟩ := sp.exists_epsStar_isHurwitz h22 h0
  refine ⟨εs, hεs, fun ε hε0 hεlt => ?_⟩
  set L := Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (splitScale e ε)
  have hHur : LinearSystems.IsHurwitz (splitScale e ε * J) := by
    have h := hε ε hε0 hεlt
    rw [← Linear.spectrallyStable_iff_isHurwitz] at h ⊢
    rw [LinearSP.stateMatrix, Linear.spectrallyStable_reindex, ← reindex_splitScale_mul,
      Linear.spectrallyStable_reindex] at h
    exact h
  have hderiv : fderiv ℝ (splitScaledField e ε f) (Φ s₀) =
      Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (splitScale e ε * J) := by
    have h := (L.hasFDerivAt.comp (Φ s₀) hJ).fderiv
    rw [← ContinuousLinearMap.mul_def, ← map_mul] at h
    exact h
  refine Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local hU hx _
    (L.contDiff.comp_contDiffOn hf) ?_ hderiv hHur
  simp [splitScaledField, heq]

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
