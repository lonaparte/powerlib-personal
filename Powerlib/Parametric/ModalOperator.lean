import Powerlib.Parametric.NormalForm
import Powerlib.Parametric.ModalBounds

/-!
# Transport matrix normal forms to Euclidean state operators

The matrix-to-operator map is constructed from the actual matrix action. It
preserves multiplication and diagonal generators and is continuous and real
linear. Thus the entrywise Fourier homological proof transports to the operator
setting used by the trajectory and finite-time estimates.
-/

noncomputable section

namespace Powerlib.Parametric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix action on complex Euclidean coordinates, as a real-linear map in
the matrix argument. -/
def modalOperatorLinear :
    Matrix ι ι ℂ →ₗ[ℝ] (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) where
  toFun A := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).restrictScalars ℝ
  map_add' A B := by
    ext z i
    change (A + B).mulVec (WithLp.ofLp z) i =
      A.mulVec (WithLp.ofLp z) i + B.mulVec (WithLp.ofLp z) i
    exact congrFun (Matrix.add_mulVec A B (WithLp.ofLp z)) i
  map_smul' r A := by
    ext z i
    change (r • A).mulVec (WithLp.ofLp z) i = (r • A.mulVec (WithLp.ofLp z)) i
    exact congrFun (Matrix.smul_mulVec r A (WithLp.ofLp z)) i

/-- The matrix-to-operator map is continuous because its domain is finite
dimensional. This transports actual time derivatives. -/
def modalOperator :
    Matrix ι ι ℂ →L[ℝ] (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) :=
  LinearMap.toContinuousLinearMap modalOperatorLinear

@[simp]
theorem modalOperator_apply (A : Matrix ι ι ℂ) (z : EuclideanSpace ℂ ι) (i : ι) :
    modalOperator A z i = A.mulVec (WithLp.ofLp z) i := rfl

/-- Matrix composition agrees with operator composition. -/
@[simp]
theorem modalOperator_mul (A B : Matrix ι ι ℂ) :
    modalOperator (A * B) = modalOperator A * modalOperator B := by
  ext z i
  change (A * B).mulVec (WithLp.ofLp z) i =
    A.mulVec (B.mulVec (WithLp.ofLp z)) i
  exact congrFun (Matrix.mulVec_mulVec (WithLp.ofLp z) A B).symm i

@[simp]
theorem modalOperator_one : modalOperator (1 : Matrix ι ι ℂ) = 1 := by
  ext z i
  change (1 : Matrix ι ι ℂ).mulVec (WithLp.ofLp z) i = z i
  exact congrFun (Matrix.one_mulVec (WithLp.ofLp z)) i

/-- The diagonal used in the matrix normal form is the dissipative modal
operator already supplied to the finite-time estimate. -/
@[simp]
theorem modalOperator_diagonal (lam : ι → ℂ) :
    modalOperator (Matrix.diagonal lam) = modalDiagonal lam := by
  ext z i
  change (Matrix.diagonal lam).mulVec (WithLp.ofLp z) i = lam i * z i
  exact Matrix.mulVec_diagonal lam (WithLp.ofLp z) i

/-- Transport a matrix-valued time derivative to the real operator space. -/
theorem hasDerivAt_modalOperator
    {A : ℝ → Matrix ι ι ℂ} {A' : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s : ℝ => modalOperator (A s)) (modalOperator A') t := by
  let K : (ι → ι → ℂ) →L[ℝ] (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) :=
    modalOperator
  have hpi : HasDerivAt (fun s : ℝ => (A s : ι → ι → ℂ)) (A' : ι → ι → ℂ) t := hA
  simpa only [Function.comp_def, K] using! K.hasFDerivAt.comp_hasDerivAt t hpi

open NormalForm

/-- The constructed single-harmonic correction satisfies the homological
equation as an actual continuous-linear-operator-valued derivative. -/
theorem hasDerivAt_modalHomological
    (β : ℂ) (lam : ι → ℂ) (C : Matrix ι ι ℂ) (removed : ι → ι → Prop)
    (hgap : ∀ j r, removed j r → β - lam j + lam r ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => modalOperator (fourierMode β (homologicalCoefficient β lam C removed) s))
      (modalDiagonal lam * modalOperator (fourierMode β (homologicalCoefficient β lam C removed) t) -
        modalOperator (fourierMode β (homologicalCoefficient β lam C removed) t) * modalDiagonal lam +
        modalOperator (fourierMode β (removedCoefficient C removed) t)) t := by
  have h := hasDerivAt_modalOperator
    (hasDerivAt_homological β lam C removed hgap t)
  simpa only [map_add, map_sub, modalOperator_mul, modalOperator_diagonal] using h

/-- Both pump harmonics can be transported and combined without postulating
the homological equation in the operator coordinates. -/
theorem hasDerivAt_two_modalHomological
    (β₁ β₂ : ℂ) (lam : ι → ℂ) (C₁ C₂ : Matrix ι ι ℂ)
    (removed₁ removed₂ : ι → ι → Prop)
    (hgap₁ : ∀ j r, removed₁ j r → β₁ - lam j + lam r ≠ 0)
    (hgap₂ : ∀ j r, removed₂ j r → β₂ - lam j + lam r ≠ 0)
    (t : ℝ) :
    let S₁ := fun s => modalOperator (fourierMode β₁ (homologicalCoefficient β₁ lam C₁ removed₁) s)
    let S₂ := fun s => modalOperator (fourierMode β₂ (homologicalCoefficient β₂ lam C₂ removed₂) s)
    let H₁ := fun s => modalOperator (fourierMode β₁ (removedCoefficient C₁ removed₁) s)
    let H₂ := fun s => modalOperator (fourierMode β₂ (removedCoefficient C₂ removed₂) s)
    HasDerivAt (fun s : ℝ => S₁ s + S₂ s)
      (modalDiagonal lam * (S₁ t + S₂ t) -
        (S₁ t + S₂ t) * modalDiagonal lam + H₁ t + H₂ t) t := by
  dsimp only
  refine ((hasDerivAt_modalHomological β₁ lam C₁ removed₁ hgap₁ t).add
    (hasDerivAt_modalHomological β₂ lam C₂ removed₂ hgap₂ t)).congr_deriv ?_
  noncomm_ring

end Powerlib.Parametric
