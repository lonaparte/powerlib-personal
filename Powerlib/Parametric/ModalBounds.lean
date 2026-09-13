import Powerlib.Parametric.FiniteTime
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Dissipativity in Euclidean modal coordinates

The real part of every diagonal eigenvalue is nonpositive, so the diagonal
modal operator contributes no positive Euclidean energy growth. A bounded
retained modulation contributes at most its operator norm. This supplies the
one-sided hypothesis used by the finite-time perturbation estimates.
-/

noncomputable section

namespace Powerlib.Parametric

variable {ι : Type*} [Fintype ι]

/-- The diagonal modal operator, first as a complex continuous linear map. -/
def modalDiagonalComplex (lam : ι → ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => lam i * x i)
      map_add' := by
        intro x y
        ext i
        change lam i * (x i + y i) = lam i * x i + lam i * y i
        exact mul_add _ _ _
      map_smul' := by
        intro c x
        ext i
        change lam i * (c * x i) = c * (lam i * x i)
        ring }

/-- Realification preserves the same coordinate formula and Euclidean norm. -/
def modalDiagonal (lam : ι → ℂ) :
    EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  (modalDiagonalComplex lam).restrictScalars ℝ

@[simp]
theorem modalDiagonal_apply (lam : ι → ℂ) (z : EuclideanSpace ℂ ι) (i : ι) :
    modalDiagonal lam z i = lam i * z i := rfl

/-- A scalar mode's contribution to the real energy derivative. -/
theorem real_inner_complex_mode (a z : ℂ) :
    inner ℝ z (a * z) = a.re * (z.re ^ 2 + z.im ^ 2) := by
  rw [real_inner_eq_re_inner ℂ]
  simp [RCLike.inner_apply]
  ring

/-- The modal diagonal is dissipative whenever every decay rate is
nonnegative. Strict Hurwitz inequalities are stronger than needed here. -/
theorem modalDiagonal_dissipative (lam : ι → ℂ) (hlam : ∀ i, (lam i).re ≤ 0)
    (z : EuclideanSpace ℂ ι) : inner ℝ z (modalDiagonal lam z) ≤ 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_nonpos
  intro i _
  rw [modalDiagonal_apply, real_inner_complex_mode]
  exact mul_nonpos_of_nonpos_of_nonneg (hlam i) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Strict Hurwitz decay immediately supplies the dissipativity assumption. -/
theorem modalDiagonal_dissipative_of_hurwitz
    (lam : ι → ℂ) (hlam : ∀ i, (lam i).re < 0) (z : EuclideanSpace ℂ ι) :
    inner ℝ z (modalDiagonal lam z) ≤ 0 :=
  modalDiagonal_dissipative lam (fun i => (hlam i).le) z

/-- Concrete modal adapter for the one-sided finite-time estimate: imaginary
carrier frequencies do not enter the upper growth bound. -/
theorem oneSided_modalDiagonal_add
    (lam : ι → ℂ) (hlam : ∀ i, (lam i).re ≤ 0)
    (P : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    {ε K : ℝ} (hε : 0 ≤ ε) (hP : ‖P‖ ≤ K)
    (a b : EuclideanSpace ℂ ι) :
    inner ℝ (a - b)
        ((modalDiagonal lam + ε • P) a - (modalDiagonal lam + ε • P) b) ≤
      ε * K * ‖a - b‖ ^ 2 :=
  oneSided_dissipative_add hε hP (modalDiagonal_dissipative lam hlam) a b

end Powerlib.Parametric
