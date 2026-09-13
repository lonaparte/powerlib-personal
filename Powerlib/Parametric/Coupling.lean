import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Modal resolvent and parametric coupling

Finite-dimensional complex linear algebra underlying the first harmonic
response. A basis of actual eigenvectors is supplied, rather than an assumed
response formula. The finite modal response is proved to solve the resolvent
equation. No ODE existence, averaging, or stability assertion is assumed here.
-/

noncomputable section

namespace Powerlib.Parametric

open Module
open scoped BigOperators ComplexConjugate

section ModalResponse

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℂ E]

/-- The finite modal candidate for `(z I - A)⁻¹ b`. The theorem below supplies
its resolvent semantics when the basis consists of eigenvectors of `A`. -/
def modalResponse (v : Basis ι ℂ E) (eig : ι → ℂ) (b : E) (z : ℂ) : E :=
  ∑ j, (v.repr b j / (z - eig j)) • v j

/-- The scalar denominator in the paper's decay-rate/frequency notation. -/
theorem spectral_denominator (ω σ Ω : ℝ) :
    Complex.I * (ω : ℂ) - (-(σ : ℂ) + Complex.I * (Ω : ℂ)) =
      (σ : ℂ) + Complex.I * ((ω : ℂ) - (Ω : ℂ)) := by
  ring

/-- Hurwitz eigenvalues cannot meet a positive- or negative-frequency
imaginary-axis spectral parameter. Positivity of the frequency is unnecessary. -/
theorem spectral_denominator_ne_zero (ω : ℝ) (eig : ℂ) (heig : eig.re < 0) :
    Complex.I * (ω : ℂ) - eig ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    Complex.zero_re] at hre
  linarith

/-- Every modal coordinate has the expected denominator. -/
theorem modalResponse_coordinate (v : Basis ι ℂ E) (eig : ι → ℂ)
    (b : E) (z : ℂ) (j : ι) :
    v.repr (modalResponse v eig b z) j = v.repr b j / (z - eig j) := by
  exact congrFun (v.repr_sum_self (fun r => v.repr b r / (z - eig r))) j

/-- Diagonal action in an eigenvector basis, derived by expanding the input. -/
theorem eigenbasis_apply_coordinate (v : Basis ι ℂ E) (A : E →ₗ[ℂ] E)
    (eig : ι → ℂ) (heigen : ∀ j, A (v j) = eig j • v j)
    (x : E) (j : ι) :
    v.repr (A x) j = eig j * v.repr x j := by
  have hAx : A x = ∑ r, (eig r * v.repr x r) • v r := by
    calc
      A x = A (∑ r, v.repr x r • v r) := by rw [v.sum_repr]
      _ = ∑ r, (eig r * v.repr x r) • v r := by
        simp only [map_sum, map_smul, heigen, smul_smul, mul_comm]
  calc
    v.repr (A x) j = v.repr (∑ r, (eig r * v.repr x r) • v r) j := by rw [hAx]
    _ = eig j * v.repr x j := by
      exact congrFun (v.repr_sum_self (fun r => eig r * v.repr x r)) j

/-- The modal formula solves the actual linear resolvent equation. -/
theorem modalResponse_resolvent (v : Basis ι ℂ E) (A : E →ₗ[ℂ] E)
    (eig : ι → ℂ) (heigen : ∀ j, A (v j) = eig j • v j)
    (b : E) (z : ℂ) (hgap : ∀ j, z - eig j ≠ 0) :
    z • modalResponse v eig b z - A (modalResponse v eig b z) = b := by
  apply v.repr.injective
  ext j
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    smul_eq_mul]
  rw [eigenbasis_apply_coordinate v A eig heigen,
    modalResponse_coordinate]
  field_simp [hgap j]
  <;> ring

/-- There is no second solution of the resolvent equation. -/
theorem modalResponse_unique (v : Basis ι ℂ E) (A : E →ₗ[ℂ] E)
    (eig : ι → ℂ) (heigen : ∀ j, A (v j) = eig j • v j)
    (b : E) (z : ℂ) (hgap : ∀ j, z - eig j ≠ 0)
    (x : E) (hx : z • x - A x = b) :
    x = modalResponse v eig b z := by
  apply v.repr.injective
  ext j
  rw [modalResponse_coordinate]
  apply (eq_div_iff (hgap j)).mpr
  have h := congrArg (fun y : E => v.repr y j) hx
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    smul_eq_mul] at h
  rw [eigenbasis_apply_coordinate v A eig heigen] at h
  linear_combination h

/-- Changing the complete eigenbasis does not change the physical response.
In particular, rescaling the target eigenvectors inside the basis leaves the
response used to compute the Jacobian modulation unchanged. -/
theorem modalResponse_basis_independent {κ : Type*} [Fintype κ]
    (v : Basis ι ℂ E) (w : Basis κ ℂ E) (A : E →ₗ[ℂ] E)
    (eig : ι → ℂ) (μ : κ → ℂ)
    (hv : ∀ j, A (v j) = eig j • v j)
    (hw : ∀ j, A (w j) = μ j • w j)
    (b : E) (z : ℂ) (heig : ∀ j, z - eig j ≠ 0)
    (hμ : ∀ j, z - μ j ≠ 0) :
    modalResponse v eig b z = modalResponse w μ b z := by
  exact modalResponse_unique w A μ hw b z hμ _
    (modalResponse_resolvent v A eig hv b z heig)

/-- Including the fixed complex input phasor gives the forced linear response. -/
theorem forced_modalResponse_resolvent (v : Basis ι ℂ E) (A : E →ₗ[ℂ] E)
    (eig : ι → ℂ) (heigen : ∀ j, A (v j) = eig j • v j)
    (b : E) (z u : ℂ) (hgap : ∀ j, z - eig j ≠ 0) :
    z • (u • modalResponse v eig b z) - A (u • modalResponse v eig b z) =
      u • b := by
  rw [map_smul, smul_comm z u, ← smul_sub,
    modalResponse_resolvent v A eig heigen b z hgap]

end ModalResponse

section Coupling

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℂ E]

/-- Project the trajectory-induced bilinear modulation through a left mode. -/
theorem projected_modalResponse (v : Basis ι ℂ E) (eig : ι → ℂ)
    (b : E) (z : ℂ) (H : E →ₗ[ℂ] E →ₗ[ℂ] E)
    (left : E →ₗ[ℂ] ℂ) (partner : E) :
    left (H (modalResponse v eig b z) partner) =
      ∑ j, (v.repr b j * left (H (v j) partner)) / (z - eig j) := by
  simp only [modalResponse, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- First-harmonic conjugate-channel coupling. `H` represents `fₓₓ`, `F`
represents `fₓᵤ[·,1]`, and `left` is the left eigenvector as a covector. -/
def modalCoupling (v : Basis ι ℂ E) (eig : ι → ℂ) (b : E) (z u : ℂ)
    (H : E →ₗ[ℂ] E →ₗ[ℂ] E) (F : E →ₗ[ℂ] E)
    (left : E →ₗ[ℂ] ℂ) (partner : E) : ℂ :=
  left (H (u • modalResponse v eig b z) partner + u • F partner)

/-- The paper's frequency-dependent coupling sum, proved from the finite
resolvent formula and bilinearity. No denominator hypothesis is needed for this
algebraic identity; nonzero denominators enter its resolvent interpretation. -/
theorem modalCoupling_expansion (v : Basis ι ℂ E) (eig : ι → ℂ)
    (b : E) (z u : ℂ) (H : E →ₗ[ℂ] E →ₗ[ℂ] E)
    (F : E →ₗ[ℂ] E) (left : E →ₗ[ℂ] ℂ) (partner : E) :
    modalCoupling v eig b z u H F left partner =
      u * (left (F partner) +
        ∑ j, (v.repr b j * left (H (v j) partner)) / (z - eig j)) := by
  simp only [modalCoupling, map_add, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  rw [projected_modalResponse]
  ring

/-- Scaling a right eigenvector by `α` and its left covector by `α⁻¹`
preserves their pairing. The conjugate partner scales by `conj α`. -/
theorem biorthogonal_scaling (left : E →ₗ[ℂ] ℂ) (right : E)
    (α : ℂ) (hα : α ≠ 0) :
    (α⁻¹ • left) (α • right) = left right := by
  simp [LinearMap.smul_apply, map_smul, smul_eq_mul, hα]

/-- The coupling changes only by `conj α / α` under modal renormalization. -/
theorem modalCoupling_scaling (v : Basis ι ℂ E) (eig : ι → ℂ)
    (b : E) (z u : ℂ) (H : E →ₗ[ℂ] E →ₗ[ℂ] E)
    (F : E →ₗ[ℂ] E) (left : E →ₗ[ℂ] ℂ) (partner : E) (α : ℂ) :
    modalCoupling v eig b z u H F (α⁻¹ • left) (conj α • partner) =
      (conj α / α) * modalCoupling v eig b z u H F left partner := by
  simp only [modalCoupling, LinearMap.smul_apply, map_smul, map_add,
    smul_eq_mul]
  ring

/-- Nonzero modal normalization has no effect on coupling magnitude. -/
theorem modalCoupling_norm_scaling (v : Basis ι ℂ E) (eig : ι → ℂ)
    (b : E) (z u : ℂ) (H : E →ₗ[ℂ] E →ₗ[ℂ] E)
    (F : E →ₗ[ℂ] E) (left : E →ₗ[ℂ] ℂ) (partner : E)
    (α : ℂ) (hα : α ≠ 0) :
    ‖modalCoupling v eig b z u H F (α⁻¹ • left) (conj α • partner)‖ =
      ‖modalCoupling v eig b z u H F left partner‖ := by
  rw [modalCoupling_scaling, Complex.norm_mul, Complex.norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hα), one_mul]

end Coupling

/-- Frequency conversion of the conjugate component has zero relative drift
exactly at twice the intrinsic frequency. -/
theorem primary_phase_matching (ω Ω : ℝ) :
    ω - Ω = Ω ↔ ω = 2 * Ω := by
  constructor <;> intro h <;> linarith

/-- The half-frequency detuning vanishes at the same matching condition. -/
theorem detuning_zero_iff (ω Ω : ℝ) :
    Ω - ω / 2 = 0 ↔ ω = 2 * Ω := by
  constructor <;> intro h <;> linarith

end Powerlib.Parametric
