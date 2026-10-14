import theorem.Linear.Transfer

/-! # Linearization of nonlinear fields

LeanForControl's indirect method for a `C¹` field `f : ℝⁿ → ℝⁿ` with an equilibrium `x*` whose
Jacobian, computed by `fderiv`, is the matrix `A`.

Scope.
* Generic foundation, independent of any model. The proofs are the upstream theorems
  `hurwitz_linearization_locally_exponentially_stable` and
  `unstable_of_exists_complex_eigenvalue_re_pos`, unchanged; the root form only converts a root of
  `Linear.characteristicMatrix` into an eigenvector.

Source: work-sync `theory/T-dynamical-systems.md` §1.3 (first-order linearization at an
equilibrium) and `theory/T-small-signal-stability.md` §1.3, §1.6 (local stability from the
eigenvalues); Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.7, as formalized in LeanForControl.

Results.
* `locallyExponentiallyStable_of_isHurwitz_jacobian`,
  `locallyExponentiallyStable_of_spectrallyStable_jacobian`: a Hurwitz (spectrally stable) `A`
  gives local exponential stability.
* `unstable_of_jacobian_eigenvalue_re_pos`, `unstable_of_characteristic_root_re_pos`: an
  eigenvalue, or a root of the characteristic polynomial `det (s I - A)`, in the open right half
  plane gives instability.
-/

noncomputable section

namespace powerlib.Dynamics

open Matrix LinearSystems

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A Hurwitz Jacobian at an equilibrium gives local exponential stability (LeanForControl's
`hurwitz_linearization_locally_exponentially_stable`). -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_isHurwitz_jacobian
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : IsHurwitz A) : LocallyExponentiallyStable f x_eq :=
  hurwitz_linearization_locally_exponentially_stable A hf heq hJac hA

/-- A spectrally stable Jacobian at an equilibrium gives local exponential stability. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_spectrallyStable_jacobian
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : Linear.SpectrallyStable A) : LocallyExponentiallyStable f x_eq :=
  locallyExponentiallyStable_of_isHurwitz_jacobian A hf heq hJac
    ((Linear.spectrallyStable_iff_isHurwitz A).mp hA)

/-- A Jacobian eigenvalue in the open right half plane gives instability (LeanForControl's
`unstable_of_exists_complex_eigenvalue_re_pos`). -/
@[powerlib_foundation] theorem unstable_of_jacobian_eigenvalue_re_pos
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hunstable : ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re) :
    Unstable f x_eq :=
  unstable_of_exists_complex_eigenvalue_re_pos A hf heq hJac hunstable

/-- A root of the Jacobian's characteristic polynomial in the open right half plane gives
instability. -/
@[powerlib_foundation] theorem unstable_of_characteristic_root_re_pos
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {s : ℂ} (hroot : (Linear.characteristicMatrix A s).det = 0) (hs : 0 < s.re) :
    Unstable f x_eq := by
  obtain ⟨v, hv, heig⟩ := Linear.exists_eigenvector_of_root hroot
  exact unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac ⟨s, v, hv, heig, hs⟩

end powerlib.Dynamics
