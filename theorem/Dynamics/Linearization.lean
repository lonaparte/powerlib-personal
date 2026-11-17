import theorem.Linear.Transfer

/-! # Linearization of nonlinear fields

LeanForControl's indirect method for a `C¹` field `f : ℝⁿ → ℝⁿ` with an equilibrium `x*` whose
Jacobian, computed by `fderiv`, is the matrix `A`.

Scope.
* Generic foundation, independent of any model. The indirect method itself is used directly from
  LeanForControl (`hurwitz_linearization_locally_exponentially_stable`,
  `unstable_of_exists_complex_eigenvalue_re_pos`, same hypotheses); this module adds only the
  pole forms, which convert `Linear.SpectrallyStable` and a root of `Linear.characteristicMatrix`
  into the eigenpair statements.

Source: work-sync `theory/T-dynamical-systems.md` §1.3 (first-order linearization at an
equilibrium) and `theory/T-small-signal-stability.md` §1.3, §1.6 (local stability from the
eigenvalues); Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.7, as formalized in LeanForControl.

Results.
* Local exponential stability from a spectrally stable Jacobian is LeanForControl's
  `hurwitz_linearization_locally_exponentially_stable` with `Linear.spectrallyStable_iff_isHurwitz`.
* `unstable_of_characteristic_root_re_pos`: a root of the characteristic polynomial
  `det (s I - A)` in the open right half plane gives instability (an eigenvalue: LeanForControl's
  `unstable_of_exists_complex_eigenvalue_re_pos`).
-/

noncomputable section

namespace powerlib.Dynamics

open Matrix LinearSystems

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A root of the Jacobian's characteristic polynomial in the open right half plane gives
instability. -/
@[tmio T, powerlib_foundation] theorem unstable_of_characteristic_root_re_pos
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {s : ℂ} (hroot : (Linear.characteristicMatrix A s).det = 0) (hs : 0 < s.re) :
    Unstable f x_eq := by
  obtain ⟨v, hv, heig⟩ := Linear.exists_eigenvector_of_root hroot
  exact unstable_of_exists_complex_eigenvalue_re_pos A hf heq hJac ⟨s, v, hv, heig, hs⟩

end powerlib.Dynamics
