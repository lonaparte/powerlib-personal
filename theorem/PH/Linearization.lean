import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import theorem.PH.Nonlinear
import theorem.Dynamics.Linearization

/-! Smoothness and linearization of the zero-input nonlinear port-Hamiltonian field
`f(x) = (J(x) − R(x)) ∇H(x)` of `powerlib.PH.NonlinearModel`.

Model boundary.
* Same model as `theorem/PH/Nonlinear.lean`: state `State n`, continuous time, zero input
  `u = 0` (the field does not depend on `g`). Regularity is assumed entrywise for `J`, `R`
  and as `C¹` (or differentiability at a point) for the gradient field `dH`.
* Linearization point: a critical point `x*` of `H` (`∇H(x*) = 0`), hence an equilibrium.
  With `Q` the derivative of `∇H` at `x*` (the Hessian), the Jacobian of `f` at `x*` is
  `A = (J(x*) − R(x*)) Q`: the derivatives of `J` and `R` drop out because `∇H(x*) = 0`.
* Conclusions: local exponential stability of `x*` when `A` is Hurwitz, and instability of
  `x*` when `A` has an eigenvalue with positive real part, both for the full nonlinear
  zero-input field (Lyapunov indirect method, via `theorem/Hurwitz.lean`).
* Excluded: nonzero constant inputs / shifted Hamiltonians, critical points that are not
  equilibria of a forced system, PBC, delay, PWM, PLL, saturation.

Source: work-sync `theory/T-ph.md` §1.10 (linearization (1.15), `A_ph = (J* − R*) Q`
with `Q = ∇²H(x*)`).
Correction: §1.10 requires `Q ≻ 0` to call (1.15) the linearization; the Jacobian identity
holds for any critical point and any Hessian `Q`. Definiteness of `Q` is only relevant for
stability, and is not assumed by the Hurwitz / instability statements here.

Family and connection conclusions. No family: `NonlinearModel` is the generic framework of
`theorem/PH/Nonlinear.lean`, which no family takes as its model type. The two former
`@[powerlib_domain]` theorems (`locallyExponentiallyStable_of_isHurwitz`,
`unstable_of_eigenvalue_re_pos`) are generic implications for every nonlinear pH system and are
relabeled `@[powerlib_foundation]` (the indirect method, LeanForControl's linearization theorems
through `Dynamics.Linearization`). Concrete families built on `NonlinearModel` (for example the
classical machine in `theorem/PH/SyncMachine.lean`) publish their connection conclusions through
`Family.IsNonlinearPH.mem_den_flow_shift`.
-/

noncomputable section
namespace powerlib.PH
open Matrix Set Filter
open powerlib.Dynamics (State)

variable {n m : ℕ}

namespace NonlinearModel

variable (M : NonlinearModel n m)

private lemma field_apply (x : State n) (u : Fin m → ℝ) (i : Fin n) :
    M.field x u i =
      ∑ j, (M.J x i j - M.R x i j) * M.dH x j + ∑ j, M.g x i j * u j := by
  simp [field, mulVec, dotProduct]

/-- Entrywise `Cᵏ` coefficients and a `Cᵏ` gradient give a `Cᵏ` field for each fixed input. -/
@[powerlib_foundation] theorem contDiff_field {k : WithTop ℕ∞}
    (hJ : ∀ i j, ContDiff ℝ k fun x => M.J x i j) (hR : ∀ i j, ContDiff ℝ k fun x => M.R x i j)
    (hg : ∀ i j, ContDiff ℝ k fun x => M.g x i j) (hdH : ContDiff ℝ k M.dH)
    (u : Fin m → ℝ) : ContDiff ℝ k fun x => M.field x u := by
  rw [contDiff_euclidean]
  intro i
  have hb := contDiff_euclidean.mp hdH
  simp only [field_apply]
  exact (ContDiff.sum fun j _ => ((hJ i j).sub (hR i j)).mul (hb j)).add
    (ContDiff.sum fun j _ => (hg i j).mul contDiff_const)

/-- Entrywise `Cᵏ` `J`, `R` and a `Cᵏ` gradient give a `Cᵏ` zero-input field. -/
@[powerlib_foundation] theorem contDiff_zeroInputField {k : WithTop ℕ∞}
    (hJ : ∀ i j, ContDiff ℝ k fun x => M.J x i j) (hR : ∀ i j, ContDiff ℝ k fun x => M.R x i j)
    (hdH : ContDiff ℝ k M.dH) : ContDiff ℝ k M.zeroInputField := by
  rw [contDiff_euclidean]
  intro i
  have hb := contDiff_euclidean.mp hdH
  have hfun : (fun x => M.zeroInputField x i) =
      fun x => ∑ j, (M.J x i j - M.R x i j) * M.dH x j := by
    funext x
    simp [zeroInputField, field_apply]
  rw [hfun]
  exact ContDiff.sum fun j _ => ((hJ i j).sub (hR i j)).mul (hb j)

/-- At a critical point `x*` of `H`, the Jacobian of `(J − R) ∇H` is `(J(x*) − R(x*)) Q`,
where `Q` is the derivative of `∇H` at `x*`. -/
@[powerlib_foundation] theorem hasFDerivAt_zeroInputField_of_dH_eq_zero {xs : State n}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hJ : ∀ i j, DifferentiableAt ℝ (fun x => M.J x i j) xs)
    (hR : ∀ i j, DifferentiableAt ℝ (fun x => M.R x i j) xs)
    (hdH : HasFDerivAt M.dH (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q) xs)
    (h0 : M.dH xs = 0) :
    HasFDerivAt M.zeroInputField
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((M.J xs - M.R xs) * Q)) xs := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  rw [hasFDerivWithinAt_univ]
  have hb : ∀ j, HasFDerivAt (fun x => M.dH x j)
      (PiLp.proj 2 (fun _ : Fin n => ℝ) j ∘L Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q)
      xs := by
    intro j
    have h := (hasFDerivWithinAt_piLp 2).mp (hdH.hasFDerivWithinAt (s := univ)) j
    exact hasFDerivWithinAt_univ.mp h
  have hterm := fun j => ((hJ i j).hasFDerivAt.sub (hR i j).hasFDerivAt).mul (hb j)
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)
  convert hsum using 1
  · funext x
    simp [zeroInputField, field_apply]
  · ext v
    have h0j : ∀ j, M.dH xs j = 0 := fun j => by rw [h0]; rfl
    simp [h0j, mulVec, dotProduct, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]

/-- The Jacobian of the zero-input field at a critical point of `H`. -/
@[powerlib_foundation] theorem fderiv_zeroInputField_of_dH_eq_zero {xs : State n}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hJ : ∀ i j, DifferentiableAt ℝ (fun x => M.J x i j) xs)
    (hR : ∀ i j, DifferentiableAt ℝ (fun x => M.R x i j) xs)
    (hdH : HasFDerivAt M.dH (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q) xs)
    (h0 : M.dH xs = 0) :
    fderiv ℝ M.zeroInputField xs =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((M.J xs - M.R xs) * Q) :=
  (M.hasFDerivAt_zeroInputField_of_dH_eq_zero hJ hR hdH h0).fderiv

/-- Lyapunov indirect method for nonlinear pH systems: at a critical point `x*` of `H`
with Hessian `Q`, if `(J(x*) − R(x*)) Q` is Hurwitz then `x*` is a locally exponentially
stable equilibrium of the full zero-input field. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_isHurwitz {xs : State n}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hJ : ∀ i j, ContDiff ℝ 1 fun x => M.J x i j) (hR : ∀ i j, ContDiff ℝ 1 fun x => M.R x i j)
    (hdH : ContDiff ℝ 1 M.dH)
    (hQ : fderiv ℝ M.dH xs = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q)
    (h0 : M.dH xs = 0) (hA : LinearSystems.IsHurwitz ((M.J xs - M.R xs) * Q)) :
    LocallyExponentiallyStable M.zeroInputField xs := by
  have hdiff : DifferentiableAt ℝ M.dH xs := (hdH.differentiable (by norm_num)) xs
  have hJac := M.fderiv_zeroInputField_of_dH_eq_zero
    (fun i j => ((hJ i j).differentiable (by norm_num)) xs)
    (fun i j => ((hR i j).differentiable (by norm_num)) xs)
    (hQ ▸ hdiff.hasFDerivAt) h0
  exact Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian _
    (M.contDiff_zeroInputField hJ hR hdH) (M.zeroInputField_eq_zero_of_dH_eq_zero h0) hJac hA

/-- At a critical point `x*` of `H` with Hessian `Q`, an eigenvalue of `(J(x*) − R(x*)) Q`
with positive real part makes `x*` an unstable equilibrium of the full zero-input field. -/
@[powerlib_foundation] theorem unstable_of_eigenvalue_re_pos {xs : State n}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hJ : ∀ i j, ContDiff ℝ 1 fun x => M.J x i j) (hR : ∀ i j, ContDiff ℝ 1 fun x => M.R x i j)
    (hdH : ContDiff ℝ 1 M.dH)
    (hQ : fderiv ℝ M.dH xs = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q)
    (h0 : M.dH xs = 0)
    (hunstable : ∃ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 ∧
      ((M.J xs - M.R xs) * Q).map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re) :
    Unstable M.zeroInputField xs := by
  have hdiff : DifferentiableAt ℝ M.dH xs := (hdH.differentiable (by norm_num)) xs
  have hJac := M.fderiv_zeroInputField_of_dH_eq_zero
    (fun i j => ((hJ i j).differentiable (by norm_num)) xs)
    (fun i j => ((hR i j).differentiable (by norm_num)) xs)
    (hQ ▸ hdiff.hasFDerivAt) h0
  exact Dynamics.unstable_of_jacobian_eigenvalue_re_pos _
    (M.contDiff_zeroInputField hJ hR hdH) (M.zeroInputField_eq_zero_of_dH_eq_zero h0) hJac
    hunstable

end NonlinearModel

end powerlib.PH
