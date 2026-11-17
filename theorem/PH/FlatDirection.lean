import theorem.PH.Linearization
import theorem.Dynamics.ConverseLinearization

/-! # A coordinate the Hamiltonian ignores: no locally exponentially stable origin

A nonlinear port-Hamiltonian model with a linear gradient `∇H(x) = Q x` whose Hamiltonian does
not depend on one coordinate (`Q e_k = 0`, a zero column of `Q`) has no locally exponentially
stable origin, for its zero-input field and for that field shifted by any constant drift `c`:
at the origin `∇H(0) = 0`, so the Jacobian is `(J(0) − R(0)) Q`
(`fderiv_zeroInputField_of_dH_eq_zero`, `theorem/PH/Linearization.lean`), which kills `e_k`,
while a locally exponentially stable point of a `C¹` field has an injective Jacobian (converse
linearization, `Dynamics.fderiv_injective_of_locallyExponentiallyStable`).

Scope.
* Generic: arbitrary `NonlinearModel n m` with entrywise `C¹` structure matrices `J`, `R` and a
  linear gradient; no model. A constant drift `c` covers frame-rotation terms that do no work.

Source: `theorem/PH/Linearization.lean`, `theorem/Dynamics/ConverseLinearization.lean`;
work-sync `theory/T-ph.md` §1.10 (the linearization `(J* − R*) Q`).

Results.
* `NonlinearModel.not_locallyExponentiallyStable_of_col_eq_zero`.
* Instances: the seven-state dq machine and the 11-state single machine, node and link models
  (`theorem/PowerSystem/Synchronous/PH.lean`, `theorem/PowerSystem/Synchronous/SMIB11PH.lean`),
  whose Hamiltonians do not depend on the rotor angle.

Family and connection conclusions.
* None: a generic behavioural law on fields; the instances publish their conclusions through
  their families.
-/

noncomputable section
namespace powerlib.PH.NonlinearModel
open Matrix
open powerlib.Dynamics (State)

variable {n m : ℕ} (M : NonlinearModel n m)

/-- **A coordinate the Hamiltonian ignores rules out local exponential stability of the origin.**
If `∇H(x) = Q x` with `Q e_k = 0` and `J`, `R` are entrywise `C¹`, then for every constant drift
`c` the origin is not a locally exponentially stable point of `x ↦ (J(x) − R(x)) ∇H(x) − c`. -/
@[tmio T, powerlib_foundation] theorem not_locallyExponentiallyStable_of_col_eq_zero
    {Q : Matrix (Fin n) (Fin n) ℝ} (hdH : M.dH = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q)
    (hJ : ∀ i j, ContDiff ℝ 1 fun x => M.J x i j) (hR : ∀ i j, ContDiff ℝ 1 fun x => M.R x i j)
    {k : Fin n} (hk : Q.col k = 0) (c : State n) :
    ¬ LocallyExponentiallyStable (fun x => M.zeroInputField x - c) 0 := by
  intro h
  have hQ : HasFDerivAt M.dH (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q) 0 := by
    rw [hdH]
    exact ContinuousLinearMap.hasFDerivAt _
  have hC : ContDiff ℝ 1 fun x => M.zeroInputField x - c :=
    (M.contDiff_zeroInputField hJ hR (by rw [hdH]; exact ContinuousLinearMap.contDiff _)).sub
      contDiff_const
  have hfd : fderiv ℝ (fun x => M.zeroInputField x - c) 0 (EuclideanSpace.single k 1) = 0 := by
    rw [fderiv_sub_const, M.fderiv_zeroInputField_of_dH_eq_zero
      (fun i j => ((hJ i j).differentiable one_ne_zero) 0)
      (fun i j => ((hR i j).differentiable one_ne_zero) 0) hQ (by rw [hdH, map_zero])]
    ext i
    simp [hk]
  have hv : (EuclideanSpace.single k 1 : State n) ≠ 0 := fun h0 => by
    simpa using congrArg (fun z : State n => z k) h0
  exact hv (Dynamics.fderiv_injective_of_locallyExponentiallyStable hC h (by rw [hfd, map_zero]))

end powerlib.PH.NonlinearModel
