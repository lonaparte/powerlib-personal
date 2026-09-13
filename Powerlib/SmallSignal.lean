import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Minimal small-signal stability interface

The input is a real state matrix `A` for the continuous-time linearized system
`δx' = A δx`. Here "small-signal stable" means exponential stability of this
linear system. The connection to a nonlinear model or a DAE is outside this file.

There is exactly one domain axiom: `linear_spectral_criterion`. The time-domain
property and the spectral property are defined independently before that axiom.
-/

noncomputable section

namespace Powerlib

variable {n : ℕ}

/-- A global differentiable trajectory of `x' = A x`. For a finite real constant
matrix, global trajectories exist for every initial state. The stability bound
below concerns forward time only. -/
def IsTrajectory (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ → Fin n → ℝ) : Prop :=
  ∀ t : ℝ, HasDerivAt x (A.mulVec (x t)) t

/-- Uniform exponential decay of every trajectory, in the finite product norm.
`C` and `α` are independent of the initial state, trajectory, and time. -/
def SmallSignalStable (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ x : ℝ → Fin n → ℝ, IsTrajectory A x →
      ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-α * t) * ‖x 0‖

/-- A complex root of the actual characteristic polynomial of `A`, after
extending scalars from `ℝ` to `ℂ`. No supplied eigenvalue list is trusted. -/
def HasEigenvalue (A : Matrix (Fin n) (Fin n) ℝ) (z : ℂ) : Prop :=
  (A.map (algebraMap ℝ ℂ)).charpoly.eval z = 0

/-- Every complex eigenvalue has strictly negative real part. -/
def Hurwitz (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z : ℂ, HasEigenvalue A z → z.re < 0

/-- The sole domain axiom: the spectral criterion for exponential stability of
a finite-dimensional continuous-time real LTI system. This is deliberately
assumed, not a completed Lean proof of the analytical theorem. -/
axiom linear_spectral_criterion (A : Matrix (Fin n) (Fin n) ℝ) :
  SmallSignalStable A ↔ Hurwitz A

/-- Use a proof about all characteristic roots to obtain a stability conclusion.
This theorem depends on `linear_spectral_criterion`. -/
theorem smallSignalStable_of_hurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (h : Hurwitz A) : SmallSignalStable A :=
  (linear_spectral_criterion A).mpr h

/-- A single eigenvalue with nonnegative real part rules out exponential
stability. At zero real part this does NOT assert Lyapunov instability or any
conclusion about the original nonlinear system. -/
theorem not_smallSignalStable_of_eigenvalue_nonneg
    {A : Matrix (Fin n) (Fin n) ℝ} {z : ℂ}
    (hz : HasEigenvalue A z) (hre : 0 ≤ z.re) : ¬ SmallSignalStable A := by
  intro h
  exact (not_lt_of_ge hre) ((linear_spectral_criterion A).mp h z hz)

end Powerlib
