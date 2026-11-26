import theorem.Periodic.LTI

/-! # Liouville's formula for linear time-varying systems

The determinant of the transition matrix of `ẋ = A(t) x` is the exponential of the integrated
trace, `det Φ(t, s) = exp(∫ₛᵗ tr A)` (Liouville / Abel–Jacobi). Hence the product of the Floquet
multipliers of a periodic system is `det M = exp(∫₀ᵀ tr A)`, whatever the modulation, and for a
constant matrix `det e^{A} = e^{tr A}`.

Scope.
* `ẋ = A(t) x` on `ℝ^X` (finite `X`) with a continuous real state matrix `A`; the transition
  matrix is the Peano–Baker matrix `transition A t s` of `theorem/Periodic/Transition.lean`
  (a fundamental matrix on all of `ℝ`, `Dynamics.stm_hasDerivAt`). No boundedness or
  periodicity is needed for Liouville's formula; the monodromy statements assume a `T`-periodic
  `A`.
* Matrices carry the operator `L∞` norm (`Matrix.Norms.Operator`); the derivative of a
  matrix-valued curve is taken in that norm.
* Generic mathematics; no model family.

Source: Liouville's formula (Abel–Jacobi identity) for linear differential systems, the
determinant law behind the product of the Floquet multipliers (Yakubovich–Starzhinskii);
it fixes the product of the multipliers of a damped second-order system to `e^{−2cT}`, the
starting point of the two-state boundary in `theorem/Periodic/TwoStateBoundary.lean`. Mathlib's
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` lists `det (exp A) = exp (trace A)`
as a TODO; `det_exp` proves it for real matrices.

Results.
* `hasDerivAt_det` — Jacobi's formula: `d/dt det Y(t) = tr(adj Y(t) · Ẏ(t))` (Leibniz expansion
  of the determinant, `Finset.mul_prod_erase`, Cramer's rule `Matrix.cramer_eq_adjugate_mulVec`).
* `hasDerivAt_det_transition` — `∂_t det Φ(t, s) = tr A(t) · det Φ(t, s)`.
* `det_transition` — Liouville: `det Φ(t, s) = exp(∫ₛᵗ tr A)` for all `t, s`.
* `det_monodromy` — for a `T`-periodic `A`: `det M_s = exp(∫₀ᵀ tr A)` for every initial time
  `s`; `det_monodromy_of_trace` — a constant trace `tr A(t) ≡ τ` gives `det M = e^{τT}` (the
  damped second-order case `τ = −2c` gives `e^{−2cT}`).
* `det_exp`, `det_exp_smul` — `det e^{A} = e^{tr A}` and `det e^{tA} = e^{t tr A}` for real
  square matrices.
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Jacobi's formula.** For a differentiable matrix curve,
`d/dt det Y(t) = tr(adj Y(t) · Ẏ(t))`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_det {Y : ℝ → Matrix X X ℝ} {Y' : Matrix X X ℝ}
    {t : ℝ} (h : HasDerivAt Y Y' t) :
    HasDerivAt (fun s => (Y s).det) ((adjugate (Y t) * Y').trace) t := by
  have he : ∀ a b : X, HasDerivAt (fun s => Y s a b) (Y' a b) t := by
    intro a b
    let L : Matrix X X ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      { toFun := fun N => N a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact L.hasFDerivAt.comp_hasDerivAt t h
  have hterm : ∀ σ : Equiv.Perm X,
      HasDerivAt (fun s => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, Y s (σ i) i)
        (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ i, (∏ j ∈ Finset.univ.erase i, Y t (σ j) j) • Y' (σ i) i) t := by
    intro σ
    have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s => Y s (σ i) i)
      (f' := fun i => Y' (σ i) i) (fun i _ => he (σ i) i)
    exact hp.const_mul _
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => hterm σ)
  have hdet : (fun s => (Y s).det) =
      fun s => ∑ σ : Equiv.Perm X, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, Y s (σ i) i := by
    funext s
    exact Matrix.det_apply' _
  rw [hdet]
  refine hsum.congr_deriv ?_
  -- the diagonal of `adj Y · Ẏ` is the sum of the determinants with one column replaced
  have key : ∀ i, (adjugate (Y t) * Y') i i = ∑ σ : Equiv.Perm X,
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((∏ j ∈ Finset.univ.erase i, Y t (σ j) j) * Y' (σ i) i) := by
    intro i
    have h1 : (adjugate (Y t) * Y') i i = cramer (Y t) (fun k => Y' k i) i := by
      rw [cramer_eq_adjugate_mulVec]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, cramer_apply, det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), updateCol_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [updateCol_ne (Finset.ne_of_mem_erase hj)]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  simp [smul_eq_mul]

variable {A : ℝ → Matrix X X ℝ}

/-- `∂_t det Φ(t, s) = tr A(t) · det Φ(t, s)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_det_transition (hA : Continuous A) (t s : ℝ) :
    HasDerivAt (fun u => (transition A u s).det) ((A t).trace * (transition A t s).det) t := by
  refine (hasDerivAt_det (Dynamics.stm_hasDerivAt hA t s)).congr_deriv ?_
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, mul_comm]

/-- **Liouville's formula.** `det Φ(t, s) = exp(∫ₛᵗ tr A)` for all `t, s`. -/
@[tmio T, powerlib_foundation] theorem det_transition (hA : Continuous A) (t s : ℝ) :
    (transition A t s).det = Real.exp (∫ r in s..t, (A r).trace) := by
  have htr : Continuous fun r => (A r).trace := hA.matrix_trace
  set g : ℝ → ℝ := fun u => (transition A u s).det * Real.exp (-∫ r in s..u, (A r).trace)
    with hg
  have hd : ∀ u, HasDerivAt g 0 u := by
    intro u
    have h2 : HasDerivAt (fun u => ∫ r in s..u, (A r).trace) ((A u).trace) u :=
      (htr.integral_hasStrictDerivAt s u).hasDerivAt
    refine ((hasDerivAt_det_transition hA u s).mul h2.neg.exp).congr_deriv ?_
    ring
  have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t s
  simp only [hg, LinearSystems.stateTransitionMatrix_self, det_one, intervalIntegral.integral_same,
    neg_zero, Real.exp_zero, mul_one] at hc
  have h := congrArg (· * Real.exp (∫ r in s..t, (A r).trace)) hc
  simp only [one_mul, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h
  exact h

/-- For a `T`-periodic state matrix the product of the Floquet multipliers is
`det M_s = exp(∫₀ᵀ tr A)`, for every initial time `s`. -/
@[tmio T, powerlib_foundation] theorem det_monodromy (hA : Continuous A) {T : ℝ}
    (hP : Periodic A T) (s : ℝ) :
    (monodromy A T s).det = Real.exp (∫ r in (0 : ℝ)..T, (A r).trace) := by
  have hPtr : Periodic (fun r => (A r).trace) T := fun r => by simp only [hP r]
  rw [monodromy, det_transition hA, hPtr.intervalIntegral_add_eq s 0, zero_add]

/-- A constant trace `tr A(t) ≡ τ` gives `det M = e^{τT}`; for a damped second-order system in
state form (`τ = −2c`) the product of the multipliers is `e^{−2cT}`. -/
@[tmio T, powerlib_foundation] theorem det_monodromy_of_trace (hA : Continuous A) {T τ : ℝ}
    (hP : Periodic A T) (htr : ∀ t, (A t).trace = τ) (s : ℝ) :
    (monodromy A T s).det = Real.exp (τ * T) := by
  rw [det_monodromy hA hP s]
  simp only [htr, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring_nf

/-- `det e^{A} = e^{tr A}` for a real square matrix. -/
@[tmio T, powerlib_foundation] theorem det_exp (B : Matrix X X ℝ) :
    (NormedSpace.exp B).det = Real.exp B.trace := by
  have h := det_transition (A := fun _ => B) continuous_const 1 0
  rw [transition_const B zero_le_one, sub_zero, one_smul] at h
  rw [h]
  simp

/-- `det e^{tA} = e^{t tr A}`. -/
@[tmio T, powerlib_foundation] theorem det_exp_smul (B : Matrix X X ℝ) (t : ℝ) :
    (NormedSpace.exp (t • B)).det = Real.exp (t * B.trace) := by
  rw [det_exp, Matrix.trace_smul, smul_eq_mul]

end powerlib.Periodic
