import theorem.LTI.Discrete
import theorem.Linear.EigenMap
import theorem.Criteria.Hurwitz

/-! # One-step schemes for an autonomous field and their linear-field reduction

One-step time-integration schemes for an autonomous vector field, their exact reduction to
discrete LTI recursions when the field is linear, and the stability of those recursions.

Model boundary.
* The continuous model is an autonomous field `f : E → E` (`ẋ = f x`), with a fixed step `h`.
  For the linear results `E = Fin n → ℝ` and `f = linearField A`, i.e. `ẋ = A x`; inputs, if
  any, are already set to zero (perturbation coordinates).
* Schemes are trajectory predicates written directly from the update rule: forward Euler
  `x_{k+1} = x_k + h f(x_k)`, backward Euler `x_{k+1} = x_k + h f(x_{k+1})`, trapezoidal rule
  `x_{k+1} = x_k + (h/2)(f(x_k) + f(x_{k+1}))`. No step-size control, no Newton iteration
  error: the implicit equation is assumed solved exactly.
* For a linear field the predicates are proved equivalent to the discrete recursions with
  matrices `1 + hA`, `(1 - hA)⁻¹` and `(1 - (h/2)A)⁻¹ (1 + (h/2)A)` (the latter two whenever
  the implicit matrix is invertible).
* Stability statements are about the discretized recursion, not the continuous system.

Source: work-sync theory/T-numerical-integration.md §1.2, §1.3, §1.7, §2.7;
theory/T-emt-simulation.md §1.3–§1.5 (trapezoidal discretization).

Results.
* `isUnit_det_one_sub_smul_of_isHurwitz` — for a Hurwitz `A` and any `c > 0`, `1 - cA` is
  invertible, so backward Euler and the trapezoidal rule are uniquely solvable for every
  `h > 0`.
* `trapezoidal_schurStable_iff_isHurwitz` — when well posed, the trapezoidal recursion is Schur
  stable exactly when `A` is Hurwitz (A-stability with an exact stability region, through the
  Cayley map `μ = (1 + hlam/2)/(1 - hlam/2)`; `norm_one_add_div_one_sub_lt_one_iff`).
* The matrix statements read the eigenvalues of the three one-step matrices through the generic
  Möbius eigenvalue map `Linear.schurStable_mobius_iff` (`theorem/Linear/EigenMap.lean`): `1 + hλ`,
  `1/(1 - hλ)` and `(1 + hλ/2)/(1 - hλ/2)`.
* `backwardEuler_schurStable_of_isHurwitz` — Hurwitz implies Schur stability of backward Euler
  (one direction only: backward Euler also damps some unstable modes).
* `forwardEuler_schurStable_iff` — forward Euler is Schur stable exactly when every eigenvalue
  `λ` satisfies `‖1 + hlam‖ < 1`.
* `trapezoidal_exponentiallyStable_of_isHurwitz`,
  `backwardEuler_exponentiallyStable_of_isHurwitz` — trajectory-level geometric decay of every
  scheme trajectory.
-/

noncomputable section
namespace powerlib.Numerics
open Matrix

section Schemes

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Forward (explicit) Euler trajectory with step `h` for `ẋ = f x`. -/
def IsForwardEulerTrajectory (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  ∀ k, x (k + 1) = x k + h • f (x k)

/-- Backward (implicit) Euler trajectory with step `h` for `ẋ = f x`. -/
def IsBackwardEulerTrajectory (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  ∀ k, x (k + 1) = x k + h • f (x (k + 1))

/-- Trapezoidal-rule trajectory with step `h` for `ẋ = f x`. -/
def IsTrapezoidalTrajectory (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  ∀ k, x (k + 1) = x k + (h / 2) • (f (x k) + f (x (k + 1)))

end Schemes

variable {n : ℕ}

/-- The linear field `ẋ = A x`. -/
def linearField (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ := A *ᵥ x

def forwardEulerMatrix (h : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + h • A

def backwardEulerMatrix (h : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - h • A)⁻¹

def trapezoidalMatrix (h : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - (h / 2) • A)⁻¹ * (1 + (h / 2) • A)

section Reduction

variable (A : Matrix (Fin n) (Fin n) ℝ) (h : ℝ)

@[powerlib_foundation] private lemma one_sub_smul_mulVec (c : ℝ) (y : Fin n → ℝ) :
    (1 - c • A) *ᵥ y = y - c • (A *ᵥ y) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

@[powerlib_foundation] private lemma one_add_smul_mulVec (c : ℝ) (y : Fin n → ℝ) :
    (1 + c • A) *ᵥ y = y + c • (A *ᵥ y) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

@[powerlib_foundation] private lemma eq_inv_mulVec_iff {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsUnit P.det) (y z : Fin n → ℝ) : y = P⁻¹ *ᵥ z ↔ P *ᵥ y = z := by
  constructor
  · rintro rfl
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
  · rintro rfl
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec]

/-- Forward Euler on a linear field is the recursion with `1 + hA`. -/
@[tmio T, powerlib_foundation] theorem isForwardEulerTrajectory_iff (x : ℕ → Fin n → ℝ) :
    IsForwardEulerTrajectory (linearField A) h x ↔
      ∀ k, x (k + 1) = LTI.Model.step ⟨forwardEulerMatrix h A⟩ (x k) := by
  simp only [IsForwardEulerTrajectory, LTI.Model.step,
    forwardEulerMatrix, linearField, one_add_smul_mulVec]

/-- Backward Euler on a linear field is the recursion with `(1 - hA)⁻¹`. -/
@[powerlib_foundation] theorem isBackwardEulerTrajectory_iff (hP : IsUnit (1 - h • A).det)
    (x : ℕ → Fin n → ℝ) :
    IsBackwardEulerTrajectory (linearField A) h x ↔
      ∀ k, x (k + 1) = LTI.Model.step ⟨backwardEulerMatrix h A⟩ (x k) := by
  simp only [IsBackwardEulerTrajectory, LTI.Model.step,
    backwardEulerMatrix, linearField]
  refine forall_congr' fun k => ?_
  rw [eq_inv_mulVec_iff hP, one_sub_smul_mulVec, sub_eq_iff_eq_add]

/-- The trapezoidal rule on a linear field is the recursion with
`(1 - (h/2)A)⁻¹ (1 + (h/2)A)`. -/
@[powerlib_foundation] theorem isTrapezoidalTrajectory_iff (hP : IsUnit (1 - (h / 2) • A).det)
    (x : ℕ → Fin n → ℝ) :
    IsTrapezoidalTrajectory (linearField A) h x ↔
      ∀ k, x (k + 1) = LTI.Model.step ⟨trapezoidalMatrix h A⟩ (x k) := by
  simp only [IsTrapezoidalTrajectory, LTI.Model.step,
    trapezoidalMatrix, linearField]
  refine forall_congr' fun k => ?_
  rw [← Matrix.mulVec_mulVec, eq_inv_mulVec_iff hP, one_sub_smul_mulVec, one_add_smul_mulVec,
    smul_add, sub_eq_iff_eq_add, add_assoc]

end Reduction

section Spectral

open LinearSystems

variable {A : Matrix (Fin n) (Fin n) ℝ} {h : ℝ}

/-- Real part of the Cayley-type quotient `(w - 1)/(w + 1)`. -/
@[powerlib_foundation] theorem re_sub_one_div_add_one (w : ℂ) :
    ((w - 1) / (w + 1)).re = (Complex.normSq w - 1) / Complex.normSq (w + 1) := by
  rw [Complex.div_re]
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im, Complex.add_im,
    Complex.one_im, sub_zero, add_zero, Complex.normSq_apply]
  ring

/-- `‖1 + w‖² - ‖1 - w‖² = 4 Re w`. -/
@[powerlib_foundation] theorem normSq_one_add_sub_normSq_one_sub (w : ℂ) :
    Complex.normSq (1 + w) - Complex.normSq (1 - w) = 4 * w.re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.add_im, Complex.sub_im, Complex.one_im]
  ring

/-- The Cayley map `z ↦ (1 + z)/(1 - z)` sends the open left half plane onto the open unit disk:
for `1 - z ≠ 0`, `‖(1 + z)/(1 - z)‖ < 1` exactly when `Re z < 0`. -/
@[powerlib_foundation] theorem norm_one_add_div_one_sub_lt_one_iff {z : ℂ} (hz : 1 - z ≠ 0) :
    ‖(1 + z) / (1 - z)‖ < 1 ↔ z.re < 0 := by
  have hpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr hz
  have key := normSq_one_add_sub_normSq_one_sub z
  rw [norm_div, div_lt_one hpos, ← sq_lt_sq₀ (norm_nonneg _) hpos.le,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> linarith

/-- `1 - cA = (-c) A + 1`, the denominator of the implicit schemes in Möbius form. -/
private lemma one_sub_smul_eq (c : ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℝ) - c • A = (-c) • A + (1 : ℝ) • 1 := by
  rw [neg_smul, one_smul, neg_add_eq_sub]

/-- For a Hurwitz matrix and any `c > 0`, the implicit matrix `1 - cA = c (c⁻¹ - A)` is
invertible (`Criteria.det_smul_sub_ne_zero_of_isHurwitz`). -/
@[powerlib_foundation] theorem isUnit_det_one_sub_smul_of_isHurwitz (hA : IsHurwitz A) {c : ℝ}
    (hc : 0 < c) : IsUnit (1 - c • A).det := by
  rw [isUnit_iff_ne_zero, show 1 - c • A = c • (c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) - A) by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul], det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc.ne')
    (Criteria.det_smul_sub_ne_zero_of_isHurwitz hA (inv_nonneg.mpr hc.le))

/-- The trapezoidal matrix is the Möbius image `(1 - (h/2) A)⁻¹ (1 + (h/2) A)` of `A`. -/
private lemma trapezoidal_mobius (hP : IsUnit (1 - (h / 2) • A).det) :
    ((-(h / 2)) • A + (1 : ℝ) • 1) * trapezoidalMatrix h A = (h / 2) • A + (1 : ℝ) • 1 := by
  rw [← one_sub_smul_eq, trapezoidalMatrix, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP,
    Matrix.one_mul, one_smul, add_comm]

/-- The trapezoidal recursion is Schur stable exactly when `A` is Hurwitz (for `h > 0` and a
well-posed implicit step): the Cayley map `λ ↦ (1 + hλ/2)/(1 - hλ/2)` of the eigenvalues
(`Linear.schurStable_mobius_iff`, `norm_one_add_div_one_sub_lt_one_iff`). -/
@[powerlib_foundation] theorem trapezoidal_schurStable_iff_isHurwitz (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • A).det) :
    LTI.SchurStable (trapezoidalMatrix h A) ↔ IsHurwitz A := by
  have hQ : IsUnit ((-(h / 2)) • A + (1 : ℝ) • 1).det := by rwa [← one_sub_smul_eq]
  have hM := trapezoidal_mobius hP
  rw [Linear.schurStable_mobius_iff (by linarith) hQ hM, Linear.isHurwitz_iff_forall_eigen]
  refine forall₄_congr fun lam v hv heig => ?_
  have hz := (Linear.eigen_mobius hQ hM hv heig).1
  have e : ((h / 2 : ℝ) : ℂ) * lam + ((1 : ℝ) : ℂ) = 1 + ((h / 2 : ℝ) : ℂ) * lam := by
    push_cast; ring
  have e' : ((-(h / 2) : ℝ) : ℂ) * lam + ((1 : ℝ) : ℂ) = 1 - ((h / 2 : ℝ) : ℂ) * lam := by
    push_cast; ring
  rw [e'] at hz
  rw [e, e', norm_one_add_div_one_sub_lt_one_iff hz, Complex.re_ofReal_mul]
  constructor
  · intro h1
    by_contra h2
    exact absurd h1 (not_lt.mpr (mul_nonneg (half_pos hh).le (not_lt.mp h2)))
  · exact mul_neg_of_pos_of_neg (half_pos hh)

/-- Trapezoidal rule: Hurwitz implies Schur stability for every `h > 0`. -/
@[powerlib_foundation] theorem trapezoidal_schurStable_of_isHurwitz (hA : IsHurwitz A)
    (hh : 0 < h) : LTI.SchurStable (trapezoidalMatrix h A) :=
  (trapezoidal_schurStable_iff_isHurwitz hh
    (isUnit_det_one_sub_smul_of_isHurwitz hA (half_pos hh))).2 hA

/-- Trapezoidal rule, converse: a well-posed Schur-stable trapezoidal recursion comes from a
Hurwitz matrix.  Together with `trapezoidal_schurStable_of_isHurwitz` the trapezoidal rule
neither creates nor destroys stability of `ẋ = A x`. -/
@[powerlib_foundation] theorem isHurwitz_of_trapezoidal_schurStable (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • A).det) (hS : LTI.SchurStable (trapezoidalMatrix h A)) :
    IsHurwitz A :=
  (trapezoidal_schurStable_iff_isHurwitz hh hP).1 hS

/-- Backward Euler: Hurwitz implies Schur stability for every `h > 0` (the eigenvalues map to
`1/(1 - hλ)`, `Linear.schurStable_mobius_iff`). -/
@[powerlib_foundation] theorem backwardEuler_schurStable_of_isHurwitz (hA : IsHurwitz A)
    (hh : 0 < h) : LTI.SchurStable (backwardEulerMatrix h A) := by
  have hP := isUnit_det_one_sub_smul_of_isHurwitz hA hh
  have hM : ((-h) • A + (1 : ℝ) • 1) * backwardEulerMatrix h A = (0 : ℝ) • A + (1 : ℝ) • 1 := by
    rw [← one_sub_smul_eq, backwardEulerMatrix, Matrix.mul_nonsing_inv _ hP, zero_smul, zero_add,
      one_smul]
  rw [Linear.schurStable_mobius_iff (by simpa using hh.ne') (by rwa [← one_sub_smul_eq]) hM]
  intro lam v hv heig
  have hre := Linear.isHurwitz_iff_forall_eigen.mp hA lam v hv heig
  have h1 : 1 < (((-h : ℝ) : ℂ) * lam + ((1 : ℝ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    nlinarith
  have h2 := h1.trans_le (Complex.re_le_norm _)
  simp only [Complex.ofReal_one] at h2
  simp only [Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_one, norm_div, norm_one]
  rw [div_lt_one (by linarith)]
  exact h2

/-- Forward Euler is Schur stable exactly when every eigenvalue `λ` of `A` has
`‖1 + hλ‖ < 1` (that is, `hλ` is in the open forward-Euler disk). -/
@[powerlib_foundation] theorem forwardEuler_schurStable_iff (hh : h ≠ 0) :
    LTI.SchurStable (forwardEulerMatrix h A) ↔
      ∀ (lam : ℂ) (v : Fin n → ℂ), v ≠ 0 → A.map (algebraMap ℝ ℂ) *ᵥ v = lam • v →
        ‖1 + (h : ℂ) * lam‖ < 1 := by
  rw [Linear.schurStable_mobius_iff (A := A) (α := h) (β := 1) (γ := 0) (δ := 1)
    (by simpa using hh) (by simp) (by simp [forwardEulerMatrix, add_comm])]
  refine forall₄_congr fun lam v _ _ => ?_
  simp [add_comm]

end Spectral

section Semantic

open LinearSystems

variable {A : Matrix (Fin n) (Fin n) ℝ} {h : ℝ}

/-- Every trapezoidal trajectory of a Hurwitz linear field decays geometrically, for every
step `h > 0`. -/
@[powerlib_foundation] theorem trapezoidal_exponentiallyStable_of_isHurwitz (hA : IsHurwitz A)
    (hh : 0 < h) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsTrapezoidalTrajectory (linearField A) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hP := isUnit_det_one_sub_smul_of_isHurwitz hA (half_pos hh)
  obtain ⟨C, hC, ρ, hρ0, hρ1, hb⟩ := LTI.exponentiallyStable_of_schurStable
    (m := ⟨trapezoidalMatrix h A⟩) (trapezoidal_schurStable_of_isHurwitz hA hh)
  exact ⟨C, hC, ρ, hρ0, hρ1, fun x hx => hb x ((isTrapezoidalTrajectory_iff A h hP x).mp hx)⟩

/-- Every backward-Euler trajectory of a Hurwitz linear field decays geometrically, for every
step `h > 0`. -/
@[powerlib_foundation] theorem backwardEuler_exponentiallyStable_of_isHurwitz (hA : IsHurwitz A)
    (hh : 0 < h) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsBackwardEulerTrajectory (linearField A) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hP := isUnit_det_one_sub_smul_of_isHurwitz hA hh
  obtain ⟨C, hC, ρ, hρ0, hρ1, hb⟩ := LTI.exponentiallyStable_of_schurStable
    (m := ⟨backwardEulerMatrix h A⟩) (backwardEuler_schurStable_of_isHurwitz hA hh)
  exact ⟨C, hC, ρ, hρ0, hρ1,
    fun x hx => hb x ((isBackwardEulerTrajectory_iff A h hP x).mp hx)⟩

/-- A well-posed trapezoidal step has exactly one trajectory from each initial state. -/
@[powerlib_foundation] theorem trapezoidal_existsUnique (hP : IsUnit (1 - (h / 2) • A).det)
    (initial : Fin n → ℝ) :
    ∃! x, IsTrapezoidalTrajectory (linearField A) h x ∧ x 0 = initial := by
  refine ⟨LTI.response ⟨trapezoidalMatrix h A⟩ initial,
    ⟨(isTrapezoidalTrajectory_iff A h hP _).mpr (LTI.response_isTrajectory _ _),
      LTI.response_zero _ _⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  funext k
  rw [LTI.eq_response ((isTrapezoidalTrajectory_iff A h hP y).mp hy) k, hy0]

/-- A well-posed backward-Euler step has exactly one trajectory from each initial state. -/
@[powerlib_foundation] theorem backwardEuler_existsUnique (hP : IsUnit (1 - h • A).det)
    (initial : Fin n → ℝ) :
    ∃! x, IsBackwardEulerTrajectory (linearField A) h x ∧ x 0 = initial := by
  refine ⟨LTI.response ⟨backwardEulerMatrix h A⟩ initial,
    ⟨(isBackwardEulerTrajectory_iff A h hP _).mpr (LTI.response_isTrajectory _ _),
      LTI.response_zero _ _⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  funext k
  rw [LTI.eq_response ((isBackwardEulerTrajectory_iff A h hP y).mp hy) k, hy0]

end Semantic

end powerlib.Numerics
