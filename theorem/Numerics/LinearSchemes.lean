import theorem.LTI.Discrete
import theorem.Linear.EigenMap
import theorem.Criteria.Hurwitz

/-! # One-step schemes for an autonomous field and their linear-field reduction

One-step time-integration schemes for an autonomous vector field, their exact reduction to
discrete LTI recursions when the field is linear, and the stability of those recursions.

Model boundary.
* The continuous model is an autonomous field `f : E → E` (`ẋ = f x`), with a fixed step `h`.
  For the linear results `E = Fin n → ℝ` and `f = linearField A`, i.e. `ẋ = A x`; constant
  inputs are read in deviation coordinates (`trajectory_sub_const_iff`,
  `affineField_shift_eq_linearField`).
* Schemes are trajectory predicates written directly from the update rule: forward Euler
  `x_{k+1} = x_k + h f(x_k)` and the θ-method `x_{k+1} = x_k + h((1 − θ) f(x_k) + θ f(x_{k+1}))`
  (`IsThetaTrajectory`), whose cases backward Euler (`θ = 1`) and trapezoidal rule (`θ = ½`) are
  abbreviations. No step-size control, no Newton iteration error: the implicit equation is
  assumed solved exactly.
* For a linear field the predicates are proved equivalent to the discrete recursions with
  matrices `1 + hA` and `(1 − θhA)⁻¹ (1 + (1 − θ)hA)` (`thetaMatrix`; whenever the implicit
  matrix is invertible).
* Stability statements are about the discretized recursion, not the continuous system.

Source: work-sync theory/T-numerical-integration.md §1.2, §1.3, §1.7, §2.7;
theory/T-emt-simulation.md §1.3–§1.5 (trapezoidal discretization).

Results.
* `isThetaTrajectory_iff`, `isForwardEulerTrajectory_iff` — the linear reductions;
  `theta_existsUnique` — a well-posed θ-step has exactly one trajectory from each initial state.
* `isUnit_det_one_sub_smul_of_isHurwitz` — for a Hurwitz `A` and any `c > 0`, `1 - cA` is
  invertible, so every θ-method with `θ > 0` is uniquely solvable for every `h > 0`.
* `trapezoidal_schurStable_iff_isHurwitz` — when well posed, the trapezoidal recursion is Schur
  stable exactly when `A` is Hurwitz (A-stability with an exact stability region, through the
  Cayley map `μ = (1 + hlam/2)/(1 - hlam/2)`; `norm_one_add_div_one_sub_lt_one_iff`).
* The matrix statements read the eigenvalues of the one-step matrices through the generic
  Möbius eigenvalue map `Linear.schurStable_mobius_iff` (`theorem/Linear/EigenMap.lean`): `1 + hλ`
  and `(1 + (1 − θ)hλ)/(1 − θhλ)`.
* `theta_schurStable_of_isHurwitz` — for `θ ≥ ½` (backward Euler, trapezoidal rule) Hurwitz
  implies Schur stability for every `h > 0` (one direction only: backward Euler also damps some
  unstable modes).
* `forwardEuler_schurStable_iff` — forward Euler is Schur stable exactly when every eigenvalue
  `λ` satisfies `‖1 + hlam‖ < 1`.
* `trajectory_sub_const_iff`, `affineField_shift_eq_linearField` — the schemes commute with a
  constant shift of the state; for a constant input `b` about an equilibrium `A x_e + b = 0`
  the affine schemes are the linear schemes in the deviation `x − x_e`.
* `theta_exponentiallyStable_of_isHurwitz` — trajectory-level geometric decay of every θ-method
  trajectory (`θ ≥ ½`).
-/

noncomputable section
namespace powerlib.Numerics
open Matrix

section Schemes

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Forward (explicit) Euler trajectory with step `h` for `ẋ = f x`. -/
def IsForwardEulerTrajectory (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  ∀ k, x (k + 1) = x k + h • f (x k)

/-- θ-method trajectory with step `h` for `ẋ = f x`:
`x_{k+1} = x_k + h ((1 − θ) f(x_k) + θ f(x_{k+1}))`. -/
def IsThetaTrajectory (θ : ℝ) (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  ∀ k, x (k + 1) = x k + h • ((1 - θ) • f (x k) + θ • f (x (k + 1)))

/-- Backward (implicit) Euler trajectory with step `h` for `ẋ = f x`: the θ-method, `θ = 1`. -/
abbrev IsBackwardEulerTrajectory (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  IsThetaTrajectory 1 f h x

/-- Trapezoidal-rule trajectory with step `h` for `ẋ = f x`: the θ-method, `θ = ½`. -/
abbrev IsTrapezoidalTrajectory (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  IsThetaTrajectory (1 / 2) f h x

/-- **Deviation coordinates.** The schemes commute with a constant shift of the state: `x` is a
trajectory of `f` iff `x − x_e` is a trajectory of the shifted field `z ↦ f (z + x_e)`
(forward Euler and every θ-method). -/
@[tmio T, powerlib_foundation] theorem trajectory_sub_const_iff (f : E → E) (h : ℝ) (xe : E)
    (x : ℕ → E) :
    (IsForwardEulerTrajectory f h x ↔
        IsForwardEulerTrajectory (fun z => f (z + xe)) h fun k => x k - xe) ∧
      ∀ θ : ℝ, (IsThetaTrajectory θ f h x ↔
        IsThetaTrajectory θ (fun z => f (z + xe)) h fun k => x k - xe) := by
  have key : ∀ a b d : E, a - xe = b - xe + d ↔ a = b + d := fun a b d => by
    rw [sub_add_eq_add_sub, sub_left_inj]
  refine ⟨?_, fun θ => ?_⟩ <;>
    exact forall_congr' fun k => by simp only [sub_add_cancel, key]

end Schemes

variable {n : ℕ}

/-- The linear field `ẋ = A x`. -/
def linearField (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ := A *ᵥ x

def forwardEulerMatrix (h : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + h • A

/-- The θ-method step matrix `(1 − θhA)⁻¹ (1 + (1 − θ)hA)`. -/
def thetaMatrix (θ h : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - (θ * h) • A)⁻¹ * (1 + ((1 - θ) * h) • A)

/-- Backward-Euler step matrix: `θ = 1`, i.e. `(1 − hA)⁻¹`. -/
abbrev backwardEulerMatrix (h : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  thetaMatrix 1 h A

/-- Trapezoidal step matrix: `θ = ½`, i.e. `(1 − (h/2)A)⁻¹ (1 + (h/2)A)`. -/
abbrev trapezoidalMatrix (h : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  thetaMatrix (1 / 2) h A

/-- **Constant input about an equilibrium.** If `A x_e + b = 0`, the shifted affine field
`z ↦ A (z + x_e) + b` is `linearField A`; with `trajectory_sub_const_iff`, every scheme for
`ẋ = A x + b` is the linear scheme for `ẋ = A x` in the deviation `x − x_e`. -/
@[tmio T, powerlib_foundation] theorem affineField_shift_eq_linearField
    {A : Matrix (Fin n) (Fin n) ℝ} {b xe : Fin n → ℝ} (he : A *ᵥ xe + b = 0) :
    (fun z => A *ᵥ (z + xe) + b) = linearField A := by
  funext z
  rw [mulVec_add, add_assoc, he, add_zero, linearField]

section Reduction

variable (A : Matrix (Fin n) (Fin n) ℝ) (h : ℝ)

@[tmio T, powerlib_foundation] private lemma one_sub_smul_mulVec (c : ℝ) (y : Fin n → ℝ) :
    (1 - c • A) *ᵥ y = y - c • (A *ᵥ y) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

@[tmio T, powerlib_foundation] private lemma one_add_smul_mulVec (c : ℝ) (y : Fin n → ℝ) :
    (1 + c • A) *ᵥ y = y + c • (A *ᵥ y) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

@[tmio T, powerlib_foundation] private lemma eq_inv_mulVec_iff {P : Matrix (Fin n) (Fin n) ℝ}
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

/-- The θ-method on a linear field is the recursion with `(1 − θhA)⁻¹ (1 + (1 − θ)hA)`, whenever
the implicit matrix `1 − θhA` is invertible. -/
@[tmio T, powerlib_foundation] theorem isThetaTrajectory_iff {θ : ℝ}
    (hP : IsUnit (1 - (θ * h) • A).det) (x : ℕ → Fin n → ℝ) :
    IsThetaTrajectory θ (linearField A) h x ↔
      ∀ k, x (k + 1) = LTI.Model.step ⟨thetaMatrix θ h A⟩ (x k) := by
  simp only [IsThetaTrajectory, LTI.Model.step, thetaMatrix, linearField]
  refine forall_congr' fun k => ?_
  rw [← Matrix.mulVec_mulVec, eq_inv_mulVec_iff hP, one_sub_smul_mulVec, one_add_smul_mulVec,
    sub_eq_iff_eq_add, smul_add, smul_smul, smul_smul, mul_comm h, mul_comm h θ, add_assoc]

end Reduction

section Spectral

open LinearSystems

variable {A : Matrix (Fin n) (Fin n) ℝ} {h : ℝ}

/-- `‖1 + w‖² - ‖1 - w‖² = 4 Re w`. -/
@[tmio T, powerlib_foundation] theorem normSq_one_add_sub_normSq_one_sub (w : ℂ) :
    Complex.normSq (1 + w) - Complex.normSq (1 - w) = 4 * w.re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.add_im, Complex.sub_im, Complex.one_im]
  ring

/-- The Cayley map `z ↦ (1 + z)/(1 - z)` sends the open left half plane onto the open unit disk:
for `1 - z ≠ 0`, `‖(1 + z)/(1 - z)‖ < 1` exactly when `Re z < 0`. -/
@[tmio T, powerlib_foundation] theorem norm_one_add_div_one_sub_lt_one_iff {z : ℂ} (hz : 1 - z ≠ 0) :
    ‖(1 + z) / (1 - z)‖ < 1 ↔ z.re < 0 := by
  have hpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr hz
  have key := normSq_one_add_sub_normSq_one_sub z
  rw [norm_div, div_lt_one hpos, ← sq_lt_sq₀ (norm_nonneg _) hpos.le,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> linarith

/-- `1 - cA = (-c) A + 1`, the denominator of the implicit schemes in Möbius form. -/
@[tmio T, powerlib_foundation] private lemma one_sub_smul_eq (c : ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℝ) - c • A = (-c) • A + (1 : ℝ) • 1 := by
  rw [neg_smul, one_smul, neg_add_eq_sub]

/-- For a Hurwitz matrix and any `c > 0`, the implicit matrix `1 - cA = c (c⁻¹ - A)` is
invertible (`Criteria.det_smul_sub_ne_zero_of_isHurwitz`). -/
@[tmio T, powerlib_foundation] theorem isUnit_det_one_sub_smul_of_isHurwitz (hA : IsHurwitz A) {c : ℝ}
    (hc : 0 < c) : IsUnit (1 - c • A).det := by
  rw [isUnit_iff_ne_zero, show 1 - c • A = c • (c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) - A) by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul], det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc.ne')
    (Criteria.det_smul_sub_ne_zero_of_isHurwitz hA (inv_nonneg.mpr hc.le))

/-- The θ-method matrix is the Möbius image `(1 − θhA)⁻¹ (1 + (1 − θ)hA)` of `A`. -/
@[tmio T, powerlib_foundation] private lemma theta_mobius {θ : ℝ}
    (hP : IsUnit (1 - (θ * h) • A).det) :
    ((-(θ * h)) • A + (1 : ℝ) • 1) * thetaMatrix θ h A = ((1 - θ) * h) • A + (1 : ℝ) • 1 := by
  rw [← one_sub_smul_eq, thetaMatrix, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP,
    Matrix.one_mul, one_smul, add_comm]

/-- The trapezoidal recursion is Schur stable exactly when `A` is Hurwitz (for `h > 0` and a
well-posed implicit step): the Cayley map `λ ↦ (1 + hλ/2)/(1 - hλ/2)` of the eigenvalues
(`Linear.schurStable_mobius_iff`, `norm_one_add_div_one_sub_lt_one_iff`). -/
@[tmio T, powerlib_foundation] theorem trapezoidal_schurStable_iff_isHurwitz (hh : 0 < h)
    (hP : IsUnit (1 - (1 / 2 * h) • A).det) :
    LTI.SchurStable (trapezoidalMatrix h A) ↔ IsHurwitz A := by
  have hQ : IsUnit ((-(1 / 2 * h)) • A + (1 : ℝ) • 1).det := by rwa [← one_sub_smul_eq]
  have hM := theta_mobius hP
  rw [Linear.schurStable_mobius_iff (by linarith) hQ hM, Linear.isHurwitz_iff_forall_eigen]
  refine forall₄_congr fun lam v hv heig => ?_
  have hz := Linear.eigen_mobius_denom_ne_zero hQ hv heig
  have e : (((1 - 1 / 2) * h : ℝ) : ℂ) * lam + ((1 : ℝ) : ℂ) = 1 + ((h / 2 : ℝ) : ℂ) * lam := by
    push_cast; ring
  have e' : ((-(1 / 2 * h) : ℝ) : ℂ) * lam + ((1 : ℝ) : ℂ) = 1 - ((h / 2 : ℝ) : ℂ) * lam := by
    push_cast; ring
  rw [e'] at hz
  rw [e, e', norm_one_add_div_one_sub_lt_one_iff hz, Complex.re_ofReal_mul]
  constructor
  · intro h1
    by_contra h2
    exact absurd h1 (not_lt.mpr (mul_nonneg (half_pos hh).le (not_lt.mp h2)))
  · exact mul_neg_of_pos_of_neg (half_pos hh)

/-- θ-method with `θ ≥ ½` (backward Euler `θ = 1`, trapezoidal rule `θ = ½`): Hurwitz implies
Schur stability for every `h > 0`. The eigenvalues map to `(1 + (1 − θ)hλ)/(1 − θhλ)`
(`Linear.schurStable_mobius_iff`), and `|1 − θz|² − |1 + (1 − θ)z|² = −2h Re λ + (2θ − 1)|z|²`
for `z = hλ`. -/
@[tmio T, powerlib_foundation] theorem theta_schurStable_of_isHurwitz {θ : ℝ} (hA : IsHurwitz A)
    (hθ : 1 / 2 ≤ θ) (hh : 0 < h) : LTI.SchurStable (thetaMatrix θ h A) := by
  have hP := isUnit_det_one_sub_smul_of_isHurwitz hA (c := θ * h) (mul_pos (by linarith) hh)
  have hQ : IsUnit ((-(θ * h)) • A + (1 : ℝ) • 1).det := by rwa [← one_sub_smul_eq]
  rw [Linear.schurStable_mobius_iff (by nlinarith) hQ (theta_mobius hP)]
  intro lam v hv heig
  have hre := Linear.isHurwitz_iff_forall_eigen.mp hA lam v hv heig
  have hz := Linear.eigen_mobius_denom_ne_zero hQ hv heig
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hz), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_one, Complex.one_re,
    Complex.one_im]
  nlinarith [mul_pos hh (neg_pos.mpr hre), mul_nonneg (mul_nonneg (sq_nonneg h)
    (by linarith : (0 : ℝ) ≤ 2 * θ - 1)) (add_nonneg (sq_nonneg lam.re) (sq_nonneg lam.im))]

/-- Forward Euler is Schur stable exactly when every eigenvalue `λ` of `A` has
`‖1 + hλ‖ < 1` (that is, `hλ` is in the open forward-Euler disk). -/
@[tmio T, powerlib_foundation] theorem forwardEuler_schurStable_iff (hh : h ≠ 0) :
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

/-- Every θ-method trajectory (`θ ≥ ½`) of a Hurwitz linear field decays geometrically, for
every step `h > 0`. -/
@[tmio T, powerlib_foundation] theorem theta_exponentiallyStable_of_isHurwitz {θ : ℝ}
    (hA : IsHurwitz A) (hθ : 1 / 2 ≤ θ) (hh : 0 < h) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsThetaTrajectory θ (linearField A) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hP := isUnit_det_one_sub_smul_of_isHurwitz hA (c := θ * h) (mul_pos (by linarith) hh)
  obtain ⟨C, hC, ρ, hρ0, hρ1, hb⟩ := LTI.exponentiallyStable_of_schurStable
    (m := ⟨thetaMatrix θ h A⟩) (theta_schurStable_of_isHurwitz hA hθ hh)
  exact ⟨C, hC, ρ, hρ0, hρ1, fun x hx => hb x ((isThetaTrajectory_iff A h hP x).mp hx)⟩

/-- A well-posed θ-method step has exactly one trajectory from each initial state. -/
@[tmio T, powerlib_foundation] theorem theta_existsUnique {θ : ℝ}
    (hP : IsUnit (1 - (θ * h) • A).det) (initial : Fin n → ℝ) :
    ∃! x, IsThetaTrajectory θ (linearField A) h x ∧ x 0 = initial := by
  refine ⟨LTI.response ⟨thetaMatrix θ h A⟩ initial,
    ⟨(isThetaTrajectory_iff A h hP _).mpr (LTI.response_isTrajectory _ _),
      LTI.response_zero _ _⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  funext k
  rw [LTI.eq_response ((isThetaTrajectory_iff A h hP y).mp hy) k, hy0]

end Semantic

end powerlib.Numerics
