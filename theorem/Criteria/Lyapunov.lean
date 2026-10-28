import theorem.Attributes
import dependencies.LeanForControl

/-! # Lyapunov-inequality criterion for the spectrum (foundation)

A Lyapunov inequality `wᵀ P (M w) < 0` (or `≤ 0`) with `P` positive definite places the spectrum
of `M` in the open (or closed) left half plane. Every such argument in the library reads the
quadratic form at the real and imaginary parts of one complex eigenvector.

Scope.
* Static linear algebra of one real square matrix `M` on any finite index type; nothing here
  describes a physical system and no model family is defined.

Source: the standard Lyapunov-inequality argument, used by the composite Lyapunov proof of
work-sync theory/T-singular-perturbation.md §1.1–§1.4.

Results.
* `mulVec_re_im_of_eigenpair`: a complex eigenpair `(μ, a + i b)` of a real `M` gives
  `M a = Re μ • a - Im μ • b` and `M b = Im μ • a + Re μ • b`.
* `lyapunov_form_eigenpair` (the Lyapunov form at an eigenvector): for symmetric `P`,
  `aᵀ P M a + bᵀ P M b = Re μ · (aᵀ P a + bᵀ P b)`.
* `re_neg_of_lyapunov`: if `P = Pᵀ` is positive definite and `wᵀ P (M w) < 0` for every
  `w ≠ 0`, every complex eigenvalue of `M` has negative real part; `re_nonpos_of_lyapunov`: with
  `wᵀ P (M w) ≤ 0`, nonpositive real part.
* `isHurwitz_of_lyapunov`: the strict criterion stated for `LinearSystems.IsHurwitz` on
  `Fin N`.
* `dotProduct_mulVec_comm_of_symm`: `uᵀ P w = wᵀ P u` for symmetric `P`.

Used by the Lyapunov certificates of `theorem/Linear/Certificate.lean`, the spectrum of linear
port-Hamiltonian systems (`theorem/PH/PositiveReal.lean`, `theorem/PH/Observability.lean`,
`theorem/PH/Composition.lean`), the two-time-scale linear theorem
(`theorem/SingularPerturbation/Linear.lean`) and the boundary-layer / frozen-fast /
finite-horizon singular-perturbation modules.

Family and connection conclusions.
* None: static linear algebra.
-/

noncomputable section
namespace powerlib.Criteria
open Matrix

@[tmio T, powerlib_foundation] theorem dotProduct_mulVec_comm_of_symm {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} (hP : Pᵀ = P) (u w : ι → ℝ) :
    u ⬝ᵥ (P *ᵥ w) = w ⬝ᵥ (P *ᵥ u) := by
  rw [dotProduct_mulVec, ← hP, vecMul_transpose, hP, dotProduct_comm]

section Eigen

variable {ι : Type*} [Fintype ι] {M P : Matrix ι ι ℝ}

/-- Real and imaginary parts of a complex eigenpair `(μ, a + i b)` of a real matrix:
`M a = Re μ • a - Im μ • b` and `M b = Im μ • a + Re μ • b`. -/
@[tmio T, powerlib_foundation] theorem mulVec_re_im_of_eigenpair {μ : ℂ} {v : ι → ℂ}
    (heig : M.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    M *ᵥ (fun i => (v i).re) = μ.re • (fun i => (v i).re) - μ.im • (fun i => (v i).im) ∧
      M *ᵥ (fun i => (v i).im) = μ.im • (fun i => (v i).re) + μ.re • (fun i => (v i).im) := by
  constructor <;> ext i
  · have h := congrArg Complex.re (congrFun heig i)
    simp only [mulVec, dotProduct, Matrix.map_apply, Complex.coe_algebraMap, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Pi.smul_apply,
      smul_eq_mul] at h ⊢
    simpa using h
  · have h := congrArg Complex.im (congrFun heig i)
    simp only [mulVec, dotProduct, Matrix.map_apply, Complex.coe_algebraMap, Complex.im_sum,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Pi.smul_apply,
      smul_eq_mul] at h ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith

/-- **The Lyapunov form at a complex eigenvector.** For symmetric `P` and a complex eigenpair
`(μ, a + i b)` of the real matrix `M`: `aᵀ P M a + bᵀ P M b = Re μ · (aᵀ P a + bᵀ P b)`. -/
@[tmio T, powerlib_foundation] theorem lyapunov_form_eigenpair (hP : Pᵀ = P) {μ : ℂ} {v : ι → ℂ}
    (heig : M.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (fun i => (v i).re) ⬝ᵥ (P *ᵥ (M *ᵥ fun i => (v i).re)) +
        (fun i => (v i).im) ⬝ᵥ (P *ᵥ (M *ᵥ fun i => (v i).im)) =
      μ.re * ((fun i => (v i).re) ⬝ᵥ (P *ᵥ fun i => (v i).re) +
        (fun i => (v i).im) ⬝ᵥ (P *ᵥ fun i => (v i).im)) := by
  obtain ⟨hMa, hMb⟩ := mulVec_re_im_of_eigenpair heig
  rw [hMa, hMb]
  simp only [mulVec_sub, mulVec_add, mulVec_smul, dotProduct_sub, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  rw [dotProduct_mulVec_comm_of_symm hP (fun i => (v i).re) (fun i => (v i).im)]
  ring

/-- A nonzero complex vector has a nonzero real or imaginary part. -/
@[tmio T, powerlib_foundation] private theorem re_ne_zero_or_im_ne_zero {v : ι → ℂ} (hv : v ≠ 0) :
    (fun i => (v i).re) ≠ 0 ∨ (fun i => (v i).im) ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (funext fun i => Complex.ext (congrFun h.1 i) (congrFun h.2 i))

/-- The energy `aᵀ P a + bᵀ P b` of a nonzero complex vector under a positive definite `P`. -/
@[tmio T, powerlib_foundation] private theorem form_re_im_pos
    (hPpos : ∀ w : ι → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (P *ᵥ w)) {v : ι → ℂ} (hv : v ≠ 0) :
    0 < (fun i => (v i).re) ⬝ᵥ (P *ᵥ fun i => (v i).re) +
      (fun i => (v i).im) ⬝ᵥ (P *ᵥ fun i => (v i).im) := by
  have hge : ∀ w : ι → ℝ, 0 ≤ w ⬝ᵥ (P *ᵥ w) := fun w => by
    by_cases hw : w = 0
    · simp [hw]
    · exact (hPpos w hw).le
  rcases re_ne_zero_or_im_ne_zero hv with h | h
  · linarith [hPpos _ h, hge fun i => (v i).im]
  · linarith [hPpos _ h, hge fun i => (v i).re]

/-- If `P = Pᵀ` is positive definite and `wᵀ P (M w) < 0` for all `w ≠ 0`, every complex
eigenvalue of `M` has negative real part. -/
@[tmio T, powerlib_foundation] theorem re_neg_of_lyapunov
    (hPsymm : Pᵀ = P) (hPpos : ∀ w : ι → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (P *ᵥ w))
    (hdiss : ∀ w : ι → ℝ, w ≠ 0 → w ⬝ᵥ (P *ᵥ (M *ᵥ w)) < 0)
    {μ : ℂ} {v : ι → ℂ} (hv : v ≠ 0) (heig : M.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ.re < 0 := by
  have hle : ∀ w, w ⬝ᵥ (P *ᵥ (M *ᵥ w)) ≤ 0 := fun w => by
    by_cases hw : w = 0
    · simp [hw]
    · exact (hdiss w hw).le
  have hform := lyapunov_form_eigenpair hPsymm heig
  have hS := form_re_im_pos hPpos hv
  have hneg : μ.re * ((fun i => (v i).re) ⬝ᵥ (P *ᵥ fun i => (v i).re) +
      (fun i => (v i).im) ⬝ᵥ (P *ᵥ fun i => (v i).im)) < 0 := by
    rw [← hform]
    rcases re_ne_zero_or_im_ne_zero hv with h | h
    · linarith [hdiss _ h, hle fun i => (v i).im]
    · linarith [hdiss _ h, hle fun i => (v i).re]
  by_contra hμ
  push Not at hμ
  linarith [mul_nonneg hμ hS.le]

/-- Closed half plane: if `P = Pᵀ` is positive definite and `wᵀ P (M w) ≤ 0` for all `w`, every
complex eigenvalue of `M` has nonpositive real part. -/
@[tmio T, powerlib_foundation] theorem re_nonpos_of_lyapunov
    (hPsymm : Pᵀ = P) (hPpos : ∀ w : ι → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (P *ᵥ w))
    (hdiss : ∀ w : ι → ℝ, w ⬝ᵥ (P *ᵥ (M *ᵥ w)) ≤ 0)
    {μ : ℂ} {v : ι → ℂ} (hv : v ≠ 0) (heig : M.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ.re ≤ 0 := by
  have hform := lyapunov_form_eigenpair hPsymm heig
  have hS := form_re_im_pos hPpos hv
  have hle : μ.re * ((fun i => (v i).re) ⬝ᵥ (P *ᵥ fun i => (v i).re) +
      (fun i => (v i).im) ⬝ᵥ (P *ᵥ fun i => (v i).im)) ≤ 0 := by
    rw [← hform]
    linarith [hdiss fun i => (v i).re, hdiss fun i => (v i).im]
  by_contra hμ
  push Not at hμ
  linarith [mul_pos hμ hS]

end Eigen

/-- Lyapunov-inequality criterion for `LinearSystems.IsHurwitz`. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_of_lyapunov {N : ℕ} {M P : Matrix (Fin N) (Fin N) ℝ}
    (hPsymm : Pᵀ = P) (hPpos : ∀ w : Fin N → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (P *ᵥ w))
    (hdiss : ∀ w : Fin N → ℝ, w ≠ 0 → w ⬝ᵥ (P *ᵥ (M *ᵥ w)) < 0) :
    LinearSystems.IsHurwitz M := by
  intro μ v hv heig
  simpa using re_neg_of_lyapunov hPsymm hPpos hdiss hv heig

end powerlib.Criteria
