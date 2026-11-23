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
* `re_neg_of_lyapunov_observable` (semidefinite dissipation and observability): if
  `P = Pᵀ ⪰ 0`, `wᵀ P (M w) ≤ 0` for every `w`, and the only real eigen-pair `(a, b)` of `M`
  (`M a = x a − y b`, `M b = y a + x b`, `x ≥ 0`) without dissipation is zero, every complex
  eigenvalue of `M` has negative real part.
* `re_neg_of_lyapunov`: if `P = Pᵀ` is positive definite and `wᵀ P (M w) < 0` for every
  `w ≠ 0`, every complex eigenvalue of `M` has negative real part (on `Fin N` this is
  `LinearSystems.IsHurwitz M`); `re_nonpos_of_lyapunov`: with `wᵀ P (M w) ≤ 0`, nonpositive
  real part.
* `dotProduct_mulVec_comm_of_symm`: `uᵀ P w = wᵀ P u` for symmetric `P`.

Used by the Lyapunov certificates of `theorem/Linear/Certificate.lean`, the spectrum of linear
port-Hamiltonian systems (`theorem/PH/PositiveReal.lean`, `theorem/PH/Observability.lean`,
`theorem/PH/Composition.lean`), the two-time-scale linear theorem
(`theorem/SingularPerturbation/Linear.lean`), the boundary-layer / frozen-fast /
finite-horizon singular-perturbation modules and the gain condition of the multi-area
load-frequency control (`theorem/PowerSystem/Frequency/LFCNetwork.lean`).

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

/-- **Semidefinite dissipation and observability.** Let `P = Pᵀ` be positive semidefinite with
`wᵀ P (M w) ≤ 0` for every `w`. If the only real pair `(a, b)` with `M a = x a − y b`,
`M b = y a + x b`, `x ≥ 0` and no dissipation (`aᵀ P M a = bᵀ P M b = 0`) is `a = b = 0`, every
complex eigenvalue of `M` has negative real part: at `Re μ ≥ 0` the Lyapunov form at the
eigenvector (`lyapunov_form_eigenpair`) forces both dissipations to vanish. -/
@[tmio T, powerlib_foundation] theorem re_neg_of_lyapunov_observable (hPsymm : Pᵀ = P)
    (hPnn : ∀ w : ι → ℝ, 0 ≤ w ⬝ᵥ (P *ᵥ w)) (hdiss : ∀ w : ι → ℝ, w ⬝ᵥ (P *ᵥ (M *ᵥ w)) ≤ 0)
    (hobs : ∀ (x y : ℝ) (a b : ι → ℝ), M *ᵥ a = x • a - y • b → M *ᵥ b = y • a + x • b →
      0 ≤ x → a ⬝ᵥ (P *ᵥ (M *ᵥ a)) = 0 → b ⬝ᵥ (P *ᵥ (M *ᵥ b)) = 0 → a = 0 ∧ b = 0)
    {μ : ℂ} {v : ι → ℂ} (hv : v ≠ 0) (heig : M.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ.re < 0 := by
  by_contra hμ
  push Not at hμ
  obtain ⟨hMa, hMb⟩ := mulVec_re_im_of_eigenpair heig
  have hform := lyapunov_form_eigenpair hPsymm heig
  have ha := hdiss fun i => (v i).re
  have hb := hdiss fun i => (v i).im
  have hS := mul_nonneg hμ (add_nonneg (hPnn fun i => (v i).re) (hPnn fun i => (v i).im))
  obtain ⟨h1, h2⟩ := hobs _ _ _ _ hMa hMb hμ (by linarith) (by linarith)
  rcases re_ne_zero_or_im_ne_zero hv with h | h
  · exact h h1
  · exact h h2

/-- If `P = Pᵀ` is positive definite and `wᵀ P (M w) < 0` for all `w ≠ 0`, every complex
eigenvalue of `M` has negative real part (`re_neg_of_lyapunov_observable`: a pair without
dissipation is zero). -/
@[tmio T, powerlib_foundation] theorem re_neg_of_lyapunov
    (hPsymm : Pᵀ = P) (hPpos : ∀ w : ι → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (P *ᵥ w))
    (hdiss : ∀ w : ι → ℝ, w ≠ 0 → w ⬝ᵥ (P *ᵥ (M *ᵥ w)) < 0)
    {μ : ℂ} {v : ι → ℂ} (hv : v ≠ 0) (heig : M.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ.re < 0 := by
  have hle : ∀ w, w ⬝ᵥ (P *ᵥ (M *ᵥ w)) ≤ 0 := fun w => by
    by_cases hw : w = 0
    · simp [hw]
    · exact (hdiss w hw).le
  have hge : ∀ w, 0 ≤ w ⬝ᵥ (P *ᵥ w) := fun w => by
    by_cases hw : w = 0
    · simp [hw]
    · exact (hPpos w hw).le
  exact re_neg_of_lyapunov_observable hPsymm hge hle (fun _ _ a b _ _ _ ha hb =>
    ⟨by_contra fun h => (hdiss a h).ne ha, by_contra fun h => (hdiss b h).ne hb⟩) hv heig

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

end powerlib.Criteria
