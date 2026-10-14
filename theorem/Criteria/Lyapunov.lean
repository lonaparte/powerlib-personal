import theorem.Attributes
import dependencies.LeanForControl

/-! # Lyapunov-inequality criterion for the spectrum (foundation)

Static linear algebra of one real square matrix `M`; nothing here describes a physical system.

* `re_neg_of_lyapunov`: if `P = Pᵀ` is positive definite and `wᵀ P (M w) < 0` for every
  `w ≠ 0`, every complex eigenvalue of `M` has negative real part (the real and imaginary parts
  of a complex eigenvector both satisfy the strict inequality, and their sum gives
  `Re μ · (aᵀPa + bᵀPb) < 0`).
* `isHurwitz_of_lyapunov`: the same criterion stated for `LinearSystems.IsHurwitz` on
  `Fin N`.
* `dotProduct_mulVec_comm_of_symm`: `uᵀ P w = wᵀ P u` for symmetric `P`.

Used by the two-time-scale linear theorem (`theorem/SingularPerturbation/Linear.lean`) and the
boundary-layer / frozen-fast / finite-horizon singular-perturbation modules.

Source: the standard Lyapunov-inequality argument, used by the composite Lyapunov proof of
work-sync theory/T-singular-perturbation.md §1.1–§1.4.
-/

noncomputable section
namespace powerlib.Criteria
open Matrix

@[powerlib_foundation] theorem dotProduct_mulVec_comm_of_symm {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} (hP : Pᵀ = P) (u w : ι → ℝ) :
    u ⬝ᵥ (P *ᵥ w) = w ⬝ᵥ (P *ᵥ u) := by
  rw [dotProduct_mulVec, ← hP, vecMul_transpose, hP, dotProduct_comm]

/-- If `P = Pᵀ` is positive definite and `wᵀ P (M w) < 0` for all `w ≠ 0`, every complex
eigenvalue of `M` has negative real part. -/
@[powerlib_foundation] theorem re_neg_of_lyapunov {ι : Type*} [Fintype ι] {M P : Matrix ι ι ℝ}
    (hPsymm : Pᵀ = P) (hPpos : ∀ w : ι → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (P *ᵥ w))
    (hdiss : ∀ w : ι → ℝ, w ≠ 0 → w ⬝ᵥ (P *ᵥ (M *ᵥ w)) < 0)
    {μ : ℂ} {v : ι → ℂ} (hv : v ≠ 0) (heig : M.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ.re < 0 := by
  set a : ι → ℝ := fun i => (v i).re with ha_def
  set b : ι → ℝ := fun i => (v i).im with hb_def
  have hcomp : ∀ i, (M.map (algebraMap ℝ ℂ) *ᵥ v) i = ((M *ᵥ a) i : ℂ) + ((M *ᵥ b) i : ℂ) * Complex.I := by
    intro i
    simp only [mulVec, dotProduct, Matrix.map_apply, Complex.coe_algebraMap, a, b]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← Complex.re_add_im (v j)]
    ring
  have hMa : M *ᵥ a = μ.re • a - μ.im • b := by
    ext i
    have h := congrArg Complex.re ((hcomp i).symm.trans (congrFun heig i))
    simp [a, b, Complex.mul_re] at h ⊢
    linarith
  have hMb : M *ᵥ b = μ.re • b + μ.im • a := by
    ext i
    have h := congrArg Complex.im ((hcomp i).symm.trans (congrFun heig i))
    simp [a, b, Complex.mul_im] at h ⊢
    linarith
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    apply Complex.ext
    · simpa [a] using congrFun h.1 i
    · simpa [b] using congrFun h.2 i
  have hsum : a ⬝ᵥ (P *ᵥ (M *ᵥ a)) + b ⬝ᵥ (P *ᵥ (M *ᵥ b)) =
      μ.re * (a ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ b)) := by
    rw [hMa, hMb]
    simp only [mulVec_sub, mulVec_add, mulVec_smul, dotProduct_sub, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    rw [dotProduct_mulVec_comm_of_symm hPsymm a b]
    ring
  have hle : ∀ w, w ⬝ᵥ (P *ᵥ (M *ᵥ w)) ≤ 0 := fun w => by
    by_cases hw : w = 0
    · simp [hw]
    · exact (hdiss w hw).le
  have hge : ∀ w, 0 ≤ w ⬝ᵥ (P *ᵥ w) := fun w => by
    by_cases hw : w = 0
    · simp [hw]
    · exact (hPpos w hw).le
  by_contra hμ
  push Not at hμ
  rcases hab with ha | hb
  · have h1 := hdiss a ha
    have h2 := hle b
    have h3 := hPpos a ha
    have h4 := hge b
    nlinarith
  · have h1 := hdiss b hb
    have h2 := hle a
    have h3 := hPpos b hb
    have h4 := hge a
    nlinarith

/-- Lyapunov-inequality criterion for `LinearSystems.IsHurwitz`. -/
@[powerlib_foundation] theorem isHurwitz_of_lyapunov {N : ℕ} {M P : Matrix (Fin N) (Fin N) ℝ}
    (hPsymm : Pᵀ = P) (hPpos : ∀ w : Fin N → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (P *ᵥ w))
    (hdiss : ∀ w : Fin N → ℝ, w ≠ 0 → w ⬝ᵥ (P *ᵥ (M *ᵥ w)) < 0) :
    LinearSystems.IsHurwitz M := by
  intro μ v hv heig
  simpa using re_neg_of_lyapunov hPsymm hPpos hdiss hv heig

end powerlib.Criteria
