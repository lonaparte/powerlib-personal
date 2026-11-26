import theorem.ParametricResonance.StableBasis
import theorem.Linear.EigenMap
import LeanForControl.LinearSystems.Stability.Continuous.ExponentialStability

/-! # Modal coordinates with a contracting stable block from the spectrum of the physical matrix

`StableBasis.stable_modal_of_eig` constructs real modal coordinates from the critical eigenvectors
and asks for the spectral radius of `e^{TA}(I − Π)` below one. Here that condition is derived
from the spectrum of `A` alone: if `jΩ` is geometrically simple and every other eigenvalue lies in
the open left half plane, the stable block `A_s` is Hurwitz and `ρ(e^{TA_s}) < 1` for every
`T > 0`.

Scope.
* `A : Matrix (Fin n) (Fin n) ℝ`, `n = m + 2`, the pair `±jΩ` (`Ω ≠ 0`) with right and left
  eigenvectors `r`, `u`, `u r = 1`; complex eigenpairs of the complexification.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (the stable remainder of the averaging step); Gelfand's
formula through `LinearSystems.spectralRadius_exp_complexification_lt_one`.

Results.
* `spectralRadius_expS_of_hurwitz` — a Hurwitz block has `ρ(e^{TA_s}) < 1`, `T > 0`.
* `stable_modal_of_hurwitz` — modal coordinates `Q A P = diag(base(0, Ω), A_s)` with
  `ρ(e^{TA_s}) < 1` from geometric simplicity of `jΩ` and the left-half-plane condition on the
  other eigenvalues.

Corrections.
None: replaces a hypothesis on `e^{TA}` by one on the eigenvalues of `A`.

Family and connection conclusions.
None: static evidence on the linear algebra of the modal decomposition.
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbit
open Complex Matrix
open BlockAveraging (expS)

/-- A Hurwitz block contracts over every positive time: `ρ(e^{T A_s}) < 1`. -/
@[tmio T, powerlib_foundation] theorem spectralRadius_expS_of_hurwitz {m : ℕ}
    {As : Matrix (Fin m) (Fin m) ℝ} (hA : LinearSystems.IsHurwitz As) {T : ℝ} (hT : 0 < T) :
    spectralRadius ℂ ((expS As T).map (algebraMap ℝ ℂ)) < 1 := by
  have h := LinearSystems.spectralRadius_exp_complexification_lt_one
    ((Linear.isHurwitz_smul_iff hT As).2 hA)
  rw [expS, MatrixAlgebra.complexification_exp]
  exact h

/-- Real modal coordinates with a contracting stable block from spectral data of the physical
matrix only: the pair `±jΩ` with eigenvectors `r`, `u` (`u r = 1`), geometric simplicity of `jΩ`
(every eigenvector is a multiple of `r`), and every other eigenvalue in the open left half plane.
-/
@[tmio T, powerlib_foundation] theorem stable_modal_of_hurwitz {n m : ℕ} (hnm : n = m + 2)
    {A : Matrix (Fin n) (Fin n) ℝ} {Ω : ℝ} (hΩ : Ω ≠ 0) {r u : Fin n → ℂ}
    (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ v : Fin n → ℂ, A.map (algebraMap ℝ ℂ) *ᵥ v = ((Ω : ℂ) * I) • v →
      v = (u ⬝ᵥ v) • r)
    (hstab : ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 → A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
      μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0) {T : ℝ} (hT : 0 < T) :
    ∃ (P : Matrix (Fin n) (Fin 2 ⊕ Fin m) ℝ) (Q : Matrix (Fin 2 ⊕ Fin m) (Fin n) ℝ)
      (As : Matrix (Fin m) (Fin m) ℝ), P * Q = 1 ∧ Q * P = 1 ∧
      Q * A * P = fromBlocks (TwoToOne.base 0 Ω) 0 0 As ∧
      BlockAveraging.physLeft Q = u ∧ BlockAveraging.physRight P = r ∧
      spectralRadius ℂ ((expS As T).map (algebraMap ℝ ℂ)) < 1 := by
  obtain ⟨W, W', hW, hWW, huW, hWr⟩ := exists_stable_basis hΩ hr hu hur (m := m)
    (by simp [hnm])
  have e : Fin n ≃ Fin 2 ⊕ Fin m := (finCongr (by omega)).trans finSumFinEquiv.symm
  obtain ⟨hQP, hPQ, hA0, hL, hR⟩ := modal_of_basis e hΩ hr hu hur hW hWW huW hWr
  refine ⟨_, _, W' * A * W, hPQ, hQP, hA0, hL, hR, spectralRadius_expS_of_hurwitz ?_ hT⟩
  intro μ w hw heq
  set v : Fin n → ℂ := W.map (algebraMap ℝ ℂ) *ᵥ w with hv
  have hAv : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v := by
    rw [hv, Matrix.mulVec_mulVec, ← Matrix.map_mul, hW, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      heq, Matrix.mulVec_smul]
  have hW'v : W'.map (algebraMap ℝ ℂ) *ᵥ v = w := by
    rw [hv, Matrix.mulVec_mulVec, ← Matrix.map_mul, hWW,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hv0 : v ≠ 0 := by
    intro h0; apply hw; rw [← hW'v, h0, Matrix.mulVec_zero]
  have huv : ∀ x : Fin m → ℂ, u ⬝ᵥ (W.map (algebraMap ℝ ℂ) *ᵥ x) = 0 := fun x => by
    rw [Matrix.dotProduct_mulVec, huW, zero_dotProduct]
  have hmu1 : μ ≠ (Ω : ℂ) * I := by
    rintro rfl
    apply hv0
    rw [hsimple v hAv, hv, huv, zero_smul]
  have hmu2 : μ ≠ -((Ω : ℂ) * I) := by
    rintro rfl
    have hstar : A.map (algebraMap ℝ ℂ) *ᵥ star v = ((Ω : ℂ) * I) • star v := by
      have h := congrArg star hAv
      rw [star_smul] at h
      have hm : star (A.map (algebraMap ℝ ℂ) *ᵥ v) = A.map (algebraMap ℝ ℂ) *ᵥ star v := by
        funext i; simp [Matrix.mulVec, dotProduct]
      rw [← hm, h]
      congr 1
      simp
    have hsv : star v = W.map (algebraMap ℝ ℂ) *ᵥ star w := by
      funext i; simp [hv, Matrix.mulVec, dotProduct]
    apply hv0
    have h0 : star v = 0 := by rw [hsimple _ hstar, hsv, huv, zero_smul]
    have := congrArg star h0
    simpa using this
  simpa using hstab μ v hv0 hAv hmu1 hmu2

end powerlib.ParametricResonance.ForcedOrbit
