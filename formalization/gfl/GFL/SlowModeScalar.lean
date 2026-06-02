/-
  Theorem B, full system — the slow-mode equation reframed as a SCALAR root problem (path C).

  Reviewer's observation (correct): locating the slow eigenvalue λ_slow ≈ −b of the full 9×9 J_S
  does NOT require matrix perturbation theory (Bauer–Fike / Kato) or complex Rouché.  By the Schur
  determinant identity (`variantS_schur_det`), for μ ∉ spec(A),

      det(J_S − μ·I) = det(A − μ·I) · h(μ),   h(μ) := (j99 − μ) − ρᵀ(A − μ·I)⁻¹ c,

  so μ is an eigenvalue of J_S iff the SCALAR function h vanishes.  This file machine-checks the
  backbone of the scalar route (all pure linear algebra, no `sorry`):

    * `slowModeH`               : the scalar slow-mode function h.
    * `slowMode_det_factor`     : det(J_S − μI) = det(A − μI)·h(μ)  (Schur identity, renamed).
    * `slowMode_det_zero_iff`   : for μ ∉ spec(A),  det(J_S − μI) = 0 ↔ h(μ) = 0.
    * `eigenvalue_of_slowMode_zero` : h(μ) = 0  ⟹  μ is a genuine eigenvalue of J_S
                                      (∃ nonzero v, J_S·v = μ•v) — the scalar zero IS an eigenvalue.
    * `slowModeH_at_neg_b`      : h(−b) = −(3/2)·(wn/(Sn·D))·Vg·b²·[(A+bI)⁻¹A⁻¹c]₀  — the residual
                                  of the leading guess μ = −b is EXACTLY O(b²).

  What remains for the full existence statement |λ_slow − (−b)| ≤ C·b² (documented in TODO.md, and
  NOT a Mathlib blocker — see C in the review): h is C¹ in μ near −b with h'(−b) = −1 + O(b) ≠ 0,
  so the scalar inverse function theorem (`Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`)
  produces the unique nearby root μ* = −b + O(b²).  The matrix-free O(b²) residual proved here is
  the substance of that bound.
-/
import GFL.AsymptoticB
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace GFL

open Matrix

/-- The scalar slow-mode function `h(μ) := (j99 − μ) − ρᵀ(A − μ·I)⁻¹ c`.
For `μ ∉ spec(A)`, `μ ∈ spec(J_S) ↔ h(μ) = 0` (`slowMode_det_zero_iff`). -/
noncomputable def slowModeH (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 μ : ℝ) : ℝ :=
  (j99 - μ) - ρ ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ c)

/-- Schur determinant identity, restated with `h`: `det(J_S − μI) = det(A − μI)·h(μ)`. -/
theorem slowMode_det_factor (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 μ : ℝ)
    (hA : IsUnit (A - μ • 1).det) :
    (JSblock A c ρ j99 - μ • 1).det = (A - μ • 1).det * slowModeH A c ρ j99 μ :=
  variantS_schur_det A c ρ j99 μ hA

/-- **Eigenvalue ⟺ scalar zero.**  For `μ ∉ spec(A)` (`A − μI` invertible), `μ` is an eigenvalue
of `J_S` iff the scalar slow-mode function vanishes: `det(J_S − μI) = 0 ↔ h(μ) = 0`. -/
theorem slowMode_det_zero_iff (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 μ : ℝ)
    (hA : IsUnit (A - μ • 1).det) :
    (JSblock A c ρ j99 - μ • 1).det = 0 ↔ slowModeH A c ρ j99 μ = 0 := by
  rw [slowMode_det_factor A c ρ j99 μ hA, mul_eq_zero, or_iff_right hA.ne_zero]

/-- **The scalar zero IS an eigenvalue.**  If `h(μ) = 0` (and `μ ∉ spec(A)`), then `J_S − μI` is
singular, so there is a nonzero `v` with `J_S · v = μ · v`: `μ` is a genuine eigenvalue of the
full block system `J_S`.  (Same nontrivial-kernel argument as Theorem A, via
`exists_mulVec_eq_zero_iff`.) -/
theorem eigenvalue_of_slowMode_zero (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 μ : ℝ)
    (hA : IsUnit (A - μ • 1).det) (hh : slowModeH A c ρ j99 μ = 0) :
    ∃ v : (Fin 8 ⊕ Unit) → ℝ, v ≠ 0 ∧ JSblock A c ρ j99 *ᵥ v = μ • v := by
  have hdet : (JSblock A c ρ j99 - μ • 1).det = 0 :=
    (slowMode_det_zero_iff A c ρ j99 μ hA).mpr hh
  obtain ⟨v, hv0, hvk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, ?_⟩
  have h := hvk
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h
  exact h

/-- **The residual of the leading guess `μ = −b` is exactly `O(b²)`.**
With `j99 = −b` (Variant S) and the Power-Lock hypotheses,
`h(−b) = −(3/2)·(wn/(Sn·D))·Vg · b² · [(A+bI)⁻¹A⁻¹c]₀`.  So the scalar function `h` — whose zero is
the slow eigenvalue — is already `O(b²)` at the leading guess `−b`; this is the matrix-free content
of `λ_slow = −b + O(b²)`.  (Proof: `h(−b) = (j99 + b) − ρᵀ(A+bI)⁻¹c = 0 − [b² term]` via
`schur_term_b_sq`.) -/
theorem slowModeH_at_neg_b (p : Params)
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : IsUnit A.det) (hB : IsUnit (A + p.b • 1).det)
    (c v : Fin 8 → ℝ) (hAv : A *ᵥ v = -c) (hv0 : v 0 = 0)
    (ρ : Fin 8 → ℝ) (hρ : ρ = (-(3 / 2) * p.kappa * p.Vg) • Pi.single 0 1)
    (j99 : ℝ) (hj99 : j99 = -p.b) :
    slowModeH A c ρ j99 (-p.b)
      = -((3 / 2) * (p.wn / (p.Sn * p.D)) * p.Vg * p.b ^ 2 *
          (((A + p.b • 1)⁻¹ *ᵥ (A⁻¹ *ᵥ c)) 0)) := by
  have hsub : A - (-p.b) • (1 : Matrix (Fin 8) (Fin 8) ℝ) = A + p.b • 1 := by
    rw [neg_smul, sub_neg_eq_add]
  unfold slowModeH
  rw [hsub, hj99, schur_term_b_sq p A hA hB c v hAv hv0 ρ hρ]
  ring

end GFL
