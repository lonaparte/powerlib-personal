/-
  Theorem B — full-system O(b²) asymptotic of the slow eigenvalue.

  STATUS: PARTIAL.  This file proves the *algebraic* core that pins the order to b²,
  with NO `sorry`.  The two pieces that require operator-norm / complex-analysis
  infrastructure currently absent or awkward in Mathlib are NOT proved here and are
  documented in `BLOCKERS.md` (no stubs).

  What IS proved (pure linear algebra; path (a), the direct-algebraic route):

  * `resolvent_id`        : the resolvent identity `(A+b·I)⁻¹ = A⁻¹ − b·(A+b·I)⁻¹A⁻¹`.
  * `schur_term_at_neg_b` : the requested factorisation — the Schur term at `μ = −b` is
                            `−b·K` for an explicit `K` (so it is O(b); the O(1) term is 0
                            by `schur_term_zero`).
  * `schur_term_b_sq`     : the EXACT identity
        `ρᵀ(A+b·I)⁻¹c  =  (3/2)·(wn/(Sn·D))·Vg · b² · [ (A+b·I)⁻¹A⁻¹c ]₀`,
        i.e. the Schur correction carries an explicit factor `b²` (the `b` from the
        resolvent identity times the `b` hidden in `ρ` through `κ = (wn/(Sn·D))·b`).
        This is the machine-checked "second order in b" structure.

  What is NOT proved here (see BLOCKERS.md):
  (B1) a uniform bound `|[ (A+b·I)⁻¹A⁻¹c ]₀| ≤ C` for small b (continuity/Neumann bound on
       the matrix inverse under a sub-multiplicative operator norm), which would upgrade
       `schur_term_b_sq` to `|ρᵀ(A+b·I)⁻¹c| ≤ C·b²`;
  (B2) existence/uniqueness of the eigenvalue `λ_slow` of the full 9×9 `J_S` with
       `|λ_slow − (−b)| ≤ C·b²` (Rouché / contraction-mapping to the determinant root).
-/
import GFL.TheoremB

namespace GFL

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Resolvent identity.**  For invertible `A` and `A + b·I`,
`(A + b·I)⁻¹ = A⁻¹ − b·((A + b·I)⁻¹ * A⁻¹)`.  (Exact; no series.) -/
theorem resolvent_id (A : Matrix n n ℝ) (b : ℝ)
    (hA : IsUnit A.det) (hB : IsUnit (A + b • 1).det) :
    (A + b • (1 : Matrix n n ℝ))⁻¹ = A⁻¹ - b • ((A + b • 1)⁻¹ * A⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv (A + b • 1) hB, Matrix.one_mul,
      show (A + b • (1 : Matrix n n ℝ)) * A⁻¹ - b • A⁻¹ = (A + b • 1 - b • 1) * A⁻¹ by
        rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul],
      add_sub_cancel_right, Matrix.mul_nonsing_inv A hA]

/-- **Resolvent (second) identity — exact difference.**  For `A − μI` and `A − νI` both invertible,
`(A − μI)⁻¹ − (A − νI)⁻¹ = (μ − ν) • ((A − μI)⁻¹ * (A − νI)⁻¹)`.  This is the exact difference
quotient underlying `d/dμ (A − μI)⁻¹ = (A − μI)⁻²` (the slope is the RHS over `(μ−ν)`). -/
theorem resolvent_sub (A : Matrix n n ℝ) (μ ν : ℝ)
    (hμ : IsUnit (A - μ • 1).det) (hν : IsUnit (A - ν • 1).det) :
    (A - μ • (1 : Matrix n n ℝ))⁻¹ - (A - ν • 1)⁻¹
      = (μ - ν) • ((A - μ • 1)⁻¹ * (A - ν • 1)⁻¹) := by
  have hdiff : (A - ν • (1 : Matrix n n ℝ)) - (A - μ • 1) = (μ - ν) • 1 := by
    rw [sub_sub_sub_cancel_left, sub_smul]
  have key : (A - μ • (1 : Matrix n n ℝ))⁻¹ * ((A - ν • 1) - (A - μ • 1)) * (A - ν • 1)⁻¹
      = (A - μ • 1)⁻¹ - (A - ν • 1)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv (A - ν • 1) hν, Matrix.mul_one,
        Matrix.nonsing_inv_mul (A - μ • 1) hμ, Matrix.one_mul]
  rw [← key, hdiff, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

/-- Resolvent identity applied to a vector `c`. -/
theorem resolvent_mulVec (A : Matrix n n ℝ) (b : ℝ)
    (hA : IsUnit A.det) (hB : IsUnit (A + b • 1).det) (c : n → ℝ) :
    (A + b • (1 : Matrix n n ℝ))⁻¹ *ᵥ c
      = A⁻¹ *ᵥ c - b • ((A + b • 1)⁻¹ *ᵥ (A⁻¹ *ᵥ c)) := by
  conv_lhs => rw [resolvent_id A b hA hB]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec]

/-- **`schur_term_at_neg_b` (factorisation).**  Under the Power-Lock hypotheses (which give
`ρᵀ A⁻¹ c = 0` via `schur_term_zero`), the Schur term at `μ = −b` factors as `−b·K` with
`K := ρᵀ (A+b·I)⁻¹ A⁻¹ c`.  Hence it is O(b): the O(1) part vanishes exactly. -/
theorem schur_term_at_neg_b (p : Params)
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : IsUnit A.det) (hB : IsUnit (A + p.b • 1).det)
    (c v : Fin 8 → ℝ) (hAv : A *ᵥ v = -c) (hv0 : v 0 = 0)
    (ρ : Fin 8 → ℝ) (hρ : ρ = (-(3 / 2) * p.kappa * p.Vg) • Pi.single 0 1) :
    ∃ K : ℝ, ρ ⬝ᵥ ((A + p.b • 1)⁻¹ *ᵥ c) = -p.b * K := by
  have hz : ρ ⬝ᵥ (A⁻¹ *ᵥ c) = 0 := schur_term_zero p A hA c v hAv hv0 ρ hρ
  refine ⟨ρ ⬝ᵥ ((A + p.b • 1)⁻¹ *ᵥ (A⁻¹ *ᵥ c)), ?_⟩
  rw [resolvent_mulVec A p.b hA hB c, dotProduct_sub, dotProduct_smul, hz, smul_eq_mul]
  ring

/-- κ and b are proportional along the physical timescale-separation scaling:
`κ = (wn/(Sn·D))·b`  (both `∝ 1/H`). -/
theorem kappa_eq_const_mul_b (p : Params) : p.kappa = (p.wn / (p.Sn * p.D)) * p.b := by
  have := p.H_pos; have := p.Sn_pos; have := p.D_pos
  unfold Params.kappa Params.b
  field_simp

/-- **`schur_term_b_sq` — the exact O(b²) identity.**  Substituting `κ = (wn/(Sn·D))·b`
into the factorisation gives an explicit factor `b²`:
`ρᵀ(A+b·I)⁻¹c = (3/2)·(wn/(Sn·D))·Vg · b² · [ (A+b·I)⁻¹A⁻¹c ]₀`.
The only `b`-dependent factor on the right besides `b²` is the `0`-component of the bounded
vector `(A+b·I)⁻¹A⁻¹c` (→ `(A⁻²c)₀` as `b → 0`). -/
theorem schur_term_b_sq (p : Params)
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : IsUnit A.det) (hB : IsUnit (A + p.b • 1).det)
    (c v : Fin 8 → ℝ) (hAv : A *ᵥ v = -c) (hv0 : v 0 = 0)
    (ρ : Fin 8 → ℝ) (hρ : ρ = (-(3 / 2) * p.kappa * p.Vg) • Pi.single 0 1) :
    ρ ⬝ᵥ ((A + p.b • 1)⁻¹ *ᵥ c)
      = (3 / 2) * (p.wn / (p.Sn * p.D)) * p.Vg * p.b ^ 2 *
          (((A + p.b • 1)⁻¹ *ᵥ (A⁻¹ *ᵥ c)) 0) := by
  have hz : ρ ⬝ᵥ (A⁻¹ *ᵥ c) = 0 := schur_term_zero p A hA c v hAv hv0 ρ hρ
  rw [resolvent_mulVec A p.b hA hB c, dotProduct_sub, dotProduct_smul, hz, smul_eq_mul,
      hρ, smul_dotProduct, single_dotProduct, smul_eq_mul, kappa_eq_const_mul_b]
  ring

end GFL
