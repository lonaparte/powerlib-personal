/-
  Theorem C (§7): oscillation requires an explicit angle→power coupling `Ks`.

  Augment Variant S with an angle state `δ` and stiffness `Ks ≥ 0`:
      δ'  = dw
      dw' = −b·dw − β·Ks·δ              (β := wn/(2H) > 0)
  On the reduced manifold (`P_meas ≡ P_ref`) the `(δ, dw)` subsystem is linear with
  companion matrix `!![0, 1; −β·Ks, −b]` and characteristic polynomial

      λ² + b·λ + β·Ks   (= `cp b (β·Ks)` below; write `s := β·Ks ≥ 0`).

  We prove:
    * `charpoly_eq` : the companion matrix's characteristic polynomial is `cp b s`.
    * (C1) `Ks = 0` ⟹ eigenvalues `{0, −b}`, both real (and these are the only roots).
    * (C2) `Ks > 0` ⟹ eigenvalues `−b/2 ± i·ω` with `ω ≥ 0`, `ω² = β·Ks − b²/4`;
            real part `−b/2`, natural frequency `ω_osc = ω = √(β·Ks − b²/4)`, and the
            eigenvalues are non-real (oscillatory) iff `β·Ks > b²/4`.
-/
import GFL.Model

namespace GFL

open Matrix Complex

/-- Characteristic polynomial `λ² + b·λ + s` of the reduced `(δ, dw)` system, as a map
`ℂ → ℂ`.  Here `s = β·Ks ≥ 0`. -/
noncomputable def cp (b s : ℝ) (z : ℂ) : ℂ := z ^ 2 + (b : ℂ) * z + (s : ℂ)

/-- The `(δ, dw)` companion matrix `!![0, 1; −s, −b]` (entries cast to `ℂ`). -/
noncomputable def Mc (b s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -(s : ℂ), -(b : ℂ)]

/-- The characteristic polynomial of the companion matrix is `cp b s`:
`det (λ·I − M) = λ² + b·λ + s`. -/
theorem charpoly_eq (b s : ℝ) (z : ℂ) :
    (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Mc b s).det = cp b s z := by
  rw [Matrix.det_fin_two]
  simp only [Mc, cp, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.of_apply,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  norm_num
  ring

/-- **Theorem C, part (C1): `Ks = 0`.**
The characteristic polynomial `λ² + b·λ` has exactly the two real roots `0` and `−b`. -/
theorem thmC_Ks_zero (b : ℝ) :
    cp b 0 0 = 0 ∧ cp b 0 (-(b : ℂ)) = 0 ∧
    (∀ z : ℂ, cp b 0 z = 0 → z = 0 ∨ z = -(b : ℂ)) := by
  refine ⟨by simp [cp], by rw [cp]; push_cast; ring, ?_⟩
  intro z hz
  have hfac : z * (z + (b : ℂ)) = 0 := by rw [cp] at hz; push_cast at hz; linear_combination hz
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl h
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- **Theorem C, part (C2): `Ks > 0`.**
With `s := β·Ks` and any `ω ≥ 0` such that `ω² = s − b²/4` (i.e. `ω = √(s − b²/4)`):
the two roots `−b/2 ± i·ω` annihilate the characteristic polynomial, have real part
`−b/2` and imaginary parts `±ω`, and are non-real (oscillatory) iff `b²/4 < s`. -/
theorem thmC_onset (b s ω : ℝ) (hω : ω ^ 2 = s - b ^ 2 / 4) (hωnn : 0 ≤ ω) :
    cp b s ((-b / 2 : ℝ) + (ω : ℂ) * Complex.I) = 0 ∧
    cp b s ((-b / 2 : ℝ) + ((-ω : ℝ) : ℂ) * Complex.I) = 0 ∧
    ((-b / 2 : ℝ) + (ω : ℂ) * Complex.I).re = -b / 2 ∧
    ((-b / 2 : ℝ) + (ω : ℂ) * Complex.I).im = ω ∧
    (((-b / 2 : ℝ) + (ω : ℂ) * Complex.I).im ≠ 0 ↔ b ^ 2 / 4 < s) := by
  -- ω*ω form of the hypothesis (for the real-part equation)
  have hωω : ω * ω = s - b ^ 2 / 4 := by rw [← pow_two]; exact hω
  -- a single root computation for imaginary coefficient `t` with `t² = ω²`
  have root : ∀ t : ℝ, t ^ 2 = ω ^ 2 → cp b s ((-b / 2 : ℝ) + (t : ℂ) * Complex.I) = 0 := by
    intro t ht
    have htt : t * t = s - b ^ 2 / 4 := by rw [← pow_two, ht]; exact hω
    rw [Complex.ext_iff]
    refine ⟨?_, ?_⟩
    all_goals
      simp only [cp, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re,
        Complex.zero_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add]
    all_goals ring_nf
    all_goals nlinarith [htt, hωω]
  refine ⟨root ω rfl, root (-ω) (by rw [neg_pow]; ring), ?_, ?_, ?_⟩
  · simp [Complex.add_re, Complex.mul_re]
  · simp [Complex.add_im, Complex.mul_im]
  · -- non-real iff b²/4 < s
    have him : ((-b / 2 : ℝ) + (ω : ℂ) * Complex.I).im = ω := by simp [Complex.add_im, Complex.mul_im]
    rw [him]
    constructor
    · intro hne
      have hpos : 0 < ω := lt_of_le_of_ne hωnn (Ne.symm hne)
      have : 0 < ω ^ 2 := pow_pos hpos 2
      linarith [hω, this]
    · intro hlt hzero
      rw [hzero] at hω
      simp at hω
      linarith [hω, hlt]

/-- **Theorem C2 — exhaustiveness / reverse direction.**
With `ω ≥ 0`, `ω² = β·Ks − b²/4` (so `β·Ks ≥ b²/4`): the characteristic polynomial factors,
so its roots are **exactly** `{−b/2 + iω, −b/2 − iω}` — there are no others.  Consequently a
root is non-real (oscillatory) **iff** `β·Ks > b²/4`, proven in *both* directions (this gives
the reverse `complex root ⟹ discriminant < 0`, not only the forward construction). -/
theorem thmC_roots_exhaustive (b s ω : ℝ) (hω : ω ^ 2 = s - b ^ 2 / 4) (z : ℂ) :
    cp b s z = 0 ↔
      z = (-b / 2 : ℝ) + (ω : ℂ) * Complex.I ∨ z = (-b / 2 : ℝ) + ((-ω : ℝ) : ℂ) * Complex.I := by
  have hωC : (ω : ℂ) ^ 2 = (s : ℂ) - (b : ℂ) ^ 2 / 4 := by exact_mod_cast hω
  -- sum and product of the two roots
  have hsum : ((-b / 2 : ℝ) + (ω : ℂ) * Complex.I) + ((-b / 2 : ℝ) + ((-ω : ℝ) : ℂ) * Complex.I)
      = -(b : ℂ) := by push_cast; ring
  have hprod : ((-b / 2 : ℝ) + (ω : ℂ) * Complex.I) * ((-b / 2 : ℝ) + ((-ω : ℝ) : ℂ) * Complex.I)
      = (s : ℂ) := by
    push_cast
    linear_combination (-(ω : ℂ) ^ 2) * Complex.I_sq + hωC
  -- the monic quadratic factors as (z − r₊)(z − r₋)
  have key : cp b s z
      = (z - ((-b / 2 : ℝ) + (ω : ℂ) * Complex.I)) *
        (z - ((-b / 2 : ℝ) + ((-ω : ℝ) : ℂ) * Complex.I)) := by
    have expand :
        (z - ((-b / 2 : ℝ) + (ω : ℂ) * Complex.I)) *
          (z - ((-b / 2 : ℝ) + ((-ω : ℝ) : ℂ) * Complex.I))
        = z ^ 2
          - (((-b / 2 : ℝ) + (ω : ℂ) * Complex.I) + ((-b / 2 : ℝ) + ((-ω : ℝ) : ℂ) * Complex.I)) * z
          + ((-b / 2 : ℝ) + (ω : ℂ) * Complex.I) * ((-b / 2 : ℝ) + ((-ω : ℝ) : ℂ) * Complex.I) := by
      ring
    rw [cp, expand, hsum, hprod]; ring
  rw [key, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- **Theorem C2 — overdamped (real-root) case `β·Ks ≤ b²/4`.**
With `μ ≥ 0`, `μ² = b²/4 − β·Ks`: the characteristic polynomial factors over the reals,
its roots are **exactly** the two real numbers `−b/2 ± μ`, and in particular both roots are
real (`im = 0`) — no oscillation.  Together with `thmC_roots_exhaustive` this covers the
full discriminant trichotomy. -/
theorem thmC_real_roots (b s μ : ℝ) (hμ : μ ^ 2 = b ^ 2 / 4 - s) (z : ℂ) :
    cp b s z = 0 ↔ z = ((-b / 2 + μ : ℝ) : ℂ) ∨ z = ((-b / 2 - μ : ℝ) : ℂ) := by
  have hμC : (μ : ℂ) ^ 2 = (b : ℂ) ^ 2 / 4 - (s : ℂ) := by exact_mod_cast hμ
  have hsum : (((-b / 2 + μ : ℝ)) : ℂ) + (((-b / 2 - μ : ℝ)) : ℂ) = -(b : ℂ) := by
    push_cast; ring
  have hprod : (((-b / 2 + μ : ℝ)) : ℂ) * (((-b / 2 - μ : ℝ)) : ℂ) = (s : ℂ) := by
    push_cast; linear_combination -hμC
  have key : cp b s z
      = (z - (((-b / 2 + μ : ℝ)) : ℂ)) * (z - (((-b / 2 - μ : ℝ)) : ℂ)) := by
    have expand :
        (z - (((-b / 2 + μ : ℝ)) : ℂ)) * (z - (((-b / 2 - μ : ℝ)) : ℂ))
        = z ^ 2 - ((((-b / 2 + μ : ℝ)) : ℂ) + (((-b / 2 - μ : ℝ)) : ℂ)) * z
          + (((-b / 2 + μ : ℝ)) : ℂ) * (((-b / 2 - μ : ℝ)) : ℂ) := by ring
    rw [cp, expand, hsum, hprod]; ring
  rw [key, mul_eq_zero, sub_eq_zero, sub_eq_zero]

end GFL
