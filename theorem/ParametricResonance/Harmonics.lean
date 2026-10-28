import theorem.ParametricResonance.ForcedResponse

/-! # Harmonic bookkeeping of the single-tone pump (third-order continuation)

Exact trigonometric identities used by the order-by-order harmonic balance of the source (§10),
and solvability of every harmonic equation.

Scope.
* Single-tone pump `u = δ cos(ω_p t)` with `e = e^{jω_p t}`; Hurwitz state matrix `A₀` for the
  harmonic equations.

Source: work-sync projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md §10.

Results.
* `u = (δ/2)(e + e⁻¹)`, so `u|_{e¹} = δ/2`.
* `u² = δ² [1/2 + (e² + e⁻²)/4]`.
* `u³ = δ³ [(3/8)(e + e⁻¹) + (1/8)(e³ + e⁻³)]`, so `u³|_{e¹} = 3δ³/8`, `u³|_{e³} = δ³/8`.
* `harmonic_solvable` — for a Hurwitz `A₀` every harmonic equation
  `(jhω_p I − A₀) X = R` (`h ∈ ℤ`, any right-hand side) has the unique solution
  `X = (jhω_p I − A₀)⁻¹ R`; no denominator `jhω_p − λ_k` vanishes.

Not formalized.
* The full third-order coefficient formulas (`Y₁`, `P₃`, `Y₃`, `P₃₃`) of the source
  (multilinear bookkeeping without a stated property).
-/

noncomputable section
namespace powerlib.ParametricResonance

open Complex Matrix

/-- `δ cos θ = (δ/2)(e^{jθ} + e^{−jθ})`. -/
@[tmio T, powerlib_foundation] theorem pump_harmonic1 (δ θ : ℝ) :
    ((δ * Real.cos θ : ℝ) : ℂ) = δ / 2 * (exp (θ * I) + exp (-(θ * I))) := by
  have h1 : exp (θ * I) = Complex.cos θ + Complex.sin θ * I := Complex.exp_mul_I θ
  have h2 : exp (-(θ * I)) = Complex.cos θ - Complex.sin θ * I := by
    rw [show -((θ : ℂ) * I) = (-(θ : ℂ)) * I by ring, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]; ring
  rw [h1, h2]; push_cast; ring

/-- `u² = δ² [1/2 + (e² + e⁻²)/4]`. -/
@[powerlib_foundation] theorem pump_harmonic2 (δ θ : ℝ) :
    ((δ * Real.cos θ : ℝ) : ℂ) ^ 2 =
      δ ^ 2 * (1 / 2 + (exp (θ * I) ^ 2 + exp (-(θ * I)) ^ 2) / 4) := by
  rw [pump_harmonic1]
  have h : exp (θ * I) * exp (-(θ * I)) = 1 := by rw [← Complex.exp_add]; simp
  linear_combination (δ ^ 2 / 2) * h

/-- `u³ = δ³ [(3/8)(e + e⁻¹) + (1/8)(e³ + e⁻³)]`. -/
@[powerlib_foundation] theorem pump_harmonic3 (δ θ : ℝ) :
    ((δ * Real.cos θ : ℝ) : ℂ) ^ 3 =
      δ ^ 3 * (3 / 8 * (exp (θ * I) + exp (-(θ * I))) +
        1 / 8 * (exp (θ * I) ^ 3 + exp (-(θ * I)) ^ 3)) := by
  rw [pump_harmonic1]
  have h : exp (θ * I) * exp (-(θ * I)) = 1 := by rw [← Complex.exp_add]; simp
  linear_combination (3 * δ ^ 3 / 8 * (exp (θ * I) + exp (-(θ * I)))) * h

/-- For a Hurwitz `A₀`, every harmonic equation `(jhω_p I − A₀) X = R` is uniquely solvable. -/
@[powerlib_foundation] theorem harmonic_solvable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) (ωp : ℝ) (h : ℤ) (R : Fin n → ℂ) :
    ∃! X : Fin n → ℂ, Linear.characteristicMatrix A (((h * ωp : ℝ) : ℂ) * I) *ᵥ X = R := by
  have hdet := det_characteristicMatrix_imag_ne_zero hA (h * ωp)
  set M := Linear.characteristicMatrix A (((h * ωp : ℝ) : ℂ) * I)
  refine ⟨M⁻¹ *ᵥ R, ?_, fun X hX => ?_⟩
  · simp only
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  · rw [← hX, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]

end powerlib.ParametricResonance
