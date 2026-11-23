import theorem.Linear.Realization
import theorem.Criteria.Hurwitz

/-! # Hurwitz criteria for monic quadratics and real 2×2 matrices

Hurwitz and instability criteria for real quadratics and `2 × 2` matrices, with thin generic
semantic corollaries at the end.

Scope.
* `LinearSystems.IsHurwitz A` is the LeanForControl eigenpair predicate: every complex
  eigenpair `(μ, v)`, `v ≠ 0`, of the complexified matrix `A.map (algebraMap ℝ ℂ)` has
  `μ.re < 0`.
* `Linear.SpectrallyStable A` is the powerlib characteristic-root predicate:
  `det (s • 1 - A) = 0 → s.re < 0` (`theorem/Linear/Transfer.lean`).
* Both are statements about one fixed real matrix; they say nothing about a physical model
  until a Jacobian or state matrix of a formalized system is identified with `A`. No model family
  is defined: static algebra and generic semantic implications only (foundation results,
  Rules §3).

Source: standard Routh–Hurwitz criterion for degree two (shared criteria interface for the
work-sync formalization).

Results.
* Any dimension: characteristic roots ↔ eigenpairs
  (`Linear.det_characteristicMatrix_eq_zero_iff_exists_eigenpair`, any index; the root form of
  `IsHurwitz` is `Linear.spectrallyStable_iff_isHurwitz`, the polynomial form
  `Criteria.isHurwitz_iff_of_charpoly`).
* Monic real quadratic `s ^ 2 + a1 * s + a0`: all complex roots in the open left half-plane
  iff `0 < a1 ∧ 0 < a0` (both directions, `quadratic_roots_re_neg_iff`; the necessary direction
  is Stodola's condition `Criteria.coeff_pos_of_roots_re_neg`); explicit root witnesses
  with `0 < re` (`exists_quadratic_root_pos_of_const_neg`,
  `exists_quadratic_root_re_pos_of_linear_neg`, instances of the generic witnesses of
  `theorem/Criteria/Hurwitz.lean`);
  all roots real iff `0 ≤ a1 ^ 2 - 4 * a0` (`quadratic_roots_real_iff`). For a real quadratic
  `a x² + b x + c` with `a > 0`: negative exactly strictly between the two roots (`quad_neg_iff`),
  and `(−b ± √D)/(2a)` are its roots when `D ≥ 0` (`quad_root`). For `λ² + aλ + b` with `a > 0`,
  `0 ≤ b`, `4b ≤ a²` (`ε = b/a²`): real roots iff `ε ≤ 1/4` (`eigen_real_iff`),
  `λ± = −(a/2)(1 ∓ √(1 − 4ε))` (`eigen_roots`), `λ₊/λ₋ = 4ε/(1 + √(1 − 4ε))² ∈ [ε, 4ε]`
  (`eigen_ratio`, `eigen_ratio_ge`, `eigen_ratio_le`), `λ₋ ∈ [−a, −a/2]` (`eigen_fast_bounds`),
  `λ₊ ∈ [−2b/a, −b/a]` (`eigen_slow_bounds`).
* `A : Matrix (Fin 2) (Fin 2) ℝ`: `det (s • 1 - A) = s ^ 2 - tr A * s + det A`
  (`det_characteristicMatrix_fin_two`); `IsHurwitz A ↔ A.trace < 0 ∧ 0 < A.det`
  (`isHurwitz_fin_two_iff`; for `SpectrallyStable` through `Linear.spectrallyStable_iff_isHurwitz`;
  for the literal `!![a, b; c, d]`, `isHurwitz_fin_two_of_iff`, and for the companion form
  `!![0, 1; -a0, -a1]`, `isHurwitz_companion_two_iff`; in coefficients `a₂ s² + a₁ s + a₀`,
  `a₂ > 0`, `tr = −a₁/a₂`, `det = a₀/a₂`: `isHurwitz_iff_of_coeffs_quadratic`). The damping ratio
  `dampingRatio A = −tr A / (2 √det A)` and natural frequency `naturalFrequency A = √det A`
  (definitions): `ω_n² = det A` (`naturalFrequency_sq`), `2 ζ ω_n = −tr A`
  (`two_mul_dampingRatio_mul_naturalFrequency`), hence for `det A > 0`,
  `det (s • 1 − A) = s² + 2ζω_n s + ω_n²` (`det_characteristicMatrix_standard`); `ζ` is
  invariant under similarity (`dampingRatio_conj`).
* Instability witnesses: `A.det < 0` and `0 < A.trace` are the cases `n = 2` of the generic
  witnesses `Criteria.exists_pos_real_eigenvalue_of_det`, `Criteria.exists_root_re_pos_of_det`
  (`(-1) ^ 2 * A.det = A.det`), `Criteria.exists_eigenpair_re_pos_of_trace_pos` and
  `Criteria.exists_root_re_pos_of_trace_pos`; their disjunction, a strict violation of
  `isHurwitz_fin_two_iff`, is `exists_root_re_pos_of_violation_fin_two`.
* Discriminant: all eigenvalues real iff `0 ≤ tr² − 4 det`
  (`eigenvalues_real_iff_discriminant_nonneg`); nilpotency: `A ^ 2 = 0 ↔ tr A = 0 ∧ det A = 0`
  (`sq_eq_zero_iff_trace_det_eq_zero_fin_two`) and `IsNilpotent A ↔ tr A = 0 ∧ det A = 0`
  (`isNilpotent_iff_trace_det_eq_zero_fin_two`).
* Semantic corollaries: linearization at an equilibrium of a `ContDiff ℝ 1` vector field on
  `EuclideanSpace ℝ (Fin 2)` (local exponential stability,
  `locallyExponentiallyStable_of_jacobian_fin_two`; instability from `det < 0` or `0 < tr` is the
  any-dimension `Criteria.unstable_of_jacobian_det`, `Criteria.unstable_of_jacobian_trace_pos`)
  and the attractive sentences of a two-state linear field (`holds_affine_fin_two_iff`). These
  only repackage LeanForControl's `hurwitz_linearization_locally_exponentially_stable` and the
  linear hub `Linear.holds_iff_isHurwitz`; the model boundary is whatever vector field the caller
  supplies.
-/

noncomputable section
namespace powerlib.Criteria
open Matrix Polynomial

/-! ## Any dimension: characteristic roots and eigenpairs -/

section General

variable {n : ℕ}

@[tmio T, powerlib_foundation] theorem det_characteristicMatrix_eq_zero_of_eigenpair
    (A : Matrix (Fin n) (Fin n) ℝ) {s : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0)
    (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = s • v) :
    (Linear.characteristicMatrix A s).det = 0 :=
  (Linear.det_characteristicMatrix_eq_zero_iff_exists_eigenpair A s).mpr ⟨v, hv, heig⟩

/-- A characteristic root with positive real part, in the eigenpair shape used by
LeanForControl's `unstable_of_exists_complex_eigenvalue_re_pos`. -/
@[tmio T, powerlib_foundation] theorem exists_eigenpair_re_pos_of_characteristic_root
    (A : Matrix (Fin n) (Fin n) ℝ) {s : ℂ} (h : (Linear.characteristicMatrix A s).det = 0)
    (hs : 0 < s.re) :
    ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  obtain ⟨v, hv, heig⟩ := Linear.exists_eigenvector_of_root h
  exact ⟨s, v, hv, heig, hs⟩

end General

/-! ## Monic real quadratics -/

section Quadratic

/-- Real part of a root of the monic real quadratic: `x² − y² + a1 x + a0 = 0` for `s = x + iy`. -/
@[tmio T, powerlib_foundation] theorem quadratic_root_re {a1 a0 : ℝ} {s : ℂ}
    (h : s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0) :
    s.re ^ 2 - s.im ^ 2 + a1 * s.re + a0 = 0 := by
  have hr := congrArg Complex.re h
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re] at hr
  linear_combination hr

/-- Imaginary part of a root of the monic real quadratic: `y (2x + a1) = 0` for `s = x + iy`. -/
@[tmio T, powerlib_foundation] theorem quadratic_root_im {a1 a0 : ℝ} {s : ℂ}
    (h : s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0) :
    s.im * (2 * s.re + a1) = 0 := by
  have hi := congrArg Complex.im h
  simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_im] at hi
  linear_combination hi

@[tmio T, powerlib_foundation] theorem quadratic_root_of_re_im {a1 a0 x y : ℝ}
    (hre : x ^ 2 - y ^ 2 + a1 * x + a0 = 0) (him : y * (2 * x + a1) = 0) :
    (⟨x, y⟩ : ℂ) ^ 2 + (a1 : ℂ) * ⟨x, y⟩ + (a0 : ℂ) = 0 := by
  apply Complex.ext
  · simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re]
    linear_combination hre
  · simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im]
    linear_combination him

@[tmio T, powerlib_foundation] theorem quadratic_real_root_complex {a1 a0 r : ℝ}
    (h : r ^ 2 + a1 * r + a0 = 0) :
    (r : ℂ) ^ 2 + (a1 : ℂ) * (r : ℂ) + (a0 : ℂ) = 0 := by
  exact_mod_cast h

/-- The monic real quadratic `X² + a1 X + a0` as a polynomial, to apply the generic criteria of
`theorem/Criteria/Hurwitz.lean`. -/
private def quadraticPoly (a1 a0 : ℝ) : ℝ[X] := X ^ 2 + C a1 * X + C a0

@[tmio T, powerlib_foundation] private theorem quadraticPoly_monic (a1 a0 : ℝ) :
    (quadraticPoly a1 a0).Monic := by
  unfold quadraticPoly
  monicity!

@[tmio T, powerlib_foundation] private theorem aeval_quadraticPoly (a1 a0 : ℝ) (s : ℂ) :
    aeval s (quadraticPoly a1 a0) = s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) := by
  simp [quadraticPoly]

/-- `a0 < 0`: a positive real root (`Criteria.exists_pos_root_of_coeff_zero_neg`). -/
@[tmio T, powerlib_foundation] theorem exists_quadratic_root_pos_of_const_neg {a1 a0 : ℝ}
    (h0 : a0 < 0) : ∃ r : ℝ, 0 < r ∧ r ^ 2 + a1 * r + a0 = 0 := by
  obtain ⟨r, hr, hroot⟩ := exists_pos_root_of_coeff_zero_neg (quadraticPoly_monic a1 a0)
    (by simpa [quadraticPoly] using h0)
  exact ⟨r, hr, by simpa [quadraticPoly] using hroot⟩

/-- `a1 < 0`: a root with positive real part (`Criteria.exists_root_re_pos_of_coeff_neg`). -/
@[tmio T, powerlib_foundation] theorem exists_quadratic_root_re_pos_of_linear_neg {a1 a0 : ℝ}
    (h1 : a1 < 0) : ∃ s : ℂ, s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧ 0 < s.re := by
  obtain ⟨s, hs, hre⟩ := exists_root_re_pos_of_coeff_neg (quadraticPoly_monic a1 a0) (k := 1)
    (by simpa [quadraticPoly, coeff_X] using h1)
  exact ⟨s, by rwa [aeval_quadraticPoly] at hs, hre⟩

/-- Routh–Hurwitz for a monic real quadratic, both directions: the necessary direction is
Stodola's condition (`Criteria.coeff_pos_of_roots_re_neg`). -/
@[tmio T, powerlib_foundation] theorem quadratic_roots_re_neg_iff (a1 a0 : ℝ) :
    (∀ s : ℂ, s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 → s.re < 0) ↔ 0 < a1 ∧ 0 < a0 := by
  constructor
  · intro H
    have h := coeff_pos_of_roots_re_neg (quadraticPoly_monic a1 a0) fun s hs =>
      H s (by rwa [aeval_quadraticPoly] at hs)
    have hd : (quadraticPoly a1 a0).natDegree = 2 := by
      unfold quadraticPoly
      compute_degree!
    exact ⟨by simpa [quadraticPoly, coeff_X] using h 1 (by omega),
      by simpa [quadraticPoly] using h 0 (by omega)⟩
  · rintro ⟨h1, h0⟩ s hs
    have hr := quadratic_root_re hs
    have hi := quadratic_root_im hs
    by_contra hx
    push Not at hx
    rcases mul_eq_zero.mp hi with hy | hx'
    · rw [hy] at hr
      nlinarith [sq_nonneg s.re, mul_nonneg h1.le hx]
    · linarith

/-- All complex roots of a monic real quadratic are real iff its discriminant is nonnegative. -/
@[tmio T, powerlib_foundation] theorem quadratic_roots_real_iff (a1 a0 : ℝ) :
    (∀ s : ℂ, s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 → s.im = 0) ↔ 0 ≤ a1 ^ 2 - 4 * a0 := by
  constructor
  · intro H
    by_contra hΔ
    push Not at hΔ
    have hpos : 0 < -(a1 ^ 2 - 4 * a0) := neg_pos.mpr hΔ
    have hsq := Real.sq_sqrt hpos.le
    have him := H ⟨-a1 / 2, Real.sqrt (-(a1 ^ 2 - 4 * a0)) / 2⟩
      (quadratic_root_of_re_im (by linear_combination (-1 / 4 : ℝ) * hsq) (by ring))
    have : Real.sqrt (-(a1 ^ 2 - 4 * a0)) / 2 = 0 := him
    have := Real.sqrt_pos.mpr hpos
    linarith
  · intro hΔ s hs
    have hr := quadratic_root_re hs
    have hi := quadratic_root_im hs
    rcases mul_eq_zero.mp hi with hy | hx
    · exact hy
    · have hre : s.re = -a1 / 2 := by linarith
      rw [hre] at hr
      have : s.im ^ 2 = -(a1 ^ 2 - 4 * a0) / 4 := by linear_combination -hr
      have h2 : s.im ^ 2 ≤ 0 := by rw [this]; linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h2 (sq_nonneg _))

/-! ### Real quadratics with positive leading coefficient: sign and roots -/

/-- For `a > 0`, `a x² + b x + c < 0` iff `x` lies strictly between the two roots. -/
@[tmio T, powerlib_foundation] theorem quad_neg_iff {a b c x : ℝ} (ha : 0 < a) :
    a * x ^ 2 + b * x + c < 0 ↔
      (-b - √(b ^ 2 - 4 * a * c)) / (2 * a) < x ∧ x < (-b + √(b ^ 2 - 4 * a * c)) / (2 * a) := by
  have h : a * x ^ 2 + b * x + c < 0 ↔ (2 * a * x + b) ^ 2 < b ^ 2 - 4 * a * c := by
    constructor <;> intro h <;> nlinarith
  rw [h, Real.sq_lt, div_lt_iff₀ (by positivity), lt_div_iff₀ (by positivity)]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- For `a ≠ 0` and nonnegative discriminant, `(−b ± √D)/(2a)` are roots. -/
@[tmio T, powerlib_foundation] theorem quad_root {a b c : ℝ} (ha : a ≠ 0) (hD : 0 ≤ b ^ 2 - 4 * a * c)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    a * ((-b + σ * √(b ^ 2 - 4 * a * c)) / (2 * a)) ^ 2 +
      b * ((-b + σ * √(b ^ 2 - 4 * a * c)) / (2 * a)) + c = 0 := by
  have hs := Real.sq_sqrt hD
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set r := √(b ^ 2 - 4 * a * c) with hr
  have key : a * ((-b + σ * r) / (2 * a)) ^ 2 + b * ((-b + σ * r) / (2 * a)) + c =
      (σ ^ 2 * r ^ 2 - (b ^ 2 - 4 * a * c)) / (4 * a) := by
    field_simp; ring
  rw [key, hσ2, hs]; simp

/-! ### Real roots of `λ² + aλ + b`: closed form, ratio and bounds -/

/-- The in-phase eigenvalues are real iff `ε_od ≤ 1/4` (`a ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem eigen_real_iff {a b : ℝ} (ha : a ≠ 0) :
    0 ≤ a ^ 2 - 4 * b ↔ b / a ^ 2 ≤ 1 / 4 := by
  have ha2 : 0 < a ^ 2 := by positivity
  rw [div_le_iff₀ ha2]
  constructor <;> intro h <;> linarith

/-- Real eigenvalues `λ± = −(a/2)(1 ∓ √(1 − 4ε))`, `ε = b/a²` (`a > 0`, `4b ≤ a²`), roots of
`λ² + aλ + b`. -/
@[tmio T, powerlib_foundation] theorem eigen_roots {a b : ℝ} (ha : 0 < a) (hd : 4 * b ≤ a ^ 2) :
    let s := Real.sqrt (1 - 4 * (b / a ^ 2))
    (-(a / 2) * (1 - s)) ^ 2 + a * (-(a / 2) * (1 - s)) + b = 0 ∧
      (-(a / 2) * (1 + s)) ^ 2 + a * (-(a / 2) * (1 + s)) + b = 0 := by
  intro s
  have h1 : 0 ≤ 1 - 4 * (b / a ^ 2) := by
    rw [sub_nonneg, ← le_div_iff₀' (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by positivity)]
    linarith
  have hs : s ^ 2 = 1 - 4 * (b / a ^ 2) := Real.sq_sqrt h1
  have ha2 : a ^ 2 ≠ 0 := by positivity
  have hs' : a ^ 2 * s ^ 2 = a ^ 2 - 4 * b := by rw [hs]; field_simp
  constructor
  · linear_combination (1 / 4 : ℝ) * hs'
  · linear_combination (1 / 4 : ℝ) * hs'

/-- Exact eigenvalue ratio: `λ₊/λ₋ = 4ε/(1 + √(1 − 4ε))²` (`a > 0`, `4b ≤ a²`). -/
@[tmio T, powerlib_foundation] theorem eigen_ratio {a b : ℝ} (ha : 0 < a) (hd : 4 * b ≤ a ^ 2) :
    let ε := b / a ^ 2
    let s := Real.sqrt (1 - 4 * ε)
    (-(a / 2) * (1 - s)) / (-(a / 2) * (1 + s)) = 4 * ε / (1 + s) ^ 2 := by
  intro ε s
  have h1 : 0 ≤ 1 - 4 * ε := by
    simp only [ε]
    rw [sub_nonneg, ← le_div_iff₀' (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by positivity)]
    linarith
  have hs : s ^ 2 = 1 - 4 * ε := Real.sq_sqrt h1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hpos : 0 < 1 + s := by linarith
  have : -(a / 2) * (1 + s) ≠ 0 := by
    have : 0 < a / 2 * (1 + s) := by positivity
    linarith
  rw [div_eq_div_iff this (by positivity)]
  linear_combination (a / 2) * (1 + s) * hs

/-- Lower bound of the eigenvalue ratio: `ε ≤ 4ε/(1 + √(1 − 4ε))²`
(`a > 0`, `0 ≤ b`, `4b ≤ a²`). -/
@[tmio T, powerlib_foundation] theorem eigen_ratio_ge {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hd : 4 * b ≤ a ^ 2) :
    let ε := b / a ^ 2
    let s := Real.sqrt (1 - 4 * ε)
    ε ≤ 4 * ε / (1 + s) ^ 2 := by
  intro ε s
  have hε : 0 ≤ ε := by positivity
  have h1 : 0 ≤ 1 - 4 * ε := by
    simp only [ε]
    rw [sub_nonneg, ← le_div_iff₀' (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by positivity)]
    linarith
  have hs : s ^ 2 = 1 - 4 * ε := Real.sq_sqrt h1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by nlinarith
  have hpos : 0 < 1 + s := by linarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- Upper bound of the eigenvalue ratio: `4ε/(1 + √(1 − 4ε))² ≤ 4ε` (`0 ≤ b`). -/
@[tmio T, powerlib_foundation] theorem eigen_ratio_le {a b : ℝ} (hb : 0 ≤ b) :
    let ε := b / a ^ 2
    let s := Real.sqrt (1 - 4 * ε)
    4 * ε / (1 + s) ^ 2 ≤ 4 * ε := by
  intro ε s
  have hε : 0 ≤ ε := by positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hpos : 0 < 1 + s := by linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hε hs0, mul_nonneg hε (sq_nonneg s)]

/-- Fast eigenvalue bounds: `λ₋ = −(a/2)(1 + √(1 − 4ε)) ∈ [−a, −a/2]`
(`a > 0`, `0 ≤ b`, `4b ≤ a²`). -/
@[tmio T, powerlib_foundation] theorem eigen_fast_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hd : 4 * b ≤ a ^ 2) :
    let s := Real.sqrt (1 - 4 * (b / a ^ 2))
    (-a ≤ -(a / 2) * (1 + s)) ∧ -(a / 2) * (1 + s) ≤ -(a / 2) := by
  intro s
  have h1 : 0 ≤ 1 - 4 * (b / a ^ 2) := by
    rw [sub_nonneg, ← le_div_iff₀' (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by positivity)]
    linarith
  have hs : s ^ 2 = 1 - 4 * (b / a ^ 2) := Real.sq_sqrt h1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by nlinarith [div_nonneg hb (sq_nonneg a)]
  exact ⟨by nlinarith, by nlinarith⟩

/-- Slow eigenvalue bounds: `λ₊ = −(a/2)(1 − √(1 − 4ε)) ∈ [−2b/a, −b/a]`
(`a > 0`, `0 ≤ b`, `4b ≤ a²`). -/
@[tmio T, powerlib_foundation] theorem eigen_slow_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hd : 4 * b ≤ a ^ 2) :
    let s := Real.sqrt (1 - 4 * (b / a ^ 2))
    (-(2 * b / a) ≤ -(a / 2) * (1 - s)) ∧ -(a / 2) * (1 - s) ≤ -(b / a) := by
  intro s
  have h1 : 0 ≤ 1 - 4 * (b / a ^ 2) := by
    rw [sub_nonneg, ← le_div_iff₀' (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by positivity)]
    linarith
  have hs : s ^ 2 = 1 - 4 * (b / a ^ 2) := Real.sq_sqrt h1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by nlinarith [div_nonneg hb (sq_nonneg a)]
  have hkey : a / 2 * (1 - s) * (1 + s) = 2 * b / a := by
    have : (1 - s) * (1 + s) = 4 * (b / a ^ 2) := by nlinarith
    rw [mul_assoc, this]; field_simp; ring
  constructor
  · -- `a/2 (1 − s) = (2b/a)/(1 + s) ≤ 2b/a`
    have h2 : a / 2 * (1 - s) ≤ 2 * b / a := by
      have : 0 ≤ a / 2 * (1 - s) := by nlinarith
      nlinarith
    linarith
  · have h2 : b / a ≤ a / 2 * (1 - s) := by
      have h3 : (1 + s) ≤ 2 := by linarith
      have : 0 ≤ a / 2 * (1 - s) := by nlinarith
      have h4 : 2 * b / a ≤ a / 2 * (1 - s) * 2 := by
        rw [← hkey]; exact mul_le_mul_of_nonneg_left h3 this
      have : 2 * b / a = 2 * (b / a) := by ring
      linarith
    linarith

end Quadratic

/-! ## Real 2×2 matrices -/

section FinTwo

@[tmio T, powerlib_foundation] theorem det_characteristicMatrix_fin_two
    (A : Matrix (Fin 2) (Fin 2) ℝ) (s : ℂ) :
    (Linear.characteristicMatrix A s).det = s ^ 2 - (A.trace : ℂ) * s + (A.det : ℂ) := by
  simp only [Linear.characteristicMatrix, Matrix.det_fin_two, Matrix.trace_fin_two,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Complex.coe_algebraMap,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul]
  push_cast
  ring

/-- Routh–Hurwitz for real 2×2 matrices: `IsHurwitz A ↔ tr A < 0 ∧ 0 < det A`. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_fin_two_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    LinearSystems.IsHurwitz A ↔ A.trace < 0 ∧ 0 < A.det := by
  rw [← Linear.spectrallyStable_iff_isHurwitz]
  unfold Linear.SpectrallyStable
  simp only [det_characteristicMatrix_fin_two, sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg]
  rw [quadratic_roots_re_neg_iff, neg_pos]

/-- **A strict violation of the 2×2 Hurwitz conditions**, `0 < tr A` or `det A < 0`, gives a
characteristic root in the open right half plane (the generic witnesses
`exists_root_re_pos_of_trace_pos`, `exists_root_re_pos_of_det` with `(−1)² = 1`). -/
@[tmio T, powerlib_foundation] theorem exists_root_re_pos_of_violation_fin_two
    (A : Matrix (Fin 2) (Fin 2) ℝ) (h : 0 < A.trace ∨ A.det < 0) :
    ∃ s : ℂ, (Linear.characteristicMatrix A s).det = 0 ∧ 0 < s.re := by
  rcases h with h | h
  · exact exists_root_re_pos_of_trace_pos A h
  · exact exists_root_re_pos_of_det A (by rw [neg_one_sq, one_mul]; exact h)

@[tmio T, powerlib_foundation] theorem isHurwitz_fin_two_of_iff (a b c d : ℝ) :
    LinearSystems.IsHurwitz !![a, b; c, d] ↔ a + d < 0 ∧ 0 < a * d - b * c := by
  rw [isHurwitz_fin_two_iff, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]

/-- Routh–Hurwitz for a 2×2 matrix with characteristic polynomial `(a₂ s² + a₁ s + a₀) / a₂`,
`a₂ > 0`, given by its invariants `tr A = −a₁/a₂`, `det A = a₀/a₂`:
`IsHurwitz A ↔ 0 < a₁ ∧ 0 < a₀`. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_iff_of_coeffs_quadratic
    (A : Matrix (Fin 2) (Fin 2) ℝ) {a2 a1 a0 : ℝ} (h2 : 0 < a2) (htr : A.trace = -a1 / a2)
    (hdet : A.det = a0 / a2) : LinearSystems.IsHurwitz A ↔ 0 < a1 ∧ 0 < a0 := by
  rw [isHurwitz_fin_two_iff, htr, hdet, neg_div, neg_lt_zero, div_pos_iff_of_pos_right h2,
    div_pos_iff_of_pos_right h2]

/-- Companion form of `s ^ 2 + a1 * s + a0`: Hurwitz iff `0 < a0 ∧ 0 < a1`. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_companion_two_iff (a0 a1 : ℝ) :
    LinearSystems.IsHurwitz !![0, 1; -a0, -a1] ↔ 0 < a0 ∧ 0 < a1 := by
  rw [isHurwitz_fin_two_of_iff]
  constructor
  · rintro ⟨h1, h0⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by linarith, by linarith⟩

/-- The damping ratio `ζ = −tr A / (2 √det A)` of a real 2×2 matrix: for `det A > 0` its
characteristic polynomial is `s² + 2ζω_n s + ω_n²` with `ω_n = √det A`. Signed (negative for
`tr A > 0`); meaningful for a complex pair. -/
def dampingRatio (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := -A.trace / (2 * Real.sqrt A.det)

/-- The natural frequency `ω_n = √det A` of a real 2×2 matrix. -/
def naturalFrequency (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := Real.sqrt A.det

/-- `ω_n² = det A` (for `det A ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem naturalFrequency_sq (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hdet : 0 ≤ A.det) : naturalFrequency A ^ 2 = A.det :=
  Real.sq_sqrt hdet

/-- `2 ζ ω_n = −tr A` (for `det A > 0`). -/
@[tmio T, powerlib_foundation] theorem two_mul_dampingRatio_mul_naturalFrequency
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : 0 < A.det) :
    2 * dampingRatio A * naturalFrequency A = -A.trace := by
  have hω : naturalFrequency A ≠ 0 := (Real.sqrt_pos.mpr hdet).ne'
  rw [dampingRatio, ← naturalFrequency]
  field_simp

/-- Standard second-order form: for `det A > 0`,
`det (s • 1 − A) = s² + 2 ζ ω_n s + ω_n²` with `ζ = dampingRatio A`, `ω_n = naturalFrequency A`. -/
@[tmio T, powerlib_foundation] theorem det_characteristicMatrix_standard
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : 0 < A.det) (s : ℂ) :
    (Linear.characteristicMatrix A s).det = s ^ 2 +
      2 * (dampingRatio A : ℂ) * (naturalFrequency A : ℂ) * s + (naturalFrequency A : ℂ) ^ 2 := by
  have h2 := naturalFrequency_sq A hdet.le
  have h1 := two_mul_dampingRatio_mul_naturalFrequency A hdet
  have h1c := congrArg (fun x : ℝ => (x : ℂ)) h1
  have h2c := congrArg (fun x : ℝ => (x : ℂ)) h2
  push_cast at h1c h2c
  rw [det_characteristicMatrix_fin_two]
  linear_combination (-s) * h1c - h2c

/-- The damping ratio is invariant under a change of coordinates `A ↦ T A S`, `T S = S T = 1`
(trace and determinant are). -/
@[tmio T, powerlib_foundation] theorem dampingRatio_conj {T S : Matrix (Fin 2) (Fin 2) ℝ}
    (hTS : T * S = 1) (hST : S * T = 1) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    dampingRatio (T * A * S) = dampingRatio A := by
  rw [dampingRatio, dampingRatio, Matrix.det_conj_of_mul_eq_one hTS hST, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, hST, Matrix.one_mul]

/-! ### Discriminant and nilpotency -/

/-- All eigenvalues of a real 2×2 matrix are real iff `0 ≤ tr² − 4 det`. -/
@[tmio T, powerlib_foundation] theorem eigenvalues_real_iff_discriminant_nonneg
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 → A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v → μ.im = 0) ↔
      0 ≤ A.trace ^ 2 - 4 * A.det := by
  have hdisc : (-A.trace) ^ 2 - 4 * A.det = A.trace ^ 2 - 4 * A.det := by ring
  rw [← hdisc, ← quadratic_roots_real_iff]
  constructor
  · intro H s hs
    obtain ⟨v, hv, heig⟩ := Linear.exists_eigenvector_of_root
      (by
        rw [det_characteristicMatrix_fin_two, sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg]
        exact hs)
    exact H s v hv heig
  · intro H μ v hv heig
    have h := det_characteristicMatrix_eq_zero_of_eigenpair A hv heig
    rw [det_characteristicMatrix_fin_two, sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg] at h
    exact H μ h

/-- Cayley–Hamilton for 2×2 matrices. -/
@[tmio T, powerlib_foundation] theorem sq_eq_trace_smul_sub_det_smul_fin_two
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A ^ 2 = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.det_fin_two] <;> ring

@[tmio T, powerlib_foundation] theorem sq_eq_zero_iff_trace_det_eq_zero_fin_two
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A ^ 2 = 0 ↔ A.trace = 0 ∧ A.det = 0 := by
  constructor
  · intro h
    have hd : A.det = 0 := by
      have := congrArg Matrix.det h
      rw [Matrix.det_pow, Matrix.det_zero] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hCH := sq_eq_trace_smul_sub_det_smul_fin_two A
    rw [h, hd, zero_smul, sub_zero] at hCH
    have ht := congrArg Matrix.trace hCH
    rw [Matrix.trace_smul, Matrix.trace_zero, smul_eq_mul] at ht
    exact ⟨by nlinarith [sq_nonneg A.trace], hd⟩
  · rintro ⟨ht, hd⟩
    rw [sq_eq_trace_smul_sub_det_smul_fin_two, ht, hd, zero_smul, zero_smul, sub_zero]

@[tmio T, powerlib_foundation] theorem isNilpotent_iff_trace_det_eq_zero_fin_two
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    IsNilpotent A ↔ A.trace = 0 ∧ A.det = 0 := by
  constructor
  · intro h
    have ht : A.trace = 0 := (Matrix.isNilpotent_trace_of_isNilpotent h).eq_zero
    obtain ⟨k, hk⟩ := h
    have hd : A.det = 0 := by
      have := congrArg Matrix.det hk
      rw [Matrix.det_pow] at this
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [pow_zero] at hk
        exact absurd hk one_ne_zero
      · rw [Matrix.det_zero] at this
        exact pow_eq_zero_iff hk0.ne' |>.mp this
    exact ⟨ht, hd⟩
  · intro h
    exact ⟨2, (sq_eq_zero_iff_trace_det_eq_zero_fin_two A).2 h⟩

end FinTwo

/-! ## Semantic corollaries (linearization and linear fields)

These are generic semantic implications about an arbitrary caller-supplied field: foundation
results (Rules §3), not model-specific engineering conclusions. A model family that uses them
publishes its conclusions as connection statements (see
`theorem/GridTiedConverter/PLL/PIPLLFamily.lean`). -/

section Semantic

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Linearization at an equilibrium of a `C¹` field on `ℝ²`: a Jacobian with
`tr < 0` and `det > 0` gives local exponential stability (LeanForControl's
`hurwitz_linearization_locally_exponentially_stable`). -/
@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_of_jacobian_fin_two
    {f : ℝ² → ℝ²} {x_eq : ℝ²}
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A)
    (htr : A.trace < 0) (hdet : 0 < A.det) : LocallyExponentiallyStable f x_eq :=
  hurwitz_linearization_locally_exponentially_stable A hf heq hJac
    ((isHurwitz_fin_two_iff A).2 ⟨htr, hdet⟩)

/-- Two-state continuous-time linear field `x' = A (x - e)`: every attractive sentence of the
Flow semantics (in particular global exponential stability) holds at `e` iff
`tr A < 0 ∧ det A > 0` (the linear hub `Linear.holds_iff_isHurwitz`). -/
@[tmio T, powerlib_foundation] theorem holds_affine_fin_two_iff (A : Matrix (Fin 2) (Fin 2) ℝ) (e : ℝ²)
    {P : Flow.Property} (hP : P.Attractive) :
    P.holds (LinearSystems.affineLinearVectorField A e) e ↔ A.trace < 0 ∧ 0 < A.det :=
  (Linear.holds_iff_isHurwitz e hP).trans (isHurwitz_fin_two_iff A)

end Semantic

end powerlib.Criteria
