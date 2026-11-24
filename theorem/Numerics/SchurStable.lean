import theorem.Linear.Transfer

/-! # Schur stability of a real matrix and the signs of a cubic characteristic polynomial
(foundation)

A real square matrix is Schur stable when every root of its characteristic polynomial lies in the
open unit disk (`Numerics.SchurStable`, the discrete-time counterpart of
`Linear.SpectrallyStable`): the iteration `x⁺ = A x` decays. For a one-step method applied to a
linear field `ẋ = A x` the matrix is the step matrix, e.g. `I + h A` for explicit Euler. A monic
real cubic takes the value zero to the right of every point where it is nonpositive and to the
left of every point where it is nonnegative (`exists_cubic_root_ge`, `exists_cubic_root_le`, the
intermediate value theorem with a Cauchy bound). Hence a Schur stable matrix whose characteristic
determinant on the real axis is a monic real cubic `p` has `p > 0` on `[1, ∞)` and `p < 0` on
`(−∞, −1]` (`SchurStable.cubic_pos`, `SchurStable.cubic_neg`): the necessary conditions
`p(1) > 0`, `p(−1) < 0` of the Jury test, extended to every real point outside the open disk. A
characteristic root on or outside the unit circle refutes Schur stability
(`not_schurStable_of_det_eq_zero`).

Scope.
* Generic: arbitrary real square matrices over a finite index type, arbitrary real cubic
  coefficients; static algebra, no model, no time. The instances (the step matrix of the
  explicit Euler discretization of a linearized grid-forming port) are in
  `theorem/GridTiedConverter/GFM/Discrete/StepAwareEuler.lean`.

Source: the characteristic matrix of `theorem/Linear/Transfer.lean`
(`Linear.characteristicMatrix`, `Linear.SpectrallyStable`); Jury, *Theory and Application of the
z-Transform Method* (1964) (the necessary conditions `p(1) > 0`, `(−1)ⁿ p(−1) > 0` of the
stability test); the intermediate value theorem (`intermediate_value_Icc`).

Results.
* `Numerics.SchurStable A`: every root of `det(z I − A)` has `‖z‖ < 1`.
* `exists_cubic_root_ge`, `exists_cubic_root_le`: a monic real cubic nonpositive (nonnegative)
  at `x₀` vanishes at some `x ≥ x₀` (`x ≤ x₀`).
* `SchurStable.cubic_pos`, `SchurStable.cubic_neg`: the signs of a monic cubic characteristic
  polynomial of a Schur stable matrix outside `(−1, 1)`.
* `not_schurStable_of_det_eq_zero`: a characteristic root `z` with `1 ≤ ‖z‖` refutes Schur
  stability.
-/

noncomputable section

namespace powerlib.Numerics

open Set

/-- A real square matrix is **Schur stable** when every root of its characteristic polynomial
lies in the open unit disk. -/
def SchurStable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ z : ℂ, (Linear.characteristicMatrix A z).det = 0 → ‖z‖ < 1

/-- **A monic real cubic nonpositive at `x₀` vanishes at some `x ≥ x₀`**: at `x₀ + R`, with the
Cauchy bound `R = 1 + |a₂| + |a₁| + |a₀|` of the cubic `y³ + a₂ y² + a₁ y + a₀` shifted to
`x₀`, it is at least `R² > 0` (intermediate value theorem). -/
@[tmio T, powerlib_foundation] theorem exists_cubic_root_ge {c₂ c₁ c₀ x₀ : ℝ}
    (h : x₀ ^ 3 + c₂ * x₀ ^ 2 + c₁ * x₀ + c₀ ≤ 0) :
    ∃ x, x₀ ≤ x ∧ x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ = 0 := by
  set a₂ := 3 * x₀ + c₂
  set a₁ := 3 * x₀ ^ 2 + 2 * c₂ * x₀ + c₁
  set a₀ := x₀ ^ 3 + c₂ * x₀ ^ 2 + c₁ * x₀ + c₀ with ha₀
  set R := 1 + |a₂| + |a₁| + |a₀| with hRdef
  have hR : 1 ≤ R := by
    have := abs_nonneg a₂
    have := abs_nonneg a₁
    have := abs_nonneg a₀
    linarith
  have hshift : (x₀ + R) ^ 3 + c₂ * (x₀ + R) ^ 2 + c₁ * (x₀ + R) + c₀ =
      R ^ 3 + a₂ * R ^ 2 + a₁ * R + a₀ := by
    simp only [a₂, a₁, a₀]
    ring
  have hpos : 0 ≤ (x₀ + R) ^ 3 + c₂ * (x₀ + R) ^ 2 + c₁ * (x₀ + R) + c₀ := by
    rw [hshift]
    have e1 : -|a₂| * R ^ 2 ≤ a₂ * R ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_abs_le a₂) (sq_nonneg R)
    have e2 : -|a₁| * R ≤ a₁ * R := mul_le_mul_of_nonneg_right (neg_abs_le a₁) (by linarith)
    have e3 : |a₁| * R ≤ |a₁| * R ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg a₁)
    have e4 : |a₀| ≤ |a₀| * R ^ 2 := le_mul_of_one_le_right (abs_nonneg a₀) (by nlinarith)
    have e5 : R ^ 3 - (|a₂| + |a₁| + |a₀|) * R ^ 2 = R ^ 2 := by
      rw [hRdef]
      ring
    linarith [neg_abs_le a₀, sq_nonneg R]
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀)
      (Icc x₀ (x₀ + R)) := by fun_prop
  obtain ⟨x, hx, hx0⟩ :=
    intermediate_value_Icc (by linarith : x₀ ≤ x₀ + R) hcont ⟨h, hpos⟩
  exact ⟨x, hx.1, hx0⟩

/-- **A monic real cubic nonnegative at `x₀` vanishes at some `x ≤ x₀`** (`exists_cubic_root_ge`
for `−p(−x)`). -/
@[tmio T, powerlib_foundation] theorem exists_cubic_root_le {c₂ c₁ c₀ x₀ : ℝ}
    (h : 0 ≤ x₀ ^ 3 + c₂ * x₀ ^ 2 + c₁ * x₀ + c₀) :
    ∃ x, x ≤ x₀ ∧ x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ = 0 := by
  obtain ⟨y, hy, hy0⟩ := exists_cubic_root_ge (c₂ := -c₂) (c₁ := c₁) (c₀ := -c₀) (x₀ := -x₀)
    (by nlinarith)
  exact ⟨-y, by linarith, by linear_combination -hy0⟩

/-- **A characteristic root on or outside the unit circle refutes Schur stability.** -/
@[tmio T, powerlib_foundation] theorem not_schurStable_of_det_eq_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} {z : ℂ} (hz : 1 ≤ ‖z‖)
    (h0 : (Linear.characteristicMatrix A z).det = 0) : ¬ SchurStable A :=
  fun hA => (hA z h0).not_ge hz

/-- **The characteristic cubic of a Schur stable matrix is positive on `[1, ∞)`**: if
`det(r I − A) = r³ + c₂ r² + c₁ r + c₀` on the real axis and `p(x) ≤ 0` at some `x ≥ 1`, the cubic
has a real root `r ≥ x ≥ 1` (`exists_cubic_root_ge`), a characteristic root outside the open
disk. -/
@[tmio T, powerlib_foundation] theorem SchurStable.cubic_pos {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : SchurStable A) {c₂ c₁ c₀ : ℝ}
    (hp : ∀ r : ℝ, (Linear.characteristicMatrix A r).det =
      ((r ^ 3 + c₂ * r ^ 2 + c₁ * r + c₀ : ℝ) : ℂ)) {x : ℝ} (hx : 1 ≤ x) :
    0 < x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ := by
  refine lt_of_not_ge fun hle => ?_
  obtain ⟨r, hr, hr0⟩ := exists_cubic_root_ge hle
  refine not_schurStable_of_det_eq_zero (z := r) ?_ (by rw [hp, hr0, Complex.ofReal_zero]) hA
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-- **The characteristic cubic of a Schur stable matrix is negative on `(−∞, −1]`**
(`exists_cubic_root_le`). -/
@[tmio T, powerlib_foundation] theorem SchurStable.cubic_neg {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : SchurStable A) {c₂ c₁ c₀ : ℝ}
    (hp : ∀ r : ℝ, (Linear.characteristicMatrix A r).det =
      ((r ^ 3 + c₂ * r ^ 2 + c₁ * r + c₀ : ℝ) : ℂ)) {x : ℝ} (hx : x ≤ -1) :
    x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ < 0 := by
  refine lt_of_not_ge fun hle => ?_
  obtain ⟨r, hr, hr0⟩ := exists_cubic_root_le hle
  refine not_schurStable_of_det_eq_zero (z := r) ?_ (by rw [hp, hr0, Complex.ofReal_zero]) hA
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  linarith

end powerlib.Numerics
