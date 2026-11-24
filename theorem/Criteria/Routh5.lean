import theorem.Criteria.Routh4
import theorem.Criteria.RouthHurwitz

/-! # Routh–Hurwitz criterion for monic real quintics

The degree-five Routh–Hurwitz criterion in both directions, its instability witnesses and its
matrix form in any state dimension.

Scope.
* No model family is defined or fixed here. Every statement is static algebra about real
  polynomials and matrices, so all of them are foundation results (Rules §3). Model families that
  use the criterion publish their engineering conclusions as connection statements (pattern:
  `theorem/GridTiedConverter/GFM/Line/VSMLPF.lean`).

Source: the Routh–Hurwitz criterion (A. Hurwitz, *Math. Ann.* 46 (1895); F. R. Gantmacher,
*The Theory of Matrices*, vol. 2, Ch. XV), degree five, with the Routh reduction step to degree
four (`theorem/Criteria/RouthHurwitz.lean`, `theorem/Criteria/Routh4.lean`) and Orlando's formula
for the last Hurwitz determinant (shared criteria interface for the work-sync formalization).

Results.
* Hurwitz determinants of the monic quintic `s⁵ + a₄ s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀`: `Δ₁ = a₄`,
  `Δ₂ = a₄ a₃ − a₂` (`quinticHurwitzDet2`), `Δ₃ = a₂ Δ₂ − a₄ (a₄ a₁ − a₀)` (`quinticHurwitzDet3`),
  `Δ₄ = a₁ Δ₃ − a₀ (a₃ Δ₂ − a₄ a₁ + a₀)` (`quinticHurwitzDet4`), `Δ₅ = a₀ Δ₄`
  (`quinticHurwitzDet5`): the leading principal minors of the Hurwitz matrix
  `[[a₄, a₂, a₀, 0, 0], [1, a₃, a₁, 0, 0], [0, a₄, a₂, a₀, 0], [0, 1, a₃, a₁, 0],
  [0, 0, a₄, a₂, a₀]]` (`quinticHurwitzDet_eq_det`). `QuinticRouth` is the condition list
  `Δ₁, …, Δ₅ > 0` and `QuinticRouthViolation` its strict violation (a negative coefficient or a
  negative `Δ₂`, `Δ₃`, `Δ₄`).
* **Criterion** (`quintic_hurwitz_iff`): every complex root has negative real part iff
  `Δ₁, …, Δ₅ > 0`. Sufficient direction: `quintic_roots_re_neg_of`; necessary direction:
  `quintic_routh_of_roots_re_neg`.
* Routh step (`quintic_eq_routhStep`): for `a₄ ≠ 0`,
  `p(s) = (s + a₄) u(s) + a₄ v(s)` with `u = s⁴ + (a₂/a₄) s² + a₀/a₄` and
  `v = (Δ₂/a₄²) s³ + ((a₄ a₁ − a₀)/a₄²) s`, the even and odd parts of the Routh-reduced quartic
  `u + v`, whose second and third Hurwitz determinants are `Δ₃/a₄³` and `Δ₄/a₄⁴`
  (`quintic_routhStep_hurwitzDet`).
* Factorization: every real quintic has a real root (`exists_quintic_real_root`, odd degree) and
  is `(s + r)(s² + b s + c)(s² + p s + q)` over ℝ (`quintic_factor`, `quintic_eq_mul`); in these
  factors `Δ₄ = b p (r² + b r + c)(r² + p r + q)((b + p)(b q + c p) + (c − q)²)`
  (`quinticHurwitzDet4_eq_factors`, the factor form of Orlando's formula `Δ₄ = ∏_{i<j} (z_i + z_j)`
  over the roots).
* Instability: if every root has nonpositive real part, every coefficient and `Δ₂`, `Δ₃`, `Δ₄`
  are nonnegative (`quintic_coeffs_nonneg_of_roots_re_nonpos`), so a strict violation gives a
  root with positive real part (`exists_quintic_root_re_pos_of_violation`); the Routh conditions
  exclude their violation (`not_quinticRouthViolation_of_quinticRouth`).
* Matrix interface for any state dimension: if `det (s • 1 - A)` is identified with the quintic
  for every `s`, `IsHurwitz A` iff `QuinticRouth`
  (`isHurwitz_iff_of_det_characteristicMatrix_quintic`, through the generic interface
  `Criteria.isHurwitz_iff_of_det_characteristicMatrix`), and a strict violation gives an
  eigenpair with positive real part
  (`exists_eigenvalue_re_pos_of_det_characteristicMatrix_quintic_violation`, in the shape of
  `unstable_of_exists_complex_eigenvalue_re_pos`).

Proof of the criterion: one Routh step (`Criteria.hurwitz_iff_routhStep`,
`theorem/Criteria/RouthHurwitz.lean`) reduces the quintic to `a₄` times the quartic
`s⁴ + c₃ s³ + c₂ s² + c₁ s + c₀` of `quintic_routhStep_hurwitzDet`, decided by
`quartic_hurwitz_iff`; its conditions are `Δ₁, …, Δ₅ > 0` by `c₃ c₂ − c₁ = Δ₃/a₄³` and
`c₃ c₂ c₁ − c₁² − c₃² c₀ = Δ₄/a₄⁴`. The factorization serves the closed-half-plane statement:
factor the quintic as `(s + r)(s² + b s + c)(s² + p s + q)`; nonpositive real parts give
nonnegative `r, b, c, p, q`, and in these factors `Δ₂`, `Δ₃`, `Δ₄` are sums of products of
nonnegative terms (`Δ₃` up to the square `b p (c − q)²`).
-/

noncomputable section
namespace powerlib.Criteria
open Matrix Polynomial

/-! ## Hurwitz determinants -/

section Determinants

/-- Second Hurwitz determinant of `s⁵ + a₄ s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀`: `Δ₂ = a₄ a₃ − a₂`. -/
def quinticHurwitzDet2 (a4 a3 a2 : ℝ) : ℝ := a4 * a3 - a2

/-- Third Hurwitz determinant of the monic quintic: `Δ₃ = a₂ Δ₂ − a₄ (a₄ a₁ − a₀)`. -/
def quinticHurwitzDet3 (a4 a3 a2 a1 a0 : ℝ) : ℝ :=
  a2 * quinticHurwitzDet2 a4 a3 a2 - a4 * (a4 * a1 - a0)

/-- Fourth Hurwitz determinant of the monic quintic: `Δ₄ = a₁ Δ₃ − a₀ (a₃ Δ₂ − a₄ a₁ + a₀)`. -/
def quinticHurwitzDet4 (a4 a3 a2 a1 a0 : ℝ) : ℝ :=
  a1 * quinticHurwitzDet3 a4 a3 a2 a1 a0 -
    a0 * (a3 * quinticHurwitzDet2 a4 a3 a2 - a4 * a1 + a0)

/-- Fifth Hurwitz determinant of the monic quintic: `Δ₅ = a₀ Δ₄`. -/
def quinticHurwitzDet5 (a4 a3 a2 a1 a0 : ℝ) : ℝ := a0 * quinticHurwitzDet4 a4 a3 a2 a1 a0

/-- The Hurwitz determinants are the leading principal minors of the Hurwitz matrix of the monic
quintic (`Δ₁ = a₄` is its corner entry). -/
@[tmio T, powerlib_foundation] theorem quinticHurwitzDet_eq_det (a4 a3 a2 a1 a0 : ℝ) :
    (!![a4, a2; 1, a3] : Matrix (Fin 2) (Fin 2) ℝ).det = quinticHurwitzDet2 a4 a3 a2 ∧
      (!![a4, a2, a0; 1, a3, a1; 0, a4, a2] : Matrix (Fin 3) (Fin 3) ℝ).det =
        quinticHurwitzDet3 a4 a3 a2 a1 a0 ∧
      (!![a4, a2, a0, 0; 1, a3, a1, 0; 0, a4, a2, a0; 0, 1, a3, a1] :
          Matrix (Fin 4) (Fin 4) ℝ).det = quinticHurwitzDet4 a4 a3 a2 a1 a0 ∧
      (!![a4, a2, a0, 0, 0; 1, a3, a1, 0, 0; 0, a4, a2, a0, 0; 0, 1, a3, a1, 0;
          0, 0, a4, a2, a0] : Matrix (Fin 5) (Fin 5) ℝ).det =
        quinticHurwitzDet5 a4 a3 a2 a1 a0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; simp only [quinticHurwitzDet2]; ring
  · rw [Matrix.det_fin_three]
    simp [quinticHurwitzDet3, quinticHurwitzDet2]; ring
  · rw [det_fin_four]
    simp [quinticHurwitzDet4, quinticHurwitzDet3, quinticHurwitzDet2]; ring
  · simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.submatrix_apply]
    simp [Fin.succAbove, Fin.lt_def, quinticHurwitzDet5, quinticHurwitzDet4, quinticHurwitzDet3,
      quinticHurwitzDet2]
    ring

/-- The quintic Routh–Hurwitz conditions: the Hurwitz determinants `Δ₁ = a₄, Δ₂, …, Δ₅` are
positive. -/
abbrev QuinticRouth (a4 a3 a2 a1 a0 : ℝ) : Prop :=
  0 < a4 ∧ 0 < quinticHurwitzDet2 a4 a3 a2 ∧ 0 < quinticHurwitzDet3 a4 a3 a2 a1 a0 ∧
    0 < quinticHurwitzDet4 a4 a3 a2 a1 a0 ∧ 0 < quinticHurwitzDet5 a4 a3 a2 a1 a0

/-- A strict violation of the quintic Routh–Hurwitz conditions: a negative coefficient or a
negative Hurwitz determinant `Δ₂`, `Δ₃`, `Δ₄` (`Δ₁ = a₄`; `Δ₅ = a₀ Δ₄ < 0` needs `a₀ < 0` or
`Δ₄ < 0`). -/
abbrev QuinticRouthViolation (a4 a3 a2 a1 a0 : ℝ) : Prop :=
  a4 < 0 ∨ a3 < 0 ∨ a2 < 0 ∨ a1 < 0 ∨ a0 < 0 ∨ quinticHurwitzDet2 a4 a3 a2 < 0 ∨
    quinticHurwitzDet3 a4 a3 a2 a1 a0 < 0 ∨ quinticHurwitzDet4 a4 a3 a2 a1 a0 < 0

end Determinants

/-! ## Monic real quintics -/

section Quintic

/-! ### Sufficient direction: the Routh step -/

/-- **Routh step.** For `a₄ ≠ 0` the quintic is `(s + a₄) u + a₄ v` with
`u = s⁴ + (a₂/a₄) s² + a₀/a₄`, `v = (Δ₂/a₄²) s³ + ((a₄ a₁ − a₀)/a₄²) s` the even and odd parts
of the Routh-reduced quartic `u + v`. -/
@[tmio T, powerlib_foundation] theorem quintic_eq_routhStep {a4 a3 a2 a1 a0 : ℝ} (h4 : a4 ≠ 0)
    (s : ℂ) :
    s ^ 5 + (a4 : ℂ) * s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) =
      (s + a4) * (s ^ 4 + ((a2 / a4 : ℝ) : ℂ) * s ^ 2 + ((a0 / a4 : ℝ) : ℂ)) +
        a4 * (((quinticHurwitzDet2 a4 a3 a2 / a4 ^ 2 : ℝ) : ℂ) * s ^ 3 +
          (((a4 * a1 - a0) / a4 ^ 2 : ℝ) : ℂ) * s) := by
  have h4' : (a4 : ℂ) ≠ 0 := by exact_mod_cast h4
  simp only [quinticHurwitzDet2]
  push_cast
  field_simp
  ring

/-- The Hurwitz determinants of the Routh-reduced quartic `s⁴ + c₃ s³ + c₂ s² + c₁ s + c₀`,
`c₃ = Δ₂/a₄²`, `c₂ = a₂/a₄`, `c₁ = (a₄ a₁ − a₀)/a₄²`, `c₀ = a₀/a₄`: `c₃ c₂ − c₁ = Δ₃/a₄³` and
`c₃ c₂ c₁ − c₁² − c₃² c₀ = Δ₄/a₄⁴`. -/
@[tmio T, powerlib_foundation] theorem quintic_routhStep_hurwitzDet {a4 a3 a2 a1 a0 : ℝ}
    (h4 : a4 ≠ 0) :
    quinticHurwitzDet2 a4 a3 a2 / a4 ^ 2 * (a2 / a4) - (a4 * a1 - a0) / a4 ^ 2 =
        quinticHurwitzDet3 a4 a3 a2 a1 a0 / a4 ^ 3 ∧
      quinticHurwitzDet2 a4 a3 a2 / a4 ^ 2 * (a2 / a4) * ((a4 * a1 - a0) / a4 ^ 2) -
          ((a4 * a1 - a0) / a4 ^ 2) ^ 2 - (quinticHurwitzDet2 a4 a3 a2 / a4 ^ 2) ^ 2 * (a0 / a4) =
        quinticHurwitzDet4 a4 a3 a2 a1 a0 / a4 ^ 4 := by
  simp only [quinticHurwitzDet4, quinticHurwitzDet3, quinticHurwitzDet2]
  constructor
  · field_simp
  · field_simp; ring

/-- **Routh–Hurwitz, degree five, both directions**: every complex root of the monic real quintic
has negative real part iff its Hurwitz determinants `Δ₁, …, Δ₅` are positive. One Routh step
(`Criteria.hurwitz_iff_routhStep`) gives `a₄` times the quartic `s⁴ + c₃ s³ + c₂ s² + c₁ s + c₀`
of `quintic_routhStep_hurwitzDet`, decided by `quartic_hurwitz_iff`. -/
@[tmio T, powerlib_foundation] theorem quintic_hurwitz_iff (a4 a3 a2 a1 a0 : ℝ) :
    (∀ s : ℂ, s ^ 5 + (a4 : ℂ) * s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 +
      (a1 : ℂ) * s + (a0 : ℂ) = 0 → s.re < 0) ↔ QuinticRouth a4 a3 a2 a1 a0 := by
  set f : ℝ[X] := X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 with hf
  have hd : f.natDegree = 5 := by rw [hf]; compute_degree!
  have hm : f.Monic := by rw [hf]; monicity!
  have hnc : f.nextCoeff = a4 := by
    rw [nextCoeff_of_natDegree_pos (by rw [hd]; norm_num), hd]
    simp [hf, coeff_X_pow]
  have hev : ∀ s : ℂ, aeval s f = s ^ 5 + (a4 : ℂ) * s ^ 4 + (a3 : ℂ) * s ^ 3 +
      (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) := fun s => by simp [hf]
  have hstep := hurwitz_iff_routhStep (p := f) (by rw [hd]; norm_num)
    (by rw [hm.leadingCoeff]; exact one_pos)
  simp only [hev, hnc] at hstep
  rw [hstep]
  by_cases h4 : 0 < a4
  swap
  · simp only [h4, false_and, QuinticRouth]
  have h4' : (a4 : ℂ) ≠ 0 := by exact_mod_cast h4.ne'
  have hq : ∀ s : ℂ, aeval s (routhStep f) = (a4 : ℂ) * (s ^ 4 +
      ((quinticHurwitzDet2 a4 a3 a2 / a4 ^ 2 : ℝ) : ℂ) * s ^ 3 + ((a2 / a4 : ℝ) : ℂ) * s ^ 2 +
        (((a4 * a1 - a0) / a4 ^ 2 : ℝ) : ℂ) * s + ((a0 / a4 : ℝ) : ℂ)) := by
    intro s
    rw [aeval_routhStep_eq, hm.leadingCoeff, hnc, hd, hev, hev]
    simp only [quinticHurwitzDet2]
    push_cast
    field_simp
    ring
  rw [show (∀ s : ℂ, aeval s (routhStep f) = 0 → s.re < 0) ↔ ∀ s : ℂ, s ^ 4 +
      ((quinticHurwitzDet2 a4 a3 a2 / a4 ^ 2 : ℝ) : ℂ) * s ^ 3 + ((a2 / a4 : ℝ) : ℂ) * s ^ 2 +
        (((a4 * a1 - a0) / a4 ^ 2 : ℝ) : ℂ) * s + ((a0 / a4 : ℝ) : ℂ) = 0 → s.re < 0 from
    forall_congr' fun s => imp_congr_left (by rw [hq, mul_eq_zero, or_iff_right h4']),
    quartic_hurwitz_iff]
  obtain ⟨g2, g3⟩ := quintic_routhStep_hurwitzDet (a3 := a3) (a2 := a2) (a1 := a1) (a0 := a0)
    h4.ne'
  simp only [h4, true_and]
  generalize hc3 : quinticHurwitzDet2 a4 a3 a2 / a4 ^ 2 = c3 at g2 g3 ⊢
  generalize hc2 : a2 / a4 = c2 at g2 g3 ⊢
  generalize hc1 : (a4 * a1 - a0) / a4 ^ 2 = c1 at g2 g3 ⊢
  generalize hc0 : a0 / a4 = c0 at g3 ⊢
  have e1 : c1 * (c3 * c2 - c1) = (c3 * c2 * c1 - c1 ^ 2 - c3 ^ 2 * c0) + c3 ^ 2 * c0 := by ring
  constructor
  · rintro ⟨k3, k1, k0, kg⟩
    have d2 : 0 < quinticHurwitzDet2 a4 a3 a2 :=
      (div_pos_iff_of_pos_right (pow_pos h4 2)).mp (hc3 ▸ k3)
    have d4 : 0 < quinticHurwitzDet4 a4 a3 a2 a1 a0 :=
      (div_pos_iff_of_pos_right (pow_pos h4 4)).mp (by rw [← g3]; linarith)
    have d0 : 0 < a0 := (div_pos_iff_of_pos_right h4).mp (hc0 ▸ k0)
    have d3 : 0 < quinticHurwitzDet3 a4 a3 a2 a1 a0 := by
      have : 0 < c1 * (c3 * c2 - c1) := by rw [e1]; nlinarith [sq_nonneg c3]
      exact (div_pos_iff_of_pos_right (pow_pos h4 3)).mp (g2 ▸ pos_of_mul_pos_right this k1.le)
    exact ⟨h4, d2, d3, d4, mul_pos d0 d4⟩
  · rintro ⟨-, d2, d3, d4, d5⟩
    have d0 : 0 < a0 := by
      by_contra h0
      push Not at h0
      have : quinticHurwitzDet5 a4 a3 a2 a1 a0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 d4.le
      linarith
    have k3 : 0 < c3 := hc3 ▸ div_pos d2 (pow_pos h4 2)
    have k0 : 0 < c0 := hc0 ▸ div_pos d0 h4
    have kg : 0 < c3 * c2 * c1 - c1 ^ 2 - c3 ^ 2 * c0 := by rw [g3]; positivity
    have kd : 0 < c3 * c2 - c1 := by rw [g2]; positivity
    have k1 : 0 < c1 := pos_of_mul_pos_left (by rw [e1]; positivity) kd.le
    exact ⟨k3, k1, k0, by linarith⟩

/-- **Routh–Hurwitz (sufficient), degree five.** Positive Hurwitz determinants place every
complex root in the open left half plane. -/
@[tmio T, powerlib_foundation] theorem quintic_roots_re_neg_of {a4 a3 a2 a1 a0 : ℝ}
    (h : QuinticRouth a4 a3 a2 a1 a0) (s : ℂ)
    (hs : s ^ 5 + (a4 : ℂ) * s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s +
      (a0 : ℂ) = 0) :
    s.re < 0 :=
  (quintic_hurwitz_iff a4 a3 a2 a1 a0).mpr h s hs

/-! ### Factorization and the necessary direction -/

/-- Every monic real quintic has a real root (odd degree, `Criteria.exists_root_of_odd_natDegree`).
-/
@[tmio T, powerlib_foundation] theorem exists_quintic_real_root (a4 a3 a2 a1 a0 : ℝ) :
    ∃ x : ℝ, x ^ 5 + a4 * x ^ 4 + a3 * x ^ 3 + a2 * x ^ 2 + a1 * x + a0 = 0 := by
  set f : ℝ[X] := X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0
  have hm : f.Monic := by simp only [f]; monicity!
  have hd : f.natDegree = 5 := by simp only [f]; compute_degree!
  obtain ⟨x, hx⟩ := exists_root_of_odd_natDegree hm (by rw [hd]; decide)
  exact ⟨x, by simpa [f] using hx⟩

/-- Every monic real quintic is a product `(s + r)(s² + b s + c)(s² + p s + q)` of monic real
factors, in coefficient form. -/
@[tmio T, powerlib_foundation] theorem quintic_factor (a4 a3 a2 a1 a0 : ℝ) :
    ∃ r b c p q : ℝ, a4 = r + (b + p) ∧ a3 = c + q + b * p + r * (b + p) ∧
      a2 = b * q + c * p + r * (c + q + b * p) ∧ a1 = c * q + r * (b * q + c * p) ∧
      a0 = r * (c * q) := by
  obtain ⟨x, hx⟩ := exists_quintic_real_root a4 a3 a2 a1 a0
  obtain ⟨b, c, p, q, e3, e2, e1, e0⟩ := quartic_factor_quadratics (a4 + x)
    (a3 + x * (a4 + x)) (a2 + x * (a3 + x * (a4 + x))) (a1 + x * (a2 + x * (a3 + x * (a4 + x))))
  exact ⟨-x, b, c, p, q, by linear_combination e3, by linear_combination e2 - x * e3,
    by linear_combination e1 - x * e2, by linear_combination e0 - x * e1,
    by linear_combination hx - x * e0⟩

/-- The quintic in factored form. -/
@[tmio T, powerlib_foundation] theorem quintic_eq_mul {a4 a3 a2 a1 a0 r b c p q : ℝ}
    (h4 : a4 = r + (b + p)) (h3 : a3 = c + q + b * p + r * (b + p))
    (h2 : a2 = b * q + c * p + r * (c + q + b * p)) (h1 : a1 = c * q + r * (b * q + c * p))
    (h0 : a0 = r * (c * q)) (s : ℂ) :
    s ^ 5 + (a4 : ℂ) * s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) =
      (s + r) * ((s ^ 2 + (b : ℂ) * s + (c : ℂ)) * (s ^ 2 + (p : ℂ) * s + (q : ℂ))) := by
  subst h4 h3 h2 h1 h0
  push_cast
  ring

/-- **Orlando's formula**, degree five: in the factors `(s + r)(s² + b s + c)(s² + p s + q)`,
`Δ₄ = b p (r² + b r + c)(r² + p r + q)((b + p)(b q + c p) + (c − q)²)`. -/
@[tmio T, powerlib_foundation] theorem quinticHurwitzDet4_eq_factors
    {a4 a3 a2 a1 a0 r b c p q : ℝ}
    (h4 : a4 = r + (b + p)) (h3 : a3 = c + q + b * p + r * (b + p))
    (h2 : a2 = b * q + c * p + r * (c + q + b * p)) (h1 : a1 = c * q + r * (b * q + c * p))
    (h0 : a0 = r * (c * q)) :
    quinticHurwitzDet4 a4 a3 a2 a1 a0 = b * p * (r ^ 2 + b * r + c) * (r ^ 2 + p * r + q) *
      ((b + p) * (b * q + c * p) + (c - q) ^ 2) := by
  subst h4 h3 h2 h1 h0
  simp only [quinticHurwitzDet4, quinticHurwitzDet3, quinticHurwitzDet2]
  ring

/-- `Δ₂` and `Δ₃` in the factors: `Δ₂ = (r + b)(r + p)(b + p) + b c + p q` and
`Δ₃ = b p ((b + p)(b q + c p) + (c − q)²) + r T` with `T` a polynomial with nonnegative
coefficients. -/
@[tmio T, powerlib_foundation] private theorem quinticHurwitzDet23_eq_factors
    {a4 a3 a2 a1 a0 r b c p q : ℝ}
    (h4 : a4 = r + (b + p)) (h3 : a3 = c + q + b * p + r * (b + p))
    (h2 : a2 = b * q + c * p + r * (c + q + b * p)) (h1 : a1 = c * q + r * (b * q + c * p))
    (h0 : a0 = r * (c * q)) :
    quinticHurwitzDet2 a4 a3 a2 = (r + b) * (r + p) * (b + p) + b * c + p * q ∧
      quinticHurwitzDet3 a4 a3 a2 a1 a0 = b * p * ((b + p) * (b * q + c * p) + (c - q) ^ 2) +
        r * (r ^ 2 * (b ^ 2 * p + b * c + b * p ^ 2 + p * q) +
          r * (b ^ 3 * p + b ^ 2 * c + 2 * b ^ 2 * p ^ 2 + b * c * p + b * p ^ 3 + b * p * q +
            p ^ 2 * q) +
          (b ^ 3 * p ^ 2 + 2 * b ^ 2 * c * p + b ^ 2 * p ^ 3 + b ^ 2 * p * q + b * c ^ 2 +
            b * c * p ^ 2 + 2 * b * p ^ 2 * q + p * q ^ 2)) := by
  subst h4 h3 h2 h1 h0
  simp only [quinticHurwitzDet3, quinticHurwitzDet2]
  constructor <;> ring

/-- **Routh–Hurwitz (necessary), degree five.** If every complex root has negative real part,
the Hurwitz determinants are positive. -/
@[tmio T, powerlib_foundation] theorem quintic_routh_of_roots_re_neg {a4 a3 a2 a1 a0 : ℝ}
    (H : ∀ s : ℂ, s ^ 5 + (a4 : ℂ) * s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 +
      (a1 : ℂ) * s + (a0 : ℂ) = 0 → s.re < 0) :
    QuinticRouth a4 a3 a2 a1 a0 :=
  (quintic_hurwitz_iff a4 a3 a2 a1 a0).mp H

/-! ### Instability -/

/-- A monic real quadratic whose roots have nonpositive real part has nonnegative coefficients
(the quadratic witnesses `exists_quadratic_root_re_pos_of_linear_neg`,
`exists_quadratic_root_pos_of_const_neg`). -/
@[tmio T, powerlib_foundation] private theorem quadratic_coeffs_nonneg {a1 a0 : ℝ}
    (H : ∀ s : ℂ, s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 → s.re ≤ 0) : 0 ≤ a1 ∧ 0 ≤ a0 := by
  constructor
  · by_contra h
    obtain ⟨s, hs, hre⟩ := exists_quadratic_root_re_pos_of_linear_neg (a0 := a0) (not_le.mp h)
    exact absurd (H s hs) (not_le.mpr hre)
  · by_contra h
    obtain ⟨r, hr, hroot⟩ := exists_quadratic_root_pos_of_const_neg (a1 := a1) (not_le.mp h)
    have := H r (quadratic_real_root_complex hroot)
    rw [Complex.ofReal_re] at this
    linarith

/-- Closed half plane: if every root of the monic real quintic has nonpositive real part, every
coefficient and the Hurwitz determinants `Δ₂`, `Δ₃`, `Δ₄` are nonnegative. -/
@[tmio T, powerlib_foundation] theorem quintic_coeffs_nonneg_of_roots_re_nonpos
    {a4 a3 a2 a1 a0 : ℝ}
    (H : ∀ s : ℂ, s ^ 5 + (a4 : ℂ) * s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 +
      (a1 : ℂ) * s + (a0 : ℂ) = 0 → s.re ≤ 0) :
    0 ≤ a4 ∧ 0 ≤ a3 ∧ 0 ≤ a2 ∧ 0 ≤ a1 ∧ 0 ≤ a0 ∧ 0 ≤ quinticHurwitzDet2 a4 a3 a2 ∧
      0 ≤ quinticHurwitzDet3 a4 a3 a2 a1 a0 ∧ 0 ≤ quinticHurwitzDet4 a4 a3 a2 a1 a0 := by
  obtain ⟨r, b, c, p, q, h4, h3, h2, h1, h0⟩ := quintic_factor a4 a3 a2 a1 a0
  have hmul := quintic_eq_mul h4 h3 h2 h1 h0
  have hr : 0 ≤ r := by
    have := H (-(r : ℂ)) (by rw [hmul]; ring)
    simpa using this
  obtain ⟨hb, hc⟩ := quadratic_coeffs_nonneg (a1 := b) (a0 := c)
    fun z hz => H z (by rw [hmul, hz, zero_mul, mul_zero])
  obtain ⟨hp, hq⟩ := quadratic_coeffs_nonneg (a1 := p) (a0 := q)
    fun z hz => H z (by rw [hmul, hz, mul_zero, mul_zero])
  obtain ⟨d2, d3⟩ := quinticHurwitzDet23_eq_factors h4 h3 h2 h1 h0
  have d4 := quinticHurwitzDet4_eq_factors h4 h3 h2 h1 h0
  refine ⟨by rw [h4]; positivity, by rw [h3]; positivity, by rw [h2]; positivity,
    by rw [h1]; positivity, by rw [h0]; positivity, by rw [d2]; positivity, by rw [d3]; positivity,
    by rw [d4]; positivity⟩

/-- A strict violation of the quintic Routh–Hurwitz conditions (a negative coefficient, or a
negative `Δ₂`, `Δ₃`, `Δ₄`) gives a root with positive real part. -/
@[tmio T, powerlib_foundation] theorem exists_quintic_root_re_pos_of_violation
    {a4 a3 a2 a1 a0 : ℝ} (h : QuinticRouthViolation a4 a3 a2 a1 a0) :
    ∃ s : ℂ, s ^ 5 + (a4 : ℂ) * s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s +
      (a0 : ℂ) = 0 ∧ 0 < s.re := by
  by_contra hn
  push Not at hn
  obtain ⟨g4, g3, g2, g1, g0, d2, d3, d4⟩ := quintic_coeffs_nonneg_of_roots_re_nonpos hn
  rcases h with h | h | h | h | h | h | h | h <;> linarith

/-- The quintic Routh–Hurwitz conditions exclude their strict violation. -/
@[tmio T, powerlib_foundation] theorem not_quinticRouthViolation_of_quinticRouth
    {a4 a3 a2 a1 a0 : ℝ} (h : QuinticRouth a4 a3 a2 a1 a0) :
    ¬ QuinticRouthViolation a4 a3 a2 a1 a0 := by
  intro hv
  obtain ⟨s, hs, hre⟩ := exists_quintic_root_re_pos_of_violation hv
  exact absurd (quintic_roots_re_neg_of h s hs) (not_lt.mpr hre.le)

end Quintic

/-! ## Matrix interface -/

section Matrix

variable {n : ℕ}

/-- **Routh–Hurwitz (both directions), matrix form**: if the characteristic determinant of `A`
is the monic quintic, `IsHurwitz A` iff its Hurwitz determinants `Δ₁, …, Δ₅` are positive. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_iff_of_det_characteristicMatrix_quintic
    (A : Matrix (Fin n) (Fin n) ℝ) {a4 a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 5 + (a4 : ℂ) * s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ)) :
    LinearSystems.IsHurwitz A ↔ QuinticRouth a4 a3 a2 a1 a0 :=
  (isHurwitz_iff_of_det_characteristicMatrix A fun s => by rw [hchar]).trans
    (quintic_hurwitz_iff a4 a3 a2 a1 a0)

/-- A strict violation of the quintic Routh–Hurwitz conditions gives an eigenpair with positive
real part, in the shape of `unstable_of_exists_complex_eigenvalue_re_pos`. -/
@[tmio T, powerlib_foundation] theorem
    exists_eigenvalue_re_pos_of_det_characteristicMatrix_quintic_violation
    (A : Matrix (Fin n) (Fin n) ℝ) {a4 a3 a2 a1 a0 : ℝ}
    (hchar : ∀ s : ℂ, (Linear.characteristicMatrix A s).det =
      s ^ 5 + (a4 : ℂ) * s ^ 4 + (a3 : ℂ) * s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ))
    (h : QuinticRouthViolation a4 a3 a2 a1 a0) :
    ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  obtain ⟨s, hs, hre⟩ := exists_quintic_root_re_pos_of_violation h
  exact exists_eigenpair_re_pos_of_characteristic_root A (by rw [hchar]; exact hs) hre

end Matrix

end powerlib.Criteria
