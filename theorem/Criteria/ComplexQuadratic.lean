import theorem.Criteria.Hurwitz2

/-! # Hurwitz criterion for monic complex quadratics (foundation)

For `p(s) = s² + α s + β` with complex coefficients `α, β`:
all roots satisfy `Re s < 0` iff `Re α > 0` and
`(Re α)² Re β + Re α · Im α · Im β − (Im β)² > 0`.

The proof uses Vieta's relations for a root pair `s₁, s₂ = −α − s₁`:
`(Re α)² Re β + Re α Im α Im β − (Im β)² = Re s₁ · Re s₂ · ((Re s₁ + Re s₂)² + (Im s₁ − Im s₂)²)`
(`vieta_discriminant`). Both directions are proved; existence of a root comes from the
algebraic closedness of `ℂ`.

Special case used for the decoupled current loop with inductance mismatch
(`theorem/CurrentControl/Mismatch.lean`): if `β = c` is real then the condition is
`Re α > 0 ∧ c > 0`, independently of `Im α` (`complexQuadratic_realConst_roots_re_neg_iff`).

Source: needed by work-sync `theory/T-decoupling-control.md` §1.4 / §2.2 (characteristic
polynomial `L s² + (R + Kp + jωΔL) s + Ki` of the mismatched decoupled PI loop); the criterion
is the degree-two case of the Hermite–Biehler / Bilharz test for complex polynomials.
-/

noncomputable section
namespace powerlib.Criteria

/-- Vieta form of the complex-quadratic Hurwitz discriminant. -/
@[powerlib_foundation] theorem vieta_discriminant (s₁ s₂ : ℂ) :
    (-(s₁ + s₂)).re ^ 2 * (s₁ * s₂).re + (-(s₁ + s₂)).re * (-(s₁ + s₂)).im * (s₁ * s₂).im -
        (s₁ * s₂).im ^ 2 =
      s₁.re * s₂.re * ((s₁.re + s₂.re) ^ 2 + (s₁.im - s₂.im) ^ 2) := by
  simp only [Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im]
  ring

/-- The second root of a monic quadratic. -/
@[powerlib_foundation] theorem quadratic_partner {α β s : ℂ} (hs : s ^ 2 + α * s + β = 0) :
    α = -(s + (-α - s)) ∧ β = s * (-α - s) ∧ (-α - s) ^ 2 + α * (-α - s) + β = 0 := by
  refine ⟨by ring, by linear_combination hs, by linear_combination hs⟩

@[powerlib_foundation] private lemma re_neg_of_pair {x₁ x₂ y₁ y₂ : ℝ} (h1 : 0 < -(x₁ + x₂))
    (h2 : 0 < x₁ * x₂ * ((x₁ + x₂) ^ 2 + (y₁ - y₂) ^ 2)) : x₁ < 0 := by
  have hb : 0 < (x₁ + x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
    nlinarith [pow_pos h1 2, sq_nonneg (y₁ - y₂)]
  have hx : 0 < x₁ * x₂ := pos_of_mul_pos_left h2 hb.le
  nlinarith

/-- Hurwitz criterion for `s² + α s + β`, both directions. -/
@[powerlib_foundation] theorem complexQuadratic_roots_re_neg_iff (α β : ℂ) :
    (∀ s : ℂ, s ^ 2 + α * s + β = 0 → s.re < 0) ↔
      0 < α.re ∧ 0 < α.re ^ 2 * β.re + α.re * α.im * β.im - β.im ^ 2 := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self (discrim (1 : ℂ) α β)
    obtain ⟨s, hs⟩ := exists_quadratic_eq_zero (one_ne_zero) ⟨d, hd⟩
    have hs' : s ^ 2 + α * s + β = 0 := by linear_combination hs
    obtain ⟨hα, hβ, hs₂⟩ := quadratic_partner hs'
    have h₁ := h s hs'
    have h₂ := h _ hs₂
    rw [hα, hβ, vieta_discriminant]
    refine ⟨by simp only [Complex.neg_re, Complex.add_re]; linarith, ?_⟩
    have hp : 0 < s.re * (-α - s).re := mul_pos_of_neg_of_neg h₁ h₂
    have hq : 0 < (s.re + (-α - s).re) ^ 2 + (s.im - (-α - s).im) ^ 2 := by
      have : 0 < -(s.re + (-α - s).re) := by linarith
      nlinarith [pow_pos this 2, sq_nonneg (s.im - (-α - s).im)]
    exact mul_pos hp hq
  · rintro ⟨h1, h2⟩ s hs
    obtain ⟨hα, hβ, -⟩ := quadratic_partner hs
    rw [hα, hβ, vieta_discriminant] at h2
    rw [hα] at h1
    simp only [Complex.neg_re, Complex.add_re] at h1
    exact re_neg_of_pair (y₁ := s.im) (y₂ := (-α - s).im) (by linarith) h2

/-- Real constant term: the criterion reduces to `Re α > 0 ∧ c > 0` for every `Im α`. -/
@[powerlib_foundation] theorem complexQuadratic_realConst_roots_re_neg_iff (a b c : ℝ) :
    (∀ s : ℂ, s ^ 2 + (⟨a, b⟩ : ℂ) * s + (c : ℂ) = 0 → s.re < 0) ↔ 0 < a ∧ 0 < c := by
  rw [complexQuadratic_roots_re_neg_iff]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  constructor
  · rintro ⟨ha, hc⟩
    exact ⟨ha, pos_of_mul_pos_right hc (by positivity)⟩
  · rintro ⟨ha, hc⟩
    exact ⟨ha, by positivity⟩

end powerlib.Criteria
