import theorem.SpecialFunctions.ReactiveProduct

/-! # The largest cross term of two complex numbers in two disks under a combined bound (foundation)

The largest value of the cross term `Im(z₁ z̄₂)` of two complex numbers over the disks
`‖z₁‖ ≤ a`, `‖z₂‖ ≤ b` cut by a bound `‖p z₁ + q z₂‖ ≤ k` on one real combination of them. It is
the complex form of `reactiveMax` (`theorem/SpecialFunctions/ReactiveProduct.lean`): with
`u = p²‖z₁‖²`, `v = q²‖z₂‖²` and `r = 2pq Re(z₁ z̄₂)`,
`‖p z₁ + q z₂‖² = u + v + r` and `4uv − r² = 4p²q² Im(z₁ z̄₂)²`, so the three bounds become
`0 ≤ u ≤ p²a²`, `0 ≤ v ≤ q²b²`, `u + v + r ≤ k²` and the objective becomes `4uv − r²`. Conversely
every feasible `(u, v, r)` comes from a pair `(z₁, z₂)`, whose cross term can be given either sign
(conjugating both numbers flips it). Hence, for `p, q ≠ 0` and `a, b, k ≥ 0`, the largest cross
term is `√reactiveMax(p²a², q²b², k²)/(2|pq|)`.

Scope.
* Generic static algebra of two complex numbers and real parameters; nothing here describes a
  physical system and no model is defined.

Source: elementary algebra; `|z₁ z̄₂|² = ‖z₁‖²‖z₂‖² = Re(z₁ z̄₂)² + Im(z₁ z̄₂)²`, and the optimum
`reactiveMax`, `reactiveArg` of `theorem/SpecialFunctions/ReactiveProduct.lean`; no paper. For the
optimizer `(u, v, r) = reactiveArg` the attaining pair has `‖z₁‖ = √u/|p|`, `‖z₂‖ = √v/|q|` and the
prescribed product `z₁ z̄₂ = r/(2pq) + j s/(2pq)`, which exists because
`(r² + s²)/(4p²q²) = uv/(p²q²)` (`z₁` real, `z₂ = conj(z₁ z̄₂)/z₁`, or `z₁ = 0` when `u = 0`).

Results.
* `sq_im_mul_conj_le_reactiveMax`: `‖z₁‖ ≤ a`, `‖z₂‖ ≤ b` and `‖p z₁ + q z₂‖ ≤ k` give
  `4p²q² Im(z₁ z̄₂)² ≤ reactiveMax (p²a²) (q²b²) (k²)`.
* `exists_im_mul_conj_eq`: for `p, q ≠ 0`, `a, b, k ≥ 0` and either square root `s` of
  `reactiveMax (p²a²) (q²b²) (k²)`, some pair meeting the three bounds has `2pq Im(z₁ z̄₂) = s`.
* `isGreatest_im_mul_conj`: for `p, q ≠ 0` and `a, b, k ≥ 0`, the greatest value of `Im(z₁ z̄₂)`
  over the pairs meeting the three bounds is `√reactiveMax (p²a²) (q²b²) (k²) / (2|pq|)`.
-/

noncomputable section
namespace powerlib.SpecialFunctions

open ComplexConjugate

/-- `‖p z₁ + q z₂‖² = p²‖z₁‖² + q²‖z₂‖² + 2pq Re(z₁ z̄₂)`. -/
@[tmio T, powerlib_foundation] private theorem norm_sq_real_comb (p q : ℝ) (z₁ z₂ : ℂ) :
    ‖(p : ℂ) * z₁ + (q : ℂ) * z₂‖ ^ 2 =
      p ^ 2 * ‖z₁‖ ^ 2 + q ^ 2 * ‖z₂‖ ^ 2 + 2 * p * q * (z₁ * conj z₂).re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- `4 (p²‖z₁‖²)(q²‖z₂‖²) − (2pq Re(z₁ z̄₂))² = 4p²q² Im(z₁ z̄₂)²`. -/
@[tmio T, powerlib_foundation] private theorem cross_sq (p q : ℝ) (z₁ z₂ : ℂ) :
    4 * (p ^ 2 * ‖z₁‖ ^ 2) * (q ^ 2 * ‖z₂‖ ^ 2) - (2 * p * q * (z₁ * conj z₂).re) ^ 2 =
      4 * p ^ 2 * q ^ 2 * (z₁ * conj z₂).im ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- A product of prescribed modulus has factors of prescribed moduli: for `s, t ≥ 0` and
`‖ζ‖ = s t` there are `z₁`, `z₂` with `‖z₁‖ = s`, `‖z₂‖ = t` and `z₁ z̄₂ = ζ`. -/
@[tmio T, powerlib_foundation] private theorem exists_mul_conj_eq {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) {ζ : ℂ} (hζ : ‖ζ‖ = s * t) :
    ∃ z₁ z₂ : ℂ, ‖z₁‖ = s ∧ ‖z₂‖ = t ∧ z₁ * conj z₂ = ζ := by
  rcases eq_or_lt_of_le hs with h0 | hpos
  · subst h0
    rw [zero_mul, norm_eq_zero] at hζ
    refine ⟨0, (t : ℂ), by simp, ?_, by simp [hζ]⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  · have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    refine ⟨(s : ℂ), conj ζ / (s : ℂ), ?_, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    · rw [norm_div, Complex.norm_conj, hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      field_simp
    · rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
      field_simp

/-- `‖z₁‖ ≤ a`, `‖z₂‖ ≤ b` and `‖p z₁ + q z₂‖ ≤ k` give
`4p²q² Im(z₁ z̄₂)² ≤ reactiveMax (p²a²) (q²b²) (k²)`. -/
@[tmio T, powerlib_foundation] theorem sq_im_mul_conj_le_reactiveMax {z₁ z₂ : ℂ} {p q a b k : ℝ}
    (h₁ : ‖z₁‖ ≤ a) (h₂ : ‖z₂‖ ≤ b) (hk : ‖(p : ℂ) * z₁ + (q : ℂ) * z₂‖ ≤ k) :
    4 * p ^ 2 * q ^ 2 * (z₁ * conj z₂).im ^ 2 ≤
      reactiveMax (p ^ 2 * a ^ 2) (q ^ 2 * b ^ 2) (k ^ 2) := by
  have hS : p ^ 2 * ‖z₁‖ ^ 2 + q ^ 2 * ‖z₂‖ ^ 2 + 2 * p * q * (z₁ * conj z₂).re ≤ k ^ 2 := by
    rw [← norm_sq_real_comb]
    exact pow_le_pow_left₀ (norm_nonneg _) hk 2
  have hu : p ^ 2 * ‖z₁‖ ^ 2 ≤ p ^ 2 * a ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h₁ 2) (sq_nonneg _)
  have hv : q ^ 2 * ‖z₂‖ ^ 2 ≤ q ^ 2 * b ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h₂ 2) (sq_nonneg _)
  rw [← cross_sq]
  exact le_reactiveMax (sq_nonneg k) (by positivity) hu (by positivity) hv hS

/-- For `p, q ≠ 0`, `a, b, k ≥ 0` and either square root `s` of
`reactiveMax (p²a²) (q²b²) (k²)`, some pair with `‖z₁‖ ≤ a`, `‖z₂‖ ≤ b`, `‖p z₁ + q z₂‖ ≤ k` has
`2pq Im(z₁ z̄₂) = s`. -/
@[tmio T, powerlib_foundation] theorem exists_im_mul_conj_eq {p q a b k s : ℝ} (hp : p ≠ 0)
    (hq : q ≠ 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 ≤ k)
    (hs : s ^ 2 = reactiveMax (p ^ 2 * a ^ 2) (q ^ 2 * b ^ 2) (k ^ 2)) :
    ∃ z₁ z₂ : ℂ, ‖z₁‖ ≤ a ∧ ‖z₂‖ ≤ b ∧ ‖(p : ℂ) * z₁ + (q : ℂ) * z₂‖ ≤ k ∧
      2 * p * q * (z₁ * conj z₂).im = s := by
  obtain ⟨hu0, huU, hv0, hvV, hS⟩ := reactiveArg_feasible (U := p ^ 2 * a ^ 2)
    (V := q ^ 2 * b ^ 2) (by positivity) (by positivity) (sq_nonneg k)
  have hval := reactiveArg_value (p ^ 2 * a ^ 2) (q ^ 2 * b ^ 2) (k ^ 2)
  set u := (reactiveArg (p ^ 2 * a ^ 2) (q ^ 2 * b ^ 2) (k ^ 2)).1
  set v := (reactiveArg (p ^ 2 * a ^ 2) (q ^ 2 * b ^ 2) (k ^ 2)).2.1
  set r := (reactiveArg (p ^ 2 * a ^ 2) (q ^ 2 * b ^ 2) (k ^ 2)).2.2
  have hpa : 0 < |p| := abs_pos.mpr hp
  have hqa : 0 < |q| := abs_pos.mpr hq
  set ζ : ℂ := ((r / (2 * p * q) : ℝ) : ℂ) + ((s / (2 * p * q) : ℝ) : ℂ) * Complex.I with hζdef
  have hζ : ‖ζ‖ = Real.sqrt u / |p| * (Real.sqrt v / |q|) := by
    have h2 : ‖ζ‖ ^ 2 = (Real.sqrt u / |p| * (Real.sqrt v / |q|)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hζdef, Complex.normSq_add_mul_I, mul_pow, div_pow, div_pow,
        div_pow, div_pow, Real.sq_sqrt hu0, Real.sq_sqrt hv0, sq_abs, sq_abs, hs, ← hval]
      field_simp
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h2
  obtain ⟨z₁, z₂, hz₁, hz₂, hz⟩ := exists_mul_conj_eq (by positivity) (by positivity) hζ
  refine ⟨z₁, z₂, ?_, ?_, ?_, ?_⟩
  · rw [hz₁, div_le_iff₀ hpa]
    calc Real.sqrt u ≤ Real.sqrt ((|p| * a) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [mul_pow, sq_abs]; exact huU)
      _ = a * |p| := by rw [Real.sqrt_sq (by positivity)]; ring
  · rw [hz₂, div_le_iff₀ hqa]
    calc Real.sqrt v ≤ Real.sqrt ((|q| * b) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [mul_pow, sq_abs]; exact hvV)
      _ = b * |q| := by rw [Real.sqrt_sq (by positivity)]; ring
  · refine (sq_le_sq₀ (norm_nonneg _) hk).mp ?_
    have hre : 2 * p * q * (z₁ * conj z₂).re = r := by
      rw [hz, hζdef]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re,
        mul_zero, add_zero]
      field_simp
    rw [norm_sq_real_comb, hre, hz₁, hz₂, div_pow, div_pow, Real.sq_sqrt hu0, Real.sq_sqrt hv0,
      sq_abs, sq_abs]
    have e : p ^ 2 * (u / p ^ 2) + q ^ 2 * (v / q ^ 2) = u + v := by field_simp
    rw [e]
    exact hS
  · rw [hz, hζdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
      zero_add]
    field_simp

/-- For `p, q ≠ 0` and `a, b, k ≥ 0`, the greatest cross term `Im(z₁ z̄₂)` over `‖z₁‖ ≤ a`,
`‖z₂‖ ≤ b`, `‖p z₁ + q z₂‖ ≤ k` is `√reactiveMax (p²a²) (q²b²) (k²) / (2|pq|)`. -/
@[tmio T, powerlib_foundation] theorem isGreatest_im_mul_conj {p q a b k : ℝ} (hp : p ≠ 0)
    (hq : q ≠ 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 ≤ k) :
    IsGreatest {x : ℝ | ∃ z₁ z₂ : ℂ, ‖z₁‖ ≤ a ∧ ‖z₂‖ ≤ b ∧ ‖(p : ℂ) * z₁ + (q : ℂ) * z₂‖ ≤ k ∧
        x = (z₁ * conj z₂).im}
      (Real.sqrt (reactiveMax (p ^ 2 * a ^ 2) (q ^ 2 * b ^ 2) (k ^ 2)) / (2 * |p * q|)) := by
  have hpq : 0 < |p * q| := abs_pos.mpr (mul_ne_zero hp hq)
  have hR := reactiveMax_nonneg (U := p ^ 2 * a ^ 2) (V := q ^ 2 * b ^ 2) (by positivity)
    (by positivity) (sq_nonneg k)
  set R := reactiveMax (p ^ 2 * a ^ 2) (q ^ 2 * b ^ 2) (k ^ 2)
  constructor
  · have hs : (p * q / |p * q| * Real.sqrt R) ^ 2 = R := by
      rw [mul_pow, div_pow, sq_abs, div_self (pow_ne_zero 2 (mul_ne_zero hp hq)), one_mul,
        Real.sq_sqrt hR]
    obtain ⟨z₁, z₂, h₁, h₂, hk', hz⟩ := exists_im_mul_conj_eq hp hq ha hb hk hs
    refine ⟨z₁, z₂, h₁, h₂, hk', ?_⟩
    have hpq' : p * q ≠ 0 := mul_ne_zero hp hq
    have e : p * q / |p * q| * Real.sqrt R * |p * q| = p * q * Real.sqrt R := by field_simp
    rw [div_eq_iff (by positivity), eq_comm]
    refine mul_left_cancel₀ hpq' ?_
    linear_combination |p * q| * hz + e
  · rintro x ⟨z₁, z₂, h₁, h₂, hk', rfl⟩
    have hsq := sq_im_mul_conj_le_reactiveMax h₁ h₂ hk'
    rw [le_div_iff₀ (by positivity)]
    have e : (2 * |p * q| * (z₁ * conj z₂).im) ^ 2 = 4 * p ^ 2 * q ^ 2 * (z₁ * conj z₂).im ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
      ring
    have := Real.abs_le_sqrt (e ▸ hsq)
    linarith [le_abs_self (2 * |p * q| * (z₁ * conj z₂).im)]

end powerlib.SpecialFunctions
