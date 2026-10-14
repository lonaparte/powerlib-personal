import theorem.Network.Swing.Four

/-! # Networked swing equations: four machines with five or six lines

Source: work-sync `theory/T-synchronization-manifold.md` §1.7 and §2.2 (swing network
`Mᵢ θ̈ᵢ = P_{m,i} − Dᵢ θ̇ᵢ − ∑ⱼ Bᵢⱼ sin(θᵢ − θⱼ)` and its energy function); the model is
`theorem/Network/Swing/Basic.lean` (`Swing.family`); the potential, the Hessian and cubic forms and
the characterization of local asymptotic stability are in `theorem/Network/Swing/Degenerate.lean`;
the cut, flat-direction and four-cycle results are in `theorem/Network/Swing/Four.lean`.

Model boundary. Exactly the model of `theorem/Network/Swing/Basic.lean` for four machines (`n = 3`):
reduced state `(δ, ω)` of order `Fin (3 + (3 + 1))` (relative angles `θ_{i+1} − θ₀`, then the
frequency deviations), positive inertia and damping, constant power, symmetric nonnegative
lossless couplings, constant voltages; no governor, AVR, PLL, converter control, delay or PWM;
continuous time. Statements concern the selected angle profile `θ*` of a model.

Mathematical content. At a power-balance point the Hessian form of the network potential is
`A₂(u) = ∑ wᵢⱼ (uᵢ − uⱼ)²` with signed weights `wᵢⱼ = Bᵢⱼ cos(θᵢ − θⱼ)` and the cubic form is
`A₃(u) = ∑ Bᵢⱼ sin(θᵢ − θⱼ)(uᵢ − uⱼ)³`. Local asymptotic stability with a non-Hurwitz reduced
Jacobian leaves a non-constant null direction `u` of the positive semidefinite form `A₂` with
`A₃(u) = 0` (`hessForm_nonneg_of_localAsymptoticStable`,
`cubicForm_eq_zero_of_localAsymptoticStable`). The four-machine networks not covered by
`mem_den_locallyAsymptoticallyStable_iff_four` (at most four lines) are the diamond (exactly one
uncoupled pair) and the complete graph; on both, `A₃(u) ≠ 0`.
* The diamond, uncoupled pair `σ0 σ3`, hub `σ1 σ2`. Each two-line branch `σ1 – σk – σ2`
  (`k = 0, 3`) with balanced middle machine and positive degree `s` satisfies the identity
  `s³ (d cos Φ · A₂ᵇ + sin Φ · A₃ᵇ) = d³ P Q |P cos²a + Q cos²b · e^{iΦ}|²` (`branch_identity`;
  `a + b = Φ = θ(σ1) − θ(σ2)`, `d = u(σ1) − u(σ2)`), and the hub contributes `d³ B_hub`; with
  `A₂(u) = 0` this gives `sin Φ · A₃(u) = d³ (B_hub + nonnegative)` (`diamond_cubic_ne_zero`).
* The complete graph. Four points on a circle leave a gap of at least `π/2`, so the machines can
  be relabelled by increasing lifted angles `0, γ₁, γ₁ + γ₂, γ₁ + γ₂ + γ₃` of spread at most
  `3π/2` (`exists_sorted_lift`). Positive cuts force `γᵢ < π/2`; a null direction forces the
  extreme line `03` negative; the lines `02`, `13` are positive, of zero weight or negative.
  Reductions at the middle machines (Schur complements: `psd_reduce_one_zero`,
  `psd_reduce_one_three`, `psd_reduce_two_zero`, `psd_reduce_two_three`) order the null direction
  (`order_of_nonneg`, `order_of_neg_02`, `order_of_neg_02_13`): with `u₀ < u₃` it increases with
  the lifted angle, up to one adjacent transposition (`0 < 2 < 1 < 3` when only `03` is negative,
  `0 < 1 < 3 < 2` when `02, 03` are negative). The circulation then splits into directed cycles,
  each with exactly one negative line, and every cycle term is positive by the superadditivity of
  `tan` (`tan_sum_mul_sq_lt`): `cubic_pos_of_monotone`, `cubic_pos_cross`, `cubic_pos_two_neg`,
  `cubic_pos_three_neg`. Cases `sorted_case_nonneg`, `sorted_case_neg` (its mirror image, reversed
  machines and negated direction, covers `13` negative with `02` nonnegative),
  `sorted_case_neg_neg`, collected in `sorted_cubic_pos`; `sorted_cubic_ne_zero` adds the case
  `u₀ = u₃` (no flow on `03`: the diamond identity) and the reflection `u ↦ −u`.

Results.
* Static foundation: `branch_identity`, `branch_nonneg`, `diamond_cubic_ne_zero`,
  `cubic_pos_of_monotone`, `cubic_pos_three_neg`, `cubic_pos_cross`, `cubic_pos_two_neg`,
  `tan_neg_of_pi_div_two_lt_of_lt_pi`, `order_of_nonneg`, `order_of_neg_02`, `order_of_neg_02_13`,
  the four `psd_reduce_*`, `cos_pos_of_nonneg_of_lt`, `flow_eq_tan`, `sorted_case_nonneg`,
  `sorted_case_neg`, `sorted_case_neg_neg`, `sorted_cubic_pos`, `sorted_cubic_ne_zero`
  (four coupled machines in sorted lifted angles: the cubic form is nonzero along every
  non-constant null direction of a positive semidefinite Hessian form with positive cuts),
  `exists_sorted_lift`, `eq_of_labelled_eq`, `exists_perm_zero_three`.
* Family conclusions: `exact_locallyAsymptoticallyStable_four` — for four machines the local
  asymptotic translation `{powerFlow, jacobianStable}` of `Swing.family` is exact; and
  `mem_den_locallyAsymptoticallyStable_iff_four_machines` — every four-machine model is locally
  asymptotically stable exactly when its profile is a power-balance point with a Hurwitz reduced
  Jacobian (no restriction on the lines). With `exact_locallyAsymptoticallyStable_zero`, `_two`,
  `_three` and `not_exact_locallyAsymptoticallyStable` (five or more machines) the local asymptotic
  translation is decided for every number of machines: exact up to four machines, not exact from
  five.
* Implementation evidence (private, model level): `not_localAsymptoticStable_diamond`,
  `not_localAsymptoticStable_complete`, `not_localAsymptoticStable_four_machines` (with
  `not_localAsymptoticStable_four` of `Swing/Four` for two uncoupled pairs) and the labelled-form
  helpers `cut_pos_of_localAsymptoticStable`, `labelled_nonneg_of_localAsymptoticStable`,
  `exists_null_of_localAsymptoticStable`.

Connection architecture. The family is `Swing.family`; the public model conclusions are
`connection%` statements on its generated denotation. The identities, orderings, cycle bounds and
the lift are static real arithmetic (foundation); the behavioural fold arguments on the model stay
private.
-/

noncomputable section
namespace powerlib.Network.Swing
open Matrix Finset Filter Topology Metric
open scoped Real
open powerlib.Dynamics (State)

variable {n : ℕ}

/-! ## The diamond: a branch identity -/

/-- **Branch identity.** A branch of two lines from machine `1` through a balanced middle machine to
machine `2` (amplitudes `P, Q`, line angles `a, b` with `a + b = Φ`, increments `xa, xb` with
`P cos a · xa = Q cos b · xb` and `xa + xb = d`): with `s = P cos a + Q cos b`,
`s³ (d cos Φ (P cos a xa² + Q cos b xb²) + sin Φ (P sin a xa³ + Q sin b xb³)) =
d³ P Q ((P cos² a)² + (Q cos² b)² + 2 (P cos² a)(Q cos² b) cos Φ)`. -/
@[powerlib_foundation] theorem branch_identity {P Q a b xa xb d : ℝ}
    (hs : P * Real.cos a * xa = Q * Real.cos b * xb) (hd : xa + xb = d) :
    (P * Real.cos a + Q * Real.cos b) ^ 3 *
      (d * Real.cos (a + b) * (P * Real.cos a * xa ^ 2 + Q * Real.cos b * xb ^ 2) +
        Real.sin (a + b) * (P * Real.sin a * xa ^ 3 + Q * Real.sin b * xb ^ 3)) =
      d ^ 3 * (P * Q) * ((P * Real.cos a ^ 2) ^ 2 + (Q * Real.cos b ^ 2) ^ 2 +
        2 * (P * Real.cos a ^ 2) * (Q * Real.cos b ^ 2) * Real.cos (a + b)) := by
  have h1 : (P * Real.cos a + Q * Real.cos b) * xa = d * (Q * Real.cos b) := by
    linear_combination hs + (Q * Real.cos b) * hd
  have h2 : (P * Real.cos a + Q * Real.cos b) * xb = d * (P * Real.cos a) := by
    linear_combination -hs + (P * Real.cos a) * hd
  have key : (P * Real.cos a + Q * Real.cos b) ^ 3 *
      (d * Real.cos (a + b) * (P * Real.cos a * xa ^ 2 + Q * Real.cos b * xb ^ 2) +
        Real.sin (a + b) * (P * Real.sin a * xa ^ 3 + Q * Real.sin b * xb ^ 3)) =
      d * Real.cos (a + b) * (P * Real.cos a + Q * Real.cos b) *
        (P * Real.cos a * ((P * Real.cos a + Q * Real.cos b) * xa) ^ 2 +
          Q * Real.cos b * ((P * Real.cos a + Q * Real.cos b) * xb) ^ 2) +
      Real.sin (a + b) * (P * Real.sin a * ((P * Real.cos a + Q * Real.cos b) * xa) ^ 3 +
          Q * Real.sin b * ((P * Real.cos a + Q * Real.cos b) * xb) ^ 3) := by ring
  rw [key, h1, h2, Real.cos_add, Real.sin_add]
  linear_combination (P * Q ^ 3 * Real.cos b ^ 4 * d ^ 3) * Real.sin_sq_add_cos_sq a +
    (P ^ 3 * Q * Real.cos a ^ 4 * d ^ 3) * Real.sin_sq_add_cos_sq b

/-- `U² + V² + 2UV cos φ = |U + V e^{iφ}|² ≥ 0`. -/
@[powerlib_foundation] theorem branch_nonneg (U V φ : ℝ) :
    0 ≤ U ^ 2 + V ^ 2 + 2 * U * V * Real.cos φ := by
  nlinarith [sq_nonneg (U + V * Real.cos φ), sq_nonneg (V * Real.sin φ), Real.sin_sq_add_cos_sq φ]

/-- **The cubic term on a diamond.** Five lines: the hub `12` (`B₁₂ > 0`) and the branches
`1 – 0 – 2`, `1 – 3 – 2` (`B ≥ 0`), machines `0` and `3` balanced with positive degrees `s₀, s₃`.
A null direction of the Hessian form with `g₁ ≠ g₂` has a nonzero cubic term: with
`d = g₁ − g₂` and `Φ = θ₁ − θ₂`, `s₀³ s₃³ sin Φ · A₃ = d³ (s₀³ s₃³ B₁₂ + nonnegative branch terms)`
(`branch_identity`). -/
@[powerlib_foundation]
theorem diamond_cubic_ne_zero {θ₀ θ₁ θ₂ θ₃ B₀₁ B₀₂ B₁₂ B₁₃ B₂₃ g₀ g₁ g₂ g₃ : ℝ}
    (h01 : 0 ≤ B₀₁) (h02 : 0 ≤ B₀₂) (h12 : 0 < B₁₂) (h13 : 0 ≤ B₁₃) (h23 : 0 ≤ B₂₃)
    (hs₀ : 0 < B₀₁ * Real.cos (θ₀ - θ₁) + B₀₂ * Real.cos (θ₀ - θ₂))
    (hs₃ : 0 < B₁₃ * Real.cos (θ₁ - θ₃) + B₂₃ * Real.cos (θ₂ - θ₃))
    (N₀ : B₀₁ * Real.cos (θ₀ - θ₁) * (g₀ - g₁) + B₀₂ * Real.cos (θ₀ - θ₂) * (g₀ - g₂) = 0)
    (N₃ : B₁₃ * Real.cos (θ₁ - θ₃) * (g₃ - g₁) + B₂₃ * Real.cos (θ₂ - θ₃) * (g₃ - g₂) = 0)
    (hA : B₀₁ * Real.cos (θ₀ - θ₁) * (g₀ - g₁) ^ 2 + B₀₂ * Real.cos (θ₀ - θ₂) * (g₀ - g₂) ^ 2 +
      B₁₂ * Real.cos (θ₁ - θ₂) * (g₁ - g₂) ^ 2 + B₁₃ * Real.cos (θ₁ - θ₃) * (g₁ - g₃) ^ 2 +
      B₂₃ * Real.cos (θ₂ - θ₃) * (g₂ - g₃) ^ 2 = 0)
    (hd : g₁ ≠ g₂) :
    B₀₁ * Real.sin (θ₀ - θ₁) * (g₀ - g₁) ^ 3 + B₀₂ * Real.sin (θ₀ - θ₂) * (g₀ - g₂) ^ 3 +
      B₁₂ * Real.sin (θ₁ - θ₂) * (g₁ - g₂) ^ 3 + B₁₃ * Real.sin (θ₁ - θ₃) * (g₁ - g₃) ^ 3 +
      B₂₃ * Real.sin (θ₂ - θ₃) * (g₂ - g₃) ^ 3 ≠ 0 := by
  intro hC
  set d := g₁ - g₂ with hd_def
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hd
  -- the two branches, as paths from machine 1 to machine 2
  have c01 : Real.cos (θ₀ - θ₁) = Real.cos (θ₁ - θ₀) := by
    rw [← Real.cos_neg]; ring_nf
  have s01 : Real.sin (θ₀ - θ₁) = -Real.sin (θ₁ - θ₀) := by
    rw [← Real.sin_neg]; ring_nf
  have c23 : Real.cos (θ₂ - θ₃) = Real.cos (θ₃ - θ₂) := by
    rw [← Real.cos_neg]; ring_nf
  have s23 : Real.sin (θ₂ - θ₃) = -Real.sin (θ₃ - θ₂) := by
    rw [← Real.sin_neg]; ring_nf
  have e₀ : (θ₁ - θ₀) + (θ₀ - θ₂) = θ₁ - θ₂ := by ring
  have e₃ : (θ₁ - θ₃) + (θ₃ - θ₂) = θ₁ - θ₂ := by ring
  have I₀ := branch_identity (P := B₀₁) (Q := B₀₂) (a := θ₁ - θ₀) (b := θ₀ - θ₂)
    (xa := g₁ - g₀) (xb := g₀ - g₂) (d := d) (by rw [← c01]; linear_combination -N₀)
    (by rw [hd_def]; ring)
  have I₃ := branch_identity (P := B₁₃) (Q := B₂₃) (a := θ₁ - θ₃) (b := θ₃ - θ₂)
    (xa := g₁ - g₃) (xb := g₃ - g₂) (d := d) (by rw [← c23]; linear_combination -N₃)
    (by rw [hd_def]; ring)
  rw [e₀, ← c01] at I₀
  rw [e₃, ← c23] at I₃
  rw [s01, s23] at hC
  have hK₀ := branch_nonneg (B₀₁ * Real.cos (θ₀ - θ₁) ^ 2) (B₀₂ * Real.cos (θ₀ - θ₂) ^ 2)
    (θ₁ - θ₂)
  have hK₃ := branch_nonneg (B₁₃ * Real.cos (θ₁ - θ₃) ^ 2) (B₂₃ * Real.cos (θ₂ - θ₃) ^ 2)
    (θ₁ - θ₂)
  -- the hub
  have hub : d * Real.cos (θ₁ - θ₂) * (B₁₂ * Real.cos (θ₁ - θ₂) * d ^ 2) +
      Real.sin (θ₁ - θ₂) * (B₁₂ * Real.sin (θ₁ - θ₂) * d ^ 3) = d ^ 3 * B₁₂ := by
    linear_combination (d ^ 3 * B₁₂) * Real.sin_sq_add_cos_sq (θ₁ - θ₂)
  set s₀ := B₀₁ * Real.cos (θ₀ - θ₁) + B₀₂ * Real.cos (θ₀ - θ₂) with hs₀_def
  set s₃ := B₁₃ * Real.cos (θ₁ - θ₃) + B₂₃ * Real.cos (θ₂ - θ₃) with hs₃_def
  set K₀ := (B₀₁ * Real.cos (θ₀ - θ₁) ^ 2) ^ 2 + (B₀₂ * Real.cos (θ₀ - θ₂) ^ 2) ^ 2 +
    2 * (B₀₁ * Real.cos (θ₀ - θ₁) ^ 2) * (B₀₂ * Real.cos (θ₀ - θ₂) ^ 2) * Real.cos (θ₁ - θ₂)
  set K₃ := (B₁₃ * Real.cos (θ₁ - θ₃) ^ 2) ^ 2 + (B₂₃ * Real.cos (θ₂ - θ₃) ^ 2) ^ 2 +
    2 * (B₁₃ * Real.cos (θ₁ - θ₃) ^ 2) * (B₂₃ * Real.cos (θ₂ - θ₃) ^ 2) * Real.cos (θ₁ - θ₂)
  have total : d ^ 3 * (s₀ ^ 3 * s₃ ^ 3 * B₁₂ + s₃ ^ 3 * ((B₀₁ * B₀₂) * K₀) +
      s₀ ^ 3 * ((B₁₃ * B₂₃) * K₃)) = 0 := by
    linear_combination (s₀ ^ 3 * s₃ ^ 3 * d * Real.cos (θ₁ - θ₂)) * hA +
      (s₀ ^ 3 * s₃ ^ 3 * Real.sin (θ₁ - θ₂)) * hC - s₃ ^ 3 * I₀ - s₀ ^ 3 * I₃ -
      s₀ ^ 3 * s₃ ^ 3 * hub
  have hpos : 0 < s₀ ^ 3 * s₃ ^ 3 * B₁₂ + s₃ ^ 3 * ((B₀₁ * B₀₂) * K₀) +
      s₀ ^ 3 * ((B₁₃ * B₂₃) * K₃) := by
    have := mul_pos (mul_pos (pow_pos hs₀ 3) (pow_pos hs₃ 3)) h12
    have := mul_nonneg (pow_pos hs₃ 3).le (mul_nonneg (mul_nonneg h01 h02) hK₀)
    have := mul_nonneg (pow_pos hs₀ 3).le (mul_nonneg (mul_nonneg h13 h23) hK₃)
    linarith
  rcases mul_eq_zero.mp total with h | h
  · exact hd0 (pow_eq_zero_iff (by norm_num) |>.mp h)
  · linarith

/-! ## The complete graph in sorted lifted angles: cubic terms of cycles -/

/-- A monotone direction with nonnegative line flows and a positive flow on `03` has a positive
cubic term. -/
@[powerlib_foundation] theorem cubic_pos_of_monotone {F₀₁ F₀₂ F₀₃ F₁₂ F₁₃ F₂₃ u₀ u₁ u₂ u₃ : ℝ}
    (f01 : 0 ≤ F₀₁) (f02 : 0 ≤ F₀₂) (f03 : 0 < F₀₃) (f12 : 0 ≤ F₁₂) (f13 : 0 ≤ F₁₃)
    (f23 : 0 ≤ F₂₃) (h01 : u₀ ≤ u₁) (h12 : u₁ ≤ u₂) (h23 : u₂ ≤ u₃) (h03 : u₀ < u₃) :
    0 < F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 := by
  have := mul_nonneg f01 (pow_nonneg (sub_nonneg.mpr h01) 3)
  have := mul_nonneg f02 (pow_nonneg (sub_nonneg.mpr (h01.trans h12)) 3)
  have := mul_pos f03 (pow_pos (sub_pos.mpr h03) 3)
  have := mul_nonneg f12 (pow_nonneg (sub_nonneg.mpr h12) 3)
  have := mul_nonneg f13 (pow_nonneg (sub_nonneg.mpr (h12.trans h23)) 3)
  have := mul_nonneg f23 (pow_nonneg (sub_nonneg.mpr h23) 3)
  linarith

/-- Three negative lines `02, 03, 13` and a monotone null direction. -/
@[powerlib_foundation]
theorem cubic_pos_three_neg {γ₁ γ₂ γ₃ W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃ F₀₁ F₀₂ F₀₃ F₁₂ F₁₃ F₂₃
      u₀ u₁ u₂ u₃ : ℝ}
    (hγ₁ : 0 ≤ γ₁ ∧ γ₁ < π / 2) (hγ₂ : 0 ≤ γ₂ ∧ γ₂ < π / 2) (hγ₃ : 0 ≤ γ₃ ∧ γ₃ < π / 2)
    (hσ : π / 2 < γ₁ + γ₂ + γ₃)
    (w02 : W₀₂ < 0) (w03 : W₀₃ < 0) (w13 : W₁₃ < 0)
    (f01 : F₀₁ = Real.tan γ₁ * W₀₁) (f12 : F₁₂ = Real.tan γ₂ * W₁₂)
    (f23 : F₂₃ = Real.tan γ₃ * W₂₃) (f03 : F₀₃ = Real.tan (γ₁ + γ₂ + γ₃) * W₀₃)
    (f02 : 0 ≤ F₀₂) (f13 : 0 ≤ F₁₃)
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0)
    (N₃ : W₀₃ * (u₃ - u₀) + W₁₃ * (u₃ - u₁) + W₂₃ * (u₃ - u₂) = 0)
    (h01 : u₀ < u₁) (h12 : u₁ < u₂) (h23 : u₂ < u₃) :
    0 < F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 := by
  set T₁ := Real.tan γ₁
  set T₂ := Real.tan γ₂
  set T₃ := Real.tan γ₃
  set T := Real.tan (γ₁ + γ₂ + γ₃)
  have t₁ : 0 ≤ T₁ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hγ₁.1 hγ₁.2.le
  have t₂ : 0 ≤ T₂ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hγ₂.1 hγ₂.2.le
  have t₃ : 0 ≤ T₃ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hγ₃.1 hγ₃.2.le
  have hS := tan_sum_mul_sq_lt (β₂ := γ₁) (β₃ := γ₂) (β₄ := γ₃) (a₂ := u₁ - u₀)
    (a₃ := u₂ - u₁) (a₄ := u₃ - u₂) ⟨by linarith [Real.pi_pos], hγ₁.2⟩
    ⟨by linarith [Real.pi_pos], hγ₂.2⟩ ⟨by linarith [Real.pi_pos], hγ₃.2⟩
    (sub_pos.mpr h01) (sub_pos.mpr h12) (sub_pos.mpr h23) hσ
  have hsum : (u₁ - u₀) + (u₂ - u₁) + (u₃ - u₂) = u₃ - u₀ := by ring
  rw [hsum] at hS
  set D := T₁ * (u₁ - u₀) ^ 2 + T₂ * (u₂ - u₁) ^ 2 + T₃ * (u₃ - u₂) ^ 2 - T * (u₃ - u₀) ^ 2
  have hD : 0 < D := by simp only [D]; linarith
  have y03 : 0 < -W₀₃ * (u₃ - u₀) := mul_pos (by linarith) (by linarith)
  have y02 : 0 ≤ -W₀₂ * (u₂ - u₀) := mul_nonneg (by linarith) (by linarith)
  have y13 : 0 ≤ -W₁₃ * (u₃ - u₁) := mul_nonneg (by linarith) (by linarith)
  have key : F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 =
      (-W₀₃ * (u₃ - u₀)) * D + T₁ * (-W₀₂ * (u₂ - u₀)) * (u₁ - u₀) ^ 2 +
      T₂ * (-W₀₂ * (u₂ - u₀) + -W₁₃ * (u₃ - u₁)) * (u₂ - u₁) ^ 2 +
      T₃ * (-W₁₃ * (u₃ - u₁)) * (u₃ - u₂) ^ 2 + F₀₂ * (u₂ - u₀) ^ 3 +
      F₁₃ * (u₃ - u₁) ^ 3 := by
    rw [f01, f12, f23, f03]
    linear_combination (T₁ * (u₀ - u₁) ^ 2) * N₁ +
      (T₁ * (u₀ - u₁) ^ 2 + T₂ * (u₁ - u₂) ^ 2) * N₂ +
      (T₁ * (u₀ - u₁) ^ 2 + T₂ * (u₁ - u₂) ^ 2 + T₃ * (u₂ - u₃) ^ 2) * N₃
  rw [key]
  have := mul_pos y03 hD
  have := mul_nonneg (mul_nonneg t₁ y02) (sq_nonneg (u₁ - u₀))
  have := mul_nonneg (mul_nonneg t₂ (add_nonneg y02 y13)) (sq_nonneg (u₂ - u₁))
  have := mul_nonneg (mul_nonneg t₃ y13) (sq_nonneg (u₃ - u₂))
  have := mul_nonneg f02 (pow_nonneg (by linarith : (0:ℝ) ≤ u₂ - u₀) 3)
  have := mul_nonneg f13 (pow_nonneg (by linarith : (0:ℝ) ≤ u₃ - u₁) 3)
  linarith

/-- `tan x < 0` on `(π/2, π)`. -/
@[powerlib_foundation]
theorem tan_neg_of_pi_div_two_lt_of_lt_pi {x : ℝ} (h1 : π / 2 < x) (h2 : x < π) :
    Real.tan x < 0 := by
  rw [Real.tan_eq_sin_div_cos]
  exact div_neg_of_pos_of_neg (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) h2)
    (Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [Real.pi_pos]))

/-- Only the line `03` negative; the null direction orders the machines `0 < 2 < 1 < 3`. -/
@[powerlib_foundation]
theorem cubic_pos_cross {γ₁ γ₂ γ₃ W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃ F₀₁ F₀₂ F₀₃ F₁₂ F₁₃ F₂₃
      u₀ u₁ u₂ u₃ : ℝ}
    (hγ₂ : 0 ≤ γ₂ ∧ γ₂ < π / 2) (h02 : 0 ≤ γ₁ + γ₂ ∧ γ₁ + γ₂ < π / 2)
    (h13 : 0 ≤ γ₂ + γ₃ ∧ γ₂ + γ₃ < π / 2) (hσ : π / 2 < γ₁ + γ₂ + γ₃)
    (w01 : 0 < W₀₁) (w12 : 0 < W₁₂) (w23 : 0 < W₂₃)
    (f02 : F₀₂ = Real.tan (γ₁ + γ₂) * W₀₂) (f12 : F₁₂ = Real.tan γ₂ * W₁₂)
    (f13 : F₁₃ = Real.tan (γ₂ + γ₃) * W₁₃) (f03 : F₀₃ = Real.tan (γ₁ + γ₂ + γ₃) * W₀₃)
    (f01 : 0 ≤ F₀₁) (f23 : 0 ≤ F₂₃)
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0)
    (N₃ : W₀₃ * (u₃ - u₀) + W₁₃ * (u₃ - u₁) + W₂₃ * (u₃ - u₂) = 0)
    (h02u : u₀ < u₂) (h21 : u₂ < u₁) (h13u : u₁ < u₃) :
    0 < F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 := by
  set T₂ := Real.tan γ₂
  set T₀₂ := Real.tan (γ₁ + γ₂)
  set T₁₃ := Real.tan (γ₂ + γ₃)
  set T := Real.tan (γ₁ + γ₂ + γ₃)
  have t02 : 0 ≤ T₀₂ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two h02.1 h02.2.le
  have t13 : 0 ≤ T₁₃ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two h13.1 h13.2.le
  have tT : T < 0 := tan_neg_of_pi_div_two_lt_of_lt_pi hσ (by linarith)
  have hS := tan_sum_mul_sq_lt (β₂ := γ₂ + γ₃) (β₃ := -γ₂) (β₄ := γ₁ + γ₂)
    (a₂ := u₃ - u₁) (a₃ := u₁ - u₂) (a₄ := u₂ - u₀) ⟨by linarith [Real.pi_pos], h13.2⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    ⟨by linarith [Real.pi_pos], h02.2⟩
    (sub_pos.mpr h13u) (sub_pos.mpr h21) (sub_pos.mpr h02u) (by linarith)
  have hsum : (u₃ - u₁) + (u₁ - u₂) + (u₂ - u₀) = u₃ - u₀ := by ring
  have hang : γ₂ + γ₃ + -γ₂ + (γ₁ + γ₂) = γ₁ + γ₂ + γ₃ := by ring
  rw [hsum, hang, Real.tan_neg] at hS
  set D := T₁₃ * (u₃ - u₁) ^ 2 + -T₂ * (u₁ - u₂) ^ 2 + T₀₂ * (u₂ - u₀) ^ 2 -
    T * (u₃ - u₀) ^ 2
  have hD : 0 < D := by simp only [D]; linarith
  have y12 : 0 < W₁₂ * (u₁ - u₂) := mul_pos w12 (by linarith)
  have y32 : 0 < W₂₃ * (u₃ - u₂) := mul_pos w23 (by linarith)
  have y10 : 0 < W₀₁ * (u₁ - u₀) := mul_pos w01 (by linarith)
  have key : F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 =
      (W₁₂ * (u₁ - u₂)) * D + F₀₁ * (u₁ - u₀) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 +
      T₀₂ * (W₂₃ * (u₃ - u₂)) * (u₂ - u₀) ^ 2 +
      (-T) * (W₀₁ * (u₁ - u₀) + W₂₃ * (u₃ - u₂)) * (u₃ - u₀) ^ 2 +
      T₁₃ * (W₀₁ * (u₁ - u₀)) * (u₃ - u₁) ^ 2 := by
    rw [f02, f12, f13, f03]
    linear_combination (T * (u₀ - u₃) ^ 2 - T₁₃ * (u₁ - u₃) ^ 2) * N₁ +
      (T₀₂ * (u₀ - u₂) ^ 2) * N₂ + (T * (u₀ - u₃) ^ 2) * N₃
  rw [key]
  have := mul_pos y12 hD
  have := mul_nonneg f01 (pow_nonneg (by linarith : (0:ℝ) ≤ u₁ - u₀) 3)
  have := mul_nonneg f23 (pow_nonneg (by linarith : (0:ℝ) ≤ u₃ - u₂) 3)
  have := mul_nonneg (mul_nonneg t02 y32.le) (sq_nonneg (u₂ - u₀))
  have := mul_nonneg (mul_nonneg (neg_nonneg.mpr tT.le) (add_pos y10 y32).le)
    (sq_nonneg (u₃ - u₀))
  have := mul_nonneg (mul_nonneg t13 y10.le) (sq_nonneg (u₃ - u₁))
  linarith

/-- Lines `02, 03` negative; the null direction orders the machines `0 < 1 < 3 < 2`. -/
@[powerlib_foundation]
theorem cubic_pos_two_neg {γ₁ γ₂ γ₃ W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃ F₀₁ F₀₂ F₀₃ F₁₂ F₁₃ F₂₃
      u₀ u₁ u₂ u₃ : ℝ}
    (hγ₁ : 0 ≤ γ₁ ∧ γ₁ < π / 2) (hγ₃ : 0 ≤ γ₃ ∧ γ₃ < π / 2)
    (h13 : 0 ≤ γ₂ + γ₃ ∧ γ₂ + γ₃ < π / 2) (h02 : π / 2 < γ₁ + γ₂ ∧ γ₁ + γ₂ < π)
    (w12 : 0 < W₁₂) (w23 : 0 < W₂₃) (w03 : W₀₃ < 0)
    (f01 : F₀₁ = Real.tan γ₁ * W₀₁) (f02 : F₀₂ = Real.tan (γ₁ + γ₂) * W₀₂)
    (f13 : F₁₃ = Real.tan (γ₂ + γ₃) * W₁₃) (f23 : F₂₃ = Real.tan γ₃ * W₂₃)
    (f03 : 0 ≤ F₀₃) (f12 : 0 ≤ F₁₂)
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0)
    (N₃ : W₀₃ * (u₃ - u₀) + W₁₃ * (u₃ - u₁) + W₂₃ * (u₃ - u₂) = 0)
    (h01 : u₀ < u₁) (h13u : u₁ < u₃) (h32 : u₃ < u₂) :
    0 < F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 := by
  set T₁ := Real.tan γ₁
  set T₃ := Real.tan γ₃
  set T₀₂ := Real.tan (γ₁ + γ₂)
  set T₁₃ := Real.tan (γ₂ + γ₃)
  have t1 : 0 ≤ T₁ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hγ₁.1 hγ₁.2.le
  have t13 : 0 ≤ T₁₃ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two h13.1 h13.2.le
  have t02 : T₀₂ < 0 := tan_neg_of_pi_div_two_lt_of_lt_pi h02.1 h02.2
  have hS := tan_sum_mul_sq_lt (β₂ := -γ₃) (β₃ := γ₂ + γ₃) (β₄ := γ₁)
    (a₂ := u₂ - u₃) (a₃ := u₃ - u₁) (a₄ := u₁ - u₀)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    ⟨by linarith [Real.pi_pos], h13.2⟩ ⟨by linarith [Real.pi_pos], hγ₁.2⟩
    (sub_pos.mpr h32) (sub_pos.mpr h13u) (sub_pos.mpr h01) (by linarith)
  have hsum : (u₂ - u₃) + (u₃ - u₁) + (u₁ - u₀) = u₂ - u₀ := by ring
  have hang : -γ₃ + (γ₂ + γ₃) + γ₁ = γ₁ + γ₂ := by ring
  rw [hsum, hang, Real.tan_neg] at hS
  set D := -T₃ * (u₂ - u₃) ^ 2 + T₁₃ * (u₃ - u₁) ^ 2 + T₁ * (u₁ - u₀) ^ 2 -
    T₀₂ * (u₂ - u₀) ^ 2
  have hD : 0 < D := by simp only [D]; linarith
  have y23 : 0 < W₂₃ * (u₂ - u₃) := mul_pos w23 (by linarith)
  have y21 : 0 < W₁₂ * (u₂ - u₁) := mul_pos w12 (by linarith)
  have y03 : 0 < -W₀₃ * (u₃ - u₀) := mul_pos (by linarith) (by linarith)
  have key : F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 =
      (W₂₃ * (u₂ - u₃)) * D + T₁ * (W₁₂ * (u₂ - u₁) + -W₀₃ * (u₃ - u₀)) * (u₁ - u₀) ^ 2 +
      (-T₀₂) * (W₁₂ * (u₂ - u₁)) * (u₂ - u₀) ^ 2 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + T₁₃ * (-W₀₃ * (u₃ - u₀)) * (u₃ - u₁) ^ 2 := by
    rw [f01, f02, f13, f23]
    linear_combination (T₁ * (u₀ - u₁) ^ 2) * N₁ + (T₀₂ * (u₀ - u₂) ^ 2) * N₂ +
      (T₁ * (u₀ - u₁) ^ 2 + T₁₃ * (u₁ - u₃) ^ 2) * N₃
  rw [key]
  have := mul_pos y23 hD
  have := mul_nonneg (mul_nonneg t1 (add_pos y21 y03).le) (sq_nonneg (u₁ - u₀))
  have := mul_nonneg (mul_nonneg (neg_nonneg.mpr t02.le) y21.le) (sq_nonneg (u₂ - u₀))
  have := mul_nonneg f03 (pow_nonneg (by linarith : (0:ℝ) ≤ u₃ - u₀) 3)
  have := mul_nonneg f12 (pow_nonneg (by linarith : (0:ℝ) ≤ u₂ - u₁) 3)
  have := mul_nonneg (mul_nonneg t13 y03.le) (sq_nonneg (u₃ - u₁))
  linarith

/-! ## Orderings of the null direction -/

/-- Nonnegative weights at the two middle machines: the null direction keeps them strictly between
the end machines. -/
@[powerlib_foundation] theorem order_of_nonneg {W₀₁ W₀₂ W₁₂ W₁₃ W₂₃ u₀ u₁ u₂ u₃ : ℝ}
    (w01 : 0 < W₀₁) (w12 : 0 < W₁₂) (w23 : 0 < W₂₃) (w02 : 0 ≤ W₀₂) (w13 : 0 ≤ W₁₃)
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0) (h03 : u₀ < u₃) :
    u₀ < u₁ ∧ u₀ < u₂ ∧ u₁ < u₃ ∧ u₂ < u₃ := by
  have A : u₀ < u₁ := by
    by_contra h
    push Not at h
    rcases le_or_gt u₁ u₂ with h12 | h21
    · have t1 : W₀₁ * (u₁ - u₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w01.le (by linarith)
      have t2 : W₁₂ * (u₁ - u₂) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w12.le (by linarith)
      have t3 : W₁₃ * (u₁ - u₃) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w13 (by linarith)
      have e1 : u₁ - u₀ = 0 :=
        (mul_eq_zero.mp (by linarith : W₀₁ * (u₁ - u₀) = 0)).resolve_left w01.ne'
      have e2 : u₁ - u₂ = 0 :=
        (mul_eq_zero.mp (by linarith : W₁₂ * (u₁ - u₂) = 0)).resolve_left w12.ne'
      have : W₂₃ * (u₂ - u₃) < 0 := mul_neg_of_pos_of_neg w23 (by linarith)
      have : W₀₂ * (u₂ - u₀) = 0 := by rw [show u₂ - u₀ = 0 by linarith, mul_zero]
      have : W₁₂ * (u₂ - u₁) = 0 := by rw [show u₂ - u₁ = 0 by linarith, mul_zero]
      linarith
    · have : W₀₂ * (u₂ - u₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w02 (by linarith)
      have : W₁₂ * (u₂ - u₁) < 0 := mul_neg_of_pos_of_neg w12 (by linarith)
      have : W₂₃ * (u₂ - u₃) < 0 := mul_neg_of_pos_of_neg w23 (by linarith)
      linarith
  have B : u₀ < u₂ := by
    by_contra h
    push Not at h
    rcases le_or_gt u₂ u₁ with h21 | h12
    · have : W₀₂ * (u₂ - u₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w02 (by linarith)
      have : W₁₂ * (u₂ - u₁) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w12.le (by linarith)
      have : W₂₃ * (u₂ - u₃) < 0 := mul_neg_of_pos_of_neg w23 (by linarith)
      linarith
    · linarith
  have C : u₁ < u₃ := by
    by_contra h
    push Not at h
    rcases le_or_gt u₂ u₁ with h21 | h12
    · have : 0 < W₀₁ * (u₁ - u₀) := mul_pos w01 (by linarith)
      have : 0 ≤ W₁₂ * (u₁ - u₂) := mul_nonneg w12.le (by linarith)
      have : 0 ≤ W₁₃ * (u₁ - u₃) := mul_nonneg w13 (by linarith)
      linarith
    · have : 0 ≤ W₀₂ * (u₂ - u₀) := mul_nonneg w02 (by linarith)
      have : 0 < W₁₂ * (u₂ - u₁) := mul_pos w12 (by linarith)
      have : 0 < W₂₃ * (u₂ - u₃) := mul_pos w23 (by linarith)
      linarith
  have D : u₂ < u₃ := by
    by_contra h
    push Not at h
    rcases le_or_gt u₁ u₂ with h12 | h21
    · have t2 : 0 ≤ W₁₂ * (u₂ - u₁) := mul_nonneg w12.le (by linarith)
      have t3 : 0 ≤ W₂₃ * (u₂ - u₃) := mul_nonneg w23.le (by linarith)
      have t1 : 0 ≤ W₀₂ * (u₂ - u₀) := mul_nonneg w02 (by linarith)
      have e2 : u₂ - u₁ = 0 :=
        (mul_eq_zero.mp (by linarith : W₁₂ * (u₂ - u₁) = 0)).resolve_left w12.ne'
      linarith
    · linarith
  exact ⟨A, B, C, D⟩

/-- Reduction at machine 1: the reduced cut of machine 0. -/
@[powerlib_foundation] theorem psd_reduce_one_zero {W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃ : ℝ}
    (hQ : ∀ a b c d : ℝ, 0 ≤ W₀₁ * (a - b) ^ 2 + W₀₂ * (a - c) ^ 2 + W₀₃ * (a - d) ^ 2 +
      W₁₂ * (b - c) ^ 2 + W₁₃ * (b - d) ^ 2 + W₂₃ * (c - d) ^ 2)
    (s : 0 < W₀₁ + W₁₂ + W₁₃) :
    0 ≤ (W₀₁ + W₁₂ + W₁₃) * (W₀₂ + W₀₃) + W₀₁ * (W₁₂ + W₁₃) := by
  have h := hQ 1 (W₀₁ / (W₀₁ + W₁₂ + W₁₃)) 0 0
  have e : (W₀₁ + W₁₂ + W₁₃) * (W₀₁ * (1 - W₀₁ / (W₀₁ + W₁₂ + W₁₃)) ^ 2 + W₀₂ * (1 - 0) ^ 2 +
      W₀₃ * (1 - 0) ^ 2 + W₁₂ * (W₀₁ / (W₀₁ + W₁₂ + W₁₃) - 0) ^ 2 +
      W₁₃ * (W₀₁ / (W₀₁ + W₁₂ + W₁₃) - 0) ^ 2 + W₂₃ * (0 - 0) ^ 2) =
      (W₀₁ + W₁₂ + W₁₃) * (W₀₂ + W₀₃) + W₀₁ * (W₁₂ + W₁₃) := by
    field_simp
    ring
  rw [← e]
  exact mul_nonneg s.le h

/-- Reduction at machine 1: the reduced cut of machine 3. -/
@[powerlib_foundation] theorem psd_reduce_one_three {W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃ : ℝ}
    (hQ : ∀ a b c d : ℝ, 0 ≤ W₀₁ * (a - b) ^ 2 + W₀₂ * (a - c) ^ 2 + W₀₃ * (a - d) ^ 2 +
      W₁₂ * (b - c) ^ 2 + W₁₃ * (b - d) ^ 2 + W₂₃ * (c - d) ^ 2)
    (s : 0 < W₀₁ + W₁₂ + W₁₃) :
    0 ≤ (W₀₁ + W₁₂ + W₁₃) * (W₀₃ + W₂₃) + W₁₃ * (W₀₁ + W₁₂) := by
  have h := hQ 0 (W₁₃ / (W₀₁ + W₁₂ + W₁₃)) 0 1
  have e : (W₀₁ + W₁₂ + W₁₃) * (W₀₁ * (0 - W₁₃ / (W₀₁ + W₁₂ + W₁₃)) ^ 2 + W₀₂ * (0 - 0) ^ 2 +
      W₀₃ * (0 - 1) ^ 2 + W₁₂ * (W₁₃ / (W₀₁ + W₁₂ + W₁₃) - 0) ^ 2 +
      W₁₃ * (W₁₃ / (W₀₁ + W₁₂ + W₁₃) - 1) ^ 2 + W₂₃ * (0 - 1) ^ 2) =
      (W₀₁ + W₁₂ + W₁₃) * (W₀₃ + W₂₃) + W₁₃ * (W₀₁ + W₁₂) := by
    field_simp
    ring
  rw [← e]
  exact mul_nonneg s.le h

/-- Reduction at machine 2: the reduced cut of machine 0. -/
@[powerlib_foundation] theorem psd_reduce_two_zero {W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃ : ℝ}
    (hQ : ∀ a b c d : ℝ, 0 ≤ W₀₁ * (a - b) ^ 2 + W₀₂ * (a - c) ^ 2 + W₀₃ * (a - d) ^ 2 +
      W₁₂ * (b - c) ^ 2 + W₁₃ * (b - d) ^ 2 + W₂₃ * (c - d) ^ 2)
    (s : 0 < W₀₂ + W₁₂ + W₂₃) :
    0 ≤ (W₀₂ + W₁₂ + W₂₃) * (W₀₁ + W₀₃) + W₀₂ * (W₁₂ + W₂₃) := by
  have h := hQ 1 0 (W₀₂ / (W₀₂ + W₁₂ + W₂₃)) 0
  have e : (W₀₂ + W₁₂ + W₂₃) * (W₀₁ * (1 - 0) ^ 2 + W₀₂ * (1 - W₀₂ / (W₀₂ + W₁₂ + W₂₃)) ^ 2 +
      W₀₃ * (1 - 0) ^ 2 + W₁₂ * (0 - W₀₂ / (W₀₂ + W₁₂ + W₂₃)) ^ 2 +
      W₁₃ * (0 - 0) ^ 2 + W₂₃ * (W₀₂ / (W₀₂ + W₁₂ + W₂₃) - 0) ^ 2) =
      (W₀₂ + W₁₂ + W₂₃) * (W₀₁ + W₀₃) + W₀₂ * (W₁₂ + W₂₃) := by
    field_simp
    ring
  rw [← e]
  exact mul_nonneg s.le h

/-- Reduction at machine 2: the reduced cut of machine 3. -/
@[powerlib_foundation] theorem psd_reduce_two_three {W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃ : ℝ}
    (hQ : ∀ a b c d : ℝ, 0 ≤ W₀₁ * (a - b) ^ 2 + W₀₂ * (a - c) ^ 2 + W₀₃ * (a - d) ^ 2 +
      W₁₂ * (b - c) ^ 2 + W₁₃ * (b - d) ^ 2 + W₂₃ * (c - d) ^ 2)
    (s : 0 < W₀₂ + W₁₂ + W₂₃) :
    0 ≤ (W₀₂ + W₁₂ + W₂₃) * (W₀₃ + W₁₃) + W₂₃ * (W₀₂ + W₁₂) := by
  have h := hQ 0 0 (W₂₃ / (W₀₂ + W₁₂ + W₂₃)) 1
  have e : (W₀₂ + W₁₂ + W₂₃) * (W₀₁ * (0 - 0) ^ 2 + W₀₂ * (0 - W₂₃ / (W₀₂ + W₁₂ + W₂₃)) ^ 2 +
      W₀₃ * (0 - 1) ^ 2 + W₁₂ * (0 - W₂₃ / (W₀₂ + W₁₂ + W₂₃)) ^ 2 +
      W₁₃ * (0 - 1) ^ 2 + W₂₃ * (W₂₃ / (W₀₂ + W₁₂ + W₂₃) - 1) ^ 2) =
      (W₀₂ + W₁₂ + W₂₃) * (W₀₃ + W₁₃) + W₂₃ * (W₀₂ + W₁₂) := by
    field_simp
    ring
  rw [← e]
  exact mul_nonneg s.le h

/-- One negative line at machine 0 besides `03`: the null direction puts machine 2 (and then
machine 1) above machine 0. -/
@[powerlib_foundation] theorem order_of_neg_02 {W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃ u₀ u₁ u₂ u₃ : ℝ}
    (w01 : 0 < W₀₁) (w12 : 0 < W₁₂) (w23 : 0 < W₂₃) (w13 : 0 ≤ W₁₃)
    (s₁ : 0 < W₀₁ + W₁₂ + W₁₃)
    (P₁ : 0 ≤ (W₀₁ + W₁₂ + W₁₃) * (W₀₂ + W₀₃) + W₀₁ * (W₁₂ + W₁₃))
    (N₀ : W₀₁ * (u₀ - u₁) + W₀₂ * (u₀ - u₂) + W₀₃ * (u₀ - u₃) = 0)
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0) (h03 : u₀ < u₃) :
    u₀ < u₂ ∧ u₀ < u₁ := by
  set s := W₀₁ + W₁₂ + W₁₃ with hs
  set a := s * W₀₂ + W₀₁ * W₁₂
  set b := s * W₀₃ + W₀₁ * W₁₃
  set c := s * W₂₃ + W₁₂ * W₁₃
  have hc : 0 < c := by
    have := mul_pos s₁ w23
    have := mul_nonneg w12.le w13
    linarith
  have R₀ : a * (u₀ - u₂) + b * (u₀ - u₃) = 0 := by
    linear_combination s * N₀ + W₀₁ * N₁
  have R₂ : a * (u₂ - u₀) + c * (u₂ - u₃) = 0 := by
    linear_combination s * N₂ + W₁₂ * N₁
  have hab : 0 ≤ a + b := by simp only [a, b]; linarith
  have h2 : u₀ < u₂ := by
    by_contra h
    push Not at h
    have hcpos : 0 < a * (u₂ - u₀) := by
      have : c * (u₂ - u₃) < 0 := mul_neg_of_pos_of_neg hc (by linarith)
      linarith
    have ha : a < 0 := by
      by_contra ha
      push Not at ha
      have : a * (u₂ - u₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (by linarith)
      linarith
    have hb : b < 0 := by
      by_contra hb
      push Not at hb
      have : b * (u₀ - u₃) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (by linarith)
      linarith
    linarith
  refine ⟨h2, ?_⟩
  by_contra h
  push Not at h
  have : W₀₁ * (u₁ - u₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w01.le (by linarith)
  have : W₁₂ * (u₁ - u₂) < 0 := mul_neg_of_pos_of_neg w12 (by linarith)
  have : W₁₃ * (u₁ - u₃) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w13 (by linarith)
  linarith

/-- Negative lines `02` and `13` (besides `03`): the null direction is strictly monotone. -/
@[powerlib_foundation] theorem order_of_neg_02_13 {W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃ u₀ u₁ u₂ u₃ : ℝ}
    (w12 : 0 < W₁₂) (w02 : W₀₂ < 0) (w03 : W₀₃ < 0) (w13 : W₁₃ < 0) (w01 : 0 < W₀₁)
    (w23 : 0 < W₂₃)
    (s₁ : 0 < W₀₁ + W₁₂ + W₁₃) (s₂ : 0 < W₀₂ + W₁₂ + W₂₃)
    (P₁ : 0 ≤ (W₀₁ + W₁₂ + W₁₃) * (W₀₂ + W₀₃) + W₀₁ * (W₁₂ + W₁₃))
    (P₂ : 0 ≤ (W₀₁ + W₁₂ + W₁₃) * (W₀₃ + W₂₃) + W₁₃ * (W₀₁ + W₁₂))
    (P₃ : 0 ≤ (W₀₂ + W₁₂ + W₂₃) * (W₀₁ + W₀₃) + W₀₂ * (W₁₂ + W₂₃))
    (P₄ : 0 ≤ (W₀₂ + W₁₂ + W₂₃) * (W₀₃ + W₁₃) + W₂₃ * (W₀₂ + W₁₂))
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0) (h03 : u₀ < u₃) :
    u₀ < u₁ ∧ u₁ < u₂ ∧ u₂ < u₃ := by
  -- reduction at machine 1
  set s := W₀₁ + W₁₂ + W₁₃ with hs
  set a := s * W₀₂ + W₀₁ * W₁₂
  set b := s * W₀₃ + W₀₁ * W₁₃
  set c := s * W₂₃ + W₁₂ * W₁₃
  have hb : b < 0 := by
    have := mul_pos s₁ (neg_pos.mpr w03)
    have := mul_pos w01 (neg_pos.mpr w13)
    simp only [b]; linarith
  have ha : 0 < a := by simp only [a, b] at *; linarith
  have hc : 0 < c := by simp only [c, b] at *; linarith
  have R₂ : a * (u₂ - u₀) + c * (u₂ - u₃) = 0 := by
    linear_combination s * N₂ + W₁₂ * N₁
  have h02 : u₀ < u₂ := by
    by_contra h
    push Not at h
    have : a * (u₂ - u₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le (by linarith)
    have : c * (u₂ - u₃) < 0 := mul_neg_of_pos_of_neg hc (by linarith)
    linarith
  have h23 : u₂ < u₃ := by
    by_contra h
    push Not at h
    have : 0 < a * (u₂ - u₀) := mul_pos ha (by linarith)
    have : 0 ≤ c * (u₂ - u₃) := mul_nonneg hc.le (by linarith)
    linarith
  -- reduction at machine 2
  set s' := W₀₂ + W₁₂ + W₂₃ with hs'
  set a' := s' * W₀₁ + W₀₂ * W₁₂
  set b' := s' * W₀₃ + W₀₂ * W₂₃
  set c' := s' * W₁₃ + W₁₂ * W₂₃
  have hb' : b' < 0 := by
    have := mul_pos s₂ (neg_pos.mpr w03)
    have := mul_pos (neg_pos.mpr w02) w23
    simp only [b']; nlinarith
  have ha' : 0 < a' := by simp only [a', b'] at *; linarith
  have hc' : 0 < c' := by simp only [c', b'] at *; linarith
  have R₁ : a' * (u₁ - u₀) + c' * (u₁ - u₃) = 0 := by
    linear_combination s' * N₁ + W₁₂ * N₂
  have h01 : u₀ < u₁ := by
    by_contra h
    push Not at h
    have : a' * (u₁ - u₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha'.le (by linarith)
    have : c' * (u₁ - u₃) < 0 := mul_neg_of_pos_of_neg hc' (by linarith)
    linarith
  have h13 : u₁ < u₃ := by
    by_contra h
    push Not at h
    have : 0 < a' * (u₁ - u₀) := mul_pos ha' (by linarith)
    have : 0 ≤ c' * (u₁ - u₃) := mul_nonneg hc'.le (by linarith)
    linarith
  refine ⟨h01, ?_, h23⟩
  by_contra h
  push Not at h
  have : W₀₂ * (u₂ - u₀) < 0 := mul_neg_of_neg_of_pos w02 (by linarith)
  have : W₁₂ * (u₂ - u₁) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w12.le (by linarith)
  have : W₂₃ * (u₂ - u₃) < 0 := mul_neg_of_pos_of_neg w23 (by linarith)
  linarith

/-! ## Sign cases of the lines `02` and `13` -/

/-- `cos x > 0` on `[0, π/2)`. -/
@[powerlib_foundation]
theorem cos_pos_of_nonneg_of_lt {x : ℝ} (h0 : 0 ≤ x) (h1 : x < π / 2) : 0 < Real.cos x :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩

/-- Line flow from weight: `B sin α = tan α · B cos α` when `cos α ≠ 0`. -/
@[powerlib_foundation]
theorem flow_eq_tan {B α W F : ℝ} (hW : W = B * Real.cos α) (hF : F = B * Real.sin α)
    (hc : Real.cos α ≠ 0) : F = Real.tan α * W := by
  rw [hW, hF, Real.tan_eq_sin_div_cos]
  field_simp

/-- Sorted lifted angles, case `02` and `13` nonnegative. -/
@[powerlib_foundation]
theorem sorted_case_nonneg {γ₁ γ₂ γ₃ B₀₁ B₀₂ B₀₃ B₁₂ B₁₃ B₂₃ W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃
      F₀₁ F₀₂ F₀₃ F₁₂ F₁₃ F₂₃ u₀ u₁ u₂ u₃ : ℝ}
    (hγ₁ : 0 ≤ γ₁ ∧ γ₁ < π / 2) (hγ₂ : 0 ≤ γ₂ ∧ γ₂ < π / 2) (hγ₃ : 0 ≤ γ₃ ∧ γ₃ < π / 2)
    (hσ : π / 2 < γ₁ + γ₂ + γ₃) (h02 : γ₁ + γ₂ ≤ π / 2) (h13 : γ₂ + γ₃ ≤ π / 2)
    (b01 : 0 < B₀₁) (b02 : 0 < B₀₂) (b03 : 0 < B₀₃) (b12 : 0 < B₁₂) (b13 : 0 < B₁₃)
    (b23 : 0 < B₂₃)
    (hW₀₁ : W₀₁ = B₀₁ * Real.cos γ₁) (hW₀₂ : W₀₂ = B₀₂ * Real.cos (γ₁ + γ₂))
    (hW₀₃ : W₀₃ = B₀₃ * Real.cos (γ₁ + γ₂ + γ₃)) (hW₁₂ : W₁₂ = B₁₂ * Real.cos γ₂)
    (hW₁₃ : W₁₃ = B₁₃ * Real.cos (γ₂ + γ₃)) (hW₂₃ : W₂₃ = B₂₃ * Real.cos γ₃)
    (hF₀₁ : F₀₁ = B₀₁ * Real.sin γ₁) (hF₀₂ : F₀₂ = B₀₂ * Real.sin (γ₁ + γ₂))
    (hF₀₃ : F₀₃ = B₀₃ * Real.sin (γ₁ + γ₂ + γ₃)) (hF₁₂ : F₁₂ = B₁₂ * Real.sin γ₂)
    (hF₁₃ : F₁₃ = B₁₃ * Real.sin (γ₂ + γ₃)) (hF₂₃ : F₂₃ = B₂₃ * Real.sin γ₃)
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0)
    (N₃ : W₀₃ * (u₃ - u₀) + W₁₃ * (u₃ - u₁) + W₂₃ * (u₃ - u₂) = 0) (h03 : u₀ < u₃) :
    0 < F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 := by
  have pi := Real.pi_pos
  have w01 : 0 < W₀₁ := by rw [hW₀₁]; exact mul_pos b01 (cos_pos_of_nonneg_of_lt hγ₁.1 hγ₁.2)
  have w12 : 0 < W₁₂ := by rw [hW₁₂]; exact mul_pos b12 (cos_pos_of_nonneg_of_lt hγ₂.1 hγ₂.2)
  have w23 : 0 < W₂₃ := by rw [hW₂₃]; exact mul_pos b23 (cos_pos_of_nonneg_of_lt hγ₃.1 hγ₃.2)
  have w02 : 0 ≤ W₀₂ := by
    rw [hW₀₂]; exact mul_nonneg b02.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith, h02⟩)
  have w13 : 0 ≤ W₁₃ := by
    rw [hW₁₃]; exact mul_nonneg b13.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith, h13⟩)
  have c03 : Real.cos (γ₁ + γ₂ + γ₃) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hσ (by linarith)
  have w03 : W₀₃ < 0 := by rw [hW₀₃]; exact mul_neg_of_pos_of_neg b03 c03
  have f01 : 0 ≤ F₀₁ := by
    rw [hF₀₁]; exact mul_nonneg b01.le (Real.sin_nonneg_of_nonneg_of_le_pi hγ₁.1 (by linarith))
  have f02 : 0 ≤ F₀₂ := by
    rw [hF₀₂]; exact mul_nonneg b02.le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith))
  have f03 : 0 < F₀₃ := by
    rw [hF₀₃]; exact mul_pos b03 (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have f12 : 0 ≤ F₁₂ := by
    rw [hF₁₂]; exact mul_nonneg b12.le (Real.sin_nonneg_of_nonneg_of_le_pi hγ₂.1 (by linarith))
  have f13 : 0 ≤ F₁₃ := by
    rw [hF₁₃]; exact mul_nonneg b13.le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith))
  have f23 : 0 ≤ F₂₃ := by
    rw [hF₂₃]; exact mul_nonneg b23.le (Real.sin_nonneg_of_nonneg_of_le_pi hγ₃.1 (by linarith))
  obtain ⟨o01, o02, o13, o23⟩ := order_of_nonneg w01 w12 w23 w02 w13 N₁ N₂ h03
  rcases le_or_gt u₁ u₂ with h12 | h21
  · exact cubic_pos_of_monotone f01 f02 f03 f12 f13 f23 o01.le h12 o23.le h03
  have l02 : γ₁ + γ₂ < π / 2 := by
    rcases h02.lt_or_eq with h | h
    · exact h
    · exfalso
      have : W₀₂ = 0 := by rw [hW₀₂, h, Real.cos_pi_div_two, mul_zero]
      have : W₁₂ * (u₂ - u₁) < 0 := mul_neg_of_pos_of_neg w12 (by linarith)
      have : W₂₃ * (u₂ - u₃) < 0 := mul_neg_of_pos_of_neg w23 (by linarith)
      have : W₀₂ * (u₂ - u₀) = 0 := by rw [‹W₀₂ = 0›, zero_mul]
      linarith
  have l13 : γ₂ + γ₃ < π / 2 := by
    rcases h13.lt_or_eq with h | h
    · exact h
    · exfalso
      have : W₁₃ = 0 := by rw [hW₁₃, h, Real.cos_pi_div_two, mul_zero]
      have : 0 < W₀₁ * (u₁ - u₀) := mul_pos w01 (by linarith)
      have : 0 < W₁₂ * (u₁ - u₂) := mul_pos w12 (by linarith)
      have : W₁₃ * (u₁ - u₃) = 0 := by rw [‹W₁₃ = 0›, zero_mul]
      linarith
  exact cubic_pos_cross hγ₂ ⟨by linarith, l02⟩ ⟨by linarith, l13⟩ hσ w01 w12 w23
    (flow_eq_tan hW₀₂ hF₀₂ (cos_pos_of_nonneg_of_lt (by linarith) l02).ne')
    (flow_eq_tan hW₁₂ hF₁₂ (cos_pos_of_nonneg_of_lt hγ₂.1 hγ₂.2).ne')
    (flow_eq_tan hW₁₃ hF₁₃ (cos_pos_of_nonneg_of_lt (by linarith) l13).ne')
    (flow_eq_tan hW₀₃ hF₀₃ c03.ne) f01 f23 N₁ N₂ N₃ o02 h21 o13

/-- Sorted lifted angles, case `02` negative and `13` nonnegative. -/
@[powerlib_foundation]
theorem sorted_case_neg {γ₁ γ₂ γ₃ B₀₁ B₀₂ B₀₃ B₁₂ B₁₃ B₂₃ W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃
      F₀₁ F₀₂ F₀₃ F₁₂ F₁₃ F₂₃ u₀ u₁ u₂ u₃ : ℝ}
    (hγ₁ : 0 ≤ γ₁ ∧ γ₁ < π / 2) (hγ₂ : 0 ≤ γ₂ ∧ γ₂ < π / 2) (hγ₃ : 0 ≤ γ₃ ∧ γ₃ < π / 2)
    (h02 : π / 2 < γ₁ + γ₂) (h13 : γ₂ + γ₃ ≤ π / 2)
    (b01 : 0 < B₀₁) (b02 : 0 < B₀₂) (b03 : 0 < B₀₃) (b12 : 0 < B₁₂) (b13 : 0 < B₁₃)
    (b23 : 0 < B₂₃)
    (hW₀₁ : W₀₁ = B₀₁ * Real.cos γ₁) (hW₀₂ : W₀₂ = B₀₂ * Real.cos (γ₁ + γ₂))
    (hW₀₃ : W₀₃ = B₀₃ * Real.cos (γ₁ + γ₂ + γ₃)) (hW₁₂ : W₁₂ = B₁₂ * Real.cos γ₂)
    (hW₁₃ : W₁₃ = B₁₃ * Real.cos (γ₂ + γ₃)) (hW₂₃ : W₂₃ = B₂₃ * Real.cos γ₃)
    (hF₀₁ : F₀₁ = B₀₁ * Real.sin γ₁) (hF₀₂ : F₀₂ = B₀₂ * Real.sin (γ₁ + γ₂))
    (hF₀₃ : F₀₃ = B₀₃ * Real.sin (γ₁ + γ₂ + γ₃)) (hF₁₂ : F₁₂ = B₁₂ * Real.sin γ₂)
    (hF₁₃ : F₁₃ = B₁₃ * Real.sin (γ₂ + γ₃)) (hF₂₃ : F₂₃ = B₂₃ * Real.sin γ₃)
    (N₀ : W₀₁ * (u₀ - u₁) + W₀₂ * (u₀ - u₂) + W₀₃ * (u₀ - u₃) = 0)
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0)
    (N₃ : W₀₃ * (u₃ - u₀) + W₁₃ * (u₃ - u₁) + W₂₃ * (u₃ - u₂) = 0)
    (s₁ : 0 < W₀₁ + W₁₂ + W₁₃)
    (P₁ : 0 ≤ (W₀₁ + W₁₂ + W₁₃) * (W₀₂ + W₀₃) + W₀₁ * (W₁₂ + W₁₃)) (h03 : u₀ < u₃) :
    0 < F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 := by
  have pi := Real.pi_pos
  have w01 : 0 < W₀₁ := by rw [hW₀₁]; exact mul_pos b01 (cos_pos_of_nonneg_of_lt hγ₁.1 hγ₁.2)
  have w12 : 0 < W₁₂ := by rw [hW₁₂]; exact mul_pos b12 (cos_pos_of_nonneg_of_lt hγ₂.1 hγ₂.2)
  have w23 : 0 < W₂₃ := by rw [hW₂₃]; exact mul_pos b23 (cos_pos_of_nonneg_of_lt hγ₃.1 hγ₃.2)
  have w13 : 0 ≤ W₁₃ := by
    rw [hW₁₃]; exact mul_nonneg b13.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith, h13⟩)
  have c02 : Real.cos (γ₁ + γ₂) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h02 (by linarith)
  have w02 : W₀₂ < 0 := by rw [hW₀₂]; exact mul_neg_of_pos_of_neg b02 c02
  have c03 : Real.cos (γ₁ + γ₂ + γ₃) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
  have w03 : W₀₃ < 0 := by rw [hW₀₃]; exact mul_neg_of_pos_of_neg b03 c03
  have f01 : 0 ≤ F₀₁ := by
    rw [hF₀₁]; exact mul_nonneg b01.le (Real.sin_nonneg_of_nonneg_of_le_pi hγ₁.1 (by linarith))
  have f02 : 0 ≤ F₀₂ := by
    rw [hF₀₂]; exact mul_nonneg b02.le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith))
  have f03 : 0 < F₀₃ := by
    rw [hF₀₃]; exact mul_pos b03 (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have f12 : 0 ≤ F₁₂ := by
    rw [hF₁₂]; exact mul_nonneg b12.le (Real.sin_nonneg_of_nonneg_of_le_pi hγ₂.1 (by linarith))
  have f13 : 0 ≤ F₁₃ := by
    rw [hF₁₃]; exact mul_nonneg b13.le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith))
  have f23 : 0 ≤ F₂₃ := by
    rw [hF₂₃]; exact mul_nonneg b23.le (Real.sin_nonneg_of_nonneg_of_le_pi hγ₃.1 (by linarith))
  obtain ⟨o02, o01⟩ := order_of_neg_02 w01 w12 w23 w13 s₁ P₁ N₀ N₁ N₂ h03
  rcases h13.lt_or_eq with l13 | e13
  · have w13' : 0 < W₁₃ := by
      rw [hW₁₃]; exact mul_pos b13 (cos_pos_of_nonneg_of_lt (by linarith) l13)
    rcases le_or_gt u₂ u₃ with h23 | h32
    · have o12 : u₁ < u₂ := by
        by_contra h
        push Not at h
        have : W₀₂ * (u₂ - u₀) < 0 := mul_neg_of_neg_of_pos w02 (by linarith)
        have : W₁₂ * (u₂ - u₁) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w12.le (by linarith)
        have : W₂₃ * (u₂ - u₃) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w23.le (by linarith)
        linarith
      exact cubic_pos_of_monotone f01 f02 f03 f12 f13 f23 o01.le o12.le h23 h03
    · have o13 : u₁ < u₃ := by
        by_contra h
        push Not at h
        have : W₀₃ * (u₃ - u₀) < 0 := mul_neg_of_neg_of_pos w03 (by linarith)
        have : W₁₃ * (u₃ - u₁) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w13 (by linarith)
        have : W₂₃ * (u₃ - u₂) < 0 := mul_neg_of_pos_of_neg w23 (by linarith)
        linarith
      exact cubic_pos_two_neg hγ₁ hγ₃ ⟨by linarith, l13⟩ ⟨h02, by linarith⟩ w12 w23
        w03 (flow_eq_tan hW₀₁ hF₀₁ (cos_pos_of_nonneg_of_lt hγ₁.1 hγ₁.2).ne')
        (flow_eq_tan hW₀₂ hF₀₂ c02.ne)
        (flow_eq_tan hW₁₃ hF₁₃ (cos_pos_of_nonneg_of_lt (by linarith) l13).ne')
        (flow_eq_tan hW₂₃ hF₂₃ (cos_pos_of_nonneg_of_lt hγ₃.1 hγ₃.2).ne') f03.le f12 N₁ N₂ N₃
        o01 o13 h32
  · have w13' : W₁₃ = 0 := by rw [hW₁₃, e13, Real.cos_pi_div_two, mul_zero]
    have o12 : u₁ < u₂ := by
      have : 0 < W₀₁ * (u₁ - u₀) := mul_pos w01 (by linarith)
      have : W₁₃ * (u₁ - u₃) = 0 := by rw [w13', zero_mul]
      by_contra h
      push Not at h
      have : 0 ≤ W₁₂ * (u₁ - u₂) := mul_nonneg w12.le (by linarith)
      linarith
    have o23 : u₂ < u₃ := by
      have : W₀₃ * (u₃ - u₀) < 0 := mul_neg_of_neg_of_pos w03 (by linarith)
      have : W₁₃ * (u₃ - u₁) = 0 := by rw [w13', zero_mul]
      by_contra h
      push Not at h
      have : W₂₃ * (u₃ - u₂) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos w23.le (by linarith)
      linarith
    exact cubic_pos_of_monotone f01 f02 f03 f12 f13 f23 o01.le o12.le o23.le h03

/-- Sorted lifted angles, case `02` and `13` both negative. -/
@[powerlib_foundation]
theorem sorted_case_neg_neg {γ₁ γ₂ γ₃ B₀₁ B₀₂ B₀₃ B₁₂ B₁₃ B₂₃ W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃
      F₀₁ F₀₂ F₀₃ F₁₂ F₁₃ F₂₃ u₀ u₁ u₂ u₃ : ℝ}
    (hγ₁ : 0 ≤ γ₁ ∧ γ₁ < π / 2) (hγ₂ : 0 ≤ γ₂ ∧ γ₂ < π / 2) (hγ₃ : 0 ≤ γ₃ ∧ γ₃ < π / 2)
    (h02 : π / 2 < γ₁ + γ₂) (h13 : π / 2 < γ₂ + γ₃)
    (b01 : 0 < B₀₁) (b02 : 0 < B₀₂) (b03 : 0 < B₀₃) (b12 : 0 < B₁₂) (b13 : 0 < B₁₃)
    (b23 : 0 < B₂₃)
    (hW₀₁ : W₀₁ = B₀₁ * Real.cos γ₁) (hW₀₂ : W₀₂ = B₀₂ * Real.cos (γ₁ + γ₂))
    (hW₀₃ : W₀₃ = B₀₃ * Real.cos (γ₁ + γ₂ + γ₃)) (hW₁₂ : W₁₂ = B₁₂ * Real.cos γ₂)
    (hW₁₃ : W₁₃ = B₁₃ * Real.cos (γ₂ + γ₃)) (hW₂₃ : W₂₃ = B₂₃ * Real.cos γ₃)
    (hF₀₁ : F₀₁ = B₀₁ * Real.sin γ₁) (hF₀₂ : F₀₂ = B₀₂ * Real.sin (γ₁ + γ₂))
    (hF₀₃ : F₀₃ = B₀₃ * Real.sin (γ₁ + γ₂ + γ₃)) (hF₁₂ : F₁₂ = B₁₂ * Real.sin γ₂)
    (hF₁₃ : F₁₃ = B₁₃ * Real.sin (γ₂ + γ₃)) (hF₂₃ : F₂₃ = B₂₃ * Real.sin γ₃)
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0)
    (N₃ : W₀₃ * (u₃ - u₀) + W₁₃ * (u₃ - u₁) + W₂₃ * (u₃ - u₂) = 0)
    (s₁ : 0 < W₀₁ + W₁₂ + W₁₃) (s₂ : 0 < W₀₂ + W₁₂ + W₂₃)
    (P₁ : 0 ≤ (W₀₁ + W₁₂ + W₁₃) * (W₀₂ + W₀₃) + W₀₁ * (W₁₂ + W₁₃))
    (P₂ : 0 ≤ (W₀₁ + W₁₂ + W₁₃) * (W₀₃ + W₂₃) + W₁₃ * (W₀₁ + W₁₂))
    (P₃ : 0 ≤ (W₀₂ + W₁₂ + W₂₃) * (W₀₁ + W₀₃) + W₀₂ * (W₁₂ + W₂₃))
    (P₄ : 0 ≤ (W₀₂ + W₁₂ + W₂₃) * (W₀₃ + W₁₃) + W₂₃ * (W₀₂ + W₁₂)) (h03 : u₀ < u₃) :
    0 < F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 := by
  have pi := Real.pi_pos
  have w01 : 0 < W₀₁ := by rw [hW₀₁]; exact mul_pos b01 (cos_pos_of_nonneg_of_lt hγ₁.1 hγ₁.2)
  have w12 : 0 < W₁₂ := by rw [hW₁₂]; exact mul_pos b12 (cos_pos_of_nonneg_of_lt hγ₂.1 hγ₂.2)
  have w23 : 0 < W₂₃ := by rw [hW₂₃]; exact mul_pos b23 (cos_pos_of_nonneg_of_lt hγ₃.1 hγ₃.2)
  have c02 : Real.cos (γ₁ + γ₂) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h02 (by linarith)
  have w02 : W₀₂ < 0 := by rw [hW₀₂]; exact mul_neg_of_pos_of_neg b02 c02
  have c13 : Real.cos (γ₂ + γ₃) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h13 (by linarith)
  have w13 : W₁₃ < 0 := by rw [hW₁₃]; exact mul_neg_of_pos_of_neg b13 c13
  have c03 : Real.cos (γ₁ + γ₂ + γ₃) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
  have w03 : W₀₃ < 0 := by rw [hW₀₃]; exact mul_neg_of_pos_of_neg b03 c03
  have f02 : 0 ≤ F₀₂ := by
    rw [hF₀₂]; exact mul_nonneg b02.le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith))
  have f13 : 0 ≤ F₁₃ := by
    rw [hF₁₃]; exact mul_nonneg b13.le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith))
  obtain ⟨o01, o12, o23⟩ := order_of_neg_02_13 w12 w02 w03 w13 w01 w23 s₁ s₂ P₁ P₂ P₃ P₄
    N₁ N₂ h03
  exact cubic_pos_three_neg hγ₁ hγ₂ hγ₃ (by linarith) w02 w03 w13
    (flow_eq_tan hW₀₁ hF₀₁ (cos_pos_of_nonneg_of_lt hγ₁.1 hγ₁.2).ne')
    (flow_eq_tan hW₁₂ hF₁₂ (cos_pos_of_nonneg_of_lt hγ₂.1 hγ₂.2).ne')
    (flow_eq_tan hW₂₃ hF₂₃ (cos_pos_of_nonneg_of_lt hγ₃.1 hγ₃.2).ne')
    (flow_eq_tan hW₀₃ hF₀₃ c03.ne) f02 f13 N₁ N₂ N₃ o01 o12 o23

/-- **Sorted lifted angles: the cubic term is positive along a null direction rising from machine
`0` to machine `3`.** -/
@[powerlib_foundation]
theorem sorted_cubic_pos {γ₁ γ₂ γ₃ B₀₁ B₀₂ B₀₃ B₁₂ B₁₃ B₂₃ W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃
      F₀₁ F₀₂ F₀₃ F₁₂ F₁₃ F₂₃ u₀ u₁ u₂ u₃ : ℝ}
    (hγ₁ : 0 ≤ γ₁ ∧ γ₁ < π / 2) (hγ₂ : 0 ≤ γ₂ ∧ γ₂ < π / 2) (hγ₃ : 0 ≤ γ₃ ∧ γ₃ < π / 2)
    (hσ : π / 2 < γ₁ + γ₂ + γ₃)
    (b01 : 0 < B₀₁) (b02 : 0 < B₀₂) (b03 : 0 < B₀₃) (b12 : 0 < B₁₂) (b13 : 0 < B₁₃)
    (b23 : 0 < B₂₃)
    (hW₀₁ : W₀₁ = B₀₁ * Real.cos γ₁) (hW₀₂ : W₀₂ = B₀₂ * Real.cos (γ₁ + γ₂))
    (hW₀₃ : W₀₃ = B₀₃ * Real.cos (γ₁ + γ₂ + γ₃)) (hW₁₂ : W₁₂ = B₁₂ * Real.cos γ₂)
    (hW₁₃ : W₁₃ = B₁₃ * Real.cos (γ₂ + γ₃)) (hW₂₃ : W₂₃ = B₂₃ * Real.cos γ₃)
    (hF₀₁ : F₀₁ = B₀₁ * Real.sin γ₁) (hF₀₂ : F₀₂ = B₀₂ * Real.sin (γ₁ + γ₂))
    (hF₀₃ : F₀₃ = B₀₃ * Real.sin (γ₁ + γ₂ + γ₃)) (hF₁₂ : F₁₂ = B₁₂ * Real.sin γ₂)
    (hF₁₃ : F₁₃ = B₁₃ * Real.sin (γ₂ + γ₃)) (hF₂₃ : F₂₃ = B₂₃ * Real.sin γ₃)
    (N₀ : W₀₁ * (u₀ - u₁) + W₀₂ * (u₀ - u₂) + W₀₃ * (u₀ - u₃) = 0)
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0)
    (N₃ : W₀₃ * (u₃ - u₀) + W₁₃ * (u₃ - u₁) + W₂₃ * (u₃ - u₂) = 0)
    (s₁ : 0 < W₀₁ + W₁₂ + W₁₃) (s₂ : 0 < W₀₂ + W₁₂ + W₂₃)
    (P₁ : 0 ≤ (W₀₁ + W₁₂ + W₁₃) * (W₀₂ + W₀₃) + W₀₁ * (W₁₂ + W₁₃))
    (P₂ : 0 ≤ (W₀₁ + W₁₂ + W₁₃) * (W₀₃ + W₂₃) + W₁₃ * (W₀₁ + W₁₂))
    (P₃ : 0 ≤ (W₀₂ + W₁₂ + W₂₃) * (W₀₁ + W₀₃) + W₀₂ * (W₁₂ + W₂₃))
    (P₄ : 0 ≤ (W₀₂ + W₁₂ + W₂₃) * (W₀₃ + W₁₃) + W₂₃ * (W₀₂ + W₁₂)) (h03 : u₀ < u₃) :
    0 < F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 := by
  rcases le_or_gt (γ₁ + γ₂) (π / 2) with h02 | h02 <;>
    rcases le_or_gt (γ₂ + γ₃) (π / 2) with h13 | h13
  · exact sorted_case_nonneg hγ₁ hγ₂ hγ₃ hσ h02 h13 b01 b02 b03 b12 b13 b23 hW₀₁ hW₀₂ hW₀₃
      hW₁₂ hW₁₃ hW₂₃ hF₀₁ hF₀₂ hF₀₃ hF₁₂ hF₁₃ hF₂₃ N₁ N₂ N₃ h03
  · -- the mirror image (reverse the machines, negate the direction) of the next case
    have e3 : γ₃ + γ₂ + γ₁ = γ₁ + γ₂ + γ₃ := by ring
    have := sorted_case_neg (γ₁ := γ₃) (γ₂ := γ₂) (γ₃ := γ₁) (B₀₁ := B₂₃) (B₀₂ := B₁₃)
      (B₀₃ := B₀₃) (B₁₂ := B₁₂) (B₁₃ := B₀₂) (B₂₃ := B₀₁) (W₀₁ := W₂₃) (W₀₂ := W₁₃)
      (W₀₃ := W₀₃) (W₁₂ := W₁₂) (W₁₃ := W₀₂) (W₂₃ := W₀₁) (F₀₁ := F₂₃) (F₀₂ := F₁₃)
      (F₀₃ := F₀₃) (F₁₂ := F₁₂) (F₁₃ := F₀₂) (F₂₃ := F₀₁) (u₀ := -u₃) (u₁ := -u₂)
      (u₂ := -u₁) (u₃ := -u₀) hγ₃ hγ₂ hγ₁ (by linarith) (by linarith) b23 b13 b03 b12 b02 b01
      hW₂₃ (by rw [hW₁₃, add_comm]) (by rw [hW₀₃, e3]) hW₁₂ (by rw [hW₀₂, add_comm]) hW₀₁
      hF₂₃ (by rw [hF₁₃, add_comm]) (by rw [hF₀₃, e3]) hF₁₂ (by rw [hF₀₂, add_comm]) hF₀₁
      (by linear_combination -N₃) (by linear_combination -N₂) (by linear_combination -N₁)
      (by linear_combination -N₀) (by linarith) (by convert P₄ using 1; ring) (by linarith)
    convert this using 1
    ring
  · exact sorted_case_neg hγ₁ hγ₂ hγ₃ h02 h13 b01 b02 b03 b12 b13 b23 hW₀₁ hW₀₂ hW₀₃
      hW₁₂ hW₁₃ hW₂₃ hF₀₁ hF₀₂ hF₀₃ hF₁₂ hF₁₃ hF₂₃ N₀ N₁ N₂ N₃ s₁ P₁ h03
  · exact sorted_case_neg_neg hγ₁ hγ₂ hγ₃ h02 h13 b01 b02 b03 b12 b13 b23 hW₀₁ hW₀₂ hW₀₃
      hW₁₂ hW₁₃ hW₂₃ hF₀₁ hF₀₂ hF₀₃ hF₁₂ hF₁₃ hF₂₃ N₁ N₂ N₃ s₁ s₂ P₁ P₂ P₃ P₄ h03

/-- **Four coupled machines in sorted lifted angles: the cubic term is nonzero along every
non-constant null direction.** The machines are labelled by increasing lifted angles
`0, γ₁, γ₁ + γ₂, γ₁ + γ₂ + γ₃` (total spread at most `3π/2`), all six pairs are coupled, the
Hessian form is positive semidefinite with the null direction `u`, and the cuts used below have
positive total weight. -/
@[powerlib_foundation]
theorem sorted_cubic_ne_zero {γ₁ γ₂ γ₃ B₀₁ B₀₂ B₀₃ B₁₂ B₁₃ B₂₃ W₀₁ W₀₂ W₀₃ W₁₂ W₁₃ W₂₃
      F₀₁ F₀₂ F₀₃ F₁₂ F₁₃ F₂₃ u₀ u₁ u₂ u₃ : ℝ}
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂) (hγ₃ : 0 ≤ γ₃) (hspread : γ₁ + γ₂ + γ₃ ≤ π + π / 2)
    (b01 : 0 < B₀₁) (b02 : 0 < B₀₂) (b03 : 0 < B₀₃) (b12 : 0 < B₁₂) (b13 : 0 < B₁₃)
    (b23 : 0 < B₂₃)
    (hW₀₁ : W₀₁ = B₀₁ * Real.cos γ₁) (hW₀₂ : W₀₂ = B₀₂ * Real.cos (γ₁ + γ₂))
    (hW₀₃ : W₀₃ = B₀₃ * Real.cos (γ₁ + γ₂ + γ₃)) (hW₁₂ : W₁₂ = B₁₂ * Real.cos γ₂)
    (hW₁₃ : W₁₃ = B₁₃ * Real.cos (γ₂ + γ₃)) (hW₂₃ : W₂₃ = B₂₃ * Real.cos γ₃)
    (hF₀₁ : F₀₁ = B₀₁ * Real.sin γ₁) (hF₀₂ : F₀₂ = B₀₂ * Real.sin (γ₁ + γ₂))
    (hF₀₃ : F₀₃ = B₀₃ * Real.sin (γ₁ + γ₂ + γ₃)) (hF₁₂ : F₁₂ = B₁₂ * Real.sin γ₂)
    (hF₁₃ : F₁₃ = B₁₃ * Real.sin (γ₂ + γ₃)) (hF₂₃ : F₂₃ = B₂₃ * Real.sin γ₃)
    (hc₀ : 0 < W₀₁ + W₀₂ + W₀₃) (hc₀₁ : 0 < W₀₂ + W₀₃ + W₁₂ + W₁₃)
    (hc₃ : 0 < W₀₃ + W₁₃ + W₂₃) (hc₁ : 0 < W₀₁ + W₁₂ + W₁₃) (hc₂ : 0 < W₀₂ + W₁₂ + W₂₃)
    (hQ : ∀ a b c d : ℝ, 0 ≤ W₀₁ * (a - b) ^ 2 + W₀₂ * (a - c) ^ 2 + W₀₃ * (a - d) ^ 2 +
      W₁₂ * (b - c) ^ 2 + W₁₃ * (b - d) ^ 2 + W₂₃ * (c - d) ^ 2)
    (N₀ : W₀₁ * (u₀ - u₁) + W₀₂ * (u₀ - u₂) + W₀₃ * (u₀ - u₃) = 0)
    (N₁ : W₀₁ * (u₁ - u₀) + W₁₂ * (u₁ - u₂) + W₁₃ * (u₁ - u₃) = 0)
    (N₂ : W₀₂ * (u₂ - u₀) + W₁₂ * (u₂ - u₁) + W₂₃ * (u₂ - u₃) = 0)
    (N₃ : W₀₃ * (u₃ - u₀) + W₁₃ * (u₃ - u₁) + W₂₃ * (u₃ - u₂) = 0)
    (hu : ¬ (u₀ = u₁ ∧ u₁ = u₂ ∧ u₂ = u₃)) :
    F₀₁ * (u₁ - u₀) ^ 3 + F₀₂ * (u₂ - u₀) ^ 3 + F₀₃ * (u₃ - u₀) ^ 3 +
      F₁₂ * (u₂ - u₁) ^ 3 + F₁₃ * (u₃ - u₁) ^ 3 + F₂₃ * (u₃ - u₂) ^ 3 ≠ 0 := by
  have pi := Real.pi_pos
  have cn : ∀ {B x W : ℝ}, 0 < B → W = B * Real.cos x → π / 2 ≤ x → x ≤ π + π / 2 → W ≤ 0 :=
    fun hB hW h1 h2 => by
      rw [hW]; exact mul_nonpos_of_nonneg_of_nonpos hB.le
        (Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2)
  -- consecutive machines are within `π/2` (else a cut of nonpositive weight)
  have l₁ : γ₁ < π / 2 := by
    by_contra h
    push Not at h
    have := cn b01 hW₀₁ h (by linarith)
    have := cn b02 hW₀₂ (by linarith) (by linarith)
    have := cn b03 hW₀₃ (by linarith) (by linarith)
    linarith
  have l₂ : γ₂ < π / 2 := by
    by_contra h
    push Not at h
    have := cn b02 hW₀₂ (by linarith) (by linarith)
    have := cn b03 hW₀₃ (by linarith) (by linarith)
    have := cn b12 hW₁₂ h (by linarith)
    have := cn b13 hW₁₃ (by linarith) (by linarith)
    linarith
  have l₃ : γ₃ < π / 2 := by
    by_contra h
    push Not at h
    have := cn b03 hW₀₃ (by linarith) (by linarith)
    have := cn b13 hW₁₃ (by linarith) (by linarith)
    have := cn b23 hW₂₃ h (by linarith)
    linarith
  have w01 : 0 < W₀₁ := by rw [hW₀₁]; exact mul_pos b01 (cos_pos_of_nonneg_of_lt hγ₁ l₁)
  have w12 : 0 < W₁₂ := by rw [hW₁₂]; exact mul_pos b12 (cos_pos_of_nonneg_of_lt hγ₂ l₂)
  have w23 : 0 < W₂₃ := by rw [hW₂₃]; exact mul_pos b23 (cos_pos_of_nonneg_of_lt hγ₃ l₃)
  -- the null direction forces a negative line `03`
  have hσ : π / 2 < γ₁ + γ₂ + γ₃ := by
    by_contra h
    push Not at h
    have cp : ∀ {B x W : ℝ}, 0 < B → W = B * Real.cos x → 0 ≤ x → x ≤ π / 2 → 0 ≤ W :=
      fun hB hW h1 h2 => by
        rw [hW]; exact mul_nonneg hB.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩)
    have p02 := cp b02 hW₀₂ (by linarith) (by linarith)
    have p03 := cp b03 hW₀₃ (by linarith) h
    have p13 := cp b13 hW₁₃ (by linarith) (by linarith)
    have hA : W₀₁ * (u₀ - u₁) ^ 2 + W₀₂ * (u₀ - u₂) ^ 2 + W₀₃ * (u₀ - u₃) ^ 2 +
        W₁₂ * (u₁ - u₂) ^ 2 + W₁₃ * (u₁ - u₃) ^ 2 + W₂₃ * (u₂ - u₃) ^ 2 = 0 := by
      linear_combination u₀ * N₀ + u₁ * N₁ + u₂ * N₂ + u₃ * N₃
    have t01 := mul_nonneg w01.le (sq_nonneg (u₀ - u₁))
    have t02 := mul_nonneg p02 (sq_nonneg (u₀ - u₂))
    have t03 := mul_nonneg p03 (sq_nonneg (u₀ - u₃))
    have t12 := mul_nonneg w12.le (sq_nonneg (u₁ - u₂))
    have t13 := mul_nonneg p13 (sq_nonneg (u₁ - u₃))
    have t23 := mul_nonneg w23.le (sq_nonneg (u₂ - u₃))
    have e01 : u₀ - u₁ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((mul_eq_zero.mp (by linarith : W₀₁ * (u₀ - u₁) ^ 2 = 0)).resolve_left w01.ne')
    have e12 : u₁ - u₂ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((mul_eq_zero.mp (by linarith : W₁₂ * (u₁ - u₂) ^ 2 = 0)).resolve_left w12.ne')
    have e23 : u₂ - u₃ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((mul_eq_zero.mp (by linarith : W₂₃ * (u₂ - u₃) ^ 2 = 0)).resolve_left w23.ne')
    exact hu ⟨by linarith, by linarith, by linarith⟩
  have w03 : W₀₃ < 0 := by
    rw [hW₀₃]; exact mul_neg_of_pos_of_neg b03
      (Real.cos_neg_of_pi_div_two_lt_of_lt hσ (by linarith))
  have P₁ := psd_reduce_one_zero hQ hc₁
  have P₂ := psd_reduce_one_three hQ hc₁
  have P₃ := psd_reduce_two_zero hQ hc₂
  have P₄ := psd_reduce_two_three hQ hc₂
  rcases lt_trichotomy u₀ u₃ with h03 | h03 | h03
  · exact (sorted_cubic_pos ⟨hγ₁, l₁⟩ ⟨hγ₂, l₂⟩ ⟨hγ₃, l₃⟩ hσ b01 b02 b03 b12 b13 b23 hW₀₁ hW₀₂
      hW₀₃ hW₁₂ hW₁₃ hW₂₃ hF₀₁ hF₀₂ hF₀₃ hF₁₂ hF₁₃ hF₂₃ N₀ N₁ N₂ N₃ hc₁ hc₂ P₁ P₂ P₃ P₄
      h03).ne'
  · -- `u₀ = u₃`: the line `03` carries nothing and the diamond identity applies
    subst h03
    have s₀ : 0 < W₀₁ + W₀₂ := by
      have e : (W₀₁ + W₁₂ + W₁₃) * (W₀₁ + W₀₂) =
          ((W₀₁ + W₁₂ + W₁₃) * (W₀₂ + W₀₃) + W₀₁ * (W₁₂ + W₁₃)) + W₀₁ * W₀₁ +
            (W₀₁ + W₁₂ + W₁₃) * (-W₀₃) := by ring
      have h1 := mul_pos w01 w01
      have h2 := mul_pos hc₁ (neg_pos.mpr w03)
      have : 0 < (W₀₁ + W₁₂ + W₁₃) * (W₀₁ + W₀₂) := by rw [e]; linarith
      exact pos_of_mul_pos_right this hc₁.le
    have s₃ : 0 < W₁₃ + W₂₃ := by
      have e : (W₀₂ + W₁₂ + W₂₃) * (W₁₃ + W₂₃) =
          ((W₀₂ + W₁₂ + W₂₃) * (W₀₃ + W₁₃) + W₂₃ * (W₀₂ + W₁₂)) + W₂₃ * W₂₃ +
            (W₀₂ + W₁₂ + W₂₃) * (-W₀₃) := by ring
      have h1 := mul_pos w23 w23
      have h2 := mul_pos hc₂ (neg_pos.mpr w03)
      have : 0 < (W₀₂ + W₁₂ + W₂₃) * (W₁₃ + W₂₃) := by rw [e]; linarith
      exact pos_of_mul_pos_right this hc₂.le
    have d12 : u₁ ≠ u₂ := by
      intro h
      subst h
      have : (W₀₁ + W₀₂) * (u₀ - u₁) = 0 := by linear_combination N₀
      have e := (mul_eq_zero.mp this).resolve_left s₀.ne'
      exact hu ⟨by linarith, rfl, by linarith⟩
    have c01 : Real.cos (0 - γ₁) = Real.cos γ₁ := by rw [zero_sub, Real.cos_neg]
    have c02 : Real.cos (0 - (γ₁ + γ₂)) = Real.cos (γ₁ + γ₂) := by rw [zero_sub, Real.cos_neg]
    have c12 : Real.cos (γ₁ - (γ₁ + γ₂)) = Real.cos γ₂ := by
      rw [show γ₁ - (γ₁ + γ₂) = -γ₂ by ring, Real.cos_neg]
    have c13 : Real.cos (γ₁ - (γ₁ + γ₂ + γ₃)) = Real.cos (γ₂ + γ₃) := by
      rw [show γ₁ - (γ₁ + γ₂ + γ₃) = -(γ₂ + γ₃) by ring, Real.cos_neg]
    have c23 : Real.cos (γ₁ + γ₂ - (γ₁ + γ₂ + γ₃)) = Real.cos γ₃ := by
      rw [show γ₁ + γ₂ - (γ₁ + γ₂ + γ₃) = -γ₃ by ring, Real.cos_neg]
    have n01 : Real.sin (0 - γ₁) = -Real.sin γ₁ := by rw [zero_sub, Real.sin_neg]
    have n02 : Real.sin (0 - (γ₁ + γ₂)) = -Real.sin (γ₁ + γ₂) := by rw [zero_sub, Real.sin_neg]
    have n12 : Real.sin (γ₁ - (γ₁ + γ₂)) = -Real.sin γ₂ := by
      rw [show γ₁ - (γ₁ + γ₂) = -γ₂ by ring, Real.sin_neg]
    have n13 : Real.sin (γ₁ - (γ₁ + γ₂ + γ₃)) = -Real.sin (γ₂ + γ₃) := by
      rw [show γ₁ - (γ₁ + γ₂ + γ₃) = -(γ₂ + γ₃) by ring, Real.sin_neg]
    have n23 : Real.sin (γ₁ + γ₂ - (γ₁ + γ₂ + γ₃)) = -Real.sin γ₃ := by
      rw [show γ₁ + γ₂ - (γ₁ + γ₂ + γ₃) = -γ₃ by ring, Real.sin_neg]
    have hD := diamond_cubic_ne_zero (θ₀ := 0) (θ₁ := γ₁) (θ₂ := γ₁ + γ₂)
      (θ₃ := γ₁ + γ₂ + γ₃) (B₀₁ := B₀₁) (B₀₂ := B₀₂) (B₁₂ := B₁₂) (B₁₃ := B₁₃) (B₂₃ := B₂₃)
      (g₀ := u₀) (g₁ := u₁) (g₂ := u₂) (g₃ := u₀) b01.le b02.le b12 b13.le b23.le
      (by rw [c01, c02, ← hW₀₁, ← hW₀₂]; exact s₀)
      (by rw [c13, c23, ← hW₁₃, ← hW₂₃]; exact s₃)
      (by rw [c01, c02, ← hW₀₁, ← hW₀₂]; linear_combination N₀)
      (by rw [c13, c23, ← hW₁₃, ← hW₂₃]; linear_combination N₃)
      (by rw [c01, c02, c12, c13, c23, ← hW₀₁, ← hW₀₂, ← hW₁₂, ← hW₁₃, ← hW₂₃]
          linear_combination u₀ * N₀ + u₁ * N₁ + u₂ * N₂ + u₀ * N₃) d12
    rw [n01, n02, n12, n13, n23] at hD
    intro hC
    apply hD
    rw [hF₀₁, hF₀₂, hF₀₃, hF₁₂, hF₁₃, hF₂₃] at hC
    linear_combination hC
  · have := sorted_cubic_pos (u₀ := -u₀) (u₁ := -u₁) (u₂ := -u₂) (u₃ := -u₃) ⟨hγ₁, l₁⟩
      ⟨hγ₂, l₂⟩ ⟨hγ₃, l₃⟩ hσ b01 b02 b03 b12 b13 b23 hW₀₁ hW₀₂ hW₀₃ hW₁₂ hW₁₃ hW₂₃ hF₀₁ hF₀₂
      hF₀₃ hF₁₂ hF₁₃ hF₂₃ (by linear_combination -N₀) (by linear_combination -N₁)
      (by linear_combination -N₂) (by linear_combination -N₃) hc₁ hc₂ P₁ P₂ P₃ P₄
      (by linarith)
    intro hC
    have e : F₀₁ * (-u₁ - -u₀) ^ 3 + F₀₂ * (-u₂ - -u₀) ^ 3 + F₀₃ * (-u₃ - -u₀) ^ 3 +
        F₁₂ * (-u₂ - -u₁) ^ 3 + F₁₃ * (-u₃ - -u₁) ^ 3 + F₂₃ * (-u₃ - -u₂) ^ 3 = 0 := by
      linear_combination -hC
    linarith

/-! ## Lifted angles -/

/-- **Sorted lifted angles of four machines.** Four angles can be relabelled (by `σ`) and shifted
by multiples of `2π` so that the lifted angles increase and span at most `3π/2`: four points on a
circle leave a gap of at least `π/2`. -/
@[powerlib_foundation]
theorem exists_sorted_lift (θ : Fin 4 → ℝ) : ∃ (σ : Equiv.Perm (Fin 4)) (t : Fin 4 → ℝ),
    t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 - t 0 ≤ π + π / 2 ∧
      ∀ k, ∃ m : ℤ, θ (σ k) = t k + m * (2 * π) := by
  set r : Fin 4 → ℝ := fun k => toIcoMod Real.two_pi_pos 0 (θ k) with hr_def
  have hr : ∀ k, 0 ≤ r k ∧ r k < 2 * π := fun k => by
    have := toIcoMod_mem_Ico' Real.two_pi_pos (θ k)
    exact ⟨this.1, this.2⟩
  have hθ : ∀ k, ∃ m : ℤ, θ k = r k + m * (2 * π) := fun k =>
    ⟨toIcoDiv Real.two_pi_pos 0 (θ k), by
      rw [hr_def]
      simp only
      rw [← zsmul_eq_mul]
      exact (toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 (θ k)).symm⟩
  set τ := Tuple.sort r
  have hmono := Tuple.monotone_sort r
  have s01 : r (τ 0) ≤ r (τ 1) := hmono (show (0 : Fin 4) ≤ 1 by decide)
  have s12 : r (τ 1) ≤ r (τ 2) := hmono (show (1 : Fin 4) ≤ 2 by decide)
  have s23 : r (τ 2) ≤ r (τ 3) := hmono (show (2 : Fin 4) ≤ 3 by decide)
  have b0 := hr (τ 0)
  have b1 := hr (τ 1)
  have b2 := hr (τ 2)
  have b3 := hr (τ 3)
  have shift : ∀ k : Fin 4, ∀ c : ℝ, ∀ z : ℤ, c = z * (2 * π) →
      ∃ m : ℤ, θ (τ k) = (r (τ k) + c) + m * (2 * π) := by
    intro k c z hc
    obtain ⟨m, hm⟩ := hθ (τ k)
    exact ⟨m - z, by rw [hm, hc]; push_cast; ring⟩
  by_cases g4 : r (τ 3) - r (τ 0) ≤ π + π / 2
  · refine ⟨τ, fun k => r (τ k), s01, s12, s23, g4, fun k => ?_⟩
    obtain ⟨m, hm⟩ := hθ (τ k)
    exact ⟨m, hm⟩
  by_cases g1 : π / 2 ≤ r (τ 1) - r (τ 0)
  · refine ⟨(Equiv.addRight 1).trans τ, ![r (τ 1), r (τ 2), r (τ 3), r (τ 0) + 2 * π],
      s12, s23, by simp; linarith, by simp; linarith, fun k => ?_⟩
    fin_cases k
    · simpa using shift 1 0 0 (by simp)
    · simpa using shift 2 0 0 (by simp)
    · simpa using shift 3 0 0 (by simp)
    · simpa using shift 0 (2 * π) 1 (by simp)
  by_cases g2 : π / 2 ≤ r (τ 2) - r (τ 1)
  · refine ⟨(Equiv.addRight 2).trans τ,
      ![r (τ 2), r (τ 3), r (τ 0) + 2 * π, r (τ 1) + 2 * π], s23, by simp; linarith,
      by simp; linarith, by simp; linarith, fun k => ?_⟩
    fin_cases k
    · simpa using shift 2 0 0 (by simp)
    · simpa using shift 3 0 0 (by simp)
    · simpa using shift 0 (2 * π) 1 (by simp)
    · simpa using shift 1 (2 * π) 1 (by simp)
  have g3 : π / 2 ≤ r (τ 3) - r (τ 2) := by linarith
  refine ⟨(Equiv.addRight 3).trans τ,
    ![r (τ 3), r (τ 0) + 2 * π, r (τ 1) + 2 * π, r (τ 2) + 2 * π], by simp; linarith,
    by simp; linarith, by simp; linarith, by simp; linarith, fun k => ?_⟩
  fin_cases k
  · simpa using shift 3 0 0 (by simp)
  · simpa using shift 0 (2 * π) 1 (by simp)
  · simpa using shift 1 (2 * π) 1 (by simp)
  · simpa using shift 2 (2 * π) 1 (by simp)

/-! ## The model: four machines with five or six lines (implementation evidence) -/

/-- **A cut of the labelled machines has positive weight at a locally asymptotically stable point.**
`c` is the indicator (in labelled order) of a nonempty proper group of machines. -/
private theorem cut_pos_of_localAsymptoticStable {p : Params 3} {θ : Fin (3 + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hLAS : LocalAsymptoticStable (reducedField p) (equilibrium θ)) (σ : Equiv.Perm (Fin 4))
    (c : Fin 4 → ℝ) (hc : ∀ k, c k = 0 ∨ c k = 1) {i₀ j₀ : Fin 4} (hi : c i₀ = 1)
    (hj : c j₀ = 0) :
    0 < weightOf p θ σ 0 1 * (c 0 - c 1) ^ 2 + weightOf p θ σ 0 2 * (c 0 - c 2) ^ 2 +
      weightOf p θ σ 0 3 * (c 0 - c 3) ^ 2 + weightOf p θ σ 1 2 * (c 1 - c 2) ^ 2 +
      weightOf p θ σ 1 3 * (c 1 - c 3) ^ 2 + weightOf p θ σ 2 3 * (c 2 - c 3) ^ 2 := by
  set X : Finset (Fin (3 + 1)) := Finset.univ.filter (fun k => c (σ.symm k) = 1) with hX
  have hg : groupIndicator X = fun k => c (σ.symm k) := by
    funext k
    simp only [groupIndicator, hX, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hc (σ.symm k) with h | h <;> simp [h]
  have h1 := hessForm_groupIndicator p θ X
  have h2 := hessForm_four p θ (groupIndicator X) σ
  rw [hg] at h1 h2
  simp only [Equiv.symm_apply_apply] at h2
  by_contra hle
  push Not at hle
  exact not_localAsymptoticStable_of_cut hbal X (by linarith) (i₀ := σ i₀) (j₀ := σ j₀)
    (by simp [hX, hi]) (by simp [hX, hj]) hLAS

/-- The Hessian form in labelled coordinates is positive semidefinite at a locally asymptotically
stable power-balance point. -/
private theorem labelled_nonneg_of_localAsymptoticStable {p : Params 3} {θ : Fin (3 + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hLAS : LocalAsymptoticStable (reducedField p) (equilibrium θ)) (σ : Equiv.Perm (Fin 4))
    (g₀ g₁ g₂ g₃ : ℝ) :
    0 ≤ weightOf p θ σ 0 1 * (g₀ - g₁) ^ 2 + weightOf p θ σ 0 2 * (g₀ - g₂) ^ 2 +
      weightOf p θ σ 0 3 * (g₀ - g₃) ^ 2 + weightOf p θ σ 1 2 * (g₁ - g₂) ^ 2 +
      weightOf p θ σ 1 3 * (g₁ - g₃) ^ 2 + weightOf p θ σ 2 3 * (g₂ - g₃) ^ 2 := by
  have := hessForm_nonneg_of_localAsymptoticStable hbal hLAS (fun k => ![g₀, g₁, g₂, g₃] (σ.symm k))
  rw [hessForm_four p θ _ σ] at this
  simp only [Equiv.symm_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at this
  linarith

/-- A non-Hurwitz reduced Jacobian at a locally asymptotically stable point leaves a non-constant
null direction of the Hessian form with zero cubic form. -/
private theorem exists_null_of_localAsymptoticStable {p : Params 3} {θ : Fin (3 + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hLAS : LocalAsymptoticStable (reducedField p) (equilibrium θ))
    (hH : ¬ LinearSystems.IsHurwitz (jacobian p θ)) :
    ∃ u : Fin (3 + 1) → ℝ, (∃ k, u k ≠ u 0) ∧ hessForm p θ u = 0 ∧ cubicForm p θ u = 0 := by
  obtain ⟨u, hu0, hu, hle⟩ := exists_hessForm_nonpos hH
  have hQ0 : hessForm p θ u = 0 :=
    le_antisymm hle (hessForm_nonneg_of_localAsymptoticStable hbal hLAS u)
  refine ⟨u, ?_, hQ0, cubicForm_eq_zero_of_localAsymptoticStable hbal hLAS u hQ0⟩
  by_contra h
  push Not at h
  apply hu
  funext k
  rw [h k, hu0]
  rfl

/-- A direction constant on the labelled machines is constant. -/
@[powerlib_foundation] theorem eq_of_labelled_eq {u : Fin (3 + 1) → ℝ} (σ : Equiv.Perm (Fin 4))
    (h : u (σ 0) = u (σ 1) ∧ u (σ 1) = u (σ 2) ∧ u (σ 2) = u (σ 3)) (k : Fin (3 + 1)) :
    u k = u 0 := by
  have hall : ∀ m : Fin 4, u (σ m) = u (σ 0) := by
    intro m
    fin_cases m
    · rfl
    · exact h.1.symm
    · exact (h.1.trans h.2.1).symm
    · exact (h.1.trans (h.2.1.trans h.2.2)).symm
  calc u k = u (σ (σ.symm k)) := by rw [σ.apply_symm_apply]
    _ = u (σ 0) := hall _
    _ = u (σ (σ.symm 0)) := (hall _).symm
    _ = u 0 := by rw [σ.apply_symm_apply]

/-- **The diamond: one uncoupled pair, four machines.** Label the machines by `σ` so that `σ0`
and `σ3` are uncoupled and the hub `σ1 σ2` is coupled. At a power-balance point with a
non-Hurwitz reduced Jacobian the selected point is not locally asymptotically stable: along a null
direction normalized by `d = u(σ1) − u(σ2)` and with `Φ = θ(σ1) − θ(σ2)`,
`sin Φ · A₃ = d³ (B_hub + E₀ + E₃)` with nonnegative branch terms (`diamond_cubic_ne_zero`), a
fold. -/
private theorem not_localAsymptoticStable_diamond (p : Params 3) (θ : Fin (3 + 1) → ℝ)
    (σ : Equiv.Perm (Fin 4)) (h03 : p.B (σ 0) (σ 3) = 0) (h12 : 0 < p.B (σ 1) (σ 2))
    (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hH : ¬ LinearSystems.IsHurwitz (jacobian p θ)) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  intro hLAS
  obtain ⟨u, ⟨k₁, hk₁⟩, hQ0, hC0⟩ := exists_null_of_localAsymptoticStable hbal hLAS hH
  have hQ := labelled_nonneg_of_localAsymptoticStable hbal hLAS σ
  rw [hessForm_four p θ u σ] at hQ0
  rw [cubicForm_four p θ u σ] at hC0
  have hw03 : weightOf p θ σ 0 3 = 0 := by rw [weightOf, h03, zero_mul]
  have hf03 : flowOf p θ σ 0 3 = 0 := by rw [flowOf, h03, zero_mul]
  obtain ⟨N0, N1, N2, N3⟩ := null_four hQ (g₀ := u (σ 0)) (g₁ := u (σ 1)) (g₂ := u (σ 2))
    (g₃ := u (σ 3)) (by linarith)
  have c0 := cut_pos_of_localAsymptoticStable hbal hLAS σ ![1, 0, 0, 0]
    (by intro k; fin_cases k <;> simp) (i₀ := 0) (j₀ := 1) (by simp) (by simp)
  have c3 := cut_pos_of_localAsymptoticStable hbal hLAS σ ![0, 0, 0, 1]
    (by intro k; fin_cases k <;> simp) (i₀ := 3) (j₀ := 0) (by simp) (by simp)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at c0 c3
  norm_num at c0 c3
  rw [hw03] at N0 N3 hQ0 c0 c3
  rw [hf03] at hC0
  have s₀ : 0 < weightOf p θ σ 0 1 + weightOf p θ σ 0 2 := by linarith
  have s₃ : 0 < weightOf p θ σ 1 3 + weightOf p θ σ 2 3 := by linarith
  have hd : u (σ 1) ≠ u (σ 2) := by
    intro h
    have e0 : (weightOf p θ σ 0 1 + weightOf p θ σ 0 2) * (u (σ 0) - u (σ 1)) = 0 := by
      rw [← h] at N0; linear_combination N0
    have e3 : (weightOf p θ σ 1 3 + weightOf p θ σ 2 3) * (u (σ 3) - u (σ 1)) = 0 := by
      rw [← h] at N3; linear_combination N3
    have f0 := (mul_eq_zero.mp e0).resolve_left s₀.ne'
    have f3 := (mul_eq_zero.mp e3).resolve_left s₃.ne'
    exact hk₁ (eq_of_labelled_eq σ ⟨by linarith, h, by linarith⟩ k₁)
  refine diamond_cubic_ne_zero (θ₀ := θ (σ 0)) (θ₁ := θ (σ 1)) (θ₂ := θ (σ 2))
    (θ₃ := θ (σ 3)) (B₀₁ := p.B (σ 0) (σ 1)) (B₀₂ := p.B (σ 0) (σ 2))
    (B₁₂ := p.B (σ 1) (σ 2)) (B₁₃ := p.B (σ 1) (σ 3)) (B₂₃ := p.B (σ 2) (σ 3))
    (g₀ := u (σ 0)) (g₁ := u (σ 1)) (g₂ := u (σ 2)) (g₃ := u (σ 3)) (p.B_nonneg _ _)
    (p.B_nonneg _ _) h12 (p.B_nonneg _ _) (p.B_nonneg _ _) s₀ s₃
    (by simp only [weightOf] at N0; linear_combination N0)
    (by simp only [weightOf] at N3; linear_combination N3)
    (by simp only [weightOf] at hQ0; linear_combination hQ0 / 2) hd ?_
  simp only [flowOf] at hC0
  linear_combination hC0 / 2

/-- **The complete graph: all six pairs coupled, four machines.** At a power-balance point with a
non-Hurwitz reduced Jacobian the selected point is not locally asymptotically stable. The machines
are relabelled by increasing lifted angles (`exists_sorted_lift`); every cut has positive weight
(else `not_localAsymptoticStable_of_cut`), and along every non-constant null direction the cubic
form is nonzero (`sorted_cubic_ne_zero`): a fold. -/
private theorem not_localAsymptoticStable_complete (p : Params 3) (θ : Fin (3 + 1) → ℝ)
    (hB : ∀ i j : Fin 4, i ≠ j → 0 < p.B i j) (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hH : ¬ LinearSystems.IsHurwitz (jacobian p θ)) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  intro hLAS
  obtain ⟨u, ⟨k₁, hk₁⟩, hQ0, hC0⟩ := exists_null_of_localAsymptoticStable hbal hLAS hH
  obtain ⟨σ, t, t01, t12, t23, tsp, ht⟩ := exists_sorted_lift θ
  have trig : ∀ i j : Fin 4, Real.cos (θ (σ i) - θ (σ j)) = Real.cos (t i - t j) ∧
      Real.sin (θ (σ i) - θ (σ j)) = Real.sin (t i - t j) := by
    intro i j
    obtain ⟨mi, hmi⟩ := ht i
    obtain ⟨mj, hmj⟩ := ht j
    have e : θ (σ i) - θ (σ j) = (t i - t j) + ((mi - mj : ℤ) : ℝ) * (2 * π) := by
      rw [hmi, hmj]; push_cast; ring
    rw [e, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    exact ⟨rfl, rfl⟩
  have cw : ∀ i j : Fin 4, ∀ α : ℝ, t j - t i = α →
      weightOf p θ σ i j = p.B (σ i) (σ j) * Real.cos α := by
    intro i j α h
    rw [weightOf, (trig i j).1, show t i - t j = -α by linarith, Real.cos_neg]
  have cf : ∀ i j : Fin 4, ∀ α : ℝ, t j - t i = α →
      flowOf p θ σ i j = -(p.B (σ i) (σ j) * Real.sin α) := by
    intro i j α h
    rw [flowOf, (trig i j).2, show t i - t j = -α by linarith, Real.sin_neg]
    ring
  have hb : ∀ i j : Fin 4, i ≠ j → 0 < p.B (σ i) (σ j) := fun i j h =>
    hB _ _ (σ.injective.ne h)
  have hQ := labelled_nonneg_of_localAsymptoticStable hbal hLAS σ
  rw [hessForm_four p θ u σ] at hQ0
  rw [cubicForm_four p θ u σ] at hC0
  obtain ⟨N0, N1, N2, N3⟩ := null_four hQ (g₀ := u (σ 0)) (g₁ := u (σ 1)) (g₂ := u (σ 2))
    (g₃ := u (σ 3)) (by linarith)
  have cut : ∀ c : Fin 4 → ℝ, (∀ k, c k = 0 ∨ c k = 1) → ∀ i₀ j₀ : Fin 4, c i₀ = 1 →
      c j₀ = 0 → _ := fun c hc i₀ j₀ hi hj =>
    cut_pos_of_localAsymptoticStable hbal hLAS σ c hc hi hj
  have c0 := cut ![1, 0, 0, 0] (by intro k; fin_cases k <;> simp) 0 1 (by simp) (by simp)
  have c01 := cut ![1, 1, 0, 0] (by intro k; fin_cases k <;> simp) 0 2 (by simp) (by simp)
  have c3 := cut ![0, 0, 0, 1] (by intro k; fin_cases k <;> simp) 3 0 (by simp) (by simp)
  have c1 := cut ![0, 1, 0, 0] (by intro k; fin_cases k <;> simp) 1 0 (by simp) (by simp)
  have c2 := cut ![0, 0, 1, 0] (by intro k; fin_cases k <;> simp) 2 0 (by simp) (by simp)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at c0 c01 c3 c1 c2
  norm_num at c0 c01 c3 c1 c2
  refine sorted_cubic_ne_zero (γ₁ := t 1 - t 0) (γ₂ := t 2 - t 1) (γ₃ := t 3 - t 2)
    (B₀₁ := p.B (σ 0) (σ 1)) (B₀₂ := p.B (σ 0) (σ 2)) (B₀₃ := p.B (σ 0) (σ 3))
    (B₁₂ := p.B (σ 1) (σ 2)) (B₁₃ := p.B (σ 1) (σ 3)) (B₂₃ := p.B (σ 2) (σ 3))
    (F₀₁ := p.B (σ 0) (σ 1) * Real.sin (t 1 - t 0))
    (F₀₂ := p.B (σ 0) (σ 2) * Real.sin (t 1 - t 0 + (t 2 - t 1)))
    (F₀₃ := p.B (σ 0) (σ 3) * Real.sin (t 1 - t 0 + (t 2 - t 1) + (t 3 - t 2)))
    (F₁₂ := p.B (σ 1) (σ 2) * Real.sin (t 2 - t 1))
    (F₁₃ := p.B (σ 1) (σ 3) * Real.sin (t 2 - t 1 + (t 3 - t 2)))
    (F₂₃ := p.B (σ 2) (σ 3) * Real.sin (t 3 - t 2))
    (by linarith) (by linarith) (by linarith) (by linarith) (hb 0 1 (by decide))
    (hb 0 2 (by decide)) (hb 0 3 (by decide)) (hb 1 2 (by decide)) (hb 1 3 (by decide))
    (hb 2 3 (by decide)) (cw 0 1 _ rfl) (cw 0 2 _ (by ring)) (cw 0 3 _ (by ring))
    (cw 1 2 _ rfl) (cw 1 3 _ (by ring)) (cw 2 3 _ rfl) rfl rfl rfl rfl rfl rfl c0 c01 c3 c1 c2
    hQ N0 N1 N2 N3 ?_ ?_
  · intro h
    exact hk₁ (eq_of_labelled_eq σ h k₁)
  · rw [cf 0 1 (t 1 - t 0) rfl, cf 0 2 (t 1 - t 0 + (t 2 - t 1)) (by ring),
      cf 0 3 (t 1 - t 0 + (t 2 - t 1) + (t 3 - t 2)) (by ring), cf 1 2 (t 2 - t 1) rfl,
      cf 1 3 (t 2 - t 1 + (t 3 - t 2)) (by ring), cf 2 3 (t 3 - t 2) rfl] at hC0
    linear_combination hC0 / 2

/-- A labelling of four machines with prescribed machines in positions `0` and `3`. -/
@[powerlib_foundation] theorem exists_perm_zero_three : ∀ {i j : Fin 4}, i ≠ j →
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 3 = j := by
  decide

/-- **Every four-machine network.** At a power-balance point with a non-Hurwitz reduced Jacobian
the selected point is not locally asymptotically stable: all six pairs coupled
(`not_localAsymptoticStable_complete`), exactly the pair `σ0 σ3` uncoupled with the hub `σ1 σ2`
coupled (`not_localAsymptoticStable_diamond`), or two disjoint uncoupled pairs (the lines lie on a
four-cycle, `not_localAsymptoticStable_four`). -/
private theorem not_localAsymptoticStable_four_machines (p : Params 3) (θ : Fin (3 + 1) → ℝ)
    (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hH : ¬ LinearSystems.IsHurwitz (jacobian p θ)) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  by_cases hall : ∀ i j : Fin 4, i ≠ j → 0 < p.B i j
  · exact not_localAsymptoticStable_complete p θ hall hbal hH
  push Not at hall
  obtain ⟨i, j, hij, hle⟩ := hall
  have h0 : p.B i j = 0 := le_antisymm hle (p.B_nonneg i j)
  obtain ⟨σ, hσ0, hσ3⟩ := exists_perm_zero_three hij
  by_cases h12 : 0 < p.B (σ 1) (σ 2)
  · exact not_localAsymptoticStable_diamond p θ σ (by rw [hσ0, hσ3]; exact h0) h12 hbal hH
  have h12' : p.B (σ 1) (σ 2) = 0 := le_antisymm (not_lt.mp h12) (p.B_nonneg _ _)
  refine not_localAsymptoticStable_four p θ ((Equiv.swap (2 : Fin 4) 3).trans σ) ?_ (Or.inl ?_)
    hbal hH
  · have e1 : (Equiv.swap (2 : Fin 4) 3) 1 = 1 := by decide
    have e3 : (Equiv.swap (2 : Fin 4) 3) 3 = 2 := by decide
    simp only [Equiv.trans_apply, e1, e3]
    exact h12'
  · have e0 : (Equiv.swap (2 : Fin 4) 3) 0 = 0 := by decide
    have e2 : (Equiv.swap (2 : Fin 4) 3) 2 = 3 := by decide
    simp only [Equiv.trans_apply, e0, e2, hσ0, hσ3]
    exact h0

/-! ## The family: exactness for four machines -/

private theorem mem_den_flow_iff_dense {m : Model n} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (reducedField m.params) (equilibrium m.θ) :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

private theorem powerFlow_of_equilibrium_dense {p : Params n} {θ : Fin (n + 1) → ℝ}
    (h : reducedField p (equilibrium θ) = 0) : ∀ k, p.P k = powerInjection p.B θ k := by
  intro k
  have hk := congrArg (fun z : State (n + (n + 1)) => z (wIdx k)) h
  simp only [reducedField_wIdx, equilibrium, reduce_wIdx, angleMap_reduce,
    powerInjection_add_const, PiLp.zero_apply] at hk
  rw [div_eq_zero_iff, or_iff_left (p.M_pos k).ne'] at hk
  simp only [Pi.zero_apply, mul_zero, sub_zero] at hk
  linarith

/-- **Four machines: the local asymptotic translation is exact.** For every four-machine network
(`n = 3`), local asymptotic stability of the selected profile holds exactly when it is a
power-balance point with a Hurwitz reduced Jacobian. -/
@[powerlib_domain] theorem exact_locallyAsymptoticallyStable_four :
    connection% ((family (n := 3)).Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [TMIO.mem_realize, mem_den_flow_iff_dense]
  change _ ↔ LocalAsymptoticStable _ _
  simp only [family, translate, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  constructor
  · rintro ⟨hp, hH⟩
    exact Flow.locallyExponentiallyStable_localAsymptoticStable
      (Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian (jacobian m.params m.θ)
        (reducedField_contDiff m.params) (reducedField_equilibrium m.params m.θ hp)
        (hasFDerivAt_reducedField m.params m.θ).fderiv hH)
  · intro hLAS
    have hp := powerFlow_of_equilibrium_dense (Dynamics.isEquilibrium_of_lyapunovStable
      (reducedField_contDiff m.params) hLAS.1)
    refine ⟨hp, ?_⟩
    by_contra hH
    exact not_localAsymptoticStable_four_machines m.params m.θ hp hH hLAS

/-- **Membership in local asymptotic stability for every four-machine network**: power balance
with a Hurwitz reduced Jacobian (no restriction on the lines). -/
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_four_machines (m : Model 3) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      (∀ k, m.params.P k = powerInjection m.params.B m.θ k) ∧
      LinearSystems.IsHurwitz (jacobian m.params m.θ)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff_dense]
  change LocalAsymptoticStable _ _ ↔ _
  constructor
  · intro hLAS
    have hp := powerFlow_of_equilibrium_dense (Dynamics.isEquilibrium_of_lyapunovStable
      (reducedField_contDiff m.params) hLAS.1)
    refine ⟨hp, ?_⟩
    by_contra hH
    exact not_localAsymptoticStable_four_machines m.params m.θ hp hH hLAS
  · rintro ⟨hp, hH⟩
    exact Flow.locallyExponentiallyStable_localAsymptoticStable
      (Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian (jacobian m.params m.θ)
        (reducedField_contDiff m.params) (reducedField_equilibrium m.params m.θ hp)
        (hasFDerivAt_reducedField m.params m.θ).fderiv hH)

end powerlib.Network.Swing
