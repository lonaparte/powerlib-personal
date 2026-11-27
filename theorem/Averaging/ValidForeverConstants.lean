import theorem.Averaging.PeriodicOrbitConstants

/-! # Averaging on `[0, ∞)` with explicit constants

`Averaging.averaging_valid_forever` (`theorem/Averaging/PeriodicOrbitStability.lean`) extends the
`O(ε)` estimate of first-order averaging from `[0, L/ε]` to all `t ≥ 0` when the averaged solution
is attracted to an equilibrium `y*` with a Hurwitz averaged Jacobian `J = Df̄(y*)`; its constants
`ε₀, δ₀, κ₁` exist because a Lyapunov matrix exists. Here a Lyapunov certificate `(P, Q)` of `J`
is a hypothesis and every constant is a closed-form expression. After the slow time `L` the
sampled deviation `e_k = x(t₁ + kT) − x̄(t₁ + kT)`, `t₁ = L/ε`, is one perturbed Euler step of `J`
per period (`perturbed_averaged_difference_step`), with a residual `σ = η C₂` that does not vanish
with `e_k`; the σ-term of `Averaging.lyapunov_perturbed_step_le`,
`V(e + hJe + p) ≤ (1 − ch)V(e) + Dσ²/h` with `c = q₁/(8p₂)`, `D = 12p₂²/q₁`, `h = εT`, keeps the
sublevel set `V ≤ Λ`, `Λ = p₂A² + Dσ²/(ch²) = p₂A² + 96p₂³(σ/(εT))²/q₁²`, invariant, where `A` is
the KBM bound at `t₁`. Hence `‖e_k‖ ≤ √(Λ/p₁)` for all `k` and, between the samples, the deviation
grows by at most the drift over one period.

The estimate is made for perturbed curves `ẋ = ε f(x, t) + q(t)`, `‖q‖ ≤ ηM_q`, `ε² ≤ η ≤ ε`
(the setting of `theorem/Averaging/PerturbedPeriodicOrbits.lean`), whose error on `[0, ∞)` is
`O(ε + η/ε)` — e.g. `O(ε^κ)` for `η = ε^{1+κ}` — and specialised to `ẋ = ε f(x, t) + ε² r(x, t)`,
where it is `O(ε)` with the constant `validForeverBound p₁ p₂ q₁ C_K (C₂/T) + (2M + M_r)T`.

Scope.
* `f` as in `Averaging.averaging_valid_forever` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, `n > 0`:
  the hypotheses of `Averaging.kbm_first_order` (period `T > 0`, continuity, `T`-periodicity,
  Lipschitz constant `ℓ`, bound `M`), an `L₂`-Lipschitz state derivative `Df` on the ball
  `‖x − y*‖ ≤ ρ`, `Df(y*, ·)` continuous, and `Df̄(y*)` the operator of a real matrix `J`.
* Lyapunov certificate as in `Averaging.exp_stable_of_lyapunov`: `P ≻ 0`, `PJ + JᵀP = −Q`,
  `p₁‖e‖² ≤ eᵀPe ≤ p₂‖e‖²`, `q₁‖e‖² ≤ eᵀQe`, `q₁ > 0`, `‖J‖ ≤ a`.
* Smallness by explicit inequalities: a radius `r₁ ≤ ρ` with `96p₂³(L₂r₁)² ≤ q₁²p₁`, the depth
  conditions `2εTp₂a² ≤ q₁`, `εTq₁ ≤ p₂`, and `√(Λ/p₁) ≤ r₁/2`; the averaged solution is in the
  ball `‖x̄ − y*‖ ≤ r₁/2` from the slow time `L` on. Unlike `Averaging.exp_stable_of_lyapunov`,
  no condition on `ρ` or on the Lipschitz constant `L_S` of the period map is needed: the
  comparison curve is the averaged solution, not a second solution.
* For `η = ε²` the conditions read `ε ≤ ε₀` with `ε₀` the minimum of `1`, `q₁/(2Tp₂a²)`,
  `p₂/(Tq₁)` and `r₁/(2 validForeverBound p₁ p₂ q₁ C_K (C₂/T))`.
* Generic mathematics, no model family; the property is written out in the statements.

Source: Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear Dynamical Systems*, Ch. 5
(validity of averaging on `[0, ∞)` near an attracting hyperbolic equilibrium, the
Eckhaus/Sanchez-Palencia theorem); Khalil, *Nonlinear Systems*, Ch. 4 and 10 (quadratic Lyapunov
functions with `λ_min`/`λ_max` bounds, averaging); the explicit perturbed Euler step
`Averaging.lyapunov_perturbed_step_le`, the KBM estimate `Averaging.kbm_perturbed`, the one-period
estimates `Averaging.perturbed_period_step_le`, `Averaging.averaged_period_step_le`,
`Averaging.fieldAverage_sub_linear_le`.

Results.
* `perturbed_averaged_difference_step` — one period of the difference between a perturbed curve
  and an averaged solution near `y*` is a perturbed Euler step of `A = Df̄(y*)`,
  `‖p‖ ≤ εT L₂r₁ ‖e‖ + η(C_S + ℓMT²)`.
* `validForeverBound`, `validForeverBound_smul` — `√((p₂A² + 96p₂³σ²/q₁²)/p₁)` and its
  homogeneity.
* `averaging_valid_forever_perturbed` — for perturbed curves,
  `‖x(t) − x̄(t)‖ ≤ validForeverBound p₁ p₂ q₁ A (ηC₂/(εT)) + (2εM + ηM_q)T` for ALL `t ≥ 0`,
  `A = ((2ℓMLT + 2MT)ε + LηM_q/ε) e^{ℓL}`.
* `averaging_valid_forever_of_lyapunov` — `Averaging.averaging_valid_forever` with explicit
  constants: `‖x(t) − x̄(t)‖ ≤ (validForeverBound p₁ p₂ q₁ C_K (C₂/T) + (2M + M_r)T) ε`.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology intervalIntegral
open scoped Interval

/-! ## One period of the difference between a perturbed curve and an averaged solution -/

section Difference

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ → E} {T ℓ M ρ L₂ : ℝ} {Df : E → ℝ → E →L[ℝ] E} {ystar : E}

/-- **One period of the difference between a perturbed curve and an averaged solution near `y*`
is a perturbed Euler step of the linearized averaged field**: for `ẋ = ε f(x, t) + q(t)` on
`[s, s + T]`, `‖q‖ ≤ ηM_q`, `ε² ≤ η ≤ ε`, and a solution `x̄` of `x̄̇ = ε f̄(x̄)`,
`x(s + T) − x̄(s + T) = e + εT A e + p` with `e = x(s) − x̄(s)`, `A = Df̄(y*)` and
`‖p‖ ≤ εT L₂ r₁ ‖e‖ + η(C_S + ℓMT²)`, while `x(s)`, `x̄(s)` lie in the ball of radius `r₁ ≤ ρ`
(`Averaging.perturbed_period_step_le`, `Averaging.averaged_period_step_le`,
`Averaging.fieldAverage_sub_linear_le`). -/
@[tmio T, powerlib_foundation] theorem perturbed_averaged_difference_step [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {A : E →L[ℝ] E} (hA : HasFDerivAt (fieldAverage f T) A ystar)
    {ε η Mq : ℝ} (hε : 0 ≤ ε) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η) (hMq : 0 ≤ Mq)
    {x xbar q : ℝ → E} {s r₁ : ℝ}
    (hx : ∀ t ∈ Icc s (s + T), HasDerivAt x (ε • f (x t) t + q t) t)
    (hq : ∀ t ∈ Icc s (s + T), ‖q t‖ ≤ η * Mq)
    (hxbar : ∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t)
    (hxs : ‖x s - ystar‖ ≤ r₁) (hxbs : ‖xbar s - ystar‖ ≤ r₁) (hr₁ : r₁ ≤ ρ) :
    ∃ p : E, x (s + T) - xbar (s + T) = (x s - xbar s) + (ε * T) • A (x s - xbar s) + p ∧
      ‖p‖ ≤ ε * T * (L₂ * r₁) * ‖x s - xbar s‖ +
        η * (stroboConst ℓ M Mq T + ℓ * M * T ^ 2) := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  refine ⟨(ε * T) • (fieldAverage f T (x s) - fieldAverage f T (xbar s) - A (x s - xbar s)) +
    ((x (s + T) - x s - (ε * T) • fieldAverage f T (x s)) -
      (xbar (s + T) - xbar s - (ε * T) • fieldAverage f T (xbar s))), ?_, ?_⟩
  · simp only [smul_sub]; abel
  have h1 := fieldAverage_sub_linear_le hf hρ hL₂ hD hDl hDc hA hr₁ hxs hxbs
  have h2 := perturbed_period_step_le hf hε hηε hεη hMq hx hq
  have h3 := averaged_period_step_le hf hε hxbar s
  have h4 : ε ^ 2 * (ℓ * M * T ^ 2) ≤ η * (ℓ * M * T ^ 2) :=
    mul_le_mul_of_nonneg_right hεη (by positivity)
  calc _ ≤ ε * T * (L₂ * r₁ * ‖x s - xbar s‖) +
        (η * stroboConst ℓ M Mq T + ε ^ 2 * (ℓ * M * T ^ 2)) := by
        refine (norm_add_le _ _).trans
          (add_le_add ?_ ((norm_sub_le _ _).trans (add_le_add h2 h3)))
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ _ := by nlinarith

end Difference

/-! ## The invariant Lyapunov level -/

/-- The closed-form bound `√((p₂A² + 96p₂³σ²/q₁²)/p₁)` of the sampled deviation: `A` bounds the
deviation when the averaged solution has entered the ball, `σ` is the residual of one period per
unit of `εT`, and `96p₂³/q₁² = D/c` for the constants `c = q₁/(8p₂)`, `D = 12p₂²/q₁` of
`Averaging.lyapunov_perturbed_step_le`. -/
def validForeverBound (p₁ p₂ q₁ A σ : ℝ) : ℝ :=
  Real.sqrt ((p₂ * A ^ 2 + 96 * p₂ ^ 3 * σ ^ 2 / q₁ ^ 2) / p₁)

/-- `validForeverBound` is positively homogeneous in `(A, σ)`. -/
@[tmio T, powerlib_foundation] theorem validForeverBound_smul (p₁ p₂ q₁ A σ : ℝ) {c : ℝ}
    (hc : 0 ≤ c) :
    validForeverBound p₁ p₂ q₁ (c * A) (c * σ) = c * validForeverBound p₁ p₂ q₁ A σ := by
  rw [validForeverBound, validForeverBound,
    show (p₂ * (c * A) ^ 2 + 96 * p₂ ^ 3 * (c * σ) ^ 2 / q₁ ^ 2) / p₁ =
      c ^ 2 * ((p₂ * A ^ 2 + 96 * p₂ ^ 3 * σ ^ 2 / q₁ ^ 2) / p₁) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-! ## Averaging on `[0, ∞)` -/

section StabilityRn

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

local notation "op" A:max => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A

open MatrixAlgebra Matrix

/-- **Averaging is valid on `[0, ∞)` for perturbed curves, explicit constants.** Let `f` be as in
`Averaging.averaging_valid_forever` (`Df̄(y*) = J`) and let `(P, Q)` be a Lyapunov certificate of
`J`: `P ≻ 0`, `PJ + JᵀP = −Q`, `p₁‖e‖² ≤ eᵀPe ≤ p₂‖e‖²`, `q₁‖e‖² ≤ eᵀQe`, `q₁ > 0`,
`‖J‖ ≤ a`. Take `0 < r₁ ≤ ρ` with `96p₂³(L₂r₁)² ≤ q₁²p₁`, a depth `ε > 0`, `ε² ≤ η ≤ ε`, with
`2εTp₂a² ≤ q₁` and `εTq₁ ≤ p₂`, a slow time `L ≥ 0`, and put
`A = ((2ℓMLT + 2MT)ε + LηM_q/ε) e^{ℓL}` (the KBM bound of `Averaging.kbm_perturbed` at `L/ε`),
`C₂ = C_S + ℓMT²` and `B = validForeverBound p₁ p₂ q₁ A (ηC₂/(εT))`, with `B ≤ r₁/2`. If `x`
solves `ẋ = ε f(x, t) + q(t)` with `‖q‖ ≤ ηM_q` for `t ≥ 0`, `x̄` solves `x̄̇ = ε f̄(x̄)`,
`x(0) = x̄(0)`, and `x̄` stays in the ball `‖x̄ − y*‖ ≤ r₁/2` from `L/ε` on, then for ALL `t ≥ 0`
`‖x(t) − x̄(t)‖ ≤ B + (2εM + ηM_q)T`. -/
@[tmio T, powerlib_foundation] theorem averaging_valid_forever_perturbed [NeZero n]
    {f : ℝⁿ → ℝ → ℝⁿ} {T ℓ M ρ L₂ : ℝ} {Df : ℝⁿ → ℝ → ℝⁿ →L[ℝ] ℝⁿ} {ystar : ℝⁿ}
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {J : Matrix (Fin n) (Fin n) ℝ}
    (hA : HasFDerivAt (fieldAverage f T) (op J) ystar)
    {P Q : Matrix (Fin n) (Fin n) ℝ} (hPd : P.PosDef) (hLyap : P * J + Jᵀ * P = -Q)
    {p₁ p₂ q₁ a : ℝ} (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hbd : ∀ e : ℝⁿ, p₁ * ‖e‖ ^ 2 ≤ quadraticForm P e ∧ quadraticForm P e ≤ p₂ * ‖e‖ ^ 2)
    (hQ : ∀ e : ℝⁿ, q₁ * ‖e‖ ^ 2 ≤ quadraticForm Q e) (ha : ‖op J‖ ≤ a)
    {r₁ ε η Mq L : ℝ} (hr₁ : 0 < r₁) (hr₁ρ : r₁ ≤ ρ)
    (hκ : 96 * p₂ ^ 3 * (L₂ * r₁) ^ 2 ≤ q₁ ^ 2 * p₁)
    (hε : 0 < ε) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η) (hMq : 0 ≤ Mq)
    (hεa : 2 * (ε * T) * p₂ * a ^ 2 ≤ q₁) (hεq : ε * T * q₁ ≤ p₂) (hL : 0 ≤ L)
    (hsmall : validForeverBound p₁ p₂ q₁
      (((2 * ℓ * M * L * T + 2 * M * T) * ε + L * η * Mq / ε) * Real.exp (ℓ * L))
      (η * (stroboConst ℓ M Mq T + ℓ * M * T ^ 2) / (ε * T)) ≤ r₁ / 2)
    {x xbar q : ℝ → ℝⁿ} (hx : ∀ t, 0 ≤ t → HasDerivAt x (ε • f (x t) t + q t) t)
    (hq : ∀ t, 0 ≤ t → ‖q t‖ ≤ η * Mq)
    (hxbar : ∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t) (h0 : x 0 = xbar 0)
    (hin : ∀ t, L / ε ≤ t → ‖xbar t - ystar‖ ≤ r₁ / 2) :
    ∀ t, 0 ≤ t → ‖x t - xbar t‖ ≤ validForeverBound p₁ p₂ q₁
      (((2 * ℓ * M * L * T + 2 * M * T) * ε + L * η * Mq / ε) * Real.exp (ℓ * L))
      (η * (stroboConst ℓ M Mq T + ℓ * M * T ^ 2) / (ε * T)) + (2 * ε * M + η * Mq) * T := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  have hη0 : 0 ≤ η := (sq_nonneg ε).trans hεη
  have hp₁₂ : p₁ ≤ p₂ := by
    have hn : ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ) : ℝⁿ)‖ = 1 := by simp
    have h := hbd (EuclideanSpace.single 0 1)
    rw [hn, one_pow, mul_one, mul_one] at h
    exact h.1.trans h.2
  have hp₂ : 0 < p₂ := hp₁.trans_le hp₁₂
  have hC₂0 : 0 ≤ stroboConst ℓ M Mq T + ℓ * M * T ^ 2 := by rw [stroboConst]; positivity
  generalize hC₂ : stroboConst ℓ M Mq T + ℓ * M * T ^ 2 = C₂ at hsmall hC₂0 ⊢
  have hA₀0 : 0 ≤ ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * η * Mq / ε) * Real.exp (ℓ * L) := by
    positivity
  -- KBM on `[0, L/ε]`
  have hkbm : ∀ s ∈ Icc 0 (L / ε), ‖x s - xbar s‖ ≤
      ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * η * Mq / ε) * Real.exp (ℓ * L) := by
    intro s hs
    have hq' : ∀ t ∈ Icc 0 (L / ε), ‖q t‖ ≤ ε * (η * Mq / ε) := fun t ht => by
      rw [show ε * (η * Mq / ε) = η * Mq by field_simp]; exact hq t ht.1
    have h := kbm_perturbed hf hε hL (η := η * Mq / ε) (x := x) (xbar := xbar) (q := q)
      (fun t ht => (hx t ht.1).hasDerivWithinAt) hq' hxbar h0 s hs
    refine h.trans (le_of_eq ?_)
    ring
  generalize hA₀ : ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * η * Mq / ε) * Real.exp (ℓ * L) =
    A₀ at hsmall hA₀0 hkbm ⊢
  have hh0 : 0 < ε * T := mul_pos hε hT
  generalize hh : ε * T = h at hsmall hh0 hεa hεq ⊢
  have hσ0 : 0 ≤ η * C₂ := mul_nonneg hη0 hC₂0
  generalize hσ : η * C₂ = σ at hsmall hσ0 ⊢
  have hΛ0 : 0 ≤ p₂ * A₀ ^ 2 + 96 * p₂ ^ 3 * (σ / h) ^ 2 / q₁ ^ 2 := by positivity
  have hX0 : 0 ≤ 96 * p₂ ^ 3 * (σ / h) ^ 2 / q₁ ^ 2 := by positivity
  have hpA : 0 ≤ p₂ * A₀ ^ 2 := by positivity
  have hX : 96 * p₂ ^ 3 * (σ / h) ^ 2 / q₁ ^ 2 ≤ p₂ * A₀ ^ 2 + 96 * p₂ ^ 3 * (σ / h) ^ 2 / q₁ ^ 2 :=
    le_add_of_nonneg_left hpA
  have hkey : 12 * p₂ ^ 2 / q₁ * σ ^ 2 / h =
      q₁ / (8 * p₂) * h * (96 * p₂ ^ 3 * (σ / h) ^ 2 / q₁ ^ 2) := by
    field_simp; ring
  generalize hΛ : p₂ * A₀ ^ 2 + 96 * p₂ ^ 3 * (σ / h) ^ 2 / q₁ ^ 2 = Λ at hΛ0 hX
  have hBΛ : validForeverBound p₁ p₂ q₁ A₀ (σ / h) = Real.sqrt (Λ / p₁) := by
    rw [validForeverBound, hΛ]
  rw [hBΛ] at hsmall ⊢
  have hBn : ∀ v : ℝⁿ, quadraticForm P v ≤ Λ → ‖v‖ ≤ Real.sqrt (Λ / p₁) := by
    intro v hv
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hp₁]
    have := (hbd v).1
    linarith
  have hA₀Λ : p₂ * A₀ ^ 2 ≤ Λ := by rw [← hΛ]; linarith
  generalize hB : Real.sqrt (Λ / p₁) = B at hsmall hBn ⊢
  -- the sampled deviation after `L/ε` stays in the sublevel set `V ≤ Λ`
  have ht₁0 : 0 ≤ L / ε := div_nonneg hL hε.le
  generalize ht₁ : L / ε = t₁ at ht₁0 hkbm hin
  set e : ℕ → ℝⁿ := fun k => x (t₁ + k * T) - xbar (t₁ + k * T) with he
  have hbarr : ∀ k : ℕ, ‖xbar (t₁ + k * T) - ystar‖ ≤ r₁ / 2 := fun k =>
    hin _ (by have : (0 : ℝ) ≤ k * T := by positivity
              linarith)
  have hc1 : q₁ / (8 * p₂) * h ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    have : h * q₁ ≤ p₂ := by linarith
    linarith
  have hc0 : 0 ≤ q₁ / (8 * p₂) * h := by positivity
  have hind : ∀ k : ℕ, quadraticForm P (e k) ≤ Λ := by
    intro k
    induction k with
    | zero =>
      have h1 : ‖e 0‖ ≤ A₀ := by
        simp only [he, Nat.cast_zero, zero_mul, add_zero]
        exact hkbm t₁ ⟨ht₁0, le_rfl⟩
      calc quadraticForm P (e 0) ≤ p₂ * ‖e 0‖ ^ 2 := (hbd _).2
        _ ≤ p₂ * A₀ ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) hp₂.le
        _ ≤ Λ := hA₀Λ
    | succ k ih =>
      have hek : ‖e k‖ ≤ B := hBn _ ih
      have hxk : ‖x (t₁ + k * T) - ystar‖ ≤ r₁ := by
        calc ‖x (t₁ + k * T) - ystar‖ = ‖e k + (xbar (t₁ + k * T) - ystar)‖ := by
              simp only [he]; congr 1; abel
          _ ≤ B + r₁ / 2 := (norm_add_le _ _).trans (add_le_add hek (hbarr k))
          _ ≤ r₁ := by linarith
      have hk0 : 0 ≤ t₁ + k * T := by positivity
      obtain ⟨p, hpe, hpn⟩ := perturbed_averaged_difference_step hf hρ hL₂ hD hDl hDc hA hε.le
        hηε hεη hMq (x := x) (xbar := xbar) (q := q) (s := t₁ + k * T)
        (fun t ht => hx t (hk0.trans ht.1)) (fun t ht => hq t (hk0.trans ht.1)) hxbar hxk
        ((hbarr k).trans (by linarith)) hr₁ρ
      rw [hC₂, hσ, hh] at hpn
      have hek1 : e (k + 1) = e k + h • (op J) (e k) + p := by
        simp only [he]
        rw [show t₁ + ((k + 1 : ℕ) : ℝ) * T = t₁ + k * T + T by push_cast; ring, hpe, hh]
      have hs := lyapunov_perturbed_step_le hPd hLyap hp₁ hp₂ hq₁ hbd hQ ha hh0 hεa hεq hκ (e k)
        p (σ := σ) hpn
      rw [← hek1, hkey] at hs
      refine hs.trans ?_
      have h1 := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hc1)
      have h2 := mul_le_mul_of_nonneg_left hX hc0
      linarith
  -- every time `t ≥ 0`
  intro t ht
  have hgap0 : 0 ≤ (2 * ε * M + η * Mq) * T := by positivity
  rcases le_or_gt t t₁ with htt | htt
  · refine (hkbm t ⟨ht, htt⟩).trans ?_
    have hAB : A₀ ≤ B := by
      rw [← hB]
      refine Real.le_sqrt_of_sq_le ?_
      rw [le_div_iff₀ hp₁]
      have : p₁ * A₀ ^ 2 ≤ p₂ * A₀ ^ 2 := mul_le_mul_of_nonneg_right hp₁₂ (sq_nonneg _)
      linarith
    linarith
  set k := ⌊(t - t₁) / T⌋₊ with hk
  have hkT : (k : ℝ) * T ≤ t - t₁ := by
    have := Nat.floor_le (div_nonneg (sub_nonneg.mpr htt.le) hT.le)
    calc (k : ℝ) * T ≤ (t - t₁) / T * T := mul_le_mul_of_nonneg_right this hT.le
      _ = t - t₁ := by field_simp
  have hkT' : t - t₁ - k * T ≤ T := by
    have := Nat.lt_floor_add_one ((t - t₁) / T)
    have : t - t₁ < ((k : ℝ) + 1) * T := by
      calc t - t₁ = (t - t₁) / T * T := by field_simp
        _ < ((k : ℝ) + 1) * T := mul_lt_mul_of_pos_right this hT
    linarith
  have hek : ‖e k‖ ≤ B := hBn _ (hind k)
  have hk0 : 0 ≤ t₁ + k * T := by positivity
  have hdx := perturbed_drift_le hf.2.2.2.2.2 hε.le (x := x) (q := q) (a := t₁ + k * T) (b := t)
    (by linarith) (fun s hs => hx s (hk0.trans hs.1)) (fun s hs => hq s (hk0.trans hs.1))
  have hdxb := averaged_drift hf hε.le hxbar (r := t₁ + k * T) (s := t) (by linarith)
  have e1 : x t - xbar t = e k + (x t - x (t₁ + k * T)) - (xbar t - xbar (t₁ + k * T)) := by
    simp only [he]; abel
  rw [e1]
  have hgap : (2 * ε * M + η * Mq) * (t - (t₁ + k * T)) ≤ (2 * ε * M + η * Mq) * T :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsplit : (ε * M + η * Mq) * (t - (t₁ + k * T)) + ε * M * (t - (t₁ + k * T)) =
      (2 * ε * M + η * Mq) * (t - (t₁ + k * T)) := by ring
  calc ‖e k + (x t - x (t₁ + k * T)) - (xbar t - xbar (t₁ + k * T))‖
      ≤ ‖e k‖ + ‖x t - x (t₁ + k * T)‖ + ‖xbar t - xbar (t₁ + k * T)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ B + (2 * ε * M + η * Mq) * T := by linarith

/-- **`Averaging.averaging_valid_forever` with explicit constants** (`ẋ = ε f(x, t) + ε² r(x, t)`).
With `f`, a Lyapunov certificate `(P, Q)` of `J = Df̄(y*)` and `r₁` as in
`averaging_valid_forever_perturbed`, a remainder with `‖r‖ ≤ M_r`, a depth `0 < ε ≤ 1` with
`2εTp₂a² ≤ q₁`, `εTq₁ ≤ p₂`, a slow time `L ≥ 0`, the KBM constant
`C_K = (2ℓMLT + 2MT + LM_r) e^{ℓL}` of `Averaging.kbm_perturbed`, `C₂ = C_S + ℓMT²` and
`K = validForeverBound p₁ p₂ q₁ C_K (C₂/T) = √((p₂C_K² + 96p₂³C₂²/(q₁²T²))/p₁)` with
`Kε ≤ r₁/2`: if `x̄` solves `x̄̇ = ε f̄(x̄)` and stays in the ball `‖x̄ − y*‖ ≤ r₁/2` from `L/ε`
on, the solution `x` of `ẋ = ε f(x, t) + ε² r(x, t)` with `x(0) = x̄(0)` satisfies
`‖x(t) − x̄(t)‖ ≤ (K + (2M + M_r)T) ε` for ALL `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem averaging_valid_forever_of_lyapunov [NeZero n]
    {f r : ℝⁿ → ℝ → ℝⁿ} {T ℓ M Mr ρ L₂ : ℝ} {Df : ℝⁿ → ℝ → ℝⁿ →L[ℝ] ℝⁿ} {ystar : ℝⁿ}
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hrM : ∀ x t, ‖r x t‖ ≤ Mr) (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {J : Matrix (Fin n) (Fin n) ℝ}
    (hA : HasFDerivAt (fieldAverage f T) (op J) ystar)
    {P Q : Matrix (Fin n) (Fin n) ℝ} (hPd : P.PosDef) (hLyap : P * J + Jᵀ * P = -Q)
    {p₁ p₂ q₁ a : ℝ} (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hbd : ∀ e : ℝⁿ, p₁ * ‖e‖ ^ 2 ≤ quadraticForm P e ∧ quadraticForm P e ≤ p₂ * ‖e‖ ^ 2)
    (hQ : ∀ e : ℝⁿ, q₁ * ‖e‖ ^ 2 ≤ quadraticForm Q e) (ha : ‖op J‖ ≤ a)
    {r₁ ε L : ℝ} (hr₁ : 0 < r₁) (hr₁ρ : r₁ ≤ ρ)
    (hκ : 96 * p₂ ^ 3 * (L₂ * r₁) ^ 2 ≤ q₁ ^ 2 * p₁)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεa : 2 * (ε * T) * p₂ * a ^ 2 ≤ q₁) (hεq : ε * T * q₁ ≤ p₂)
    (hL : 0 ≤ L)
    (hsmall : validForeverBound p₁ p₂ q₁
      ((2 * ℓ * M * L * T + 2 * M * T + L * Mr) * Real.exp (ℓ * L))
      ((stroboConst ℓ M Mr T + ℓ * M * T ^ 2) / T) * ε ≤ r₁ / 2)
    {x xbar : ℝ → ℝⁿ} (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t)
    (hxbar : ∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t) (h0 : x 0 = xbar 0)
    (hin : ∀ t, L / ε ≤ t → ‖xbar t - ystar‖ ≤ r₁ / 2) :
    ∀ t, 0 ≤ t → ‖x t - xbar t‖ ≤ (validForeverBound p₁ p₂ q₁
      ((2 * ℓ * M * L * T + 2 * M * T + L * Mr) * Real.exp (ℓ * L))
      ((stroboConst ℓ M Mr T + ℓ * M * T ^ 2) / T) + (2 * M + Mr) * T) * ε := by
  have hT := hf.1
  have hMr : 0 ≤ Mr := (norm_nonneg _).trans (hrM ystar 0)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  set CK := (2 * ℓ * M * L * T + 2 * M * T + L * Mr) * Real.exp (ℓ * L) with hCK
  set C₂ := stroboConst ℓ M Mr T + ℓ * M * T ^ 2 with hC₂
  have hAeq : ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * ε ^ 2 * Mr / ε) * Real.exp (ℓ * L) =
      ε * CK := by
    rw [hCK]; field_simp
  have hσeq : ε ^ 2 * C₂ / (ε * T) = ε * (C₂ / T) := by field_simp
  have hB : validForeverBound p₁ p₂ q₁
      (((2 * ℓ * M * L * T + 2 * M * T) * ε + L * ε ^ 2 * Mr / ε) * Real.exp (ℓ * L))
      (ε ^ 2 * C₂ / (ε * T)) = validForeverBound p₁ p₂ q₁ CK (C₂ / T) * ε := by
    rw [hAeq, hσeq, validForeverBound_smul _ _ _ _ _ hε.le, mul_comm]
  have h := averaging_valid_forever_perturbed hf hρ hL₂ hD hDl hDc hA hPd hLyap hp₁ hq₁ hbd hQ
    ha hr₁ hr₁ρ hκ hε hε2 le_rfl hMr hεa hεq hL (by rw [hB]; exact hsmall)
    (q := fun t => ε ^ 2 • r (x t) t) (fun t _ => hx t)
    (fun t _ => by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hrM _ _) (by positivity)) hxbar h0 hin
  intro t ht
  refine (h t ht).trans ?_
  rw [hB]
  have : ε ^ 2 * Mr ≤ ε * Mr := mul_le_mul_of_nonneg_right hε2 hMr
  nlinarith

end StabilityRn

end powerlib.Averaging
