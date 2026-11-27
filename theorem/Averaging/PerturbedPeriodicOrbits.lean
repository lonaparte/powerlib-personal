import theorem.Averaging.PeriodicOrbits

/-! # Periodic orbits from averaging under perturbations of order `ε^{1+κ}`

`theorem/Averaging/PeriodicOrbits.lean` proves Bogoliubov's second theorem for
`ẋ = ε f(x, t) + ε² r(x, t)`. A second-order normal form, obtained by a near-identity change of
coordinates, usually leaves a smaller but not quadratic remainder: the transformed amplitude of a
weakly nonlinear oscillator with a quadratic stiffness obeys `Ẇ = ε secondField(W, t) + O(ε^{3/2})`
(`ParametricResonance.QuadraticCubic.hasDerivAt_transformed_scaled`). Here the perturbation is
only of order `η` with `ε² ≤ η ≤ ε` (e.g. `η = ε^{1+κ}`, `0 < κ ≤ 1`, `rpow_order_le`), and it is
not required to be a field: it is a perturbation `q(t)` along each curve, bounded by `ηM_q` and
`ηℓ_q`-Lipschitz along pairs of curves. The period map of a family of such curves is again one
Euler step of the averaged field up to `η C_S`, with an `η L_S`-Lipschitz remainder, so a
hyperbolic equilibrium `y*` of `f̄` is again a fixed point of the period map, now `O(η/ε)`-close
to `y*` (`O(ε^κ)`), and unique near `y*`.

Scope.
* `f` satisfies the hypotheses of `Averaging.kbm_first_order` (period `T > 0`, continuity,
  `T`-periodicity, global Lipschitz constant `ℓ`, bound `M`), written out in every statement, and
  for the fixed point the smoothness hypotheses of `Averaging.exists_periodic_orbit` on the ball
  `‖x − y*‖ ≤ ρ` (an `L₂`-Lipschitz derivative `Df`, `Df(y*, ·)` continuous), `f̄(y*) = 0` and an
  invertible `A = Df̄(y*)` with inverse `B`.
* Curves `x` on `[τ, τ + T]` with `ẋ = ε f(x, t) + q(t)`, `0 < ε ≤ 1`, `ε² ≤ η ≤ ε`,
  `‖q‖ ≤ ηM_q`, and for two curves `‖q_x − q_z‖ ≤ ηℓ_q ‖x − z‖`. The curves are not assumed to
  solve a common differential equation; the perturbation may come from a coordinate change, a
  truncation remainder or a forcing, and may depend on `ε` (the constants do not). The family
  form (`exists_periodic_point_perturbed`) only needs one curve per initial value at time `0`.
* The constants `C_S = stroboConst ℓ M M_q T`, `L_S = stroboLip ℓ ℓ_q L₂ M M_q T` are those of
  `Averaging.period_step_le` / `Averaging.period_step_sub_le` with `(M_r, ℓ_r)` replaced by
  `(M_q, ℓ_q)`.
* Generic mathematics, no model family.

Source: Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations*
(the second theorem of Bogoliubov: periodic solutions near hyperbolic equilibria of the averaged
system); Hale, *Ordinary Differential Equations*, Ch. V; Sanders–Verhulst–Murdock, *Averaging
Methods in Nonlinear Dynamical Systems*, Ch. 2.9 and 6 (higher-order averaging, near-identity
transformations with remainders of fractional order); the one-period estimates are proved here
from `Averaging.periodIntegral_eq`, `Averaging.second_diff_le`,
`Averaging.fieldAverage_sub_linear_le` and Grönwall's inequality (Mathlib
`norm_le_gronwallBound_of_norm_deriv_right_le`).

Results.
* `perturbed_drift_le` — `‖x(b) − x(a)‖ ≤ (εM + ηM_q)(b − a)`.
* `perturbed_period_step_le` — `‖x(τ + T) − x(τ) − εT f̄(x(τ))‖ ≤ η C_S`.
* `perturbed_sub_le_exp` — Grönwall over one period, `‖x − z‖ ≤ e^{(ℓ + ℓ_q)T} ‖x(τ) − z(τ)‖`.
* `perturbed_period_step_sub_le` — the remainder of the period map is `η L_S`-Lipschitz for two
  curves starting in the ball of radius `r₁`, `r₁ + ε(M + M_q)T ≤ ρ`.
* `exists_periodic_point_perturbed` — **the period map of a perturbed family has a unique fixed
  point near `y*`**, `‖y_ε − y*‖ ≤ 2η‖B‖C_S/(εT)`, under `4η‖B‖L_S ≤ εT`, `2η‖B‖C_S ≤ εr₀T`.
* `rpow_order_le` — `ε² ≤ ε^{1+κ} ≤ ε` for `0 < ε ≤ 1`, `0 ≤ κ ≤ 1`.
* `exists_periodic_orbit_perturbed` — **Bogoliubov's second theorem with a remainder of order
  `η`**: `ẋ = ε f(x, t) + η r(x, t)` has a `T`-periodic solution with
  `‖x_ε(t) − y*‖ ≤ 2η‖B‖C_S/(εT) + ε(M + M_r)T`, unique among solutions with `x(T) = x(0)`,
  `‖x(0) − y*‖ ≤ r₀`.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology intervalIntegral
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ → E} {T ℓ M : ℝ}

section OnePeriod

/-- **Drift of a perturbed curve**: if `ẋ = ε f(x, t) + q(t)` on `[a, b]` with `‖f‖ ≤ M`,
`‖q‖ ≤ ηM_q`, then `‖x(b) − x(a)‖ ≤ (εM + ηM_q)(b − a)`. -/
@[tmio T, powerlib_foundation] theorem perturbed_drift_le (hfM : ∀ x t, ‖f x t‖ ≤ M)
    {ε η Mq : ℝ} (hε : 0 ≤ ε) {x q : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (ε • f (x t) t + q t) t)
    (hq : ∀ t ∈ Icc a b, ‖q t‖ ≤ η * Mq) : ‖x b - x a‖ ≤ (ε * M + η * Mq) * (b - a) := by
  refine norm_image_sub_le_of_norm_deriv_le_segment' (f := x)
    (f' := fun t => ε • f (x t) t + q t)
    (fun t ht => (hx t ht).hasDerivWithinAt) (fun t ht => ?_) b ⟨hab, le_rfl⟩
  have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
  calc ‖ε • f (x t) t + q t‖ ≤ ‖ε • f (x t) t‖ + ‖q t‖ := norm_add_le _ _
    _ = ε * ‖f (x t) t‖ + ‖q t‖ := by rw [norm_smul, Real.norm_of_nonneg hε]
    _ ≤ ε * M + η * Mq := add_le_add (mul_le_mul_of_nonneg_left (hfM _ _) hε) (hq t ht')

/-- The drift over (part of) one period, `‖x(s) − x(τ)‖ ≤ ε(M + M_q)T` for `s ∈ [τ, τ + T]`. -/
@[tmio T, powerlib_foundation] private theorem drift_period (hfM : ∀ x t, ‖f x t‖ ≤ M)
    (hM : 0 ≤ M) {ε η Mq : ℝ} (hε : 0 ≤ ε) (hηε : η ≤ ε) (hMq : 0 ≤ Mq)
    {x q : ℝ → E} {τ : ℝ} (hx : ∀ t ∈ Icc τ (τ + T), HasDerivAt x (ε • f (x t) t + q t) t)
    (hq : ∀ t ∈ Icc τ (τ + T), ‖q t‖ ≤ η * Mq) :
    ∀ s ∈ Icc τ (τ + T), ‖x s - x τ‖ ≤ ε * (M + Mq) * T := by
  intro s hs
  have hd := perturbed_drift_le hfM hε hs.1 (fun t ht => hx t ⟨ht.1, ht.2.trans hs.2⟩)
    (fun t ht => hq t ⟨ht.1, ht.2.trans hs.2⟩)
  refine hd.trans ?_
  have h1 : ε * M + η * Mq ≤ ε * (M + Mq) := by nlinarith
  exact mul_le_mul h1 (by linarith [hs.2]) (by linarith [hs.1]) (by positivity)

/-- **One period of a perturbed curve is one Euler step of the averaged field up to `η C_S`**:
for `ẋ = ε f(x, t) + q(t)` on `[τ, τ + T]`, `‖q‖ ≤ ηM_q`, `0 ≤ ε`, `ε² ≤ η ≤ ε`:
`‖x(τ + T) − x(τ) − εT f̄(x(τ))‖ ≤ η (ℓ(M + M_q)T² + M_q T)`. -/
@[tmio T, powerlib_foundation] theorem perturbed_period_step_le [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    {ε η Mq : ℝ} (hε : 0 ≤ ε) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η) (hMq : 0 ≤ Mq) {x q : ℝ → E}
    {τ : ℝ} (hx : ∀ t ∈ Icc τ (τ + T), HasDerivAt x (ε • f (x t) t + q t) t)
    (hq : ∀ t ∈ Icc τ (τ + T), ‖q t‖ ≤ η * Mq) :
    ‖x (τ + T) - x τ - (ε * T) • fieldAverage f T (x τ)‖ ≤ η * stroboConst ℓ M Mq T := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (x τ) 0)
  set y := x τ with hy
  have hcy : Continuous fun s => f y s := PeriodicField.continuous_snd hf y
  set g : ℝ → E := fun s => x s - y - ε • ∫ r in τ..s, f y r with hgdef
  have hg : ∀ s ∈ Icc τ (τ + T), HasDerivAt g (ε • f (x s) s + q s - ε • f y s) s := by
    intro s hs
    have h1 := (hcy.integral_hasStrictDerivAt τ s).hasDerivAt
    exact ((hx s hs).sub_const y).sub (h1.const_smul ε)
  have hdr := drift_period hf.2.2.2.2.2 hM hε hηε hMq hx hq
  have hbound : ∀ s ∈ Ico τ (τ + T),
      ‖ε • f (x s) s + q s - ε • f y s‖ ≤ ε ^ 2 * (ℓ * (M + Mq) * T) + η * Mq := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    have e : ε • f (x s) s + q s - ε • f y s = ε • (f (x s) s - f y s) + q s := by
      rw [smul_sub]; abel
    rw [e]
    calc ‖ε • (f (x s) s - f y s) + q s‖ ≤ ε * ‖f (x s) s - f y s‖ + ‖q s‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_of_nonneg hε]
      _ ≤ ε * (ℓ * (ε * (M + Mq) * T)) + η * Mq := by
          gcongr
          · exact (hf.2.2.2.2.1 _ _ _).trans (mul_le_mul_of_nonneg_left (hdr s hs') hℓ)
          · exact hq s hs'
      _ = ε ^ 2 * (ℓ * (M + Mq) * T) + η * Mq := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
    (fun s hs => (hg s hs).hasDerivWithinAt) hbound (τ + T) ⟨by linarith, le_rfl⟩
  have hg0 : g τ = 0 := by simp [hgdef, hy]
  have hgT : g (τ + T) = x (τ + T) - x τ - (ε * T) • fieldAverage f T (x τ) := by
    simp only [hgdef]; rw [periodIntegral_eq hf y τ, smul_smul]
  rw [hg0, sub_zero, hgT, show τ + T - τ = T by ring] at h
  refine h.trans ?_
  have hA : 0 ≤ ℓ * (M + Mq) * T * T := by positivity
  have := mul_le_mul_of_nonneg_right hεη hA
  simp only [stroboConst]
  nlinarith

/-- **Grönwall over one period for perturbed curves**: if `‖q_x − q_z‖ ≤ ηℓ_q‖x − z‖` on
`[τ, τ + T]`, `0 ≤ ε ≤ 1`, `0 ≤ η ≤ 1`, then `‖x(s) − z(s)‖ ≤ e^{(ℓ + ℓ_q)T} ‖x(τ) − z(τ)‖`
there. -/
@[tmio T, powerlib_foundation] theorem perturbed_sub_le_exp
    (hfl : ∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) (hℓ : 0 ≤ ℓ) {ε η ℓq : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hℓq : 0 ≤ ℓq) {x z qx qz : ℝ → E}
    {τ : ℝ} (hx : ∀ t ∈ Icc τ (τ + T), HasDerivAt x (ε • f (x t) t + qx t) t)
    (hz : ∀ t ∈ Icc τ (τ + T), HasDerivAt z (ε • f (z t) t + qz t) t)
    (hqxz : ∀ t ∈ Icc τ (τ + T), ‖qx t - qz t‖ ≤ η * ℓq * ‖x t - z t‖) :
    ∀ s ∈ Icc τ (τ + T), ‖x s - z s‖ ≤ Real.exp ((ℓ + ℓq) * T) * ‖x τ - z τ‖ := by
  set K := ε * ℓ + η * ℓq with hK
  have hK0 : 0 ≤ K := by positivity
  have hKle : K ≤ ℓ + ℓq := by
    have h1 : ε * ℓ ≤ ℓ := mul_le_of_le_one_left hℓ hε1
    have h2 : η * ℓq ≤ ℓq := mul_le_of_le_one_left hℓq hη1
    linarith
  have hdiff : ∀ t ∈ Icc τ (τ + T), HasDerivAt (fun s => x s - z s)
      (ε • (f (x t) t - f (z t) t) + (qx t - qz t)) t := by
    intro t ht
    have := (hx t ht).sub (hz t ht)
    convert this using 1; rw [smul_sub]; abel
  have hnd : ∀ t ∈ Icc τ (τ + T),
      ‖ε • (f (x t) t - f (z t) t) + (qx t - qz t)‖ ≤ K * ‖x t - z t‖ := by
    intro t ht
    calc _ ≤ ε * ‖f (x t) t - f (z t) t‖ + ‖qx t - qz t‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_of_nonneg hε]
      _ ≤ ε * (ℓ * ‖x t - z t‖) + η * ℓq * ‖x t - z t‖ :=
          add_le_add (mul_le_mul_of_nonneg_left (hfl _ _ _) hε) (hqxz t ht)
      _ = K * ‖x t - z t‖ := by ring
  intro s hs
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => x s - z s)
    (δ := ‖x τ - z τ‖) (K := K) (ε := 0)
    (fun t ht => (hdiff t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hdiff t (Ico_subset_Icc_self ht)).hasDerivWithinAt) le_rfl
    (fun t ht => by rw [add_zero]; exact hnd t (Ico_subset_Icc_self ht)) s hs
  rw [gronwallBound_ε0] at h
  refine h.trans ?_
  rw [mul_comm (Real.exp _)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  exact mul_le_mul hKle (by linarith [hs.2]) (by linarith [hs.1]) (by positivity)

variable {Df : E → ℝ → E →L[ℝ] E} {ystar : E} {ρ L₂ : ℝ}

/-- **The remainder of the period map of perturbed curves is `η L_S`-Lipschitz.** For two curves
`ẋ = ε f(x, t) + q_x(t)`, `ż = ε f(z, t) + q_z(t)` on `[τ, τ + T]` (`0 ≤ ε ≤ 1`,
`ε² ≤ η ≤ ε`, `‖q‖ ≤ ηM_q`, `‖q_x − q_z‖ ≤ ηℓ_q‖x − z‖`) starting in the ball
`‖· − y*‖ ≤ r₁` with `r₁ + ε(M + M_q)T ≤ ρ`, where `f(·, t)` has an `L₂`-Lipschitz derivative:
`‖(x(τ + T) − x(τ) − εT f̄(x(τ))) − (z(τ + T) − z(τ) − εT f̄(z(τ)))‖ ≤ η L_S ‖x(τ) − z(τ)‖`,
`L_S = stroboLip ℓ ℓ_q L₂ M M_q T`. -/
@[tmio T, powerlib_foundation] theorem perturbed_period_step_sub_le [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hL₂ : 0 ≤ L₂) (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    {ε η ℓq Mq : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η) (hℓq : 0 ≤ ℓq)
    (hMq : 0 ≤ Mq) {x z qx qz : ℝ → E} {τ r₁ : ℝ}
    (hx : ∀ t ∈ Icc τ (τ + T), HasDerivAt x (ε • f (x t) t + qx t) t)
    (hz : ∀ t ∈ Icc τ (τ + T), HasDerivAt z (ε • f (z t) t + qz t) t)
    (hqx : ∀ t ∈ Icc τ (τ + T), ‖qx t‖ ≤ η * Mq) (hqz : ∀ t ∈ Icc τ (τ + T), ‖qz t‖ ≤ η * Mq)
    (hqxz : ∀ t ∈ Icc τ (τ + T), ‖qx t - qz t‖ ≤ η * ℓq * ‖x t - z t‖)
    (hxτ : ‖x τ - ystar‖ ≤ r₁) (hzτ : ‖z τ - ystar‖ ≤ r₁) (hr₁ : r₁ + ε * (M + Mq) * T ≤ ρ) :
    ‖(x (τ + T) - x τ - (ε * T) • fieldAverage f T (x τ)) -
        (z (τ + T) - z τ - (ε * T) • fieldAverage f T (z τ))‖ ≤
      η * stroboLip ℓ ℓq L₂ M Mq T * ‖x τ - z τ‖ := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (x τ) 0)
  have hη0 : 0 ≤ η := (sq_nonneg ε).trans hεη
  set e₀ := ‖x τ - z τ‖ with he₀
  set G := Real.exp ((ℓ + ℓq) * T) with hG
  have hG1 : 1 ≤ G := Real.one_le_exp (by positivity)
  have hgr := perturbed_sub_le_exp hf.2.2.2.2.1 hℓ hε hε1 hη0 (hηε.trans hε1) hℓq hx hz hqxz
  have hdiff : ∀ t ∈ Icc τ (τ + T), HasDerivAt (fun s => x s - z s)
      (ε • (f (x t) t - f (z t) t) + (qx t - qz t)) t := by
    intro t ht
    have := (hx t ht).sub (hz t ht)
    convert this using 1; rw [smul_sub]; abel
  -- the deviation of `x − z` from its initial value
  have hdev : ∀ s ∈ Icc τ (τ + T),
      ‖(x s - z s) - (x τ - z τ)‖ ≤ ε * (ℓ + ℓq) * (G * e₀) * T := by
    intro s hs
    have hbd : ∀ u ∈ Ico τ s, ‖ε • (f (x u) u - f (z u) u) + (qx u - qz u)‖ ≤
        ε * (ℓ + ℓq) * (G * e₀) := by
      intro u hu
      have hu' : u ∈ Icc τ (τ + T) := ⟨hu.1, hu.2.le.trans hs.2⟩
      calc _ ≤ ε * ‖f (x u) u - f (z u) u‖ + ‖qx u - qz u‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_of_nonneg hε]
        _ ≤ ε * (ℓ * (G * e₀)) + η * ℓq * (G * e₀) := by
            gcongr
            · exact (hf.2.2.2.2.1 _ _ _).trans (mul_le_mul_of_nonneg_left (hgr u hu') hℓ)
            · exact (hqxz u hu').trans (mul_le_mul_of_nonneg_left (hgr u hu') (by positivity))
        _ ≤ ε * (ℓ * (G * e₀)) + ε * ℓq * (G * e₀) := by
            gcongr
        _ = ε * (ℓ + ℓq) * (G * e₀) := by ring
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u => x u - z u)
      (f' := fun u => ε • (f (x u) u - f (z u) u) + (qx u - qz u))
      (fun u hu => (hdiff u ⟨hu.1, hu.2.trans hs.2⟩).hasDerivWithinAt) hbd s ⟨hs.1, le_rfl⟩
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by positivity))
  have hdx := drift_period hf.2.2.2.2.2 hM hε hηε hMq hx hqx
  have hdz := drift_period hf.2.2.2.2.2 hM hε hηε hMq hz hqz
  have hball : ∀ w : ℝ → E, ‖w τ - ystar‖ ≤ r₁ → ∀ s, ‖w s - w τ‖ ≤ ε * (M + Mq) * T →
      ‖w s - ystar‖ ≤ ρ := by
    intro w hw s hs
    calc ‖w s - ystar‖ = ‖(w s - w τ) + (w τ - ystar)‖ := by congr 1; abel
      _ ≤ ‖w s - w τ‖ + ‖w τ - ystar‖ := norm_add_le _ _
      _ ≤ ρ := by linarith
  have hdrift0 : 0 ≤ ε * (M + Mq) * T := by positivity
  have hxτ' : ‖x τ - ystar‖ ≤ ρ := by linarith
  have hzτ' : ‖z τ - ystar‖ ≤ ρ := by linarith
  -- the remainder of the period map along the difference
  set yx := x τ
  set yz := z τ
  have hcx : Continuous fun s => f yx s := PeriodicField.continuous_snd hf yx
  have hcz : Continuous fun s => f yz s := PeriodicField.continuous_snd hf yz
  set g : ℝ → E := fun s => (x s - z s) - (yx - yz) - ε • ∫ r in τ..s, (f yx r - f yz r)
    with hgdef
  have hg : ∀ s ∈ Icc τ (τ + T), HasDerivAt g (ε • (f (x s) s - f (z s) s) + (qx s - qz s) -
      ε • (f yx s - f yz s)) s := by
    intro s hs
    have h1 := ((hcx.sub hcz).integral_hasStrictDerivAt τ s).hasDerivAt
    exact ((hdiff s hs).sub_const (yx - yz)).sub (h1.const_smul ε)
  have hbound : ∀ s ∈ Ico τ (τ + T),
      ‖ε • (f (x s) s - f (z s) s) + (qx s - qz s) - ε • (f yx s - f yz s)‖ ≤
        η * (G * e₀) * (T * (L₂ * (M + Mq) + ℓ * (ℓ + ℓq)) + ℓq) := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    have hsd := second_diff_le hD hDl hf.2.2.2.2.1 hℓ hL₂ (hball x hxτ s (hdx s hs'))
      (hball z hzτ s (hdz s hs')) hxτ' hzτ' (hdx s hs') (hdz s hs') s
    have e : ε • (f (x s) s - f (z s) s) + (qx s - qz s) - ε • (f yx s - f yz s) =
        ε • ((f (x s) s - f (z s) s) - (f yx s - f yz s)) + (qx s - qz s) := by
      rw [smul_sub ε (f (x s) s - f (z s) s)]; abel
    rw [e]
    calc ‖ε • ((f (x s) s - f (z s) s) - (f yx s - f yz s)) + (qx s - qz s)‖
        ≤ ε * ‖(f (x s) s - f (z s) s) - (f yx s - f yz s)‖ + ‖qx s - qz s‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_of_nonneg hε]
      _ ≤ ε * (L₂ * (ε * (M + Mq) * T) * (G * e₀) + ℓ * (ε * (ℓ + ℓq) * (G * e₀) * T)) +
            η * ℓq * (G * e₀) := by
          gcongr
          · refine hsd.trans ?_
            gcongr
            · exact hgr s hs'
            · exact hdev s hs'
          · exact (hqxz s hs').trans (mul_le_mul_of_nonneg_left (hgr s hs') (by positivity))
      _ = ε ^ 2 * (G * e₀) * (T * (L₂ * (M + Mq) + ℓ * (ℓ + ℓq))) + η * (G * e₀) * ℓq := by
          ring
      _ ≤ η * (G * e₀) * (T * (L₂ * (M + Mq) + ℓ * (ℓ + ℓq))) + η * (G * e₀) * ℓq := by
          gcongr
      _ = η * (G * e₀) * (T * (L₂ * (M + Mq) + ℓ * (ℓ + ℓq)) + ℓq) := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
    (fun s hs => (hg s hs).hasDerivWithinAt) hbound (τ + T) ⟨by linarith, le_rfl⟩
  have hg0 : g τ = 0 := by simp only [hgdef, integral_same, smul_zero, sub_zero]; abel
  have hint : ∫ r in τ..τ + T, (f yx r - f yz r) =
      T • fieldAverage f T yx - T • fieldAverage f T yz := by
    rw [intervalIntegral.integral_sub (hcx.intervalIntegrable _ _) (hcz.intervalIntegrable _ _),
      periodIntegral_eq hf yx τ, periodIntegral_eq hf yz τ]
  have hgT : g (τ + T) = (x (τ + T) - x τ - (ε * T) • fieldAverage f T (x τ)) -
      (z (τ + T) - z τ - (ε * T) • fieldAverage f T (z τ)) := by
    simp only [hgdef]
    rw [hint, smul_sub, smul_smul, smul_smul]
    abel
  rw [hg0, sub_zero, hgT, show τ + T - τ = T by ring] at h
  refine h.trans (le_of_eq ?_)
  simp only [stroboLip, ← hG]
  ring

end OnePeriod

section Orbit

variable {Df : E → ℝ → E →L[ℝ] E} {ystar : E} {ρ L₂ : ℝ}

/-- **The period map of a perturbed family has a unique fixed point near a hyperbolic
equilibrium of the averaged field.** Let `f` be as in `Averaging.exists_periodic_orbit`
(`f̄(y*) = 0`, `A = Df̄(y*)` with inverse `B`), and let `X y` be a curve with `X y 0 = y` for every
`y` in the ball `‖y − y*‖ ≤ r₀` solving `Ẋ = ε f(X, t) + Q y t` on `[0, T]`, with
`‖Q y‖ ≤ ηM_q` and `‖Q y − Q y'‖ ≤ ηℓ_q ‖X y − X y'‖` (`0 < ε ≤ 1`, `ε² ≤ η ≤ ε`). If
`2r₀ ≤ ρ`, `4‖B‖L₂r₀ ≤ 1`, `2ε(M + M_q)T ≤ ρ`, `4η‖B‖L_S ≤ εT` and `2η‖B‖C_S ≤ εr₀T`, then the
period map `y ↦ X y T` has a fixed point `y_ε` with `‖y_ε − y*‖ ≤ 2η‖B‖C_S/(εT)`, and it is its
only fixed point in the ball (`perturbed_period_step_le`, `perturbed_period_step_sub_le`, and the
Newton-type contraction `y ↦ y − (εT A)⁻¹ (X y T − y)`). -/
@[tmio T, powerlib_foundation] theorem exists_periodic_point_perturbed [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) (h0 : fieldAverage f T ystar = 0) {A B : E →L[ℝ] E}
    (hA : HasFDerivAt (fieldAverage f T) A ystar) (hAB : ∀ v, A (B v) = v)
    (hBA : ∀ v, B (A v) = v) {r₀ ε η ℓq Mq : ℝ} (hr₀ : 0 < r₀) (hr₀ρ : 2 * r₀ ≤ ρ)
    (hr₀L : 4 * ‖B‖ * L₂ * r₀ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η)
    (hℓq : 0 ≤ ℓq) (hMq : 0 ≤ Mq) (hερ : 2 * ε * (M + Mq) * T ≤ ρ)
    (hηL : 4 * η * ‖B‖ * stroboLip ℓ ℓq L₂ M Mq T ≤ ε * T)
    (hηC : 2 * η * ‖B‖ * stroboConst ℓ M Mq T ≤ ε * r₀ * T) {X Q : E → ℝ → E}
    (hX0 : ∀ y, X y 0 = y)
    (hX : ∀ y, ‖y - ystar‖ ≤ r₀ → ∀ t ∈ Icc 0 T, HasDerivAt (X y) (ε • f (X y t) t + Q y t) t)
    (hQ : ∀ y, ‖y - ystar‖ ≤ r₀ → ∀ t ∈ Icc 0 T, ‖Q y t‖ ≤ η * Mq)
    (hQl : ∀ y y', ‖y - ystar‖ ≤ r₀ → ‖y' - ystar‖ ≤ r₀ → ∀ t ∈ Icc 0 T,
      ‖Q y t - Q y' t‖ ≤ η * ℓq * ‖X y t - X y' t‖) :
    ∃ y, ‖y - ystar‖ ≤ 2 * η * ‖B‖ * stroboConst ℓ M Mq T / (ε * T) ∧ X y T = y ∧
      ∀ y', ‖y' - ystar‖ ≤ r₀ → X y' T = y' → y' = y := by
  have hT := hf.1
  have hεT : 0 < ε * T := mul_pos hε hT
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  set CS := stroboConst ℓ M Mq T with hCS
  set LS := stroboLip ℓ ℓq L₂ M Mq T with hLS
  have hX' : ∀ y, ‖y - ystar‖ ≤ r₀ → ∀ t ∈ Icc 0 (0 + T),
      HasDerivAt (X y) (ε • f (X y t) t + Q y t) t := fun y hy t ht =>
    hX y hy t (by rwa [zero_add] at ht)
  have hQ' : ∀ y, ‖y - ystar‖ ≤ r₀ → ∀ t ∈ Icc 0 (0 + T), ‖Q y t‖ ≤ η * Mq := fun y hy t ht =>
    hQ y hy t (by rwa [zero_add] at ht)
  -- the remainder of the period map
  set Ψ : E → E := fun y => X y T - y - (ε * T) • fieldAverage f T y with hΨ
  have hΨb : ∀ y, ‖y - ystar‖ ≤ r₀ → ‖Ψ y‖ ≤ η * CS := by
    intro y hy
    have h := perturbed_period_step_le hf hε.le hηε hεη hMq (hX' y hy) (hQ' y hy)
    rw [zero_add, hX0] at h
    exact h
  have hΨl : ∀ y z, ‖y - ystar‖ ≤ r₀ → ‖z - ystar‖ ≤ r₀ → ‖Ψ y - Ψ z‖ ≤ η * LS * ‖y - z‖ := by
    intro y z hy hz
    have h := perturbed_period_step_sub_le hf hL₂ hD hDl hε.le hε1 hηε hεη hℓq hMq (hX' y hy)
      (hX' z hz) (hQ' y hy) (hQ' z hz)
      (fun t ht => hQl y z hy hz t (by rwa [zero_add] at ht)) (τ := 0) (r₁ := r₀)
      (by rw [hX0]; exact hy) (by rw [hX0]; exact hz) (by linarith)
    simp only [zero_add, hX0] at h
    exact h
  -- the Newton-type map
  set N : E → E := fun y => y - B (fieldAverage f T y + (ε * T)⁻¹ • Ψ y) with hN
  have hNlip : ∀ y z, ‖y - ystar‖ ≤ r₀ → ‖z - ystar‖ ≤ r₀ → ‖N y - N z‖ ≤ 2⁻¹ * ‖y - z‖ := by
    intro y z hy hz
    have e : N y - N z = -(B (fieldAverage f T y - fieldAverage f T z - A (y - z)) +
        (ε * T)⁻¹ • B (Ψ y - Ψ z)) := by
      simp only [hN, map_sub, map_add, map_smul, hBA]
      simp only [smul_sub]; abel
    rw [e, norm_neg]
    have h1 := fieldAverage_sub_linear_le hf hρ hL₂ hD hDl hDc hA (by linarith) hy hz
    have h2 := hΨl y z hy hz
    calc ‖B (fieldAverage f T y - fieldAverage f T z - A (y - z)) +
          (ε * T)⁻¹ • B (Ψ y - Ψ z)‖
        ≤ ‖B‖ * (L₂ * r₀ * ‖y - z‖) + (ε * T)⁻¹ * (‖B‖ * (η * LS * ‖y - z‖)) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
          · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hεT.le)]
            exact mul_le_mul_of_nonneg_left
              ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
              (inv_nonneg.mpr hεT.le)
      _ = (‖B‖ * L₂ * r₀ + η * ‖B‖ * LS / (ε * T)) * ‖y - z‖ := by field_simp
      _ ≤ (4⁻¹ + 4⁻¹) * ‖y - z‖ := by
          gcongr
          · linarith
          · rw [div_le_iff₀ hεT]; linarith
      _ = 2⁻¹ * ‖y - z‖ := by norm_num
  have hys : ‖ystar - ystar‖ ≤ r₀ := by simp [hr₀.le]
  have hN0 : ‖N ystar - ystar‖ ≤ η * ‖B‖ * CS / (ε * T) := by
    have e : N ystar - ystar = -((ε * T)⁻¹ • B (Ψ ystar)) := by
      simp only [hN, h0, zero_add, map_smul]; abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hεT.le)]
    calc (ε * T)⁻¹ * ‖B (Ψ ystar)‖ ≤ (ε * T)⁻¹ * (‖B‖ * (η * CS)) :=
          mul_le_mul_of_nonneg_left ((B.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (hΨb _ hys) (norm_nonneg _))) (inv_nonneg.mpr hεT.le)
      _ = η * ‖B‖ * CS / (ε * T) := by field_simp
  have hN0' : η * ‖B‖ * CS / (ε * T) ≤ r₀ / 2 := by
    rw [div_le_iff₀ hεT]; linarith
  have hball : ∀ y, ‖y - ystar‖ ≤ r₀ → ‖N y - ystar‖ ≤ r₀ := by
    intro y hy
    calc ‖N y - ystar‖ = ‖(N y - N ystar) + (N ystar - ystar)‖ := by congr 1; abel
      _ ≤ 2⁻¹ * ‖y - ystar‖ + η * ‖B‖ * CS / (ε * T) :=
          (norm_add_le _ _).trans (add_le_add (hNlip y ystar hy hys) hN0)
      _ ≤ r₀ := by linarith
  -- the fixed point
  have hmaps : MapsTo N (Metric.closedBall ystar r₀) (Metric.closedBall ystar r₀) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    exact hball y hy
  have hcontr : ContractingWith 2⁻¹ (hmaps.restrict N _ _) := by
    refine ⟨by rw [inv_lt_one₀ (by norm_num)]; norm_num, ?_⟩
    apply LipschitzOnWith.mapsToRestrict
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    rw [Metric.mem_closedBall, dist_eq_norm] at hy hz
    rw [dist_eq_norm, dist_eq_norm]
    have : ((2⁻¹ : NNReal) : ℝ) = 2⁻¹ := by norm_num
    rw [this]
    exact hNlip y z hy hz
  obtain ⟨yε, hyε, hfix, -, -⟩ := hcontr.exists_fixedPoint' Metric.isClosed_closedBall.isComplete
    hmaps (Metric.mem_closedBall_self hr₀.le) (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_eq_norm] at hyε
  have hfix' : N yε = yε := hfix
  -- a fixed point of `N` is a fixed point of the period map and conversely
  have hfixper : ∀ y, N y = y ↔ X y T = y := by
    intro y
    constructor
    · intro hy
      have h1 : B (fieldAverage f T y + (ε * T)⁻¹ • Ψ y) = 0 := by
        simp only [hN] at hy; exact sub_eq_self.mp hy
      have h2 : fieldAverage f T y + (ε * T)⁻¹ • Ψ y = 0 := by
        rw [← hAB (fieldAverage f T y + (ε * T)⁻¹ • Ψ y), h1, map_zero]
      have h3 : Ψ y = -((ε * T) • fieldAverage f T y) := by
        have := congrArg (fun v => (ε * T) • v) h2
        simp only [smul_add, smul_smul, mul_inv_cancel₀ hεT.ne', one_smul, smul_zero] at this
        exact eq_neg_of_add_eq_zero_right this
      have h4 : X y T - y - (ε * T) • fieldAverage f T y = -((ε * T) • fieldAverage f T y) := h3
      have e : X y T = (X y T - y - (ε * T) • fieldAverage f T y) + y +
          (ε * T) • fieldAverage f T y := by abel
      rw [e, h4]; abel
    · intro hy
      have hΨy : Ψ y = -((ε * T) • fieldAverage f T y) := by
        simp only [hΨ, hy]; abel
      simp only [hN, hΨy, smul_neg, smul_smul, inv_mul_cancel₀ hεT.ne', one_smul, add_neg_cancel,
        map_zero, sub_zero]
  refine ⟨yε, ?_, (hfixper yε).mp hfix', fun y' hy' hy'T => ?_⟩
  · have h := hNlip yε ystar hyε hys
    rw [hfix'] at h
    have : ‖yε - ystar‖ ≤ 2⁻¹ * ‖yε - ystar‖ + η * ‖B‖ * CS / (ε * T) :=
      calc ‖yε - ystar‖ = ‖(yε - N ystar) + (N ystar - ystar)‖ := by congr 1; abel
        _ ≤ ‖yε - N ystar‖ + ‖N ystar - ystar‖ := norm_add_le _ _
        _ ≤ 2⁻¹ * ‖yε - ystar‖ + η * ‖B‖ * CS / (ε * T) := add_le_add h hN0
    have e : 2 * η * ‖B‖ * CS / (ε * T) = 2 * (η * ‖B‖ * CS / (ε * T)) := by ring
    rw [e]; linarith
  · have hN' : N y' = y' := (hfixper y').mpr hy'T
    have h := hNlip y' yε hy' hyε
    rw [hN', hfix'] at h
    have : ‖y' - yε‖ = 0 := by linarith [norm_nonneg (y' - yε)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- `ε² ≤ ε^{1+κ} ≤ ε` for `0 < ε ≤ 1` and `0 ≤ κ ≤ 1`: a perturbation of order `ε^{1+κ}` meets
the order hypotheses `ε² ≤ η ≤ ε` of `exists_periodic_point_perturbed`. -/
@[tmio T, powerlib_foundation] theorem rpow_order_le {ε κ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) : ε ^ 2 ≤ ε ^ (1 + κ) ∧ ε ^ (1 + κ) ≤ ε := by
  constructor
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by push_cast; linarith)
  · calc ε ^ (1 + κ) ≤ ε ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
      _ = ε := Real.rpow_one ε

/-- **Bogoliubov's second theorem with a remainder of order `η`** (`ε² ≤ η ≤ ε`, e.g.
`η = ε^{1+κ}`, `rpow_order_le`). Let `f` be as in `Averaging.exists_periodic_orbit` and let `r`
satisfy the hypotheses of `Averaging.kbm_first_order` (constants `ℓ_r`, `M_r`, independent of
`ε`). Under `2r₀ ≤ ρ`, `4‖B‖L₂r₀ ≤ 1`, `2ε(M + M_r)T ≤ ρ`, `4η‖B‖L_S ≤ εT`, `2η‖B‖C_S ≤ εr₀T`,
the system `ẋ = ε f(x, t) + η r(x, t)` has a `T`-periodic solution `x_ε` with
`‖x_ε(t) − y*‖ ≤ 2η‖B‖C_S/(εT) + ε(M + M_r)T` for all `t`, the only solution with `x(T) = x(0)`
and `‖x(0) − y*‖ ≤ r₀` (`exists_periodic_point_perturbed` with `Q y t = η r(X y t, t)`). -/
@[tmio T, powerlib_foundation] theorem exists_periodic_orbit_perturbed [CompleteSpace E]
    {r : E → ℝ → E} {ℓr Mr : ℝ}
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hr : 0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
      (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) (h0 : fieldAverage f T ystar = 0) {A B : E →L[ℝ] E}
    (hA : HasFDerivAt (fieldAverage f T) A ystar) (hAB : ∀ v, A (B v) = v)
    (hBA : ∀ v, B (A v) = v) {r₀ ε η : ℝ} (hr₀ : 0 < r₀) (hr₀ρ : 2 * r₀ ≤ ρ)
    (hr₀L : 4 * ‖B‖ * L₂ * r₀ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η)
    (hερ : 2 * ε * (M + Mr) * T ≤ ρ) (hηL : 4 * η * ‖B‖ * stroboLip ℓ ℓr L₂ M Mr T ≤ ε * T)
    (hηC : 2 * η * ‖B‖ * stroboConst ℓ M Mr T ≤ ε * r₀ * T) :
    ∃ x : ℝ → E, (∀ t, HasDerivAt x (ε • f (x t) t + η • r (x t) t) t) ∧
      (∀ t, x (t + T) = x t) ∧
      (∀ t, ‖x t - ystar‖ ≤ 2 * η * ‖B‖ * stroboConst ℓ M Mr T / (ε * T) + ε * (M + Mr) * T) ∧
      ∀ z : ℝ → E, (∀ t, HasDerivAt z (ε • f (z t) t + η • r (z t) t) t) →
        z T = z 0 → ‖z 0 - ystar‖ ≤ r₀ → z = x := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hℓr := hr.2.1
  have hη0 : 0 ≤ η := (sq_nonneg ε).trans hεη
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  have hMr : 0 ≤ Mr := (norm_nonneg _).trans (hr.2.2.2.2.2 ystar 0)
  -- the field, its continuity and Lipschitz constant
  set v : ℝ → E → E := fun t y => ε • f y t + η • r y t with hv
  have hvc : Continuous (Function.uncurry v) := by
    have h1 : Continuous fun q : ℝ × E => f q.2 q.1 :=
      hf.2.2.1.comp (continuous_snd.prodMk continuous_fst)
    have h2 : Continuous fun q : ℝ × E => r q.2 q.1 :=
      hr.2.2.1.comp (continuous_snd.prodMk continuous_fst)
    exact (h1.const_smul ε).add (h2.const_smul η)
  have hvl : ∀ t, LipschitzWith (Real.toNNReal (ε * ℓ + η * ℓr)) (v t) := by
    intro t
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    calc ‖ε • f y t + η • r y t - (ε • f z t + η • r z t)‖
        = ‖ε • (f y t - f z t) + η • (r y t - r z t)‖ := by congr 1; simp only [smul_sub]; abel
      _ ≤ ε * ‖f y t - f z t‖ + η * ‖r y t - r z t‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hε.le, Real.norm_of_nonneg hη0]
      _ ≤ ε * (ℓ * ‖y - z‖) + η * (ℓr * ‖y - z‖) := by
          gcongr
          · exact hf.2.2.2.2.1 _ _ _
          · exact hr.2.2.2.2.1 _ _ _
      _ = (ε * ℓ + η * ℓr) * ‖y - z‖ := by ring
  have huniq : ∀ x z : ℝ → E, (∀ t, HasDerivAt x (v t (x t)) t) →
      (∀ t, HasDerivAt z (v t (z t)) t) → ∀ t₀, x t₀ = z t₀ → x = z := fun x z hx hz t₀ h =>
    ODE_solution_unique_univ (v := v) (s := fun _ => univ) (fun t => (hvl t).lipschitzOnWith)
      (fun t => ⟨hx t, mem_univ _⟩) (fun t => ⟨hz t, mem_univ _⟩) h
  have hsol : ∀ y : E, ∃ x : ℝ → E, x 0 = y ∧ ∀ t, HasDerivAt x (v t (x t)) t := fun y =>
    ParametricResonance.DuffingMathieu.exists_global_solution hvc hvl y
  choose X hX0 hX using hsol
  obtain ⟨yε, hyεb, hper0, hun⟩ := exists_periodic_point_perturbed hf hρ hL₂ hD hDl hDc h0 hA
    hAB hBA hr₀ hr₀ρ hr₀L hε hε1 hηε hεη hℓr hMr hερ hηL hηC (X := X)
    (Q := fun y t => η • r (X y t) t) hX0 (fun y _ t _ => hX y t)
    (fun y _ t _ => by
      rw [norm_smul, Real.norm_of_nonneg hη0]
      exact mul_le_mul_of_nonneg_left (hr.2.2.2.2.2 _ _) hη0)
    (fun y y' _ _ t _ => by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hη0, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hr.2.2.2.2.1 _ _ _) hη0)
  have hx := hX yε
  have hxper : ∀ t, X yε (t + T) = X yε t := by
    have hshift : ∀ t, HasDerivAt (fun t => X yε (t + T)) (v t (X yε (t + T))) t := by
      intro t
      have h := (hx (t + T)).comp_add_const t T
      simp only [hv, hf.2.2.2.1, hr.2.2.2.1] at h ⊢
      exact h
    have := huniq _ _ hshift hx 0 (by show X yε (0 + T) = X yε 0; rw [zero_add, hper0, hX0])
    exact fun t => congrFun this t
  refine ⟨X yε, hx, hxper, fun t => ?_, fun z hz hzT hz0 => ?_⟩
  · obtain ⟨t', ht', hxt⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) (f := X yε) hxper hT t
    rw [hxt]
    have hd := perturbed_drift_le hf.2.2.2.2.2 hε.le (q := fun t => η • r (X yε t) t) ht'.1
      (fun t _ => hx t) (fun t _ => by
        rw [norm_smul, Real.norm_of_nonneg hη0]
        exact mul_le_mul_of_nonneg_left (hr.2.2.2.2.2 _ _) hη0)
    rw [sub_zero, hX0] at hd
    have h1 : (ε * M + η * Mr) * t' ≤ ε * (M + Mr) * T := by
      have : ε * M + η * Mr ≤ ε * (M + Mr) := by nlinarith
      exact mul_le_mul this ht'.2.le ht'.1 (by positivity)
    calc ‖X yε t' - ystar‖ = ‖(X yε t' - yε) + (yε - ystar)‖ := by congr 1; abel
      _ ≤ (ε * M + η * Mr) * t' + 2 * η * ‖B‖ * stroboConst ℓ M Mr T / (ε * T) :=
          (norm_add_le _ _).trans (add_le_add hd hyεb)
      _ ≤ _ := by linarith
  · have hzX : z = X (z 0) := huniq _ _ hz (hX (z 0)) 0 (by rw [hX0])
    have hz0' : z 0 = yε := hun (z 0) hz0 (by rw [← hzX]; exact hzT)
    rw [hzX, hz0']

end Orbit

end powerlib.Averaging
