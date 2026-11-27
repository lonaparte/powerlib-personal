import theorem.Averaging.NearIdentity

/-! # The inverse of the near-identity transformation; the transformed equation along every solution

`theorem/Averaging/NearIdentity.lean` constructs the near-identity transformation
`x = y + ε u(y, t)` of first-order averaging (`Averaging.strobGen`) and derives the transformed
equation `(I + ε D_y u) ẏ = ε f̄(y) + ε (f(y + εu, t) − f(y, t))` for a differentiable curve `y`
whose transform solves `ẋ = ε f(x, t)` (`Averaging.transformed_eq`, `Averaging.transformed_le`).
Here that curve is constructed for every solution, and the transformed equation is written as a
field. For `2εℓT < 1` the map `y ↦ y + ε u(y, t)` is a bi-Lipschitz bijection of `E`:
`y ↦ x − εu(y, t)` is a contraction with constant `2εℓT` (`Averaging.norm_strobGen_sub_le`; Banach's fixed point
theorem, Mathlib `ContractingWith.fixedPoint`), so every curve `x` has exactly one transformed
curve `y` with `x(t) = y(t) + ε u(y(t), t)`. It is continuous where `x` is, with
`(1 − 2εℓT)‖y(s) − y(t)‖ ≤ ‖x(s) − x(t)‖ + 2εM|s − t|` (`u` is `2M`-Lipschitz in time), and
differentiable where `x` is: the map `Ψ(y, s) = (y + εu(y, s), s)` has the invertible derivative
`(v, τ) ↦ ((I + εD_y u)v + τε(f − f̄), τ)` (joint differentiability of the generator,
`hasStrictFDerivAt_uncurry_strobGen`) and `s ↦ (y(s), s)` is a continuous left inverse of `Ψ`
along `s ↦ (x(s), s)` — the easy half of the inverse function theorem (Mathlib
`HasFDerivAt.of_comp_of_leftInverse`) — so `ẏ = (I + εD_y u)⁻¹(ẋ − ε(f(y, t) − f̄(y)))`
(`hasDerivAt_transformedCurve`). Along every solution of `ẋ = ε f(x, t)` this is
`ẏ = ε f̄(y) + ε² R(y, t)` with the explicit remainder field
`R(y, t) = (I + εD_y u)⁻¹(ε⁻¹(f(y + εu, t) − f(y, t)) − D_y u f̄(y))` (`nearIdRemainder`), bounded
by `4ℓMT/(1 − 2εℓT)` — which equals the constant `2ℓMT + 2ℓT(M + 2εℓMT)/(1 − 2εℓT)` of
`Averaging.transformed_le` — and Lipschitz in `y` once `Df` is `L₂`-Lipschitz.

Scope.
* `ẋ = ε f(x, t)` on a real Banach space `E`, `f` with the hypotheses of
  `Averaging.kbm_first_order` (period `T > 0`, continuity, `T`-periodicity, global Lipschitz
  constant `ℓ`, bound `M`), written out in every statement; `0 ≤ ε` (`0 < ε` for the remainder
  field) and `2εℓT < 1`.
* For the derivative: `f(·, t)` has the derivative `Df(x, t)` everywhere and `Df` is jointly
  continuous, as in `Averaging.hasFDerivAt_strobGen`. For the Lipschitz bound of the remainder:
  `Df(·, t)` is `L₂`-Lipschitz on all of `E`, uniformly in `t`.
* The transformed curve is defined for an arbitrary curve `x`; it is differentiable at every
  time at which `x` is. The global hypotheses make the inverse global; no ball is needed.
* Generic mathematics, no model family.

Source: Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations*
(the averaging change of variables); Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear
Dynamical Systems*, Ch. 2.8–2.9 (invertibility of the near-identity transformation and the
transformed equation `ẏ = ε f̄(y) + ε² R(y, t, ε)`); Hale, *Ordinary Differential Equations*,
Ch. V; Mathlib `ContractingWith.fixedPoint`, `hasStrictFDerivAt_uncurry_coprod`,
`HasFDerivAt.of_comp_of_leftInverse`; `Averaging.second_diff_le` for the second differences of `f`.

Results.
* `norm_nearIdentity_sub_ge` — `‖(y + εu(y)) − (z + εu(z))‖ ≥ (1 − 2εℓT)‖y − z‖`.
* `existsUnique_nearIdentity_inv` — `y ↦ y + εu(y, t)` is a bijection for `2εℓT < 1`.
* `existsUnique_transformedCurve` — every curve `x` has exactly one transformed curve `y`.
* `norm_strobGen_time_sub_le` — `‖u(y, s) − u(y, t)‖ ≤ 2M|s − t|`.
* `norm_transformedCurve_sub_le` — `(1 − 2εℓT)‖y(s) − y(t)‖ ≤ ‖x(s) − x(t)‖ + 2εM|s − t|`.
* `hasStrictFDerivAt_uncurry_strobGen` — the generator is jointly strictly differentiable.
* `hasDerivAt_transformedCurve` — `ẏ = (I + εD_y u)⁻¹(ẋ − ε(f(y, t) − f̄(y)))`.
* `transformed_solution` — for every solution `x`, the transformed curve exists, is
  differentiable and satisfies `Averaging.transformed_eq` and the bound of
  `Averaging.transformed_le`.
* `nearIdRemainder`, `hasDerivAt_transformed_solution` — `ẏ = ε f̄(y) + ε² R(y, t)` along every
  solution.
* `norm_nearIdRemainder_le` — `‖R(y, t)‖ ≤ 4ℓMT/(1 − 2εℓT)` for all `y, t`.
* `norm_strobGenD_sub_le` — `D_y u` is `2L₂T`-Lipschitz in the state.
* `norm_nearIdRemainder_sub_le` — `R` is Lipschitz in `y` with the constant
  `4T(L₂M(1 + εℓT) + ℓ²)/(1 − 2εℓT) + 8εℓL₂MT²/(1 − 2εℓT)²`.
* `continuous_uncurry_strobGenD`, `nearIdRemainder_periodic`,
  `continuous_uncurry_nearIdRemainder` — continuity and periodicity.
* `nearIdRemainder_field` — `R` satisfies the hypotheses on the remainder `r` of
  `Averaging.exists_periodic_orbit` (continuous, `T`-periodic, Lipschitz, bounded), so the
  transformed equation is of the form `ẏ = ε g(y, t) + ε² r(y, t)` with `g = f̄`.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology intervalIntegral MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ → E} {T ℓ M : ℝ}

/-! ## The inverse of the near-identity map -/

/-- **The near-identity map expands distances by at least `1 − 2εℓT`**:
`(1 − 2εℓT)‖y − z‖ ≤ ‖(y + εu(y, t)) − (z + εu(z, t))‖` for `ε ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem norm_nearIdentity_sub_ge
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    {ε : ℝ} (hε : 0 ≤ ε) (y z : E) (t : ℝ) :
    (1 - 2 * ε * ℓ * T) * ‖y - z‖ ≤
      ‖(y + ε • strobGen f T y t) - (z + ε • strobGen f T z t)‖ := by
  have h1 : ‖ε • (strobGen f T y t - strobGen f T z t)‖ ≤ 2 * ε * ℓ * T * ‖y - z‖ := by
    rw [norm_smul, Real.norm_of_nonneg hε]
    calc ε * ‖strobGen f T y t - strobGen f T z t‖ ≤ ε * (2 * ℓ * T * ‖y - z‖) :=
          mul_le_mul_of_nonneg_left (norm_strobGen_sub_le hf y z t) hε
      _ = 2 * ε * ℓ * T * ‖y - z‖ := by ring
  have h2 : y - z = ((y + ε • strobGen f T y t) - (z + ε • strobGen f T z t)) -
      ε • (strobGen f T y t - strobGen f T z t) := by rw [smul_sub]; abel
  have h3 : ‖y - z‖ ≤ ‖(y + ε • strobGen f T y t) - (z + ε • strobGen f T z t)‖ +
      2 * ε * ℓ * T * ‖y - z‖ :=
    calc ‖y - z‖ = ‖((y + ε • strobGen f T y t) - (z + ε • strobGen f T z t)) -
          ε • (strobGen f T y t - strobGen f T z t)‖ := congrArg norm h2
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add le_rfl h1)
  linarith

/-- **The near-identity transformation is invertible**: for `0 ≤ ε`, `2εℓT < 1`, every `x` has
exactly one preimage `y`, `y + εu(y, t) = x` (Banach's fixed point theorem for the contraction
`y ↦ x − εu(y, t)`). -/
@[tmio T, powerlib_foundation] theorem existsUnique_nearIdentity_inv
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    {ε : ℝ} (hε : 0 ≤ ε) (hεℓ : 2 * ε * ℓ * T < 1) (x : E) (t : ℝ) :
    ∃! y : E, y + ε • strobGen f T y t = x := by
  have hK : 0 ≤ 2 * ε * ℓ * T := by have := hf.1; have := hf.2.1; positivity
  have hc : ContractingWith (Real.toNNReal (2 * ε * ℓ * T))
      fun y => x - ε • strobGen f T y t := by
    refine ⟨Real.toNNReal_lt_one.mpr hεℓ, LipschitzWith.of_dist_le_mul fun y z => ?_⟩
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK, sub_sub_sub_cancel_left, ← smul_sub,
      norm_smul, Real.norm_of_nonneg hε]
    calc ε * ‖strobGen f T z t - strobGen f T y t‖ ≤ ε * (2 * ℓ * T * ‖z - y‖) :=
          mul_le_mul_of_nonneg_left (norm_strobGen_sub_le hf z y t) hε
      _ = 2 * ε * ℓ * T * ‖y - z‖ := by rw [norm_sub_rev]; ring
  have hfix : x - ε • strobGen f T (ContractingWith.fixedPoint _ hc) t =
      ContractingWith.fixedPoint _ hc := hc.fixedPoint_isFixedPt
  refine ⟨ContractingWith.fixedPoint _ hc, ?_, fun y hy => ?_⟩
  · calc ContractingWith.fixedPoint _ hc + ε • strobGen f T (ContractingWith.fixedPoint _ hc) t =
        (x - ε • strobGen f T (ContractingWith.fixedPoint _ hc) t) +
          ε • strobGen f T (ContractingWith.fixedPoint _ hc) t := by rw [hfix]
      _ = x := sub_add_cancel _ _
  · exact hc.fixedPoint_unique (eq_sub_of_add_eq hy).symm

/-- **Every curve has exactly one transformed curve**: for `0 ≤ ε`, `2εℓT < 1` and every
`x : ℝ → E` there is exactly one `y : ℝ → E` with `x(t) = y(t) + εu(y(t), t)` for all `t`. -/
@[tmio T, powerlib_foundation] theorem existsUnique_transformedCurve
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    {ε : ℝ} (hε : 0 ≤ ε) (hεℓ : 2 * ε * ℓ * T < 1) (x : ℝ → E) :
    ∃! y : ℝ → E, ∀ t, x t = y t + ε • strobGen f T (y t) t := by
  have h := fun t => existsUnique_nearIdentity_inv hf hε hεℓ (x t) t
  exact ⟨fun t => (h t).exists.choose, fun t => ((h t).exists.choose_spec).symm,
    fun z hz => funext fun t => (h t).unique (hz t).symm (h t).exists.choose_spec⟩

omit [CompleteSpace E] in
/-- **The generator is `2M`-Lipschitz in time**: `‖u(y, s) − u(y, t)‖ ≤ 2M|s − t|`. -/
@[tmio T, powerlib_foundation] theorem norm_strobGen_time_sub_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) (y : E) (s t : ℝ) :
    ‖strobGen f T y s - strobGen f T y t‖ ≤ 2 * M * |s - t| := by
  have hc : Continuous fun r => f y r - fieldAverage f T y :=
    (PeriodicField.continuous_snd hf y).sub continuous_const
  rw [strobGen, strobGen, intervalIntegral.integral_interval_sub_left
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun r _ => ?_
  exact (norm_sub_le _ _).trans (by linarith [hf.2.2.2.2.2 y r, norm_fieldAverage_le hf y])

/-- **The transformed curve moves at most as fast as the curve, up to the generator's drift**:
if `x(t) = y(t) + εu(y(t), t)` for all `t`, `ε ≥ 0`, then
`(1 − 2εℓT)‖y(s) − y(t)‖ ≤ ‖x(s) − x(t)‖ + 2εM|s − t|`. -/
@[tmio T, powerlib_foundation] theorem norm_transformedCurve_sub_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    {ε : ℝ} (hε : 0 ≤ ε) {x y : ℝ → E} (hxy : ∀ t, x t = y t + ε • strobGen f T (y t) t)
    (s t : ℝ) :
    (1 - 2 * ε * ℓ * T) * ‖y s - y t‖ ≤ ‖x s - x t‖ + 2 * ε * M * |s - t| := by
  have h1 := norm_nearIdentity_sub_ge hf hε (y s) (y t) s
  have h2 : (y s + ε • strobGen f T (y s) s) - (y t + ε • strobGen f T (y t) s) =
      (x s - x t) - ε • (strobGen f T (y t) s - strobGen f T (y t) t) := by
    rw [hxy s, hxy t, smul_sub]; abel
  have h3 : ‖ε • (strobGen f T (y t) s - strobGen f T (y t) t)‖ ≤ 2 * ε * M * |s - t| := by
    rw [norm_smul, Real.norm_of_nonneg hε]
    calc ε * ‖strobGen f T (y t) s - strobGen f T (y t) t‖ ≤ ε * (2 * M * |s - t|) :=
          mul_le_mul_of_nonneg_left (norm_strobGen_time_sub_le hf _ s t) hε
      _ = 2 * ε * M * |s - t| := by ring
  rw [h2] at h1
  exact h1.trans ((norm_sub_le _ _).trans (add_le_add le_rfl h3))

/-! ## Differentiability of the transformed curve -/

variable {Df : E → ℝ → E →L[ℝ] E}

omit [CompleteSpace E] in
/-- The state derivative `D_y u` of the generator is jointly continuous in `(y, t)`. -/
@[tmio T, powerlib_foundation] theorem continuous_uncurry_strobGenD
    (hDc : Continuous (Function.uncurry Df)) : Continuous (Function.uncurry (strobGenD Df T)) := by
  have h1 : Continuous fun p : E × ℝ => ∫ s in (0 : ℝ)..p.2, Df p.1 s :=
    continuous_parametric_primitive_of_continuous hDc
  have h2 : Continuous fun p : E × ℝ => ∫ s in (0 : ℝ)..T, Df p.1 s :=
    continuous_parametric_intervalIntegral_of_continuous' hDc 0 T |>.comp continuous_fst
  exact h1.sub ((continuous_snd.div_const T).smul h2)

/-- **The generator is jointly strictly differentiable** (continuous partial derivatives,
Mathlib `hasStrictFDerivAt_uncurry_coprod`): the derivative of `(y, t) ↦ u(y, t)` at `(y, t)` is
`(v, τ) ↦ D_y u(y, t) v + τ (f(y, t) − f̄(y))`. -/
@[tmio T, powerlib_foundation] theorem hasStrictFDerivAt_uncurry_strobGen
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    (y : E) (t : ℝ) :
    HasStrictFDerivAt (Function.uncurry (strobGen f T))
      ((strobGenD Df T y t).coprod
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f y t - fieldAverage f T y))) (y, t) := by
  set f₂ : E → ℝ → ℝ →L[ℝ] E := fun x s =>
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f x s - fieldAverage f T x) with hf₂
  have hcD : Continuous (Function.uncurry (strobGenD Df T)) := continuous_uncurry_strobGenD hDc
  have hcf : Continuous fun p : E × ℝ => f p.1 p.2 - fieldAverage f T p.1 :=
    hf.2.2.1.sub ((fieldAverage_continuous hf).comp continuous_fst)
  have hc₂ : Continuous (Function.uncurry f₂) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).continuous.comp hcf
  exact hasStrictFDerivAt_uncurry_coprod (f := strobGen f T) (f₁ := strobGenD Df T)
    (f₂ := f₂) (u := (y, t))
    (Eventually.of_forall fun v => hasFDerivAt_strobGen hf hD hDc v.1 v.2)
    (Eventually.of_forall fun v => (hasDerivAt_strobGen_time hf v.1 v.2).hasFDerivAt)
    hcD.continuousAt hc₂.continuousAt

/-- **The transformed curve is differentiable where the curve is** (the easy half of the inverse
function theorem, Mathlib `HasFDerivAt.of_comp_of_leftInverse`, for
`Ψ(y, s) = (y + εu(y, s), s)`): if `x(s) = y(s) + εu(y(s), s)` for all `s`, `0 ≤ ε`,
`2εℓT < 1`, and `x` has the derivative `x'` at `t`, then `y` has the derivative
`(I + εD_y u(y(t), t))⁻¹(x' − ε(f(y(t), t) − f̄(y(t))))` at `t`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_transformedCurve
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {ε : ℝ} (hε : 0 ≤ ε) (hεℓ : 2 * ε * ℓ * T < 1) {x y : ℝ → E}
    (hxy : ∀ s, x s = y s + ε • strobGen f T (y s) s) {x' : E} {t : ℝ} (hx : HasDerivAt x x' t) :
    HasDerivAt y (Ring.inverse (1 + ε • strobGenD Df T (y t) t)
      (x' - ε • (f (y t) t - fieldAverage f T (y t)))) t := by
  have hq : 0 < 1 - 2 * ε * ℓ * T := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (y t) 0)
  -- continuity of `y` at `t`
  have hyc : ContinuousAt y t := by
    have h1 : Tendsto (fun s => ‖x s - x t‖) (𝓝 t) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hx.continuousAt.tendsto
    have h2 : Tendsto (fun s : ℝ => |s - t|) (𝓝 t) (𝓝 0) := by
      have := ((continuous_id.sub continuous_const).abs.tendsto t :
        Tendsto (fun s : ℝ => |id s - t|) (𝓝 t) (𝓝 |id t - t|))
      simpa using this
    have h3 : Tendsto (fun s => (‖x s - x t‖ + 2 * ε * M * |s - t|) / (1 - 2 * ε * ℓ * T))
        (𝓝 t) (𝓝 0) := by
      have := (h1.add (h2.const_mul (2 * ε * M))).div_const (1 - 2 * ε * ℓ * T)
      simpa using this
    refine tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) h3)
    rw [le_div_iff₀ hq, mul_comm]
    exact norm_transformedCurve_sub_le hf hε hxy s t
  set D := strobGenD Df T (y t) t with hDdef
  set w : E := f (y t) t - fieldAverage f T (y t) with hw
  have hu : IsUnit (1 + ε • D) := isUnit_one_add_strobGenD hf hD hDc hε hεℓ (y t) t
  have hS := hasStrictFDerivAt_uncurry_strobGen hf hD hDc (y t) t
  -- the map `(y, s) ↦ (y + εu(y, s), s)`, its derivative and a left inverse of the derivative
  set Ψ' : E × ℝ →L[ℝ] E × ℝ := (ContinuousLinearMap.fst ℝ E ℝ +
      ε • D.coprod (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w)).prod
    (ContinuousLinearMap.snd ℝ E ℝ) with hΨ'
  have hΨ : HasFDerivAt (fun p : E × ℝ => (p.1 + ε • strobGen f T p.1 p.2, p.2)) Ψ' (y t, t) := by
    have h1 : HasFDerivAt (fun p : E × ℝ => p.1 + ε • strobGen f T p.1 p.2)
        (ContinuousLinearMap.fst ℝ E ℝ +
          ε • D.coprod (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w)) (y t, t) :=
      hasFDerivAt_fst.add (hS.hasFDerivAt.const_smul ε)
    exact h1.prodMk hasFDerivAt_snd
  set Φ : E × ℝ →L[ℝ] E × ℝ := (Ring.inverse (1 + ε • D) ∘L (ContinuousLinearMap.fst ℝ E ℝ -
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (ε • w)) ∘L
        ContinuousLinearMap.snd ℝ E ℝ)).prod (ContinuousLinearMap.snd ℝ E ℝ) with hΦ
  have hAinv : ∀ v, Ring.inverse (1 + ε • D) ((1 + ε • D) v) = v := fun v => by
    rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hu, one_apply_eq_self]
  have hinv : Function.LeftInverse Φ Ψ' := by
    rintro ⟨v, τ⟩
    have e1 : v + ε • (D v + τ • w) - τ • (ε • w) = (1 + ε • D) v := by
      rw [add_apply, one_apply_eq_self, smul_apply, smul_add, smul_comm ε τ w]
      abel
    simp only [hΦ, hΨ', ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, sub_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, add_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coprod_apply]
    rw [e1, hAinv]
  have hh : HasFDerivAt (fun s => (x s, s)) ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      x').prod (ContinuousLinearMap.id ℝ ℝ)) t :=
    hx.hasFDerivAt.prodMk (hasFDerivAt_id t)
  have hcomp : (fun p : E × ℝ => (p.1 + ε • strobGen f T p.1 p.2, p.2)) ∘ (fun s => (y s, s))
      =ᶠ[𝓝 t] fun s => (x s, s) :=
    Eventually.of_forall fun s => by simp only [Function.comp_apply, hxy s]
  have hg := HasFDerivAt.of_comp_of_leftInverse (g := fun s => (y s, s))
    (hyc.prodMk continuousAt_id) hΨ hh hcomp hinv
  have hy₀ := (hasFDerivAt_fst.comp t hg).hasDerivAt
  have hy : HasDerivAt y _ t := hy₀
  refine hy.congr_deriv ?_
  simp only [hΦ, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', sub_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, ContinuousLinearMap.coe_id', id, one_smul]

/-- **The transformed curve of every solution** (for `0 ≤ ε`, `2εℓT < 1`): for every solution
`x` of `ẋ = ε f(x, t)` there are a curve `y` with `x(t) = y(t) + εu(y(t), t)` (unique,
`existsUnique_transformedCurve`) and its derivative `y'`, and they satisfy the transformed
equation `Averaging.transformed_eq` and the bound `‖ẏ − ε f̄(y)‖ ≤ ε² R_ε` of
`Averaging.transformed_le`, `R_ε = 2ℓMT + 2ℓT(M + 2εℓMT)/(1 − 2εℓT)`. -/
@[tmio T, powerlib_foundation] theorem transformed_solution
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {ε : ℝ} (hε : 0 ≤ ε) (hεℓ : 2 * ε * ℓ * T < 1) {x : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ε • f (x t) t) t) :
    ∃ y y' : ℝ → E, (∀ t, x t = y t + ε • strobGen f T (y t) t) ∧ (∀ t, HasDerivAt y (y' t) t) ∧
      (∀ t, y' t + ε • strobGenD Df T (y t) t (y' t) = ε • fieldAverage f T (y t) +
        ε • (f (y t + ε • strobGen f T (y t) t) t - f (y t) t)) ∧
      ∀ t, ‖y' t - ε • fieldAverage f T (y t)‖ ≤
        ε ^ 2 * (2 * ℓ * M * T + 2 * ℓ * T * (M + 2 * ε * ℓ * M * T) / (1 - 2 * ε * ℓ * T)) := by
  obtain ⟨y, hxy, -⟩ := existsUnique_transformedCurve hf hε hεℓ x
  have hy : ∀ t, HasDerivAt y (Ring.inverse (1 + ε • strobGenD Df T (y t) t)
      (ε • f (x t) t - ε • (f (y t) t - fieldAverage f T (y t)))) t := fun t =>
    hasDerivAt_transformedCurve hf hD hDc hε hεℓ hxy (hx t)
  have hx' : ∀ t, HasDerivAt (fun t => y t + ε • strobGen f T (y t) t)
      (ε • f (y t + ε • strobGen f T (y t) t) t) t := by
    intro t
    have e : (fun t => y t + ε • strobGen f T (y t) t) = x := funext fun s => (hxy s).symm
    rw [e, ← hxy t]
    exact hx t
  exact ⟨y, _, hxy, hy, transformed_eq hf hD hDc hy hx', transformed_le hf hD hDc hε hεℓ hy hx'⟩

/-! ## The transformed equation as a field -/

/-- The remainder field of the transformed equation,
`R(y, t) = (I + εD_y u(y, t))⁻¹(ε⁻¹(f(y + εu(y, t), t) − f(y, t)) − D_y u(y, t) f̄(y))`:
along every solution, `ẏ = ε f̄(y) + ε² R(y, t)` (`hasDerivAt_transformed_solution`). -/
def nearIdRemainder (f : E → ℝ → E) (Df : E → ℝ → E →L[ℝ] E) (T ε : ℝ) (y : E) (t : ℝ) : E :=
  Ring.inverse (1 + ε • strobGenD Df T y t)
    (ε⁻¹ • (f (y + ε • strobGen f T y t) t - f y t) - strobGenD Df T y t (fieldAverage f T y))

/-- **The transformed equation along every solution**: for `0 < ε`, `2εℓT < 1`, a solution `x`
of `ẋ = ε f(x, t)` and its transformed curve `y` (`x = y + εu(y, t)`),
`ẏ = ε f̄(y) + ε² R(y, t)` with the remainder field `R = nearIdRemainder f Df T ε`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_transformed_solution
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {ε : ℝ} (hε : 0 < ε) (hεℓ : 2 * ε * ℓ * T < 1) {x y : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ε • f (x t) t) t) (hxy : ∀ t, x t = y t + ε • strobGen f T (y t) t)
    (t : ℝ) :
    HasDerivAt y (ε • fieldAverage f T (y t) + ε ^ 2 • nearIdRemainder f Df T ε (y t) t) t := by
  have h := hasDerivAt_transformedCurve hf hD hDc hε.le hεℓ hxy (hx t)
  refine h.congr_deriv ?_
  set D := strobGenD Df T (y t) t with hDdef
  have hu : IsUnit (1 + ε • D) := isUnit_one_add_strobGenD hf hD hDc hε.le hεℓ (y t) t
  have hAinv : ∀ v, Ring.inverse (1 + ε • D) ((1 + ε • D) v) = v := fun v => by
    rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hu, one_apply_eq_self]
  set fb := fieldAverage f T (y t) with hfb
  set Δ := f (y t + ε • strobGen f T (y t) t) t - f (y t) t with hΔ
  have e0 : ε ^ 2 • (ε⁻¹ • Δ) = ε • Δ := by
    rw [smul_smul, show ε ^ 2 * ε⁻¹ = ε by field_simp]
  have e1 : ε • f (x t) t - ε • (f (y t) t - fb) =
      (1 + ε • D) (ε • fb) + ε ^ 2 • (ε⁻¹ • Δ - D fb) := by
    rw [show ε ^ 2 • (ε⁻¹ • Δ - D fb) = ε • Δ - ε ^ 2 • D fb by rw [smul_sub, e0], hxy t,
      add_apply, one_apply_eq_self, smul_apply, map_smul, hΔ]
    module
  rw [e1, map_add, hAinv, map_smul]
  rfl

/-- The inverse of `I + B` for `‖B‖ ≤ q < 1` has norm at most `1/(1 − q)`. -/
@[tmio T, powerlib_foundation] private theorem norm_ringInverse_one_add_le {B : E →L[ℝ] E}
    {q : ℝ} (hB : ‖B‖ ≤ q) (hq : q < 1) : ‖Ring.inverse (1 + B)‖ ≤ (1 - q)⁻¹ := by
  have hu : IsUnit (1 + B) := by
    have h : ‖-B‖ < 1 := by rw [norm_neg]; linarith
    have hu := (Units.oneSub _ h).isUnit
    rwa [Units.val_oneSub, sub_neg_eq_add] at hu
  have hq' : 0 < 1 - q := by linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hq'.le) fun w => ?_
  have hv : Ring.inverse (1 + B) w + B (Ring.inverse (1 + B) w) = w := by
    have h := congrArg (fun L : E →L[ℝ] E => L w) (Ring.mul_inverse_cancel _ hu)
    simpa using h
  have h1 : ‖Ring.inverse (1 + B) w‖ ≤ ‖w‖ + q * ‖Ring.inverse (1 + B) w‖ := by
    calc ‖Ring.inverse (1 + B) w‖ = ‖w - B (Ring.inverse (1 + B) w)‖ :=
          congrArg norm (eq_sub_of_add_eq hv)
      _ ≤ ‖w‖ + ‖B (Ring.inverse (1 + B) w)‖ := norm_sub_le _ _
      _ ≤ ‖w‖ + q * ‖Ring.inverse (1 + B) w‖ := by
          gcongr
          exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  rw [inv_mul_eq_div, le_div_iff₀ hq']
  linarith

/-- The numerator of the remainder is bounded by `4ℓMT`. -/
@[tmio T, powerlib_foundation] private theorem norm_remainder_num_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {ε : ℝ} (hε : 0 < ε) (y : E) (t : ℝ) :
    ‖ε⁻¹ • (f (y + ε • strobGen f T y t) t - f y t) - strobGenD Df T y t (fieldAverage f T y)‖ ≤
      4 * ℓ * M * T := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 y 0)
  have h1 : ‖ε⁻¹ • (f (y + ε • strobGen f T y t) t - f y t)‖ ≤ 2 * ℓ * M * T := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    have h := hf.2.2.2.2.1 (y + ε • strobGen f T y t) y t
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le] at h
    have hu := norm_strobGen_le hf y t
    calc ε⁻¹ * ‖f (y + ε • strobGen f T y t) t - f y t‖ ≤
          ε⁻¹ * (ℓ * (ε * ‖strobGen f T y t‖)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = ℓ * ‖strobGen f T y t‖ := by field_simp
      _ ≤ ℓ * (2 * M * T) := mul_le_mul_of_nonneg_left hu hℓ
      _ = 2 * ℓ * M * T := by ring
  have h2 : ‖strobGenD Df T y t (fieldAverage f T y)‖ ≤ 2 * ℓ * M * T := by
    calc ‖strobGenD Df T y t (fieldAverage f T y)‖ ≤
          ‖strobGenD Df T y t‖ * ‖fieldAverage f T y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (2 * ℓ * T) * M := mul_le_mul (norm_strobGenD_le hf hD hDc y t)
          (norm_fieldAverage_le hf y) (norm_nonneg _) (by positivity)
      _ = 2 * ℓ * M * T := by ring
  exact (norm_sub_le _ _).trans (by linarith)

/-- **The remainder field is bounded**: `‖R(y, t)‖ ≤ 4ℓMT/(1 − 2εℓT)` for all `y, t`
(`0 < ε`, `2εℓT < 1`). The constant equals `2ℓMT + 2ℓT(M + 2εℓMT)/(1 − 2εℓT)`, the constant of
`Averaging.transformed_le`. -/
@[tmio T, powerlib_foundation] theorem norm_nearIdRemainder_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {ε : ℝ} (hε : 0 < ε) (hεℓ : 2 * ε * ℓ * T < 1) (y : E) (t : ℝ) :
    ‖nearIdRemainder f Df T ε y t‖ ≤ 4 * ℓ * M * T / (1 - 2 * ε * ℓ * T) := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 y 0)
  have hB : ‖ε • strobGenD Df T y t‖ ≤ 2 * ε * ℓ * T := by
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    have := mul_le_mul_of_nonneg_left (norm_strobGenD_le hf hD hDc y t) hε.le
    linarith
  have hinv := norm_ringInverse_one_add_le hB hεℓ
  have hN := norm_remainder_num_le hf hD hDc hε y t
  calc ‖nearIdRemainder f Df T ε y t‖ ≤ ‖Ring.inverse (1 + ε • strobGenD Df T y t)‖ *
        ‖ε⁻¹ • (f (y + ε • strobGen f T y t) t - f y t) -
          strobGenD Df T y t (fieldAverage f T y)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (1 - 2 * ε * ℓ * T)⁻¹ * (4 * ℓ * M * T) :=
        mul_le_mul hinv hN (norm_nonneg _) (inv_nonneg.mpr (by linarith))
    _ = 4 * ℓ * M * T / (1 - 2 * ε * ℓ * T) := by rw [inv_mul_eq_div]

/-! ## The Lipschitz constant of the remainder -/

omit [CompleteSpace E] in
/-- **The state derivative of the generator is `2L₂T`-Lipschitz** when `Df(·, t)` is
`L₂`-Lipschitz: `‖D_y u(y, t) − D_y u(z, t)‖ ≤ 2L₂T‖y − z‖`. -/
@[tmio T, powerlib_foundation] theorem norm_strobGenD_sub_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {L₂ : ℝ} (hL₂ : 0 ≤ L₂) (hDl : ∀ x y t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖) (y z : E) (t : ℝ) :
    ‖strobGenD Df T y t - strobGenD Df T z t‖ ≤ 2 * L₂ * T * ‖y - z‖ := by
  have hT := hf.1
  have hP : Function.Periodic (fun t => strobGenD Df T y t - strobGenD Df T z t) T := fun t => by
    simp only [strobGenD_periodic hf hD hDc]
  obtain ⟨t', ht', hxt⟩ := hP.exists_mem_Ico₀ hT t
  rw [hxt]
  have hcy : Continuous (Df y) := hDc.comp (continuous_const.prodMk continuous_id)
  have hcz : Continuous (Df z) := hDc.comp (continuous_const.prodMk continuous_id)
  have e : strobGenD Df T y t' - strobGenD Df T z t' = (∫ s in (0 : ℝ)..t', (Df y s - Df z s)) -
      (t' / T) • ∫ s in (0 : ℝ)..T, (Df y s - Df z s) := by
    rw [strobGenD, strobGenD, intervalIntegral.integral_sub (hcy.intervalIntegrable _ _)
      (hcz.intervalIntegrable _ _), intervalIntegral.integral_sub (hcy.intervalIntegrable _ _)
      (hcz.intervalIntegrable _ _), smul_sub]
    abel
  rw [e]
  have h1 := norm_integral_le_of_norm_le_const (a := 0) (b := t')
    (f := fun s => Df y s - Df z s) (C := L₂ * ‖y - z‖) (fun s _ => hDl y z s)
  have h2 := norm_integral_le_of_norm_le_const (a := 0) (b := T)
    (f := fun s => Df y s - Df z s) (C := L₂ * ‖y - z‖) (fun s _ => hDl y z s)
  rw [sub_zero, abs_of_nonneg ht'.1] at h1
  rw [sub_zero, abs_of_pos hT] at h2
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg ht'.1 hT.le)]
  have h3 : t' / T * ‖∫ s in (0 : ℝ)..T, (Df y s - Df z s)‖ ≤ t' / T * (L₂ * ‖y - z‖ * T) :=
    mul_le_mul_of_nonneg_left h2 (div_nonneg ht'.1 hT.le)
  have h4 : t' / T * (L₂ * ‖y - z‖ * T) = L₂ * ‖y - z‖ * t' := by field_simp
  have h5 : 0 ≤ L₂ * ‖y - z‖ := by positivity
  nlinarith [ht'.2]

/-- **The remainder field is Lipschitz in the state.** If moreover `Df(·, t)` is `L₂`-Lipschitz
on `E` (uniformly in `t`), then for `0 < ε`, `2εℓT < 1`:
`‖R(y, t) − R(z, t)‖ ≤ (4T(L₂M(1 + εℓT) + ℓ²)/(1 − 2εℓT) + 8εℓL₂MT²/(1 − 2εℓT)²) ‖y − z‖`
(second differences of `f`, `Averaging.second_diff_le`; `I + εD_y u` is invertible with
`‖(I + εD_y u)⁻¹‖ ≤ 1/(1 − 2εℓT)` and `D_y u` is `2L₂T`-Lipschitz). -/
@[tmio T, powerlib_foundation] theorem norm_nearIdRemainder_sub_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {L₂ : ℝ} (hL₂ : 0 ≤ L₂) (hDl : ∀ x y t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    {ε : ℝ} (hε : 0 < ε) (hεℓ : 2 * ε * ℓ * T < 1) (y z : E) (t : ℝ) :
    ‖nearIdRemainder f Df T ε y t - nearIdRemainder f Df T ε z t‖ ≤
      (4 * T * (L₂ * M * (1 + ε * ℓ * T) + ℓ ^ 2) / (1 - 2 * ε * ℓ * T) +
        8 * ε * ℓ * L₂ * M * T ^ 2 / (1 - 2 * ε * ℓ * T) ^ 2) * ‖y - z‖ := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 y 0)
  have hq : 0 < 1 - 2 * ε * ℓ * T := by linarith
  set q := 2 * ε * ℓ * T with hqdef
  set Dy := strobGenD Df T y t with hDy
  set Dz := strobGenD Df T z t with hDz
  set uy := strobGen f T y t with huy
  set uz := strobGen f T z t with huz
  obtain ⟨Ny, hNy⟩ : ∃ N, N = ε⁻¹ • (f (y + ε • uy) t - f y t) - Dy (fieldAverage f T y) :=
    ⟨_, rfl⟩
  obtain ⟨Nz, hNz⟩ : ∃ N, N = ε⁻¹ • (f (z + ε • uz) t - f z t) - Dz (fieldAverage f T z) :=
    ⟨_, rfl⟩
  have hRy : nearIdRemainder f Df T ε y t = Ring.inverse (1 + ε • Dy) Ny := by rw [hNy]; rfl
  have hRz : nearIdRemainder f Df T ε z t = Ring.inverse (1 + ε • Dz) Nz := by rw [hNz]; rfl
  have hBy : ‖ε • Dy‖ ≤ q := by
    rw [norm_smul, Real.norm_of_nonneg hε.le, hqdef]
    have := mul_le_mul_of_nonneg_left (norm_strobGenD_le hf hD hDc y t) hε.le
    linarith
  have hBz : ‖ε • Dz‖ ≤ q := by
    rw [norm_smul, Real.norm_of_nonneg hε.le, hqdef]
    have := mul_le_mul_of_nonneg_left (norm_strobGenD_le hf hD hDc z t) hε.le
    linarith
  have hiy := norm_ringInverse_one_add_le hBy hεℓ
  have hiz := norm_ringInverse_one_add_le hBz hεℓ
  have hzu : IsUnit (1 + ε • Dz) := isUnit_one_add_strobGenD hf hD hDc hε.le hεℓ z t
  have hyu : IsUnit (1 + ε • Dy) := isUnit_one_add_strobGenD hf hD hDc hε.le hεℓ y t
  have hNzb : ‖Nz‖ ≤ 4 * ℓ * M * T := hNz ▸ norm_remainder_num_le hf hD hDc hε z t
  have hDyz : ‖Dy - Dz‖ ≤ 2 * L₂ * T * ‖y - z‖ :=
    norm_strobGenD_sub_le hf hD hDc hL₂ hDl y z t
  -- the numerators
  have hΔ : ‖(f (y + ε • uy) t - f y t) - (f (z + ε • uz) t - f z t)‖ ≤
      ε * (2 * L₂ * M * T * (1 + q) + 2 * ℓ ^ 2 * T) * ‖y - z‖ := by
    have huyz : ‖uy - uz‖ ≤ 2 * ℓ * T * ‖y - z‖ := norm_strobGen_sub_le hf y z t
    have hm1 : ‖(y + ε • uy) - (z + ε • uz)‖ ≤ (1 + q) * ‖y - z‖ := by
      have e : (y + ε • uy) - (z + ε • uz) = (y - z) + ε • (uy - uz) := by rw [smul_sub]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hε.le, hqdef]
      have := mul_le_mul_of_nonneg_left huyz hε.le
      nlinarith
    have hm2 : ‖y - z‖ ≤ (1 + q) * ‖y - z‖ := by
      have : 0 ≤ q * ‖y - z‖ := by rw [hqdef]; positivity
      linarith
    have hsd := second_diff_le (f := f) (Df := Df) (ystar := 0)
      (ρ := ‖y + ε • uy‖ + ‖y‖ + ‖z + ε • uz‖ + ‖z‖) (fun x _ => hD x) (fun x y _ _ => hDl x y)
      hf.2.2.2.2.1 hℓ hL₂ (a := y + ε • uy) (b := y) (c := z + ε • uz) (d := z)
      (by rw [sub_zero]; linarith [norm_nonneg y, norm_nonneg (z + ε • uz), norm_nonneg z])
      (by rw [sub_zero]; linarith [norm_nonneg (y + ε • uy), norm_nonneg (z + ε • uz),
        norm_nonneg z])
      (by rw [sub_zero]; linarith [norm_nonneg (y + ε • uy), norm_nonneg y, norm_nonneg z])
      (by rw [sub_zero]; linarith [norm_nonneg (y + ε • uy), norm_nonneg y,
        norm_nonneg (z + ε • uz)]) hm1 hm2 t
    have hab : ‖(y + ε • uy) - y‖ ≤ ε * (2 * M * T) := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le]
      exact mul_le_mul_of_nonneg_left (norm_strobGen_le hf y t) hε.le
    have habcd : ‖((y + ε • uy) - y) - ((z + ε • uz) - z)‖ ≤ ε * (2 * ℓ * T * ‖y - z‖) := by
      rw [add_sub_cancel_left, add_sub_cancel_left, ← smul_sub, norm_smul,
        Real.norm_of_nonneg hε.le]
      exact mul_le_mul_of_nonneg_left huyz hε.le
    refine hsd.trans ?_
    have hq0 : 0 ≤ 1 + q := by rw [hqdef]; positivity
    have k1 : L₂ * ((1 + q) * ‖y - z‖) * ‖(y + ε • uy) - y‖ ≤
        L₂ * ((1 + q) * ‖y - z‖) * (ε * (2 * M * T)) :=
      mul_le_mul_of_nonneg_left hab (by positivity)
    have k2 := mul_le_mul_of_nonneg_left habcd hℓ
    nlinarith
  have hNyz : ‖Ny - Nz‖ ≤ 4 * T * (L₂ * M * (1 + ε * ℓ * T) + ℓ ^ 2) * ‖y - z‖ := by
    have e : Ny - Nz = ε⁻¹ • ((f (y + ε • uy) t - f y t) - (f (z + ε • uz) t - f z t)) -
        ((Dy - Dz) (fieldAverage f T y) + Dz (fieldAverage f T y - fieldAverage f T z)) := by
      rw [hNy, hNz]
      simp only [smul_sub, sub_apply, map_sub]
      abel
    rw [e]
    have k1 : ‖ε⁻¹ • ((f (y + ε • uy) t - f y t) - (f (z + ε • uz) t - f z t))‖ ≤
        (2 * L₂ * M * T * (1 + q) + 2 * ℓ ^ 2 * T) * ‖y - z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
      calc ε⁻¹ * ‖(f (y + ε • uy) t - f y t) - (f (z + ε • uz) t - f z t)‖ ≤
            ε⁻¹ * (ε * (2 * L₂ * M * T * (1 + q) + 2 * ℓ ^ 2 * T) * ‖y - z‖) :=
            mul_le_mul_of_nonneg_left hΔ (by positivity)
        _ = (2 * L₂ * M * T * (1 + q) + 2 * ℓ ^ 2 * T) * ‖y - z‖ := by field_simp
    have k2 : ‖(Dy - Dz) (fieldAverage f T y)‖ ≤ 2 * L₂ * T * ‖y - z‖ * M :=
      ((Dy - Dz).le_opNorm _).trans (mul_le_mul hDyz (norm_fieldAverage_le hf y)
        (norm_nonneg _) (by positivity))
    have k3 : ‖Dz (fieldAverage f T y - fieldAverage f T z)‖ ≤ 2 * ℓ * T * (ℓ * ‖y - z‖) :=
      (Dz.le_opNorm _).trans (mul_le_mul (norm_strobGenD_le hf hD hDc z t)
        (fieldAverage_lipschitz hf y z) (norm_nonneg _) (by positivity))
    have k4 := (norm_sub_le (ε⁻¹ • ((f (y + ε • uy) t - f y t) - (f (z + ε • uz) t - f z t)))
      ((Dy - Dz) (fieldAverage f T y) + Dz (fieldAverage f T y - fieldAverage f T z))).trans
      (add_le_add k1 ((norm_add_le _ _).trans (add_le_add k2 k3)))
    refine k4.trans (le_of_eq ?_)
    rw [hqdef]; ring
  -- the inverses
  have hinvd : ‖Ring.inverse (1 + ε • Dy) - Ring.inverse (1 + ε • Dz)‖ ≤
      (1 - q)⁻¹ * (ε * (2 * L₂ * T * ‖y - z‖)) * (1 - q)⁻¹ := by
    have hid : Ring.inverse (1 + ε • Dy) - Ring.inverse (1 + ε • Dz) =
        Ring.inverse (1 + ε • Dy) * ((1 + ε • Dz) - (1 + ε • Dy)) * Ring.inverse (1 + ε • Dz) := by
      rw [mul_sub, sub_mul, mul_assoc, Ring.mul_inverse_cancel _ hzu, mul_one,
        Ring.inverse_mul_cancel _ hyu, one_mul]
    have hdiff : ‖(1 + ε • Dz) - (1 + ε • Dy)‖ ≤ ε * (2 * L₂ * T * ‖y - z‖) := by
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hε.le, norm_sub_rev]
      exact mul_le_mul_of_nonneg_left hDyz hε.le
    rw [hid]
    refine (norm_mul_le _ _).trans ?_
    refine mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul hiy hdiff (norm_nonneg _)
      (inv_nonneg.mpr hq.le))) hiz (norm_nonneg _) (by positivity)
  -- combine
  rw [hRy, hRz]
  have e : Ring.inverse (1 + ε • Dy) Ny - Ring.inverse (1 + ε • Dz) Nz =
      Ring.inverse (1 + ε • Dy) (Ny - Nz) +
        (Ring.inverse (1 + ε • Dy) - Ring.inverse (1 + ε • Dz)) Nz := by
    rw [map_sub, sub_apply]; abel
  rw [e]
  have k1 : ‖Ring.inverse (1 + ε • Dy) (Ny - Nz)‖ ≤
      (1 - q)⁻¹ * (4 * T * (L₂ * M * (1 + ε * ℓ * T) + ℓ ^ 2) * ‖y - z‖) :=
    ((Ring.inverse (1 + ε • Dy)).le_opNorm _).trans
      (mul_le_mul hiy hNyz (norm_nonneg _) (inv_nonneg.mpr hq.le))
  have k2 : ‖(Ring.inverse (1 + ε • Dy) - Ring.inverse (1 + ε • Dz)) Nz‖ ≤
      (1 - q)⁻¹ * (ε * (2 * L₂ * T * ‖y - z‖)) * (1 - q)⁻¹ * (4 * ℓ * M * T) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hinvd hNzb (norm_nonneg _)
      (by positivity))
  refine (norm_add_le _ _).trans ((add_le_add k1 k2).trans (le_of_eq ?_))
  rw [hqdef]
  field_simp
  ring

/-! ## The remainder is a periodic field of the averaging class -/

/-- The remainder field is `T`-periodic in time. -/
@[tmio T, powerlib_foundation] theorem nearIdRemainder_periodic
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    (ε : ℝ) (y : E) (t : ℝ) :
    nearIdRemainder f Df T ε y (t + T) = nearIdRemainder f Df T ε y t := by
  simp only [nearIdRemainder, strobGen_periodic hf, strobGenD_periodic hf hD hDc, hf.2.2.2.1]

/-- The remainder field is jointly continuous in `(y, t)` (`Ring.inverse` is continuous at units,
Mathlib `NormedRing.inverse_continuousAt`). -/
@[tmio T, powerlib_foundation] theorem continuous_uncurry_nearIdRemainder
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {ε : ℝ} (hε : 0 ≤ ε) (hεℓ : 2 * ε * ℓ * T < 1) :
    Continuous (Function.uncurry (nearIdRemainder f Df T ε)) := by
  have hu : Continuous (Function.uncurry (strobGen f T)) := continuous_iff_continuousAt.mpr
    fun p => (hasStrictFDerivAt_uncurry_strobGen hf hD hDc p.1 p.2).continuousAt
  have hcD : Continuous (Function.uncurry (strobGenD Df T)) := continuous_uncurry_strobGenD hDc
  have hA : Continuous fun p : E × ℝ => (1 : E →L[ℝ] E) + ε • strobGenD Df T p.1 p.2 :=
    continuous_const.add (hcD.const_smul ε)
  have hinv : Continuous fun p : E × ℝ =>
      Ring.inverse ((1 : E →L[ℝ] E) + ε • strobGenD Df T p.1 p.2) := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    obtain ⟨v, hv⟩ := isUnit_one_add_strobGenD hf hD hDc hε hεℓ p.1 p.2
    have h := NormedRing.inverse_continuousAt v
    rw [hv] at h
    have h2 : ContinuousAt (Ring.inverse ∘
        fun p : E × ℝ => (1 : E →L[ℝ] E) + ε • strobGenD Df T p.1 p.2) p :=
      ContinuousAt.comp (f := fun p : E × ℝ => (1 : E →L[ℝ] E) + ε • strobGenD Df T p.1 p.2) h
        hA.continuousAt
    exact h2
  have hg : Continuous fun p : E × ℝ => f (p.1 + ε • strobGen f T p.1 p.2) p.2 :=
    hf.2.2.1.comp ((continuous_fst.add (hu.const_smul ε)).prodMk continuous_snd)
  have hN : Continuous fun p : E × ℝ => ε⁻¹ • (f (p.1 + ε • strobGen f T p.1 p.2) p.2 - f p.1 p.2) -
      strobGenD Df T p.1 p.2 (fieldAverage f T p.1) :=
    ((hg.sub hf.2.2.1).const_smul ε⁻¹).sub
      (hcD.clm_apply ((fieldAverage_continuous hf).comp continuous_fst))
  exact hinv.clm_apply hN

/-- **The remainder is a field of the class of `Averaging.kbm_first_order`**: for `0 < ε`,
`2εℓT < 1` and `Df(·, t)` `L₂`-Lipschitz, `R = nearIdRemainder f Df T ε` is continuous,
`T`-periodic, `L_R`-Lipschitz in the state with
`L_R = 4T(L₂M(1 + εℓT) + ℓ²)/(1 − 2εℓT) + 8εℓL₂MT²/(1 − 2εℓT)²` and bounded by
`4ℓMT/(1 − 2εℓT)` — the hypotheses on the remainder `r` of `Averaging.exists_periodic_orbit`,
`Averaging.exp_stable_of_lyapunov` and `Averaging.averaging_valid_forever`, so that the
transformed equation `ẏ = ε f̄(y) + ε² R(y, t)` (`hasDerivAt_transformed_solution`) is of their
form (the averaged field `f̄`, autonomous, is continuous, `ℓ`-Lipschitz and bounded by `M`:
`Averaging.fieldAverage_continuous`, `Averaging.fieldAverage_lipschitz`,
`Averaging.norm_fieldAverage_le`). -/
@[tmio T, powerlib_foundation] theorem nearIdRemainder_field
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hD : ∀ x t, HasFDerivAt (fun y => f y t) (Df x t) x) (hDc : Continuous (Function.uncurry Df))
    {L₂ : ℝ} (hL₂ : 0 ≤ L₂) (hDl : ∀ x y t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    {ε : ℝ} (hε : 0 < ε) (hεℓ : 2 * ε * ℓ * T < 1) :
    0 < T ∧ 0 ≤ 4 * T * (L₂ * M * (1 + ε * ℓ * T) + ℓ ^ 2) / (1 - 2 * ε * ℓ * T) +
        8 * ε * ℓ * L₂ * M * T ^ 2 / (1 - 2 * ε * ℓ * T) ^ 2 ∧
      Continuous (Function.uncurry (nearIdRemainder f Df T ε)) ∧
      (∀ y t, nearIdRemainder f Df T ε y (t + T) = nearIdRemainder f Df T ε y t) ∧
      (∀ y z t, ‖nearIdRemainder f Df T ε y t - nearIdRemainder f Df T ε z t‖ ≤
        (4 * T * (L₂ * M * (1 + ε * ℓ * T) + ℓ ^ 2) / (1 - 2 * ε * ℓ * T) +
          8 * ε * ℓ * L₂ * M * T ^ 2 / (1 - 2 * ε * ℓ * T) ^ 2) * ‖y - z‖) ∧
      ∀ y t, ‖nearIdRemainder f Df T ε y t‖ ≤ 4 * ℓ * M * T / (1 - 2 * ε * ℓ * T) := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hq : 0 < 1 - 2 * ε * ℓ * T := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (0 : E) 0)
  refine ⟨hT, ?_, continuous_uncurry_nearIdRemainder hf hD hDc hε.le hεℓ,
    nearIdRemainder_periodic hf hD hDc ε, norm_nearIdRemainder_sub_le hf hD hDc hL₂ hDl hε hεℓ,
    norm_nearIdRemainder_le hf hD hDc hε hεℓ⟩
  have h1 : 0 ≤ 4 * T * (L₂ * M * (1 + ε * ℓ * T) + ℓ ^ 2) / (1 - 2 * ε * ℓ * T) :=
    div_nonneg (by positivity) hq.le
  have h2 : 0 ≤ 8 * ε * ℓ * L₂ * M * T ^ 2 / (1 - 2 * ε * ℓ * T) ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg _)
  linarith

end powerlib.Averaging
