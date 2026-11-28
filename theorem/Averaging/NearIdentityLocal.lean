import theorem.Averaging.NearIdentityInverse
import theorem.Map.CenterManifold

/-! # The near-identity transformation of a field given only on a ball

`theorem/Averaging/NearIdentityInverse.lean` inverts the near-identity transformation
`x = y + εu(y, t)`, `u(y, t) = ∫₀ᵗ (f(y, s) − f̄(y)) ds`, and writes the transformed equation
`ẏ = εf̄(y) + ε²R(y, t)` for a field with the hypotheses of `Averaging.kbm_first_order` on all of
`E`; its Scope notes that the global hypotheses make the inverse global. Here `f` has the
averaging hypotheses only on the open ball `‖x − x₀‖ < ρ`: continuity, `T`-periodicity, Lipschitz
constant `ℓ`, bound `M`, the state derivative `Df` (jointly continuous), and for the Lipschitz
bound of the remainder an `L₂`-Lipschitz `Df`, all on the ball. With the same constants as the
global theorems, read off the local data:
* for `0 ≤ ε`, `2εℓT < 1` and radii `ρ₂ + 2εMT ≤ ρ₁ < ρ` the map `y ↦ y + εu(y, t)` is
  bi-Lipschitz on the ball (constants `1 ∓ 2εℓT`) and maps
  `D = {‖y − x₀‖ ≤ ρ₁, ‖y + εu(y, t) − x₀‖ ≤ ρ₂}` bijectively onto the closed ball of radius `ρ₂`;
  `D` lies between the closed balls of radii `ρ₂ ∓ 2εMT` (`nearIdentity_bijOn_local`: the
  contraction `y ↦ x − εu(y, t)` of the closed ball of radius `ρ₁`, Mathlib
  `ContractingWith.efixedPoint'`);
* every solution of `ẋ = εf(x, t)` on an open set of times `S` that stays in the closed ball of
  radius `ρ₂` has exactly one transformed curve `y` in the closed ball of radius `ρ₁`, and for
  `0 < ε` it is differentiable on `S` with `ẏ = εf̄(y) + ε²R(y, t)`, `R = nearIdRemainder f Df T ε`
  the remainder field of `NearIdentityInverse`, `‖R(y(t), t)‖ ≤ 4ℓMT/(1 − 2εℓT)`
  (`transformed_solution_local`);
* on every closed ball of radius `ρ₃` with `ρ₃ + 2εMT < ρ` the remainder is `T`-periodic, bounded
  by `4ℓMT/(1 − 2εℓT)` and Lipschitz with
  `L_R = 4T(L₂M(1 + εℓT) + ℓ²)/(1 − 2εℓT) + 8εℓL₂MT²/(1 − 2εℓT)²`
  (`nearIdRemainder_field_local`), the constants of `Averaging.nearIdRemainder_field`.

Method. No cut-off of the field is used. A cut-off equal to `f` near the solution would make the
global theorems applicable, but: in a general Banach space there is no `C¹` cut-off function at
all (no `C¹` bump on `ℓ¹` or `C[0, 1]`), and the retractions that exist in every normed space (the
radial retraction `Map.CenterManifold.ballRetract`, the clamp
`ParametricResonance.DuffingMathieu.clampC` on `ℂ`) are only Lipschitz, so `f ∘ π` has no
derivative; a multiplicative cut-off `χf` (Hilbert space) has the Lipschitz constant
`ℓ + M sup‖Dχ‖ > ℓ`, so the smallness condition and every constant would be those of the cut-off
field; a smooth `1`-Lipschitz radial retraction (Hilbert space) keeps `ℓ` and `M` but not `L₂`.
Instead the global lemmas are reused pointwise: for `y` in the ball the frozen field
`(z, s) ↦ f(y, s)` (and `(z, s) ↦ Df(y, s)` in `E →L[ℝ] E`, and the differences
`f(y, s) − f(z, s)`, `Df(y, s) − Df(z, s)`) has the global hypotheses with Lipschitz constant `0`,
and its generator is `u(y, ·)` (resp. `D_y u(y, ·)`, resp. the differences), so
`Averaging.norm_strobGen_le`, `Averaging.strobGen_periodic`, `Averaging.norm_strobGen_time_sub_le`,
`Averaging.hasDerivAt_strobGen_time`, `Averaging.norm_fieldAverage_le`, `Averaging.strobGen_eq`
give the bounds on the ball with the local constants; the joint continuity of `D_y u` at a point
of the ball is `Averaging.continuous_uncurry_strobGenD` for `Df(π(·), ·)`, `π` the radial
retraction onto a smaller closed ball (only continuity is needed there). The differentiation under
the integral sign, the left-inverse argument and the remainder estimates are carried out on the
convex ball.

Scope.
* `ẋ = εf(x, t)` on a real Banach space `E`; the hypotheses on `f` (period `T > 0`, `0 ≤ ℓ`,
  `ContinuousOn` on `ball x₀ ρ ×ˢ univ`, periodicity, Lipschitz constant `ℓ`, bound `M`), on `Df`
  (`HasFDerivAt (f · t) (Df x t) x` and joint continuity on the ball) and the `L₂`-Lipschitz bound
  of `Df` are written out in every statement, all on the OPEN ball; nothing is assumed outside it.
* Radii: `ρ > 0` where the existence of preimages or the bound `M ≥ 0` is used; preimages for
  `‖x − x₀‖ ≤ ρ₂` in the closed ball of radius `ρ₁`, `ρ₂ + 2εMT ≤ ρ₁ < ρ`; remainder bounds where
  `y` and `y + εu(y, t)` lie in the ball. `0 ≤ ε` for the map, `0 < ε` for the remainder field.
* Solutions on an open set of times `S` (e.g. `ℝ` or an interval `(0, L/ε)`), staying in the
  closed ball of radius `ρ₂` on `S`; uniqueness of the transformed curve is among the curves with
  values in the closed ball of radius `ρ₁` on `S`. Continuity of `R` in `(y, t)` is not claimed.
* Generic mathematics, no model family.

Source: Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear Dynamical Systems*, Ch. 2.8–2.9
(the near-identity transformation and the transformed equation `ẏ = εf̄(y) + ε²R(y, t, ε)` on a
domain `D ⊂ ℝⁿ`, for solutions that stay in the interior of `D`); Hale, *Ordinary Differential
Equations*, Ch. V; the global theorems `Averaging.existsUnique_transformedCurve`,
`Averaging.hasDerivAt_transformedCurve`, `Averaging.hasDerivAt_transformed_solution`,
`Averaging.norm_nearIdRemainder_le`, `Averaging.norm_nearIdRemainder_sub_le`,
`Averaging.nearIdRemainder_field` (`theorem/Averaging/NearIdentityInverse.lean`) and the open
item of its Scope (the inverse on a ball); Mathlib `ContractingWith.efixedPoint'`,
`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`,
`hasStrictFDerivAt_uncurry_coprod`, `HasFDerivAt.of_comp_of_leftInverse`,
`HasFDerivAt.le_of_lip'`.

Results.
* `norm_fderiv_le_local` — `‖Df(y, t)‖ ≤ ℓ` on the ball.
* `norm_strobGen_le_local`, `norm_strobGen_sub_le_local`, `norm_strobGen_time_sub_le_local`,
  `strobGen_periodic_local`, `hasDerivAt_strobGen_time_local` — `‖u‖ ≤ 2MT`, `u` is
  `2ℓT`-Lipschitz in the state and `2M`-Lipschitz in time, periodic, `∂ₜu = f − f̄`, on the ball.
* `norm_fieldAverage_le_local`, `norm_fieldAverage_sub_le_local` — `‖f̄‖ ≤ M`, `f̄` is
  `ℓ`-Lipschitz on the ball.
* `norm_strobGenD_le_local`, `strobGenD_periodic_local`, `norm_strobGenD_sub_le_local` —
  `‖D_y u‖ ≤ 2ℓT`, periodic, `2L₂T`-Lipschitz on the ball.
* `hasFDerivAt_strobGen_local`, `continuousAt_uncurry_strobGenD_local`,
  `hasStrictFDerivAt_uncurry_strobGen_local` — the state derivative, its joint continuity and the
  joint strict derivative of the generator at every point of the ball.
* `isUnit_one_add_strobGenD_local` — `I + εD_y u` is invertible, `‖(I + εD_y u)⁻¹‖ ≤ 1/(1 − 2εℓT)`.
* `norm_nearIdentity_sub_local` — the near-identity map is bi-Lipschitz on the ball.
* `nearIdentity_bijOn_local` — the bijection between the nested balls.
* `norm_transformedCurve_sub_le_local`, `hasDerivAt_transformedCurve_local` — continuity and
  derivative of a transformed curve that stays in the ball.
* `norm_nearIdRemainder_le_local`, `norm_nearIdRemainder_sub_le_local`,
  `nearIdRemainder_periodic_local`, `nearIdRemainder_field_local` — the remainder field on the
  ball, with the constants of `Averaging.nearIdRemainder_field`.
* `transformed_solution_local` — **the theorem**: every solution in the inner ball has a unique
  transformed curve in the ball, and it satisfies `ẏ = εf̄(y) + ε²R(y, t)`.

Corrections.
None: an extension (the local version of `theorem/Averaging/NearIdentityInverse.lean`).
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology intervalIntegral MeasureTheory Metric
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ → E} {Df : E → ℝ → E →L[ℝ] E} {T ℓ M L₂ ρ : ℝ} {x₀ : E}

/-! ## Frozen fields -/

/-- A continuous `T`-periodic function of time bounded by `K`, read as a field that does not
depend on the state, has the hypotheses of `Averaging.kbm_first_order` with Lipschitz constant
`0`. -/
@[tmio T, powerlib_foundation] private theorem frozen_hyp {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ → F} {K : ℝ} (hT : 0 < T) (hg : Continuous g)
    (hper : ∀ s, g (s + T) = g s) (hb : ∀ s, ‖g s‖ ≤ K) :
    0 < T ∧ (0 : ℝ) ≤ 0 ∧ Continuous (Function.uncurry fun (_ : F) (s : ℝ) => g s) ∧
      (∀ (_ : F) t, g (t + T) = g t) ∧ (∀ (x y : F) t, ‖g t - g t‖ ≤ 0 * ‖x - y‖) ∧
      ∀ (_ : F) t, ‖g t‖ ≤ K :=
  ⟨hT, le_rfl, hg.comp continuous_snd, fun _ t => hper t, fun _ _ t => by simp, fun _ t => hb t⟩

/-- The generator of a difference of two frozen fields is the difference of the generators. -/
@[tmio T, powerlib_foundation] private theorem strobGen_frozen_sub {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {g₁ g₂ : ℝ → F}
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) (w : F) (t : ℝ) :
    strobGen (fun (_ : F) s => g₁ s - g₂ s) T w t =
      strobGen (fun (_ : F) s => g₁ s) T w t - strobGen (fun (_ : F) s => g₂ s) T w t := by
  simp only [strobGen, fieldAverage]
  rw [intervalIntegral.integral_sub (h₁.intervalIntegrable 0 T) (h₂.intervalIntegrable 0 T),
    ← intervalIntegral.integral_sub (f := fun s => g₁ s - T⁻¹ • ∫ s in (0 : ℝ)..T, g₁ s)
      (g := fun s => g₂ s - T⁻¹ • ∫ s in (0 : ℝ)..T, g₂ s)
      ((h₁.sub continuous_const).intervalIntegrable 0 t)
      ((h₂.sub continuous_const).intervalIntegrable 0 t)]
  congr 1
  funext s
  rw [smul_sub]
  abel

/-- The average of a difference of two frozen fields is the difference of the averages. -/
@[tmio T, powerlib_foundation] private theorem fieldAverage_frozen_sub {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {g₁ g₂ : ℝ → F}
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) (w : F) :
    fieldAverage (fun (_ : F) s => g₁ s - g₂ s) T w =
      fieldAverage (fun (_ : F) s => g₁ s) T w - fieldAverage (fun (_ : F) s => g₂ s) T w := by
  simp only [fieldAverage]
  rw [intervalIntegral.integral_sub (h₁.intervalIntegrable 0 T) (h₂.intervalIntegrable 0 T),
    smul_sub]

/-! ## The field on the ball -/

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[tmio T, powerlib_foundation] private theorem continuous_slice {G : Type*} [TopologicalSpace G]
    {g : E → ℝ → G} (hc : ContinuousOn (Function.uncurry g) (ball x₀ ρ ×ˢ univ)) {y : E}
    (hy : y ∈ ball x₀ ρ) : Continuous (g y) :=
  hc.comp_continuous (continuous_const.prodMk continuous_id) fun s => ⟨hy, mem_univ s⟩

omit [CompleteSpace E] in
/-- On the open ball the derivative is bounded by the Lipschitz constant: `‖Df(y, t)‖ ≤ ℓ`. -/
@[tmio T, powerlib_foundation] theorem norm_fderiv_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x) {y : E}
    (hy : y ∈ ball x₀ ρ) (t : ℝ) : ‖Df y t‖ ≤ ℓ := by
  refine (hD y hy t).le_of_lip' hf.2.1 ?_
  filter_upwards [isOpen_ball.mem_nhds hy] with x hx using hf.2.2.2.2.1 x hx y hy t

omit [CompleteSpace E] in
/-- On the open ball the derivative is `T`-periodic in time (uniqueness of derivatives). -/
@[tmio T, powerlib_foundation] private theorem fderiv_periodic_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x) {y : E}
    (hy : y ∈ ball x₀ ρ) (s : ℝ) : Df y (s + T) = Df y s := by
  have h := hD y hy (s + T)
  have e : (fun w => f w s) =ᶠ[𝓝 y] fun w => f w (s + T) := by
    filter_upwards [isOpen_ball.mem_nhds hy] with w hw using (hf.2.2.2.1 w hw s).symm
  exact (h.congr_of_eventuallyEq e).unique (hD y hy s)

omit [CompleteSpace E] in
/-- The frozen field `f(y, ·)` of a point of the ball. -/
@[tmio T, powerlib_foundation] private theorem frozen_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M) {y : E} (hy : y ∈ ball x₀ ρ) :
    0 < T ∧ (0 : ℝ) ≤ 0 ∧ Continuous (Function.uncurry fun (_ : E) (s : ℝ) => f y s) ∧
      (∀ (_ : E) t, f y (t + T) = f y t) ∧ (∀ (x z : E) t, ‖f y t - f y t‖ ≤ 0 * ‖x - z‖) ∧
      ∀ (_ : E) t, ‖f y t‖ ≤ M :=
  frozen_hyp hf.1 (continuous_slice hf.2.2.1 hy) (hf.2.2.2.1 y hy) (hf.2.2.2.2.2 y hy)

/-- **The generator is bounded on the ball**: `‖u(y, t)‖ ≤ 2MT` for `y` in the ball. -/
@[tmio T, powerlib_foundation] theorem norm_strobGen_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M) {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) :
    ‖strobGen f T y t‖ ≤ 2 * M * T :=
  norm_strobGen_le (f := fun (_ : E) s => f y s) (frozen_local hf hy) y t

/-- **The generator is `2ℓT`-Lipschitz on the ball.** -/
@[tmio T, powerlib_foundation] theorem norm_strobGen_sub_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    {y z : E} (hy : y ∈ ball x₀ ρ) (hz : z ∈ ball x₀ ρ) (t : ℝ) :
    ‖strobGen f T y t - strobGen f T z t‖ ≤ 2 * ℓ * T * ‖y - z‖ := by
  have cy := continuous_slice hf.2.2.1 hy
  have cz := continuous_slice hf.2.2.1 hz
  have h := norm_strobGen_le (f := fun (_ : E) s => f y s - f z s)
    (frozen_hyp hf.1 (cy.sub cz) (fun s => by rw [hf.2.2.2.1 y hy, hf.2.2.2.1 z hz])
      (fun s => hf.2.2.2.2.1 y hy z hz s)) y t
  rw [strobGen_frozen_sub cy cz] at h
  calc ‖strobGen f T y t - strobGen f T z t‖ ≤ 2 * (ℓ * ‖y - z‖) * T := h
    _ = 2 * ℓ * T * ‖y - z‖ := by ring

omit [CompleteSpace E] in
/-- The average of the field is bounded by `M` on the ball. -/
@[tmio T, powerlib_foundation] theorem norm_fieldAverage_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    {y : E} (hy : y ∈ ball x₀ ρ) : ‖fieldAverage f T y‖ ≤ M :=
  norm_fieldAverage_le (f := fun (_ : E) s => f y s) (frozen_local hf hy) y

/-- The average of the field is `ℓ`-Lipschitz on the ball. -/
@[tmio T, powerlib_foundation] theorem norm_fieldAverage_sub_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    {y z : E} (hy : y ∈ ball x₀ ρ) (hz : z ∈ ball x₀ ρ) :
    ‖fieldAverage f T y - fieldAverage f T z‖ ≤ ℓ * ‖y - z‖ := by
  have cy := continuous_slice hf.2.2.1 hy
  have cz := continuous_slice hf.2.2.1 hz
  have h := norm_fieldAverage_le (f := fun (_ : E) s => f y s - f z s)
    (frozen_hyp hf.1 (cy.sub cz) (fun s => by rw [hf.2.2.2.1 y hy, hf.2.2.2.1 z hz])
      (fun s => hf.2.2.2.2.1 y hy z hz s)) y
  rw [fieldAverage_frozen_sub cy cz] at h
  exact h

/-- The generator is `T`-periodic in time on the ball. -/
@[tmio T, powerlib_foundation] theorem strobGen_periodic_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) : strobGen f T y (t + T) = strobGen f T y t :=
  strobGen_periodic (f := fun (_ : E) s => f y s) (frozen_local hf hy) y t

omit [CompleteSpace E] in
/-- The generator is `2M`-Lipschitz in time on the ball. -/
@[tmio T, powerlib_foundation] theorem norm_strobGen_time_sub_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    {y : E} (hy : y ∈ ball x₀ ρ) (s t : ℝ) :
    ‖strobGen f T y s - strobGen f T y t‖ ≤ 2 * M * |s - t| :=
  norm_strobGen_time_sub_le (f := fun (_ : E) s => f y s) (frozen_local hf hy) y s t

/-- The time derivative of the generator on the ball is the oscillating part `f(y, t) − f̄(y)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_strobGen_time_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) :
    HasDerivAt (strobGen f T y) (f y t - fieldAverage f T y) t :=
  hasDerivAt_strobGen_time (f := fun (_ : E) s => f y s) (frozen_local hf hy) y t

@[tmio T, powerlib_foundation] private theorem strobGen_eq_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) :
    strobGen f T y t = (∫ s in (0 : ℝ)..t, f y s) - (t / T) • ∫ s in (0 : ℝ)..T, f y s := by
  have h := strobGen_eq (f := fun (_ : E) s => f y s) (frozen_local hf hy) y t
  rw [show strobGen f T y t = strobGen (fun (_ : E) s => f y s) T y t from rfl, h, fieldAverage,
    smul_smul, div_eq_mul_inv]

/-! ## The state derivative of the generator on the ball -/

omit [CompleteSpace E] in
/-- The frozen derivative `Df(y, ·)` of a point of the ball. -/
@[tmio T, powerlib_foundation] private theorem frozenD_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ)) {y : E} (hy : y ∈ ball x₀ ρ) :
    0 < T ∧ (0 : ℝ) ≤ 0 ∧ Continuous (Function.uncurry fun (_ : E →L[ℝ] E) (s : ℝ) => Df y s) ∧
      (∀ (_ : E →L[ℝ] E) t, Df y (t + T) = Df y t) ∧
      (∀ (x z : E →L[ℝ] E) t, ‖Df y t - Df y t‖ ≤ 0 * ‖x - z‖) ∧
      ∀ (_ : E →L[ℝ] E) t, ‖Df y t‖ ≤ ℓ :=
  frozen_hyp hf.1 (continuous_slice hDc hy) (fderiv_periodic_local hf hD hy)
    (norm_fderiv_le_local hf hD hy)

@[tmio T, powerlib_foundation] private theorem strobGenD_eq_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) :
    strobGenD Df T y t = strobGen (fun (_ : E →L[ℝ] E) s => Df y s) T 0 t := by
  rw [strobGen_eq (frozenD_local hf hD hDc hy) 0 t, strobGenD, fieldAverage, smul_smul,
    div_eq_mul_inv]

/-- **`‖D_y u(y, t)‖ ≤ 2ℓT` on the ball.** -/
@[tmio T, powerlib_foundation] theorem norm_strobGenD_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) : ‖strobGenD Df T y t‖ ≤ 2 * ℓ * T := by
  rw [strobGenD_eq_local hf hD hDc hy]
  exact norm_strobGen_le (frozenD_local hf hD hDc hy) 0 t

/-- The state derivative of the generator is `T`-periodic in time on the ball. -/
@[tmio T, powerlib_foundation] theorem strobGenD_periodic_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) :
    strobGenD Df T y (t + T) = strobGenD Df T y t := by
  rw [strobGenD_eq_local hf hD hDc hy, strobGenD_eq_local hf hD hDc hy]
  exact strobGen_periodic (frozenD_local hf hD hDc hy) 0 t

/-- **`D_y u` is `2L₂T`-Lipschitz on the ball** when `Df(·, t)` is `L₂`-Lipschitz there. -/
@[tmio T, powerlib_foundation] theorem norm_strobGenD_sub_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    (hDl : ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    {y z : E} (hy : y ∈ ball x₀ ρ) (hz : z ∈ ball x₀ ρ) (t : ℝ) :
    ‖strobGenD Df T y t - strobGenD Df T z t‖ ≤ 2 * L₂ * T * ‖y - z‖ := by
  have cy := continuous_slice hDc hy
  have cz := continuous_slice hDc hz
  have h := norm_strobGen_le (f := fun (_ : E →L[ℝ] E) s => Df y s - Df z s)
    (frozen_hyp hf.1 (cy.sub cz) (fun s => by
      rw [fderiv_periodic_local hf hD hy, fderiv_periodic_local hf hD hz])
      (fun s => hDl y hy z hz s)) 0 t
  rw [strobGen_frozen_sub cy cz] at h
  rw [strobGenD_eq_local hf hD hDc hy, strobGenD_eq_local hf hD hDc hz]
  calc _ ≤ 2 * (L₂ * ‖y - z‖) * T := h
    _ = 2 * L₂ * T * ‖y - z‖ := by ring

/-- **Differentiation under the integral sign on the ball**: at every point of the open ball the
generator is differentiable in the state with derivative `strobGenD`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_strobGen_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) :
    HasFDerivAt (fun w => strobGen f T w t) (strobGenD Df T y t) y := by
  have hb : ball x₀ ρ ∈ 𝓝 y := isOpen_ball.mem_nhds hy
  have hprim : ∀ b : ℝ, HasFDerivAt (fun w => ∫ s in (0 : ℝ)..b, f w s)
      (∫ s in (0 : ℝ)..b, Df y s) y := by
    intro b
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (bound := fun _ => ℓ) (s := ball x₀ ρ) hb ?_
      ((continuous_slice hf.2.2.1 hy).intervalIntegrable _ _)
      (continuous_slice hDc hy).aestronglyMeasurable ?_ intervalIntegrable_const ?_
    · filter_upwards [hb] with w hw using (continuous_slice hf.2.2.1 hw).aestronglyMeasurable
    · exact Eventually.of_forall fun s _ w hw => norm_fderiv_le_local hf hD hw s
    · exact Eventually.of_forall fun s _ w hw => hD w hw s
  have e : (fun w => (∫ s in (0 : ℝ)..t, f w s) - (t / T) • ∫ s in (0 : ℝ)..T, f w s)
      =ᶠ[𝓝 y] fun w => strobGen f T w t := by
    filter_upwards [hb] with w hw using (strobGen_eq_local hf hw t).symm
  exact ((hprim t).sub ((hprim T).const_smul (t / T))).congr_of_eventuallyEq e.symm

omit [CompleteSpace E] in
/-- The state derivative of the generator is jointly continuous at every point of the ball
(the cut-off `Df(π(·), ·)` with the radial retraction `π` onto a smaller closed ball,
`Map.CenterManifold.ballRetract`, is jointly continuous on all of `E × ℝ`, and
`Averaging.continuous_uncurry_strobGenD` applies to it). -/
@[tmio T, powerlib_foundation] theorem continuousAt_uncurry_strobGenD_local
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) :
    ContinuousAt (Function.uncurry (strobGenD Df T)) (y, t) := by
  have hy0 : dist y x₀ < ρ := hy
  set ρ' := (dist y x₀ + ρ) / 2 with hρ'
  have hρ'0 : 0 ≤ ρ' := by rw [hρ']; linarith [dist_nonneg (x := y) (y := x₀)]
  have hρ'ρ : ρ' < ρ := by rw [hρ']; linarith
  have hyρ' : y ∈ ball x₀ ρ' := by rw [mem_ball, hρ']; linarith
  set r : E → E := fun w => x₀ + Map.CenterManifold.ballRetract ρ' (w - x₀) with hr
  have hrc : Continuous r := continuous_const.add
    ((Map.CenterManifold.lipschitzWith_ballRetract hρ'0).continuous.comp
      (continuous_id.sub continuous_const))
  have hrb : ∀ w, r w ∈ ball x₀ ρ := fun w => by
    rw [mem_ball, dist_eq_norm, hr]
    simp only [add_sub_cancel_left]
    exact (Map.CenterManifold.norm_ballRetract_le hρ'0 _).trans_lt hρ'ρ
  have hreq : ∀ w ∈ ball x₀ ρ', r w = w := fun w hw => by
    rw [mem_ball, dist_eq_norm] at hw
    rw [hr]
    simp only [Map.CenterManifold.ballRetract_of_norm_le hw.le, add_sub_cancel]
  have hc' : Continuous (Function.uncurry fun w s => Df (r w) s) :=
    hDc.comp_continuous ((hrc.comp continuous_fst).prodMk continuous_snd)
      fun p => ⟨hrb p.1, mem_univ _⟩
  have hcont := continuous_uncurry_strobGenD (T := T) hc'
  have heq : Function.uncurry (strobGenD (fun w s => Df (r w) s) T) =ᶠ[𝓝 (y, t)]
      Function.uncurry (strobGenD Df T) := by
    filter_upwards [(isOpen_ball.prod isOpen_univ).mem_nhds
      (show (y, t) ∈ ball x₀ ρ' ×ˢ (univ : Set ℝ) from ⟨hyρ', mem_univ t⟩)] with p hp
    simp only [Function.uncurry, strobGenD, hreq p.1 hp.1]
  exact hcont.continuousAt.congr heq

/-- **The generator is jointly strictly differentiable at every point of the ball**, with the
derivative `(v, τ) ↦ D_y u(y, t) v + τ (f(y, t) − f̄(y))` (Mathlib
`hasStrictFDerivAt_uncurry_coprod`). -/
@[tmio T, powerlib_foundation] theorem hasStrictFDerivAt_uncurry_strobGen_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) :
    HasStrictFDerivAt (Function.uncurry (strobGen f T))
      ((strobGenD Df T y t).coprod
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f y t - fieldAverage f T y))) (y, t) := by
  set f₂ : E → ℝ → ℝ →L[ℝ] E := fun x s =>
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f x s - fieldAverage f T x) with hf₂
  have hU : ball x₀ ρ ×ˢ (univ : Set ℝ) ∈ 𝓝 (y, t) :=
    (isOpen_ball.prod isOpen_univ).mem_nhds ⟨hy, mem_univ t⟩
  have hlip : LipschitzOnWith (Real.toNNReal ℓ) (fieldAverage f T) (ball x₀ ρ) :=
    LipschitzOnWith.of_dist_le_mul fun a ha b hb => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hf.2.1]
      exact norm_fieldAverage_sub_le_local hf ha hb
  have hfa : ContinuousAt (fieldAverage f T) y :=
    hlip.continuousOn.continuousAt (isOpen_ball.mem_nhds hy)
  have hcf : ContinuousAt (fun p : E × ℝ => f p.1 p.2 - fieldAverage f T p.1) (y, t) :=
    (hf.2.2.1.continuousAt hU).sub
      (ContinuousAt.comp (g := fieldAverage f T) (f := Prod.fst) hfa continuousAt_fst)
  have hc₂ : ContinuousAt (Function.uncurry f₂) (y, t) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp hcf
  exact hasStrictFDerivAt_uncurry_coprod (f := strobGen f T) (f₁ := strobGenD Df T)
    (f₂ := f₂) (u := (y, t))
    (by filter_upwards [hU] with v hv using hasFDerivAt_strobGen_local hf hD hDc hv.1 v.2)
    (by filter_upwards [hU] with v hv using
      (hasDerivAt_strobGen_time_local hf hv.1 v.2).hasFDerivAt)
    (continuousAt_uncurry_strobGenD_local hDc hy t) hc₂

/-- **`I + ε D_y u` is invertible on the ball** for `0 ≤ ε`, `2εℓT < 1`, and
`‖(I + ε D_y u)⁻¹‖ ≤ 1/(1 − 2εℓT)` (Neumann series). -/
@[tmio T, powerlib_foundation] theorem isUnit_one_add_strobGenD_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    {ε : ℝ} (hε : 0 ≤ ε) (hεℓ : 2 * ε * ℓ * T < 1) {y : E} (hy : y ∈ ball x₀ ρ) (t : ℝ) :
    IsUnit (1 + ε • strobGenD Df T y t) ∧
      ‖Ring.inverse (1 + ε • strobGenD Df T y t)‖ ≤ (1 - 2 * ε * ℓ * T)⁻¹ := by
  set B := ε • strobGenD Df T y t with hBdef
  have hB : ‖B‖ ≤ 2 * ε * ℓ * T := by
    rw [hBdef, norm_smul, Real.norm_of_nonneg hε]
    have := mul_le_mul_of_nonneg_left (norm_strobGenD_le_local hf hD hDc hy t) hε
    linarith
  have hu : IsUnit (1 + B) := by
    have h : ‖-B‖ < 1 := by rw [norm_neg]; linarith
    have hu := (Units.oneSub _ h).isUnit
    rwa [Units.val_oneSub, sub_neg_eq_add] at hu
  refine ⟨hu, ?_⟩
  have hq' : 0 < 1 - 2 * ε * ℓ * T := by linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hq'.le) fun w => ?_
  have hv : Ring.inverse (1 + B) w + B (Ring.inverse (1 + B) w) = w := by
    have h := congrArg (fun L : E →L[ℝ] E => L w) (Ring.mul_inverse_cancel _ hu)
    simpa using h
  have h1 : ‖Ring.inverse (1 + B) w‖ ≤ ‖w‖ + 2 * ε * ℓ * T * ‖Ring.inverse (1 + B) w‖ := by
    calc ‖Ring.inverse (1 + B) w‖ = ‖w - B (Ring.inverse (1 + B) w)‖ :=
          congrArg norm (eq_sub_of_add_eq hv)
      _ ≤ ‖w‖ + ‖B (Ring.inverse (1 + B) w)‖ := norm_sub_le _ _
      _ ≤ ‖w‖ + 2 * ε * ℓ * T * ‖Ring.inverse (1 + B) w‖ := by
          gcongr
          exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  rw [inv_mul_eq_div, le_div_iff₀ hq']
  linarith

/-! ## The near-identity map on the ball -/

/-- **The near-identity map is bi-Lipschitz on the ball**: for `y, z` in the ball and `ε ≥ 0`,
`(1 − 2εℓT)‖y − z‖ ≤ ‖(y + εu(y, t)) − (z + εu(z, t))‖ ≤ (1 + 2εℓT)‖y − z‖`. -/
@[tmio T, powerlib_foundation] theorem norm_nearIdentity_sub_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    {ε : ℝ} (hε : 0 ≤ ε) {y z : E} (hy : y ∈ ball x₀ ρ) (hz : z ∈ ball x₀ ρ) (t : ℝ) :
    (1 - 2 * ε * ℓ * T) * ‖y - z‖ ≤
        ‖(y + ε • strobGen f T y t) - (z + ε • strobGen f T z t)‖ ∧
      ‖(y + ε • strobGen f T y t) - (z + ε • strobGen f T z t)‖ ≤
        (1 + 2 * ε * ℓ * T) * ‖y - z‖ := by
  have h1 : ‖ε • (strobGen f T y t - strobGen f T z t)‖ ≤ 2 * ε * ℓ * T * ‖y - z‖ := by
    rw [norm_smul, Real.norm_of_nonneg hε]
    calc ε * ‖strobGen f T y t - strobGen f T z t‖ ≤ ε * (2 * ℓ * T * ‖y - z‖) :=
          mul_le_mul_of_nonneg_left (norm_strobGen_sub_le_local hf hy hz t) hε
      _ = 2 * ε * ℓ * T * ‖y - z‖ := by ring
  have e : (y + ε • strobGen f T y t) - (z + ε • strobGen f T z t) =
      (y - z) + ε • (strobGen f T y t - strobGen f T z t) := by rw [smul_sub]; abel
  rw [e]
  constructor
  · have h3 : ‖y - z‖ ≤ ‖(y - z) + ε • (strobGen f T y t - strobGen f T z t)‖ +
        2 * ε * ℓ * T * ‖y - z‖ := by
      have h := norm_sub_le ((y - z) + ε • (strobGen f T y t - strobGen f T z t))
        (ε • (strobGen f T y t - strobGen f T z t))
      rw [add_sub_cancel_right] at h
      linarith
    linarith
  · exact (norm_add_le _ _).trans (by linarith)

/-- **The near-identity map is a bijection between nested balls.** Let `0 ≤ ε`, `2εℓT < 1` and
radii `ρ₂ + 2εMT ≤ ρ₁ < ρ`. At every time `t`, every `x` with `‖x − x₀‖ ≤ ρ₂` has exactly one
preimage `y` with `‖y − x₀‖ ≤ ρ₁`, `y + εu(y, t) = x` (Banach's fixed point theorem for the
contraction `y ↦ x − εu(y, t)` of the closed ball of radius `ρ₁`, Mathlib
`ContractingWith.efixedPoint'`). So `y ↦ y + εu(y, t)` maps the set
`D = {‖y − x₀‖ ≤ ρ₁, ‖y + εu(y, t) − x₀‖ ≤ ρ₂}` bijectively onto the closed ball of radius `ρ₂`,
and `D` lies between the closed balls of radii `ρ₂ − 2εMT` and `ρ₂ + 2εMT`; on the open ball of
radius `ρ` the map is bi-Lipschitz with constants `1 ∓ 2εℓT` (`norm_nearIdentity_sub_local`). -/
@[tmio T, powerlib_foundation] theorem nearIdentity_bijOn_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) {ε : ℝ} (hε : 0 ≤ ε) (hεℓ : 2 * ε * ℓ * T < 1) {ρ₁ ρ₂ : ℝ} (hρ₁ : ρ₁ < ρ)
    (hρ₂ : ρ₂ + 2 * ε * M * T ≤ ρ₁) (t : ℝ) :
    (∀ x ∈ closedBall x₀ ρ₂, ∃! y, y ∈ closedBall x₀ ρ₁ ∧ y + ε • strobGen f T y t = x) ∧
      BijOn (fun y => y + ε • strobGen f T y t)
        (closedBall x₀ ρ₁ ∩ (fun y => y + ε • strobGen f T y t) ⁻¹' closedBall x₀ ρ₂)
        (closedBall x₀ ρ₂) ∧
      closedBall x₀ (ρ₂ - 2 * ε * M * T) ⊆
        closedBall x₀ ρ₁ ∩ (fun y => y + ε • strobGen f T y t) ⁻¹' closedBall x₀ ρ₂ ∧
      closedBall x₀ ρ₁ ∩ (fun y => y + ε • strobGen f T y t) ⁻¹' closedBall x₀ ρ₂ ⊆
        closedBall x₀ (ρ₂ + 2 * ε * M * T) := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 x₀ (mem_ball_self hρ) 0)
  have hεM : 0 ≤ 2 * ε * M * T := by positivity
  have hsub : closedBall x₀ ρ₁ ⊆ ball x₀ ρ := closedBall_subset_ball hρ₁
  have hu : ∀ y ∈ ball x₀ ρ, ‖ε • strobGen f T y t‖ ≤ 2 * ε * M * T := fun y hy => by
    rw [norm_smul, Real.norm_of_nonneg hε]
    have := mul_le_mul_of_nonneg_left (norm_strobGen_le_local hf hy t) hε
    linarith
  -- uniqueness on the closed ball of radius `ρ₁`
  have huniq : ∀ y₁ ∈ closedBall x₀ ρ₁, ∀ y₂ ∈ closedBall x₀ ρ₁,
      y₁ + ε • strobGen f T y₁ t = y₂ + ε • strobGen f T y₂ t → y₁ = y₂ := by
    intro y₁ h₁ y₂ h₂ he
    have h := (norm_nearIdentity_sub_local hf hε (hsub h₁) (hsub h₂) t).1
    rw [he, sub_self, norm_zero] at h
    have hq : 0 < 1 - 2 * ε * ℓ * T := by linarith
    have : ‖y₁ - y₂‖ ≤ 0 := by nlinarith [norm_nonneg (y₁ - y₂)]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  -- existence: the contraction `y ↦ x − εu(y, t)` of the closed ball of radius `ρ₁`
  have hex : ∀ x ∈ closedBall x₀ ρ₂, ∃ y ∈ closedBall x₀ ρ₁, y + ε • strobGen f T y t = x := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    set φ : E → E := fun y => x - ε • strobGen f T y t with hφ
    have hmaps : MapsTo φ (closedBall x₀ ρ₁) (closedBall x₀ ρ₁) := fun y hy => by
      rw [mem_closedBall, dist_eq_norm, hφ]
      have e : x - ε • strobGen f T y t - x₀ = (x - x₀) - ε • strobGen f T y t := by abel
      rw [e]
      exact (norm_sub_le _ _).trans (by linarith [hu y (hsub hy)])
    have hK : 0 ≤ 2 * ε * ℓ * T := by positivity
    have hc : ContractingWith (Real.toNNReal (2 * ε * ℓ * T))
        (hmaps.restrict φ (closedBall x₀ ρ₁) (closedBall x₀ ρ₁)) := by
      refine ⟨Real.toNNReal_lt_one.mpr hεℓ, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
      rw [Subtype.dist_eq, Subtype.dist_eq, Real.coe_toNNReal _ hK]
      simp only [MapsTo.val_restrict_apply, hφ]
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_left, ← smul_sub, norm_smul,
        Real.norm_of_nonneg hε]
      calc ε * ‖strobGen f T b t - strobGen f T a t‖ ≤ ε * (2 * ℓ * T * ‖(b : E) - (a : E)‖) :=
            mul_le_mul_of_nonneg_left (norm_strobGen_sub_le_local hf (hsub b.2) (hsub a.2) t) hε
        _ = 2 * ε * ℓ * T * ‖(a : E) - (b : E)‖ := by rw [norm_sub_rev]; ring
    have hx₀ : x₀ ∈ closedBall x₀ ρ₁ := mem_closedBall_self (by linarith [norm_nonneg (x - x₀)])
    set y₀ := ContractingWith.efixedPoint' φ isClosed_closedBall.isComplete hmaps hc x₀ hx₀
      (edist_ne_top _ _) with hy₀
    have hy : y₀ ∈ closedBall x₀ ρ₁ :=
      ContractingWith.efixedPoint_mem' isClosed_closedBall.isComplete hmaps hc hx₀
        (edist_ne_top _ _)
    have hfix : x - ε • strobGen f T y₀ t = y₀ :=
      ContractingWith.efixedPoint_isFixedPt' isClosed_closedBall.isComplete hmaps hc hx₀
        (edist_ne_top _ _)
    refine ⟨y₀, hy, ?_⟩
    have h := congrArg (· + ε • strobGen f T y₀ t) hfix
    simp only [sub_add_cancel] at h
    exact h.symm
  refine ⟨fun x hx => ?_, ⟨fun y hy => hy.2, fun y₁ h₁ y₂ h₂ he => huniq y₁ h₁.1 y₂ h₂.1 he,
    fun x hx => ?_⟩, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hex x hx
    exact ⟨y, ⟨hy, hyx⟩, fun z hz => huniq z hz.1 y hy (hz.2.trans hyx.symm)⟩
  · obtain ⟨y, hy, hyx⟩ := hex x hx
    refine ⟨y, ⟨hy, ?_⟩, hyx⟩
    show y + ε • strobGen f T y t ∈ closedBall x₀ ρ₂
    rw [hyx]; exact hx
  · rw [mem_closedBall, dist_eq_norm] at hy
    have hy₁ : y ∈ closedBall x₀ ρ₁ := by
      rw [mem_closedBall, dist_eq_norm]; linarith
    refine ⟨hy₁, ?_⟩
    show y + ε • strobGen f T y t ∈ closedBall x₀ ρ₂
    rw [mem_closedBall, dist_eq_norm]
    have e : y + ε • strobGen f T y t - x₀ = (y - x₀) + ε • strobGen f T y t := by abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [hu y (hsub hy₁)])
  · obtain ⟨hy₁, hy₂⟩ := hy
    have hy₂' : ‖y + ε • strobGen f T y t - x₀‖ ≤ ρ₂ := by
      have := hy₂; rwa [mem_preimage, mem_closedBall, dist_eq_norm] at this
    rw [mem_closedBall, dist_eq_norm]
    have e : y - x₀ = (y + ε • strobGen f T y t - x₀) - ε • strobGen f T y t := by abel
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith [hu y (hsub hy₁)])

/-! ## The transformed curve of a solution that stays in the ball -/

/-- **The transformed curve moves at most as fast as the curve, on the ball**: if
`x(s) = y(s) + εu(y(s), s)`, `x(t) = y(t) + εu(y(t), t)` with `y(s)`, `y(t)` in the ball and
`ε ≥ 0`, then `(1 − 2εℓT)‖y(s) − y(t)‖ ≤ ‖x(s) − x(t)‖ + 2εM|s − t|`. -/
@[tmio T, powerlib_foundation] theorem norm_transformedCurve_sub_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    {ε : ℝ} (hε : 0 ≤ ε) {x y : ℝ → E} {s t : ℝ} (hys : y s ∈ ball x₀ ρ) (hyt : y t ∈ ball x₀ ρ)
    (hxs : x s = y s + ε • strobGen f T (y s) s) (hxt : x t = y t + ε • strobGen f T (y t) t) :
    (1 - 2 * ε * ℓ * T) * ‖y s - y t‖ ≤ ‖x s - x t‖ + 2 * ε * M * |s - t| := by
  have h1 := (norm_nearIdentity_sub_local hf hε hys hyt s).1
  have h2 : (y s + ε • strobGen f T (y s) s) - (y t + ε • strobGen f T (y t) s) =
      (x s - x t) - ε • (strobGen f T (y t) s - strobGen f T (y t) t) := by
    rw [hxs, hxt, smul_sub]; abel
  have h3 : ‖ε • (strobGen f T (y t) s - strobGen f T (y t) t)‖ ≤ 2 * ε * M * |s - t| := by
    rw [norm_smul, Real.norm_of_nonneg hε]
    calc ε * ‖strobGen f T (y t) s - strobGen f T (y t) t‖ ≤ ε * (2 * M * |s - t|) :=
          mul_le_mul_of_nonneg_left (norm_strobGen_time_sub_le_local hf hyt s t) hε
      _ = 2 * ε * M * |s - t| := by ring
  rw [h2] at h1
  exact h1.trans ((norm_sub_le _ _).trans (add_le_add le_rfl h3))

/-- **The transformed curve is differentiable where the curve is, on the ball** (the easy half of
the inverse function theorem, Mathlib `HasFDerivAt.of_comp_of_leftInverse`): if near `t` the
curve `y` stays in the closed ball of radius `ρ₁ < ρ` and `x(s) = y(s) + εu(y(s), s)`, `0 ≤ ε`,
`2εℓT < 1`, and `x` has the derivative `x'` at `t`, then `y` has the derivative
`(I + εD_y u(y(t), t))⁻¹(x' − ε(f(y(t), t) − f̄(y(t))))` at `t`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_transformedCurve_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    {ε : ℝ} (hε : 0 ≤ ε) (hεℓ : 2 * ε * ℓ * T < 1) {ρ₁ : ℝ} (hρ₁ : ρ₁ < ρ) {x y : ℝ → E}
    {t : ℝ} (hxy : ∀ᶠ s in 𝓝 t, y s ∈ closedBall x₀ ρ₁ ∧ x s = y s + ε • strobGen f T (y s) s)
    {x' : E} (hx : HasDerivAt x x' t) :
    HasDerivAt y (Ring.inverse (1 + ε • strobGenD Df T (y t) t)
      (x' - ε • (f (y t) t - fieldAverage f T (y t)))) t := by
  have hq : 0 < 1 - 2 * ε * ℓ * T := by linarith
  have hsub : closedBall x₀ ρ₁ ⊆ ball x₀ ρ := closedBall_subset_ball hρ₁
  have hxyt := hxy.self_of_nhds
  have hyt : y t ∈ ball x₀ ρ := hsub hxyt.1
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
      (squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ h3)
    filter_upwards [hxy] with s hs
    rw [le_div_iff₀ hq, mul_comm]
    exact norm_transformedCurve_sub_le_local hf hε (hsub hs.1) hyt hs.2 hxyt.2
  set D := strobGenD Df T (y t) t with hDdef
  set w : E := f (y t) t - fieldAverage f T (y t) with hw
  have hu : IsUnit (1 + ε • D) := (isUnit_one_add_strobGenD_local hf hD hDc hε hεℓ hyt t).1
  have hS := hasStrictFDerivAt_uncurry_strobGen_local hf hD hDc hyt t
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
      =ᶠ[𝓝 t] fun s => (x s, s) := by
    filter_upwards [hxy] with s hs
    simp only [Function.comp_apply, hs.2]
  have hg := HasFDerivAt.of_comp_of_leftInverse (g := fun s => (y s, s))
    (hyc.prodMk continuousAt_id) hΨ hh hcomp hinv
  have hy₀ := (hasFDerivAt_fst.comp t hg).hasDerivAt
  have hy : HasDerivAt y _ t := hy₀
  refine hy.congr_deriv ?_
  simp only [hΦ, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', sub_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, ContinuousLinearMap.coe_id', id, one_smul]

/-! ## The remainder field on the ball -/

/-- The numerator of the remainder is bounded by `4ℓMT` where `y` and `y + εu(y, t)` lie in the
ball. -/
@[tmio T, powerlib_foundation] private theorem norm_remainder_num_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    {ε : ℝ} (hε : 0 < ε) {y : E} (hy : y ∈ ball x₀ ρ) {t : ℝ}
    (hyu : y + ε • strobGen f T y t ∈ ball x₀ ρ) :
    ‖ε⁻¹ • (f (y + ε • strobGen f T y t) t - f y t) - strobGenD Df T y t (fieldAverage f T y)‖ ≤
      4 * ℓ * M * T := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 y hy 0)
  have h1 : ‖ε⁻¹ • (f (y + ε • strobGen f T y t) t - f y t)‖ ≤ 2 * ℓ * M * T := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    have h := hf.2.2.2.2.1 _ hyu y hy t
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le] at h
    have hu := norm_strobGen_le_local hf hy t
    calc ε⁻¹ * ‖f (y + ε • strobGen f T y t) t - f y t‖ ≤
          ε⁻¹ * (ℓ * (ε * ‖strobGen f T y t‖)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = ℓ * ‖strobGen f T y t‖ := by field_simp
      _ ≤ ℓ * (2 * M * T) := mul_le_mul_of_nonneg_left hu hℓ
      _ = 2 * ℓ * M * T := by ring
  have h2 : ‖strobGenD Df T y t (fieldAverage f T y)‖ ≤ 2 * ℓ * M * T := by
    calc ‖strobGenD Df T y t (fieldAverage f T y)‖ ≤
          ‖strobGenD Df T y t‖ * ‖fieldAverage f T y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (2 * ℓ * T) * M := mul_le_mul (norm_strobGenD_le_local hf hD hDc hy t)
          (norm_fieldAverage_le_local hf hy) (norm_nonneg _) (by positivity)
      _ = 2 * ℓ * M * T := by ring
  exact (norm_sub_le _ _).trans (by linarith)

/-- **The remainder field is bounded on the ball**: `‖R(y, t)‖ ≤ 4ℓMT/(1 − 2εℓT)` wherever `y`
and `y + εu(y, t)` lie in the ball (`0 < ε`, `2εℓT < 1`); the constant of
`Averaging.norm_nearIdRemainder_le`. -/
@[tmio T, powerlib_foundation] theorem norm_nearIdRemainder_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    {ε : ℝ} (hε : 0 < ε) (hεℓ : 2 * ε * ℓ * T < 1) {y : E} (hy : y ∈ ball x₀ ρ) {t : ℝ}
    (hyu : y + ε • strobGen f T y t ∈ ball x₀ ρ) :
    ‖nearIdRemainder f Df T ε y t‖ ≤ 4 * ℓ * M * T / (1 - 2 * ε * ℓ * T) := by
  obtain ⟨-, hinv⟩ := isUnit_one_add_strobGenD_local hf hD hDc hε.le hεℓ hy t
  have hN := norm_remainder_num_le_local hf hD hDc hε hy hyu
  calc ‖nearIdRemainder f Df T ε y t‖ ≤ ‖Ring.inverse (1 + ε • strobGenD Df T y t)‖ *
        ‖ε⁻¹ • (f (y + ε • strobGen f T y t) t - f y t) -
          strobGenD Df T y t (fieldAverage f T y)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (1 - 2 * ε * ℓ * T)⁻¹ * (4 * ℓ * M * T) :=
        mul_le_mul hinv hN (norm_nonneg _) (inv_nonneg.mpr (by linarith))
    _ = 4 * ℓ * M * T / (1 - 2 * ε * ℓ * T) := by rw [inv_mul_eq_div]

omit [CompleteSpace E] in
/-- Second differences of a field with Lipschitz derivative on the (convex) ball. -/
@[tmio T, powerlib_foundation] private theorem second_diff_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hL₂ : 0 ≤ L₂)
    (hDl : ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    {a b c d : E} (ha : a ∈ ball x₀ ρ) (hb : b ∈ ball x₀ ρ) (hc : c ∈ ball x₀ ρ)
    (hd : d ∈ ball x₀ ρ) {m : ℝ} (hac : ‖a - c‖ ≤ m) (hbd : ‖b - d‖ ≤ m) (t : ℝ) :
    ‖(f a t - f b t) - (f c t - f d t)‖ ≤ L₂ * m * ‖a - b‖ + ℓ * ‖(a - b) - (c - d)‖ := by
  set p : ℝ → E := fun θ => b + θ • (a - b) with hp
  set q : ℝ → E := fun θ => d + θ • (c - d) with hq
  have hpm : ∀ θ ∈ Icc (0 : ℝ) 1, p θ ∈ ball x₀ ρ := fun θ hθ =>
    (convex_ball x₀ ρ).add_smul_sub_mem hb ha hθ
  have hqm : ∀ θ ∈ Icc (0 : ℝ) 1, q θ ∈ ball x₀ ρ := fun θ hθ =>
    (convex_ball x₀ ρ).add_smul_sub_mem hd hc hθ
  have hseg : ∀ (u v : E) (θ : ℝ), HasDerivAt (fun θ : ℝ => v + θ • (u - v)) (u - v) θ :=
    fun u v θ => by
      have h := ((hasDerivAt_id θ).smul_const (u - v)).const_add v
      simpa using h
  have hderiv : ∀ θ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun θ => f (p θ) t - f (q θ) t)
      (Df (p θ) t (a - b) - Df (q θ) t (c - d)) (Icc 0 1) θ := by
    intro θ hθ
    have h1 := (hD (p θ) (hpm θ hθ) t).comp_hasDerivAt θ (hseg a b θ)
    have h2 := (hD (q θ) (hqm θ hθ) t).comp_hasDerivAt θ (hseg c d θ)
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ θ ∈ Ico (0 : ℝ) 1, ‖Df (p θ) t (a - b) - Df (q θ) t (c - d)‖ ≤
      L₂ * m * ‖a - b‖ + ℓ * ‖(a - b) - (c - d)‖ := by
    intro θ hθ
    have hθ' := Ico_subset_Icc_self hθ
    have hpq : ‖p θ - q θ‖ ≤ m := by
      have e : p θ - q θ = (1 - θ) • (b - d) + θ • (a - c) := by
        simp only [hp, hq, sub_smul, one_smul, smul_sub]; abel
      rw [e]
      calc ‖(1 - θ) • (b - d) + θ • (a - c)‖ ≤ (1 - θ) * ‖b - d‖ + θ * ‖a - c‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hθ'.2]),
              Real.norm_of_nonneg hθ'.1]
        _ ≤ (1 - θ) * m + θ * m := by
            gcongr
            · linarith [hθ'.2]
            · exact hθ'.1
        _ = m := by ring
    have hDq : ‖Df (q θ) t‖ ≤ ℓ := norm_fderiv_le_local hf hD (hqm θ hθ') t
    have e : Df (p θ) t (a - b) - Df (q θ) t (c - d) =
        (Df (p θ) t - Df (q θ) t) (a - b) + Df (q θ) t ((a - b) - (c - d)) := by
      simp only [sub_apply, map_sub]; abel
    rw [e]
    calc ‖(Df (p θ) t - Df (q θ) t) (a - b) + Df (q θ) t ((a - b) - (c - d))‖
        ≤ ‖Df (p θ) t - Df (q θ) t‖ * ‖a - b‖ + ‖Df (q θ) t‖ * ‖(a - b) - (c - d)‖ :=
          (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.le_opNorm _ _)
            (ContinuousLinearMap.le_opNorm _ _))
      _ ≤ (L₂ * ‖p θ - q θ‖) * ‖a - b‖ + ℓ * ‖(a - b) - (c - d)‖ := by
          gcongr
          exact hDl _ (hpm θ hθ') _ (hqm θ hθ') t
      _ ≤ L₂ * m * ‖a - b‖ + ℓ * ‖(a - b) - (c - d)‖ := by gcongr
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  have e : (f (p 1) t - f (q 1) t) - (f (p 0) t - f (q 0) t) =
      (f a t - f b t) - (f c t - f d t) := by
    simp only [hp, hq, one_smul, zero_smul, add_zero, add_sub_cancel]; abel
  rw [e] at h
  exact h

/-- **The remainder field is Lipschitz on the ball.** If moreover `Df(·, t)` is `L₂`-Lipschitz on
the ball, then for `0 < ε`, `2εℓT < 1` and `y`, `z`, `y + εu(y, t)`, `z + εu(z, t)` in the ball:
`‖R(y, t) − R(z, t)‖ ≤ (4T(L₂M(1 + εℓT) + ℓ²)/(1 − 2εℓT) + 8εℓL₂MT²/(1 − 2εℓT)²) ‖y − z‖`, the
constant of `Averaging.norm_nearIdRemainder_sub_le`. -/
@[tmio T, powerlib_foundation] theorem norm_nearIdRemainder_sub_le_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ)) (hL₂ : 0 ≤ L₂)
    (hDl : ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    {ε : ℝ} (hε : 0 < ε) (hεℓ : 2 * ε * ℓ * T < 1) {y z : E} (hy : y ∈ ball x₀ ρ)
    (hz : z ∈ ball x₀ ρ) {t : ℝ} (hyu : y + ε • strobGen f T y t ∈ ball x₀ ρ)
    (hzu : z + ε • strobGen f T z t ∈ ball x₀ ρ) :
    ‖nearIdRemainder f Df T ε y t - nearIdRemainder f Df T ε z t‖ ≤
      (4 * T * (L₂ * M * (1 + ε * ℓ * T) + ℓ ^ 2) / (1 - 2 * ε * ℓ * T) +
        8 * ε * ℓ * L₂ * M * T ^ 2 / (1 - 2 * ε * ℓ * T) ^ 2) * ‖y - z‖ := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 y hy 0)
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
  obtain ⟨hyu', hiy⟩ := isUnit_one_add_strobGenD_local hf hD hDc hε.le hεℓ hy t
  obtain ⟨hzu', hiz⟩ := isUnit_one_add_strobGenD_local hf hD hDc hε.le hεℓ hz t
  have hNzb : ‖Nz‖ ≤ 4 * ℓ * M * T := hNz ▸ norm_remainder_num_le_local hf hD hDc hε hz hzu
  have hDyz : ‖Dy - Dz‖ ≤ 2 * L₂ * T * ‖y - z‖ :=
    norm_strobGenD_sub_le_local hf hD hDc hDl hy hz t
  -- the numerators
  have hΔ : ‖(f (y + ε • uy) t - f y t) - (f (z + ε • uz) t - f z t)‖ ≤
      ε * (2 * L₂ * M * T * (1 + q) + 2 * ℓ ^ 2 * T) * ‖y - z‖ := by
    have huyz : ‖uy - uz‖ ≤ 2 * ℓ * T * ‖y - z‖ := norm_strobGen_sub_le_local hf hy hz t
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
    have hsd := second_diff_le_local hf hD hL₂ hDl hyu hy hzu hz hm1 hm2 t
    have hab : ‖(y + ε • uy) - y‖ ≤ ε * (2 * M * T) := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le]
      exact mul_le_mul_of_nonneg_left (norm_strobGen_le_local hf hy t) hε.le
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
      ((Dy - Dz).le_opNorm _).trans (mul_le_mul hDyz (norm_fieldAverage_le_local hf hy)
        (norm_nonneg _) (by positivity))
    have k3 : ‖Dz (fieldAverage f T y - fieldAverage f T z)‖ ≤ 2 * ℓ * T * (ℓ * ‖y - z‖) :=
      (Dz.le_opNorm _).trans (mul_le_mul (norm_strobGenD_le_local hf hD hDc hz t)
        (norm_fieldAverage_sub_le_local hf hy hz) (norm_nonneg _) (by positivity))
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
      rw [mul_sub, sub_mul, mul_assoc, Ring.mul_inverse_cancel _ hzu', mul_one,
        Ring.inverse_mul_cancel _ hyu', one_mul]
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

/-- The remainder field is `T`-periodic in time where `y` and `y + εu(y, t)` lie in the ball. -/
@[tmio T, powerlib_foundation] theorem nearIdRemainder_periodic_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    (ε : ℝ) {y : E} (hy : y ∈ ball x₀ ρ) {t : ℝ}
    (hyu : y + ε • strobGen f T y t ∈ ball x₀ ρ) :
    nearIdRemainder f Df T ε y (t + T) = nearIdRemainder f Df T ε y t := by
  simp only [nearIdRemainder, strobGen_periodic_local hf hy, strobGenD_periodic_local hf hD hDc hy,
    hf.2.2.2.1 _ hyu, hf.2.2.2.1 y hy]

/-- **The remainder is a field of the averaging class on every ball that the near-identity map
keeps inside the domain.** For `0 < ρ`, `0 < ε`, `2εℓT < 1`, `Df(·, t)` `L₂`-Lipschitz on the ball
and a radius `ρ₃` with `ρ₃ + 2εMT < ρ`, on the closed ball of radius `ρ₃` the remainder
`R = nearIdRemainder f Df T ε` is `T`-periodic, Lipschitz in the state with
`L_R = 4T(L₂M(1 + εℓT) + ℓ²)/(1 − 2εℓT) + 8εℓL₂MT²/(1 − 2εℓT)²` and bounded by
`4ℓMT/(1 − 2εℓT)` — the constants of `Averaging.nearIdRemainder_field`, from the local data. -/
@[tmio T, powerlib_foundation] theorem nearIdRemainder_field_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ)) (hL₂ : 0 ≤ L₂)
    (hDl : ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hρ : 0 < ρ) {ε : ℝ} (hε : 0 < ε) (hεℓ : 2 * ε * ℓ * T < 1) {ρ₃ : ℝ}
    (hρ₃ : ρ₃ + 2 * ε * M * T < ρ) :
    (∀ y ∈ closedBall x₀ ρ₃, ∀ t,
        nearIdRemainder f Df T ε y (t + T) = nearIdRemainder f Df T ε y t) ∧
      (∀ y ∈ closedBall x₀ ρ₃, ∀ z ∈ closedBall x₀ ρ₃, ∀ t,
        ‖nearIdRemainder f Df T ε y t - nearIdRemainder f Df T ε z t‖ ≤
          (4 * T * (L₂ * M * (1 + ε * ℓ * T) + ℓ ^ 2) / (1 - 2 * ε * ℓ * T) +
            8 * ε * ℓ * L₂ * M * T ^ 2 / (1 - 2 * ε * ℓ * T) ^ 2) * ‖y - z‖) ∧
      ∀ y ∈ closedBall x₀ ρ₃, ∀ t,
        ‖nearIdRemainder f Df T ε y t‖ ≤ 4 * ℓ * M * T / (1 - 2 * ε * ℓ * T) := by
  have hT := hf.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 x₀ (mem_ball_self hρ) 0)
  have hεM : 0 ≤ 2 * ε * M * T := by positivity
  have hin : ∀ y ∈ closedBall x₀ ρ₃, y ∈ ball x₀ ρ := fun y hy =>
    closedBall_subset_ball (by linarith) hy
  have hinu : ∀ y ∈ closedBall x₀ ρ₃, ∀ t, y + ε • strobGen f T y t ∈ ball x₀ ρ := by
    intro y hy t
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball, dist_eq_norm]
    have e : y + ε • strobGen f T y t - x₀ = (y - x₀) + ε • strobGen f T y t := by abel
    rw [e]
    have h1 : ‖ε • strobGen f T y t‖ ≤ 2 * ε * M * T := by
      rw [norm_smul, Real.norm_of_nonneg hε.le]
      have := mul_le_mul_of_nonneg_left (norm_strobGen_le_local hf (hin y (by
        rw [mem_closedBall, dist_eq_norm]; exact hy)) t) hε.le
      linarith
    exact (norm_add_le _ _).trans_lt (by linarith)
  exact ⟨fun y hy t => nearIdRemainder_periodic_local hf hD hDc ε (hin y hy) (hinu y hy t),
    fun y hy z hz t => norm_nearIdRemainder_sub_le_local hf hD hDc hL₂ hDl hε hεℓ (hin y hy)
      (hin z hz) (hinu y hy t) (hinu z hz t),
    fun y hy t => norm_nearIdRemainder_le_local hf hD hDc hε hεℓ (hin y hy) (hinu y hy t)⟩

/-! ## The transformed equation along a solution in the ball -/

/-- **The transformed equation along a solution that stays in the ball.** Let `f` have the
averaging hypotheses on the open ball of radius `ρ > 0` about `x₀` (continuity, `T`-periodicity,
Lipschitz constant `ℓ`, bound `M`, derivative `Df` jointly continuous there), `0 < ε`,
`2εℓT < 1`, radii `ρ₂ + 2εMT ≤ ρ₁ < ρ`, `S` an open set of times and `x` a solution of
`ẋ = εf(x, t)` on `S` with `‖x(t) − x₀‖ ≤ ρ₂` for `t ∈ S`. Then there is a curve `y` with
`‖y(t) − x₀‖ ≤ ρ₁`, `x(t) = y(t) + εu(y(t), t)` and `‖x(t) − y(t)‖ ≤ 2εMT` on `S`; it is unique on
`S` among the curves in that ball (`nearIdentity_bijOn_local`); on `S` it is differentiable with
`ẏ = εf̄(y) + ε²R(y, t)`, `R = nearIdRemainder f Df T ε`, and `‖R(y(t), t)‖ ≤ 4ℓMT/(1 − 2εℓT)`. -/
@[tmio T, powerlib_foundation] theorem transformed_solution_local
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ ContinuousOn (Function.uncurry f) (ball x₀ ρ ×ˢ univ) ∧
      (∀ x ∈ ball x₀ ρ, ∀ t, f x (t + T) = f x t) ∧
      (∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ∀ t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧
      ∀ x ∈ ball x₀ ρ, ∀ t, ‖f x t‖ ≤ M)
    (hD : ∀ x ∈ ball x₀ ρ, ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDc : ContinuousOn (Function.uncurry Df) (ball x₀ ρ ×ˢ univ))
    (hρ : 0 < ρ) {ε : ℝ} (hε : 0 < ε) (hεℓ : 2 * ε * ℓ * T < 1) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : ρ₁ < ρ) (hρ₂ : ρ₂ + 2 * ε * M * T ≤ ρ₁) {x : ℝ → E} {S : Set ℝ} (hS : IsOpen S)
    (hxS : ∀ t ∈ S, x t ∈ closedBall x₀ ρ₂) (hx : ∀ t ∈ S, HasDerivAt x (ε • f (x t) t) t) :
    ∃ y : ℝ → E, (∀ t ∈ S, y t ∈ closedBall x₀ ρ₁ ∧ x t = y t + ε • strobGen f T (y t) t ∧
        ‖x t - y t‖ ≤ 2 * ε * M * T) ∧
      (∀ z : ℝ → E, (∀ t ∈ S, z t ∈ closedBall x₀ ρ₁ ∧ x t = z t + ε • strobGen f T (z t) t) →
        EqOn z y S) ∧
      (∀ t ∈ S, HasDerivAt y
        (ε • fieldAverage f T (y t) + ε ^ 2 • nearIdRemainder f Df T ε (y t) t) t) ∧
      ∀ t ∈ S, ‖nearIdRemainder f Df T ε (y t) t‖ ≤ 4 * ℓ * M * T / (1 - 2 * ε * ℓ * T) := by
  classical
  have hT := hf.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 x₀ (mem_ball_self hρ) 0)
  have hεM : 0 ≤ 2 * ε * M * T := by positivity
  have hsub : closedBall x₀ ρ₁ ⊆ ball x₀ ρ := closedBall_subset_ball hρ₁
  have hsub₂ : closedBall x₀ ρ₂ ⊆ ball x₀ ρ :=
    (closedBall_subset_closedBall (by linarith)).trans hsub
  have hB := fun t => (nearIdentity_bijOn_local hf hρ hε.le hεℓ hρ₁ hρ₂ t).1
  set y : ℝ → E := fun t => if h : t ∈ S then (hB t (x t) (hxS t h)).exists.choose else x t
    with hydef
  have hyS : ∀ t ∈ S, y t ∈ closedBall x₀ ρ₁ ∧ y t + ε • strobGen f T (y t) t = x t :=
    fun t ht => by
      simp only [hydef, ht, ↓reduceDIte]
      exact (hB t (x t) (hxS t ht)).exists.choose_spec
  refine ⟨y, fun t ht => ⟨(hyS t ht).1, (hyS t ht).2.symm, ?_⟩,
    fun z hz t ht => (hB t (x t) (hxS t ht)).unique ⟨(hz t ht).1, (hz t ht).2.symm⟩ (hyS t ht),
    fun t ht => ?_, fun t ht => ?_⟩
  · rw [← (hyS t ht).2, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le]
    have := mul_le_mul_of_nonneg_left (norm_strobGen_le_local hf (hsub (hyS t ht).1) t) hε.le
    linarith
  · have hxy : ∀ᶠ s in 𝓝 t, y s ∈ closedBall x₀ ρ₁ ∧ x s = y s + ε • strobGen f T (y s) s := by
      filter_upwards [hS.mem_nhds ht] with s hs using ⟨(hyS s hs).1, (hyS s hs).2.symm⟩
    have h := hasDerivAt_transformedCurve_local hf hD hDc hε.le hεℓ hρ₁ hxy (hx t ht)
    refine h.congr_deriv ?_
    have hyt : y t ∈ ball x₀ ρ := hsub (hyS t ht).1
    set D := strobGenD Df T (y t) t with hDdef
    have hu : IsUnit (1 + ε • D) := (isUnit_one_add_strobGenD_local hf hD hDc hε.le hεℓ hyt t).1
    have hAinv : ∀ v, Ring.inverse (1 + ε • D) ((1 + ε • D) v) = v := fun v => by
      rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hu, one_apply_eq_self]
    set fb := fieldAverage f T (y t) with hfb
    set Δ := f (y t + ε • strobGen f T (y t) t) t - f (y t) t with hΔ
    have e0 : ε ^ 2 • (ε⁻¹ • Δ) = ε • Δ := by
      rw [smul_smul, show ε ^ 2 * ε⁻¹ = ε by field_simp]
    have e1 : ε • f (x t) t - ε • (f (y t) t - fb) =
        (1 + ε • D) (ε • fb) + ε ^ 2 • (ε⁻¹ • Δ - D fb) := by
      rw [show ε ^ 2 • (ε⁻¹ • Δ - D fb) = ε • Δ - ε ^ 2 • D fb by rw [smul_sub, e0],
        ← (hyS t ht).2, add_apply, one_apply_eq_self, smul_apply, map_smul, hΔ]
      module
    rw [e1, map_add, hAinv, map_smul]
    rfl
  · exact norm_nearIdRemainder_le_local hf hD hDc hε hεℓ (hsub (hyS t ht).1)
      (by rw [(hyS t ht).2]; exact hsub₂ (hxS t ht))

end powerlib.Averaging
