import theorem.Periodic.FlipOrbitUniform
import theorem.Dynamics.Locality

/-! # The flip reduction of a periodic solution of a field that is only locally Lipschitz

`theorem/Periodic/FlipOrbit.lean` and `theorem/Periodic/FlipOrbitUniform.lean` decide a periodic
solution `x_*` of a `T`-periodic system `ẋ = G(t, x)` at a simple multiplier `−1` for a field
that is globally Lipschitz in the state, which the flow and the period map need. A smooth field
is in general only locally Lipschitz (a cubic nonlinearity is not globally Lipschitz). This
module removes the global hypothesis: a `T`-periodic field of class `C¹` in `x` with `D_xG`
jointly continuous agrees on the ball `‖x‖ < R` with the field `G̃(t, x) = G(t, ψ_R(x))`,
`ψ_R(x) = χ_R(x) x` with a smooth bump `χ_R` (Mathlib `ContDiffBump`) equal to `1` on the closed
ball of radius `max R 1` and supported in the ball of radius `max R 1 + 1`. `G̃` is continuous,
`C¹` in `x` with jointly continuous derivative, `T`-periodic and globally Lipschitz in `x`
(`‖D_xG̃‖ ≤ ‖D_xG‖ ‖Dψ_R‖`, both factors bounded: `ψ_R` takes values in a compact ball, `Dψ_R` has
compact support, `G` is periodic), and it is as smooth in `x` as `G`. For `R` beyond the orbit and
the tube of the Taylor hypothesis, `G̃` has the same solution `x_*`, the same Jacobian along it,
the same Taylor coefficients and the same flip coefficient, and the verdicts of
`FlipOrbitUniform` apply to `G̃`. They are transferred back to `G`: a solution of `G̃` that stays
within distance `1` of `x_*` stays in the ball, so it solves `G`; solutions of `G` are unique
(local Lipschitz bound from the continuity of `D_xG` on compact sets, Mathlib
`ODE_solution_unique_of_mem_Icc_right`), so every solution of `G` near the orbit is one of `G̃`.

Scope.
* Solutions in `ℝ^X` (`X → ℝ`, finite `X`, sup norm), continuous time, integral curves on
  segments `[τ, t]` and rays `[τ, ∞)` (Mathlib `IsIntegralCurveOn`); the map semantics on `ℝⁿ`
  through `FlipOrbit.euclidMap`, as in `theorem/Periodic/FlipOrbit.lean`.
* `G` is `T`-periodic in `t` (`T > 0`), continuous, differentiable in `x` with `D_xG` jointly
  continuous in `(t, x)`; no Lipschitz bound. `x_*` is a global solution with `x_*(T) = x_*(0)`
  (hence `T`-periodic, `periodic_of_fixed_of_fderiv`). The Taylor and spectral hypotheses are those
  of `FlipOrbit`; for a field of class `C⁴` in `x` they are stated with `D_x²G/2`, `D_x³G/6` as in
  `FlipOrbit.orbit_stable_of_flipCoeff_pos_of_contDiff`.
* Since `G` has no global flow, the period map is described locally: a map `P` with
  `x(T) = P(x(0))` for every solution of `G` on `[0, T]` starting within `r` of `x_*(0)`, such
  solutions existing; the stability notions of maps only depend on `P` near the fixed point.
  The solution statements hold from every initial time `τ` with constants independent of `τ`;
  for the stable side every solution starting within `δ` exists on `[τ, ∞)`; the escaping
  solutions of the unstable side are solutions on segments `[τ, t]` (beyond the tube a locally
  Lipschitz field may blow up).
* The cut-off field is globally Lipschitz but its higher derivatives are not claimed to be
  bounded: the flip reduction only reads the field on the tube about `x_*`, where `G̃ = G`.
* The degenerate flip `a² + b = 0` is not decided (as in `FlipOrbit`).
* Generic mathematics; no model family.

Source: the localization of a locally Lipschitz field by a smooth cut-off and the uniqueness of
solutions of locally Lipschitz fields (standard; Mathlib `ODE_solution_unique_of_mem_Icc_right`);
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §5.4 (the Poincaré map of a
periodic orbit is defined near the orbit only); the open items of
`theorem/Periodic/FlipOrbit.lean` and `theorem/Periodic/FlowDerivative.lean` (Scope: "a field
that is only locally Lipschitz is first multiplied by a smooth cut-off equal to `1` near the orbit,
which is not done here").

Results.
* `exists_lipschitzOnWith_closedBall`, `eqOn_of_isIntegralCurveOn_Icc_of_fderiv`,
  `eq_of_hasDerivAt_of_fderiv`, `periodic_of_fixed_of_fderiv` — a field with jointly continuous
  `D_xG` is Lipschitz on compact sets; its solutions on segments and its global solutions are
  unique; a returning global solution of a periodic field is periodic.
* `bump`, `cutoff`, `cutoff_eq`, `norm_cutoff_le`, `contDiff_cutoff`,
  `exists_bound_fderiv_cutoff` — the smooth cut-off of the state.
* `localField`, `localField_eq`, `localField_eventuallyEq`, `fderiv_localField_eq`,
  `continuous_localField`, `differentiableAt_localField`, `fderiv_localField`,
  `continuous_fderiv_localField`, `periodic_localField`, `exists_lipschitzWith_localField`,
  `contDiff_localField`, `isIntegralCurveOn_of_localField` — the localized field: equal to `G` on
  the ball, as regular as `G`, periodic, globally Lipschitz; its solutions in the ball solve `G`.
* **The theorems**: `orbit_stable_of_flipCoeff_pos_local` (`a² + b > 0`: the local period map is
  locally asymptotically, not exponentially, stable; `x_*` is uniformly Lyapunov stable and
  uniformly attracting, the solutions near it exist for all forward time) and
  `orbit_unstable_of_flipCoeff_neg_local` (`a² + b < 0`: the local period map is unstable, and one
  escape radius serves every initial time), for fields without a global Lipschitz bound;
  `orbit_stable_of_flipCoeff_pos_of_contDiff_local`,
  `orbit_unstable_of_flipCoeff_neg_of_contDiff_local` — the same for fields of class `C⁴` in `x`.

Corrections.
None: an extension (the flip reduction of `FlipOrbit` for fields that are only locally
Lipschitz).

Family and connection conclusions.
None: static evidence on periodic ODEs (stability of a periodic solution at a period-doubling
multiplier).
-/

noncomputable section
namespace powerlib.Periodic.LocalField

open Set Matrix Function Filter Topology Metric
open scoped Matrix.Norms.Operator
open FlowDerivative PeriodMapTaylor FlipOrbit FlipOrbitUniform

/-! ## Uniqueness for fields with a continuous derivative -/

section Uniqueness

variable {X : Type*} [Fintype X] {G : ℝ → (X → ℝ) → X → ℝ}

/-- **Lipschitz on compact sets.** A field differentiable in `x` with `D_xG` jointly continuous
is Lipschitz in `x` on the closed ball of radius `R`, uniformly for `t ∈ [a, b]` (the bound of
`‖D_xG‖` on the compact `[a, b] × B̄(0, R)` and the mean value inequality). -/
@[tmio T, powerlib_foundation] theorem exists_lipschitzOnWith_closedBall
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2) (a b R : ℝ) :
    ∃ L : NNReal, ∀ t ∈ Icc a b, LipschitzOnWith L (G t) (closedBall 0 R) := by
  have hcpt := (isCompact_Icc (a := a) (b := b)).prod (isCompact_closedBall (0 : X → ℝ) R)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hD.continuousOn
  refine ⟨C.toNNReal, fun t ht => ?_⟩
  refine (convex_closedBall 0 R).lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hGd t x)
    fun x hx => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)

/-- **Uniqueness on segments.** For a field with jointly continuous `D_xG` two solutions on
`[a, b]` with the same value at `a` agree on `[a, b]`. -/
@[tmio T, powerlib_foundation] theorem eqOn_of_isIntegralCurveOn_Icc_of_fderiv
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2) {x y : ℝ → X → ℝ} {a b : ℝ}
    (hx : IsIntegralCurveOn x G (Icc a b)) (hy : IsIntegralCurveOn y G (Icc a b))
    (h0 : x a = y a) : EqOn x y (Icc a b) := by
  obtain ⟨R₁, hR₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hx.continuousOn
  obtain ⟨R₂, hR₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hy.continuousOn
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_closedBall hGd hD a b (max R₁ R₂)
  refine ODE_solution_unique_of_mem_Icc_right (s := fun _ => closedBall 0 (max R₁ R₂))
    (fun t ht => hL t (Ico_subset_Icc_self ht)) hx.continuousOn
    (hasDerivWithinAt_Ici_of_isIntegralCurveOn hx) (fun t ht => ?_) hy.continuousOn
    (hasDerivWithinAt_Ici_of_isIntegralCurveOn hy) (fun t ht => ?_) h0
  · rw [mem_closedBall, dist_zero_right]
    exact (hR₁ t (Ico_subset_Icc_self ht)).trans (le_max_left _ _)
  · rw [mem_closedBall, dist_zero_right]
    exact (hR₂ t (Ico_subset_Icc_self ht)).trans (le_max_right _ _)

/-- **Uniqueness of global solutions.** For a field with jointly continuous `D_xG` two global
solutions that agree at one time agree everywhere (forward and backward). -/
@[tmio T, powerlib_foundation] theorem eq_of_hasDerivAt_of_fderiv
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2) {x y : ℝ → X → ℝ}
    (hx : ∀ t, HasDerivAt x (G t (x t)) t) (hy : ∀ t, HasDerivAt y (G t (y t)) t) {t₀ : ℝ}
    (h0 : x t₀ = y t₀) : x = y := by
  funext t
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun r => (hx r).continuousAt
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun r => (hy r).continuousAt
  set a := min t t₀ - 1 with ha
  set b := max t t₀ + 1 with hb
  obtain ⟨R₁, hR₁⟩ := isCompact_Icc (a := a) (b := b) |>.exists_bound_of_continuousOn
    hxc.continuousOn
  obtain ⟨R₂, hR₂⟩ := isCompact_Icc (a := a) (b := b) |>.exists_bound_of_continuousOn
    hyc.continuousOn
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_closedBall hGd hD a b (max R₁ R₂)
  have h := ODE_solution_unique_of_mem_Icc (s := fun _ => closedBall 0 (max R₁ R₂))
    (fun r hr => hL r (Ioo_subset_Icc_self hr))
    (show t₀ ∈ Ioo a b from ⟨by rw [ha]; linarith [min_le_right t t₀],
      by rw [hb]; linarith [le_max_right t t₀]⟩)
    hxc.continuousOn (fun r _ => hx r)
    (fun r hr => by
      rw [mem_closedBall, dist_zero_right]
      exact (hR₁ r (Ioo_subset_Icc_self hr)).trans (le_max_left _ _))
    hyc.continuousOn (fun r _ => hy r)
    (fun r hr => by
      rw [mem_closedBall, dist_zero_right]
      exact (hR₂ r (Ioo_subset_Icc_self hr)).trans (le_max_right _ _)) h0
  exact h ⟨by rw [ha]; linarith [min_le_left t t₀], by rw [hb]; linarith [le_max_left t t₀]⟩

/-- **A returning solution is periodic.** For a `T`-periodic field with jointly continuous `D_xG`
a global solution with `x_*(T) = x_*(0)` is `T`-periodic. -/
@[tmio T, powerlib_foundation] theorem periodic_of_fixed_of_fderiv
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2) {T : ℝ} (hGper : Periodic G T)
    {xs : ℝ → X → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0) :
    Periodic xs T := by
  have h := eq_of_hasDerivAt_of_fderiv hGd hD (x := fun t => xs (t + T)) (y := xs)
    (fun t => by simpa only [hGper t] using (hxs (t + T)).comp_add_const t T) hxs (t₀ := 0)
    (by simpa using hfix)
  exact fun t => congrFun h t

end Uniqueness

/-! ## The smooth cut-off and the localized field -/

section Cutoff

variable {X : Type*} [Fintype X] {G : ℝ → (X → ℝ) → X → ℝ}

/-- The bump of the cut-off: a smooth function equal to `1` on the closed ball of radius
`max R 1` about `0`, with values in `[0, 1]`, supported in the ball of radius `max R 1 + 1`. -/
def bump (R : ℝ) : ContDiffBump (0 : X → ℝ) :=
  ⟨max R 1, max R 1 + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩

/-- The smooth cut-off of the state, `ψ_R(x) = χ_R(x) x`. -/
def cutoff (R : ℝ) (x : X → ℝ) : X → ℝ := (bump (X := X) R) x • x

@[tmio T, powerlib_foundation] theorem cutoff_eq {R : ℝ} {x : X → ℝ} (hx : ‖x‖ ≤ R) :
    cutoff R x = x := by
  rw [cutoff, (bump (X := X) R).one_of_mem_closedBall, one_smul]
  rw [mem_closedBall, dist_zero_right]
  exact hx.trans (le_max_left _ _)

@[tmio T, powerlib_foundation] theorem norm_cutoff_le (R : ℝ) (x : X → ℝ) :
    ‖cutoff R x‖ ≤ max R 1 + 1 := by
  rw [cutoff, norm_smul, Real.norm_of_nonneg (bump (X := X) R).nonneg]
  by_cases hx : x ∈ support (bump (X := X) R)
  · rw [(bump (X := X) R).support_eq, mem_ball, dist_zero_right] at hx
    calc (bump (X := X) R) x * ‖x‖ ≤ 1 * ‖x‖ :=
          mul_le_mul_of_nonneg_right (bump (X := X) R).le_one (norm_nonneg _)
      _ ≤ max R 1 + 1 := by rw [one_mul]; exact hx.le
  · rw [notMem_support.1 hx, zero_mul]
    have := le_max_right R 1
    linarith

@[tmio T, powerlib_foundation] theorem contDiff_cutoff (R : ℝ) (k : ℕ∞) :
    ContDiff ℝ k (cutoff (X := X) R) :=
  (bump (X := X) R).contDiff.smul contDiff_id

/-- The derivative of the cut-off is bounded (it is continuous with compact support). -/
@[tmio T, powerlib_foundation] theorem exists_bound_fderiv_cutoff (R : ℝ) :
    ∃ C, ∀ x, ‖fderiv ℝ (cutoff (X := X) R) x‖ ≤ C := by
  have hcs : HasCompactSupport (cutoff (X := X) R) :=
    (bump (X := X) R).hasCompactSupport.smul_right
  exact ((contDiff_cutoff R 1).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hcs.fderiv ℝ)

/-- The field localized to the ball of radius `R`: `G̃(t, x) = G(t, ψ_R(x))`. -/
def localField (G : ℝ → (X → ℝ) → X → ℝ) (R t : ℝ) (x : X → ℝ) : X → ℝ := G t (cutoff R x)

@[tmio T, powerlib_foundation] theorem localField_eq {R t : ℝ} {x : X → ℝ} (hx : ‖x‖ ≤ R) :
    localField G R t x = G t x := by
  rw [localField, cutoff_eq hx]

/-- On the open ball the localized field agrees with `G` near every point. -/
@[tmio T, powerlib_foundation] theorem localField_eventuallyEq {R t : ℝ} {x : X → ℝ}
    (hx : ‖x‖ < R) : localField G R t =ᶠ[𝓝 x] G t := by
  have hU : {y : X → ℝ | ‖y‖ < R} ∈ 𝓝 x :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hx
  filter_upwards [hU] with y hy
  exact localField_eq (le_of_lt hy)

@[tmio T, powerlib_foundation] theorem fderiv_localField_eq {R t : ℝ} {x : X → ℝ}
    (hx : ‖x‖ < R) : fderiv ℝ (localField G R t) x = fderiv ℝ (G t) x :=
  (localField_eventuallyEq hx).fderiv_eq

@[tmio T, powerlib_foundation] theorem continuous_localField (hGc : Continuous (uncurry G))
    (R : ℝ) : Continuous (uncurry (localField G R)) :=
  hGc.comp (continuous_fst.prodMk ((contDiff_cutoff R 0).continuous.comp continuous_snd))

@[tmio T, powerlib_foundation] theorem differentiableAt_localField
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x) (R t : ℝ) (x : X → ℝ) :
    DifferentiableAt ℝ (localField G R t) x :=
  (hGd t (cutoff R x)).comp x ((contDiff_cutoff R 1).differentiable (by norm_num) x)

@[tmio T, powerlib_foundation] theorem fderiv_localField
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x) (R t : ℝ) (x : X → ℝ) :
    fderiv ℝ (localField G R t) x = (fderiv ℝ (G t) (cutoff R x)).comp (fderiv ℝ (cutoff R) x) :=
  fderiv_comp x (hGd t _) ((contDiff_cutoff R 1).differentiable (by norm_num) x)

@[tmio T, powerlib_foundation] theorem continuous_fderiv_localField
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2) (R : ℝ) :
    Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (localField G R p.1) p.2 := by
  have h : (fun p : ℝ × (X → ℝ) => fderiv ℝ (localField G R p.1) p.2) =
      fun p => (fderiv ℝ (G p.1) (cutoff R p.2)).comp (fderiv ℝ (cutoff R) p.2) :=
    funext fun p => fderiv_localField hGd R p.1 p.2
  rw [h]
  exact (hD.comp (continuous_fst.prodMk ((contDiff_cutoff R 0).continuous.comp
    continuous_snd))).clm_comp
    (((contDiff_cutoff R 1).continuous_fderiv (by norm_num)).comp continuous_snd)

@[tmio T, powerlib_foundation] theorem periodic_localField {T : ℝ} (hGper : Periodic G T)
    (R : ℝ) : Periodic (localField G R) T := fun t => by
  show (fun x => G (t + T) (cutoff R x)) = fun x => G t (cutoff R x)
  rw [hGper t]

/-- **The localized field is globally Lipschitz.** For a `T`-periodic field with jointly
continuous `D_xG`, `‖D_xG̃(t, x)‖ ≤ ‖D_xG(t, ψ_R(x))‖ ‖Dψ_R(x)‖` is bounded: `ψ_R` takes values in
the closed ball of radius `max R 1 + 1`, `t` may be taken in `[0, T)`, and `Dψ_R` is bounded. -/
@[tmio T, powerlib_foundation] theorem exists_lipschitzWith_localField
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2) {T : ℝ} (hT : 0 < T)
    (hGper : Periodic G T) (R : ℝ) : ∃ K : NNReal, ∀ t, LipschitzWith K (localField G R t) := by
  obtain ⟨C₁, hC₁⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := T)).prod
    (isCompact_closedBall (0 : X → ℝ) (max R 1 + 1))).exists_bound_of_continuousOn
    hD.continuousOn
  obtain ⟨C₂, hC₂⟩ := exists_bound_fderiv_cutoff (X := X) R
  refine ⟨(max C₁ 0 * max C₂ 0).toNNReal, fun t => ?_⟩
  refine lipschitzWith_of_nnnorm_fderiv_le (fun x => differentiableAt_localField hGd R t x)
    fun x => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal', fderiv_localField hGd]
  refine le_max_of_le_left ?_
  obtain ⟨t', ht', hGt⟩ := hGper.exists_mem_Ico₀ hT t
  rw [hGt]
  refine ((fderiv ℝ (G t') (cutoff R x)).opNorm_comp_le _).trans ?_
  have h1 : ‖fderiv ℝ (G t') (cutoff R x)‖ ≤ max C₁ 0 :=
    (hC₁ (t', cutoff R x) ⟨Ico_subset_Icc_self ht', by
      rw [mem_closedBall, dist_zero_right]; exact norm_cutoff_le R x⟩).trans (le_max_left _ _)
  exact mul_le_mul h1 ((hC₂ x).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

@[tmio T, powerlib_foundation] theorem contDiff_localField {k : ℕ∞} {R t : ℝ}
    (hG : ContDiff ℝ k (G t)) : ContDiff ℝ k (localField G R t) :=
  hG.comp (contDiff_cutoff R k)

/-- A solution of the localized field that stays in the closed ball of radius `R` solves `G`. -/
@[tmio T, powerlib_foundation] theorem isIntegralCurveOn_of_localField {R : ℝ}
    {x : ℝ → X → ℝ} {S : Set ℝ} (hx : IsIntegralCurveOn x (localField G R) S)
    (hR : ∀ t ∈ S, ‖x t‖ ≤ R) : IsIntegralCurveOn x G S := fun t ht => by
  have := hx t ht
  rwa [localField_eq (hR t ht)] at this

end Cutoff

/-! ## The flip reduction for a field without a global Lipschitz bound -/

section Orbit

/-- The ball of radius `R` that contains the orbit with the tube `‖u‖ ≤ ρ` (strictly) and the
tube of radius `1`. -/
@[tmio T, powerlib_foundation] private theorem exists_radius {X : Type*} [Fintype X]
    {xs : ℝ → X → ℝ} (hxs : Continuous xs) {T : ℝ} (hT : 0 < T) (hxsp : Periodic xs T) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ∃ R : ℝ, (∀ t (u : X → ℝ), ‖u‖ ≤ ρ → ‖xs t + u‖ < R) ∧
      ∀ t (y : X → ℝ), ‖y - xs t‖ ≤ 1 → ‖y‖ ≤ R := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1
    (hxsp.compact_of_continuous hT.ne' hxs).isBounded
  refine ⟨B + ρ + 1, fun t u hu => ?_, fun t y hy => ?_⟩
  · have := hB (xs t) (mem_range_self t)
    calc ‖xs t + u‖ ≤ ‖xs t‖ + ‖u‖ := norm_add_le _ _
      _ < B + ρ + 1 := by linarith
  · have := hB (xs t) (mem_range_self t)
    calc ‖y‖ = ‖xs t + (y - xs t)‖ := by rw [add_sub_cancel]
      _ ≤ ‖xs t‖ + ‖y - xs t‖ := norm_add_le _ _
      _ ≤ B + ρ + 1 := by linarith

variable {n : ℕ} {G : ℝ → (Fin n → ℝ) → Fin n → ℝ}

/-- **The local period map.** The period map of the localized field is the period map of `G`
near `x_*(0)`: from within `r = e^{−KT}` of `x_*(0)` a solution of `G` on `[0, T]` exists, and
every one ends at `P(x(0))`. -/
@[tmio T, powerlib_foundation] private theorem periodMap_local {R : ℝ} {K : NNReal}
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hGlc : Continuous (uncurry (localField G R)))
    (hK : ∀ t, LipschitzWith K (localField G R t)) {T : ℝ} (hT : 0 ≤ T) {xs : ℝ → Fin n → ℝ}
    (hxsl : ∀ t, HasDerivAt xs (localField G R t (xs t)) t)
    (hRnear : ∀ t (y : Fin n → ℝ), ‖y - xs t‖ ≤ 1 → ‖y‖ ≤ R) :
    ∃ r, 0 < r ∧ (∀ ξ, ‖ξ - xs 0‖ < r →
        ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x G (Icc 0 T)) ∧
      ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Icc 0 T) → ‖x 0 - xs 0‖ < r →
        x T = periodMap hGlc hK T (x 0) := by
  have hC0 : 0 < Real.exp (K * T) := Real.exp_pos _
  have hsol : ∀ ξ, ‖ξ - xs 0‖ < 1 / Real.exp (K * T) →
      IsIntegralCurveOn (flow hGlc hK 0 ξ) G (Icc 0 T) := by
    intro ξ hξ
    refine isIntegralCurveOn_of_localField
      ((flow_solution hGlc hK 0 ξ).mono Icc_subset_Ici_self) fun u hu => hRnear u _ ?_
    have h := dist_le_of_isIntegralCurveOn_Icc hK
      ((flow_solution hGlc hK 0 ξ).mono Icc_subset_Ici_self)
      (fun r _ => (hxsl r).hasDerivWithinAt) u hu
    rw [dist_eq_norm, dist_eq_norm, flow_start, sub_zero] at h
    have he : Real.exp (K * u) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hu.2 K.2)
    rw [lt_div_iff₀ hC0] at hξ
    calc ‖flow hGlc hK 0 ξ u - xs u‖ ≤ ‖ξ - xs 0‖ * Real.exp (K * u) := h
      _ ≤ ‖ξ - xs 0‖ * Real.exp (K * T) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ 1 := hξ.le
  refine ⟨1 / Real.exp (K * T), by positivity,
    fun ξ hξ => ⟨flow hGlc hK 0 ξ, flow_start hGlc hK 0 ξ, hsol ξ hξ⟩, fun x hx hx0 => ?_⟩
  exact eqOn_of_isIntegralCurveOn_Icc_of_fderiv hGd hD hx (hsol (x 0) hx0)
    (flow_start hGlc hK 0 (x 0)).symm ⟨hT, le_rfl⟩

/-- A solution of `G` on `[τ, t]` along which the localized flow from its initial state stays
within `1` of `x_*` is that flow. -/
@[tmio T, powerlib_foundation] private theorem eqOn_flow_local {R : ℝ} {K : NNReal}
    (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hGlc : Continuous (uncurry (localField G R)))
    (hK : ∀ t, LipschitzWith K (localField G R t)) {xs : ℝ → Fin n → ℝ}
    (hRnear : ∀ t (y : Fin n → ℝ), ‖y - xs t‖ ≤ 1 → ‖y‖ ≤ R) {τ t : ℝ} {x : ℝ → Fin n → ℝ}
    (hx : IsIntegralCurveOn x G (Icc τ t))
    (hnear : ∀ u ∈ Icc τ t, ‖flow hGlc hK τ (x τ) u - xs u‖ ≤ 1) :
    EqOn x (flow hGlc hK τ (x τ)) (Icc τ t) :=
  eqOn_of_isIntegralCurveOn_Icc_of_fderiv hGd hD hx
    (isIntegralCurveOn_of_localField ((flow_solution hGlc hK τ (x τ)).mono Icc_subset_Ici_self)
      fun u hu => hRnear u _ (hnear u hu))
    (flow_start hGlc hK τ (x τ)).symm

/-- **The flip reduction of a periodic solution of a locally Lipschitz field, stable side.** Let
`G` be `T`-periodic in `t`, continuous, differentiable in `x` with `D_xG` jointly continuous (no
Lipschitz bound), `x_*` a global solution with `x_*(T) = x_*(0)`, with the cubic Taylor expansion
along `x_*` and the spectral data of `FlipOrbit.orbit_stable_of_flipCoeff_pos` (simple multiplier
`−1` of `M = monodromy (jacobianAlong G x_*) T 0` with stable complement, `k` solving the
homological equation). If the flip coefficient `a² + b` is positive, then:
* the period map of `G` near `x_*(0)` — a map `P` with `x(T) = P(x(0))` for the solutions of `G`
  on `[0, T]` starting within `r` of `x_*(0)`, which exist — is locally asymptotically, not
  exponentially, stable at `x_*(0)` (read on `ℝⁿ`);
* `x_*` is uniformly Lyapunov stable: for every `ε` one `δ` serves every initial time `τ` and
  every solution on a segment `[τ, t]`;
* from within some `δ` of `x_*(τ)` the solutions exist on `[τ, ∞)` and are uniformly attracted:
  for every `ε` one time `S` makes every solution on `[τ, t]`, `t ≥ τ + S`, end within `ε`. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_flipCoeff_pos_local
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2) {T : ℝ} (hT : 0 < T)
    (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t)
    (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {c₄ ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) • vm)
    (hab : 0 < (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) ^ 2 +
      (wm ⬝ᵥ thirdVariation (jacobianAlong G xs) Q₂ Q₃ 0 T (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) Q₂ 0 T vm k +
          secondVariation (jacobianAlong G xs) Q₂ 0 T k vm))) :
    (∃ (P : (Fin n → ℝ) → Fin n → ℝ) (r : ℝ), 0 < r ∧
      (∀ ξ, ‖ξ - xs 0‖ < r → ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x G (Icc 0 T)) ∧
      (∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Icc 0 T) → ‖x 0 - xs 0‖ < r →
        x T = P (x 0)) ∧
      Map.LocalAsymptoticStable (euclidMap P) ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap P)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ t : ℝ) (x : ℝ → Fin n → ℝ), τ ≤ t →
      IsIntegralCurveOn x G (Icc τ t) → ‖x τ - xs τ‖ < δ → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ (∀ (τ : ℝ) (ξ : Fin n → ℝ), ‖ξ - xs τ‖ < δ →
        ∃ x : ℝ → Fin n → ℝ, x τ = ξ ∧ IsIntegralCurveOn x G (Ici τ)) ∧
      ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ t : ℝ) (x : ℝ → Fin n → ℝ), τ + S ≤ t →
        IsIntegralCurveOn x G (Icc τ t) → ‖x τ - xs τ‖ < δ → ‖x t - xs t‖ < ε := by
  -- the localized field
  have hxsp := periodic_of_fixed_of_fderiv hGd hD hGper hxs hfix
  have hxsc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  obtain ⟨R, hRtube, hRnear⟩ := exists_radius hxsc hT hxsp hρ.le
  have hRxs : ∀ t, ‖xs t‖ < R := fun t => by simpa using hRtube t 0 (by simp [hρ.le])
  obtain ⟨K, hK⟩ := exists_lipschitzWith_localField hGd hD hT hGper R
  have hGlc := continuous_localField hGc R
  have hxsl : ∀ t, HasDerivAt xs (localField G R t (xs t)) t := fun t => by
    rw [localField_eq (hRxs t).le]; exact hxs t
  have hjac : jacobianAlong (localField G R) xs = jacobianAlong G xs := funext fun t => by
    unfold jacobianAlong; rw [fderiv_localField_eq (hRxs t)]
  have hTayl : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖localField G R r (xs r + u) -
      localField G R r (xs r) - fderiv ℝ (localField G R r) (xs r) u - Q₂ r u u -
        Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4 := fun r hr u hu => by
    rw [localField_eq (hRtube r u hu).le, localField_eq (hRxs r).le,
      fderiv_localField_eq (hRxs r)]
    exact hTay r hr u hu
  rw [← hjac] at hv hw hS hk hab
  -- the verdict for the localized field
  obtain ⟨hmap, hstab, δa, hδa, hatt⟩ := orbit_uniformly_stable_of_flipCoeff_pos hGlc
    (differentiableAt_localField hGd R) (continuous_fderiv_localField hGd hD R) hK hT
    (periodic_localField hGper R) hxsl hfix hQ₂ hQ₃ hρ hTayl hv hw hwv hS hk hab
  obtain ⟨r, hr, hex, hP⟩ := periodMap_local hGd hD hGlc hK hT.le hxsl hRnear
  -- from within `δ₁` the localized flow stays within `1` of `x_*`
  obtain ⟨δ₁, hδ₁, hb₁⟩ := hstab 1 one_pos
  have hnear : ∀ τ (ξ : Fin n → ℝ), ‖ξ - xs τ‖ < δ₁ → ∀ u, τ ≤ u →
      ‖flow hGlc hK τ ξ u - xs u‖ < 1 := fun τ ξ hξ u hu =>
    hb₁ τ _ (flow_solution hGlc hK τ ξ) (by rwa [flow_start]) u hu
  refine ⟨⟨periodMap hGlc hK T, r, hr, hex, hP, hmap⟩, fun ε hε => ?_, min δa δ₁,
    lt_min hδa hδ₁, fun τ ξ hξ => ?_, fun ε hε => ?_⟩
  · -- uniform Lyapunov stability
    obtain ⟨δ, hδ, hb⟩ := hstab (min ε 1) (lt_min hε one_pos)
    refine ⟨δ, hδ, fun τ t x hτt hx hx0 => ?_⟩
    have hfl : ∀ u, τ ≤ u → ‖flow hGlc hK τ (x τ) u - xs u‖ < min ε 1 := fun u hu =>
      hb τ _ (flow_solution hGlc hK τ (x τ)) (by rwa [flow_start]) u hu
    have heq := eqOn_flow_local hGd hD hGlc hK hRnear hx fun u hu =>
      ((hfl u hu.1).trans_le (min_le_right _ _)).le
    rw [heq ⟨hτt, le_rfl⟩]
    exact (hfl t hτt).trans_le (min_le_left _ _)
  · -- existence on `[τ, ∞)`
    exact ⟨flow hGlc hK τ ξ, flow_start hGlc hK τ ξ,
      isIntegralCurveOn_of_localField (flow_solution hGlc hK τ ξ) fun u hu =>
        hRnear u _ (hnear τ ξ (hξ.trans_le (min_le_right _ _)) u hu).le⟩
  · -- uniform attraction
    obtain ⟨S, hS0, hS⟩ := hatt ε hε
    refine ⟨S, hS0, fun τ t x hτt hx hx0 => ?_⟩
    have hx0' : ‖flow hGlc hK τ (x τ) τ - xs τ‖ < δa := by
      rw [flow_start]; exact hx0.trans_le (min_le_left _ _)
    have heq := eqOn_flow_local hGd hD hGlc hK hRnear hx fun u hu =>
      (hnear τ (x τ) (hx0.trans_le (min_le_right _ _)) u hu.1).le
    rw [heq ⟨by linarith, le_rfl⟩]
    exact hS τ _ (flow_solution hGlc hK τ (x τ)) hx0' t hτt

/-- **The flip reduction of a periodic solution of a locally Lipschitz field, unstable side.**
Under the hypotheses of `orbit_stable_of_flipCoeff_pos_local`, a negative flip coefficient
`a² + b` makes the period map of `G` near `x_*(0)` unstable and `x_*` unstable with one escape
radius for every initial time: there is `ε > 0` such that for every `τ` and every `δ > 0` a
solution of `G` on a segment `[τ, t]` starts within `δ` of `x_*(τ)` and ends at the distance at
least `ε` from `x_*(t)`. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_flipCoeff_neg_local
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2) {T : ℝ} (hT : 0 < T)
    (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t)
    (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {c₄ ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) • vm)
    (hab : (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) ^ 2 +
      (wm ⬝ᵥ thirdVariation (jacobianAlong G xs) Q₂ Q₃ 0 T (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) Q₂ 0 T vm k +
          secondVariation (jacobianAlong G xs) Q₂ 0 T k vm)) < 0) :
    (∃ (P : (Fin n → ℝ) → Fin n → ℝ) (r : ℝ), 0 < r ∧
      (∀ ξ, ‖ξ - xs 0‖ < r → ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x G (Icc 0 T)) ∧
      (∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Icc 0 T) → ‖x 0 - xs 0‖ < r →
        x T = P (x 0)) ∧
      Map.Unstable (euclidMap P) ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    ∃ ε, 0 < ε ∧ ∀ (τ δ : ℝ), 0 < δ → ∃ (x : ℝ → Fin n → ℝ) (t : ℝ), τ ≤ t ∧
      IsIntegralCurveOn x G (Icc τ t) ∧ ‖x τ - xs τ‖ < δ ∧ ε ≤ ‖x t - xs t‖ := by
  -- the localized field
  have hxsp := periodic_of_fixed_of_fderiv hGd hD hGper hxs hfix
  have hxsc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  obtain ⟨R, hRtube, hRnear⟩ := exists_radius hxsc hT hxsp hρ.le
  have hRxs : ∀ t, ‖xs t‖ < R := fun t => by simpa using hRtube t 0 (by simp [hρ.le])
  obtain ⟨K, hK⟩ := exists_lipschitzWith_localField hGd hD hT hGper R
  have hGlc := continuous_localField hGc R
  have hxsl : ∀ t, HasDerivAt xs (localField G R t (xs t)) t := fun t => by
    rw [localField_eq (hRxs t).le]; exact hxs t
  have hjac : jacobianAlong (localField G R) xs = jacobianAlong G xs := funext fun t => by
    unfold jacobianAlong; rw [fderiv_localField_eq (hRxs t)]
  have hTayl : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖localField G R r (xs r + u) -
      localField G R r (xs r) - fderiv ℝ (localField G R r) (xs r) u - Q₂ r u u -
        Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4 := fun r hr u hu => by
    rw [localField_eq (hRtube r u hu).le, localField_eq (hRxs r).le,
      fderiv_localField_eq (hRxs r)]
    exact hTay r hr u hu
  rw [← hjac] at hv hw hS hk hab
  -- the verdict for the localized field
  obtain ⟨hmap, ε₀, hε₀, hesc⟩ := orbit_uniformly_unstable_of_flipCoeff_neg hGlc
    (differentiableAt_localField hGd R) (continuous_fderiv_localField hGd hD R) hK hT
    (periodic_localField hGper R) hxsl hfix hQ₂ hQ₃ hρ hTayl hv hw hwv hS hk hab
  obtain ⟨r, hr, hex, hP⟩ := periodMap_local hGd hD hGlc hK hT.le hxsl hRnear
  refine ⟨⟨periodMap hGlc hK T, r, hr, hex, hP, hmap⟩, min ε₀ 1, lt_min hε₀ one_pos,
    fun τ δ hδ => ?_⟩
  obtain ⟨y, hy, hy0, t₁, ht₁, hyt₁⟩ :=
    hesc (min δ (min ε₀ 1)) (lt_min hδ (lt_min hε₀ one_pos)) τ
  -- the first time the escaping solution reaches the distance `min ε₀ 1`; until then it is in
  -- the tube of radius `1`, where it solves `G`
  have hfirst : ∃ s ∈ Icc τ t₁, (∀ u ∈ Icc τ s, ‖y u - xs u‖ ≤ 1) ∧
      min ε₀ 1 ≤ ‖y s - xs s‖ := by
    by_contra hcon
    push Not at hcon
    have hc := Dynamics.forall_lt_of_first_exit (φ := fun u => y u - xs u) (Φ := norm)
      (c := min ε₀ 1) continuous_norm
      ((hy.continuousOn.mono Icc_subset_Ici_self).sub hxsc.continuousOn)
      (hy0.trans_le (min_le_right _ _))
      (fun s hs hle => hcon s hs fun u hu => (hle u hu).trans (min_le_right _ _)) t₁
      ⟨ht₁, le_rfl⟩
    exact absurd hyt₁ (not_le.2 (hc.trans_le (min_le_left _ _)))
  obtain ⟨s, hs, hle, hesc'⟩ := hfirst
  exact ⟨y, s, hs.1, isIntegralCurveOn_of_localField (hy.mono Icc_subset_Ici_self)
    fun u hu => hRnear u _ (hle u hu), hy0.trans_le (min_le_left _ _), hesc'⟩

/-- **Fields of class `C⁴` without a global Lipschitz bound, stable side.**
`orbit_stable_of_flipCoeff_pos_local` for a field with `G(t, ·)` of class `C⁴`, `D_x²G`, `D_x³G`
continuous along `x_*` and `‖D_x⁴G‖ ≤ B₄` on the tube of radius `ρ` about `x_*`, with
`Q₂ = D_x²G/2 = taylor2 G x_*` and `Q₃ = D_x³G/6 = taylor3 G x_*`
(`PeriodMapTaylor.taylor_along_of_contDiff`). -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_flipCoeff_pos_of_contDiff_local
    (hGc : Continuous (uncurry G)) (hG4 : ∀ t, ContDiff ℝ 4 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2) {T : ℝ} (hT : 0 < T)
    (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t)
    (hfix : xs T = xs 0) (hD2 : Continuous fun r => fderiv ℝ (fderiv ℝ (G r)) (xs r))
    (hD3 : Continuous fun r => iteratedFDeriv ℝ 3 (G r) (xs r)) {ρ B₄ : ℝ} (hρ : 0 < ρ)
    (hB4 : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 4 (G r) y‖ ≤ B₄)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm) • vm)
    (hab : 0 < (wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm) ^ 2 +
      (wm ⬝ᵥ thirdVariation (jacobianAlong G xs) (taylor2 G xs) (taylor3 G xs) 0 T
          (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm k +
          secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T k vm))) :
    (∃ (P : (Fin n → ℝ) → Fin n → ℝ) (r : ℝ), 0 < r ∧
      (∀ ξ, ‖ξ - xs 0‖ < r → ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x G (Icc 0 T)) ∧
      (∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Icc 0 T) → ‖x 0 - xs 0‖ < r →
        x T = P (x 0)) ∧
      Map.LocalAsymptoticStable (euclidMap P) ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap P)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ t : ℝ) (x : ℝ → Fin n → ℝ), τ ≤ t →
      IsIntegralCurveOn x G (Icc τ t) → ‖x τ - xs τ‖ < δ → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ (∀ (τ : ℝ) (ξ : Fin n → ℝ), ‖ξ - xs τ‖ < δ →
        ∃ x : ℝ → Fin n → ℝ, x τ = ξ ∧ IsIntegralCurveOn x G (Ici τ)) ∧
      ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ t : ℝ) (x : ℝ → Fin n → ℝ), τ + S ≤ t →
        IsIntegralCurveOn x G (Icc τ t) → ‖x τ - xs τ‖ < δ → ‖x t - xs t‖ < ε :=
  orbit_stable_of_flipCoeff_pos_local hGc (fun t => (hG4 t).differentiable (by norm_num)) hD hT
    hGper hxs hfix (hD2.const_smul (1 / 2 : ℝ)) (hD3.const_smul (1 / 6 : ℝ)) hρ
    (taylor_along_of_contDiff (fun r _ y _ => (hG4 r).contDiffAt) hB4) hv hw hwv hS hk hab

/-- **Fields of class `C⁴` without a global Lipschitz bound, unstable side.**
`orbit_unstable_of_flipCoeff_neg_local` with `Q₂ = D_x²G/2`, `Q₃ = D_x³G/6` along `x_*`, under
the hypotheses of `orbit_stable_of_flipCoeff_pos_of_contDiff_local`. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_flipCoeff_neg_of_contDiff_local
    (hGc : Continuous (uncurry G)) (hG4 : ∀ t, ContDiff ℝ 4 (G t))
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2) {T : ℝ} (hT : 0 < T)
    (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t)
    (hfix : xs T = xs 0) (hD2 : Continuous fun r => fderiv ℝ (fderiv ℝ (G r)) (xs r))
    (hD3 : Continuous fun r => iteratedFDeriv ℝ 3 (G r) (xs r)) {ρ B₄ : ℝ} (hρ : 0 < ρ)
    (hB4 : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ 4 (G r) y‖ ≤ B₄)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm) • vm)
    (hab : (wm ⬝ᵥ secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm vm) ^ 2 +
      (wm ⬝ᵥ thirdVariation (jacobianAlong G xs) (taylor2 G xs) (taylor3 G xs) 0 T
          (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T vm k +
          secondVariation (jacobianAlong G xs) (taylor2 G xs) 0 T k vm)) < 0) :
    (∃ (P : (Fin n → ℝ) → Fin n → ℝ) (r : ℝ), 0 < r ∧
      (∀ ξ, ‖ξ - xs 0‖ < r → ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x G (Icc 0 T)) ∧
      (∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Icc 0 T) → ‖x 0 - xs 0‖ < r →
        x T = P (x 0)) ∧
      Map.Unstable (euclidMap P) ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    ∃ ε, 0 < ε ∧ ∀ (τ δ : ℝ), 0 < δ → ∃ (x : ℝ → Fin n → ℝ) (t : ℝ), τ ≤ t ∧
      IsIntegralCurveOn x G (Icc τ t) ∧ ‖x τ - xs τ‖ < δ ∧ ε ≤ ‖x t - xs t‖ :=
  orbit_unstable_of_flipCoeff_neg_local hGc (fun t => (hG4 t).differentiable (by norm_num)) hD
    hT hGper hxs hfix (hD2.const_smul (1 / 2 : ℝ)) (hD3.const_smul (1 / 6 : ℝ)) hρ
    (taylor_along_of_contDiff (fun r _ y _ => (hG4 r).contDiffAt) hB4) hv hw hwv hS hk hab

end Orbit

end powerlib.Periodic.LocalField
