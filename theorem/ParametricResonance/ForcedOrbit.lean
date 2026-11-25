import theorem.ParametricResonance.BlockAveraging

/-! # The forced periodic orbit of a periodically driven system near an equilibrium

The variational equation of the source is taken along the forced trajectory
`x*(t) = x₀ + ε Re{z e^{jωt}} + O(ε²)`. This file proves that this trajectory exists. In deviation
coordinates `y = x − x₀` the system is `ẏ = A y + ε b(t) + N_ε(t, y)` with `T`-periodic `b`, `N`;
when `I − e^{TA}` is invertible (the linear part has no Floquet multiplier `1`, i.e. no eigenvalue
in `(2πj/T)ℤ`) and `N` is quadratically small, there is for small `ε` a `T`-periodic solution in a
ball of radius `cε`, it is unique there, and every such solution satisfies `‖y − ε y_p‖ ≤ C ε²`,
`y_p` the periodic solution of `ẏ_p = A y_p + b`. The proof is the implicit function theorem in
its contraction form: `y = G(εb + N_ε(·, y))` with the periodic Green operator `G`, a contraction
on a closed ball of bounded continuous periodic functions.

Scope.
* Finite state space `X → ℝ` (sup norm), constant `A`, continuous `T`-periodic `b`, and `N`
  jointly continuous in `(t, y)` on `ℝ × {‖y‖ ≤ ρ}` (for each `0 ≤ ε ≤ ε₀`), `T`-periodic in `t`,
  with
  `‖N_ε(t, 0)‖ ≤ K ε²` and `‖N_ε(t, y₁) − N_ε(t, y₂)‖ ≤ K(‖y₁‖ + ‖y₂‖ + ε)‖y₁ − y₂‖` on a ball
  `‖yᵢ‖ ≤ ρ`, for `0 ≤ ε ≤ ε₀` (a `C²` vector field with `f(x₀, u₀) = 0` and a smooth input).
* `I − e^{TA}` is given with a two-sided inverse `M` (constructed from modal coordinates in
  `ForcedOrbitFloquet.exists_minv_of_modal`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (`J_p = A₀ + ε Re{A₁ e^{jω_p t}}` along the forced
trajectory, `g_m = l_mᴴ A₁ r_m*`, first-order averaging), [8, 9] of that report.

Results.
* `green`, `green_eq`, `green_hasDerivAt`, `green_periodic` — the periodic Green operator
  `G h(t) = M ∫_{t−T}^{t} e^{(t−s)A} h(s) ds` solves `ẏ = A y + h` and is `T`-periodic;
  `green_add`, `green_smul`, `green_sub`, `green_bound` (`‖G h‖ ≤ C_L sup‖h‖`).
* `periodic_homogeneous_zero`, `periodic_eq_green` — every periodic solution of `ẏ = A y + h` is
  `G h`.
* `norm_N_le`, `orbit_contraction` — existence and local uniqueness for fixed `ε` under explicit
  smallness conditions; `orbit_expansion` — `‖y − ε y_p‖ ≤ C_L(Kε² + K(r + ε)r)`.
* `forced_orbit` — for all `ε ∈ (0, ε₁]`: existence in the ball of radius `cε`, uniqueness there,
  and `‖y − ε y_p‖ ≤ C ε²`.
* Helpers: `entryCLM`, `mulVecCLM`, `hasDerivAt_mulVec`, `expS_add`, `expS_zero`, `minv_comm`,
  `continuous_expS_neg_mulVec`, `integrable_kernel`, `exists_bound_of_periodic_vec`.

Corrections.
None.

Family and connection conclusions.
None: static evidence on periodically forced ODEs (existence and expansion of the periodic orbit).
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbit
open Matrix Set Filter Topology
open scoped Matrix.Norms.Operator Interval BoundedContinuousFunction
open BlockAveraging (expS expS_mul_neg hasDerivAt_expS expS_comm continuous_expS)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Calculus helpers -/

/-- The entry `(i, j)` as a continuous linear map. -/
def entryCLM (i j : X) : Matrix X X ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Multiplication by a constant matrix as a continuous linear map. -/
def mulVecCLM (M : Matrix X X ℝ) : (X → ℝ) →L[ℝ] (X → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem mulVecCLM_apply (M : Matrix X X ℝ) (v : X → ℝ) :
    mulVecCLM M v = M *ᵥ v := rfl

omit [DecidableEq X] in
/-- Product rule for `t ↦ M(t) v(t)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_mulVec {M : ℝ → Matrix X X ℝ}
    {v : ℝ → X → ℝ} {M' : Matrix X X ℝ} {v' : X → ℝ} {t : ℝ} (hM : HasDerivAt M M' t)
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun t => M t *ᵥ v t) (M' *ᵥ v t + M t *ᵥ v') t := by
  rw [hasDerivAt_pi]
  intro i
  have hj : ∀ j ∈ (Finset.univ : Finset X), HasDerivAt (fun t => M t i j * v t j)
      (M' i j * v t j + M t i j * v' j) t := fun j _ =>
    ((entryCLM i j).hasFDerivAt.comp_hasDerivAt t hM).mul (hasDerivAt_pi.1 hv j)
  have hs := HasDerivAt.fun_sum hj
  convert hs using 1
  · funext s; simp [Matrix.mulVec, dotProduct]
  · simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib]

@[tmio T, powerlib_foundation] theorem expS_add (A : Matrix X X ℝ) (a b : ℝ) :
    expS A a * expS A b = expS A (a + b) := by
  have hc : Commute (a • A) (b • A) := (Commute.refl A).smul_left a |>.smul_right b
  rw [BlockAveraging.expS, BlockAveraging.expS, BlockAveraging.expS,
    ← Matrix.exp_add_of_commute _ _ hc, add_smul]

@[tmio T, powerlib_foundation] theorem expS_zero (A : Matrix X X ℝ) : expS A 0 = 1 := by
  simp [BlockAveraging.expS]

/-! ### The periodic Green operator of `ẏ = A y + h` -/

/-- `G h (t) = (I − e^{TA})⁻¹ e^{tA} ∫_{t−T}^{t} e^{−sA} h(s) ds`: the `T`-periodic solution of
`ẏ = A y + h` for `T`-periodic `h` (`Minv = (I − e^{TA})⁻¹`). -/
def green (A Minv : Matrix X X ℝ) (T : ℝ) (h : ℝ → X → ℝ) (t : ℝ) : X → ℝ :=
  Minv *ᵥ (expS A t *ᵥ ∫ s in (t - T)..t, expS A (-s) *ᵥ h s)

@[tmio T, powerlib_foundation] theorem continuous_expS_neg_mulVec (A : Matrix X X ℝ)
    {h : ℝ → X → ℝ} (hh : Continuous h) : Continuous (fun s => expS A (-s) *ᵥ h s) :=
  ((continuous_expS A).comp continuous_neg).matrix_mulVec hh

/-- `G h = Minv ∫_{t−T}^{t} e^{(t−s)A} h(s) ds`. -/
@[tmio T, powerlib_foundation] theorem green_eq (A Minv : Matrix X X ℝ) (T : ℝ)
    {h : ℝ → X → ℝ} (hh : Continuous h) (t : ℝ) :
    green A Minv T h t = Minv *ᵥ ∫ s in (t - T)..t, expS A (t - s) *ᵥ h s := by
  rw [green, ← mulVecCLM_apply (expS A t),
    ← (mulVecCLM (expS A t)).intervalIntegral_comp_comm
      ((continuous_expS_neg_mulVec A hh).intervalIntegrable _ _)]
  congr 2
  funext s
  rw [mulVecCLM_apply, Matrix.mulVec_mulVec, expS_add, sub_eq_add_neg]

/-- `Minv` commutes with `A` when it inverts `I − e^{TA}`. -/
@[tmio T, powerlib_foundation] theorem minv_comm {A Minv : Matrix X X ℝ} {T : ℝ}
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1) : Minv * A = A * Minv := by
  have hc : (1 - expS A T) * A = A * (1 - expS A T) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, expS_comm]
  calc Minv * A = Minv * A * ((1 - expS A T) * Minv) := by rw [hR, Matrix.mul_one]
    _ = Minv * ((1 - expS A T) * A) * Minv := by simp only [Matrix.mul_assoc, hc]
    _ = A * Minv := by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]

/-- `G h` solves `ẏ = A y + h` for continuous `T`-periodic `h`. -/
@[tmio T, powerlib_foundation] theorem green_hasDerivAt {A Minv : Matrix X X ℝ} {T : ℝ}
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1) {h : ℝ → X → ℝ}
    (hh : Continuous h) (hper : ∀ s, h (s + T) = h s) (t : ℝ) :
    HasDerivAt (green A Minv T h) (A *ᵥ green A Minv T h t + h t) t := by
  set g := fun s => expS A (-s) *ᵥ h s with hgd
  have hg : Continuous g := continuous_expS_neg_mulVec A hh
  have hIeq : (fun t => ∫ s in (t - T)..t, g s) =
      fun t => (∫ s in (0 : ℝ)..t, g s) - ∫ s in (0 : ℝ)..(t - T), g s := by
    funext t
    rw [intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)]
  have hI : HasDerivAt (fun t => ∫ s in (t - T)..t, g s) (g t - g (t - T)) t := by
    rw [hIeq]
    have h1 := (hg.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hl : HasDerivAt (fun t : ℝ => t - T) 1 t := by
      simpa using (hasDerivAt_id t).sub_const T
    have h2 := (hg.integral_hasStrictDerivAt 0 (t - T)).hasDerivAt.scomp t hl
    have h3 := h1.sub h2
    simp only [one_smul] at h3
    exact h3
  have hP := hasDerivAt_mulVec (hasDerivAt_expS A t) hI
  have hF := hasDerivAt_mulVec (hasDerivAt_const t Minv) hP
  refine hF.congr_deriv ?_
  have hc := minv_comm hL hR
  have e1 : expS A t *ᵥ g t = h t := by
    rw [hgd]; simp only; rw [Matrix.mulVec_mulVec, (expS_mul_neg A t).1, Matrix.one_mulVec]
  have e2 : expS A t *ᵥ g (t - T) = expS A T *ᵥ h t := by
    have hp := hper (t - T)
    rw [sub_add_cancel] at hp
    rw [hgd]; simp only
    rw [Matrix.mulVec_mulVec, expS_add, ← hp]
    congr 2; ring
  rw [zero_mulVec, zero_add, Matrix.mulVec_sub, e1, e2, expS_comm, Matrix.mulVec_add,
    ← Matrix.mulVec_mulVec]
  have k1 : Minv *ᵥ (A *ᵥ (expS A t *ᵥ ∫ s in (t - T)..t, g s)) = A *ᵥ green A Minv T h t := by
    rw [green, Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
  rw [k1]
  congr 1
  have : h t - expS A T *ᵥ h t = (1 - expS A T) *ᵥ h t := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [this, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]

/-- `G h` is `T`-periodic for `T`-periodic `h`. -/
@[tmio T, powerlib_foundation] theorem green_periodic (A Minv : Matrix X X ℝ) (T : ℝ)
    {h : ℝ → X → ℝ} (hh : Continuous h) (hper : ∀ s, h (s + T) = h s) (t : ℝ) :
    green A Minv T h (t + T) = green A Minv T h t := by
  rw [green_eq A Minv T hh, green_eq A Minv T hh]
  congr 1
  have e := intervalIntegral.integral_comp_add_right
    (fun s => expS A (t + T - s) *ᵥ h s) T (a := t - T) (b := t)
  rw [show t + T - T = t - T + T by ring, ← e]
  congr 1
  funext s
  rw [hper s]
  congr 2
  ring

@[tmio T, powerlib_foundation] theorem integrable_kernel (A : Matrix X X ℝ) {h : ℝ → X → ℝ}
    (hh : Continuous h) (t a b : ℝ) :
    IntervalIntegrable (fun s => expS A (t - s) *ᵥ h s) MeasureTheory.volume a b := by
  exact (((continuous_expS A).comp (continuous_const.sub continuous_id)).matrix_mulVec
    hh).intervalIntegrable a b

/-- `G` is additive. -/
@[tmio T, powerlib_foundation] theorem green_add (A Minv : Matrix X X ℝ) (T : ℝ)
    {h1 h2 : ℝ → X → ℝ} (h1c : Continuous h1) (h2c : Continuous h2) (t : ℝ) :
    green A Minv T (fun s => h1 s + h2 s) t = green A Minv T h1 t + green A Minv T h2 t := by
  rw [green_eq A Minv T (h := fun s => h1 s + h2 s) (h1c.add h2c), green_eq A Minv T h1c,
    green_eq A Minv T h2c, ← Matrix.mulVec_add,
    ← intervalIntegral.integral_add (integrable_kernel A h1c t _ _) (integrable_kernel A h2c t _ _)]
  congr 2; funext s; rw [Matrix.mulVec_add]

/-- `G` is homogeneous. -/
@[tmio T, powerlib_foundation] theorem green_smul (A Minv : Matrix X X ℝ) (T c : ℝ)
    {h : ℝ → X → ℝ} (hc : Continuous h) (t : ℝ) :
    green A Minv T (fun s => c • h s) t = c • green A Minv T h t := by
  rw [green_eq A Minv T (h := fun s => c • h s) (hc.const_smul c), green_eq A Minv T hc,
    ← Matrix.mulVec_smul, ← intervalIntegral.integral_smul]
  congr 2; funext s; rw [Matrix.mulVec_smul]

/-- `‖G h‖ ≤ C_L sup ‖h‖`. -/
@[tmio T, powerlib_foundation] theorem green_bound (A Minv : Matrix X X ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ CL, 0 ≤ CL ∧ ∀ (h : ℝ → X → ℝ) (H : ℝ), Continuous h → (∀ s, ‖h s‖ ≤ H) →
      ∀ t, ‖green A Minv T h t‖ ≤ CL * H := by
  obtain ⟨CE, hCE⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_expS A).continuousOn
  set CE' := max CE 0
  refine ⟨‖Minv‖ * CE' * T, by positivity, fun h H hc hH t => ?_⟩
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  rw [green_eq A Minv T hc]
  have hint : ‖∫ s in (t - T)..t, expS A (t - s) *ᵥ h s‖ ≤ CE' * H * T := by
    have hb : ∀ s ∈ Ι (t - T) t, ‖expS A (t - s) *ᵥ h s‖ ≤ CE' * H := by
      intro s hs
      rw [Set.uIoc_of_le (by linarith)] at hs
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      have hm : t - s ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      exact mul_le_mul ((hCE _ hm).trans (le_max_left _ _)) (hH s) (norm_nonneg _)
        (le_max_right _ _)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rwa [show t - (t - T) = T by ring, abs_of_nonneg hT] at this
  calc ‖Minv *ᵥ ∫ s in (t - T)..t, expS A (t - s) *ᵥ h s‖
      ≤ ‖Minv‖ * ‖∫ s in (t - T)..t, expS A (t - s) *ᵥ h s‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ ‖Minv‖ * (CE' * H * T) := mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ = ‖Minv‖ * CE' * T * H := by ring

/-- A `T`-periodic solution of `ẇ = A w` vanishes when `I − e^{TA}` is invertible. -/
@[tmio T, powerlib_foundation] theorem periodic_homogeneous_zero {A Minv : Matrix X X ℝ} {T : ℝ}
    (hL : Minv * (1 - expS A T) = 1) {w : ℝ → X → ℝ}
    (hw : ∀ t, HasDerivAt w (A *ᵥ w t) t) (hwp : w T = w 0) (t : ℝ) : w t = 0 := by
  have hφ : ∀ t, HasDerivAt (fun t => expS A (-t) *ᵥ w t) 0 t := by
    intro t
    have hE := (hasDerivAt_expS A (-t)).scomp t (hasDerivAt_neg t)
    have h := hasDerivAt_mulVec hE (hw t)
    refine h.congr_deriv ?_
    rw [Matrix.mulVec_mulVec]
    simp [Function.comp, Matrix.neg_mulVec]
  have hconst : ∀ t, expS A (-t) *ᵥ w t = w 0 := by
    intro t
    have := is_const_of_deriv_eq_zero (f := fun t => expS A (-t) *ᵥ w t)
      (fun t => (hφ t).differentiableAt) (fun t => (hφ t).deriv) t 0
    rw [this]; simp [expS_zero]
  have hsol : ∀ t, w t = expS A t *ᵥ w 0 := by
    intro t
    rw [← hconst t, Matrix.mulVec_mulVec, (expS_mul_neg A t).1, Matrix.one_mulVec]
  have h0 : w 0 = 0 := by
    have e : (1 - expS A T) *ᵥ w 0 = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hsol T, hwp, sub_self]
    rw [← Matrix.one_mulVec (w 0), ← hL, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]
  rw [hsol t, h0, Matrix.mulVec_zero]

/-- Every `T`-periodic solution of `ẏ = A y + h` is `G h`. -/
@[tmio T, powerlib_foundation] theorem periodic_eq_green {A Minv : Matrix X X ℝ} {T : ℝ}
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1) {h : ℝ → X → ℝ}
    (hh : Continuous h) (hper : ∀ s, h (s + T) = h s) {y : ℝ → X → ℝ}
    (hy : ∀ t, HasDerivAt y (A *ᵥ y t + h t) t) (hyp : ∀ t, y (t + T) = y t) (t : ℝ) :
    y t = green A Minv T h t := by
  have hw : ∀ t, HasDerivAt (fun t => y t - green A Minv T h t) (A *ᵥ (y t - green A Minv T h t)) t := by
    intro t
    have := (hy t).sub (green_hasDerivAt hL hR hh hper t)
    refine this.congr_deriv ?_
    rw [Matrix.mulVec_sub]; abel
  have hwp : y T - green A Minv T h T = y 0 - green A Minv T h 0 := by
    have h1 := hyp 0
    have h2 := green_periodic A Minv T hh hper 0
    rw [zero_add] at h1 h2
    rw [h1, h2]
  have := periodic_homogeneous_zero hL hw hwp t
  exact sub_eq_zero.1 this

/-- `G` respects differences. -/
@[tmio T, powerlib_foundation] theorem green_sub (A Minv : Matrix X X ℝ) (T : ℝ)
    {h1 h2 : ℝ → X → ℝ} (h1c : Continuous h1) (h2c : Continuous h2) (t : ℝ) :
    green A Minv T h1 t - green A Minv T h2 t = green A Minv T (fun s => h1 s - h2 s) t := by
  rw [green_eq A Minv T (h := fun s => h1 s - h2 s) (h1c.sub h2c), green_eq A Minv T h1c,
    green_eq A Minv T h2c, ← Matrix.mulVec_sub,
    ← intervalIntegral.integral_sub (integrable_kernel A h1c t _ _) (integrable_kernel A h2c t _ _)]
  congr 2; funext s; rw [Matrix.mulVec_sub]

/-! ### The forced periodic orbit -/

omit [DecidableEq X] in
/-- The quadratic bound in the ball: `‖N(t, y)‖ ≤ K ε² + K(‖y‖ + ε)‖y‖`. -/
@[tmio T, powerlib_foundation] theorem norm_N_le {N : ℝ → (X → ℝ) → X → ℝ} {K ρ ε : ℝ}
    (hρ : 0 ≤ ρ) (hN0 : ∀ t, ‖N t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ → ‖N t y1 - N t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    (t : ℝ) {y : X → ℝ} (hy : ‖y‖ ≤ ρ) :
    ‖N t y‖ ≤ K * ε ^ 2 + K * (‖y‖ + ε) * ‖y‖ := by
  have h := hNL t y 0 hy (by simpa using hρ)
  simp only [norm_zero, add_zero, sub_zero] at h
  calc ‖N t y‖ = ‖N t 0 + (N t y - N t 0)‖ := by rw [add_sub_cancel]
    _ ≤ ‖N t 0‖ + ‖N t y - N t 0‖ := norm_add_le _ _
    _ ≤ K * ε ^ 2 + K * (‖y‖ + ε) * ‖y‖ := add_le_add (hN0 t) h

/-- Existence and local uniqueness of the forced periodic orbit of `ẏ = A y + ε b(t) + N(t, y)` in
the ball of radius `r`, by the contraction mapping principle in the space of bounded continuous
functions: `y = G(εb + N(·, y))`. -/
@[tmio T, powerlib_foundation] theorem orbit_contraction {A Minv : Matrix X X ℝ} {T : ℝ}
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1) {b : ℝ → X → ℝ}
    (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t) {N : ℝ → (X → ℝ) → X → ℝ}
    {CL K ρ r ε Bb : ℝ}
    (hNc : ContinuousOn (fun p : ℝ × (X → ℝ) => N p.1 p.2) (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ t y, N (t + T) y = N t y)
    (hCL : ∀ (h : ℝ → X → ℝ) (H : ℝ), Continuous h → (∀ s, ‖h s‖ ≤ H) →
      ∀ t, ‖green A Minv T h t‖ ≤ CL * H)
    (hCL0 : 0 ≤ CL) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hr0 : 0 ≤ r) (hrρ : r ≤ ρ)
    (hBb : ∀ t, ‖b t‖ ≤ Bb) (hN0 : ∀ t, ‖N t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ → ‖N t y1 - N t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    (hmap : CL * (ε * Bb + (K * ε ^ 2 + K * (r + ε) * r)) ≤ r) (hq : CL * K * (2 * r + ε) < 1) :
    (∃ y : ℝ → X → ℝ, Continuous y ∧ (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ r) ∧
      ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N t (y t))) t) ∧
    ∀ y1 y2 : ℝ → X → ℝ, (∀ t, y1 (t + T) = y1 t) → (∀ t, ‖y1 t‖ ≤ r) →
      (∀ t, HasDerivAt y1 (A *ᵥ y1 t + (ε • b t + N t (y1 t))) t) →
      (∀ t, y2 (t + T) = y2 t) → (∀ t, ‖y2 t‖ ≤ r) →
      (∀ t, HasDerivAt y2 (A *ᵥ y2 t + (ε • b t + N t (y2 t))) t) → y1 = y2 := by
  have hρ : 0 ≤ ρ := hr0.trans hrρ
  set Hb := ε * Bb + (K * ε ^ 2 + K * (r + ε) * r) with hHb
  set F : (ℝ → X → ℝ) → ℝ → X → ℝ := fun y s => ε • b s + N s (y s) with hF
  have hFc : ∀ y : ℝ → X → ℝ, Continuous y → (∀ t, ‖y t‖ ≤ r) → Continuous (F y) :=
    fun y hy hyb => (hb.const_smul ε).add (hNc.comp_continuous (continuous_id.prodMk hy)
      (fun s => Set.mk_mem_prod (Set.mem_univ _) (mem_closedBall_zero_iff.2 ((hyb s).trans hrρ))))
  have hFp : ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) → ∀ s, F y (s + T) = F y s := by
    intro y hy s; simp only [hF, hbp, hNp, hy]
  have hFb : ∀ y : ℝ → X → ℝ, (∀ t, ‖y t‖ ≤ r) → ∀ s, ‖F y s‖ ≤ Hb := by
    intro y hy s
    have h1 : ‖ε • b s‖ ≤ ε * Bb := by
      rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left (hBb s) hε
    have h2 := norm_N_le hρ hN0 hNL s ((hy s).trans hrρ)
    have h3 : K * ε ^ 2 + K * (‖y s‖ + ε) * ‖y s‖ ≤ K * ε ^ 2 + K * (r + ε) * r := by
      have := hy s; have := norm_nonneg (y s); gcongr
    exact (norm_add_le _ _).trans (add_le_add h1 (h2.trans h3))
  have hFL : ∀ y1 y2 : ℝ → X → ℝ, (∀ t, ‖y1 t‖ ≤ r) → (∀ t, ‖y2 t‖ ≤ r) → ∀ D, 0 ≤ D →
      (∀ t, ‖y1 t - y2 t‖ ≤ D) → ∀ s, ‖F y1 s - F y2 s‖ ≤ K * (2 * r + ε) * D := by
    intro y1 y2 h1 h2 D hD hd s
    have e : F y1 s - F y2 s = N s (y1 s) - N s (y2 s) := by simp only [hF]; abel
    rw [e]
    refine (hNL s _ _ ((h1 s).trans hrρ) ((h2 s).trans hrρ)).trans ?_
    have : K * (‖y1 s‖ + ‖y2 s‖ + ε) ≤ K * (2 * r + ε) := by
      have := h1 s; have := h2 s; gcongr; linarith
    exact mul_le_mul this (hd s) (norm_nonneg _) (by positivity)
  -- the operator on solutions
  have hGsol : ∀ y : ℝ → X → ℝ, Continuous y → (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ r) → ∀ t,
      HasDerivAt (green A Minv T (F y)) (A *ᵥ green A Minv T (F y) t + F y t) t :=
    fun y hy hyp hyb t => green_hasDerivAt hL hR (hFc y hy hyb) (hFp y hyp) t
  -- the closed set
  set S : Set (ℝ →ᵇ (X → ℝ)) := {y | (∀ t, y (t + T) = y t) ∧ ∀ t, ‖y t‖ ≤ r} with hS
  have hev : ∀ t, Continuous fun y : ℝ →ᵇ (X → ℝ) => y t := fun t =>
    (continuous_apply t).comp BoundedContinuousFunction.continuous_coe
  have hSc : IsClosed S := by
    have e : S = (⋂ t, {y : ℝ →ᵇ (X → ℝ) | y (t + T) = y t}) ∩
        ⋂ t, {y : ℝ →ᵇ (X → ℝ) | ‖y t‖ ≤ r} := by
      ext y; simp [hS]
    rw [e]
    exact (isClosed_iInter fun t => isClosed_eq (hev _) (hev _)).inter
      (isClosed_iInter fun t => isClosed_le (hev t).norm continuous_const)
  have : CompleteSpace S := hSc.completeSpace_coe
  have : Nonempty S := ⟨⟨0, fun t => rfl, fun t => by simpa using hr0⟩⟩
  have hGc : ∀ y : ℝ →ᵇ (X → ℝ), y ∈ S → Continuous (green A Minv T (F y)) := fun y hy =>
    continuous_iff_continuousAt.2 fun t => (hGsol y y.continuous hy.1 hy.2 t).continuousAt
  have hGb : ∀ y : ℝ →ᵇ (X → ℝ), y ∈ S → ∀ t, ‖green A Minv T (F y) t‖ ≤ r := fun y hy t =>
    (hCL _ _ (hFc y y.continuous hy.2) (hFb y hy.2) t).trans hmap
  let Φ : S → S := fun y => ⟨BoundedContinuousFunction.ofNormedAddCommGroup
    (green A Minv T (F y.1)) (hGc y.1 y.2) r (hGb y.1 y.2),
    fun t => green_periodic A Minv T (hFc y.1 y.1.continuous y.2.2) (hFp y.1 y.2.1) t, hGb y.1 y.2⟩
  have hΦ : ∀ y : S, ⇑(Φ y).1 = green A Minv T (F y.1) := fun y => rfl
  set q := CL * K * (2 * r + ε) with hqd
  have hq0 : 0 ≤ q := by positivity
  have hcontr : ContractingWith ⟨q, hq0⟩ Φ := by
    refine ⟨by exact_mod_cast hq, LipschitzWith.of_dist_le_mul fun y1 y2 => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq]
    show dist (Φ y1).1 (Φ y2).1 ≤ q * dist y1.1 y2.1
    have hD := dist_nonneg (x := y1.1) (y := y2.1)
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun t => ?_
    rw [hΦ, hΦ, dist_eq_norm, green_sub A Minv T (hFc _ y1.1.continuous y1.2.2)
      (hFc _ y2.1.continuous y2.2.2)]
    have hd : ∀ t, ‖y1.1 t - y2.1 t‖ ≤ dist y1.1 y2.1 := fun t => by
      rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist t
    have := hCL _ _ ((hFc _ y1.1.continuous y1.2.2).sub (hFc _ y2.1.continuous y2.2.2))
      (hFL _ _ y1.2.2 y2.2.2 _ hD hd) t
    calc ‖green A Minv T (fun s => F y1.1 s - F y2.1 s) t‖
        ≤ CL * (K * (2 * r + ε) * dist y1.1 y2.1) := this
      _ = q * dist y1.1 y2.1 := by rw [hqd]; ring
  -- bounded continuous version of a solution
  have hsolS : ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ r) →
      (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N t (y t))) t) →
      ∃ z : S, ⇑z.1 = y ∧ Function.IsFixedPt Φ z := by
    intro y hyp hyb hyd
    have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hyd t).continuousAt
    refine ⟨⟨BoundedContinuousFunction.ofNormedAddCommGroup y hyc r hyb, hyp, hyb⟩, rfl, ?_⟩
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro t
    show green A Minv T (F y) t = y t
    exact (periodic_eq_green hL hR (hFc y hyc hyb) (hFp y hyp) hyd hyp t).symm
  refine ⟨?_, ?_⟩
  · set z := ContractingWith.fixedPoint Φ hcontr
    have hz : Φ z = z := ContractingWith.fixedPoint_isFixedPt (f := Φ) hcontr
    have hzf : ⇑z.1 = green A Minv T (F z.1) := by rw [← hΦ, hz]
    refine ⟨z.1, z.1.continuous, z.2.1, z.2.2, fun t => ?_⟩
    have := hGsol z.1 z.1.continuous z.2.1 z.2.2 t
    rw [← hzf] at this
    exact this
  · intro y1 y2 h1p h1b h1d h2p h2b h2d
    obtain ⟨z1, hz1, hf1⟩ := hsolS y1 h1p h1b h1d
    obtain ⟨z2, hz2, hf2⟩ := hsolS y2 h2p h2b h2d
    have := ContractingWith.fixedPoint_unique' hcontr hf1 hf2
    rw [← hz1, ← hz2, this]

/-- First-order expansion of any small periodic solution: `‖y − ε y_p‖ ≤ C_L(Kε² + K(r + ε)r)`
where `y_p` is the periodic solution of `ẏ_p = A y_p + b`. -/
@[tmio T, powerlib_foundation] theorem orbit_expansion {A Minv : Matrix X X ℝ} {T : ℝ}
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1) {b : ℝ → X → ℝ}
    (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t) {N : ℝ → (X → ℝ) → X → ℝ}
    {CL K ρ r ε : ℝ}
    (hNc : ContinuousOn (fun p : ℝ × (X → ℝ) => N p.1 p.2) (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ t y, N (t + T) y = N t y)
    (hCL : ∀ (h : ℝ → X → ℝ) (H : ℝ), Continuous h → (∀ s, ‖h s‖ ≤ H) →
      ∀ t, ‖green A Minv T h t‖ ≤ CL * H)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hrρ : r ≤ ρ) (hr0 : 0 ≤ r) (hN0 : ∀ t, ‖N t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ → ‖N t y1 - N t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    {y : ℝ → X → ℝ} (hyp : ∀ t, y (t + T) = y t) (hyb : ∀ t, ‖y t‖ ≤ r)
    (hyd : ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N t (y t))) t)
    {yp : ℝ → X → ℝ} (hpp : ∀ t, yp (t + T) = yp t) (hpd : ∀ t, HasDerivAt yp (A *ᵥ yp t + b t) t)
    (t : ℝ) : ‖y t - ε • yp t‖ ≤ CL * (K * ε ^ 2 + K * (r + ε) * r) := by
  have hρ : 0 ≤ ρ := hr0.trans hrρ
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hyd t).continuousAt
  have hyin : ∀ s, (s, y s) ∈ Set.univ ×ˢ Metric.closedBall (0 : X → ℝ) ρ := fun s =>
    Set.mk_mem_prod (Set.mem_univ _) (mem_closedBall_zero_iff.2 ((hyb s).trans hrρ))
  have hNyc : Continuous (fun s => N s (y s)) := hNc.comp_continuous (continuous_id.prodMk hyc) hyin
  have hFc : Continuous (fun s => ε • b s + N s (y s)) := (hb.const_smul ε).add hNyc
  have hFp : ∀ s, ε • b (s + T) + N (s + T) (y (s + T)) = ε • b s + N s (y s) := fun s => by
    rw [hbp, hNp, hyp]
  rw [periodic_eq_green hL hR hFc hFp hyd hyp t, periodic_eq_green hL hR hb hbp hpd hpp t,
    ← green_smul A Minv T ε hb, green_sub A Minv T (h2 := fun s => ε • b s) hFc (hb.const_smul ε)]
  have e : (fun s => ε • b s + N s (y s) - ε • b s) = fun s => N s (y s) := by
    funext s; abel
  rw [e]
  refine hCL _ _ hNyc (fun s => ?_) t
  refine (norm_N_le hρ hN0 hNL s ((hyb s).trans hrρ)).trans ?_
  have := hyb s; have := norm_nonneg (y s); gcongr

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem exists_bound_of_periodic_vec {b : ℝ → X → ℝ} {T : ℝ}
    (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t) (hT : 0 < T) : ∃ B, ∀ t, ‖b t‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hb.continuousOn
  refine ⟨B, fun t => ?_⟩
  obtain ⟨y, hy, hty⟩ := (show Function.Periodic b T from hbp).exists_mem_Ico₀ hT t
  rw [hty]
  exact hB y (Ico_subset_Icc_self hy)

/-- The forced periodic orbit for small `ε`: existence in the ball of radius `cε`, uniqueness
there, and the first-order expansion `‖y − ε y_p‖ ≤ C ε²`. -/
@[tmio T, powerlib_foundation] theorem forced_orbit {A Minv : Matrix X X ℝ} {T : ℝ} (hT : 0 < T)
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1) {b : ℝ → X → ℝ}
    (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t) {N : ℝ → ℝ → (X → ℝ) → X → ℝ}
    {K ρ ε0 : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hε0 : 0 < ε0)
    (hNc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => N ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ ε t y, N ε (t + T) y = N ε t y)
    (hN0 : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖N ε t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
      ‖N ε t y1 - N ε t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖) :
    ∃ c C ε1, 0 ≤ c ∧ 0 ≤ C ∧ 0 < ε1 ∧ ε1 ≤ ε0 ∧ c * ε1 ≤ ρ ∧ ∀ ε, 0 < ε → ε ≤ ε1 →
      (∃ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) ∧
      (∀ y1 y2 : ℝ → X → ℝ, (∀ t, y1 (t + T) = y1 t) → (∀ t, ‖y1 t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y1 (A *ᵥ y1 t + (ε • b t + N ε t (y1 t))) t) →
        (∀ t, y2 (t + T) = y2 t) → (∀ t, ‖y2 t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y2 (A *ᵥ y2 t + (ε • b t + N ε t (y2 t))) t) → y1 = y2) ∧
      ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
        ∀ yp : ℝ → X → ℝ, (∀ t, yp (t + T) = yp t) → (∀ t, HasDerivAt yp (A *ᵥ yp t + b t) t) →
        ∀ t, ‖y t - ε • yp t‖ ≤ C * ε ^ 2 := by
  obtain ⟨CL, hCL0, hCL⟩ := green_bound A Minv hT.le
  obtain ⟨Bb0, hBb0⟩ := exists_bound_of_periodic_vec hb hbp hT
  set Bb := max Bb0 0
  have hBb : ∀ t, ‖b t‖ ≤ Bb := fun t => (hBb0 t).trans (le_max_left _ _)
  have hBb0' : 0 ≤ Bb := le_max_right _ _
  set c := 2 * CL * (Bb + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  set κ := K * (1 + (c + 1) * c) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set a := (2 * c + 1) * CL * K with ha
  have ha0 : 0 ≤ a := by positivity
  set ε1 := min ε0 (min (ρ / (c + 1)) (min (1 / (a + 1)) (1 / (κ + 1)))) with hε1
  have hρc : 0 < ρ / (c + 1) := by positivity
  have hε1p : 0 < ε1 := lt_min hε0 (lt_min hρc (lt_min (by positivity) (by positivity)))
  have hε1a : ε1 ≤ ε0 := min_le_left _ _
  have hε1b : ε1 ≤ ρ / (c + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hε1c : ε1 ≤ 1 / (a + 1) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε1d : ε1 ≤ 1 / (κ + 1) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcρ : ∀ ε, 0 ≤ ε → ε ≤ ε1 → c * ε ≤ ρ := by
    intro ε hε h
    have h1 : (c + 1) * ε ≤ ρ := by
      have := h.trans hε1b
      rw [le_div_iff₀ (by positivity)] at this; linarith
    nlinarith
  refine ⟨c, CL * κ, ε1, hc0, by positivity, hε1p, hε1a, hcρ ε1 hε1p.le le_rfl, fun ε hε hεe => ?_⟩
  have hεa : a * ε < 1 := by
    have h := hεe.trans hε1c
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hεκ : κ * ε ≤ 1 := by
    have h := hεe.trans hε1d
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hε0' : ε ≤ ε0 := hεe.trans hε1a
  have hr0 : 0 ≤ c * ε := by positivity
  have hrρ := hcρ ε hε.le hεe
  have hmap : CL * (ε * Bb + (K * ε ^ 2 + K * (c * ε + ε) * (c * ε))) ≤ c * ε := by
    have e : K * ε ^ 2 + K * (c * ε + ε) * (c * ε) = κ * ε * ε := by rw [hκ]; ring
    rw [e]
    have h1 : κ * ε * ε ≤ ε := by nlinarith
    calc CL * (ε * Bb + κ * ε * ε) ≤ CL * (ε * Bb + ε) := by gcongr
      _ = c * ε / 2 := by rw [hc]; ring
      _ ≤ c * ε := by linarith
  have hq : CL * K * (2 * (c * ε) + ε) < 1 := by
    have : CL * K * (2 * (c * ε) + ε) = a * ε := by rw [ha]; ring
    rw [this]; exact hεa
  obtain ⟨hex, huniq⟩ := orbit_contraction (N := N ε) hL hR hb hbp (hNc ε hε.le hε0') (hNp ε) hCL hCL0 hK
    hε.le hr0 hrρ hBb (hN0 ε hε.le hε0') (hNL ε hε.le hε0') hmap hq
  refine ⟨?_, huniq, ?_⟩
  · obtain ⟨y, -, hyp, hyb, hyd⟩ := hex
    exact ⟨y, hyp, hyb, hyd⟩
  · intro y hyp hyb hyd yp hpp hpd t
    refine (orbit_expansion hL hR hb hbp (hNc ε hε.le hε0') (hNp ε) hCL hK hε.le hrρ hr0
      (hN0 ε hε.le hε0') (hNL ε hε.le hε0') hyp hyb hyd hpp hpd t).trans (le_of_eq ?_)
    rw [hκ]; ring

end powerlib.ParametricResonance.ForcedOrbit
