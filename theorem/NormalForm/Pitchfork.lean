import theorem.NormalForm.Fold
import theorem.NormalForm.Logistic
import theorem.Flow.Certificate
import theorem.Dynamics.CriticalLinearization
import theorem.Potential.DoubleWell
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Transcritical and pitchfork normal forms

Equilibria, exchange of stability, the degenerate cubic point, the `ℤ₂` symmetry, the basin of
the supercritical branch and the pitchfork barrier of the truncated one-dimensional normal forms.

Model boundary.
* One state `x` (coordinate `x 0` of `State 1`), constant parameter `μ ∈ ℝ`, continuous time, no
  input, noise, delay or saturation. The vector fields are exactly
  transcritical `ẋ = μ x − x²` (`transField`), supercritical pitchfork `ẋ = μ x − x³`
  (`superField`), subcritical pitchfork `ẋ = μ x + x³` (`subField`),
  with no higher-order remainder. Conclusions are equilibrium sets and trajectory-level
  stability of those equilibria for the lifted `State 1` systems.
* Truncated normal forms, no model family; all results remain public foundation support. Global
  asymptotic stability is `powerlib.Flow.GloballyAsymptoticallyStable` (equilibrium, forward
  completeness and LeanForControl's `GlobalAsymptoticStable`).

Source: work-sync theory/T-pitchfork-bifurcation.md §1.1–1.3, theory/T-bifurcation.md §1.4,
theory/T-attractors-basins.md (codes example (a): 1D pitchfork bistable, basin boundary 0),
theory/T-fold-critical-scaling.md §2.3.

Results.
* Transcritical: equilibria `0, μ` (`transField_eq_zero_iff`); exchange of stability
  (`f_x(0) = μ`, `f_x(μ) = −μ`; `trans_stability_neg`, `trans_stability_pos`).
* Supercritical pitchfork: equilibria `0` and `±√μ` (`μ > 0`, `superField_eq_zero_iff`);
  `f_x = μ − 3x²` (`deriv_superField`), so `f_x(0) = μ` and `f_x(±√μ) = −2μ`
  (`super_slope_sqrt`, `super_slope_neg_sqrt`); `0` is locally exponentially stable for
  `μ < 0` and unstable for `μ > 0` (`super_origin_stable`, `super_origin_unstable`), where `±√μ`
  are locally exponentially stable (`super_branch_stable`).
* At `μ = 0` the field is the critical cubic `ẋ = −x³` (`superSystem_zero_eq_cubicField`,
  `Dynamics.cubicField (−1)` of `theorem/Dynamics/CriticalLinearization.lean`): the origin is
  globally asymptotically stable (`super_zero_globallyAsymptoticallyStable`, strict Lyapunov
  function `x²`) but **not** locally exponentially stable, its Jacobian being zero
  (`super_zero_not_locallyExponentiallyStable`).
* Subcritical pitchfork: equilibria `0` and `±√(−μ)` (`μ < 0`, `subField_eq_zero_iff`), the side
  branches are unstable (`f_x = −2μ > 0`, `sub_branch_unstable`); the origin is locally
  exponentially stable for `μ < 0` and unstable for `μ > 0` (`sub_origin_stable`,
  `sub_origin_unstable`).
* `ℤ₂` symmetry: an odd field `f(−x) = −f(x)` has `f(0) = 0` and all even-order derivatives
  vanish at `0` (`odd_apply_zero`, `odd_iteratedDeriv_even_zero`); both pitchfork fields are odd
  (`superField_odd`, `subField_odd`).
* Basin of the supercritical branch: for `μ > 0` every forward-complete solution with
  `x(t₀) > 0` converges to `√μ`: the square `x²` solves the logistic equation
  (`super_sq_isIntegralCurveOn`), whose explicit solution and limit in
  `theorem/NormalForm/Logistic.lean` give `super_bernoulli` (`w = 1/x²`) and `super_tendsto_sqrt`.
* Potential of the supercritical pitchfork, `V(x) = −μx²/2 + x⁴/4` (`potential`): the double
  well `Potential.doubleWell μ 1` of `theorem/Potential/DoubleWell.lean`, so
  `V(0) − V(±√μ) = μ²/4` is `Potential.doubleWell_barrier` at `a = μ ≥ 0`, `b = 1`.

Potential shapes: the fold potential `−μx + x³/3` and its barrier `(4/3) μ^{3/2}` are in
`theorem/NormalForm/Fold.lean`.

Corrections. (T-fold-critical-scaling §2.3 contrasts the fold barrier exponent `3/2` with
"`1` (pitchfork)"): for the pitchfork normal form the barrier is `μ²/4`, so the exponent is `2`,
not `1` (`Potential.doubleWell_barrier` with `b = 1`).
-/

noncomputable section
namespace powerlib.NormalForm.Pitchfork
open Set Filter Topology
open powerlib.Dynamics (State)

/-! ## Transcritical normal form -/

/-- The transcritical normal form `x ↦ μ x − x²`. -/
def transField (μ : ℝ) (x : ℝ) : ℝ := μ * x - x ^ 2

@[tmio T, powerlib_foundation] theorem transField_contDiff (μ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (transField μ) := by
  unfold transField; fun_prop

@[tmio M, powerlib_foundation] theorem hasDerivAt_transField (μ x : ℝ) :
    HasDerivAt (transField μ) (μ - 2 * x) x := by
  have h := ((hasDerivAt_id' x).const_mul μ).sub (hasDerivAt_pow 2 x)
  unfold transField
  convert h using 1
  push_cast; ring

@[tmio M, powerlib_foundation] theorem deriv_transField (μ x : ℝ) : deriv (transField μ) x = μ - 2 * x :=
  (hasDerivAt_transField μ x).deriv

@[tmio M, powerlib_foundation] theorem transField_eq_zero_iff (μ x : ℝ) :
    transField μ x = 0 ↔ x = 0 ∨ x = μ := by
  unfold transField
  constructor
  · intro h
    have : x * (μ - x) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> ring

/-- Exchange of stability, `μ < 0`: the origin is stable and `x = μ` is unstable. -/
@[tmio TM, powerlib_foundation] theorem trans_stability_neg {μ : ℝ} (hμ : μ < 0) :
    LocallyExponentiallyStable (lift (transField μ)) (embed 0) ∧
      Unstable (lift (transField μ)) (embed μ) :=
  ⟨lift_locallyExponentiallyStable (transField_contDiff μ) (by simp [transField])
      (by rw [deriv_transField]; linarith),
    lift_unstable (transField_contDiff μ) (by simp [transField]; ring)
      (by rw [deriv_transField]; linarith)⟩

/-- Exchange of stability, `μ > 0`: the origin is unstable and `x = μ` is stable. -/
@[tmio TM, powerlib_foundation] theorem trans_stability_pos {μ : ℝ} (hμ : 0 < μ) :
    Unstable (lift (transField μ)) (embed 0) ∧
      LocallyExponentiallyStable (lift (transField μ)) (embed μ) :=
  ⟨lift_unstable (transField_contDiff μ) (by simp [transField])
      (by rw [deriv_transField]; linarith),
    lift_locallyExponentiallyStable (transField_contDiff μ) (by simp [transField]; ring)
      (by rw [deriv_transField]; linarith)⟩

/-! ## Supercritical pitchfork `ẋ = μ x − x³` -/

/-- The supercritical pitchfork normal form `x ↦ μ x − x³`. -/
def superField (μ : ℝ) (x : ℝ) : ℝ := μ * x - x ^ 3

/-- The supercritical pitchfork as a vector field on `State 1`. -/
def superSystem (μ : ℝ) : State 1 → State 1 := lift (superField μ)

@[tmio M, powerlib_foundation] theorem superField_contDiff (μ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (superField μ) := by
  unfold superField; fun_prop

@[tmio M, powerlib_foundation] theorem hasDerivAt_superField (μ x : ℝ) :
    HasDerivAt (superField μ) (μ - 3 * x ^ 2) x := by
  have h := ((hasDerivAt_id' x).const_mul μ).sub (hasDerivAt_pow 3 x)
  unfold superField
  convert h using 1
  push_cast; ring

@[tmio M, powerlib_foundation] theorem deriv_superField (μ x : ℝ) :
    deriv (superField μ) x = μ - 3 * x ^ 2 :=
  (hasDerivAt_superField μ x).deriv

@[tmio M, powerlib_foundation] theorem superField_eq_zero_iff (μ x : ℝ) :
    superField μ x = 0 ↔ x = 0 ∨ (0 ≤ μ ∧ (x = √μ ∨ x = -√μ)) := by
  have hfac : superField μ x = x * Fold.field μ x := by simp [superField, Fold.field]; ring
  rw [hfac, mul_eq_zero, Fold.field_eq_zero_iff]

/-- Linearization slope at the branch `√μ`: `f_x(√μ) = −2μ` (`μ ≥ 0`). -/
@[tmio M, powerlib_foundation] theorem super_slope_sqrt {μ : ℝ} (hμ : 0 ≤ μ) :
    deriv (superField μ) √μ = -2 * μ := by
  rw [deriv_superField, Real.sq_sqrt hμ]
  ring

/-- Linearization slope at the branch `−√μ`: `f_x(−√μ) = −2μ` (`μ ≥ 0`). -/
@[tmio M, powerlib_foundation] theorem super_slope_neg_sqrt {μ : ℝ} (hμ : 0 ≤ μ) :
    deriv (superField μ) (-√μ) = -2 * μ := by
  rw [deriv_superField, neg_sq, Real.sq_sqrt hμ]
  ring

@[tmio TM, powerlib_foundation] theorem super_origin_stable {μ : ℝ} (hμ : μ < 0) :
    LocallyExponentiallyStable (superSystem μ) (embed 0) :=
  lift_locallyExponentiallyStable (superField_contDiff μ) (by simp [superField])
    (by rw [deriv_superField]; linarith)

@[tmio TM, powerlib_foundation] theorem super_origin_unstable {μ : ℝ} (hμ : 0 < μ) :
    Unstable (superSystem μ) (embed 0) :=
  lift_unstable (superField_contDiff μ) (by simp [superField])
    (by rw [deriv_superField]; linarith)

@[tmio TM, powerlib_foundation] theorem super_branch_stable {μ : ℝ} (hμ : 0 < μ) :
    LocallyExponentiallyStable (superSystem μ) (embed √μ) ∧
      LocallyExponentiallyStable (superSystem μ) (embed (-√μ)) := by
  have h1 := super_slope_sqrt hμ.le
  have h2 := super_slope_neg_sqrt hμ.le
  refine ⟨lift_locallyExponentiallyStable (superField_contDiff μ)
      ((superField_eq_zero_iff μ _).mpr (Or.inr ⟨hμ.le, Or.inl rfl⟩)) (by rw [h1]; linarith),
    lift_locallyExponentiallyStable (superField_contDiff μ)
      ((superField_eq_zero_iff μ _).mpr (Or.inr ⟨hμ.le, Or.inr rfl⟩)) (by rw [h2]; linarith)⟩

/-! ### The degenerate point `μ = 0`: asymptotic but not exponential stability -/

/-- At `μ = 0` the supercritical pitchfork is the critical cubic field `ẋ = −x³`
(`Dynamics.cubicField (−1)` on `ℝ¹`). -/
@[tmio M, powerlib_foundation] theorem superSystem_zero_eq_cubicField :
    superSystem 0 = Dynamics.cubicField (-1) := by
  funext x
  ext i
  fin_cases i
  simp [superSystem, superField, Dynamics.cubicField, norm_state1]
  ring

/-- At `μ = 0` the origin of `ẋ = −x³` is globally asymptotically stable
(`Dynamics.cubic_neg_globallyAsymptoticallyStable`). -/
@[tmio TM, powerlib_foundation] theorem super_zero_globallyAsymptoticallyStable :
    Flow.GloballyAsymptoticallyStable (superSystem 0) 0 := by
  rw [superSystem_zero_eq_cubicField]
  exact Dynamics.cubic_neg_globallyAsymptoticallyStable one_pos

/-- At `μ = 0` the origin is not locally exponentially stable: the Jacobian of `ẋ = −x³` at `0`
is zero (`Dynamics.not_locallyExponentiallyStable_of_fderiv_apply_eq_zero_local`). -/
@[tmio TM, powerlib_foundation] theorem super_zero_not_locallyExponentiallyStable :
    ¬ LocallyExponentiallyStable (superSystem 0) (embed 0) := by
  rw [superSystem_zero_eq_cubicField, embed_zero]
  refine Dynamics.not_locallyExponentiallyStable_of_fderiv_apply_eq_zero_local isOpen_univ
    (Set.mem_univ _) (Dynamics.cubicField_contDiff _).contDiffOn (v := embed 1) ?_ ?_
  · rw [Ne, ← embed_zero, embed_eq_iff]; norm_num
  · rw [Dynamics.cubicField_jacobian]; simp

/-! ### Basin of the positive branch -/

/-- The square `ρ = x²` of a solution of `ẋ = μx − x³` solves the logistic amplitude equation
`ρ̇ = 2μρ − 2ρ²` (`Logistic.field μ (−1)`). -/
@[tmio M, powerlib_foundation] theorem super_sq_isIntegralCurveOn {μ : ℝ} {ψ : ℝ → ℝ} {s : Set ℝ}
    (hψ : IsIntegralCurveOn ψ (fun _ r => superField μ r) s) :
    IsIntegralCurveOn (fun t => ψ t ^ 2) (fun _ r => Logistic.field μ (-1) r) s := by
  intro t ht
  convert (hψ t ht).pow 2 using 1
  simp only [Logistic.field, superField]
  push_cast; ring

/-- For `μ > 0`, every solution with `x(a) > 0` satisfies
`1/x² − 1/μ = (1/x(a)² − 1/μ) e^{−2μ(t−a)}` (`Logistic.reciprocal_formula` for `ρ = x²`,
`l = −1`). -/
@[tmio M, powerlib_foundation] theorem super_bernoulli {μ : ℝ} (hμ : 0 < μ) {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : IsIntegralCurveOn ψ (fun _ r => superField μ r) (Icc a b)) (ha : 0 < ψ a) :
    ∀ t ∈ Icc a b, 1 / ψ t ^ 2 - 1 / μ = (1 / ψ a ^ 2 - 1 / μ) * Real.exp (-2 * μ * (t - a)) := by
  intro t ht
  have h := Logistic.reciprocal_formula hμ.ne' (super_sq_isIntegralCurveOn hψ) (by positivity)
    t ht
  simpa [sub_eq_add_neg, neg_div] using h

/-- For `μ > 0` the positive half-line lies in the basin of `√μ`: every forward-complete
solution with `x(a) > 0` converges to `√μ` (`Logistic.tendsto_level` for `ρ = x²`). -/
@[tmio TM, powerlib_foundation] theorem super_tendsto_sqrt {μ : ℝ} (hμ : 0 < μ) {ψ : ℝ → ℝ} {a : ℝ}
    (hψ : IsIntegralCurveOn ψ (fun _ r => superField μ r) (Ici a)) (ha : 0 < ψ a) :
    Tendsto ψ atTop (𝓝 √μ) := by
  have hlim := Logistic.tendsto_level hμ (by norm_num) (super_sq_isIntegralCurveOn hψ)
    (by positivity)
  rw [div_neg, div_one, neg_neg] at hlim
  refine ((Real.continuous_sqrt.tendsto μ).comp hlim).congr'
    (eventually_atTop.mpr ⟨a, fun t ht => ?_⟩)
  have hpos := pos_of_pos (superField_contDiff μ) (by simp [superField])
    (hψ.mono Icc_subset_Ici_self) ha t ⟨ht, le_rfl⟩
  simp [Real.sqrt_sq hpos.le]

/-! ## Subcritical pitchfork `ẋ = μ x + x³` -/

/-- The subcritical pitchfork normal form `x ↦ μ x + x³`. -/
def subField (μ : ℝ) (x : ℝ) : ℝ := μ * x + x ^ 3

/-- The subcritical pitchfork as a vector field on `State 1`. -/
def subSystem (μ : ℝ) : State 1 → State 1 := lift (subField μ)

@[tmio M, powerlib_foundation] theorem subField_contDiff (μ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (subField μ) := by
  unfold subField; fun_prop

@[tmio M, powerlib_foundation] theorem hasDerivAt_subField (μ x : ℝ) :
    HasDerivAt (subField μ) (μ + 3 * x ^ 2) x := by
  have h := ((hasDerivAt_id' x).const_mul μ).add (hasDerivAt_pow 3 x)
  unfold subField
  convert h using 1
  push_cast; ring

@[tmio M, powerlib_foundation] theorem deriv_subField (μ x : ℝ) :
    deriv (subField μ) x = μ + 3 * x ^ 2 :=
  (hasDerivAt_subField μ x).deriv

@[tmio M, powerlib_foundation] theorem subField_eq_zero_iff (μ x : ℝ) :
    subField μ x = 0 ↔ x = 0 ∨ (μ ≤ 0 ∧ (x = √(-μ) ∨ x = -√(-μ))) := by
  have hfac : subField μ x = -(x * Fold.field (-μ) x) := by simp [subField, Fold.field]; ring
  rw [hfac, neg_eq_zero, mul_eq_zero, Fold.field_eq_zero_iff, neg_nonneg]

/-- Subcritical side branches `±√(−μ)` (`μ < 0`) have slope `−2μ > 0` and are unstable. -/
@[tmio TM, powerlib_foundation] theorem sub_branch_unstable {μ : ℝ} (hμ : μ < 0) :
    Unstable (subSystem μ) (embed √(-μ)) ∧
      Unstable (subSystem μ) (embed (-√(-μ))) := by
  have hs : √(-μ) ^ 2 = -μ := Real.sq_sqrt (by linarith)
  refine ⟨lift_unstable (subField_contDiff μ)
      ((subField_eq_zero_iff μ _).mpr (Or.inr ⟨hμ.le, Or.inl rfl⟩))
      (by rw [deriv_subField, hs]; linarith),
    lift_unstable (subField_contDiff μ)
      ((subField_eq_zero_iff μ _).mpr (Or.inr ⟨hμ.le, Or.inr rfl⟩))
      (by rw [deriv_subField, neg_sq, hs]; linarith)⟩

@[tmio TM, powerlib_foundation] theorem sub_origin_stable {μ : ℝ} (hμ : μ < 0) :
    LocallyExponentiallyStable (subSystem μ) (embed 0) :=
  lift_locallyExponentiallyStable (subField_contDiff μ) (by simp [subField])
    (by rw [deriv_subField]; linarith)

@[tmio TM, powerlib_foundation] theorem sub_origin_unstable {μ : ℝ} (hμ : 0 < μ) :
    Unstable (subSystem μ) (embed 0) :=
  lift_unstable (subField_contDiff μ) (by simp [subField])
    (by rw [deriv_subField]; linarith)

/-! ## `ℤ₂` symmetry -/

/-- An odd scalar field has the origin as an equilibrium. -/
@[tmio T, powerlib_foundation] theorem odd_apply_zero {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) :
    f 0 = 0 := by
  have := hodd 0
  rw [neg_zero] at this
  linarith

/-- An odd scalar field has vanishing even-order derivatives at the origin. -/
@[tmio T, powerlib_foundation] theorem odd_iteratedDeriv_even_zero {f : ℝ → ℝ}
    (hodd : ∀ x, f (-x) = -f x) (k : ℕ) : iteratedDeriv (2 * k) f 0 = 0 := by
  have hfun : (fun x => f (-x)) = fun x => -f x := funext hodd
  have h := iteratedDeriv_comp_neg (2 * k) f 0
  rw [hfun, iteratedDeriv_fun_neg, neg_zero, pow_mul, neg_one_sq, one_pow, one_smul] at h
  linarith

@[tmio M, powerlib_foundation] theorem superField_odd (μ x : ℝ) : superField μ (-x) = -superField μ x := by
  simp [superField]; ring

@[tmio M, powerlib_foundation] theorem subField_odd (μ x : ℝ) : subField μ (-x) = -subField μ x := by
  simp [subField]; ring

/-! ## Potential -/

/-- The supercritical pitchfork potential `V(x) = −μx²/2 + x⁴/4` (`V' = −(μx − x³)`): the
double well `Potential.doubleWell μ 1`; its barrier `μ²/4` is `Potential.doubleWell_barrier`. -/
abbrev potential (μ : ℝ) : ℝ → ℝ := Potential.doubleWell μ 1

end powerlib.NormalForm.Pitchfork
