import theorem.Asymptotics.Guard.Potential
import theorem.Asymptotics.LaplaceMethod
import theorem.Stochastic.MFPT
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Guard mean first-passage time: the double integral and its bounds at a cut

One-variable real analysis of an explicit double integral, the mean first-passage time (MFPT) of the
truncated subcritical-Hopf amplitude. The integral is the Kramers double integral
`Stochastic.MFPT.kramersT` (the solution of the backward equation, `theorem/Stochastic/MFPT.lean`)
of the effective radial potential `V = U − D̃ log r`, started at the reflecting point `r = 0`
where `V` diverges; as there, that it equals the expected first-passage time of the diffusion
(Dynkin / Itô) is not formalized. This module defines the integral and proves the deterministic
bounds at a cut `a < r_c` from which `Asymptotics/Guard/MFPTExpansion.lean` obtains the two-term
expansions and, as their corollaries, the single-term asymptotics `T_committed / T_guard → 2` and
`T_guard ~ P e^X`.

Model boundary.
* Potential: the truncated subcritical-Hopf potential `U(r) = α r²/2 − l₁ r⁴/4` of
  `Asymptotics/Guard/Potential.lean` (`guardPotential`), `α, l₁ > 0`, well at `r = 0`, barrier
  top at `r_c = √(α/l₁)` (`guardRadius`), barrier height `ΔU = α²/(4 l₁)`.
* MFPT (source §1.2, two-dimensional amplitude measure, natural reflection at `r = 0`):
  `T(r_b) = D̃⁻¹ ∫₀^{r_b} (dy/y) e^{U(y)/D̃} ∫₀^y z e^{−U(z)/D̃} dz` (`guardMFPT α l₁ D̃ r_b`),
  the Kramers MFPT (`γ = 1`, reflecting point `0`, absorbing point `r_b`) of
  `V(r) = U(r) − D̃ log r` (`guardEffPotential`).
  `T_guard = T(r_c)` is the first arrival at the barrier top; `T_committed = T(r_b)` with any
  downstream boundary `r_b > r_c` is committed escape.
* Asymptotic regime (of the consumers in `MFPTExpansion`): noise intensity `D̃ → 0⁺` at fixed
  `α, l₁, r_b`, equivalently `X = ΔU/D̃ → ∞`.

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.2 ("逃逸时间的两种边界，比值恰为 2",
`T_committed / T_guard → 2` and "趋近 2 的方式本身是 `1 + O(X^{−1/2})`"), §1.3 (the potential
`U = αr²/2 − l₁r⁴/4` and `T_guard ∼ (√π/2) √(D̃ l₁)/α² e^X (1 + O(X^{−1/2}))`), §1.5 (`× 2` for
committed escape).

Results.
* `guardMFPT` — the MFPT `T(r_b)`, defined as `Stochastic.MFPT.kramersT` of the effective
  potential; `guardMFPT_eq` writes it with inner integral `K = guardInner` and outer integrand
  `guardIntegrand`, the Kramers outer integrand of `V` (`outerG_guardEffPotential`, with
  `e^{−V/D̃} = |r| e^{−U/D̃}`, `gibbs_guardEffPotential`). The generic Kramers laws apply with
  `θ_r = 0` (`locallyIntegrable_gibbs_guardEffPotential`; `V` is smooth at `r ≠ 0`);
  `guardMFPT_pos` (`T(r_b) > 0`) is `kramersT_pos` at the divergent point `θ = 0`. The asymptotic
  statements are corollaries of the two-term expansions in
  `Asymptotics/Guard/MFPTExpansion.lean`: `tendsto_guardMFPT_ratio` (`T(r_b)/T(r_c) → 2`),
  `tendsto_guardMFPT_ratio_inv`, `guardMFPT_ratio_sub_two_isBigO`, `guardMFPT_guard_isBigO`,
  `tendsto_guardMFPT_guard`, `guardMFPT_committed_isBigO`.
* Bounds at a cut `0 < a < r_c` with reflected cut `ψ(a) = √(2r_c² − a²) ≤ r_b`
  (`guard_exists_cut`), `I = ∫_a^{r_c} y⁻¹ e^{U/D̃}` the barrier weight:
  `K(a) I ≤ ∫_a^{r_c} h ≤ K(r_c) I` (`guard_inside_bounds`);
  `K(ψ(a)) ≤ (1 + κ) K(a)` (`guardInner_reflect_le`); the tails satisfy
  `∫₀^a h + ∫_{ψ(a)}^{r_b} h ≤ ε K(a) I` (`guard_tails_le`), with explicit `κ = guardKappa`,
  `ε = guardEps`, `κ, ε ≥ 0` (`guardKappa_nonneg`, `guardEps_nonneg`) and `κ, ε = o(D̃)`
  (`tendsto_guardKappa_div`, `tendsto_guardEps_div`, from `tendsto_exp_neg_div_div` and
  `tendsto_exp_neg_div_div_div`).
* Gaussian bounds for the inner integral (relative error `O(1/X)`):
  `(D̃/α)(1 − e^{−αa²/(2D̃)}) ≤ K(a)` and `K(r_c) ≤ (D̃/α)(1 + 16 l₁D̃/α²)`
  (`guardInner_ge_gauss`, `guardInner_le_gauss`); `mul_guardPrefactor_eq`:
  `D̃ P = (D̃/α) · r_c⁻¹ · √(π/(α/D̃))/2` with `P = guardPrefactor α l₁ D̃ = (√π/2) √(D̃ l₁)/α²`.
* Supporting facts: `U(z) = ΔU − (l₁/4)(z² − r_c²)²` (`guardPotential_eq_barrier_sub`),
  monotonicity / integrability / two-sided bounds of the inner integral `K` (`guardInner_*`), of
  the outer integrand (`guardIntegrand_*`) and integrability of the weight
  (`intervalIntegrable_guardWeight`).
-/

noncomputable section
namespace powerlib.Asymptotics.Guard

open Real Set Filter Topology MeasureTheory intervalIntegral

/-! ## The mean first-passage time and its two boundary choices -/

/-- Inner integral of the MFPT formula, `K(y) = ∫₀^y z e^{−U(z)/D̃} dz`. -/
def guardInner (α l₁ D y : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..y, z * Real.exp (-(guardPotential α l₁ z / D))

/-- Outer integrand of the MFPT formula, `y⁻¹ e^{U(y)/D̃} K(y)`. -/
def guardIntegrand (α l₁ D y : ℝ) : ℝ :=
  y⁻¹ * Real.exp (guardPotential α l₁ y / D) * guardInner α l₁ D y

/-- Effective radial potential `V(r) = U(r) − D̃ log r` of the two-dimensional amplitude measure:
`e^{−V/D̃} = r e^{−U/D̃}` for `r > 0`; `V → +∞` at the reflecting point `r = 0`. -/
def guardEffPotential (α l₁ D r : ℝ) : ℝ := guardPotential α l₁ r - D * Real.log r

/-- Mean first-passage time to the outer boundary `r_b`: the Kramers MFPT
(`Stochastic.MFPT.kramersT`, `γ = 1`) of the effective potential, reflecting point `0`,
absorbing point `r_b`, started at `0`; explicitly
`T(r_b) = D̃⁻¹ ∫₀^{r_b} (dy/y) e^{U(y)/D̃} ∫₀^y z e^{−U(z)/D̃} dz` (`guardMFPT_eq`).
`r_b = r_c` is the first arrival at the barrier top (`T_guard`); `r_b > r_c` is committed escape
(`T_committed`). -/
def guardMFPT (α l₁ D rb : ℝ) : ℝ :=
  Stochastic.MFPT.kramersT (guardEffPotential α l₁ D) D 1 0 rb 0

variable {α l₁ : ℝ}

/-! ## The guard MFPT as a Kramers MFPT -/

section Kramers

variable {D : ℝ}

/-- `e^{−V/D̃} = |r| e^{−U/D̃}` for `r ≠ 0`. -/
@[tmio M, powerlib_foundation] theorem gibbs_guardEffPotential (hD : D ≠ 0) {z : ℝ} (hz : z ≠ 0) :
    Stochastic.FP.gibbs (guardEffPotential α l₁ D) D z =
      |z| * Real.exp (-(guardPotential α l₁ z / D)) := by
  rw [Stochastic.FP.gibbs, guardEffPotential, ← Real.exp_log_eq_abs hz, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The Gibbs weight of the effective potential is locally integrable, so the generic Kramers laws
of `theorem/Stochastic/MFPT.lean` apply with `θ_r = 0` (`V` is continuous and differentiable at
every `r ≠ 0`). -/
@[tmio M, powerlib_foundation] theorem locallyIntegrable_gibbs_guardEffPotential (hD : D ≠ 0) :
    LocallyIntegrable (Stochastic.FP.gibbs (guardEffPotential α l₁ D) D) := by
  refine (Continuous.locallyIntegrable
    (f := fun z => |z| * Real.exp (-(guardPotential α l₁ z / D)))
    (by unfold guardPotential Potential.doubleWell; fun_prop)).congr ?_
  filter_upwards [(countable_singleton (0 : ℝ)).ae_notMem volume] with z hz
  exact (gibbs_guardEffPotential hD hz).symm

/-- The Kramers outer integrand of the effective potential is `guardIntegrand`. -/
@[tmio M, powerlib_foundation] theorem outerG_guardEffPotential (hD : D ≠ 0) (y : ℝ) :
    Stochastic.MFPT.outerG (guardEffPotential α l₁ D) D 0 y = guardIntegrand α l₁ D y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Stochastic.MFPT.outerG, Stochastic.MFPT.innerI, guardIntegrand]
  have hI : y * Stochastic.MFPT.innerI (guardEffPotential α l₁ D) D 0 y =
      |y| * guardInner α l₁ D y := by
    simp only [Stochastic.MFPT.innerI, guardInner, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(countable_singleton (0 : ℝ)).ae_notMem volume] with z hz0 hz
    rw [gibbs_guardEffPotential hD hz0]
    rcases hy.lt_or_gt with hy | hy
    · rw [uIoc_of_ge hy.le] at hz
      rw [abs_of_neg hy, abs_of_neg (lt_of_le_of_ne hz.2 hz0)]; ring
    · rw [uIoc_of_le hy.le] at hz
      rw [abs_of_pos hy, abs_of_pos hz.1]
  have hE : Real.exp (guardEffPotential α l₁ D y / D) =
      Real.exp (guardPotential α l₁ y / D) * |y|⁻¹ := by
    rw [← Real.exp_log_eq_abs hy, ← Real.exp_neg, ← Real.exp_add, guardEffPotential]
    congr 1
    field_simp
    ring
  have hy' : |y| ≠ 0 := abs_ne_zero.mpr hy
  rw [Stochastic.MFPT.outerG, hE, guardIntegrand,
    show Stochastic.MFPT.innerI (guardEffPotential α l₁ D) D 0 y = |y| * guardInner α l₁ D y / y
      by rw [eq_div_iff hy, mul_comm, hI]]
  field_simp

/-- The guard MFPT as the explicit double integral of the source note. -/
@[tmio M, powerlib_foundation] theorem guardMFPT_eq (α l₁ D rb : ℝ) :
    guardMFPT α l₁ D rb = D⁻¹ * ∫ y in (0 : ℝ)..rb, guardIntegrand α l₁ D y := by
  rcases eq_or_ne D 0 with rfl | hD
  · simp [guardMFPT, Stochastic.MFPT.kramersT]
  · simp only [guardMFPT, Stochastic.MFPT.kramersT, outerG_guardEffPotential hD, one_div]

end Kramers

/-- `U(z) = ΔU − (l₁/4)(z² − r_c²)²`. -/
@[tmio M, powerlib_foundation] theorem guardPotential_eq_barrier_sub (hl : 0 < l₁) (z : ℝ) :
    guardPotential α l₁ z = barrierHeight α l₁ - l₁ / 4 * (z ^ 2 - α / l₁) ^ 2 := by
  simp only [guardPotential, Potential.doubleWell, barrierHeight]; field_simp; ring

/-- `U` is a decreasing function of `(z² − r_c²)²`. -/
@[tmio M, powerlib_foundation] theorem guardPotential_le_of_sq_le (hl : 0 < l₁) {z w : ℝ}
    (h : (z ^ 2 - α / l₁) ^ 2 ≤ (w ^ 2 - α / l₁) ^ 2) :
    guardPotential α l₁ w ≤ guardPotential α l₁ z := by
  rw [guardPotential_eq_barrier_sub hl, guardPotential_eq_barrier_sub hl]
  have : 0 < l₁ / 4 := by positivity
  nlinarith

@[tmio M, powerlib_foundation] theorem guardPotential_le_quad (hl : 0 ≤ l₁) (z : ℝ) :
    guardPotential α l₁ z ≤ α * z ^ 2 / 2 := by
  simp only [guardPotential, Potential.doubleWell]
  nlinarith [pow_nonneg (sq_nonneg z) 2, sq_nonneg (z ^ 2)]

@[tmio M, powerlib_foundation] theorem guardPotential_le_barrier (hl : 0 < l₁) (z : ℝ) :
    guardPotential α l₁ z ≤ barrierHeight α l₁ := by
  have h := Potential.doubleWell_min (a := α) hl z
  rw [neg_div] at h
  rw [guardPotential, barrierHeight]
  linarith

@[tmio M, powerlib_foundation] theorem guardPotential_pos (hl : 0 < l₁) {z : ℝ}
    (hz : 0 < z) (hz2 : z ^ 2 < 2 * (α / l₁)) : 0 < guardPotential α l₁ z := by
  have : guardPotential α l₁ z = z ^ 2 / 4 * (l₁ * (2 * (α / l₁) - z ^ 2)) := by
    simp only [guardPotential, Potential.doubleWell]; field_simp; ring
  rw [this]
  have : 0 < 2 * (α / l₁) - z ^ 2 := by linarith
  positivity

section Inner

variable {D : ℝ}

@[tmio M, powerlib_foundation] theorem continuous_guardInner_integrand (α l₁ D : ℝ) :
    Continuous fun z => z * Real.exp (-(guardPotential α l₁ z / D)) := by
  unfold guardPotential Potential.doubleWell; fun_prop

@[tmio M, powerlib_foundation] theorem hasDerivAt_guardInner (α l₁ D y : ℝ) :
    HasDerivAt (guardInner α l₁ D) (y * Real.exp (-(guardPotential α l₁ y / D))) y :=
  ((continuous_guardInner_integrand α l₁ D).integral_hasStrictDerivAt 0 y).hasDerivAt

@[tmio M, powerlib_foundation] theorem continuous_guardInner (α l₁ D : ℝ) :
    Continuous (guardInner α l₁ D) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_guardInner α l₁ D y).continuousAt

/-- `K(y₂) − K(y₁) = ∫_{y₁}^{y₂} z e^{−U/D̃}`. -/
@[tmio M, powerlib_foundation] theorem guardInner_sub (α l₁ D y₁ y₂ : ℝ) :
    guardInner α l₁ D y₂ - guardInner α l₁ D y₁ =
      ∫ z in y₁..y₂, z * Real.exp (-(guardPotential α l₁ z / D)) := by
  simp only [guardInner]
  rw [integral_interval_sub_left]
  · exact (continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _
  · exact (continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _

@[tmio M, powerlib_foundation] theorem guardInner_mono {y₁ y₂ : ℝ} (h0 : 0 ≤ y₁) (h : y₁ ≤ y₂) :
    guardInner α l₁ D y₁ ≤ guardInner α l₁ D y₂ := by
  have := guardInner_sub α l₁ D y₁ y₂
  have hnn : 0 ≤ ∫ z in y₁..y₂, z * Real.exp (-(guardPotential α l₁ z / D)) :=
    integral_nonneg h fun z hz => mul_nonneg (h0.trans hz.1) (Real.exp_pos _).le
  linarith

@[tmio M, powerlib_foundation] theorem guardInner_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ guardInner α l₁ D y := by
  have := guardInner_mono (α := α) (l₁ := l₁) (D := D) le_rfl hy
  simpa [guardInner] using this

/-- `K(y) ≤ (y²/2)(1 + e^{−U(y)/D̃})`: on `[0, y]` the potential is at least `min(0, U(y))`. -/
@[tmio M, powerlib_foundation] theorem guardInner_le (hl : 0 < l₁) (hD : 0 < D) {y : ℝ} (hy : 0 ≤ y) :
    guardInner α l₁ D y ≤ y ^ 2 / 2 * (1 + Real.exp (-(guardPotential α l₁ y / D))) := by
  have hb : ∀ z ∈ Icc (0 : ℝ) y, z * Real.exp (-(guardPotential α l₁ z / D)) ≤
      z * (1 + Real.exp (-(guardPotential α l₁ y / D))) := by
    intro z hz
    apply mul_le_mul_of_nonneg_left _ hz.1
    -- `(z² − ρ)² ≤ max(ρ², (y² − ρ)²)`
    have hz2 : z ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hz.1 hz.2 2
    have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
    rcases le_or_gt (z ^ 2) (2 * (α / l₁)) with h | h
    · -- `(z² − ρ)² ≤ ρ² = (0² − ρ)²`, so `U(z) ≥ U(0) = 0`
      have h0 : (z ^ 2 - α / l₁) ^ 2 ≤ ((0 : ℝ) ^ 2 - α / l₁) ^ 2 := by nlinarith
      have := guardPotential_le_of_sq_le (α := α) hl h0
      have hU0 : guardPotential α l₁ 0 = 0 := by simp [guardPotential, Potential.doubleWell]
      rw [hU0] at this
      have : Real.exp (-(guardPotential α l₁ z / D)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := div_nonneg this hD.le; linarith)
      linarith [Real.exp_pos (-(guardPotential α l₁ y / D))]
    · -- `z² > 2ρ`: then `(z² − ρ)² ≤ (y² − ρ)²`, so `U(z) ≥ U(y)`
      have h1 : (z ^ 2 - α / l₁) ^ 2 ≤ (y ^ 2 - α / l₁) ^ 2 := by nlinarith
      have := guardPotential_le_of_sq_le (α := α) hl h1
      have : Real.exp (-(guardPotential α l₁ z / D)) ≤ Real.exp (-(guardPotential α l₁ y / D)) :=
        Real.exp_le_exp.mpr (by rw [neg_le_neg_iff]; exact div_le_div_of_nonneg_right this hD.le)
      linarith [Real.exp_pos (-(guardPotential α l₁ y / D))]
  calc guardInner α l₁ D y ≤ ∫ z in (0 : ℝ)..y, z * (1 + Real.exp (-(guardPotential α l₁ y / D))) :=
        integral_mono_on hy ((continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun z : ℝ =>
            z * (1 + Real.exp (-(guardPotential α l₁ y / D)))).intervalIntegrable _ _) hb
    _ = y ^ 2 / 2 * (1 + Real.exp (-(guardPotential α l₁ y / D))) := by
        rw [intervalIntegral.integral_mul_const, integral_id]; ring

/-- `K(a) ≥ (D̃/2) e^{−α/2}` once `D̃ ≤ a²`. -/
@[tmio M, powerlib_foundation] theorem guardInner_ge (hα : 0 ≤ α) (hl : 0 ≤ l₁) (hD : 0 < D) {a : ℝ}
    (ha : 0 ≤ a)
    (hDa : D ≤ a ^ 2) : D / 2 * Real.exp (-(α / 2)) ≤ guardInner α l₁ D a := by
  have hs : √D ≤ a := by
    rw [show a = √(a ^ 2) from (Real.sqrt_sq ha).symm]; exact Real.sqrt_le_sqrt hDa
  have hs0 : 0 ≤ √D := Real.sqrt_nonneg D
  calc D / 2 * Real.exp (-(α / 2)) = ∫ z in (0 : ℝ)..√D, z * Real.exp (-(α / 2)) := by
        rw [intervalIntegral.integral_mul_const, integral_id, Real.sq_sqrt hD.le]; ring
    _ ≤ ∫ z in (0 : ℝ)..√D, z * Real.exp (-(guardPotential α l₁ z / D)) := by
        apply integral_mono_on hs0 ((by fun_prop : Continuous fun z : ℝ =>
            z * Real.exp (-(α / 2))).intervalIntegrable _ _)
          ((continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _)
        intro z hz
        apply mul_le_mul_of_nonneg_left _ hz.1
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff, div_le_iff₀ hD]
        have h1 := guardPotential_le_quad (α := α) hl z
        have h2 : z ^ 2 ≤ D := by
          have := pow_le_pow_left₀ hz.1 hz.2 2; rwa [Real.sq_sqrt hD.le] at this
        nlinarith
    _ ≤ guardInner α l₁ D a := guardInner_mono hs0 hs

@[tmio M, powerlib_foundation] theorem guardInner_sub_le (hD : 0 < D) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hU : ∀ z ∈ Icc a b, guardPotential α l₁ a ≤ guardPotential α l₁ z) :
    guardInner α l₁ D b - guardInner α l₁ D a ≤
      (b - a) * (b * Real.exp (-(guardPotential α l₁ a / D))) := by
  rw [guardInner_sub]
  calc ∫ z in a..b, z * Real.exp (-(guardPotential α l₁ z / D))
      ≤ ∫ z in a..b, b * Real.exp (-(guardPotential α l₁ a / D)) := by
        apply integral_mono_on hab ((continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _)
          intervalIntegrable_const
        intro z hz
        apply mul_le_mul hz.2 _ (Real.exp_pos _).le (ha.trans hab)
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff]; exact div_le_div_of_nonneg_right (hU z hz) hD.le
    _ = (b - a) * (b * Real.exp (-(guardPotential α l₁ a / D))) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

end Inner

section Outer

variable {D : ℝ}

@[tmio M, powerlib_foundation] theorem guardIntegrand_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ guardIntegrand α l₁ D y :=
  mul_nonneg (mul_nonneg (inv_nonneg.2 hy) (Real.exp_pos _).le) (guardInner_nonneg hy)

/-- `y⁻¹ e^{U/D̃} K(y) ≤ (y/2)(e^{U(y)/D̃} + 1)`. -/
@[tmio M, powerlib_foundation] theorem guardIntegrand_le (hl : 0 < l₁) (hD : 0 < D) {y : ℝ} (hy : 0 < y) :
    guardIntegrand α l₁ D y ≤ y / 2 * (Real.exp (guardPotential α l₁ y / D) + 1) := by
  unfold guardIntegrand
  have hK := guardInner_le (α := α) hl hD hy.le
  have e : Real.exp (guardPotential α l₁ y / D) * Real.exp (-(guardPotential α l₁ y / D)) = 1 := by
    rw [← Real.exp_add]; simp
  calc y⁻¹ * Real.exp (guardPotential α l₁ y / D) * guardInner α l₁ D y
      ≤ y⁻¹ * Real.exp (guardPotential α l₁ y / D) *
          (y ^ 2 / 2 * (1 + Real.exp (-(guardPotential α l₁ y / D)))) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
    _ = y / 2 * (Real.exp (guardPotential α l₁ y / D) +
          Real.exp (guardPotential α l₁ y / D) * Real.exp (-(guardPotential α l₁ y / D))) := by
        field_simp
    _ = y / 2 * (Real.exp (guardPotential α l₁ y / D) + 1) := by rw [e]

@[tmio M, powerlib_foundation] theorem continuous_exp_guardPotential (α l₁ D : ℝ) :
    Continuous fun y => Real.exp (guardPotential α l₁ y / D) := by
  unfold guardPotential Potential.doubleWell; fun_prop

@[tmio M, powerlib_foundation] theorem continuousOn_guardIntegrand (α l₁ D : ℝ) :
    ContinuousOn (guardIntegrand α l₁ D) (Ioi 0) := by
  have h1 : ContinuousOn (fun y : ℝ => y⁻¹) (Ioi 0) :=
    continuousOn_inv₀.mono fun y hy => (ne_of_gt hy : y ≠ 0)
  exact (h1.mul (continuous_exp_guardPotential α l₁ D).continuousOn).mul
    (continuous_guardInner α l₁ D).continuousOn

@[tmio M, powerlib_foundation] theorem intervalIntegrable_guardIntegrand (hl : 0 < l₁) (hD : 0 < D)
    {R : ℝ} (hR : 0 ≤ R) : IntervalIntegrable (guardIntegrand α l₁ D) volume 0 R := by
  refine IntervalIntegrable.mono_fun'
    (g := fun _ => R / 2 * (Real.exp (barrierHeight α l₁ / D) + 1)) intervalIntegrable_const ?_ ?_
  · exact ((measurable_inv.mul (continuous_exp_guardPotential α l₁ D).measurable).mul
      (continuous_guardInner α l₁ D).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
    rw [uIoc_of_le hR] at hy
    rw [Real.norm_eq_abs, abs_of_nonneg (guardIntegrand_nonneg hy.1.le)]
    refine (guardIntegrand_le hl hD hy.1).trans ?_
    apply mul_le_mul (by linarith [hy.2]) _ (by positivity) (by linarith [hy.2, hy.1])
    have := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (guardPotential_le_barrier (α := α) hl y) hD.le)
    linarith

@[tmio M, powerlib_foundation] theorem intervalIntegrable_guardIntegrand_of_pos {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : IntervalIntegrable (guardIntegrand α l₁ D) volume a b :=
  ((continuousOn_guardIntegrand α l₁ D).mono fun y hy => by
    simp only [mem_Ioi]
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hy; linarith [hy.1]
    · rw [uIcc_of_ge h] at hy; linarith [hy.1]).intervalIntegrable

/-- `T(r_b) > 0` for `r_b > 0`: `Stochastic.MFPT.kramersT_pos` at the reflecting point `θ = 0`,
where the effective potential diverges. -/
@[tmio M, powerlib_foundation] theorem guardMFPT_pos (hl : 0 < l₁) (hD : 0 < D) {rb : ℝ}
    (hrb : 0 < rb) : 0 < guardMFPT α l₁ D rb := by
  refine Stochastic.MFPT.kramersT_pos (locallyIntegrable_gibbs_guardEffPotential hD.ne') ?_ hD
    one_pos le_rfl hrb
  rw [funext (outerG_guardEffPotential (α := α) (l₁ := l₁) hD.ne')]
  exact intervalIntegrable_guardIntegrand hl hD hrb.le

end Outer

/-! ## Bounds at a cut `0 < a < r_c`: inside the top, across it, tails -/

/-- Relative size of the tails, an explicit upper bound for `(A_tail + B_tail)/(K(a) I)`. -/
def guardEps (α l₁ a rb D : ℝ) : ℝ :=
  (a ^ 2 / 2 + (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2)) *
      (Real.exp (guardPotential α l₁ a / D) + 1) /
    (D / 2 * Real.exp (-(α / 2)) * ((√(α / l₁) - (a + √(α / l₁)) / 2) / √(α / l₁) *
      Real.exp (guardPotential α l₁ ((a + √(α / l₁)) / 2) / D)))

/-- Relative growth of the inner integral across the barrier, an explicit upper bound for
`K(ψ(a))/K(a) − 1`. -/
def guardKappa (α l₁ a D : ℝ) : ℝ :=
  (√(2 * (α / l₁) - a ^ 2) - a) * (√(2 * (α / l₁) - a ^ 2) *
    Real.exp (-(guardPotential α l₁ a / D))) / (D / 2 * Real.exp (-(α / 2)))

section Cut

variable {D : ℝ}

/-- The weight `w(y) = y⁻¹ e^{U(y)/D̃}` is interval integrable on `[a, b]`, `0 < a ≤ b`. -/
@[tmio M, powerlib_foundation] theorem intervalIntegrable_guardWeight {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun y => y⁻¹ * Real.exp (guardPotential α l₁ y / D)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.mul _ (continuous_exp_guardPotential α l₁ D).continuousOn
  exact continuousOn_inv₀.mono fun y hy => (ne_of_gt (ha.trans_le hy.1) : y ≠ 0)

/-- Bounds for the part of the outer integral just inside the barrier top:
`K(a) I ≤ ∫_a^b h ≤ K(b) I`, `I = ∫_a^b y⁻¹ e^{U/D̃}` (used with `b = r_c`). -/
@[tmio M, powerlib_foundation] theorem guard_inside_bounds {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    guardInner α l₁ D a * ∫ y in a..b, y⁻¹ * Real.exp (guardPotential α l₁ y / D) ≤
        ∫ y in a..b, guardIntegrand α l₁ D y ∧
      ∫ y in a..b, guardIntegrand α l₁ D y ≤
        guardInner α l₁ D b * ∫ y in a..b, y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
  have hw := intervalIntegrable_guardWeight (α := α) (l₁ := l₁) (D := D) ha hab
  have hh : IntervalIntegrable (guardIntegrand α l₁ D) volume a b :=
    intervalIntegrable_guardIntegrand_of_pos ha (ha.trans_le hab)
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hab (hw.const_mul _) hh
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    simp only [guardIntegrand]
    rw [mul_comm (guardInner α l₁ D a)]
    exact mul_le_mul_of_nonneg_left (guardInner_mono ha.le hy.1)
      (mul_nonneg (inv_nonneg.2 hy0.le) (Real.exp_pos _).le)
  · rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hab hh (hw.const_mul _)
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    simp only [guardIntegrand]
    rw [mul_comm (guardInner α l₁ D b)]
    exact mul_le_mul_of_nonneg_left (guardInner_mono hy0.le hy.2)
      (mul_nonneg (inv_nonneg.2 hy0.le) (Real.exp_pos _).le)

/-- Lower bound for the main weight integral: `I ≥ ((r_c − m)/r_c) e^{U(m)/D̃}` for `a ≤ m ≤ r_c`
with `U ≥ U(m)` on `[m, r_c]`. -/
@[tmio M, powerlib_foundation] private theorem guard_weight_ge (hD : 0 < D) {a m rc : ℝ} (ha : 0 < a)
    (ham : a ≤ m) (hmr : m ≤ rc)
    (hU : ∀ y ∈ Icc m rc, guardPotential α l₁ m ≤ guardPotential α l₁ y) :
    (rc - m) / rc * Real.exp (guardPotential α l₁ m / D) ≤
      ∫ y in a..rc, y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
  have hm0 : 0 < m := ha.trans_le ham
  have hrc0 : 0 < rc := hm0.trans_le hmr
  calc (rc - m) / rc * Real.exp (guardPotential α l₁ m / D) =
        ∫ y in m..rc, rc⁻¹ * Real.exp (guardPotential α l₁ m / D) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ ∫ y in m..rc, y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
        apply integral_mono_on hmr intervalIntegrable_const
          (intervalIntegrable_guardWeight hm0 hmr)
        intro y hy
        have hy0 : 0 < y := hm0.trans_le hy.1
        apply mul_le_mul (inv_anti₀ hy0 hy.2) _ (Real.exp_pos _).le (inv_nonneg.2 hy0.le)
        exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hU y hy) hD.le)
    _ ≤ ∫ y in a..rc, y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
        apply integral_mono_interval ham hmr le_rfl
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
          exact mul_nonneg (inv_nonneg.2 (ha.trans hy.1).le) (Real.exp_pos _).le
        · exact intervalIntegrable_guardWeight ha (ham.trans hmr)

/-- Tail bound: `∫_c^d h ≤ (d − c)(d/2)(e^{U*/D̃} + 1)` when `U ≤ U*` on `[c, d]`, `0 ≤ c ≤ d`. -/
@[tmio M, powerlib_foundation] private theorem guard_tail_le (hl : 0 < l₁) (hD : 0 < D) {c d Us : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (hU : ∀ y ∈ Icc c d, guardPotential α l₁ y ≤ Us)
    (hint : IntervalIntegrable (guardIntegrand α l₁ D) volume c d) :
    ∫ y in c..d, guardIntegrand α l₁ D y ≤ (d - c) * (d / 2 * (Real.exp (Us / D) + 1)) := by
  calc ∫ y in c..d, guardIntegrand α l₁ D y ≤ ∫ y in c..d, d / 2 * (Real.exp (Us / D) + 1) := by
        apply integral_mono_on hcd hint intervalIntegrable_const
        intro y hy
        rcases eq_or_lt_of_le (hc.trans hy.1) with h0 | h0
        · rw [← h0]; simp only [guardIntegrand, inv_zero, zero_mul]
          have : 0 ≤ d := hc.trans hcd
          positivity
        · refine (guardIntegrand_le hl hD h0).trans ?_
          apply mul_le_mul (by linarith [hy.2]) _ (by positivity) (by linarith [hc, hcd])
          have := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hU y hy) hD.le)
          linarith
    _ = (d - c) * (d / 2 * (Real.exp (Us / D) + 1)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

/-- The two tails are exponentially small against the main part: with
`I = ∫_a^{r_c} y⁻¹ e^{U/D̃}`, `∫₀^a h + ∫_{ψ(a)}^{r_b} h ≤ ε K(a) I`. -/
@[tmio M, powerlib_foundation] theorem guard_tails_le (hα : 0 < α) (hl : 0 < l₁) {a rb : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hψ : √(2 * (α / l₁) - a ^ 2) ≤ rb) (hD : 0 < D)
    (hDa : D ≤ a ^ 2) :
    (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) +
        ∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y ≤
      guardEps α l₁ a rb D * (guardInner α l₁ D a *
        ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le (two_ne_zero); rwa [hrc2] at this
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hψ0 : 0 < √(2 * (α / l₁) - a ^ 2) := hrc.trans_le hrcψ
  have ham : a < (a + √(α / l₁)) / 2 := by linarith
  have hmr : (a + √(α / l₁)) / 2 < √(α / l₁) := by linarith
  have hUa_le : ∀ y ∈ Icc 0 a, guardPotential α l₁ y ≤ guardPotential α l₁ a := by
    intro y hy
    apply guardPotential_le_of_sq_le hl
    have : y ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hy.1 hy.2 2
    nlinarith [sq_nonneg y]
  have hUψ_le : ∀ y ∈ Icc √(2 * (α / l₁) - a ^ 2) rb,
      guardPotential α l₁ y ≤ guardPotential α l₁ a := by
    intro y hy
    apply guardPotential_le_of_sq_le hl
    have hψa2 : √(2 * (α / l₁) - a ^ 2) ^ 2 = 2 * (α / l₁) - a ^ 2 := Real.sq_sqrt (by linarith)
    have : √(2 * (α / l₁) - a ^ 2) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hψ0.le hy.1 2
    nlinarith
  have hUm_ge : ∀ y ∈ Icc ((a + √(α / l₁)) / 2) √(α / l₁),
      guardPotential α l₁ ((a + √(α / l₁)) / 2) ≤ guardPotential α l₁ y := by
    intro y hy
    apply guardPotential_le_of_sq_le hl
    have hm0 : 0 < (a + √(α / l₁)) / 2 := by linarith
    have h1 : ((a + √(α / l₁)) / 2) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hm0.le hy.1 2
    have h2 : y ^ 2 ≤ √(α / l₁) ^ 2 := pow_le_pow_left₀ (hm0.le.trans hy.1) hy.2 2
    nlinarith
  have hKa := guardInner_ge (l₁ := l₁) hα.le hl.le hD ha.le hDa
  have hKa0 : 0 < guardInner α l₁ D a := lt_of_lt_of_le (by positivity) hKa
  have hI := guard_weight_ge (l₁ := l₁) hD ha ham.le hmr.le hUm_ge
  have hint0a : IntervalIntegrable (guardIntegrand α l₁ D) volume 0 a :=
    intervalIntegrable_guardIntegrand hl hD ha.le
  have hintψb : IntervalIntegrable (guardIntegrand α l₁ D) volume √(2 * (α / l₁) - a ^ 2) rb :=
    intervalIntegrable_guardIntegrand_of_pos hψ0 (hψ0.trans_le hψ)
  have hAt := guard_tail_le (l₁ := l₁) hl hD le_rfl ha.le hUa_le hint0a
  have hBt := guard_tail_le (l₁ := l₁) hl hD hψ0.le hψ hUψ_le hintψb
  generalize (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) = I at hI ⊢
  generalize (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) = At at hAt ⊢
  generalize (∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y) = Bt at hBt ⊢
  have hrm : 0 < √(α / l₁) - (a + √(α / l₁)) / 2 := by linarith
  have hQ : D / 2 * Real.exp (-(α / 2)) * ((√(α / l₁) - (a + √(α / l₁)) / 2) / √(α / l₁) *
      Real.exp (guardPotential α l₁ ((a + √(α / l₁)) / 2) / D)) ≤ guardInner α l₁ D a * I :=
    mul_le_mul hKa hI (by positivity) hKa0.le
  have hP0 : 0 ≤ (a ^ 2 / 2 + (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2)) *
      (Real.exp (guardPotential α l₁ a / D) + 1) := by
    have : 0 ≤ rb - √(2 * (α / l₁) - a ^ 2) := by linarith
    have : 0 ≤ rb := by linarith
    positivity
  have hP : At + Bt ≤ (a ^ 2 / 2 + (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2)) *
      (Real.exp (guardPotential α l₁ a / D) + 1) := by
    have h1 : (a - 0) * (a / 2 * (Real.exp (guardPotential α l₁ a / D) + 1)) =
        a ^ 2 / 2 * (Real.exp (guardPotential α l₁ a / D) + 1) := by ring
    have h2 : (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2 *
        (Real.exp (guardPotential α l₁ a / D) + 1)) = (rb - √(2 * (α / l₁) - a ^ 2)) *
        (rb / 2) * (Real.exp (guardPotential α l₁ a / D) + 1) := by ring
    rw [h1] at hAt; rw [h2] at hBt
    linarith
  refine hP.trans ?_
  unfold guardEps
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left hQ hP0

/-- `K(ψ(a)) ≤ (1 + κ) K(a)`: across the barrier the inner integral grows by an exponentially
small relative amount. -/
@[tmio M, powerlib_foundation] theorem guardInner_reflect_le (hα : 0 < α) (hl : 0 < l₁) {a : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hD : 0 < D) (hDa : D ≤ a ^ 2) :
    guardInner α l₁ D √(2 * (α / l₁) - a ^ 2) ≤
      (1 + guardKappa α l₁ a D) * guardInner α l₁ D a := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le (two_ne_zero); rwa [hrc2] at this
  have hψa2 : √(2 * (α / l₁) - a ^ 2) ^ 2 = 2 * (α / l₁) - a ^ 2 := Real.sq_sqrt (by linarith)
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hUa_ge : ∀ z ∈ Icc a √(2 * (α / l₁) - a ^ 2),
      guardPotential α l₁ a ≤ guardPotential α l₁ z := by
    intro z hz
    apply guardPotential_le_of_sq_le hl
    have h1 : a ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ ha.le hz.1 2
    have h2 : z ^ 2 ≤ √(2 * (α / l₁) - a ^ 2) ^ 2 := pow_le_pow_left₀ (ha.le.trans hz.1) hz.2 2
    nlinarith
  have hKa := guardInner_ge (l₁ := l₁) hα.le hl.le hD ha.le hDa
  have hKψ := guardInner_sub_le (l₁ := l₁) hD ha.le (har.le.trans hrcψ) hUa_ge
  have hk : (√(2 * (α / l₁) - a ^ 2) - a) * (√(2 * (α / l₁) - a ^ 2) *
      Real.exp (-(guardPotential α l₁ a / D))) ≤ guardKappa α l₁ a D * guardInner α l₁ D a := by
    unfold guardKappa
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : 0 ≤ (√(2 * (α / l₁) - a ^ 2) - a) * (√(2 * (α / l₁) - a ^ 2) *
        Real.exp (-(guardPotential α l₁ a / D))) := by
      have : 0 ≤ √(2 * (α / l₁) - a ^ 2) - a := by linarith
      positivity
    exact mul_le_mul_of_nonneg_left hKa this
  linarith

@[tmio M, powerlib_foundation] theorem guardKappa_nonneg (hα : 0 < α) (hl : 0 < l₁) {a : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hD : 0 < D) : 0 ≤ guardKappa α l₁ a D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le (two_ne_zero); rwa [hrc2] at this
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  unfold guardKappa
  have : 0 ≤ √(2 * (α / l₁) - a ^ 2) - a := by linarith
  positivity

@[tmio M, powerlib_foundation] theorem guardEps_nonneg (hα : 0 < α) (hl : 0 < l₁) {a rb : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hψ : √(2 * (α / l₁) - a ^ 2) ≤ rb) (hD : 0 < D) :
    0 ≤ guardEps α l₁ a rb D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrm : 0 < √(α / l₁) - (a + √(α / l₁)) / 2 := by linarith
  have hb : 0 ≤ rb - √(2 * (α / l₁) - a ^ 2) := by linarith
  have hrb : 0 ≤ rb := (Real.sqrt_nonneg _).trans hψ
  unfold guardEps
  apply div_nonneg
  · exact mul_nonneg (add_nonneg (by positivity) (mul_nonneg hb (by positivity))) (by positivity)
  · exact mul_nonneg (by positivity) (mul_nonneg (div_nonneg hrm.le hrc.le) (by positivity))

/-- `e^{−c/D̃}/D̃ → 0` as `D̃ → 0⁺` (`c > 0`). -/
@[tmio T, powerlib_foundation] theorem tendsto_exp_neg_div_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun D : ℝ => Real.exp (-(c / D)) / D) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t * Real.exp (-(c * t))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hc)).const_mul c⁻¹
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, id, pow_one]
    field_simp
  refine (h1.comp tendsto_inv_nhdsGT_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  simp only [Function.comp_apply]
  rw [div_eq_mul_inv, mul_comm, div_eq_mul_inv c]

/-- `e^{−c/D̃}/D̃² → 0` as `D̃ → 0⁺` (`c > 0`). -/
@[tmio T, powerlib_foundation] theorem tendsto_exp_neg_div_div_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun D : ℝ => Real.exp (-(c / D)) / D / D) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_exp_neg_div_div (half_pos hc)).mul (tendsto_exp_neg_div_div (half_pos hc))
  rw [mul_zero] at h
  refine h.congr fun D => ?_
  rw [div_mul_div_comm, ← Real.exp_add, show -(c / 2 / D) + -(c / 2 / D) = -(c / D) by ring,
    div_div]

/-- `κ = o(D̃)`: the inner-integral growth across the barrier is exponentially small. -/
@[tmio M, powerlib_foundation] theorem tendsto_guardKappa_div (hl : 0 < l₁) {a : ℝ} (ha : 0 < a)
    (ha2 : a ^ 2 < 2 * (α / l₁)) :
    Tendsto (fun D => guardKappa α l₁ a D / D) (𝓝[>] 0) (𝓝 0) := by
  have hU := guardPotential_pos (α := α) hl ha ha2
  have h := (tendsto_exp_neg_div_div_div hU).const_mul
    ((√(2 * (α / l₁) - a ^ 2) - a) * √(2 * (α / l₁) - a ^ 2) / (Real.exp (-(α / 2)) / 2))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD0 : (D : ℝ) ≠ 0 := ne_of_gt hD
  simp only [guardKappa]
  field_simp

/-- `ε = o(D̃)`: the tails are exponentially small. -/
@[tmio M, powerlib_foundation] theorem tendsto_guardEps_div (hl : 0 < l₁) {a rb : ℝ} (ha : 0 < a)
    (har : a < √(α / l₁)) (hρ : 0 < α / l₁) :
    Tendsto (fun D => guardEps α l₁ a rb D / D) (𝓝[>] 0) (𝓝 0) := by
  set m := (a + √(α / l₁)) / 2 with hmdef
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have ham : a < m := by simp only [hmdef]; linarith
  have hmr : m < √(α / l₁) := by simp only [hmdef]; linarith
  have hm0 : 0 < m := ha.trans ham
  have hm2 : m ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ hmr hm0.le two_ne_zero; rwa [hrc2] at this
  have ha2 : a ^ 2 < m ^ 2 := pow_lt_pow_left₀ ham ha.le two_ne_zero
  have hUm : 0 < guardPotential α l₁ m := guardPotential_pos hl hm0 (by linarith)
  have hUma : 0 < guardPotential α l₁ m - guardPotential α l₁ a := by
    rw [guardPotential_eq_barrier_sub hl, guardPotential_eq_barrier_sub hl]
    have : (m ^ 2 - α / l₁) ^ 2 < (a ^ 2 - α / l₁) ^ 2 := by nlinarith
    have : 0 < l₁ / 4 := by positivity
    nlinarith
  have hq : 0 < (√(α / l₁) - m) / √(α / l₁) := div_pos (by linarith) hrc
  set C := (a ^ 2 / 2 + (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2)) /
    (Real.exp (-(α / 2)) / 2 * ((√(α / l₁) - m) / √(α / l₁))) with hCdef
  have h := ((tendsto_exp_neg_div_div_div hUma).add
    (tendsto_exp_neg_div_div_div hUm)).const_mul C
  rw [add_zero, mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD0 : (D : ℝ) ≠ 0 := ne_of_gt hD
  have e1 : Real.exp (-((guardPotential α l₁ m - guardPotential α l₁ a) / D)) =
      Real.exp (guardPotential α l₁ a / D) / Real.exp (guardPotential α l₁ m / D) := by
    rw [← Real.exp_sub]; congr 1; field_simp; ring
  have e2 : Real.exp (-(guardPotential α l₁ m / D)) = 1 / Real.exp (guardPotential α l₁ m / D) := by
    rw [Real.exp_neg, one_div]
  simp only [guardEps, ← hmdef, hCdef]
  rw [e1, e2]
  have hE := Real.exp_pos (guardPotential α l₁ m / D)
  have hE2 := Real.exp_pos (-(α / 2))
  have hq' : (√(α / l₁) - m) / √(α / l₁) ≠ 0 := hq.ne'
  field_simp

/-- Choice of the cut: there is `a ∈ (0, r_c)` with reflected cut `ψ(a) = √(2r_c² − a²) ≤ r_b`. -/
@[tmio M, powerlib_foundation] theorem guard_exists_cut (hα : 0 < α) (hl : 0 < l₁) {rb : ℝ}
    (hrb : guardRadius α l₁ < rb) :
    ∃ a, 0 < a ∧ a < √(α / l₁) ∧ √(2 * (α / l₁) - a ^ 2) ≤ rb := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  set rc := guardRadius α l₁ with hrcdef
  have hrcs : rc = √(α / l₁) := rfl
  have hrc : 0 < rc := Real.sqrt_pos.mpr hρ
  have hrc2 : rc ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have hψc : ContinuousAt (fun a : ℝ => √(2 * (α / l₁) - a ^ 2)) rc := by fun_prop
  have hψrc : √(2 * (α / l₁) - rc ^ 2) = rc := by rw [hrc2, hrcs]; ring_nf
  have h1 : ∀ᶠ a in 𝓝 rc, √(2 * (α / l₁) - a ^ 2) < rb :=
    hψc.eventually (gt_mem_nhds (by show √(2 * (α / l₁) - rc ^ 2) < rb; rw [hψrc]; exact hrb))
  have h3 : ∀ᶠ a in 𝓝 rc, 0 < a := eventually_gt_nhds hrc
  have hev : ∀ᶠ a in 𝓝[<] rc, 0 < a ∧ a < rc ∧ √(2 * (α / l₁) - a ^ 2) < rb := by
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h3, self_mem_nhdsWithin]
      with a h1a h3a h4a
    exact ⟨h3a, h4a, h1a⟩
  obtain ⟨a, h3a, h4a, h1a⟩ := hev.exists
  exact ⟨a, h3a, h4a, h1a.le⟩

end Cut

/-! ## Gaussian bounds for the inner integral; the prefactor -/

section Gauss

/-- Lower Gaussian bound for the inner integral: `K(y) ≥ (D̃/α)(1 − e^{−αy²/(2D̃)})`, `y ≥ 0`
(from `U(z) ≤ αz²/2`). -/
@[tmio M, powerlib_foundation] theorem guardInner_ge_gauss (hα : 0 < α) (hl : 0 ≤ l₁) {D y : ℝ}
    (hD : 0 < D) (hy : 0 ≤ y) :
    D / α * (1 - Real.exp (-(α / (2 * D)) * y ^ 2)) ≤ guardInner α l₁ D y := by
  have hβ : 0 < α / (2 * D) := by positivity
  rw [show D / α = (2 * (α / (2 * D)))⁻¹ by field_simp, mul_comm (2 * (α / (2 * D)))⁻¹,
    ← div_eq_mul_inv, ← integral_mul_exp_neg_mul_sq_interval hβ]
  apply integral_mono_on hy
    ((by fun_prop : Continuous fun z : ℝ =>
      z * Real.exp (-(α / (2 * D)) * z ^ 2)).intervalIntegrable _ _)
    ((continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _)
  intro z hz
  apply mul_le_mul_of_nonneg_left _ hz.1
  apply Real.exp_le_exp.mpr
  have h := guardPotential_le_quad (α := α) hl z
  have : guardPotential α l₁ z / D ≤ α / (2 * D) * z ^ 2 := by
    rw [div_le_iff₀ hD]
    have e : α / (2 * D) * z ^ 2 * D = α * z ^ 2 / 2 := by field_simp
    rw [e]; exact h
  linarith

/-- Upper Gaussian bound for the inner integral up to the barrier top:
`K(r_c) ≤ (D̃/α)(1 + 16 l₁ D̃/α²)` (from `e^{−U/D̃} ≤ e^{−αz²/(2D̃)} + (l₁z⁴/(4D̃)) e^{−αz²/(4D̃)}`
on `[0, r_c]` and the fifth half-line moment). -/
@[tmio M, powerlib_foundation] theorem guardInner_le_gauss (hα : 0 < α) (hl : 0 < l₁) {D : ℝ}
    (hD : 0 < D) :
    guardInner α l₁ D √(α / l₁) ≤ D / α * (1 + 16 * l₁ * D / α ^ 2) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 ≤ √(α / l₁) := Real.sqrt_nonneg _
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have hc : 0 < α / (4 * D) := by positivity
  have hg5 : Continuous fun z : ℝ =>
      l₁ / (4 * D) * (z ^ 5 * Real.exp (-(α / (4 * D)) * z ^ 2)) := by fun_prop
  have hg1 : Continuous fun z : ℝ => z * Real.exp (-(α / (2 * D)) * z ^ 2) := by fun_prop
  have hpt : ∀ z ∈ Icc (0 : ℝ) √(α / l₁), z * Real.exp (-(guardPotential α l₁ z / D)) ≤
      z * Real.exp (-(α / (2 * D)) * z ^ 2) +
        l₁ / (4 * D) * (z ^ 5 * Real.exp (-(α / (4 * D)) * z ^ 2)) := by
    intro z hz
    have hz2 : z ^ 2 ≤ α / l₁ := by
      have := pow_le_pow_left₀ hz.1 hz.2 2; rwa [hrc2] at this
    have hlz : l₁ * z ^ 2 ≤ α := by rwa [le_div_iff₀ hl, mul_comm] at hz2
    set s := guardPotential α l₁ z / D with hs
    set t := α / (2 * D) * z ^ 2 with ht
    have hts : t - s = l₁ / (4 * D) * z ^ 4 := by
      simp only [hs, ht, guardPotential, Potential.doubleWell]; field_simp; ring
    have hs4 : α / (4 * D) * z ^ 2 ≤ s := by
      simp only [hs, guardPotential, Potential.doubleWell]
      rw [le_div_iff₀ hD]
      have e : α / (4 * D) * z ^ 2 * D = α * z ^ 2 / 4 := by field_simp
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hlz (sq_nonneg z)]
    have hts0 : 0 ≤ t - s := by rw [hts]; positivity
    -- `e^{−s} ≤ e^{−t} + (t − s) e^{−s}`
    have hexp : Real.exp (-s) ≤ Real.exp (-t) + (t - s) * Real.exp (-s) := by
      have h1 := Real.add_one_le_exp (-(t - s))
      have h2 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
        rw [← Real.exp_add]; congr 1; ring
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-s)).le
      nlinarith
    have hexp2 : Real.exp (-s) ≤ Real.exp (-(α / (4 * D)) * z ^ 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have : Real.exp (-s) ≤ Real.exp (-t) +
        l₁ / (4 * D) * z ^ 4 * Real.exp (-(α / (4 * D)) * z ^ 2) := by
      rw [← hts]; nlinarith [mul_le_mul_of_nonneg_left hexp2 hts0]
    have e1 : Real.exp (-t) = Real.exp (-(α / (2 * D)) * z ^ 2) := by
      simp only [ht]; ring_nf
    rw [e1] at this
    calc z * Real.exp (-s) ≤ z * (Real.exp (-(α / (2 * D)) * z ^ 2) +
          l₁ / (4 * D) * z ^ 4 * Real.exp (-(α / (4 * D)) * z ^ 2)) :=
          mul_le_mul_of_nonneg_left this hz.1
      _ = _ := by ring
  have hint5 : IntegrableOn (fun z : ℝ => l₁ / (4 * D) *
      (z ^ 5 * Real.exp (-(α / (4 * D)) * z ^ 2))) (Ioi 0) :=
    ((integrable_pow_mul_exp_neg_mul_sq hc 5).const_mul _).integrableOn
  calc guardInner α l₁ D √(α / l₁)
      ≤ ∫ z in (0 : ℝ)..√(α / l₁), (z * Real.exp (-(α / (2 * D)) * z ^ 2) +
          l₁ / (4 * D) * (z ^ 5 * Real.exp (-(α / (4 * D)) * z ^ 2))) :=
        integral_mono_on hrc ((continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _)
          ((hg1.add hg5).intervalIntegrable _ _) hpt
    _ = (∫ z in (0 : ℝ)..√(α / l₁), z * Real.exp (-(α / (2 * D)) * z ^ 2)) +
          ∫ z in (0 : ℝ)..√(α / l₁), l₁ / (4 * D) *
            (z ^ 5 * Real.exp (-(α / (4 * D)) * z ^ 2)) :=
        intervalIntegral.integral_add (hg1.intervalIntegrable _ _) (hg5.intervalIntegrable _ _)
    _ ≤ D / α + l₁ / (4 * D) * (1 / (α / (4 * D)) ^ 3) := by
        apply add_le_add
        · have hβ : 0 < α / (2 * D) := by positivity
          rw [integral_mul_exp_neg_mul_sq_interval hβ, div_le_iff₀ (by positivity),
            show D / α * (2 * (α / (2 * D))) = 1 by field_simp]
          linarith [Real.exp_pos (-(α / (2 * D)) * √(α / l₁) ^ 2)]
        · refine (intervalIntegral_le_integral_Ioi hrc hint5 fun z hz => by positivity).trans ?_
          rw [MeasureTheory.integral_const_mul, gaussMoment5 hc]
    _ = D / α * (1 + 16 * l₁ * D / α ^ 2) := by field_simp; ring

/-- `D̃ P = (D̃/α) · r_c⁻¹ · √(π/(α/D̃))/2`: the prefactor is the product of the inner Gaussian
mass `D̃/α`, the weight `1/r_c` at the top and the half Gaussian `√(πD̃/α)/2`. -/
@[tmio M, powerlib_foundation] theorem mul_guardPrefactor_eq (hα : 0 < α) (hl : 0 < l₁) {D : ℝ}
    (hD : 0 < D) :
    D * guardPrefactor α l₁ D = D / α * ((√(α / l₁))⁻¹ * (√(π / (α / D)) / 2)) := by
  have e1 : π / (α / D) = π * D / α := by field_simp
  rw [guardPrefactor, e1, Real.sqrt_div' _ hα.le, Real.sqrt_div' _ hl.le,
    Real.sqrt_mul Real.pi_pos.le, Real.sqrt_mul hD.le]
  have hsl : 0 < √l₁ := Real.sqrt_pos.mpr hl
  obtain ⟨u, hu, hu2⟩ : ∃ u, u = √α ∧ u ^ 2 = α := ⟨_, rfl, Real.sq_sqrt hα.le⟩
  have hu0 : 0 < u := hu ▸ Real.sqrt_pos.mpr hα
  rw [← hu, ← hu2]
  field_simp

end Gauss

end powerlib.Asymptotics.Guard
