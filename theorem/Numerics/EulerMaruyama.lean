import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # Exact mean-square recursions of Euler–Maruyama steps

Exact second-moment recursions of explicit and drift-implicit Euler–Maruyama steps on the scalar
test equations, and their mean-square stability conditions.

Model boundary.
* One scalar EM step with Gaussian increment `ΔW ~ N(0, h)` independent of the current state
  `X` (a real random variable on a probability space). We compute the exact second moment of the
  next state:
  * multiplicative-noise test equation `dX = -λX dt + βX dW` (explicit EM):
    `E[X_{n+1}²] = ((1-λh)² + β²h) E[X_n²]` (`em_multiplicative_step`);
  * the same equation, drift-implicit EM `X_{n+1} = (X_n + βX_nΔW)/(1+λh)`:
    `E[X_{n+1}²] = (1+β²h)/(1+λh)² · E[X_n²]` (`driftImplicit_multiplicative_step`);
  * additive-noise test equation `dX = -λX dt + β dW` (explicit EM):
    `E[X_{n+1}²] = (1-λh)² E[X_n²] + β²h` (`em_additive_step`).
  The resulting deterministic recursions are then analysed.
* These are statements about the discrete scheme only; nothing is claimed about the
  continuous-time SDE.

Source: work-sync theory/T-sde-systems.md §1.14.1 (Euler–Maruyama step),
§1.14.5 (mean-square stability regions of explicit and drift-implicit EM).

Results.
* `em_multiplicative_ms_tendsto_zero_iff`, `msFactorEM_lt_one_iff` — explicit EM on the
  multiplicative-noise equation is mean-square stable iff `(1-λh)² + β²h < 1`, i.e. (for
  `h > 0`) iff `λ²h < 2λ - β²`: a step-size restriction.
* `em_additive_secondMoment_ge`, `em_additive_not_tendsto_zero`,
  `em_additive_secondMoment_tendsto` — additive noise with `β ≠ 0`: the second moment is at
  least `β²h` after one step, so it never tends to `0`; when `(1-λh)² < 1` it converges to
  `β²h / (1 - (1-λh)²)` whatever the initial value.
* `driftImplicit_msFactor_lt_one`, `driftImplicit_msFactor_counterexample` — drift-implicit EM:
  when the SDE is mean-square stable (`β² < 2λ`, `λ > 0`) the factor is `< 1` for every step
  `h > 0`; without `β² < 2λ` this fails (`λ = 1`, `β = 2`, `h = 1`).

Corrections.
* T-sde-systems §1.14.5: the note states the criterion `|1-λΔt|² + β²Δt < 1` for the
  *additive*-noise test equation `dX = -λX dt + β dW`. That criterion is the mean-square
  criterion of the *multiplicative*-noise equation `dX = -λX dt + βX dW`
  (`em_multiplicative_ms_tendsto_zero_iff`). For additive noise with `β ≠ 0` the second moment
  never tends to `0` (`em_additive_secondMoment_ge`); it converges to `β²h / (1 - (1-λh)²)` iff
  `|1-λh| < 1` (`em_additive_secondMoment_tendsto`). Likewise the drift-implicit "A-stability"
  holds for every step `h > 0` exactly when the SDE itself is mean-square stable, `β² < 2λ`
  (`driftImplicit_msFactor_lt_one`), not for arbitrary `β`.
-/

noncomputable section
namespace powerlib.Numerics

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

/-- Second moment of `c + β z` under `N(0, h)`. -/
@[powerlib_foundation] theorem integral_affine_sq_gaussian (c β : ℝ) (h : ℝ≥0) :
    ∫ z, (c + β * z) ^ 2 ∂(gaussianReal 0 h) = c ^ 2 + β ^ 2 * h := by
  have hv : ∫ z, z ^ 2 ∂(gaussianReal 0 h) = h := by
    have := variance_fun_id_gaussianReal (μ := (0:ℝ)) (v := h)
    rw [variance_eq_integral measurable_id'.aemeasurable] at this
    simpa [integral_id_gaussianReal] using this
  have i1 : Integrable (fun z : ℝ => z) (gaussianReal 0 h) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have i2 : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 h) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have e : (fun z : ℝ => (c + β * z) ^ 2) = fun z => c ^ 2 + (2 * c * β * z + β ^ 2 * z ^ 2) := by
    funext z; ring
  have i3 : Integrable (fun z : ℝ => 2 * c * β * z + β ^ 2 * z ^ 2) (gaussianReal 0 h) :=
    (i1.const_mul (2 * c * β)).add (i2.const_mul (β ^ 2))
  have i4 : Integrable (fun z : ℝ => 2 * c * β * z) (gaussianReal 0 h) := i1.const_mul _
  have i5 : Integrable (fun z : ℝ => β ^ 2 * z ^ 2) (gaussianReal 0 h) := i2.const_mul _
  rw [e, integral_add (integrable_const _) i3, integral_add i4 i5, integral_const_mul,
    integral_const_mul, hv]
  simp [integral_id_gaussianReal]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Mean-square factor of an explicit EM step for `dX = -λX dt + βX dW`. -/
def msFactorEM (lam β h : ℝ) : ℝ := (1 - lam * h) ^ 2 + β ^ 2 * h

/-- Mean-square factor of a drift-implicit EM step for `dX = -λX dt + βX dW`. -/
def msFactorImplicit (lam β h : ℝ) : ℝ := (1 + β ^ 2 * h) / (1 + lam * h) ^ 2

omit [IsProbabilityMeasure P] in
/-- Explicit EM, multiplicative noise: `E[(X(1 - λh + βΔW))²] = msFactorEM · E[X²]`. -/
@[powerlib_foundation] theorem em_multiplicative_step {X Z : Ω → ℝ} {h : ℝ≥0} {lam β : ℝ}
    (hXm : Measurable X) (hZ : HasLaw Z (gaussianReal 0 h) P) (hZm : Measurable Z)
    (hind : IndepFun X Z P) :
    ∫ ω, (X ω * (1 - lam * h + β * Z ω)) ^ 2 ∂P
      = msFactorEM lam β h * ∫ ω, X ω ^ 2 ∂P := by
  have hind2 : IndepFun (fun ω => X ω ^ 2) (fun ω => (1 - lam * h + β * Z ω) ^ 2) P :=
    hind.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun z : ℝ => (1 - lam * h + β * z) ^ 2)
      (by fun_prop) (by fun_prop)
  have e : (fun ω => (X ω * (1 - lam * h + β * Z ω)) ^ 2)
      = fun ω => X ω ^ 2 * (1 - lam * h + β * Z ω) ^ 2 := by funext ω; ring
  rw [e, hind2.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop), mul_comm,
    msFactorEM]
  congr 1
  have := hZ.integral_comp (f := fun z : ℝ => (1 - lam * h + β * z) ^ 2) (by fun_prop)
  simp only [Function.comp_def] at this
  rw [this, integral_affine_sq_gaussian]

omit [IsProbabilityMeasure P] in
/-- Drift-implicit EM, multiplicative noise: `X_{n+1} = (X + βXΔW)/(1+λh)`. -/
@[powerlib_foundation] theorem driftImplicit_multiplicative_step {X Z : Ω → ℝ} {h : ℝ≥0}
    {lam β : ℝ} (hXm : Measurable X) (hZ : HasLaw Z (gaussianReal 0 h) P) (hZm : Measurable Z)
    (hind : IndepFun X Z P) :
    ∫ ω, ((X ω + β * X ω * Z ω) / (1 + lam * h)) ^ 2 ∂P
      = msFactorImplicit lam β h * ∫ ω, X ω ^ 2 ∂P := by
  have e : (fun ω => ((X ω + β * X ω * Z ω) / (1 + lam * h)) ^ 2)
      = fun ω => ((1 + lam * h) ^ 2)⁻¹ * (X ω * (1 - 0 * (h : ℝ) + β * Z ω)) ^ 2 := by
    funext ω; rw [div_pow]; ring
  rw [e, integral_const_mul, em_multiplicative_step (lam := 0) hXm hZ hZm hind, msFactorEM,
    msFactorImplicit]
  ring

/-- Explicit EM, additive noise: `E[(aX + βΔW)²] = a² E[X²] + β²h` for `X ∈ L²`. -/
@[powerlib_foundation] theorem em_additive_step {X Z : Ω → ℝ} {h : ℝ≥0} {a β : ℝ}
    (hX : MemLp X 2 P) (hZ : HasLaw Z (gaussianReal 0 h) P) (hind : IndepFun X Z P) :
    ∫ ω, (a * X ω + β * Z ω) ^ 2 ∂P = a ^ 2 * ∫ ω, X ω ^ 2 ∂P + β ^ 2 * h := by
  have hZ2 : MemLp Z 2 P := hZ.hasGaussianLaw.memLp_two
  have hZ1 : Integrable Z P := hZ2.integrable one_le_two
  have hX1 : Integrable X P := hX.integrable one_le_two
  have hXZ : Integrable (fun ω => X ω * Z ω) P := hind.integrable_mul hX1 hZ1
  have hEZ : ∫ ω, Z ω ∂P = 0 := by rw [hZ.integral_eq, integral_id_gaussianReal]
  have hEZ2 : ∫ ω, Z ω ^ 2 ∂P = h := by
    have := hZ.integral_comp (f := fun z : ℝ => (0 + 1 * z) ^ 2) (by fun_prop)
    simp only [Function.comp_def, zero_add, one_mul] at this
    rw [this]; simpa using integral_affine_sq_gaussian 0 1 h
  have hEXZ : ∫ ω, X ω * Z ω ∂P = 0 := by
    rw [hind.integral_fun_mul_eq_mul_integral hX.aestronglyMeasurable hZ2.aestronglyMeasurable,
      hEZ, mul_zero]
  have e : (fun ω => (a * X ω + β * Z ω) ^ 2)
      = fun ω => a ^ 2 * X ω ^ 2 + (2 * a * β * (X ω * Z ω) + β ^ 2 * Z ω ^ 2) := by
    funext ω; ring
  have i1 : Integrable (fun ω => a ^ 2 * X ω ^ 2) P := hX.integrable_sq.const_mul _
  have i2 : Integrable (fun ω => 2 * a * β * (X ω * Z ω)) P := hXZ.const_mul _
  have i3 : Integrable (fun ω => β ^ 2 * Z ω ^ 2) P := hZ2.integrable_sq.const_mul _
  have i23 : Integrable (fun ω => 2 * a * β * (X ω * Z ω) + β ^ 2 * Z ω ^ 2) P := i2.add i3
  rw [e, integral_add i1 i23, integral_add i2 i3, integral_const_mul,
    integral_const_mul, integral_const_mul, hEXZ, hEZ2]
  ring

/-! ## The deterministic second-moment recursions -/

/-- Multiplicative noise: `m_n = c^n m₀` tends to `0` iff `c < 1` (`c ≥ 0`, `m₀ ≠ 0`). -/
@[powerlib_foundation] theorem geometric_tendsto_zero_iff {c m₀ : ℝ} (hc : 0 ≤ c) (hm : m₀ ≠ 0) :
    Tendsto (fun n : ℕ => c ^ n * m₀) atTop (𝓝 0) ↔ c < 1 := by
  constructor
  · intro h
    have h' : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) := by
      have := h.div_const m₀
      simpa [mul_div_assoc, div_self hm] using this
    have := (tendsto_pow_atTop_nhds_zero_iff).mp h'
    rwa [abs_of_nonneg hc] at this
  · intro h
    have : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hc h
    simpa using this.mul_const m₀

@[powerlib_foundation] theorem msFactorEM_nonneg (lam : ℝ) {h : ℝ} (hh : 0 ≤ h) (β : ℝ) :
    0 ≤ msFactorEM lam β h := by
  unfold msFactorEM; positivity

/-- Explicit EM for the multiplicative-noise test equation is mean-square stable
(`E[X_n²] = c^n E[X_0²] → 0`, `E[X_0²] ≠ 0`) iff `(1-λh)² + β²h < 1`. -/
@[powerlib_foundation] theorem em_multiplicative_ms_tendsto_zero_iff {lam β h m₀ : ℝ}
    (hh : 0 ≤ h) (hm : m₀ ≠ 0) :
    Tendsto (fun n : ℕ => msFactorEM lam β h ^ n * m₀) atTop (𝓝 0) ↔
      (1 - lam * h) ^ 2 + β ^ 2 * h < 1 :=
  geometric_tendsto_zero_iff (msFactorEM_nonneg lam hh β) hm

/-- For `h > 0` the explicit-EM factor is `< 1` iff `λ²h < 2λ - β²`: a step-size restriction. -/
@[powerlib_foundation] theorem msFactorEM_lt_one_iff {lam β h : ℝ} (hh : 0 < h) :
    msFactorEM lam β h < 1 ↔ lam ^ 2 * h < 2 * lam - β ^ 2 := by
  unfold msFactorEM
  constructor
  · intro H
    have : h * (lam ^ 2 * h - 2 * lam + β ^ 2) < 0 := by nlinarith
    have := (mul_neg_iff.mp this)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  · intro H
    have : h * (lam ^ 2 * h - 2 * lam + β ^ 2) < 0 := mul_neg_of_pos_of_neg hh (by linarith)
    nlinarith

/-- Drift-implicit EM: whenever the SDE is mean-square stable (`β² < 2λ`, `λ > 0`), the
mean-square factor is `< 1` for every step `h > 0`. -/
@[powerlib_foundation] theorem driftImplicit_msFactor_lt_one {lam β h : ℝ} (hlam : 0 < lam)
    (hβ : β ^ 2 < 2 * lam) (hh : 0 < h) : msFactorImplicit lam β h < 1 := by
  unfold msFactorImplicit
  have hpos : 0 < (1 + lam * h) ^ 2 := by positivity
  rw [div_lt_one hpos]
  nlinarith [mul_pos hlam hh, mul_pos (mul_pos hlam hlam) (mul_pos hh hh)]

/-- Without `β² < 2λ`, drift-implicit EM is not mean-square stable for all steps: for
`λ = 1, β = 2`, the factor exceeds `1` at `h = 1`. -/
@[powerlib_foundation] theorem driftImplicit_msFactor_counterexample :
    1 < msFactorImplicit 1 2 1 := by
  norm_num [msFactorImplicit]

/-- Additive-noise second-moment recursion `m_{n+1} = a² m_n + b`. -/
def addRec (a2 b m₀ : ℝ) : ℕ → ℝ
  | 0 => m₀
  | n + 1 => a2 * addRec a2 b m₀ n + b

/-- The additive recursion stays nonnegative. -/
@[powerlib_foundation] theorem addRec_nonneg {a2 b m₀ : ℝ} (ha : 0 ≤ a2) (hb : 0 ≤ b)
    (hm : 0 ≤ m₀) (n : ℕ) : 0 ≤ addRec a2 b m₀ n := by
  induction n with
  | zero => exact hm
  | succ k ih => simp only [addRec]; positivity

/-- With additive noise the second moment is bounded below by `b = β²h` after one step
(correction to T-sde-systems §1.14.5). -/
@[powerlib_foundation] theorem em_additive_secondMoment_ge {a2 b m₀ : ℝ} (ha : 0 ≤ a2)
    (hb : 0 ≤ b) (hm : 0 ≤ m₀) (n : ℕ) : b ≤ addRec a2 b m₀ (n + 1) := by
  simp only [addRec]
  nlinarith [addRec_nonneg ha hb hm n]

/-- Hence, with additive noise `b = β²h > 0`, the second moment does not tend to `0`. -/
@[powerlib_foundation] theorem em_additive_not_tendsto_zero {a2 b m₀ : ℝ} (ha : 0 ≤ a2)
    (hm : 0 ≤ m₀) (hb : 0 < b) : ¬ Tendsto (addRec a2 b m₀) atTop (𝓝 0) := by
  intro h
  have h1 : Tendsto (fun n => addRec a2 b m₀ (n + 1)) atTop (𝓝 0) :=
    h.comp (tendsto_add_atTop_nat 1)
  have := ge_of_tendsto' h1 (em_additive_secondMoment_ge ha hb.le hm)
  linarith

/-- Closed form of the additive recursion. -/
@[powerlib_foundation] theorem addRec_eq {a2 b m₀ : ℝ} (ha : a2 ≠ 1) (n : ℕ) :
    addRec a2 b m₀ n = a2 ^ n * (m₀ - b / (1 - a2)) + b / (1 - a2) := by
  have h1 : (1 - a2) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  induction n with
  | zero => simp [addRec]
  | succ n ih =>
    simp only [addRec, ih, pow_succ]
    field_simp
    ring

/-- With additive noise and `0 ≤ a² < 1` the second moment converges to `b/(1-a²)`
(`= β²h/(1-(1-λh)²)` for the EM step), whatever the initial value. -/
@[powerlib_foundation] theorem em_additive_secondMoment_tendsto {a2 b m₀ : ℝ} (h0 : 0 ≤ a2)
    (h1 : a2 < 1) : Tendsto (addRec a2 b m₀) atTop (𝓝 (b / (1 - a2))) := by
  have e : addRec a2 b m₀ = fun n => a2 ^ n * (m₀ - b / (1 - a2)) + b / (1 - a2) :=
    funext (addRec_eq h1.ne)
  rw [e]
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const (m₀ - b / (1 - a2))).add_const
    (b / (1 - a2))
  simpa using this

/-- With additive noise and `a² > 1`, `b ≥ 0` and a nonnegative initial moment above the
fixed point direction, the second moment diverges. -/
@[powerlib_foundation] theorem em_additive_secondMoment_tendsto_atTop {a2 b m₀ : ℝ} (h1 : 1 < a2)
    (hb : 0 < b) (hm : 0 ≤ m₀) : Tendsto (addRec a2 b m₀) atTop atTop := by
  have e : addRec a2 b m₀ = fun n => a2 ^ n * (m₀ - b / (1 - a2)) + b / (1 - a2) :=
    funext (addRec_eq h1.ne')
  rw [e]
  have hpos : 0 < m₀ - b / (1 - a2) := by
    have : b / (1 - a2) < 0 := div_neg_of_pos_of_neg hb (by linarith)
    linarith
  exact tendsto_atTop_add_const_right _ _
    ((tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const hpos)

end powerlib.Numerics
