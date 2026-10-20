import theorem.Frequency.SwingGovernor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Low-inertia frequency dynamics: time scales, critical inertia, frequency variance

Static foundation results (identities, an inversion, integrals, inequalities) for low-inertia
frequency dynamics: rotating-frame network equations, the critical inertia of a RoCoF limit, and
the inertia dependence of the frequency variance under stochastic load.

Model boundary.
* Continuous-time, linear, single-area, Kundur per-unit; no turbine, PLL, delay,
  voltage–frequency coupling.
* Stochastic statements are about the stationary variance integral
  `σ² = ∫₀^∞ |H(jω)|² S(ω) dω` of the note, not about a stochastic differential equation.
* The first-order plant `firstOrderModel` is a `Linear.Plant 1 1` (state, input and output
  `Δω`, `ΔP_L`, `Δω`). The only trajectory-level statement, `rocof_le_iff_criticalInertia`,
  reads the critical-inertia condition off the initial slope of a forward solution of the
  `Frequency.SwingGovernor` plant.

Source: work-sync `theory/T-low-inertia-frequency.md` §1.1 (time scales), §1.3 (dq network
equations), §1.5 (critical inertia), §1.7 (frequency variance under stochastic load).

Results.
* `rotatingFrame_hasDerivAt`, `dq_firstOrder`, `dq_firstOrder_re`, `dq_firstOrder_im` (§1.3):
  for a stationary-frame element `X ẋ_αβ = s_αβ − Y x_αβ` (series `R–L` line: `X = L`, `Y = R`,
  `s = v_i − v_j`; node capacitor: `X = C`, `Y = 0`, `s` = net injected current), the
  rotating-frame quantity `x_dq = e^{−j ω_s t} x_αβ` obeys
  `X ẋ_dq = s_dq − Y x_dq − j ω_s X x_dq`, i.e. `X ẋ_d = s_d − Y x_d + ω_s X x_q`,
  `X ẋ_q = s_q − Y x_q − ω_s X x_d` (product rule, `ω_s` constant).
* `criticalInertia`, `rocof_bound_iff`, `rocof_le_iff_criticalInertia` (§1.5): with the
  two-state model's initial RoCoF `|ḟ(0⁺)| = |ΔP_L| f₀/(2H)`,
  `|ḟ(0⁺)| ≤ ḟ_max ⇔ H ≥ H_crit = |ΔP_L| f₀/(2 ḟ_max)`; `criticalInertia_example`:
  `1 Hz/s`, `0.1 pu`, `50 Hz` give `2.5 s`.
* `firstOrderModel`, `firstOrder_transfer`, `firstOrder_normSq_transfer` (§1.7): the
  swing + droop model `M Δω̇ = −ΔP_L − (K_R + D) Δω` has `H(s) = −1/(M s + β)`,
  `β = K_R + D`, and `|H(jω)|² = 1/(β² + M² ω²)`; `normSq_tendsto_zero`,
  `mul_normSq_tendsto_atTop`: low-frequency limit `1/β²` (independent of `M`), high-frequency
  asymptote `|H|² ω² → 1/M²`.
* `whiteNoise_variance` (§1.7): `∫₀^∞ dω/(β² + M² ω²) = π/(2βM)`, so for a white PSD `S₀` the
  variance is `S₀ π/(2βM)` and `M σ²` is independent of `M` (exponent `p = 1`).
* `variance_antitone`, `variance_le_sq_mul` (§1.7): for **any** nonnegative PSD `S`,
  `M ↦ σ²(M)` is nonincreasing and `M ↦ M² σ²(M)` is nondecreasing; hence a power law
  `σ² = c M^{−p}` fitted at two inertia levels has `0 ≤ p ≤ 2` (`powerLaw_exponent_mem`).
  `nordel_not_explained`: the note's Nordel data (`M` 250 → 100 GW·s, `σ_Δf` 6 → 18 mHz,
  variance ratio 9 > 2.5² = 6.25, `p ≈ 2.4`) **cannot** be produced by this first-order model
  with any nonnegative PSD; the note's explanation "noise concentrated above `ω_c`" can give at
  most `p = 2`.
* `variance_tendsto_zero`, `twoPointExponent_tendsto_zero` (§1.7, `p = 0` end): for an
  integrable nonnegative PSD with `∫ S > 0`, `σ²(M) → (∫ S)/β²` as `M → 0` (all noise below the
  corner `ω_c = β/M`), so the two-point exponent `p(M, κM) = ln(σ²(M)/σ²(κM))/ln κ` tends to
  `0`. `mul_variance_tendsto_atTop`, `twoPointExponent_tendsto_two` (`p = 2` end): if `S(ω)/ω²`
  is integrable with positive integral, `M² σ²(M) → ∫ S/ω²` as `M → ∞` (all noise above the
  corner), so `p(M, κM) → 2`. Both by dominated convergence. Together with
  `powerLaw_exponent_mem` this makes `[0, 2]` the exact range of the exponent: both ends are
  attained asymptotically, low-frequency noise at small inertia and high-frequency noise at
  large inertia (the note's "low-frequency OU noise ⇒ `p = 0`, high-frequency noise ⇒ `p = 2`";
  the note's band statements are regimes of `M` relative to the noise band, not exact power
  laws).

Family and connection conclusions.
* None: this module defines no family; its results are identities, transfer functions,
  integrals and inequalities (foundation; the swing + governor stability conclusions are the
  connection statements of `Frequency.SwingGovernor.family`).
* `rocof_le_iff_criticalInertia` quantifies over a forward solution and its initial slope,
  outside the sentence language: it is private implementation evidence (Rules §3a), derived
  from the generic `LTI.hasDerivWithinAt_apply_zero` and the static `SwingGovernor.field_apply`.

Correction (§1.1).
* The electromechanical time constant `T_em = 2H/ω_s` is about 25 ms for `H = 4 s` at 50 Hz
  (`electromechanicalTime_example`), not "几秒"; the seconds-scale constant is `M = 2H` itself
  (the time constant of the per-unit swing equation).
-/

noncomputable section
namespace powerlib.Frequency.LowInertia
open Set Filter Matrix MeasureTheory
open scoped Topology

/-! ## dq network equations (§1.3) -/

/-- Park rotation `e^{−j ω t}`. -/
def rot (ω t : ℝ) : ℂ := Complex.exp (-((ω : ℂ) * Complex.I) * (t : ℂ))

/-- Product rule for the Park rotation `x_dq(t) = e^{−j ω t} x_αβ(t)`. -/
@[powerlib_foundation] theorem rotatingFrame_hasDerivAt {xs : ℝ → ℂ} {xs' : ℂ} {ω t : ℝ}
    (h : HasDerivAt xs xs' t) :
    HasDerivAt (fun t : ℝ => rot ω t * xs t)
      (rot ω t * xs' - (ω : ℂ) * Complex.I * (rot ω t * xs t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => -((ω : ℂ) * Complex.I) * (s : ℂ))
      (-((ω : ℂ) * Complex.I)) t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (-((ω : ℂ) * Complex.I))
  have hexp := hlin.cexp
  have := hexp.mul h
  unfold rot
  convert this using 1
  ring

/-- dq form of a first-order stationary-frame element `X ẋ_αβ = s_αβ − Y x_αβ`:
`ẋ_dq = (s_dq − Y x_dq)/X − j ω x_dq`. -/
@[powerlib_foundation] theorem dq_firstOrder {X Y ω t : ℝ} {xs ss : ℝ → ℂ}
    (h : HasDerivAt xs ((ss t - Y * xs t) / X) t) :
    HasDerivAt (fun t : ℝ => rot ω t * xs t)
      ((rot ω t * ss t - Y * (rot ω t * xs t)) / X - (ω : ℂ) * Complex.I * (rot ω t * xs t)) t := by
  have := rotatingFrame_hasDerivAt (ω := ω) h
  convert this using 2
  ring

/-- Real (d-axis) part: `X ẋ_d = s_d − Y x_d + ω X x_q`. -/
@[powerlib_foundation] theorem dq_firstOrder_re {X Y ω t : ℝ} {xs ss : ℝ → ℂ} (hX : X ≠ 0)
    (h : HasDerivAt xs ((ss t - Y * xs t) / X) t) :
    HasDerivAt (fun t : ℝ => (rot ω t * xs t).re)
      (((rot ω t * ss t).re - Y * (rot ω t * xs t).re + ω * X * (rot ω t * xs t).im) / X) t := by
  have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (dq_firstOrder (ω := ω) h)
  refine h1.congr_deriv ?_
  rw [Complex.reCLM_apply]
  generalize rot ω t * ss t = w
  generalize rot ω t * xs t = z
  simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
  field_simp
  ring

/-- Imaginary (q-axis) part: `X ẋ_q = s_q − Y x_q − ω X x_d`. -/
@[powerlib_foundation] theorem dq_firstOrder_im {X Y ω t : ℝ} {xs ss : ℝ → ℂ} (hX : X ≠ 0)
    (h : HasDerivAt xs ((ss t - Y * xs t) / X) t) :
    HasDerivAt (fun t : ℝ => (rot ω t * xs t).im)
      (((rot ω t * ss t).im - Y * (rot ω t * xs t).im - ω * X * (rot ω t * xs t).re) / X) t := by
  have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (dq_firstOrder (ω := ω) h)
  refine h1.congr_deriv ?_
  rw [Complex.imCLM_apply]
  generalize rot ω t * ss t = w
  generalize rot ω t * xs t = z
  simp only [Complex.sub_im, Complex.div_ofReal_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
  field_simp
  ring

/-! ## Critical inertia (§1.5) -/

/-- `H_crit = |ΔP_L| f₀ / (2 ḟ_max)`. -/
def criticalInertia (ΔPL f₀ rocofMax : ℝ) : ℝ := |ΔPL| * f₀ / (2 * rocofMax)

/-- Algebraic inversion of the RoCoF formula. -/
@[powerlib_foundation] theorem rocof_bound_iff {ΔPL f₀ H r : ℝ} (hH : 0 < H) (hr : 0 < r) :
    |ΔPL| * f₀ / (2 * H) ≤ r ↔ criticalInertia ΔPL f₀ r ≤ H := by
  unfold criticalInertia
  rw [div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.5 at trajectory level: for the two-state swing + governor plant with `M = 2H`, from rest, the
initial RoCoF `ḟ(0⁺)` (Hz/s, `f = f₀(1 + Δω)`) satisfies `|ḟ(0⁺)| ≤ ḟ_max` iff `H ≥ H_crit`. -/
private theorem rocof_le_iff_criticalInertia {H D K Tg ΔPL f₀ r ρ : ℝ}
    (hH : 0 < H) (hf : 0 < f₀) (hr : 0 < r) {x : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hx : IsIntegralCurveOn x
      (fun _ y => (SwingGovernor.plant (2 * H) D K Tg).inputField (load ΔPL) y) (Ici 0))
    (h0 : x 0 = 0) (hρ : HasDerivWithinAt (fun t => f₀ * (1 + x t 0)) ρ (Ici 0) 0) :
    |ρ| ≤ r ↔ criticalInertia ΔPL f₀ r ≤ H := by
  have hr0 : HasDerivWithinAt (fun t => x t 0) (-ΔPL / (2 * H)) (Ici 0) 0 := by
    have h := LTI.hasDerivWithinAt_apply_zero hx 0
    rw [SwingGovernor.field_apply, h0] at h
    convert h using 1
    simp only [Fin.isValue, Matrix.cons_val_zero, PiLp.zero_apply]
    ring
  have h : HasDerivWithinAt (fun t => f₀ * (1 + x t 0)) (-(ΔPL * f₀) / (2 * H)) (Ici 0) 0 := by
    have h := (hr0.const_add 1).const_mul f₀
    convert h using 1
    ring
  have hρ' : ρ = -(ΔPL * f₀) / (2 * H) :=
    (uniqueDiffWithinAt_Ici 0).eq_deriv _ hρ h
  rw [hρ', abs_div, abs_neg, abs_mul, abs_of_pos hf, abs_of_pos (by positivity : 0 < 2 * H)]
  exact rocof_bound_iff hH hr

/-- Worked example of §1.5: `ḟ_max = 1 Hz/s`, `ΔP_L = 0.1 pu`, `f₀ = 50 Hz` ⇒ `H_crit = 2.5 s`. -/
@[powerlib_foundation] theorem criticalInertia_example :
    criticalInertia 0.1 50 1 = 2.5 := by
  norm_num [criticalInertia, abs_of_pos]

/-! ## First-order swing + droop model and its frequency response (§1.7) -/

/-- `M Δω̇ = −ΔP_L − β Δω`, `β = K_R + D`; state `Δω`, input `ΔP_L`, output `Δω`. -/
def firstOrderModel (M β : ℝ) : Linear.Plant 1 1 where
  A := !![-β / M]
  B := !![-1 / M]
  C := !![1]
  D := 0

/-- `H(s) = −1/(M s + β)` (both sides `0` at the pole). -/
@[powerlib_foundation] theorem firstOrder_transfer {M β : ℝ} (hM : M ≠ 0) (s : ℂ) :
    Linear.transfer (firstOrderModel M β) s 0 0 = -1 / ((M : ℂ) * s + β) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hdet : (Linear.characteristicMatrix (firstOrderModel M β).A s).det = s + β / M := by
    simp [firstOrderModel, Linear.characteristicMatrix]
    ring
  have hadj : (Linear.complexify (firstOrderModel M β).C *
      (Linear.characteristicMatrix (firstOrderModel M β).A s).adjugate *
        Linear.complexify (firstOrderModel M β).B) 0 0 = -1 / M := by
    simp [firstOrderModel, Matrix.adjugate_fin_one, Matrix.mul_apply, Linear.complexify]
  have hD : Linear.complexify (firstOrderModel M β).D 0 0 = 0 := by simp [firstOrderModel]
  rw [Linear.transfer_eq_adjugate]
  simp only [Matrix.add_apply, Matrix.smul_apply, hadj, hD, smul_eq_mul, add_zero, hdet]
  have key : (M : ℂ) * s + β = M * (s + β / M) := by field_simp
  rw [key]
  by_cases h : s + (β : ℂ) / M = 0
  · rw [h]; simp
  · field_simp

/-- `|H(jω)|² = 1/(β² + M² ω²)`. -/
@[powerlib_foundation] theorem firstOrder_normSq_transfer {M β : ℝ} (hM : M ≠ 0)
    (ω : ℝ) :
    Complex.normSq (Linear.transfer (firstOrderModel M β) (ω * Complex.I) 0 0) =
      1 / (β ^ 2 + M ^ 2 * ω ^ 2) := by
  rw [firstOrder_transfer hM, Complex.normSq_div, Complex.normSq_neg, Complex.normSq_one]
  congr 1
  rw [Complex.normSq_apply]
  simp
  ring

/-- Low-frequency limit `|H(jω)|² → 1/β²`, independent of `M`. -/
@[powerlib_foundation] theorem normSq_tendsto_zero {M β : ℝ} (hβ : β ≠ 0) :
    Tendsto (fun ω : ℝ => 1 / (β ^ 2 + M ^ 2 * ω ^ 2)) (𝓝 0) (𝓝 (1 / β ^ 2)) := by
  have hc : Continuous (fun ω : ℝ => β ^ 2 + M ^ 2 * ω ^ 2) := by fun_prop
  have := (hc.tendsto 0).inv₀ (by simpa using pow_ne_zero 2 hβ)
  simpa [one_div] using this

/-- High-frequency asymptote: `ω² |H(jω)|² → 1/M²`. -/
@[powerlib_foundation] theorem mul_normSq_tendsto_atTop {M β : ℝ} (hM : M ≠ 0) :
    Tendsto (fun ω : ℝ => ω ^ 2 * (1 / (β ^ 2 + M ^ 2 * ω ^ 2))) atTop (𝓝 (1 / M ^ 2)) := by
  have hM2 : 0 < M ^ 2 := by positivity
  have hinv : Tendsto (fun ω : ℝ => (ω ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num))
  have h1 : Tendsto (fun ω : ℝ => β ^ 2 * (ω ^ 2)⁻¹ + M ^ 2) atTop (𝓝 (β ^ 2 * 0 + M ^ 2)) :=
    (hinv.const_mul _).add_const _
  rw [mul_zero, zero_add] at h1
  have h2 := h1.inv₀ hM2.ne'
  refine (h2.congr' ?_).trans (by rw [one_div])
  filter_upwards [eventually_gt_atTop 0] with ω hω
  have : ω ^ 2 ≠ 0 := by positivity
  field_simp

/-! ## Frequency variance (§1.7) -/

/-- `∫₀^∞ dω/(β² + M² ω²) = π/(2 β M)` for `β, M > 0`. -/
@[powerlib_foundation] theorem whiteNoise_variance {M β : ℝ} (hM : 0 < M) (hβ : 0 < β) :
    ∫ ω in Ioi (0 : ℝ), 1 / (β ^ 2 + M ^ 2 * ω ^ 2) = Real.pi / (2 * β * M) := by
  have hc : 0 < M / β := div_pos hM hβ
  have h1 : (fun ω : ℝ => 1 / (β ^ 2 + M ^ 2 * ω ^ 2)) =
      fun ω => (β ^ 2)⁻¹ * (fun y : ℝ => (1 + y ^ 2)⁻¹) (M / β * ω) := by
    funext ω
    field_simp
  rw [h1, integral_const_mul, integral_comp_mul_left_Ioi (fun y : ℝ => (1 + y ^ 2)⁻¹) 0 hc,
    mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul]
  field_simp

/-- Frequency variance `σ²(M) = ∫₀^∞ S(ω)/(β² + M² ω²) dω` for a PSD `S`. -/
def variance (S : ℝ → ℝ) (β M : ℝ) : ℝ := ∫ ω in Ioi (0 : ℝ), S ω / (β ^ 2 + M ^ 2 * ω ^ 2)

/-- White PSD `S₀`: `σ² = S₀ π/(2βM)`, so `M σ²` does not depend on `M` (`p = 1`). -/
@[powerlib_foundation] theorem variance_white {S₀ M β : ℝ} (hM : 0 < M) (hβ : 0 < β) :
    variance (fun _ => S₀) β M = S₀ * Real.pi / (2 * β * M) ∧
      M * variance (fun _ => S₀) β M = S₀ * Real.pi / (2 * β) := by
  have h : variance (fun _ => S₀) β M = S₀ * Real.pi / (2 * β * M) := by
    unfold variance
    have : (fun ω : ℝ => S₀ / (β ^ 2 + M ^ 2 * ω ^ 2)) =
        fun ω => S₀ * (1 / (β ^ 2 + M ^ 2 * ω ^ 2)) := by
      funext ω; ring
    rw [this, integral_const_mul, whiteNoise_variance hM hβ]
    ring
  refine ⟨h, ?_⟩
  rw [h]
  field_simp

section Elasticity

variable {S : ℝ → ℝ} {β M₁ M₂ : ℝ}

@[powerlib_foundation] private theorem denom_pos (hβ : β ≠ 0) (M ω : ℝ) :
    0 < β ^ 2 + M ^ 2 * ω ^ 2 := by
  have := pow_pos (abs_pos.2 hβ) 2
  rw [sq_abs] at this
  positivity

/-- Integrability at a smaller inertia implies integrability at a larger one. -/
@[powerlib_foundation] theorem integrable_of_le (hβ : β ≠ 0) (hS : ∀ ω, 0 ≤ S ω)
    (hM : M₁ ^ 2 ≤ M₂ ^ 2)
    (hint : IntegrableOn (fun ω => S ω / (β ^ 2 + M₁ ^ 2 * ω ^ 2)) (Ioi 0))
    (hmeas : AEStronglyMeasurable (fun ω => S ω / (β ^ 2 + M₂ ^ 2 * ω ^ 2))
      (volume.restrict (Ioi 0))) :
    IntegrableOn (fun ω => S ω / (β ^ 2 + M₂ ^ 2 * ω ^ 2)) (Ioi 0) := by
  refine hint.mono' hmeas (Eventually.of_forall fun ω => ?_)
  have h1 := denom_pos hβ M₁ ω
  have h2 := denom_pos hβ M₂ ω
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hS ω) h2.le)]
  exact div_le_div_of_nonneg_left (hS ω) h1 (by nlinarith [sq_nonneg ω])

/-- More inertia never increases the variance (`p ≥ 0`). -/
@[powerlib_foundation] theorem variance_antitone (hβ : β ≠ 0) (hS : ∀ ω, 0 ≤ S ω)
    (hM : M₁ ^ 2 ≤ M₂ ^ 2)
    (h₁ : IntegrableOn (fun ω => S ω / (β ^ 2 + M₁ ^ 2 * ω ^ 2)) (Ioi 0))
    (h₂ : IntegrableOn (fun ω => S ω / (β ^ 2 + M₂ ^ 2 * ω ^ 2)) (Ioi 0)) :
    variance S β M₂ ≤ variance S β M₁ := by
  refine setIntegral_mono h₂ h₁ fun ω => ?_
  have h1 := denom_pos hβ M₁ ω
  exact div_le_div_of_nonneg_left (hS ω) h1 (by nlinarith [sq_nonneg ω])

/-- `M² σ²(M)` is nondecreasing (`p ≤ 2`): `σ²(M₁) ≤ (M₂/M₁)² σ²(M₂)` for `0 < M₁ ≤ M₂`. -/
@[powerlib_foundation] theorem variance_le_sq_mul (hβ : β ≠ 0) (hS : ∀ ω, 0 ≤ S ω)
    (hM₁ : 0 < M₁) (hM : M₁ ≤ M₂)
    (h₁ : IntegrableOn (fun ω => S ω / (β ^ 2 + M₁ ^ 2 * ω ^ 2)) (Ioi 0))
    (h₂ : IntegrableOn (fun ω => S ω / (β ^ 2 + M₂ ^ 2 * ω ^ 2)) (Ioi 0)) :
    M₁ ^ 2 * variance S β M₁ ≤ M₂ ^ 2 * variance S β M₂ := by
  unfold variance
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_mono (h₁.const_mul _) (h₂.const_mul _) fun ω => ?_
  have h1 := denom_pos hβ M₁ ω
  have h2 := denom_pos hβ M₂ ω
  have hS' := hS ω
  rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ h1 h2]
  have hb : 0 < β ^ 2 := by positivity
  have hsq : M₁ ^ 2 ≤ M₂ ^ 2 := pow_le_pow_left₀ hM₁.le hM 2
  have : M₁ ^ 2 * (β ^ 2 + M₂ ^ 2 * ω ^ 2) ≤ M₂ ^ 2 * (β ^ 2 + M₁ ^ 2 * ω ^ 2) := by
    nlinarith
  calc M₁ ^ 2 * S ω * (β ^ 2 + M₂ ^ 2 * ω ^ 2) = S ω * (M₁ ^ 2 * (β ^ 2 + M₂ ^ 2 * ω ^ 2)) := by
        ring
    _ ≤ S ω * (M₂ ^ 2 * (β ^ 2 + M₁ ^ 2 * ω ^ 2)) := mul_le_mul_of_nonneg_left this hS'
    _ = M₂ ^ 2 * S ω * (β ^ 2 + M₁ ^ 2 * ω ^ 2) := by ring

/-- A power law `σ²(M) = c M^{−p}` matched at two inertia levels `M₁ < M₂` (with `σ² > 0`)
has exponent `0 ≤ p ≤ 2`. -/
@[powerlib_foundation] theorem powerLaw_exponent_mem (hβ : β ≠ 0) (hS : ∀ ω, 0 ≤ S ω)
    (hM₁ : 0 < M₁) (hM : M₁ < M₂)
    (h₁ : IntegrableOn (fun ω => S ω / (β ^ 2 + M₁ ^ 2 * ω ^ 2)) (Ioi 0))
    (h₂ : IntegrableOn (fun ω => S ω / (β ^ 2 + M₂ ^ 2 * ω ^ 2)) (Ioi 0))
    {c p : ℝ} (hc₁ : variance S β M₁ = c * M₁ ^ (-p)) (hc₂ : variance S β M₂ = c * M₂ ^ (-p))
    (hpos : 0 < variance S β M₂) : 0 ≤ p ∧ p ≤ 2 := by
  have hM₂ : 0 < M₂ := hM₁.trans hM
  have hsq : M₁ ^ 2 ≤ M₂ ^ 2 := pow_le_pow_left₀ hM₁.le hM.le 2
  have hanti := variance_antitone hβ hS hsq h₁ h₂
  have hsqm := variance_le_sq_mul hβ hS hM₁ hM.le h₁ h₂
  have hc : 0 < c := by
    rw [hc₂] at hpos
    exact pos_of_mul_pos_left hpos (Real.rpow_pos_of_pos hM₂ _).le
  have hratio : variance S β M₁ / variance S β M₂ = (M₂ / M₁) ^ p := by
    rw [hc₁, hc₂, Real.div_rpow hM₂.le hM₁.le, Real.rpow_neg hM₁.le, Real.rpow_neg hM₂.le]
    field_simp
  have hbase : 1 < M₂ / M₁ := (one_lt_div hM₁).2 hM
  constructor
  · have h1 : 1 ≤ (M₂ / M₁) ^ p := by
      rw [← hratio, le_div_iff₀ hpos]; linarith
    by_contra hp
    push Not at hp
    have := Real.rpow_lt_one_of_one_lt_of_neg hbase hp
    linarith
  · have h2 : (M₂ / M₁) ^ p ≤ (M₂ / M₁) ^ (2 : ℝ) := by
      rw [← hratio, div_le_iff₀ hpos, Real.div_rpow hM₂.le hM₁.le]
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    exact (Real.rpow_le_rpow_left_iff hbase).1 h2

/-- The note's Nordel data (`M`: 250 → 100 GW·s, `σ_Δf`: 6 → 18 mHz, i.e. variance ratio 9)
cannot come from the first-order model with any nonnegative PSD: the model allows at most
`(250/100)² = 6.25`. -/
@[powerlib_foundation] theorem nordel_not_explained (hβ : β ≠ 0) (hS : ∀ ω, 0 ≤ S ω)
    (h₁ : IntegrableOn (fun ω => S ω / (β ^ 2 + (100 : ℝ) ^ 2 * ω ^ 2)) (Ioi 0))
    (h₂ : IntegrableOn (fun ω => S ω / (β ^ 2 + (250 : ℝ) ^ 2 * ω ^ 2)) (Ioi 0)) :
    ¬ (variance S β 100 = 9 * variance S β 250 ∧ 0 < variance S β 250) := by
  rintro ⟨h, hpos⟩
  have := variance_le_sq_mul hβ hS (by norm_num : (0 : ℝ) < 100) (by norm_num) h₁ h₂
  rw [h] at this
  nlinarith

end Elasticity

/-! ## The two ends of the exponent range (§1.7) -/

section Asymptotics

variable {S : ℝ → ℝ} {β : ℝ}

/-- Two-point scaling exponent `p(M₁, M₂) = ln(σ²(M₁)/σ²(M₂)) / ln(M₂/M₁)` of the variance:
the exponent of the power law `σ² = c M^{−p}` through the two points. -/
def twoPointExponent (S : ℝ → ℝ) (β M₁ M₂ : ℝ) : ℝ :=
  Real.log (variance S β M₁ / variance S β M₂) / Real.log (M₂ / M₁)

/-- **Low-frequency end (`p → 0`).** For an integrable nonnegative PSD the variance tends to
`(∫ S)/β²` as the inertia vanishes: all the noise lies below the corner `ω_c = β/M → ∞`, where
`|H|² → 1/β²` does not depend on `M`. -/
@[powerlib_foundation] theorem variance_tendsto_zero (hβ : β ≠ 0) (hS : ∀ ω, 0 ≤ S ω)
    (hint : IntegrableOn S (Ioi 0)) :
    Tendsto (fun M => variance S β M) (𝓝 0) (𝓝 ((∫ ω in Ioi (0 : ℝ), S ω) / β ^ 2)) := by
  have hb : 0 < β ^ 2 := by positivity
  have hlim : (∫ ω in Ioi (0 : ℝ), S ω) / β ^ 2 = ∫ ω in Ioi (0 : ℝ), S ω / β ^ 2 :=
    (integral_div _ _).symm
  rw [hlim]
  unfold variance
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => S ω / β ^ 2) ?_ ?_
    (hint.div_const _) ?_
  · refine Eventually.of_forall fun M => ?_
    exact hint.aestronglyMeasurable.div₀ (by fun_prop : Continuous fun ω : ℝ =>
      β ^ 2 + M ^ 2 * ω ^ 2).aestronglyMeasurable
  · refine Eventually.of_forall fun M => Eventually.of_forall fun ω => ?_
    have hd : β ^ 2 ≤ β ^ 2 + M ^ 2 * ω ^ 2 := by nlinarith [sq_nonneg (M * ω)]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hS ω) (hb.trans_le hd).le)]
    exact div_le_div_of_nonneg_left (hS ω) hb hd
  · refine Eventually.of_forall fun ω => ?_
    have hc : Continuous fun M : ℝ => S ω / (β ^ 2 + M ^ 2 * ω ^ 2) :=
      continuous_const.div (by fun_prop) fun M => by
        have : 0 ≤ M ^ 2 * ω ^ 2 := by positivity
        linarith
    simpa using hc.tendsto 0

/-- **High-frequency end (`p → 2`).** If `S(ω)/ω²` is integrable, `M² σ²(M)` tends to
`∫ S/ω²` as the inertia grows: all the noise lies above the corner `ω_c = β/M → 0`, where
`|H|² ≈ 1/(M² ω²)`. -/
@[powerlib_foundation] theorem mul_variance_tendsto_atTop (hβ : β ≠ 0) (hS : ∀ ω, 0 ≤ S ω)
    (hint : IntegrableOn (fun ω => S ω / ω ^ 2) (Ioi 0)) :
    Tendsto (fun M => M ^ 2 * variance S β M) atTop
      (𝓝 (∫ ω in Ioi (0 : ℝ), S ω / ω ^ 2)) := by
  have hSm : AEStronglyMeasurable S (volume.restrict (Ioi (0 : ℝ))) := by
    refine (hint.aestronglyMeasurable.mul
      (continuous_pow 2).aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ω (hω : 0 < ω)
    simp only [Pi.mul_apply]
    field_simp
  unfold variance
  simp_rw [← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => S ω / ω ^ 2) ?_ ?_ hint ?_
  · refine Eventually.of_forall fun M => ?_
    exact (hSm.div₀ (by fun_prop : Continuous fun ω : ℝ =>
      β ^ 2 + M ^ 2 * ω ^ 2).aestronglyMeasurable).const_mul _
  · refine Eventually.of_forall fun M => ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ω (hω : 0 < ω)
    have hω2 : 0 < ω ^ 2 := by positivity
    have hb : 0 < β ^ 2 := by positivity
    have hden : 0 < β ^ 2 + M ^ 2 * ω ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg M) (div_nonneg (hS ω) hden.le)),
      mul_div_assoc', div_le_div_iff₀ hden hω2]
    nlinarith [hS ω, sq_nonneg β, mul_nonneg (hS ω) (sq_nonneg β)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ω (hω : 0 < ω)
    have hω2 : 0 < ω ^ 2 := by positivity
    have hinv : Tendsto (fun M : ℝ => β ^ 2 / M ^ 2 + ω ^ 2) atTop (𝓝 (0 + ω ^ 2)) := by
      have : Tendsto (fun M : ℝ => β ^ 2 / M ^ 2) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n := 2) (by norm_num))).const_mul (β ^ 2)
      exact this.add_const _
    rw [zero_add] at hinv
    have h := (tendsto_const_nhds (x := S ω)).div hinv hω2.ne'
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM
    have hM2 : 0 < M ^ 2 := by positivity
    show S ω / (β ^ 2 / M ^ 2 + ω ^ 2) = M ^ 2 * (S ω / (β ^ 2 + M ^ 2 * ω ^ 2))
    have hb : 0 < β ^ 2 := by positivity
    have hden : 0 < β ^ 2 + M ^ 2 * ω ^ 2 := by positivity
    field_simp

/-- **`p → 0` at small inertia.** For an integrable nonnegative PSD with `∫ S > 0`, the two-point
exponent between `M` and `κ M` (`κ > 1` fixed; the limit holds for every `κ`) tends to `0` as
`M → 0⁺`. -/
@[powerlib_foundation] theorem twoPointExponent_tendsto_zero (hβ : β ≠ 0) (hS : ∀ ω, 0 ≤ S ω)
    (hint : IntegrableOn S (Ioi 0)) (hpos : 0 < ∫ ω in Ioi (0 : ℝ), S ω) (κ : ℝ) :
    Tendsto (fun M => twoPointExponent S β M (κ * M)) (𝓝[>] 0) (𝓝 0) := by
  set L := (∫ ω in Ioi (0 : ℝ), S ω) / β ^ 2 with hLdef
  have hL : 0 < L := div_pos hpos (by positivity)
  have h0 := variance_tendsto_zero hβ hS hint
  have h1 : Tendsto (fun M => variance S β M) (𝓝[>] 0) (𝓝 L) := h0.mono_left nhdsWithin_le_nhds
  have hk : Tendsto (fun M : ℝ => κ * M) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ) (f := fun M : ℝ => κ * M)
  have h2 : Tendsto (fun M => variance S β (κ * M)) (𝓝[>] 0) (𝓝 L) :=
    (h0.comp hk).mono_left nhdsWithin_le_nhds
  have hratio := h1.div h2 hL.ne'
  rw [div_self hL.ne'] at hratio
  have hlog := ((Real.continuousAt_log one_ne_zero).tendsto.comp hratio).div_const (Real.log κ)
  rw [Real.log_one, zero_div] at hlog
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with M (hM : 0 < M)
  simp only [Function.comp_apply, twoPointExponent, Pi.div_apply]
  rw [mul_div_assoc, div_self hM.ne', mul_one]

/-- **`p → 2` at large inertia.** If `S(ω)/ω²` is integrable with positive integral, the
two-point exponent between `M` and `κ M` (`κ > 1` fixed) tends to `2` as `M → ∞`. -/
@[powerlib_foundation] theorem twoPointExponent_tendsto_two (hβ : β ≠ 0) (hS : ∀ ω, 0 ≤ S ω)
    (hint : IntegrableOn (fun ω => S ω / ω ^ 2) (Ioi 0))
    (hpos : 0 < ∫ ω in Ioi (0 : ℝ), S ω / ω ^ 2) {κ : ℝ} (hκ : 1 < κ) :
    Tendsto (fun M => twoPointExponent S β M (κ * M)) atTop (𝓝 2) := by
  set L := ∫ ω in Ioi (0 : ℝ), S ω / ω ^ 2 with hLdef
  have hκ0 : 0 < κ := by linarith
  have h1 := mul_variance_tendsto_atTop hβ hS hint
  have h2 : Tendsto (fun M => (κ * M) ^ 2 * variance S β (κ * M)) atTop (𝓝 L) :=
    h1.comp (tendsto_id.const_mul_atTop hκ0)
  have hratio := (h1.div h2 hpos.ne').const_mul (κ ^ 2)
  rw [div_self hpos.ne', mul_one] at hratio
  have hlog := ((Real.continuousAt_log (by positivity)).tendsto.comp hratio).div_const
    (Real.log κ)
  have hk : Real.log (κ ^ 2) / Real.log κ = 2 := by
    rw [Real.log_pow]
    field_simp [(Real.log_pos hκ).ne']
    norm_num
  rw [hk] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  simp only [Function.comp_apply, twoPointExponent, Pi.div_apply]
  have e1 : κ * M / M = κ := by field_simp
  have e2 : κ ^ 2 * (M ^ 2 * variance S β M / ((κ * M) ^ 2 * variance S β (κ * M))) =
      variance S β M / variance S β (κ * M) := by
    rw [show (κ * M) ^ 2 * variance S β (κ * M) = (κ ^ 2 * M ^ 2) * variance S β (κ * M) by ring,
      ← mul_div_assoc, show κ ^ 2 * (M ^ 2 * variance S β M) =
        (κ ^ 2 * M ^ 2) * variance S β M by ring, mul_div_mul_left _ _ (by positivity)]
  rw [e1, e2]

end Asymptotics

/-! ## Time scales (§1.1) -/

/-- Electromechanical time constant `T_em = 2H/ω_s`. -/
def electromechanicalTime (H ωs : ℝ) : ℝ := 2 * H / ωs

/-- Correction (§1.1): `T_em` is about 25 ms (`H = 4 s`, 50 Hz), not "several seconds". -/
@[powerlib_foundation] theorem electromechanicalTime_example :
    0.025 < electromechanicalTime 4 (2 * Real.pi * 50) ∧
      electromechanicalTime 4 (2 * Real.pi * 50) < 0.026 := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  unfold electromechanicalTime
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- Even `H = 10 s` gives `T_em < 0.07 s` at 50 Hz. -/
@[powerlib_foundation] theorem electromechanicalTime_lt {H : ℝ} (hH : H ≤ 10) :
    electromechanicalTime H (2 * Real.pi * 50) < 0.07 := by
  have h1 := Real.pi_gt_three
  unfold electromechanicalTime
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

end powerlib.Frequency.LowInertia
