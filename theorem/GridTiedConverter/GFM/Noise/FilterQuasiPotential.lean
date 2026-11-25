import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ControlledAction
import theorem.GridTiedConverter.GFM.Noise.FilterReversibility

/-! # Escape exponent of the noisy three-state GFM: Hamilton–Jacobi bounds

Domain module: the quasi-potential (Freidlin–Wentzell escape exponent) of the noisy GFM with
set-point noise, for the two-state model of `theorem/GridTiedConverter/GFM/Noise/Embedding.lean`
and the three-state model (VSM + power filter) of
`theorem/GridTiedConverter/GFM/Noise/FilterEmbedding.lean`, read through the generic
degenerate-noise objects of `theorem/Stochastic/ControlledAction.lean`. The noise acts on the
frequency row only (rank-one diffusion), so the positive-definite action of
`Stochastic.LargeDeviations` does not apply. The two-state model has the exact Hamilton–Jacobi
solution `(2D/σ_P²) H` (the Gibbs exponent `H/T`, `σ_P² = 2DT`); the three-state model has no
exact solution of that shape, and a subsolution bounds its escape exponent from below by
`(1 − A/(D ω_c))` times the two-state value `2D ΔU/σ_P²`.

Model boundary.
* Voltage source behind a lossy quasi-static line (`R ≥ 0`, `X > 0`), export-positive power
  `P(δ) = c₀ + A sin(δ − α)`, per unit, dq frame at nominal frequency (as in
  `GFM.Noise.Embedding`). Two-state: state `(δ, p)` on `Fin 2 → ℝ`, `p = M Δω`, drift
  `Params.swingDrift` (the noisy field at `w = 0`), set-point noise column `(0, σ_P)`.
  Three-state: state `(δ, ω, P_f)` on `Fin 3 → ℝ`, drift `Params3.sdeDrift` (the lossy VSM +
  filter field `δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P(δ) − P_f)`), set-point noise
  column `(0, σ_P/M, 0)`; `M, ω_c, A > 0`, `D ≥ 0`. In both, `noisyField_setPoint`: the
  controlled field is the noisy model with the set-point disturbance `ΔP = σ_P v` (control `v`).
* Only the power set-point channel (the grid-frequency and voltage channels are excluded); any
  damping reference (it does not enter at zero grid-frequency disturbance).
* The escape exponent is the deterministic quasi-potential `V(x_A, x)` (admissible pairs of
  `Stochastic.LDP.controlQuasiPotential`). The path-space large-deviation principle of the
  noisy model with this action as rate (Schilder, `theorem/Stochastic/Schilder.lean`, and the
  Freidlin–Wentzell LDP, `theorem/GridTiedConverter/GFM/Noise/FreidlinWentzell.lean`) is proved;
  the exit-time asymptotics `ε log E[τ_exit] → V(stable equilibrium, saddle)` are not formalized,
  and no statement here concerns the law of the exit time.
* Excluded as in `GFM.Noise.FilterEmbedding`.

Source: GFM counterpart study, note t2-noise item 7 (escape of the three-state model; its
minimum-action numerics, scratch notes outside the repository, are observations only and are not
used);
M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984), Ch. 4
(quasi-potential, Hamilton–Jacobi characterization); W. H. Fleming,
R. W. Rishel, *Deterministic and Stochastic Optimal Control* (1975), Ch. IV (verification
theorem); the two-state Gibbs density `theorem/GridTiedConverter/GFM/Noise/Escape.lean`.

Results.
* Two-state: `Params.hj_swing` (the swing energy scaled by `2D/σ_P²` solves the Hamilton–Jacobi
  equation exactly), `Params.swingQP_ge` (`V₂(x_A, x) ≥ (2D/σ_P²)(H(x) − H(x_A))`),
  `Params.swingQP_rest_ge` (between rest points: `V₂ ≥ 2D (U(δ_u) − U(δ_s))/σ_P²`,
  `U(δ) = Params.potential (δ − α)`; at the stable equilibrium and the saddle, the two-state
  value `2D ΔU/σ_P²`).
* Three-state: `Params3.hj_filter` (the Hamilton–Jacobi Hamiltonian of
  `c (M ω²/2 + U(δ) + (P_f − P(δ))²/(2A))`, `c = 2(D − A/ω_c)/σ_P²`, is
  `−c [(A/ω_c) ω² + (1 + cos(δ − α)) ω (P_f − P(δ)) + (ω_c/A)(P_f − P(δ))²] ≤ 0`),
  `Params3.setPointQP_ge`, `Params3.setPointQP_rest_ge` (`A ≤ D ω_c`:
  `V₃(x_s, x_u) ≥ 2(D − A/ω_c) ΔU/σ_P²`, the two-state value with `D` replaced by
  `D − A/ω_c`), `Params.liminf_setPointQP_ge` (`liminf_{ω_c → ∞} V₃ ≥ 2D ΔU/σ_P²`, the lower half
  of the limit).
* `Params3.hj_swingEnergy`: the exact two-state certificate read on three states has the
  Hamilton–Jacobi residual `−(2D/σ_P²) ω (P_f − P(δ))`, of either sign: it is not a subsolution.
* `Params3.hj_separable_const`: every solution of the Hamilton–Jacobi equation of the form
  `c M ω²/2 + G(δ, P_f)` (`G` with partial derivatives) is constant (`c = 0`, `G` constant): the
  two-state solution has no three-state extension by a function of the filter state.
* Upper bounds and limits are in `theorem/GridTiedConverter/GFM/Noise/EscapeExponent.lean`:
  `GFM.Noise.Params.swingQP_saddle_eq` (the two-state exponent equals `2D ΔU/σ_P²`) and
  `GFM.Noise.Params.tendsto_setPointQP` (`V₃ → 2D ΔU/σ_P²` as `ω_c → ∞`),
  `GFM.Noise.Params.setPointQP_lt_swingQP` (`V₃ < V₂` for every `ω_c` above the explicit
  threshold `escThreshold`), `GFM.Noise.Params.setPointQP_lt_swingQP_slow` (`V₃ < V₂` below an
  explicit small bandwidth). Not formalized: `V₃ < V₂` between the two.
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real Set Filter
open scoped ENNReal
open powerlib.Stochastic.LDP

local notation "π₂" i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i
local notation "π₃" i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i

/-! ## The two-state model -/

namespace Params

variable (p : Params)

/-- Drift of the noisy two-state model on `Fin 2 → ℝ` (state `(δ, M Δω)`): the noisy field at
zero disturbance. -/
def swingDrift (x : Fin 2 → ℝ) : Fin 2 → ℝ := p.noisyField 0 (WithLp.toLp 2 x) 0

/-- Set-point noise column of intensity `σ_P`, momentum row: `(0, σ_P)`. -/
def swingColumn (σP : ℝ) : Fin 2 → ℝ := ![0, σP]

/-- Quasi-potential of the two-state model with set-point noise. -/
def swingQP (σP : ℝ) (xA x : Fin 2 → ℝ) : ℝ≥0∞ :=
  controlQuasiPotential p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP) xA x

/-- Swing energy `H(δ, p) = p²/(2M) + U(δ)`, `U(δ) = V(δ − α)` (`Params.potential`). -/
def swingEnergy (x : Fin 2 → ℝ) : ℝ := x 1 ^ 2 / (2 * p.M) + p.potential (x 0 - p.α)

/-- Its derivative `dH = U'(δ) dδ + (p/M) dp`. -/
def swingEnergyDeriv (x : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  p.potentialDeriv (x 0 - p.α) • (π₂ 0) + (x 1 / p.M) • (π₂ 1)

@[tmio M, powerlib_domain] theorem swingDrift_apply (x : Fin 2 → ℝ) :
    p.swingDrift x =
      ![x 1 / p.M, p.Pref - (p.c0 + p.A * Real.sin (x 0 - p.α)) - p.D * (x 1 / p.M)] := by
  have hP := p.sourcePower_noise (x 0) 0 0
  simp only [add_zero, Complex.ofReal_zero, zero_mul, mul_zero, sub_zero] at hP
  ext i; fin_cases i <;> simp [swingDrift, noisyField, hP]

/-- **The skeleton is the noisy model**: the controlled field with control `v` is the noisy
two-state field with the set-point disturbance `ΔP = σ_P v`, any damping reference. -/
@[tmio M, powerlib_domain] theorem noisyField_setPoint (κ σP v : ℝ) (x : Fin 2 → ℝ) :
    p.noisyField κ (WithLp.toLp 2 x) ![σP * v, 0, 0, 0] =
      controlField p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP) x ![v] := by
  ext i; fin_cases i
  · simp [controlField, swingDrift, noisyField, swingColumn]
  · simp [controlField, swingDrift, noisyField, swingColumn]; ring

@[tmio M, powerlib_domain] theorem hasFDerivAt_swingEnergy (x : Fin 2 → ℝ) :
    HasFDerivAt p.swingEnergy (p.swingEnergyDeriv x) x := by
  have hU := (p.hasDerivAt_potential (x 0 - p.α)).comp_hasFDerivAt x
    ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 x).sub_const p.α)
  have hK := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 x).pow 2).const_mul
    (1 / (2 * p.M))
  have h := hK.add hU
  have hf : p.swingEnergy = fun y => 1 / (2 * p.M) * y 1 ^ 2 + (p.potential ∘ fun y => y 0 - p.α)
      y := by
    funext y; simp only [swingEnergy, Function.comp]; ring
  rw [hf]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have hM := p.M_pos.ne'
  simp [swingEnergyDeriv]
  field_simp
  ring

/-- **Exact Hamilton–Jacobi solution (two states)**: `W = (2D/σ_P²) H` satisfies
`dW(b) + ½ dW(σ)² = 0` at every state (`σ_P ≠ 0`). -/
@[tmio M, powerlib_domain] theorem hj_swing {σP : ℝ} (hσ : σP ≠ 0) (x : Fin 2 → ℝ) :
    hjHamiltonian p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP) x
      ((2 * p.D / σP ^ 2) • p.swingEnergyDeriv x) = 0 := by
  have hM := p.M_pos.ne'
  simp [hjHamiltonian, swingDrift_apply, swingEnergyDeriv, swingColumn, potentialDeriv, toSM]
  field_simp
  ring

/-- **Two-state lower bound**: `V₂(x_A, x) ≥ (2D/σ_P²)(H(x) − H(x_A))`. -/
@[tmio M, powerlib_domain] theorem swingQP_ge {σP : ℝ} (hσ : σP ≠ 0) (xA x : Fin 2 → ℝ) :
    ENNReal.ofReal (2 * p.D / σP ^ 2 * (p.swingEnergy x - p.swingEnergy xA)) ≤
      p.swingQP σP xA x := by
  have h := le_controlQuasiPotential (b := p.swingDrift)
    (σ := fun _ (_ : Fin 1) => swingColumn σP) (W := fun y => 2 * p.D / σP ^ 2 * p.swingEnergy y)
    (fun y => (p.hasFDerivAt_swingEnergy y).const_mul _) (fun y => (p.hj_swing hσ y).le) xA x
  rw [← mul_sub] at h
  exact h

/-- **Two-state escape exponent, lower bound**: from the rest point `(δ_s, 0)` to the rest point
`(δ_u, 0)` (in particular from the stable equilibrium to the saddle),
`V₂ ≥ 2D (U(δ_u) − U(δ_s))/σ_P²`. -/
@[tmio M, powerlib_domain] theorem swingQP_rest_ge {σP : ℝ} (hσ : σP ≠ 0) (δs δu : ℝ) :
    ENNReal.ofReal (2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2) ≤
      p.swingQP σP ![δs, 0] ![δu, 0] := by
  convert p.swingQP_ge hσ ![δs, 0] ![δu, 0] using 2
  simp [swingEnergy]
  ring

end Params

/-! ## The three-state model -/

namespace Params3

variable (p : Params3)

/-- Set-point noise column of intensity `σ_P`: `(0, σ_P/M, 0)` (`σ_P` times the `ΔP` column of
`Params3.noiseMatrix`). -/
def setPointColumn (σP : ℝ) : Fin 3 → ℝ := ![0, σP / p.M, 0]

/-- Quasi-potential (escape exponent) of the three-state model with set-point noise. -/
def setPointQP (σP : ℝ) (xA x : Fin 3 → ℝ) : ℝ≥0∞ :=
  controlQuasiPotential p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) xA x

/-- Candidate quasi-potential `M ω²/2 + U(δ) + (P_f − P(δ))²/(2A)`: the swing energy plus a
penalty on the filter lag. -/
def filterEnergy (x : Fin 3 → ℝ) : ℝ :=
  p.M * x 1 ^ 2 / 2 + p.potential (x 0 - p.α) + (x 2 - p.toLossy.Pe (x 0)) ^ 2 / (2 * p.A)

/-- Its derivative. -/
def filterEnergyDeriv (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (p.potentialDeriv (x 0 - p.α) - (x 2 - p.toLossy.Pe (x 0)) * Real.cos (x 0 - p.α)) • (π₃ 0) +
    (p.M * x 1) • (π₃ 1) + ((x 2 - p.toLossy.Pe (x 0)) / p.A) • (π₃ 2)

/-- **The skeleton is the noisy model**: the controlled field with control `v` is the noisy
three-state field with the set-point disturbance `ΔP = σ_P v`, any damping reference. -/
@[tmio M, powerlib_domain] theorem noisyField_setPoint (κ σP v : ℝ) (x : Fin 3 → ℝ) :
    p.noisyField κ (WithLp.toLp 2 x) ![σP * v, 0, 0, 0] =
      controlField p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) x ![v] := by
  rw [noisyField_eq]
  ext i; fin_cases i
  · simp [controlField, sdeDrift, setPointColumn, noiseMatrix]
  · simp [controlField, sdeDrift, setPointColumn, noiseMatrix]; ring
  · simp [controlField, sdeDrift, setPointColumn, noiseMatrix]

@[tmio M, powerlib_domain] private theorem hasDerivAt_Pe (δ : ℝ) :
    HasDerivAt p.toLossy.Pe (p.A * Real.cos (δ - p.α)) δ := by
  have h := (((Real.hasDerivAt_sin (δ - p.α)).comp δ ((hasDerivAt_id δ).sub_const p.α)).const_mul
    p.A).const_add p.c0
  convert h using 1
  · funext t; simp [VSMLPFLossy.Pe, toLossy]
  · simp

@[tmio M, powerlib_domain] theorem hasFDerivAt_filterEnergy (x : Fin 3 → ℝ) :
    HasFDerivAt p.filterEnergy (p.filterEnergyDeriv x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 x
  have hU := (p.hasDerivAt_potential (x 0 - p.α)).comp_hasFDerivAt x (h0.sub_const p.α)
  have hPe := (p.hasDerivAt_Pe (x 0)).comp_hasFDerivAt x h0
  have hK := (h1.pow 2).const_mul (p.M / 2)
  have hL := ((h2.sub hPe).pow 2).const_mul (1 / (2 * p.A))
  have h := (hK.add hU).add hL
  have hf : p.filterEnergy = fun y => (p.M / 2 * y 1 ^ 2 + (p.potential ∘ fun y => y 0 - p.α) y) +
      1 / (2 * p.A) * (y 2 - (p.toLossy.Pe ∘ fun y => y 0) y) ^ 2 := by
    funext y; simp only [filterEnergy, Function.comp]; ring
  rw [hf]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have hA := p.A_pos.ne'
  simp [filterEnergyDeriv]
  field_simp
  ring

/-- **Hamilton–Jacobi Hamiltonian of the filter-lag candidate**: with `y = P_f − P(δ)` and
`c = 2(D − A/ω_c)/σ_P²`, `H(x, c dE(x)) = −c [(A/ω_c) ω² + (1 + cos(δ − α)) ω y + (ω_c/A) y²]`
(`σ_P ≠ 0`). -/
@[tmio M, powerlib_domain] theorem hj_filter {σP : ℝ} (hσ : σP ≠ 0) (x : Fin 3 → ℝ) :
    hjHamiltonian p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) x
      ((2 * (p.D - p.A / p.ωc) / σP ^ 2) • p.filterEnergyDeriv x) =
      -(2 * (p.D - p.A / p.ωc) / σP ^ 2) * (p.A / p.ωc * x 1 ^ 2 +
        (1 + Real.cos (x 0 - p.α)) * x 1 * (x 2 - p.toLossy.Pe (x 0)) +
          p.ωc / p.A * (x 2 - p.toLossy.Pe (x 0)) ^ 2) := by
  have hM := p.M_pos.ne'
  have hA := p.A_pos.ne'
  have hω := p.ωc_pos.ne'
  simp [hjHamiltonian, sdeDrift_apply, filterEnergyDeriv, setPointColumn, Params.potentialDeriv,
    Params.toSM, VSMLPFLossy.Pe, toLossy]
  field_simp
  ring

/-- The quadratic form of `hj_filter` is nonnegative: `1 + cos ∈ [0, 2]`. -/
@[tmio M, powerlib_domain] private theorem lag_form_nonneg {a w y cs : ℝ} (ha : 0 < a)
    (hcs : |cs| ≤ 1) : 0 ≤ a * w ^ 2 + (1 + cs) * w * y + a⁻¹ * y ^ 2 := by
  have hk : 0 ≤ 1 - (1 + cs) ^ 2 / 4 := by
    have := abs_le.mp hcs; nlinarith
  have e : a * w ^ 2 + (1 + cs) * w * y + a⁻¹ * y ^ 2 =
      a * (w + a⁻¹ * ((1 + cs) / 2) * y) ^ 2 + a⁻¹ * (1 - (1 + cs) ^ 2 / 4) * y ^ 2 := by
    field_simp; ring
  rw [e]
  have := inv_pos.mpr ha
  positivity

/-- **Hamilton–Jacobi subsolution (three states)**: for `A ≤ D ω_c`, `c dE` with
`c = 2(D − A/ω_c)/σ_P² ≥ 0` satisfies `H ≤ 0` at every state. -/
@[tmio M, powerlib_domain] theorem hj_filter_nonpos {σP : ℝ} (hσ : σP ≠ 0)
    (hA : p.A ≤ p.D * p.ωc) (x : Fin 3 → ℝ) :
    hjHamiltonian p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) x
      ((2 * (p.D - p.A / p.ωc) / σP ^ 2) • p.filterEnergyDeriv x) ≤ 0 := by
  rw [p.hj_filter hσ]
  have hω := p.ωc_pos
  have hc : 0 ≤ 2 * (p.D - p.A / p.ωc) / σP ^ 2 := by
    have : p.A / p.ωc ≤ p.D := (div_le_iff₀ hω).mpr hA
    positivity
  have hq := lag_form_nonneg (a := p.A / p.ωc) (w := x 1) (y := x 2 - p.toLossy.Pe (x 0))
    (div_pos p.A_pos hω) (abs_cos_le_one (x 0 - p.α))
  rw [inv_div] at hq
  nlinarith

/-- **The two-state certificate is not a three-state subsolution**: for the gradient
`(2D/σ_P²)(U'(δ) dδ + M ω dω)` of the swing energy `(2D/σ_P²)(M ω²/2 + U(δ))` (exact for two
states, `Params.hj_swing`), the three-state Hamilton–Jacobi Hamiltonian is
`−(2D/σ_P²) ω (P_f − P(δ))`, positive wherever the frequency and the filter lag have opposite
signs (`D > 0`): the filter-lag term of `filterEnergy` and the reduced factor `D − A/ω_c` of
`hj_filter` repair it. -/
@[tmio M, powerlib_domain] theorem hj_swingEnergy {σP : ℝ} (hσ : σP ≠ 0) (x : Fin 3 → ℝ) :
    hjHamiltonian p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) x
      ((2 * p.D / σP ^ 2) • (p.potentialDeriv (x 0 - p.α) • (π₃ 0) + (p.M * x 1) • (π₃ 1))) =
      -(2 * p.D / σP ^ 2) * x 1 * (x 2 - p.toLossy.Pe (x 0)) := by
  have hM := p.M_pos.ne'
  simp [hjHamiltonian, sdeDrift_apply, setPointColumn, Params.potentialDeriv, Params.toSM,
    VSMLPFLossy.Pe, toLossy]
  field_simp
  ring

/-- **Three-state lower bound**: for `A ≤ D ω_c`,
`V₃(x_A, x) ≥ (2(D − A/ω_c)/σ_P²)(E(x) − E(x_A))`, `E = filterEnergy`. -/
@[tmio M, powerlib_domain] theorem setPointQP_ge {σP : ℝ} (hσ : σP ≠ 0) (hA : p.A ≤ p.D * p.ωc)
    (xA x : Fin 3 → ℝ) :
    ENNReal.ofReal (2 * (p.D - p.A / p.ωc) / σP ^ 2 * (p.filterEnergy x - p.filterEnergy xA)) ≤
      p.setPointQP σP xA x := by
  have h := le_controlQuasiPotential (b := p.sdeDrift)
    (σ := fun _ (_ : Fin 1) => p.setPointColumn σP)
    (W := fun y => 2 * (p.D - p.A / p.ωc) / σP ^ 2 * p.filterEnergy y)
    (fun y => (p.hasFDerivAt_filterEnergy y).const_mul _) (fun y => p.hj_filter_nonpos hσ hA y)
    xA x
  rw [← mul_sub] at h
  exact h

/-- **Three-state escape exponent, lower bound**: from the rest point `(δ_s, 0, P(δ_s))` to the
rest point `(δ_u, 0, P(δ_u))` of the slow set (in particular from the stable equilibrium to the
saddle), for `A ≤ D ω_c`, `V₃ ≥ 2(D − A/ω_c)(U(δ_u) − U(δ_s))/σ_P²`: the two-state value
(`Params.swingQP_rest_ge`) with the damping `D` replaced by `D − A/ω_c`. -/
@[tmio M, powerlib_domain] theorem setPointQP_rest_ge {σP : ℝ} (hσ : σP ≠ 0)
    (hA : p.A ≤ p.D * p.ωc) (δs δu : ℝ) :
    ENNReal.ofReal (2 * (p.D - p.A / p.ωc) *
        (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2) ≤
      p.setPointQP σP ![δs, 0, p.toLossy.Pe δs] ![δu, 0, p.toLossy.Pe δu] := by
  convert p.setPointQP_ge hσ hA ![δs, 0, p.toLossy.Pe δs] ![δu, 0, p.toLossy.Pe δu] using 2
  simp [filterEnergy]
  ring

/-- The Hamilton–Jacobi Hamiltonian of `c M ω²/2 + G(δ, P_f)` in coordinates, with the partial
derivatives `G_δ`, `G_z` at `(δ, P_f)`. -/
@[tmio M, powerlib_domain] private theorem hj_separable_apply (σP c : ℝ) (gδ gz : ℝ)
    (x : Fin 3 → ℝ) :
    hjHamiltonian p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) x
      (gδ • (π₃ 0) + (c * p.M * x 1) • (π₃ 1) + gz • (π₃ 2)) =
      gδ * x 1 + c * x 1 * (p.Pref - x 2 - p.D * x 1) +
        gz * (p.ωc * (p.toLossy.Pe (x 0) - x 2)) + 1 / 2 * (c * x 1 * σP) ^ 2 := by
  have hM := p.M_pos.ne'
  simp [hjHamiltonian, sdeDrift_apply, setPointColumn]
  field_simp

/-- **No exact solution of the separable shape**: if `W = c M ω²/2 + G(δ, P_f)` (`G` with partial
derivatives `G_δ`, `G_z` everywhere) solves the Hamilton–Jacobi equation
`H(x, dW(x)) = 0` at every state, then `c = 0` and `G` is constant: the exact two-state solution
`(2D/σ_P²)(M ω²/2 + U(δ))` (`Params.hj_swing`) has no three-state extension by a function of the
filter state, for every noise intensity. (The `ω`-linear part forces `G_δ = c (P_f − P_ref)`,
the `ω`-free part `G_z = 0` off the slow set `P_f = P(δ)`.) -/
@[tmio M, powerlib_domain] theorem hj_separable_const {σP c : ℝ} {G Gδ Gz : ℝ → ℝ → ℝ}
    (hδ : ∀ a z, HasDerivAt (fun t => G t z) (Gδ a z) a)
    (hz : ∀ a z, HasDerivAt (fun s => G a s) (Gz a z) z)
    (hHJ : ∀ x : Fin 3 → ℝ,
      hjHamiltonian p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) x
        (Gδ (x 0) (x 2) • (π₃ 0) + (c * p.M * x 1) • (π₃ 1) + Gz (x 0) (x 2) • (π₃ 2)) = 0) :
    c = 0 ∧ ∀ a b z w, G a z = G b w := by
  have hω := p.ωc_pos.ne'
  have key : ∀ a ω z, Gδ a z * ω + c * ω * (p.Pref - z - p.D * ω) +
      Gz a z * (p.ωc * (p.toLossy.Pe a - z)) + 1 / 2 * (c * ω * σP) ^ 2 = 0 := by
    intro a ω z
    have h := hHJ ![a, ω, z]
    rw [hj_separable_apply] at h
    simpa using h
  -- `ω = 0`: `G_z = 0` off the slow set
  have hz0 : ∀ a z, p.toLossy.Pe a ≠ z → Gz a z = 0 := by
    intro a z hne
    have h := key a 0 z
    have : p.ωc * (p.toLossy.Pe a - z) * Gz a z = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hω (sub_ne_zero.mpr hne))
  -- `ω = ±1`: `G_δ = c (P_f − P_ref)`
  have hδc : ∀ a z, Gδ a z = c * (z - p.Pref) := by
    intro a z
    linear_combination (key a 1 z - key a (-1) z) / 2
  have hPe : ∀ a, p.toLossy.Pe a ≤ p.c0 + p.A := fun a => by
    have := Real.sin_le_one (a - p.α)
    have hA := p.A_pos
    simp only [VSMLPFLossy.Pe, toLossy]
    nlinarith
  -- `G(1, z) − G(0, z) = c (z − P_ref)`
  have hstep : ∀ z, G 1 z - G 0 z = c * (z - p.Pref) := by
    intro z
    have hd : ∀ t, HasDerivAt (fun t => G t z - c * (z - p.Pref) * t) 0 t := fun t =>
      ((hδ t z).sub ((hasDerivAt_id' t).const_mul (c * (z - p.Pref)))).congr_deriv
        (by rw [hδc]; ring)
    have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv)
      1 0
    linarith
  have hc : c = 0 := by
    set z₁ := p.c0 + p.A + 1
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => G 1 s - G 0 s)
      (fun s => Gz 1 s - Gz 0 s) (show z₁ < z₁ + 1 by linarith)
      (fun s _ => ((hz 1 s).sub (hz 0 s)).continuousAt.continuousWithinAt)
      (fun s _ => (hz 1 s).sub (hz 0 s))
    have h1 : Gz 1 ξ = 0 := hz0 1 ξ (by linarith [hPe 1, hξ.1])
    have h0 : Gz 0 ξ = 0 := hz0 0 ξ (by linarith [hPe 0, hξ.1])
    rw [h1, h0, hstep, hstep] at hslope
    have : c * 1 = 0 := by
      have e : z₁ + 1 - z₁ = 1 := by ring
      rw [e, div_one] at hslope
      linarith
    linarith
  refine ⟨hc, ?_⟩
  -- with `c = 0`: `G` does not depend on the angle, and its `P_f`-derivative vanishes
  have hangle : ∀ a z, G a z = G 0 z := by
    intro a z
    have hd : ∀ t, HasDerivAt (fun t => G t z) 0 t := fun t => by
      simpa [hδc, hc] using hδ t z
    exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) a 0
  have hk : ∀ s, HasDerivAt (fun s => G 0 s) 0 s := by
    intro s
    obtain ⟨a, ha⟩ : ∃ a, p.toLossy.Pe a ≠ s := by
      by_cases hs : s = p.c0 + p.A
      · refine ⟨p.α - π / 2, ?_⟩
        simp only [VSMLPFLossy.Pe, toLossy, sub_sub_cancel_left, Real.sin_neg, Real.sin_pi_div_two]
        have := p.A_pos
        intro h; linarith
      · refine ⟨p.α + π / 2, ?_⟩
        simp only [VSMLPFLossy.Pe, toLossy, add_sub_cancel_left, Real.sin_pi_div_two, mul_one]
        exact fun h => hs h.symm
    have hfun : (fun s => G a s) = fun s => G 0 s := funext fun s => hangle a s
    have h := hz a s
    rw [hfun, hz0 a s ha] at h
    exact h
  intro a b z w
  rw [hangle a z, hangle b w]
  exact is_const_of_deriv_eq_zero (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) z w

end Params3

/-! ## The fast-filter limit (lower half) -/

namespace Params

variable (p : Params)

/-- **Lower half of the limit `ω_c → ∞`**: for the three-state models
`⟨p, ω_c⟩` (`ω_c > 0`) built on the two-state parameters `p` (`D > 0`), between the rest points
`(δ_s, 0, P(δ_s))` and `(δ_u, 0, P(δ_u))`,
`liminf_{ω_c → ∞} V₃ ≥ 2D (U(δ_u) − U(δ_s))/σ_P²`, the two-state value
(`Params.swingQP_rest_ge`; from `Params3.setPointQP_rest_ge`). -/
@[tmio M, powerlib_domain] theorem liminf_setPointQP_ge (hD : 0 < p.D) {σP : ℝ} (hσ : σP ≠ 0)
    (δs δu : ℝ) :
    ENNReal.ofReal (2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2) ≤
      liminf (fun ωc : Ioi (0 : ℝ) => (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).setPointQP σP
        ![δs, 0, p.c0 + p.A * Real.sin (δs - p.α)] ![δu, 0, p.c0 + p.A * Real.sin (δu - p.α)])
        atTop := by
  set ΔU := p.potential (δu - p.α) - p.potential (δs - p.α)
  have hcoe : Tendsto (fun ωc : Ioi (0 : ℝ) => (ωc : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have ht : Tendsto (fun ωc : Ioi (0 : ℝ) =>
      ENNReal.ofReal (2 * (p.D - p.A / ωc) * ΔU / σP ^ 2)) atTop
      (nhds (ENNReal.ofReal (2 * p.D * ΔU / σP ^ 2))) := by
    apply ENNReal.tendsto_ofReal
    have h := ((((tendsto_inv_atTop_zero.comp hcoe).const_mul p.A).const_sub p.D).const_mul
      2).mul_const ΔU |>.div_const (σP ^ 2)
    simpa [div_eq_mul_inv] using h
  have hA : ∀ᶠ ωc : Ioi (0 : ℝ) in atTop, p.A ≤ p.D * ωc := by
    filter_upwards [hcoe.eventually_ge_atTop (p.A / p.D)] with ωc h
    rwa [div_le_iff₀ hD, mul_comm] at h
  refine le_of_forall_lt fun b hb => ?_
  obtain ⟨b', hbb', hb'⟩ := exists_between hb
  refine lt_of_lt_of_le hbb' (Filter.le_liminf_of_le (by isBoundedDefault) ?_)
  filter_upwards [ht.eventually_const_lt hb', hA] with ωc h1 h2
  refine h1.le.trans ?_
  have := (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).setPointQP_rest_ge hσ h2 δs δu
  simpa [VSMLPFLossy.Pe, Params3.toLossy] using this

end Params

end powerlib.GFM.Noise
