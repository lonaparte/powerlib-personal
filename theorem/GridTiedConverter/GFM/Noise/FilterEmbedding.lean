import dependencies.Mathlib
import theorem.Attributes
import theorem.GridTiedConverter.GFM.VSMLPFLossy
import theorem.GridTiedConverter.GFM.Noise.Embedding

/-! # Noise channels of the three-state GFM (VSM + power filter): exact rows, Itô and Stratonovich

Domain module: the grid-forming converter of `theorem/GridTiedConverter/GFM/Noise/Embedding.lean`
(voltage source behind a lossy quasi-static line) with a first-order filter on the measured active
power, the three-state model `GFM.VSMLPFLossy`, with the same four disturbance channels (power
set-point, grid frequency, d- and q-axis grid voltage). Every channel enters affinely and exactly;
the voltage channels enter through the filter. All statements are algebraic or calculus identities
at one state (diffusion matrix, Itô expression for an arbitrary Hessian, Stratonovich drift
correction); no SDE solution, law or expectation is formalized (Rules §3).

Model boundary.
* Source `E∠δ` (constant `E > 0`) behind the series impedance `R + jX` (`R ≥ 0`, `X > 0`) into the
  grid voltage `v_g = (V + ξ_d) + j ξ_q` (`V > 0`), per unit, dq frame rotating at the nominal
  frequency, single-phase equivalent; the active power at the source `GFM.Noise.Params.sourcePower`
  is export-positive (GFM convention, `theorem/GridTiedConverter/GFM/VSMLPF.lean`), from
  `S̄ = V̄ Ī*` with the current positive out of the converter.
* State `x = (δ, ω, P_f)` (`Dynamics.State 3`, in this order): angle relative to the grid,
  frequency deviation (not momentum), filtered power. VSM synchronization with a first-order power
  filter: `δ̇ = ω − ω_g`, `M ω̇ = P_ref + ΔP − P_f − D (ω − κ ω_g)`,
  `Ṗ_f = ω_c (P(δ, V + ξ_d + j ξ_q) − P_f)`; `M, ω_c > 0`, `D ≥ 0` (`Params3`). Disturbances
  `w = (ΔP, ω_g, ξ_d, ξ_q)`; `κ` selects the damping reference (`κ = 0` nominal frequency, `κ = 1`
  the grid frequency). Undisturbed, the field is `GFM.VSMLPFLossy.field` of
  `Params3.toLossy` (`c₀ = E²R/|Z|²`, `A = E V/|Z|`, `α = arg(X + jR)`).
* The disturbances are white-noise channels with intensities `σ = (σ_P, ε, σ_d, σ_q)` (diffusion
  `h = B(δ) diag σ`); the Itô correction is the expression `Stochastic.SPH.itoCorrection` at an
  arbitrary symmetric Hessian (no constant-structure energy is assumed), the Stratonovich drift
  correction `Stochastic.SPH.stratCorrection` with the derivatives of `h` computed by `fderiv`.
* Excluded: line and filter-capacitor dynamics, inner voltage/current loops, Q–V droop (constant
  `E`), PLL, delay, PWM, current limiting; continuous time.

Source: GFM counterpart study, note t2-noise item 3 and script s8 (three-state Stratonovich and Itô
terms; derived and checked symbolically, scratch notes outside the repository); work-sync
`theory/T-sph.md` §1.2, §1.5 (generator, Itô/Stratonovich drift conversion); Kundur, *Power
System Stability and Control* (1994), Ch. 6 (power through a series impedance); the two-state
counterpart `theorem/GridTiedConverter/GFM/Noise/Embedding.lean`.

Results.
* `Params3.noisyField_eq`: the disturbed field is the lossy three-state field
  `GFM.VSMLPFLossy.field` plus `B(δ) w` exactly, with the noise matrix
  `B(δ) = !![0, −1, 0, 0; 1/M, κ D/M, 0, 0; 0, 0, ω_c k sin(δ − α), −ω_c k cos(δ − α)]`
  (`k = E/|Z|`, from `GFM.Noise.Params.sourcePower_noise`): the voltage noise reaches the
  frequency only through the filter state.
* `Params3.diffusion_mul_transpose`: `h hᵀ` is block diagonal, `(δ, ω)` block
  `!![ε², −κ D ε²/M; −κ D ε²/M, (σ_P² + κ² D² ε²)/M²]`, filter entry
  `ω_c² k² (σ_d² sin²(δ − α) + σ_q² cos²(δ − α))`.
* `Params3.ito_eq`: for every Hessian `K` of any candidate energy,
  `Δ_Itô = ½ (ε² K₀₀ − κ D ε²/M (K₀₁ + K₁₀) + (σ_P² + κ² D² ε²)/M² K₁₁ +
  ω_c² k² (σ_d² sin² + σ_q² cos²) K₂₂)`: with nominal damping only diagonal Hessian entries enter,
  and an energy with `K₁₁ = M` (any extension of the swing kinetic energy) gives the set-point term
  `σ_P²/(2M)` of the two-state model (`GFM.Noise.Params.ito_eq`).
* `Params3.strat_eq_zero`: the Stratonovich drift correction of the merged noise vanishes for every
  channel, both damping references and state-dependent voltage rows: the only state-dependent
  entries are the filter-row voltage entries, which depend on the angle only, while the angle row
  of those columns is zero. The Itô and Stratonovich drifts coincide, as for two states
  (`GFM.Noise.Params.strat_eq_zero`).
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real Matrix
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two)
open powerlib.Stochastic.SPH

/-- Parameters of the three-state GFM on a lossy line: the two-state parameters and the power
filter bandwidth `ω_c > 0`. -/
structure Params3 extends Params where
  ωc : ℝ
  ωc_pos : 0 < ωc

namespace Params3

variable (p : Params3)

/-- The undisturbed model: the lossy VSM + filter `⟨M, D, ω_c, P_ref, c₀, A, α⟩`. -/
def toLossy : VSMLPFLossy :=
  ⟨p.M, p.D, p.ωc, p.Pref, p.c0, p.A, p.α⟩

/-- Noise matrix at the angle `δ` (columns: set-point `ΔP`, grid frequency `ω_g`, grid voltage
`ξ_d`, `ξ_q`; `κ` the damping reference). -/
def noiseMatrix (κ δ : ℝ) : Matrix (Fin 3) (Fin 4) ℝ :=
  !![0, -1, 0, 0;
     1 / p.M, κ * p.D / p.M, 0, 0;
     0, 0, p.ωc * (p.k * Real.sin (δ - p.α)), -(p.ωc * (p.k * Real.cos (δ - p.α)))]

/-- Disturbed field at the state `x = (δ, ω, P_f)` and the disturbance values
`w = (ΔP, ω_g, ξ_d, ξ_q)`: `δ̇ = ω − ω_g`, `ω̇ = (P_ref + ΔP − P_f − D (ω − κ ω_g))/M`,
`Ṗ_f = ω_c (P(δ, V + ξ_d + j ξ_q) − P_f)`. -/
def noisyField (κ : ℝ) (x : State 3) (w : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![x 1 - w 1, (p.Pref + w 0 - x 2 - p.D * (x 1 - κ * w 1)) / p.M,
    p.ωc * (p.sourcePower (x 0) (((p.V + w 2 : ℝ) : ℂ) + (w 3 : ℂ) * Complex.I) - x 2)]

/-- **Affine reading**: the disturbed field is the lossy three-state field plus `B(δ) w`,
exactly. -/
@[tmio M, powerlib_domain] theorem noisyField_eq (κ : ℝ) (x : State 3) (w : Fin 4 → ℝ) :
    p.noisyField κ x w = WithLp.ofLp (p.toLossy.field x) + p.noiseMatrix κ (x 0) *ᵥ w := by
  have hP := p.sourcePower_noise (x 0) (w 2) (w 3)
  simp only [Complex.ofReal_add] at hP
  have hM := p.M_pos.ne'
  ext i; fin_cases i
  · simp [noisyField, noiseMatrix, VSMLPFLossy.field, dotProduct, Fin.sum_univ_four, mk3]
    ring
  · simp [noisyField, noiseMatrix, VSMLPFLossy.field, toLossy, dotProduct, Fin.sum_univ_four,
      mk3]
    field_simp
    ring
  · simp [noisyField, noiseMatrix, VSMLPFLossy.field, VSMLPFLossy.Pe, toLossy, dotProduct,
      Fin.sum_univ_four, mk3, hP]
    ring

/-- Diffusion `h = B(δ) diag σ`, `σ = (σ_P, ε, σ_d, σ_q)`. -/
def diffusion (κ : ℝ) (σ : Fin 4 → ℝ) (δ : ℝ) : Matrix (Fin 3) (Fin 4) ℝ :=
  p.noiseMatrix κ δ * diagonal σ

@[tmio M, powerlib_domain] theorem diffusion_apply (κ : ℝ) (σ : Fin 4 → ℝ) (δ : ℝ) (i : Fin 3)
    (j : Fin 4) : p.diffusion κ σ δ i j = p.noiseMatrix κ δ i j * σ j := mul_diagonal _ _ _ _

/-- `h hᵀ` is block diagonal: the `(δ, ω)` block of the set-point and frequency channels and the
filter entry of the voltage channels. -/
@[tmio M, powerlib_domain] theorem diffusion_mul_transpose (κ : ℝ) (σ : Fin 4 → ℝ) (δ : ℝ) :
    p.diffusion κ σ δ * (p.diffusion κ σ δ)ᵀ =
      !![σ 1 ^ 2, -(κ * p.D * σ 1 ^ 2 / p.M), 0;
         -(κ * p.D * σ 1 ^ 2 / p.M), (σ 0 ^ 2 + κ ^ 2 * p.D ^ 2 * σ 1 ^ 2) / p.M ^ 2, 0;
         0, 0, p.ωc ^ 2 * p.k ^ 2 *
           (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 + σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2)] := by
  have hM := p.M_pos.ne'
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diffusion_apply, noiseMatrix, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp

/-- **Itô correction for an arbitrary Hessian** `K` (any candidate energy):
`Δ_Itô = ½ (ε² K₀₀ − κ D ε²/M (K₀₁ + K₁₀) + (σ_P² + κ² D² ε²)/M² K₁₁ +
ω_c² k² (σ_d² sin²(δ − α) + σ_q² cos²(δ − α)) K₂₂)`. -/
@[tmio M, powerlib_domain] theorem ito_eq (κ : ℝ) (σ : Fin 4 → ℝ) (δ : ℝ)
    (K : Matrix (Fin 3) (Fin 3) ℝ) :
    itoCorrection (p.diffusion κ σ δ) K =
      1 / 2 * (σ 1 ^ 2 * K 0 0 - κ * p.D * σ 1 ^ 2 / p.M * (K 0 1 + K 1 0) +
        (σ 0 ^ 2 + κ ^ 2 * p.D ^ 2 * σ 1 ^ 2) / p.M ^ 2 * K 1 1 +
        p.ωc ^ 2 * p.k ^ 2 * (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 +
          σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2) * K 2 2) := by
  unfold itoCorrection
  rw [diffusion_mul_transpose]
  rw [Matrix.trace_fin_three]
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-! ## Stratonovich correction -/

/-- **Stratonovich = Itô for every three-state channel**: the drift correction
`c_k = ½ Σ_{j,l} h_{lj} ∂_l h_{kj}` of the merged noise vanishes (`∂h` by `fderiv`): the only
state-dependent entries are the filter-row voltage entries, which depend on the angle only, while
the angle row of those columns is zero. -/
@[tmio M, powerlib_domain] theorem strat_eq_zero (κ : ℝ) (σ : Fin 4 → ℝ) (x : State 3) :
    stratCorrection (p.diffusion κ σ (x 0))
      (fun k j l => fderiv ℝ (fun y : State 3 => p.diffusion κ σ (y 0) k j) x
        (EuclideanSpace.single l 1)) = 0 := by
  have hd : ∀ k j, Differentiable ℝ (fun t => p.diffusion κ σ t k j) := by
    intro k j
    fin_cases k <;> fin_cases j <;>
      simp [diffusion_apply, noiseMatrix] <;> fun_prop
  have hf : ∀ k j (v : State 3), fderiv ℝ (fun y : State 3 => p.diffusion κ σ (y 0) k j) x v =
      deriv (fun t => p.diffusion κ σ t k j) (x 0) * v 0 := by
    intro k j v
    have h := ((hd k j (x 0)).hasDerivAt).comp_hasFDerivAt x
      ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x))
    have h' : HasFDerivAt (fun y : State 3 => p.diffusion κ σ (y 0) k j)
        (deriv (fun t => p.diffusion κ σ t k j) (x 0) •
          (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State 3 →L[ℝ] ℝ)) x := h
    rw [h'.fderiv]
    simp [mul_comm]
  funext k
  simp only [stratCorrection, Pi.zero_apply, hf]
  simp [Fin.sum_univ_four]
  fin_cases k <;> simp [diffusion_apply, noiseMatrix]

end Params3

end powerlib.GFM.Noise
