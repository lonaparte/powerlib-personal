import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SPH
import theorem.PowerSystem.Synchronous.PH
import theorem.GridTiedConverter.GFL.Noise.DampingClass

/-! # Noise channels of the reduced two-state GFM: exact noise rows, Itô and Stratonovich terms

Domain module: the grid-forming converter as a voltage source behind a lossy line, reduced to the
two-state synchronization model, with four disturbance channels (power set-point, grid frequency,
d- and q-axis grid voltage). Its drift is the classical machine `Synchronous.classicalSM` in the
shifted angle and every channel enters affinely and exactly. All statements are algebraic or
calculus identities at one state (gradient, Hessian, diffusion matrix); no SDE solution, law,
expectation or escape statement is made (Rules §3).

Model boundary.
* Source `E∠δ` (constant amplitude `E > 0`, angle `δ` relative to the grid) behind a quasi-static
  (phasor) series impedance `R + jX` (`R ≥ 0`, `X > 0`, `|Z|² = R² + X²`) into the grid voltage
  `v_g = (V + ξ_d) + j ξ_q` (`V > 0`), per unit, in the dq frame rotating at the nominal
  frequency. Active power at the source `P = Re(E e^{jδ} · conj((E e^{jδ} − v_g)/(R + jX)))`,
  export-positive (GFM convention, as in `theorem/GridTiedConverter/GFM/VSMLPF.lean`), from
  `S̄ = V̄ Ī*` with the current `Ī` positive out of the converter; single-phase equivalent (with
  amplitude-invariant dq quantities the three-phase power is `3/2` times it).
* State `x = (δ, p)`, `p = M Δω` (momentum coordinates of `Synchronous.classicalSM`), VSM
  synchronization `δ̇ = Δω − ω_g`, `ṗ = P_ref + ΔP − P − D (Δω − κ ω_g)`, `M > 0`, `D ≥ 0`.
  Disturbances `w = (ΔP, ω_g, ξ_d, ξ_q)` (set-point, grid frequency, grid voltage d and q); `κ`
  selects the damping reference: `κ = 0` nominal frequency, `κ = 1` the grid frequency.
* The disturbances are white-noise channels with intensities `σ = (σ_P, ε, σ_d, σ_q)`
  (diffusion `h = B(δ) diag σ`); the Itô correction is the algebraic expression
  `½ tr(h hᵀ ∇²H)` (`Stochastic.SPH.itoCorrection`), the Stratonovich drift correction the
  expression `Stochastic.SPH.stratCorrection` with the derivatives of `h` computed by `fderiv`.
* Excluded: line and filter dynamics, inner voltage/current loops, Q–V droop (constant `E`), power
  filter (the three-state model, `theorem/GridTiedConverter/GFM/Noise/NoiseLyapunov.lean`), PLL,
  delay, PWM, current limiting; continuous time.

Source: GFM counterpart study, note t2-noise items 1–4 (SPHS embedding, Itô correction, Stratonovich
correction, fluctuation–dissipation per channel; derived and checked symbolically, scratch notes
outside the repository); work-sync `theory/T-sph.md` §1.2–§1.5 (generator, Itô/Stratonovich);
Kundur, *Power System Stability and Control* (1994), Ch. 6 (power through a series impedance);
the GFL counterpart `theorem/GridTiedConverter/GFL/Noise/Embedding.lean`.

Results.
* Phasor power: `sourcePower_eq` (rectangular form), `sourcePower_noise`:
  `P(δ, V + ξ_d + j ξ_q) = c₀ + A sin(δ − α) + k (sin(δ − α) ξ_d − cos(δ − α) ξ_q)` exactly, with
  `c₀ = E²R/|Z|²`, `A = E V/|Z|`, `k = E/|Z|`, `α = arg(X + jR)` (`sin_alpha`, `cos_alpha`):
  the power is affine in the complex grid voltage, so the voltage noise rows are exact.
* `noisyField_eq`: the disturbed field is the classical machine `Synchronous.classicalSM` with
  `b = A`, `P_m = P_ref − c₀` (`Params.toSM`), evaluated at the shifted state `(δ − α, p)`
  (`Params.shift`), plus `B(δ) w` with the noise matrix
  `B(δ) = !![0, −1, 0, 0; 1, κ D, −k sin(δ − α), k cos(δ − α)]`. Its pH data are the machine's:
  `J = !![0, 1; −1, 0]`, `R = diag(0, D)` (`GFL.Noise.swingPH_R`), energy balance
  `Synchronous.classicalSM_dampingPower`.
* `hasFDerivAt_dH_shift`: the Hessian of `H` at `x` is `diag(A cos(δ − α), 1/M)`
  (`Synchronous.classicalSM_hasFDerivAt_dH` through the shift).
* `diffusion_mul_transpose`, `ito_eq`: `Δ_Itô = σ_P²/(2M) + (ε²/2)(A cos(δ − α) + κ² D²/M) +
  (k²/(2M))(σ_d² sin²(δ − α) + σ_q² cos²(δ − α))`.
* Sign: `ito_nonneg_of_freq_zero` (without the frequency channel `Δ_Itô ≥ 0` at every state:
  no damping-ratio threshold, unlike `PLL.StochasticPH.pllIto_saddle_neg_iff`); `ito_neg_iff`
  (nominal damping: `Δ_Itô < 0 ⇔ σ_P² + k²(σ_d² sin² + σ_q² cos²) < ε² M A (−cos(δ − α))`, the
  threshold on `ε²` at the saddle `cos(δ − α) < 0`); grid-referenced damping, frequency channel:
  `ito_gridRef_saddle` (`Δ_Itô = (ε² κ_b/2)(4ζ_b² − 1)`, `κ_b = −A cos(δ − α)`,
  `ζ_b = GFL.Noise.zetaA M D κ_b`), `ito_gridRef_neg_iff` (`Δ_Itô < 0 ⇔ ζ_b < ½`, the GFL law
  `ζ > ½` reversed), `ito_gridRef_pos_of_cos_pos` (positive on the node side).
* `strat_eq_zero`: the Stratonovich drift correction of the merged noise (all channels, both
  damping references, state-dependent voltage rows) vanishes: the Itô and Stratonovich drifts
  coincide.
* `fdt_iff`: `h hᵀ = 2 T R` at every state iff `ε = 0`, `σ_d² = σ_q²` and
  `σ_P² + k² σ_q² = 2 D T`: the set-point channel (`GFL.Noise.classA_torque_fdt`) and the
  isotropic voltage channel (`T = k² σ_v²/(2D)`) are exactly fluctuation–dissipation, the
  frequency channel never (`GFL.Noise.classA_frequency_not_fdt`), anisotropic voltage noise never.
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real Matrix
open powerlib.Dynamics (State)
open powerlib.Stochastic.SPH

/-- Parameters of the reduced two-state GFM on a lossy line, with their physical ranges. -/
structure Params where
  M : ℝ
  D : ℝ
  E : ℝ
  V : ℝ
  R : ℝ
  X : ℝ
  Pref : ℝ
  M_pos : 0 < M
  D_nonneg : 0 ≤ D
  E_pos : 0 < E
  V_pos : 0 < V
  R_nonneg : 0 ≤ R
  X_pos : 0 < X

namespace Params

variable (p : Params)

/-- `|Z|² = R² + X²`. -/
def absSq : ℝ := p.R ^ 2 + p.X ^ 2

/-- `|Z| = √(R² + X²)`. -/
def absZ : ℝ := √p.absSq

/-- Loss angle `α = arg(X + jR)` (`= atan2(R, X)`). -/
def α : ℝ := Complex.arg (p.X + p.R * Complex.I)

/-- Load offset `c₀ = E² R/|Z|²`. -/
def c0 : ℝ := p.E ^ 2 * p.R / p.absSq

/-- Power amplitude `A = E V/|Z|`. -/
def A : ℝ := p.E * p.V / p.absZ

/-- Voltage-noise gain `k = E/|Z|` (`A = k V`). -/
def k : ℝ := p.E / p.absZ

@[tmio M, powerlib_domain] theorem absSq_pos : 0 < p.absSq := by
  have := p.X_pos; unfold absSq; positivity

@[tmio M, powerlib_domain] theorem absZ_pos : 0 < p.absZ := Real.sqrt_pos.mpr p.absSq_pos

@[tmio M, powerlib_domain] theorem absZ_sq : p.absZ ^ 2 = p.absSq :=
  Real.sq_sqrt p.absSq_pos.le

@[tmio M, powerlib_domain] theorem A_pos : 0 < p.A := by
  have := p.E_pos; have := p.V_pos; have := p.absZ_pos; unfold A; positivity

@[tmio M, powerlib_domain] theorem k_pos : 0 < p.k := by
  have := p.E_pos; have := p.absZ_pos; unfold k; positivity

@[tmio M, powerlib_domain] private lemma norm_XR : ‖(p.X : ℂ) + p.R * Complex.I‖ = p.absZ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp [absZ, absSq]
  ring_nf

@[tmio M, powerlib_domain] theorem sin_alpha : Real.sin p.α = p.R / p.absZ := by
  rw [α, Complex.sin_arg, norm_XR]; simp

@[tmio M, powerlib_domain] theorem cos_alpha : Real.cos p.α = p.X / p.absZ := by
  have h : (p.X : ℂ) + p.R * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; exact p.X_pos.ne' this
  rw [α, Complex.cos_arg h, norm_XR]; simp

/-! ## Phasor power at the source -/

/-- Active power at the source, `P = Re(E e^{jδ} · conj((E e^{jδ} − v_g)/(R + jX)))`
(`S̄ = V̄ Ī*`, export-positive), for a complex grid voltage `v_g`. -/
def sourcePower (δ : ℝ) (vg : ℂ) : ℝ :=
  ((p.E : ℂ) * Complex.exp (δ * Complex.I) *
    (starRingEnd ℂ) (((p.E : ℂ) * Complex.exp (δ * Complex.I) - vg) /
      ((p.R : ℂ) + p.X * Complex.I))).re

/-- Rectangular form: `P = [R(E² − E(v_d cos δ + v_q sin δ)) + X E (v_d sin δ − v_q cos δ)]/|Z|²`
with `v_g = v_d + j v_q`. -/
@[tmio M, powerlib_domain] theorem sourcePower_eq (δ : ℝ) (vg : ℂ) :
    p.sourcePower δ vg = (p.R * (p.E ^ 2 - p.E * (vg.re * Real.cos δ + vg.im * Real.sin δ)) +
      p.X * p.E * (vg.re * Real.sin δ - vg.im * Real.cos δ)) / p.absSq := by
  have hZ : p.R * p.R + p.X * p.X ≠ 0 := by
    have := p.absSq_pos; unfold absSq at this; nlinarith
  have hZ' : p.R ^ 2 + p.X ^ 2 ≠ 0 := p.absSq_pos.ne'
  have hsc := Real.sin_sq_add_cos_sq δ
  unfold sourcePower absSq
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, Complex.normSq_apply, mul_zero, zero_mul,
    sub_zero, add_zero, zero_add, mul_one]
  field_simp
  linear_combination (p.E ^ 2 * p.R) * hsc

/-- **Exact noise rows**: with the grid voltage `V + ξ_d + j ξ_q`,
`P = c₀ + A sin(δ − α) + k (sin(δ − α) ξ_d − cos(δ − α) ξ_q)` (affine in the voltage noise). -/
@[tmio M, powerlib_domain] theorem sourcePower_noise (δ ξd ξq : ℝ) :
    p.sourcePower δ (((p.V + ξd : ℝ) : ℂ) + (ξq : ℂ) * Complex.I) =
      p.c0 + p.A * Real.sin (δ - p.α) +
        p.k * (Real.sin (δ - p.α) * ξd - Real.cos (δ - p.α) * ξq) := by
  have hz := p.absZ_pos.ne'
  have hz2 := p.absZ_sq
  rw [sourcePower_eq, Real.sin_sub, Real.cos_sub, sin_alpha, cos_alpha]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    zero_add, add_zero]
  unfold c0 A k
  rw [← hz2]
  field_simp
  ring

/-! ## The disturbed two-state model -/

/-- The classical machine of the shifted angle: `b = A`, `P_m = P_ref − c₀`. -/
def toSM : Synchronous.ClassicalSMParams :=
  ⟨p.M, p.D, p.A, p.Pref - p.c0, p.M_pos, p.D_nonneg, p.A_pos⟩

/-- Shifted state `(δ − α, p)`. -/
def shift (x : State 2) : State 2 := x - WithLp.toLp 2 ![p.α, 0]

@[tmio M, simp, powerlib_domain] theorem shift_apply_zero (x : State 2) :
    p.shift x 0 = x 0 - p.α := by simp [shift]

@[tmio M, simp, powerlib_domain] theorem shift_apply_one (x : State 2) :
    p.shift x 1 = x 1 := by simp [shift]

/-- Noise matrix at the angle `δ` (columns: set-point `ΔP`, grid frequency `ω_g`, grid voltage
`ξ_d`, `ξ_q`; `κ` the damping reference). -/
def noiseMatrix (κ δ : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  !![0, -1, 0, 0; 1, κ * p.D, -(p.k * Real.sin (δ - p.α)), p.k * Real.cos (δ - p.α)]

/-- Disturbed field at the state `x = (δ, p)` and the disturbance values `w = (ΔP, ω_g, ξ_d, ξ_q)`:
`δ̇ = p/M − ω_g`, `ṗ = P_ref + ΔP − P(δ, V + ξ_d + j ξ_q) − D (p/M − κ ω_g)`. -/
def noisyField (κ : ℝ) (x : State 2) (w : Fin 4 → ℝ) : Fin 2 → ℝ :=
  ![x 1 / p.M - w 1, p.Pref + w 0 -
    p.sourcePower (x 0) (((p.V + w 2 : ℝ) : ℂ) + (w 3 : ℂ) * Complex.I) -
      p.D * (x 1 / p.M - κ * w 1)]

/-- **Affine reading**: the disturbed field is the classical-machine field at the shifted state
plus `B(δ) w`, exactly. -/
@[tmio M, powerlib_domain] theorem noisyField_eq (κ : ℝ) (x : State 2) (w : Fin 4 → ℝ) :
    p.noisyField κ x w = WithLp.ofLp ((Synchronous.classicalSM p.toSM).field (p.shift x) 0) +
      p.noiseMatrix κ (x 0) *ᵥ w := by
  have hP := p.sourcePower_noise (x 0) (w 2) (w 3)
  simp only [Complex.ofReal_add] at hP
  rw [Synchronous.classicalSM_field]
  ext i; fin_cases i
  · simp [noisyField, noiseMatrix, toSM, dotProduct, Fin.sum_univ_four]; ring
  · simp [noisyField, noiseMatrix, toSM, dotProduct, Fin.sum_univ_four, hP]
    ring

/-- Hessian `diag(A cos(δ − α), 1/M)` of `H` at `x`. -/
def hessian (x : State 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.toSM.b * Real.cos (p.shift x 0), 0; 0, 1 / p.toSM.M]

/-- The Hessian of the machine Hamiltonian along the shift
(`Synchronous.classicalSM_hasFDerivAt_dH`). -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_dH_shift (x : State 2) :
    HasFDerivAt (fun y => (Synchronous.classicalSM p.toSM).dH (p.shift y))
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (p.hessian x)) x := by
  have h := (Synchronous.classicalSM_hasFDerivAt_dH p.toSM (p.shift x)).comp x
    ((hasFDerivAt_id x).sub_const (WithLp.toLp 2 ![p.α, 0]))
  rw [ContinuousLinearMap.comp_id] at h
  exact h

/-- Diffusion `h = B(δ) diag σ`, `σ = (σ_P, ε, σ_d, σ_q)`. -/
def diffusion (κ : ℝ) (σ : Fin 4 → ℝ) (δ : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  p.noiseMatrix κ δ * diagonal σ

@[tmio M, powerlib_domain] theorem diffusion_apply (κ : ℝ) (σ : Fin 4 → ℝ) (δ : ℝ) (i : Fin 2)
    (j : Fin 4) : p.diffusion κ σ δ i j = p.noiseMatrix κ δ i j * σ j := mul_diagonal _ _ _ _

/-- `h hᵀ = !![ε², −κDε²; −κDε², σ_P² + κ²D²ε² + k²(σ_d² sin² + σ_q² cos²)]`. -/
@[tmio M, powerlib_domain] theorem diffusion_mul_transpose (κ : ℝ) (σ : Fin 4 → ℝ) (δ : ℝ) :
    p.diffusion κ σ δ * (p.diffusion κ σ δ)ᵀ =
      !![σ 1 ^ 2, -(κ * p.D * σ 1 ^ 2); -(κ * p.D * σ 1 ^ 2),
        σ 0 ^ 2 + κ ^ 2 * p.D ^ 2 * σ 1 ^ 2 + p.k ^ 2 * (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 +
          σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diffusion_apply, noiseMatrix, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- **Itô correction of the merged noise**: `Δ_Itô = σ_P²/(2M) + (ε²/2)(A cos(δ − α) + κ²D²/M) +
(k²/(2M))(σ_d² sin²(δ − α) + σ_q² cos²(δ − α))`. -/
@[tmio M, powerlib_domain] theorem ito_eq (κ : ℝ) (σ : Fin 4 → ℝ) (x : State 2) :
    itoCorrection (p.diffusion κ σ (x 0)) (p.hessian x) =
      σ 0 ^ 2 / (2 * p.M) + σ 1 ^ 2 / 2 * (p.A * Real.cos (x 0 - p.α) + κ ^ 2 * p.D ^ 2 / p.M) +
        p.k ^ 2 / (2 * p.M) * (σ 2 ^ 2 * Real.sin (x 0 - p.α) ^ 2 +
          σ 3 ^ 2 * Real.cos (x 0 - p.α) ^ 2) := by
  have hM := p.M_pos.ne'
  unfold itoCorrection
  rw [diffusion_mul_transpose]
  simp [hessian, toSM, Matrix.trace_fin_two]
  field_simp
  ring

/-- Without the frequency channel (`ε = 0`) the correction is nonnegative at every state: the
set-point and voltage channels have no threshold. -/
@[tmio M, powerlib_domain] theorem ito_nonneg_of_freq_zero (κ : ℝ) {σ : Fin 4 → ℝ}
    (hε : σ 1 = 0) (x : State 2) : 0 ≤ itoCorrection (p.diffusion κ σ (x 0)) (p.hessian x) := by
  have := p.M_pos
  rw [ito_eq, hε]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
    add_zero]
  positivity

/-- **Nominal damping, threshold on the frequency noise**: `Δ_Itô < 0` iff
`σ_P² + k²(σ_d² sin² + σ_q² cos²) < ε² M A (−cos(δ − α))`; at the saddle (`cos(δ − α) < 0`)
this is a threshold on `ε²`, at the node (`cos > 0`) it never holds. -/
@[tmio M, powerlib_domain] theorem ito_neg_iff (σ : Fin 4 → ℝ) (x : State 2) :
    itoCorrection (p.diffusion 0 σ (x 0)) (p.hessian x) < 0 ↔
      σ 0 ^ 2 + p.k ^ 2 * (σ 2 ^ 2 * Real.sin (x 0 - p.α) ^ 2 +
          σ 3 ^ 2 * Real.cos (x 0 - p.α) ^ 2) <
        σ 1 ^ 2 * p.M * p.A * -Real.cos (x 0 - p.α) := by
  have hM := p.M_pos
  rw [ito_eq]
  have e : σ 0 ^ 2 / (2 * p.M) + σ 1 ^ 2 / 2 * (p.A * Real.cos (x 0 - p.α) +
      (0 : ℝ) ^ 2 * p.D ^ 2 / p.M) + p.k ^ 2 / (2 * p.M) * (σ 2 ^ 2 * Real.sin (x 0 - p.α) ^ 2 +
        σ 3 ^ 2 * Real.cos (x 0 - p.α) ^ 2) =
      (σ 0 ^ 2 + p.k ^ 2 * (σ 2 ^ 2 * Real.sin (x 0 - p.α) ^ 2 +
        σ 3 ^ 2 * Real.cos (x 0 - p.α) ^ 2) - σ 1 ^ 2 * p.M * p.A * -Real.cos (x 0 - p.α)) /
        (2 * p.M) := by
    field_simp; ring
  rw [e, div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h; right; exact ⟨by linarith, by linarith⟩

/-- Grid-frequency channel alone (`σ_P = σ_d = σ_q = 0`). -/
def freqOnly (ε : ℝ) : Fin 4 → ℝ := ![0, ε, 0, 0]

/-- **Grid-referenced damping at the saddle**: with `κ_b = −A cos(δ − α) > 0` and
`ζ_b = GFL.Noise.zetaA M D κ_b = D/(2√(M κ_b))`, `Δ_Itô = (ε² κ_b/2)(4ζ_b² − 1)`. -/
@[tmio M, powerlib_domain] theorem ito_gridRef_saddle (ε : ℝ) {x : State 2}
    (hc : Real.cos (x 0 - p.α) < 0) :
    itoCorrection (p.diffusion 1 (freqOnly ε) (x 0)) (p.hessian x) =
      ε ^ 2 * (-(p.A * Real.cos (x 0 - p.α))) / 2 *
        (4 * GFL.Noise.zetaA p.M p.D (-(p.A * Real.cos (x 0 - p.α))) ^ 2 - 1) := by
  have hM := p.M_pos
  have hκ : 0 < -(p.A * Real.cos (x 0 - p.α)) := by nlinarith [p.A_pos]
  set κb := -(p.A * Real.cos (x 0 - p.α)) with hκb
  have hz : 4 * GFL.Noise.zetaA p.M p.D κb ^ 2 = p.D ^ 2 / (p.M * κb) := by
    rw [GFL.Noise.zetaA, div_pow, mul_pow, Real.sq_sqrt (mul_pos hM hκ).le]
    field_simp
    ring
  rw [ito_eq, hz]
  simp only [freqOnly, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have e : p.A * Real.cos (x 0 - p.α) = -κb := by rw [hκb]; ring
  rw [e]
  field_simp
  ring

/-- **The ζ_b < ½ law (grid-referenced damping)**: at the saddle, for `ε ≠ 0`,
`Δ_Itô < 0 ⇔ ζ_b < ½` — the reverse of the GFL law `Δ_Itô < 0 ⇔ ζ > ½`
(`PLL.StochasticPH.pllIto_saddle_neg_iff`). -/
@[tmio M, powerlib_domain] theorem ito_gridRef_neg_iff {ε : ℝ} (hε : ε ≠ 0) {x : State 2}
    (hc : Real.cos (x 0 - p.α) < 0) :
    itoCorrection (p.diffusion 1 (freqOnly ε) (x 0)) (p.hessian x) < 0 ↔
      GFL.Noise.zetaA p.M p.D (-(p.A * Real.cos (x 0 - p.α))) < 1 / 2 := by
  have hκ : 0 < -(p.A * Real.cos (x 0 - p.α)) := by nlinarith [p.A_pos]
  have hz : 0 ≤ GFL.Noise.zetaA p.M p.D (-(p.A * Real.cos (x 0 - p.α))) := by
    unfold GFL.Noise.zetaA; have := p.D_nonneg; positivity
  have hpos : 0 < ε ^ 2 * (-(p.A * Real.cos (x 0 - p.α))) / 2 := by positivity
  rw [ito_gridRef_saddle p ε hc]
  constructor
  · intro h
    have : 4 * GFL.Noise.zetaA p.M p.D (-(p.A * Real.cos (x 0 - p.α))) ^ 2 - 1 < 0 := by
      by_contra hc'; push Not at hc'
      have := mul_nonneg hpos.le hc'
      linarith
    nlinarith
  · intro h
    exact mul_neg_of_pos_of_neg hpos (by nlinarith)

/-- On the node side (`cos(δ − α) > 0`) the grid-referenced frequency correction is positive. -/
@[tmio M, powerlib_domain] theorem ito_gridRef_pos_of_cos_pos {ε : ℝ} (hε : ε ≠ 0)
    {x : State 2} (hc : 0 < Real.cos (x 0 - p.α)) :
    0 < itoCorrection (p.diffusion 1 (freqOnly ε) (x 0)) (p.hessian x) := by
  have := p.M_pos; have := p.A_pos
  rw [ito_eq]
  simp only [freqOnly, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have : 0 < p.A * Real.cos (x 0 - p.α) := mul_pos (by assumption) hc
  positivity

/-! ## Stratonovich correction -/

/-- **Stratonovich = Itô for every GFM channel**: the drift correction
`c_k = ½ Σ_{j,l} h_{lj} ∂_l h_{kj}` of the merged noise vanishes (`∂h` by `fderiv`): the only
state-dependent entries are the voltage entries of the momentum row, which depend on the angle
only, while the angle row of those columns is zero. -/
@[tmio M, powerlib_domain] theorem strat_eq_zero (κ : ℝ) (σ : Fin 4 → ℝ) (x : State 2) :
    stratCorrection (p.diffusion κ σ (x 0))
      (fun k j l => fderiv ℝ (fun y : State 2 => p.diffusion κ σ (y 0) k j) x
        (EuclideanSpace.single l 1)) = 0 := by
  have hd : ∀ k j, Differentiable ℝ (fun t => p.diffusion κ σ t k j) := by
    intro k j
    fin_cases k <;> fin_cases j <;>
      simp [diffusion_apply, noiseMatrix] <;> fun_prop
  have hf : ∀ k j (v : State 2), fderiv ℝ (fun y : State 2 => p.diffusion κ σ (y 0) k j) x v =
      deriv (fun t => p.diffusion κ σ t k j) (x 0) * v 0 := by
    intro k j v
    have h := ((hd k j (x 0)).hasDerivAt).comp_hasFDerivAt x
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x))
    have h' : HasFDerivAt (fun y : State 2 => p.diffusion κ σ (y 0) k j)
        (deriv (fun t => p.diffusion κ σ t k j) (x 0) •
          (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ)) x := h
    rw [h'.fderiv]
    simp [mul_comm]
  funext k
  simp only [stratCorrection, Pi.zero_apply, hf]
  simp [Fin.sum_univ_four]
  fin_cases k <;> simp [diffusion_apply, noiseMatrix]

/-! ## Fluctuation–dissipation -/

/-- **Fluctuation–dissipation per channel**: `h hᵀ = 2 T R` (`R = diag(0, D)` the machine's
dissipation, `GFL.Noise.swingPH_R`) at every state iff `ε = 0`, `σ_d² = σ_q²` and
`σ_P² + k² σ_q² = 2 D T`. -/
@[tmio M, powerlib_domain] theorem fdt_iff (κ : ℝ) (σ : Fin 4 → ℝ) (T : ℝ) :
    (∀ x : State 2, p.diffusion κ σ (x 0) * (p.diffusion κ σ (x 0))ᵀ =
        (2 * T) • (Synchronous.classicalSM p.toSM).R (p.shift x)) ↔
      σ 1 = 0 ∧ σ 2 ^ 2 = σ 3 ^ 2 ∧ σ 0 ^ 2 + p.k ^ 2 * σ 3 ^ 2 = 2 * p.D * T := by
  have hk := p.k_pos.ne'
  simp only [GFL.Noise.swingPH_R, diffusion_mul_transpose]
  constructor
  · intro h
    have h0 := h (WithLp.toLp 2 ![p.α, 0])
    have h1 := h (WithLp.toLp 2 ![p.α + π / 2, 0])
    have e00 := congrFun (congrFun h0 0) 0
    have e11 := congrFun (congrFun h0 1) 1
    have f11 := congrFun (congrFun h1 1) 1
    simp [GFL.Noise.RA, toSM] at e00 e11 f11
    refine ⟨e00, ?_, ?_⟩
    · rw [e00] at e11 f11
      have : p.k ^ 2 * (σ 2 ^ 2 - σ 3 ^ 2) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hk)
      linarith
    · rw [e00] at e11; linarith
  · rintro ⟨h1, h2, h3⟩ x
    have hsc := Real.sin_sq_add_cos_sq (x 0 - p.α)
    ext i j; fin_cases i <;> fin_cases j <;> simp [GFL.Noise.RA, toSM, h1]
    rw [h2]
    linear_combination h3 + p.k ^ 2 * σ 3 ^ 2 * hsc

end Params

end powerlib.GFM.Noise
