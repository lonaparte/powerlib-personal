import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SPH
import theorem.Transform.Park

/-! # Itô correction of the SRF-PLL SPHS and its GFL form-B / grid-disturbance specializations

Model boundary.
State `(θ_e, η)` of the SRF-PLL (phase error, PI integrator), Hamiltonian
`𝓗 = 𝒱(θ_e) + ½ K_i η²`.  The voltage disturbance `ξ_v = (ξ_d, ξ_q)` enters through the
1×2 row `σ_v(θ_e)`: `dθ_e ∋ K_p σ_v dW_v`, `dη ∋ σ_v dW_v`.  The form-B specialization is the
quasi-steady line + LC algebra of T-gfl-dynamics §1.6 (inner current loop and outer loops frozen,
`ω_g` constant); the grid-voltage perturbation replaces `V_g` by `V_g + ξ_d` and `0` by `ξ_q`.
Everything here is **foundation**: the Itô correction is the algebraic expression
`½ tr(h hᵀ ∇²𝓗)` at a state (see `SPH.itoCorrection`); no SDE solution, Itô formula,
escape rate or stability claim is made (Rules §3).

Source: work-sync `theory/T-pll-sph.md` §1.1–§1.2 (noise coupling `h_noise = (K_p σ_v, σ_v)ᵀ`,
Hessian `diag(𝒱'', K_i)`, `Δ_Itô = ½ σ_v²[K_p² 𝒱'' + K_i]` (1.6), saddle value and the
`ζ = 1/2` threshold (1.7), frequency-channel supplement `½ σ_ω² 𝒱''`), `theory/T-pll-ph.md`
(potential `𝒱(θ) = V_g(1 − cos θ)`), `theory/T-gfl-sph.md` §1.1–§1.3 (form-B `σ_v(θ_e)`),
`theory/T-gfl-dynamics.md` §1.6–§1.7 (form-B quasi-steady line + LC algebraic equations),
`theory/T-grid-disturbance-stochastic.md` §1.2.a (Park projection `σ_v^bare`).

Results.
* `pllIto`: `Δ_Itô = ½ σ_v σ_vᵀ (K_p² 𝒱'' + K_i)` for the SRF-PLL noise coupling;
  `pllIto_freq` adds the frequency channel `½ σ_ω² 𝒱''`.
* `pllIto_saddle`, `pllIto_saddle_neg_iff`, `pllIto_saddle_pos_iff`, `pllIto_bottom_pos`: at the
  saddle `θ_e = π` the correction is negative iff `ζ > 1/2`; at the well bottom it is positive.
* `pllIto_bare`, `park_q_eq_sigmaBare`, `park_isotropic_cov`, `park_q_variance`: the bare
  grid-disturbance coupling `σ_v^bare = (−sin θ, cos θ)` (unit norm) of the Park projection.
* `lineResidual_eq_zero_iff`, `lineSolution_split`, `pllInput_noise_split`, `gflSigma_sq`,
  `gflIto`: the form-B quasi-steady line + LC solution, its noise row `σ_v(θ_e)` and the form-B
  Itô correction.

Correction (T-gfl-sph §1.3 / T-pll-sph (1.6)).  `σ_v` is a **row vector**, so "σ_v²" must be
read as `σ_v σ_vᵀ = σ_v ⬝ σ_v` (`pllNoise_mul_transpose`).  With that reading the closed forms of
the note are reproduced exactly (`pllIto`, `gflSigma_sq`).
-/

noncomputable section
namespace powerlib.PLL.StochasticPH

open Matrix Real
open powerlib.Stochastic.SPH

/-! ## Potential and Hessian -/

/-- SRF-PLL phase potential `𝒱(θ) = V_g (1 − cos θ)` (T-pll-ph §1.0). -/
def pllV (Vg θ : ℝ) : ℝ := Vg * (1 - cos θ)

/-- `𝒱' = V_g sin θ = −h(θ)` with the phase detector `h(θ) = −V_g sin θ`. -/
@[tmio M, powerlib_foundation] theorem pllV_hasDerivAt (Vg θ : ℝ) :
    HasDerivAt (pllV Vg) (Vg * sin θ) θ := by
  have := ((hasDerivAt_cos θ).const_sub 1).const_mul Vg
  unfold pllV
  exact this.congr_deriv (by ring)

/-- `𝒱'' = V_g cos θ`. -/
@[powerlib_foundation] theorem pllV'_hasDerivAt (Vg θ : ℝ) :
    HasDerivAt (fun θ => Vg * sin θ) (Vg * cos θ) θ :=
  (hasDerivAt_sin θ).const_mul Vg

/-- The `η`-part `½ K_i η²` has first derivative `K_i η` and second derivative `K_i`. -/
@[powerlib_foundation] theorem pllEta_hasDerivAt (Ki η : ℝ) :
    HasDerivAt (fun η => (1 / 2 : ℝ) * Ki * η ^ 2) (Ki * η) η := by
  have := ((hasDerivAt_pow 2 η).const_mul ((1 / 2 : ℝ) * Ki))
  convert this using 1; ring

/-- Hessian `∇²𝓗 = diag(𝒱''(θ), K_i)` of `𝓗 = 𝒱(θ) + ½ K_i η²` (separable, no cross term). -/
def pllHess (V2 Ki : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![V2, 0; 0, Ki]

/-! ## Noise coupling and the Itô correction (T-pll-sph (1.6)) -/

/-- Voltage-noise coupling `h_noise = (K_p σ_v, σ_v)ᵀ` (rows: `θ_e`, `η`; columns: `d`, `q`). -/
def pllNoise (Kp : ℝ) (σv : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Kp * σv 0, Kp * σv 1; σv 0, σv 1]

@[powerlib_foundation] theorem pllNoise_mul_transpose (Kp : ℝ) (σv : Fin 2 → ℝ) :
    pllNoise Kp σv * (pllNoise Kp σv)ᵀ = (σv ⬝ᵥ σv) • !![Kp ^ 2, Kp; Kp, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pllNoise, mul_apply, Fin.sum_univ_two, dotProduct] <;> ring

/-- `Δ_Itô^PLL = ½ (σ_v σ_vᵀ) (K_p² 𝒱'' + K_i)`. -/
@[powerlib_foundation] theorem pllIto (Kp Ki V2 : ℝ) (σv : Fin 2 → ℝ) :
    itoCorrection (pllNoise Kp σv) (pllHess V2 Ki)
      = (1 / 2 : ℝ) * (σv ⬝ᵥ σv) * (Kp ^ 2 * V2 + Ki) := by
  unfold itoCorrection
  rw [pllNoise_mul_transpose, smul_mul_assoc, trace_smul]
  simp [pllHess, trace_fin_two]
  ring

/-- PLL damping ratio `ζ = K_p √V_g / (2 √K_i)` (T-pll-dynamics §1.3). -/
def zeta (Kp Vg Ki : ℝ) : ℝ := Kp * √Vg / (2 * √Ki)

@[powerlib_foundation] theorem four_zeta_sq {Kp Vg Ki : ℝ} (hVg : 0 ≤ Vg) (hKi : 0 < Ki) :
    4 * zeta Kp Vg Ki ^ 2 = Kp ^ 2 * Vg / Ki := by
  unfold zeta
  rw [div_pow, mul_pow, mul_pow, sq_sqrt hVg, sq_sqrt hKi.le]
  field_simp
  ring

@[powerlib_foundation] theorem pllV_second_zero (Vg : ℝ) : Vg * cos 0 = Vg := by simp

@[powerlib_foundation] theorem pllV_second_pi (Vg : ℝ) : Vg * cos π = -Vg := by simp

/-- Saddle value: `Δ_Itô^PLL(π) = ½ σ_v σ_vᵀ K_i (1 − 4ζ²)`. -/
@[powerlib_foundation] theorem pllIto_saddle {Kp Vg Ki : ℝ} (hVg : 0 ≤ Vg) (hKi : 0 < Ki)
    (σv : Fin 2 → ℝ) :
    itoCorrection (pllNoise Kp σv) (pllHess (Vg * cos π) Ki)
      = (1 / 2 : ℝ) * (σv ⬝ᵥ σv) * Ki * (1 - 4 * zeta Kp Vg Ki ^ 2) := by
  rw [pllIto, pllV_second_pi, four_zeta_sq hVg hKi]
  field_simp
  ring

/-- **ζ = 1/2 threshold**: for nonzero voltage noise, `Δ_Itô^PLL(π) < 0 ⇔ ζ > 1/2`. -/
@[powerlib_foundation] theorem pllIto_saddle_neg_iff {Kp Vg Ki : ℝ} (hKp : 0 ≤ Kp)
    (hVg : 0 ≤ Vg) (hKi : 0 < Ki) {σv : Fin 2 → ℝ} (hσ : σv ≠ 0) :
    itoCorrection (pllNoise Kp σv) (pllHess (Vg * cos π) Ki) < 0 ↔ 1 / 2 < zeta Kp Vg Ki := by
  have hs : 0 < σv ⬝ᵥ σv := by
    rcases (dotProduct_self_star_pos_iff (v := σv)).mpr hσ with h
    simpa using h
  have hz : 0 ≤ zeta Kp Vg Ki := by unfold zeta; positivity
  rw [pllIto_saddle hVg hKi]
  constructor
  · intro h
    have : 1 - 4 * zeta Kp Vg Ki ^ 2 < 0 := by
      by_contra hc; push Not at hc
      have : 0 ≤ (1 / 2 : ℝ) * (σv ⬝ᵥ σv) * Ki * (1 - 4 * zeta Kp Vg Ki ^ 2) := by positivity
      linarith
    nlinarith
  · intro h
    have : 1 - 4 * zeta Kp Vg Ki ^ 2 < 0 := by nlinarith
    have hpos : 0 < (1 / 2 : ℝ) * (σv ⬝ᵥ σv) * Ki := by positivity
    exact mul_neg_of_pos_of_neg hpos this

/-- Conversely `Δ_Itô^PLL(π) > 0 ⇔ ζ < 1/2` (PI-channel diffusion dominates). -/
@[powerlib_foundation] theorem pllIto_saddle_pos_iff {Kp Vg Ki : ℝ} (hKp : 0 ≤ Kp)
    (hVg : 0 ≤ Vg) (hKi : 0 < Ki) {σv : Fin 2 → ℝ} (hσ : σv ≠ 0) :
    0 < itoCorrection (pllNoise Kp σv) (pllHess (Vg * cos π) Ki) ↔ zeta Kp Vg Ki < 1 / 2 := by
  have hs : 0 < σv ⬝ᵥ σv := by
    simpa using (dotProduct_self_star_pos_iff (v := σv)).mpr hσ
  have hz : 0 ≤ zeta Kp Vg Ki := by unfold zeta; positivity
  rw [pllIto_saddle hVg hKi]
  have hpos : 0 < (1 / 2 : ℝ) * (σv ⬝ᵥ σv) * Ki := by positivity
  constructor
  · intro h
    have : 0 < 1 - 4 * zeta Kp Vg Ki ^ 2 := (pos_iff_pos_of_mul_pos h).mp hpos
    nlinarith
  · intro h
    exact mul_pos hpos (by nlinarith)

/-- Well bottom `θ_e = 0`: `Δ_Itô^PLL > 0` (noise rectification). -/
@[powerlib_foundation] theorem pllIto_bottom_pos {Kp Vg Ki : ℝ} (hVg : 0 ≤ Vg) (hKi : 0 < Ki)
    {σv : Fin 2 → ℝ} (hσ : σv ≠ 0) :
    0 < itoCorrection (pllNoise Kp σv) (pllHess (Vg * cos 0) Ki) := by
  have hs : 0 < σv ⬝ᵥ σv := by
    simpa using (dotProduct_self_star_pos_iff (v := σv)).mpr hσ
  rw [pllIto, pllV_second_zero]
  positivity

/-- Park geometry `σ_v^bare(θ) = (−sin θ, cos θ)` has unit norm. -/
def sigmaBare (θ : ℝ) : Fin 2 → ℝ := ![-sin θ, cos θ]

@[powerlib_foundation] theorem sigmaBare_dot_self (θ : ℝ) : sigmaBare θ ⬝ᵥ sigmaBare θ = 1 := by
  simp [sigmaBare, dotProduct, Fin.sum_univ_two]
  nlinarith [sin_sq_add_cos_sq θ]

/-- Bare SRF-PLL: `Δ_Itô = ½ (K_p² 𝒱'' + K_i)`. -/
@[powerlib_foundation] theorem pllIto_bare (Kp Ki V2 θ : ℝ) :
    itoCorrection (pllNoise Kp (sigmaBare θ)) (pllHess V2 Ki)
      = (1 / 2 : ℝ) * (Kp ^ 2 * V2 + Ki) := by
  rw [pllIto, sigmaBare_dot_self]; ring

/-- Forced-Wiener frequency channel: extra column `(σ_ω, 0)ᵀ` (only the `θ_e` equation). -/
def pllNoiseFreq (Kp : ℝ) (σv : Fin 2 → ℝ) (σω : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![Kp * σv 0, Kp * σv 1, σω; σv 0, σv 1, 0]

@[powerlib_foundation] theorem pllNoiseFreq_mul_transpose (Kp σω : ℝ) (σv : Fin 2 → ℝ) :
    pllNoiseFreq Kp σv σω * (pllNoiseFreq Kp σv σω)ᵀ
      = pllNoise Kp σv * (pllNoise Kp σv)ᵀ + !![σω ^ 2, 0; 0, 0] := by
  rw [pllNoise_mul_transpose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pllNoiseFreq, mul_apply, Fin.sum_univ_three, dotProduct, Fin.sum_univ_two] <;> ring

/-- The frequency channel adds `½ σ_ω² 𝒱''` (no `K_p²` factor, no PI-channel term). -/
@[powerlib_foundation] theorem pllIto_freq (Kp Ki V2 σω : ℝ) (σv : Fin 2 → ℝ) :
    itoCorrection (pllNoiseFreq Kp σv σω) (pllHess V2 Ki)
      = itoCorrection (pllNoise Kp σv) (pllHess V2 Ki) + (1 / 2 : ℝ) * σω ^ 2 * V2 := by
  unfold itoCorrection
  rw [pllNoiseFreq_mul_transpose, add_mul, trace_add, mul_add]
  congr 1
  simp [pllHess, trace_fin_two]
  ring

/-! ## Grid-voltage disturbance: Park projection (T-grid-disturbance-stochastic §1.2.a) -/

/-- The `q` component of the Park-rotated grid disturbance is `σ_v^bare(θ) ⬝ ξ`. -/
@[powerlib_foundation] theorem park_q_eq_sigmaBare (θ : ℝ) (ξ : Fin 2 → ℝ) :
    (powerlib.Transform.park θ *ᵥ ξ) 1 = sigmaBare θ ⬝ᵥ ξ := by
  simp [sigmaBare, dotProduct, Fin.sum_univ_two]

/-- Isotropic disturbance covariance `s I` is invariant under the Park rotation. -/
@[powerlib_foundation] theorem park_isotropic_cov (θ s : ℝ) :
    powerlib.Transform.park θ * (s • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      (powerlib.Transform.park θ)ᵀ = s • 1 := by
  rw [show (powerlib.Transform.park θ)ᵀ = powerlib.Transform.rot θ by
      rw [powerlib.Transform.park_eq_transpose_rot, transpose_transpose],
    mul_smul_comm, mul_one, smul_mul_assoc, powerlib.Transform.park_mul_rot]

/-- Anisotropic disturbance `diag(s_d, s_q)`: the projected `q` variance
`sin²θ s_d + cos²θ s_q` depends on `θ_e` (state-dependent N port) unless `s_d = s_q`. -/
@[powerlib_foundation] theorem park_q_variance (θ sd sq : ℝ) :
    sigmaBare θ ⬝ᵥ (!![sd, 0; 0, sq] *ᵥ sigmaBare θ) = sin θ ^ 2 * sd + cos θ ^ 2 * sq := by
  simp [sigmaBare, dotProduct, Fin.sum_univ_two, mulVec]
  ring

/-! ## GFL form B: closed form of `σ_v(θ_e)` (T-gfl-sph §1.1) -/

/-- Form-B quasi-steady line equations (T-gfl-dynamics §1.6 with the LC slow manifold of §1.7
substituted, `v_{c,d} = (i_q − i_{g,q})/(ω C)`, `v_{c,q} = (i_{g,d} − i_d)/(ω C)`), with the grid
disturbance `V_g → V_g + ξ_d`, `0 → ξ_q`.  `ig = (i_{g,d}, i_{g,q})`, `idq = (i_d, i_q)`. -/
def lineResidual (R L C ω Vg : ℝ) (idq ig ξ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(idq 1 - ig 1) / (ω * C) - (Vg + ξ 0) - R * ig 0 + ω * L * ig 1,
    (ig 0 - idq 0) / (ω * C) - ξ 1 - R * ig 1 - ω * L * ig 0]

/-- Effective reactance `X = ωL − 1/(ωC)`. -/
def lineX (L C ω : ℝ) : ℝ := ω * L - 1 / (ω * C)

/-- Coefficient matrix of the form-B line system (independent of `θ_e`). -/
def lineMatrix (R X : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-R, X; -X, -R]

/-- Driving term `r` (depends on `θ_e` only through `idq`). -/
def lineDrive (C ω Vg : ℝ) (idq : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![Vg - idq 1 / (ω * C), idq 0 / (ω * C)]

@[powerlib_foundation] theorem lineResidual_eq_zero_iff {R L C ω Vg : ℝ}
    (idq ig ξ : Fin 2 → ℝ) :
    lineResidual R L C ω Vg idq ig ξ = 0 ↔
      lineMatrix R (lineX L C ω) *ᵥ ig = lineDrive C ω Vg idq + ξ := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [lineResidual] at h0 h1
    ext i; fin_cases i
    · simp [lineMatrix, lineDrive, lineX, mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination h0
    · simp [lineMatrix, lineDrive, lineX, mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination h1
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [lineMatrix, lineDrive, lineX, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    ext i; fin_cases i
    · simp [lineResidual]; linear_combination h0
    · simp [lineResidual]; linear_combination h1

@[powerlib_foundation] theorem lineMatrix_det (R X : ℝ) : (lineMatrix R X).det = R ^ 2 + X ^ 2 := by
  simp [lineMatrix, det_fin_two]; ring

/-- Line sensitivity `G = M⁻¹`. -/
def lineG (R X : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (lineMatrix R X)⁻¹

/-- Superposition: for a lossy line (`R ≠ 0`) the unique solution splits as
`i_g = M⁻¹ r + G ξ` with `G = M⁻¹` independent of `θ_e` and of `ξ`. -/
@[powerlib_foundation] theorem lineSolution_split {R L C ω Vg : ℝ} (hR : R ≠ 0)
    (idq ig ξ : Fin 2 → ℝ) :
    lineResidual R L C ω Vg idq ig ξ = 0 ↔
      ig = lineG R (lineX L C ω) *ᵥ lineDrive C ω Vg idq + lineG R (lineX L C ω) *ᵥ ξ := by
  have hdet : IsUnit (lineMatrix R (lineX L C ω)).det := by
    rw [lineMatrix_det]; exact isUnit_iff_ne_zero.mpr (by positivity)
  rw [lineResidual_eq_zero_iff, lineG, ← mulVec_add]
  constructor
  · intro h; rw [← h, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  · intro h; rw [h, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]

/-- PLL input `ωC v_{c,q}^c = −sin θ (i_q − i_{g,q}) + cos θ (i_{g,d} − i_d)`
(T-gfl-dynamics §1.7). -/
def pllInput (θ : ℝ) (idq ig : Fin 2 → ℝ) : ℝ :=
  -sin θ * (idq 1 - ig 1) + cos θ * (ig 0 - idq 0)

/-- Form-B voltage-noise coefficient `σ_v(θ) = (1/(ωC)) [sin θ G_q + cos θ G_d]` (row). -/
def gflSigma (C ω θ : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → ℝ :=
  fun j => (1 / (ω * C)) * (sin θ * G 1 j + cos θ * G 0 j)

/-- **σ_v closed form (T-gfl-sph (1.1)).** Along the line solution, the PLL input splits into
its noise-free value plus `ωC σ_v(θ) ⬝ ξ`, with the `θ_e`-dependence of the noise channel only
through the Park factors `(sin θ, cos θ)`. -/
@[powerlib_foundation] theorem pllInput_noise_split {R L C ω Vg : ℝ} (hωC : ω * C ≠ 0)
    (θ : ℝ) (idq ξ : Fin 2 → ℝ) :
    let G := lineG R (lineX L C ω)
    pllInput θ idq (G *ᵥ lineDrive C ω Vg idq + G *ᵥ ξ)
      = pllInput θ idq (G *ᵥ lineDrive C ω Vg idq) + ω * C * (gflSigma C ω θ G ⬝ᵥ ξ) := by
  intro G
  have hω : ω ≠ 0 := left_ne_zero_of_mul hωC
  have hC : C ≠ 0 := right_ne_zero_of_mul hωC
  simp only [pllInput, gflSigma, dotProduct, Fin.sum_univ_two, Pi.add_apply, mulVec]
  field_simp
  ring

/-- `σ_v σ_vᵀ = (ωC)⁻² (sin²θ ‖G_q‖² + 2 sin θ cos θ ⟨G_q, G_d⟩ + cos²θ ‖G_d‖²)`. -/
@[powerlib_foundation] theorem gflSigma_sq (C ω θ : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) :
    gflSigma C ω θ G ⬝ᵥ gflSigma C ω θ G
      = (1 / (ω * C)) ^ 2 * (sin θ ^ 2 * (G 1 ⬝ᵥ G 1) + 2 * sin θ * cos θ * (G 1 ⬝ᵥ G 0)
          + cos θ ^ 2 * (G 0 ⬝ᵥ G 0)) := by
  simp only [gflSigma, dotProduct, Fin.sum_univ_two]
  ring

/-- Form-B Itô correction: `Δ_Itô = ½ σ_v σ_vᵀ (K_p² 𝒱'' + K_i)` with the closed-form `σ_v`. -/
@[powerlib_foundation] theorem gflIto (Kp Ki V2 C ω θ : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) :
    itoCorrection (pllNoise Kp (gflSigma C ω θ G)) (pllHess V2 Ki)
      = (1 / 2 : ℝ) * ((1 / (ω * C)) ^ 2 * (sin θ ^ 2 * (G 1 ⬝ᵥ G 1)
          + 2 * sin θ * cos θ * (G 1 ⬝ᵥ G 0) + cos θ ^ 2 * (G 0 ⬝ᵥ G 0)))
          * (Kp ^ 2 * V2 + Ki) := by
  rw [pllIto, gflSigma_sq]

end powerlib.PLL.StochasticPH
