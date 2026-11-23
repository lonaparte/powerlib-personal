import dependencies.Mathlib
import theorem.Passive.Series
import theorem.Passive.Parallel
import theorem.Attributes
import theorem.Stochastic.SPH
import theorem.PowerSystem.Synchronous.StochasticPH
import theorem.Transform.Park
import theorem.GridTiedConverter.PLL.Linear

/-! # Itô correction of the SRF-PLL SPHS and its grid-disturbance specialization

Model boundary.
State `(θ_e, η)` of the SRF-PLL (phase error, PI integrator), Hamiltonian
`𝓗 = 𝒱(θ_e) + ½ K_i η²`.  The voltage disturbance `ξ_v = (ξ_d, ξ_q)` enters through the
1×2 row `σ_v(θ_e)`: `dθ_e ∋ K_p σ_v dW_v`, `dη ∋ σ_v dW_v`.  The GFL form-B row `σ_v(θ_e)` (the
quasi-steady line + LC algebra, grid EMF `(V_g + ξ_d, ξ_q)`) is `GFL.LCLine.Network.sigmaV`
(`theorem/GridTiedConverter/GFL/LCLine/Reduction.lean`); its Itô correction is
`GFL.Noise.Embed.gflIto`.
These are algebraic identities of the selected PLL models and supporting signal lemmas. The correction is
`½ tr(h hᵀ ∇²𝓗)` at a state (see `SPH.itoCorrection`); no SDE solution, Itô formula,
escape rate or stability claim is made (Rules §3).

Source: `theorem/Stochastic/SPH.lean` (`itoCorrection`, `itoCorrection_merged`),
`theorem/PowerSystem/Synchronous/StochasticPH.lean` (`sparseNoise`, `itoCorrection_sparseNoise`);
work-sync `theory/T-pll-sph.md` §1.1–§1.2 (noise coupling `h_noise = (K_p σ_v, σ_v)ᵀ`,
Hessian `diag(𝒱'', K_i)`, `Δ_Itô = ½ σ_v²[K_p² 𝒱'' + K_i]` (1.6), saddle value and the
`ζ = 1/2` threshold (1.7), frequency-channel supplement `½ σ_ω² 𝒱''`), `theory/T-pll-ph.md`
(potential `𝒱(θ) = V_g(1 − cos θ)`, `PLL.srfPotential`),
`theory/T-grid-disturbance-stochastic.md` §1.2.a (Park projection `σ_v^bare`).

Results.
* `pllIto`: `Δ_Itô = ½ σ_v σ_vᵀ (K_p² 𝒱'' + K_i)` for the SRF-PLL noise coupling;
  `pllIto_freq` adds the frequency channel `½ σ_ω² 𝒱''`.
* `pllIto_saddle`, `pllIto_saddle_neg_iff`, `pllIto_saddle_pos_iff`, `pllIto_bottom_pos`: at the
  saddle `θ_e = π` the correction is negative iff `ζ > 1/2`; at the well bottom it is positive.
* `pllIto_bare`, `park_q_eq_sigmaBare`, `park_isotropic_cov`, `park_q_variance`: the bare
  grid-disturbance coupling `σ_v^bare = (−sin θ, cos θ)` (unit norm) of the Park projection.

Correction (T-gfl-sph §1.3 / T-pll-sph (1.6)).  `σ_v` is a **row vector**, so "σ_v²" must be
read as `σ_v σ_vᵀ = σ_v ⬝ σ_v` (`pllNoise_mul_transpose`).  With that reading the closed forms of
the note are reproduced exactly (`pllIto`; for the form-B row,
`GFL.LCLine.Network.sigmaV_dot_self`).
-/

noncomputable section
namespace powerlib.PLL.StochasticPH

open Matrix Real
open powerlib.Stochastic.SPH

/-! ## Potential and Hessian -/

/-- Hessian `∇²𝓗 = diag(𝒱''(θ), K_i)` of `𝓗 = 𝒱(θ) + ½ K_i η²` (separable, no cross term). -/
def pllHess (V2 Ki : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![V2, 0; 0, Ki]

/-! ## Noise coupling and the Itô correction (T-pll-sph (1.6)) -/

/-- Voltage-noise coupling `h_noise = (K_p σ_v, σ_v)ᵀ` (rows: `θ_e`, `η`; columns: `d`, `q`). -/
def pllNoise (Kp : ℝ) (σv : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Kp * σv 0, Kp * σv 1; σv 0, σv 1]

@[tmio M, powerlib_domain] theorem pllNoise_mul_transpose (Kp : ℝ) (σv : Fin 2 → ℝ) :
    pllNoise Kp σv * (pllNoise Kp σv)ᵀ = (σv ⬝ᵥ σv) • !![Kp ^ 2, Kp; Kp, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pllNoise, mul_apply, Fin.sum_univ_two, dotProduct] <;> ring

/-- `Δ_Itô^PLL = ½ (σ_v σ_vᵀ) (K_p² 𝒱'' + K_i)`. -/
@[tmio M, powerlib_domain] theorem pllIto (Kp Ki V2 : ℝ) (σv : Fin 2 → ℝ) :
    itoCorrection (pllNoise Kp σv) (pllHess V2 Ki)
      = (1 / 2 : ℝ) * (σv ⬝ᵥ σv) * (Kp ^ 2 * V2 + Ki) := by
  unfold itoCorrection
  rw [pllNoise_mul_transpose, smul_mul_assoc, trace_smul]
  simp [pllHess, trace_fin_two]
  ring

/-- Saddle value: `Δ_Itô^PLL(π) = ½ σ_v σ_vᵀ K_i (1 − 4ζ²)`, with the PLL damping ratio
`ζ = PLL.zeta V_g K_p K_i = K_p √V_g / (2 √K_i)` (T-pll-dynamics §1.3). -/
@[tmio M, powerlib_domain] theorem pllIto_saddle {Kp Vg Ki : ℝ} (hVg : 0 ≤ Vg) (hKi : 0 < Ki)
    (σv : Fin 2 → ℝ) :
    itoCorrection (pllNoise Kp σv) (pllHess (Vg * cos π) Ki)
      = (1 / 2 : ℝ) * (σv ⬝ᵥ σv) * Ki * (1 - 4 * PLL.zeta Vg Kp Ki ^ 2) := by
  have h4 : 4 * PLL.zeta Vg Kp Ki ^ 2 = Vg * Kp ^ 2 / Ki := by
    rcases hVg.eq_or_lt with rfl | hVg
    · simp [PLL.zeta]
    · exact PLL.four_mul_zeta_sq hVg.ne' (mul_pos hVg hKi)
  rw [pllIto, Real.cos_pi, mul_neg_one, h4]
  field_simp
  ring

/-- **ζ = 1/2 threshold**: for nonzero voltage noise, `Δ_Itô^PLL(π) < 0 ⇔ ζ > 1/2`. -/
@[tmio M, powerlib_domain] theorem pllIto_saddle_neg_iff {Kp Vg Ki : ℝ} (hKp : 0 ≤ Kp)
    (hVg : 0 ≤ Vg) (hKi : 0 < Ki) {σv : Fin 2 → ℝ} (hσ : σv ≠ 0) :
    itoCorrection (pllNoise Kp σv) (pllHess (Vg * cos π) Ki) < 0 ↔ 1 / 2 < PLL.zeta Vg Kp Ki := by
  have hs : 0 < σv ⬝ᵥ σv := by
    rcases (dotProduct_self_star_pos_iff (v := σv)).mpr hσ with h
    simpa using h
  have hz : 0 ≤ PLL.zeta Vg Kp Ki := by unfold PLL.zeta PLL.omegaN; positivity
  rw [pllIto_saddle hVg hKi]
  constructor
  · intro h
    have : 1 - 4 * PLL.zeta Vg Kp Ki ^ 2 < 0 := by
      by_contra hc; push Not at hc
      have : 0 ≤ (1 / 2 : ℝ) * (σv ⬝ᵥ σv) * Ki * (1 - 4 * PLL.zeta Vg Kp Ki ^ 2) := by positivity
      linarith
    nlinarith
  · intro h
    have : 1 - 4 * PLL.zeta Vg Kp Ki ^ 2 < 0 := by nlinarith
    have hpos : 0 < (1 / 2 : ℝ) * (σv ⬝ᵥ σv) * Ki := by positivity
    exact mul_neg_of_pos_of_neg hpos this

/-- Conversely `Δ_Itô^PLL(π) > 0 ⇔ ζ < 1/2` (PI-channel diffusion dominates). -/
@[tmio M, powerlib_domain] theorem pllIto_saddle_pos_iff {Kp Vg Ki : ℝ} (hKp : 0 ≤ Kp)
    (hVg : 0 ≤ Vg) (hKi : 0 < Ki) {σv : Fin 2 → ℝ} (hσ : σv ≠ 0) :
    0 < itoCorrection (pllNoise Kp σv) (pllHess (Vg * cos π) Ki) ↔ PLL.zeta Vg Kp Ki < 1 / 2 := by
  have hs : 0 < σv ⬝ᵥ σv := by
    simpa using (dotProduct_self_star_pos_iff (v := σv)).mpr hσ
  have hz : 0 ≤ PLL.zeta Vg Kp Ki := by unfold PLL.zeta PLL.omegaN; positivity
  rw [pllIto_saddle hVg hKi]
  have hpos : 0 < (1 / 2 : ℝ) * (σv ⬝ᵥ σv) * Ki := by positivity
  constructor
  · intro h
    have : 0 < 1 - 4 * PLL.zeta Vg Kp Ki ^ 2 := (pos_iff_pos_of_mul_pos h).mp hpos
    nlinarith
  · intro h
    exact mul_pos hpos (by nlinarith)

/-- Well bottom `θ_e = 0`: `Δ_Itô^PLL > 0` (noise rectification). -/
@[tmio M, powerlib_domain] theorem pllIto_bottom_pos {Kp Vg Ki : ℝ} (hVg : 0 ≤ Vg) (hKi : 0 < Ki)
    {σv : Fin 2 → ℝ} (hσ : σv ≠ 0) :
    0 < itoCorrection (pllNoise Kp σv) (pllHess (Vg * cos 0) Ki) := by
  have hs : 0 < σv ⬝ᵥ σv := by
    simpa using (dotProduct_self_star_pos_iff (v := σv)).mpr hσ
  rw [pllIto, Real.cos_zero, mul_one]
  positivity

/-- Park geometry `σ_v^bare(θ) = (−sin θ, cos θ)` has unit norm. -/
def sigmaBare (θ : ℝ) : Fin 2 → ℝ := ![-sin θ, cos θ]

@[tmio M, powerlib_domain] theorem sigmaBare_dot_self (θ : ℝ) : sigmaBare θ ⬝ᵥ sigmaBare θ = 1 := by
  simp [sigmaBare, dotProduct, Fin.sum_univ_two]
  nlinarith [sin_sq_add_cos_sq θ]

/-- Bare SRF-PLL: `Δ_Itô = ½ (K_p² 𝒱'' + K_i)`. -/
@[tmio M, powerlib_domain] theorem pllIto_bare (Kp Ki V2 θ : ℝ) :
    itoCorrection (pllNoise Kp (sigmaBare θ)) (pllHess V2 Ki)
      = (1 / 2 : ℝ) * (Kp ^ 2 * V2 + Ki) := by
  rw [pllIto, sigmaBare_dot_self]; ring

/-- Forced-Wiener frequency channel: extra column `(σ_ω, 0)ᵀ` (only the `θ_e` equation), the
sparse noise `Synchronous.SM.sparseNoise ![0] ![σ_ω]` appended to the PI-channel coupling. -/
def pllNoiseFreq (Kp : ℝ) (σv : Fin 2 → ℝ) (σω : ℝ) : Matrix (Fin 2) (Fin 2 ⊕ Fin 1) ℝ :=
  fromCols (pllNoise Kp σv) (Synchronous.SM.sparseNoise ![0] ![σω])

/-- The frequency channel adds `½ σ_ω² 𝒱''` (no `K_p²` factor, no PI-channel term): the merged
correction of the two independent channels (`SPH.itoCorrection_merged`) with the sparse one
(`Synchronous.SM.itoCorrection_sparseNoise`). -/
@[tmio M, powerlib_domain] theorem pllIto_freq (Kp Ki V2 σω : ℝ) (σv : Fin 2 → ℝ) :
    itoCorrection (pllNoiseFreq Kp σv σω) (pllHess V2 Ki)
      = itoCorrection (pllNoise Kp σv) (pllHess V2 Ki) + (1 / 2 : ℝ) * σω ^ 2 * V2 := by
  have h := itoCorrection_merged (pllNoise Kp σv) (Synchronous.SM.sparseNoise ![0] ![σω]) 1
    (pllHess V2 Ki)
  rw [Matrix.mul_one] at h
  rw [pllNoiseFreq, h, Synchronous.SM.itoCorrection_sparseNoise]
  simp [pllHess]
  ring

/-! ## Grid-voltage disturbance: Park projection (T-grid-disturbance-stochastic §1.2.a) -/

/-- The `q` component of the Park-rotated grid disturbance is `σ_v^bare(θ) ⬝ ξ`. -/
@[tmio M, powerlib_domain] theorem park_q_eq_sigmaBare (θ : ℝ) (ξ : Fin 2 → ℝ) :
    (powerlib.Transform.park θ *ᵥ ξ) 1 = sigmaBare θ ⬝ᵥ ξ := by
  simp [sigmaBare, dotProduct, Fin.sum_univ_two]

/-- Isotropic disturbance covariance `s I` is invariant under the Park rotation. -/
@[tmio M, powerlib_domain] theorem park_isotropic_cov (θ s : ℝ) :
    powerlib.Transform.park θ * (s • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      (powerlib.Transform.park θ)ᵀ = s • 1 := by
  rw [show (powerlib.Transform.park θ)ᵀ = powerlib.Transform.rot θ by
      rw [powerlib.Transform.park_eq_transpose_rot, transpose_transpose],
    mul_smul_comm, mul_one, smul_mul_assoc, powerlib.Transform.park_mul_rot]

/-- Anisotropic disturbance `diag(s_d, s_q)`: the projected `q` variance
`sin²θ s_d + cos²θ s_q` depends on `θ_e` (state-dependent N port) unless `s_d = s_q`. -/
@[tmio M, powerlib_domain] theorem park_q_variance (θ sd sq : ℝ) :
    sigmaBare θ ⬝ᵥ (!![sd, 0; 0, sq] *ᵥ sigmaBare θ) = sin θ ^ 2 * sd + cos θ ^ 2 * sq := by
  simp [sigmaBare, dotProduct, Fin.sum_univ_two, mulVec]
  ring

end powerlib.PLL.StochasticPH
