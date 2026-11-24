import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.LyapunovCovariance
import theorem.PowerSystem.Frequency.StochasticCOI
import theorem.GridTiedConverter.GFM.VSMLPF
import theorem.GridTiedConverter.GFM.Noise.Embedding
import theorem.GridTiedConverter.GFL.Noise.NoiseLyapunov

/-! # Closed-form covariance Lyapunov solutions of the linearized noisy GFM (two and three states)

Domain module. The matrices below are proved to be the unique solutions of the continuous
Lyapunov equation `A P + P Aᵀ + B Bᵀ = 0` of the linearized GFM with a noise port `B`; they are
not asserted to be stationary covariances of any stochastic process (no SDE is formalized).

Model boundary.
* Two states: the reduced GFM of `theorem/GridTiedConverter/GFM/Noise/Embedding.lean` linearized
  at an angle `δ*` in the coordinates `(δ, ω)` (`ω = p/M`): `A` is the swing Jacobian
  `SwingParams.jacobian` of the classical machine `GFM.Noise.Params.toSM` at `θ* = δ* − α`
  (computed by `fderiv`, `SwingParams.hasFDerivAt_field`), the mechanical Jacobian
  `Frequency.FreqCov.swingA M D K` with `K = A cos(δ* − α)` (`jacobian_eq`). Noise port
  `diag(1, 1/M) h(δ*)` (`diffusionOmega`): the diffusion of `GFM.Noise.Params.diffusion` in the
  coordinates `(δ, ω)`, the voltage rows frozen at the operating angle.
* Three states: the VSM with a first-order power filter `GFM.VSMLPF` (lossless line; the lossy
  line is the same model after the shift of `theorem/GridTiedConverter/GFM/VSMLPFLossy.lean`),
  state `(δ, ω, P_f)`, `A = VSMLPF.jacobian δ*` (computed by `fderiv`,
  `VSMLPF.hasFDerivAt_field`), `K = K₀ cos δ*`. Noise ports: power set-point `(0, s/M, 0)ᵀ`
  (`portPref`), grid frequency `(−ε, 0, 0)ᵀ` (`portFreq`), measured power / grid voltage through
  the filter `(0, 0, ω_c s)ᵀ` (`portVolt`, `s` the power-noise intensity, e.g. `k σ_q cos` of the
  voltage row at the operating angle). Continuous time, unit-intensity white noise idealization.
* Physical range for uniqueness: `M, D, ω_c > 0`, `0 < K < K_H = D ω_c + D²/M` (Hurwitz,
  the VSMLPF stability region).

Source: GFM counterpart study, note t2-noise items 6 and 8 (covariance closed forms of the two- and
three-state channels, equipartition breaking; derived symbolically and checked against a
numerical Lyapunov solver, scratch notes outside the repository); work-sync
`theory/T-frequency-stability-stochastic.md` §1.3 (Lyapunov equation (1.7)); the GFL counterpart
`theorem/GridTiedConverter/GFL/Noise/NoiseLyapunov.lean`.

Results.
* Two states: `jacobian_eq`; `diffusionOmega_freq` (the grid-frequency port in `(δ, ω)` is
  `(−ε, κ D ε/M)ᵀ`); `covFreq_solves`, `covFreq_unique`: the frequency-channel solution
  `Var δ = ε²(D²(1 − κ)² + K M)/(2 D K)`, `Cov = −ε²/2`, `Var ω = ε²(D² κ² + K M)/(2 D M)`
  (nominal damping `κ = 0`: `Var ω = K ε²/(2D)`; grid-referenced `κ = 1`: `Var δ = M ε²/(2D)`),
  unique for `M, D, K ≠ 0` (`Stochastic.Lyapunov.solvesCovLyapunov_unique_fin_two`);
  `powerRow_cov_unique`: without the frequency channel the solution is the library's
  `Frequency.FreqCov.swingCov M D K a(θ*)` (`Frequency.FreqCov.swingCov_unique`, `a` the momentum
  diffusion of the power rows).
* GFL dictionary `(K_p, K_i, g) = (D, K, 1/M)`, coordinates `(p, δ)` (`dictT`):
  `linA_dictionary` (the linearizations coincide with `GFL.Noise.linA`), `covW_dictionary` (the
  GFL frequency-channel solution `GFL.Noise.covW` is the GFM set-point solution),
  `covV_dictionary` (the GFL voltage-channel solution `GFL.Noise.covV` is the GFM
  grid-frequency solution with grid-referenced damping): the noise channels exchange roles.
* Three states (namespace `GFM.Noise.VSM3`): `cov3Pref_solves`, `cov3Freq_solves`,
  `cov3Volt_solves` (closed forms with the common denominator `2 M (K_H − K)`, `KH`, `gap`),
  `cov3_unique` (uniqueness in the Hurwitz region,
  `Stochastic.Lyapunov.solvesCovLyapunov_unique`, Hurwitz by the cubic Routh criterion
  `Criteria.isHurwitz_iff_of_coeffs_cubic`).
* Equipartition breaking (set-point channel, `T = s²/(2D)`): `cov3Pref_omega`
  (`Var ω = (T/M) K_H/(K_H − K)`, against `T/M` for two states), `cov3Pref_delta`
  (`Var δ = (T/K)(K_H + D K/(M ω_c))/(K_H − K)`), `cov3Pref_cross` (`Cov(δ, ω) = 0`),
  `cov3Pref_omega_ne` (`Var ω ≠ T/M` whenever `K ≠ 0`).
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real Matrix
open powerlib.Stochastic.Lyapunov (SolvesCovLyapunov)

/-! ## Two states -/

namespace Params

variable (p : Params)

/-- The linearization at `θ = δ − α` in `(δ, ω)`: the swing Jacobian of the machine `toSM` is the
mechanical Jacobian with synchronizing coefficient `K = A cos θ`. -/
@[tmio M, powerlib_domain] theorem jacobian_eq (θ : ℝ) :
    p.toSM.toSwing.jacobian θ = Frequency.FreqCov.swingA p.M p.D (p.A * Real.cos θ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Synchronous.SwingParams.jacobian, Synchronous.ClassicalSMParams.toSwing,
      Synchronous.SwingParams.syncCoeff, Synchronous.SwingParams.sinusoid,
      PhasePlane.Conservative.jacobian, toSM]

/-- Noise port in the coordinates `(δ, ω)`: `diag(1, 1/M) h(δ)`. -/
def diffusionOmega (κ : ℝ) (σ : Fin 4 → ℝ) (δ : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  Dynamics.scaleMatrix p.M⁻¹ * p.diffusion κ σ δ

/-- The grid-frequency port in `(δ, ω)`: `B Bᵀ` of the column `(−ε, κ D ε/M)ᵀ`. -/
@[tmio M, powerlib_domain] theorem diffusionOmega_freq (κ ε δ : ℝ) :
    p.diffusionOmega κ (freqOnly ε) δ * (p.diffusionOmega κ (freqOnly ε) δ)ᵀ =
      !![-ε; κ * p.D * ε / p.M] * (!![-ε; κ * p.D * ε / p.M])ᵀ := by
  have hS : p.diffusionOmega κ (freqOnly ε) δ = !![0, -ε, 0, 0; 0, κ * p.D * ε / p.M, 0, 0] := by
    ext i j
    rw [diffusionOmega, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [Dynamics.scaleMatrix, diffusion_apply, noiseMatrix, freqOnly]
    all_goals ring
  rw [hS]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_one, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

end Params

/-- Frequency-channel solution in `(δ, ω)` (`κ` the damping reference). -/
def covFreq (M D K κ ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ε ^ 2 * (D ^ 2 * (1 - κ) ^ 2 + K * M) / (2 * D * K), -(ε ^ 2 / 2);
     -(ε ^ 2 / 2), ε ^ 2 * (D ^ 2 * κ ^ 2 + K * M) / (2 * D * M)]

namespace Params

variable (p : Params)

/-- `covFreq` solves the Lyapunov equation of the frequency channel. -/
@[tmio M, powerlib_domain] theorem covFreq_solves (κ ε δ : ℝ) (hD : p.D ≠ 0)
    (hK : p.A * Real.cos (δ - p.α) ≠ 0) :
    SolvesCovLyapunov (p.toSM.toSwing.jacobian (δ - p.α))
      (covFreq p.M p.D (p.A * Real.cos (δ - p.α)) κ ε)
      (p.diffusionOmega κ (freqOnly ε) δ * (p.diffusionOmega κ (freqOnly ε) δ)ᵀ) := by
  have hM := p.M_pos.ne'
  have hA := left_ne_zero_of_mul hK
  have hc := right_ne_zero_of_mul hK
  rw [jacobian_eq, diffusionOmega_freq]
  unfold SolvesCovLyapunov
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.transpose_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Frequency.FreqCov.swingA, PhasePlane.Conservative.jacobian, covFreq] <;>
    field_simp <;> ring

/-- Uniqueness of the frequency-channel solution (`tr A = −D/M ≠ 0`, `det A = K/M ≠ 0`). -/
@[tmio M, powerlib_domain] theorem covFreq_unique {κ ε δ : ℝ} (hD : p.D ≠ 0)
    (hK : p.A * Real.cos (δ - p.α) ≠ 0) {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : SolvesCovLyapunov (p.toSM.toSwing.jacobian (δ - p.α)) P
      (p.diffusionOmega κ (freqOnly ε) δ * (p.diffusionOmega κ (freqOnly ε) δ)ᵀ)) :
    P = covFreq p.M p.D (p.A * Real.cos (δ - p.α)) κ ε := by
  have hM := p.M_pos.ne'
  refine Stochastic.Lyapunov.solvesCovLyapunov_unique_fin_two ?_ ?_ hP
    (p.covFreq_solves κ ε δ hD hK)
  · rw [jacobian_eq, PhasePlane.Conservative.trace_jacobian]
    exact div_ne_zero (neg_ne_zero.mpr hD) hM
  · rw [jacobian_eq, PhasePlane.Conservative.det_jacobian]
    exact div_ne_zero hK hM

/-- **Power rows**: without the frequency channel the unique solution is the library's swing
covariance `Frequency.FreqCov.swingCov M D K a(θ*)` with the momentum diffusion
`a = σ_P² + k²(σ_d² sin²θ* + σ_q² cos²θ*)` at the operating angle (`K > 0`, `D > 0`). -/
@[tmio M, powerlib_domain] theorem powerRow_cov_unique (κ : ℝ) {σ : Fin 4 → ℝ} (hε : σ 1 = 0)
    {δ : ℝ} (hD : 0 < p.D) (hK : 0 < p.A * Real.cos (δ - p.α)) {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : SolvesCovLyapunov (p.toSM.toSwing.jacobian (δ - p.α)) P
      (p.diffusionOmega κ σ δ * (p.diffusionOmega κ σ δ)ᵀ)) :
    P = Frequency.FreqCov.swingCov p.M p.D (p.A * Real.cos (δ - p.α))
      (σ 0 ^ 2 + p.k ^ 2 * (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 +
        σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2)) := by
  set a := σ 0 ^ 2 + p.k ^ 2 * (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 +
    σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2) with ha
  have ha0 : 0 ≤ a := by positivity
  have hQ : p.diffusionOmega κ σ δ * (p.diffusionOmega κ σ δ)ᵀ =
      Frequency.FreqCov.swingNoise p.M √a 0 * (Frequency.FreqCov.swingNoise p.M √a 0)ᵀ := by
    rw [Frequency.FreqCov.swingNoise_mul_transpose, Real.sq_sqrt ha0, diffusionOmega,
      Matrix.transpose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc (p.diffusion κ σ δ), diffusion_mul_transpose, hε]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> simp [Dynamics.scaleMatrix, ha]
    all_goals ring
  rw [jacobian_eq, hQ] at hP
  have h := Frequency.FreqCov.swingCov_unique p.M_pos hD hK √a 0 hP
  rwa [Real.sq_sqrt ha0, zero_pow two_ne_zero, add_zero] at h

end Params

/-! ## The GFL dictionary -/

/-- The coordinate change `(δ, ω) ↦ (p, δ) = (M ω, δ)`. -/
def dictT (M : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, M; 1, 0]

/-- **Linearizations coincide under the dictionary** `(K_p, K_i, g) = (D, K, 1/M)`: in the
coordinates `(p, δ)` the GFM linearization is the GFL code-convention linearization
`GFL.Noise.linA D K (1/M)` of `theorem/GridTiedConverter/GFL/Noise/NoiseLyapunov.lean`. -/
@[tmio M, powerlib_domain] theorem linA_dictionary {M : ℝ} (hM : M ≠ 0) (D K : ℝ) :
    dictT M * Frequency.FreqCov.swingA M D K = GFL.Noise.linA D K (1 / M) * dictT M := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dictT, Frequency.FreqCov.swingA, PhasePlane.Conservative.jacobian, GFL.Noise.linA,
      PLL.piPLLJacobian, NormalForm.BogdanovTakens.proportionalMatrix, Dynamics.signMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

/-- The GFL frequency-channel (Gibbs) solution `GFL.Noise.covW` is, under the dictionary, the GFM
set-point solution with unit noise (`Frequency.FreqCov.swingCov M D K 1`). -/
@[tmio M, powerlib_domain] theorem covW_dictionary {M : ℝ} (hM : M ≠ 0) (D K : ℝ) :
    dictT M * Frequency.FreqCov.swingCov M D K 1 * (dictT M)ᵀ = GFL.Noise.covW D K (1 / M) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dictT, Frequency.FreqCov.swingCov, GFL.Noise.covW, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.vecMul_diagonal]
  all_goals field_simp

/-- The GFL voltage-channel solution `GFL.Noise.covV` is, under the dictionary, the GFM
grid-frequency solution with grid-referenced damping (`κ = 1`). -/
@[tmio M, powerlib_domain] theorem covV_dictionary {M K : ℝ} (hM : M ≠ 0) (hK : K ≠ 0) (D ε : ℝ) :
    dictT M * covFreq M D K 1 ε * (dictT M)ᵀ = GFL.Noise.covV D K (1 / M) ε := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dictT, covFreq, GFL.Noise.covV, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp
  all_goals ring

/-! ## Three states (VSM + power filter) -/

namespace VSM3

variable (g : VSMLPF)

/-- Power set-point port `(0, s/M, 0)ᵀ`. -/
def portPref (s : ℝ) : Matrix (Fin 3) (Fin 1) ℝ := !![0; s / g.M; 0]

/-- Grid-frequency port `(−ε, 0, 0)ᵀ`. -/
def portFreq (ε : ℝ) : Matrix (Fin 3) (Fin 1) ℝ := !![-ε; 0; 0]

/-- Measured-power (grid-voltage) port through the filter `(0, 0, ω_c s)ᵀ`. -/
def portVolt (s : ℝ) : Matrix (Fin 3) (Fin 1) ℝ := !![0; 0; g.ωc * s]

/-- The Routh (Hopf) bound `K_H = D ω_c + D²/M`. -/
def KH : ℝ := g.D * g.ωc + g.D ^ 2 / g.M

/-- `M (K_H − K)` as a polynomial: `M D ω_c + D² − M K`. -/
def gap (K : ℝ) : ℝ := g.M * g.D * g.ωc + g.D ^ 2 - g.M * K

/-- Set-point channel solution (common factor `s²/(2 M (K_H − K))`). -/
def cov3Pref (K s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (s ^ 2 / (2 * gap g K)) •
    !![(g.D * g.ωc + K + g.M * g.ωc ^ 2) / (K * g.ωc), 0, g.D + g.M * g.ωc;
       0, (g.D + g.M * g.ωc) / g.M, -K;
       g.D + g.M * g.ωc, -K, K * (g.D + g.M * g.ωc)]

/-- Grid-frequency channel solution. -/
def cov3Freq (K ε : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (ε ^ 2 / (2 * gap g K)) •
    !![(g.D ^ 3 * g.ωc + g.D ^ 2 * K + g.D ^ 2 * g.M * g.ωc ^ 2 + g.D * K * g.M * g.ωc +
          K * g.M ^ 2 * g.ωc ^ 2) / (K * g.ωc), -gap g K,
        g.D ^ 3 + g.D ^ 2 * g.M * g.ωc + K * g.M ^ 2 * g.ωc;
       -gap g K, K * (g.D + g.M * g.ωc), -(g.D * K * (g.D + g.M * g.ωc));
       g.D ^ 3 + g.D ^ 2 * g.M * g.ωc + K * g.M ^ 2 * g.ωc, -(g.D * K * (g.D + g.M * g.ωc)),
        K * (g.D ^ 3 + g.D ^ 2 * g.M * g.ωc + K * g.M ^ 2 * g.ωc)]

/-- Measured-power channel solution. -/
def cov3Volt (K s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (s ^ 2 / (2 * gap g K)) •
    !![(g.D + g.M * g.ωc) / K, 0, g.M * g.ωc;
       0, g.ωc, -(g.D * g.ωc);
       g.M * g.ωc, -(g.D * g.ωc), g.D * g.ωc * (g.D + g.M * g.ωc)]

@[tmio M, powerlib_domain] theorem cov3Pref_solves {δ : ℝ} (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    (hK : g.K0 * Real.cos δ ≠ 0) (hgap : gap g (g.K0 * Real.cos δ) ≠ 0) (s : ℝ) :
    SolvesCovLyapunov (g.jacobian δ) (cov3Pref g (g.K0 * Real.cos δ) s)
      (portPref g s * (portPref g s)ᵀ) := by
  unfold SolvesCovLyapunov
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_one,
    Matrix.transpose_apply, Matrix.zero_apply]
  have hK0 := left_ne_zero_of_mul hK
  have hc := right_ne_zero_of_mul hK
  fin_cases i <;> fin_cases j <;>
    simp [VSMLPF.jacobian, cov3Pref, portPref] <;> field_simp <;> (try unfold gap) <;> ring

@[tmio M, powerlib_domain] theorem cov3Freq_solves {δ : ℝ} (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    (hK : g.K0 * Real.cos δ ≠ 0) (hgap : gap g (g.K0 * Real.cos δ) ≠ 0) (ε : ℝ) :
    SolvesCovLyapunov (g.jacobian δ) (cov3Freq g (g.K0 * Real.cos δ) ε)
      (portFreq ε * (portFreq ε)ᵀ) := by
  unfold SolvesCovLyapunov
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_one,
    Matrix.transpose_apply, Matrix.zero_apply]
  have hK0 := left_ne_zero_of_mul hK
  have hc := right_ne_zero_of_mul hK
  fin_cases i <;> fin_cases j <;>
    simp [VSMLPF.jacobian, cov3Freq, portFreq] <;> field_simp <;> (try unfold gap) <;> ring

@[tmio M, powerlib_domain] theorem cov3Volt_solves {δ : ℝ} (hM : g.M ≠ 0)
    (hK : g.K0 * Real.cos δ ≠ 0) (hgap : gap g (g.K0 * Real.cos δ) ≠ 0) (s : ℝ) :
    SolvesCovLyapunov (g.jacobian δ) (cov3Volt g (g.K0 * Real.cos δ) s)
      (portVolt g s * (portVolt g s)ᵀ) := by
  unfold SolvesCovLyapunov
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_one,
    Matrix.transpose_apply, Matrix.zero_apply]
  have hK0 := left_ne_zero_of_mul hK
  have hc := right_ne_zero_of_mul hK
  fin_cases i <;> fin_cases j <;>
    simp [VSMLPF.jacobian, cov3Volt, portVolt] <;> field_simp <;> (try unfold gap) <;> ring

/-- In the stability region `0 < K < K_H` (`M, D, ω_c > 0`) the Jacobian is Hurwitz (cubic Routh
criterion on `M s³ + (D + M ω_c) s² + D ω_c s + ω_c K`), so every forcing has at most one
solution. -/
@[tmio M, powerlib_domain] theorem cov3_unique {δ : ℝ} (hM : 0 < g.M) (hD : 0 < g.D)
    (hω : 0 < g.ωc) (hK : 0 < g.K0 * Real.cos δ) (hKH : g.K0 * Real.cos δ < KH g)
    {P P' Q : Matrix (Fin 3) (Fin 3) ℝ} (hP : SolvesCovLyapunov (g.jacobian δ) P Q)
    (hP' : SolvesCovLyapunov (g.jacobian δ) P' Q) : P = P' := by
  refine Stochastic.Lyapunov.solvesCovLyapunov_unique ?_ hP hP'
  rw [Criteria.isHurwitz_iff_of_coeffs_cubic _ hM (a2 := g.D + g.M * g.ωc)
    (a1 := g.D * g.ωc) (a0 := g.ωc * (g.K0 * Real.cos δ))
    (by rw [VSMLPF.trace_jacobian]; field_simp; ring) (VSMLPF.principalMinorSum_jacobian _ _)
    (by rw [VSMLPF.det_jacobian])]
  refine ⟨by positivity, mul_pos hω hK, ?_⟩
  have h1 : g.M * (g.K0 * Real.cos δ) < g.M * KH g := mul_lt_mul_of_pos_left hKH hM
  have h2 : g.M * KH g = g.M * g.D * g.ωc + g.D ^ 2 := by unfold KH; field_simp
  nlinarith [mul_pos hω hM]

/-! ### Equipartition breaking (set-point channel) -/

/-- `Var ω = (T/M) K_H/(K_H − K)` with `T = s²/(2D)` (two states: `T/M`). -/
@[tmio M, powerlib_domain] theorem cov3Pref_omega (hM : g.M ≠ 0) (hD : g.D ≠ 0) {K : ℝ}
    (hgap : gap g K ≠ 0) (s : ℝ) :
    cov3Pref g K s 1 1 = s ^ 2 / (2 * g.D) / g.M * (KH g / (KH g - K)) := by
  have hKH : KH g - K ≠ 0 := by
    intro h; apply hgap; unfold gap; unfold KH at h; field_simp at h; linarith
  unfold gap at hgap
  simp [cov3Pref, gap, KH] at hKH ⊢
  field_simp
  ring

/-- `Var δ = (T/K)(K_H + D K/(M ω_c))/(K_H − K)` (two states: `T/K`). -/
@[tmio M, powerlib_domain] theorem cov3Pref_delta (hM : g.M ≠ 0) (hD : g.D ≠ 0) (hω : g.ωc ≠ 0)
    {K : ℝ} (hK : K ≠ 0) (hgap : gap g K ≠ 0) (s : ℝ) :
    cov3Pref g K s 0 0 =
      s ^ 2 / (2 * g.D) / K * ((KH g + g.D * K / (g.M * g.ωc)) / (KH g - K)) := by
  have hKH : KH g - K ≠ 0 := by
    intro h; apply hgap; unfold gap; unfold KH at h; field_simp at h; linarith
  unfold gap at hgap
  simp [cov3Pref, gap, KH] at hKH ⊢
  field_simp
  ring

/-- `Cov(δ, ω) = 0`, as for two states. -/
@[tmio M, powerlib_domain] theorem cov3Pref_cross (K s : ℝ) : cov3Pref g K s 0 1 = 0 := by
  simp [cov3Pref]

/-- **Equipartition is broken** by the filter: for `s ≠ 0`, `K ≠ 0` (below the Hopf bound),
`Var ω ≠ T/M`.

(`M, D > 0`; the filter bandwidth enters only through `K_H`.) -/
@[tmio M, powerlib_domain] theorem cov3Pref_omega_ne (hM : 0 < g.M) (hD : 0 < g.D) {K : ℝ}
    (hK : K ≠ 0) (hgap : gap g K ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    cov3Pref g K s 1 1 ≠ s ^ 2 / (2 * g.D) / g.M := by
  rw [cov3Pref_omega g hM.ne' hD.ne' hgap]
  intro h
  have hT : s ^ 2 / (2 * g.D) / g.M ≠ 0 := by positivity
  have h1 : KH g / (KH g - K) = 1 := by
    have := mul_left_cancel₀ hT (h.trans (mul_one _).symm)
    exact this
  have hKH : KH g - K ≠ 0 := by
    intro h0; rw [h0, div_zero] at h1; exact zero_ne_one h1
  rw [div_eq_one_iff_eq hKH] at h1
  exact hK (by linarith)

end VSM3

end powerlib.GFM.Noise
