import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes
import theorem.Criteria.Hurwitz2
import theorem.Stochastic.LyapunovCovariance
import theorem.Stochastic.OUMoments
import theorem.LTI.Oscillator2
import Mathlib.Probability.Moments.Variance

/-! # Linearized stochastic COI swing: stationary covariance, moment equations, lag covariance

Source: work-sync `theory/T-frequency-stability-stochastic.md` §1.3 (linearization (1.5),
`ω_n`, `ζ` (1.6), Lyapunov equation (1.7), closed forms (1.8)–(1.9)), §1.4 (moment equations
(1.11) and their limit), §1.5 (lag covariance of `ω̃` and the windowed ROCOF (1.12)).

Model boundary.  Linearized COI swing around the operating point `(δ*, 0)` (raw rad/s units):
state `x = (δ̃, ω̃)` (index `0` = angle deviation, index `1` = speed deviation), drift matrix
`A = [[0, 1], [−k/M, −D/M]]` with `M = M_COI`, `D = D_COI`, `k = V''(δ*)`, and constant noise
matrix `Σ = [[0, 0], [σ_ω/M, σ_v/M]]` (two independent Wiener channels; the voltage channel is
frozen at the operating point).  Continuous time.  The COI aggregation and the linearization
themselves are taken as given; no PLL, delay, limiter or network detail is modelled.

Scope (Rules §3).  Everything here is a statement about the deterministic moment objects:
the algebraic Lyapunov equation `A P + P Aᵀ + Σ Σᵀ = 0`, the differential Lyapunov equation
`Ṗ = A P + P Aᵀ + Σ Σᵀ`, the mean `e^{tA} m₀` and the lag function `C(τ) = e^{τA} P∞`.
That these are the moments / autocovariance of the Itô solution of (1.5) is **not** proved
(Itô calculus is out of scope); these are foundation results, not stochastic stability theorems.

Main results.
* `swingCov_solves`, `swingCov_unique`: for `M, D, k > 0` the unique solution of (1.7) is
  `p₁₂ = 0`, `p₂₂ = s²/(2MD)`, `p₁₁ = s²/(2Dk)` with `s² = σ_ω² + σ_v²` ((1.8), (1.9));
  `swingCov_angle_eq`: `Var δ̃ = Var ω̃ / ω_n²`.
* `swing_cov_tendsto`, `swing_mean_tendsto`: every solution of the moment ODEs converges to
  `(0, P∞)`.
* The matrix exponential tools `LTI.exp_smul_eq_of_hasDerivAt` (uniqueness of the matrix
  exponential as the solution of `Ė = A E`, `E 0 = 1`) and `LTI.exp_smul_of_sq_eq` (closed form
  when `(A + a I)² = −w² I`) are in `theorem/LTI/Oscillator2.lean`.
* `swing_lagCov_speed`: for the underdamped case `D² < 4Mk`,
  `(e^{τA} P∞)_{ω ω} = Var(ω̃) e^{−ζω_n τ} [cos ω_d τ − (ζω_n/ω_d) sin ω_d τ]`, the boxed formula
  of §1.5 (`ζω_n = D/(2M)`, `ω_d² = k/M − D²/(4M²)`).
* `swing_ouStatVar`, `swing_ouVar_tendsto` (`theory/T-sde-systems.md` §2.2.2): the scalar noisy
  swing `M dΔω = −DΔω dt + β dW` read as an Ornstein–Uhlenbeck process (`θ = D/M`, `σ = β/M`,
  the OU moment functions of `theorem/Stochastic/OUMoments.lean`) has stationary variance
  `β²/(2DM)`, and its variance function tends to it for `D, M > 0`.

Correction (§1.5, eq. (1.12)).  The windowed ROCOF is `(ω(t+Δt) − ω(t))/Δt`, so
`Var(ROCOF) = (2 Var ω̃ − 2 Cov(ω̃(t), ω̃(t+Δt)))/Δt²` (`variance_rocof`,
`variance_rocof_stationary`).  Formula (1.12) carries an extra factor `1/M_COI`; the speed
variance already contains the inertia, so that factor is wrong.
-/

noncomputable section
namespace powerlib.Frequency.FreqCov

open Matrix Filter MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Frobenius Topology
open powerlib.Stochastic.Lyapunov

variable {n : ℕ}

-- Same compatibility instance as `theorem/Stochastic/LyapunovCovariance.lean`.
noncomputable local instance frobeniusENormedAddMonoid'' :
    ENormedAddMonoid (Matrix (Fin n) (Fin n) ℝ) :=
  (NormedAddCommGroup.toENormedAddCommMonoid :
    ENormedAddCommMonoid (Matrix (Fin n) (Fin n) ℝ)).toENormedAddMonoid

/-! ## The linearized model -/

/-- Drift matrix of (1.5), state `(δ̃, ω̃)`. -/
def swingA (M D k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -(k / M), -(D / M)]

/-- Noise matrix of (1.5): columns = (frequency channel, voltage channel). -/
def swingNoise (M sω sv : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; sω / M, sv / M]

/-- Candidate stationary covariance with total noise power `s2 = σ_ω² + σ_v²`. -/
def swingCov (M D k s2 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![s2 / (2 * D * k), 0; 0, s2 / (2 * M * D)]

@[powerlib_foundation] theorem swingNoise_mul_transpose (M sω sv : ℝ) :
    swingNoise M sω sv * (swingNoise M sω sv)ᵀ = !![0, 0; 0, (sω ^ 2 + sv ^ 2) / M ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swingNoise, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `A` is Hurwitz for `M, D, k > 0`. -/
@[powerlib_foundation] theorem swingA_isHurwitz {M D k : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hk : 0 < k) : LinearSystems.IsHurwitz (swingA M D k) := by
  rw [swingA, powerlib.Criteria.isHurwitz_fin_two_of_iff]
  constructor
  · have : 0 < D / M := div_pos hD hM
    linarith
  · have : 0 < k / M := div_pos hk hM
    nlinarith

/-- (1.8)–(1.9) solve the covariance Lyapunov equation (1.7). -/
@[powerlib_foundation] theorem swingCov_solves {M D k : ℝ} (hM : M ≠ 0) (hD : D ≠ 0)
    (hk : k ≠ 0) (sω sv : ℝ) :
    SolvesCovLyapunov (swingA M D k) (swingCov M D k (sω ^ 2 + sv ^ 2))
      (swingNoise M sω sv * (swingNoise M sω sv)ᵀ) := by
  unfold SolvesCovLyapunov
  rw [swingNoise_mul_transpose]
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> simp [swingA, swingCov] <;> field_simp <;> ring

/-- Uniqueness: every solution of (1.7) is the closed form (1.8)–(1.9). -/
@[powerlib_foundation] theorem swingCov_unique {M D k : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hk : 0 < k) (sω sv : ℝ) {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : SolvesCovLyapunov (swingA M D k) P (swingNoise M sω sv * (swingNoise M sω sv)ᵀ)) :
    P = swingCov M D k (sω ^ 2 + sv ^ 2) :=
  solvesCovLyapunov_unique (swingA_isHurwitz hM hD hk) hP
    (swingCov_solves hM.ne' hD.ne' hk.ne' sω sv)

/-- Entries of the stationary covariance: `p₁₂ = 0`, `Var ω̃ = s²/(2MD)`, `Var δ̃ = s²/(2Dk)`. -/
@[powerlib_foundation] theorem swingCov_entries (M D k s2 : ℝ) :
    swingCov M D k s2 0 1 = 0 ∧ swingCov M D k s2 1 0 = 0 ∧
      swingCov M D k s2 1 1 = s2 / (2 * M * D) ∧ swingCov M D k s2 0 0 = s2 / (2 * D * k) := by
  simp [swingCov]

/-- `Var δ̃ = Var ω̃ / ω_n²`, `ω_n² = k/M` ((1.9)). -/
@[powerlib_foundation] theorem swingCov_angle_eq {M D k : ℝ} (hM : M ≠ 0) (hk : k ≠ 0)
    (s2 : ℝ) : swingCov M D k s2 0 0 = swingCov M D k s2 1 1 / (k / M) := by
  simp only [swingCov, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    cons_val_one]
  by_cases hD : D = 0
  · simp [hD]
  field_simp

/-- The stationary covariance is positive definite when the total noise power is positive. -/
@[powerlib_foundation] theorem swingCov_posDef {M D k s2 : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hk : 0 < k) (hs : 0 < s2) : (swingCov M D k s2).PosDef := by
  have h1 : 0 < s2 / (2 * D * k) := by positivity
  have h2 : 0 < s2 / (2 * M * D) := by positivity
  have : swingCov M D k s2 = Matrix.diagonal ![s2 / (2 * D * k), s2 / (2 * M * D)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [swingCov]
  rw [this, Matrix.posDef_diagonal_iff]
  intro i; fin_cases i <;> simp [h1, h2]

/-! ## Moment equations (1.11) and their limits -/

/-- Every solution of the differential Lyapunov equation (1.11) converges entrywise to the
stationary covariance (1.8)–(1.9). -/
@[powerlib_foundation] theorem swing_cov_tendsto {M D k : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hk : 0 < k) (sω sv : ℝ) {P : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hP : ∀ t, HasDerivAt P (swingA M D k * P t + P t * (swingA M D k)ᵀ +
      swingNoise M sω sv * (swingNoise M sω sv)ᵀ) t) (i j : Fin 2) :
    Tendsto (fun t => P t i j) atTop (𝓝 (swingCov M D k (sω ^ 2 + sv ^ 2) i j)) := by
  have hinf := swingCov_solves hM.ne' hD.ne' hk.ne' sω sv
  rw [covODE_unique hinf hP rfl]
  exact covSol_tendsto_entry (swingA_isHurwitz hM hD hk) i j

/-- The mean `e^{tA} m₀` of (1.11) tends to `0`. -/
@[powerlib_foundation] theorem swing_mean_tendsto {M D k : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hk : 0 < k) (m₀ : Fin 2 → ℝ) :
    Tendsto (fun t : ℝ => NormedSpace.exp (t • swingA M D k) *ᵥ m₀) atTop (𝓝 0) := by
  have hE := tendsto_norm_exp_smul_zero (swingA_isHurwitz hM hD hk)
  rw [tendsto_pi_nhds]
  intro i
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [show (0 : ℝ) = ∑ j : Fin 2, 0 * m₀ j by simp]
  refine tendsto_finsetSum _ fun j _ => (Tendsto.mul_const _ ?_)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun t => norm_nonneg _) (fun t => abs_entry_le_norm _ i j) hE

/-! ## Lag covariance of the speed (§1.5) -/

/-- `B = A + (D/2M) I` squares to `−ω_d² I` with `ω_d² = k/M − D²/(4M²)`. -/
@[powerlib_foundation] theorem swingA_shift_sq {M D k : ℝ} (hM : M ≠ 0) :
    (swingA M D k + (D / (2 * M)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        (swingA M D k + (D / (2 * M)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      -(k / M - (D / (2 * M)) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swingA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> field_simp <;> ring

/-- **Speed lag covariance (§1.5, boxed)**, underdamped `D² < 4 M k`:
`(e^{τA} P∞)_{ωω} = Var(ω̃) e^{−aτ} [cos(ω_d τ) − (a/ω_d) sin(ω_d τ)]`, `a = ζω_n = D/(2M)`,
`ω_d = √(k/M − a²)`. -/
@[powerlib_foundation] theorem swing_lagCov_speed {M D k : ℝ} (hM : 0 < M)
    (hund : (D / (2 * M)) ^ 2 < k / M) (s2 τ : ℝ) :
    (NormedSpace.exp (τ • swingA M D k) * swingCov M D k s2) 1 1 =
      swingCov M D k s2 1 1 * (Real.exp (-(D / (2 * M)) * τ) *
        (Real.cos (Real.sqrt (k / M - (D / (2 * M)) ^ 2) * τ) -
          D / (2 * M) / Real.sqrt (k / M - (D / (2 * M)) ^ 2) *
            Real.sin (Real.sqrt (k / M - (D / (2 * M)) ^ 2) * τ))) := by
  set a := D / (2 * M) with ha
  set w := Real.sqrt (k / M - a ^ 2) with hw
  have hpos : 0 < k / M - a ^ 2 := by linarith
  have hw0 : w ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hw2 : w ^ 2 = k / M - a ^ 2 := Real.sq_sqrt hpos.le
  have hB : (swingA M D k + a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      (swingA M D k + a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = -(w ^ 2) • 1 := by
    rw [hw2, ha]; exact swingA_shift_sq hM.ne'
  rw [LTI.exp_smul_of_sq_eq hw0 hB τ, Matrix.mul_apply, Fin.sum_univ_two]
  simp [swingCov, swingA]
  simp only [ha]
  field_simp
  ring

/-- The lag function `C(τ) = e^{τA} P` solves `Ċ = A C`, `C 0 = P` (deterministic part of the
lagged moment equation). -/
@[powerlib_foundation] theorem lagCov_hasDerivAt (A P : Matrix (Fin n) (Fin n) ℝ) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) * P)
      (A * (NormedSpace.exp (τ • A) * P)) τ := by
  have := (hasDerivAt_exp_smul_const' A τ).mul_const P
  convert! this using 1
  exact (Matrix.mul_assoc A _ P).symm

/-! ## Windowed ROCOF (correction to (1.12)) -/

/-- `Var((Y − X)/Δt) = (Var Y − 2 Cov(Y, X) + Var X)/Δt²` for square-integrable `X, Y`. -/
@[powerlib_foundation] theorem variance_rocof {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (Δ : ℝ) :
    Var[fun ω => (Y ω - X ω) / Δ; μ] =
      (Var[Y; μ] - 2 * cov[Y, X; μ] + Var[X; μ]) / Δ ^ 2 := by
  have h : (fun ω => (Y ω - X ω) / Δ) = fun ω => Δ⁻¹ * (Y ω - X ω) := by
    funext ω; ring
  rw [h, variance_const_mul, variance_fun_sub hY hX]
  field_simp

/-- **Correction to (1.12)**: with stationary `Var ω̃(t) = Var ω̃(t+Δt) = v` and lag covariance
`c`, the ROCOF variance is `(2v − 2c)/Δt²`; no `1/M_COI` factor appears. -/
@[powerlib_foundation] theorem variance_rocof_stationary {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {v c Δ : ℝ} (hvX : Var[X; μ] = v) (hvY : Var[Y; μ] = v) (hc : cov[X, Y; μ] = c) :
    Var[fun ω => (Y ω - X ω) / Δ; μ] = (2 * v - 2 * c) / Δ ^ 2 := by
  rw [variance_rocof hX hY, hvX, hvY, covariance_comm, hc]
  ring

/-! ## Noisy swing equation (T-sde-systems §2.2.2) -/

section NoisySwing

open powerlib.Stochastic.OU (ouStatVar ouVar ouVar_tendsto)

/-- Writing `M dΔω = -DΔω dt + β dW` as an OU with `θ = D/M`, `σ = β/M`, the stationary
variance `σ²/(2θ)` equals `β²/(2DM)` (algebraic part only). -/
@[powerlib_foundation] theorem swing_ouStatVar {M D : ℝ} (hM : M ≠ 0) (hD : D ≠ 0) (β : ℝ) :
    ouStatVar (D / M) (β / M) = β ^ 2 / (2 * D * M) := by
  unfold ouStatVar
  field_simp

/-- The variance function of the noisy swing tends to `β²/(2DM)` when `D, M > 0`. -/
@[powerlib_foundation] theorem swing_ouVar_tendsto {M D : ℝ} (hM : 0 < M) (hD : 0 < D) (β : ℝ) :
    Tendsto (ouVar (D / M) (β / M)) atTop (𝓝 (β ^ 2 / (2 * D * M))) := by
  rw [← swing_ouStatVar hM.ne' hD.ne']
  exact ouVar_tendsto (div_pos hD hM) _

end NoisySwing

end powerlib.Frequency.FreqCov
