import theorem.GridTiedConverter.GFL.LCLine.Reduction
import theorem.GridTiedConverter.PLL.PIPLLPH
import theorem.Dynamics.Transport
import theorem.Stochastic.LyapunovCovariance

/-! # Second-order form and closed-form Lyapunov-equation solutions of the linearized GFL-PLL

Domain module. Everything here is algebra or calculus about the reduced PLL field
`θ̇ = K_p h(θ) + K_i η`, `η̇ = h(θ)` and its linearization. In particular the matrices `covV`,
`covW` below are proved to be the unique solutions of the continuous Lyapunov equation
`A P + P Aᵀ + B Bᵀ = 0`; they are *not* asserted here to be stationary covariances of any
stochastic process (no stochastic model is formalized).

Model boundary.
The reduced PLL field above and its linearization at a stable point. Conventions: the
linearization is written in the project-code convention of
`sn-critical-scaling.md` §2: `A = [[−K_p g, −K_i], [g, 0]]` with `g > 0` at a stable point.
It is the text-convention Jacobian `piPLLJacobian K_p K_i h′` with `h′ = −g`, conjugated by
`diag(1, −1)` (`linA`, by definition; so it is Hurwitz iff `0 < K_p g ∧ 0 < K_i g`,
`PLL.piPLLJacobian_isHurwitz_iff` through `Linear.isHurwitz_conj`). Voltage-channel input
`B_v = (−K_p σ, σ)ᵀ` (unit intensity, sensitivity `σ`), frequency-channel input
`B_ω = (−1, 0)ᵀ`, the PLL input port `PLL.pllB` (`theorem/GridTiedConverter/PLL/PIPLLPH.lean`;
its `θ` row is unchanged by the sign of `η`).

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/sn-critical-scaling.md`
§1–§3.

Results.
* `oscillator_form` (`sn-critical-scaling.md` §1): along any solution,
  `θ̈ − K_p h′(θ) θ̇ − K_i h(θ) = 0`.
* `covV_lyapunov`, `covW_lyapunov`: the closed forms
  `Var(θ)^(v) = σ²(K_i + K_p² g)/(2 K_p g²)`, `Var(η)^(v) = σ²/(2 K_p g)`,
  `Cov^(v) = −σ²/(2g)`, `Var(θ)^(ω) = 1/(2 K_p g)`, `Var(η)^(ω) = 1/(2 K_p K_i)` solve the
  Lyapunov equation; `covV_unique`, `covW_unique` : the solution is unique whenever `K_p ≠ 0`,
  `g ≠ 0`, `K_i ≠ 0` (in particular when `A` is Hurwitz): then
  `tr A ≠ 0`, `det A ≠ 0` and the generic `Stochastic.Lyapunov.solvesCovLyapunov_unique_fin_two`
  applies (`theorem/Stochastic/LyapunovCovariance.lean`).
* `varThetaQ_eq`, `varThetaQ_tendsto` : with the gauge identity `σ_q = g/V_g`
  (`Network.sigma_q_eq`), the q-channel value is `(K_i + K_p² g)/(2 K_p V_g²)`, which has the finite
  limit `K_i/(2 K_p V_g²)` as `g → 0` (saddle-node).

Correction: the note checks the closed forms against a numerical Lyapunov solver and the
gauge identity to `1e−5`; here both are exact.
-/

noncomputable section
namespace powerlib.GFL.Noise
open Real Matrix Filter Topology
open powerlib.PLL
open powerlib.GFL.LCLine
open powerlib.NormalForm.BogdanovTakens (proportionalMatrix trace_proportionalMatrix
  det_proportionalMatrix)

/-- Second-order oscillator form of the reduced PLL: if `θ̇ = K_p h(θ) + K_i η` and `η̇ = h(θ)`
everywhere, then `θ̈ = K_p h′(θ) θ̇ + K_i h(θ)`. -/
@[tmio T, powerlib_foundation] theorem oscillator_form {h h' : ℝ → ℝ} {Kp Ki : ℝ} {θ η : ℝ → ℝ}
    (hh : ∀ x, HasDerivAt h (h' x) x)
    (hθ : ∀ s, HasDerivAt θ (Kp * h (θ s) + Ki * η s) s)
    (hη : ∀ s, HasDerivAt η (h (θ s)) s) (t : ℝ) :
    HasDerivAt (deriv θ) (Kp * h' (θ t) * deriv θ t + Ki * h (θ t)) t := by
  have hd : deriv θ = fun s => Kp * h (θ s) + Ki * η s := funext fun s => (hθ s).deriv
  have h1 := (((hh (θ t)).comp t (hθ t)).const_mul Kp).add ((hη t).const_mul Ki)
  rw [hd]
  convert h1 using 1
  · funext s; simp
  · show Kp * h' (θ t) * (Kp * h (θ t) + Ki * η t) + Ki * h (θ t) = _
    ring

/-- `diag(1, −1)`. -/
abbrev flipEta : Matrix (Fin 2) (Fin 2) ℝ := Dynamics.signMatrix ![1, -1]

/-- Linearization in the code convention, `A = [[−K_p g, −K_i], [g, 0]]`: the text-convention
PI-PLL Jacobian `piPLLJacobian K_p K_i h′` with `h′ = −g`, conjugated by `diag(1, −1)` (the sign
of `η`). -/
abbrev linA (Kp Ki g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  flipEta * piPLLJacobian Kp Ki (-g) * flipEta

/-- Voltage-channel input `B_v = (−K_p σ, σ)ᵀ`. -/
def portV (Kp σ : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![-(Kp * σ); σ]

/-- Closed-form solution for the voltage channel. -/
def covV (Kp Ki g σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ ^ 2 * (Ki + Kp ^ 2 * g) / (2 * Kp * g ^ 2), -(σ ^ 2 / (2 * g));
     -(σ ^ 2 / (2 * g)), σ ^ 2 / (2 * Kp * g)]

/-- Closed-form solution for the frequency channel. -/
def covW (Kp Ki g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / (2 * Kp * g), 0; 0, 1 / (2 * Kp * Ki)]

/-- `covV` solves `A P + P Aᵀ + B_v B_vᵀ = 0`. -/
@[tmio M, powerlib_domain] theorem covV_lyapunov {Kp Ki g : ℝ} (hKp : Kp ≠ 0) (hg : g ≠ 0) (σ : ℝ) :
    linA Kp Ki g * covV Kp Ki g σ + covV Kp Ki g σ * (linA Kp Ki g)ᵀ +
      portV Kp σ * (portV Kp σ)ᵀ = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.transpose_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> simp [Dynamics.signMatrix, proportionalMatrix, covV, portV] <;>
    field_simp <;> ring

/-- `covW` solves `A P + P Aᵀ + B_ω B_ωᵀ = 0`. -/
@[tmio M, powerlib_domain] theorem covW_lyapunov {Kp Ki g : ℝ} (hKp : Kp ≠ 0) (hKi : Ki ≠ 0)
    (hg : g ≠ 0) :
    linA Kp Ki g * covW Kp Ki g + covW Kp Ki g * (linA Kp Ki g)ᵀ + pllB * pllBᵀ = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.transpose_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> simp [Dynamics.signMatrix, proportionalMatrix, covW, pllB] <;>
    field_simp <;> ring

/-- `tr A = −K_p g ≠ 0` and `det A = K_i g ≠ 0`: the Lyapunov operator of `A` is injective
(`Stochastic.Lyapunov.eq_zero_of_lyapunovOp_fin_two`). -/
@[tmio M, powerlib_domain] private lemma linA_trace_det {Kp Ki g : ℝ} (hKp : Kp ≠ 0) (hg : g ≠ 0)
    (hKi : Ki ≠ 0) : (linA Kp Ki g).trace ≠ 0 ∧ (linA Kp Ki g).det ≠ 0 := by
  have h := Dynamics.signMatrix_mul_self ![1, -1]
  rw [linA, Matrix.trace_mul_cycle, h, one_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
    ← Matrix.det_mul, h, Matrix.det_one, one_mul, trace_proportionalMatrix, det_proportionalMatrix]
  simp [hKp, hg, hKi]

/-- The Lyapunov equation of the voltage channel has the unique solution `covV`. -/
@[tmio M, powerlib_domain] theorem covV_unique {Kp Ki g σ : ℝ} (hKp : Kp ≠ 0) (hg : g ≠ 0)
    (hKi : Ki ≠ 0) {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : linA Kp Ki g * P + P * (linA Kp Ki g)ᵀ + portV Kp σ * (portV Kp σ)ᵀ = 0) :
    P = covV Kp Ki g σ :=
  Stochastic.Lyapunov.solvesCovLyapunov_unique_fin_two (linA_trace_det hKp hg hKi).1
    (linA_trace_det hKp hg hKi).2 hP (covV_lyapunov hKp hg σ)

/-- The Lyapunov equation of the frequency channel has the unique solution `covW`. -/
@[tmio M, powerlib_domain] theorem covW_unique {Kp Ki g : ℝ} (hKp : Kp ≠ 0) (hg : g ≠ 0)
    (hKi : Ki ≠ 0) {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : linA Kp Ki g * P + P * (linA Kp Ki g)ᵀ + pllB * pllBᵀ = 0) :
    P = covW Kp Ki g :=
  Stochastic.Lyapunov.solvesCovLyapunov_unique_fin_two (linA_trace_det hKp hg hKi).1
    (linA_trace_det hKp hg hKi).2 hP (covW_lyapunov hKp hKi hg)

/-- q-channel: with `σ_q = g/V_g`, `Var(θ)^(q) = (K_i + K_p² g)/(2 K_p V_g²)`. -/
@[tmio M, powerlib_domain] theorem varThetaQ_eq {Kp Ki g Vg : ℝ} (hKp : Kp ≠ 0) (hg : g ≠ 0)
    (hVg : Vg ≠ 0) : covV Kp Ki g (g / Vg) 0 0 = (Ki + Kp ^ 2 * g) / (2 * Kp * Vg ^ 2) := by
  simp [covV]
  field_simp

/-- The q-channel value stays finite at the saddle-node: it tends to `K_i/(2 K_p V_g²)` as
`g → 0`. -/
@[tmio M, powerlib_domain] theorem varThetaQ_tendsto {Kp Ki Vg : ℝ} (hKp : Kp ≠ 0) (hVg : Vg ≠ 0) :
    Tendsto (fun g => covV Kp Ki g (g / Vg) 0 0) (𝓝[≠] 0) (𝓝 (Ki / (2 * Kp * Vg ^ 2))) := by
  have hc : Tendsto (fun g : ℝ => (Ki + Kp ^ 2 * g) / (2 * Kp * Vg ^ 2)) (𝓝 0)
      (𝓝 (Ki / (2 * Kp * Vg ^ 2))) := by
    have : Continuous (fun g : ℝ => (Ki + Kp ^ 2 * g) / (2 * Kp * Vg ^ 2)) := by fun_prop
    simpa using this.tendsto 0
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with g hg
  exact (varThetaQ_eq hKp hg hVg).symm

/-- The integrator variance of the frequency channel does not depend on the operating point. -/
@[tmio M, powerlib_domain] theorem varEtaW_eq (Kp Ki g : ℝ) : covW Kp Ki g 1 1 = 1 /
    (2 * Kp * Ki) := by
  simp [covW]

end powerlib.GFL.Noise
