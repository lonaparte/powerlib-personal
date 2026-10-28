import theorem.GFL.LCLine.Reduction
import theorem.PLL.PIPLL

/-! # Second-order form and closed-form Lyapunov-equation solutions of the linearized GFL-PLL

Foundation module. Everything here is algebra or calculus about the reduced PLL field
`θ̇ = K_p h(θ) + K_i η`, `η̇ = h(θ)` and its linearization. In particular the matrices `covV`,
`covW` below are proved to be the unique solutions of the continuous Lyapunov equation
`A P + P Aᵀ + B Bᵀ = 0`; they are *not* asserted here to be stationary covariances of any
stochastic process (no stochastic model is formalized).

Model boundary.
The reduced PLL field above and its linearization at a stable point. Conventions: the
linearization is written in the project-code convention of
`sn-critical-scaling.md` §2: `A = [[−K_p g, −K_i], [g, 0]]` with `g > 0` at a stable point.
It is the text-convention Jacobian `piPLLJacobian K_p K_i h′` with `h′ = −g`, conjugated by
`diag(1, −1)` (`linA_eq_conj`). Voltage-channel input `B_v = (−K_p σ, σ)ᵀ` (unit intensity,
sensitivity `σ`), frequency-channel input `B_ω = (−1, 0)ᵀ`.

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/sn-critical-scaling.md`
§1–§3.

Results.
* `oscillator_form` (`sn-critical-scaling.md` §1): along any solution,
  `θ̈ − K_p h′(θ) θ̇ − K_i h(θ) = 0`.
* `covV_lyapunov`, `covW_lyapunov`: the closed forms
  `Var(θ)^(v) = σ²(K_i + K_p² g)/(2 K_p g²)`, `Var(η)^(v) = σ²/(2 K_p g)`,
  `Cov^(v) = −σ²/(2g)`, `Var(θ)^(ω) = 1/(2 K_p g)`, `Var(η)^(ω) = 1/(2 K_p K_i)` solve the
  Lyapunov equation; `lyapunov_unique` : the solution is unique whenever `K_p g ≠ 0`, `g ≠ 0`,
  `K_i ≠ 0` (in particular when `A` is Hurwitz, `isHurwitz_linA_iff`).
* `varThetaQ_eq`, `varThetaQ_tendsto` : with the gauge identity `σ_q = g/V_g`
  (`Params.sigma_q_eq`), the q-channel value is `(K_i + K_p² g)/(2 K_p V_g²)`, which has the finite
  limit `K_i/(2 K_p V_g²)` as `g → 0` (saddle-node).

Correction: the note checks the closed forms against a numerical Lyapunov solver and the
gauge identity to `1e−5`; here both are exact.
-/

noncomputable section
namespace powerlib.GFL.Noise
open Real Matrix Filter Topology
open powerlib.PLL
open powerlib.GFL.LCLine

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

/-- Linearization in the code convention, `A = [[−K_p g, −K_i], [g, 0]]`. -/
def linA (Kp Ki g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-(Kp * g), -Ki; g, 0]

/-- `diag(1, −1)`. -/
def flipEta : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The code-convention linearization is the text-convention Jacobian with `h′ = −g`,
conjugated by `diag(1, −1)` (the sign of `η`). -/
@[powerlib_foundation] theorem linA_eq_conj (Kp Ki g : ℝ) :
    linA Kp Ki g = flipEta * piPLLJacobian Kp Ki (-g) * flipEta := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [linA, flipEta, piPLLJacobian, Matrix.mul_apply, Fin.sum_univ_two]

@[powerlib_foundation] theorem isHurwitz_linA_iff (Kp Ki g : ℝ) :
    LinearSystems.IsHurwitz (linA Kp Ki g) ↔ 0 < Kp * g ∧ 0 < Ki * g := by
  rw [linA, Criteria.isHurwitz_fin_two_of_iff]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- Voltage-channel input `B_v = (−K_p σ, σ)ᵀ`. -/
def portV (Kp σ : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![-(Kp * σ); σ]

/-- Frequency-channel input `B_ω = (−1, 0)ᵀ`. -/
def portW : Matrix (Fin 2) (Fin 1) ℝ := !![-1; 0]

/-- Closed-form solution for the voltage channel. -/
def covV (Kp Ki g σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ ^ 2 * (Ki + Kp ^ 2 * g) / (2 * Kp * g ^ 2), -(σ ^ 2 / (2 * g));
     -(σ ^ 2 / (2 * g)), σ ^ 2 / (2 * Kp * g)]

/-- Closed-form solution for the frequency channel. -/
def covW (Kp Ki g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / (2 * Kp * g), 0; 0, 1 / (2 * Kp * Ki)]

/-- `covV` solves `A P + P Aᵀ + B_v B_vᵀ = 0`. -/
@[powerlib_foundation] theorem covV_lyapunov {Kp Ki g : ℝ} (hKp : Kp ≠ 0) (hg : g ≠ 0) (σ : ℝ) :
    linA Kp Ki g * covV Kp Ki g σ + covV Kp Ki g σ * (linA Kp Ki g)ᵀ +
      portV Kp σ * (portV Kp σ)ᵀ = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.transpose_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> simp [linA, covV, portV] <;> field_simp <;> ring

/-- `covW` solves `A P + P Aᵀ + B_ω B_ωᵀ = 0`. -/
@[powerlib_foundation] theorem covW_lyapunov {Kp Ki g : ℝ} (hKp : Kp ≠ 0) (hKi : Ki ≠ 0)
    (hg : g ≠ 0) :
    linA Kp Ki g * covW Kp Ki g + covW Kp Ki g * (linA Kp Ki g)ᵀ + portW * portWᵀ = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.transpose_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> simp [linA, covW, portW] <;> field_simp <;> ring

/-- Uniqueness: the Lyapunov operator `X ↦ A X + X Aᵀ` is injective when `K_p g ≠ 0`, `g ≠ 0`,
`K_i ≠ 0`. -/
@[powerlib_foundation] theorem lyapunov_unique {Kp Ki g : ℝ} (hKpg : Kp * g ≠ 0) (hg : g ≠ 0)
    (hKi : Ki ≠ 0) {Q X Y : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : linA Kp Ki g * X + X * (linA Kp Ki g)ᵀ + Q = 0)
    (hY : linA Kp Ki g * Y + Y * (linA Kp Ki g)ᵀ + Q = 0) : X = Y := by
  have e : ∀ i j, (linA Kp Ki g * X + X * (linA Kp Ki g)ᵀ + Q) i j -
      (linA Kp Ki g * Y + Y * (linA Kp Ki g)ᵀ + Q) i j = 0 := by
    intro i j; rw [hX, hY]; simp
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    at e00 e01 e10 e11
  simp [linA] at e00 e01 e10 e11
  -- unknowns d_ij = X_ij − Y_ij
  have s11 : (X 0 1 - Y 0 1) + (X 1 0 - Y 1 0) = 0 := by
    have : g * ((X 0 1 - Y 0 1) + (X 1 0 - Y 1 0)) = 0 := by linear_combination e11
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hg
    · exact h
  have d00 : X 0 0 - Y 0 0 = 0 := by
    have : (Kp * g) * (X 0 0 - Y 0 0) = 0 := by linear_combination -e00 / 2 - Ki * s11 / 2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hKpg
    · exact h
  have d01 : X 0 1 - Y 0 1 = X 1 0 - Y 1 0 := by
    have : (Kp * g) * ((X 0 1 - Y 0 1) - (X 1 0 - Y 1 0)) = 0 := by
      linear_combination e10 - e01
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hKpg
    · linarith
  have hz01 : X 0 1 - Y 0 1 = 0 := by linarith
  have d11 : X 1 1 - Y 1 1 = 0 := by
    have : Ki * (X 1 1 - Y 1 1) = 0 := by
      linear_combination -e01 + g * d00 - Kp * g * hz01
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hKi
    · exact h
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- The Lyapunov equation of the voltage channel has the unique solution `covV`. -/
@[powerlib_foundation] theorem covV_unique {Kp Ki g σ : ℝ} (hKp : Kp ≠ 0) (hg : g ≠ 0)
    (hKi : Ki ≠ 0) {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : linA Kp Ki g * P + P * (linA Kp Ki g)ᵀ + portV Kp σ * (portV Kp σ)ᵀ = 0) :
    P = covV Kp Ki g σ :=
  lyapunov_unique (mul_ne_zero hKp hg) hg hKi hP (covV_lyapunov hKp hg σ)

/-- The Lyapunov equation of the frequency channel has the unique solution `covW`. -/
@[powerlib_foundation] theorem covW_unique {Kp Ki g : ℝ} (hKp : Kp ≠ 0) (hg : g ≠ 0)
    (hKi : Ki ≠ 0) {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : linA Kp Ki g * P + P * (linA Kp Ki g)ᵀ + portW * portWᵀ = 0) :
    P = covW Kp Ki g :=
  lyapunov_unique (mul_ne_zero hKp hg) hg hKi hP (covW_lyapunov hKp hKi hg)

/-- q-channel: with `σ_q = g/V_g`, `Var(θ)^(q) = (K_i + K_p² g)/(2 K_p V_g²)`. -/
@[powerlib_foundation] theorem varThetaQ_eq {Kp Ki g Vg : ℝ} (hKp : Kp ≠ 0) (hg : g ≠ 0)
    (hVg : Vg ≠ 0) : covV Kp Ki g (g / Vg) 0 0 = (Ki + Kp ^ 2 * g) / (2 * Kp * Vg ^ 2) := by
  simp [covV]
  field_simp

/-- The q-channel value stays finite at the saddle-node: it tends to `K_i/(2 K_p V_g²)` as
`g → 0`. -/
@[powerlib_foundation] theorem varThetaQ_tendsto {Kp Ki Vg : ℝ} (hKp : Kp ≠ 0) (hVg : Vg ≠ 0) :
    Tendsto (fun g => covV Kp Ki g (g / Vg) 0 0) (𝓝[≠] 0) (𝓝 (Ki / (2 * Kp * Vg ^ 2))) := by
  have hc : Tendsto (fun g : ℝ => (Ki + Kp ^ 2 * g) / (2 * Kp * Vg ^ 2)) (𝓝 0)
      (𝓝 (Ki / (2 * Kp * Vg ^ 2))) := by
    have : Continuous (fun g : ℝ => (Ki + Kp ^ 2 * g) / (2 * Kp * Vg ^ 2)) := by fun_prop
    simpa using this.tendsto 0
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with g hg
  exact (varThetaQ_eq hKp hg hVg).symm

/-- The integrator variance of the frequency channel does not depend on the operating point. -/
@[powerlib_foundation] theorem varEtaW_eq (Kp Ki g : ℝ) : covW Kp Ki g 1 1 = 1 / (2 * Kp * Ki) := by
  simp [covW]

/-- The model's q-axis EMF sensitivity is `σ_q = g/V_g` with `g = −h′(θ)` (gauge identity), so the
q-channel value at an equilibrium of the model is `(K_i + K_p² g)/(2 K_p V_g²)`. -/
@[powerlib_foundation] theorem Params.varThetaQ_model (p : Params) (hwC : p.wC ≠ 0)
    (hΔ : p.Δ ≠ 0) (hVg : p.Vg ≠ 0) (hKp : p.Kp ≠ 0) (θ : ℝ) (hg : deriv p.h θ ≠ 0) :
    HasDerivAt (fun Eq => p.hE θ p.Vg Eq) (-deriv p.h θ / p.Vg) 0 ∧
      covV p.Kp p.Ki (-deriv p.h θ) (-deriv p.h θ / p.Vg) 0 0 =
        (p.Ki + p.Kp ^ 2 * (-deriv p.h θ)) / (2 * p.Kp * p.Vg ^ 2) :=
  ⟨p.sigma_q_eq hwC hΔ hVg θ, varThetaQ_eq hKp (neg_ne_zero.mpr hg) hVg⟩

end powerlib.GFL.Noise
