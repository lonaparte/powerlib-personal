import theorem.GFL.PIPLL

/-! # PI-PLL with a biased sinusoidal phase detector `h(θ) = −V sin θ + μ`

Model boundary (domain module).
* System: the general PI-PLL of `theorem/GFL/PIPLL.lean` (state `(θ, η)` in this order,
  `θ̇ = K_p h(θ) + K_i η − δω`, `η̇ = h(θ)`, constant `δω`) with the phase-detector
  characteristic of the "simple pendulum" model of T-pll-dynamics §1.13.2,
  `h(θ) = −V sin θ + μ` (`biasedPD V μ`), `V > 0`; `μ` is a constant bias of the phase
  detector (small-signal frequency/offset bias in the note). Continuous time, autonomous; no
  pre-filter, delay, PWM, current loop or saturation. All equilibrium and stability results are
  instantiations of `theorem/GFL/PIPLL.lean`.
* Level: equilibrium set and local behaviour at equilibria (linearization).

Results (T-pll-dynamics §1.13.2).
* `|μ| > V`: no equilibrium at all (frequency-drift / loss of lock).
* `|μ| < V`: in every period window `[−π/2, 3π/2)` the zeros of `h` are exactly
  `θ₁ = arcsin(μ/V)` and `θ₂ = π − arcsin(μ/V)`, `θ₁ ≠ θ₂`; with `K_p, K_i > 0` the
  equilibrium `(θ₁, δω/K_i)` is locally exponentially stable and `(θ₂, δω/K_i)` is unstable
  (saddle): exactly one stable and one saddle per period.
* `|μ| = V` (fold): `θ* = ±π/2` is a double zero (`h' = 0`) and the Jacobian at the
  equilibrium is a nonzero nilpotent matrix (non-hyperbolic).

Source: work-sync `theory/T-pll-dynamics.md` §1.13.2.
-/

noncomputable section
namespace powerlib.PLL
open powerlib.Dynamics (State)
open powerlib.GFL (piPLLField piPLLState)

/-- Biased sinusoidal phase detector `h(θ) = −V sin θ + μ`. -/
def biasedPD (V μ θ : ℝ) : ℝ := -(V * Real.sin θ) + μ

@[powerlib_foundation] theorem hasDerivAt_biasedPD (V μ θ : ℝ) :
    HasDerivAt (biasedPD V μ) (-(V * Real.cos θ)) θ := by
  have := (((Real.hasDerivAt_sin θ).const_mul V).neg).add_const μ
  exact this

@[powerlib_foundation] theorem contDiff_biasedPD (V μ : ℝ) : ContDiff ℝ 1 (biasedPD V μ) :=
  ((contDiff_const.mul Real.contDiff_sin).neg).add contDiff_const

/-- `|μ| > V ≥ 0`: the biased PLL has no equilibrium. -/
@[powerlib_domain] theorem biased_no_equilibrium {V μ : ℝ} (hV : 0 ≤ V) (hμ : V < |μ|)
    (Kp Ki δω : ℝ) (x : State 2) : piPLLField (biasedPD V μ) Kp Ki δω x ≠ 0 := by
  intro h
  have h1 : biasedPD V μ (x 0) = 0 := by
    have := congrArg (fun y : State 2 => y 1) h
    simpa using this
  have hs : |V * Real.sin (x 0)| ≤ V := by
    rw [abs_mul, abs_of_nonneg hV]
    exact mul_le_of_le_one_right hV (Real.abs_sin_le_one _)
  have : μ = V * Real.sin (x 0) := by simp only [biasedPD] at h1; linarith
  rw [this] at hμ
  linarith

/-- `|μ| < V`: in the window `[−π/2, 3π/2)` the zeros of `h` are exactly
`arcsin(μ/V)` and `π − arcsin(μ/V)`, and they are distinct. -/
@[powerlib_foundation] theorem biasedPD_zeros {V μ : ℝ} (hV : 0 < V) (hμ : |μ| < V) :
    {θ | θ ∈ Set.Ico (-(Real.pi / 2)) (3 * Real.pi / 2) ∧ biasedPD V μ θ = 0} =
      {Real.arcsin (μ / V), Real.pi - Real.arcsin (μ / V)} ∧
      Real.arcsin (μ / V) ≠ Real.pi - Real.arcsin (μ / V) := by
  have hx : |μ / V| < 1 := by rw [abs_div, abs_of_pos hV, div_lt_one hV]; exact hμ
  have hx' := abs_lt.mp hx
  have hlo := Real.neg_pi_div_two_lt_arcsin.mpr hx'.1
  have hhi := Real.arcsin_lt_pi_div_two.mpr hx'.2
  have hsin : Real.sin (Real.arcsin (μ / V)) = μ / V := Real.sin_arcsin hx'.1.le hx'.2.le
  have hzero : ∀ θ, biasedPD V μ θ = 0 ↔ Real.sin θ = μ / V := by
    intro θ
    simp only [biasedPD]
    constructor
    · intro h; field_simp; linarith
    · intro h; rw [h]; field_simp; ring
  refine ⟨?_, by intro h; linarith⟩
  ext θ
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Ico, hzero]
  constructor
  · rintro ⟨⟨h1, h2⟩, hs⟩
    by_cases hθ : θ ≤ Real.pi / 2
    · left
      rw [← hs, Real.arcsin_sin h1 hθ]
    · right
      have h3 : Real.sin (Real.pi - θ) = μ / V := by rw [Real.sin_pi_sub, hs]
      have := Real.arcsin_sin (x := Real.pi - θ) (by linarith) (by linarith)
      rw [h3] at this
      linarith
  · rintro (rfl | rfl)
    · exact ⟨⟨hlo.le, by linarith [Real.pi_pos]⟩, hsin⟩
    · exact ⟨⟨by linarith, by linarith [Real.pi_pos]⟩, by rw [Real.sin_pi_sub, hsin]⟩

/-- `|μ| < V`, `K_p, K_i > 0`: the equilibrium at `θ₁ = arcsin(μ/V)` is locally
exponentially stable. -/
@[powerlib_domain] theorem biased_locallyExponentiallyStable {V μ Kp Ki : ℝ} (hV : 0 < V)
    (hμ : |μ| < V) (hKp : 0 < Kp) (hKi : 0 < Ki) (δω : ℝ) :
    Dynamics.LocallyExponentiallyStable (piPLLField (biasedPD V μ) Kp Ki δω)
      (piPLLState (Real.arcsin (μ / V)) (δω / Ki)) := by
  have hx : |μ / V| < 1 := by rw [abs_div, abs_of_pos hV, div_lt_one hV]; exact hμ
  have hx' := abs_lt.mp hx
  have hcos : 0 < Real.cos (Real.arcsin (μ / V)) := by
    rw [Real.cos_arcsin]; apply Real.sqrt_pos.mpr; nlinarith
  refine GFL.piPLL_locallyExponentiallyStable (contDiff_biasedPD V μ) ?_
    (hasDerivAt_biasedPD V μ _) (by nlinarith) hKp hKi
  rw [biasedPD, Real.sin_arcsin hx'.1.le hx'.2.le]; field_simp; ring

/-- `|μ| < V`, `K_i > 0`: the equilibrium at `θ₂ = π − arcsin(μ/V)` is unstable (saddle). -/
@[powerlib_domain] theorem biased_unstable {V μ Kp Ki : ℝ} (hV : 0 < V) (hμ : |μ| < V)
    (hKi : 0 < Ki) (δω : ℝ) :
    Dynamics.Unstable (piPLLField (biasedPD V μ) Kp Ki δω)
      (piPLLState (Real.pi - Real.arcsin (μ / V)) (δω / Ki)) := by
  have hx : |μ / V| < 1 := by rw [abs_div, abs_of_pos hV, div_lt_one hV]; exact hμ
  have hx' := abs_lt.mp hx
  have hcos : 0 < Real.cos (Real.arcsin (μ / V)) := by
    rw [Real.cos_arcsin]; apply Real.sqrt_pos.mpr; nlinarith
  refine GFL.piPLL_unstable (contDiff_biasedPD V μ) ?_ (hasDerivAt_biasedPD V μ _) ?_ hKi
  · rw [biasedPD, Real.sin_pi_sub, Real.sin_arcsin hx'.1.le hx'.2.le]; field_simp; ring
  · rw [Real.cos_pi_sub]; nlinarith

/-- Fold `μ = V` (`V ≠ 0`, `K_i ≠ 0`): `θ* = π/2` is an equilibrium with `h'(θ*) = 0`, and the
Jacobian there is the nonzero nilpotent matrix `[[0, K_i], [0, 0]]` (non-hyperbolic). The case
`μ = −V` is symmetric (`θ* = −π/2`). -/
@[powerlib_domain] theorem biased_fold {V Kp Ki : ℝ} (hKi : Ki ≠ 0) (δω : ℝ) :
    piPLLField (biasedPD V V) Kp Ki δω (piPLLState (Real.pi / 2) (δω / Ki)) = 0 ∧
      fderiv ℝ (piPLLField (biasedPD V V) Kp Ki δω) (piPLLState (Real.pi / 2) (δω / Ki)) =
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (GFL.piPLLJacobian Kp Ki 0) ∧
      GFL.piPLLJacobian Kp Ki 0 ≠ 0 ∧ (GFL.piPLLJacobian Kp Ki 0) ^ 2 = 0 ∧
      ¬ LinearSystems.IsHurwitz (GFL.piPLLJacobian Kp Ki 0) := by
  have hd := hasDerivAt_biasedPD V V (Real.pi / 2)
  rw [Real.cos_pi_div_two, mul_zero, neg_zero] at hd
  exact GFL.piPLL_jacobian_nilpotent_of_deriv_zero (by simp [biasedPD]) hd hKi

end powerlib.PLL
