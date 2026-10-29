import theorem.PLL.PIPLLFamily
import theorem.SpecialFunctions.Sinusoid

/-! # PI-PLL with a biased sinusoidal phase detector `h(θ) = −V sin θ + μ`

Model boundary.
* System: the general PI-PLL of `theorem/PLL/PIPLL.lean` (state `(θ, η)` in this order,
  `θ̇ = K_p h(θ) + K_i η − δω`, `η̇ = h(θ)`, constant `δω`) with the phase-detector
  characteristic of the "simple pendulum" model of T-pll-dynamics §1.13.2,
  `h(θ) = −V sin θ + μ` (`biasedPD V μ`), `V > 0`; `μ` is a constant bias of the phase
  detector (small-signal frequency/offset bias in the note). Continuous time, autonomous; no
  pre-filter, delay, PWM, current loop or saturation. All equilibrium and stability results are
  instantiations of `theorem/PLL/PIPLL.lean` and of the PI-PLL family
  (`theorem/PLL/PIPLLFamily.lean`).
* Level: equilibrium set and local behaviour at equilibria (linearization).

Source: work-sync `theory/T-pll-dynamics.md` §1.13.2.

Results.
* `|μ| > V`: no equilibrium at all (frequency-drift / loss of lock).
* `|μ| < V`: in every period window `[−π/2, 3π/2)` the zeros of `h` are exactly
  `θ₁ = arcsin(μ/V)` and `θ₂ = π − arcsin(μ/V)`, `θ₁ ≠ θ₂`; with `K_p, K_i > 0` the
  equilibrium `(θ₁, δω/K_i)` is locally exponentially stable and `(θ₂, δω/K_i)` is unstable
  (saddle): exactly one stable and one saddle per period.
* `|μ| = V` (fold): `θ* = ±π/2` is a double zero (`h' = 0`) and the Jacobian at the
  equilibrium is a nonzero nilpotent matrix (non-hyperbolic).

Family and connection conclusions.
No new family: the biased PLL is the member
`biasedModel V μ K_p K_i δω θ*` of the PI-PLL family `PLL.PIPLL.family`, whose system map reads
the field translated so that the selected point `(θ*, δω / K_i)` is the origin. The stable and
saddle equilibria are connection statements on that family's semantics connection
(`biased_mem_den_locallyExponentiallyStable`, `biased_mem_den_unstable`); loss of lock for
`|μ| > V` is stated on its requirement connection (`biased_not_phaseLocked`). The absence of
equilibria (`biased_no_equilibrium`), the zero set of `h` (`biasedPD_zeros`) and the fold
Jacobian (`biased_fold`) are static evidence on the model, not connection conclusions.
-/

noncomputable section
namespace powerlib.PLL
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Biased sinusoidal phase detector `h(θ) = −V sin θ + μ`. -/
def biasedPD (V μ θ : ℝ) : ℝ := -(V * Real.sin θ) + μ

@[tmio M, powerlib_foundation] theorem hasDerivAt_biasedPD (V μ θ : ℝ) :
    HasDerivAt (biasedPD V μ) (-(V * Real.cos θ)) θ := by
  have := (((Real.hasDerivAt_sin θ).const_mul V).neg).add_const μ
  exact this

@[powerlib_foundation] theorem contDiff_biasedPD (V μ : ℝ) : ContDiff ℝ 1 (biasedPD V μ) :=
  ((contDiff_const.mul Real.contDiff_sin).neg).add contDiff_const

/-- `|μ| > V ≥ 0`: the biased PLL has no equilibrium.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem biased_no_equilibrium {V μ : ℝ} (hV : 0 ≤ V) (hμ : V < |μ|)
    (Kp Ki δω : ℝ) (x : ℝ²) : piPLLField (biasedPD V μ) Kp Ki δω x ≠ 0 := by
  intro h
  have h1 : biasedPD V μ (x 0) = 0 := by
    have := congrArg (fun y : ℝ² => y 1) h
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

/-- The PI-PLL model with the biased detector, read about the selected phase `θ*`
(selected point `(θ*, δω / K_i)`). -/
def biasedModel (V μ Kp Ki δω θ : ℝ) : PIPLL.Model :=
  ⟨biasedPD V μ, Kp, Ki, δω, θ, contDiff_biasedPD V μ⟩

@[powerlib_foundation] theorem biasedModel_deriv (V μ Kp Ki δω θ : ℝ) :
    deriv (biasedModel V μ Kp Ki δω θ).h (biasedModel V μ Kp Ki δω θ).θ =
      -(V * Real.cos θ) :=
  (hasDerivAt_biasedPD V μ θ).deriv

/-- `|μ| < V`, `K_p, K_i > 0`: the equilibrium at `θ₁ = arcsin(μ/V)` is locally
exponentially stable, for every constant frequency offset `δω`. -/
@[tmio TM, powerlib_domain] theorem biased_mem_den_locallyExponentiallyStable {V μ Kp Ki : ℝ}
    (hV : 0 < V) (hμ : |μ| < V) (hKp : 0 < Kp) (hKi : 0 < Ki) (δω : ℝ) :
    connection% (biasedModel V μ Kp Ki δω (Real.arcsin (μ / V)) ∈
      PIPLL.family.den (.flow .locallyExponentiallyStable)) := by
  have hcos := SpecialFunctions.cos_arcsin_div_pos hμ hV
  refine PIPLL.mem_den_locallyExponentiallyStable_of_pos _ hKp hKi ?_ ?_
  · change biasedPD V μ (Real.arcsin (μ / V)) = 0
    rw [biasedPD, SpecialFunctions.mul_sin_arcsin_div hμ.le hV, neg_add_cancel]
  · rw [biasedModel_deriv]; nlinarith

/-- `|μ| < V`, `K_i > 0`: the equilibrium at `θ₂ = π − arcsin(μ/V)` is unstable (saddle), for
every `K_p` and every constant frequency offset `δω`. -/
@[tmio TM, powerlib_domain] theorem biased_mem_den_unstable {V μ Kp Ki : ℝ} (hV : 0 < V) (hμ : |μ| < V)
    (hKi : 0 < Ki) (δω : ℝ) :
    connection% (biasedModel V μ Kp Ki δω (Real.pi - Real.arcsin (μ / V)) ∈
      PIPLL.family.den (.flow .unstable)) := by
  have hcos := SpecialFunctions.cos_pi_sub_arcsin_div_neg hμ hV
  refine PIPLL.mem_den_unstable_of_pos _ hKi ?_ ?_
  · change biasedPD V μ (Real.pi - Real.arcsin (μ / V)) = 0
    rw [biasedPD, SpecialFunctions.mul_sin_pi_sub_arcsin_div hμ.le hV, neg_add_cancel]
  · rw [biasedModel_deriv]; nlinarith

/-- `|μ| > V ≥ 0`: loss of lock on the requirement connection — no selected phase of the biased
PLL meets the phase-locking requirement of the PI-PLL family. -/
@[tmio M, powerlib_domain] theorem biased_not_phaseLocked {V μ : ℝ} (hV : 0 ≤ V) (hμ : V < |μ|)
    (Kp Ki δω θ : ℝ) :
    connection% (biasedModel V μ Kp Ki δω θ ∉
      TMIO.realize PIPLL.Meets {.phaseLocked}) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% TMIO.mem_realize)]
  intro h
  have hp : PIPLL.Meets (biasedModel V μ Kp Ki δω θ) .phaseLocked := h _ rfl
  exact biased_no_equilibrium hV hμ Kp Ki δω _
    ((piPLLField_point_eq_zero_iff (Kp := Kp)).mpr hp)

/-- Fold `μ = V` (`V ≠ 0`, `K_i ≠ 0`): `θ* = π/2` is an equilibrium with `h'(θ*) = 0`, and the
Jacobian there is the nonzero nilpotent matrix `[[0, K_i], [0, 0]]` (non-hyperbolic). The case
`μ = −V` is symmetric (`θ* = −π/2`). Static evidence on the model (linearization only), not a
connection conclusion. -/
@[powerlib_foundation] theorem biased_fold {V Kp Ki : ℝ} (hKi : Ki ≠ 0) (δω : ℝ) :
    piPLLField (biasedPD V V) Kp Ki δω (PhasePlane.mk (Real.pi / 2) (δω / Ki)) = 0 ∧
      fderiv ℝ (piPLLField (biasedPD V V) Kp Ki δω) (PhasePlane.mk (Real.pi / 2) (δω / Ki)) =
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian Kp Ki 0) ∧
      piPLLJacobian Kp Ki 0 ≠ 0 ∧ (piPLLJacobian Kp Ki 0) ^ 2 = 0 ∧
      ¬ LinearSystems.IsHurwitz (piPLLJacobian Kp Ki 0) := by
  have hd := hasDerivAt_biasedPD V V (Real.pi / 2)
  rw [Real.cos_pi_div_two, mul_zero, neg_zero] at hd
  exact piPLL_jacobian_nilpotent_of_deriv_zero (by simp [biasedPD]) hd hKi

end powerlib.PLL
