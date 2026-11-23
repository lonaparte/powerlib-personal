import theorem.GridTiedConverter.PLL.TrigPD
import theorem.SpecialFunctions.Sinusoid

/-! # PI-PLL with a biased sinusoidal phase detector `h(θ) = −V sin θ + μ`

Model boundary.
* System: the general PI-PLL of `theorem/GridTiedConverter/PLL/PIPLL.lean` (state `(θ, η)` in this
  order, `θ̇ = K_p h(θ) + K_i η − δω`, `η̇ = h(θ)`, constant `δω`) with the phase-detector
  characteristic of the "simple pendulum" model of T-pll-dynamics §1.13.2,
  `h(θ) = −V sin θ + μ` (`biasedPD V μ`), `V > 0`; `μ` is a constant bias of the phase
  detector (small-signal frequency/offset bias in the note). Continuous time, autonomous; no
  pre-filter, delay, PWM, current loop or saturation. All equilibrium and stability results are
  instantiations of `theorem/GridTiedConverter/PLL/PIPLL.lean` and of the PI-PLL family
  (`theorem/GridTiedConverter/PLL/PIPLLFamily.lean`).
* Level: equilibrium set and local behaviour at equilibria (linearization).

Source: work-sync `theory/T-pll-dynamics.md` §1.13.2.

Results.
* `|μ| > V`: no equilibrium at all (frequency-drift / loss of lock).
* `|μ| < V`: in every period window `[−π/2, 3π/2)` the zeros of `h` are exactly
  `θ₁ = arcsin(μ/V)` and `θ₂ = π − arcsin(μ/V)`, `θ₁ ≠ θ₂`; with `K_p, K_i > 0` the
  equilibrium `(θ₁, δω/K_i)` is locally exponentially stable and `(θ₂, δω/K_i)` is unstable
  (saddle): exactly one stable and one saddle per period.
* `|μ| = V` (fold): `θ* = ±π/2` is a double zero (`h' = 0`), so the equilibrium
  `(±π/2, δω/K_i)` (`piPLLField_eq_zero_iff`) has the Jacobian `piPLLJacobian K_p K_i 0`
  (`fderiv_piPLLField` at slope `0`), a nonzero nilpotent matrix (non-hyperbolic;
  `piPLLJacobian_zero_sq`, `piPLLJacobian_zero_ne_zero`).
* `biasedPD` is the trigonometric polynomial `SpecialFunctions.trigPoly2 μ 0 (−V) 0 0` and
  `biasedModel` the member `trigModel μ 0 (−V) 0 0` of `theorem/GridTiedConverter/PLL/TrigPD.lean`
  (definitions), so the stable and saddle equilibria are the trigonometric laws
  `trigPLL_mem_den_locallyExponentiallyStable`, `trigPLL_mem_den_unstable` at `θ₁`, `θ₂`;
  `biasedPD_apply`: `h(θ) = −V sin θ + μ`.

Family and connection conclusions.
No new family: the biased PLL is the member
`biasedModel V μ K_p K_i δω θ*` of the PI-PLL family `PLL.PIPLL.family`, whose system map reads
the field translated so that the selected point `(θ*, δω / K_i)` is the origin. The stable and
saddle equilibria are connection statements on that family's semantics connection
(`biased_mem_den_locallyExponentiallyStable`, `biased_mem_den_unstable`); loss of lock for
`|μ| > V` is stated on its requirement connection (`biased_not_phaseLocked`). The absence of
equilibria (`biased_no_equilibrium`) and the zero set of `h` (`biasedPD_zeros`) are static
evidence on the model, not connection conclusions.
-/

noncomputable section
namespace powerlib.PLL
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Biased sinusoidal phase detector `h(θ) = −V sin θ + μ`: the trigonometric polynomial
`SpecialFunctions.trigPoly2` with constant `μ`, `sin θ` coefficient `−V` and no other terms. -/
abbrev biasedPD (V μ : ℝ) : ℝ → ℝ := SpecialFunctions.trigPoly2 μ 0 (-V) 0 0

@[tmio M, powerlib_domain] theorem biasedPD_apply (V μ θ : ℝ) :
    biasedPD V μ θ = -(V * Real.sin θ) + μ := by
  simp only [biasedPD, SpecialFunctions.trigPoly2]
  ring

/-- `|μ| > V ≥ 0`: the biased PLL has no equilibrium.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem biased_no_equilibrium {V μ : ℝ} (hV : 0 ≤ V) (hμ : V < |μ|)
    (Kp Ki δω : ℝ) (x : ℝ²) : piPLLField (biasedPD V μ) Kp Ki δω x ≠ 0 := by
  intro h
  have h1 : biasedPD V μ (x 0) = 0 := by
    have := congrArg (fun y : ℝ² => y 1) h
    simpa using this
  have hs : |V * Real.sin (x 0)| ≤ V := by
    rw [abs_mul, abs_of_nonneg hV]
    exact mul_le_of_le_one_right hV (Real.abs_sin_le_one _)
  have : μ = V * Real.sin (x 0) := by rw [biasedPD_apply] at h1; linarith
  rw [this] at hμ
  linarith

/-- `|μ| < V`: in the window `[−π/2, 3π/2)` the zeros of `h` are exactly
`arcsin(μ/V)` and `π − arcsin(μ/V)`, and they are distinct. -/
@[tmio M, powerlib_domain] theorem biasedPD_zeros {V μ : ℝ} (hV : 0 < V) (hμ : |μ| < V) :
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
    rw [biasedPD_apply]
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
(selected point `(θ*, δω / K_i)`): the trigonometric member `trigModel μ 0 (−V) 0 0`. -/
abbrev biasedModel (V μ Kp Ki δω θ : ℝ) : PIPLL.Model := trigModel μ 0 (-V) 0 0 Kp Ki δω θ

/-- `|μ| < V`, `K_p, K_i > 0`: the equilibrium at `θ₁ = arcsin(μ/V)` is locally
exponentially stable, for every constant frequency offset `δω`. -/
@[tmio TM, powerlib_domain] theorem biased_mem_den_locallyExponentiallyStable {V μ Kp Ki : ℝ}
    (hV : 0 < V) (hμ : |μ| < V) (hKp : 0 < Kp) (hKi : 0 < Ki) (δω : ℝ) :
    connection% (biasedModel V μ Kp Ki δω (Real.arcsin (μ / V)) ∈
      PIPLL.family.den (.flow .locallyExponentiallyStable)) := by
  have hcos := SpecialFunctions.cos_arcsin_div_pos hμ hV
  refine trigPLL_mem_den_locallyExponentiallyStable hKp hKi ?_ ?_
  · exact (biasedPD_apply V μ _).trans
      (by rw [SpecialFunctions.mul_sin_arcsin_div hμ.le hV, neg_add_cancel])
  · simp only [SpecialFunctions.trigPoly2Deriv]; nlinarith

/-- `|μ| < V`, `K_i > 0`: the equilibrium at `θ₂ = π − arcsin(μ/V)` is unstable (saddle), for
every `K_p` and every constant frequency offset `δω`. -/
@[tmio TM, powerlib_domain] theorem biased_mem_den_unstable {V μ Kp Ki : ℝ} (hV : 0 < V) (hμ : |μ| < V)
    (hKi : 0 < Ki) (δω : ℝ) :
    connection% (biasedModel V μ Kp Ki δω (Real.pi - Real.arcsin (μ / V)) ∈
      PIPLL.family.den (.flow .unstable)) := by
  have hcos := SpecialFunctions.cos_pi_sub_arcsin_div_neg hμ hV
  refine trigPLL_mem_den_unstable hKi ?_ ?_
  · exact (biasedPD_apply V μ _).trans
      (by rw [SpecialFunctions.mul_sin_pi_sub_arcsin_div hμ.le hV, neg_add_cancel])
  · simp only [SpecialFunctions.trigPoly2Deriv]; nlinarith

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

end powerlib.PLL
