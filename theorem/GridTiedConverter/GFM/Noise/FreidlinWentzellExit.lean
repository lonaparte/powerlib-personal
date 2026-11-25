import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.UniformLDP
import theorem.Stochastic.QuasiPotentialLevel
import theorem.GridTiedConverter.GFM.Noise.FreidlinWentzellExact
import theorem.GridTiedConverter.GFM.Noise.FreidlinWentzellSaddle

/-! # Ingredients of the exit-time asymptotics for the noisy two-state GFM

Domain module: the two-state GFM swing with set-point noise
(`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzell.lean`). Two of the ingredients of the
Freidlin–Wentzell exit theorem `ε log E τ_ε → V̄` are proved here.
* The large-deviation principle of the solutions `x^{ε, x₀}` holds **uniformly over initial points
  in a compact set** (`Stochastic.LDP.IsLDP.limsup_iSup_solMap_le`,
  `Stochastic.LDP.IsLDP.le_liminf_iInf_solMap` applied to Schilder's theorem); the noise is
  degenerate (one column), joint continuity of the pathwise solution replaces ellipticity.
* The exit exponent through the energy level `{H = H(x_u) − η}` below the saddle,
  `V̄(η) = inf_{H(x) = H(x_u) − η} V₂(x_s, x)`, lies between `2D(ΔU − η)/σ_P²` and `2DΔU/σ_P²`
  and tends to `2DΔU/σ_P²` as `η → 0⁺` (`ΔU = U(δ_u) − U(δ_s)`): every path to the saddle
  crosses the level (`Stochastic.LDP.iInf_level_le_controlQuasiPotential`), and the
  Hamilton–Jacobi bound with `V_FW = V₂` (`Params.fwQP_eq_swingQP`, `Params.fwQP_ge`) bounds the
  level from below.

Model boundary.
* The two-state model of `FreidlinWentzell.lean`, `D > 0`, `c₀ ≤ P_ref < c₀ + A`: stable
  equilibrium `δ_s = arcsin s + α`, saddle `δ_u = π − arcsin s + α`, `s = (P_ref − c₀)/A`.
  `H(δ, p) = p²/(2M) + U(δ − α)` (`Params.swingEnergy`). The level set is the whole level set of
  `H` (all wells of the periodic potential); the boundary of the well containing `x_s` is the part
  of it in the strip `δ_u − 2π < δ < δ_u`.
* Not formalized: the Markov property of the solution at deterministic or hitting times and the
  exit-time bounds themselves (`limsup ε log E τ_ε ≤ V̄`, `liminf ε log E τ_ε ≥ V̄`).

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 3 §3 (uniformity in the initial point), Ch. 4 §2 (exit from a domain, the quasi-potential on
its boundary); A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.
(1998), Cor. 5.6.15 and §5.7 (exit problem).

Results.
* `Params.limsup_iSup_setPoint_le`, `Params.le_liminf_iInf_setPoint` (**uniform
  Freidlin–Wentzell bounds over compact sets of initial points**).
* `Params.escapeLevel_ge`, `Params.escapeLevel_le`, `Params.tendsto_escapeLevel` (**the exit
  exponent through the energy level `H(x_u) − η` tends to `2DΔU/σ_P²`**).
-/

noncomputable section
namespace powerlib.GFM.Noise

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal NNReal
open powerlib.Stochastic.LDP

namespace Params

variable (p : Params)

/-- **Uniform upper bound** (two states): for `K` compact and every set `A` of paths,
`limsup_{ε→0⁺} ε log sup_{x₀ ∈ K} P(x^{ε, x₀} ∈ A) ≤ −inf_{x₀ ∈ K} inf_{cl A} J_{x₀}`. -/
@[tmio M, powerlib_domain] theorem limsup_iSup_setPoint_le {σP : ℝ} {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)} (hX : Measurable X)
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) {Kc : Set (Fin 2 → ℝ)}
    (hKc : IsCompact Kc) (A : Set C(Icc (0 : ℝ) T, Fin 2 → ℝ)) :
    limsup (fun ε : ℝ => (ε : EReal) * ENNReal.log (⨆ x₀ ∈ Kc,
        P {ω | solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP) x₀
          (√ε • X ω) ∈ A})) (𝓝[>] 0) ≤
      -(⨅ x₀ ∈ Kc, ⨅ φ ∈ closure A,
        ((fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) x₀ T φ : ℝ≥0∞) : EReal)) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  have h := isLDP_schilder hB hT hX hXB
  have hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ id ε :=
    eventually_nhdsWithin_of_forall fun ε hε => le_of_lt hε
  have hu := h.limsup_iSup_solMap_le hs hK (columnsCLM fun _ : Fin 1 => swingColumn σP) hKc A
  refine le_trans (limsup_le_limsup ?_) hu
  filter_upwards [hs] with ε hε
  refine mul_le_mul_of_nonneg_left (ENNReal.log_le_log (iSup₂_mono fun x₀ _ => ?_))
    (by exact_mod_cast hε)
  exact Measure.le_map_apply (μ := P) (f := fun ω => √ε • X ω)
    (by exact (hX.const_smul (√ε)).aemeasurable)
    (solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP) x₀ ⁻¹' A)

/-- **Uniform lower bound** (two states): for `K` compact and `G` open,
`liminf_{ε→0⁺} ε log inf_{x₀ ∈ K} P(x^{ε, x₀} ∈ G) ≥ −sup_{x₀ ∈ K} inf_G J_{x₀}`. -/
@[tmio M, powerlib_domain] theorem le_liminf_iInf_setPoint {σP : ℝ} {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)} (hX : Measurable X)
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) {Kc : Set (Fin 2 → ℝ)}
    (hKc : IsCompact Kc) {G : Set C(Icc (0 : ℝ) T, Fin 2 → ℝ)} (hG : IsOpen G) :
    -(((⨆ x₀ ∈ Kc, ⨅ φ ∈ G,
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) x₀ T φ : ℝ≥0∞)) : EReal) ≤
      liminf (fun ε : ℝ => (ε : EReal) * ENNReal.log (⨅ x₀ ∈ Kc,
        P {ω | solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP) x₀
          (√ε • X ω) ∈ G})) (𝓝[>] 0) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  have h := isLDP_schilder hB hT hX hXB
  have hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ id ε :=
    eventually_nhdsWithin_of_forall fun ε hε => le_of_lt hε
  have hl := h.le_liminf_iInf_solMap hs hK (columnsCLM fun _ : Fin 1 => swingColumn σP) hKc hG
  refine hl.trans (le_of_eq (liminf_congr (Eventually.of_forall fun ε => ?_)))
  congr 2
  refine iInf_congr fun x₀ => iInf_congr fun _ => ?_
  rw [Measure.map_apply (by exact hX.const_smul (√ε))
    ((hG.preimage (continuous_solMap hK _ x₀)).measurableSet)]
  rfl

/-- **The barrier is positive**: `U(π − arcsin s) − U(arcsin s) > 0` for `c₀ ≤ P_ref < c₀ + A`
(`U' = A sin θ − (P_ref − c₀) > 0` between the two rest angles). -/
@[tmio M, powerlib_domain] theorem potential_barrier_pos (h0 : p.c0 ≤ p.Pref)
    (h1 : p.Pref < p.c0 + p.A) :
    0 < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) := by
  have hA := p.A_pos
  set s := (p.Pref - p.c0) / p.A with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hA.le
  have hs1 : s < 1 := by rw [hs, div_lt_one hA]; linarith
  have ha0 : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.mpr hs0
  have ha1 : Real.arcsin s < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hlt : Real.arcsin s < π - Real.arcsin s := by linarith
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope p.potential p.potentialDeriv hlt
    (fun z _ => (p.hasDerivAt_potential z).continuousAt.continuousWithinAt)
    (fun z _ => p.hasDerivAt_potential z)
  have hsin : s < Real.sin ξ := by
    have hss : Real.sin (Real.arcsin s) = s := Real.sin_arcsin (by linarith) hs1.le
    have e := Real.sin_sub_sin ξ (Real.arcsin s)
    have hp1 : 0 < Real.sin ((ξ - Real.arcsin s) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hξ.1]) (by linarith [hξ.2, Real.pi_pos])
    have hp2 : 0 < Real.cos ((ξ + Real.arcsin s) / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hξ.1, Real.pi_pos], by linarith [hξ.2]⟩
    rw [hss] at e
    nlinarith [mul_pos hp1 hp2]
  have hd : 0 < p.potentialDeriv ξ := by
    have hb : p.toSM.b = p.A := rfl
    have hPm : p.toSM.Pm = p.Pref - p.c0 := rfl
    unfold potentialDeriv
    rw [hb, hPm]
    have : p.Pref - p.c0 = p.A * s := by rw [hs]; field_simp
    rw [this]
    nlinarith
  rw [hslope] at hd
  exact (div_pos_iff_of_pos_right (by linarith)).mp hd

/-- The swing energy is continuous. -/
@[tmio M, powerlib_domain] theorem continuous_swingEnergy : Continuous p.swingEnergy := by
  unfold swingEnergy potential
  fun_prop

/-- **The exit exponent through an energy level, lower bound**: every state on the level
`H = H(x_u) − η` costs at least `2D(ΔU − η)/σ_P²` from `x_s`. -/
@[tmio M, powerlib_domain] theorem escapeLevel_ge {σP : ℝ} (hσ : σP ≠ 0) (η : ℝ) :
    ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) / σP ^ 2) ≤
      ⨅ x ∈ {x | p.swingEnergy x =
          p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η},
        p.swingQP σP ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] x := by
  refine le_iInf₂ fun x hx => ?_
  rw [← p.fwQP_eq_swingQP hσ]
  refine le_trans (le_of_eq ?_) (p.fwQP_ge hσ _ x)
  congr 1
  rw [show p.swingEnergy x = _ from hx]
  simp [swingEnergy]
  ring

/-- **The exit exponent through an energy level, upper bound**: for `0 ≤ η ≤ ΔU`, some state on
the level `H = H(x_u) − η` costs at most the saddle exponent `2DΔU/σ_P²` from `x_s` (every path
to the saddle crosses the level). -/
@[tmio M, powerlib_domain] theorem escapeLevel_le {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη0 : 0 ≤ η)
    (hη1 : η ≤ p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) :
    ⨅ x ∈ {x | p.swingEnergy x =
          p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η},
        p.swingQP σP ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] x ≤
      ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) / σP ^ 2) := by
  rw [← p.swingQP_saddle_eq hσ hD h0 h1]
  unfold swingQP
  refine iInf_level_le_controlQuasiPotential _ _ p.continuous_swingEnergy ?_ ?_
  · simp [swingEnergy]; linarith
  · simp [swingEnergy]; linarith

/-- **The exit exponent through the energy level `H(x_u) − η` tends to the saddle exponent**
`2DΔU/σ_P²` as `η → 0⁺`. -/
@[tmio M, powerlib_domain] theorem tendsto_escapeLevel {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) :
    Tendsto (fun η : ℝ => ⨅ x ∈ {x | p.swingEnergy x =
          p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η},
        p.swingQP σP ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] x) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) / σP ^ 2))) := by
  set ΔU := p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
    p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) with hΔU
  have hΔU0 : 0 < ΔU := p.potential_barrier_pos h0 h1
  have hlow : Tendsto (fun η : ℝ => ENNReal.ofReal (2 * p.D * (ΔU - η) / σP ^ 2)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (2 * p.D * ΔU / σP ^ 2))) := by
    refine ENNReal.tendsto_ofReal ?_
    have : Tendsto (fun η : ℝ => 2 * p.D * (ΔU - η) / σP ^ 2) (𝓝 0)
        (𝓝 (2 * p.D * (ΔU - 0) / σP ^ 2)) :=
      ((continuous_const.mul (continuous_const.sub continuous_id)).div_const _).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · exact Eventually.of_forall fun η => p.escapeLevel_ge hσ η
  · have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), η < ΔU :=
      (eventually_lt_nhds hΔU0).filter_mono nhdsWithin_le_nhds
    filter_upwards [hev, self_mem_nhdsWithin] with η hη hη0
    exact p.escapeLevel_le hσ hD h0 h1 (le_of_lt hη0) hη.le

end Params

end powerlib.GFM.Noise
