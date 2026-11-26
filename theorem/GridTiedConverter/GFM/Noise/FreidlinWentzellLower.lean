import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ExitTimeLyapunov
import theorem.GridTiedConverter.GFM.Noise.FreidlinWentzellWell

/-! # Exit of the noisy two-state GFM from its potential well: the exponential law

Domain module: the noisy two-state GFM with set-point noise
(`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzell.lean`) and the closed potential well
`Params.energyWell η` below the saddle level of
`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellWell.lean`. The mean exit time from the well
started at `x_s` grows at least at the rate of the boundary level,
`liminf_{ε→0⁺} ε log E τ_ε ≥ V̄(η) = 2D(ΔU − η)/σ_P²`, the exit time itself exceeds `e^{β/ε}`
with probability `1 − O(e^{−γ/ε})` for every `β < V̄(η)`, and with the upper bound of
`FreidlinWentzellWell.lean` the **exponential law** `ε log E τ_ε → 2D(ΔU − η)/σ_P²` holds. The
lower bounds are the generic law `Stochastic.LDP.le_liminf_log_lintegral_exitTime_of_lyapunov`
(and its probability form) of `theorem/Stochastic/ExitTimeLyapunov.lean` with `V = H`,
`a = 2D/σ_P²`: the Hamilton–Jacobi bound `Params.fwQP_ge`; the level (a path leaving the well
reaches `H = H(x_u) − η` or a saddle angle above it, `Params.exists_level_of_mem_closure_leave`);
and the dissipation of `H` (away from `x_s` the noiseless flow loses a uniform amount of energy per
unit time, `Params.exists_swingEnergy_freeSwing_drop`).

Model boundary.
* The two-state model of `FreidlinWentzell.lean`: state `(δ, p)` on `Fin 2 → ℝ`, drift
  `Params.swingDrift`, noise column `(0, σ_P)`; `σ_P ≠ 0`, `D > 0`, `c₀ ≤ P_ref < c₀ + A`;
  `δ_s = arcsin s + α`, `s = (P_ref − c₀)/A`, `H = Params.swingEnergy`,
  `ΔU = U(π − arcsin s) − U(arcsin s)`; `0 < η < ΔU`. The exit time is
  `Stochastic.LDP.exitTime` of `Params.energyWell η` from `x_s = (δ_s, 0)` for a Brownian motion
  all of whose paths are continuous; `E τ_ε` its lower Lebesgue integral.
* `Params.exists_level_of_mem_closure_leave` holds for any continuous `G ≥ U(δ − α)` on states
  whose first coordinate is the angle; the three-state filter well uses it
  (`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellFilter.lean`).
* Exit place. The boundary of the well is the energy level `H = H(x_u) − η` in the strip, on which
  the Hamilton–Jacobi lower bound `(2D/σ_P²)(H − H(x_s))` of the quasi-potential is constant:
  the exit-place part of the exit theorem singles out no neighbourhood of the saddle. For the well
  cut at an angle the exit concentrates at the cut point
  (`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellPlace.lean`, through
  `Params.eventually_measure_exitTime_energyWell_le`). The domain whose exit concentrates at the
  saddle, the basin of attraction of `x_s`, is bounded by the stable manifolds of the saddles — an
  invariant (characteristic) boundary through equilibria of the drift, outside the hypotheses of
  Dembo–Zeitouni §5.7; it is not treated.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §2–3 (exit from a domain: `ε log E τ_ε → min_{∂D} V`); A. Dembo, O. Zeitouni,
*Large Deviations Techniques and Applications*, 2nd ed. (1998), Thm 5.7.11(a); LaSalle's
argument for the damped swing (`theorem/PowerSystem/Synchronous/DampedEAC.lean`).

Results.
* `Params.exists_level_of_mem_closure_leave` (**a path leaving a well of the strip reaches its
  level**).
* `Params.le_liminf_log_exitTime_energyWell` (**`liminf ε log E τ_ε ≥ 2D(ΔU − η)/σ_P²`**),
  `Params.eventually_measure_exitTime_energyWell_le` (**`P(τ_ε ≤ e^{β/ε}) ≤ e^{−γ/ε}`** for
  `β < 2D(ΔU − η)/σ_P²`).
* `Params.tendsto_log_exitTime_energyWell` (**exponential law of the mean exit time**:
  `ε log E τ_ε → 2D(ΔU − η)/σ_P²`).
-/

noncomputable section
namespace powerlib.GFM.Noise

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal NNReal
open powerlib.Stochastic.LDP

namespace Params

variable (p : Params)

variable {σP : ℝ}

/-- **A path leaving a well of the strip reaches its level**: for a continuous `G` on states whose
first coordinate is the angle, with `U(δ − α) ≤ G(x)`, and a level `H_l ≤ U(δ_u − α)`, every path
from `y` in `{δ_u − 2π ≤ δ ≤ δ_u, G ≤ H_l}` that lies in the closure of the paths leaving it
reaches `G ≥ H_l` (inside the open strip it must cross the level; at a saddle angle `G ≥ U ≥ H_l`;
`c₀ ≤ P_ref`, so `U(δ_u − 2π − α) ≥ U(δ_u − α)`). -/
@[tmio M, powerlib_domain] theorem exists_level_of_mem_closure_leave (h0 : p.c0 ≤ p.Pref)
    {n : ℕ} {G : (Fin (n + 1) → ℝ) → ℝ} (hG : Continuous G)
    (hGU : ∀ x, p.potential (x 0 - p.α) ≤ G x) {Hl : ℝ}
    (hHl : Hl ≤ p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A))) {y : Fin (n + 1) → ℝ}
    (hy : π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α - 2 * π ≤ y 0 ∧
      y 0 ≤ π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α ∧ G y ≤ Hl) {T : ℝ≥0}
    {φ : C(Icc (0 : ℝ) T, Fin (n + 1) → ℝ)}
    (hφ : φ ∈ closure {φ : C(Icc (0 : ℝ) T, Fin (n + 1) → ℝ) | ∃ t, φ t ∉
      {x : Fin (n + 1) → ℝ | π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α - 2 * π ≤ x 0 ∧
        x 0 ≤ π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α ∧ G x ≤ Hl}})
    (hφ0 : φ ⟨0, le_rfl, T.coe_nonneg⟩ = y) : ∃ t, Hl ≤ G (φ t) := by
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  set W := {x : Fin (n + 1) → ℝ | π - a + p.α - 2 * π ≤ x 0 ∧ x 0 ≤ π - a + p.α ∧ G x ≤ Hl}
    with hW
  set A := {φ : C(Icc (0 : ℝ) T, Fin (n + 1) → ℝ) | ∃ t, φ t ∉ W} with hA_def
  set W' := {x : Fin (n + 1) → ℝ | π - a + p.α - 2 * π < x 0 ∧ x 0 < π - a + p.α ∧ G x < Hl}
    with hW'
  have hW'o : IsOpen W' :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt (continuous_apply 0) continuous_const).inter (isOpen_lt hG continuous_const))
  have hW'W : W' ⊆ W := fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  have hclA : closure A ⊆ {φ : C(Icc (0 : ℝ) T, Fin (n + 1) → ℝ) | ¬ MapsTo φ univ W'} := by
    refine closure_minimal (fun φ hφ hmaps => ?_) ?_
    · obtain ⟨t, ht⟩ := hφ
      exact ht (hW'W (hmaps (mem_univ t)))
    · exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hW'o).isClosed_compl
  have hout := (hclA hφ)
  simp only [mem_ofPred_eq, MapsTo, mem_univ, true_implies, not_forall] at hout
  obtain ⟨t₁, ht₁⟩ := hout
  by_cases hE : Hl ≤ G (φ t₁)
  · exact ⟨t₁, hE⟩
  have hstrip : ¬ (π - a + p.α - 2 * π < φ t₁ 0 ∧ φ t₁ 0 < π - a + p.α) := fun h =>
    ht₁ ⟨h.1, h.2, lt_of_not_ge hE⟩
  have hcont : ContinuousOn (fun s => pathExt φ s 0) (Icc 0 t₁) :=
    ((continuous_apply 0).comp (continuous_pathExt φ)).continuousOn
  have hv0 : pathExt φ 0 0 = y 0 := by
    rw [pathExt_of_mem _ ⟨le_rfl, T.coe_nonneg⟩, hφ0]
  have hvt : pathExt φ t₁ 0 = φ t₁ 0 := by rw [pathExt_of_mem _ t₁.2]
  have hπ := Real.pi_pos
  rcases not_and_or.mp hstrip with hl | hr
  · rw [not_lt] at hl
    obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc' t₁.2.1 hcont
      (show π - a + p.α - 2 * π ∈ Icc (pathExt φ t₁ 0) (pathExt φ 0 0) from
        ⟨by rw [hvt]; exact hl, by rw [hv0]; exact hy.1⟩)
    simp only at hsv
    have hsm : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t₁.2.2⟩
    refine ⟨⟨s, hsm⟩, ?_⟩
    have h1' := hGU (φ ⟨s, hsm⟩)
    have hsv' : φ ⟨s, hsm⟩ 0 = π - a + p.α - 2 * π := by
      rw [← pathExt_of_mem _ hsm]; exact hsv
    rw [hsv', show π - a + p.α - 2 * π - p.α = (π - a) - 2 * π by ring,
      p.potential_sub_two_pi] at h1'
    have : 0 ≤ 2 * π * (p.Pref - p.c0) := by nlinarith
    linarith
  · rw [not_lt] at hr
    obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc t₁.2.1 hcont
      (show π - a + p.α ∈ Icc (pathExt φ 0 0) (pathExt φ t₁ 0) from
        ⟨by rw [hv0]; exact hy.2.1, by rw [hvt]; exact hr⟩)
    simp only at hsv
    have hsm : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t₁.2.2⟩
    refine ⟨⟨s, hsm⟩, ?_⟩
    have h1' := hGU (φ ⟨s, hsm⟩)
    have hsv' : φ ⟨s, hsm⟩ 0 = π - a + p.α := by
      rw [← pathExt_of_mem _ hsm]; exact hsv
    rw [hsv', show π - a + p.α - p.α = π - a by ring] at h1'
    linarith

/-- The data of the well at `x_s = (δ_s, 0)`: it lies in the well, below its level, the rate
factor `2D/σ_P²` is positive, and the level value is `2D(ΔU − η)/σ_P²`. -/
@[tmio M, powerlib_domain] private theorem well_data (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ}
    (hη1 : η < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) :
    ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] ∈ p.energyWell η ∧
      p.swingEnergy ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] <
        p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η ∧ 0 < 2 * p.D / σP ^ 2 ∧
      (((2 * p.D / σP ^ 2 * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η -
          p.swingEnergy ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0]) : ℝ) : EReal) =
        ((ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
          p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) / σP ^ 2) : ℝ≥0∞) : EReal)) := by
  set as := Real.arcsin ((p.Pref - p.c0) / p.A) with has
  have hA := p.A_pos
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hA).mpr (by linarith)
  have has0 : 0 ≤ as := Real.arcsin_nonneg.mpr hs0
  have has1 : as < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hxsE : p.swingEnergy ![as + p.α, 0] = p.potential as := by simp [swingEnergy]
  have hσ2 : 0 < σP ^ 2 := by positivity
  have ha0 : 0 < 2 * p.D / σP ^ 2 := by positivity
  refine ⟨⟨by simp; linarith [Real.pi_pos], by simp; linarith, by rw [hxsE]; linarith⟩,
    by rw [hxsE]; linarith, ha0, ?_⟩
  have hv0 : 0 ≤ 2 * p.D * (p.potential (π - as) - p.potential as - η) / σP ^ 2 := by
    have : 0 ≤ p.potential (π - as) - p.potential as - η := by linarith
    positivity
  rw [EReal.coe_ennreal_ofReal, max_eq_left hv0, hxsE]
  congr 1
  ring

/-- **Lower bound for the mean exit time from the well** (two states, `σ_P ≠ 0`, `D > 0`,
`c₀ ≤ P_ref < c₀ + A`, `0 < η < ΔU`): the exit time `τ_ε` of the noisy model started at `x_s`
from `Params.energyWell η` satisfies `liminf_{ε→0⁺} ε log E τ_ε ≥ 2D(ΔU − η)/σ_P²`. The generic
law `Stochastic.LDP.le_liminf_log_lintegral_exitTime_of_lyapunov` with `V = H`, `a = 2D/σ_P²`:
the Hamilton–Jacobi bound `Params.fwQP_ge`, the level `exists_level_of_mem_closure_leave`, the
drop `Params.exists_swingEnergy_freeSwing_drop`. -/
@[tmio M, powerlib_domain] theorem le_liminf_log_exitTime_energyWell (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous fun t => B t ω) :
    ((ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) / σP ^ 2) : ℝ≥0∞) : EReal) ≤
      liminf (fun ε : ℝ => (ε : EReal) * ENNReal.log (∫⁻ ω, exitTime p.swingDrift
        (columnsCLM fun _ : Fin 1 => swingColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] (p.energyWell η) (√ε) B hBc ω ∂P))
        (𝓝[>] 0) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  obtain ⟨hxsW, hlt, ha0, hvE⟩ := p.well_data hσ hD h0 h1 hη1
  have hgen := le_liminf_log_lintegral_exitTime_of_lyapunov hB hBc (p.isCompact_energyWell η)
    hxsW hK (columnsCLM fun _ : Fin 1 => swingColumn σP) p.continuous_swingEnergy ha0 hlt
    (fun y x => p.fwQP_ge hσ y x)
    (fun y hy φ hφ hφ0 => p.exists_level_of_mem_closure_leave h0 p.continuous_swingEnergy
      p.potential_le_swingEnergy (by linarith) hy hφ hφ0)
    (fun r hr => p.exists_swingEnergy_freeSwing_drop (σP := σP) hD h0 h1 hη0 hr)
  rwa [hvE] at hgen

/-- **The exit time from the well is exponentially large in probability** (two states,
`σ_P ≠ 0`, `D > 0`, `c₀ ≤ P_ref < c₀ + A`, `0 < η < ΔU`): for every
`β < 2D(ΔU − η)/σ_P²` there is `γ > 0` with `P(τ_ε ≤ e^{β/ε}) ≤ e^{−γ/ε}` for all small `ε`
(`Stochastic.LDP.eventually_measure_exitTime_le_of_lyapunov` with the data of
`le_liminf_log_exitTime_energyWell`). -/
@[tmio M, powerlib_domain] theorem eventually_measure_exitTime_energyWell_le (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous fun t => B t ω) {β : ℝ}
    (hβ : β < 2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) / σP ^ 2) :
    ∃ γ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | exitTime p.swingDrift
        (columnsCLM fun _ : Fin 1 => swingColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] (p.energyWell η) (√ε) B hBc ω ≤
      ENNReal.ofReal (Real.exp (β / ε))} ≤ ENNReal.ofReal (Real.exp (-γ / ε)) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  obtain ⟨hxsW, hlt, ha0, hvE⟩ := p.well_data hσ hD h0 h1 hη1
  have hv : 2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) / σP ^ 2 =
      2 * p.D / σP ^ 2 * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η -
        p.swingEnergy ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0]) := by
    simp [swingEnergy]; ring
  rw [hv] at hβ
  exact eventually_measure_exitTime_le_of_lyapunov hB hBc (p.isCompact_energyWell η) hxsW hK
    (columnsCLM fun _ : Fin 1 => swingColumn σP) p.continuous_swingEnergy ha0 hlt
    (fun y x => p.fwQP_ge hσ y x)
    (fun y hy φ hφ hφ0 => p.exists_level_of_mem_closure_leave h0 p.continuous_swingEnergy
      p.potential_le_swingEnergy (by linarith) hy hφ hφ0)
    (fun r hr => p.exists_swingEnergy_freeSwing_drop (σP := σP) hD h0 h1 hη0 hr) hβ

/-- **The exponential law of the mean exit time from the well** (two states, `σ_P ≠ 0`, `D > 0`,
`c₀ ≤ P_ref < c₀ + A`, `0 < η < ΔU`): `ε log E τ_ε → 2D(ΔU − η)/σ_P²` as `ε → 0⁺`, the lower
bound `le_liminf_log_exitTime_energyWell` with the upper bound
`GFM.Noise.Params.limsup_log_exitTime_energyWell_le`. -/
@[tmio M, powerlib_domain] theorem tendsto_log_exitTime_energyWell (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous fun t => B t ω) :
    Tendsto (fun ε : ℝ => (ε : EReal) * ENNReal.log (∫⁻ ω, exitTime p.swingDrift
        (columnsCLM fun _ : Fin 1 => swingColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] (p.energyWell η) (√ε) B hBc ω ∂P))
      (𝓝[>] 0) (𝓝 ((ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin
        ((p.Pref - p.c0) / p.A)) - p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) /
          σP ^ 2) : ℝ≥0∞) : EReal)) :=
  tendsto_of_le_liminf_of_limsup_le
    (p.le_liminf_log_exitTime_energyWell hσ hD h0 h1 hη0 hη1 hB hBc)
    (p.limsup_log_exitTime_energyWell_le hσ hD h0 h1 hη0 hη1.le hB hBc)

end Params

end powerlib.GFM.Noise
