import dependencies.Mathlib
import theorem.Attributes
import theorem.GridTiedConverter.GFM.Noise.FreidlinWentzellLower

/-! # Exit place of the noisy two-state GFM from a cut potential well

Domain module: the noisy two-state GFM with set-point noise
(`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzell.lean`) and the cut well
`Params.cutWell η d = {x ∈ Params.energyWell η : δ ≤ d}` of
`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellWell.lean` (`δ_s < d < δ_u`,
`U(d − α) < U(δ_u − α) − η`). On its boundary the Hamilton–Jacobi value `(2D/σ_P²)(H − H(x_s))`
of the quasi-potential has the unique minimiser `z* = (d, 0)`: on the cut `δ = d` the energy is
`U(d − α) + p²/(2M)`, on the arc it is the level `U(δ_u − α) − η`. The **exit place
concentrates at `z*`**: for every `r > 0`, the probability that the solution started at `x_s`
touches the boundary at distance `≥ r` from `z*` before it leaves the cut well is at most
`e^{−γ/ε}` for all small `ε`. Such a touch needs the energy `U(d − α) + κ`,
`κ = min(r²/(2M), U(δ_u − α) − η − U(d − α))`, before the exit from the cut well: either the
cut well survives up to `e^{β/ε}` (probability `≤ E τ_cut e^{−β/ε}`, the mean exit time grows at
most at the rate `2D(U(d − α) − U(δ_s − α))/σ_P²` of the cut point,
`Params.limsup_log_exitTime_cutWell_le`), or the energy well at the level `U(d − α) + κ/2` is left
before `e^{β/ε}` (probability `≤ e^{−γ/ε}`, `Params.eventually_measure_exitTime_energyWell_le`),
with `β` between the two exponents. Deterministic time blocks and the Markov property at
deterministic times suffice; no hitting-time strong Markov argument is needed.

Model boundary.
* The two-state model of `FreidlinWentzell.lean`: state `(δ, p)` on `Fin 2 → ℝ` (sup norm),
  drift `Params.swingDrift`, noise column `(0, σ_P)`; `σ_P ≠ 0`, `D > 0`, `c₀ ≤ P_ref < c₀ + A`,
  `δ_s = arcsin s + α < d < δ_u = π − arcsin s + α`, `η > 0`, `U(d − α) < U(π − arcsin s) − η`.
  The solution is started at `x_s`, driven by a Brownian motion all of whose paths are continuous.
* The event: for some horizon `T` and `t ≤ T`, the solution on `[0, T]` stays in the cut well up to
  `t` and is at time `t` on the topological boundary at distance `≥ r` from `z*`. It contains the
  exit through a boundary point at distance `≥ r` (the first exit point lies on the boundary).
* The domain is not the basin of attraction: the cut is transversal to the flow except at `z*`,
  where the drift `(0, P_ref − P(d)) ≠ 0` is tangent to it. The exit place of the basin (a
  characteristic boundary through the saddle), of the uncut well (constant Hamilton–Jacobi value
  on its boundary) and of the three-state model is not treated; nor is the law of `τ_ε/E τ_ε`.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §2 (Thm 4.2.1: the exit concentrates at the minimisers of the quasi-potential on the
boundary); A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed. (1998),
Thm 5.7.11(b) (the exit place, by the strong Markov property at hitting times; replaced here by
the comparison of two exit times).

Results.
* `Params.le_swingEnergy_of_mem_frontier_cutWell` (the energy on the boundary away from `z*`).
* `Params.eventually_measure_exitPlace_cutWell_le` (**exit place**: the boundary is touched away
  from `z*` before the exit with probability `≤ e^{−γ/ε}`).
-/

noncomputable section
namespace powerlib.GFM.Noise

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal NNReal
open powerlib.Stochastic.LDP

namespace Params

variable (p : Params)

/-- **The energy on the boundary of the cut well away from the cut point**: a boundary state at
sup-distance `≥ r` from `(d, 0)` has energy at least
`U(d − α) + min(r²/(2M), U(δ_u − α) − η − U(d − α))` (`c₀ ≤ P_ref`, `d < δ_u`). -/
@[tmio M, powerlib_domain] theorem le_swingEnergy_of_mem_frontier_cutWell (h0 : p.c0 ≤ p.Pref)
    {η : ℝ} (hη0 : 0 < η) {d : ℝ} (hd1 : d < π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    {r : ℝ} (hr : 0 ≤ r) {x : Fin 2 → ℝ} (hx : x ∈ frontier (p.cutWell η d))
    (hxr : r ≤ dist x ![d, 0]) :
    p.potential (d - p.α) + min (r ^ 2 / (2 * p.M))
      (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η - p.potential (d - p.α)) ≤
      p.swingEnergy x := by
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  set m := min (r ^ 2 / (2 * p.M)) (p.potential (π - a) - η - p.potential (d - p.α)) with hm
  have hM := p.M_pos
  have hπ := Real.pi_pos
  have hxK : x ∈ p.cutWell η d := (p.isCompact_cutWell η d).isClosed.frontier_subset hx
  obtain ⟨⟨hx1, hx2, hx3⟩, hx4⟩ := hxK
  simp only [mem_ofPred_eq] at hx4
  by_contra hlt
  rw [not_le] at hlt
  set O := {x : Fin 2 → ℝ | π - a + p.α - 2 * π < x 0 ∧ x 0 < π - a + p.α ∧
    p.swingEnergy x < p.potential (π - a) - η ∧ x 0 < d} with hO
  have hOo : IsOpen O :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt (continuous_apply 0) continuous_const).inter
        ((isOpen_lt p.continuous_swingEnergy continuous_const).inter
          (isOpen_lt (continuous_apply 0) continuous_const)))
  have hOK : O ⊆ p.cutWell η d := fun y hy => ⟨⟨hy.1.le, hy.2.1.le, hy.2.2.1.le⟩, hy.2.2.2.le⟩
  have hint : x ∉ interior (p.cutWell η d) := hx.2
  refine hint (interior_maximal hOK hOo ⟨?_, by linarith, ?_, ?_⟩)
  · -- not at the left saddle angle, where the energy exceeds the level
    by_contra hle
    rw [not_lt] at hle
    have hx0 : x 0 = π - a + p.α - 2 * π := le_antisymm hle hx1
    have h1' := p.potential_le_swingEnergy x
    rw [hx0, show π - a + p.α - 2 * π - p.α = (π - a) - 2 * π by ring,
      p.potential_sub_two_pi] at h1'
    have : 0 ≤ 2 * π * (p.Pref - p.c0) := by nlinarith
    linarith
  · have : m ≤ p.potential (π - a) - η - p.potential (d - p.α) := min_le_right _ _
    linarith
  · -- not on the cut, where the distance to `(d, 0)` is `|p|`
    by_contra hle
    rw [not_lt] at hle
    have hx0 : x 0 = d := le_antisymm hx4 hle
    have hdist : dist x ![d, 0] ≤ |x 1| := by
      refine (dist_pi_le_iff (abs_nonneg _)).mpr fun i => ?_
      fin_cases i
      · simp [hx0]
      · simp
    have hr1 : r ≤ |x 1| := hxr.trans hdist
    have hE : p.swingEnergy x = x 1 ^ 2 / (2 * p.M) + p.potential (d - p.α) := by
      simp [swingEnergy, hx0]
    have hm1 : m ≤ r ^ 2 / (2 * p.M) := min_le_left _ _
    have hsq : r ^ 2 ≤ x 1 ^ 2 := by
      rw [← sq_abs (x 1)]
      exact pow_le_pow_left₀ hr hr1 2
    have : r ^ 2 / (2 * p.M) ≤ x 1 ^ 2 / (2 * p.M) := by gcongr
    linarith

/-- **Exit place of the cut well** (two states, `σ_P ≠ 0`, `D > 0`, `c₀ ≤ P_ref < c₀ + A`,
`η > 0`, `δ_s < d < δ_u`, `U(d − α) < U(δ_u − α) − η`): for every `r > 0` there is `γ > 0` such
that, for all small `ε`, the solution started at `x_s` touches the boundary of `Params.cutWell η d`
at sup-distance `≥ r` from the cut point `(d, 0)`, before leaving the cut well, with probability
at most `e^{−γ/ε}`: the exit concentrates at the unique minimiser `(d, 0)` of the
Hamilton–Jacobi value on the boundary. -/
@[tmio M, powerlib_domain] theorem eventually_measure_exitPlace_cutWell_le {σP : ℝ}
    (hσ : σP ≠ 0) (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ}
    (hη0 : 0 < η) {d : ℝ} (hd0 : Real.arcsin ((p.Pref - p.c0) / p.A) + p.α < d)
    (hd1 : d < π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hdU : p.potential (d - p.α) < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η)
    {r : ℝ} (hr : 0 < r) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous fun t => B t ω) :
    ∃ γ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ T : ℝ≥0, ∃ t : Icc (0 : ℝ) T,
      (∀ s : Icc (0 : ℝ) T, s ≤ t → solMap p.swingDrift
        (columnsCLM fun _ : Fin 1 => swingColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] (√ε • brownPath B hBc T ω) s ∈
          p.cutWell η d) ∧
      solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] (√ε • brownPath B hBc T ω) t ∈
          frontier (p.cutWell η d) ∧
      r ≤ dist (solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] (√ε • brownPath B hBc T ω) t) ![d, 0]} ≤
      ENNReal.ofReal (Real.exp (-γ / ε)) := by
  obtain ⟨L, hL⟩ := p.lipschitzWith_swingDrift
  set N := columnsCLM fun _ : Fin 1 => swingColumn σP with hN
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  set xs : Fin 2 → ℝ := ![a + p.α, 0] with hxs
  set K := p.cutWell η d with hK
  have hM := p.M_pos
  have hA := p.A_pos
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hA).mpr (by linarith)
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hs0
  have ha1 : a < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hσ2 : 0 < σP ^ 2 := by positivity
  set ac := 2 * p.D / σP ^ 2 with hac
  have hac0 : 0 < ac := by positivity
  have hUd : p.potential a < p.potential (d - p.α) :=
    p.potential_lt_potential h0 h1 (by linarith) (by linarith)
  -- the energy gap of the far boundary and the comparison well
  set κ := min (r ^ 2 / (2 * p.M)) (p.potential (π - a) - η - p.potential (d - p.α)) with hκ
  have hκ0 : 0 < κ := lt_min (by positivity) (by linarith)
  have hκ1 : κ ≤ p.potential (π - a) - η - p.potential (d - p.α) := min_le_right _ _
  set η' := p.potential (π - a) - (p.potential (d - p.α) + κ / 2) with hη'
  have hη'0 : 0 < η' := by rw [hη']; linarith
  have hη'1 : η' < p.potential (π - a) - p.potential a := by rw [hη']; linarith
  set Vs := ac * (p.potential (d - p.α) - p.potential a) with hVs
  have hVs0 : 0 ≤ Vs := mul_nonneg hac0.le (by linarith)
  set gap := ac * (κ / 2) with hgap
  have hgap0 : 0 < gap := by positivity
  set β := Vs + gap / 2 with hβ
  -- the energy well at the level `U(d − α) + κ/2` survives `e^{β/ε}`
  have hβ2 : β < 2 * p.D * (p.potential (π - a) - p.potential a - η') / σP ^ 2 := by
    have : 2 * p.D * (p.potential (π - a) - p.potential a - η') / σP ^ 2 = Vs + gap := by
      rw [hVs, hgap, hη', hac]; ring
    rw [this, hβ]; linarith
  obtain ⟨γ₂, hγ₂, hev2⟩ := p.eventually_measure_exitTime_energyWell_le hσ hD h0 h1 hη'0 hη'1 hB
    hBc hβ2
  -- the cut well does not survive `e^{β/ε}`
  have hup := p.limsup_log_exitTime_cutWell_le hσ hD h0 h1 hη0 hd0 hd1 hdU hB hBc
  have hVs' : 2 * p.D * (p.potential (d - p.α) - p.potential a) / σP ^ 2 = Vs := by
    rw [hVs, hac]; ring
  rw [hVs', EReal.coe_ennreal_ofReal, max_eq_left hVs0] at hup
  have hev1 := eventually_lt_of_limsup_lt (lt_of_le_of_lt hup
    (EReal.coe_lt_coe_iff.mpr (by linarith : Vs < Vs + gap / 4)))
  set γ := min (gap / 4) γ₂ / 2 with hγ
  have hγ0 : 0 < γ := by positivity
  have hγ1 : 2 * γ ≤ gap / 4 := by rw [hγ]; linarith [min_le_left (gap / 4) γ₂]
  have hγ2 : 2 * γ ≤ γ₂ := by rw [hγ]; linarith [min_le_right (gap / 4) γ₂]
  have hev3 := eventually_exp_neg_div_le (c := γ) (η := 1 / 2) hγ0 (by norm_num)
  refine ⟨γ, hγ0, ?_⟩
  filter_upwards [hev1, hev2, hev3, self_mem_nhdsWithin] with ε h1ε h2ε h3ε (hε : 0 < ε)
  have hEτ : ∫⁻ ω, exitTime p.swingDrift N xs K (√ε) B hBc ω ∂P ≤
      ENNReal.ofReal (Real.exp ((Vs + gap / 4) / ε)) := le_exp_of_mul_log_le hε h1ε.le
  -- the horizon `e^{β/ε}` and the survival event
  set H : ℝ≥0 := ⟨Real.exp (β / ε), (Real.exp_pos _).le⟩ with hH
  have hH0 : 0 < (H : ℝ) := Real.exp_pos _
  set St := {ω | ∀ t, solMap p.swingDrift N xs (√ε • brownPath B hBc H ω) t ∈ K} with hSt
  have hSt_le : P St ≤ ENNReal.ofReal (Real.exp (-(gap / 4) / ε)) := by
    let _ : MeasurableSpace C(Icc (0 : ℝ) H, Fin 2 → ℝ) := borel _
    have : BorelSpace C(Icc (0 : ℝ) H, Fin 2 → ℝ) := ⟨rfl⟩
    have hcl : IsClosed {φ : C(Icc (0 : ℝ) H, Fin 2 → ℝ) | ∀ t, φ t ∈ K} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun t => (p.isCompact_cutWell η d).isClosed.preimage
        (continuous_eval_const t)
    have hStn : NullMeasurableSet St P :=
      nullMeasurableSet_brownPath hB hBc hH0 hL N xs (√ε) hcl.measurableSet
    have hmul : (H : ℝ≥0∞) * P St ≤ ENNReal.ofReal (Real.exp ((Vs + gap / 4) / ε)) := by
      calc (H : ℝ≥0∞) * P St = ∫⁻ _ in St, (H : ℝ≥0∞) ∂P := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ ω in St, exitTime p.swingDrift N xs K (√ε) B hBc ω ∂P :=
            lintegral_mono_ae ((ae_restrict_mem₀ hStn).mono fun ω hω =>
              le_exitTime_of_forall_mem hBc hL N xs (√ε) hω)
        _ ≤ _ := setLIntegral_le_lintegral _ _
        _ ≤ _ := hEτ
    have hHe : (H : ℝ≥0∞) = ENNReal.ofReal (Real.exp (β / ε)) := by
      rw [← ENNReal.ofReal_coe_nnreal]; rfl
    rw [hHe, mul_comm] at hmul
    have hdiv := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
      (Or.inl ENNReal.ofReal_ne_top)).mpr hmul
    refine hdiv.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
    congr 2
    rw [hβ]; ring
  -- a touch of the far boundary needs the comparison level before the exit
  have hincl : {ω | ∃ T : ℝ≥0, ∃ t : Icc (0 : ℝ) T,
      (∀ s : Icc (0 : ℝ) T, s ≤ t → solMap p.swingDrift N xs (√ε • brownPath B hBc T ω) s ∈ K) ∧
      solMap p.swingDrift N xs (√ε • brownPath B hBc T ω) t ∈ frontier K ∧
      r ≤ dist (solMap p.swingDrift N xs (√ε • brownPath B hBc T ω) t) ![d, 0]} ⊆
      St ∪ {ω | exitTime p.swingDrift N xs (p.energyWell η') (√ε) B hBc ω ≤
        ENNReal.ofReal (Real.exp (β / ε))} := by
    rintro ω ⟨T₀, t₀, hstay, hfr, hdist⟩
    have hE := p.le_swingEnergy_of_mem_frontier_cutWell h0 hη0 hd1 hr.le hfr hdist
    have hout : solMap p.swingDrift N xs (√ε • brownPath B hBc T₀ ω) t₀ ∉ p.energyWell η' :=
      fun h => by have := h.2.2; rw [hη'] at this; linarith
    by_cases hst : ω ∈ St
    · exact Or.inl hst
    right
    have hst' : ∃ t₁ : Icc (0 : ℝ) H,
        solMap p.swingDrift N xs (√ε • brownPath B hBc H ω) t₁ ∉ K := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hst hcon
    obtain ⟨t₁, ht₁⟩ := hst'
    -- the touch happens before `e^{β/ε}`
    have ht₀H : (t₀ : ℝ) ≤ H := by
      by_contra hlt
      rw [not_le] at hlt
      have ht₁T₀ : (t₁ : ℝ) ≤ T₀ := t₁.2.2.trans (hlt.le.trans t₀.2.2)
      have e1 := restrictPath_solMap_brownPath hBc hL N xs (√ε) (le_sup_left : T₀ ≤ T₀ ⊔ H) ω
      have e2 := restrictPath_solMap_brownPath hBc hL N xs (√ε) (le_sup_right : H ≤ T₀ ⊔ H) ω
      have v1 := DFunLike.congr_fun e1 ⟨t₁, t₁.2.1, ht₁T₀⟩
      have v2 := DFunLike.congr_fun e2 t₁
      have hin := hstay ⟨t₁, t₁.2.1, ht₁T₀⟩ (show (t₁ : ℝ) ≤ t₀ by linarith [t₁.2.2])
      rw [← v1] at hin
      have : restrictPath (le_sup_left : T₀ ≤ T₀ ⊔ H)
          (solMap p.swingDrift N xs (√ε • brownPath B hBc (T₀ ⊔ H) ω)) ⟨t₁, t₁.2.1, ht₁T₀⟩ =
          restrictPath (le_sup_right : H ≤ T₀ ⊔ H)
            (solMap p.swingDrift N xs (√ε • brownPath B hBc (T₀ ⊔ H) ω)) t₁ := rfl
      rw [this, v2] at hin
      exact ht₁ hin
    calc exitTime p.swingDrift N xs (p.energyWell η') (√ε) B hBc ω
        ≤ firstExit (p.energyWell η') (solMap p.swingDrift N xs (√ε • brownPath B hBc T₀ ω)) :=
          iInf_le _ T₀
      _ ≤ ENNReal.ofReal t₀ := iInf₂_le t₀ hout
      _ ≤ ENNReal.ofReal (Real.exp (β / ε)) := ENNReal.ofReal_le_ofReal ht₀H
  refine (measure_mono hincl).trans ((measure_union_le _ _).trans ?_)
  have hsum : Real.exp (-(gap / 4) / ε) + Real.exp (-γ₂ / ε) ≤ Real.exp (-γ / ε) := by
    have e1 : Real.exp (-(gap / 4) / ε) ≤ Real.exp (-(2 * γ) / ε) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hε.le)
    have e2 : Real.exp (-γ₂ / ε) ≤ Real.exp (-(2 * γ) / ε) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hε.le)
    have e3 : Real.exp (-(2 * γ) / ε) = Real.exp (-γ / ε) * Real.exp (-γ / ε) := by
      rw [← Real.exp_add]; congr 1; ring
    have := Real.exp_pos (-γ / ε)
    nlinarith
  calc P St + P {ω | exitTime p.swingDrift N xs (p.energyWell η') (√ε) B hBc ω ≤
        ENNReal.ofReal (Real.exp (β / ε))}
      ≤ ENNReal.ofReal (Real.exp (-(gap / 4) / ε)) + ENNReal.ofReal (Real.exp (-γ₂ / ε)) :=
        add_le_add hSt_le h2ε
    _ = ENNReal.ofReal (Real.exp (-(gap / 4) / ε) + Real.exp (-γ₂ / ε)) :=
        (ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsum

end Params

end powerlib.GFM.Noise
