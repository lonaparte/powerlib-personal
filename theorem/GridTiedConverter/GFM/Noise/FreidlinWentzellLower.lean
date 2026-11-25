import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ExitTimeLower
import theorem.GridTiedConverter.GFM.Noise.FreidlinWentzellWell

/-! # Exit of the noisy two-state GFM from its potential well: the exponential law

Domain module: the noisy two-state GFM with set-point noise
(`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzell.lean`) and the closed potential well
`Params.energyWell η` below the saddle level of
`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellWell.lean`. The mean exit time from the well
started at `x_s` grows at least at the rate of the boundary level,
`liminf_{ε→0⁺} ε log E τ_ε ≥ V̄(η) = 2D(ΔU − η)/σ_P²`, and with the upper bound of
`FreidlinWentzellWell.lean` the **exponential law** `ε log E τ_ε → 2D(ΔU − η)/σ_P²` holds. The
lower bound is the generic deterministic-time chain
`Stochastic.LDP.le_liminf_log_lintegral_exitTime` with `V = θ (2D/σ_P²) H`: leaving the well
from `y` costs at least `(2D/σ_P²)(H(x_u) − η − H(y))` (Hamilton–Jacobi bound `Params.fwQP_ge` at
the first boundary state), and the moment inequality comes from the dissipation of `H` — away
from `x_s` the noiseless flow loses a uniform amount of energy per unit time, so do the solutions
driven by paths of small sup norm (tube lemma), hence by paths of small Schilder rate, while a
path of rate `≥ c₁` pays `(1 − θ) c₁` beyond its energy gain.

Model boundary.
* The two-state model of `FreidlinWentzell.lean`: state `(δ, p)` on `Fin 2 → ℝ`, drift
  `Params.swingDrift`, noise column `(0, σ_P)`; `σ_P ≠ 0`, `D > 0`, `c₀ ≤ P_ref < c₀ + A`;
  `δ_s = arcsin s + α`, `s = (P_ref − c₀)/A`, `H = Params.swingEnergy`,
  `ΔU = U(π − arcsin s) − U(arcsin s)`; `0 < η < ΔU`. The exit time is
  `Stochastic.LDP.exitTime` of `Params.energyWell η` from `x_s = (δ_s, 0)` for a Brownian motion
  all of whose paths are continuous; `E τ_ε` its lower Lebesgue integral.
* Exit place (not stated). The boundary of the well is the energy level `H = H(x_u) − η` in the
  strip, a regular closed level curve (`∇H ≠ 0` on it) on which the Hamilton–Jacobi lower bound
  `(2D/σ_P²)(H − H(x_s))` of the quasi-potential is constant: the exit-place part of the exit
  theorem (concentration on the minimisers of `V(x_s, ·)` on the boundary) singles out no
  neighbourhood of the saddle. The drift enters across this boundary
  (`H'(x) b(x) = −D (p/M)² < 0`) except at the two turning points `p = 0`, where it is tangent
  and nonzero; the results here do not use Dembo–Zeitouni's non-characteristic boundary
  assumption. The domain whose exit concentrates at the saddle, the basin of attraction of
  `x_s`, is bounded by the stable manifolds of the saddles — an invariant (characteristic)
  boundary through equilibria of the drift, outside the hypotheses of Dembo–Zeitouni §5.7
  (Thm 5.7.11 assumes `⟨b, n⟩ < 0` on the boundary); it is not treated. The three-state model is
  not treated.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §2–3 (exit from a domain: `ε log E τ_ε → min_{∂D} V`); A. Dembo, O. Zeitouni,
*Large Deviations Techniques and Applications*, 2nd ed. (1998), Thm 5.7.11(a); LaSalle's
argument for the damped swing (`theorem/PowerSystem/Synchronous/DampedEAC.lean`).

Results.
* `Params.le_liminf_log_exitTime_energyWell` (**`liminf ε log E τ_ε ≥ 2D(ΔU − η)/σ_P²`**).
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

/-- **Leaving the well from one of its states costs the energy gap**: every path from `y` in the
well that leaves it (or lies in the closure of the leaving paths) has rate at least
`(2D/σ_P²)(H(x_u) − η − H(y))`; it reaches the boundary level (or a saddle angle, above it). -/
@[tmio M, powerlib_domain] private theorem fwRate_leave_ge (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) {η : ℝ} (hη : 0 < η) {y : Fin 2 → ℝ} (hy : y ∈ p.energyWell η) {T : ℝ≥0}
    {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ)}
    (hφ : φ ∈ closure {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) | ∃ t, φ t ∉ p.energyWell η}) :
    ENNReal.ofReal (2 * p.D / σP ^ 2 * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      η - p.swingEnergy y)) ≤ fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) y T φ := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  set N := columnsCLM fun _ : Fin 1 => swingColumn σP with hN
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  set W := p.energyWell η with hW
  set Hl := p.potential (π - a) - η with hHl
  set A := {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) | ∃ t, φ t ∉ W} with hA_def
  set W' := {x : Fin 2 → ℝ | π - a + p.α - 2 * π < x 0 ∧ x 0 < π - a + p.α ∧
    p.swingEnergy x < Hl} with hW'
  have hW'o : IsOpen W' :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt (continuous_apply 0) continuous_const).inter
        (isOpen_lt p.continuous_swingEnergy continuous_const))
  have hW'W : W' ⊆ W := fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  have hclA : closure A ⊆ {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) | ¬ MapsTo φ univ W'} := by
    refine closure_minimal (fun φ hφ hmaps => ?_) ?_
    · obtain ⟨t, ht⟩ := hφ
      exact ht (hW'W (hmaps (mem_univ t)))
    · exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hW'o).isClosed_compl
  rcases eq_or_ne (fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) y T φ) ⊤ with
    htop | htop
  · rw [htop]; exact le_top
  -- the path starts at `y`
  have hφ0 : φ ⟨0, le_rfl, T.coe_nonneg⟩ = y := by
    obtain ⟨w, hw⟩ := iInf_lt_iff.mp (lt_top_iff_ne_top.mpr htop)
    obtain ⟨hwφ, hwr⟩ := iInf_lt_iff.mp hw
    have hw0 := pathExt_zero_of_schilderRate_ne_top (ne_top_of_lt hwr)
    rw [← hwφ, solMap_spec hK]
    have : w ⟨0, le_rfl, T.coe_nonneg⟩ = 0 := by
      ext j; fin_cases j
      rw [← pathExt_of_mem w ⟨le_rfl, T.coe_nonneg⟩]
      exact hw0
    simp [this]
  -- a time at which the energy reaches the level
  obtain ⟨t₂, ht₂⟩ : ∃ t₂ : Icc (0 : ℝ) T, Hl ≤ p.swingEnergy (φ t₂) := by
    have hout := (hclA hφ)
    simp only [mem_ofPred_eq, MapsTo, mem_univ, true_implies, not_forall] at hout
    obtain ⟨t₁, ht₁⟩ := hout
    by_cases hE : Hl ≤ p.swingEnergy (φ t₁)
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
      have h1' := p.potential_le_swingEnergy (φ ⟨s, hsm⟩)
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
      have h1' := p.potential_le_swingEnergy (φ ⟨s, hsm⟩)
      have hsv' : φ ⟨s, hsm⟩ 0 = π - a + p.α := by
        rw [← pathExt_of_mem _ hsm]; exact hsv
      rw [hsv', show π - a + p.α - p.α = π - a by ring] at h1'
      linarith
  -- the rate dominates the Hamilton–Jacobi value at that state
  have hq := iInf_pushRate_le_of_le hK N y φ (t := ⟨t₂, t₂.2.1⟩) t₂.2.2
  have hhj := p.fwQP_ge hσ y (φ t₂)
  refine le_trans ?_ (hhj.trans hq)
  refine ENNReal.ofReal_le_ofReal ?_
  have hσ2 : 0 < σP ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- `fwRate_leave_ge` scaled by `θ ∈ [0, 1]`. -/
@[tmio M, powerlib_domain] private theorem fwRate_leave_ge_mul (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) {η : ℝ} (hη : 0 < η) {θ : ℝ} (hθ1 : θ ≤ 1)
    {y : Fin 2 → ℝ} (hy : y ∈ p.energyWell η) {T : ℝ≥0} {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ)}
    (hφ : φ ∈ closure {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) | ∃ t, φ t ∉ p.energyWell η}) :
    ENNReal.ofReal (θ * (2 * p.D / σP ^ 2) *
        (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η) -
      θ * (2 * p.D / σP ^ 2) * p.swingEnergy y) ≤
      fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) y T φ := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (p.fwRate_leave_ge hσ hD h0 hη hy hφ)
  have h2 : 0 ≤ p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η - p.swingEnergy y := by
    linarith [hy.2.2]
  have ha : 0 ≤ 2 * p.D / σP ^ 2 := by positivity
  have h3 : θ * (2 * p.D / σP ^ 2) ≤ 2 * p.D / σP ^ 2 := mul_le_of_le_one_left ha hθ1
  have h4 := mul_le_mul_of_nonneg_right h3 h2
  linarith

/-- **Small noise keeps the energy drop**: away from `x_s` (distance `≥ r`) every state of the
well loses at least `c > 0` of energy over `[0, 1]` along every solution driven by a path of
sup norm `< ρ` (the noiseless drop `Params.exists_swingEnergy_freeSwing_drop` and the tube
lemma). -/
@[tmio M, powerlib_domain] private theorem exists_tube (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref)
    (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : 0 < r) :
    ∃ c > 0, ∃ ρ > 0, ∀ y ∈ p.energyWell η,
      r ≤ dist y ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] →
      ∀ w : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ), ‖w‖ < ρ →
        p.swingEnergy (pathExt (solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP)
          y w) 1) ≤ p.swingEnergy y - c := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  obtain ⟨c, hc, hdrop⟩ := p.exists_swingEnergy_freeSwing_drop (σP := σP) hD h0 h1 hη hr
  set xs : Fin 2 → ℝ := ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] with hxs
  set Kt := p.energyWell η ∩ {y | r ≤ dist y xs} with hKt_def
  have hKt : IsCompact Kt :=
    (p.isCompact_energyWell η).inter_right (isClosed_le continuous_const
      (continuous_id.dist continuous_const))
  set g : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ) → (Fin 2 → ℝ) → ℝ := fun w y =>
    p.swingEnergy (pathExt (solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP)
      y w) 1) - p.swingEnergy y with hg_def
  have hg : Continuous fun z : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ) × (Fin 2 → ℝ) =>
      g z.1 z.2 := by
    have h := (continuous_solMap_uncurry hK (columnsCLM fun _ : Fin 1 => swingColumn σP)
      (T := 1)).comp (continuous_snd.prodMk continuous_fst)
    exact (p.continuous_swingEnergy.comp ((continuous_pathExt_apply 1).comp h)).sub
      (p.continuous_swingEnergy.comp continuous_snd)
  have hev : ∀ᶠ w in 𝓝 (0 : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ)), ∀ y ∈ Kt,
      g w y < -(c / 2) := by
    refine hKt.eventually_forall_of_forall_eventually fun y hy => ?_
    have h0' : g 0 y < -(c / 2) := by
      have := hdrop y hy.1 hy.2
      show p.swingEnergy (pathExt (p.freeSwing σP y 1) 1) - p.swingEnergy y < _
      linarith
    exact (hg.tendsto (0, y)).eventually (gt_mem_nhds h0')
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨c / 2, by positivity, ρ, hρ, fun y hy hry w hw => ?_⟩
  have := hball (show dist w 0 < ρ by rwa [dist_zero_right]) y ⟨hy, hry⟩
  simp only [hg_def] at this
  linarith

/-- **The moment inequality** (block length `1`): with `a = 2D/σ_P²`, `θ ∈ (0, 1)`, the energy
drop `c` of `exists_tube` for driving paths of norm `< ρ` away from `x_s` (distance `≥ r`), and
`H ≤ H(x_s) + ζ` within distance `r` of `x_s`, every path from `y` in the well satisfies
`J_y(φ) ≥ θ a H(φ(1)) − max(θ a H(y) − δ, θ a (H(x_s) + ζ))`, `δ = min(θ a c, (1 − θ) ρ²/4)`:
small-rate paths lose energy, the others pay for the gain at the full Hamilton–Jacobi rate. -/
@[tmio M, powerlib_domain] private theorem fwRate_moment_ge (hσ : σP ≠ 0) (hD : 0 < p.D)
    {η θ c ρ ζ r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hρ : 0 < ρ)
    (htube : ∀ y ∈ p.energyWell η,
      r ≤ dist y ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] →
      ∀ w : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ), ‖w‖ < ρ →
        p.swingEnergy (pathExt (solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP)
          y w) 1) ≤ p.swingEnergy y - c)
    (hnear : ∀ y, dist y ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] < r →
      p.swingEnergy y ≤ p.swingEnergy ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] + ζ)
    {y : Fin 2 → ℝ} (hy : y ∈ p.energyWell η)
    (φ : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 2 → ℝ)) :
    ENNReal.ofReal (θ * (2 * p.D / σP ^ 2) * p.swingEnergy (pathExt φ ((1 : ℝ≥0) : ℝ)) -
      max (θ * (2 * p.D / σP ^ 2) * p.swingEnergy y -
        min (θ * (2 * p.D / σP ^ 2) * c) ((1 - θ) * (ρ ^ 2 / 4)))
        (θ * (2 * p.D / σP ^ 2) * (p.swingEnergy
          ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] + ζ))) ≤
      fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) y 1 φ := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  set N := columnsCLM fun _ : Fin 1 => swingColumn σP with hN
  set xs : Fin 2 → ℝ := ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] with hxs
  set a := 2 * p.D / σP ^ 2 with ha
  have ha0 : 0 < a := by have : 0 < σP ^ 2 := by positivity
                         positivity
  set δ := min (θ * a * c) ((1 - θ) * (ρ ^ 2 / 4)) with hδ
  set J := fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) y 1 φ with hJ
  set Hφ := p.swingEnergy (pathExt φ ((1 : ℝ≥0) : ℝ)) with hHφ
  rcases eq_or_ne J ⊤ with htop | htop
  · rw [htop]; exact le_top
  -- the Hamilton–Jacobi bound at the end point
  have hend : φ ⟨((1 : ℝ≥0) : ℝ), (1 : ℝ≥0).coe_nonneg, le_rfl⟩ = pathExt φ ((1 : ℝ≥0) : ℝ) :=
    (pathExt_of_mem _ ⟨(1 : ℝ≥0).coe_nonneg, le_rfl⟩).symm
  have hHJ : ENNReal.ofReal (a * (Hφ - p.swingEnergy y)) ≤ J := by
    have hq := iInf_pushRate_le_of_le hK N y φ (t := 1) le_rfl
    have hhj := p.fwQP_ge hσ y (φ ⟨((1 : ℝ≥0) : ℝ), (1 : ℝ≥0).coe_nonneg, le_rfl⟩)
    have h := hhj.trans hq
    rw [hend] at h
    exact h
  have hJr : a * (Hφ - p.swingEnergy y) ≤ J.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal htop).mp hHJ
  by_cases hry : dist y xs < r
  · -- near `x_s`
    have hHy := hnear y hry
    refine le_trans ?_ hHJ
    refine ENNReal.ofReal_le_ofReal_iff'.mpr ?_
    have hm : θ * a * (p.swingEnergy xs + ζ) ≤ max (θ * a * p.swingEnergy y - δ)
        (θ * a * (p.swingEnergy xs + ζ)) := le_max_right _ _
    have hθa : 0 ≤ θ * a := by positivity
    have h1 : θ * a * Hφ - max (θ * a * p.swingEnergy y - δ) (θ * a * (p.swingEnergy xs + ζ)) ≤
        θ * a * (Hφ - p.swingEnergy y) := by nlinarith
    by_cases hle : p.swingEnergy y ≤ Hφ
    · left
      refine h1.trans ?_
      have h2 : 0 ≤ Hφ - p.swingEnergy y := by linarith
      have h3 : θ * a ≤ a := by nlinarith
      exact mul_le_mul_of_nonneg_right h3 h2
    · right
      refine h1.trans ?_
      have h2 : Hφ - p.swingEnergy y ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos hθa h2
  rw [not_lt] at hry
  have hmax : θ * a * p.swingEnergy y - δ ≤ max (θ * a * p.swingEnergy y - δ)
      (θ * a * (p.swingEnergy xs + ζ)) := le_max_left _ _
  by_cases hJc : J < ENNReal.ofReal (ρ ^ 2 / 4)
  · -- a small rate: the energy drops
    obtain ⟨w, hw⟩ := iInf_lt_iff.mp hJc
    obtain ⟨hwφ, hwr⟩ := iInf_lt_iff.mp hw
    have hwn := norm_le_of_schilderRate_lt hwr
    have hwρ : ‖w‖ < ρ := by
      refine lt_of_le_of_lt hwn ?_
      rw [Real.sqrt_lt' hρ]
      push_cast
      nlinarith
    have hdrop := htube y hy hry w hwρ
    rw [hwφ] at hdrop
    have hδc : δ ≤ θ * a * c := min_le_left _ _
    rw [ENNReal.ofReal_of_nonpos]
    · exact zero_le
    · have : θ * a * Hφ ≤ θ * a * (p.swingEnergy y - c) :=
        mul_le_mul_of_nonneg_left hdrop (by positivity)
      nlinarith
  · -- a large rate: it pays for the energy gain
    rw [not_lt] at hJc
    have hc₁ : ρ ^ 2 / 4 ≤ J.toReal := (ENNReal.ofReal_le_iff_le_toReal htop).mp hJc
    have hδ1 : δ ≤ (1 - θ) * (ρ ^ 2 / 4) := min_le_right _ _
    rw [← ENNReal.ofReal_toReal htop]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : θ * (a * (Hφ - p.swingEnergy y)) ≤ θ * J.toReal :=
      mul_le_mul_of_nonneg_left hJr hθ0.le
    have h2 : (1 - θ) * (ρ ^ 2 / 4) ≤ (1 - θ) * J.toReal :=
      mul_le_mul_of_nonneg_left hc₁ (by linarith)
    nlinarith

/-- **Lower bound for the mean exit time from the well** (two states, `σ_P ≠ 0`, `D > 0`,
`c₀ ≤ P_ref < c₀ + A`, `0 < η < ΔU`): the exit time `τ_ε` of the noisy model started at `x_s`
from `Params.energyWell η` satisfies `liminf_{ε→0⁺} ε log E τ_ε ≥ 2D(ΔU − η)/σ_P²`. The generic
chain `Stochastic.LDP.le_liminf_log_lintegral_exitTime` with `V = θ (2D/σ_P²) H`, block length
`1`: the exit inequality is `fwRate_leave_ge`, the moment inequality `fwRate_moment_ge`; then
`θ → 1` and the bottom level `H(x_s) + ζ`, `ζ → 0`. -/
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
  set N := columnsCLM fun _ : Fin 1 => swingColumn σP with hN
  set as := Real.arcsin ((p.Pref - p.c0) / p.A) with has
  set xs : Fin 2 → ℝ := ![as + p.α, 0] with hxs
  set W := p.energyWell η with hW
  set Hl := p.potential (π - as) - η with hHl
  set a := 2 * p.D / σP ^ 2 with ha
  have ha0 : 0 < a := by have : 0 < σP ^ 2 := by positivity
                         positivity
  have hA := p.A_pos
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hA).mpr (by linarith)
  have has0 : 0 ≤ as := Real.arcsin_nonneg.mpr hs0
  have has1 : as < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hxsE : p.swingEnergy xs = p.potential as := by simp [swingEnergy, hxs]
  have hxsW : xs ∈ W := by
    refine ⟨by simp [hxs]; linarith [Real.pi_pos], by simp [hxs]; linarith, ?_⟩
    rw [hxsE]
    linarith
  have hgap : 0 < Hl - p.swingEnergy xs := by rw [hxsE, hHl]; linarith
  set v := a * (Hl - p.swingEnergy xs) with hv
  have hv0 : 0 < v := mul_pos ha0 hgap
  have hvE : 2 * p.D * (p.potential (π - as) - p.potential as - η) / σP ^ 2 = v := by
    rw [hv, ha, hHl, hxsE]; ring
  rw [hvE, EReal.coe_ennreal_ofReal, max_eq_left hv0.le]
  refine le_of_forall_lt_imp_le_of_dense fun β₀ hβ₀ => ?_
  induction β₀ using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hβ₀ not_top_lt
  | coe β₀ =>
  have hβ₀' : β₀ < v := EReal.coe_lt_coe_iff.mp hβ₀
  obtain ⟨β, hβ₀β, hβ⟩ := exists_between (max_lt hβ₀' hv0)
  have hβ0 : 0 < β := lt_of_le_of_lt (le_max_right _ _) hβ₀β
  refine le_trans (EReal.coe_le_coe_iff.mpr (le_of_max_le_left hβ₀β.le)) ?_
  -- the parameters `θ`, `ζ`, `r`
  set g := v - β with hg
  have hg0 : 0 < g := by linarith
  have hgv : g < v := by linarith
  set θ := 1 - g / (4 * v) with hθ
  have hgv4 : g / (4 * v) < 1 / 4 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hθ0 : 0 < θ := by have : 0 < g / (4 * v) := by positivity
                         linarith
  have hθ1 : θ < 1 := by have : 0 < g / (4 * v) := by positivity
                         linarith
  set ζ := min ((Hl - p.swingEnergy xs) / 2) (g / (4 * a)) with hζ
  have hζ0 : 0 < ζ := lt_min (by linarith) (by positivity)
  have hζ1 : ζ ≤ (Hl - p.swingEnergy xs) / 2 := min_le_left _ _
  have hζ2 : ζ ≤ g / (4 * a) := min_le_right _ _
  obtain ⟨r, hr, hnear⟩ := Metric.continuousAt_iff.mp
    (p.continuous_swingEnergy.continuousAt (x := xs)) ζ hζ0
  have hnear' : ∀ y, dist y xs < r → p.swingEnergy y ≤ p.swingEnergy xs + ζ := by
    intro y hy
    have := hnear hy
    rw [Real.dist_eq, abs_lt] at this
    linarith
  obtain ⟨c, hc, ρ, hρ, htube⟩ := p.exists_tube (σP := σP) hD h0 h1 hη0 hr
  set δ := min (θ * a * c) ((1 - θ) * (ρ ^ 2 / 4)) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (mul_pos (by linarith) (by positivity))
  -- the generic chain
  have hT1 : (0 : ℝ) < ((1 : ℝ≥0) : ℝ) := by norm_num
  have hθa : 0 < θ * a := mul_pos hθ0 ha0
  have hx₀V : θ * a * p.swingEnergy xs ≤ θ * a * (p.swingEnergy xs + ζ) :=
    mul_le_mul_of_nonneg_left (by linarith) hθa.le
  have hexit : ∀ y ∈ W, ∀ φ ∈ closure {φ : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 2 → ℝ) |
      ∃ t, φ t ∉ W}, ENNReal.ofReal (θ * a * Hl - θ * a * p.swingEnergy y) ≤
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) y 1 φ :=
    fun y hy φ hφ => p.fwRate_leave_ge_mul hσ hD h0 hη0 hθ1.le hy hφ
  have hmom : ∀ y ∈ W, ∀ φ : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 2 → ℝ),
      ENNReal.ofReal (θ * a * p.swingEnergy (pathExt φ ((1 : ℝ≥0) : ℝ)) -
        max (θ * a * p.swingEnergy y - δ) (θ * a * (p.swingEnergy xs + ζ))) ≤
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) y 1 φ :=
    fun y hy φ => p.fwRate_moment_ge hσ hD hθ0 hθ1 hρ htube hnear' hy φ
  have hvb : θ * a * (p.swingEnergy xs + ζ) < θ * a * Hl :=
    mul_lt_mul_of_pos_left (by linarith) hθa
  have hgen := le_liminf_log_lintegral_exitTime hB hBc (p.isCompact_energyWell η) hxsW hT1 hK N
    (V := fun x => θ * a * p.swingEnergy x) (p.continuous_swingEnergy.const_mul _) hδ0 hvb
    hx₀V hexit (fun y hy φ _ => hmom y hy φ)
  refine le_trans ?_ hgen
  refine EReal.coe_le_coe_iff.mpr ?_
  -- `θ a (Hl − H(x_s) − ζ) ≥ β`
  have h1 : a * ζ ≤ g / 4 := by
    calc a * ζ ≤ a * (g / (4 * a)) := mul_le_mul_of_nonneg_left hζ2 ha0.le
      _ = g / 4 := by field_simp
  have h2 : θ * v = v - g / 4 := by rw [hθ]; field_simp
  have h3 : θ * a * Hl - θ * a * (p.swingEnergy xs + ζ) = θ * v - θ * (a * ζ) := by
    rw [hv]; ring
  rw [h3, h2]
  have h4 : θ * (a * ζ) ≤ g / 4 := by
    have : θ * (a * ζ) ≤ 1 * (a * ζ) :=
      mul_le_mul_of_nonneg_right hθ1.le (mul_nonneg ha0.le hζ0.le)
    linarith
  linarith

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
