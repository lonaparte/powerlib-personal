import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ControlledAction
import theorem.GridTiedConverter.GFM.Noise.FilterQuasiPotential
import theorem.PowerSystem.Synchronous.DampedEAC
import theorem.Dynamics.LagFilter

/-! # Escape exponents of the noisy GFM: the exact two-state value and the fast-filter limit

Domain module: the quasi-potential (Freidlin–Wentzell escape exponent) with set-point noise
(`GFM.Noise.Params.swingQP`, `GFM.Noise.Params3.setPointQP` of
`theorem/GridTiedConverter/GFM/Noise/FilterQuasiPotential.lean`) from the stable equilibrium to
the saddle. Two-state: exactly the Gibbs value `2D ΔU/σ_P²`. Three-state (VSM + power filter):
it tends to that value as the filter bandwidth `ω_c → ∞`. Lower bounds are the Hamilton–Jacobi
(sub)solutions of `GFM.Noise.FilterQuasiPotential`; upper bounds are explicit admissible pairs of
`theorem/Stochastic/ControlledAction.lean` joined by
`Stochastic.LDP.controlQuasiPotential_triangle`.

Model boundary.
* The models of `GFM.Noise.FilterQuasiPotential` (voltage source behind a lossy quasi-static
  line, export-positive power `P(δ) = c₀ + A sin(δ − α)`, per unit; two states `(δ, p)`,
  `p = M Δω`, noise column `(0, σ_P)`; three states `(δ, ω, P_f)`, noise column
  `(0, σ_P/M, 0)`), with `σ_P ≠ 0`, `D > 0` and `c₀ ≤ P_ref < c₀ + A`: two equilibria per
  period, the stable one `δ_s = arcsin s + α` and the saddle `δ_u = π − arcsin s + α`
  (`s = (P_ref − c₀)/A`), the saddle `δ_u` being the lower barrier of the well.
* The family over the bandwidth: `⟨p, ω_c⟩ : Params3` for `ω_c ∈ (0, ∞)` with fixed two-state
  parameters `p`; rest points `(δ, 0, P(δ))`.
* The noiseless two-state dynamics is read, inside proofs only (no connection statement), as the
  canonical swing model `Synchronous.SwingParams` with `P_m = P_ref`, `k₁ = c₀`, `k₂ = A`,
  `k₃ = α` (frequency `ω = p/M`), for its potential-well LaSalle estimate.
* Deterministic variational statements only; Freidlin–Wentzell's theorem (the link with the
  exit-time law) is not formalized.

Source: Freidlin, Wentzell, *Random Perturbations of Dynamical Systems* (1984), Ch. 4 (the
quasi-potential of a damped Hamiltonian system with momentum noise is the scaled energy; uphill
paths are time-reversed relaxation paths); `theorem/PowerSystem/Synchronous/DampedEAC.lean`
(LaSalle on the potential well); GFM counterpart study, note t2-noise item 7 (numerical
minimum-action values, e.g. `M = D = A = σ_P = 1`, `P_ref = c₀`: `V₂ = 4`, `V₃/V₂ ≈ 0.997, 0.97,
0.88, 0.59` at `ω_c = 100, 10, 3, 1`; scratch notes outside the repository).

Results.
* `Params.swingQP_saddle_eq`: `V₂((δ_s, 0), (δ_u, 0)) = 2D (U(δ_u) − U(δ_s))/σ_P²`,
  `U(δ) = Params.potential (δ − α)`. Upper bound: a noiseless trajectory from `(δ_u − η, 0)`
  (below the saddle level) converges to `(δ_s, 0)`; its momentum-flipped time reversal follows the
  feedback of the exact solution `(2D/σ_P²) H`, so its action is exactly `ΔW`
  (`Stochastic.LDP.controlAction_eq_of_feedback`); cubic Hermite angle profiles with vanishing
  action join its ends to the equilibria.
* `Params.limsup_setPointQP_le`, `Params.tendsto_setPointQP`: for the three-state models
  `V₃ → 2D (U(δ_u) − U(δ_s))/σ_P²` as `ω_c → ∞` (with `Params.liminf_setPointQP_ge`). Upper
  bound: the same two-state pieces followed by the filter (`P_f` solving
  `Ṗ_f = ω_c (P(δ) − P_f)`; lag `≤ |e₀| + 2G/ω_c` for a `G`-Lipschitz `P(δ(t))`), whose extra
  control `(P_f − P(δ))/σ_P` costs `O(1/ω_c)`, and an exact arrival at the saddle by an angle
  endBump `δ_u + l t²(1 − t)²` whose amplitude is fixed by the intermediate value theorem (possible
  once `ω_c² e^{−ω_c}` is small).
* Generic helpers (lag filter, quadratic action estimate, end bump) are in
  `theorem/Dynamics/LagFilter.lean`.
* Not formalized: `V₃ ≤ V₂` at a finite `ω_c` (observed numerically: `V₃ < V₂` at every tested
  `ω_c`); it needs an admissible three-state pair of action below `2D ΔU/σ_P²`, i.e. a
  construction exploiting the filter lag rather than suppressing it.
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real Set Filter Topology
open scoped ENNReal
open powerlib.Stochastic.LDP
open powerlib.Dynamics (State lagFilter hasDerivAt_lagFilter lagFilter_zero abs_lagFilter_sub_le
  integral_sq_add_le hasDerivAt_vec_two hasDerivWithinAt_vec_three endBump endBumpVel endBumpAcc
  hasDerivAt_endBump hasDerivAt_endBumpVel endBump_bounds sin_add_sub_sin_bounds
  integral_exp_mul_endBump_ge)

namespace Params

variable (p : Params)

/-! ## Short connecting pieces near a rest point -/

/-- Cubic Hermite angle on `[0, 1]` from `(δ_a, p_a)` to `(δ_b, p_b)` (velocities `p/M`). -/
private def gAngle (a b : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  a 0 + (b 0 - a 0) * (3 * t ^ 2 - 2 * t ^ 3) + a 1 / p.M * (t - 2 * t ^ 2 + t ^ 3) +
    b 1 / p.M * (t ^ 3 - t ^ 2)

private def gVel (a b : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  (b 0 - a 0) * (6 * t - 6 * t ^ 2) + a 1 / p.M * (1 - 4 * t + 3 * t ^ 2) +
    b 1 / p.M * (3 * t ^ 2 - 2 * t)

private def gAcc (a b : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  (b 0 - a 0) * (6 - 12 * t) + a 1 / p.M * (-4 + 6 * t) + b 1 / p.M * (6 * t - 2)

/-- The connecting path `(δ, M δ̇)`. -/
private def gPath (a b : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  ![p.gAngle a b t, p.M * p.gVel a b t]

/-- Its control: `σ_P u = M δ̈ + (P(δ) − P_ref) + D δ̇`. -/
private def gCtrl (σP : ℝ) (a b : Fin 2 → ℝ) (t : ℝ) : Fin 1 → ℝ :=
  ![(p.M * p.gAcc a b t + (p.c0 + p.A * Real.sin (p.gAngle a b t - p.α) - p.Pref) +
    p.D * p.gVel a b t) / σP]

@[tmio M, powerlib_domain] private theorem hasDerivAt_gAngle (a b : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (p.gAngle a b) (p.gVel a b t) t := by
  have h1 := hasDerivAt_id t
  have h2 := hasDerivAt_pow 2 t
  have h3 := hasDerivAt_pow 3 t
  have h := ((((h2.const_mul 3).sub (h3.const_mul 2)).const_mul (b 0 - a 0)).const_add
    (a 0)).add ((((h1.sub (h2.const_mul 2)).add h3).const_mul (a 1 / p.M)).add
      ((h3.sub h2).const_mul (b 1 / p.M)))
  convert h using 1
  · funext s; simp only [gAngle, Pi.add_apply, Pi.sub_apply, id]; ring
  · simp only [gVel]; push_cast; ring

@[tmio M, powerlib_domain] private theorem hasDerivAt_gVel (a b : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (p.gVel a b) (p.gAcc a b t) t := by
  have h1 := hasDerivAt_id t
  have h2 := hasDerivAt_pow 2 t
  have h := (((h1.const_mul 6).sub (h2.const_mul 6)).const_mul (b 0 - a 0)).add
    (((((h1.const_mul 4).const_sub 1).add (h2.const_mul 3)).const_mul (a 1 / p.M)).add
      (((h2.const_mul 3).sub (h1.const_mul 2)).const_mul (b 1 / p.M)))
  convert h using 1
  · funext s; simp only [gVel, Pi.add_apply, Pi.sub_apply, id]; ring
  · simp only [gAcc]; push_cast; ring

/-- The controlled two-state field in coordinates. -/
@[tmio M, powerlib_domain] private theorem controlField_swing (σP v : ℝ) (x : Fin 2 → ℝ) :
    controlField p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP) x ![v] =
      ![x 1 / p.M, p.Pref - (p.c0 + p.A * Real.sin (x 0 - p.α)) - p.D * (x 1 / p.M) +
        v * σP] := by
  ext i; fin_cases i <;> simp [controlField, swingDrift_apply, swingColumn]

@[tmio M, powerlib_domain] private theorem hasDerivAt_gPath {σP : ℝ} (hσ : σP ≠ 0)
    (a b : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (p.gPath a b) (controlField p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP)
      (p.gPath a b t) (p.gCtrl σP a b t)) t := by
  have hM := p.M_pos.ne'
  have e : controlField p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP) (p.gPath a b t)
      (p.gCtrl σP a b t) = ![p.gVel a b t, p.M * p.gAcc a b t] := by
    rw [gCtrl, controlField_swing]
    ext i; fin_cases i
    · simp [gPath]; field_simp
    · simp [gPath]; field_simp; ring
  rw [e]
  exact hasDerivAt_vec_two (p.hasDerivAt_gAngle a b t) ((p.hasDerivAt_gVel a b t).const_mul p.M)

@[tmio M, powerlib_domain] private theorem swingQP_le_glue {σP : ℝ} (hσ : σP ≠ 0)
    (a b : Fin 2 → ℝ) :
    p.swingQP σP a b ≤ ENNReal.ofReal (controlAction (p.gCtrl σP a b) 1) := by
  have hM := p.M_pos.ne'
  refine controlQuasiPotential_le zero_le_one ?_ ?_
    (fun t _ => (p.hasDerivAt_gPath hσ a b t).continuousAt.continuousWithinAt)
    (fun t _ => (p.hasDerivAt_gPath hσ a b t).hasDerivWithinAt) ?_
  · ext i; fin_cases i
    · simp [gPath, gAngle]
    · simp [gPath, gVel]; field_simp
  · ext i; fin_cases i
    · simp [gPath, gAngle]; ring
    · simp [gPath, gVel]; field_simp; ring
  · have : Continuous fun t => ∑ j, p.gCtrl σP a b t j ^ 2 := by
      simp only [gCtrl, gAngle, gVel, gAcc, Fin.sum_univ_one, Matrix.cons_val_zero]
      fun_prop
    exact this.intervalIntegrable 0 1

@[tmio M, powerlib_domain] private theorem continuous_glue (σP : ℝ) :
    Continuous fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => controlAction (p.gCtrl σP q.1 q.2) 1 := by
  have h : Continuous fun x : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ℝ =>
      ∑ j, p.gCtrl σP x.1.1 x.1.2 x.2 j ^ 2 := by
    simp only [gCtrl, gAngle, gVel, gAcc, Fin.sum_univ_one, Matrix.cons_val_zero]
    fun_prop
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 1)

@[tmio M, powerlib_domain] private theorem glue_rest (σP : ℝ) {δe : ℝ}
    (he : p.c0 + p.A * Real.sin (δe - p.α) = p.Pref) :
    controlAction (p.gCtrl σP ![δe, 0] ![δe, 0]) 1 = 0 := by
  unfold controlAction
  simp [gCtrl, gAngle, gVel, gAcc, he]

/-- **Cheap connections near a rest point**: for every `ε > 0` there is `ρ > 0` such that any two
states within `ρ` of the rest point `(δ_e, 0)` (`P(δ_e) = P_ref`) are joined with action below
`ε`. -/
@[tmio M, powerlib_domain] private theorem glue_small {σP : ℝ} (hσ : σP ≠ 0) {δe : ℝ}
    (he : p.c0 + p.A * Real.sin (δe - p.α) = p.Pref) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ a b : Fin 2 → ℝ, dist a ![δe, 0] < ρ → dist b ![δe, 0] < ρ →
      p.swingQP σP a b ≤ ENNReal.ofReal ε := by
  obtain ⟨ρ, hρ, h⟩ := Metric.continuousAt_iff.mp
    ((p.continuous_glue σP).continuousAt (x := (![δe, 0], ![δe, 0]))) ε hε
  refine ⟨ρ, hρ, fun a b ha hb => ?_⟩
  have hd : dist (a, b) (![δe, 0], ![δe, 0]) < ρ := by
    rw [Prod.dist_eq]; exact max_lt ha hb
  have := h hd
  simp only [p.glue_rest σP he, Real.dist_eq, sub_zero] at this
  exact (p.swingQP_le_glue hσ a b).trans (ENNReal.ofReal_le_ofReal (le_of_abs_le this.le))

/-! ## The uphill piece: a time-reversed relaxation -/

/-- The two-state model read as the canonical swing model (frequency `ω = p/M`). -/
private def swingModel : Synchronous.SwingParams := ⟨p.M, p.D, p.Pref, p.c0, p.A, p.α⟩

/-- `(δ, ω) ↦ (δ, −M ω)`: momentum coordinates with the frequency reversed. -/
private def flipMom (x : State 2) : Fin 2 → ℝ := ![x 0, -(p.M * x 1)]

@[tmio M, powerlib_domain] private theorem continuous_flipMom : Continuous p.flipMom := by
  have h0 := (Dynamics.contDiff_coord (n := 2) (k := 0) 0).continuous
  have h1 := (Dynamics.contDiff_coord (n := 2) (k := 0) 1).continuous
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact h0
  · exact (h1.const_mul p.M).neg

/-- LaSalle on the potential well of `swingModel` (`D > 0`): the generic
`Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel` with the well obligations
`Synchronous.SwingParams.eq_zero_of_lie_energy`, `Synchronous.SwingParams.eq_deltaS_of_rest`
(the same application is private in `theorem/PowerSystem/Synchronous/DampedEAC.lean`: a region of
attraction of a model field is outside the sentence language). -/
@[tmio TM, powerlib_domain] private theorem well_attracts (hD : 0 < p.D)
    (h : |p.Pref - p.c0| < p.A) {c : ℝ}
    (hc1 : c < p.swingModel.potential p.swingModel.deltaS p.swingModel.deltaU)
    (hc2 : c < p.swingModel.potential p.swingModel.deltaS (p.swingModel.deltaU - 2 * π)) :
    {x ∈ p.swingModel.wellWindow | p.swingModel.energy p.swingModel.deltaS x ≤ c} ⊆
      Flow.regionOfAttraction p.swingModel.field (PhasePlane.mk p.swingModel.deltaS 0) := by
  set sp := p.swingModel
  have hM : 0 < sp.M := p.M_pos
  have hk : 0 < sp.k₂ := p.A_pos
  refine Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel sp.isOpen_wellWindow
    sp.contDiff_field (sp.contDiff_energy _) (fun x _ => ?_) (sp.isCompact_wellSublevel hM hc1 hc2)
    (Dynamics.LaSalle.lasalle_condition_of_lieDeriv_mem sp.contDiff_field
      (h := fun x : State 2 => x 1) (Dynamics.contDiff_coord 1)
      (fun x hx => sp.eq_zero_of_lie_energy hM hD _ hx.2)
      (fun x hx hder => sp.eq_deltaS_of_rest hM hk h hx.1.1
        (sp.eq_zero_of_lie_energy hM hD _ hx.2) hder))
  rw [sp.field_eq_conservative]
  exact PhasePlane.Conservative.energy_lie_nonpos hM.ne' hD.le (sp.hasDerivAt_potential _) x

/-- **The uphill piece**: from a state `y` in the region of attraction of `(δ_s, 0)`, for every
`ρ > 0` there is `z` within `ρ` of `(δ_s, 0)` (momentum coordinates) joined to the flipped state
`(y₀, −M y₁)` with action `(2D/σ_P²)(H(flip y) − H(z))`: the momentum-flipped time reversal of
the relaxation from `y` follows the feedback of the exact solution. -/
@[tmio TM, powerlib_domain] private theorem relax_uphill {σP : ℝ} (hσ : σP ≠ 0) {y : State 2}
    (hy : y ∈ Flow.regionOfAttraction p.swingModel.field
      (PhasePlane.mk p.swingModel.deltaS 0)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (L : ℝ) (ψ : ℝ → Fin 2 → ℝ) (u : ℝ → Fin 1 → ℝ), 0 ≤ L ∧
      dist (ψ 0) ![p.swingModel.deltaS, 0] < ρ ∧ ψ L = p.flipMom y ∧
      ContinuousOn ψ (Icc 0 L) ∧ (∀ t ∈ Ico 0 L, HasDerivWithinAt ψ (controlField p.swingDrift
        (fun _ (_ : Fin 1) => swingColumn σP) (ψ t) (u t)) (Ici t) t) ∧
      ContinuousOn (fun t => u t 0) (Icc 0 L) ∧
      controlAction u L = 2 * p.D / σP ^ 2 * (p.swingEnergy (ψ L) - p.swingEnergy (ψ 0)) := by
  set sp := p.swingModel
  have hM := p.M_pos.ne'
  obtain ⟨⟨φ, hφ0, hφ⟩, hconv⟩ := hy
  have ht := hconv φ hφ0 hφ
  have hfs : p.flipMom (PhasePlane.mk sp.deltaS 0) = ![sp.deltaS, 0] := by
    ext i; fin_cases i <;> simp [flipMom]
  have ht' : Tendsto (fun t => p.flipMom (φ t)) atTop (𝓝 ![sp.deltaS, 0]) := by
    rw [← hfs]; exact (p.continuous_flipMom.tendsto _).comp ht
  obtain ⟨L, hL, hL0⟩ :=
    ((ht'.eventually (Metric.ball_mem_nhds _ hρ)).and (eventually_ge_atTop 0)).exists
  set ψ : ℝ → Fin 2 → ℝ := fun s => p.flipMom (φ (L - s)) with hψ
  set u : ℝ → Fin 1 → ℝ := fun s => ![2 * p.D * ψ s 1 / (σP * p.M)] with hu
  have hmaps : MapsTo (fun s => L - s) (Icc 0 L) (Ici 0) := fun s hs => by
    simp only [mem_Ici]; linarith [hs.2]
  have hcφ : ContinuousOn (fun s => φ (L - s)) (Icc 0 L) :=
    hφ.continuousOn.comp (continuousOn_const.sub continuousOn_id) hmaps
  have hcψ : ContinuousOn ψ (Icc 0 L) := p.continuous_flipMom.comp_continuousOn hcφ
  -- the feedback derivative along the reversed path
  have hder : ∀ s ∈ Ico 0 L, HasDerivWithinAt ψ (controlField p.swingDrift
      (fun _ (_ : Fin 1) => swingColumn σP) (ψ s) (u s)) (Ici s) s := by
    intro s hs
    have hpos : 0 < L - s := by linarith [hs.2]
    have hc : ∀ j : Fin 2, HasDerivAt (fun r => φ (L - r) j) (-(sp.field (φ (L - s)) j)) s :=
      fun j => (sp.coord_hasDerivAt hφ (show L - s ∈ Ici 0 from le_of_lt hpos)
        (Ici_mem_nhds hpos) j).comp_const_sub L s
    have e : controlField p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP) (ψ s) (u s) =
        ![-(sp.field (φ (L - s)) 0), -(p.M * -(sp.field (φ (L - s)) 1))] := by
      rw [show u s = ![2 * p.D * ψ s 1 / (σP * p.M)] from rfl, controlField_swing]
      ext i; fin_cases i
      · simp [ψ, flipMom, Synchronous.SwingParams.field_apply_zero]; field_simp
      · simp [ψ, flipMom, sp, swingModel, Synchronous.SwingParams.field_apply_one,
          Synchronous.SwingParams.accel, Synchronous.SwingParams.Pe]
        field_simp
        ring
    rw [e]
    exact (hasDerivAt_vec_two (hc 0) ((hc 1).const_mul p.M).neg).hasDerivWithinAt
  have hucont : ContinuousOn (fun s => u s 0) (Icc 0 L) := by
    have h1 : ContinuousOn (fun s => ψ s 1) (Icc 0 L) :=
      (continuous_apply 1).comp_continuousOn hcψ
    simp only [u, Matrix.cons_val_zero]
    exact (continuousOn_const.mul h1).div_const _
  have hint : IntervalIntegrable (fun s => ∑ j, u s j ^ 2) MeasureTheory.volume 0 L := by
    refine ContinuousOn.intervalIntegrable_of_Icc hL0 ?_
    simp only [Fin.sum_univ_one]
    exact hucont.pow 2
  have hfb : ∀ t ∈ Icc 0 L, ∀ j, u t j = ((2 * p.D / σP ^ 2) • p.swingEnergyDeriv (ψ t))
      (swingColumn σP) := by
    intro t _ j
    fin_cases j
    simp [u, swingEnergyDeriv, swingColumn]
    field_simp
  have hψ0 : ψ 0 = p.flipMom (φ L) := by simp [ψ]
  have hψL : ψ L = p.flipMom y := by simp [ψ, hφ0]
  have hW : ∀ t ∈ Icc 0 L, HasFDerivAt (fun x => 2 * p.D / σP ^ 2 * p.swingEnergy x)
      ((2 * p.D / σP ^ 2) • p.swingEnergyDeriv (ψ t)) (ψ t) :=
    fun t _ => (p.hasFDerivAt_swingEnergy (ψ t)).const_mul _
  have hHJ : ∀ t ∈ Icc 0 L, hjHamiltonian p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP)
      (ψ t) ((2 * p.D / σP ^ 2) • p.swingEnergyDeriv (ψ t)) = 0 :=
    fun t _ => p.hj_swing hσ (ψ t)
  clear_value ψ u
  have hS := controlAction_eq_of_feedback (b := p.swingDrift)
    (σ := fun _ (_ : Fin 1) => swingColumn σP) (W := fun x => 2 * p.D / σP ^ 2 * p.swingEnergy x)
    (dW := fun x => (2 * p.D / σP ^ 2) • p.swingEnergyDeriv x) (φ := ψ) (u := u) hL0 hW hHJ
    hfb hcψ hder hint
  have hS' : controlAction u L =
      2 * p.D / σP ^ 2 * (p.swingEnergy (p.flipMom y) - p.swingEnergy (p.flipMom (φ L))) := by
    rw [hS, hψ0, hψL]; ring
  exact ⟨L, ψ, u, hL0, by rw [hψ0]; exact hL, hψL, hcψ, hder, hucont, by
    rw [hS', hψ0, hψL]⟩

/-! ## The exact two-state escape exponent -/

@[tmio M, powerlib_domain] private theorem swingModel_potential (δ₀ δ : ℝ) :
    p.swingModel.potential δ₀ δ = p.potential (δ - p.α) - p.potential (δ₀ - p.α) := by
  simp only [Synchronous.SwingParams.potential, swingModel, Params.potential, toSM]
  ring

@[tmio M, powerlib_domain] private theorem swingEnergy_rest (δ : ℝ) :
    p.swingEnergy ![δ, 0] = p.potential (δ - p.α) := by
  simp [swingEnergy]

/-- `U(δ_s) < U(δ)` (`swingModel` potential) on `(δ_s, δ_u]`, the uphill side of the well. -/
@[tmio M, powerlib_domain] private theorem potential_lt_of_mem (h : |p.Pref - p.c0| < p.A)
    {a b : ℝ} (hab : a < b) (ha : p.swingModel.deltaS ≤ a) (hb : b ≤ p.swingModel.deltaU) :
    p.swingModel.potential p.swingModel.deltaS a <
      p.swingModel.potential p.swingModel.deltaS b := by
  set sp := p.swingModel
  have hk : 0 < sp.k₂ := p.A_pos
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (sp.potential sp.deltaS)
    (fun δ => sp.Pe δ - sp.Pm) hab
    (fun z _ => (sp.hasDerivAt_potential sp.deltaS z).continuousAt.continuousWithinAt)
    (fun z _ => sp.hasDerivAt_potential sp.deltaS z)
  have hpos := sp.Pm_lt_Pe_of_mem hk h (δ := ξ) ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  have hd : 0 < b - a := by linarith
  have : 0 < (sp.potential sp.deltaS b - sp.potential sp.deltaS a) / (b - a) := by
    rw [← hslope]; linarith
  have := (div_pos_iff_of_pos_right hd).mp this
  linarith

/-- **Upper bound** `V₂((δ_s, 0), (δ_u, 0)) ≤ (2D/σ_P²)(U(δ_u) − U(δ_s))`. -/
@[tmio M, powerlib_domain] private theorem swingQP_saddle_le {σP : ℝ} (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) :
    p.swingQP σP ![p.swingModel.deltaS, 0] ![p.swingModel.deltaU, 0] ≤
      ENNReal.ofReal (2 * p.D / σP ^ 2 *
        p.swingModel.potential p.swingModel.deltaS p.swingModel.deltaU) := by
  set sp := p.swingModel with hsp
  set δs := sp.deltaS with hδs
  set δu := sp.deltaU with hδu
  set c' := 2 * p.D / σP ^ 2 with hc'def
  have hk : 0 < sp.k₂ := p.A_pos
  have habs : |p.Pref - p.c0| < p.A := abs_lt.2 ⟨by linarith [p.A_pos], by linarith⟩
  have habs' : |sp.Pm - sp.k₁| < sp.k₂ := habs
  have hc' : 0 < c' := by have := pow_pos (abs_pos.mpr hσ) 2; rw [sq_abs] at this; positivity
  have hlt : δs < δu := sp.deltaS_lt_deltaU hk habs'
  have hsin : p.A * Real.sin (Real.arcsin sp.loadRatio) = p.Pref - p.c0 :=
    sp.sin_loadRatio hk habs'.le
  have hes : p.c0 + p.A * Real.sin (δs - p.α) = p.Pref := by
    have e : δs - p.α = Real.arcsin sp.loadRatio := by
      rw [hδs, Synchronous.SwingParams.deltaS]
      show Real.arcsin sp.loadRatio + p.α - p.α = _; ring
    rw [e]; linarith
  have heu : p.c0 + p.A * Real.sin (δu - p.α) = p.Pref := by
    have e : δu - p.α = π - Real.arcsin sp.loadRatio := by
      rw [hδu, Synchronous.SwingParams.deltaU]
      show π - Real.arcsin sp.loadRatio + p.α - p.α = _; ring
    rw [e, Real.sin_pi_sub]; linarith
  have hΔ : 0 < sp.potential δs δu := by
    have h := p.potential_lt_of_mem habs hlt le_rfl le_rfl
    rw [← hsp, ← hδs, Synchronous.SwingParams.potential_self] at h
    exact h
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set e := (ε : ℝ) / 4 with hedef
  have he : 0 < e := by have : (0 : ℝ) < ε := hε; positivity
  obtain ⟨ρs, hρs, hgs⟩ := p.glue_small hσ hes he
  obtain ⟨ρu, hρu, hgu⟩ := p.glue_small hσ heu he
  have hEc : Continuous p.swingEnergy :=
    continuous_iff_continuousAt.2 fun x => (p.hasFDerivAt_swingEnergy x).continuousAt
  obtain ⟨ρe, hρe, hE⟩ := Metric.continuousAt_iff.mp (hEc.continuousAt (x := ![δs, 0]))
    (e / c') (div_pos he hc')
  set η := min (ρu / 2) ((δu - δs) / 2) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηu : η < ρu := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηd : η < δu - δs := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set y : State 2 := PhasePlane.mk (δu - η) 0 with hydef
  have hyE : sp.energy δs y = sp.potential δs (δu - η) := by
    simp [y, PhasePlane.Conservative.separableEnergy]
  have hc1 : sp.energy δs y < sp.potential δs δu := by
    have h := p.potential_lt_of_mem habs (a := δu - η) (b := δu) (by linarith) (by linarith)
      le_rfl
    rw [← hsp] at h
    rw [hyE]; exact h
  have hc2 : sp.energy δs y < sp.potential δs (δu - 2 * π) := by
    rw [sp.potential_sub_two_pi]
    have : 0 ≤ sp.Pm - sp.k₁ := by show 0 ≤ p.Pref - p.c0; linarith
    nlinarith [Real.pi_pos]
  have hy : y ∈ {x ∈ sp.wellWindow | sp.energy δs x ≤ sp.energy δs y} := by
    refine ⟨⟨?_, ?_⟩, le_rfl⟩
    · simp only [y, PhasePlane.mk_apply_zero]
      linarith [sp.deltaU_sub_two_pi_lt_deltaS hk habs']
    · simp only [y, PhasePlane.mk_apply_zero]; linarith
  have hroa := p.well_attracts hD habs hc1 hc2 hy
  obtain ⟨L, ψ, u, hL0, hz, hψL, hcψ, hder, hucont, hS⟩ :=
    p.relax_uphill hσ hroa (lt_min hρs hρe)
  set z := ψ 0 with hzdef
  have hzV : p.swingQP σP z (p.flipMom y) ≤
      ENNReal.ofReal (2 * p.D / σP ^ 2 * (p.swingEnergy (p.flipMom y) - p.swingEnergy z)) := by
    rw [← hψL, ← hS]
    refine controlQuasiPotential_le hL0 rfl rfl hcψ hder
      (ContinuousOn.intervalIntegrable_of_Icc hL0 ?_)
    simp only [Fin.sum_univ_one]
    exact hucont.pow 2
  have hfy : p.flipMom y = ![δu - η, 0] := by
    ext i; fin_cases i <;> simp [flipMom, y]
  rw [hfy] at hzV
  have hV1 : p.swingQP σP ![δs, 0] z ≤ ENNReal.ofReal e :=
    hgs _ _ (by simp [hρs]) (lt_of_lt_of_le hz (min_le_left _ _))
  have hV3 : p.swingQP σP ![δu - η, 0] ![δu, 0] ≤ ENNReal.ofReal e := by
    refine hgu _ _ ?_ (by simp [hρu])
    rw [dist_pi_lt_iff hρu]
    intro i; fin_cases i
    · show dist (δu - η) δu < ρu
      rw [Real.dist_eq, show δu - η - δu = -η by ring, abs_neg, abs_of_pos hη]
      exact hηu
    · show dist (0 : ℝ) 0 < ρu
      simpa using hρu
  have hEz := hE (lt_of_lt_of_le hz (min_le_right _ _))
  rw [Real.dist_eq, abs_lt] at hEz
  have hmid : c' * (p.swingEnergy ![δu - η, 0] - p.swingEnergy z) ≤
      c' * sp.potential δs δu + e := by
    have h1' : p.swingEnergy ![δu - η, 0] - p.swingEnergy ![δs, 0] ≤ sp.potential δs δu := by
      have h := p.potential_lt_of_mem habs (a := δu - η) (b := δu) (by linarith) (by linarith)
        le_rfl
      rw [swingEnergy_rest, swingEnergy_rest, ← swingModel_potential, ← hsp]
      exact h.le
    have h2' : c' * (p.swingEnergy ![δs, 0] - p.swingEnergy z) ≤ e := by
      have := hEz.1
      have : p.swingEnergy ![δs, 0] - p.swingEnergy z < e / c' := by linarith
      calc c' * (p.swingEnergy ![δs, 0] - p.swingEnergy z) ≤ c' * (e / c') :=
            mul_le_mul_of_nonneg_left this.le hc'.le
        _ = e := by field_simp
    nlinarith
  have hm0 : 0 ≤ c' * sp.potential δs δu + e := by positivity
  calc p.swingQP σP ![δs, 0] ![δu, 0]
      ≤ p.swingQP σP ![δs, 0] z + (p.swingQP σP z ![δu - η, 0] +
          p.swingQP σP ![δu - η, 0] ![δu, 0]) :=
        (controlQuasiPotential_triangle _ _ _ z _).trans
          (add_le_add le_rfl (controlQuasiPotential_triangle _ _ _ _ _))
    _ ≤ ENNReal.ofReal e + (ENNReal.ofReal (c' * sp.potential δs δu + e) + ENNReal.ofReal e) :=
        add_le_add hV1 (add_le_add (hzV.trans (ENNReal.ofReal_le_ofReal hmid)) hV3)
    _ = ENNReal.ofReal (c' * sp.potential δs δu + 3 * e) := by
        rw [← ENNReal.ofReal_add hm0 he.le, ← ENNReal.ofReal_add he.le (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (c' * sp.potential δs δu) + ε := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by rw [hedef]; linarith)

/-- **The two-state escape exponent is the Gibbs value** (`D > 0`, `c₀ ≤ P_ref < c₀ + A`,
`σ_P ≠ 0`): from the stable equilibrium `δ_s = arcsin s + α` to the saddle
`δ_u = π − arcsin s + α` (`s = (P_ref − c₀)/A`),
`V₂((δ_s, 0), (δ_u, 0)) = 2D (U(δ_u) − U(δ_s))/σ_P²`, `U(δ) = Params.potential (δ − α)`. -/
@[tmio M, powerlib_domain] theorem swingQP_saddle_eq {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) :
    p.swingQP σP ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0]
        ![π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] =
      ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) / σP ^ 2) := by
  apply le_antisymm
  · have h := p.swingQP_saddle_le hσ hD h0 h1
    have hS : p.swingModel.deltaS = Real.arcsin ((p.Pref - p.c0) / p.A) + p.α := rfl
    have hU : p.swingModel.deltaU = π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α := rfl
    rw [swingModel_potential, hS, hU] at h
    simp only [add_sub_cancel_right] at h
    convert h using 2
    ring
  · have h := p.swingQP_rest_ge hσ (Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
      (π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    simpa only [add_sub_cancel_right] using h

end Params

/-! ## The three-state model following a two-state path -/

namespace Params3

/-- The controlled three-state field in coordinates. -/
@[tmio M, powerlib_domain] private theorem controlField_filter (p3 : Params3) (σP v : ℝ)
    (x : Fin 3 → ℝ) :
    controlField p3.sdeDrift (fun _ (_ : Fin 1) => p3.setPointColumn σP) x ![v] =
      ![x 1, (p3.Pref - x 2 - p3.D * x 1) / p3.M + v * (σP / p3.M),
        p3.ωc * (p3.c0 + p3.A * Real.sin (x 0 - p3.α) - x 2)] := by
  ext i; fin_cases i <;>
    simp [controlField, sdeDrift_apply, setPointColumn, VSMLPFLossy.Pe, toLossy]

/-- **Following a two-state path**: a two-state admissible pair `(φ, u)` on `[0, T]` (momentum
coordinates) and the filter driven by `h = P(δ)` give a three-state admissible pair from
`(δ(0), p(0)/M, z₀)` to `(δ(T), p(T)/M, z(T))`, with control `u + (z − P(δ))/σ_P`. -/
@[tmio TM, powerlib_domain] private theorem setPointQP_le_follow (p3 : Params3) {σP : ℝ}
    (hσ : σP ≠ 0) {T : ℝ} (hT : 0 ≤ T) {φ : ℝ → Fin 2 → ℝ} {u : ℝ → Fin 1 → ℝ}
    (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField p3.swingDrift
      (fun _ (_ : Fin 1) => Params.swingColumn σP) (φ t) (u t)) (Ici t) t)
    (hu : ContinuousOn (fun t => u t 0) (Icc 0 T)) {h : ℝ → ℝ} (hh : Continuous h)
    (hhφ : ∀ t ∈ Icc 0 T, h t = p3.c0 + p3.A * Real.sin (φ t 0 - p3.α)) (z₀ : ℝ) :
    p3.setPointQP σP ![φ 0 0, φ 0 1 / p3.M, z₀]
        ![φ T 0, φ T 1 / p3.M, lagFilter p3.ωc z₀ h T] ≤
      ENNReal.ofReal (1 / 2 * ∫ t in (0 : ℝ)..T,
        (u t 0 + (lagFilter p3.ωc z₀ h t - h t) / σP) ^ 2) := by
  have hM := p3.M_pos.ne'
  have hZ : ∀ t, HasDerivAt (lagFilter p3.ωc z₀ h) (p3.ωc * (h t - lagFilter p3.ωc z₀ h t)) t :=
    hasDerivAt_lagFilter hh
  have hZc : Continuous (lagFilter p3.ωc z₀ h) :=
    continuous_iff_continuousAt.2 fun t => (hZ t).continuousAt
  have hc0 : ContinuousOn (fun t => φ t 0) (Icc 0 T) := (continuous_apply 0).comp_continuousOn hc
  have hc1 : ContinuousOn (fun t => φ t 1) (Icc 0 T) := (continuous_apply 1).comp_continuousOn hc
  have hc3 : ContinuousOn (fun t => ![φ t 0, φ t 1 / p3.M, lagFilter p3.ωc z₀ h t])
      (Icc 0 T) := by
    refine continuousOn_pi.2 fun i => ?_
    fin_cases i
    · exact hc0
    · exact hc1.div_const _
    · exact hZc.continuousOn
  have hd3 : ∀ t ∈ Ico 0 T, HasDerivWithinAt
      (fun t => ![φ t 0, φ t 1 / p3.M, lagFilter p3.ωc z₀ h t])
      (controlField p3.sdeDrift (fun _ (_ : Fin 1) => p3.setPointColumn σP)
        ![φ t 0, φ t 1 / p3.M, lagFilter p3.ωc z₀ h t]
        ![u t 0 + (lagFilter p3.ωc z₀ h t - h t) / σP]) (Ici t) t := by
    intro t ht
    have h2 := hφ t ht
    have hu1 : u t = ![u t 0] := by ext j; fin_cases j; rfl
    rw [hu1, Params.controlField_swing] at h2
    have d0 : HasDerivWithinAt (fun r => φ r 0) (φ t 1 / p3.M) (Ici t) t := by
      simpa using hasDerivWithinAt_pi.1 h2 0
    have d1 : HasDerivWithinAt (fun r => φ r 1) (p3.Pref - (p3.c0 + p3.A *
        Real.sin (φ t 0 - p3.α)) - p3.D * (φ t 1 / p3.M) + u t 0 * σP) (Ici t) t := by
      simpa using hasDerivWithinAt_pi.1 h2 1
    have hht := hhφ t (Ico_subset_Icc_self ht)
    rw [controlField_filter]
    convert hasDerivWithinAt_vec_three d0 (d1.div_const p3.M) (hZ t).hasDerivWithinAt using 1
    ext i; fin_cases i
    · simp
    · simp [hht]; field_simp; ring
    · simp [hht]
  have hint : IntervalIntegrable (fun t => ∑ j, (![u t 0 + (lagFilter p3.ωc z₀ h t - h t) / σP] :
      Fin 1 → ℝ) j ^ 2) MeasureTheory.volume 0 T := by
    refine ContinuousOn.intervalIntegrable_of_Icc hT ?_
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    exact (hu.add ((hZc.continuousOn.sub hh.continuousOn).div_const _)).pow 2
  have hle := controlQuasiPotential_le (b := p3.sdeDrift)
    (σ := fun _ (_ : Fin 1) => p3.setPointColumn σP)
    (u := fun t => ![u t 0 + (lagFilter p3.ωc z₀ h t - h t) / σP]) hT rfl rfl hc3 hd3 hint
  rw [lagFilter_zero] at hle
  convert hle using 2 <;> first | rfl | simp [controlAction]

end Params3

/-- `P(δ)` along a two-state admissible pair is Lipschitz in time when the frequency is bounded. -/
@[tmio TM, powerlib_domain] private theorem Params.Pe_lipschitz_along (p : Params) {σP T V : ℝ}
    {φ : ℝ → Fin 2 → ℝ} {u : ℝ → Fin 1 → ℝ} (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField p.swingDrift
      (fun _ (_ : Fin 1) => Params.swingColumn σP) (φ t) (u t)) (Ici t) t)
    (hV : ∀ t ∈ Icc 0 T, |φ t 1 / p.M| ≤ V) :
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |(p.c0 + p.A * Real.sin (φ s 0 - p.α)) -
      (p.c0 + p.A * Real.sin (φ t 0 - p.α))| ≤ p.A * V * |s - t| := by
  have hc0 : ContinuousOn (fun t => φ t 0) (Icc 0 T) := (continuous_apply 0).comp_continuousOn hc
  have key : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a ≤ b → |φ b 0 - φ a 0| ≤ V * (b - a) := by
    intro a ha b hb hab
    have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun r => φ r 0)
      (f' := fun r => φ r 1 / p.M) (C := V) (hc0.mono (Icc_subset_Icc ha.1 hb.2))
      (fun r hr => by
        have h2 := hφ r ⟨ha.1.trans hr.1, hr.2.trans_le hb.2⟩
        have hu1 : u r = ![u r 0] := by ext j; fin_cases j; rfl
        rw [hu1, Params.controlField_swing] at h2
        simpa using hasDerivWithinAt_pi.1 h2 0)
      (fun r hr => by
        rw [Real.norm_eq_abs]; exact hV r ⟨ha.1.trans hr.1, hr.2.le.trans hb.2⟩) b
      ⟨hab, le_rfl⟩
    simpa [Real.norm_eq_abs] using this
  have hA := p.A_pos
  intro s hs t ht
  have hsin : ∀ x y : ℝ, |(p.c0 + p.A * Real.sin (x - p.α)) - (p.c0 + p.A * Real.sin (y - p.α))| ≤
      p.A * |x - y| := fun x y => by
    have := Real.abs_sin_sub_sin_le (x - p.α) (y - p.α)
    rw [show p.c0 + p.A * Real.sin (x - p.α) - (p.c0 + p.A * Real.sin (y - p.α)) =
      p.A * (Real.sin (x - p.α) - Real.sin (y - p.α)) by ring, abs_mul, abs_of_pos hA]
    calc p.A * |Real.sin (x - p.α) - Real.sin (y - p.α)| ≤ p.A * |x - p.α - (y - p.α)| :=
          mul_le_mul_of_nonneg_left this hA.le
      _ = p.A * |x - y| := by ring_nf
  rcases le_total s t with hst | hst
  · have := key s hs t ht hst
    rw [abs_sub_comm (φ t 0)] at this
    calc _ ≤ p.A * |φ s 0 - φ t 0| := hsin _ _
      _ ≤ p.A * (V * (t - s)) := mul_le_mul_of_nonneg_left this hA.le
      _ = p.A * V * |s - t| := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; ring
  · have := key t ht s hs hst
    calc _ ≤ p.A * |φ s 0 - φ t 0| := hsin _ _
      _ ≤ p.A * (V * (s - t)) := mul_le_mul_of_nonneg_left this hA.le
      _ = p.A * V * |s - t| := by rw [abs_of_nonneg (by linarith)]; ring

namespace Params

/-- A two-state pair from an angle profile `δ` with derivatives `v`, `a`. -/
@[tmio M, powerlib_domain] private theorem hasDerivAt_anglePath (p : Params) {σP : ℝ}
    (hσ : σP ≠ 0) {δ v a : ℝ → ℝ} {t : ℝ} (hδ : HasDerivAt δ (v t) t)
    (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun t => ![δ t, p.M * v t]) (controlField p.swingDrift
      (fun _ (_ : Fin 1) => swingColumn σP) ![δ t, p.M * v t]
      ![(p.M * a t + (p.c0 + p.A * Real.sin (δ t - p.α) - p.Pref) + p.D * v t) / σP]) t := by
  have hM := p.M_pos.ne'
  rw [controlField_swing]
  convert hasDerivAt_vec_two hδ (hv.const_mul p.M) using 1
  ext i; fin_cases i
  · simp; field_simp
  · simp; field_simp; ring

end Params

namespace Params3

/-- The endBump of amplitude `l` (`|l| ≤ Λ`) whose filter ends at `P_ref`: action bound. -/
@[tmio TM, powerlib_domain] private theorem setPointQP_bump_le (p3 : Params3) {σP : ℝ}
    (hσ : σP ≠ 0) {δe : ℝ} (he : p3.c0 + p3.A * Real.sin (δe - p3.α) = p3.Pref) {Λ l z₃ : ℝ}
    (hΛ : 0 < Λ) (hlΛ : |l| ≤ Λ)
    (hFl : lagFilter p3.ωc z₃ (fun s => p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α)) 1 =
      p3.Pref) :
    p3.setPointQP σP ![δe, 0, z₃] ![δe, 0, p3.Pref] ≤ ENNReal.ofReal
      (1 / 2 * ((2 * p3.M + p3.A + p3.D) * Λ / |σP|) ^ 2 +
        ((2 * p3.M + p3.A + p3.D) * Λ / |σP| * (|z₃ - p3.Pref| + 2 * (p3.A * Λ) / p3.ωc) /
          |σP| + (|z₃ - p3.Pref| + 2 * (p3.A * Λ) / p3.ωc) ^ 2 / σP ^ 2)) := by
  have hω0 := p3.ωc_pos
  have hM := p3.M_pos
  have hA := p3.A_pos
  have hD := p3.D_nonneg
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = δe - p3.α := ⟨_, rfl⟩
  have hlt : ∀ s, p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α) - p3.Pref =
      p3.A * (Real.sin (θ + l * endBump s) - Real.sin θ) := fun s => by
    rw [← he, hθ]; ring_nf
  obtain ⟨U, hUdef⟩ : ∃ U, U = (2 * p3.M + p3.A + p3.D) * Λ / |σP| := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = |z₃ - p3.Pref| + 2 * (p3.A * Λ) / p3.ωc := ⟨_, rfl⟩
  have hpath : ∀ t, HasDerivAt (fun t => ![δe + l * endBump t, p3.M * (l * endBumpVel t)])
      (controlField p3.swingDrift (fun _ (_ : Fin 1) => Params.swingColumn σP)
        ![δe + l * endBump t, p3.M * (l * endBumpVel t)]
        ![(p3.M * (l * endBumpAcc t) + (p3.c0 + p3.A * Real.sin (δe + l * endBump t - p3.α) -
          p3.Pref) + p3.D * (l * endBumpVel t)) / σP]) t := fun t =>
    Params.hasDerivAt_anglePath p3.toParams hσ (δ := fun t => δe + l * endBump t)
      (v := fun t => l * endBumpVel t) (a := fun t => l * endBumpAcc t) (hasDerivAt_endBump l δe t)
      (hasDerivAt_endBumpVel l t)
  have hfc : Continuous fun t => (p3.M * (l * endBumpAcc t) + (p3.c0 + p3.A *
      Real.sin (δe + l * endBump t - p3.α) - p3.Pref) + p3.D * (l * endBumpVel t)) / σP := by
    unfold endBump endBumpVel endBumpAcc; fun_prop
  have hhc : Continuous fun s => p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α) := by
    unfold endBump; fun_prop
  have hfollow := setPointQP_le_follow p3 hσ zero_le_one
    (φ := fun t => ![δe + l * endBump t, p3.M * (l * endBumpVel t)])
    (fun t _ => (hpath t).continuousAt.continuousWithinAt) (fun t _ => (hpath t).hasDerivWithinAt)
    (by simpa using hfc.continuousOn) hhc (fun t _ => by simp) z₃
  have hs0 : (![δe + l * endBump 0, p3.M * (l * endBumpVel 0) / p3.M, z₃] : Fin 3 → ℝ) =
      ![δe, 0, z₃] := by
    ext i; fin_cases i <;> simp [endBump, endBumpVel]
  have hs1 : (![δe + l * endBump 1, p3.M * (l * endBumpVel 1) / p3.M, lagFilter p3.ωc z₃
      (fun s => p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α)) 1] : Fin 3 → ℝ) =
      ![δe, 0, p3.Pref] := by
    ext i; fin_cases i
    · simp [endBump]
    · simp [endBumpVel]; norm_num
    · exact hFl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hfollow
  rw [hs0, hs1] at hfollow
  refine hfollow.trans (ENNReal.ofReal_le_ofReal ?_)
  have hZc : Continuous
      (lagFilter p3.ωc z₃ fun s => p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α)) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_lagFilter hhc t).continuousAt
  have hUb : ∀ t ∈ Icc (0 : ℝ) 1, |(p3.M * (l * endBumpAcc t) + (p3.c0 + p3.A *
      Real.sin (δe + l * endBump t - p3.α) - p3.Pref) + p3.D * (l * endBumpVel t)) / σP| ≤ U := by
    intro t ht
    obtain ⟨hb0, hb1, hv, ha⟩ := endBump_bounds ht
    rw [hlt t, abs_div, hUdef]
    refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
    have h1 : |p3.M * (l * endBumpAcc t)| ≤ p3.M * (Λ * 2) := by
      rw [abs_mul, abs_mul, abs_of_pos hM]; gcongr
    have h2 : |p3.A * (Real.sin (θ + l * endBump t) - Real.sin θ)| ≤ p3.A * Λ := by
      rw [abs_mul, abs_of_pos hA]; gcongr
      calc |Real.sin (θ + l * endBump t) - Real.sin θ| ≤ |θ + l * endBump t - θ| :=
            Real.abs_sin_sub_sin_le _ _
        _ = |l| * endBump t := by rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hb0]
        _ ≤ Λ * 1 := mul_le_mul hlΛ hb1 hb0 hΛ.le
        _ = Λ := mul_one _
    have h3 : |p3.D * (l * endBumpVel t)| ≤ p3.D * (Λ * 1) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hD]; gcongr
    calc _ ≤ |p3.M * (l * endBumpAcc t)| + |p3.A * (Real.sin (θ + l * endBump t) - Real.sin θ)| +
          |p3.D * (l * endBumpVel t)| := abs_add_three _ _ _
      _ ≤ _ := by nlinarith
  have hV : ∀ t ∈ Icc (0 : ℝ) 1, |(fun t => ![δe + l * endBump t, p3.M * (l * endBumpVel t)]) t 1 /
      p3.M| ≤ Λ := by
    intro t ht
    obtain ⟨-, -, hv, -⟩ := endBump_bounds ht
    show |p3.M * (l * endBumpVel t) / p3.M| ≤ Λ
    rw [mul_div_cancel_left₀ _ hM.ne', abs_mul]
    calc |l| * |endBumpVel t| ≤ Λ * 1 := mul_le_mul hlΛ hv (abs_nonneg _) hΛ.le
      _ = Λ := mul_one _
  have hLip := p3.toParams.Pe_lipschitz_along (fun t _ => (hpath t).continuousAt.continuousWithinAt)
    (fun t _ => (hpath t).hasDerivWithinAt) hV
  have hEb : ∀ t ∈ Icc (0 : ℝ) 1, |lagFilter p3.ωc z₃ (fun s => p3.c0 + p3.A *
      Real.sin (δe + l * endBump s - p3.α)) t -
        (p3.c0 + p3.A * Real.sin (δe + l * endBump t - p3.α))| ≤ E := by
    intro t ht
    have := abs_lagFilter_sub_le (ω := p3.ωc) (z₀ := z₃) (G := p3.A * Λ) hω0 hhc
      (mul_nonneg hA.le hΛ.le)
      (fun s hs t ht => by simpa using hLip s hs t ht) ht
    rw [hEdef]; simpa [endBump, he] using this
  have hsq := integral_sq_add_le zero_le_one hfc.continuousOn
    (w := fun t => lagFilter p3.ωc z₃ (fun s => p3.c0 + p3.A *
      Real.sin (δe + l * endBump s - p3.α)) t -
        (p3.c0 + p3.A * Real.sin (δe + l * endBump t - p3.α)))
    ((hZc.sub hhc).continuousOn) hUb hEb hσ
  have hfU : 1 / 2 * ∫ t in (0 : ℝ)..1, ((p3.M * (l * endBumpAcc t) + (p3.c0 + p3.A *
      Real.sin (δe + l * endBump t - p3.α) - p3.Pref) + p3.D * (l * endBumpVel t)) / σP) ^ 2 ≤
      1 / 2 * U ^ 2 := by
    have : ∫ t in (0 : ℝ)..1, ((p3.M * (l * endBumpAcc t) + (p3.c0 + p3.A *
        Real.sin (δe + l * endBump t - p3.α) - p3.Pref) + p3.D * (l * endBumpVel t)) / σP) ^ 2 ≤
        ∫ t in (0 : ℝ)..1, U ^ 2 := by
      refine intervalIntegral.integral_mono_on zero_le_one ((hfc.pow 2).intervalIntegrable _ _)
        intervalIntegrable_const fun t ht => ?_
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hUb t ht) 2
    simp only [intervalIntegral.integral_const, sub_zero, one_smul] at this
    linarith
  simp only [one_mul] at hsq
  subst hUdef hEdef
  linarith

/-- **Exact arrival at the saddle**: from `(δ_e, 0, z₃)` at a saddle rest point (`P(δ_e) = P_ref`,
`cos(δ_e − α) < 0`) the state `(δ_e, 0, P_ref)` is reached by an angle endBump
`δ_e + l t²(1 − t)²` on `[0, 1]`, the amplitude `l ∈ [−Λ, Λ]` chosen by the intermediate value
theorem, as soon as `72 ω_c² e^{−ω_c} |z₃ − P_ref| ≤ A κ Λ` (`κ = −cos(δ_e − α)`); the action is
bounded through `integral_sq_add_le`. -/
@[tmio TM, powerlib_domain] private theorem setPointQP_saddle_fix (p3 : Params3) {σP : ℝ}
    (hσ : σP ≠ 0) {δe : ℝ} (he : p3.c0 + p3.A * Real.sin (δe - p3.α) = p3.Pref)
    (hcos : Real.cos (δe - p3.α) < 0) {Λ : ℝ} (hΛ : 0 < Λ)
    (hΛκ : Λ ≤ -Real.cos (δe - p3.α) / 2) (hω2 : 2 ≤ p3.ωc) {z₃ : ℝ}
    (hz : 72 * p3.ωc ^ 2 * Real.exp (-p3.ωc) * |z₃ - p3.Pref| ≤
      p3.A * -Real.cos (δe - p3.α) * Λ) :
    p3.setPointQP σP ![δe, 0, z₃] ![δe, 0, p3.Pref] ≤ ENNReal.ofReal
      (1 / 2 * ((2 * p3.M + p3.A + p3.D) * Λ / |σP|) ^ 2 +
        ((2 * p3.M + p3.A + p3.D) * Λ / |σP| * (|z₃ - p3.Pref| + 2 * (p3.A * Λ) / p3.ωc) /
          |σP| + (|z₃ - p3.Pref| + 2 * (p3.A * Λ) / p3.ωc) ^ 2 / σP ^ 2)) := by
  have hω0 : 0 < p3.ωc := by linarith
  have hM := p3.M_pos
  have hA := p3.A_pos
  have hD := p3.D_nonneg
  set ω := p3.ωc with hωdef
  set θ := δe - p3.α with hθ
  have hκ0 : 0 < -Real.cos θ := by linarith
  have hlt : ∀ l s, p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α) - p3.Pref =
      p3.A * (Real.sin (θ + l * endBump s) - Real.sin θ) := fun l s => by
    rw [← he, hθ]; ring_nf
  have hcf : ∀ l, Continuous fun s => Real.exp (ω * s) *
      (p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α)) := fun l => by unfold endBump; fun_prop
  -- `ω ∫₀¹ e^{ωs} ds = e^ω − 1`
  have hexp1 : ω * ∫ s in (0 : ℝ)..1, Real.exp (ω * s) = Real.exp ω - 1 := by
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => Real.exp (ω * s) / ω)
        (Real.exp (ω * s)) s := fun s _ => by
      have := (((hasDerivAt_id' s).const_mul ω).exp).div_const ω
      convert this using 1; field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun s =>
      Real.exp (ω * s)).intervalIntegrable 0 1)]
    simp; field_simp
  have hee : Real.exp (-ω) * Real.exp ω = 1 := by rw [← Real.exp_add]; simp
  set F : ℝ → ℝ := fun l => lagFilter ω z₃
    (fun s => p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α)) 1 with hFdef
  have hFe : ∀ l, F l - p3.Pref = Real.exp (-ω) * ((z₃ - p3.Pref) + ω * ∫ s in (0 : ℝ)..1,
      Real.exp (ω * s) * (p3.A * (Real.sin (θ + l * endBump s) - Real.sin θ))) := by
    intro l
    have hsub : ω * ∫ s in (0 : ℝ)..1,
        Real.exp (ω * s) * (p3.A * (Real.sin (θ + l * endBump s) - Real.sin θ)) =
        ω * (∫ s in (0 : ℝ)..1, Real.exp (ω * s) *
          (p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α))) - p3.Pref * (Real.exp ω - 1) := by
      have h1 : ∫ s in (0 : ℝ)..1, Real.exp (ω * s) *
          (p3.A * (Real.sin (θ + l * endBump s) - Real.sin θ)) =
          ∫ s in (0 : ℝ)..1, (Real.exp (ω * s) *
            (p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α)) -
              p3.Pref * Real.exp (ω * s)) :=
        intervalIntegral.integral_congr fun s _ => by
          show _ = _; rw [← hlt]; ring
      rw [h1, intervalIntegral.integral_sub ((hcf l).intervalIntegrable 0 1)
        ((by fun_prop : Continuous fun s => p3.Pref * Real.exp (ω * s)).intervalIntegrable 0 1),
        intervalIntegral.integral_const_mul, ← hexp1]
      ring
    simp only [hFdef, lagFilter, mul_one]
    rw [hsub]
    linear_combination p3.Pref * hee
  have hFc : Continuous F := by
    have h : Continuous (Function.uncurry fun l s : ℝ => Real.exp (ω * s) *
        (p3.c0 + p3.A * Real.sin (δe + l * endBump s - p3.α))) := by
      simp only [endBump]; fun_prop
    have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume) h 0 1
    simp only [hFdef, lagFilter, mul_one]
    fun_prop
  have hI := integral_exp_mul_endBump_ge hω2
  -- the two signs
  have hsgn : ∀ l, |l| ≤ Λ → ∀ s ∈ Icc (0 : ℝ) 1, |l * endBump s| ≤ -Real.cos θ / 2 := by
    intro l hl s hs
    obtain ⟨hb0, hb1, -, -⟩ := endBump_bounds hs
    rw [abs_mul, abs_of_nonneg hb0]
    calc |l| * endBump s ≤ Λ * 1 := mul_le_mul hl hb1 hb0 hΛ.le
      _ ≤ _ := by linarith
  have hneg : F Λ - p3.Pref ≤ 0 := by
    rw [hFe]
    have hle : ∫ s in (0 : ℝ)..1, Real.exp (ω * s) * (p3.A * (Real.sin (θ + Λ * endBump s) -
        Real.sin θ)) ≤ ∫ s in (0 : ℝ)..1, p3.A * (Real.cos θ / 2 * Λ) *
          (Real.exp (ω * s) * endBump s) := by
      refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun s hs => ?_
      · exact (by unfold endBump; fun_prop : Continuous fun s => Real.exp (ω * s) *
          (p3.A * (Real.sin (θ + Λ * endBump s) - Real.sin θ))).intervalIntegrable _ _
      · exact (by unfold endBump; fun_prop : Continuous fun s => p3.A * (Real.cos θ / 2 * Λ) *
          (Real.exp (ω * s) * endBump s)).intervalIntegrable _ _
      · obtain ⟨hb0, -, -, -⟩ := endBump_bounds hs
        have := (sin_add_sub_sin_bounds (hsgn Λ (by rw [abs_of_pos hΛ]) s hs)).1
          (mul_nonneg hΛ.le hb0)
        have he0 := Real.exp_pos (ω * s)
        calc Real.exp (ω * s) * (p3.A * (Real.sin (θ + Λ * endBump s) - Real.sin θ))
            ≤ Real.exp (ω * s) * (p3.A * (Real.cos θ / 2 * (Λ * endBump s))) := by gcongr
          _ = _ := by ring
    rw [intervalIntegral.integral_const_mul] at hle
    have hc' : p3.A * (Real.cos θ / 2 * Λ) < 0 := by
      have : Real.cos θ / 2 * Λ < 0 := by nlinarith
      nlinarith
    have h2 := mul_le_mul_of_nonpos_left hI hc'.le
    have h3 : ω * (p3.A * (Real.cos θ / 2 * Λ)) * (Real.exp ω / (36 * ω ^ 3)) =
        -(p3.A * -Real.cos θ * Λ / (72 * ω ^ 2)) * Real.exp ω := by field_simp; ring
    have h4 : Real.exp (-ω) * |z₃ - p3.Pref| ≤ p3.A * -Real.cos θ * Λ / (72 * ω ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have hfin : (z₃ - p3.Pref) + ω * ∫ s in (0 : ℝ)..1, Real.exp (ω * s) *
        (p3.A * (Real.sin (θ + Λ * endBump s) - Real.sin θ)) ≤
        |z₃ - p3.Pref| - p3.A * -Real.cos θ * Λ / (72 * ω ^ 2) * Real.exp ω := by
      have := mul_le_mul_of_nonneg_left (hle.trans h2) hω0.le
      nlinarith [le_abs_self (z₃ - p3.Pref)]
    have := mul_le_mul_of_nonneg_left hfin (Real.exp_pos (-ω)).le
    have e2 : Real.exp (-ω) * (|z₃ - p3.Pref| - p3.A * -Real.cos θ * Λ / (72 * ω ^ 2) *
        Real.exp ω) = Real.exp (-ω) * |z₃ - p3.Pref| - p3.A * -Real.cos θ * Λ / (72 * ω ^ 2) := by
      linear_combination (-(p3.A * -Real.cos θ * Λ / (72 * ω ^ 2))) * hee
    linarith
  have hpos : 0 ≤ F (-Λ) - p3.Pref := by
    rw [hFe]
    have hle : ∫ s in (0 : ℝ)..1, p3.A * (Real.cos θ / 2 * -Λ) * (Real.exp (ω * s) * endBump s) ≤
        ∫ s in (0 : ℝ)..1, Real.exp (ω * s) * (p3.A * (Real.sin (θ + -Λ * endBump s) -
          Real.sin θ)) := by
      refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun s hs => ?_
      · exact (by unfold endBump; fun_prop : Continuous fun s => p3.A * (Real.cos θ / 2 * -Λ) *
          (Real.exp (ω * s) * endBump s)).intervalIntegrable _ _
      · exact (by unfold endBump; fun_prop : Continuous fun s => Real.exp (ω * s) *
          (p3.A * (Real.sin (θ + -Λ * endBump s) - Real.sin θ))).intervalIntegrable _ _
      · obtain ⟨hb0, -, -, -⟩ := endBump_bounds hs
        have := (sin_add_sub_sin_bounds (hsgn (-Λ) (by rw [abs_neg, abs_of_pos hΛ]) s hs)).2
          (by nlinarith)
        have he0 := Real.exp_pos (ω * s)
        calc p3.A * (Real.cos θ / 2 * -Λ) * (Real.exp (ω * s) * endBump s)
            = Real.exp (ω * s) * (p3.A * (Real.cos θ / 2 * (-Λ * endBump s))) := by ring
          _ ≤ _ := by gcongr
    rw [intervalIntegral.integral_const_mul] at hle
    have hc' : 0 < p3.A * (Real.cos θ / 2 * -Λ) := by
      have : 0 < Real.cos θ / 2 * -Λ := by nlinarith
      positivity
    have h2 := mul_le_mul_of_nonneg_left hI hc'.le
    have h4 : Real.exp (-ω) * |z₃ - p3.Pref| ≤ p3.A * -Real.cos θ * Λ / (72 * ω ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h3 : ω * (p3.A * (Real.cos θ / 2 * -Λ)) * (Real.exp ω / (36 * ω ^ 3)) =
        (p3.A * -Real.cos θ * Λ / (72 * ω ^ 2)) * Real.exp ω := by field_simp; ring
    have hfin : |z₃ - p3.Pref| * 0 + (p3.A * -Real.cos θ * Λ / (72 * ω ^ 2) * Real.exp ω -
        |z₃ - p3.Pref|) ≤ (z₃ - p3.Pref) + ω * ∫ s in (0 : ℝ)..1, Real.exp (ω * s) *
          (p3.A * (Real.sin (θ + -Λ * endBump s) - Real.sin θ)) := by
      have := mul_le_mul_of_nonneg_left (h2.trans hle) hω0.le
      nlinarith [neg_abs_le (z₃ - p3.Pref)]
    have := mul_le_mul_of_nonneg_left hfin (Real.exp_pos (-ω)).le
    have e2 : Real.exp (-ω) * (|z₃ - p3.Pref| * 0 + (p3.A * -Real.cos θ * Λ / (72 * ω ^ 2) *
        Real.exp ω - |z₃ - p3.Pref|)) =
        p3.A * -Real.cos θ * Λ / (72 * ω ^ 2) - Real.exp (-ω) * |z₃ - p3.Pref| := by
      linear_combination (p3.A * -Real.cos θ * Λ / (72 * ω ^ 2)) * hee
    linarith
  obtain ⟨l, hlmem, hFl⟩ := intermediate_value_Icc' (by linarith : -Λ ≤ Λ) hFc.continuousOn
    (show p3.Pref ∈ Icc (F Λ) (F (-Λ)) from ⟨by linarith, by linarith⟩)
  exact p3.setPointQP_bump_le hσ he hΛ (abs_le.2 ⟨hlmem.1, hlmem.2⟩) hFl

end Params3

namespace Params3

/-- **Following a two-state pair, with bounds**: the three-state pair of `setPointQP_le_follow`
ends at a filter value within `e₀ + 2AV/ω_c` of `P(δ(T))`, and its action exceeds the two-state
action by at most `T (U E/|σ_P| + E²/σ_P²)`, `E = e₀ + 2AV/ω_c`. -/
@[tmio TM, powerlib_domain] private theorem follow_bound (p3 : Params3) {σP : ℝ} (hσ : σP ≠ 0)
    {T U V z₀ e₀ : ℝ} (hT : 0 ≤ T) {φ : ℝ → Fin 2 → ℝ} {u : ℝ → Fin 1 → ℝ}
    (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField p3.swingDrift
      (fun _ (_ : Fin 1) => Params.swingColumn σP) (φ t) (u t)) (Ici t) t)
    (hu : ContinuousOn (fun t => u t 0) (Icc 0 T)) (hU : ∀ t ∈ Icc 0 T, |u t 0| ≤ U)
    (hV : ∀ t ∈ Icc 0 T, |φ t 1 / p3.M| ≤ V)
    (he₀ : |z₀ - (p3.c0 + p3.A * Real.sin (φ 0 0 - p3.α))| ≤ e₀) :
    ∃ Z : ℝ, |Z - (p3.c0 + p3.A * Real.sin (φ T 0 - p3.α))| ≤ e₀ + 2 * (p3.A * V) / p3.ωc ∧
      p3.setPointQP σP ![φ 0 0, φ 0 1 / p3.M, z₀] ![φ T 0, φ T 1 / p3.M, Z] ≤
        ENNReal.ofReal (controlAction u T + T * (U * (e₀ + 2 * (p3.A * V) / p3.ωc) / |σP| +
          (e₀ + 2 * (p3.A * V) / p3.ωc) ^ 2 / σP ^ 2)) := by
  have hA := p3.A_pos
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0 ⟨le_rfl, hT⟩)
  set h : ℝ → ℝ := fun s => p3.c0 + p3.A * Real.sin (φ (projIcc 0 T hT s) 0 - p3.α) with hhdef
  have hφc : Continuous fun s => φ (projIcc 0 T hT s) :=
    hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun s => (projIcc 0 T hT s).2
  have hhc : Continuous h := by
    simp only [hhdef]
    exact continuous_const.add (continuous_const.mul
      (Real.continuous_sin.comp (((continuous_apply 0).comp hφc).sub continuous_const)))
  have hhφ : ∀ t ∈ Icc 0 T, h t = p3.c0 + p3.A * Real.sin (φ t 0 - p3.α) := fun t ht => by
    simp [hhdef, projIcc_of_mem hT ht]
  have hLip := p3.toParams.Pe_lipschitz_along hc hφ hV
  have hlag : ∀ t ∈ Icc 0 T, |lagFilter p3.ωc z₀ h t - h t| ≤ e₀ + 2 * (p3.A * V) / p3.ωc := by
    intro t ht
    have := abs_lagFilter_sub_le (ω := p3.ωc) (z₀ := z₀) (G := p3.A * V) p3.ωc_pos hhc
      (mul_nonneg hA.le hV0) (fun s hs r hr => by rw [hhφ s hs, hhφ r hr]; exact hLip s hs r hr) ht
    rw [hhφ 0 ⟨le_rfl, hT⟩] at this
    linarith
  refine ⟨lagFilter p3.ωc z₀ h T, by rw [← hhφ T ⟨hT, le_rfl⟩]; exact hlag T ⟨hT, le_rfl⟩, ?_⟩
  refine (p3.setPointQP_le_follow hσ hT hc hφ hu hhc hhφ z₀).trans (ENNReal.ofReal_le_ofReal ?_)
  have hZc : Continuous (lagFilter p3.ωc z₀ h) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_lagFilter hhc t).continuousAt
  have hsq := integral_sq_add_le hT hu (w := fun t => lagFilter p3.ωc z₀ h t - h t)
    (hZc.sub hhc).continuousOn hU hlag hσ
  have hact : controlAction u T = 1 / 2 * ∫ t in (0 : ℝ)..T, u t 0 ^ 2 := by
    simp [controlAction]
  rw [hact]
  exact hsq

end Params3

namespace Params

variable (p : Params)

@[tmio M, powerlib_domain] private theorem gPath_zero (a b : Fin 2 → ℝ) : p.gPath a b 0 = a := by
  have hM := p.M_pos.ne'
  ext i; fin_cases i
  · simp [gPath, gAngle]
  · simp [gPath, gVel]; field_simp

@[tmio M, powerlib_domain] private theorem gPath_one (a b : Fin 2 → ℝ) : p.gPath a b 1 = b := by
  have hM := p.M_pos.ne'
  ext i; fin_cases i
  · simp [gPath, gAngle]; ring
  · simp [gPath, gVel]; field_simp; ring

/-- Bounds on a compact interval for the connecting pieces. -/
@[tmio M, powerlib_domain] private theorem glue_bounds (σP : ℝ) (a b : Fin 2 → ℝ) :
    ∃ U V : ℝ, (∀ t ∈ Icc (0 : ℝ) 1, |p.gCtrl σP a b t 0| ≤ U) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, |p.gPath a b t 1 / p.M| ≤ V := by
  have hu : Continuous fun t => p.gCtrl σP a b t 0 := by
    simp only [gCtrl, gAngle, gVel, gAcc, Matrix.cons_val_zero]; fun_prop
  have hv : Continuous fun t => p.gPath a b t 1 / p.M := by
    simp only [gPath, gVel, Matrix.cons_val_one]; fun_prop
  obtain ⟨U, hU⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.continuousOn
  obtain ⟨V, hV⟩ := isCompact_Icc.exists_bound_of_continuousOn hv.continuousOn
  exact ⟨U, V, fun t ht => by simpa using hU t ht, fun t ht => by
    have := hV t ht; rwa [Real.norm_eq_abs] at this⟩

end Params

namespace Params3

/-- **Assembly**: three two-state pairs (rest point `δ_s` → … → rest point `δ_u`) followed by the
filter, then the exact endBump at the saddle. -/
@[tmio TM, powerlib_domain] private theorem fast_assembly (p3 : Params3) {σP : ℝ} (hσ : σP ≠ 0)
    {δs δu : ℝ} (hes : p3.c0 + p3.A * Real.sin (δs - p3.α) = p3.Pref)
    (heu : p3.c0 + p3.A * Real.sin (δu - p3.α) = p3.Pref) (hcosu : Real.cos (δu - p3.α) < 0)
    {T₁ T₂ T₃ Us Vs Λ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) (hT₃ : 0 ≤ T₃)
    (hUs : 0 ≤ Us) (hVs : 0 ≤ Vs) {φ₁ φ₂ φ₃ : ℝ → Fin 2 → ℝ} {u₁ u₂ u₃ : ℝ → Fin 1 → ℝ}
    (hc₁ : ContinuousOn φ₁ (Icc 0 T₁)) (hc₂ : ContinuousOn φ₂ (Icc 0 T₂))
    (hc₃ : ContinuousOn φ₃ (Icc 0 T₃))
    (hφ₁ : ∀ t ∈ Ico 0 T₁, HasDerivWithinAt φ₁ (controlField p3.swingDrift
      (fun _ (_ : Fin 1) => Params.swingColumn σP) (φ₁ t) (u₁ t)) (Ici t) t)
    (hφ₂ : ∀ t ∈ Ico 0 T₂, HasDerivWithinAt φ₂ (controlField p3.swingDrift
      (fun _ (_ : Fin 1) => Params.swingColumn σP) (φ₂ t) (u₂ t)) (Ici t) t)
    (hφ₃ : ∀ t ∈ Ico 0 T₃, HasDerivWithinAt φ₃ (controlField p3.swingDrift
      (fun _ (_ : Fin 1) => Params.swingColumn σP) (φ₃ t) (u₃ t)) (Ici t) t)
    (hu₁ : ContinuousOn (fun t => u₁ t 0) (Icc 0 T₁))
    (hu₂ : ContinuousOn (fun t => u₂ t 0) (Icc 0 T₂))
    (hu₃ : ContinuousOn (fun t => u₃ t 0) (Icc 0 T₃))
    (hU₁ : ∀ t ∈ Icc 0 T₁, |u₁ t 0| ≤ Us) (hU₂ : ∀ t ∈ Icc 0 T₂, |u₂ t 0| ≤ Us)
    (hU₃ : ∀ t ∈ Icc 0 T₃, |u₃ t 0| ≤ Us)
    (hV₁ : ∀ t ∈ Icc 0 T₁, |φ₁ t 1 / p3.M| ≤ Vs) (hV₂ : ∀ t ∈ Icc 0 T₂, |φ₂ t 1 / p3.M| ≤ Vs)
    (hV₃ : ∀ t ∈ Icc 0 T₃, |φ₃ t 1 / p3.M| ≤ Vs)
    (h10 : φ₁ 0 = ![δs, 0]) (h12 : φ₂ 0 = φ₁ T₁) (h23 : φ₃ 0 = φ₂ T₂) (h3T : φ₃ T₃ = ![δu, 0])
    (hΛ : 0 < Λ) (hΛκ : Λ ≤ -Real.cos (δu - p3.α) / 2) (hω2 : 2 ≤ p3.ωc)
    (hz : 72 * p3.ωc ^ 2 * Real.exp (-p3.ωc) * (2 * (p3.A * Vs) / p3.ωc +
      2 * (p3.A * Vs) / p3.ωc + 2 * (p3.A * Vs) / p3.ωc) ≤ p3.A * -Real.cos (δu - p3.α) * Λ) :
    p3.setPointQP σP ![δs, 0, p3.Pref] ![δu, 0, p3.Pref] ≤ ENNReal.ofReal
      ((controlAction u₁ T₁ + T₁ * (Us * (2 * (p3.A * Vs) / p3.ωc) / |σP| +
          (2 * (p3.A * Vs) / p3.ωc) ^ 2 / σP ^ 2)) +
        ((controlAction u₂ T₂ + T₂ * (Us * (2 * (2 * (p3.A * Vs) / p3.ωc)) / |σP| +
          (2 * (2 * (p3.A * Vs) / p3.ωc)) ^ 2 / σP ^ 2)) +
        ((controlAction u₃ T₃ + T₃ * (Us * (3 * (2 * (p3.A * Vs) / p3.ωc)) / |σP| +
          (3 * (2 * (p3.A * Vs) / p3.ωc)) ^ 2 / σP ^ 2)) +
        (1 / 2 * ((2 * p3.M + p3.A + p3.D) * Λ / |σP|) ^ 2 +
          ((2 * p3.M + p3.A + p3.D) * Λ / |σP| * (3 * (2 * (p3.A * Vs) / p3.ωc) +
            2 * (p3.A * Λ) / p3.ωc) / |σP| + (3 * (2 * (p3.A * Vs) / p3.ωc) +
              2 * (p3.A * Λ) / p3.ωc) ^ 2 / σP ^ 2))))) := by
  have hω0 := p3.ωc_pos
  have hA := p3.A_pos
  have hD := p3.D_nonneg
  have hM := p3.M_pos
  have hσa : 0 < |σP| := abs_pos.mpr hσ
  obtain ⟨E, hEdef⟩ : ∃ E, E = 2 * (p3.A * Vs) / p3.ωc := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  -- piece 1
  obtain ⟨Z1, hZ1, hV1⟩ := p3.follow_bound hσ (z₀ := p3.Pref) (e₀ := 0) hT₁ hc₁ hφ₁ hu₁ hU₁ hV₁
    (by rw [h10]; simp [hes])
  -- piece 2
  obtain ⟨Z2, hZ2, hV2⟩ := p3.follow_bound hσ (z₀ := Z1) (e₀ := 0 + E) hT₂ hc₂ hφ₂ hu₂ hU₂ hV₂
    (by rw [h12]; exact hZ1.trans_eq (by rw [hEdef]))
  -- piece 3
  obtain ⟨Z3, hZ3, hV3⟩ := p3.follow_bound hσ (z₀ := Z2) (e₀ := 0 + E + E) hT₃ hc₃ hφ₃ hu₃ hU₃ hV₃
    (by rw [h23]; exact hZ2.trans_eq (by rw [hEdef]))
  rw [← hEdef] at hV1 hV2 hV3 hZ3
  rw [h3T] at hZ3 hV3
  simp only [Matrix.cons_val_zero, heu] at hZ3
  have hZ3' : |Z3 - p3.Pref| ≤ 3 * E := by linarith
  -- piece 4
  have hz' : 72 * p3.ωc ^ 2 * Real.exp (-p3.ωc) * |Z3 - p3.Pref| ≤
      p3.A * -Real.cos (δu - p3.α) * Λ := by
    refine le_trans ?_ hz
    rw [← hEdef]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hV4 := p3.setPointQP_saddle_fix hσ heu hcosu hΛ hΛκ hω2 hz'
  -- the points
  rw [h10] at hV1
  rw [h12] at hV2
  rw [h23] at hV3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_div] at hV1 hV3
  -- triangle inequalities
  have hT := (controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hV1
    ((controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hV2
      ((controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hV3 hV4)))))
  refine hT.trans ?_
  have n1 := controlAction_nonneg u₁ hT₁
  have n2 := controlAction_nonneg u₂ hT₂
  have n3 := controlAction_nonneg u₃ hT₃
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h4 : (2 * p3.M + p3.A + p3.D) * Λ / |σP| * (|Z3 - p3.Pref| + 2 * (p3.A * Λ) / p3.ωc) /
      |σP| + (|Z3 - p3.Pref| + 2 * (p3.A * Λ) / p3.ωc) ^ 2 / σP ^ 2 ≤
      (2 * p3.M + p3.A + p3.D) * Λ / |σP| * (3 * E + 2 * (p3.A * Λ) / p3.ωc) / |σP| +
        (3 * E + 2 * (p3.A * Λ) / p3.ωc) ^ 2 / σP ^ 2 := by
    gcongr
  rw [hEdef] at h4
  have hx3 : 2 * (p3.A * Vs) / p3.ωc + 2 * (p3.A * Vs) / p3.ωc + 2 * (p3.A * Vs) / p3.ωc =
      3 * (2 * (p3.A * Vs) / p3.ωc) := by ring
  have hx2 : 2 * (p3.A * Vs) / p3.ωc + 2 * (p3.A * Vs) / p3.ωc =
      2 * (2 * (p3.A * Vs) / p3.ωc) := by ring
  rw [hEdef]
  simp only [zero_add]
  rw [hx3, hx2]
  linarith

end Params3

namespace Params

variable (p : Params)

/-- **Fast filter, upper bound (core)**: for every `ε > 0`, eventually in `ω_c`, the three-state
escape exponent is at most the two-state value plus `ε`. -/
@[tmio TM, powerlib_domain] private theorem limsup_core {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ωc : Ioi (0 : ℝ) in atTop, (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).setPointQP σP
        ![p.swingModel.deltaS, 0, p.c0 + p.A * Real.sin (p.swingModel.deltaS - p.α)]
        ![p.swingModel.deltaU, 0, p.c0 + p.A * Real.sin (p.swingModel.deltaU - p.α)] ≤
      ENNReal.ofReal (2 * p.D / σP ^ 2 *
        p.swingModel.potential p.swingModel.deltaS p.swingModel.deltaU + ε) := by
  set sp := p.swingModel with hsp
  set δs := sp.deltaS with hδs
  set δu := sp.deltaU with hδu
  set c' := 2 * p.D / σP ^ 2 with hc'def
  have hk : 0 < sp.k₂ := p.A_pos
  have habs : |p.Pref - p.c0| < p.A := abs_lt.2 ⟨by linarith [p.A_pos], by linarith⟩
  have habs' : |sp.Pm - sp.k₁| < sp.k₂ := habs
  have hc' : 0 < c' := by have := pow_pos (abs_pos.mpr hσ) 2; rw [sq_abs] at this; positivity
  have hlt : δs < δu := sp.deltaS_lt_deltaU hk habs'
  have hsin : p.A * Real.sin (Real.arcsin sp.loadRatio) = p.Pref - p.c0 :=
    sp.sin_loadRatio hk habs'.le
  have hes : p.c0 + p.A * Real.sin (δs - p.α) = p.Pref := by
    have e : δs - p.α = Real.arcsin sp.loadRatio := by
      rw [hδs, Synchronous.SwingParams.deltaS]
      show Real.arcsin sp.loadRatio + p.α - p.α = _; ring
    rw [e]; linarith
  have heu : p.c0 + p.A * Real.sin (δu - p.α) = p.Pref := by
    have e : δu - p.α = π - Real.arcsin sp.loadRatio := by
      rw [hδu, Synchronous.SwingParams.deltaU]
      show π - Real.arcsin sp.loadRatio + p.α - p.α = _; ring
    rw [e, Real.sin_pi_sub]; linarith
  have hΔ : 0 < sp.potential δs δu := by
    have h := p.potential_lt_of_mem habs hlt le_rfl le_rfl
    rw [← hsp, ← hδs, Synchronous.SwingParams.potential_self] at h
    exact h
  have hM := p.M_pos
  have hA := p.A_pos
  have hcosu : Real.cos (δu - p.α) < 0 := by
    have e : δu - p.α = π - Real.arcsin sp.loadRatio := by
      rw [hδu, Synchronous.SwingParams.deltaU]
      show π - Real.arcsin sp.loadRatio + p.α - p.α = _; ring
    rw [e, Real.cos_pi_sub, Real.cos_arcsin, neg_lt_zero]
    apply Real.sqrt_pos.2
    have h := sp.abs_loadRatio_lt hk habs'
    have : sp.loadRatio ^ 2 < 1 := by
      rw [← sq_abs]; exact pow_lt_one₀ (abs_nonneg _) h (by norm_num)
    linarith
  set e := ε / 8 with hedef
  have he : 0 < e := by positivity
  -- cheap connections at both rest points
  have hglue : ∀ {δe : ℝ}, p.c0 + p.A * Real.sin (δe - p.α) = p.Pref → ∃ ρ > 0,
      ∀ a b : Fin 2 → ℝ, dist a ![δe, 0] < ρ → dist b ![δe, 0] < ρ →
        controlAction (p.gCtrl σP a b) 1 < e := by
    intro δe hδe
    obtain ⟨ρ, hρ, h⟩ := Metric.continuousAt_iff.mp
      ((p.continuous_glue σP).continuousAt (x := (![δe, 0], ![δe, 0]))) e he
    refine ⟨ρ, hρ, fun a b ha hb => ?_⟩
    have := h (show dist (a, b) (![δe, 0], ![δe, 0]) < ρ by rw [Prod.dist_eq]; exact max_lt ha hb)
    simp only [p.glue_rest σP hδe, Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  obtain ⟨ρs, hρs, hgs⟩ := hglue hes
  obtain ⟨ρu, hρu, hgu⟩ := hglue heu
  have hEc : Continuous p.swingEnergy :=
    continuous_iff_continuousAt.2 fun x => (p.hasFDerivAt_swingEnergy x).continuousAt
  obtain ⟨ρe, hρe, hE⟩ := Metric.continuousAt_iff.mp (hEc.continuousAt (x := ![δs, 0]))
    (e / c') (div_pos he hc')
  set η := min (ρu / 2) ((δu - δs) / 2) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηu : η < ρu := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηd : η < δu - δs := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set y : State 2 := PhasePlane.mk (δu - η) 0 with hydef
  have hyE : sp.energy δs y = sp.potential δs (δu - η) := by
    simp [y, PhasePlane.Conservative.separableEnergy]
  have hc1 : sp.energy δs y < sp.potential δs δu := by
    have h := p.potential_lt_of_mem habs (a := δu - η) (b := δu) (by linarith) (by linarith)
      le_rfl
    rw [← hsp] at h
    rw [hyE]; exact h
  have hc2 : sp.energy δs y < sp.potential δs (δu - 2 * π) := by
    rw [sp.potential_sub_two_pi]
    have : 0 ≤ sp.Pm - sp.k₁ := by show 0 ≤ p.Pref - p.c0; linarith
    nlinarith [Real.pi_pos]
  have hy : y ∈ {x ∈ sp.wellWindow | sp.energy δs x ≤ sp.energy δs y} := by
    refine ⟨⟨?_, ?_⟩, le_rfl⟩
    · simp only [y, PhasePlane.mk_apply_zero]
      linarith [sp.deltaU_sub_two_pi_lt_deltaS hk habs']
    · simp only [y, PhasePlane.mk_apply_zero]; linarith
  obtain ⟨L, ψ, u, hL0, hz, hψL, hcψ, hder, hucont, hS⟩ :=
    p.relax_uphill hσ (p.well_attracts hD habs hc1 hc2 hy) (lt_min hρs hρe)
  have hfy : p.flipMom y = ![δu - η, 0] := by
    ext i; fin_cases i <;> simp [flipMom, y]
  rw [hfy] at hψL
  have hEz := hE (lt_of_lt_of_le hz (min_le_right _ _))
  rw [Real.dist_eq, abs_lt] at hEz
  have hmid : controlAction u L ≤ c' * sp.potential δs δu + e := by
    rw [hS, hψL]
    have h1' : p.swingEnergy ![δu - η, 0] - p.swingEnergy ![δs, 0] ≤ sp.potential δs δu := by
      have h := p.potential_lt_of_mem habs (a := δu - η) (b := δu) (by linarith) (by linarith)
        le_rfl
      rw [swingEnergy_rest, swingEnergy_rest, ← swingModel_potential, ← hsp]
      exact h.le
    have h2' : c' * (p.swingEnergy ![δs, 0] - p.swingEnergy (ψ 0)) ≤ e := by
      have : p.swingEnergy ![δs, 0] - p.swingEnergy (ψ 0) < e / c' := by linarith [hEz.1]
      calc c' * (p.swingEnergy ![δs, 0] - p.swingEnergy (ψ 0)) ≤ c' * (e / c') :=
            mul_le_mul_of_nonneg_left this.le hc'.le
        _ = e := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h1' hc'.le
    have e3 : c' * (p.swingEnergy ![δu - η, 0] - p.swingEnergy (ψ 0)) =
        c' * (p.swingEnergy ![δu - η, 0] - p.swingEnergy ![δs, 0]) +
          c' * (p.swingEnergy ![δs, 0] - p.swingEnergy (ψ 0)) := by ring
    rw [e3]; exact add_le_add h3 h2'
  -- bounds along the three explicit pieces
  obtain ⟨U1, V1, hU1, hV1⟩ := p.glue_bounds σP ![δs, 0] (ψ 0)
  obtain ⟨U3, V3, hU3, hV3⟩ := p.glue_bounds σP ![δu - η, 0] ![δu, 0]
  obtain ⟨Uψ, hUψ⟩ := isCompact_Icc.exists_bound_of_continuousOn hucont
  obtain ⟨Vψ, hVψ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((continuous_apply 1).comp_continuousOn hcψ).div_const p.M)
  set Us := |U1| + |Uψ| + |U3| with hUs
  set Vs := |V1| + |Vψ| + |V3| with hVs
  have hUs0 : 0 ≤ Us := by positivity
  have hVs0 : 0 ≤ Vs := by positivity
  have hS1 : controlAction (p.gCtrl σP ![δs, 0] (ψ 0)) 1 < e :=
    hgs _ _ (by simp [hρs]) (lt_of_lt_of_le hz (min_le_left _ _))
  have hS3 : controlAction (p.gCtrl σP ![δu - η, 0] ![δu, 0]) 1 < e := by
    refine hgu _ _ ?_ (by simp [hρu])
    rw [dist_pi_lt_iff hρu]
    intro i; fin_cases i
    · show dist (δu - η) δu < ρu
      rw [Real.dist_eq, show δu - η - δu = -η by ring, abs_neg, abs_of_pos hη]
      exact hηu
    · show dist (0 : ℝ) 0 < ρu
      simpa using hρu
  -- the endBump amplitude
  set κ := -Real.cos (δu - p.α) with hκ
  have hκ0 : 0 < κ := by linarith
  set K := 2 * p.M + p.A + p.D with hK
  have hK0 : 0 < K := by have := p.D_nonneg; positivity
  set Λ := min (κ / 2) (|σP| * min 1 e / K) with hΛdef
  have hσa : 0 < |σP| := abs_pos.mpr hσ
  have hΛ : 0 < Λ := lt_min (by linarith) (by have := lt_min one_pos he; positivity)
  have hΛκ : Λ ≤ -Real.cos (δu - p.α) / 2 := min_le_left _ _
  have hΛc : 1 / 2 * (K * Λ / |σP|) ^ 2 ≤ e := by
    have h1 : K * Λ / |σP| ≤ min 1 e := by
      rw [div_le_iff₀ hσa]
      calc K * Λ ≤ K * (|σP| * min 1 e / K) := mul_le_mul_of_nonneg_left (min_le_right _ _)
            hK0.le
        _ = min 1 e * |σP| := by field_simp
    have h2 : 0 ≤ K * Λ / |σP| := by positivity
    have hm0 : 0 ≤ min 1 e := le_min zero_le_one he.le
    have hm1 : min 1 e ≤ 1 := min_le_left _ _
    have h3 : (K * Λ / |σP|) ^ 2 ≤ min 1 e :=
      calc (K * Λ / |σP|) ^ 2 ≤ (min 1 e) ^ 2 := pow_le_pow_left₀ h2 h1 2
        _ ≤ min 1 e := by rw [sq]; exact mul_le_of_le_one_left hm0 hm1
    have := min_le_right 1 e
    linarith
  -- the eventual conditions in `ω_c`
  have hcoe : Tendsto (fun ωc : Ioi (0 : ℝ) => (ωc : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hr : ∀ c : ℝ, Tendsto (fun ωc : Ioi (0 : ℝ) => c / (ωc : ℝ)) atTop (𝓝 0) := fun c =>
    tendsto_const_nhds.div_atTop hcoe
  have h1 := hr (2 * (p.A * Vs))
  have h2 := hr (2 * (p.A * Λ))
  have hex : Tendsto (fun ωc : Ioi (0 : ℝ) =>
      1 * (Us * (2 * (p.A * Vs) / ωc) / |σP| + (2 * (p.A * Vs) / ωc) ^ 2 / σP ^ 2) +
      L * (Us * (2 * (2 * (p.A * Vs) / ωc)) / |σP| + (2 * (2 * (p.A * Vs) / ωc)) ^ 2 / σP ^ 2) +
      1 * (Us * (3 * (2 * (p.A * Vs) / ωc)) / |σP| + (3 * (2 * (p.A * Vs) / ωc)) ^ 2 / σP ^ 2) +
      (K * Λ / |σP| * (3 * (2 * (p.A * Vs) / ωc) + 2 * (p.A * Λ) / ωc) / |σP| +
        (3 * (2 * (p.A * Vs) / ωc) + 2 * (p.A * Λ) / ωc) ^ 2 / σP ^ 2)) atTop (𝓝 0) := by
    have t1 := (((h1.const_mul Us).div_const |σP|).add ((h1.pow 2).div_const (σP ^ 2))).const_mul 1
    have t2 := ((((h1.const_mul 2).const_mul Us).div_const |σP|).add
      (((h1.const_mul 2).pow 2).div_const (σP ^ 2))).const_mul L
    have t3 := ((((h1.const_mul 3).const_mul Us).div_const |σP|).add
      (((h1.const_mul 3).pow 2).div_const (σP ^ 2))).const_mul 1
    have t4 := ((((h1.const_mul 3).add h2).const_mul (K * Λ / |σP|)).div_const |σP|).add
      ((((h1.const_mul 3).add h2).pow 2).div_const (σP ^ 2))
    have := ((t1.add t2).add t3).add t4
    simpa using this
  have hexp : Tendsto (fun ωc : Ioi (0 : ℝ) => 72 * (ωc : ℝ) ^ 2 * Real.exp (-(ωc : ℝ)) *
      (2 * (p.A * Vs) / ωc + 2 * (p.A * Vs) / ωc + 2 * (p.A * Vs) / ωc)) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hcoe).const_mul
      (432 * (p.A * Vs))
    rw [mul_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun ωc => ?_)
    have : (ωc : ℝ) ≠ 0 := (mem_Ioi.mp ωc.2).ne'
    simp only [Function.comp, pow_one]
    field_simp
    ring
  have hκΛ : 0 < p.A * -Real.cos (δu - p.α) * Λ := by positivity
  have aU1 := abs_nonneg U1
  have aUψ := abs_nonneg Uψ
  have aU3 := abs_nonneg U3
  have aV1 := abs_nonneg V1
  have aVψ := abs_nonneg Vψ
  have aV3 := abs_nonneg V3
  have hU1s : U1 ≤ Us := by rw [hUs]; linarith [le_abs_self U1]
  have hUψs : Uψ ≤ Us := by rw [hUs]; linarith [le_abs_self Uψ]
  have hU3s : U3 ≤ Us := by rw [hUs]; linarith [le_abs_self U3]
  have hV1s : V1 ≤ Vs := by rw [hVs]; linarith [le_abs_self V1]
  have hVψs : Vψ ≤ Vs := by rw [hVs]; linarith [le_abs_self Vψ]
  have hV3s : V3 ≤ Vs := by rw [hVs]; linarith [le_abs_self V3]
  have h4e : (0 : ℝ) < 4 * e := by linarith
  filter_upwards [hcoe.eventually_ge_atTop 2, hex.eventually (gt_mem_nhds h4e),
    hexp.eventually (gt_mem_nhds hκΛ)] with ωc hω2 hexs hzs
  have hfa := Params3.fast_assembly ⟨p, ωc, mem_Ioi.mp ωc.2⟩ hσ (δs := δs) (δu := δu) hes heu
    hcosu (T₁ := 1) (T₂ := L) (T₃ := 1) (Us := Us) (Vs := Vs) (Λ := Λ) zero_le_one hL0
    zero_le_one hUs0 hVs0 (φ₁ := p.gPath ![δs, 0] (ψ 0)) (φ₂ := ψ)
    (φ₃ := p.gPath ![δu - η, 0] ![δu, 0])
    (fun t _ => (p.hasDerivAt_gPath hσ _ _ t).continuousAt.continuousWithinAt) hcψ
    (fun t _ => (p.hasDerivAt_gPath hσ _ _ t).continuousAt.continuousWithinAt)
    (fun t _ => (p.hasDerivAt_gPath hσ _ _ t).hasDerivWithinAt) hder
    (fun t _ => (p.hasDerivAt_gPath hσ _ _ t).hasDerivWithinAt)
    (by simp only [gCtrl, gAngle, gVel, gAcc, Matrix.cons_val_zero]; fun_prop) hucont
    (by simp only [gCtrl, gAngle, gVel, gAcc, Matrix.cons_val_zero]; fun_prop)
    (fun t ht => (hU1 t ht).trans hU1s)
    (fun t ht => by
      have := hUψ t ht; rw [Real.norm_eq_abs] at this; exact this.trans hUψs)
    (fun t ht => (hU3 t ht).trans hU3s)
    (fun t ht => (hV1 t ht).trans hV1s)
    (fun t ht => by
      have := hVψ t ht; rw [Real.norm_eq_abs] at this; exact this.trans hVψs)
    (fun t ht => (hV3 t ht).trans hV3s)
    (p.gPath_zero _ _) (p.gPath_one _ _).symm (by rw [p.gPath_zero, hψL]) (p.gPath_one _ _)
    hΛ hΛκ hω2 hzs.le
  dsimp only at hfa
  rw [hes, heu]
  refine hfa.trans (ENNReal.ofReal_le_ofReal ?_)
  have hS2 := hmid
  have hS1' := hS1.le
  have hS3' := hS3.le
  linarith


/-- **Fast filter, upper half of the limit** (`D > 0`, `c₀ ≤ P_ref < c₀ + A`, `σ_P ≠ 0`): for
the three-state models `⟨p, ω_c⟩` from the stable equilibrium `(δ_s, 0, P(δ_s))` to the saddle
`(δ_u, 0, P(δ_u))`, `limsup_{ω_c → ∞} V₃ ≤ 2D (U(δ_u) − U(δ_s))/σ_P²`. -/
@[tmio M, powerlib_domain] theorem limsup_setPointQP_le {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {δs δu : ℝ}
    (hδs : δs = Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hδu : δu = π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α) :
    limsup (fun ωc : Ioi (0 : ℝ) => (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).setPointQP σP
        ![δs, 0, p.c0 + p.A * Real.sin (δs - p.α)] ![δu, 0, p.c0 + p.A * Real.sin (δu - p.α)])
        atTop ≤
      ENNReal.ofReal (2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2) := by
  have hs : δs = p.swingModel.deltaS := hδs
  have hu : δu = p.swingModel.deltaU := hδu
  have hval : 2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2 =
      2 * p.D / σP ^ 2 * p.swingModel.potential p.swingModel.deltaS p.swingModel.deltaU := by
    rw [swingModel_potential, ← hs, ← hu]; ring
  rw [hval, hs, hu]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  refine (Filter.limsup_le_of_le (by isBoundedDefault)
    (p.limsup_core hσ hD h0 h1 (ε := ε) hε)).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_add_le

/-- **The fast-filter limit** (`D > 0`, `c₀ ≤ P_ref < c₀ + A`, `σ_P ≠ 0`): the three-state escape
exponent from the stable equilibrium to the saddle tends to the two-state value
`2D (U(δ_u) − U(δ_s))/σ_P²` as `ω_c → ∞` (`Params.liminf_setPointQP_ge`,
`Params.limsup_setPointQP_le`); the two-state exponent is this value exactly
(`Params.swingQP_saddle_eq`). -/
@[tmio M, powerlib_domain] theorem tendsto_setPointQP {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {δs δu : ℝ}
    (hδs : δs = Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hδu : δu = π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α) :
    Tendsto (fun ωc : Ioi (0 : ℝ) => (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).setPointQP σP
        ![δs, 0, p.c0 + p.A * Real.sin (δs - p.α)] ![δu, 0, p.c0 + p.A * Real.sin (δu - p.α)])
      atTop (𝓝 (ENNReal.ofReal
        (2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2))) :=
  tendsto_of_le_liminf_of_limsup_le (p.liminf_setPointQP_ge hD hσ δs δu)
    (p.limsup_setPointQP_le hσ hD h0 h1 hδs hδu)

end Params


end powerlib.GFM.Noise
