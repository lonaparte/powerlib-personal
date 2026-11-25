import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ControlledAction
import theorem.GridTiedConverter.GFM.Noise.FilterQuasiPotential
import theorem.GridTiedConverter.GFM.Noise.UphillAction
import theorem.PowerSystem.Synchronous.DampedEAC
import theorem.Dynamics.LagFilter

/-! # Escape exponents of the noisy GFM: the two-state value, the filter limit and deficit

Domain module: the quasi-potential (Freidlin–Wentzell escape exponent) with set-point noise
(`GFM.Noise.Params.swingQP`, `GFM.Noise.Params3.setPointQP` of
`theorem/GridTiedConverter/GFM/Noise/FilterQuasiPotential.lean`) from the stable equilibrium to
the saddle. Two-state: exactly the Gibbs value `2D ΔU/σ_P²`. Three-state (VSM + power filter):
it tends to that value as the filter bandwidth `ω_c → ∞`, from below: `V₃ ≤ V₂ − c/ω_c` with
`c > 0` for all large `ω_c`, hence `V₃ < V₂` there. Lower bounds are the Hamilton–Jacobi
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
(LaSalle on the potential well); GFM counterpart study, note t2-noise item 7 (the first-order
deficit `−(2D/(σ_P² ω_c)) A ∫ cos(δ − α) ω²` along the uphill orbit; its minimum-action numerics
are observations only, not used); the energy identity `A cos(δ − α) ω² = M ω̇² +
d/dt(ω (P(δ) − P_ref) − D ω²/2)` along the uphill flow `M ω̇ = P_ref − P(δ) + D ω`, derived and
checked symbolically (sympy, exact) in the audit scratch notes outside the repository.

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
* `Params.setPointQP_le_sub` (for every `ω_c ≥ Params.escThreshold`:
  `V₃ ≤ 2D ΔU/σ_P² − escGain/(2σ_P² ω_c)`) and `Params.setPointQP_lt_swingQP` (`V₃ < V₂ =
  Params.swingQP` there), with the explicit constants `escBarrier` (`ΔU`), `escBandAngle`,
  `escBandGap` (`f₀ = A sin θ_a − (P_ref − c₀)`, `θ_a = (arcsin s + π/2)/2`), `escSpeed`,
  `escGain`, `escThreshold`. Construction: the same three two-state pieces (`relax_uphill`
  with an `ω_c`-dependent truncation) followed by the filter, whose lag `e = P_f − P(δ)` is used
  rather than suppressed: `2σ_P² S₃ ≤ ∫w² − (2/ω_c)∫w ġ + O(1/ω_c²)`
  (`Dynamics.lagFilter_tracking`, `w = σ_P u`, `g = P(δ(t))`); on the uphill piece `w = 2Dω`,
  and the energy identity gives the gain `(2D/ω_c)(M ∫ ω̇² − G(ψ(0)))`;
  `∫ ω̇² ≥ v⁴/(4 N_max)` uniformly in the truncation (`up_speed`: the angle crosses the band
  `[θ_a, π − θ_a]` on which `P − P_ref ≥ f₀`, so the speed reaches `v = escSpeed`;
  `Dynamics.sq_le_of_zero_end` at the rest end). A unit rest at the saddle and the exact arrival
  (`setPointQP_saddle_fix` with `Λ = 1/ω_c²`) close the pair; the exponential smallness is
  `e^ω ≥ ω⁵/120`.
* `Params.setPointQP_lt_swingQP_slow` (`V₃ < V₂` for `ω_c τ₁ ≤ 1` and
  `8A²ω_c² t_max³ ≤ D ΔU`, `T = escSlowTime`, `τ₁ = escSlowDwell`, `t_max = escSlowSpan`):
  the filter nearly frozen, a five-piece pair — rest-to-rest transits of duration `T` from `δ_s`
  to `π/2 + α`, then to `3π/2 + α`, then to `δ_u` (cubic angle profiles), a dwell `τ₁` at the
  top of the well and a dwell `τ* = log((Z₃ − P_b)/(Z_r − P_b))/ω_c` beyond the saddle chosen
  so that the last transit ends exactly at `P_f = P_ref` (`Dynamics.lagFilter_const`,
  `Dynamics.lagFilter_mono`, `Dynamics.lagFilter_eq_add`); its action is at most
  `3DΔU/(2σ_P²)` (`Dynamics.abs_lagFilter_sub_const_le`).
* Generic helpers (lag filter, quadratic action and tracking estimates, comparison and drift,
  end bump) are in `theorem/Dynamics/LagFilter.lean`.
* Every bandwidth, balanced set point: for `P_ref = c₀`,
  `GFM.Noise.Params.setPointQP_lt_swingQP_balanced` (`V₃ < V₂` for every `ω_c > 0`, with an
  explicit deficit) in `theorem/GridTiedConverter/GFM/Noise/BalancedEscape.lean`: an exact
  trajectory of the uphill field (`theorem/GridTiedConverter/GFM/Noise/UphillAction.lean`,
  action `(2D/σ_P²)(ΔF − (M/ω_c)∫ω̇²)`) found by shooting on the time-reversed field, whose
  reflection symmetry about the saddle needs `P_ref = c₀`.
* Not formalized: `V₃ < V₂` for `c₀ < P_ref < c₀ + A` and `ω_c` between the two explicit ranges
  above, `min(1/τ₁, √(DΔU/(8A² t_max³))) < ω_c < escThreshold`. The pairs of this module carry
  crude error terms there; the uphill-trajectory route of `GFM.Noise.BalancedEscape` lacks the
  reflection symmetry, and its right/left exit dichotomy is not available in general (for weak
  damping all orbits leaving the stable equilibrium on the uphill field exit over the saddle,
  the heteroclinic sitting at a jump of the exit time: an observation, not used).
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real Set Filter Topology
open scoped ENNReal
open powerlib.Stochastic.LDP
open powerlib.Dynamics (State lagFilter hasDerivAt_lagFilter lagFilter_zero abs_lagFilter_sub_le
  integral_sq_add_le hasDerivAt_vec_two hasDerivWithinAt_vec_three endBump endBumpVel endBumpAcc
  hasDerivAt_endBump hasDerivAt_endBumpVel endBump_bounds sin_add_sub_sin_bounds
  integral_exp_mul_endBump_ge lagFilter_tracking lagFilter_const sq_le_of_zero_end
  lagFilter_eq_add lagFilter_mono abs_lagFilter_sub_const_le)

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
      ContinuousOn ψ (Icc 0 L) ∧ (∀ t ∈ Ico 0 L, HasDerivAt ψ (controlField p.swingDrift
        (fun _ (_ : Fin 1) => swingColumn σP) (ψ t) (u t)) t) ∧
      ContinuousOn (fun t => u t 0) (Icc 0 L) ∧ (∀ t, u t 0 = 2 * p.D * ψ t 1 / (σP * p.M)) ∧
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
  have hder : ∀ s ∈ Ico 0 L, HasDerivAt ψ (controlField p.swingDrift
      (fun _ (_ : Fin 1) => swingColumn σP) (ψ s) (u s)) s := by
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
    exact hasDerivAt_vec_two (hc 0) ((hc 1).const_mul p.M).neg
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
  have hu0 : ∀ t, u t 0 = 2 * p.D * ψ t 1 / (σP * p.M) := fun t => rfl
  clear_value ψ u
  have hS := controlAction_eq_of_feedback (b := p.swingDrift)
    (σ := fun _ (_ : Fin 1) => swingColumn σP) (W := fun x => 2 * p.D / σP ^ 2 * p.swingEnergy x)
    (dW := fun x => (2 * p.D / σP ^ 2) • p.swingEnergyDeriv x) (φ := ψ) (u := u) hL0 hW hHJ
    hfb hcψ (fun t ht => (hder t ht).hasDerivWithinAt) hint
  have hS' : controlAction u L =
      2 * p.D / σP ^ 2 * (p.swingEnergy (p.flipMom y) - p.swingEnergy (p.flipMom (φ L))) := by
    rw [hS, hψ0, hψL]; ring
  exact ⟨L, ψ, u, hL0, by rw [hψ0]; exact hL, hψL, hcψ, hder, hucont, hu0, by
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
  obtain ⟨L, ψ, u, hL0, hz, hψL, hcψ, hder, hucont, -, hS⟩ :=
    p.relax_uphill hσ hroa (lt_min hρs hρe)
  set z := ψ 0 with hzdef
  have hzV : p.swingQP σP z (p.flipMom y) ≤
      ENNReal.ofReal (2 * p.D / σP ^ 2 * (p.swingEnergy (p.flipMom y) - p.swingEnergy z)) := by
    rw [← hψL, ← hS]
    refine controlQuasiPotential_le hL0 rfl rfl hcψ (fun t ht => (hder t ht).hasDerivWithinAt)
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
    rw [controlField_setPoint]
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
  obtain ⟨L, ψ, u, hL0, hz, hψL, hcψ, hder', hucont, -, hS⟩ :=
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
    (fun t _ => (p.hasDerivAt_gPath hσ _ _ t).hasDerivWithinAt)
    (fun t ht => (hder' t ht).hasDerivWithinAt)
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

/-! ## The first-order deficit: three-state pairs below the two-state value -/

namespace Params3

/-- **Following a two-state pair, quadratic estimate**: the three-state pair of
`setPointQP_le_follow` (filter started at `z₀`) has action `S ≥ 0` with
`2σ_P² S ≤ ∫w² − (2/ω_c)∫w g + ∫w'²/ω_c² + 2∫g²/ω_c² + (2/ω_c)(w(0)e(0) − w(T)e(T))
  + (2/ω_c)(e(0)² − e(T)²)` (`Dynamics.lagFilter_tracking`), where `w = σ_P u` (right
derivative `w'`), `g = A cos(δ − α) ω` is the rate of `P(δ)` and `e = P_f − P(δ)` the lag; the
end lag obeys `e(T)² ≤ e(0)² + ∫g²/ω_c`. -/
@[tmio TM, powerlib_domain] private theorem follow_track (p3 : Params3) {σP : ℝ} (hσ : σP ≠ 0)
    {T z₀ : ℝ} (hT : 0 ≤ T) {φ : ℝ → Fin 2 → ℝ} {u : ℝ → Fin 1 → ℝ} {w' : ℝ → ℝ}
    (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField p3.swingDrift
      (fun _ (_ : Fin 1) => Params.swingColumn σP) (φ t) (u t)) (Ici t) t)
    (hu : ContinuousOn (fun t => u t 0) (Icc 0 T))
    (hw : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => σP * u s 0) (w' t) (Ici t) t)
    (hw' : ContinuousOn w' (Icc 0 T)) :
    ∃ Z S : ℝ, 0 ≤ S ∧
      (Z - (p3.c0 + p3.A * Real.sin (φ T 0 - p3.α))) ^ 2 ≤
        (z₀ - (p3.c0 + p3.A * Real.sin (φ 0 0 - p3.α))) ^ 2 + (∫ t in (0 : ℝ)..T,
          (p3.A * Real.cos (φ t 0 - p3.α) * (φ t 1 / p3.M)) ^ 2) / p3.ωc ∧
      2 * σP ^ 2 * S ≤ (∫ t in (0 : ℝ)..T, (σP * u t 0) ^ 2) -
        2 / p3.ωc * (∫ t in (0 : ℝ)..T,
          σP * u t 0 * (p3.A * Real.cos (φ t 0 - p3.α) * (φ t 1 / p3.M))) +
        (∫ t in (0 : ℝ)..T, w' t ^ 2) / p3.ωc ^ 2 + 2 * (∫ t in (0 : ℝ)..T,
          (p3.A * Real.cos (φ t 0 - p3.α) * (φ t 1 / p3.M)) ^ 2) / p3.ωc ^ 2 +
        2 / p3.ωc * (σP * u 0 0 * (z₀ - (p3.c0 + p3.A * Real.sin (φ 0 0 - p3.α))) -
          σP * u T 0 * (Z - (p3.c0 + p3.A * Real.sin (φ T 0 - p3.α)))) +
        2 / p3.ωc * ((z₀ - (p3.c0 + p3.A * Real.sin (φ 0 0 - p3.α))) ^ 2 -
          (Z - (p3.c0 + p3.A * Real.sin (φ T 0 - p3.α))) ^ 2) ∧
      p3.setPointQP σP ![φ 0 0, φ 0 1 / p3.M, z₀] ![φ T 0, φ T 1 / p3.M, Z] ≤
        ENNReal.ofReal S ∧
      ∀ c : ℝ, (∀ t ∈ Icc 0 T, p3.c0 + p3.A * Real.sin (φ t 0 - p3.α) = c) →
        Z = c + (z₀ - c) * Real.exp (-(p3.ωc * T)) := by
  have hA := p3.A_pos
  have hσ2 : 0 < σP ^ 2 := by positivity
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
  set g : ℝ → ℝ := fun t => p3.A * Real.cos (φ t 0 - p3.α) * (φ t 1 / p3.M) with hgdef
  have hc0 : ContinuousOn (fun t => φ t 0) (Icc 0 T) := (continuous_apply 0).comp_continuousOn hc
  have hc1 : ContinuousOn (fun t => φ t 1) (Icc 0 T) := (continuous_apply 1).comp_continuousOn hc
  have hgc : ContinuousOn g (Icc 0 T) :=
    (continuousOn_const.mul (Real.continuous_cos.comp_continuousOn
      (hc0.sub continuousOn_const))).mul (hc1.div_const _)
  have hg : ∀ t ∈ Ico 0 T, HasDerivWithinAt h (g t) (Ici t) t := by
    intro t ht
    have h2 := hφ t ht
    have hu1 : u t = ![u t 0] := by ext j; fin_cases j; rfl
    rw [hu1, Params.controlField_swing] at h2
    have d0 : HasDerivWithinAt (fun r => φ r 0) (φ t 1 / p3.M) (Ici t) t := by
      simpa using hasDerivWithinAt_pi.1 h2 0
    have hP := (((Real.hasDerivAt_sin (φ t 0 - p3.α)).comp_hasDerivWithinAt t
      (d0.sub_const p3.α)).const_mul p3.A).const_add p3.c0
    have heq : h =ᶠ[𝓝[Ici t] t] fun r => p3.c0 + p3.A * Real.sin (φ r 0 - p3.α) := by
      filter_upwards [Icc_mem_nhdsGE ht.2] with r hr
      exact hhφ r ⟨ht.1.trans hr.1, hr.2⟩
    refine (hP.congr_of_eventuallyEq heq (hhφ t (Ico_subset_Icc_self ht))).congr_deriv ?_
    simp only [hgdef]; ring
  have hwc : ContinuousOn (fun s => σP * u s 0) (Icc 0 T) := continuousOn_const.mul hu
  obtain ⟨hend, hint⟩ := lagFilter_tracking (z₀ := z₀) p3.ωc_pos hT hhc hg hgc hw hwc hw'
  set Z := lagFilter p3.ωc z₀ h with hZdef
  have hZc : Continuous Z :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_lagFilter hhc t).continuousAt
  set S := 1 / 2 * ∫ t in (0 : ℝ)..T, (u t 0 + (Z t - h t) / σP) ^ 2 with hSdef
  have hS0 : 0 ≤ S := mul_nonneg (by norm_num)
    (intervalIntegral.integral_nonneg hT fun t _ => sq_nonneg _)
  have hSeq : 2 * σP ^ 2 * S = ∫ t in (0 : ℝ)..T, (σP * u t 0 + (Z t - h t)) ^ 2 := by
    rw [hSdef, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1; funext t; field_simp
  have h0 := hhφ 0 ⟨le_rfl, hT⟩
  have hT' := hhφ T ⟨hT, le_rfl⟩
  refine ⟨Z T, S, hS0, ?_, ?_, p3.setPointQP_le_follow hσ hT hc hφ hu hhc hhφ z₀, ?_⟩
  · rw [← h0, ← hT']; exact hend
  · rw [hSeq, ← h0, ← hT']; exact hint
  · intro c hcst
    have hh : h = fun _ => c := funext fun s => by
      simp only [hhdef]; exact hcst _ (projIcc 0 T hT s).2
    rw [hZdef, hh, lagFilter_const]

/-- **Rest at the saddle**: holding `(δ_e, 0)` (`P(δ_e) = P_ref`) for unit time lets the filter
relax, `P_f − P_ref ↦ (z − P_ref) e^{−ω_c}`, with action at most `(z − P_ref)²/(ω_c σ_P²)`. -/
@[tmio TM, powerlib_domain] private theorem setPointQP_rest_le (p3 : Params3) {σP : ℝ}
    (hσ : σP ≠ 0) {δe : ℝ} (he : p3.c0 + p3.A * Real.sin (δe - p3.α) = p3.Pref) (z : ℝ) :
    ∃ S : ℝ, 0 ≤ S ∧ σP ^ 2 * S ≤ (z - p3.Pref) ^ 2 / p3.ωc ∧
      p3.setPointQP σP ![δe, 0, z]
        ![δe, 0, p3.Pref + (z - p3.Pref) * Real.exp (-p3.ωc)] ≤ ENNReal.ofReal S := by
  have hrest : ∀ t, HasDerivAt (fun _ : ℝ => (![δe, 0] : Fin 2 → ℝ)) (controlField p3.swingDrift
      (fun _ (_ : Fin 1) => Params.swingColumn σP) ![δe, 0] ![0]) t := by
    intro t
    rw [Params.controlField_swing]
    have e : (![0 / p3.M, p3.Pref - (p3.c0 + p3.A * Real.sin (δe - p3.α)) - p3.D * (0 / p3.M) +
        0 * σP] : Fin 2 → ℝ) = 0 := by
      ext i; fin_cases i <;> simp [he]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [e]; exact hasDerivAt_const t _
  obtain ⟨Z, S, hS0, -, hS, hV, hZ⟩ := p3.follow_track hσ (z₀ := z) zero_le_one
    (φ := fun _ => ![δe, 0]) (u := fun _ => ![0]) (w' := fun _ => 0) continuousOn_const
    (fun t _ => (hrest t).hasDerivWithinAt) continuousOn_const
    (fun t _ => by simpa using (hasDerivWithinAt_const t (Ici t) (0 : ℝ))) continuousOn_const
  refine ⟨S, hS0, ?_, ?_⟩
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, he, zero_div, mul_zero, zero_mul,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, intervalIntegral.integral_zero,
      sub_zero, add_zero, zero_add] at hS
    have hω := p3.ωc_pos
    have : 0 ≤ 2 / p3.ωc * (Z - p3.Pref) ^ 2 := by positivity
    have e2 : 2 / p3.ωc * ((z - p3.Pref) ^ 2 - (Z - p3.Pref) ^ 2) =
        2 * ((z - p3.Pref) ^ 2 / p3.ωc) - 2 / p3.ωc * (Z - p3.Pref) ^ 2 := by ring
    linarith
  · have hZ' := hZ p3.Pref fun t _ => he
    simp only [mul_one] at hZ'
    simpa [hZ'] using hV

end Params3

namespace Params

variable (p : Params)

/-! ### Along the feedback (uphill) pair -/

/-- Uphill acceleration `ω̇ = (P_ref − P(δ) + D ω)/M` (`ω = p/M`) of the feedback pair. -/
private def upAcc (x : Fin 2 → ℝ) : ℝ :=
  (p.Pref - (p.c0 + p.A * Real.sin (x 0 - p.α)) + p.D * (x 1 / p.M)) / p.M

/-- `G = ω (P(δ) − P_ref) − D ω²/2`: along the uphill field `Ġ = A cos(δ − α) ω² − M ω̇²`. -/
private def lagG (x : Fin 2 → ℝ) : ℝ :=
  x 1 / p.M * (p.c0 + p.A * Real.sin (x 0 - p.α) - p.Pref) - p.D * (x 1 / p.M) ^ 2 / 2

@[tmio M, powerlib_domain] private theorem continuous_lagG : Continuous p.lagG := by
  unfold lagG; fun_prop

@[tmio M, powerlib_domain] private theorem continuous_upAcc : Continuous p.upAcc := by
  unfold upAcc; fun_prop

@[tmio M, powerlib_domain] private theorem lagG_rest (δ : ℝ) : p.lagG ![δ, 0] = 0 := by
  simp [lagG]

/-- The feedback pair in coordinates: `δ̇ = ω`, `ω̇ = upAcc`. -/
@[tmio M, powerlib_domain] private theorem up_hasDerivAt {σP : ℝ} (hσ : σP ≠ 0) {L : ℝ}
    {ψ : ℝ → Fin 2 → ℝ} {u : ℝ → Fin 1 → ℝ}
    (hder : ∀ t ∈ Ico 0 L, HasDerivAt ψ (controlField p.swingDrift
      (fun _ (_ : Fin 1) => swingColumn σP) (ψ t) (u t)) t)
    (hu : ∀ t, u t 0 = 2 * p.D * ψ t 1 / (σP * p.M)) {t : ℝ} (ht : t ∈ Ico 0 L) :
    HasDerivAt (fun s => ψ s 0) (ψ t 1 / p.M) t ∧
      HasDerivAt (fun s => ψ s 1 / p.M) (p.upAcc (ψ t)) t ∧
      HasDerivAt (fun s => p.swingEnergy (ψ s)) (p.D * (ψ t 1 / p.M) ^ 2) t := by
  have hM := p.M_pos.ne'
  have h := hder t ht
  have hu1 : u t = ![u t 0] := by ext j; fin_cases j; rfl
  have hE := (p.hasFDerivAt_swingEnergy (ψ t)).comp_hasDerivAt t h
  rw [hu1, controlField_swing, hu] at h hE
  have h0 := hasDerivAt_pi.1 h 0
  have h1 := hasDerivAt_pi.1 h 1
  refine ⟨by simpa using h0, ?_, ?_⟩
  · convert h1.div_const p.M using 1
    simp [upAcc]; field_simp; ring
  · refine hE.congr_deriv ?_
    simp [swingEnergyDeriv, potentialDeriv, toSM]; field_simp; ring

/-- **The energy identity behind the deficit**: along the uphill pair,
`A ∫ cos(δ − α) ω² = M ∫ ω̇² + G(T) − G(0)` (`Ġ = A cos(δ − α) ω² − M ω̇²`). -/
@[tmio M, powerlib_domain] private theorem up_identity {σP : ℝ} (hσ : σP ≠ 0) {L : ℝ}
    (hL : 0 ≤ L) {ψ : ℝ → Fin 2 → ℝ} {u : ℝ → Fin 1 → ℝ} (hc : ContinuousOn ψ (Icc 0 L))
    (hder : ∀ t ∈ Ico 0 L, HasDerivAt ψ (controlField p.swingDrift
      (fun _ (_ : Fin 1) => swingColumn σP) (ψ t) (u t)) t)
    (hu : ∀ t, u t 0 = 2 * p.D * ψ t 1 / (σP * p.M)) :
    p.A * (∫ t in (0 : ℝ)..L, Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M) ^ 2) =
      p.M * (∫ t in (0 : ℝ)..L, p.upAcc (ψ t) ^ 2) + (p.lagG (ψ L) - p.lagG (ψ 0)) := by
  have hM := p.M_pos.ne'
  have hc0 : ContinuousOn (fun t => ψ t 0) (Icc 0 L) := (continuous_apply 0).comp_continuousOn hc
  have hc1 : ContinuousOn (fun t => ψ t 1) (Icc 0 L) := (continuous_apply 1).comp_continuousOn hc
  have i1 : ContinuousOn (fun t => Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M) ^ 2) (Icc 0 L) :=
    (Real.continuous_cos.comp_continuousOn (hc0.sub continuousOn_const)).mul
      ((hc1.div_const _).pow 2)
  have i2 : ContinuousOn (fun t => p.upAcc (ψ t) ^ 2) (Icc 0 L) :=
    (p.continuous_upAcc.comp_continuousOn hc).pow 2
  have hFTC : ∫ t in (0 : ℝ)..L, (p.A * (Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M) ^ 2) -
      p.M * p.upAcc (ψ t) ^ 2) = p.lagG (ψ L) - p.lagG (ψ 0) := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL
      (p.continuous_lagG.comp_continuousOn hc) (fun t ht => ?_)
      (((continuousOn_const.mul i1).sub (continuousOn_const.mul i2)).intervalIntegrable_of_Icc hL)
    obtain ⟨hθ, hω, -⟩ := p.up_hasDerivAt hσ hder hu (Ioo_subset_Ico_self ht)
    have hP := ((((hθ.sub_const p.α).sin).const_mul p.A).const_add p.c0).sub_const p.Pref
    have h := (hω.mul hP).sub (((hω.pow 2).const_mul p.D).div_const 2)
    refine HasDerivAt.hasDerivWithinAt ?_
    convert h using 1
    · funext s; simp only [lagG, Function.comp_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    · simp only [upAcc, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      field_simp; ring
  have j1 : IntervalIntegrable (fun t => p.A * (Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M) ^ 2))
      MeasureTheory.volume 0 L := (continuousOn_const.mul i1).intervalIntegrable_of_Icc hL
  have j2 : IntervalIntegrable (fun t => p.M * p.upAcc (ψ t) ^ 2) MeasureTheory.volume 0 L :=
    (continuousOn_const.mul i2).intervalIntegrable_of_Icc hL
  rw [intervalIntegral.integral_sub j1 j2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hFTC
  linarith

/-- **A definite speed along the uphill pair, explicit form**: if the angle `θ = δ − α` crosses
the band `[θ_a, θ_b]` on which `P(δ) − P_ref ≥ f₀`, the speed reaches `v` somewhere, for every
`v > 0` with `2 D v ≤ f₀` and `4 M v² ≤ f₀ (θ_b − θ_a)` (on the last crossing interval
`ω̇ ≤ −f₀/(2M)` and `θ̇ = ω`: mean value theorem). -/
@[tmio M, powerlib_domain] private theorem up_speed {σP : ℝ} (hσ : σP ≠ 0) {L : ℝ}
    (hL : 0 ≤ L) {ψ : ℝ → Fin 2 → ℝ} {u : ℝ → Fin 1 → ℝ} (hc : ContinuousOn ψ (Icc 0 L))
    (hder : ∀ t ∈ Ico 0 L, HasDerivAt ψ (controlField p.swingDrift
      (fun _ (_ : Fin 1) => swingColumn σP) (ψ t) (u t)) t)
    (hu : ∀ t, u t 0 = 2 * p.D * ψ t 1 / (σP * p.M)) {θa θb f₀ v : ℝ} (hab : θa < θb)
    (h0 : ψ 0 0 - p.α < θa) (hL' : θb ≤ ψ L 0 - p.α)
    (hband : ∀ θ ∈ Icc θa θb, f₀ ≤ p.c0 + p.A * Real.sin θ - p.Pref)
    (hv : 0 < v) (hDv : 2 * p.D * v ≤ f₀) (hE : 4 * p.M * v ^ 2 ≤ f₀ * (θb - θa)) :
    ∃ t ∈ Icc 0 L, v ≤ |ψ t 1 / p.M| := by
  have hM := p.M_pos
  have hDn := p.D_nonneg
  by_contra hno
  push Not at hno
  have hc0 : ContinuousOn (fun t => ψ t 0 - p.α) (Icc 0 L) :=
    ((continuous_apply 0).comp_continuousOn hc).sub continuousOn_const
  -- the first time the angle reaches `θ_b`
  set S₂ := Icc 0 L ∩ (fun t => ψ t 0 - p.α) ⁻¹' Ici θb with hS₂
  have hS₂c : IsClosed S₂ := hc0.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hS₂n : S₂.Nonempty := ⟨L, ⟨hL, le_rfl⟩, hL'⟩
  have hS₂b : BddBelow S₂ := ⟨0, fun t ht => ht.1.1⟩
  set t₂ := sInf S₂ with ht₂
  have ht₂m : t₂ ∈ S₂ := hS₂c.csInf_mem hS₂n hS₂b
  have hbelow : ∀ t ∈ Icc 0 L, t < t₂ → ψ t 0 - p.α < θb := fun t ht htt => by
    by_contra h
    exact absurd (csInf_le hS₂b ⟨ht, not_lt.mp h⟩) (not_le.mpr htt)
  -- the last time before `t₂` the angle is at most `θ_a`
  set S₁ := Icc 0 t₂ ∩ (fun t => ψ t 0 - p.α) ⁻¹' Iic θa with hS₁
  have hS₁c : IsClosed S₁ :=
    (hc0.mono (Icc_subset_Icc le_rfl ht₂m.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hS₁n : S₁.Nonempty := ⟨0, ⟨le_rfl, ht₂m.1.1⟩, h0.le⟩
  have hS₁b : BddAbove S₁ := ⟨t₂, fun t ht => ht.1.2⟩
  set t₁ := sSup S₁ with ht₁
  have ht₁m : t₁ ∈ S₁ := hS₁c.csSup_mem hS₁n hS₁b
  have habove : ∀ t ∈ Icc 0 t₂, t₁ < t → θa < ψ t 0 - p.α := fun t ht htt => by
    by_contra h
    exact absurd (le_csSup hS₁b ⟨ht, not_lt.mp h⟩) (not_le.mpr htt)
  have h12 : t₁ < t₂ := by
    rcases ht₁m.1.2.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := ht₁m.2
      have h2 := ht₂m.2
      simp only [mem_preimage, mem_Iic, mem_Ici] at h1 h2
      rw [h] at h1; linarith
  have hsub : Icc t₁ t₂ ⊆ Icc 0 L := Icc_subset_Icc ht₁m.1.1 ht₂m.1.2
  have hIoo : ∀ s ∈ Ioo t₁ t₂, s ∈ Ico 0 L := fun s hs =>
    ⟨ht₁m.1.1.trans hs.1.le, hs.2.trans_le ht₂m.1.2⟩
  have hdt : 0 < t₂ - t₁ := by linarith
  -- mean value theorem for `ω` and `θ`
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun s => ψ s 1 / p.M)
    (fun s => p.upAcc (ψ s)) h12
    ((((continuous_apply 1).comp_continuousOn hc).div_const _).mono hsub)
    fun s hs => (p.up_hasDerivAt hσ hder hu (hIoo s hs)).2.1
  obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope (fun s => ψ s 0 - p.α)
    (fun s => ψ s 1 / p.M) h12 (hc0.mono hsub)
    fun s hs => (p.up_hasDerivAt hσ hder hu (hIoo s hs)).1.sub_const p.α
  have hξI := hsub (Ioo_subset_Icc_self hξ)
  have hθξ : ψ ξ 0 - p.α ∈ Icc θa θb :=
    ⟨(habove ξ ⟨hξI.1, hξ.2.le⟩ hξ.1).le, (hbelow ξ hξI hξ.2).le⟩
  have hF := hband _ hθξ
  have hωξ := hno ξ hξI
  have hq : p.upAcc (ψ ξ) ≤ -(f₀ / (2 * p.M)) := by
    have : p.D * (ψ ξ 1 / p.M) ≤ p.D * v :=
      mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hωξ.le) hDn
    simp only [upAcc]
    rw [div_le_iff₀ hM]
    have e : -(f₀ / (2 * p.M)) * p.M = -(f₀ / 2) := by field_simp
    rw [e]
    linarith
  have hΔ : ψ t₂ 1 / p.M - ψ t₁ 1 / p.M = p.upAcc (ψ ξ) * (t₂ - t₁) := by
    rw [hξeq]; field_simp
  have hω1 := hno t₁ (hsub ⟨le_rfl, h12.le⟩)
  have hω2 := hno t₂ (hsub ⟨h12.le, le_rfl⟩)
  have hT : f₀ * (t₂ - t₁) < 4 * p.M * v := by
    have h1 : -(2 * v) < ψ t₂ 1 / p.M - ψ t₁ 1 / p.M := by
      have := neg_abs_le (ψ t₂ 1 / p.M); have := le_abs_self (ψ t₁ 1 / p.M); linarith
    have h2 : p.upAcc (ψ ξ) * (t₂ - t₁) ≤ -(f₀ / (2 * p.M)) * (t₂ - t₁) :=
      mul_le_mul_of_nonneg_right hq hdt.le
    have e : -(f₀ / (2 * p.M)) * (t₂ - t₁) = -(f₀ * (t₂ - t₁)) / (2 * p.M) := by ring
    rw [hΔ] at h1
    have h3 : -(2 * v) < -(f₀ * (t₂ - t₁)) / (2 * p.M) := by linarith
    rw [lt_div_iff₀ (by positivity)] at h3
    linarith
  have hθ : θb - θa ≤ v * (t₂ - t₁) := by
    have h1 := ht₁m.2
    have h2 := ht₂m.2
    simp only [mem_preimage, mem_Iic, mem_Ici] at h1 h2
    have hζI := hsub (Ioo_subset_Icc_self hζ)
    have hωζ := hno ζ hζI
    have e : ψ t₂ 0 - p.α - (ψ t₁ 0 - p.α) = ψ ζ 1 / p.M * (t₂ - t₁) := by
      rw [hζeq]; field_simp
    have : ψ ζ 1 / p.M * (t₂ - t₁) ≤ v * (t₂ - t₁) :=
      mul_le_mul_of_nonneg_right ((le_abs_self _).trans hωζ.le) hdt.le
    linarith
  have hf0 : 0 ≤ f₀ := le_trans (by positivity) hDv
  have h5 : f₀ * (θb - θa) ≤ f₀ * (v * (t₂ - t₁)) := mul_le_mul_of_nonneg_left hθ hf0
  have h6 : v * (f₀ * (t₂ - t₁)) < v * (4 * p.M * v) := mul_lt_mul_of_pos_left hT hv
  have e1 : f₀ * (v * (t₂ - t₁)) = v * (f₀ * (t₂ - t₁)) := by ring
  have e2 : v * (4 * p.M * v) = 4 * p.M * v ^ 2 := by ring
  linarith

/-- On `[θ_a, π − θ_a]` (`θ_a ≥ −π/2`) the sine is at least `sin θ_a`. -/
@[tmio T, powerlib_foundation] private theorem sin_ge_of_mem_band {θa θ : ℝ}
    (h1 : -(π / 2) ≤ θa) (hθ : θ ∈ Icc θa (π - θa)) :
    Real.sin θa ≤ Real.sin θ := by
  rcases le_or_gt θ (π / 2) with h | h
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two h1 h hθ.1
  · rw [← Real.sin_pi_sub θ]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two h1 (by linarith) (by linarith [hθ.2])

/-- **Lower bound for `∫ ω̇²`**: if the speed reaches `v` and `ω(L) = 0`, then
`∫ ω̇² ≥ v⁴/(4N)` for every `N ≥ ∫ ω²` (`Dynamics.sq_le_of_zero_end` with `λ = v²/(2N)`). -/
@[tmio M, powerlib_domain] private theorem up_lower {σP : ℝ} (hσ : σP ≠ 0) {L : ℝ}
    (hL : 0 ≤ L) {ψ : ℝ → Fin 2 → ℝ} {u : ℝ → Fin 1 → ℝ} (hc : ContinuousOn ψ (Icc 0 L))
    (hder : ∀ t ∈ Ico 0 L, HasDerivAt ψ (controlField p.swingDrift
      (fun _ (_ : Fin 1) => swingColumn σP) (ψ t) (u t)) t)
    (hu : ∀ t, u t 0 = 2 * p.D * ψ t 1 / (σP * p.M)) (hL1 : ψ L 1 = 0) {v N : ℝ} (hv : 0 < v)
    (hN : 0 < N) (hNle : ∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2 ≤ N)
    (hvt : ∃ t ∈ Icc 0 L, v ≤ |ψ t 1 / p.M|) :
    v ^ 4 / (4 * N) ≤ ∫ t in (0 : ℝ)..L, p.upAcc (ψ t) ^ 2 := by
  obtain ⟨t, ht, hvt⟩ := hvt
  have hc1 : ContinuousOn (fun s => ψ s 1 / p.M) (Icc 0 L) :=
    ((continuous_apply 1).comp_continuousOn hc).div_const _
  have hq : ContinuousOn (fun s => p.upAcc (ψ s)) (Icc 0 L) :=
    p.continuous_upAcc.comp_continuousOn hc
  set l := v ^ 2 / (2 * N) with hldef
  have hl : 0 < l := by positivity
  have hsq := sq_le_of_zero_end ht.2 hl (x := fun s => ψ s 1 / p.M)
    (x' := fun s => p.upAcc (ψ s))
    (fun s hs => (p.up_hasDerivAt hσ hder hu ⟨ht.1.trans hs.1, hs.2⟩).2.1.hasDerivWithinAt)
    (hc1.mono (Icc_subset_Icc ht.1 le_rfl)) (hq.mono (Icc_subset_Icc ht.1 le_rfl))
    (by simp [hL1])
  have m1 : ∫ s in t..L, (ψ s 1 / p.M) ^ 2 ≤ ∫ s in (0 : ℝ)..L, (ψ s 1 / p.M) ^ 2 :=
    intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
      (Filter.Eventually.of_forall fun s => sq_nonneg _) ((hc1.pow 2).intervalIntegrable_of_Icc hL)
  have m2 : ∫ s in t..L, p.upAcc (ψ s) ^ 2 ≤ ∫ s in (0 : ℝ)..L, p.upAcc (ψ s) ^ 2 :=
    intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
      (Filter.Eventually.of_forall fun s => sq_nonneg _) ((hq.pow 2).intervalIntegrable_of_Icc hL)
  have hv2 : v ^ 2 ≤ (ψ t 1 / p.M) ^ 2 := by
    rw [← sq_abs (ψ t 1 / p.M)]; exact pow_le_pow_left₀ hv.le hvt 2
  set Q := ∫ s in (0 : ℝ)..L, p.upAcc (ψ s) ^ 2
  have h1 : v ^ 2 ≤ l * N + Q / l := by
    have := mul_le_mul_of_nonneg_left (m1.trans hNle) hl.le
    have := div_le_div_of_nonneg_right m2 hl.le
    linarith
  have h2 : l * N = v ^ 2 / 2 := by rw [hldef]; field_simp
  rw [h2] at h1
  have h3 : v ^ 2 / 2 ≤ Q / l := by linarith
  rw [hldef, div_div_eq_mul_div, le_div_iff₀ (by positivity)] at h3
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ### Short connecting pieces: the quadratic quantities -/

private def gJerk (a b : Fin 2 → ℝ) : ℝ := (b 0 - a 0) * (-12) + a 1 / p.M * 6 + b 1 / p.M * 6

/-- `σ_P` times the control of the connecting piece: `M δ̈ + (P(δ) − P_ref) + D δ̇`. -/
private def gW (a b : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  p.M * p.gAcc a b t + (p.c0 + p.A * Real.sin (p.gAngle a b t - p.α) - p.Pref) +
    p.D * p.gVel a b t

private def gW' (a b : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  p.M * p.gJerk a b + p.A * Real.cos (p.gAngle a b t - p.α) * p.gVel a b t + p.D * p.gAcc a b t

/-- Quadratic size of a connecting piece: `∫₀¹ (w² + w'² + g²) + w(0)² + w(1)²`. -/
private def glueQ (a b : Fin 2 → ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, (p.gW a b t ^ 2 + p.gW' a b t ^ 2 +
    (p.A * Real.cos (p.gAngle a b t - p.α) * p.gVel a b t) ^ 2)) +
    p.gW a b 0 ^ 2 + p.gW a b 1 ^ 2

@[tmio M, powerlib_domain] private theorem hasDerivAt_gAcc (a b : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (p.gAcc a b) (p.gJerk a b) t := by
  have h1 := hasDerivAt_id t
  have h := ((((h1.const_mul 12).const_sub 6).const_mul (b 0 - a 0)).add
    ((((h1.const_mul 6).const_add (-4))).const_mul (a 1 / p.M))).add
      ((((h1.const_mul 6).sub_const 2)).const_mul (b 1 / p.M))
  convert h using 1
  · funext s; simp only [gAcc, Pi.add_apply, id]
  · simp only [gJerk]; ring

@[tmio M, powerlib_domain] private theorem hasDerivAt_gW (a b : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (p.gW a b) (p.gW' a b t) t := by
  have hθ := p.hasDerivAt_gAngle a b t
  have h := (((p.hasDerivAt_gAcc a b t).const_mul p.M).add
    ((((hθ.sub_const p.α).sin.const_mul p.A).const_add p.c0).sub_const p.Pref)).add
      ((p.hasDerivAt_gVel a b t).const_mul p.D)
  convert h using 1
  · funext s; simp only [gW, Pi.add_apply]
  · simp only [gW']; ring

@[tmio M, powerlib_domain] private theorem gW_eq {σP : ℝ} (hσ : σP ≠ 0) (a b : Fin 2 → ℝ)
    (t : ℝ) : σP * p.gCtrl σP a b t 0 = p.gW a b t := by
  simp only [gCtrl, gW, Matrix.cons_val_zero]; field_simp

@[tmio M, powerlib_domain] private theorem continuous_glueQ :
    Continuous fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.glueQ q.1 q.2 := by
  have h : Continuous fun x : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ℝ =>
      p.gW x.1.1 x.1.2 x.2 ^ 2 + p.gW' x.1.1 x.1.2 x.2 ^ 2 +
        (p.A * Real.cos (p.gAngle x.1.1 x.1.2 x.2 - p.α) * p.gVel x.1.1 x.1.2 x.2) ^ 2 := by
    simp only [gW, gW', gJerk, gAngle, gVel, gAcc]
    fun_prop
  have hw : ∀ t : ℝ, Continuous fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.gW q.1 q.2 t := by
    intro t; simp only [gW, gAngle, gVel, gAcc]; fun_prop
  exact ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 1).add
    ((hw 0).pow 2)).add ((hw 1).pow 2)

@[tmio M, powerlib_domain] private theorem glueQ_rest {δe : ℝ}
    (he : p.c0 + p.A * Real.sin (δe - p.α) = p.Pref) : p.glueQ ![δe, 0] ![δe, 0] = 0 := by
  simp [glueQ, gW, gW', gJerk, gAngle, gVel, gAcc, he]

/-- **Small connecting pieces**: for every `ε > 0` there is `ρ > 0` such that the connecting
piece between two states within `ρ` of a rest point has `glueQ < ε`. -/
@[tmio M, powerlib_domain] private theorem glueQ_small {δe : ℝ}
    (he : p.c0 + p.A * Real.sin (δe - p.α) = p.Pref) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ a b : Fin 2 → ℝ, dist a ![δe, 0] < ρ → dist b ![δe, 0] < ρ → p.glueQ a b < ε := by
  obtain ⟨ρ, hρ, h⟩ := Metric.continuousAt_iff.mp
    ((p.continuous_glueQ).continuousAt (x := (![δe, 0], ![δe, 0]))) ε hε
  refine ⟨ρ, hρ, fun a b ha hb => ?_⟩
  have := h (show dist (a, b) (![δe, 0], ![δe, 0]) < ρ by rw [Prod.dist_eq]; exact max_lt ha hb)
  simp only [p.glueQ_rest he, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans_lt this

/-- The quadratic quantities of a connecting piece are bounded by `glueQ`. -/
@[tmio M, powerlib_domain] private theorem glue_parts (a b : Fin 2 → ℝ) :
    (∫ t in (0 : ℝ)..1, p.gW a b t ^ 2) ≤ p.glueQ a b ∧
    (∫ t in (0 : ℝ)..1, p.gW' a b t ^ 2) ≤ p.glueQ a b ∧
    (∫ t in (0 : ℝ)..1, (p.A * Real.cos (p.gAngle a b t - p.α) * p.gVel a b t) ^ 2) ≤
      p.glueQ a b ∧
    -(∫ t in (0 : ℝ)..1, p.gW a b t * (p.A * Real.cos (p.gAngle a b t - p.α) * p.gVel a b t)) ≤
      p.glueQ a b / 2 ∧
    p.gW a b 0 ^ 2 ≤ p.glueQ a b ∧ p.gW a b 1 ^ 2 ≤ p.glueQ a b := by
  set g : ℝ → ℝ := fun t => p.A * Real.cos (p.gAngle a b t - p.α) * p.gVel a b t with hgdef
  set S : ℝ → ℝ := fun t => p.gW a b t ^ 2 + p.gW' a b t ^ 2 + g t ^ 2 with hSdef
  have cw : Continuous (p.gW a b) := by unfold gW gAngle gVel gAcc; fun_prop
  have cw' : Continuous (p.gW' a b) := by unfold gW' gJerk gAngle gVel gAcc; fun_prop
  have cg : Continuous g := by simp only [hgdef]; unfold gAngle gVel; fun_prop
  have iS : IntervalIntegrable S MeasureTheory.volume 0 1 :=
    (((cw.pow 2).add (cw'.pow 2)).add (cg.pow 2)).intervalIntegrable _ _
  have mono : ∀ f : ℝ → ℝ, Continuous f → (∀ t, f t ≤ S t) →
      ∫ t in (0 : ℝ)..1, f t ≤ ∫ t in (0 : ℝ)..1, S t := fun f hf hle =>
    intervalIntegral.integral_mono_on zero_le_one (hf.intervalIntegrable _ _) iS
      fun t _ => hle t
  have hS0 : 0 ≤ ∫ t in (0 : ℝ)..1, S t :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => by simp only [hSdef]; positivity
  have h0 := sq_nonneg (p.gW a b 0)
  have h1 := sq_nonneg (p.gW a b 1)
  have hQ : p.glueQ a b = (∫ t in (0 : ℝ)..1, S t) + p.gW a b 0 ^ 2 + p.gW a b 1 ^ 2 := rfl
  have q1 : ∀ t, p.gW a b t ^ 2 ≤ S t := fun t => by
    have := sq_nonneg (p.gW' a b t); have := sq_nonneg (g t); simp only [hSdef]; linarith
  have q2 : ∀ t, p.gW' a b t ^ 2 ≤ S t := fun t => by
    have := sq_nonneg (p.gW a b t); have := sq_nonneg (g t); simp only [hSdef]; linarith
  have q3 : ∀ t, g t ^ 2 ≤ S t := fun t => by
    have := sq_nonneg (p.gW a b t); have := sq_nonneg (p.gW' a b t); simp only [hSdef]; linarith
  have q4 : ∀ t, 2 * -(p.gW a b t * g t) ≤ S t := fun t => by
    have := sq_nonneg (p.gW a b t + g t); have := sq_nonneg (p.gW' a b t)
    simp only [hSdef]; nlinarith
  refine ⟨?_, ?_, ?_, ?_, by linarith, by linarith⟩
  · have := mono (fun t => p.gW a b t ^ 2) (cw.pow 2) q1; linarith
  · have := mono (fun t => p.gW' a b t ^ 2) (cw'.pow 2) q2; linarith
  · have := mono (fun t => g t ^ 2) (cg.pow 2) q3; linarith
  · have := mono (fun t => 2 * -(p.gW a b t * g t)) (by fun_prop) q4
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg] at this
    linarith

@[tmio M, powerlib_domain] private theorem gPath_apply (a b : Fin 2 → ℝ) (t : ℝ) :
    p.gPath a b t 0 = p.gAngle a b t ∧ p.gPath a b t 1 / p.M = p.gVel a b t := by
  have hM := p.M_pos.ne'
  refine ⟨by simp [gPath], ?_⟩
  simp [gPath]; field_simp

/-- **A connecting piece followed by the filter**: the three-state pair from `(a, z₀)` to
`(b, Z)` along the cubic connecting piece, with `2σ_P² S ≤ Q + Q/ω_c + 3Q/ω_c² +` the
boundary terms of `follow_track` (`Q = glueQ a b`). -/
@[tmio TM, powerlib_domain] private theorem glue_track {σP : ℝ} (hσ : σP ≠ 0) {ω : ℝ}
    (hω : 0 < ω) (a b : Fin 2 → ℝ) (z₀ : ℝ) :
    ∃ Z S : ℝ, 0 ≤ S ∧
      (Z - (p.c0 + p.A * Real.sin (b 0 - p.α))) ^ 2 ≤
        (z₀ - (p.c0 + p.A * Real.sin (a 0 - p.α))) ^ 2 + p.glueQ a b / ω ∧
      2 * σP ^ 2 * S ≤ p.glueQ a b + p.glueQ a b / ω + 3 * p.glueQ a b / ω ^ 2 +
        2 / ω * (p.gW a b 0 * (z₀ - (p.c0 + p.A * Real.sin (a 0 - p.α))) -
          p.gW a b 1 * (Z - (p.c0 + p.A * Real.sin (b 0 - p.α)))) +
        2 / ω * ((z₀ - (p.c0 + p.A * Real.sin (a 0 - p.α))) ^ 2 -
          (Z - (p.c0 + p.A * Real.sin (b 0 - p.α))) ^ 2) ∧
      (⟨p, ω, hω⟩ : Params3).setPointQP σP ![a 0, a 1 / p.M, z₀] ![b 0, b 1 / p.M, Z] ≤
        ENNReal.ofReal S := by
  have hcw' : Continuous (p.gW' a b) := by unfold gW' gJerk gAngle gVel gAcc; fun_prop
  obtain ⟨Z, S, hS0, he, hS, hV, -⟩ := Params3.follow_track ⟨p, ω, hω⟩ hσ (z₀ := z₀)
    zero_le_one (φ := p.gPath a b) (u := p.gCtrl σP a b) (w' := p.gW' a b)
    (fun t _ => (p.hasDerivAt_gPath hσ a b t).continuousAt.continuousWithinAt)
    (fun t _ => (p.hasDerivAt_gPath hσ a b t).hasDerivWithinAt)
    (by simp only [gCtrl, gAngle, gVel, gAcc, Matrix.cons_val_zero]; fun_prop)
    (fun t _ => by
      have e : (fun s => σP * p.gCtrl σP a b s 0) = p.gW a b := funext fun s => p.gW_eq hσ a b s
      rw [e]; exact (p.hasDerivAt_gW a b t).hasDerivWithinAt)
    hcw'.continuousOn
  have hω0 := hω
  obtain ⟨q1, q2, q3, q4, -, q6⟩ := p.glue_parts a b
  dsimp only at he hS hV
  rw [p.gPath_zero, p.gPath_one] at he hS hV
  simp only [p.gW_eq hσ, (p.gPath_apply a b _).1, (p.gPath_apply a b _).2] at he hS
  refine ⟨Z, S, hS0, ?_, ?_, hV⟩
  · have := div_le_div_of_nonneg_right q3 hω.le
    linarith
  · have h2 : 2 / ω * -(∫ t in (0 : ℝ)..1, p.gW a b t * (p.A * Real.cos (p.gAngle a b t - p.α) *
        p.gVel a b t)) ≤ 2 / ω * (p.glueQ a b / 2) := mul_le_mul_of_nonneg_left q4 (by positivity)
    have h3 := div_le_div_of_nonneg_right q2 (by positivity : (0 : ℝ) ≤ ω ^ 2)
    have h4 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left q3 (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity : (0 : ℝ) ≤ ω ^ 2)
    have e1 : 2 / ω * (p.glueQ a b / 2) = p.glueQ a b / ω := by ring
    have e2 : 2 * p.glueQ a b / ω ^ 2 + p.glueQ a b / ω ^ 2 = 3 * p.glueQ a b / ω ^ 2 := by ring
    linarith

/-- The equilibria of the well: `P(δ_s) = P(δ_u) = P_ref`, `U(δ_s) < U(δ_u)` and
`cos(δ_u − α) < 0` (`|P_ref − c₀| < A`). -/
@[tmio M, powerlib_domain] private theorem rest_facts (h : |p.Pref - p.c0| < p.A) :
    p.c0 + p.A * Real.sin (p.swingModel.deltaS - p.α) = p.Pref ∧
      p.c0 + p.A * Real.sin (p.swingModel.deltaU - p.α) = p.Pref ∧
      p.potential (p.swingModel.deltaS - p.α) < p.potential (p.swingModel.deltaU - p.α) ∧
      Real.cos (p.swingModel.deltaU - p.α) < 0 := by
  set sp := p.swingModel with hsp
  have hk : 0 < sp.k₂ := p.A_pos
  have habs' : |sp.Pm - sp.k₁| < sp.k₂ := h
  have hsin : p.A * Real.sin (Real.arcsin sp.loadRatio) = p.Pref - p.c0 :=
    sp.sin_loadRatio hk habs'.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : sp.deltaS - p.α = Real.arcsin sp.loadRatio := by
      rw [Synchronous.SwingParams.deltaS]
      show Real.arcsin sp.loadRatio + p.α - p.α = _; ring
    rw [e]; linarith
  · have e : sp.deltaU - p.α = π - Real.arcsin sp.loadRatio := by
      rw [Synchronous.SwingParams.deltaU]
      show π - Real.arcsin sp.loadRatio + p.α - p.α = _; ring
    rw [e, Real.sin_pi_sub]; linarith
  · have h' := p.potential_lt_of_mem h (sp.deltaS_lt_deltaU hk habs') le_rfl le_rfl
    rw [← hsp, Synchronous.SwingParams.potential_self, swingModel_potential] at h'
    linarith
  · have e : sp.deltaU - p.α = π - Real.arcsin sp.loadRatio := by
      rw [Synchronous.SwingParams.deltaU]
      show π - Real.arcsin sp.loadRatio + p.α - p.α = _; ring
    rw [e, Real.cos_pi_sub, Real.cos_arcsin, neg_lt_zero]
    apply Real.sqrt_pos.2
    have h := sp.abs_loadRatio_lt hk habs'
    have : sp.loadRatio ^ 2 < 1 := by
      rw [← sq_abs]; exact pow_lt_one₀ (abs_nonneg _) h (by norm_num)
    linarith

/-- Junction bound: `|2/ω · (x y)| ≤ 2/ω²` for `|x| ≤ 1/ω`, `|y| ≤ 1`, `ω > 0`. -/
@[tmio T, powerlib_foundation] private theorem junction_le {ω x y : ℝ} (hω : 0 < ω)
    (hx : |x| ≤ 1 / ω) (hy : |y| ≤ 1) : |2 / ω * (x * y)| ≤ 2 * (1 / ω ^ 2) := by
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / ω)]
  calc 2 / ω * (|x| * |y|) ≤ 2 / ω * (1 / ω * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hx hy (abs_nonneg _) (by positivity))
          (by positivity)
    _ = 2 * (1 / ω ^ 2) := by field_simp

/-- The action bound of the exact arrival (`setPointQP_saddle_fix`) at `Λ = 1/ω²` and an
initial lag `|x| ≤ 1/ω²` is `O(1/ω²)`. -/
@[tmio T, powerlib_foundation] private theorem fix_le {ω σP A K x : ℝ} (hω : 1 ≤ ω)
    (hσ : σP ≠ 0) (hA : 0 < A) (hK : 0 < K) (hx : |x| ≤ 1 / ω ^ 2) :
    2 * σP ^ 2 * (1 / 2 * (K * (1 / ω ^ 2) / |σP|) ^ 2 + (K * (1 / ω ^ 2) / |σP| *
      (|x| + 2 * (A * (1 / ω ^ 2)) / ω) / |σP| + (|x| + 2 * (A * (1 / ω ^ 2)) / ω) ^ 2 /
        σP ^ 2)) ≤ 2 * (K ^ 2 / 2 + K * (1 + 2 * A) + (1 + 2 * A) ^ 2) * (1 / ω ^ 2) := by
  have hω0 : 0 < ω := by linarith
  have hs : 0 < |σP| := abs_pos.mpr hσ
  have hs2 : |σP| ^ 2 = σP ^ 2 := sq_abs σP
  set r := 1 / ω ^ 2 with hrdef
  have hr : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one (by positivity)]; nlinarith
  have hE : |x| + 2 * (A * r) / ω ≤ (1 + 2 * A) * r := by
    have : 2 * (A * r) / ω ≤ 2 * A * r := by
      rw [div_le_iff₀ hω0]; nlinarith [mul_pos hA hr]
    nlinarith
  have hE0 : 0 ≤ |x| + 2 * (A * r) / ω := by positivity
  have e : 2 * σP ^ 2 * (1 / 2 * (K * r / |σP|) ^ 2 + (K * r / |σP| * (|x| + 2 * (A * r) / ω) /
      |σP| + (|x| + 2 * (A * r) / ω) ^ 2 / σP ^ 2)) =
      K ^ 2 * r ^ 2 + 2 * (K * r * (|x| + 2 * (A * r) / ω)) + 2 * (|x| + 2 * (A * r) / ω) ^ 2 := by
    field_simp; rw [hs2]; ring
  rw [e]
  have h1 : K * r * (|x| + 2 * (A * r) / ω) ≤ K * r * ((1 + 2 * A) * r) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have h2 : (|x| + 2 * (A * r) / ω) ^ 2 ≤ ((1 + 2 * A) * r) ^ 2 := pow_le_pow_left₀ hE0 hE 2
  have h3 : r ^ 2 ≤ r := by nlinarith
  have h4 : 0 ≤ K ^ 2 + 2 * (K * (1 + 2 * A)) + 2 * (1 + 2 * A) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 h4]

/-- **The uphill pair and its quadratic data**: for `η ∈ (0, δ_u − δ_s)` and `ρ > 0`, a
feedback (uphill) pair from `ψ(0)` (within `ρ` of `(δ_s, 0)`) to `(δ_u − η, 0)`; with
`N = ∫ ω²`, `I_q = ∫ ω̇²`, `I_c = ∫ cos(δ − α) ω²`: `D N = U(δ_u − η) − H(ψ(0))`, `N ≤ N_max`,
`I_q ≥ v⁴/(4 N_max)` (from the angle band: `up_speed`, `up_lower`) and
`A I_c = M I_q − G(ψ(0))` (`up_identity`), `I_c ≤ N`. -/
@[tmio TM, powerlib_domain] private theorem uphill_facts {σP : ℝ} (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (habs : |p.Pref - p.c0| < p.A)
    {θa θb f₀ v Nmax η ρ : ℝ} (hv : 0 < v) (hab : θa < θb)
    (hband : ∀ θ ∈ Icc θa θb, f₀ ≤ p.c0 + p.A * Real.sin θ - p.Pref)
    (c3 : 2 * p.D * v ≤ f₀) (c4 : 4 * p.M * v ^ 2 ≤ f₀ * (θb - θa)) (hNmax0 : 0 < Nmax)
    (hη : 0 < η) (hηd : η < p.swingModel.deltaU - p.swingModel.deltaS)
    (hηb : θb ≤ p.swingModel.deltaU - η - p.α) (hρ : 0 < ρ)
    (hρE : ∀ x : Fin 2 → ℝ, dist x ![p.swingModel.deltaS, 0] < ρ → x 0 - p.α < θa ∧
      p.potential (p.swingModel.deltaU - p.α) - p.swingEnergy x ≤ p.D * Nmax) :
    ∃ (L : ℝ) (ψ : ℝ → Fin 2 → ℝ) (u : ℝ → Fin 1 → ℝ), 0 ≤ L ∧
      dist (ψ 0) ![p.swingModel.deltaS, 0] < ρ ∧ ψ L = ![p.swingModel.deltaU - η, 0] ∧
      ContinuousOn ψ (Icc 0 L) ∧ (∀ t ∈ Ico 0 L, HasDerivAt ψ (controlField p.swingDrift
        (fun _ (_ : Fin 1) => swingColumn σP) (ψ t) (u t)) t) ∧
      ContinuousOn (fun t => u t 0) (Icc 0 L) ∧ (∀ t, u t 0 = 2 * p.D * ψ t 1 / (σP * p.M)) ∧
      p.D * (∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2) =
        p.potential (p.swingModel.deltaU - η - p.α) - p.swingEnergy (ψ 0) ∧
      (∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2) ≤ Nmax ∧
      v ^ 4 / (4 * Nmax) ≤ ∫ t in (0 : ℝ)..L, p.upAcc (ψ t) ^ 2 ∧
      p.A * (∫ t in (0 : ℝ)..L, Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M) ^ 2) =
        p.M * (∫ t in (0 : ℝ)..L, p.upAcc (ψ t) ^ 2) + -p.lagG (ψ 0) ∧
      (∫ t in (0 : ℝ)..L, Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M) ^ 2) ≤
        ∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2 := by
  set sp := p.swingModel with hsp
  set δs := sp.deltaS with hδs
  set δu := sp.deltaU with hδu
  have hk : 0 < sp.k₂ := p.A_pos
  have habs' : |sp.Pm - sp.k₁| < sp.k₂ := habs
  have hA := p.A_pos
  obtain ⟨y, hydef⟩ : ∃ y : State 2, y = PhasePlane.mk (δu - η) 0 := ⟨_, rfl⟩
  have hyE : sp.energy δs y = sp.potential δs (δu - η) := by
    simp [hydef, PhasePlane.Conservative.separableEnergy]
  have hpl := p.potential_lt_of_mem habs (a := δu - η) (b := δu) (by linarith) (by linarith)
    le_rfl
  rw [← hsp] at hpl
  have hy1 : sp.energy δs y < sp.potential δs δu := by rw [hyE]; exact hpl
  have hy2 : sp.energy δs y < sp.potential δs (δu - 2 * π) := by
    rw [sp.potential_sub_two_pi]
    have : 0 ≤ sp.Pm - sp.k₁ := by show 0 ≤ p.Pref - p.c0; linarith
    have : 0 ≤ 2 * π * (sp.Pm - sp.k₁) := mul_nonneg (by positivity) this
    linarith
  have hy : y ∈ {x ∈ sp.wellWindow | sp.energy δs x ≤ sp.energy δs y} := by
    refine ⟨⟨?_, ?_⟩, le_rfl⟩
    · simp only [hydef, PhasePlane.mk_apply_zero]
      linarith [sp.deltaU_sub_two_pi_lt_deltaS hk habs']
    · simp only [hydef, PhasePlane.mk_apply_zero]; linarith
  obtain ⟨L, ψ, u, hL0, hz, hψL, hcψ, hder, hucont, hu0, hS⟩ :=
    p.relax_uphill hσ (p.well_attracts hD habs hy1 hy2 hy) hρ
  have hfy : p.flipMom y = ![δu - η, 0] := by
    ext i; fin_cases i <;> simp [flipMom, hydef]
  rw [hfy] at hψL
  have hL1 : ψ L 1 = 0 := by rw [hψL]; simp
  have hL0' : ψ L 0 = δu - η := by rw [hψL]; simp
  have hHL : p.swingEnergy (ψ L) = p.potential (δu - η - p.α) := by rw [hψL, swingEnergy_rest]
  have hUη' : p.potential (δu - η - p.α) < p.potential (δu - p.α) := by
    rw [swingModel_potential, swingModel_potential] at hpl; linarith
  obtain ⟨hz1, hz2⟩ := hρE (ψ 0) hz
  have hvel := p.up_speed hσ hL0 hcψ hder hu0 hab hz1 (by rw [hL0']; exact hηb) hband hv c3 c4
  have hact : controlAction u L = 2 * p.D ^ 2 / σP ^ 2 * ∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2 := by
    unfold controlAction
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1; funext t; simp only [Fin.sum_univ_one, hu0]; field_simp
  have hDN : p.D * (∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2) =
      p.potential (δu - η - p.α) - p.swingEnergy (ψ 0) := by
    have h' : 2 * p.D / σP ^ 2 * (p.D * ∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2) =
        2 * p.D / σP ^ 2 * (p.potential (δu - η - p.α) - p.swingEnergy (ψ 0)) := by
      rw [← hHL, ← hS, hact]; ring
    exact mul_left_cancel₀ (by positivity) h'
  have hNle : (∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2) ≤ Nmax := by
    have : p.D * (∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2) ≤ p.D * Nmax := by rw [hDN]; linarith
    exact le_of_mul_le_mul_left this hD
  have hQlow := p.up_lower hσ hL0 hcψ hder hu0 hL1 hv hNmax0 hNle hvel
  have hid := p.up_identity hσ hL0 hcψ hder hu0
  rw [hψL, p.lagG_rest, zero_sub] at hid
  have hc0 : ContinuousOn (fun t => ψ t 0) (Icc 0 L) := (continuous_apply 0).comp_continuousOn hcψ
  have hc1c : ContinuousOn (fun t => ψ t 1 / p.M) (Icc 0 L) :=
    ((continuous_apply 1).comp_continuousOn hcψ).div_const _
  have hcosc : ContinuousOn (fun t => Real.cos (ψ t 0 - p.α)) (Icc 0 L) :=
    Real.continuous_cos.comp_continuousOn (hc0.sub continuousOn_const)
  have hcosN : ∫ t in (0 : ℝ)..L, Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M) ^ 2 ≤
      ∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2 :=
    intervalIntegral.integral_mono_on hL0
      ((hcosc.mul (hc1c.pow 2)).intervalIntegrable_of_Icc hL0)
      ((hc1c.pow 2).intervalIntegrable_of_Icc hL0) fun t _ =>
        mul_le_of_le_one_left (sq_nonneg _) (Real.cos_le_one _)
  exact ⟨L, ψ, u, hL0, hz, hψL, hcψ, hder, hucont, hu0, hDN, hNle, hQlow, hid, hcosN⟩

/-- **The uphill pair followed by the filter** (`follow_track` with `w = σ_P u = 2Dω`): with
`N`, `I_q`, `I_c` as in `uphill_facts`, `2σ_P² S ≤ 4D²N − (2/ω_c)·2D·A I_c + 4D² I_q/ω_c²
+ 2A²N/ω_c² + (2/ω_c) w(0) e(0) + (2/ω_c)(e(0)² − e(T)²)` (`w(T) = 0` at the rest end). -/
@[tmio TM, powerlib_domain] private theorem uphill_track {σP : ℝ} (hσ : σP ≠ 0) {ω : ℝ}
    (hω : 0 < ω) {L : ℝ} (hL0 : 0 ≤ L) {ψ : ℝ → Fin 2 → ℝ} {u : ℝ → Fin 1 → ℝ}
    (hcψ : ContinuousOn ψ (Icc 0 L))
    (hder : ∀ t ∈ Ico 0 L, HasDerivAt ψ (controlField p.swingDrift
      (fun _ (_ : Fin 1) => swingColumn σP) (ψ t) (u t)) t)
    (hucont : ContinuousOn (fun t => u t 0) (Icc 0 L))
    (hu0 : ∀ t, u t 0 = 2 * p.D * ψ t 1 / (σP * p.M)) (hL1 : ψ L 1 = 0) (z₀ : ℝ) :
    ∃ Z S : ℝ, 0 ≤ S ∧
      (Z - (p.c0 + p.A * Real.sin (ψ L 0 - p.α))) ^ 2 ≤
        (z₀ - (p.c0 + p.A * Real.sin (ψ 0 0 - p.α))) ^ 2 +
          p.A ^ 2 * (∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2) / ω ∧
      2 * σP ^ 2 * S ≤ 4 * p.D ^ 2 * (∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2) -
        2 / ω * (2 * p.D * (p.A * ∫ t in (0 : ℝ)..L,
          Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M) ^ 2)) +
        4 * p.D ^ 2 * (∫ t in (0 : ℝ)..L, p.upAcc (ψ t) ^ 2) / ω ^ 2 +
        2 * (p.A ^ 2 * ∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2) / ω ^ 2 +
        2 / ω * (2 * p.D * ψ 0 1 / p.M * (z₀ - (p.c0 + p.A * Real.sin (ψ 0 0 - p.α)))) +
        2 / ω * ((z₀ - (p.c0 + p.A * Real.sin (ψ 0 0 - p.α))) ^ 2 -
          (Z - (p.c0 + p.A * Real.sin (ψ L 0 - p.α))) ^ 2) ∧
      (⟨p, ω, hω⟩ : Params3).setPointQP σP ![ψ 0 0, ψ 0 1 / p.M, z₀]
        ![ψ L 0, ψ L 1 / p.M, Z] ≤ ENNReal.ofReal S := by
  have hM := p.M_pos.ne'
  have hA := p.A_pos
  have hw2 : ∀ t ∈ Ico 0 L, HasDerivWithinAt (fun s => σP * u s 0) (2 * p.D * p.upAcc (ψ t))
      (Ici t) t := by
    intro t ht
    have e : (fun s => σP * u s 0) = fun s => 2 * p.D * (ψ s 1 / p.M) := funext fun s => by
      rw [hu0]; field_simp
    rw [e]; exact ((p.up_hasDerivAt hσ hder hu0 ht).2.1.const_mul (2 * p.D)).hasDerivWithinAt
  obtain ⟨Z, S, hS0, he, hS, hV, -⟩ := Params3.follow_track ⟨p, ω, hω⟩ hσ (z₀ := z₀) hL0
    (φ := ψ) (u := u) (w' := fun t => 2 * p.D * p.upAcc (ψ t)) hcψ
    (fun t ht => (hder t ht).hasDerivWithinAt) hucont hw2
    (continuousOn_const.mul (p.continuous_upAcc.comp_continuousOn hcψ))
  dsimp only at he hS hV
  have hc1c : ContinuousOn (fun t => ψ t 1 / p.M) (Icc 0 L) :=
    ((continuous_apply 1).comp_continuousOn hcψ).div_const _
  have hg : ∫ t in (0 : ℝ)..L, (p.A * Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M)) ^ 2 ≤
      p.A ^ 2 * ∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    have hc0 : ContinuousOn (fun t => ψ t 0) (Icc 0 L) :=
      (continuous_apply 0).comp_continuousOn hcψ
    refine intervalIntegral.integral_mono_on hL0
      (((continuousOn_const.mul (Real.continuous_cos.comp_continuousOn
        (hc0.sub continuousOn_const))).mul hc1c).pow 2 |>.intervalIntegrable_of_Icc hL0)
      ((continuousOn_const.mul (hc1c.pow 2)).intervalIntegrable_of_Icc hL0) fun t _ => ?_
    have hc2 : Real.cos (ψ t 0 - p.α) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]; exact Real.abs_cos_le_one _
    calc (p.A * Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M)) ^ 2 =
          p.A ^ 2 * (Real.cos (ψ t 0 - p.α) ^ 2 * (ψ t 1 / p.M) ^ 2) := by ring
      _ ≤ p.A ^ 2 * (1 * (ψ t 1 / p.M) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc2 (sq_nonneg _))
            (sq_nonneg _)
      _ = p.A ^ 2 * (ψ t 1 / p.M) ^ 2 := by ring
  have i1 : ∫ t in (0 : ℝ)..L, (σP * u t 0) ^ 2 =
      4 * p.D ^ 2 * ∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; rw [hu0]; field_simp; ring
  have i2 : ∫ t in (0 : ℝ)..L, σP * u t 0 * (p.A * Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M)) =
      2 * p.D * (p.A * ∫ t in (0 : ℝ)..L, Real.cos (ψ t 0 - p.α) * (ψ t 1 / p.M) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1; funext t; rw [hu0]; field_simp
  have i3 : ∫ t in (0 : ℝ)..L, (2 * p.D * p.upAcc (ψ t)) ^ 2 =
      4 * p.D ^ 2 * ∫ t in (0 : ℝ)..L, p.upAcc (ψ t) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  have hu00 : σP * u 0 0 = 2 * p.D * ψ 0 1 / p.M := by rw [hu0]; field_simp
  have hu0L : σP * u L 0 = 0 := by rw [hu0, hL1]; simp
  rw [i1, i2, i3, hu00, hu0L, zero_mul, sub_zero] at hS
  refine ⟨Z, S, hS0, ?_, ?_, hV⟩
  · have := div_le_div_of_nonneg_right hg hω.le
    linarith
  · have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity : (0 : ℝ) ≤ ω ^ 2)
    linarith

/-- Bookkeeping, one connecting piece: `2σ² S ≤ 9/ω² + (2/ω) e₀²`. -/
@[tmio T, powerlib_foundation] private theorem arith_glue {ω σ2 S Q e₀ e w0 w1 : ℝ}
    (hS : 2 * σ2 * S ≤ Q + Q / ω + 3 * Q / ω ^ 2 + 2 / ω * (w0 * e₀ - w1 * e) +
      2 / ω * (e₀ ^ 2 - e ^ 2))
    (hω1 : 1 ≤ ω) (hQ : 0 ≤ Q) (hQ' : Q < 1 / ω ^ 2) (hw0 : w0 ^ 2 ≤ Q) (hw1 : w1 ^ 2 ≤ Q)
    (he₀ : |e₀| ≤ 1) (he : |e| ≤ 1) : 2 * σ2 * S ≤ 9 * (1 / ω ^ 2) + 2 / ω * e₀ ^ 2 := by
  have hω0 : 0 < ω := by linarith
  have hw : ∀ w : ℝ, w ^ 2 ≤ Q → |w| ≤ 1 / ω := fun w h1 =>
    abs_le_of_sq_le_sq (by rw [div_pow, one_pow]; linarith) (by positivity)
  obtain ⟨-, j0⟩ := abs_le.mp (junction_le hω0 (hw _ hw0) he₀)
  obtain ⟨j1, -⟩ := abs_le.mp (junction_le hω0 (hw _ hw1) he)
  have h1 : Q / ω ≤ Q := div_le_self hQ hω1
  have h2 : 3 * Q / ω ^ 2 ≤ 3 * Q := div_le_self (by positivity) (one_le_pow₀ hω1)
  have e1 : 2 / ω * (w0 * e₀ - w1 * e) = 2 / ω * (w0 * e₀) - 2 / ω * (w1 * e) := by ring
  have e2 : 2 / ω * (e₀ ^ 2 - e ^ 2) = 2 / ω * e₀ ^ 2 - 2 / ω * e ^ 2 := by ring
  have : 0 ≤ 2 / ω * e ^ 2 := by positivity
  linarith

/-- Bookkeeping, the uphill piece:
`2σ² S ≤ 4 D ΔU − (2/ω) D M K₀ + (4 + C_q + 2A² N_max)/ω² + (2/ω) e₀²`. -/
@[tmio T, powerlib_foundation] private theorem arith_up
    {ω σ2 S e₀ e wz N Iq Ic G D M A K₀ Nmax Hz Us Uη Uu ΔU Cq : ℝ}
    (hS : 2 * σ2 * S ≤ 4 * D ^ 2 * N - 2 / ω * (2 * D * (A * Ic)) + 4 * D ^ 2 * Iq / ω ^ 2 +
      2 * (A ^ 2 * N) / ω ^ 2 + 2 / ω * (wz * e₀) + 2 / ω * (e₀ ^ 2 - e ^ 2))
    (hω1 : 1 ≤ ω) (hD : 0 < D) (hM : 0 < M) (hA : 0 < A) (hwz : |wz| ≤ 1 / ω) (he₀ : |e₀| ≤ 1)
    (hIc : A * Ic = M * Iq + -G) (hG : |G| < M * K₀ / 2) (hIq : K₀ ≤ Iq) (hIcN : Ic ≤ N)
    (hN : N ≤ Nmax) (hDN : D * N = Uη - Hz) (hUη : Uη < Uu)
    (hHz : -(1 / (2 * D * ω ^ 2)) < Hz - Us) (hΔ : ΔU = Uu - Us)
    (hCq : Cq = 4 * D ^ 2 * (A * Nmax + M * K₀ / 2) / M) :
    2 * σ2 * S ≤ 4 * D * ΔU - 2 / ω * (D * M * K₀) +
      (4 + Cq + 2 * (A ^ 2 * Nmax)) * (1 / ω ^ 2) + 2 / ω * e₀ ^ 2 := by
  have hω0 : 0 < ω := by linarith
  have hsq : 0 < ω ^ 2 := pow_pos hω0 2
  obtain ⟨-, j⟩ := abs_le.mp (junction_le hω0 hwz he₀)
  have hgain : D * M * K₀ ≤ 2 * D * (A * Ic) := by
    rw [hIc]
    have := (abs_lt.mp hG).2
    have h2 : D * M * K₀ ≤ 2 * D * (M * K₀ - M * K₀ / 2) := le_of_eq (by ring)
    have h4 : M * K₀ ≤ M * Iq := mul_le_mul_of_nonneg_left hIq hM.le
    have h3 : 2 * D * (M * K₀ - M * K₀ / 2) ≤ 2 * D * (M * Iq + -G) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hgain' : 2 / ω * (D * M * K₀) ≤ 2 / ω * (2 * D * (A * Ic)) :=
    mul_le_mul_of_nonneg_left hgain (by positivity)
  have hIqup : M * Iq ≤ A * Nmax + M * K₀ / 2 := by
    have := (abs_lt.mp hG).2
    have : A * Ic ≤ A * Nmax := mul_le_mul_of_nonneg_left (hIcN.trans hN) hA.le
    linarith
  have hq2 : 4 * D ^ 2 * Iq / ω ^ 2 ≤ Cq * (1 / ω ^ 2) := by
    rw [mul_one_div]
    refine div_le_div_of_nonneg_right ?_ hsq.le
    rw [hCq, le_div_iff₀ hM]
    have := mul_le_mul_of_nonneg_left hIqup (by positivity : (0 : ℝ) ≤ 4 * D ^ 2)
    linarith
  have hg2 : 2 * (A ^ 2 * N) / ω ^ 2 ≤ 2 * (A ^ 2 * Nmax) * (1 / ω ^ 2) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hN (sq_nonneg _)) (by norm_num)) hsq.le
  have hN4 : 4 * D ^ 2 * N ≤ 4 * D * ΔU + 2 * (1 / ω ^ 2) := by
    have e : 4 * D ^ 2 * N = 4 * D * (D * N) := by ring
    rw [e, hDN, hΔ]
    have h2 : 4 * D * (1 / (2 * D * ω ^ 2)) = 2 * (1 / ω ^ 2) := by field_simp; ring
    have h3 : 4 * D * (Uη - Hz) ≤ 4 * D * (Uu - Us + 1 / (2 * D * ω ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have e2 : 2 / ω * (e₀ ^ 2 - e ^ 2) = 2 / ω * e₀ ^ 2 - 2 / ω * e ^ 2 := by ring
  have : 0 ≤ 2 / ω * e ^ 2 := by positivity
  linarith

/-- **Bookkeeping of the deficit**: the five action bounds of the three-state pair add up to at
most `(2D/σ²) ΔU − (D M K₀/(2σ²))/ω` once `ω ≥ C_tot/(D M K₀)`. -/
@[tmio T, powerlib_foundation] private theorem deficit_arith
    {ω σ2 S₁ S₂ S₃ Sr e₁ e₂ D M K₀ ΔU C₂ Ce Cf Ctot : ℝ}
    (p1 : 2 * σ2 * S₁ ≤ 9 * (1 / ω ^ 2) + 2 / ω * 0 ^ 2)
    (p2 : 2 * σ2 * S₂ ≤ 4 * D * ΔU - 2 / ω * (D * M * K₀) + C₂ * (1 / ω ^ 2) + 2 / ω * e₁ ^ 2)
    (p3 : 2 * σ2 * S₃ ≤ 9 * (1 / ω ^ 2) + 2 / ω * e₂ ^ 2)
    (pr : 2 * σ2 * Sr ≤ (2 * Ce + 2 * Cf) * (1 / ω ^ 2))
    (he₁ : e₁ ^ 2 ≤ 1 / ω ^ 2) (he₂ : e₂ ^ 2 ≤ Ce * (1 / ω))
    (hω1 : 1 ≤ ω) (hσ2 : 0 < σ2) (hD : 0 < D) (hM : 0 < M) (hK₀ : 0 < K₀)
    (hCtot : Ctot = 20 + C₂ + 4 * Ce + 2 * Cf) (hωC : Ctot / (D * M * K₀) ≤ ω) :
    S₁ + (S₂ + (S₃ + Sr)) ≤ 2 * D / σ2 * ΔU - D * M * K₀ / (2 * σ2) / ω := by
  have hω0 : 0 < ω := by linarith
  have hrr : 1 / ω * (1 / ω) = 1 / ω ^ 2 := by rw [div_mul_div_comm, one_mul, sq]
  have hrs : 1 / ω ^ 2 ≤ 1 / ω :=
    one_div_le_one_div_of_le hω0 (by rw [sq]; exact le_mul_of_one_le_right hω0.le hω1)
  have h1 : 2 / ω * e₁ ^ 2 ≤ 2 * (1 / ω ^ 2) := by
    have := mul_le_mul_of_nonneg_left he₁ (by positivity : (0 : ℝ) ≤ 2 / ω)
    have e : 2 / ω * (1 / ω ^ 2) ≤ 2 * (1 / ω ^ 2) := by
      rw [div_mul_eq_mul_div, mul_one_div]
      exact div_le_self (by positivity) hω1 |>.trans_eq (by ring)
    linarith
  have h2 : 2 / ω * e₂ ^ 2 ≤ 2 * Ce * (1 / ω ^ 2) := by
    have := mul_le_mul_of_nonneg_left he₂ (by positivity : (0 : ℝ) ≤ 2 / ω)
    have e : 2 / ω * (Ce * (1 / ω)) = 2 * Ce * (1 / ω ^ 2) := by rw [← hrr]; ring
    linarith
  have h0 : 2 / ω * (0 : ℝ) ^ 2 = 0 := by ring
  have hsum : 2 * σ2 * (S₁ + (S₂ + (S₃ + Sr))) ≤ 4 * D * ΔU - 2 / ω * (D * M * K₀) +
      Ctot * (1 / ω ^ 2) := by
    rw [hCtot]; linarith
  have hC : Ctot * (1 / ω ^ 2) ≤ 1 / ω * (D * M * K₀) := by
    rw [div_le_iff₀ (by positivity)] at hωC
    rw [← hrr]
    have h1 : 0 ≤ 1 / ω := by positivity
    have : Ctot * (1 / ω) ≤ D * M * K₀ := by
      rw [mul_one_div, div_le_iff₀ hω0]; linarith
    calc Ctot * (1 / ω * (1 / ω)) = Ctot * (1 / ω) * (1 / ω) := by ring
      _ ≤ D * M * K₀ * (1 / ω) := mul_le_mul_of_nonneg_right this h1
      _ = 1 / ω * (D * M * K₀) := by ring
  have htot : 2 * σ2 * (S₁ + (S₂ + (S₃ + Sr))) ≤ 4 * D * ΔU - 1 / ω * (D * M * K₀) := by
    have e : 2 / ω * (D * M * K₀) = 2 * (1 / ω * (D * M * K₀)) := by ring
    linarith
  rw [show 2 * D / σ2 * ΔU - D * M * K₀ / (2 * σ2) / ω =
    (4 * D * ΔU - 1 / ω * (D * M * K₀)) / (2 * σ2) by field_simp; ring,
    le_div_iff₀ (by positivity)]
  linarith

/-- **The end at the saddle**: from `(δ_e, 0, Z)` (`P(δ_e) = P_ref`, `cos(δ_e − α) < 0`,
`|Z − P_ref| ≤ 1`) to the saddle `(δ_e, 0, P_ref)`: a unit rest (`setPointQP_rest_le`), then
the exact arrival (`setPointQP_saddle_fix` with `Λ = 1/ω²`), with
`2σ_P² S ≤ 2(Z − P_ref)²/ω + 2 C_f/ω²` for `ω` large in the stated explicit sense. -/
@[tmio TM, powerlib_domain] private theorem saddle_track {σP : ℝ} (hσ : σP ≠ 0) {ω : ℝ}
    (hω0 : 0 < ω) (hω2 : 2 ≤ ω) {δe : ℝ} (he : p.c0 + p.A * Real.sin (δe - p.α) = p.Pref)
    (hcos : Real.cos (δe - p.α) < 0) {κ : ℝ} (hκ : κ = -Real.cos (δe - p.α)) (hκ0 : 0 < κ)
    (hωκ : 2 / κ ≤ ω) (hωe1 : ω ^ 4 * Real.exp (-ω) < p.A * κ / 72)
    (hωe2 : ω ^ 4 * Real.exp (-ω) < 1) {Z : ℝ} (hZ : |Z - p.Pref| ≤ 1) :
    ∃ S : ℝ, 0 ≤ S ∧ 2 * σP ^ 2 * S ≤ 2 * ((Z - p.Pref) ^ 2 / ω) +
      2 * ((2 * p.M + p.A + p.D) ^ 2 / 2 + (2 * p.M + p.A + p.D) * (1 + 2 * p.A) +
        (1 + 2 * p.A) ^ 2) * (1 / ω ^ 2) ∧
      (⟨p, ω, hω0⟩ : Params3).setPointQP σP ![δe, 0, Z] ![δe, 0, p.Pref] ≤
        ENNReal.ofReal S := by
  have hM := p.M_pos
  have hA := p.A_pos
  have hDn := p.D_nonneg
  have hω1 : 1 ≤ ω := by linarith
  have hωsq : 0 < ω ^ 2 := pow_pos hω0 2
  have hr : 0 < 1 / ω ^ 2 := div_pos one_pos hωsq
  obtain ⟨Sr, hSr0, hSr, hVr⟩ := Params3.setPointQP_rest_le ⟨p, ω, hω0⟩ hσ he Z
  dsimp only at hSr hVr
  have hexp1 : Real.exp (-ω) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx1 : |p.Pref + (Z - p.Pref) * Real.exp (-ω) - p.Pref| ≤ Real.exp (-ω) := by
    rw [add_sub_cancel_left, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le hZ
  have hx2 : Real.exp (-ω) ≤ 1 / ω ^ 2 := by
    rw [le_div_iff₀ hωsq]
    have : ω ^ 2 * Real.exp (-ω) ≤ ω ^ 4 * Real.exp (-ω) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hω1 (by norm_num)) (Real.exp_pos _).le
    linarith
  have hΛκ : 1 / ω ^ 2 ≤ -Real.cos (δe - p.α) / 2 := by
    rw [← hκ]
    have h1 : 1 / ω ≤ κ / 2 := by
      rw [div_le_iff₀ hω0]; rw [div_le_iff₀ hκ0] at hωκ; linarith
    have h2 : 1 / ω ^ 2 ≤ 1 / ω :=
      one_div_le_one_div_of_le hω0 (by rw [sq]; exact le_mul_of_one_le_right hω0.le hω1)
    linarith
  have hz' : 72 * ω ^ 2 * Real.exp (-ω) * |p.Pref + (Z - p.Pref) * Real.exp (-ω) - p.Pref| ≤
      p.A * -Real.cos (δe - p.α) * (1 / ω ^ 2) := by
    rw [← hκ, mul_one_div, le_div_iff₀ hωsq]
    have h1 : 72 * ω ^ 2 * Real.exp (-ω) * |p.Pref + (Z - p.Pref) * Real.exp (-ω) - p.Pref| ≤
        72 * ω ^ 2 * Real.exp (-ω) * Real.exp (-ω) :=
      mul_le_mul_of_nonneg_left hx1 (by positivity)
    have h2 : 72 * ω ^ 2 * Real.exp (-ω) * Real.exp (-ω) * ω ^ 2 =
        72 * (ω ^ 4 * Real.exp (-ω)) * Real.exp (-ω) := by ring
    have h3 : 72 * (ω ^ 4 * Real.exp (-ω)) * Real.exp (-ω) ≤ 72 * (ω ^ 4 * Real.exp (-ω)) :=
      mul_le_of_le_one_right (by positivity) hexp1
    have h4 := mul_le_mul_of_nonneg_right h1 hωsq.le
    linarith
  have hVf := Params3.setPointQP_saddle_fix ⟨p, ω, hω0⟩ hσ he hcos hr hΛκ hω2
    (z₃ := p.Pref + (Z - p.Pref) * Real.exp (-ω)) hz'
  dsimp only at hVf
  have hSf := fix_le hω1 hσ hA (K := 2 * p.M + p.A + p.D) (by positivity) (hx1.trans hx2)
  have hSf0 : 0 ≤ 1 / 2 * ((2 * p.M + p.A + p.D) * (1 / ω ^ 2) / |σP|) ^ 2 +
      ((2 * p.M + p.A + p.D) * (1 / ω ^ 2) / |σP| * (|p.Pref + (Z - p.Pref) * Real.exp (-ω) -
        p.Pref| + 2 * (p.A * (1 / ω ^ 2)) / ω) / |σP| + (|p.Pref + (Z - p.Pref) *
          Real.exp (-ω) - p.Pref| + 2 * (p.A * (1 / ω ^ 2)) / ω) ^ 2 / σP ^ 2) := by
    positivity
  refine ⟨_, add_nonneg hSr0 hSf0, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hSr (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  · refine ((controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hVr hVf)).trans ?_
    rw [← ENNReal.ofReal_add hSr0 hSf0]

/-- **The deficit at one bandwidth** (the uniform data of `deficit_core` fixed): the five-piece
three-state pair (`glue_track`, `uphill_facts` + `uphill_track`, `glue_track`,
`setPointQP_rest_le`, `setPointQP_saddle_fix`) has action at most
`(2D/σ_P²) ΔU − (D M K₀/(2σ_P²))/ω_c`. -/
@[tmio TM, powerlib_domain] private theorem deficit_at {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (habs : |p.Pref - p.c0| < p.A)
    (hes : p.c0 + p.A * Real.sin (p.swingModel.deltaS - p.α) = p.Pref)
    (heu : p.c0 + p.A * Real.sin (p.swingModel.deltaU - p.α) = p.Pref)
    (hcosu : Real.cos (p.swingModel.deltaU - p.α) < 0)
    {Us Uu ΔU θa θb f₀ v Nmax K₀ κ Ce Cf Cq Ctot ρ₁ ρ₂ ω : ℝ}
    (hUs : Us = p.potential (p.swingModel.deltaS - p.α))
    (hUu : Uu = p.potential (p.swingModel.deltaU - p.α)) (hΔ : ΔU = Uu - Us) (hΔU : 0 < ΔU)
    (hab : θa < θb) (hθa : p.swingModel.deltaS - p.α < θa)
    (hθb : θb + (θa - (p.swingModel.deltaS - p.α)) ≤ p.swingModel.deltaU - p.α)
    (hband : ∀ θ ∈ Icc θa θb, f₀ ≤ p.c0 + p.A * Real.sin θ - p.Pref)
    (hv : 0 < v) (c3 : 2 * p.D * v ≤ f₀) (c4 : 4 * p.M * v ^ 2 ≤ f₀ * (θb - θa))
    (hNmax : Nmax = 2 * ΔU / p.D) (hNmax0 : 0 < Nmax) (hK₀ : K₀ = v ^ 4 / (4 * Nmax))
    (hK₀0 : 0 < K₀) (hρ₁ : 0 < ρ₁)
    (hE1 : ∀ {x : Fin 2 → ℝ}, dist x ![p.swingModel.deltaS, 0] < ρ₁ →
      dist (p.swingEnergy x) (p.swingEnergy ![p.swingModel.deltaS, 0]) < ΔU / 8)
    (hρ₂ : 0 < ρ₂) (hG1 : ∀ {x : Fin 2 → ℝ}, dist x ![p.swingModel.deltaS, 0] < ρ₂ →
      dist (p.lagG x) (p.lagG ![p.swingModel.deltaS, 0]) < p.M * K₀ / 2)
    (hκ : κ = -Real.cos (p.swingModel.deltaU - p.α)) (hκ0 : 0 < κ)
    (hCe : Ce = 2 + p.A ^ 2 * Nmax)
    (hCf : Cf = (2 * p.M + p.A + p.D) ^ 2 / 2 + (2 * p.M + p.A + p.D) * (1 + 2 * p.A) +
      (1 + 2 * p.A) ^ 2)
    (hCq : Cq = 4 * p.D ^ 2 * (p.A * Nmax + p.M * K₀ / 2) / p.M)
    (hCtot : Ctot = 24 + Cq + 2 * (p.A ^ 2 * Nmax) + 4 * Ce + 2 * Cf)
    (hω0 : 0 < ω) (hω2 : 2 ≤ ω) (hωCe : Ce ≤ ω) (hωC : Ctot / (p.D * p.M * K₀) ≤ ω)
    (hωκ : 2 / κ ≤ ω) (hωe1 : ω ^ 4 * Real.exp (-ω) < p.A * κ / 72)
    (hωe2 : ω ^ 4 * Real.exp (-ω) < 1) :
    (⟨p, ω, hω0⟩ : Params3).setPointQP σP ![p.swingModel.deltaS, 0, p.Pref]
        ![p.swingModel.deltaU, 0, p.Pref] ≤
      ENNReal.ofReal (2 * p.D / σP ^ 2 * ΔU - p.D * p.M * K₀ / (2 * σP ^ 2) / ω) := by
  set δs := p.swingModel.deltaS with hδs
  set δu := p.swingModel.deltaU with hδu
  have hM := p.M_pos
  have hA := p.A_pos
  have hω1 : 1 ≤ ω := by linarith
  have hωsq : 0 < ω ^ 2 := pow_pos hω0 2
  have hr : 0 < 1 / ω ^ 2 := div_pos one_pos hωsq
  have hr1 : 1 / ω ^ 2 ≤ 1 / ω :=
    one_div_le_one_div_of_le hω0 (by rw [sq]; exact le_mul_of_one_le_right hω0.le hω1)
  -- the radii for this `ω`
  obtain ⟨ρs, hρs, hgs⟩ := p.glueQ_small hes hr
  obtain ⟨ρu, hρu, hgu⟩ := p.glueQ_small heu hr
  have hEc : Continuous p.swingEnergy :=
    continuous_iff_continuousAt.2 fun x => (p.hasFDerivAt_swingEnergy x).continuousAt
  have hε4 : 0 < 1 / (2 * p.D * ω ^ 2) := div_pos one_pos (mul_pos (by positivity) hωsq)
  obtain ⟨ρ₄, hρ₄, hE4⟩ := Metric.continuousAt_iff.mp (hEc.continuousAt (x := ![δs, 0]))
    (1 / (2 * p.D * ω ^ 2)) hε4
  have hρ5 : 0 < p.M / (2 * p.D * ω) := div_pos hM (mul_pos (by positivity) hω0)
  have hgapθ : 0 < θa - (δs - p.α) := by linarith
  obtain ⟨ρ, hρdef⟩ : ∃ x : ℝ, x = min (min (min ρ₁ ρ₂) (θa - (δs - p.α)))
      (min (min ρs ρ₄) (p.M / (2 * p.D * ω))) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by
    rw [hρdef]; exact lt_min (lt_min (lt_min hρ₁ hρ₂) hgapθ) (lt_min (lt_min hρs hρ₄) hρ5)
  have hρ1 : ρ ≤ ρ₁ := by
    rw [hρdef]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρθ : ρ ≤ θa - (δs - p.α) := by
    rw [hρdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨η, hηdef⟩ : ∃ x : ℝ, x = min (ρu / 2) (min (θa - (δs - p.α)) ((δu - δs) / 2)) :=
    ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hηdef]; exact lt_min (by linarith) (lt_min hgapθ (by linarith))
  have hηu : η < ρu := by rw [hηdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηθ : η ≤ θa - (δs - p.α) := by
    rw [hηdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hηd : η < δu - δs := by
    rw [hηdef]; exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  have hErest : p.swingEnergy ![δs, 0] = Us := by rw [hUs]; exact p.swingEnergy_rest δs
  -- the uphill pair
  obtain ⟨L, ψ, u, hL0, hz, hψL, hcψ, hder, hucont, hu0, hDN, hNle, hQlow, hid, hcosN⟩ :=
    p.uphill_facts hσ hD h0 habs (θa := θa) (θb := θb) (f₀ := f₀) (Nmax := Nmax) (η := η)
      (ρ := ρ) hv hab hband c3 c4 hNmax0 hη hηd (by linarith) hρ (fun x hx => by
        have h := hE1 (hx.trans_le hρ1)
        rw [Real.dist_eq, hErest, abs_lt] at h
        refine ⟨?_, ?_⟩
        · have h' : |x 0 - δs| ≤ dist x ![δs, 0] := by
            have := dist_le_pi_dist x ![δs, 0] 0; simpa [Real.dist_eq] using this
          have := (abs_lt.mp (h'.trans_lt (hx.trans_le hρθ))).2
          linarith
        · have hDN : p.D * Nmax = 2 * ΔU := by rw [hNmax]; field_simp
          rw [← hUu, hDN]
          linarith)
  rw [← hK₀] at hQlow
  have hL1 : ψ L 1 = 0 := by rw [hψL]; simp
  have hzd : dist (ψ 0) ![δs, 0] < ρ := hz
  rw [hρdef] at hzd
  have hz2 : dist (ψ 0) ![δs, 0] < ρ₂ :=
    hzd.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hzs : dist (ψ 0) ![δs, 0] < ρs :=
    hzd.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hz4 : dist (ψ 0) ![δs, 0] < ρ₄ :=
    hzd.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hz5 : dist (ψ 0) ![δs, 0] < p.M / (2 * p.D * ω) :=
    hzd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hHz4 := hE4 hz4
  rw [Real.dist_eq, hErest, abs_lt] at hHz4
  have hGz := hG1 hz2
  rw [Real.dist_eq, p.lagG_rest, sub_zero] at hGz
  have hQ1 : p.glueQ ![δs, 0] (ψ 0) < 1 / ω ^ 2 := hgs _ _ (by simp [hρs]) hzs
  have hzω : |2 * p.D * ψ 0 1 / p.M| ≤ 1 / ω := by
    have h' : |ψ 0 1| ≤ dist (ψ 0) ![δs, 0] := by
      have := dist_le_pi_dist (ψ 0) ![δs, 0] 1; simpa [Real.dist_eq] using this
    have h'' : |ψ 0 1| ≤ p.M / (2 * p.D * ω) := (h'.trans_lt hz5).le
    rw [abs_div, abs_mul, abs_of_pos hM, abs_of_pos (by positivity : (0 : ℝ) < 2 * p.D),
      div_le_iff₀ hM]
    calc 2 * p.D * |ψ 0 1| ≤ 2 * p.D * (p.M / (2 * p.D * ω)) :=
          mul_le_mul_of_nonneg_left h'' (by positivity)
      _ = 1 / ω * p.M := by field_simp
  have hQ3 : p.glueQ ![δu - η, 0] ![δu, 0] < 1 / ω ^ 2 := by
    refine hgu _ _ ?_ (by simp [hρu])
    rw [dist_pi_lt_iff hρu]
    intro i; fin_cases i
    · show dist (δu - η) δu < ρu
      rw [Real.dist_eq, show δu - η - δu = -η by ring, abs_neg, abs_of_pos hη]
      exact hηu
    · show dist (0 : ℝ) 0 < ρu
      simpa using hρu
  have hUη' : p.potential (δu - η - p.α) < Uu := by
    have h := p.potential_lt_of_mem habs (a := δu - η) (b := δu) (by linarith) (by linarith)
      le_rfl
    rw [swingModel_potential, swingModel_potential] at h
    rw [hUu]; linarith
  -- the pieces followed by the filter
  obtain ⟨Z₁, S₁, hS₁0, he₁, hS₁, hV₁⟩ := p.glue_track hσ hω0 ![δs, 0] (ψ 0) p.Pref
  obtain ⟨Z₂, S₂, hS₂0, he₂, hS₂, hV₂⟩ := p.uphill_track hσ hω0 hL0 hcψ hder hucont hu0 hL1 Z₁
  obtain ⟨Z₃, S₃, hS₃0, he₃, hS₃, hV₃⟩ := p.glue_track hσ hω0 ![δu - η, 0] ![δu, 0] Z₂
  rw [hψL] at he₂ hS₂ hV₂
  have hP0 : p.Pref - (p.c0 + p.A * Real.sin ((![δs, 0] : Fin 2 → ℝ) 0 - p.α)) = 0 := by
    simp [hes]
  have hPu : p.c0 + p.A * Real.sin ((![δu, 0] : Fin 2 → ℝ) 0 - p.α) = p.Pref := by simpa using heu
  rw [hP0] at he₁ hS₁
  rw [hPu] at he₃ hS₃
  obtain ⟨-, -, -, -, q5, q6⟩ := p.glue_parts ![δs, 0] (ψ 0)
  obtain ⟨-, -, -, -, r5, r6⟩ := p.glue_parts ![δu - η, 0] ![δu, 0]
  have hQ1' : 0 ≤ p.glueQ ![δs, 0] (ψ 0) := (sq_nonneg _).trans q6
  have hQ3' : 0 ≤ p.glueQ ![δu - η, 0] ![δu, 0] := (sq_nonneg _).trans r6
  -- the lags stay small
  have hq1 : p.glueQ ![δs, 0] (ψ 0) / ω ≤ 1 / ω ^ 2 := (div_le_self hQ1' hω1).trans hQ1.le
  have hq3 : p.glueQ ![δu - η, 0] ![δu, 0] / ω ≤ 1 / ω ^ 2 := (div_le_self hQ3' hω1).trans hQ3.le
  have hAN : p.A ^ 2 * (∫ t in (0 : ℝ)..L, (ψ t 1 / p.M) ^ 2) / ω ≤ p.A ^ 2 * Nmax * (1 / ω) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNle (sq_nonneg _)) hω0.le
  have hE1' : (Z₁ - (p.c0 + p.A * Real.sin (ψ 0 0 - p.α))) ^ 2 ≤ 1 / ω ^ 2 := by
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    linarith
  have hE2' : (Z₂ - (p.c0 + p.A * Real.sin ((![δu - η, 0] : Fin 2 → ℝ) 0 - p.α))) ^ 2 ≤
      Ce * (1 / ω) := by
    have e : Ce * (1 / ω) = 2 * (1 / ω) + p.A ^ 2 * Nmax * (1 / ω) := by rw [hCe]; ring
    linarith
  have hE3' : (Z₃ - p.Pref) ^ 2 ≤ Ce * (1 / ω) := by
    have e : Ce * (1 / ω) = 2 * (1 / ω) + p.A ^ 2 * Nmax * (1 / ω) := by rw [hCe]; ring
    linarith
  have hCes : Ce * (1 / ω) ≤ 1 := by rw [mul_one_div, div_le_one hω0]; exact hωCe
  have habs1 : ∀ x : ℝ, x ^ 2 ≤ 1 → |x| ≤ 1 := fun x hx =>
    abs_le_of_sq_le_sq (by rw [one_pow]; exact hx) zero_le_one
  have ha1 := habs1 _ (hE1'.trans (hr1.trans (by rw [div_le_one hω0]; exact hω1)))
  have ha2 := habs1 _ (hE2'.trans hCes)
  have ha3 := habs1 _ (hE3'.trans hCes)
  -- the end at the saddle
  obtain ⟨Ss, hSs0, hSs, hVs⟩ := p.saddle_track hσ hω0 hω2 heu hcosu hκ hκ0 hωκ hωe1 hωe2 ha3
  rw [← hCf] at hSs
  -- the chain of pieces
  have e1 : (![(![δs, 0] : Fin 2 → ℝ) 0, (![δs, 0] : Fin 2 → ℝ) 1 / p.M, p.Pref] : Fin 3 → ℝ) =
      ![δs, 0, p.Pref] := by simp
  have e3 : (![(![δu, 0] : Fin 2 → ℝ) 0, (![δu, 0] : Fin 2 → ℝ) 1 / p.M, Z₃] : Fin 3 → ℝ) =
      ![δu, 0, Z₃] := by simp
  rw [e1] at hV₁
  rw [e3] at hV₃
  have hchain := (controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hV₁
    ((controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hV₂
      ((controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hV₃ hVs)))))
  refine hchain.trans ?_
  rw [← ENNReal.ofReal_add hS₃0 hSs0, ← ENNReal.ofReal_add hS₂0 (add_nonneg hS₃0 hSs0),
    ← ENNReal.ofReal_add hS₁0 (add_nonneg hS₂0 (add_nonneg hS₃0 hSs0))]
  apply ENNReal.ofReal_le_ofReal
  have p1 := arith_glue hS₁ hω1 hQ1' hQ1 q5 q6 (by simp) ha1
  have p2 := arith_up hS₂ hω1 hD hM hA hzω ha1 hid hGz hQlow hcosN hNle hDN hUη' hHz4.1 hΔ hCq
  have p3 := arith_glue hS₃ hω1 hQ3' hQ3 r5 r6 ha2 ha3
  have pr : 2 * σP ^ 2 * Ss ≤ (2 * Ce + 2 * Cf) * (1 / ω ^ 2) := by
    have h1 : (Z₃ - p.Pref) ^ 2 / ω ≤ Ce * (1 / ω) * (1 / ω) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_right hE3' (by positivity)
    have hrr : 1 / ω * (1 / ω) = 1 / ω ^ 2 := by rw [div_mul_div_comm, one_mul, sq]
    rw [mul_assoc, hrr] at h1
    linarith
  exact deficit_arith p1 p2 p3 pr hE1' hE2' hω1 (by positivity) hD hM hK₀0
    (by rw [hCtot]; ring) hωC

/-- `ω⁴ e^{−ω} < m` for `ω ≥ 240 max(1/m', 1)`-type thresholds: `e^ω ≥ ω⁵/120`. -/
@[tmio T, powerlib_foundation] private theorem pow_four_mul_exp_neg_lt {ω m : ℝ} (hm : 0 < m)
    (hω : 240 * max (1 / m) 1 ≤ ω) : ω ^ 4 * Real.exp (-ω) < m ∧ ω ^ 4 * Real.exp (-ω) < 1 := by
  have hm1 : 1 ≤ max (1 / m) 1 := le_max_right _ _
  have hω0 : 0 < ω := by linarith
  have he := Real.pow_div_factorial_le_exp ω hω0.le 5
  have hf : (Nat.factorial 5 : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf] at he
  have h1 : ω ^ 4 * Real.exp (-ω) ≤ 120 / ω := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hω0]
    nlinarith [pow_pos hω0 4]
  have h2 : 120 / ω ≤ 1 / (2 * max (1 / m) 1) := by
    rw [div_le_div_iff₀ hω0 (by positivity)]; linarith
  have h3 : 1 / (2 * max (1 / m) 1) < m := by
    rw [div_lt_iff₀ (by positivity)]
    have : 1 / m ≤ max (1 / m) 1 := le_max_left _ _
    rw [div_le_iff₀ hm] at this
    nlinarith
  have h4 : 1 / (2 * max (1 / m) 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  exact ⟨by linarith, by linarith⟩

/-! ### Explicit constants of the first-order deficit -/

/-- The barrier `ΔU = U(π − arcsin s) − U(arcsin s)` of the well (`s = (P_ref − c₀)/A`,
`U = Params.potential` of the shifted angle). -/
def escBarrier : ℝ :=
  p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
    p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))

/-- The band angle `θ_a = (arcsin s + π/2)/2`; on `[θ_a, π − θ_a]`, `P − P_ref ≥ escBandGap`. -/
def escBandAngle : ℝ := (Real.arcsin ((p.Pref - p.c0) / p.A) + π / 2) / 2

/-- The power gap `f₀ = A sin θ_a − (P_ref − c₀)` on the band (`= A (√((1 + s)/2) − s)`). -/
def escBandGap : ℝ := p.A * Real.sin p.escBandAngle - (p.Pref - p.c0)

/-- The speed `v = min(1, f₀/(2D), f₀ (π/2 − arcsin s)/(4M))` reached on the band. -/
def escSpeed : ℝ := min (min 1 (p.escBandGap / (2 * p.D)))
  (p.escBandGap * (π / 2 - Real.arcsin ((p.Pref - p.c0) / p.A)) / (4 * p.M))

/-- The gain constant `D M K₀`, `K₀ = v⁴/(4 N_max)`, `N_max = 2ΔU/D`. -/
def escGain : ℝ := p.D * p.M * (p.escSpeed ^ 4 / (4 * (2 * p.escBarrier / p.D)))

/-- The explicit bandwidth threshold `ω*` of the first-order deficit:
`max(2, C_e, C_tot/(D M K₀), 2/κ, 240 max(72/(A κ), 1))` with `κ = √(1 − s²)`,
`C_e = 2 + A² N_max`, `C_f = K²/2 + K(1 + 2A) + (1 + 2A)²` (`K = 2M + A + D`),
`C_q = 4D²(A N_max + M K₀/2)/M`, `C_tot = 24 + C_q + 2A² N_max + 4 C_e + 2 C_f`. -/
def escThreshold : ℝ :=
  max (max 2 (2 + p.A ^ 2 * (2 * p.escBarrier / p.D)))
    (max ((24 + 4 * p.D ^ 2 * (p.A * (2 * p.escBarrier / p.D) + p.M *
        (p.escSpeed ^ 4 / (4 * (2 * p.escBarrier / p.D))) / 2) / p.M +
      2 * (p.A ^ 2 * (2 * p.escBarrier / p.D)) + 4 * (2 + p.A ^ 2 * (2 * p.escBarrier / p.D)) +
      2 * ((2 * p.M + p.A + p.D) ^ 2 / 2 + (2 * p.M + p.A + p.D) * (1 + 2 * p.A) +
        (1 + 2 * p.A) ^ 2)) / p.escGain)
      (max (2 / √(1 - ((p.Pref - p.c0) / p.A) ^ 2))
        (240 * max (1 / (p.A * √(1 - ((p.Pref - p.c0) / p.A) ^ 2) / 72)) 1)))

@[tmio M, powerlib_domain] private theorem esc_angles :
    p.swingModel.deltaS - p.α = Real.arcsin ((p.Pref - p.c0) / p.A) ∧
      p.swingModel.deltaU - p.α = π - Real.arcsin ((p.Pref - p.c0) / p.A) := by
  constructor
  · show Real.arcsin ((p.Pref - p.c0) / p.A) + p.α - p.α = _; ring
  · show π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α - p.α = _; ring

@[tmio M, powerlib_domain] private theorem escBarrier_pos (h0 : p.c0 ≤ p.Pref)
    (h1 : p.Pref < p.c0 + p.A) : 0 < p.escBarrier := by
  have habs : |p.Pref - p.c0| < p.A := abs_lt.2 ⟨by linarith [p.A_pos], by linarith⟩
  obtain ⟨-, -, hgap, -⟩ := p.rest_facts habs
  obtain ⟨e1, e2⟩ := p.esc_angles
  rw [e1, e2] at hgap
  simp only [escBarrier]; linarith

@[tmio M, powerlib_domain] private theorem escBandGap_pos (h0 : p.c0 ≤ p.Pref)
    (h1 : p.Pref < p.c0 + p.A) : 0 < p.escBandGap := by
  have hA := p.A_pos
  have hs1 : (p.Pref - p.c0) / p.A < 1 := by rw [div_lt_one hA]; linarith
  have has1 := Real.arcsin_lt_pi_div_two.mpr hs1
  have has0 := Real.neg_pi_div_two_le_arcsin ((p.Pref - p.c0) / p.A)
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two has0
    (show p.escBandAngle ≤ π / 2 by simp only [escBandAngle]; linarith)
    (show Real.arcsin ((p.Pref - p.c0) / p.A) < p.escBandAngle by
      simp only [escBandAngle]; linarith)
  rw [Real.sin_arcsin (by rw [le_div_iff₀ hA]; linarith) hs1.le] at h
  have e : p.escBandGap = p.A * (Real.sin p.escBandAngle - (p.Pref - p.c0) / p.A) := by
    simp only [escBandGap]; field_simp [hA.ne']
  rw [e]; exact mul_pos hA (by linarith)

@[tmio M, powerlib_domain] private theorem escGain_pos (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref)
    (h1 : p.Pref < p.c0 + p.A) : 0 < p.escGain := by
  have hA := p.A_pos
  have hM := p.M_pos
  have hf := p.escBandGap_pos h0 h1
  have hb := p.escBarrier_pos h0 h1
  have hs1 : (p.Pref - p.c0) / p.A < 1 := by rw [div_lt_one hA]; linarith
  have hw : 0 < π / 2 - Real.arcsin ((p.Pref - p.c0) / p.A) := by
    linarith [Real.arcsin_lt_pi_div_two.mpr hs1]
  have hv : 0 < p.escSpeed := lt_min (lt_min one_pos (div_pos hf (by positivity)))
    (div_pos (mul_pos hf hw) (by positivity))
  simp only [escGain]
  positivity

/-- **The explicit deficit (core)**: for `ω_c ≥ escThreshold`, the three-state escape exponent
is at most `(2D/σ_P²) ΔU − escGain/(2σ_P² ω_c)` (`deficit_at` with the angle band
`[θ_a, π − θ_a]` of `escBandAngle` and `v = escSpeed`). -/
@[tmio TM, powerlib_domain] private theorem deficit_explicit {σP : ℝ} (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {ω : ℝ} (hω0 : 0 < ω)
    (hωT : p.escThreshold ≤ ω) :
    (⟨p, ω, hω0⟩ : Params3).setPointQP σP ![p.swingModel.deltaS, 0, p.Pref]
        ![p.swingModel.deltaU, 0, p.Pref] ≤
      ENNReal.ofReal (2 * p.D / σP ^ 2 * p.escBarrier - p.escGain / (2 * σP ^ 2) / ω) := by
  set sp := p.swingModel with hsp
  have habs : |p.Pref - p.c0| < p.A := abs_lt.2 ⟨by linarith [p.A_pos], by linarith⟩
  obtain ⟨hes, heu, hgap, hcosu⟩ := p.rest_facts habs
  have hM := p.M_pos
  have hA := p.A_pos
  set s := (p.Pref - p.c0) / p.A with hsdef
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hA.le
  have hs1 : s < 1 := by rw [div_lt_one hA]; linarith
  have hδs : sp.deltaS - p.α = Real.arcsin s := by
    show Real.arcsin ((p.Pref - p.c0) / p.A) + p.α - p.α = _; rw [hsdef]; ring
  have hδu : sp.deltaU - p.α = π - Real.arcsin s := by
    show π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α - p.α = _; rw [hsdef]; ring
  have has1 : Real.arcsin s < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have has0 : -(π / 2) ≤ Real.arcsin s := Real.neg_pi_div_two_le_arcsin s
  -- the barrier
  have hΔ : p.escBarrier = p.potential (sp.deltaU - p.α) - p.potential (sp.deltaS - p.α) := by
    rw [hδs, hδu]; rfl
  have hΔU : 0 < p.escBarrier := by rw [hΔ]; linarith
  -- the angle band
  set θa := p.escBandAngle with hθa
  have hθa' : θa = (Real.arcsin s + π / 2) / 2 := rfl
  have hab : θa < π - θa := by rw [hθa']; linarith
  have hθs : sp.deltaS - p.α < θa := by rw [hδs, hθa']; linarith
  have hθb : π - θa + (θa - (sp.deltaS - p.α)) ≤ sp.deltaU - p.α := by rw [hδs, hδu]; linarith
  have hf₀ : 0 < p.escBandGap := p.escBandGap_pos h0 h1
  have hband : ∀ θ ∈ Icc θa (π - θa), p.escBandGap ≤ p.c0 + p.A * Real.sin θ - p.Pref := by
    intro θ hθ
    have := sin_ge_of_mem_band (by rw [hθa']; linarith) hθ
    have : p.A * Real.sin θa ≤ p.A * Real.sin θ := mul_le_mul_of_nonneg_left this hA.le
    simp only [escBandGap]; linarith
  -- the speed
  have hw : π - θa - θa = π / 2 - Real.arcsin s := by rw [hθa']; ring
  have hw0 : 0 < π / 2 - Real.arcsin s := by linarith
  have hvmin : p.escSpeed = min (min 1 (p.escBandGap / (2 * p.D)))
      (p.escBandGap * (π / 2 - Real.arcsin s) / (4 * p.M)) := by rw [escSpeed, hsdef]
  set v := p.escSpeed with hvdef
  have hv : 0 < v := by
    rw [hvmin]
    exact lt_min (lt_min one_pos (div_pos hf₀ (by positivity)))
      (div_pos (mul_pos hf₀ hw0) (by positivity))
  have hv1 : v ≤ 1 := by rw [hvmin]; exact (min_le_left _ _).trans (min_le_left _ _)
  have c3 : 2 * p.D * v ≤ p.escBandGap := by
    have : v ≤ p.escBandGap / (2 * p.D) := by
      rw [hvmin]; exact (min_le_left _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have c4 : 4 * p.M * v ^ 2 ≤ p.escBandGap * (π - θa - θa) := by
    have h1' : v ≤ p.escBandGap * (π / 2 - Real.arcsin s) / (4 * p.M) := by
      rw [hvmin]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1'
    have h2 : v ^ 2 ≤ v := pow_le_of_le_one hv.le hv1 two_ne_zero
    have h3 : 4 * p.M * v ^ 2 ≤ 4 * p.M * v := mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [hw]; linarith
  -- the constants
  set ΔU := p.escBarrier with hΔUdef
  set Nmax := 2 * ΔU / p.D with hNmax
  have hNmax0 : 0 < Nmax := div_pos (by linarith) hD
  set K₀ := v ^ 4 / (4 * Nmax) with hK₀
  have hK₀0 : 0 < K₀ := div_pos (pow_pos hv 4) (by linarith)
  have hgain : p.escGain = p.D * p.M * K₀ := rfl
  have hEc : Continuous p.swingEnergy :=
    continuous_iff_continuousAt.2 fun x => (p.hasFDerivAt_swingEnergy x).continuousAt
  obtain ⟨ρ₁, hρ₁, hE1⟩ := Metric.continuousAt_iff.mp (hEc.continuousAt (x := ![sp.deltaS, 0]))
    (ΔU / 8) (by positivity)
  obtain ⟨ρ₂, hρ₂, hG1⟩ := Metric.continuousAt_iff.mp
    (p.continuous_lagG.continuousAt (x := ![sp.deltaS, 0])) (p.M * K₀ / 2) (by positivity)
  set κ := √(1 - s ^ 2) with hκdef
  have hκ : κ = -Real.cos (sp.deltaU - p.α) := by
    rw [hδu, Real.cos_pi_sub, Real.cos_arcsin, neg_neg]
  have hκ0 : 0 < κ := Real.sqrt_pos.2 (by nlinarith)
  -- the threshold
  have hT := hωT
  simp only [escThreshold] at hT
  simp only [← hsdef, ← hκdef, ← hΔUdef, ← hvdef, ← hNmax, ← hK₀] at hT
  have hω2 : 2 ≤ ω := ((le_max_left _ _).trans (le_max_left _ _)).trans hT
  have hωCe : 2 + p.A ^ 2 * Nmax ≤ ω := ((le_max_right _ _).trans (le_max_left _ _)).trans hT
  have hωC := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hωκ : 2 / κ ≤ ω :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hT
  have hωe := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hT
  obtain ⟨hωe1, hωe2⟩ := pow_four_mul_exp_neg_lt (m := p.A * κ / 72) (by positivity) hωe
  have hgoal := p.deficit_at hσ hD h0 habs hes heu hcosu (Us := p.potential (sp.deltaS - p.α))
    (Uu := p.potential (sp.deltaU - p.α)) (ΔU := ΔU) (θa := θa) (θb := π - θa)
    (f₀ := p.escBandGap) (v := v) (Nmax := Nmax) (K₀ := K₀) (κ := κ)
    (Ce := 2 + p.A ^ 2 * Nmax) (Cf := (2 * p.M + p.A + p.D) ^ 2 / 2 +
      (2 * p.M + p.A + p.D) * (1 + 2 * p.A) + (1 + 2 * p.A) ^ 2)
    (Cq := 4 * p.D ^ 2 * (p.A * Nmax + p.M * K₀ / 2) / p.M) rfl rfl hΔ hΔU hab hθs hθb
    hband hv c3 c4 rfl hNmax0 rfl hK₀0 hρ₁ (fun {_} hx => hE1 hx) hρ₂ (fun {_} hx => hG1 hx)
    hκ hκ0 rfl rfl rfl rfl hω0 hω2 hωCe (by rw [← hgain]; exact hωC) hωκ hωe1 hωe2
  rw [hgain]
  exact hgoal

/-- **The power filter lowers the escape exponent at first order in `1/ω_c`, explicitly**
(`D > 0`, `c₀ ≤ P_ref < c₀ + A`, `σ_P ≠ 0`): for every `ω_c ≥ escThreshold`, the three-state
escape exponent from the stable equilibrium `(δ_s, 0, P(δ_s))` to the saddle `(δ_u, 0, P(δ_u))`
satisfies `V₃ ≤ 2D (U(δ_u) − U(δ_s))/σ_P² − escGain/(2σ_P² ω_c)`. Proof: an explicit admissible
pair — the uphill feedback pair of the two-state model followed by the filter — whose first-order
gain is `(2D/(σ_P² ω_c)) A ∫ cos(δ − α) ω²`; along the uphill flow
`A cos(δ − α) ω² = M ω̇² + d/dt(ω (P(δ) − P_ref) − D ω²/2)` exactly, and `∫ ω̇² ≥ v⁴/(4 N_max)`
uniformly (`escSpeed`, from the gap `escBandGap` of `P − P_ref` on the angle band
`[θ_a, π − θ_a]`); all other terms are `O(1/ω_c²)` with explicit constants
(`Dynamics.lagFilter_tracking`). -/
@[tmio M, powerlib_domain] theorem setPointQP_le_sub {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {δs δu : ℝ}
    (hδs : δs = Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hδu : δu = π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α) (ωc : ℝ) (hω : 0 < ωc)
    (hωT : p.escThreshold ≤ ωc) :
    (⟨p, ωc, hω⟩ : Params3).setPointQP σP ![δs, 0, p.c0 + p.A * Real.sin (δs - p.α)]
        ![δu, 0, p.c0 + p.A * Real.sin (δu - p.α)] ≤
      ENNReal.ofReal (2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2 -
        p.escGain / (2 * σP ^ 2) / ωc) := by
  have hs : δs = p.swingModel.deltaS := hδs
  have hu : δu = p.swingModel.deltaU := hδu
  have habs : |p.Pref - p.c0| < p.A := abs_lt.2 ⟨by linarith [p.A_pos], by linarith⟩
  obtain ⟨hes, heu, -, -⟩ := p.rest_facts habs
  have h := p.deficit_explicit hσ hD h0 h1 hω hωT
  have hval : 2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2 =
      2 * p.D / σP ^ 2 * p.escBarrier := by
    rw [hδs, hδu]; simp only [add_sub_cancel_right, escBarrier]; ring
  rw [hval, hs, hu, hes, heu]
  exact h

/-- **`V₃ < V₂` for every bandwidth above an explicit threshold** (`D > 0`,
`c₀ ≤ P_ref < c₀ + A`, `σ_P ≠ 0`): for every `ω_c ≥ escThreshold` the three-state escape
exponent (stable equilibrium to saddle, set-point noise) is strictly below the two-state one,
`V₃ < V₂ = Params.swingQP σ_P (δ_s, 0) (δ_u, 0)` (`setPointQP_le_sub`, `swingQP_saddle_eq`). -/
@[tmio M, powerlib_domain] theorem setPointQP_lt_swingQP {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {δs δu : ℝ}
    (hδs : δs = Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hδu : δu = π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α) (ωc : ℝ) (hω : 0 < ωc)
    (hωT : p.escThreshold ≤ ωc) :
    (⟨p, ωc, hω⟩ : Params3).setPointQP σP ![δs, 0, p.c0 + p.A * Real.sin (δs - p.α)]
        ![δu, 0, p.c0 + p.A * Real.sin (δu - p.α)] < p.swingQP σP ![δs, 0] ![δu, 0] := by
  have habs : |p.Pref - p.c0| < p.A := abs_lt.2 ⟨by linarith [p.A_pos], by linarith⟩
  obtain ⟨-, -, hgap, -⟩ := p.rest_facts habs
  have h := p.setPointQP_le_sub hσ hD h0 h1 hδs hδu ωc hω hωT
  have hV : p.swingQP σP ![δs, 0] ![δu, 0] =
      ENNReal.ofReal (2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2) := by
    have := p.swingQP_saddle_eq hσ hD h0 h1
    rw [hδs, hδu]
    simpa only [add_sub_cancel_right] using this
  rw [hV]
  have hg : 0 < p.escGain := p.escGain_pos hD h0 h1
  refine h.trans_lt (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨?_, ?_⟩)
  · have : 0 < p.escGain / (2 * σP ^ 2) / ωc := by positivity
    linarith
  · have hs : δs = p.swingModel.deltaS := hδs
    have hu : δu = p.swingModel.deltaU := hδu
    rw [hs, hu]
    have : 0 < σP ^ 2 := by positivity
    have := sub_pos.mpr hgap
    positivity


/-! ## A slow filter: transits and dwells with an exact arrival -/

/-- Rest-to-rest transit `a + (b − a)(3x² − 2x³)`, `x = t/T`. -/
private def trAngle (a b T t : ℝ) : ℝ := a + (b - a) * (3 * (t / T) ^ 2 - 2 * (t / T) ^ 3)

private def trVel (a b T t : ℝ) : ℝ := (b - a) * (6 * (t / T) - 6 * (t / T) ^ 2) / T

private def trAcc (a b T t : ℝ) : ℝ := (b - a) * (6 - 12 * (t / T)) / T ^ 2

@[tmio T, powerlib_foundation] private theorem hasDerivAt_trAngle (a b T t : ℝ) :
    HasDerivAt (trAngle a b T) (trVel a b T t) t := by
  have h1 := (hasDerivAt_id t).div_const T
  have h := (((h1.pow 2).const_mul 3).sub ((h1.pow 3).const_mul 2)).const_mul (b - a)
    |>.const_add a
  convert h using 1
  · funext s; simp [trAngle]
  · simp only [trVel, id]; ring

@[tmio T, powerlib_foundation] private theorem hasDerivAt_trVel (a b T t : ℝ) :
    HasDerivAt (trVel a b T) (trAcc a b T t) t := by
  have h1 := (hasDerivAt_id t).div_const T
  have h := ((((h1.const_mul 6).sub ((h1.pow 2).const_mul 6)).const_mul (b - a)).div_const T)
  convert h using 1
  · funext s; simp [trVel]
  · simp only [trAcc, id]; ring

/-- On `[0, T]`: the angle stays between `a` and `b`, `|θ̇| ≤ (3/2)|b − a|/T`,
`|θ̈| ≤ 6|b − a|/T²`. -/
@[tmio T, powerlib_foundation] private theorem tr_bounds {a b T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) :
    (∃ g ∈ Icc (0 : ℝ) 1, trAngle a b T t = a + (b - a) * g) ∧
      |trVel a b T t| ≤ 3 / 2 * |b - a| / T ∧ |trAcc a b T t| ≤ 6 * |b - a| / T ^ 2 := by
  set x := t / T with hx
  have hx0 : 0 ≤ x := div_nonneg ht.1 hT.le
  have hx1 : x ≤ 1 := (div_le_one hT).mpr ht.2
  have hg0 : 0 ≤ 3 * x ^ 2 - 2 * x ^ 3 := by
    have : 0 ≤ x ^ 2 * (3 - 2 * x) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  have hg1 : 3 * x ^ 2 - 2 * x ^ 3 ≤ 1 := by
    have : 0 ≤ (1 - x) ^ 2 * (1 + 2 * x) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  refine ⟨⟨3 * x ^ 2 - 2 * x ^ 3, ⟨hg0, hg1⟩, rfl⟩, ?_, ?_⟩
  · have hxx : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.2 hx1)
    have hg : |6 * x - 6 * x ^ 2| ≤ 3 / 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - 1 / 2)]
    simp only [trVel, ← hx]
    rw [abs_div, abs_mul, abs_of_pos hT]
    exact div_le_div_of_nonneg_right (by nlinarith [abs_nonneg (b - a)]) hT.le
  · have hg : |6 - 12 * x| ≤ 6 := by rw [abs_le]; constructor <;> linarith
    simp only [trAcc, ← hx]
    rw [abs_div, abs_mul, abs_of_pos (pow_pos hT 2)]
    exact div_le_div_of_nonneg_right (by nlinarith [abs_nonneg (b - a)]) (by positivity)

@[tmio T, powerlib_foundation] private theorem tr_ends (a b : ℝ) {T : ℝ} (hT : T ≠ 0) :
    trAngle a b T 0 = a ∧ trAngle a b T T = b ∧ trVel a b T 0 = 0 ∧ trVel a b T T = 0 := by
  refine ⟨by simp [trAngle], ?_, by simp [trVel], ?_⟩
  · simp only [trAngle, div_self hT]; ring
  · simp only [trVel, div_self hT]; ring

/-- `|P(δ) − P_ref| ≤ 2A` (`|P_ref − c₀| < A`). -/
@[tmio M, powerlib_domain] private theorem abs_power_sub_le (habs : |p.Pref - p.c0| < p.A)
    (δ : ℝ) : |p.c0 + p.A * Real.sin (δ - p.α) - p.Pref| ≤ 2 * p.A := by
  have hA := p.A_pos
  have h1 : |p.A * Real.sin (δ - p.α)| ≤ p.A := by
    rw [abs_mul, abs_of_pos hA]; exact mul_le_of_le_one_right hA.le (Real.abs_sin_le_one _)
  calc |p.c0 + p.A * Real.sin (δ - p.α) - p.Pref| =
        |p.A * Real.sin (δ - p.α) - (p.Pref - p.c0)| := by ring_nf
    _ ≤ |p.A * Real.sin (δ - p.α)| + |p.Pref - p.c0| := abs_sub _ _
    _ ≤ 2 * p.A := by linarith

/-- **A transit followed by the filter**: the three-state pair from `(a, 0, z₀)` to
`(b, 0, Z)`, `Z = lagFilter ω z₀ (P ∘ transit) T`, with
`2σ_P² S ≤ T (6M|b − a|/T² + (3/2) D |b − a|/T + E₀ + 2AωT)²` for `|z₀ − P_ref| ≤ E₀`, and
`|Z − P_ref| ≤ E₀ + 2AωT`. -/
@[tmio TM, powerlib_domain] private theorem transit_track {σP : ℝ} (hσ : σP ≠ 0) {ω : ℝ}
    (hω : 0 < ω) (habs : |p.Pref - p.c0| < p.A) {a b T z₀ E₀ : ℝ} (hT : 0 < T)
    (hE₀ : |z₀ - p.Pref| ≤ E₀) :
    ∃ S : ℝ, 0 ≤ S ∧ 2 * σP ^ 2 * S ≤ T * (6 * p.M * |b - a| / T ^ 2 +
        3 / 2 * p.D * |b - a| / T + (E₀ + 2 * p.A * ω * T)) ^ 2 ∧
      |lagFilter ω z₀ (fun t => p.c0 + p.A * Real.sin (trAngle a b T t - p.α)) T - p.Pref| ≤
        E₀ + 2 * p.A * ω * T ∧
      (⟨p, ω, hω⟩ : Params3).setPointQP σP ![a, 0, z₀]
        ![b, 0, lagFilter ω z₀ (fun t => p.c0 + p.A * Real.sin (trAngle a b T t - p.α)) T] ≤
          ENNReal.ofReal S := by
  have hM := p.M_pos
  have hT0 := hT.ne'
  obtain ⟨e0, eT, v0, vT⟩ := tr_ends a b hT0
  set h : ℝ → ℝ := fun t => p.c0 + p.A * Real.sin (trAngle a b T t - p.α) with hhdef
  have hhc : Continuous h := by simp only [hhdef, trAngle]; fun_prop
  have hpath : ∀ t, HasDerivAt (fun t => ![trAngle a b T t, p.M * trVel a b T t])
      (controlField p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP)
        ![trAngle a b T t, p.M * trVel a b T t]
        ![(p.M * trAcc a b T t + (p.c0 + p.A * Real.sin (trAngle a b T t - p.α) - p.Pref) +
          p.D * trVel a b T t) / σP]) t := fun t =>
    Params.hasDerivAt_anglePath p hσ (hasDerivAt_trAngle a b T t) (hasDerivAt_trVel a b T t)
  have hfc : Continuous fun t => (p.M * trAcc a b T t + (p.c0 + p.A *
      Real.sin (trAngle a b T t - p.α) - p.Pref) + p.D * trVel a b T t) / σP := by
    simp only [trAcc, trAngle, trVel]; fun_prop
  have hfollow := Params3.setPointQP_le_follow ⟨p, ω, hω⟩ hσ hT.le
    (φ := fun t => ![trAngle a b T t, p.M * trVel a b T t])
    (fun t _ => (hpath t).continuousAt.continuousWithinAt) (fun t _ => (hpath t).hasDerivWithinAt)
    (by simpa using hfc.continuousOn) hhc (fun t _ => by simp [hhdef]) z₀
  dsimp only at hfollow
  have hs0 : (![trAngle a b T 0, p.M * trVel a b T 0 / p.M, z₀] : Fin 3 → ℝ) = ![a, 0, z₀] := by
    rw [e0, v0]; simp
  have hs1 : (![trAngle a b T T, p.M * trVel a b T T / p.M, lagFilter ω z₀ h T] : Fin 3 → ℝ) =
      ![b, 0, lagFilter ω z₀ h T] := by rw [eT, vT]; simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hfollow
  rw [hs0, hs1] at hfollow
  -- the drift and the integrand
  have hdrift : ∀ t ∈ Icc 0 T, |lagFilter ω z₀ h t - p.Pref| ≤ E₀ + 2 * p.A * ω * T := by
    intro t ht
    have := abs_lagFilter_sub_const_le (c := p.Pref) (B := 2 * p.A) hω.le ht.1 hhc
      (fun s _ => p.abs_power_sub_le habs _) (z₀ := z₀)
    have h2 : ω * t * (2 * p.A) ≤ 2 * p.A * ω * T := by
      have := mul_le_mul_of_nonneg_left ht.2 (by have := p.A_pos; positivity :
        (0 : ℝ) ≤ 2 * p.A * ω)
      linarith
    linarith
  set B := 6 * p.M * |b - a| / T ^ 2 + 3 / 2 * p.D * |b - a| / T with hBdef
  set E := E₀ + 2 * p.A * ω * T with hEdef
  have hZc : Continuous (lagFilter ω z₀ h) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_lagFilter hhc t).continuousAt
  have hpt : ∀ t ∈ Icc 0 T, ((p.M * trAcc a b T t + (p.c0 + p.A *
      Real.sin (trAngle a b T t - p.α) - p.Pref) + p.D * trVel a b T t) / σP +
        (lagFilter ω z₀ h t - h t) / σP) ^ 2 ≤ (B + E) ^ 2 / σP ^ 2 := by
    intro t ht
    obtain ⟨-, hv, hacc⟩ := tr_bounds (a := a) (b := b) hT ht
    have e : (p.M * trAcc a b T t + (p.c0 + p.A * Real.sin (trAngle a b T t - p.α) - p.Pref) +
        p.D * trVel a b T t) / σP + (lagFilter ω z₀ h t - h t) / σP =
        (p.M * trAcc a b T t + p.D * trVel a b T t + (lagFilter ω z₀ h t - p.Pref)) / σP := by
      simp only [hhdef]; field_simp; ring
    rw [e, div_pow]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    have h1 : |p.M * trAcc a b T t| ≤ 6 * p.M * |b - a| / T ^ 2 := by
      rw [abs_mul, abs_of_pos hM]
      calc p.M * |trAcc a b T t| ≤ p.M * (6 * |b - a| / T ^ 2) :=
            mul_le_mul_of_nonneg_left hacc hM.le
        _ = 6 * p.M * |b - a| / T ^ 2 := by ring
    have h2 : |p.D * trVel a b T t| ≤ 3 / 2 * p.D * |b - a| / T := by
      rw [abs_mul, abs_of_nonneg p.D_nonneg]
      calc p.D * |trVel a b T t| ≤ p.D * (3 / 2 * |b - a| / T) :=
            mul_le_mul_of_nonneg_left hv p.D_nonneg
        _ = 3 / 2 * p.D * |b - a| / T := by ring
    calc |p.M * trAcc a b T t + p.D * trVel a b T t + (lagFilter ω z₀ h t - p.Pref)|
        ≤ |p.M * trAcc a b T t| + |p.D * trVel a b T t| + |lagFilter ω z₀ h t - p.Pref| :=
          abs_add_three _ _ _
      _ ≤ B + E := by rw [hBdef, hEdef]; linarith [hdrift t ht]
  set S := 1 / 2 * ∫ t in (0 : ℝ)..T, ((p.M * trAcc a b T t + (p.c0 + p.A *
      Real.sin (trAngle a b T t - p.α) - p.Pref) + p.D * trVel a b T t) / σP +
        (lagFilter ω z₀ h t - h t) / σP) ^ 2 with hSdef
  refine ⟨S, mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hT.le fun t _ =>
    sq_nonneg _), ?_, hdrift T ⟨hT.le, le_rfl⟩, hfollow⟩
  have hint : ∫ t in (0 : ℝ)..T, ((p.M * trAcc a b T t + (p.c0 + p.A *
      Real.sin (trAngle a b T t - p.α) - p.Pref) + p.D * trVel a b T t) / σP +
        (lagFilter ω z₀ h t - h t) / σP) ^ 2 ≤ T * ((B + E) ^ 2 / σP ^ 2) := by
    have := intervalIntegral.integral_mono_on hT.le
      (((hfc.add ((hZc.sub hhc).div_const _)).pow 2).intervalIntegrable 0 T)
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (B + E) ^ 2 / σP ^ 2)
        MeasureTheory.volume 0 T) hpt
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
  have hσ2 : 0 < σP ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hint hσ2.le
  have e : σP ^ 2 * (T * ((B + E) ^ 2 / σP ^ 2)) = T * (B + E) ^ 2 := by field_simp
  have e2 : 2 * σP ^ 2 * S = σP ^ 2 * ∫ t in (0 : ℝ)..T, ((p.M * trAcc a b T t + (p.c0 + p.A *
      Real.sin (trAngle a b T t - p.α) - p.Pref) + p.D * trVel a b T t) / σP +
        (lagFilter ω z₀ h t - h t) / σP) ^ 2 := by rw [hSdef]; ring
  rw [e2]; linarith

/-- **A dwell followed by the filter**: holding `(δ_d, 0)` for the time `τ ≥ 0` from the filter
value `z₀` (`|z₀ − P_ref| ≤ E₀`) reaches `P(δ_d) + (z₀ − P(δ_d)) e^{−ωτ}` with
`2σ_P² S ≤ τ (E₀ + 2Aωτ)²`; the end value is within `E₀ + 2Aωτ` of `P_ref`. -/
@[tmio TM, powerlib_domain] private theorem dwell_track {σP : ℝ} (hσ : σP ≠ 0) {ω : ℝ}
    (hω : 0 < ω) (habs : |p.Pref - p.c0| < p.A) {δd τ z₀ E₀ : ℝ} (hτ : 0 ≤ τ)
    (hE₀ : |z₀ - p.Pref| ≤ E₀) :
    ∃ S : ℝ, 0 ≤ S ∧ 2 * σP ^ 2 * S ≤ τ * (E₀ + 2 * p.A * ω * τ) ^ 2 ∧
      |p.c0 + p.A * Real.sin (δd - p.α) + (z₀ - (p.c0 + p.A * Real.sin (δd - p.α))) *
        Real.exp (-(ω * τ)) - p.Pref| ≤ E₀ + 2 * p.A * ω * τ ∧
      (⟨p, ω, hω⟩ : Params3).setPointQP σP ![δd, 0, z₀] ![δd, 0, p.c0 + p.A *
        Real.sin (δd - p.α) + (z₀ - (p.c0 + p.A * Real.sin (δd - p.α))) *
          Real.exp (-(ω * τ))] ≤ ENNReal.ofReal S := by
  set Pd := p.c0 + p.A * Real.sin (δd - p.α) with hPd
  have hpath : ∀ t, HasDerivAt (fun _ : ℝ => (![δd, 0] : Fin 2 → ℝ))
      (controlField p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP) ![δd, 0]
        ![(Pd - p.Pref) / σP]) t := by
    intro t
    rw [controlField_swing]
    have e : (![(0 : ℝ) / p.M, p.Pref - Pd - p.D * (0 / p.M) + (Pd - p.Pref) / σP * σP] :
        Fin 2 → ℝ) = 0 := by
      ext i; fin_cases i <;> simp; field_simp; ring
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hPd, e]; exact hasDerivAt_const t _
  have hfollow := Params3.setPointQP_le_follow ⟨p, ω, hω⟩ hσ hτ (φ := fun _ => ![δd, 0])
    (u := fun _ => ![(Pd - p.Pref) / σP]) continuousOn_const
    (fun t _ => (hpath t).hasDerivWithinAt) continuousOn_const continuous_const
    (h := fun _ => Pd) (fun t _ => by simp [hPd]) z₀
  dsimp only at hfollow
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_div, lagFilter_const] at hfollow
  have hdrift : ∀ t ∈ Icc 0 τ,
      |lagFilter ω z₀ (fun _ => Pd) t - p.Pref| ≤ E₀ + 2 * p.A * ω * τ := by
    intro t ht
    have := abs_lagFilter_sub_const_le (c := p.Pref) (B := 2 * p.A) hω.le ht.1 continuous_const
      (fun s _ => p.abs_power_sub_le habs δd) (z₀ := z₀)
    have h2 : ω * t * (2 * p.A) ≤ 2 * p.A * ω * τ := by
      have := mul_le_mul_of_nonneg_left ht.2 (by have := p.A_pos; positivity :
        (0 : ℝ) ≤ 2 * p.A * ω)
      linarith
    linarith
  set S := 1 / 2 * ∫ t in (0 : ℝ)..τ, ((Pd - p.Pref) / σP + (Pd + (z₀ - Pd) *
    Real.exp (-(ω * t)) - Pd) / σP) ^ 2 with hSdef
  refine ⟨S, mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hτ fun t _ =>
    sq_nonneg _), ?_, ?_, hfollow⟩
  · have hpt : ∀ t ∈ Icc 0 τ, ((Pd - p.Pref) / σP + (Pd + (z₀ - Pd) * Real.exp (-(ω * t)) - Pd) /
        σP) ^ 2 ≤ (E₀ + 2 * p.A * ω * τ) ^ 2 / σP ^ 2 := by
      intro t ht
      have hd := hdrift t ht
      rw [lagFilter_const] at hd
      have e : (Pd - p.Pref) / σP + (Pd + (z₀ - Pd) * Real.exp (-(ω * t)) - Pd) / σP =
          (Pd + (z₀ - Pd) * Real.exp (-(ω * t)) - p.Pref) / σP := by field_simp; ring
      rw [e, div_pow]
      refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    have hint : ∫ t in (0 : ℝ)..τ, ((Pd - p.Pref) / σP + (Pd + (z₀ - Pd) * Real.exp (-(ω * t)) -
        Pd) / σP) ^ 2 ≤ τ * ((E₀ + 2 * p.A * ω * τ) ^ 2 / σP ^ 2) := by
      have := intervalIntegral.integral_mono_on hτ ((by fun_prop : Continuous fun t =>
        ((Pd - p.Pref) / σP + (Pd + (z₀ - Pd) * Real.exp (-(ω * t)) - Pd) / σP) ^ 2)
          |>.intervalIntegrable 0 τ) (intervalIntegrable_const : IntervalIntegrable
            (fun _ => (E₀ + 2 * p.A * ω * τ) ^ 2 / σP ^ 2) MeasureTheory.volume 0 τ) hpt
      rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    have hσ2 : 0 < σP ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hint hσ2.le
    have e : σP ^ 2 * (τ * ((E₀ + 2 * p.A * ω * τ) ^ 2 / σP ^ 2)) =
        τ * (E₀ + 2 * p.A * ω * τ) ^ 2 := by field_simp
    have e2 : 2 * σP ^ 2 * S = σP ^ 2 * ∫ t in (0 : ℝ)..τ, ((Pd - p.Pref) / σP + (Pd + (z₀ - Pd) *
        Real.exp (-(ω * t)) - Pd) / σP) ^ 2 := by rw [hSdef]; ring
    rw [e2]; linarith
  · have := hdrift τ ⟨hτ, le_rfl⟩
    rwa [lagFilter_const] at this


/-- The exact dwell time: for `P_b < Z_r ≤ Z` (`ω > 0`) there is `τ ≥ 0` with
`P_b + (Z − P_b) e^{−ωτ} = Z_r` and `ωτ ≤ (Z − Z_r)/(Z_r − P_b)`
(`τ = log((Z − P_b)/(Z_r − P_b))/ω`, `log q ≤ q − 1`). -/
@[tmio T, powerlib_foundation] private theorem exists_dwell_time {ω Pb Zr Z : ℝ} (hω : 0 < ω)
    (h1 : Pb < Zr) (h2 : Zr ≤ Z) :
    ∃ τ : ℝ, 0 ≤ τ ∧ Pb + (Z - Pb) * Real.exp (-(ω * τ)) = Zr ∧
      ω * τ ≤ (Z - Zr) / (Zr - Pb) := by
  have hd : 0 < Zr - Pb := by linarith
  have hq1 : 1 ≤ (Z - Pb) / (Zr - Pb) := by rw [le_div_iff₀ hd]; linarith
  have hq0 : 0 < (Z - Pb) / (Zr - Pb) := by linarith
  refine ⟨Real.log ((Z - Pb) / (Zr - Pb)) / ω, div_nonneg (Real.log_nonneg hq1) hω.le, ?_, ?_⟩
  · have e : ω * (Real.log ((Z - Pb) / (Zr - Pb)) / ω) = Real.log ((Z - Pb) / (Zr - Pb)) := by
      field_simp
    have hz : Z - Pb ≠ 0 := by linarith
    rw [e, Real.exp_neg, Real.exp_log hq0, inv_div]
    field_simp
    ring
  · have e : ω * (Real.log ((Z - Pb) / (Zr - Pb)) / ω) = Real.log ((Z - Pb) / (Zr - Pb)) := by
      field_simp
    rw [e]
    have := Real.log_le_sub_one_of_pos hq0
    have e2 : (Z - Pb) / (Zr - Pb) - 1 = (Z - Zr) / (Zr - Pb) := by field_simp; ring
    linarith

/-- The sign condition of the exact arrival: with `x = ωT`, `y = ωτ₁ ≥ 8x(1 + s)/(1 − s)`,
`y ≤ 1`, a filter value `Z₁ ≥ P_r` after the first transit, the top dwell
`Z₂ = P_t + (Z₁ − P_t) e^{−y}`, the second transit `Z₃ ≥ P_b + (Z₂ − P_b) e^{−x}` and the last
transit offset `K ≥ (1 − e^{−x}) P_b`: `Z₃ ≥ (P_r − K)/e^{−x}` (`P_t − P_r = A(1 − s)`,
`P_r − P_b = A(1 + s)`). -/
@[tmio T, powerlib_foundation] private theorem slow_sign {A s x y Pt Pr Pb Z₁ Z₂ Z₃ K : ℝ}
    (hA : 0 < A) (hs0 : 0 ≤ s) (hs1 : s < 1) (hx : 0 ≤ x) (hy : 8 * x * (1 + s) ≤ y * (1 - s))
    (hy1 : y ≤ 1) (hPt : Pt - Pr = A * (1 - s)) (hPb : Pr - Pb = A * (1 + s)) (hZ₁ : Pr ≤ Z₁)
    (hZ₂ : Z₂ = Pt + (Z₁ - Pt) * Real.exp (-y))
    (hZ₃ : Pb + (Z₂ - Pb) * Real.exp (-x) ≤ Z₃) (hK : (1 - Real.exp (-x)) * Pb ≤ K) :
    (Pr - K) / Real.exp (-x) ≤ Z₃ := by
  have ha := Real.exp_pos (-x)
  have hb := Real.exp_pos (-y)
  have hy0 : 0 ≤ y := by nlinarith
  -- `1 − e^{−y} ≥ y/2`, `e^{−2x} ≥ 1 − 2x`
  have hby : 1 - Real.exp (-y) ≥ y / 2 := by
    have h := Real.add_one_le_exp y
    have e : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp (-y) * (y + 1) ≤ Real.exp (-y) * Real.exp y :=
      mul_le_mul_of_nonneg_left h hb.le
    rw [e] at h2
    nlinarith [mul_nonneg hy0 (sub_nonneg.2 hy1)]
  have hax : 1 - 2 * x ≤ Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; have := Real.add_one_le_exp (-x + -x); linarith
  have hx8 : x ≤ 1 / 8 := by
    have h1 : y * (1 - s) ≤ 1 - s := mul_le_of_le_one_left (by linarith) hy1
    have h2 : 8 * x ≤ 8 * x * (1 + s) := by nlinarith
    linarith
  -- `Z₂ − P_b ≥ A(1 + s) + A(1 − s)(1 − e^{−y})`
  have hZ2 : A * (1 + s) + A * (1 - s) * (1 - Real.exp (-y)) ≤ Z₂ - Pb := by
    rw [hZ₂]
    have : 0 ≤ (Z₁ - Pr) * Real.exp (-y) := mul_nonneg (by linarith) hb.le
    linear_combination this - (1 - Real.exp (-y)) * hPt - hPb
  -- the key inequality `(Z₂ − P_b) e^{−2x} ≥ P_r − P_b`
  have hkey : A * (1 + s) ≤ (Z₂ - Pb) * (Real.exp (-x) * Real.exp (-x)) := by
    have h1 : A * (1 + s) + A * (1 - s) * (y / 2) ≤ Z₂ - Pb := by
      have : A * (1 - s) * (y / 2) ≤ A * (1 - s) * (1 - Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left hby (mul_nonneg hA.le (by linarith))
      linarith
    have h2 : (A * (1 + s) + A * (1 - s) * (y / 2)) * (1 - 2 * x) ≤
        (Z₂ - Pb) * (Real.exp (-x) * Real.exp (-x)) := by
      have hn : 0 ≤ 1 - 2 * x := by linarith
      have hpos : 0 ≤ A * (1 + s) + A * (1 - s) * (y / 2) :=
        add_nonneg (mul_nonneg hA.le (by linarith))
          (mul_nonneg (mul_nonneg hA.le (by linarith)) (by linarith))
      calc (A * (1 + s) + A * (1 - s) * (y / 2)) * (1 - 2 * x)
          ≤ (Z₂ - Pb) * (1 - 2 * x) := mul_le_mul_of_nonneg_right h1 hn
        _ ≤ (Z₂ - Pb) * (Real.exp (-x) * Real.exp (-x)) :=
            mul_le_mul_of_nonneg_left hax (by linarith)
    have h3 : A * (1 + s) ≤ (A * (1 + s) + A * (1 - s) * (y / 2)) * (1 - 2 * x) := by
      have : A * (8 * x * (1 + s)) ≤ A * (y * (1 - s)) := mul_le_mul_of_nonneg_left hy hA.le
      have hp : 0 ≤ (A * (y * (1 - s)) - A * (8 * x * (1 + s))) * (1 - 2 * x) :=
        mul_nonneg (by linarith) (by linarith)
      have hq : 0 ≤ x * A * (1 + s) * (1 - 4 * x) :=
        mul_nonneg (mul_nonneg (mul_nonneg hx hA.le) (by linarith)) (by linarith)
      linear_combination (1 / 2) * hp + 2 * hq
    linarith
  rw [div_le_iff₀ ha]
  have h5 : (Pr - Pb) ≤ (Z₂ - Pb) * Real.exp (-x) * Real.exp (-x) := by
    rw [hPb, mul_assoc]; exact hkey
  have h4 : (Z₂ - Pb) * Real.exp (-x) * Real.exp (-x) ≤ (Z₃ - Pb) * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right (by linarith) ha.le
  linear_combination h5 + h4 + hK


/-- Bookkeeping of the slow-filter pair: five pieces with transit bounds `T(b + e)²`, dwell
bounds `τ e²` (`b ≤ B`, `e ≤ E`), `6 T B² ≤ 2DΔU` and `(6T + τ₁ + τ*) E² ≤ DΔU` give a total
action below `2DΔU/σ²`. -/
@[tmio T, powerlib_foundation] private theorem slow_arith
    {σ2 T τ₁ τs B E D ΔU SA St SB Sb SC bA bB bC eA et eB eb eC : ℝ} (hσ2 : 0 < σ2)
    (hT : 0 < T) (hτ₁ : 0 ≤ τ₁) (hτs : 0 ≤ τs) (hDU : 0 < D * ΔU)
    (hSA : 2 * σ2 * SA ≤ T * (bA + eA) ^ 2) (hSt : 2 * σ2 * St ≤ τ₁ * et ^ 2)
    (hSB : 2 * σ2 * SB ≤ T * (bB + eB) ^ 2) (hSb : 2 * σ2 * Sb ≤ τs * eb ^ 2)
    (hSC : 2 * σ2 * SC ≤ T * (bC + eC) ^ 2)
    (hbA : 0 ≤ bA ∧ bA ≤ B) (hbB : 0 ≤ bB ∧ bB ≤ B) (hbC : 0 ≤ bC ∧ bC ≤ B)
    (heA : 0 ≤ eA ∧ eA ≤ E) (het : 0 ≤ et ∧ et ≤ E) (heB : 0 ≤ eB ∧ eB ≤ E)
    (heb : 0 ≤ eb ∧ eb ≤ E) (heC : 0 ≤ eC ∧ eC ≤ E)
    (hB : 6 * T * B ^ 2 ≤ 2 * (D * ΔU)) (hE : (6 * T + τ₁ + τs) * E ^ 2 ≤ D * ΔU) :
    SA + (St + (SB + (Sb + SC))) < 2 * D / σ2 * ΔU := by
  have sq : ∀ b e : ℝ, 0 ≤ b ∧ b ≤ B → 0 ≤ e ∧ e ≤ E →
      (b + e) ^ 2 ≤ 2 * B ^ 2 + 2 * E ^ 2 := fun b e hb he => by
    have h1 : (b + e) ^ 2 ≤ (B + E) ^ 2 :=
      pow_le_pow_left₀ (add_nonneg hb.1 he.1) (add_le_add hb.2 he.2) 2
    nlinarith [sq_nonneg (B - E)]
  have esq : ∀ e : ℝ, 0 ≤ e ∧ e ≤ E → e ^ 2 ≤ E ^ 2 := fun e he =>
    pow_le_pow_left₀ he.1 he.2 2
  have h1 := mul_le_mul_of_nonneg_left (sq bA eA hbA heA) hT.le
  have h2 := mul_le_mul_of_nonneg_left (esq et het) hτ₁
  have h3 := mul_le_mul_of_nonneg_left (sq bB eB hbB heB) hT.le
  have h4 := mul_le_mul_of_nonneg_left (esq eb heb) hτs
  have h5 := mul_le_mul_of_nonneg_left (sq bC eC hbC heC) hT.le
  have htot : 2 * σ2 * (SA + (St + (SB + (Sb + SC)))) ≤ 3 * (D * ΔU) := by
    have e : 6 * T * B ^ 2 + (6 * T + τ₁ + τs) * E ^ 2 = T * (2 * B ^ 2 + 2 * E ^ 2) +
        τ₁ * E ^ 2 + T * (2 * B ^ 2 + 2 * E ^ 2) + τs * E ^ 2 + T * (2 * B ^ 2 + 2 * E ^ 2) := by
      ring
    linarith
  rw [show 2 * D / σ2 * ΔU = 4 * (D * ΔU) / (2 * σ2) by field_simp; ring,
    lt_div_iff₀ (by positivity)]
  linarith

/-- `6T(6Mπ/T² + (3/2)Dπ/T)² ≤ 2DΔU` for `T ≥ max(4M/D, 27π²D/ΔU)`. -/
@[tmio T, powerlib_foundation] private theorem slow_transit_le {M D ΔU T : ℝ} (hM : 0 < M)
    (hD : 0 < D) (hΔ : 0 < ΔU) (hT : max (4 * M / D) (27 * π ^ 2 * D / ΔU) ≤ T) :
    6 * T * (6 * M * π / T ^ 2 + 3 / 2 * D * π / T) ^ 2 ≤ 2 * (D * ΔU) := by
  have hT1 : 4 * M / D ≤ T := (le_max_left _ _).trans hT
  have hT2 : 27 * π ^ 2 * D / ΔU ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT1
  have hπ := Real.pi_pos
  have hB : 6 * M * π / T ^ 2 + 3 / 2 * D * π / T ≤ 3 * D * π / T := by
    have : 6 * M * π / T ^ 2 ≤ 3 / 2 * D * π / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]
      rw [div_le_iff₀ hD] at hT1
      have h := mul_le_mul_of_nonneg_left hT1 (by positivity : (0 : ℝ) ≤ 3 / 2 * π * T)
      linear_combination h
    have e : 3 / 2 * D * π / T + 3 / 2 * D * π / T = 3 * D * π / T := by ring
    linarith
  have hB0 : 0 ≤ 6 * M * π / T ^ 2 + 3 / 2 * D * π / T := by positivity
  have h1 : (6 * M * π / T ^ 2 + 3 / 2 * D * π / T) ^ 2 ≤ (3 * D * π / T) ^ 2 :=
    pow_le_pow_left₀ hB0 hB 2
  have h2 : 6 * T * (3 * D * π / T) ^ 2 = 54 * π ^ 2 * D ^ 2 / T := by field_simp; ring
  have h3 : 54 * π ^ 2 * D ^ 2 / T ≤ 2 * (D * ΔU) := by
    rw [div_le_iff₀ hT0]
    rw [div_le_iff₀ hΔ] at hT2
    nlinarith
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 6 * T)
  linarith

/-- Transit time of the slow-filter pair, `T = max(4M/D, 27π² D/ΔU)`. -/
def escSlowTime : ℝ := max (4 * p.M / p.D) (27 * π ^ 2 * p.D / p.escBarrier)

/-- Top dwell of the slow-filter pair, `τ₁ = 8T(1 + s)/(1 − s)`, `s = (P_ref − c₀)/A`. -/
def escSlowDwell : ℝ :=
  8 * p.escSlowTime * (1 + (p.Pref - p.c0) / p.A) / (1 - (p.Pref - p.c0) / p.A)

/-- Time span of the slow-filter pair, `t_max = 7T + 3τ₁`. -/
def escSlowSpan : ℝ := 7 * p.escSlowTime + 3 * p.escSlowDwell



@[tmio M, powerlib_domain] private theorem sin_three_pi_div_two : Real.sin (3 * π / 2) = -1 := by
  rw [show 3 * π / 2 = π / 2 + π by ring, Real.sin_add_pi, Real.sin_pi_div_two]

/-- The last transit `3π/2 + α → δ_u` stays beyond the saddle: along it
`c₀ − A ≤ P(δ) ≤ P_ref`, so `K = lagFilter ω 0 (P ∘ transit) T` satisfies
`(1 − e^{−ωT})(c₀ − A) ≤ K ≤ (1 − e^{−ωT}) P_ref`. -/
@[tmio M, powerlib_domain] private theorem last_bounds (h0 : p.c0 ≤ p.Pref)
    (h1 : p.Pref < p.c0 + p.A) {ω T : ℝ} (hω : 0 ≤ ω) (hT : 0 < T) :
    (1 - Real.exp (-(ω * T))) * (p.c0 - p.A) ≤ lagFilter ω 0 (fun t => p.c0 + p.A *
        Real.sin (trAngle (3 * π / 2 + p.α) p.swingModel.deltaU T t - p.α)) T ∧
      lagFilter ω 0 (fun t => p.c0 + p.A *
        Real.sin (trAngle (3 * π / 2 + p.α) p.swingModel.deltaU T t - p.α)) T ≤
        (1 - Real.exp (-(ω * T))) * p.Pref := by
  have hA := p.A_pos
  obtain ⟨-, e2⟩ := p.esc_angles
  set s := (p.Pref - p.c0) / p.A with hsdef
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hA.le
  have hs1 : s < 1 := by rw [div_lt_one hA]; linarith
  have hPr : p.Pref = p.c0 + p.A * s := by rw [hsdef]; field_simp; ring
  have has0 : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.mpr hs0
  have has1 : Real.arcsin s < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hsin_s : Real.sin (Real.arcsin s) = s := Real.sin_arcsin (by linarith) hs1.le
  have hc : Continuous fun t => p.c0 + p.A *
      Real.sin (trAngle (3 * π / 2 + p.α) p.swingModel.deltaU T t - p.α) := by
    simp only [trAngle]; fun_prop
  constructor
  · have := lagFilter_mono (z₀ := 0) hω hT.le continuous_const hc (h := fun _ => p.c0 - p.A)
      fun t _ => by
        show p.c0 - p.A ≤ _
        nlinarith [Real.neg_one_le_sin (trAngle (3 * π / 2 + p.α) p.swingModel.deltaU T t - p.α)]
    rw [lagFilter_const] at this; linarith
  · have := lagFilter_mono (z₀ := 0) hω hT.le hc continuous_const (k := fun _ => p.Pref)
      fun t ht => by
        obtain ⟨⟨g, hg, hgeq⟩, -, -⟩ := tr_bounds (a := 3 * π / 2 + p.α)
          (b := p.swingModel.deltaU) hT ht
        have hθ : trAngle (3 * π / 2 + p.α) p.swingModel.deltaU T t - p.α =
            3 * π / 2 - (π / 2 + Real.arcsin s) * g := by
          rw [hgeq]; linear_combination g * e2
        have hle := Real.sin_le_sin_of_le_of_le_pi_div_two
          (x := π - (trAngle (3 * π / 2 + p.α) p.swingModel.deltaU T t - p.α))
          (y := Real.arcsin s) (by rw [hθ]; nlinarith [hg.1]) has1.le
          (by rw [hθ]; nlinarith [hg.2])
        rw [Real.sin_pi_sub, hsin_s] at hle
        show _ ≤ p.Pref
        rw [hPr]; nlinarith
    rw [lagFilter_const] at this; linarith

/-- Along the first transit `δ_s → π/2 + α` the power is at least `P_ref`, so the filter
started at `P_ref` ends above it. -/
@[tmio M, powerlib_domain] private theorem first_transit_ge (h0 : p.c0 ≤ p.Pref)
    (h1 : p.Pref < p.c0 + p.A) {ω T : ℝ} (hω : 0 ≤ ω) (hT : 0 < T) :
    p.Pref ≤ lagFilter ω p.Pref (fun t => p.c0 + p.A *
      Real.sin (trAngle p.swingModel.deltaS (π / 2 + p.α) T t - p.α)) T := by
  have hA := p.A_pos
  obtain ⟨e1, -⟩ := p.esc_angles
  set s := (p.Pref - p.c0) / p.A with hsdef
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hA.le
  have hs1 : s < 1 := by rw [div_lt_one hA]; linarith
  have hPr : p.Pref = p.c0 + p.A * s := by rw [hsdef]; field_simp; ring
  have has0 : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.mpr hs0
  have has1 : Real.arcsin s < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hsin_s : Real.sin (Real.arcsin s) = s := Real.sin_arcsin (by linarith) hs1.le
  have := lagFilter_mono (z₀ := p.Pref) hω hT.le continuous_const
    (k := fun t => p.c0 + p.A * Real.sin (trAngle p.swingModel.deltaS (π / 2 + p.α) T t - p.α))
    (by simp only [trAngle]; fun_prop) fun t ht => by
      obtain ⟨⟨g, hg, hgeq⟩, -, -⟩ := tr_bounds (a := p.swingModel.deltaS)
        (b := π / 2 + p.α) hT ht
      have hθ : trAngle p.swingModel.deltaS (π / 2 + p.α) T t - p.α =
          Real.arcsin s + (π / 2 - Real.arcsin s) * g := by
        rw [hgeq]; linear_combination (1 - g) * e1
      have hle := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.arcsin s)
        (y := trAngle p.swingModel.deltaS (π / 2 + p.α) T t - p.α) (by linarith)
        (by rw [hθ]; nlinarith [hg.2]) (by rw [hθ]; nlinarith [hg.1])
      rw [hsin_s] at hle
      show p.Pref ≤ _
      rw [hPr]; nlinarith
  rwa [lagFilter_const, sub_self, zero_mul, add_zero] at this

/-- Every transit keeps the power above `c₀ − A`: the filter ends above
`(c₀ − A) + (z₀ − (c₀ − A)) e^{−ωT}`. -/
@[tmio M, powerlib_domain] private theorem transit_ge_low {ω T : ℝ} (hω : 0 ≤ ω) (hT : 0 ≤ T)
    (a b z₀ : ℝ) : (p.c0 - p.A) + (z₀ - (p.c0 - p.A)) * Real.exp (-(ω * T)) ≤
      lagFilter ω z₀ (fun t => p.c0 + p.A * Real.sin (trAngle a b T t - p.α)) T := by
  have hA := p.A_pos
  have := lagFilter_mono (z₀ := z₀) hω hT continuous_const
    (k := fun t => p.c0 + p.A * Real.sin (trAngle a b T t - p.α))
    (by simp only [trAngle]; fun_prop) (h := fun _ => p.c0 - p.A) fun t _ => by
      show p.c0 - p.A ≤ _
      nlinarith [Real.neg_one_le_sin (trAngle a b T t - p.α)]
  rwa [lagFilter_const] at this

/-- **The way up** of the slow-filter pair: transit `δ_s → π/2 + α` (time `T`), dwell `τ₁` at
the top, transit to `3π/2 + α` (time `T`), all followed by the filter from `P_ref`. -/
@[tmio TM, powerlib_domain] private theorem slow_up {σP : ℝ} (hσ : σP ≠ 0)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {ω T τ₁ : ℝ} (hω : 0 < ω) (hT : 0 < T)
    (hτ₁ : 0 ≤ τ₁) :
    ∃ Z₁ Z₃ SA St SB : ℝ, 0 ≤ SA ∧ 0 ≤ St ∧ 0 ≤ SB ∧ p.Pref ≤ Z₁ ∧
      (p.c0 - p.A) + ((p.c0 + p.A) + (Z₁ - (p.c0 + p.A)) * Real.exp (-(ω * τ₁)) -
        (p.c0 - p.A)) * Real.exp (-(ω * T)) ≤ Z₃ ∧
      |Z₃ - p.Pref| ≤ 2 * p.A * ω * (2 * T + τ₁) ∧
      2 * σP ^ 2 * SA ≤ T * (6 * p.M * π / T ^ 2 + 3 / 2 * p.D * π / T + 2 * p.A * ω * T) ^ 2 ∧
      2 * σP ^ 2 * St ≤ τ₁ * (2 * p.A * ω * (T + τ₁)) ^ 2 ∧
      2 * σP ^ 2 * SB ≤ T * (6 * p.M * π / T ^ 2 + 3 / 2 * p.D * π / T +
        2 * p.A * ω * (2 * T + τ₁)) ^ 2 ∧
      (⟨p, ω, hω⟩ : Params3).setPointQP σP ![p.swingModel.deltaS, 0, p.Pref]
        ![3 * π / 2 + p.α, 0, Z₃] ≤ ENNReal.ofReal (SA + (St + SB)) := by
  have hA := p.A_pos
  have hM := p.M_pos
  have hDn := p.D_nonneg
  have hπ := Real.pi_pos
  have habs : |p.Pref - p.c0| < p.A := abs_lt.2 ⟨by linarith, by linarith⟩
  obtain ⟨e1, -⟩ := p.esc_angles
  set s := (p.Pref - p.c0) / p.A with hsdef
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hA.le
  have hs1 : s < 1 := by rw [div_lt_one hA]; linarith
  have has0 : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.mpr hs0
  have has1 : Real.arcsin s < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hPt : p.c0 + p.A * Real.sin (π / 2 + p.α - p.α) = p.c0 + p.A := by simp
  have hPb : p.c0 + p.A * Real.sin (3 * π / 2 + p.α - p.α) = p.c0 - p.A := by
    rw [add_sub_cancel_right, sin_three_pi_div_two]; ring
  have hB : ∀ d : ℝ, |d| ≤ π → 6 * p.M * |d| / T ^ 2 + 3 / 2 * p.D * |d| / T ≤
      6 * p.M * π / T ^ 2 + 3 / 2 * p.D * π / T := fun d hd => by gcongr
  -- transit A
  obtain ⟨SA, hSA0, hSA, hdA, hVA⟩ := p.transit_track hσ hω habs
    (a := p.swingModel.deltaS) (b := π / 2 + p.α) (z₀ := p.Pref) (E₀ := 0) hT (by simp)
  have hZ₁ := p.first_transit_ge h0 h1 hω.le hT
  -- the top dwell and transit B
  obtain ⟨St, hSt0, hSt, hdt, hVt⟩ := p.dwell_track hσ hω habs (δd := π / 2 + p.α) hτ₁ hdA
  obtain ⟨SB, hSB0, hSB, hdB, hVB⟩ := p.transit_track hσ hω habs (a := π / 2 + p.α)
    (b := 3 * π / 2 + p.α) hT hdt
  rw [hPt] at hdB hVB hVt
  have hZ₃ := p.transit_ge_low hω.le hT.le (π / 2 + p.α) (3 * π / 2 + p.α)
    (p.c0 + p.A + (lagFilter ω p.Pref (fun t => p.c0 + p.A *
      Real.sin (trAngle p.swingModel.deltaS (π / 2 + p.α) T t - p.α)) T - (p.c0 + p.A)) *
        Real.exp (-(ω * τ₁)))
  have hdA' : |π / 2 + p.α - p.swingModel.deltaS| ≤ π := by
    rw [show π / 2 + p.α - p.swingModel.deltaS = π / 2 - Real.arcsin s by
      linear_combination -e1, abs_of_nonneg (by linarith)]
    linarith
  have hdB' : |3 * π / 2 + p.α - (π / 2 + p.α)| ≤ π := by
    rw [show 3 * π / 2 + p.α - (π / 2 + p.α) = π by ring, abs_of_pos hπ]
  refine ⟨_, _, SA, St, SB, hSA0, hSt0, hSB0, hZ₁, hZ₃, ?_, ?_, ?_, ?_, ?_⟩
  · have e : 0 + 2 * p.A * ω * T + 2 * p.A * ω * τ₁ + 2 * p.A * ω * T =
        2 * p.A * ω * (2 * T + τ₁) := by ring
    rw [← e]; exact hdB
  · have h1 := pow_le_pow_left₀ (by positivity) (add_le_add_left (hB _ hdA')
      (0 + 2 * p.A * ω * T)) 2
    have h2 := mul_le_mul_of_nonneg_left h1 hT.le
    rw [zero_add] at h2 hSA
    linarith
  · have e : 0 + 2 * p.A * ω * T + 2 * p.A * ω * τ₁ = 2 * p.A * ω * (T + τ₁) := by ring
    rw [e] at hSt; exact hSt
  · have e : 0 + 2 * p.A * ω * T + 2 * p.A * ω * τ₁ + 2 * p.A * ω * T =
        2 * p.A * ω * (2 * T + τ₁) := by ring
    rw [e] at hSB
    have h1 := pow_le_pow_left₀ (by positivity) (add_le_add_left (hB _ hdB')
      (2 * p.A * ω * (2 * T + τ₁))) 2
    have h2 := mul_le_mul_of_nonneg_left h1 hT.le
    linarith
  · refine ((controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hVA
      ((controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hVt hVB)))).trans ?_
    rw [← ENNReal.ofReal_add hSt0 hSB0, ← ENNReal.ofReal_add hSA0 (add_nonneg hSt0 hSB0)]

/-- **The way down** of the slow-filter pair: from `(3π/2 + α, 0, Z₃)` with
`Z₃ ≥ (P_ref − K)/e^{−ωT}` (`K` the offset of the last transit, `last_bounds`) and
`|Z₃ − P_ref| ≤ 2Aω(2T + τ₁)`: a dwell of the exact length `τ* ≤ 4T + 2τ₁`
(`exists_dwell_time`), then the last transit ends exactly at `(δ_u, 0, P_ref)`. -/
@[tmio TM, powerlib_domain] private theorem slow_down {σP : ℝ} (hσ : σP ≠ 0)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {ω T τ₁ Z₃ : ℝ} (hω : 0 < ω) (hT : 0 < T)
    (hτ₁ : 0 ≤ τ₁)
    (hZ₃ : (p.Pref - lagFilter ω 0 (fun t => p.c0 + p.A *
      Real.sin (trAngle (3 * π / 2 + p.α) p.swingModel.deltaU T t - p.α)) T) /
        Real.exp (-(ω * T)) ≤ Z₃)
    (hd₃ : |Z₃ - p.Pref| ≤ 2 * p.A * ω * (2 * T + τ₁)) :
    ∃ τs Sb SC : ℝ, 0 ≤ τs ∧ τs ≤ 4 * T + 2 * τ₁ ∧ 0 ≤ Sb ∧ 0 ≤ SC ∧
      2 * σP ^ 2 * Sb ≤ τs * (2 * p.A * ω * (2 * T + τ₁ + τs)) ^ 2 ∧
      2 * σP ^ 2 * SC ≤ T * (6 * p.M * π / T ^ 2 + 3 / 2 * p.D * π / T +
        2 * p.A * ω * (3 * T + τ₁ + τs)) ^ 2 ∧
      (⟨p, ω, hω⟩ : Params3).setPointQP σP ![3 * π / 2 + p.α, 0, Z₃]
        ![p.swingModel.deltaU, 0, p.Pref] ≤ ENNReal.ofReal (Sb + SC) := by
  have hA := p.A_pos
  have hM := p.M_pos
  have hDn := p.D_nonneg
  have hπ := Real.pi_pos
  have habs : |p.Pref - p.c0| < p.A := abs_lt.2 ⟨by linarith, by linarith⟩
  obtain ⟨-, e2⟩ := p.esc_angles
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) p.A_pos.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := by rw [div_lt_one hA]; linarith
  have has0 := Real.arcsin_nonneg.mpr hs0
  have has1 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hPb : p.c0 + p.A * Real.sin (3 * π / 2 + p.α - p.α) = p.c0 - p.A := by
    rw [add_sub_cancel_right, sin_three_pi_div_two]; ring
  obtain ⟨hKlo, hKup⟩ := p.last_bounds h0 h1 hω.le hT
  set K := lagFilter ω 0 (fun t => p.c0 + p.A *
    Real.sin (trAngle (3 * π / 2 + p.α) p.swingModel.deltaU T t - p.α)) T with hKdef
  have ha := Real.exp_pos (-(ω * T))
  set Zr := (p.Pref - K) / Real.exp (-(ω * T)) with hZrdef
  have hZr1 : p.Pref ≤ Zr := by rw [hZrdef, le_div_iff₀ ha]; linear_combination hKup
  have hZr0 : p.c0 - p.A < Zr := by linarith
  obtain ⟨τs, hτs0, hτs, hτsb⟩ := exists_dwell_time hω hZr0 hZ₃
  have hτsT : τs ≤ 4 * T + 2 * τ₁ := by
    have h3 : Z₃ - p.Pref ≤ 2 * p.A * ω * (2 * T + τ₁) := (le_abs_self _).trans hd₃
    have hA2 : p.A ≤ Zr - (p.c0 - p.A) := by linarith
    have h4 : (Z₃ - Zr) / (Zr - (p.c0 - p.A)) ≤ (Z₃ - p.Pref) / p.A := by
      rw [div_le_div_iff₀ (by linarith) hA]
      have h5 : 0 ≤ Z₃ - Zr := by linarith
      have : (Z₃ - Zr) * p.A ≤ (Z₃ - Zr) * (Zr - (p.c0 - p.A)) :=
        mul_le_mul_of_nonneg_left hA2 h5
      have : (Z₃ - Zr) * (Zr - (p.c0 - p.A)) ≤ (Z₃ - p.Pref) * (Zr - (p.c0 - p.A)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    have h6 : (Z₃ - p.Pref) / p.A ≤ ω * (4 * T + 2 * τ₁) := by
      rw [div_le_iff₀ hA]; linarith
    have h7 : ω * τs ≤ ω * (4 * T + 2 * τ₁) := by linarith
    exact le_of_mul_le_mul_left h7 hω
  -- the dwell beyond the saddle
  have hd₃' : |Z₃ - p.Pref| ≤ 0 + 2 * p.A * ω * T + 2 * p.A * ω * τ₁ + 2 * p.A * ω * T := by
    have e : 0 + 2 * p.A * ω * T + 2 * p.A * ω * τ₁ + 2 * p.A * ω * T =
        2 * p.A * ω * (2 * T + τ₁) := by ring
    rw [e]; exact hd₃
  obtain ⟨Sb, hSb0, hSb, hdb, hVb⟩ := p.dwell_track hσ hω habs (δd := 3 * π / 2 + p.α) hτs0 hd₃'
  rw [hPb, hτs] at hdb hVb
  obtain ⟨SC, hSC0, hSC, -, hVC⟩ := p.transit_track hσ hω habs (a := 3 * π / 2 + p.α)
    (b := p.swingModel.deltaU) hT hdb
  have hZ₅ : lagFilter ω Zr (fun t => p.c0 + p.A *
      Real.sin (trAngle (3 * π / 2 + p.α) p.swingModel.deltaU T t - p.α)) T = p.Pref := by
    rw [lagFilter_eq_add, ← hKdef, hZrdef]; field_simp; ring
  rw [hZ₅] at hVC
  have hdC' : |p.swingModel.deltaU - (3 * π / 2 + p.α)| ≤ π := by
    rw [show p.swingModel.deltaU - (3 * π / 2 + p.α) =
      -(π / 2 + Real.arcsin ((p.Pref - p.c0) / p.A)) by linear_combination e2, abs_neg,
      abs_of_nonneg (by linarith)]
    linarith
  refine ⟨τs, Sb, SC, hτs0, hτsT, hSb0, hSC0, ?_, ?_, ?_⟩
  · have e : 0 + 2 * p.A * ω * T + 2 * p.A * ω * τ₁ + 2 * p.A * ω * T + 2 * p.A * ω * τs =
        2 * p.A * ω * (2 * T + τ₁ + τs) := by ring
    rw [e] at hSb; exact hSb
  · have e : 0 + 2 * p.A * ω * T + 2 * p.A * ω * τ₁ + 2 * p.A * ω * T + 2 * p.A * ω * τs +
        2 * p.A * ω * T = 2 * p.A * ω * (3 * T + τ₁ + τs) := by ring
    rw [e] at hSC
    have hb : 6 * p.M * |p.swingModel.deltaU - (3 * π / 2 + p.α)| / T ^ 2 + 3 / 2 * p.D *
        |p.swingModel.deltaU - (3 * π / 2 + p.α)| / T ≤ 6 * p.M * π / T ^ 2 +
          3 / 2 * p.D * π / T := by gcongr
    have h1 := pow_le_pow_left₀ (by positivity) (add_le_add_left hb
      (2 * p.A * ω * (3 * T + τ₁ + τs))) 2
    have h2 := mul_le_mul_of_nonneg_left h1 hT.le
    linarith
  · refine ((controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hVb hVC)).trans ?_
    rw [← ENNReal.ofReal_add hSb0 hSC0]

/-- **The slow-filter pair (core)**: for `ω τ₁ ≤ 1` and `8A²ω² t_max³ ≤ DΔU`, the five-piece
three-state pair (`slow_up`, `slow_down`; exact arrival by `slow_sign`) has action below
`2DΔU/σ_P²` (`slow_arith`). -/
@[tmio TM, powerlib_domain] private theorem slow_core {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {ω : ℝ} (hω : 0 < ω)
    (hω1 : ω * p.escSlowDwell ≤ 1)
    (hω2 : 8 * p.A ^ 2 * ω ^ 2 * p.escSlowSpan ^ 3 ≤ p.D * p.escBarrier) :
    ∃ S : ℝ, S < 2 * p.D / σP ^ 2 * p.escBarrier ∧
      (⟨p, ω, hω⟩ : Params3).setPointQP σP ![p.swingModel.deltaS, 0, p.Pref]
        ![p.swingModel.deltaU, 0, p.Pref] ≤ ENNReal.ofReal S := by
  have hA := p.A_pos
  have hM := p.M_pos
  have hΔ := p.escBarrier_pos h0 h1
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := by rw [div_lt_one hA]; linarith
  set s := (p.Pref - p.c0) / p.A with hsdef
  have hPr : p.Pref = p.c0 + p.A * s := by rw [hsdef]; field_simp; ring
  set T := p.escSlowTime with hTdef
  have hT : 0 < T := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set τ₁ := p.escSlowDwell with hτ₁def
  have hτ₁ : τ₁ = 8 * T * (1 + s) / (1 - s) := rfl
  have hτ₁0 : 0 ≤ τ₁ := by rw [hτ₁]; exact div_nonneg (by positivity) (by linarith)
  set tm := p.escSlowSpan with htmdef
  have htm : tm = 7 * T + 3 * τ₁ := rfl
  obtain ⟨Z₁, Z₃, SA, St, SB, hSA0, hSt0, hSB0, hZ₁, hZ₃, hd₃, hSA, hSt, hSB, hVup⟩ :=
    p.slow_up hσ h0 h1 hω hT hτ₁0
  obtain ⟨hKlo, -⟩ := p.last_bounds h0 h1 hω.le hT
  have hy : 8 * (ω * T) * (1 + s) ≤ (ω * τ₁) * (1 - s) := by
    have e : ω * (8 * T * (1 + s) / (1 - s)) * (1 - s) = 8 * (ω * T) * (1 + s) := by
      field_simp [ne_of_gt (sub_pos.2 hs1)]
    rw [hτ₁, e]
  have hZr := slow_sign hA hs0 hs1 (by positivity) hy hω1 (Pt := p.c0 + p.A)
    (Pr := p.Pref) (Pb := p.c0 - p.A) (by rw [hPr]; ring) (by rw [hPr]; ring) hZ₁ rfl hZ₃ hKlo
  obtain ⟨τs, Sb, SC, hτs0, hτsT, hSb0, hSC0, hSb, hSC, hVdown⟩ :=
    p.slow_down hσ h0 h1 hω hT hτ₁0 hZr hd₃
  refine ⟨SA + (St + (SB + (Sb + SC))), ?_, ?_⟩
  · have hDn := p.D_nonneg
    have hAω : 0 ≤ 2 * p.A * ω := by positivity
    set E := 2 * p.A * ω * tm with hEdef
    have hE : ∀ x : ℝ, 0 ≤ x → x ≤ tm → 0 ≤ 2 * p.A * ω * x ∧ 2 * p.A * ω * x ≤ E :=
      fun x hx hxt => ⟨mul_nonneg hAω hx, mul_le_mul_of_nonneg_left hxt hAω⟩
    have hB := slow_transit_le hM hD hΔ (T := T) (le_refl _)
    have hEb : (6 * T + τ₁ + τs) * E ^ 2 ≤ p.D * p.escBarrier := by
      have h1 : 6 * T + τ₁ + τs ≤ 2 * tm := by rw [htm]; linarith
      have h2 : (6 * T + τ₁ + τs) * E ^ 2 ≤ 2 * tm * E ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      have h3 : 2 * tm * E ^ 2 = 8 * p.A ^ 2 * ω ^ 2 * tm ^ 3 := by rw [hEdef]; ring
      linarith
    have hB0 : 0 ≤ 6 * p.M * π / T ^ 2 + 3 / 2 * p.D * π / T := by
      have := Real.pi_pos; positivity
    exact slow_arith (by positivity) hT hτ₁0 hτs0 (by positivity) hSA hSt hSB hSb hSC
      ⟨hB0, le_rfl⟩ ⟨hB0, le_rfl⟩ ⟨hB0, le_rfl⟩
      (hE T hT.le (by rw [htm]; linarith)) (hE _ (by linarith) (by rw [htm]; linarith))
      (hE _ (by linarith) (by rw [htm]; linarith)) (hE _ (by linarith) (by rw [htm]; linarith))
      (hE _ (by linarith) (by rw [htm]; linarith)) hB hEb
  · refine ((controlQuasiPotential_triangle _ _ _ _ _).trans (add_le_add hVup hVdown)).trans ?_
    rw [← ENNReal.ofReal_add (add_nonneg hSA0 (add_nonneg hSt0 hSB0)) (add_nonneg hSb0 hSC0)]
    apply ENNReal.ofReal_le_ofReal
    linarith

/-- **`V₃ < V₂` for every small bandwidth, explicitly** (`D > 0`, `c₀ ≤ P_ref < c₀ + A`,
`σ_P ≠ 0`): if `ω_c τ₁ ≤ 1` and `8A²ω_c² t_max³ ≤ D ΔU` (`τ₁ = escSlowDwell`,
`t_max = escSlowSpan`, `ΔU = escBarrier`), the three-state escape exponent (stable equilibrium to
saddle, set-point noise) is strictly below the two-state one. Pair (`slow_core`): with the
filter nearly frozen the restoring force is `P_ref − P_f`, small along the path, so rest-to-rest
transits of duration `T = escSlowTime` cost `O(1/T)`; a dwell at the top of the well
(`P − P_ref = A(1 − s)`) raises the filter, a dwell of exactly computed length
`τ* = log((Z₃ − P_b)/(Z_r − P_b))/ω_c` beyond the saddle (`P − P_ref = −A(1 + s)`) lowers it to
the value `Z_r` from which the last transit ends exactly at `P_f = P_ref`. -/
@[tmio M, powerlib_domain] theorem setPointQP_lt_swingQP_slow {σP : ℝ} (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {δs δu : ℝ}
    (hδs : δs = Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hδu : δu = π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α) (ωc : ℝ) (hω : 0 < ωc)
    (hω1 : ωc * p.escSlowDwell ≤ 1)
    (hω2 : 8 * p.A ^ 2 * ωc ^ 2 * p.escSlowSpan ^ 3 ≤ p.D * p.escBarrier) :
    (⟨p, ωc, hω⟩ : Params3).setPointQP σP ![δs, 0, p.c0 + p.A * Real.sin (δs - p.α)]
        ![δu, 0, p.c0 + p.A * Real.sin (δu - p.α)] < p.swingQP σP ![δs, 0] ![δu, 0] := by
  have hs : δs = p.swingModel.deltaS := hδs
  have hu : δu = p.swingModel.deltaU := hδu
  have habs : |p.Pref - p.c0| < p.A := abs_lt.2 ⟨by linarith [p.A_pos], by linarith⟩
  obtain ⟨hes, heu, -, -⟩ := p.rest_facts habs
  obtain ⟨S, hS, hV⟩ := p.slow_core hσ hD h0 h1 hω hω1 hω2
  have hV2 : p.swingQP σP ![δs, 0] ![δu, 0] =
      ENNReal.ofReal (2 * p.D / σP ^ 2 * p.escBarrier) := by
    have := p.swingQP_saddle_eq hσ hD h0 h1
    rw [hδs, hδu, this]
    congr 1; simp only [escBarrier]; ring
  rw [hV2, hs, hu, hes, heu]
  refine hV.trans_lt (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hS, ?_⟩)
  have := p.escBarrier_pos h0 h1
  have : 0 < σP ^ 2 := by positivity
  positivity

end Params

end powerlib.GFM.Noise
