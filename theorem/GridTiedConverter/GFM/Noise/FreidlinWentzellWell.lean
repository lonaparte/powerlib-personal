import dependencies.Mathlib
import theorem.Attributes
import theorem.GridTiedConverter.GFM.Noise.FreidlinWentzellExit

/-! # Exit of the noisy two-state GFM from its potential well: the boundary-level exponent

Domain module: the noisy two-state GFM with set-point noise
(`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzell.lean`), the closed potential well below
the saddle level `Params.energyWell η` and its exit time `τ_ε` from the stable equilibrium. Both
exit statements carry the Hamilton–Jacobi value of the well's boundary level,
`V̄(η) = 2D(ΔU − η)/σ_P²`: the mean exit time grows at most at this rate,
`limsup_{ε→0⁺} ε log E τ_ε ≤ V̄(η)` (the bound `GFM.Noise.Params.limsup_log_exitTime_le` of
`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellExit.lean` evaluated), and an exit before
any fixed time is exponentially unlikely at this rate,
`limsup_{ε→0⁺} ε log P(τ_ε ≤ T) ≤ −V̄(η)`. The sup–inf of the rate over the well is evaluated by
following the noiseless flow into a neighbourhood of `x_s` (away from `x_s` the energy `H` drops
by a uniform amount per unit time: LaSalle's argument along the pathwise solution), then a cubic
glue of small rate and the uphill path — the momentum-flipped time reversal of a noiseless
solution from a point just above the boundary level, of rate `(2D/σ_P²)ΔH` — out of the well;
finitely many delayed copies serve the compact well. The fixed-time bound is the large-deviation
upper bound with the Hamilton–Jacobi lower bound of the rate at the first boundary state.

Model boundary.
* The two-state model of `FreidlinWentzell.lean`: state `(δ, p)` on `Fin 2 → ℝ`, drift
  `Params.swingDrift`, noise column `(0, σ_P)`; `σ_P ≠ 0`, `D > 0`, `c₀ ≤ P_ref < c₀ + A`;
  `δ_s = arcsin s + α`, `δ_u = π − arcsin s + α`, `s = (P_ref − c₀)/A`, `H = Params.swingEnergy`,
  `ΔU = U(π − arcsin s) − U(arcsin s)` (`U = Params.potential`).
* The well `Params.energyWell η = {δ_u − 2π ≤ δ ≤ δ_u, H ≤ U(π − arcsin s) − η}`, `η > 0`
  (`η ≤ ΔU` for the mean exit time, so that `x_s` lies in it): compact, invariant under the
  noiseless flow, and `x_s` is its only state keeping its energy along the flow; its boundary is
  the energy level `H(x_u) − η`. The exit time is `Stochastic.LDP.exitTime` of the well from `x_s`
  for a Brownian motion all of whose paths are continuous; `E τ_ε` its lower Lebesgue integral.
* The matching lower bound and the exponential law `ε log E τ_ε → V̄(η)` are in
  `theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellLower.lean` (a chain of deterministic
  time blocks, `theorem/Stochastic/ExitTimeLower.lean`; the strong Markov property is in
  `theorem/Stochastic/StrongMarkov.lean`); the three-state counterpart of the lower bound is
  `theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellFilter.lean`.
* The cut well `Params.cutWell η d = {x ∈ energyWell η : δ ≤ d}` (`δ_s < d < δ_u`,
  `U(d − α) < U(δ_u − α) − η`): its mean exit time grows at most at the rate
  `2D(U(d − α) − U(δ_s − α))/σ_P²` of the cut point `(d, 0)`, the exit leading through the rest
  point `(d', 0)` just beyond the cut; the exit place of the cut well is
  `theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellPlace.lean`. The exit place of the uncut
  well is not concentrated (see the model boundary of `FreidlinWentzellLower.lean`).

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §2–3 (exit through the boundary, the uphill paths as time-reversed relaxation paths of a
damped Hamiltonian system); A. Dembo, O. Zeitouni, *Large Deviations Techniques and
Applications*, 2nd ed. (1998), Lemma 5.7.18 (uniform exit cost from the closure of the domain
through the attractor); LaSalle's invariance argument for the damped swing
(`theorem/PowerSystem/Synchronous/DampedEAC.lean`).

Results.
* `Params.energyWell` (the closed well below the saddle level), `Params.isCompact_energyWell`.
* The noiseless flow `Params.freeSwing` (the solution driven by the path `0`):
  `Params.hasDerivAt_freeSwing`, `Params.pathExt_freeSwing_zero`,
  `Params.swingEnergyDeriv_drift` (`H'(x) b(x) = −D (p/M)²`),
  `Params.hasDerivAt_swingEnergy_freeSwing`, `Params.antitoneOn_swingEnergy_freeSwing`,
  `Params.swingEnergy_freeSwing_le` (the energy decreases along it);
  `Params.eq_rest_of_swingEnergy_freeSwing_eq` (**a state of the well keeping its energy over
  `[0, 1]` is `x_s`**), `Params.exists_swingEnergy_freeSwing_drop` (**uniform energy loss away
  from `x_s`**); `Params.potential_le_swingEnergy`, `Params.potential_sub_two_pi`.
* `Params.exists_horizon_iSup_fwRate_energyWell_le`: for every `γ > 0` there is a horizon `T`
  with `sup_{x ∈ well} inf {J_x^T(φ) : φ leaves the well on [0, T]} ≤ 2D(ΔU − η)/σ_P² + γ`.
* `Params.limsup_log_exitTime_energyWell_le` (**`limsup ε log E τ_ε ≤ 2D(ΔU − η)/σ_P²`** for the
  exit from the well started at `x_s`).
* `Params.cutWell`, `Params.isCompact_cutWell`, `Params.exists_horizon_iSup_fwRate_cutWell_le`,
  `Params.limsup_log_exitTime_cutWell_le` (**`limsup ε log E τ_ε ≤
  2D(U(d − α) − U(δ_s − α))/σ_P²`** for the exit from the cut well).
* `Params.limsup_log_measure_exitTime_le` (**`limsup ε log P(τ_ε ≤ T) ≤ −2D(ΔU − η)/σ_P²`** for
  every fixed horizon `T`).
-/

noncomputable section
namespace powerlib.GFM.Noise

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal NNReal
open powerlib.Stochastic.LDP

namespace Params

variable (p : Params)

/-- The closed potential well of the noisy two-state model below the saddle level, cut at
`H(x_u) − η`: `δ_u − 2π ≤ δ ≤ δ_u`, `H(δ, p) ≤ U(δ_u − α) − η`. -/
def energyWell (η : ℝ) : Set (Fin 2 → ℝ) :=
  {x | π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α - 2 * π ≤ x 0 ∧
    x 0 ≤ π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α ∧
    p.swingEnergy x ≤ p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η}

/-- The noiseless solution of the two-state model from `y` on `[0, T]` (driving path `0`). -/
def freeSwing (σP : ℝ) (y : Fin 2 → ℝ) (T : ℝ≥0) : C(Icc (0 : ℝ) T, Fin 2 → ℝ) :=
  solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP) y 0

/-- The energy derivative along the drift: `H'(x) b(x) = −D (p/M)²`. -/
@[tmio M, powerlib_domain] theorem swingEnergyDeriv_drift (x : Fin 2 → ℝ) :
    p.swingEnergyDeriv x (p.swingDrift x) = -(p.D * (x 1 / p.M) ^ 2) := by
  have hM := p.M_pos.ne'
  simp [swingEnergyDeriv, swingDrift_apply, potentialDeriv, toSM]
  field_simp
  ring

/-- `U(θ − 2π) = U(θ) + 2π (P_ref − c₀)`. -/
@[tmio M, powerlib_domain] theorem potential_sub_two_pi (θ : ℝ) :
    p.potential (θ - 2 * π) = p.potential θ + 2 * π * (p.Pref - p.c0) := by
  simp only [potential, toSM, Real.cos_sub_two_pi]
  ring

variable {σP : ℝ}

/-- The noiseless solution has derivative `b(x(t))` inside `(0, T)`
(`Stochastic.LDP.hasDerivAt_solMap_zero`). -/
@[tmio M, powerlib_domain] theorem hasDerivAt_freeSwing (y : Fin 2 → ℝ) {T : ℝ≥0}
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (pathExt (p.freeSwing σP y T)) (p.swingDrift (pathExt (p.freeSwing σP y T) t))
      t := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  exact hasDerivAt_solMap_zero hK _ y ht

/-- The noiseless solution starts at `y` (`Stochastic.LDP.pathExt_solMap_zero`). -/
@[tmio M, powerlib_domain] theorem pathExt_freeSwing_zero (y : Fin 2 → ℝ) (T : ℝ≥0) :
    pathExt (p.freeSwing σP y T) 0 = y := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  exact pathExt_solMap_zero hK _ y T

/-- The energy derivative along the noiseless solution is `−D (p/M)²`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_swingEnergy_freeSwing (y : Fin 2 → ℝ) {T : ℝ≥0}
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => p.swingEnergy (pathExt (p.freeSwing σP y T) s))
      (-(p.D * (pathExt (p.freeSwing σP y T) t 1 / p.M) ^ 2)) t := by
  have h := (p.hasFDerivAt_swingEnergy _).comp_hasDerivAt t (p.hasDerivAt_freeSwing (σP := σP) y ht)
  rw [swingEnergyDeriv_drift] at h
  exact h

/-- The energy is non-increasing along the noiseless solution. -/
@[tmio M, powerlib_domain] theorem antitoneOn_swingEnergy_freeSwing (y : Fin 2 → ℝ) (T : ℝ≥0) :
    AntitoneOn (fun s => p.swingEnergy (pathExt (p.freeSwing σP y T) s)) (Icc 0 T) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 (T : ℝ))
    ((p.continuous_swingEnergy.comp (continuous_pathExt _)).continuousOn) ?_ ?_
  · rw [interior_Icc]
    exact fun s hs =>
      (p.hasDerivAt_swingEnergy_freeSwing y hs).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro s hs
    rw [(p.hasDerivAt_swingEnergy_freeSwing y hs).deriv]
    exact neg_nonpos.mpr (mul_nonneg p.D_nonneg (sq_nonneg _))

/-- The energy along the noiseless solution stays below its initial value. -/
@[tmio M, powerlib_domain] theorem swingEnergy_freeSwing_le (y : Fin 2 → ℝ) (T : ℝ≥0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    p.swingEnergy (pathExt (p.freeSwing σP y T) t) ≤ p.swingEnergy y := by
  have h := p.antitoneOn_swingEnergy_freeSwing (σP := σP) y T ⟨le_rfl, T.coe_nonneg⟩ ht ht.1
  simp only at h
  rwa [pathExt_freeSwing_zero] at h

/-- `U(δ − α) ≤ H(δ, p)`. -/
@[tmio M, powerlib_domain] theorem potential_le_swingEnergy (x : Fin 2 → ℝ) :
    p.potential (x 0 - p.α) ≤ p.swingEnergy x := by
  have hM := p.M_pos
  unfold swingEnergy
  have : 0 ≤ x 1 ^ 2 / (2 * p.M) := by positivity
  linarith

/-- **The well is invariant** under the noiseless flow (`c₀ ≤ P_ref`, `η > 0`): the energy does
not increase and the angle cannot reach `δ_u` or `δ_u − 2π`, where the energy is at least the
saddle level. -/
@[tmio M, powerlib_domain] private theorem free_mem_energyWell (h0 : p.c0 ≤ p.Pref) {η : ℝ}
    (hη : 0 < η) {y : Fin 2 → ℝ} (hy : y ∈ p.energyWell η) (T : ℝ≥0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : pathExt (p.freeSwing σP y T) t ∈ p.energyWell η := by
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  have hE : ∀ s ∈ Icc (0 : ℝ) T,
      p.swingEnergy (pathExt (p.freeSwing σP y T) s) ≤ p.potential (π - a) - η :=
    fun s hs => (p.swingEnergy_freeSwing_le y T hs).trans hy.2.2
  have hcont : ContinuousOn (fun s => pathExt (p.freeSwing σP y T) s 0) (Icc 0 t) :=
    ((continuous_apply 0).comp (continuous_pathExt _)).continuousOn
  have hy0 : pathExt (p.freeSwing σP y T) 0 0 = y 0 := by rw [pathExt_freeSwing_zero]
  refine ⟨?_, ?_, hE t ht⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc' ht.1 hcont ⟨hlt.le, hy0 ▸ hy.1⟩
    have h1 := p.potential_le_swingEnergy (pathExt (p.freeSwing σP y T) s)
    simp only at hsv
    rw [hsv, show π - a + p.α - 2 * π - p.α = (π - a) - 2 * π by ring,
      p.potential_sub_two_pi] at h1
    have h2 := hE s ⟨hs.1, hs.2.trans ht.2⟩
    have h3 : 0 ≤ 2 * π * (p.Pref - p.c0) := by have := Real.pi_pos; nlinarith
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc ht.1 hcont ⟨hy0 ▸ hy.2.1, hlt.le⟩
    have h1 := p.potential_le_swingEnergy (pathExt (p.freeSwing σP y T) s)
    simp only at hsv
    rw [hsv, show π - a + p.α - p.α = π - a by ring] at h1
    have h2 := hE s ⟨hs.1, hs.2.trans ht.2⟩
    linarith

/-- The angles of the rest points in `[−π − a, π − a]`, `a = arcsin s ∈ [0, π/2)`. -/
@[tmio T, powerlib_foundation] private theorem angle_cases {a θ : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a < π / 2) (hθ1 : -π - a ≤ θ) (hθ2 : θ ≤ π - a) (hs : Real.sin θ = Real.sin a) :
    θ = a ∨ θ = π - a ∨ θ = -π - a := by
  have hπ := Real.pi_pos
  obtain ⟨k, hk | hk⟩ := Real.sin_eq_sin_iff.mp hs
  · have hk1 : (k : ℝ) < 1 := by nlinarith
    have hk0 : (-1 : ℝ) < k := by nlinarith
    have hk' : k = 0 := by
      have : k < 1 := by exact_mod_cast hk1
      have : -1 < k := by exact_mod_cast hk0
      omega
    subst hk'
    left; simp at hk; linarith
  · have hk1 : (k : ℝ) < 1 := by nlinarith
    have hk0 : (-2 : ℝ) < k := by nlinarith
    have : k < 1 := by exact_mod_cast hk1
    have : -2 < k := by exact_mod_cast hk0
    have hk' : k = 0 ∨ k = -1 := by omega
    rcases hk' with rfl | rfl
    · right; left; simp at hk; linarith
    · right; right; simp at hk; linarith

/-- **A state of the well keeping its energy over `[0, 1]` is the stable equilibrium** (`D > 0`,
`c₀ ≤ P_ref < c₀ + A`): the momentum vanishes on `(0, 1)`, so the angle is constant and the rest
condition `A sin(δ − α) = P_ref − c₀` holds; in the well only `δ_s` has energy below the saddle
level. -/
@[tmio M, powerlib_domain] theorem eq_rest_of_swingEnergy_freeSwing_eq (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη : 0 < η) {y : Fin 2 → ℝ}
    (hy : y ∈ p.energyWell η)
    (heq : p.swingEnergy (pathExt (p.freeSwing σP y 1) 1) = p.swingEnergy y) :
    y = ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] := by
  set φ := p.freeSwing σP y 1 with hφ
  have hM := p.M_pos
  have hA := p.A_pos
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ) := by simp
  have hconst : ∀ s ∈ Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ),
      p.swingEnergy (pathExt φ s) = p.swingEnergy y := by
    intro s hs
    have ha := p.antitoneOn_swingEnergy_freeSwing (σP := σP) y 1 hs h1mem (by simpa using hs.2)
    have hb := p.swingEnergy_freeSwing_le (σP := σP) y 1 hs
    simp only at ha
    rw [heq] at ha
    linarith
  have hp : ∀ s ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ), pathExt φ s 1 = 0 := by
    intro s hs
    have hd := p.hasDerivAt_swingEnergy_freeSwing (σP := σP) y hs
    have hc : HasDerivAt (fun r => p.swingEnergy (pathExt φ r)) 0 s := by
      refine (hasDerivAt_const s (p.swingEnergy y)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
      exact hconst r ⟨hr.1.le, hr.2.le⟩
    have h := hd.unique hc
    have h2 : (pathExt φ s 1 / p.M) ^ 2 = 0 := by
      rcases mul_eq_zero.mp (neg_eq_zero.mp h) with h' | h'
      · exact absurd h' hD.ne'
      · exact h'
    have h3 := (pow_eq_zero_iff (n := 2) two_ne_zero).mp h2
    rwa [div_eq_zero_iff, or_iff_left hM.ne'] at h3
  have hcomp : ∀ s ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ), ∀ i,
      HasDerivAt (fun r => pathExt φ r i) (p.swingDrift (pathExt φ s) i) s :=
    fun s hs => hasDerivAt_pi.mp (p.hasDerivAt_freeSwing y hs)
  have hp' : ∀ s ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ), p.swingDrift (pathExt φ s) 1 = 0 := by
    intro s hs
    have hc : HasDerivAt (fun r => pathExt φ r 1) 0 s := by
      refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
      exact hp r hr
    exact (hcomp s hs 1).unique hc
  have hsub : ∀ r ∈ Ioo (0 : ℝ) (1 / 2), r ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ) :=
    fun r hr => ⟨hr.1, by push_cast; linarith [hr.2]⟩
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ) := ⟨by norm_num, by norm_num⟩
  have hcont : ∀ i, ContinuousOn (fun r => pathExt φ r i) (Icc 0 (1 / 2)) := fun i =>
    ((continuous_apply i).comp (continuous_pathExt φ)).continuousOn
  have hφ0 : pathExt φ 0 = y := p.pathExt_freeSwing_zero y 1
  -- the angle is constant on `[0, 1/2]`
  have hδ : pathExt φ (1 / 2) 0 = y 0 := by
    obtain ⟨c, hc, hcv⟩ := exists_hasDerivAt_eq_slope (fun r => pathExt φ r 0)
      (fun r => p.swingDrift (pathExt φ r) 0) (by norm_num : (0 : ℝ) < 1 / 2) (hcont 0)
      (fun r hr => hcomp r (hsub r hr) 0)
    rw [swingDrift_apply] at hcv
    simp only [Matrix.cons_val_zero] at hcv
    rw [hp c (hsub c hc), zero_div, hφ0] at hcv
    have : pathExt φ (1 / 2) 0 - y 0 = 0 := by
      have h2 : (pathExt φ (1 / 2) 0 - y 0) / (1 / 2 - 0) = 0 := hcv.symm
      rwa [div_eq_zero_iff, or_iff_left (by norm_num)] at h2
    linarith
  -- the momentum at `0`
  have hq : y 1 = 0 := by
    obtain ⟨c, hc, hcv⟩ := exists_hasDerivAt_eq_slope (fun r => pathExt φ r 1)
      (fun r => p.swingDrift (pathExt φ r) 1) (by norm_num : (0 : ℝ) < 1 / 2) (hcont 1)
      (fun r hr => hcomp r (hsub r hr) 1)
    rw [hp' c (hsub c hc), hp _ hhalf, hφ0] at hcv
    have h2 : (0 - y 1) / (1 / 2 - 0) = 0 := hcv.symm
    rw [div_eq_zero_iff, or_iff_left (by norm_num)] at h2
    linarith
  -- the rest condition
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hA).mpr (by linarith)
  have hsin : Real.sin (y 0 - p.α) = Real.sin a := by
    have h := hp' _ hhalf
    rw [swingDrift_apply] at h
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
    rw [hp _ hhalf, hδ] at h
    simp only [zero_div, mul_zero, sub_zero] at h
    rw [ha, Real.sin_arcsin (by linarith) hs1.le]
    field_simp
    linarith
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hs0
  have ha1 : a < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hE : p.swingEnergy y = p.potential (y 0 - p.α) := by
    simp [swingEnergy, hq]
  have hyE := hy.2.2
  rcases angle_cases ha0 ha1 (by linarith [hy.1]) (by linarith [hy.2.1]) hsin with h | h | h
  · ext i
    fin_cases i
    · simp; linarith
    · simpa using hq
  · exfalso
    rw [hE, h] at hyE
    linarith
  · exfalso
    rw [hE, h, show -π - a = (π - a) - 2 * π by ring, p.potential_sub_two_pi] at hyE
    have : 0 ≤ 2 * π * (p.Pref - p.c0) := by have := Real.pi_pos; nlinarith
    linarith

/-- The well is compact. -/
@[tmio M, powerlib_domain] theorem isCompact_energyWell (η : ℝ) :
    IsCompact (p.energyWell η) := by
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  have hM := p.M_pos
  have hA := p.A_pos
  have hclosed : IsClosed (p.energyWell η) := by
    have e : p.energyWell η = {x : Fin 2 → ℝ | π - a + p.α - 2 * π ≤ x 0} ∩
        ({x | x 0 ≤ π - a + p.α} ∩ {x | p.swingEnergy x ≤ p.potential (π - a) - η}) := by
      ext x; simp [energyWell, ha]
    rw [e]
    exact (isClosed_le continuous_const (continuous_apply 0)).inter
      ((isClosed_le (continuous_apply 0) continuous_const).inter
        (isClosed_le p.continuous_swingEnergy continuous_const))
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  set C := p.potential (π - a) - η + |p.Pref - p.c0| * (|π - a + p.α| + 2 * π + |p.α|) + p.A
    with hC
  refine (Metric.isBounded_Icc (![π - a + p.α - 2 * π, -(1 + 2 * p.M * C)] : Fin 2 → ℝ)
    ![π - a + p.α, 1 + 2 * p.M * C]).subset fun x hx => ?_
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hθ : |x 0 - p.α| ≤ |π - a + p.α| + 2 * π + |p.α| := by
    rw [abs_le]
    constructor <;> cases abs_cases (π - a + p.α) <;> cases abs_cases p.α <;>
      nlinarith [Real.pi_pos]
  have hU : -p.potential (x 0 - p.α) ≤ |p.Pref - p.c0| * (|π - a + p.α| + 2 * π + |p.α|) + p.A :=
    by
    simp only [potential, toSM]
    have h1 := Real.neg_one_le_cos (x 0 - p.α)
    have h2 := Real.cos_le_one (x 0 - p.α)
    have h3 : (p.Pref - p.c0) * (x 0 - p.α) ≤ |p.Pref - p.c0| * |x 0 - p.α| := by
      rw [← abs_mul]; exact le_abs_self _
    have h4 : |p.Pref - p.c0| * |x 0 - p.α| ≤
        |p.Pref - p.c0| * (|π - a + p.α| + 2 * π + |p.α|) :=
      mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
    nlinarith
  have hkin : x 1 ^ 2 ≤ 2 * p.M * C := by
    unfold swingEnergy at hx3
    have : x 1 ^ 2 / (2 * p.M) ≤ C := by linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  constructor
  · intro i; fin_cases i
    · simpa using hx1
    · simp; nlinarith [sq_nonneg (x 1 + 1)]
  · intro i; fin_cases i
    · simpa using hx2
    · simp; nlinarith [sq_nonneg (x 1 - 1)]

/-- The state at time `T` of the noiseless solution from `y`. -/
@[tmio M, powerlib_domain] private theorem free_add_one (y : Fin 2 → ℝ) (T : ℝ≥0) :
    pathExt (p.freeSwing σP y (T + 1)) ((T + 1 : ℝ≥0) : ℝ) =
      pathExt (p.freeSwing σP (pathExt (p.freeSwing σP y T) T) 1) 1 := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  have h := pathExt_solMap_add hK (columnsCLM fun _ : Fin 1 => swingColumn σP) y
    (T₁ := T) (T₂ := 1) (0 : C(Icc (0 : ℝ) (T + 1 : ℝ≥0), Fin 1 → ℝ))
    (t := 1) ⟨zero_le_one, by simp⟩
  have hz : ∀ s, pathExt (0 : C(Icc (0 : ℝ) (T + 1 : ℝ≥0), Fin 1 → ℝ)) s = 0 := fun s => by
    simp only [pathExt, IccExtend, Function.comp_apply]
    rfl
  have hshift : shiftPath T 1 (0 : C(Icc (0 : ℝ) (T + 1 : ℝ≥0), Fin 1 → ℝ)) = 0 := by
    ext t j
    show pathExt (0 : C(Icc (0 : ℝ) (T + 1 : ℝ≥0), Fin 1 → ℝ)) (T + t) j -
      pathExt (0 : C(Icc (0 : ℝ) (T + 1 : ℝ≥0), Fin 1 → ℝ)) T j = (0 : Fin 1 → ℝ) j
    rw [hz, hz]
    simp
  have hres : pathExt (solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP) y
      (0 : C(Icc (0 : ℝ) (T + 1 : ℝ≥0), Fin 1 → ℝ))) T = pathExt (p.freeSwing σP y T) T := by
    rw [← pathExt_restrictPath le_self_add _ ⟨T.coe_nonneg, le_rfl⟩, restrictPath_solMap hK]
    rfl
  rw [hshift, hres] at h
  simp only [freeSwing]
  push_cast
  exact h

/-- **Uniform energy loss away from `x_s`**: for `r > 0` there is `c > 0` such that every state
of the well at distance `≥ r` from `x_s` loses at least `c` of energy along the noiseless flow
over `[0, 1]`. -/
@[tmio M, powerlib_domain] theorem exists_swingEnergy_freeSwing_drop (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : 0 < r) :
    ∃ c > 0, ∀ y ∈ p.energyWell η, r ≤ dist y ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] →
      p.swingEnergy (pathExt (p.freeSwing σP y 1) 1) ≤ p.swingEnergy y - c := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  set xs : Fin 2 → ℝ := ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] with hxs
  set C := p.energyWell η ∩ {y | r ≤ dist y xs} with hC
  have hCc : IsCompact C :=
    (p.isCompact_energyWell η).inter_right (isClosed_le continuous_const
      (continuous_id.dist continuous_const))
  have hcont : Continuous fun y => pathExt (p.freeSwing σP y 1) 1 := by
    have h := (continuous_solMap_uncurry hK (columnsCLM fun _ : Fin 1 => swingColumn σP)
      (T := 1)).comp (continuous_id.prodMk (continuous_const (y := (0 : C(Icc (0 : ℝ)
        ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ)))))
    exact (continuous_eval_const _).comp h
  set d : (Fin 2 → ℝ) → ℝ :=
    fun y => p.swingEnergy y - p.swingEnergy (pathExt (p.freeSwing σP y 1) 1)
    with hd
  have hdc : Continuous d := p.continuous_swingEnergy.sub (p.continuous_swingEnergy.comp hcont)
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨1, one_pos, fun y hy hry => ?_⟩
    have : y ∈ C := ⟨hy, hry⟩
    rw [hCe] at this
    exact absurd this (notMem_empty y)
  obtain ⟨y₀, hy₀, hmin⟩ := hCc.exists_isMinOn hCne hdc.continuousOn
  have hd0 : 0 < d y₀ := by
    have hle : 0 ≤ d y₀ := by
      have := p.swingEnergy_freeSwing_le (σP := σP) y₀ 1 (t := 1) (by simp)
      simp only [hd]; linarith
    refine lt_of_le_of_ne hle fun h => ?_
    have heq : p.swingEnergy (pathExt (p.freeSwing σP y₀ 1) 1) = p.swingEnergy y₀ := by
      simp only [hd] at h; linarith
    have hrest := p.eq_rest_of_swingEnergy_freeSwing_eq hD h0 h1 hη hy₀.1 heq
    have := hy₀.2
    simp only [mem_ofPred_eq] at this
    rw [hrest, dist_self] at this
    linarith
  refine ⟨d y₀, hd0, fun y hy hry => ?_⟩
  have h := hmin (show y ∈ C from ⟨hy, hry⟩)
  change d y₀ ≤ d y at h
  simp only [hd] at h ⊢
  linarith

/-- **Every state of the well enters any neighbourhood of `x_s`** along the noiseless flow, at an
integer time (`D > 0`, `c₀ ≤ P_ref < c₀ + A`, `η > 0`). -/
@[tmio M, powerlib_domain] private theorem exists_free_mem_ball (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : 0 < r)
    {y : Fin 2 → ℝ} (hy : y ∈ p.energyWell η) :
    ∃ n : ℕ, dist (pathExt (p.freeSwing σP y n) (n : ℝ≥0))
      ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] < r := by
  obtain ⟨c, hc, hdrop⟩ := p.exists_swingEnergy_freeSwing_drop (σP := σP) hD h0 h1 hη hr
  set ψ : ℝ≥0 → Fin 2 → ℝ := fun T => pathExt (p.freeSwing σP y T) T with hψ
  have hmem : ∀ T : ℝ≥0, ψ T ∈ p.energyWell η := fun T =>
    p.free_mem_energyWell h0 hη hy T ⟨T.coe_nonneg, le_rfl⟩
  obtain ⟨m₀, -, hm₀⟩ := (p.isCompact_energyWell η).exists_isMinOn
    ⟨y, hy⟩ p.continuous_swingEnergy.continuousOn
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hstep : ∀ n : ℕ, p.swingEnergy (ψ n) ≤ p.swingEnergy y - n * c := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, sub_zero, hψ]
      rw [NNReal.coe_zero, pathExt_freeSwing_zero]
    | succ n ih =>
      have e : ψ ((n + 1 : ℕ) : ℝ≥0) = pathExt (p.freeSwing σP (ψ n) 1) 1 := by
        simp only [hψ]
        rw [Nat.cast_succ, free_add_one]
      rw [e]
      have := hdrop (ψ n) (hmem n) (hcon n)
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((p.swingEnergy y - p.swingEnergy m₀) / c)
  have h1' := hstep n
  have h2 := hm₀ (hmem n)
  simp only [mem_ofPred_eq] at h2
  rw [div_lt_iff₀ hc] at hn
  linarith

/-- From a driving path that takes `x_s` out of a compact `K` inside the well at rate `≤ V`, a
common horizon on which every state of `K` leaves `K` at rate `≤ V`: the noiseless flow enters a
neighbourhood of `x_s` served by the same path (`exists_free_mem_ball`, continuity of the solution
map), and finitely many delayed copies serve the compact `K`. -/
@[tmio M, powerlib_domain] private theorem exists_horizon_of_escape (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη : 0 < η)
    {W : Set (Fin 2 → ℝ)} (hWc : IsCompact W) (hWη : W ⊆ p.energyWell η) {V : ℝ≥0∞}
    {Ts : ℝ≥0} {ws : C(Icc (0 : ℝ) Ts, Fin 1 → ℝ)} (hws0 : pathExt ws 0 = 0)
    (hout : ∃ t, solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP)
      ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] ws t ∉ W)
    (hrateV : schilderRate Ts ws ≤ V) :
    ∃ T : ℝ≥0, 0 < (T : ℝ) ∧
      ⨆ x ∈ W, ⨅ φ ∈ {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) | ∃ t, φ t ∉ W},
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) x T φ ≤ V := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  set N := columnsCLM fun _ : Fin 1 => swingColumn σP with hN
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  -- a neighbourhood of `x_s` driven out of `W` by `ws`
  set O := {φ : C(Icc (0 : ℝ) Ts, Fin 2 → ℝ) | ∃ t, φ t ∉ W} with hO
  have hOo : ∀ T : ℝ≥0, IsOpen {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) | ∃ t, φ t ∉ W} := by
    intro T
    have : {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) | ∃ t, φ t ∉ W} = ⋃ t, (fun φ => φ t) ⁻¹' Wᶜ := by
      ext φ; simp
    rw [this]
    exact isOpen_iUnion fun t => hWc.isClosed.isOpen_compl.preimage (continuous_eval_const t)
  have hxs_out : solMap p.swingDrift N (![a + p.α, 0]) ws ∈ O := hout
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ((hOo Ts).preimage
    ((continuous_solMap_uncurry hK N).comp (continuous_id.prodMk continuous_const)))
    (![a + p.α, 0]) hxs_out
  -- for each state: free flow into the ball, then `ws`
  have hpt : ∀ x, ∃ n : ℕ, x ∈ W → ∃ t, solMap p.swingDrift N x
      (delayPath ((n : ℝ≥0) : ℝ) ((n : ℝ≥0) + Ts) ws) t ∉ W := by
    intro x
    by_cases hx : x ∈ W
    swap
    · exact ⟨0, fun h => absurd h hx⟩
    obtain ⟨n, hn⟩ := p.exists_free_mem_ball (σP := σP) hD h0 h1 hη hr (hWη hx)
    refine ⟨n, fun _ => ?_⟩
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hsplit := (forall_mem_iff_restrict_restart (K := W) _).mp hall
    have hres : restrictPath le_self_add (delayPath ((n : ℝ≥0) : ℝ) ((n : ℝ≥0) + Ts) ws) = 0 := by
      ext t j
      have ht : (t : ℝ) - ((n : ℝ≥0) : ℝ) ≤ 0 := by have := t.2.2; linarith
      have e : pathExt ws ((t : ℝ) - ((n : ℝ≥0) : ℝ)) = pathExt ws 0 := by
        simp only [pathExt, IccExtend, Function.comp_apply]
        rw [projIcc_of_le_left _ ht, projIcc_of_le_left _ le_rfl]
      show pathExt ws ((t : ℝ) - ((n : ℝ≥0) : ℝ)) j = (0 : Fin 1 → ℝ) j
      rw [e, hws0]
    have hshift : shiftPath n Ts (delayPath ((n : ℝ≥0) : ℝ) ((n : ℝ≥0) + Ts) ws) = ws := by
      ext t j
      simp only [shiftPath, ContinuousMap.coe_mk]
      have hn0 : (0 : ℝ) ≤ ((n : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      have hmem : ((n : ℝ≥0) : ℝ) + t ∈ Icc (0 : ℝ) ((n : ℝ≥0) + Ts : ℝ≥0) :=
        ⟨by linarith [t.2.1], by rw [NNReal.coe_add]; linarith [t.2.2]⟩
      have hmem0 : ((n : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) ((n : ℝ≥0) + Ts : ℝ≥0) :=
        ⟨hn0, by rw [NNReal.coe_add]; linarith [Ts.coe_nonneg]⟩
      rw [pathExt_of_mem _ hmem, pathExt_of_mem _ hmem0]
      simp only [delayPath, ContinuousMap.coe_mk, add_sub_cancel_left, sub_self, hws0,
        Pi.sub_apply, Pi.zero_apply, sub_zero]
      rw [pathExt_of_mem _ t.2]
    have hend : pathExt (solMap p.swingDrift N x (delayPath ((n : ℝ≥0) : ℝ) ((n : ℝ≥0) + Ts)
        ws)) ((n : ℝ≥0) : ℝ) = pathExt (p.freeSwing σP x n) ((n : ℝ≥0) : ℝ) := by
      rw [← pathExt_restrictPath le_self_add _ ⟨NNReal.coe_nonneg _, le_rfl⟩,
        restrictPath_solMap hK, hres]
      rfl
    have h2 := hsplit.2
    rw [restartPath_solMap hK, hshift, hend] at h2
    have hin := hball (show pathExt (p.freeSwing σP x n) (n : ℝ≥0) ∈ Metric.ball _ r from hn)
    obtain ⟨t, ht⟩ := hin
    exact ht (h2 t)
  choose nx hnx using hpt
  -- open sets of initial states served by the same driving path
  set U : (Fin 2 → ℝ) → Set (Fin 2 → ℝ) := fun x =>
    {y | ∃ t, solMap p.swingDrift N y (delayPath ((nx x : ℝ≥0) : ℝ) ((nx x : ℝ≥0) + Ts) ws) t ∉ W}
    with hU
  have hUo : ∀ x ∈ W, IsOpen (U x) := fun x _ =>
    (hOo _).preimage ((continuous_solMap_uncurry hK N).comp
      (continuous_id.prodMk continuous_const))
  have hxU : ∀ x ∈ W, x ∈ U x := fun x hx => hnx x hx
  obtain ⟨tset, htW, htfin, hcover⟩ := hWc.elim_finite_subcover_image
    (b := W) (c := U) hUo (fun x hx => mem_biUnion hx (hxU x hx))
  -- the common horizon
  set T : ℝ≥0 := 1 ⊔ htfin.toFinset.sup fun x => (nx x : ℝ≥0) + Ts with hT
  have hTpos : 0 < (T : ℝ) := by
    have : (1 : ℝ≥0) ≤ T := le_sup_left
    exact_mod_cast lt_of_lt_of_le one_pos this
  refine ⟨T, hTpos, iSup₂_le fun y hy => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (hcover hy)
  have hTx : (nx x : ℝ≥0) + Ts ≤ T :=
    le_trans (Finset.le_sup (f := fun x => (nx x : ℝ≥0) + Ts) (htfin.mem_toFinset.mpr hxt))
      le_sup_right
  set w := delayPath ((nx x : ℝ≥0) : ℝ) T ws with hw
  have hleave : ∃ t, solMap p.swingDrift N y w t ∉ W := by
    obtain ⟨t, ht⟩ := hyx
    refine ⟨inclusion (Icc_subset_Icc_right (NNReal.coe_le_coe.mpr hTx)) t, ?_⟩
    have e := congrArg (fun φ => φ t) (restrictPath_solMap hK N y hTx w)
    rw [show restrictPath hTx w = delayPath ((nx x : ℝ≥0) : ℝ) ((nx x : ℝ≥0) + Ts) ws from rfl]
      at e
    rw [← e] at ht
    exact ht
  have hrate : schilderRate T w ≤ schilderRate Ts ws :=
    schilderRate_delayPath_le (by positivity) (by exact_mod_cast hTx) ws
  calc ⨅ φ ∈ {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) | ∃ t, φ t ∉ W},
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) y T φ
      ≤ fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) y T (solMap p.swingDrift N y w) :=
        biInf_le _ hleave
    _ ≤ schilderRate T w := pushRate_le _ _ _
    _ ≤ V := hrate.trans hrateV


/-- The momentum flip `(δ, p) ↦ (δ, −p)`. -/
private def flipMomentum (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 0, -x 1]

/-- **Energy identity of the noiseless flow**:
`H(x(T)) = H(y) − (D/M²) ∫₀ᵀ p²` along the noiseless solution from `y`. -/
@[tmio M, powerlib_domain] private theorem energy_free_eq (y : Fin 2 → ℝ) (T : ℝ≥0) :
    ∫ r in (0 : ℝ)..T, p.D * (pathExt (p.freeSwing σP y T) r 1 / p.M) ^ 2 =
      p.swingEnergy y - p.swingEnergy (pathExt (p.freeSwing σP y T) T) := by
  have hc : Continuous fun r => p.D * (pathExt (p.freeSwing σP y T) r 1 / p.M) ^ 2 :=
    continuous_const.mul ((((continuous_apply 1).comp (continuous_pathExt _)).div_const _).pow 2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le T.coe_nonneg
    ((p.continuous_swingEnergy.comp (continuous_pathExt (p.freeSwing σP y T))).continuousOn)
    (fun r hr => p.hasDerivAt_swingEnergy_freeSwing (σP := σP) y hr) (hc.neg.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_neg] at h
  simp only [Function.comp_apply] at h
  rw [pathExt_freeSwing_zero] at h
  linarith

/-- **The uphill path**: the momentum-flipped time reversal of the noiseless solution from `y`
on `[0, T]`, driven by the control `(2D/(M σ_P)) p`, is the solution from `flip(x(T))`; it ends at
`flip(y)` and its driving path has Schilder rate at most `(2D/σ_P²)(H(y) − H(x(T)))`. -/
@[tmio M, powerlib_domain] private theorem exists_uphill (hσ : σP ≠ 0) (hD : 0 < p.D)
    (y : Fin 2 → ℝ) (T : ℝ≥0) :
    ∃ W : C(Icc (0 : ℝ) T, Fin 1 → ℝ),
      solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP)
          (flipMomentum (pathExt (p.freeSwing σP y T) T)) W
          ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = flipMomentum y ∧
        schilderRate T W ≤ ENNReal.ofReal (2 * p.D / σP ^ 2 *
          (p.swingEnergy y - p.swingEnergy (pathExt (p.freeSwing σP y T) T))) ∧
        pathExt W 0 = 0 := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  set N := columnsCLM fun _ : Fin 1 => swingColumn σP with hN
  set φ := p.freeSwing σP y T with hφ
  have hM := p.M_pos
  set ψ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) := ⟨fun s => flipMomentum (pathExt φ (T - s)),
    continuous_pi fun i => by
      fin_cases i
      · exact ((continuous_apply 0).comp (continuous_pathExt φ)).comp
          (continuous_const.sub continuous_subtype_val)
      · exact (((continuous_apply 1).comp (continuous_pathExt φ)).comp
          (continuous_const.sub continuous_subtype_val)).neg⟩ with hψ
  set u : ℝ → Fin 1 → ℝ := fun s _ => 2 * p.D / (p.M * σP) * -pathExt φ (T - s) 1 with hu_def
  have hu : Continuous u := continuous_pi fun _ => continuous_const.mul
    (((continuous_apply 1).comp (continuous_pathExt φ)).comp (continuous_const.sub
      continuous_id)).neg
  obtain ⟨W, hW⟩ := exists_primitive_path (T := T) (hu.intervalIntegrable 0 T)
  have hder : ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivAt (pathExt ψ) (p.swingDrift (pathExt ψ s) + N (u s)) s := by
    intro s hs
    have hTs : (T : ℝ) - s ∈ Ioo (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hφd := (p.hasDerivAt_freeSwing (σP := σP) y hTs).scomp s
      ((hasDerivAt_id s).const_sub (T : ℝ))
    rw [← hφ] at hφd
    have hev : pathExt ψ =ᶠ[𝓝 s] fun r => flipMomentum (pathExt φ (T - r)) := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
      rw [pathExt_of_mem _ ⟨hr.1.le, hr.2.le⟩]
      rfl
    have hval : pathExt ψ s = flipMomentum (pathExt φ (T - s)) := hev.self_of_nhds
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    rw [hval]
    refine hasDerivAt_pi.mpr fun i => ?_
    have hc := hasDerivAt_pi.mp hφd
    fin_cases i
    · refine (hc 0).congr_deriv ?_
      simp [flipMomentum, swingDrift_apply, hN, columnsCLM_apply, swingColumn, hu_def]
      ring
    · refine ((hc 1).neg).congr_deriv ?_
      simp [flipMomentum, swingDrift_apply, hN, columnsCLM_apply, swingColumn, hu_def]
      field_simp
      ring
  have hsol := eq_solMap_of_hasDerivAt hK N hu hW hder
  have hψ0 : pathExt ψ 0 = flipMomentum (pathExt φ T) := by
    rw [pathExt_of_mem _ ⟨le_rfl, T.coe_nonneg⟩]
    simp [hψ]
  refine ⟨W, ?_, ?_, ?_⟩
  · rw [← hψ0, ← hsol]
    simp only [hψ, ContinuousMap.coe_mk, sub_self]
    rw [hφ, pathExt_freeSwing_zero]
  rotate_left
  · rw [pathExt_of_mem _ ⟨le_rfl, T.coe_nonneg⟩, hW]
    simp
  · refine (schilderRate_le_of_continuous hu hW).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    unfold controlAction
    have he := p.energy_free_eq (σP := σP) y T
    rw [← hφ] at he
    simp only [hu_def, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    have e1 : ∫ s in (0 : ℝ)..T, (2 * p.D / (p.M * σP) * -pathExt φ (T - s) 1) ^ 2 =
        (2 * p.D / (p.M * σP)) ^ 2 * ∫ r in (0 : ℝ)..T, pathExt φ r 1 ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_comp_sub_left
        (fun r => (2 * p.D / (p.M * σP) * -pathExt φ r 1) ^ 2) (T : ℝ)]
      simp only [sub_self, sub_zero]
      congr 1; funext r; ring
    have e2 : ∫ r in (0 : ℝ)..T, p.D * (pathExt φ r 1 / p.M) ^ 2 =
        p.D / p.M ^ 2 * ∫ r in (0 : ℝ)..T, pathExt φ r 1 ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext r; field_simp
    rw [e1]
    rw [e2] at he
    have hDM : p.D / p.M ^ 2 ≠ 0 := by positivity
    have hI : ∫ r in (0 : ℝ)..T, pathExt φ r 1 ^ 2 =
        (p.swingEnergy y - p.swingEnergy (pathExt φ T)) / (p.D / p.M ^ 2) := by
      rw [← he]; field_simp
    rw [hI]
    field_simp

/-- Bounds of the cubic Hermite profiles and their derivatives on `[0, 1]`. -/
@[tmio T, powerlib_foundation] private theorem hermite_bounds {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    |3 * t ^ 2 - 2 * t ^ 3| ≤ 1 ∧ |t ^ 3 - t ^ 2| ≤ 1 ∧ |6 * t - 6 * t ^ 2| ≤ 2 ∧
      |3 * t ^ 2 - 2 * t| ≤ 1 ∧ |6 - 12 * t| ≤ 6 ∧ |6 * t - 2| ≤ 4 := by
  have h1 : 0 ≤ t ^ 2 * (3 - 2 * t) := mul_nonneg (sq_nonneg t) (by linarith)
  have h2 : 0 ≤ (1 - t) ^ 2 * (1 + 2 * t) := mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : 0 ≤ t ^ 2 * (1 - t) := mul_nonneg (sq_nonneg t) (by linarith)
  have h4 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  have h5 : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  have h6 : 0 ≤ (2 * t - 1) ^ 2 := sq_nonneg _
  have h7 : 0 ≤ (1 - t) * (1 + 3 * t) := mul_nonneg (by linarith) (by linarith)
  have h8 : 0 ≤ (3 * t - 1) ^ 2 := sq_nonneg _
  refine ⟨abs_le.mpr ⟨by nlinarith, by nlinarith⟩, abs_le.mpr ⟨by nlinarith, by nlinarith⟩,
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩, abs_le.mpr ⟨by nlinarith, by nlinarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- **Leaving the stable equilibrium cheaply** (`σ_P ≠ 0`, `c₀ ≤ P_ref < c₀ + A`): for every
`γ > 0` there is `ρ > 0` such that every state within `ρ` of `x_s` is reached from `x_s` at time
`1` by a driving path of Schilder rate at most `γ` (cubic Hermite angle profile
`δ_s + e₀ (3t² − 2t³) + (e₁/M)(t³ − t²)`, control `(M δ̈ + D δ̇ + A sin(δ − α) − P_ref + c₀)/σ_P`
of size `O(ρ)`). -/
@[tmio M, powerlib_domain] private theorem exists_glue (hσ : σP ≠ 0) (h0 : p.c0 ≤ p.Pref)
    (h1 : p.Pref < p.c0 + p.A) {γ : ℝ} (hγ : 0 < γ) :
    ∃ ρ > 0, ∀ y : Fin 2 → ℝ, dist y ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] < ρ →
      ∃ W : C(Icc (0 : ℝ) (1 : ℝ≥0), Fin 1 → ℝ),
        solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP)
            ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] W
            ⟨(1 : ℝ≥0), right_mem_Icc.mpr (1 : ℝ≥0).coe_nonneg⟩ = y ∧
          schilderRate 1 W ≤ ENNReal.ofReal γ ∧ pathExt W 0 = 0 := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  set N := columnsCLM fun _ : Fin 1 => swingColumn σP with hN
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  have hM := p.M_pos
  have hA := p.A_pos
  have hDn := p.D_nonneg
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hA).mpr (by linarith)
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hsin : p.A * Real.sin a = p.Pref - p.c0 := by
    rw [ha, Real.sin_arcsin (by linarith) hs1.le]
    field_simp
  set C₀ := 6 * p.M + 4 + 2 * p.D + p.D / p.M + p.A + p.A / p.M with hC₀
  have hC₀pos : 0 < C₀ := by positivity
  have hσa : 0 < |σP| := abs_pos.mpr hσ
  refine ⟨|σP| * Real.sqrt γ / (C₀ + 1), by positivity, fun y hy => ?_⟩
  set e₀ := y 0 - (a + p.α) with he₀
  set e₁ := y 1 with he₁
  set ρ := |σP| * Real.sqrt γ / (C₀ + 1) with hρ
  have hy0 : |e₀| ≤ ρ := by
    have := (dist_le_pi_dist y ![a + p.α, 0] 0).trans hy.le
    rwa [Real.dist_eq] at this
  have hy1 : |e₁| ≤ ρ := by
    have := (dist_le_pi_dist y ![a + p.α, 0] 1).trans hy.le
    simpa [Real.dist_eq] using this
  -- the angle profile and its derivatives
  set δf : ℝ → ℝ := fun t => a + p.α + e₀ * (3 * t ^ 2 - 2 * t ^ 3) + e₁ / p.M * (t ^ 3 - t ^ 2)
    with hδf
  set δ1 : ℝ → ℝ := fun t => e₀ * (6 * t - 6 * t ^ 2) + e₁ / p.M * (3 * t ^ 2 - 2 * t) with hδ1
  set δ2 : ℝ → ℝ := fun t => e₀ * (6 - 12 * t) + e₁ / p.M * (6 * t - 2) with hδ2
  have hd0 : ∀ t, HasDerivAt δf (δ1 t) t := fun t => by
    have := ((((hasDerivAt_pow 2 t).const_mul 3).sub ((hasDerivAt_pow 3 t).const_mul 2)).const_mul
      e₀).const_add (a + p.α) |>.add (((hasDerivAt_pow 3 t).sub (hasDerivAt_pow 2 t)).const_mul
        (e₁ / p.M))
    convert this using 1
    simp only [hδ1]
    push_cast
    ring
  have hd1 : ∀ t, HasDerivAt δ1 (δ2 t) t := fun t => by
    have := ((((hasDerivAt_id t).const_mul 6).sub ((hasDerivAt_pow 2 t).const_mul 6)).const_mul
      e₀).add ((((hasDerivAt_pow 2 t).const_mul 3).sub ((hasDerivAt_id t).const_mul 2)).const_mul
        (e₁ / p.M))
    convert this using 1
    · funext x; simp only [hδ1, id, Pi.add_apply, Pi.sub_apply]
    · simp only [hδ2]; ring
  set v : ℝ → ℝ := fun t => (p.M * δ2 t + p.D * δ1 t - (p.Pref - p.c0) +
    p.A * Real.sin (δf t - p.α)) / σP with hv
  have hvc : Continuous v := by
    simp only [hv, hδ1, hδ2, hδf]; fun_prop
  set u : ℝ → Fin 1 → ℝ := fun t _ => v t with hu
  have huc : Continuous u := continuous_pi fun _ => hvc
  obtain ⟨W, hW⟩ := exists_primitive_path (T := (1 : ℝ≥0)) (huc.intervalIntegrable 0 1)
  set ψ : C(Icc (0 : ℝ) (1 : ℝ≥0), Fin 2 → ℝ) := ⟨fun t => ![δf t, p.M * δ1 t], by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact (show Continuous δf by simp only [hδf]; fun_prop).comp continuous_subtype_val
    · exact (continuous_const.mul (show Continuous δ1 by simp only [hδ1]; fun_prop)).comp
        continuous_subtype_val⟩ with hψ
  have hder : ∀ t ∈ Ioo (0 : ℝ) (1 : ℝ≥0),
      HasDerivAt (pathExt ψ) (p.swingDrift (pathExt ψ t) + N (u t)) t := by
    intro t ht
    have hev : pathExt ψ =ᶠ[𝓝 t] fun r => ![δf r, p.M * δ1 r] := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      rw [pathExt_of_mem _ ⟨hr.1.le, hr.2.le⟩]
      rfl
    rw [hev.self_of_nhds]
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    refine hasDerivAt_pi.mpr fun i => ?_
    fin_cases i
    · refine (hd0 t).congr_deriv ?_
      simp [swingDrift_apply, hN, columnsCLM_apply, swingColumn]
      field_simp
    · refine ((hd1 t).const_mul p.M).congr_deriv ?_
      simp [swingDrift_apply, hN, columnsCLM_apply, swingColumn, hu, hv]
      field_simp
      ring
  have hsol := eq_solMap_of_hasDerivAt hK N huc hW hder
  have hψ0 : pathExt ψ 0 = ![a + p.α, 0] := by
    rw [pathExt_of_mem _ ⟨le_rfl, zero_le_one⟩]
    show ![δf 0, p.M * δ1 0] = _
    ext i; fin_cases i <;> simp [hδf, hδ1]
  rw [hψ0] at hsol
  refine ⟨W, ?_, ?_, ?_⟩
  rotate_right
  · rw [pathExt_of_mem _ ⟨le_rfl, zero_le_one⟩, hW]
    simp
  · rw [← hsol]
    show ![δf 1, p.M * δ1 1] = y
    ext i; fin_cases i
    · simp [hδf, he₀]; ring
    · simp [hδ1, he₁]; field_simp; ring
  · refine (schilderRate_le_of_continuous huc hW).trans (ENNReal.ofReal_le_ofReal ?_)
    -- `|v| ≤ C₀ ρ/|σ_P|` on `[0, 1]`
    have hvb : ∀ t ∈ Icc (0 : ℝ) 1, |v t| ≤ C₀ * ρ / |σP| := by
      intro t ht
      have ht0 := ht.1
      have ht1 := ht.2
      obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hermite_bounds ht0 ht1
      have hρ0 : 0 ≤ ρ := by positivity
      have hsin' : |p.A * Real.sin (δf t - p.α) - (p.Pref - p.c0)| ≤ p.A * (ρ + ρ / p.M) := by
        rw [← hsin, ← mul_sub, abs_mul, abs_of_pos hA]
        refine mul_le_mul_of_nonneg_left ?_ hA.le
        refine (Real.abs_sin_sub_sin_le _ _).trans ?_
        have : δf t - p.α - a = e₀ * (3 * t ^ 2 - 2 * t ^ 3) + e₁ / p.M * (t ^ 3 - t ^ 2) := by
          simp only [hδf]; ring
        rw [this]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hM]
        have h1' : |e₀| * |3 * t ^ 2 - 2 * t ^ 3| ≤ ρ * 1 :=
          mul_le_mul hy0 hb1 (abs_nonneg _) hρ0
        have h2' : |e₁| / p.M * |t ^ 3 - t ^ 2| ≤ ρ / p.M * 1 :=
          mul_le_mul (div_le_div_of_nonneg_right hy1 hM.le) hb2 (abs_nonneg _) (by positivity)
        linarith
      have hδ1b : |δ1 t| ≤ 2 * ρ + ρ / p.M := by
        simp only [hδ1]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hM]
        have h1' : |e₀| * |6 * t - 6 * t ^ 2| ≤ ρ * 2 := mul_le_mul hy0 hb3 (abs_nonneg _) hρ0
        have h2' : |e₁| / p.M * |3 * t ^ 2 - 2 * t| ≤ ρ / p.M * 1 :=
          mul_le_mul (div_le_div_of_nonneg_right hy1 hM.le) hb4 (abs_nonneg _) (by positivity)
        linarith
      have hδ2b : |δ2 t| ≤ 6 * ρ + 4 * ρ / p.M := by
        simp only [hδ2]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hM]
        have h1' : |e₀| * |6 - 12 * t| ≤ ρ * 6 := mul_le_mul hy0 hb5 (abs_nonneg _) hρ0
        have h2' : |e₁| / p.M * |6 * t - 2| ≤ ρ / p.M * 4 :=
          mul_le_mul (div_le_div_of_nonneg_right hy1 hM.le) hb6 (abs_nonneg _) (by positivity)
        have e4 : ρ / p.M * 4 = 4 * ρ / p.M := by ring
        linarith
      have hnum : |p.M * δ2 t + p.D * δ1 t - (p.Pref - p.c0) + p.A * Real.sin (δf t - p.α)| ≤
          C₀ * ρ := by
        have e : p.M * δ2 t + p.D * δ1 t - (p.Pref - p.c0) + p.A * Real.sin (δf t - p.α) =
            p.M * δ2 t + p.D * δ1 t + (p.A * Real.sin (δf t - p.α) - (p.Pref - p.c0)) := by ring
        rw [e]
        have hx := abs_add_le (p.M * δ2 t + p.D * δ1 t)
          (p.A * Real.sin (δf t - p.α) - (p.Pref - p.c0))
        have hy := abs_add_le (p.M * δ2 t) (p.D * δ1 t)
        have hm : |p.M * δ2 t| = p.M * |δ2 t| := by rw [abs_mul, abs_of_pos hM]
        have hd : |p.D * δ1 t| = p.D * |δ1 t| := by rw [abs_mul, abs_of_nonneg hDn]
        have h1' : p.M * |δ2 t| ≤ p.M * (6 * ρ + 4 * ρ / p.M) :=
          mul_le_mul_of_nonneg_left hδ2b hM.le
        have h2' : p.D * |δ1 t| ≤ p.D * (2 * ρ + ρ / p.M) := mul_le_mul_of_nonneg_left hδ1b hDn
        have e2 : C₀ * ρ = p.M * (6 * ρ + 4 * ρ / p.M) + p.D * (2 * ρ + ρ / p.M) +
            p.A * (ρ + ρ / p.M) := by
          simp only [hC₀]; field_simp; ring
        linarith
      simp only [hv]
      rw [abs_div]
      exact div_le_div_of_nonneg_right hnum hσa.le
    have hint : ∫ t in (0 : ℝ)..(1 : ℝ≥0), ∑ j, u t j ^ 2 ≤ (C₀ * ρ / |σP|) ^ 2 := by
      have hle : ∀ t ∈ Icc (0 : ℝ) 1, ∑ j, u t j ^ 2 ≤ (C₀ * ρ / |σP|) ^ 2 := by
        intro t ht
        simp only [hu, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
        exact sq_le_sq' (abs_le.mp (hvb t ht)).1 (abs_le.mp (hvb t ht)).2
      have hcu : Continuous fun t => ∑ j, u t j ^ 2 :=
        continuous_finsetSum _ fun j _ => ((continuous_apply j).comp huc).pow 2
      have := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
        (hcu.intervalIntegrable 0 1) (intervalIntegrable_const (c := (C₀ * ρ / |σP|) ^ 2)) hle
      simpa using this
    have hval : (C₀ * ρ / |σP|) ^ 2 ≤ γ := by
      have hsq := Real.sq_sqrt hγ.le
      rw [hρ, show C₀ * (|σP| * Real.sqrt γ / (C₀ + 1)) / |σP| = C₀ / (C₀ + 1) * Real.sqrt γ by
        field_simp]
      rw [mul_pow, hsq]
      have : (C₀ / (C₀ + 1)) ^ 2 ≤ 1 := by
        rw [div_pow, div_le_one (by positivity)]
        nlinarith
      nlinarith
    unfold controlAction
    have h1 : ((1 : ℝ≥0) : ℝ) = 1 := NNReal.coe_one
    simp only [h1] at hint ⊢
    linarith

/-- **Driving `x_s` through a state at rest momentum, cheaply**: for `z = (δ, 0)` in a well
`Params.energyWell η'` (`η' > 0`) and `g > 0`, a driving path starting at `0` takes the solution
from `x_s` through `z` (it leaves every set not containing `z`) at Schilder rate at most
`(2D/σ_P²)(H(z) − H(x_s)) + g`: a cubic glue of small rate to the momentum flip of a state of the
noiseless flow from `z` near `x_s`, then the uphill path (`exists_glue`, `exists_uphill`,
`Stochastic.LDP.schilderRate_concatPath_le`). -/
@[tmio M, powerlib_domain] private theorem exists_drive_to (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η' : ℝ} (hη' : 0 < η')
    {z : Fin 2 → ℝ} (hz : z ∈ p.energyWell η') (hz1 : z 1 = 0) {g : ℝ} (hg : 0 < g) :
    ∃ Ts : ℝ≥0, ∃ ws : C(Icc (0 : ℝ) Ts, Fin 1 → ℝ), pathExt ws 0 = 0 ∧
      (∀ S : Set (Fin 2 → ℝ), z ∉ S → ∃ t, solMap p.swingDrift
        (columnsCLM fun _ : Fin 1 => swingColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] ws t ∉ S) ∧
      schilderRate Ts ws ≤ ENNReal.ofReal (2 * p.D / σP ^ 2 * (p.swingEnergy z -
        p.swingEnergy ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0]) + g) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  set N := columnsCLM fun _ : Fin 1 => swingColumn σP with hN
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  set xs : Fin 2 → ℝ := ![a + p.α, 0] with hxs
  have hσ2 : 0 < σP ^ 2 := by positivity
  set ac := 2 * p.D / σP ^ 2 with hac
  have hac0 : 0 < ac := by positivity
  have hfz : flipMomentum z = z := by
    ext i; fin_cases i <;> simp [flipMomentum, hz1]
  -- radii: the glue and the continuity of the energy at `x_s`
  obtain ⟨ρ₁, hρ₁, hglue⟩ := p.exists_glue (σP := σP) hσ h0 h1 (γ := g / 2) (by positivity)
  obtain ⟨ρ₂, hρ₂, hHc⟩ : ∃ ρ₂ > 0, ∀ y, dist y xs < ρ₂ →
      p.swingEnergy xs - g / (2 * ac) < p.swingEnergy y := by
    obtain ⟨ρ₂, hρ₂, h⟩ := Metric.continuousAt_iff.mp p.continuous_swingEnergy.continuousAt
      (g / (2 * ac)) (by positivity)
    refine ⟨ρ₂, hρ₂, fun y hy => ?_⟩
    have := h hy
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hρ0 : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
  -- the noiseless flow from `z` comes near `x_s`
  obtain ⟨n, hn⟩ := p.exists_free_mem_ball (σP := σP) hD h0 h1 (η := η') hη' hρ0 hz
  set y₁ := pathExt (p.freeSwing σP z n) ((n : ℝ≥0) : ℝ) with hy₁
  have hflip : dist (flipMomentum y₁) xs ≤ dist y₁ xs := by
    refine (dist_pi_le_iff dist_nonneg).mpr fun i => ?_
    fin_cases i
    · simpa [flipMomentum, hxs] using dist_le_pi_dist y₁ xs 0
    · have := dist_le_pi_dist y₁ xs 1
      simp only [flipMomentum, hxs, Real.dist_eq] at this ⊢
      simpa [abs_neg] using this
  obtain ⟨Wg, hWg, hWgr, hWg0⟩ :=
    hglue _ (lt_of_lt_of_le (lt_of_le_of_lt hflip hn) (min_le_left _ _))
  obtain ⟨Wu, hWu, hWur, hWu0⟩ := p.exists_uphill hσ hD z n
  rw [hfz] at hWu
  have hE1 := hHc y₁ (lt_of_lt_of_le hn (min_le_right _ _))
  have hE2 : p.swingEnergy y₁ ≤ p.swingEnergy z :=
    p.swingEnergy_freeSwing_le (σP := σP) z n (t := ((n : ℝ≥0) : ℝ))
      ⟨NNReal.coe_nonneg _, le_rfl⟩
  -- the concatenated driving path from `x_s`
  set w := concatPath Wg Wu with hw
  have hw0 : pathExt w 0 = 0 := by
    rw [pathExt_of_mem _ ⟨le_rfl, NNReal.coe_nonneg _⟩]
    show pathExt Wg 0 + pathExt Wu (0 - ((1 : ℝ≥0) : ℝ)) = 0
    have e : pathExt Wu (0 - ((1 : ℝ≥0) : ℝ)) = pathExt Wu 0 := by
      simp only [pathExt, IccExtend, Function.comp_apply]
      rw [projIcc_of_le_left _ (by norm_num), projIcc_of_le_left _ le_rfl]
    rw [e, hWg0, hWu0, add_zero]
  refine ⟨(1 : ℝ≥0) + n, w, hw0, fun S hzS => ?_, ?_⟩
  · by_contra hall
    simp only [not_exists, not_not] at hall
    have h2 := ((forall_mem_iff_restrict_restart (K := S) _).mp hall).2
    have hend : pathExt (solMap p.swingDrift N xs w) ((1 : ℝ≥0) : ℝ) = flipMomentum y₁ := by
      rw [← pathExt_restrictPath le_self_add _ (s := ((1 : ℝ≥0) : ℝ))
          ⟨NNReal.coe_nonneg _, le_rfl⟩, restrictPath_solMap hK,
        restrictPath_concatPath _ _ hWu0, pathExt_of_mem _ ⟨NNReal.coe_nonneg _, le_rfl⟩]
      exact hWg
    rw [restartPath_solMap hK, shiftPath_concatPath _ _ hWu0, hend] at h2
    exact hzS (hWu ▸ h2 ⟨(n : ℝ≥0), right_mem_Icc.mpr (NNReal.coe_nonneg _)⟩)
  · -- its rate
    refine (schilderRate_concatPath_le Wg Wu).trans ?_
    have hX : 0 ≤ 2 * p.D / σP ^ 2 * (p.swingEnergy z - p.swingEnergy y₁) :=
      mul_nonneg hac0.le (by linarith)
    calc schilderRate 1 Wg + schilderRate (n : ℝ≥0) Wu
        ≤ ENNReal.ofReal (g / 2) +
            ENNReal.ofReal (2 * p.D / σP ^ 2 * (p.swingEnergy z - p.swingEnergy y₁)) :=
          add_le_add hWgr hWur
      _ = ENNReal.ofReal (g / 2 + 2 * p.D / σP ^ 2 * (p.swingEnergy z - p.swingEnergy y₁)) :=
          (ENNReal.ofReal_add (by positivity) hX).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← hac]
          have : ac * (g / (2 * ac)) = g / 2 := by field_simp
          nlinarith

/-- **Leaving the well from every state at the cost of its boundary level** (`σ_P ≠ 0`, `D > 0`,
`c₀ ≤ P_ref < c₀ + A`, `0 < η ≤ ΔU`): for every `γ > 0` there is a horizon `T > 0` such that from
every state of the well some path leaving it on `[0, T]` has Freidlin–Wentzell rate at most
`2D(ΔU − η)/σ_P² + γ`. Construction: from `x_s` through a point `z` slightly above the boundary
level, at rest momentum (`exists_drive_to`: a glue and the momentum-flipped time reversal of the
noiseless flow from `z`); the noiseless flow brings every state of the well near `x_s`, and
finitely many delayed copies serve the compact well (`exists_horizon_of_escape`). -/
@[tmio M, powerlib_domain] theorem exists_horizon_iSup_fwRate_energyWell_le (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) {γ : ℝ≥0∞} (hγ : 0 < γ) :
    ∃ T : ℝ≥0, 0 < (T : ℝ) ∧
      ⨆ x ∈ p.energyWell η, ⨅ φ ∈ {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) |
          ∃ t, φ t ∉ p.energyWell η},
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) x T φ ≤
      ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) / σP ^ 2) + γ := by
  rcases eq_or_ne γ ⊤ with hγt | hγt
  · exact ⟨1, one_pos, by rw [hγt, add_top]; exact le_top⟩
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  set xs : Fin 2 → ℝ := ![a + p.α, 0] with hxs
  set Hl := p.potential (π - a) - η with hHl
  have hA := p.A_pos
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hA).mpr (by linarith)
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hs0
  have ha1 : a < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hσ2 : 0 < σP ^ 2 := by positivity
  set ac := 2 * p.D / σP ^ 2 with hac
  have hac0 : 0 < ac := by positivity
  set g := γ.toReal with hg
  have hg0 : 0 < g := ENNReal.toReal_pos hγ.ne' hγt
  have hγg : γ = ENNReal.ofReal g := (ENNReal.ofReal_toReal hγt).symm
  -- the target point `z` slightly above the boundary level
  set ζ := min (η / 2) (g / (4 * ac)) with hζ
  have hζ0 : 0 < ζ := lt_min (by linarith) (by positivity)
  have hζη : ζ < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hζg : ac * ζ ≤ g / 4 := by
    have := min_le_right (η / 2) (g / (4 * ac))
    rw [← hζ] at this
    calc ac * ζ ≤ ac * (g / (4 * ac)) := mul_le_mul_of_nonneg_left this hac0.le
      _ = g / 4 := by field_simp
  have hUc : Continuous p.potential :=
    continuous_iff_continuousAt.2 fun θ => (p.hasDerivAt_potential θ).continuousAt
  obtain ⟨δz, hδz, hUz⟩ : ∃ δz ∈ Icc (a + p.α) (π - a + p.α),
      p.potential (δz - p.α) = Hl + ζ := by
    have hcont : ContinuousOn (fun δ => p.potential (δ - p.α)) (Icc (a + p.α) (π - a + p.α)) :=
      (hUc.comp (continuous_id.sub continuous_const)).continuousOn
    have hmem : Hl + ζ ∈ Icc (p.potential (a + p.α - p.α)) (p.potential (π - a + p.α - p.α)) := by
      simp only [add_sub_cancel_right]
      exact ⟨by linarith, by linarith⟩
    exact intermediate_value_Icc (by linarith) hcont hmem
  set z : Fin 2 → ℝ := ![δz, 0] with hz
  have hzE : p.swingEnergy z = Hl + ζ := by simp [swingEnergy, hz, hUz]
  have hπ := Real.pi_pos
  have hzW' : z ∈ p.energyWell (η - ζ) :=
    ⟨by simp [hz]; linarith [hδz.1], by simp [hz]; linarith [hδz.2], by rw [hzE]; linarith⟩
  have hzout : z ∉ p.energyWell η := fun h => by
    have := h.2.2
    rw [hzE] at this
    linarith
  obtain ⟨Ts, w, hw0, hthrough, hrate⟩ := p.exists_drive_to hσ hD h0 h1 (η' := η - ζ)
    (by linarith) hzW' (by simp [hz]) (g := g / 2) (by positivity)
  have hxsE : p.swingEnergy xs = p.potential a := by simp [swingEnergy, hxs]
  have hrate' : schilderRate Ts w ≤
      ENNReal.ofReal (2 * p.D * (p.potential (π - a) - p.potential a - η) / σP ^ 2) + γ := by
    refine hrate.trans ?_
    have hV0 : 0 ≤ ac * (Hl - p.potential a) := mul_nonneg hac0.le (by linarith)
    rw [hγg, ← ENNReal.ofReal_add (by rw [show 2 * p.D * (p.potential (π - a) - p.potential a -
      η) / σP ^ 2 = ac * (Hl - p.potential a) by rw [hac, hHl]; ring]; exact hV0) hg0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hac, hzE, hxsE, show 2 * p.D * (p.potential (π - a) - p.potential a - η) / σP ^ 2 =
      ac * (Hl - p.potential a) by rw [hac, hHl]; ring]
    nlinarith
  exact p.exists_horizon_of_escape hD h0 h1 hη0 (p.isCompact_energyWell η) subset_rfl hw0
    (hthrough _ hzout) hrate'

/-- **Mean exit time from the potential well, upper bound at the boundary level** (two states,
`σ_P ≠ 0`, `D > 0`, `c₀ ≤ P_ref < c₀ + A`, `0 < η ≤ ΔU`): for a Brownian motion with continuous
paths, the exit time `τ_ε` of the noisy two-state model started at `x_s` from the well
`Params.energyWell η` satisfies `limsup_{ε→0⁺} ε log E τ_ε ≤ 2D(ΔU − η)/σ_P²`,
`ΔU = U(δ_u) − U(δ_s)` (the generic bound `Params.limsup_log_exitTime_le` evaluated by
`Params.exists_horizon_iSup_fwRate_energyWell_le`). -/
@[tmio M, powerlib_domain] theorem limsup_log_exitTime_energyWell_le (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous fun t => B t ω) :
    limsup (fun ε : ℝ => (ε : EReal) * ENNReal.log (∫⁻ ω, exitTime p.swingDrift
        (columnsCLM fun _ : Fin 1 => swingColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] (p.energyWell η) (√ε) B hBc ω ∂P))
        (𝓝[>] 0) ≤
      ((ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) / σP ^ 2) : ℝ≥0∞) : EReal) := by
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  set v := 2 * p.D * (p.potential (π - a) - p.potential a - η) / σP ^ 2 with hv
  have hA := p.A_pos
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hA).mpr (by linarith)
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hs0
  have ha1 : a < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hv0 : 0 ≤ v := by
    have : 0 < σP ^ 2 := by positivity
    have : 0 ≤ p.potential (π - a) - p.potential a - η := by linarith
    positivity
  have hxs : (![a + p.α, 0] : Fin 2 → ℝ) ∈ p.energyWell η := by
    refine ⟨by simp; linarith [Real.pi_pos], by simp; linarith, ?_⟩
    simp [swingEnergy]
    linarith
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb not_lt_bot
  | top => exact le_top
  | coe b =>
    rw [EReal.coe_ennreal_ofReal, max_eq_left hv0, EReal.coe_lt_coe_iff] at hb
    obtain ⟨T, hT, hsup⟩ := p.exists_horizon_iSup_fwRate_energyWell_le hσ hD h0 h1 hη0 hη1
      (γ := ENNReal.ofReal (b - v)) (ENNReal.ofReal_pos.mpr (by linarith))
    refine (p.limsup_log_exitTime_le hB hBc (p.isCompact_energyWell η) hxs hT).trans ?_
    refine (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hsup).trans ?_
    rw [← ENNReal.ofReal_add hv0 (by linarith), add_sub_cancel, EReal.coe_ennreal_ofReal,
      max_eq_left (by linarith)]

/-- **Exit from the well before a fixed time is exponentially unlikely, at the rate of its
boundary level** (two states, `σ_P ≠ 0`, `D > 0`, `c₀ ≤ P_ref < c₀ + A`, `η > 0`): for every
horizon `T`, the exit time `τ_ε` of the noisy model started at `x_s` from `Params.energyWell η`
satisfies `limsup_{ε→0⁺} ε log P(τ_ε ≤ T) ≤ −2D(ΔU − η)/σ_P²`. A path leaving the well reaches
the energy level `H(x_u) − η` (or a saddle angle, above it); its rate dominates the
quasi-potential there (`Stochastic.LDP.iInf_pushRate_le_of_le`), which is at least the
Hamilton–Jacobi value (`Params.fwQP_ge`); the large-deviation upper bound
(`Params.limsup_iSup_setPoint_le`) concludes. -/
@[tmio M, powerlib_domain] theorem limsup_log_measure_exitTime_le (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη0 : 0 < η)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω)
    (T : ℝ≥0) :
    limsup (fun ε : ℝ => (ε : EReal) * ENNReal.log (P {ω | exitTime p.swingDrift
        (columnsCLM fun _ : Fin 1 => swingColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] (p.energyWell η) (√ε) B hBc ω ≤ T}))
        (𝓝[>] 0) ≤
      -((ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) / σP ^ 2) : ℝ≥0∞) : EReal) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  set N := columnsCLM fun _ : Fin 1 => swingColumn σP with hN
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  set xs : Fin 2 → ℝ := ![a + p.α, 0] with hxs
  set W := p.energyWell η with hW
  set Hl := p.potential (π - a) - η with hHl
  have hA := p.A_pos
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hA).mpr (by linarith)
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hs0
  have ha1 : a < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  set T' : ℝ≥0 := T + 1 with hT'def
  have hT' : 0 < (T' : ℝ) := by rw [hT'def, NNReal.coe_add]; positivity
  let _ : MeasurableSpace C(Icc (0 : ℝ) T', Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T', Fin 1 → ℝ) := ⟨rfl⟩
  let _ : MeasurableSpace C(Icc (0 : ℝ) T', Fin 2 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T', Fin 2 → ℝ) := ⟨rfl⟩
  obtain ⟨X, hX, -, hXB⟩ := exists_version (P := P) hB hT'
  set A := {φ : C(Icc (0 : ℝ) T', Fin 2 → ℝ) | ∃ t, φ t ∉ W} with hA_def
  -- an exit by `T` is an exit on the horizon `T + 1`
  have hincl : ∀ ε, {ω | exitTime p.swingDrift N xs W (√ε) B hBc ω ≤ T} ⊆
      {ω | solMap p.swingDrift N xs (√ε • brownPath B hBc T' ω) ∈ A} := by
    intro ε ω hω
    have hlt : exitTime p.swingDrift N xs W (√ε) B hBc ω < (T' : ℝ≥0∞) :=
      lt_of_le_of_lt hω (by rw [hT'def]; exact_mod_cast lt_add_one T)
    obtain ⟨T'', hT''⟩ := iInf_lt_iff.mp hlt
    obtain ⟨t, ht⟩ := iInf_lt_iff.mp hT''
    obtain ⟨htW, htlt⟩ := iInf_lt_iff.mp ht
    have htT' : (t : ℝ) < T' := by
      rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hT'] at htlt
      exact htlt
    have ht0 : (0 : ℝ) ≤ t := (mem_Icc.mp t.2).1
    refine ⟨⟨t, ht0, htT'.le⟩, ?_⟩
    have e1 := restrictPath_solMap hK N xs (le_sup_left : T' ≤ T' ⊔ T'')
      (√ε • brownPath B hBc (T' ⊔ T'') ω)
    have e2 := restrictPath_solMap hK N xs (le_sup_right : T'' ≤ T' ⊔ T'')
      (√ε • brownPath B hBc (T' ⊔ T'') ω)
    rw [restrictPath_smul, restrictPath_brownPath] at e1 e2
    have v1 := congrArg (fun φ => φ ⟨t, ht0, htT'.le⟩) e1
    have v2 := congrArg (fun φ => φ t) e2
    rw [← v1]
    rw [← v2] at htW
    exact htW
  -- the open interior of the well
  set W' := {x : Fin 2 → ℝ | π - a + p.α - 2 * π < x 0 ∧ x 0 < π - a + p.α ∧
    p.swingEnergy x < Hl} with hW'
  have hW'o : IsOpen W' :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt (continuous_apply 0) continuous_const).inter
        (isOpen_lt p.continuous_swingEnergy continuous_const))
  have hW'W : W' ⊆ W := fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  have hclA : closure A ⊆ {φ : C(Icc (0 : ℝ) T', Fin 2 → ℝ) | ¬ MapsTo φ univ W'} := by
    refine closure_minimal (fun φ hφ hmaps => ?_) ?_
    · obtain ⟨t, ht⟩ := hφ
      exact ht (hW'W (hmaps (mem_univ t)))
    · exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hW'o).isClosed_compl
  -- every path leaving the interior from `x_s` costs at least the level value
  have hrate : ENNReal.ofReal (2 * p.D * (p.potential (π - a) - p.potential a - η) / σP ^ 2) ≤
      ⨅ φ ∈ closure A, fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) xs T' φ := by
    refine le_iInf₂ fun φ hφ => ?_
    rcases eq_or_ne (fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) xs T' φ) ⊤ with
      htop | htop
    · rw [htop]; exact le_top
    -- the path starts at `x_s`
    have hφ0 : φ ⟨0, le_rfl, T'.coe_nonneg⟩ = xs := by
      obtain ⟨w, hw⟩ := iInf_lt_iff.mp (lt_top_iff_ne_top.mpr htop)
      obtain ⟨hwφ, hwr⟩ := iInf_lt_iff.mp hw
      have hw0 := pathExt_zero_of_schilderRate_ne_top (ne_top_of_lt hwr)
      rw [← hwφ, solMap_spec hK]
      have : w ⟨0, le_rfl, T'.coe_nonneg⟩ = 0 := by
        ext j; fin_cases j
        rw [← pathExt_of_mem w ⟨le_rfl, T'.coe_nonneg⟩]
        exact hw0
      simp [this]
    -- a time at which the energy reaches the level
    obtain ⟨t₂, ht₂⟩ : ∃ t₂ : Icc (0 : ℝ) T', Hl ≤ p.swingEnergy (φ t₂) := by
      have hout := (hclA hφ)
      simp only [mem_ofPred_eq, MapsTo, mem_univ, true_implies, not_forall] at hout
      obtain ⟨t₁, ht₁⟩ := hout
      by_cases hE : Hl ≤ p.swingEnergy (φ t₁)
      · exact ⟨t₁, hE⟩
      have hstrip : ¬ (π - a + p.α - 2 * π < φ t₁ 0 ∧ φ t₁ 0 < π - a + p.α) := fun h =>
        ht₁ ⟨h.1, h.2, lt_of_not_ge hE⟩
      have hcont : ContinuousOn (fun s => pathExt φ s 0) (Icc 0 t₁) :=
        ((continuous_apply 0).comp (continuous_pathExt φ)).continuousOn
      have hv0 : pathExt φ 0 0 = a + p.α := by
        rw [pathExt_of_mem _ ⟨le_rfl, T'.coe_nonneg⟩, hφ0]; simp [hxs]
      have hvt : pathExt φ t₁ 0 = φ t₁ 0 := by rw [pathExt_of_mem _ t₁.2]
      have hπ := Real.pi_pos
      rcases not_and_or.mp hstrip with hl | hr
      · rw [not_lt] at hl
        obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc' t₁.2.1 hcont
          (show π - a + p.α - 2 * π ∈ Icc (pathExt φ t₁ 0) (pathExt φ 0 0) from
            ⟨by rw [hvt]; exact hl, by rw [hv0]; linarith⟩)
        simp only at hsv
        have hsm : s ∈ Icc (0 : ℝ) T' := ⟨hs.1, hs.2.trans t₁.2.2⟩
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
            ⟨by rw [hv0]; linarith, by rw [hvt]; exact hr⟩)
        simp only at hsv
        have hsm : s ∈ Icc (0 : ℝ) T' := ⟨hs.1, hs.2.trans t₁.2.2⟩
        refine ⟨⟨s, hsm⟩, ?_⟩
        have h1' := p.potential_le_swingEnergy (φ ⟨s, hsm⟩)
        have hsv' : φ ⟨s, hsm⟩ 0 = π - a + p.α := by
          rw [← pathExt_of_mem _ hsm]; exact hsv
        rw [hsv', show π - a + p.α - p.α = π - a by ring] at h1'
        linarith
    -- the rate dominates the Hamilton–Jacobi value at that state
    have hq := iInf_pushRate_le_of_le hK N xs φ (t := ⟨t₂, t₂.2.1⟩) t₂.2.2
    have hhj := p.fwQP_ge hσ xs (φ t₂)
    have hxsE : p.swingEnergy xs = p.potential a := by simp [swingEnergy, hxs]
    refine le_trans ?_ (hhj.trans hq)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hxsE]
    have hσ2 : 0 < σP ^ 2 := by positivity
    rw [show 2 * p.D * (p.potential (π - a) - p.potential a - η) / σP ^ 2 =
      2 * p.D / σP ^ 2 * (Hl - p.potential a) by rw [hHl]; ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- the large-deviation upper bound
  have hu := p.limsup_iSup_setPoint_le (σP := σP) hT' hB hX hXB (isCompact_singleton (x := xs))
    A
  simp only [iSup_singleton, iInf_singleton] at hu
  calc limsup (fun ε : ℝ => (ε : EReal) * ENNReal.log
          (P {ω | exitTime p.swingDrift N xs W (√ε) B hBc ω ≤ T})) (𝓝[>] 0)
      ≤ limsup (fun ε : ℝ => (ε : EReal) * ENNReal.log
          (P {ω | solMap p.swingDrift N xs (√ε • X ω) ∈ A})) (𝓝[>] 0) := by
        refine limsup_le_limsup ?_
        filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        refine mul_le_mul_of_nonneg_left (ENNReal.log_le_log ?_) (by exact_mod_cast hε.le)
        refine (measure_mono (hincl ε)).trans (le_of_eq (measure_congr ?_))
        filter_upwards [brownPath_ae_eq hBc hXB] with ω hω
        simp only [hω]
    _ ≤ -(⨅ φ ∈ closure A,
          ((fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) xs T' φ : ℝ≥0∞) : EReal)) := hu
    _ ≤ _ := by
        refine EReal.neg_le_neg_iff.mpr (le_iInf₂ fun φ hφ => ?_)
        exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hrate.trans (iInf₂_le φ hφ))


/-! ## The well cut at an angle -/

/-- **The cut well**: the states of `Params.energyWell η` with angle at most `d`. For
`δ_s < d < δ_u` with `U(d − α) < U(δ_u − α) − η` its boundary is the cut segment `δ = d`, on
which `H = U(d − α) + p²/(2M)` is least at the rest point `(d, 0)`, and an arc of the level
`H = U(δ_u − α) − η`. -/
def cutWell (η d : ℝ) : Set (Fin 2 → ℝ) := p.energyWell η ∩ {x | x 0 ≤ d}

@[tmio M, powerlib_domain] theorem isCompact_cutWell (η d : ℝ) : IsCompact (p.cutWell η d) :=
  (p.isCompact_energyWell η).inter_right (isClosed_le (continuous_apply 0) continuous_const)

/-- **Leaving the cut well from every state at the cost of the cut point** (`σ_P ≠ 0`, `D > 0`,
`c₀ ≤ P_ref < c₀ + A`, `η > 0`, `δ_s < d < δ_u`, `U(d − α) < U(δ_u − α) − η`): for every `γ > 0`
there is a horizon `T > 0` such that from every state of the cut well some path leaving it on
`[0, T]` has Freidlin–Wentzell rate at most `2D(U(d − α) − U(δ_s − α))/σ_P² + γ`: through the rest
point `(d', 0)` just beyond the cut (`exists_drive_to`, `exists_horizon_of_escape`). -/
@[tmio M, powerlib_domain] theorem exists_horizon_iSup_fwRate_cutWell_le (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη0 : 0 < η)
    {d : ℝ} (hd0 : Real.arcsin ((p.Pref - p.c0) / p.A) + p.α < d)
    (hd1 : d < π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hdU : p.potential (d - p.α) < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η)
    {γ : ℝ≥0∞} (hγ : 0 < γ) :
    ∃ T : ℝ≥0, 0 < (T : ℝ) ∧
      ⨆ x ∈ p.cutWell η d, ⨅ φ ∈ {φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ) | ∃ t, φ t ∉ p.cutWell η d},
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) x T φ ≤
      ENNReal.ofReal (2 * p.D * (p.potential (d - p.α) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) / σP ^ 2) + γ := by
  rcases eq_or_ne γ ⊤ with hγt | hγt
  · exact ⟨1, one_pos, by rw [hγt, add_top]; exact le_top⟩
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  set xs : Fin 2 → ℝ := ![a + p.α, 0] with hxs
  set Hl := p.potential (π - a) - η with hHl
  have hA := p.A_pos
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hA).mpr (by linarith)
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hs0
  have ha1 : a < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hπ := Real.pi_pos
  have hσ2 : 0 < σP ^ 2 := by positivity
  set ac := 2 * p.D / σP ^ 2 with hac
  have hac0 : 0 < ac := by positivity
  set g := γ.toReal with hg
  have hg0 : 0 < g := ENNReal.toReal_pos hγ.ne' hγt
  have hγg : γ = ENNReal.ofReal g := (ENNReal.ofReal_toReal hγt).symm
  have hUd : p.potential a < p.potential (d - p.α) :=
    p.potential_lt_potential h0 h1 (by linarith) (by linarith)
  -- the rest point `(d', 0)` just beyond the cut
  set e₁ := min (g / (2 * ac)) (Hl - p.potential (d - p.α)) with he₁
  have he₁0 : 0 < e₁ := lt_min (by positivity) (by linarith)
  obtain ⟨δ', hδ', hUnear⟩ := Metric.continuousAt_iff.mp
    (p.hasDerivAt_potential (d - p.α)).continuousAt e₁ he₁0
  set d' := min (d + δ' / 2) ((d + (π - a + p.α)) / 2) with hd'
  have hdd' : d < d' := lt_min (by linarith) (by linarith)
  have hd'1 : d' < π - a + p.α := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hd'δ : d' - d < δ' := by have := min_le_left (d + δ' / 2) ((d + (π - a + p.α)) / 2)
                                linarith
  have hUd' : p.potential (d' - p.α) < p.potential (d - p.α) + e₁ := by
    have := hUnear (show dist (d' - p.α) (d - p.α) < δ' by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  set z : Fin 2 → ℝ := ![d', 0] with hz
  have hzE : p.swingEnergy z = p.potential (d' - p.α) := by simp [swingEnergy, hz]
  have he₁l : e₁ ≤ Hl - p.potential (d - p.α) := min_le_right _ _
  have hzW : z ∈ p.energyWell η :=
    ⟨by simp [hz]; linarith, by simp [hz]; linarith, by rw [hzE]; linarith⟩
  have hzout : z ∉ p.cutWell η d := fun h => by
    have := h.2
    simp only [mem_ofPred_eq, hz, Matrix.cons_val_zero] at this
    linarith
  obtain ⟨Ts, w, hw0, hthrough, hrate⟩ := p.exists_drive_to hσ hD h0 h1 hη0 hzW
    (by simp [hz]) (g := g / 2) (by positivity)
  have hxsE : p.swingEnergy xs = p.potential a := by simp [swingEnergy, hxs]
  have hrate' : schilderRate Ts w ≤ ENNReal.ofReal (2 * p.D * (p.potential (d - p.α) -
      p.potential a) / σP ^ 2) + γ := by
    refine hrate.trans ?_
    have e : 2 * p.D * (p.potential (d - p.α) - p.potential a) / σP ^ 2 =
        ac * (p.potential (d - p.α) - p.potential a) := by rw [hac]; ring
    have hV0 : 0 ≤ ac * (p.potential (d - p.α) - p.potential a) :=
      mul_nonneg hac0.le (by linarith)
    rw [hγg, e, ← ENNReal.ofReal_add hV0 hg0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hac, hzE, hxsE]
    have he₁g : e₁ ≤ g / (2 * ac) := min_le_left _ _
    have : ac * (g / (2 * ac)) = g / 2 := by field_simp
    nlinarith
  exact p.exists_horizon_of_escape hD h0 h1 hη0 (p.isCompact_cutWell η d) inter_subset_left hw0
    (hthrough _ hzout) hrate'

/-- **Mean exit time from the cut well, upper bound at the cut point** (two states, `σ_P ≠ 0`,
`D > 0`, `c₀ ≤ P_ref < c₀ + A`, `η > 0`, `δ_s < d < δ_u`, `U(d − α) < U(δ_u − α) − η`): the exit
time `τ_ε` of the noisy model started at `x_s` from `Params.cutWell η d` satisfies
`limsup_{ε→0⁺} ε log E τ_ε ≤ 2D(U(d − α) − U(δ_s − α))/σ_P²`. -/
@[tmio M, powerlib_domain] theorem limsup_log_exitTime_cutWell_le (hσ : σP ≠ 0)
    (hD : 0 < p.D) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ} (hη0 : 0 < η)
    {d : ℝ} (hd0 : Real.arcsin ((p.Pref - p.c0) / p.A) + p.α < d)
    (hd1 : d < π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hdU : p.potential (d - p.α) < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) :
    limsup (fun ε : ℝ => (ε : EReal) * ENNReal.log (∫⁻ ω, exitTime p.swingDrift
        (columnsCLM fun _ : Fin 1 => swingColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] (p.cutWell η d) (√ε) B hBc ω ∂P))
        (𝓝[>] 0) ≤
      ((ENNReal.ofReal (2 * p.D * (p.potential (d - p.α) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) / σP ^ 2) : ℝ≥0∞) : EReal) := by
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  set v := 2 * p.D * (p.potential (d - p.α) - p.potential a) / σP ^ 2 with hv
  have hA := p.A_pos
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hA.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hA).mpr (by linarith)
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hs0
  have ha1 : a < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hUd : p.potential a < p.potential (d - p.α) :=
    p.potential_lt_potential h0 h1 (by linarith) (by linarith)
  have hv0 : 0 ≤ v := by
    have : 0 < σP ^ 2 := by positivity
    have : 0 ≤ p.potential (d - p.α) - p.potential a := by linarith
    positivity
  have hxs : (![a + p.α, 0] : Fin 2 → ℝ) ∈ p.cutWell η d := by
    refine ⟨⟨by simp; linarith [Real.pi_pos], by simp; linarith, ?_⟩, by simp; linarith⟩
    simp [swingEnergy]
    linarith
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb not_lt_bot
  | top => exact le_top
  | coe b =>
    rw [EReal.coe_ennreal_ofReal, max_eq_left hv0, EReal.coe_lt_coe_iff] at hb
    obtain ⟨T, hT, hsup⟩ := p.exists_horizon_iSup_fwRate_cutWell_le hσ hD h0 h1 hη0 hd0 hd1 hdU
      (γ := ENNReal.ofReal (b - v)) (ENNReal.ofReal_pos.mpr (by linarith))
    refine (p.limsup_log_exitTime_le hB hBc (p.isCompact_cutWell η d) hxs hT).trans ?_
    refine (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hsup).trans ?_
    rw [← ENNReal.ofReal_add hv0 (by linarith), add_sub_cancel, EReal.coe_ennreal_ofReal,
      max_eq_left (by linarith)]


end Params

end powerlib.GFM.Noise
