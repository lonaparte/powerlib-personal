import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ExitTimeLyapunov
import theorem.GridTiedConverter.GFM.Noise.FreidlinWentzellLower

/-! # Exit of the noisy three-state GFM from its filter well: the lower bound

Domain module: the noisy three-state GFM (VSM + power filter) with set-point noise
(`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzell.lean`) and the closed well of the
filter-lag function `E(δ, ω, P_f) = M ω²/2 + U(δ − α) + (P_f − P(δ))²/(2A)`
(`Params3.filterEnergy`) below the saddle level, `Params3.filterWell η`. For `A < D ω_c` the
mean exit time from the well started at the stable equilibrium `x_s = (δ_s, 0, P(δ_s))` grows at
least at the Hamilton–Jacobi rate of its level,
`liminf_{ε→0⁺} ε log E τ_ε ≥ 2(D − A/ω_c)(ΔU − η)/σ_P²`, and `τ_ε` exceeds `e^{β/ε}` with
probability `1 − O(e^{−γ/ε})` for every smaller `β`: the two-state chain of
`FreidlinWentzellLower.lean` mirrored through the generic law
`Stochastic.LDP.le_liminf_log_lintegral_exitTime_of_lyapunov`
(`theorem/Stochastic/ExitTimeLyapunov.lean`) with `V = E`, `a = 2(D − A/ω_c)/σ_P²`: the
Hamilton–Jacobi bound `Params3.fwQP_ge`; the level (the well lies in the strip and `E ≥ U`); and
LaSalle's argument for the noiseless flow, along which
`Ė = −[D ω² + (1 + cos(δ − α)) ω y + (ω_c/A) y²]`, `y = P_f − P(δ)`, a positive-definite form
for `A < D ω_c`, so that a state keeping `E` is at rest, hence (the two-state rest argument
`Params.eq_rest_of_swingEnergy_freeSwing_eq` on the angle) the stable equilibrium.

Model boundary.
* The three-state model of `FreidlinWentzell.lean`: state `(δ, ω, P_f)` on `Fin 3 → ℝ`, drift
  `Params3.sdeDrift` (`δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P(δ) − P_f)`), noise
  column `(0, σ_P/M, 0)`; `σ_P ≠ 0`, `D > 0`, `A < D ω_c`, `c₀ ≤ P_ref < c₀ + A`;
  `P(δ) = c₀ + A sin(δ − α)`, `δ_s = arcsin s + α`, `δ_u = π − arcsin s + α`,
  `s = (P_ref − c₀)/A`, `ΔU = U(π − arcsin s) − U(arcsin s)`, `0 < η < ΔU`.
* The well `{δ_u − 2π ≤ δ ≤ δ_u, E ≤ U(π − arcsin s) − η}`: compact; its level is the
  Hamilton–Jacobi value `2(D − A/ω_c)(ΔU − η)/σ_P²` of a subsolution, a lower bound of the
  three-state quasi-potential (`GFM.Noise.Params3.setPointQP_rest_ge`), not the quasi-potential
  itself; the bound tends to `2(D − A/ω_c)ΔU/σ_P²` as `η → 0⁺`, below the two-state value
  `2DΔU/σ_P²`. The exit time is `Stochastic.LDP.exitTime` of the well for a Brownian motion all
  of whose paths are continuous, `E τ_ε` its lower Lebesgue integral.
* Not formalized: a matching upper bound (the three-state sup–inf is only bounded by
  `GFM.Noise.Params3.limsup_log_exitTime_le`), the exit from the basin of attraction, the exit
  place, the band `D ω_c ≤ A` (the form is then indefinite near `δ = α`).

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §2 (Thm 4.2.1, lower bound for the exit time) and §3 (subsolutions of the Hamilton–Jacobi
equation bound the quasi-potential); J. P. LaSalle, *The Stability of Dynamical Systems* (1976);
the three-state Hamilton–Jacobi certificate
`theorem/GridTiedConverter/GFM/Noise/FilterQuasiPotential.lean`.

Results.
* `Params3.filterWell`, `Params3.isCompact_filterWell`, `Params3.continuous_filterEnergy`,
  `Params3.potential_le_filterEnergy`.
* The noiseless flow `Params3.freeFilter`: `Params3.filterEnergyDeriv_drift` (the dissipation
  form), `Params3.hasDerivAt_filterEnergy_freeFilter`, `Params3.filterEnergy_freeFilter_le`,
  `Params3.eq_rest_of_filterEnergy_freeFilter_eq` (**a state of the well keeping `E` over `[0, 1]`
  is `x_s`**), `Params3.exists_filterEnergy_freeFilter_drop` (**uniform loss away from `x_s`**).
* `Params3.le_liminf_log_exitTime_filterWell`
  (**`liminf ε log E τ_ε ≥ 2(D − A/ω_c)(ΔU − η)/σ_P²`**),
  `Params3.eventually_measure_exitTime_filterWell_le` (**`P(τ_ε ≤ e^{β/ε}) ≤ e^{−γ/ε}`** below
  that value).
-/

noncomputable section
namespace powerlib.GFM.Noise

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal NNReal
open powerlib.Stochastic.LDP

namespace Params3

variable (p : Params3)

/-- The closed filter well of the noisy three-state model below the saddle level, cut at
`U(δ_u − α) − η`: `δ_u − 2π ≤ δ ≤ δ_u`, `E(δ, ω, P_f) ≤ U(δ_u − α) − η`. -/
def filterWell (η : ℝ) : Set (Fin 3 → ℝ) :=
  {x | π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α - 2 * π ≤ x 0 ∧
    x 0 ≤ π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α ∧
    p.filterEnergy x ≤ p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η}

/-- The noiseless solution of the three-state model from `y` on `[0, T]` (driving path `0`). -/
def freeFilter (σP : ℝ) (y : Fin 3 → ℝ) (T : ℝ≥0) : C(Icc (0 : ℝ) T, Fin 3 → ℝ) :=
  solMap p.sdeDrift (columnsCLM fun _ : Fin 1 => p.setPointColumn σP) y 0

@[tmio M, powerlib_domain] theorem continuous_filterEnergy : Continuous p.filterEnergy :=
  continuous_iff_continuousAt.2 fun x => (p.hasFDerivAt_filterEnergy x).continuousAt

/-- `U(δ − α) ≤ E(δ, ω, P_f)`. -/
@[tmio M, powerlib_domain] theorem potential_le_filterEnergy (x : Fin 3 → ℝ) :
    p.potential (x 0 - p.α) ≤ p.filterEnergy x := by
  have hM := p.M_pos
  have hA := p.A_pos
  unfold filterEnergy
  have h1 : 0 ≤ p.M * x 1 ^ 2 / 2 := by positivity
  have h2 : 0 ≤ (x 2 - p.toLossy.Pe (x 0)) ^ 2 / (2 * p.A) := by positivity
  linarith

/-- **The dissipation of `E` along the drift**:
`E'(x) b(x) = −[D ω² + (1 + cos(δ − α)) ω y + (ω_c/A) y²]`, `y = P_f − P(δ)`. -/
@[tmio M, powerlib_domain] theorem filterEnergyDeriv_drift (x : Fin 3 → ℝ) :
    p.filterEnergyDeriv x (p.sdeDrift x) = -(p.D * x 1 ^ 2 +
      (1 + Real.cos (x 0 - p.α)) * x 1 * (x 2 - p.toLossy.Pe (x 0)) +
        p.ωc / p.A * (x 2 - p.toLossy.Pe (x 0)) ^ 2) := by
  have hM := p.M_pos.ne'
  have hA := p.A_pos.ne'
  simp [filterEnergyDeriv, sdeDrift_apply, Params.potentialDeriv, Params.toSM,
    VSMLPFLossy.Pe, toLossy]
  field_simp
  ring

/-- The dissipation form is positive definite for `A < D ω_c`: it vanishes only at
`ω = y = 0`. -/
@[tmio T, powerlib_foundation] private theorem dissipation_form {D a w y cs : ℝ} (hD : 0 < D)
    (hDa : 1 < D * a) (hcs : |cs| ≤ 1) :
    0 ≤ D * w ^ 2 + (1 + cs) * w * y + a * y ^ 2 ∧
      (D * w ^ 2 + (1 + cs) * w * y + a * y ^ 2 = 0 → w = 0 ∧ y = 0) := by
  have hc := abs_le.mp hcs
  have hk : 0 < a - (1 + cs) ^ 2 / (4 * D) := by
    have h1 : (1 + cs) ^ 2 ≤ 4 := by nlinarith
    have h2 : (1 + cs) ^ 2 / (4 * D) ≤ 4 / (4 * D) := by gcongr
    have h3 : 4 / (4 * D) < a := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have e : D * w ^ 2 + (1 + cs) * w * y + a * y ^ 2 =
      D * (w + (1 + cs) / (2 * D) * y) ^ 2 + (a - (1 + cs) ^ 2 / (4 * D)) * y ^ 2 := by
    field_simp; ring
  rw [e]
  refine ⟨by positivity, fun h => ?_⟩
  have h1 : 0 ≤ D * (w + (1 + cs) / (2 * D) * y) ^ 2 := by positivity
  have h2 : 0 ≤ (a - (1 + cs) ^ 2 / (4 * D)) * y ^ 2 := by positivity
  have hy : y ^ 2 = 0 := by
    have : (a - (1 + cs) ^ 2 / (4 * D)) * y ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hk.ne'
    · exact h
  have hy0 : y = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hy
  subst hy0
  have : D * w ^ 2 = 0 := by simpa using h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hD.ne'
  · exact ⟨pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h', rfl⟩

variable {σP : ℝ}

/-- The energy derivative along the noiseless solution is minus the dissipation form. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_filterEnergy_freeFilter (y : Fin 3 → ℝ)
    {T : ℝ≥0} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => p.filterEnergy (pathExt (p.freeFilter σP y T) s))
      (-(p.D * pathExt (p.freeFilter σP y T) t 1 ^ 2 +
        (1 + Real.cos (pathExt (p.freeFilter σP y T) t 0 - p.α)) *
          pathExt (p.freeFilter σP y T) t 1 *
          (pathExt (p.freeFilter σP y T) t 2 - p.toLossy.Pe (pathExt (p.freeFilter σP y T) t 0)) +
        p.ωc / p.A * (pathExt (p.freeFilter σP y T) t 2 -
          p.toLossy.Pe (pathExt (p.freeFilter σP y T) t 0)) ^ 2)) t := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  have h := (p.hasFDerivAt_filterEnergy _).comp_hasDerivAt t
    (hasDerivAt_solMap_zero hK (columnsCLM fun _ : Fin 1 => p.setPointColumn σP) y ht)
  rw [filterEnergyDeriv_drift] at h
  exact h

/-- **The energy does not increase along the noiseless solution** (`D > 0`, `A < D ω_c`). -/
@[tmio M, powerlib_domain] theorem filterEnergy_freeFilter_le (hD : 0 < p.D)
    (hA : p.A < p.D * p.ωc) (y : Fin 3 → ℝ) (T : ℝ≥0) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (ht : t ∈ Icc (0 : ℝ) T) (hst : s ≤ t) :
    p.filterEnergy (pathExt (p.freeFilter σP y T) t) ≤
      p.filterEnergy (pathExt (p.freeFilter σP y T) s) := by
  have hω := p.ωc_pos
  have hAp := p.A_pos
  have hDa : 1 < p.D * (p.ωc / p.A) := by
    rw [mul_div_assoc', lt_div_iff₀ hAp]; linarith
  have hanti : AntitoneOn (fun s => p.filterEnergy (pathExt (p.freeFilter σP y T) s))
      (Icc (0 : ℝ) T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) (T : ℝ))
      ((p.continuous_filterEnergy.comp (continuous_pathExt _)).continuousOn)
      (fun r hr => ?_) (fun r hr => ?_)
    · rw [interior_Icc] at hr
      exact (p.hasDerivAt_filterEnergy_freeFilter (σP := σP) y hr).differentiableAt
        |>.differentiableWithinAt
    · rw [interior_Icc] at hr
      rw [(p.hasDerivAt_filterEnergy_freeFilter (σP := σP) y hr).deriv]
      have := (dissipation_form (w := pathExt (p.freeFilter σP y T) r 1)
        (y := pathExt (p.freeFilter σP y T) r 2 -
          p.toLossy.Pe (pathExt (p.freeFilter σP y T) r 0)) hD hDa
        (abs_cos_le_one (pathExt (p.freeFilter σP y T) r 0 - p.α))).1
      exact neg_nonpos.mpr this
  exact hanti hs ht hst

/-- **A state of the well keeping its energy over `[0, 1]` is the stable equilibrium**
(`D > 0`, `A < D ω_c`, `c₀ ≤ P_ref < c₀ + A`): the frequency and the filter lag vanish on
`(0, 1)` (positive-definite dissipation), so the state is at rest, `P(δ) = P_ref`, and the
two-state rest argument (`Params.eq_rest_of_swingEnergy_freeSwing_eq` at `(δ, 0)`) fixes
`δ = δ_s`. -/
@[tmio M, powerlib_domain] theorem eq_rest_of_filterEnergy_freeFilter_eq (hD : 0 < p.D)
    (hA : p.A < p.D * p.ωc) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ}
    (hη : 0 < η) {y : Fin 3 → ℝ} (hy : y ∈ p.filterWell η)
    (heq : p.filterEnergy (pathExt (p.freeFilter σP y 1) 1) = p.filterEnergy y) :
    y = ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0,
      p.toLossy.Pe (Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)] := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  set N := columnsCLM fun _ : Fin 1 => p.setPointColumn σP with hN
  set φ := p.freeFilter σP y 1 with hφ
  have hM := p.M_pos
  have hω := p.ωc_pos
  have hAp := p.A_pos
  have hDa : 1 < p.D * (p.ωc / p.A) := by
    rw [mul_div_assoc', lt_div_iff₀ hAp]; linarith
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ) := by simp
  have hφ0 : pathExt φ 0 = y := pathExt_solMap_zero hK N y 1
  have hconst : ∀ s ∈ Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ),
      p.filterEnergy (pathExt φ s) = p.filterEnergy y := by
    intro s hs
    have ha := p.filterEnergy_freeFilter_le (σP := σP) hD hA y 1 hs h1mem
      (by simpa using hs.2)
    have hb := p.filterEnergy_freeFilter_le (σP := σP) hD hA y 1 ⟨le_rfl, zero_le_one⟩ hs hs.1
    rw [← hφ] at ha hb
    rw [hφ0] at hb
    rw [heq] at ha
    linarith
  -- frequency and lag vanish inside `(0, 1)`
  have hrest : ∀ s ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ),
      pathExt φ s 1 = 0 ∧ pathExt φ s 2 - p.toLossy.Pe (pathExt φ s 0) = 0 := by
    intro s hs
    have hd := p.hasDerivAt_filterEnergy_freeFilter (σP := σP) y hs
    have hc : HasDerivAt (fun r => p.filterEnergy (pathExt φ r)) 0 s := by
      refine (hasDerivAt_const s (p.filterEnergy y)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
      exact hconst r ⟨hr.1.le, hr.2.le⟩
    have h := hd.unique hc
    exact (dissipation_form hD hDa (abs_cos_le_one _)).2 (neg_eq_zero.mp h)
  have hcomp : ∀ s ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ), ∀ i,
      HasDerivAt (fun r => pathExt φ r i) (p.sdeDrift (pathExt φ s) i) s :=
    fun s hs => hasDerivAt_pi.mp (hasDerivAt_solMap_zero hK N y hs)
  have hd1 : ∀ s ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ), p.sdeDrift (pathExt φ s) 1 = 0 := by
    intro s hs
    have hc : HasDerivAt (fun r => pathExt φ r 1) 0 s := by
      refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
      exact (hrest r hr).1
    exact (hcomp s hs 1).unique hc
  have hPf : ∀ s ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ), pathExt φ s 2 = p.Pref := by
    intro s hs
    have h := hd1 s hs
    rw [sdeDrift_apply] at h
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
    rw [(hrest s hs).1, div_eq_zero_iff, or_iff_left hM.ne'] at h
    linarith
  have hsub : ∀ r ∈ Ioo (0 : ℝ) (1 / 2), r ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ) :=
    fun r hr => ⟨hr.1, by push_cast; linarith [hr.2]⟩
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) ((1 : ℝ≥0) : ℝ) := ⟨by norm_num, by norm_num⟩
  have hcont : ∀ i, ContinuousOn (fun r => pathExt φ r i) (Icc 0 (1 / 2)) := fun i =>
    ((continuous_apply i).comp (continuous_pathExt φ)).continuousOn
  have hmvt : ∀ i, (∀ c ∈ Ioo (0 : ℝ) (1 / 2), p.sdeDrift (pathExt φ c) i = 0) →
      pathExt φ (1 / 2) i = y i := by
    intro i hi
    obtain ⟨c, hc, hcv⟩ := exists_hasDerivAt_eq_slope (fun r => pathExt φ r i)
      (fun r => p.sdeDrift (pathExt φ r) i) (by norm_num : (0 : ℝ) < 1 / 2) (hcont i)
      (fun r hr => hcomp r (hsub r hr) i)
    rw [hi c hc, hφ0] at hcv
    have h2 : (pathExt φ (1 / 2) i - y i) / (1 / 2 - 0) = 0 := hcv.symm
    rw [div_eq_zero_iff, or_iff_left (by norm_num)] at h2
    linarith
  have hδ : pathExt φ (1 / 2) 0 = y 0 := hmvt 0 fun c hc => by
    rw [sdeDrift_apply]; simpa using (hrest c (hsub c hc)).1
  have hq : y 1 = 0 := by
    rw [← hmvt 1 fun c hc => hd1 c (hsub c hc)]; exact (hrest _ hhalf).1
  have hy2 : y 2 = p.Pref := by
    rw [← hmvt 2 fun c hc => ?_]
    · exact hPf _ hhalf
    rw [sdeDrift_apply]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    have := (hrest c (hsub c hc)).2
    rw [show p.toLossy.Pe (pathExt φ c 0) - pathExt φ c 2 = 0 by linarith, mul_zero]
  have hPe : p.toLossy.Pe (y 0) = p.Pref := by
    have := (hrest _ hhalf).2
    rw [hPf _ hhalf, hδ] at this
    linarith
  -- the angle: the two-state rest argument at `(δ, 0)`
  obtain ⟨K₂, hK₂⟩ := p.lipschitzWith_swingDrift
  set z : Fin 2 → ℝ := ![y 0, 0] with hz
  have hzW : z ∈ p.energyWell η := by
    refine ⟨by simpa [hz] using hy.1, by simpa [hz] using hy.2.1, ?_⟩
    have h1' := p.potential_le_filterEnergy y
    have h2 : p.swingEnergy z = p.potential (y 0 - p.α) := by simp [Params.swingEnergy, hz]
    rw [h2]
    exact h1'.trans hy.2.2
  have hzrest : p.swingDrift z = 0 := by
    rw [Params.swingDrift_apply]
    have : p.c0 + p.A * Real.sin (y 0 - p.α) = p.Pref := by
      simpa [VSMLPFLossy.Pe, toLossy] using hPe
    ext i; fin_cases i <;> simp [hz, this]
  have hfree : p.freeSwing σP z 1 = ContinuousMap.const _ z := by
    have h := eq_solMap_of_hasDerivAt hK₂ (columnsCLM fun _ : Fin 1 => Params.swingColumn σP)
      (ψ := ContinuousMap.const (Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ)) z) (u := fun _ => 0)
      continuous_const (W := 0) (fun t => by simp only [intervalIntegral.integral_zero]; rfl)
      (fun s _ => by
        have e : pathExt (ContinuousMap.const (Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ)) z) = fun _ => z := by
          funext r; rfl
        rw [e, hzrest]
        simpa using hasDerivAt_const s z)
    have e0 : pathExt (ContinuousMap.const (Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ)) z) 0 = z := rfl
    rw [e0] at h
    exact h.symm
  have hzeq : p.swingEnergy (pathExt (p.freeSwing σP z 1) 1) = p.swingEnergy z := by
    rw [hfree]; rfl
  have hz0 := p.eq_rest_of_swingEnergy_freeSwing_eq hD h0 h1 hη hzW hzeq
  have hy0 : y 0 = Real.arcsin ((p.Pref - p.c0) / p.A) + p.α := by
    have := congrFun hz0 0
    simpa [hz] using this
  ext i; fin_cases i
  · simpa using hy0
  · simpa using hq
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [hy2, ← hy0, hPe]

/-- The well is compact. -/
@[tmio M, powerlib_domain] theorem isCompact_filterWell (η : ℝ) :
    IsCompact (p.filterWell η) := by
  set a := Real.arcsin ((p.Pref - p.c0) / p.A) with ha
  have hM := p.M_pos
  have hA := p.A_pos
  have hclosed : IsClosed (p.filterWell η) := by
    have e : p.filterWell η = {x : Fin 3 → ℝ | π - a + p.α - 2 * π ≤ x 0} ∩
        ({x | x 0 ≤ π - a + p.α} ∩ {x | p.filterEnergy x ≤ p.potential (π - a) - η}) := by
      ext x; simp [filterWell, ha]
    rw [e]
    exact (isClosed_le continuous_const (continuous_apply 0)).inter
      ((isClosed_le (continuous_apply 0) continuous_const).inter
        (isClosed_le p.continuous_filterEnergy continuous_const))
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  set C := p.potential (π - a) - η + |p.Pref - p.c0| * (|π - a + p.α| + 2 * π + |p.α|) + p.A
    with hC
  set R := |p.c0| + p.A + 1 + 2 * p.A * C with hR
  refine (Metric.isBounded_Icc (![π - a + p.α - 2 * π, -(1 + 2 * C / p.M), -R] : Fin 3 → ℝ)
    ![π - a + p.α, 1 + 2 * C / p.M, R]).subset fun x hx => ?_
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hθ : |x 0 - p.α| ≤ |π - a + p.α| + 2 * π + |p.α| := by
    rw [abs_le]
    constructor <;> cases abs_cases (π - a + p.α) <;> cases abs_cases p.α <;>
      nlinarith [Real.pi_pos]
  have hU : -p.potential (x 0 - p.α) ≤ |p.Pref - p.c0| * (|π - a + p.α| + 2 * π + |p.α|) + p.A :=
    by
    simp only [Params.potential, Params.toSM]
    have h1 := Real.neg_one_le_cos (x 0 - p.α)
    have h2 := Real.cos_le_one (x 0 - p.α)
    have h3 : (p.Pref - p.c0) * (x 0 - p.α) ≤ |p.Pref - p.c0| * |x 0 - p.α| := by
      rw [← abs_mul]; exact le_abs_self _
    have h4 : |p.Pref - p.c0| * |x 0 - p.α| ≤
        |p.Pref - p.c0| * (|π - a + p.α| + 2 * π + |p.α|) :=
      mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
    nlinarith
  have hrest : p.M * x 1 ^ 2 / 2 + (x 2 - p.toLossy.Pe (x 0)) ^ 2 / (2 * p.A) ≤ C := by
    unfold filterEnergy at hx3
    linarith
  have hk1 : 0 ≤ p.M * x 1 ^ 2 / 2 := by positivity
  have hk2 : 0 ≤ (x 2 - p.toLossy.Pe (x 0)) ^ 2 / (2 * p.A) := by positivity
  have hkin : x 1 ^ 2 ≤ 2 * C / p.M := by
    rw [le_div_iff₀ hM]; nlinarith
  have hlag : (x 2 - p.toLossy.Pe (x 0)) ^ 2 ≤ 2 * p.A * C := by
    have : (x 2 - p.toLossy.Pe (x 0)) ^ 2 / (2 * p.A) ≤ C := by linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hPe : |p.toLossy.Pe (x 0)| ≤ |p.c0| + p.A := by
    simp only [VSMLPFLossy.Pe, toLossy]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_of_pos hA]
    exact mul_le_of_le_one_right hA.le (abs_sin_le_one _)
  have hPe' := abs_le.mp hPe
  constructor
  · intro i; fin_cases i
    · simpa using hx1
    · simp; nlinarith [sq_nonneg (x 1 + 1)]
    · simp; nlinarith [sq_nonneg (x 2 - p.toLossy.Pe (x 0) + 1)]
  · intro i; fin_cases i
    · simpa using hx2
    · simp; nlinarith [sq_nonneg (x 1 - 1)]
    · simp; nlinarith [sq_nonneg (x 2 - p.toLossy.Pe (x 0) - 1)]

/-- **Uniform energy loss away from `x_s`** (`D > 0`, `A < D ω_c`, `c₀ ≤ P_ref < c₀ + A`,
`η > 0`): for `r > 0` there is `c > 0` such that every state of the well at distance `≥ r` from
`x_s` loses at least `c` of `E` along the noiseless flow over `[0, 1]`. -/
@[tmio M, powerlib_domain] theorem exists_filterEnergy_freeFilter_drop (hD : 0 < p.D)
    (hA : p.A < p.D * p.ωc) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ}
    (hη : 0 < η) {r : ℝ} (hr : 0 < r) :
    ∃ c > 0, ∀ y ∈ p.filterWell η, r ≤ dist y ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0,
        p.toLossy.Pe (Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)] →
      p.filterEnergy (pathExt (p.freeFilter σP y 1) 1) ≤ p.filterEnergy y - c := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  set xs : Fin 3 → ℝ := ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0,
    p.toLossy.Pe (Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)] with hxs
  have hCc : IsCompact (p.filterWell η ∩ {y | r ≤ dist y xs}) :=
    (p.isCompact_filterWell η).inter_right (isClosed_le continuous_const
      (continuous_id.dist continuous_const))
  obtain ⟨c, hc, h⟩ := exists_drop_of_lt hK (columnsCLM fun _ : Fin 1 => p.setPointColumn σP)
    hCc p.continuous_filterEnergy (fun y hy => by
      refine lt_of_le_of_ne (p.filterEnergy_freeFilter_le (σP := σP) hD hA y 1
        ⟨le_rfl, zero_le_one⟩ (by simp) zero_le_one |>.trans_eq ?_) fun heq => ?_
      · rw [freeFilter, pathExt_solMap_zero hK]
      · have hrest := p.eq_rest_of_filterEnergy_freeFilter_eq (σP := σP) hD hA h0 h1 hη hy.1 heq
        have := hy.2
        simp only [mem_ofPred_eq] at this
        rw [hrest, dist_self] at this
        linarith)
  exact ⟨c, hc, fun y hy hry => h y ⟨hy, hry⟩⟩

/-- The data of the filter well at `x_s`: it lies in the well, below its level, the rate factor
`2(D − A/ω_c)/σ_P²` is positive, and the level value is `2(D − A/ω_c)(ΔU − η)/σ_P²`. -/
@[tmio M, powerlib_domain] private theorem filterWell_data (hσ : σP ≠ 0)
    (hA : p.A < p.D * p.ωc) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {η : ℝ}
    (hη1 : η < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) :
    ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0,
        p.toLossy.Pe (Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)] ∈ p.filterWell η ∧
      p.filterEnergy ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0,
        p.toLossy.Pe (Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)] <
        p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) - η ∧
      0 < 2 * (p.D - p.A / p.ωc) / σP ^ 2 ∧
      p.filterEnergy ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0,
        p.toLossy.Pe (Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)] =
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) := by
  set as := Real.arcsin ((p.Pref - p.c0) / p.A) with has
  have hAp := p.A_pos
  have hω := p.ωc_pos
  have hs0 : 0 ≤ (p.Pref - p.c0) / p.A := div_nonneg (by linarith) hAp.le
  have hs1 : (p.Pref - p.c0) / p.A < 1 := (div_lt_one hAp).mpr (by linarith)
  have has0 : 0 ≤ as := Real.arcsin_nonneg.mpr hs0
  have has1 : as < π / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hxsE : p.filterEnergy ![as + p.α, 0, p.toLossy.Pe (as + p.α)] = p.potential as := by
    simp [filterEnergy]
  have hσ2 : 0 < σP ^ 2 := by positivity
  have hDA : 0 < p.D - p.A / p.ωc := by
    have : p.A / p.ωc < p.D := (div_lt_iff₀ hω).mpr hA
    linarith
  refine ⟨⟨by simp; linarith [Real.pi_pos], by simp; linarith, by rw [hxsE]; linarith⟩,
    by rw [hxsE]; linarith, by positivity, hxsE⟩

/-- **Lower bound for the mean exit time from the filter well** (three states, `σ_P ≠ 0`,
`D > 0`, `A < D ω_c`, `c₀ ≤ P_ref < c₀ + A`, `0 < η < ΔU`): the exit time `τ_ε` of the noisy
model started at `x_s` from `Params3.filterWell η` satisfies
`liminf_{ε→0⁺} ε log E τ_ε ≥ 2(D − A/ω_c)(ΔU − η)/σ_P²`. -/
@[tmio M, powerlib_domain] theorem le_liminf_log_exitTime_filterWell (hσ : σP ≠ 0)
    (hD : 0 < p.D) (hA : p.A < p.D * p.ωc) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A)
    {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous fun t => B t ω) :
    (((2 * (p.D - p.A / p.ωc) * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) / σP ^ 2 : ℝ)) : EReal) ≤
      liminf (fun ε : ℝ => (ε : EReal) * ENNReal.log (∫⁻ ω, exitTime p.sdeDrift
        (columnsCLM fun _ : Fin 1 => p.setPointColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0,
          p.toLossy.Pe (Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)] (p.filterWell η) (√ε) B
          hBc ω ∂P)) (𝓝[>] 0) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  obtain ⟨hxsW, hlt, ha0, hxsE⟩ := p.filterWell_data hσ hA h0 h1 hη1
  have hgen := le_liminf_log_lintegral_exitTime_of_lyapunov hB hBc (p.isCompact_filterWell η)
    hxsW hK (columnsCLM fun _ : Fin 1 => p.setPointColumn σP) p.continuous_filterEnergy ha0 hlt
    (fun y x => p.fwQP_ge hσ hA.le y x)
    (fun y hy φ hφ hφ0 => p.exists_level_of_mem_closure_leave h0 (n := 2)
      p.continuous_filterEnergy p.potential_le_filterEnergy (by linarith) hy hφ hφ0)
    (fun r hr => p.exists_filterEnergy_freeFilter_drop (σP := σP) hD hA h0 h1 hη0 hr)
  rw [hxsE] at hgen
  convert hgen using 2
  ring

/-- **The exit time from the filter well is exponentially large in probability** (three states,
same hypotheses): for every `β < 2(D − A/ω_c)(ΔU − η)/σ_P²` there is `γ > 0` with
`P(τ_ε ≤ e^{β/ε}) ≤ e^{−γ/ε}` for all small `ε`. -/
@[tmio M, powerlib_domain] theorem eventually_measure_exitTime_filterWell_le (hσ : σP ≠ 0)
    (hD : 0 < p.D) (hA : p.A < p.D * p.ωc) (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A)
    {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
      p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous fun t => B t ω) {β : ℝ}
    (hβ : β < 2 * (p.D - p.A / p.ωc) * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A)) - η) / σP ^ 2) :
    ∃ γ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | exitTime p.sdeDrift
        (columnsCLM fun _ : Fin 1 => p.setPointColumn σP)
        ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0,
          p.toLossy.Pe (Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)] (p.filterWell η) (√ε) B
          hBc ω ≤ ENNReal.ofReal (Real.exp (β / ε))} ≤ ENNReal.ofReal (Real.exp (-γ / ε)) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  obtain ⟨hxsW, hlt, ha0, hxsE⟩ := p.filterWell_data hσ hA h0 h1 hη1
  refine eventually_measure_exitTime_le_of_lyapunov hB hBc (p.isCompact_filterWell η) hxsW hK
    (columnsCLM fun _ : Fin 1 => p.setPointColumn σP) p.continuous_filterEnergy ha0 hlt
    (fun y x => p.fwQP_ge hσ hA.le y x)
    (fun y hy φ hφ hφ0 => p.exists_level_of_mem_closure_leave h0 (n := 2)
      p.continuous_filterEnergy p.potential_le_filterEnergy (by linarith) hy hφ hφ0)
    (fun r hr => p.exists_filterEnergy_freeFilter_drop (σP := σP) hD hA h0 h1 hη0 hr) ?_
  rw [hxsE]
  convert hβ using 1
  ring

end Params3

end powerlib.GFM.Noise
