import theorem.GridTiedConverter.GFM.VoltageModulationPortVariants

/-! # Every GFM model under the VI and PQV port disturbances

`VoltageModulationPortVariants` proves the end-to-end Floquet statements of every GFM model of the
library for a disturbance of any chart `Φ`. Here the chart is the VI chart of a port `pt`
(grid-voltage magnitude and angle, injected-current magnitude and angle;
`PortDisturbance.Port.linCV_polarAbs`) or the PQV chart of a port `pq` (grid-voltage magnitude and
angle, injected active and reactive power; `PortDisturbance.PQVPort.linCV_polarAbs`), with the
absolute Thevenin magnitude `Φ = thPolarAbs e_th V₀`; the amplitudes are `V̂ = V₀ v̂_eff` and
`θ̂ = θ̂_eff`, and on a lossless grid `P̂` drives the angle and `Q̂` the magnitude
(`PortDisturbance.PQVPort.eff_PQ_lossless`).

Model boundary.
* The models, operating points, Hopf conditions and modal data of `VoltageModulationPortVariants`;
  the port Thevenin magnitude `V₀` equals the operating voltage of the model and `e_th(0) = V₀ > 0`;
  the PQV source is the injected current at the reference voltage (`PQVPort.power_jinj`,
  `U₀ ≠ 0`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1–§2.2; the port
disturbances are new.

Results.
* `Droop.orbit_droop_port_stable`, `Droop.orbit_droop_port_unstable`,
  `Droop.orbit_droop_port_exp_stable`, `Droop.orbit_droop_pqv_stable`,
  `Droop.orbit_droop_pqv_unstable`, `Droop.orbit_droop_pqv_exp_stable` — the droop core with two
  filters.
* `DVOCCore.orbit_dvoc_port_stable`, `DVOCCore.orbit_dvoc_port_unstable`,
  `DVOCCore.orbit_dvoc_port_exp_stable`, `DVOCCore.orbit_dvoc_pqv_stable`,
  `DVOCCore.orbit_dvoc_pqv_unstable`, `DVOCCore.orbit_dvoc_pqv_exp_stable` — the dVOC core.
* `PSCFull.Model.orbit_psc_port_stable`, `PSCFull.Model.orbit_psc_port_unstable`,
  `PSCFull.Model.orbit_psc_port_exp_stable`, `PSCFull.Model.orbit_psc_pqv_stable`,
  `PSCFull.Model.orbit_psc_pqv_unstable`, `PSCFull.Model.orbit_psc_pqv_exp_stable` — the PSC with
  active damping.
* `MatchingCore.orbit_matching_port_stable`, `MatchingCore.orbit_matching_port_unstable`,
  `MatchingCore.orbit_matching_port_exp_stable`, `MatchingCore.orbit_matching_pqv_stable`,
  `MatchingCore.orbit_matching_pqv_unstable`, `MatchingCore.orbit_matching_pqv_exp_stable` —
  matching control.
* `DynQV.orbit_qv_port_stable`, `DynQV.orbit_qv_port_unstable`, `DynQV.orbit_qv_port_exp_stable`,
  `DynQV.orbit_qv_pqv_stable`, `DynQV.orbit_qv_pqv_unstable`, `DynQV.orbit_qv_pqv_exp_stable` — the
  dynamic Q–V loop.
* `DynQV.orbit_qvf_port_stable`, `DynQV.orbit_qvf_port_unstable`, `DynQV.orbit_qvf_port_exp_stable`,
  `DynQV.orbit_qvf_pqv_stable`, `DynQV.orbit_qvf_pqv_unstable`, `DynQV.orbit_qvf_pqv_exp_stable` —
  the filtered dynamic Q–V loop.
* `DynQV.orbit_net_port_stable`, `DynQV.orbit_net_port_unstable`, `DynQV.orbit_net_port_exp_stable`,
  `DynQV.orbit_net_pqv_stable`, `DynQV.orbit_net_pqv_unstable`, `DynQV.orbit_net_pqv_exp_stable` —
  the dynamic network model in a fixed frame.

Corrections.
None: an extension.

Family and connection conclusions.
* The generic VI and PQV theorems are `ParametricResonance.PortDisturbanceVIPQV`; the synchronizing
  core is `VoltageModulationPort`, the GFL converter `GFL.Parametric.PortModulation`.
-/

noncomputable section

/-! ### Droop with two filters -/

namespace powerlib.GFM.VoltageModulation.Droop
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam)
open Core (Pd)
open powerlib.GFM.PortVariants (e3)
open powerlib.ParametricResonance.PortDisturbance (Port PQVPort thPolarAbs thPolarAbs_zero
  contDiffAt_thPolarAbs)
variable (mp ω1 ωm : ℝ)

/-- The droop core with two filters under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port
`pt` (grid-voltage and injected-current magnitude and angle), end-to-end, stability (all Floquet
multipliers inside the unit circle): `orbit_droop_chart_stable` with the Thevenin amplitudes `V̂ =
V₀ v̂_eff`, `θ̂ = θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_droop_port_stable
    {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P) {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (pt : Port) (hpV : pt.V0 = V0)
    (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (dG mp ω1 ωm P δ0 V0)
        (dxeq P δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ
        PδV Ω)).re < 0)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ ((DxC (smDx (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0))
        z + (pt.V0 * pt.effV w) • (smM1 (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (dright mp ω1 ωm Pδ PV Pδδ PδV Ω)) / 2‖ ^ 2 < ‖dleft mp ω1 ωm Pδ
        PV Pδδ PδV Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
            (thPolarAbs pt.eth pt.V0)
          ((dxeq P δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
            (thPolarAbs pt.eth pt.V0)
          ((dxeq P δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 3 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor
            (dG mp ω1 ωm P δ0 V0) e3) (thPolarAbs pt.eth pt.V0)) (dxeq P δ0 V0, 0) w (2 * Ω) A0' ε
                t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_droop_chart_stable (hP := hP) (hΩ := hΩ) (hmp := hmp) (hω1 := hω1) (hd2 := hd2)
      (hPδ0 := hPδ0) (hV0 := hpV ▸ hV.ne') (hH1 := hH1) (hH2 := hH2) (hPδ := hPδ) (hPV := hPV)
      (hPδδ := hPδδ) (hPδV := hPδV) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The droop core with two filters under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port
`pt` (grid-voltage and injected-current magnitude and angle), end-to-end, parametric instability:
`orbit_droop_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_droop_port_unstable
    {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P) {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (pt : Port) (hpV : pt.V0 = V0)
    (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (dG mp ω1 ωm P δ0 V0)
        (dxeq P δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ
        PδV Ω)‖ ^ 2 < ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ ((DxC
        (smDx (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)) z + (pt.V0 * pt.effV w) •
        (smM1 (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star
        (dright mp ω1 ωm Pδ PV Pδδ PδV Ω)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
            (thPolarAbs pt.eth pt.V0)
          ((dxeq P δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
            (thPolarAbs pt.eth pt.V0)
          ((dxeq P δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (dG mp ω1 ωm P δ0 V0) e3) (thPolarAbs pt.eth pt.V0)) (dxeq P δ0 V0, 0) w (2 * Ω) A0' ε t
              (y t))
          (2 * Real.pi / (2 * Ω)) :=
  orbit_droop_chart_unstable (hP := hP) (hΩ := hΩ) (hmp := hmp) (hω1 := hω1) (hd2 := hd2)
      (hPδ0 := hPδ0) (hV0 := hpV ▸ hV.ne') (hH1 := hH1) (hH2 := hH2) (hPδ := hPδ) (hPV := hPV)
      (hPδδ := hPδδ) (hPδV := hPδV) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The droop core with two filters under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port
`pt` (grid-voltage and injected-current magnitude and angle), end-to-end, local exponential orbital
stability: `orbit_droop_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ =
θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_droop_port_exp_stable
    {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P) {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (pt : Port) (hpV : pt.V0 = V0)
    (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (dG mp ω1 ωm P δ0 V0)
        (dxeq P δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ
        PδV Ω)).re < 0)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ ((DxC (smDx (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0))
        z + (pt.V0 * pt.effV w) • (smM1 (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (dright mp ω1 ωm Pδ PV Pδδ PδV Ω)) / 2‖ ^ 2 < ‖dleft mp ω1 ωm Pδ
        PV Pδδ PδV Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
          (thPolarAbs pt.eth pt.V0) ((dxeq P δ0
          V0, (0 : Fin 4 → ℝ)).1 + y t,
        (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
            (thPolarAbs pt.eth pt.V0)
            ((dxeq P δ0 V0, (0 : Fin 4 → ℝ)).1 + a,
          (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_droop_chart_exp_stable (hP := hP) (hΩ := hΩ) (hmp := hmp) (hω1 := hω1) (hd2 := hd2)
      (hPδ0 := hPδ0) (hV0 := hpV ▸ hV.ne') (hH1 := hH1) (hH2 := hH2) (hPδ := hPδ) (hPV := hPV)
      (hPδδ := hPδδ) (hPδV := hPδV) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The droop core with two filters under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port
`pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end, stability
(all Floquet multipliers inside the unit circle): `orbit_droop_chart_stable` with the Thevenin
amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_droop_pqv_stable
    {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P) {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (pq : PQVPort) (hpV : pq.V0 = V0)
    (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (dG mp ω1 ωm P δ0 V0)
        (dxeq P δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ
        PδV Ω)).re < 0)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ ((DxC (smDx (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0))
        z + (pq.V0 * pq.effV w) • (smM1 (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (dright mp ω1 ωm Pδ PV Pδδ PδV Ω)) / 2‖ ^ 2 < ‖dleft mp ω1 ωm Pδ
        PV Pδδ PδV Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
            (thPolarAbs pq.eth pq.V0)
          ((dxeq P δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
            (thPolarAbs pq.eth pq.V0)
          ((dxeq P δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 3 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor
            (dG mp ω1 ωm P δ0 V0) e3) (thPolarAbs pq.eth pq.V0)) (dxeq P δ0 V0, 0) w (2 * Ω) A0' ε
                t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_droop_chart_stable (hP := hP) (hΩ := hΩ) (hmp := hmp) (hω1 := hω1) (hd2 := hd2)
      (hPδ0 := hPδ0) (hV0 := hpV ▸ hV.ne') (hH1 := hH1) (hH2 := hH2) (hPδ := hPδ) (hPV := hPV)
      (hPδδ := hPδδ) (hPδV := hPδV) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The droop core with two filters under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port
`pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end, parametric
instability: `orbit_droop_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ =
θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_droop_pqv_unstable
    {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P) {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (pq : PQVPort) (hpV : pq.V0 = V0)
    (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (dG mp ω1 ωm P δ0 V0)
        (dxeq P δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ
        PδV Ω)‖ ^ 2 < ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ ((DxC
        (smDx (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)) z + (pq.V0 * pq.effV w) •
        (smM1 (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star
        (dright mp ω1 ωm Pδ PV Pδδ PδV Ω)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
            (thPolarAbs pq.eth pq.V0)
          ((dxeq P δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
            (thPolarAbs pq.eth pq.V0)
          ((dxeq P δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (dG mp ω1 ωm P δ0 V0) e3) (thPolarAbs pq.eth pq.V0)) (dxeq P δ0 V0, 0) w (2 * Ω) A0' ε t
              (y t))
          (2 * Real.pi / (2 * Ω)) :=
  orbit_droop_chart_unstable (hP := hP) (hΩ := hΩ) (hmp := hmp) (hω1 := hω1) (hd2 := hd2)
      (hPδ0 := hPδ0) (hV0 := hpV ▸ hV.ne') (hH1 := hH1) (hH2 := hH2) (hPδ := hPδ) (hPV := hPV)
      (hPδδ := hPδδ) (hPδV := hPδV) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The droop core with two filters under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port
`pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end, local
exponential orbital stability: `orbit_droop_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_droop_pqv_exp_stable
    {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P) {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (pq : PQVPort) (hpV : pq.V0 = V0)
    (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (dG mp ω1 ωm P δ0 V0)
        (dxeq P δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ
        PδV Ω)).re < 0)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ ((DxC (smDx (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0))
        z + (pq.V0 * pq.effV w) • (smM1 (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (dright mp ω1 ωm Pδ PV Pδδ PδV Ω)) / 2‖ ^ 2 < ‖dleft mp ω1 ωm Pδ
        PV Pδδ PδV Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
          (thPolarAbs pq.eth pq.V0) ((dxeq P δ0
          V0, (0 : Fin 4 → ℝ)).1 + y t,
        (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3)
            (thPolarAbs pq.eth pq.V0)
            ((dxeq P δ0 V0, (0 : Fin 4 → ℝ)).1 + a,
          (dxeq P δ0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_droop_chart_exp_stable (hP := hP) (hΩ := hΩ) (hmp := hmp) (hω1 := hω1) (hd2 := hd2)
      (hPδ0 := hPδ0) (hV0 := hpV ▸ hV.ne') (hH1 := hH1) (hH2 := hH2) (hPδ := hPδ) (hPV := hPV)
      (hPδδ := hPδδ) (hPδV := hPδV) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

end powerlib.GFM.VoltageModulation.Droop

/-! ### dVOC -/

namespace powerlib.GFM.DVOCCore
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam)
open powerlib.GFM.PortVariants (e3)
open powerlib.ParametricResonance.PortDisturbance (Port PQVPort thPolarAbs thPolarAbs_zero
  contDiffAt_thPolarAbs)
variable (d : DVOCCore)

/-- The dVOC core under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt` (grid-voltage
and injected-current magnitude and angle), end-to-end, stability (all Floquet multipliers inside the
unit circle): `orbit_dvoc_chart_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff`
of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_dvoc_port_stable
    {V0 Ψ0 K νδ νP νK : ℝ} (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hδ : d.η * K = νδ) (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK) (hi : νP < νδ)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 3 → ℂ}
    (hz : (((2 * 1 : ℝ) : ℂ) * I) • z - (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) *ᵥ
        z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1)) -
        ((((2 * 1 : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)).re < 0)
    (hg : ‖left νδ νP νK ⬝ᵥ ((DxC (smDx (d.rfieldV V0) (xeq Ψ0, V0)) z + (pt.V0 * pt.effV w) •
        (smM1 (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (right νP νK)) / 2‖ ^ 2 <
        ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pt.eth pt.V0)
          ((xeq Ψ0, (0 : Fin 4 → ℝ)).1 + y t, (xeq Ψ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pt.eth pt.V0)
          ((xeq Ψ0, (0 : Fin 4 → ℝ)).1 + y t, (xeq Ψ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 3 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pt.eth pt.V0)) (xeq Ψ0, 0) w (2 * 1) A0' ε t (y t)) (2 * Real.pi / (2 * 1))
                0).map
            (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_dvoc_chart_stable (hp := hp) (hpe := hpe) (hP := hP) (hδ := hδ) (hPn := hPn) (hKn := hKn)
      (hνK := hνK) (hkp := hkp) (hki := hki) (hV0 := hpV ▸ hV.ne') (hi := hi) (hz := hz)
      (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN
      hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The dVOC core under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt` (grid-voltage
and injected-current magnitude and angle), end-to-end, parametric instability:
`orbit_dvoc_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_dvoc_port_unstable
    {V0 Ψ0 K νδ νP νK : ℝ} (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hδ : d.η * K = νδ) (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK) (hi : νP < νδ)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 3 → ℂ}
    (hz : (((2 * 1 : ℝ) : ℂ) * I) • z - (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) *ᵥ
        z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1)) -
        ((((2 * 1 : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2 < ‖left νδ νP νK ⬝ᵥ
        ((DxC (smDx (d.rfieldV V0) (xeq Ψ0, V0)) z + (pt.V0 * pt.effV w) •
        (smM1 (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (right νP νK)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pt.eth pt.V0)
          ((xeq Ψ0, (0 : Fin 4 → ℝ)).1 + y t, (xeq Ψ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pt.eth pt.V0)
          ((xeq Ψ0, (0 : Fin 4 → ℝ)).1 + y t, (xeq Ψ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (d.rfieldV V0) e3) (thPolarAbs pt.eth pt.V0)) (xeq Ψ0, 0) w (2 * 1) A0' ε t (y t))
              (2 * Real.pi / (2 * 1)) :=
  orbit_dvoc_chart_unstable (hp := hp) (hpe := hpe) (hP := hP) (hδ := hδ) (hPn := hPn) (hKn := hKn)
      (hνK := hνK) (hkp := hkp) (hki := hki) (hV0 := hpV ▸ hV.ne') (hi := hi) (hz := hz)
      (A0' := A0') (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The dVOC core under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt` (grid-voltage
and injected-current magnitude and angle), end-to-end, local exponential orbital stability:
`orbit_dvoc_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_dvoc_port_exp_stable
    {V0 Ψ0 K νδ νP νK : ℝ} (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hδ : d.η * K = νδ) (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK) (hi : νP < νδ)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 3 → ℂ}
    (hz : (((2 * 1 : ℝ) : ℂ) * I) • z - (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) *ᵥ
        z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1)) -
        ((((2 * 1 : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)).re < 0)
    (hg : ‖left νδ νP νK ⬝ᵥ ((DxC (smDx (d.rfieldV V0) (xeq Ψ0, V0)) z + (pt.V0 * pt.effV w) •
        (smM1 (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (right νP νK)) / 2‖ ^ 2 <
        ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
          (thPolarAbs pt.eth pt.V0) ((xeq Ψ0, (0 : Fin 4 →
          ℝ)).1 + y t,
        (xeq Ψ0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pt.eth pt.V0) ((xeq
            Ψ0, (0 : Fin 4 → ℝ)).1 + a,
          (xeq Ψ0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * 1) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_dvoc_chart_exp_stable (hp := hp) (hpe := hpe) (hP := hP) (hδ := hδ) (hPn := hPn)
      (hKn := hKn) (hνK := hνK) (hkp := hkp) (hki := hki) (hV0 := hpV ▸ hV.ne') (hi := hi)
      (hz := hz) (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs
      pt.contDiff_eth.contDiffAt hN hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV])
      (hvθ := pt.linCV_polarAbs hN hV w)

/-- The dVOC core under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq` (grid-voltage
magnitude and angle, injected active and reactive power), end-to-end, stability (all Floquet
multipliers inside the unit circle): `orbit_dvoc_chart_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_dvoc_pqv_stable
    {V0 Ψ0 K νδ νP νK : ℝ} (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hδ : d.η * K = νδ) (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK) (hi : νP < νδ)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 3 → ℂ}
    (hz : (((2 * 1 : ℝ) : ℂ) * I) • z - (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) *ᵥ
        z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1)) -
        ((((2 * 1 : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)).re < 0)
    (hg : ‖left νδ νP νK ⬝ᵥ ((DxC (smDx (d.rfieldV V0) (xeq Ψ0, V0)) z + (pq.V0 * pq.effV w) •
        (smM1 (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (right νP νK)) / 2‖ ^ 2 <
        ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pq.eth pq.V0)
          ((xeq Ψ0, (0 : Fin 4 → ℝ)).1 + y t, (xeq Ψ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pq.eth pq.V0)
          ((xeq Ψ0, (0 : Fin 4 → ℝ)).1 + y t, (xeq Ψ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 3 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pq.eth pq.V0)) (xeq Ψ0, 0) w (2 * 1) A0' ε t (y t)) (2 * Real.pi / (2 * 1))
                0).map
            (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_dvoc_chart_stable (hp := hp) (hpe := hpe) (hP := hP) (hδ := hδ) (hPn := hPn) (hKn := hKn)
      (hνK := hνK) (hkp := hkp) (hki := hki) (hV0 := hpV ▸ hV.ne') (hi := hi) (hz := hz)
      (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN
      hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The dVOC core under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq` (grid-voltage
magnitude and angle, injected active and reactive power), end-to-end, parametric instability:
`orbit_dvoc_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_dvoc_pqv_unstable
    {V0 Ψ0 K νδ νP νK : ℝ} (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hδ : d.η * K = νδ) (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK) (hi : νP < νδ)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 3 → ℂ}
    (hz : (((2 * 1 : ℝ) : ℂ) * I) • z - (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) *ᵥ
        z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1)) -
        ((((2 * 1 : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2 < ‖left νδ νP νK ⬝ᵥ
        ((DxC (smDx (d.rfieldV V0) (xeq Ψ0, V0)) z + (pq.V0 * pq.effV w) •
        (smM1 (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (right νP νK)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pq.eth pq.V0)
          ((xeq Ψ0, (0 : Fin 4 → ℝ)).1 + y t, (xeq Ψ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pq.eth pq.V0)
          ((xeq Ψ0, (0 : Fin 4 → ℝ)).1 + y t, (xeq Ψ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (d.rfieldV V0) e3) (thPolarAbs pq.eth pq.V0)) (xeq Ψ0, 0) w (2 * 1) A0' ε t (y t))
              (2 * Real.pi / (2 * 1)) :=
  orbit_dvoc_chart_unstable (hp := hp) (hpe := hpe) (hP := hP) (hδ := hδ) (hPn := hPn) (hKn := hKn)
      (hνK := hνK) (hkp := hkp) (hki := hki) (hV0 := hpV ▸ hV.ne') (hi := hi) (hz := hz)
      (A0' := A0') (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The dVOC core under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq` (grid-voltage
magnitude and angle, injected active and reactive power), end-to-end, local exponential orbital
stability: `orbit_dvoc_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ =
θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_dvoc_pqv_exp_stable
    {V0 Ψ0 K νδ νP νK : ℝ} (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hδ : d.η * K = νδ) (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK) (hi : νP < νδ)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 3 → ℂ}
    (hz : (((2 * 1 : ℝ) : ℂ) * I) • z - (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) *ᵥ
        z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1)) -
        ((((2 * 1 : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)).re < 0)
    (hg : ‖left νδ νP νK ⬝ᵥ ((DxC (smDx (d.rfieldV V0) (xeq Ψ0, V0)) z + (pq.V0 * pq.effV w) •
        (smM1 (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (right νP νK)) / 2‖ ^ 2 <
        ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
          (thPolarAbs pq.eth pq.V0) ((xeq Ψ0, (0 : Fin 4 →
          ℝ)).1 + y t,
        (xeq Ψ0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            (thPolarAbs pq.eth pq.V0) ((xeq
            Ψ0, (0 : Fin 4 → ℝ)).1 + a,
          (xeq Ψ0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * 1) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_dvoc_chart_exp_stable (hp := hp) (hpe := hpe) (hP := hP) (hδ := hδ) (hPn := hPn)
      (hKn := hKn) (hνK := hνK) (hkp := hkp) (hki := hki) (hV0 := hpV ▸ hV.ne') (hi := hi)
      (hz := hz) (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs
      pq.contDiff_eth.contDiffAt hN hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV])
      (hvθ := pq.linCV_polarAbs hN hV hU w)

end powerlib.GFM.DVOCCore

/-! ### PSC with active damping -/

namespace powerlib.GFM.PSCFull.Model
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam)
open powerlib.GFM.PortVariants (e4)
open powerlib.ParametricResonance.PortDisturbance (Port PQVPort thPolarAbs thPolarAbs_zero
  contDiffAt_thPolarAbs)
variable (p : Model)

/-- The PSC with active damping under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, stability (all Floquet
multipliers inside the unit circle): `orbit_psc_chart_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_psc_port_stable
    (δ0 : ℝ) (hZ : p.Z ≠ 0) (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : p.Jreal δ0 * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : p.umode δ0 Ω ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pt : Port) (hpV : pt.V0 = p.V) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (p.rfield (p.Peq δ0))
        (p.xeq δ0, p.V) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (p.shift δ0 Ω A0').re < 0)
    (hg : ‖p.umode δ0 Ω ⬝ᵥ ((DxC (smDx (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)) z +
        (pt.V0 * pt.effV w) • (smM1 (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ)) *ᵥ
        star (p.rmode δ0 Ω)) / 2‖ ^ 2 < ‖p.shift δ0 Ω A0'‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
            (thPolarAbs pt.eth pt.V0)
          ((p.xeq δ0, (0 : Fin 4 → ℝ)).1 + y t, (p.xeq δ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
            (thPolarAbs pt.eth pt.V0)
          ((p.xeq δ0, (0 : Fin 4 → ℝ)).1 + y t, (p.xeq δ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 4 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor
            (p.rfield (p.Peq δ0)) e4) (thPolarAbs pt.eth pt.V0)) (p.xeq δ0, 0) w (2 * Ω) A0' ε t
                (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_psc_chart_stable (δ0 := δ0) (hZ := hZ) (hZ0 := hZ0) (hΩ := hΩ) (hk := hk) (h1 := h1)
      (h2 := h2) (hD := hD) (hDd := hDd) (hW := hW) (hWW := hWW) (huW := huW) (hWr := hWr)
      (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The PSC with active damping under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, parametric instability:
`orbit_psc_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_psc_port_unstable
    (δ0 : ℝ) (hZ : p.Z ≠ 0) (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : p.Jreal δ0 * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : p.umode δ0 Ω ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pt : Port) (hpV : pt.V0 = p.V) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (p.rfield (p.Peq δ0))
        (p.xeq δ0, p.V) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖p.shift δ0 Ω A0'‖ ^ 2 < ‖p.umode δ0 Ω ⬝ᵥ ((DxC (smDx (p.rfield (p.Peq δ0))
        (p.xeq δ0, p.V)) z + (pt.V0 * pt.effV w) • (smM1 (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map
        (algebraMap ℝ ℂ)) *ᵥ star (p.rmode δ0 Ω)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
            (thPolarAbs pt.eth pt.V0)
          ((p.xeq δ0, (0 : Fin 4 → ℝ)).1 + y t, (p.xeq δ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
            (thPolarAbs pt.eth pt.V0)
          ((p.xeq δ0, (0 : Fin 4 → ℝ)).1 + y t, (p.xeq δ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (p.rfield (p.Peq δ0)) e4) (thPolarAbs pt.eth pt.V0)) (p.xeq δ0, 0) w (2 * Ω) A0' ε t
              (y t))
          (2 * Real.pi / (2 * Ω)) :=
  orbit_psc_chart_unstable (δ0 := δ0) (hZ := hZ) (hZ0 := hZ0) (hΩ := hΩ) (hk := hk) (h1 := h1)
      (h2 := h2) (hD := hD) (hDd := hDd) (hW := hW) (hWW := hWW) (huW := huW) (hWr := hWr)
      (hsr := hsr) (hz := hz) (A0' := A0') (hg := hg) (hΦ := contDiffAt_thPolarAbs
      pt.contDiff_eth.contDiffAt hN hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV])
      (hvθ := pt.linCV_polarAbs hN hV w)

/-- The PSC with active damping under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, local exponential orbital
stability: `orbit_psc_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff`
of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_psc_port_exp_stable
    (δ0 : ℝ) (hZ : p.Z ≠ 0) (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : p.Jreal δ0 * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : p.umode δ0 Ω ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pt : Port) (hpV : pt.V0 = p.V) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (p.rfield (p.Peq δ0))
        (p.xeq δ0, p.V) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (p.shift δ0 Ω A0').re < 0)
    (hg : ‖p.umode δ0 Ω ⬝ᵥ ((DxC (smDx (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)) z +
        (pt.V0 * pt.effV w) • (smM1 (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ)) *ᵥ
        star (p.rmode δ0 Ω)) / 2‖ ^ 2 < ‖p.shift δ0 Ω A0'‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
          (thPolarAbs pt.eth pt.V0) ((p.xeq δ0,
          (0 : Fin 4 → ℝ)).1 + y t,
        (p.xeq δ0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
            (thPolarAbs pt.eth pt.V0)
            ((p.xeq δ0, (0 : Fin 4 → ℝ)).1 + a,
          (p.xeq δ0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_psc_chart_exp_stable (δ0 := δ0) (hZ := hZ) (hZ0 := hZ0) (hΩ := hΩ) (hk := hk) (h1 := h1)
      (h2 := h2) (hD := hD) (hDd := hDd) (hW := hW) (hWW := hWW) (huW := huW) (hWr := hWr)
      (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The PSC with active damping under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, stability (all
Floquet multipliers inside the unit circle): `orbit_psc_chart_stable` with the Thevenin amplitudes
`V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_psc_pqv_stable
    (δ0 : ℝ) (hZ : p.Z ≠ 0) (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : p.Jreal δ0 * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : p.umode δ0 Ω ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pq : PQVPort) (hpV : pq.V0 = p.V) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (p.rfield (p.Peq δ0))
        (p.xeq δ0, p.V) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (p.shift δ0 Ω A0').re < 0)
    (hg : ‖p.umode δ0 Ω ⬝ᵥ ((DxC (smDx (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)) z +
        (pq.V0 * pq.effV w) • (smM1 (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ)) *ᵥ
        star (p.rmode δ0 Ω)) / 2‖ ^ 2 < ‖p.shift δ0 Ω A0'‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
            (thPolarAbs pq.eth pq.V0)
          ((p.xeq δ0, (0 : Fin 4 → ℝ)).1 + y t, (p.xeq δ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
            (thPolarAbs pq.eth pq.V0)
          ((p.xeq δ0, (0 : Fin 4 → ℝ)).1 + y t, (p.xeq δ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 4 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor
            (p.rfield (p.Peq δ0)) e4) (thPolarAbs pq.eth pq.V0)) (p.xeq δ0, 0) w (2 * Ω) A0' ε t
                (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_psc_chart_stable (δ0 := δ0) (hZ := hZ) (hZ0 := hZ0) (hΩ := hΩ) (hk := hk) (h1 := h1)
      (h2 := h2) (hD := hD) (hDd := hDd) (hW := hW) (hWW := hWW) (huW := huW) (hWr := hWr)
      (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The PSC with active damping under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, parametric
instability: `orbit_psc_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff`
of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_psc_pqv_unstable
    (δ0 : ℝ) (hZ : p.Z ≠ 0) (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : p.Jreal δ0 * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : p.umode δ0 Ω ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pq : PQVPort) (hpV : pq.V0 = p.V) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (p.rfield (p.Peq δ0))
        (p.xeq δ0, p.V) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖p.shift δ0 Ω A0'‖ ^ 2 < ‖p.umode δ0 Ω ⬝ᵥ ((DxC (smDx (p.rfield (p.Peq δ0))
        (p.xeq δ0, p.V)) z + (pq.V0 * pq.effV w) • (smM1 (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map
        (algebraMap ℝ ℂ)) *ᵥ star (p.rmode δ0 Ω)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
            (thPolarAbs pq.eth pq.V0)
          ((p.xeq δ0, (0 : Fin 4 → ℝ)).1 + y t, (p.xeq δ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
            (thPolarAbs pq.eth pq.V0)
          ((p.xeq δ0, (0 : Fin 4 → ℝ)).1 + y t, (p.xeq δ0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (p.rfield (p.Peq δ0)) e4) (thPolarAbs pq.eth pq.V0)) (p.xeq δ0, 0) w (2 * Ω) A0' ε t
              (y t))
          (2 * Real.pi / (2 * Ω)) :=
  orbit_psc_chart_unstable (δ0 := δ0) (hZ := hZ) (hZ0 := hZ0) (hΩ := hΩ) (hk := hk) (h1 := h1)
      (h2 := h2) (hD := hD) (hDd := hDd) (hW := hW) (hWW := hWW) (huW := huW) (hWr := hWr)
      (hsr := hsr) (hz := hz) (A0' := A0') (hg := hg) (hΦ := contDiffAt_thPolarAbs
      pq.contDiff_eth.contDiffAt hN hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV])
      (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The PSC with active damping under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, local
exponential orbital stability: `orbit_psc_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_psc_pqv_exp_stable
    (δ0 : ℝ) (hZ : p.Z ≠ 0) (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : p.Jreal δ0 * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : p.umode δ0 Ω ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pq : PQVPort) (hpV : pq.V0 = p.V) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (p.rfield (p.Peq δ0))
        (p.xeq δ0, p.V) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (p.shift δ0 Ω A0').re < 0)
    (hg : ‖p.umode δ0 Ω ⬝ᵥ ((DxC (smDx (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)) z +
        (pq.V0 * pq.effV w) • (smM1 (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ)) *ᵥ
        star (p.rmode δ0 Ω)) / 2‖ ^ 2 < ‖p.shift δ0 Ω A0'‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
          (thPolarAbs pq.eth pq.V0) ((p.xeq δ0,
          (0 : Fin 4 → ℝ)).1 + y t,
        (p.xeq δ0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4)
            (thPolarAbs pq.eth pq.V0)
            ((p.xeq δ0, (0 : Fin 4 → ℝ)).1 + a,
          (p.xeq δ0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_psc_chart_exp_stable (δ0 := δ0) (hZ := hZ) (hZ0 := hZ0) (hΩ := hΩ) (hk := hk) (h1 := h1)
      (h2 := h2) (hD := hD) (hDd := hDd) (hW := hW) (hWW := hWW) (huW := huW) (hWr := hWr)
      (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

end powerlib.GFM.PSCFull.Model

/-! ### Matching control -/

namespace powerlib.GFM.Matching.MatchingCore
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam)
open powerlib.GFM.VoltageModulation.Core (Pd)
open powerlib.GFM.PortVariants (e4)
open powerlib.ParametricResonance.PortDisturbance (Port PQVPort thPolarAbs thPolarAbs_zero
  contDiffAt_thPolarAbs)
variable (d : MatchingCore)

/-- Matching control under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, stability (all Floquet
multipliers inside the unit circle): `orbit_matching_chart_stable` with the Thevenin amplitudes `V̂
= V₀ v̂_eff`, `θ̂ = θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_matching_port_stable
    {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV) {δ0 V0 Ω K KV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0)
    (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K)
    (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV) (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    {r u : Fin 4 → ℂ} (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : d.jacobian K * Wm = Wm * As) (hWW : Wm' * Wm = 1) (huW : u ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (d.mG ixV δ0 V0)
        (d.meq ixV δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)) z + (pt.V0 * pt.effV w) •
        (smM1 (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 <
        ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
            (thPolarAbs pt.eth pt.V0)
          ((d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
            (thPolarAbs pt.eth pt.V0)
          ((d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 4 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor
            (d.mG ixV δ0 V0) e4) (thPolarAbs pt.eth pt.V0)) (d.meq ixV δ0 V0, 0) w (2 * Ω) A0' ε t
                (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_matching_chart_stable (hP := hP) (hΩ := hΩ) (hωb := hωb) (hωf := hωf) (hC := hC) (hτ := hτ)
      (hK := hK) (hKV := hKV) (hD2 := hD2) (hr := hr) (hu := hu) (hur := hur) (hW := hW)
      (hWW := hWW) (huW := huW) (hWr := hWr) (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs)
      (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- Matching control under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, parametric instability:
`orbit_matching_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_matching_port_unstable
    {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV) {δ0 V0 Ω K KV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0)
    (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K)
    (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV) (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    {r u : Fin 4 → ℂ} (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : d.jacobian K * Wm = Wm * As) (hWW : Wm' * Wm = 1) (huW : u ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (d.mG ixV δ0 V0)
        (d.meq ixV δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖u ⬝ᵥ
        ((DxC (smDx (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)) z + (pt.V0 * pt.effV w) •
        (smM1 (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
            (thPolarAbs pt.eth pt.V0)
          ((d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
            (thPolarAbs pt.eth pt.V0)
          ((d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (d.mG ixV δ0 V0) e4) (thPolarAbs pt.eth pt.V0)) (d.meq ixV δ0 V0, 0) w (2 * Ω) A0' ε t
              (y t))
          (2 * Real.pi / (2 * Ω)) :=
  orbit_matching_chart_unstable (hP := hP) (hΩ := hΩ) (hωb := hωb) (hωf := hωf) (hC := hC)
      (hτ := hτ) (hK := hK) (hKV := hKV) (hD2 := hD2) (hr := hr) (hu := hu) (hur := hur) (hW := hW)
      (hWW := hWW) (huW := huW) (hWr := hWr) (hsr := hsr) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- Matching control under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, local exponential orbital
stability: `orbit_matching_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ =
θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_matching_port_exp_stable
    {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV) {δ0 V0 Ω K KV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0)
    (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K)
    (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV) (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    {r u : Fin 4 → ℂ} (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : d.jacobian K * Wm = Wm * As) (hWW : Wm' * Wm = 1) (huW : u ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (d.mG ixV δ0 V0)
        (d.meq ixV δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)) z + (pt.V0 * pt.effV w) •
        (smM1 (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 <
        ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
          (thPolarAbs pt.eth pt.V0) ((d.meq ixV δ0 V0,
          (0 : Fin 4 → ℝ)).1 + y t,
        (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
            (thPolarAbs pt.eth pt.V0)
            ((d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).1 + a,
          (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a))
              (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_matching_chart_exp_stable (hP := hP) (hΩ := hΩ) (hωb := hωb) (hωf := hωf) (hC := hC)
      (hτ := hτ) (hK := hK) (hKV := hKV) (hD2 := hD2) (hr := hr) (hu := hu) (hur := hur) (hW := hW)
      (hWW := hWW) (huW := huW) (hWr := hWr) (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs)
      (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- Matching control under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, stability (all
Floquet multipliers inside the unit circle): `orbit_matching_chart_stable` with the Thevenin
amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_matching_pqv_stable
    {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV) {δ0 V0 Ω K KV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0)
    (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K)
    (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV) (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    {r u : Fin 4 → ℂ} (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : d.jacobian K * Wm = Wm * As) (hWW : Wm' * Wm = 1) (huW : u ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (d.mG ixV δ0 V0)
        (d.meq ixV δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)) z + (pq.V0 * pq.effV w) •
        (smM1 (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 <
        ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
            (thPolarAbs pq.eth pq.V0)
          ((d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
            (thPolarAbs pq.eth pq.V0)
          ((d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 4 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor
            (d.mG ixV δ0 V0) e4) (thPolarAbs pq.eth pq.V0)) (d.meq ixV δ0 V0, 0) w (2 * Ω) A0' ε t
                (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_matching_chart_stable (hP := hP) (hΩ := hΩ) (hωb := hωb) (hωf := hωf) (hC := hC) (hτ := hτ)
      (hK := hK) (hKV := hKV) (hD2 := hD2) (hr := hr) (hu := hu) (hur := hur) (hW := hW)
      (hWW := hWW) (huW := huW) (hWr := hWr) (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs)
      (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- Matching control under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, parametric
instability: `orbit_matching_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ =
θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_matching_pqv_unstable
    {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV) {δ0 V0 Ω K KV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0)
    (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K)
    (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV) (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    {r u : Fin 4 → ℂ} (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : d.jacobian K * Wm = Wm * As) (hWW : Wm' * Wm = 1) (huW : u ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (d.mG ixV δ0 V0)
        (d.meq ixV δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖u ⬝ᵥ
        ((DxC (smDx (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)) z + (pq.V0 * pq.effV w) •
        (smM1 (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
            (thPolarAbs pq.eth pq.V0)
          ((d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
            (thPolarAbs pq.eth pq.V0)
          ((d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (d.mG ixV δ0 V0) e4) (thPolarAbs pq.eth pq.V0)) (d.meq ixV δ0 V0, 0) w (2 * Ω) A0' ε t
              (y t))
          (2 * Real.pi / (2 * Ω)) :=
  orbit_matching_chart_unstable (hP := hP) (hΩ := hΩ) (hωb := hωb) (hωf := hωf) (hC := hC)
      (hτ := hτ) (hK := hK) (hKV := hKV) (hD2 := hD2) (hr := hr) (hu := hu) (hur := hur) (hW := hW)
      (hWW := hWW) (huW := huW) (hWr := hWr) (hsr := hsr) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- Matching control under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, local
exponential orbital stability: `orbit_matching_chart_exp_stable` with the Thevenin amplitudes `V̂ =
V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_matching_pqv_exp_stable
    {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV) {δ0 V0 Ω K KV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0)
    (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K)
    (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV) (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    {r u : Fin 4 → ℂ} (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : d.jacobian K * Wm = Wm * As) (hWW : Wm' * Wm = 1) (huW : u ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
        (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (d.mG ixV δ0 V0)
        (d.meq ixV δ0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)) z + (pq.V0 * pq.effV w) •
        (smM1 (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 <
        ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
          (thPolarAbs pq.eth pq.V0) ((d.meq ixV δ0 V0,
          (0 : Fin 4 → ℝ)).1 + y t,
        (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4)
            (thPolarAbs pq.eth pq.V0)
            ((d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).1 + a,
          (d.meq ixV δ0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a))
              (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_matching_chart_exp_stable (hP := hP) (hΩ := hΩ) (hωb := hωb) (hωf := hωf) (hC := hC)
      (hτ := hτ) (hK := hK) (hKV := hKV) (hD2 := hD2) (hr := hr) (hu := hu) (hur := hur) (hW := hW)
      (hWW := hWW) (huW := huW) (hWr := hWr) (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs)
      (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

end powerlib.GFM.Matching.MatchingCore

/-! ### Dynamic Q–V loop and its filtered version -/

namespace powerlib.GFM.VoltageModulation.DynQV
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam
  matXV smMwV uMag uAng)
open powerlib.GFM.PortVariants (e4 e5)
open powerlib.ParametricResonance.PortDisturbance (Port PQVPort thPolarAbs thPolarAbs_zero
  contDiffAt_thPolarAbs)
variable (c : DynQV)

/-- The dynamic Q–V loop under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, stability (all Floquet
multipliers inside the unit circle): `orbit_qv_chart_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qv_port_stable
    {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ)
    (hPE : dE P ((δ0, E0), V0) = c.PE) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r (2 * Real.pi / (2 * Ω))
        * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (c.qG P Q δ0 E0 V0)
        (qxeq P δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.left (Ω * I) ⬝ᵥ ((DxC (smDx (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)) z +
        (pt.V0 * pt.effV w) • (smM1 (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (c.right (Ω * I))) / 2‖ ^ 2 < ‖c.left (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
            (thPolarAbs pt.eth pt.V0)
          ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
            (thPolarAbs pt.eth pt.V0)
          ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 4 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0)
              e4) (thPolarAbs pt.eth pt.V0)) (qxeq P δ0 E0 V0, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_qv_chart_stable (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH) (hτ := hτ)
      (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (hF := hF) (hFd := hFd) (hsr := hsr)
      (hz := hz) (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs
      pt.contDiff_eth.contDiffAt hN hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV])
      (hvθ := pt.linCV_polarAbs hN hV w)

/-- The dynamic Q–V loop under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, parametric instability:
`orbit_qv_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qv_port_unstable
    {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ)
    (hPE : dE P ((δ0, E0), V0) = c.PE) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r (2 * Real.pi / (2 * Ω))
        * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (c.qG P Q δ0 E0 V0)
        (qxeq P δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 < ‖c.left (Ω * I)
        ⬝ᵥ ((DxC (smDx (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)) z + (pt.V0 * pt.effV w) •
        (smM1 (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star
        (c.right (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
            (thPolarAbs pt.eth pt.V0)
          ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
            (thPolarAbs pt.eth pt.V0)
          ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0
            V0) e4) (thPolarAbs pt.eth pt.V0)) (qxeq P δ0 E0 V0, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) :=
  orbit_qv_chart_unstable (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH) (hτ := hτ)
      (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (hF := hF) (hFd := hFd) (hsr := hsr)
      (hz := hz) (A0' := A0') (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN
      hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The dynamic Q–V loop under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, local exponential orbital
stability: `orbit_qv_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff`
of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qv_port_exp_stable
    {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ)
    (hPE : dE P ((δ0, E0), V0) = c.PE) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r (2 * Real.pi / (2 * Ω))
        * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (c.qG P Q δ0 E0 V0)
        (qxeq P δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.left (Ω * I) ⬝ᵥ ((DxC (smDx (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)) z +
        (pt.V0 * pt.effV w) • (smM1 (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (c.right (Ω * I))) / 2‖ ^ 2 < ‖c.left (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
          (thPolarAbs pt.eth pt.V0)
          ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
            (thPolarAbs pt.eth pt.V0)
            ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + a,
          (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a))
              (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_qv_chart_exp_stable (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH) (hτ := hτ)
      (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (hF := hF) (hFd := hFd) (hsr := hsr)
      (hz := hz) (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs
      pt.contDiff_eth.contDiffAt hN hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV])
      (hvθ := pt.linCV_polarAbs hN hV w)

/-- The dynamic Q–V loop under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, stability (all
Floquet multipliers inside the unit circle): `orbit_qv_chart_stable` with the Thevenin amplitudes
`V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qv_pqv_stable
    {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ)
    (hPE : dE P ((δ0, E0), V0) = c.PE) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r (2 * Real.pi / (2 * Ω))
        * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (c.qG P Q δ0 E0 V0)
        (qxeq P δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.left (Ω * I) ⬝ᵥ ((DxC (smDx (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)) z +
        (pq.V0 * pq.effV w) • (smM1 (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (c.right (Ω * I))) / 2‖ ^ 2 < ‖c.left (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
            (thPolarAbs pq.eth pq.V0)
          ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
            (thPolarAbs pq.eth pq.V0)
          ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 4 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0)
              e4) (thPolarAbs pq.eth pq.V0)) (qxeq P δ0 E0 V0, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_qv_chart_stable (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH) (hτ := hτ)
      (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (hF := hF) (hFd := hFd) (hsr := hsr)
      (hz := hz) (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs
      pq.contDiff_eth.contDiffAt hN hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV])
      (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The dynamic Q–V loop under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, parametric
instability: `orbit_qv_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff`
of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qv_pqv_unstable
    {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ)
    (hPE : dE P ((δ0, E0), V0) = c.PE) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r (2 * Real.pi / (2 * Ω))
        * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (c.qG P Q δ0 E0 V0)
        (qxeq P δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 < ‖c.left (Ω * I)
        ⬝ᵥ ((DxC (smDx (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)) z + (pq.V0 * pq.effV w) •
        (smM1 (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star
        (c.right (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
            (thPolarAbs pq.eth pq.V0)
          ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
            (thPolarAbs pq.eth pq.V0)
          ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0
            V0) e4) (thPolarAbs pq.eth pq.V0)) (qxeq P δ0 E0 V0, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) :=
  orbit_qv_chart_unstable (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH) (hτ := hτ)
      (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (hF := hF) (hFd := hFd) (hsr := hsr)
      (hz := hz) (A0' := A0') (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN
      hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The dynamic Q–V loop under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, local
exponential orbital stability: `orbit_qv_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qv_pqv_exp_stable
    {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ)
    (hPE : dE P ((δ0, E0), V0) = c.PE) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r (2 * Real.pi / (2 * Ω))
        * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (c.qG P Q δ0 E0 V0)
        (qxeq P δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.left (Ω * I) ⬝ᵥ ((DxC (smDx (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)) z +
        (pq.V0 * pq.effV w) • (smM1 (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (c.right (Ω * I))) / 2‖ ^ 2 < ‖c.left (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
          (thPolarAbs pq.eth pq.V0)
          ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4)
            (thPolarAbs pq.eth pq.V0)
            ((qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + a,
          (qxeq P δ0 E0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a))
              (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_qv_chart_exp_stable (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH) (hτ := hτ)
      (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (hF := hF) (hFd := hFd) (hsr := hsr)
      (hz := hz) (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs
      pq.contDiff_eth.contDiffAt hN hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV])
      (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The filtered dynamic Q–V loop under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, stability (all Floquet
multipliers inside the unit circle): `orbit_qvf_chart_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_port_stable
    (ωq : ℝ) {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE) (h2 : 0 < c.c2f ωq)
    (h0 : 0 < c.c0f ωq Ω) (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) + ωq * c.b *
        (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) - ωq *
        (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 5 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (c.qGf ωq P Q δ0 E0 V0)
        (qxeqf P Q δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e5)
    (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hs : (c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))).re < 0)
    (hg : ‖c.leftf ωq (Ω * I) ⬝ᵥ ((DxC (smDx (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)) z +
        (pt.V0 * pt.effV w) • (smM1 (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (c.rightf ωq (Ω * I))) / 2‖ ^ 2 < ‖c.leftf ωq (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            (thPolarAbs pt.eth pt.V0)
          ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 5 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            (thPolarAbs pt.eth pt.V0)
          ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 5 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0
              V0) e5) (thPolarAbs pt.eth pt.V0)) (qxeqf P Q δ0 E0 V0, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_qvf_chart_stable (ωq := ωq) (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH)
      (hτ := hτ) (hωq := hωq) (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (h2 := h2)
      (h0 := h0) (hR := hR) (hA := hA) (hB := hB) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The filtered dynamic Q–V loop under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, parametric instability:
`orbit_qvf_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_port_unstable
    (ωq : ℝ) {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE) (h2 : 0 < c.c2f ωq)
    (h0 : 0 < c.c0f ωq Ω) (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) + ωq * c.b *
        (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) - ωq *
        (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 5 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (c.qGf ωq P Q δ0 E0 V0)
        (qxeqf P Q δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e5)
    (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hg : ‖c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2 < ‖c.leftf
        ωq (Ω * I) ⬝ᵥ ((DxC (smDx (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)) z +
        (pt.V0 * pt.effV w) • (smM1 (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (c.rightf ωq (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            (thPolarAbs pt.eth pt.V0)
          ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 5 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            (thPolarAbs pt.eth pt.V0)
          ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0
            E0 V0) e5) (thPolarAbs pt.eth pt.V0)) (qxeqf P Q δ0 E0 V0, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) :=
  orbit_qvf_chart_unstable (ωq := ωq) (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH)
      (hτ := hτ) (hωq := hωq) (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (h2 := h2)
      (h0 := h0) (hR := hR) (hA := hA) (hB := hB) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The filtered dynamic Q–V loop under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, local exponential orbital
stability: `orbit_qvf_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff`
of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_port_exp_stable
    (ωq : ℝ) {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE) (h2 : 0 < c.c2f ωq)
    (h0 : 0 < c.c0f ωq Ω) (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) + ωq * c.b *
        (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) - ωq *
        (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 5 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (c.qGf ωq P Q δ0 E0 V0)
        (qxeqf P Q δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e5)
    (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hs : (c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))).re < 0)
    (hg : ‖c.leftf ωq (Ω * I) ⬝ᵥ ((DxC (smDx (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)) z +
        (pt.V0 * pt.effV w) • (smM1 (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (c.rightf ωq (Ω * I))) / 2‖ ^ 2 < ‖c.leftf ωq (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
          (thPolarAbs pt.eth pt.V0)
          ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 5 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            (thPolarAbs pt.eth pt.V0) ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + a,
          (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a))
              (Set.Ici s)
              →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_qvf_chart_exp_stable (ωq := ωq) (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH)
      (hτ := hτ) (hωq := hωq) (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (h2 := h2)
      (h0 := h0) (hR := hR) (hA := hA) (hB := hB) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The filtered dynamic Q–V loop under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port
`pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end, stability
(all Floquet multipliers inside the unit circle): `orbit_qvf_chart_stable` with the Thevenin
amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_pqv_stable
    (ωq : ℝ) {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE) (h2 : 0 < c.c2f ωq)
    (h0 : 0 < c.c0f ωq Ω) (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) + ωq * c.b *
        (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) - ωq *
        (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 5 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (c.qGf ωq P Q δ0 E0 V0)
        (qxeqf P Q δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e5)
    (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hs : (c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))).re < 0)
    (hg : ‖c.leftf ωq (Ω * I) ⬝ᵥ ((DxC (smDx (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)) z +
        (pq.V0 * pq.effV w) • (smM1 (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (c.rightf ωq (Ω * I))) / 2‖ ^ 2 < ‖c.leftf ωq (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            (thPolarAbs pq.eth pq.V0)
          ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 5 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            (thPolarAbs pq.eth pq.V0)
          ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 5 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0
              V0) e5) (thPolarAbs pq.eth pq.V0)) (qxeqf P Q δ0 E0 V0, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_qvf_chart_stable (ωq := ωq) (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH)
      (hτ := hτ) (hωq := hωq) (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (h2 := h2)
      (h0 := h0) (hR := hR) (hA := hA) (hB := hB) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The filtered dynamic Q–V loop under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port
`pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end, parametric
instability: `orbit_qvf_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff`
of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_pqv_unstable
    (ωq : ℝ) {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE) (h2 : 0 < c.c2f ωq)
    (h0 : 0 < c.c0f ωq Ω) (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) + ωq * c.b *
        (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) - ωq *
        (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 5 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (c.qGf ωq P Q δ0 E0 V0)
        (qxeqf P Q δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e5)
    (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hg : ‖c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2 < ‖c.leftf
        ωq (Ω * I) ⬝ᵥ ((DxC (smDx (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)) z +
        (pq.V0 * pq.effV w) • (smM1 (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (c.rightf ωq (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            (thPolarAbs pq.eth pq.V0)
          ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 5 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            (thPolarAbs pq.eth pq.V0)
          ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0
            E0 V0) e5) (thPolarAbs pq.eth pq.V0)) (qxeqf P Q δ0 E0 V0, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) :=
  orbit_qvf_chart_unstable (ωq := ωq) (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH)
      (hτ := hτ) (hωq := hωq) (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (h2 := h2)
      (h0 := h0) (hR := hR) (hA := hA) (hB := hB) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The filtered dynamic Q–V loop under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port
`pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end, local
exponential orbital stability: `orbit_qvf_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_pqv_exp_stable
    (ωq : ℝ) {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE) (h2 : 0 < c.c2f ωq)
    (h0 : 0 < c.c0f ωq Ω) (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) + ωq * c.b *
        (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) - ωq *
        (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 5 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (c.qGf ωq P Q δ0 E0 V0)
        (qxeqf P Q δ0 E0 V0, V0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e5)
    (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hs : (c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))).re < 0)
    (hg : ‖c.leftf ωq (Ω * I) ⬝ᵥ ((DxC (smDx (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)) z +
        (pq.V0 * pq.effV w) • (smM1 (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (c.rightf ωq (Ω * I))) / 2‖ ^ 2 < ‖c.leftf ωq (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
          (thPolarAbs pq.eth pq.V0)
          ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 5 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            (thPolarAbs pq.eth pq.V0) ((qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + a,
          (qxeqf P Q δ0 E0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a))
              (Set.Ici s)
              →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_qvf_chart_exp_stable (ωq := ωq) (hP := hP) (hQ := hQ) (hΩ := hΩ) (hω0 := hω0) (hH := hH)
      (hτ := hτ) (hωq := hωq) (hPδ := hPδ) (hPE := hPE) (hQδ := hQδ) (hQE := hQE) (h2 := h2)
      (h0 := h0) (hR := hR) (hA := hA) (hB := hB) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

end powerlib.GFM.VoltageModulation.DynQV

/-! ### Dynamic network -/

namespace powerlib.GFM.VoltageModulation.DynQV
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam
  matXV smMwV uMag uAng)
open powerlib.ParametricResonance.PortDisturbance (Port PQVPort thPolarAbs thPolarAbs_zero
  contDiffAt_thPolarAbs)
variable (c : DynQV) (R X ωb : ℝ)

/-- The dynamic network model in a fixed frame under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)`
of a port `pt` (grid-voltage and injected-current magnitude and angle), end-to-end, stability (all
Floquet multipliers inside the unit circle): `orbit_net_chart_stable` with the Thevenin amplitudes
`V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_net_port_stable
    (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) {r u : Fin 6 → ℂ}
    (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u)
    (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ a : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ a =
        ((Ω : ℂ) * I) • a → a = (u ⬝ᵥ a) • r)
    (hstab : ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ a = μ • a → μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 6 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0)
        (nxeq R X δ0 E0 V0, V0) (0, 1)) + (pt.effθ w) • ofv ![0, 0, 0, 0, 0, -(ωb / X * V0)])
    (A0' : Matrix (Fin 6) (Fin 6) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)) z +
        (pt.V0 * pt.effV w) • (smM1 (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pt.eth pt.V0)
          ((nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 6 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pt.eth pt.V0)
          ((nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (c.nHp R X ωb δ0 E0 V0)
              (thPolarAbs pt.eth pt.V0)) (nxeq R X δ0 E0 V0,
              0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_net_chart_stable (hZ := hZ) (hΩ := hΩ) (hr := hr) (hu := hu) (hur := hur)
      (hsimple := hsimple) (hstab := hstab) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The dynamic network model in a fixed frame under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)`
of a port `pt` (grid-voltage and injected-current magnitude and angle), end-to-end, parametric
instability: `orbit_net_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff`
of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_net_port_unstable
    (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) {r u : Fin 6 → ℂ}
    (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u)
    (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ a : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ a =
        ((Ω : ℂ) * I) • a → a = (u ⬝ᵥ a) • r)
    (hstab : ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ a = μ • a → μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 6 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0)
        (nxeq R X δ0 E0 V0, V0) (0, 1)) + (pt.effθ w) • ofv ![0, 0, 0, 0, 0, -(ωb / X * V0)])
    (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖u ⬝ᵥ
        ((DxC (smDx (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)) z + (pt.V0 * pt.effV w) •
        (smM1 (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) /
        2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pt.eth pt.V0)
          ((nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 6 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pt.eth pt.V0)
          ((nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (c.nHp R X ωb δ0 E0 V0)
            (thPolarAbs pt.eth pt.V0)) (nxeq R X δ0 E0
            V0, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) :=
  orbit_net_chart_unstable (hZ := hZ) (hΩ := hΩ) (hr := hr) (hu := hu) (hur := hur)
      (hsimple := hsimple) (hstab := hstab) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The dynamic network model in a fixed frame under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)`
of a port `pt` (grid-voltage and injected-current magnitude and angle), end-to-end, local
exponential orbital stability: `orbit_net_chart_exp_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_net_port_exp_stable
    (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) {r u : Fin 6 → ℂ}
    (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u)
    (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ a : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ a =
        ((Ω : ℂ) * I) • a → a = (u ⬝ᵥ a) • r)
    (hstab : ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ a = μ • a → μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    (pt : Port) (hpV : pt.V0 = V0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ)
    {z : Fin 6 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0)
        (nxeq R X δ0 E0 V0, V0) (0, 1)) + (pt.effθ w) • ofv ![0, 0, 0, 0, 0, -(ωb / X * V0)])
    (A0' : Matrix (Fin 6) (Fin 6) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)) z +
        (pt.V0 * pt.effV w) • (smM1 (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pt.eth pt.V0)
          ((nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 6 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pt.eth pt.V0)
            ((nxeq R X δ0 E0 V0, (0 :
            Fin 4 → ℝ)).1 + a,
          (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a))
              (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_net_chart_exp_stable (hZ := hZ) (hΩ := hΩ) (hr := hr) (hu := hu) (hur := hur)
      (hsimple := hsimple) (hstab := hstab) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- The dynamic network model in a fixed frame under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)`
of a port `pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end,
stability (all Floquet multipliers inside the unit circle): `orbit_net_chart_stable` with the
Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_net_pqv_stable
    (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) {r u : Fin 6 → ℂ}
    (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u)
    (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ a : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ a =
        ((Ω : ℂ) * I) • a → a = (u ⬝ᵥ a) • r)
    (hstab : ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ a = μ • a → μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 6 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0)
        (nxeq R X δ0 E0 V0, V0) (0, 1)) + (pq.effθ w) • ofv ![0, 0, 0, 0, 0, -(ωb / X * V0)])
    (A0' : Matrix (Fin 6) (Fin 6) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)) z +
        (pq.V0 * pq.effV w) • (smM1 (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pq.eth pq.V0)
          ((nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 6 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pq.eth pq.V0)
          ((nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (c.nHp R X ωb δ0 E0 V0)
              (thPolarAbs pq.eth pq.V0)) (nxeq R X δ0 E0 V0,
              0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_net_chart_stable (hZ := hZ) (hΩ := hΩ) (hr := hr) (hu := hu) (hur := hur)
      (hsimple := hsimple) (hstab := hstab) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The dynamic network model in a fixed frame under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)`
of a port `pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end,
parametric instability: `orbit_net_chart_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`,
`θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_net_pqv_unstable
    (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) {r u : Fin 6 → ℂ}
    (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u)
    (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ a : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ a =
        ((Ω : ℂ) * I) • a → a = (u ⬝ᵥ a) • r)
    (hstab : ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ a = μ • a → μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 6 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0)
        (nxeq R X δ0 E0 V0, V0) (0, 1)) + (pq.effθ w) • ofv ![0, 0, 0, 0, 0, -(ωb / X * V0)])
    (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖u ⬝ᵥ
        ((DxC (smDx (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)) z + (pq.V0 * pq.effV w) •
        (smM1 (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) /
        2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pq.eth pq.V0)
          ((nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 6 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pq.eth pq.V0)
          ((nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (c.nHp R X ωb δ0 E0 V0)
            (thPolarAbs pq.eth pq.V0)) (nxeq R X δ0 E0
            V0, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) :=
  orbit_net_chart_unstable (hZ := hZ) (hΩ := hΩ) (hr := hr) (hu := hu) (hur := hur)
      (hsimple := hsimple) (hstab := hstab) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- The dynamic network model in a fixed frame under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)`
of a port `pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end,
local exponential orbital stability: `orbit_net_chart_exp_stable` with the Thevenin amplitudes `V̂ =
V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_net_pqv_exp_stable
    (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) {r u : Fin 6 → ℂ}
    (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u)
    (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ a : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ a =
        ((Ω : ℂ) * I) • a → a = (u ⬝ᵥ a) • r)
    (hstab : ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ a = μ • a → μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    (pq : PQVPort) (hpV : pq.V0 = V0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {z : Fin 6 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0)
        (nxeq R X δ0 E0 V0, V0) (0, 1)) + (pq.effθ w) • ofv ![0, 0, 0, 0, 0, -(ωb / X * V0)])
    (A0' : Matrix (Fin 6) (Fin 6) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)) z +
        (pq.V0 * pq.effV w) • (smM1 (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pq.eth pq.V0)
          ((nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 6 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (c.nHp R X ωb δ0 E0 V0) (thPolarAbs pq.eth pq.V0)
            ((nxeq R X δ0 E0 V0, (0 :
            Fin 4 → ℝ)).1 + a,
          (nxeq R X δ0 E0 V0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a))
              (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_net_chart_exp_stable (hZ := hZ) (hΩ := hΩ) (hr := hr) (hu := hu) (hur := hur)
      (hsimple := hsimple) (hstab := hstab) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

end powerlib.GFM.VoltageModulation.DynQV
