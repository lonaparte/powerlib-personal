import theorem.GridTiedConverter.GFM.DroopVoltageOrbit
import theorem.GridTiedConverter.GFM.DVOCOrbit
import theorem.GridTiedConverter.GFM.PSCOrbit
import theorem.GridTiedConverter.GFM.MatchingVoltageOrbit
import theorem.GridTiedConverter.GFM.VoltageModulationQVOrbit
import theorem.GridTiedConverter.GFM.VoltageModulationQVFilter
import theorem.GridTiedConverter.GFM.VoltageModulationQVNetwork
import theorem.ParametricResonance.PortDisturbance

/-! # Every GFM model under port disturbances: voltage, current and power, magnitude and angle

`ParametricResonance.PortDisturbance` reduces every port disturbance (grid-voltage magnitude and
angle; injected-current magnitude and angle, or injected active and reactive power) to the
Thevenin amplitudes `(V̂, θ̂)` of its chart, and proves the end-to-end Floquet statements for every
grid-synchronized model. Here they are instantiated for every GFM model of the library that has
a voltage-modulation end-to-end theorem; each receives the disturbance of an arbitrary chart `Φ`
(`PortDisturbance.Port.linCV_polarAbs` for the VI chart, `PortDisturbance.PQVPort.linCV_polarAbs`
for the PQV chart). For the quasi-static models the angle enters through the relative angle
(`PortDisturbance.phasor`):
* `(2jΩ − A₀) z_rel = V̂ b_V − 2jΩθ̂ e_δ`;
* `A₁ = D_x(∂ₓG) z_rel + V̂ D_V(∂ₓG)`.
The dynamic network is written in a fixed frame driven by `V e^{jθ_g}` (`nfieldAbs`): the angle
forces the line equations, `b_θ = (0, …, 0, −ω_bV₀/X)`, and does not modulate the Jacobian.

Model boundary.
* The models, operating points, Hopf conditions and modal data of `DroopVoltageOrbit`,
  `DVOCOrbit`, `PSCOrbit`, `MatchingVoltageOrbit`, `VoltageModulationQVOrbit`,
  `VoltageModulationQVFilter` and `VoltageModulationQVNetwork`; the relative angle is the first
  state. The line currents of the network model are in the grid frame, which is the fixed frame at
  `θ_g = 0` (`nfieldAbs_slice`).
* A chart `Φ` of class `C³` at `0` with `Φ(0) = (V₀, 0)` and Thevenin amplitudes `(V̂, θ̂)`; the
  relative response `z` solves the forced equation; decay and detuning `εA₀'` of order `ε`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1–§2.2; the port
disturbances are new.

Results.
* `PortVariants.e3`, `PortVariants.e4`, `PortVariants.e5` — the relative angle.
* `Droop.dG`, `Droop.orbit_droop_chart_stable`, `Droop.orbit_droop_chart_unstable`,
  `Droop.orbit_droop_chart_exp_stable` — droop with two filters.
* `DVOCCore.orbit_dvoc_chart_stable`, `DVOCCore.orbit_dvoc_chart_unstable`,
  `DVOCCore.orbit_dvoc_chart_exp_stable` — dVOC.
* `PSCFull.Model.orbit_psc_chart_stable`, `PSCFull.Model.orbit_psc_chart_unstable`,
  `PSCFull.Model.orbit_psc_chart_exp_stable` — PSC with active damping.
* `MatchingCore.mG`, `MatchingCore.orbit_matching_chart_stable`,
  `MatchingCore.orbit_matching_chart_unstable`, `MatchingCore.orbit_matching_chart_exp_stable` —
  matching control.
* `DynQV.qG`, `DynQV.orbit_qv_chart_stable`, `DynQV.orbit_qv_chart_unstable`,
  `DynQV.orbit_qv_chart_exp_stable` — the dynamic Q–V loop.
* `DynQV.qGf`, `DynQV.orbit_qvf_chart_stable`, `DynQV.orbit_qvf_chart_unstable`,
  `DynQV.orbit_qvf_chart_exp_stable` — the filtered dynamic Q–V loop.
* `DynQV.nfieldAbs`, `DynQV.nfieldAbs_eq`, `DynQV.nfieldAbs_slice`, `DynQV.contDiff_nfieldAbs`,
  `DynQV.matXV_nfieldAbs`, `DynQV.fderivW_nfieldAbs_ang`, `DynQV.smMwV_nfieldAbs_ang`, `DynQV.nGp`,
  `DynQV.nHp`, `DynQV.orbit_net_chart_stable`, `DynQV.orbit_net_chart_unstable`,
  `DynQV.orbit_net_chart_exp_stable` — the dynamic network in a fixed frame.

Corrections.
None: an extension.

Family and connection conclusions.
* The synchronizing core is `VoltageModulationPort`; the GFL converter is
  `GFL.Parametric.PortModulation`. All models share the charts and the Thevenin amplitudes.
* The VI and PQV corollaries of every theorem here are in `VoltageModulationPortVariantsVIPQV`.
-/

noncomputable section

namespace powerlib.GFM.PortVariants

/-- The relative angle of a three-state model. -/
def e3 : Fin 3 → ℝ := ![1, 0, 0]
/-- The relative angle of a four-state model. -/
def e4 : Fin 4 → ℝ := ![1, 0, 0, 0]
/-- The relative angle of a five-state model. -/
def e5 : Fin 5 → ℝ := ![1, 0, 0, 0, 0]

end powerlib.GFM.PortVariants

/-! ### Droop with two filters -/

namespace powerlib.GFM.VoltageModulation.Droop
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam)
open Core (Pd)
open powerlib.GFM.PortVariants (e3)

variable (mp ω1 ωm : ℝ)

/-- The droop field at the operating point `P* = P(δ₀, V₀)`. -/
def dG (P : ℝ × ℝ → ℝ) (δ0 V0 : ℝ) : (Fin 3 → ℝ) × ℝ → Fin 3 → ℝ :=
  dfield mp ω1 ωm P (P (δ0, V0))

/-- The droop core with two filters under a port disturbance `ŵ` of any chart `Φ` with Thevenin
amplitudes `(V̂, θ̂)`, end-to-end, stability: at the Hopf point (`ω₁ω_m = Ω²`,
`m_pω₁ω_mP_δ = (ω₁ + ω_m)Ω²`), with the relative response `z` and
`g = u_d [D_x(∂ₓF) z + V̂ D_V(∂ₓF)] r̄_d`, `Re λ₁ < 0` and `|g/2| < |λ₁|` give for all small
`ε > 0` the forced orbit with all Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_droop_chart_stable {P : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z -
        (matX (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)).re < 0)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ ((DxC (smDx (dG mp ω1 ωm P δ0 V0)
        (dxeq P δ0 V0, V0)) z + v • (smM1 (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (dright mp ω1 ωm Pδ PV Pδδ PδV Ω)) / 2‖ ^ 2 <
      ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3) Φ
          ((dxeq P δ0 V0, (0 : W → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3) Φ
          ((dxeq P δ0 V0, (0 : W → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 3 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor
            (dG mp ω1 ωm P δ0 V0) e3) Φ) (dxeq P δ0 V0, 0) w (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 := by
  obtain ⟨hd2c, hr, hu, hur, hr3, hu3, hur3, -, -⟩ := droop_data mp ω1 ωm hP hΩ hmp hω1 hd2
    hPδ0 hV0 hH1 hH2 hPδ hPV hPδδ hPδV 0
  exact PortDisturbance.orbit_phasor_port_three_stable
    (contDiff_dfield mp ω1 ωm hP _).contDiffAt (dfield_eq_zero mp ω1 ωm P δ0 V0) e3 hΦ hΦ0 hvθ
    hΩ (neg_neg_of_pos hd2c) hr hu hur hr3 hu3 hur3 hz A0' hs hg

/-- The droop core with two filters under a chart disturbance, end-to-end, parametric
instability: `|λ₁| < |g/2|`. -/
@[tmio M, powerlib_domain] theorem orbit_droop_chart_unstable {P : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z -
        (matX (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2 <
      ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ ((DxC (smDx (dG mp ω1 ωm P δ0 V0)
        (dxeq P δ0 V0, V0)) z + v • (smM1 (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (dright mp ω1 ωm Pδ PV Pδδ PδV Ω)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3) Φ
          ((dxeq P δ0 V0, (0 : W → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3) Φ
          ((dxeq P δ0 V0, (0 : W → ℝ)).1 + y t, (dxeq P δ0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (dG mp ω1 ωm P δ0 V0) e3) Φ) (dxeq P δ0 V0, 0) w (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hd2c, hr, hu, hur, hr3, hu3, hur3, -, -⟩ := droop_data mp ω1 ωm hP hΩ hmp hω1 hd2
    hPδ0 hV0 hH1 hH2 hPδ hPV hPδδ hPδV 0
  exact PortDisturbance.orbit_phasor_port_three_unstable
    (contDiff_dfield mp ω1 ωm hP _).contDiffAt (dfield_eq_zero mp ω1 ωm P δ0 V0) e3 hΦ hΦ0 hvθ
    hΩ (neg_neg_of_pos hd2c) hr hu hur hr3 hu3 hur3 hz A0' hg


/-- The droop core with two filters under a chart disturbance, end-to-end with orbital stability. -/
@[tmio M, powerlib_domain] theorem orbit_droop_chart_exp_stable {P : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z -
        (matX (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)).re < 0)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ ((DxC (smDx (dG mp ω1 ωm P δ0 V0)
        (dxeq P δ0 V0, V0)) z + v • (smM1 (dG mp ω1 ωm P δ0 V0) (dxeq P δ0 V0, V0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (dright mp ω1 ωm Pδ PV Pδδ PδV Ω)) / 2‖ ^ 2 <
      ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3) Φ ((dxeq P δ0
          V0, (0 : W → ℝ)).1 + y t,
        (dxeq P δ0 V0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (dG mp ω1 ωm P δ0 V0) e3) Φ
            ((dxeq P δ0 V0, (0 : W → ℝ)).1 + a,
          (dxeq P δ0 V0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hd2c, hr, hu, hur, hr3, hu3, hur3, -, -⟩ := droop_data mp ω1 ωm hP hΩ hmp hω1 hd2
    hPδ0 hV0 hH1 hH2 hPδ hPV hPδδ hPδV 0
  exact PortDisturbance.orbit_phasor_port_three_exp_stable
    (contDiff_dfield mp ω1 ωm hP _).contDiffAt (dfield_eq_zero mp ω1 ωm P δ0 V0) e3 hΦ hΦ0 hvθ
    hΩ (neg_neg_of_pos hd2c) hr hu hur hr3 hu3 hur3 hz A0' hs hg

end powerlib.GFM.VoltageModulation.Droop

/-! ### dVOC -/

namespace powerlib.GFM.DVOCCore
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam)
open powerlib.GFM.PortVariants (e3)

variable (d : DVOCCore)

/-- The dVOC core under a port disturbance `ŵ` of any chart `Φ` with Thevenin amplitudes
`(V̂, θ̂)`, end-to-end, stability (Hopf point normalized to `Ω = 1`, drive at `2`). -/
@[tmio M, powerlib_domain] theorem orbit_dvoc_chart_stable {V0 Ψ0 K νδ νP νK : ℝ}
    (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hδ : d.η * K = νδ) (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (hV0 : V0 ≠ 0) (hi : νP < νδ)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 3 → ℂ}
    (hz : (((2 * 1 : ℝ) : ℂ) * I) • z -
        (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1)) -
        ((((2 * 1 : ℝ) : ℂ) * I) * θ) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)).re < 0)
    (hg : ‖left νδ νP νK ⬝ᵥ ((DxC (smDx (d.rfieldV V0) (xeq Ψ0, V0)) z +
        v • (smM1 (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (right νP νK)) /
        2‖ ^ 2 < ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3) Φ
          ((xeq Ψ0, (0 : W → ℝ)).1 + y t, (xeq Ψ0, (0 : W → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3) Φ
          ((xeq Ψ0, (0 : W → ℝ)).1 + y t, (xeq Ψ0, (0 : W → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 3 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor (d.rfieldV V0) e3)
            Φ) (xeq Ψ0, 0) w (2 * 1) A0' ε t (y t)) (2 * Real.pi / (2 * 1)) 0).map
            (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 := by
  have hm := d.matX_hopf hp hpe hP hδ hPn hKn hνK hkp hki hV0
  have hmc : (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) =
      Linear.complexify (hopfMatrix νδ νP νK) := by rw [hm]
  exact PortDisturbance.orbit_phasor_port_three_stable
    (d.contDiffAt_rfieldV V0 hp (by simp [xeq])) (rfieldV_eq_zero d hV0 hpe) e3 hΦ hΦ0 hvθ
    one_pos (l3 := νP - νδ) (by linarith)
    (by rw [hmc]; simpa using right_eig hνK) (by rw [hmc]; simpa using left_eig hνK)
    (left_right hνK) (by rw [hm]; exact right3_eig hνK) (by rw [hm]; exact left3_eig hνK)
    (left3_right3 hνK) hz A0' hs hg

/-- The dVOC core under a chart disturbance, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_dvoc_chart_unstable {V0 Ψ0 K νδ νP νK : ℝ}
    (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hδ : d.η * K = νδ) (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (hV0 : V0 ≠ 0) (hi : νP < νδ)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 3 → ℂ}
    (hz : (((2 * 1 : ℝ) : ℂ) * I) • z -
        (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1)) -
        ((((2 * 1 : ℝ) : ℂ) * I) * θ) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2 <
      ‖left νδ νP νK ⬝ᵥ ((DxC (smDx (d.rfieldV V0) (xeq Ψ0, V0)) z +
        v • (smM1 (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (right νP νK)) /
        2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3) Φ
          ((xeq Ψ0, (0 : W → ℝ)).1 + y t, (xeq Ψ0, (0 : W → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3) Φ
          ((xeq Ψ0, (0 : W → ℝ)).1 + y t, (xeq Ψ0, (0 : W → ℝ)).2 +
            ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (d.rfieldV V0) e3) Φ) (xeq Ψ0, 0) w (2 * 1) A0' ε t (y t)) (2 * Real.pi / (2 * 1)) := by
  have hm := d.matX_hopf hp hpe hP hδ hPn hKn hνK hkp hki hV0
  have hmc : (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) =
      Linear.complexify (hopfMatrix νδ νP νK) := by rw [hm]
  exact PortDisturbance.orbit_phasor_port_three_unstable
    (d.contDiffAt_rfieldV V0 hp (by simp [xeq])) (rfieldV_eq_zero d hV0 hpe) e3 hΦ hΦ0 hvθ
    one_pos (l3 := νP - νδ) (by linarith)
    (by rw [hmc]; simpa using right_eig hνK) (by rw [hmc]; simpa using left_eig hνK)
    (left_right hνK) (by rw [hm]; exact right3_eig hνK) (by rw [hm]; exact left3_eig hνK)
    (left3_right3 hνK) hz A0' hg


/-- The dVOC core under a chart disturbance, end-to-end with orbital stability. -/
@[tmio M, powerlib_domain] theorem orbit_dvoc_chart_exp_stable {V0 Ψ0 K νδ νP νK : ℝ}
    (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hδ : d.η * K = νδ) (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (hV0 : V0 ≠ 0) (hi : νP < νδ)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 3 → ℂ}
    (hz : (((2 * 1 : ℝ) : ℂ) * I) • z -
        (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (d.rfieldV V0) (xeq Ψ0, V0) (0, 1)) -
        ((((2 * 1 : ℝ) : ℂ) * I) * θ) • ofv e3)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)).re < 0)
    (hg : ‖left νδ νP νK ⬝ᵥ ((DxC (smDx (d.rfieldV V0) (xeq Ψ0, V0)) z +
        v • (smM1 (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (right νP νK)) /
        2‖ ^ 2 < ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * 1)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.rfieldV V0) e3) Φ ((xeq Ψ0, (0 : W →
          ℝ)).1 + y t,
        (xeq Ψ0, (0 : W → ℝ)).2 + ε • harm w (2 * 1) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (d.rfieldV V0) e3) Φ ((xeq
            Ψ0, (0 : W → ℝ)).1 + a,
          (xeq Ψ0, (0 : W → ℝ)).2 + ε • harm w (2 * 1) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hm := d.matX_hopf hp hpe hP hδ hPn hKn hνK hkp hki hV0
  have hmc : (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) =
      Linear.complexify (hopfMatrix νδ νP νK) := by rw [hm]
  exact PortDisturbance.orbit_phasor_port_three_exp_stable
    (d.contDiffAt_rfieldV V0 hp (by simp [xeq])) (rfieldV_eq_zero d hV0 hpe) e3 hΦ hΦ0 hvθ
    one_pos (l3 := νP - νδ) (by linarith)
    (by rw [hmc]; simpa using right_eig hνK) (by rw [hmc]; simpa using left_eig hνK)
    (left_right hνK) (by rw [hm]; exact right3_eig hνK) (by rw [hm]; exact left3_eig hνK)
    (left3_right3 hνK) hz A0' hs hg

end powerlib.GFM.DVOCCore

/-! ### PSC with active damping -/

namespace powerlib.GFM.PSCFull.Model
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam)
open powerlib.GFM.PortVariants (e4)

variable (p : Model)

/-- The PSC with active damping under a port disturbance `ŵ` of any chart `Φ` with Thevenin
amplitudes `(V̂, θ̂)`, end-to-end, stability, with the modal coordinates of `modal_rfield`. -/
@[tmio M, powerlib_domain] theorem orbit_psc_chart_stable (δ0 : ℝ) (hZ : p.Z ≠ 0)
    (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ}
    {As : Matrix (Fin 2) (Fin 2) ℝ} (hW : p.Jreal δ0 * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : p.umode δ0 Ω ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
      (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![p.V, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z -
        (matX (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (p.shift δ0 Ω A0').re < 0)
    (hg : ‖p.umode δ0 Ω ⬝ᵥ ((DxC (smDx (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)) z +
        v • (smM1 (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ)) *ᵥ
        star (p.rmode δ0 Ω)) / 2‖ ^ 2 < ‖p.shift δ0 Ω A0'‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4) Φ
          ((p.xeq δ0, (0 : W → ℝ)).1 + y t, (p.xeq δ0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4) Φ
          ((p.xeq δ0, (0 : W → ℝ)).1 + y t, (p.xeq δ0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 4 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor
            (p.rfield (p.Peq δ0)) e4) Φ) (p.xeq δ0, 0) w (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 := by
  obtain ⟨P, Q, hPQ, hQP, hA0, hL, hR⟩ :=
    p.modal_rfield (p.Peq δ0) δ0 hΩ hk h1 h2 hD hDd hW hWW huW hWr
  refine PortDisturbance.orbit_phasor_port_stable (p.contDiff_rfield (p.Peq δ0)).contDiffAt
    (p.rfield_eq_zero δ0 hZ hZ0) e4 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0
    hsr hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR]; exact hg

/-- The PSC with active damping under a chart disturbance, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_psc_chart_unstable (δ0 : ℝ) (hZ : p.Z ≠ 0)
    (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ}
    {As : Matrix (Fin 2) (Fin 2) ℝ} (hW : p.Jreal δ0 * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : p.umode δ0 Ω ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
      (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![p.V, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z -
        (matX (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖p.shift δ0 Ω A0'‖ ^ 2 <
      ‖p.umode δ0 Ω ⬝ᵥ ((DxC (smDx (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)) z +
        v • (smM1 (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ)) *ᵥ
        star (p.rmode δ0 Ω)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4) Φ
          ((p.xeq δ0, (0 : W → ℝ)).1 + y t, (p.xeq δ0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4) Φ
          ((p.xeq δ0, (0 : W → ℝ)).1 + y t, (p.xeq δ0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (p.rfield (p.Peq δ0)) e4) Φ) (p.xeq δ0, 0) w (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨P, Q, hPQ, hQP, hA0, hL, hR⟩ :=
    p.modal_rfield (p.Peq δ0) δ0 hΩ hk h1 h2 hD hDd hW hWW huW hWr
  refine PortDisturbance.orbit_phasor_port_unstable (p.contDiff_rfield (p.Peq δ0)).contDiffAt
    (p.rfield_eq_zero δ0 hZ hZ0) e4 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0
    hsr hz A0' ?_
  rw [hL, hR]; exact hg


/-- The PSC with active damping under a chart disturbance, end-to-end with orbital stability. -/
@[tmio M, powerlib_domain] theorem orbit_psc_chart_exp_stable (δ0 : ℝ) (hZ : p.Z ≠ 0)
    (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ}
    {As : Matrix (Fin 2) (Fin 2) ℝ} (hW : p.Jreal δ0 * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : p.umode δ0 Ω ᵥ* Wm.map (algebraMap ℝ ℂ) = 0)
    (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
      (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![p.V, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z -
        (matX (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (p.shift δ0 Ω A0').re < 0)
    (hg : ‖p.umode δ0 Ω ⬝ᵥ ((DxC (smDx (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)) z +
        v • (smM1 (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ)) *ᵥ
        star (p.rmode δ0 Ω)) / 2‖ ^ 2 < ‖p.shift δ0 Ω A0'‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4) Φ ((p.xeq δ0,
          (0 : W → ℝ)).1 + y t,
        (p.xeq δ0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (p.rfield (p.Peq δ0)) e4) Φ
            ((p.xeq δ0, (0 : W → ℝ)).1 + a,
          (p.xeq δ0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨P, Q, hPQ, hQP, hA0, hL, hR⟩ :=
    p.modal_rfield (p.Peq δ0) δ0 hΩ hk h1 h2 hD hDd hW hWW huW hWr
  refine PortDisturbance.orbit_phasor_port_exp_stable (p.contDiff_rfield (p.Peq δ0)).contDiffAt
    (p.rfield_eq_zero δ0 hZ hZ0) e4 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0
    hsr hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR]; exact hg

end powerlib.GFM.PSCFull.Model

/-! ### Matching control -/

namespace powerlib.GFM.Matching.MatchingCore
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam)
open powerlib.GFM.VoltageModulation.Core (Pd)
open powerlib.GFM.PortVariants (e4)

variable (d : MatchingCore)

/-- The matching field at the operating point `I* = G + i_x(δ₀, V₀)`. -/
def mG (ixV : ℝ × ℝ → ℝ) (δ0 V0 : ℝ) : (Fin 4 → ℝ) × ℝ → Fin 4 → ℝ :=
  d.mfield ixV (d.G + ixV (δ0, V0))

/-- Matching control under a port disturbance `ŵ` of any chart `Φ` with Thevenin amplitudes
`(V̂, θ̂)`, end-to-end, stability. -/
@[tmio M, powerlib_domain] theorem orbit_matching_chart_stable {ixV : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 ixV) {δ0 V0 Ω K KV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0)
    (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K)
    (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV) (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ}
    {As : Matrix (Fin 2) (Fin 2) ℝ} (hW : d.jacobian K * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : u ᵥ* Wm.map (algebraMap ℝ ℂ) = 0) (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
      (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z -
        (matX (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)) z +
        v • (smM1 (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) /
        2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4) Φ
          ((d.meq ixV δ0 V0, (0 : W → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4) Φ
          ((d.meq ixV δ0 V0, (0 : W → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 4 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor
            (d.mG ixV δ0 V0) e4) Φ) (d.meq ixV δ0 V0, 0) w (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 := by
  obtain ⟨-, P, Q, hPQ, hQP, hA0, hL, hR⟩ := d.matching_data hP hΩ hωb hωf hC hτ hK hKV hD2
    hr hu hur hW hWW huW hWr 0
  refine PortDisturbance.orbit_phasor_port_stable (d.contDiff_mfield hP _).contDiffAt
    (d.mfield_eq_zero ixV δ0 V0) e4 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0
    hsr hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR]; exact hg

/-- Matching control under a chart disturbance, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_matching_chart_unstable {ixV : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 ixV) {δ0 V0 Ω K KV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0)
    (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K)
    (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV) (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ}
    {As : Matrix (Fin 2) (Fin 2) ℝ} (hW : d.jacobian K * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : u ᵥ* Wm.map (algebraMap ℝ ℂ) = 0) (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
      (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z -
        (matX (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 <
      ‖u ⬝ᵥ ((DxC (smDx (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)) z +
        v • (smM1 (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) /
        2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4) Φ
          ((d.meq ixV δ0 V0, (0 : W → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4) Φ
          ((d.meq ixV δ0 V0, (0 : W → ℝ)).1 + y t, (d.meq ixV δ0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor
          (d.mG ixV δ0 V0) e4) Φ) (d.meq ixV δ0 V0, 0) w (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨-, P, Q, hPQ, hQP, hA0, hL, hR⟩ := d.matching_data hP hΩ hωb hωf hC hτ hK hKV hD2
    hr hu hur hW hWW huW hWr 0
  refine PortDisturbance.orbit_phasor_port_unstable (d.contDiff_mfield hP _).contDiffAt
    (d.mfield_eq_zero ixV δ0 V0) e4 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0
    hsr hz A0' ?_
  rw [hL, hR]; exact hg


/-- Matching control under a chart disturbance, end-to-end with orbital stability. -/
@[tmio M, powerlib_domain] theorem orbit_matching_chart_exp_stable {ixV : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 ixV) {δ0 V0 Ω K KV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0)
    (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K)
    (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV) (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {Wm : Matrix (Fin 4) (Fin 2) ℝ} {Wm' : Matrix (Fin 2) (Fin 4) ℝ}
    {As : Matrix (Fin 2) (Fin 2) ℝ} (hW : d.jacobian K * Wm = Wm * As) (hWW : Wm' * Wm = 1)
    (huW : u ᵥ* Wm.map (algebraMap ℝ ℂ) = 0) (hWr : Wm'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS As
      (2 * Real.pi / (2 * Ω))).map (algebraMap ℝ ℂ)) < 1)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z -
        (matX (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)) z +
        v • (smM1 (d.mG ixV δ0 V0) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r) /
        2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4) Φ ((d.meq ixV δ0 V0,
          (0 : W → ℝ)).1 + y t,
        (d.meq ixV δ0 V0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (d.mG ixV δ0 V0) e4) Φ
            ((d.meq ixV δ0 V0, (0 : W → ℝ)).1 + a,
          (d.meq ixV δ0 V0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨-, P, Q, hPQ, hQP, hA0, hL, hR⟩ := d.matching_data hP hΩ hωb hωf hC hτ hK hKV hD2
    hr hu hur hW hWW huW hWr 0
  refine PortDisturbance.orbit_phasor_port_exp_stable (d.contDiff_mfield hP _).contDiffAt
    (d.mfield_eq_zero ixV δ0 V0) e4 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0
    hsr hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR]; exact hg

end powerlib.GFM.Matching.MatchingCore

/-! ### Dynamic Q–V loop, its filtered version and the dynamic network -/

namespace powerlib.GFM.VoltageModulation.DynQV
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam
  matXV smMwV uMag uAng)
open powerlib.GFM.PortVariants (e4 e5)

variable (c : DynQV)

/-- The dynamic Q–V field at the operating point. -/
def qG (P Q : (ℝ × ℝ) × ℝ → ℝ) (δ0 E0 V0 : ℝ) : (Fin 4 → ℝ) × ℝ → Fin 4 → ℝ :=
  c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))

/-- The synchronizing core with a dynamic Q–V loop under a port disturbance `ŵ` of any chart
`Φ` with Thevenin amplitudes `(V̂, θ̂)`, end-to-end, stability. -/
@[tmio M, powerlib_domain] theorem orbit_qv_chart_stable {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3
    P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE)
    (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.left (Ω * I) ⬝ᵥ ((DxC (smDx (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)) z +
        v • (smM1 (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (c.right
            (Ω * I))) / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4) Φ
          ((qxeq P δ0 E0 V0, (0 : W → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4) Φ
          ((qxeq P δ0 E0 V0, (0 : W → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 4 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0)
              e4) Φ) (qxeq P δ0 E0 V0, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 := by
  have hm : matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [qG, c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  have hl := c.lag_ne hτ hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_eig (n := 4) (m := 2) rfl hΩ.ne'
      (c.right_eig hω0 hH hτ hl hF) (c.left_eig hω0 hH hτ hl hF) (c.left_right hω0 hH hl hFd) _
      hsr
  have hA0' : Qm * matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  refine PortDisturbance.orbit_phasor_port_stable (c.contDiff_qfield hP hQ _ _ _).contDiffAt
    (c.qfield_eq_zero P Q δ0 E0 V0) e4 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As
    hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR]; exact hg

/-- The dynamic Q–V core under a chart disturbance, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_qv_chart_unstable {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ
    3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE)
    (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ ((DxC (smDx (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)) z +
        v • (smM1 (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (c.right
            (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4) Φ
          ((qxeq P δ0 E0 V0, (0 : W → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4) Φ
          ((qxeq P δ0 E0 V0, (0 : W → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0
            V0) e4) Φ) (qxeq P δ0 E0 V0, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hm : matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [qG, c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  have hl := c.lag_ne hτ hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_eig (n := 4) (m := 2) rfl hΩ.ne'
      (c.right_eig hω0 hH hτ hl hF) (c.left_eig hω0 hH hτ hl hF) (c.left_right hω0 hH hl hFd) _
      hsr
  have hA0' : Qm * matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  refine PortDisturbance.orbit_phasor_port_unstable (c.contDiff_qfield hP hQ _ _ _).contDiffAt
    (c.qfield_eq_zero P Q δ0 E0 V0) e4 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As
    hA0' hsrs hz A0' ?_
  rw [hL, hR]; exact hg

/-- The dynamic Q–V core under a chart disturbance, end-to-end with orbital stability. -/
@[tmio M, powerlib_domain] theorem orbit_qv_chart_exp_stable {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff
    ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE)
    (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 4 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e4)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.left (Ω * I) ⬝ᵥ ((DxC (smDx (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)) z +
        v • (smM1 (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star (c.right
            (Ω * I))) / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4) Φ
          ((qxeq P δ0 E0 V0, (0 : W → ℝ)).1 + y t, (qxeq P δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (c.qG P Q δ0 E0 V0) e4) Φ
            ((qxeq P δ0 E0 V0, (0 : W → ℝ)).1 + a,
          (qxeq P δ0 E0 V0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hm : matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [qG, c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  have hl := c.lag_ne hτ hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_eig (n := 4) (m := 2) rfl hΩ.ne'
      (c.right_eig hω0 hH hτ hl hF) (c.left_eig hω0 hH hτ hl hF) (c.left_right hω0 hH hl hFd) _
      hsr
  have hA0' : Qm * matX (c.qG P Q δ0 E0 V0) (qxeq P δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  refine PortDisturbance.orbit_phasor_port_exp_stable (c.contDiff_qfield hP hQ _ _ _).contDiffAt
    (c.qfield_eq_zero P Q δ0 E0 V0) e4 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As
    hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR]; exact hg

/-- The filtered dynamic Q–V field at the operating point. -/
def qGf (ωq : ℝ) (P Q : (ℝ × ℝ) × ℝ → ℝ) (δ0 E0 V0 : ℝ) : (Fin 5 → ℝ) × ℝ → Fin 5 → ℝ :=
  c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))

/-- The synchronizing core with a filtered dynamic Q–V loop under a port disturbance `ŵ` of any
chart `Φ` with Thevenin amplitudes `(V̂, θ̂)`, end-to-end, stability. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_chart_stable (ωq : ℝ) {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE)
    (h2 : 0 < c.c2f ωq) (h0 : 0 < c.c0f ωq Ω)
    (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 5 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e5)
    (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hs : (c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))).re < 0)
    (hg : ‖c.leftf ωq (Ω * I) ⬝ᵥ ((DxC (smDx (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)) z +
        v • (smM1 (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star
            (c.rightf ωq (Ω * I))) / 2‖ ^ 2 <
      ‖c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5) Φ
          ((qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 5 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5) Φ
          ((qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 5 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0
              V0) e5) Φ) (qxeqf P Q δ0 E0 V0, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 := by
  have hm : matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0) = c.A0f ωq := by
    rw [qGf, c.matX_qfieldf ωq hP hQ, c.qjacf_eq ωq hPδ hPE hQδ hQE]
  obtain ⟨hF, hFd, -⟩ := c.hopff_facts ωq hτ hωq hΩ.ne' hR hA hB
  have hl := c.lagf_ne ωq hτ hωq hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR', hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 5) (m := 3) rfl hΩ.ne'
      (c.rightf_eig ωq hω0 hH hτ.ne' hl hF) (c.leftf_eig ωq hω0 hH hτ.ne' hl hF)
      (c.leftf_rightf ωq hω0 hH hl hFd) (c.hopff_simple ωq hω0 hH hτ hωq hΩ.ne' hFd)
      (fun μ v hv h h1 h2' => c.eigf_stable ωq hω0 hH hτ h2 h0 hR hA hB hv h h1 h2')
      (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  refine PortDisturbance.orbit_phasor_port_stable (c.contDiff_qfieldf ωq hP hQ _ _ _).contDiffAt
    (c.qfieldf_eq_zero ωq P Q δ0 E0 V0) e5 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As
    hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR']; exact hs
  · rw [hL, hR']; exact hg

/-- The filtered dynamic Q–V core under a chart disturbance, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_chart_unstable (ωq : ℝ) {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE)
    (h2 : 0 < c.c2f ωq) (h0 : 0 < c.c0f ωq Ω)
    (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 5 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e5)
    (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hg : ‖c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2 <
      ‖c.leftf ωq (Ω * I) ⬝ᵥ ((DxC (smDx (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)) z +
        v • (smM1 (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star
            (c.rightf ωq (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5) Φ
          ((qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 5 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5) Φ
          ((qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0
            E0 V0) e5) Φ) (qxeqf P Q δ0 E0 V0, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hm : matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0) = c.A0f ωq := by
    rw [qGf, c.matX_qfieldf ωq hP hQ, c.qjacf_eq ωq hPδ hPE hQδ hQE]
  obtain ⟨hF, hFd, -⟩ := c.hopff_facts ωq hτ hωq hΩ.ne' hR hA hB
  have hl := c.lagf_ne ωq hτ hωq hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR', hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 5) (m := 3) rfl hΩ.ne'
      (c.rightf_eig ωq hω0 hH hτ.ne' hl hF) (c.leftf_eig ωq hω0 hH hτ.ne' hl hF)
      (c.leftf_rightf ωq hω0 hH hl hFd) (c.hopff_simple ωq hω0 hH hτ hωq hΩ.ne' hFd)
      (fun μ v hv h h1 h2' => c.eigf_stable ωq hω0 hH hτ h2 h0 hR hA hB hv h h1 h2')
      (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  refine PortDisturbance.orbit_phasor_port_unstable (c.contDiff_qfieldf ωq hP hQ _ _ _).contDiffAt
    (c.qfieldf_eq_zero ωq P Q δ0 E0 V0) e5 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As
    hA0' hsrs hz A0' ?_
  rw [hL, hR']; exact hg

/-- The filtered dynamic Q–V core under a chart disturbance, end-to-end with orbital stability. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_chart_exp_stable (ωq : ℝ) {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE)
    (h2 : 0 < c.c2f ωq) (h0 : 0 < c.c0f ωq Ω)
    (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 5 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e5)
    (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hs : (c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))).re < 0)
    (hg : ‖c.leftf ωq (Ω * I) ⬝ᵥ ((DxC (smDx (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)) z +
        v • (smM1 (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star
            (c.rightf ωq (Ω * I))) / 2‖ ^ 2 <
      ‖c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5) Φ
          ((qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).1 + y t, (qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 5 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (PortDisturbance.phasor (c.qGf ωq P Q δ0 E0 V0) e5)
            Φ ((qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).1 + a,
          (qxeqf P Q δ0 E0 V0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s)
              →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hm : matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0) = c.A0f ωq := by
    rw [qGf, c.matX_qfieldf ωq hP hQ, c.qjacf_eq ωq hPδ hPE hQδ hQE]
  obtain ⟨hF, hFd, -⟩ := c.hopff_facts ωq hτ hωq hΩ.ne' hR hA hB
  have hl := c.lagf_ne ωq hτ hωq hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR', hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 5) (m := 3) rfl hΩ.ne'
      (c.rightf_eig ωq hω0 hH hτ.ne' hl hF) (c.leftf_eig ωq hω0 hH hτ.ne' hl hF)
      (c.leftf_rightf ωq hω0 hH hl hFd) (c.hopff_simple ωq hω0 hH hτ hωq hΩ.ne' hFd)
      (fun μ v hv h h1 h2' => c.eigf_stable ωq hω0 hH hτ h2 h0 hR hA hB hv h h1 h2')
      (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.qGf ωq P Q δ0 E0 V0) (qxeqf P Q δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  refine PortDisturbance.orbit_phasor_port_exp_stable (c.contDiff_qfieldf ωq hP hQ _ _ _).contDiffAt
    (c.qfieldf_eq_zero ωq P Q δ0 E0 V0) e5 hΦ hΦ0 hvθ (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As
    hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR']; exact hs
  · rw [hL, hR']; exact hg

end powerlib.GFM.VoltageModulation.DynQV

namespace powerlib.GFM.VoltageModulation.DynQV
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smJV harm DxC gridSrc reparam
  matXV smMwV uMag uAng)

variable (c : DynQV) (R X ωb : ℝ)

/-- The core with a dynamic Q–V loop behind a dynamic `R + jX` line in a fixed frame, driven by
the grid phasor `V e^{jθ_g}`: `(X/ω_b) i̇ = E e^{jδ} − V e^{jθ_g} − (R + jX) i`. -/
def nfieldAbs (Pset Eset Qset : ℝ) (q : (Fin 6 → ℝ) × (Fin 2 → ℝ)) : Fin 6 → ℝ :=
  ![c.ω0 * q.1 1,
    (Pset - q.1 2 - c.D * q.1 1) / (2 * c.H),
    c.ωc * (q.1 3 * (Real.cos (q.1 0) * q.1 4 + Real.sin (q.1 0) * q.1 5) - q.1 2),
    (Eset - q.1 3 - c.kq * (q.1 3 * (Real.sin (q.1 0) * q.1 4 - Real.cos (q.1 0) * q.1 5) - Qset)) /
      c.τ,
    ωb / X * (q.1 3 * Real.cos (q.1 0) - q.2 0 * Real.cos (q.2 1) - R * q.1 4 + X * q.1 5),
    ωb / X * (q.1 3 * Real.sin (q.1 0) - q.2 0 * Real.sin (q.2 1) - R * q.1 5 - X * q.1 4)]

/-- The fixed-frame model is the grid-frame model plus a state-independent grid term. -/
@[tmio M, powerlib_domain] theorem nfieldAbs_eq (Pset Eset Qset : ℝ)
    (q : (Fin 6 → ℝ) × (Fin 2 → ℝ)) :
    c.nfieldAbs R X ωb Pset Eset Qset q = c.nfield R X ωb Pset Eset Qset (q.1, q.2 0) +
      ![0, 0, 0, 0, ωb / X * (q.2 0 - q.2 0 * Real.cos (q.2 1)),
        -(ωb / X * (q.2 0 * Real.sin (q.2 1)))] := by
  funext i
  fin_cases i <;> simp [nfieldAbs, nfield] <;> ring

/-- At `θ_g = 0` the fixed-frame model is the grid-frame model. -/
@[tmio M, powerlib_domain] theorem nfieldAbs_slice (Pset Eset Qset : ℝ) (x : Fin 6 → ℝ) (V : ℝ) :
    c.nfieldAbs R X ωb Pset Eset Qset (x, ![V, 0]) = c.nfield R X ωb Pset Eset Qset (x, V) := by
  rw [c.nfieldAbs_eq]
  funext i; fin_cases i <;> simp

@[tmio M, powerlib_domain] theorem contDiff_nfieldAbs {n : WithTop ℕ∞} (Pset Eset Qset : ℝ) :
    ContDiff ℝ n (c.nfieldAbs R X ωb Pset Eset Qset) := by
  have h : c.nfieldAbs R X ωb Pset Eset Qset = fun q => c.nfield R X ωb Pset Eset Qset
      (q.1, q.2 0) + ![0, 0, 0, 0, ωb / X * (q.2 0 - q.2 0 * Real.cos (q.2 1)),
        -(ωb / X * (q.2 0 * Real.sin (q.2 1)))] := funext (c.nfieldAbs_eq R X ωb Pset Eset Qset)
  rw [h]
  have hw : ∀ k : Fin 2, ContDiff ℝ n fun q : (Fin 6 → ℝ) × (Fin 2 → ℝ) => q.2 k := fun k =>
    (contDiff_apply ℝ ℝ k).comp contDiff_snd
  have h1 : ContDiff ℝ n fun q : (Fin 6 → ℝ) × (Fin 2 → ℝ) =>
      c.nfield R X ωb Pset Eset Qset (q.1, q.2 0) :=
    (c.contDiff_nfield R X ωb Pset Eset Qset).comp (contDiff_fst.prodMk (hw 0))
  refine h1.add (contDiff_pi.2 fun i => ?_)
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const.mul ((hw 0).sub ((hw 0).mul (Real.contDiff_cos.comp (hw 1))))
  · exact (contDiff_const.mul ((hw 0).mul (Real.contDiff_sin.comp (hw 1)))).neg

/-- The Jacobian of the fixed-frame model is `njac` at every state and every grid angle. -/
@[tmio M, powerlib_domain] theorem matXV_nfieldAbs (Pset Eset Qset : ℝ)
    (q : (Fin 6 → ℝ) × (Fin 2 → ℝ)) :
    matXV (c.nfieldAbs R X ωb Pset Eset Qset) q = c.njac R X ωb (q.1, q.2 0) := by
  refine ParametricResonance.ForcedOrbit.matXV_of_line
    ((c.contDiff_nfieldAbs R X ωb (n := 1) _ _ _).differentiable (by norm_num) _) fun y => ?_
  have hd : DifferentiableAt ℝ (c.nfield R X ωb Pset Eset Qset) (q.1, q.2 0) :=
    (c.contDiff_nfield R X ωb (n := 1) _ _ _).differentiable (by norm_num) _
  have hl := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (ParametricResonance.ForcedOrbit.hasDerivAt_line (q.1, q.2 0) (y, 0)) (by simp)
  rw [← ParametricResonance.ForcedOrbit.matX_mulVec, c.matX_nfield] at hl
  have h2 := hl.add_const (![0, 0, 0, 0, ωb / X * (q.2 0 - q.2 0 * Real.cos (q.2 1)),
    -(ωb / X * (q.2 0 * Real.sin (q.2 1)))] : Fin 6 → ℝ)
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_def, c.nfieldAbs_eq]
  congr 2
  ext <;> simp

/-- The grid angle enters the line equations as the forcing `b_θ = (0, …, 0, −ω_b V₀/X)`. -/
@[tmio M, powerlib_domain] theorem fderivW_nfieldAbs_ang (Pset Eset Qset : ℝ) (x0 : Fin 6 → ℝ)
    (V0 : ℝ) :
    fderiv ℝ (c.nfieldAbs R X ωb Pset Eset Qset) (x0, ![V0, 0]) (0, uAng) =
      ![0, 0, 0, 0, 0, -(ωb / X * V0)] := by
  refine ParametricResonance.ForcedOrbit.fderivW_of_lineV
    ((c.contDiff_nfieldAbs R X ωb (n := 1) _ _ _).differentiable (by norm_num) _) uAng ?_
  have e : ∀ s : ℝ, ![V0, 0] + s • uAng = ![V0, s] := fun s => by
    funext k; fin_cases k <;> simp [uAng]
  simp only [e]
  have hs : HasDerivAt (fun s : ℝ => s) 1 0 := hasDerivAt_id 0
  have hg : HasDerivAt (fun s : ℝ => (![0, 0, 0, 0, ωb / X * (V0 - V0 * Real.cos s),
      -(ωb / X * (V0 * Real.sin s))] : Fin 6 → ℝ)) ![0, 0, 0, 0, 0, -(ωb / X * V0)] 0 := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · have h := ((hs.cos.const_mul V0).const_sub V0).const_mul (ωb / X)
      simpa [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff] using h
    · have h := ((hs.sin.const_mul V0).const_mul (ωb / X)).neg
      simp only [Real.cos_zero, mul_one] at h
      exact h
  have h := hg.const_add (c.nfield R X ωb Pset Eset Qset (x0, V0))
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show c.nfieldAbs R X ωb Pset Eset Qset (x0, ![V0, s]) = _
  rw [c.nfieldAbs_eq]
  simp

/-- The grid angle does not modulate the Jacobian: `D_θ(∂ₓH) = 0`. -/
@[tmio M, powerlib_domain] theorem smMwV_nfieldAbs_ang (Pset Eset Qset : ℝ) (x0 : Fin 6 → ℝ)
    (V0 : ℝ) : smMwV (c.nfieldAbs R X ωb Pset Eset Qset) (x0, ![V0, 0]) uAng = 0 := by
  refine ParametricResonance.ForcedOrbit.smMwV_of_line
    ((c.contDiff_nfieldAbs R X ωb (n := 2) _ _ _).contDiffAt) uAng
    (Jr := fun _ => c.njac R X ωb (x0, V0)) (Filter.Eventually.of_forall fun t => ?_)
    fun i j => ?_
  · rw [c.matXV_nfieldAbs]; simp [uAng]
  · simpa using hasDerivAt_const (0 : ℝ) (c.njac R X ωb (x0, V0) i j)

/-- The grid-frame network model at the operating point. -/
def nGp (δ0 E0 V0 : ℝ) : (Fin 6 → ℝ) × ℝ → Fin 6 → ℝ :=
  c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))

/-- The fixed-frame network model at the operating point. -/
def nHp (δ0 E0 V0 : ℝ) : (Fin 6 → ℝ) × (Fin 2 → ℝ) → Fin 6 → ℝ :=
  c.nfieldAbs R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))

/-- The core with a dynamic Q–V loop behind a dynamic line (fixed frame, grid phasor input)
under a port disturbance `ŵ` of any chart `Φ` with Thevenin amplitudes `(V̂, θ̂)`, end-to-end,
stability: the angle enters as the line forcing `θ̂ b_θ`, `D_θ(∂ₓH) = 0`. -/
@[tmio M, powerlib_domain] theorem orbit_net_chart_stable (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω)
    {r u : Fin 6 → ℂ} (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω
        : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u)
    (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ a : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ a =
      ((Ω : ℂ) * I) • a → a = (u ⬝ᵥ a) • r)
    (hstab : ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ a = μ • a →
      μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 6 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ
        ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) (0, 1)) + θ • ofv ![0, 0, 0,
          0, 0, -(ωb / X * V0)])
    (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)) z +
        v • (smM1 (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r)
            / 2‖ ^ 2 <
      ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) Φ
          ((nxeq R X δ0 E0 V0, (0 : W → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 6 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) Φ
          ((nxeq R X δ0 E0 V0, (0 : W → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (c.nHp R X ωb δ0 E0 V0) Φ) (nxeq R X δ0 E0 V0,
              0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 := by
  have hm : matX (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) = (c.njac R X ωb (nxeq R X δ0 E0
      V0, V0)) := c.matX_nfield R X ωb _ _ _ _
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 6) (m := 4) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hb := c.fderivW_nfieldAbs_ang R X ωb (lossyP R X ((δ0, E0), V0)) E0
    (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0) V0
  have hM := c.smMwV_nfieldAbs_ang R X ωb (lossyP R X ((δ0, E0), V0)) E0
    (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0) V0
  have hz' : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0,
      V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) (0, 1)) +
        θ • ofv (fderiv ℝ (c.nHp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, ![V0, 0]) (0, uAng)) := by
    rw [hm]; simp only [nHp]; rw [hb]; exact hz
  have hzero : θ • (smMwV (c.nHp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, ![V0, 0]) uAng).map
      (algebraMap ℝ ℂ) = 0 := by
    simp only [nHp]; rw [hM]; ext; simp
  have hHG : ∀ x V, (c.nHp R X ωb δ0 E0 V0) (x, ![V, 0]) = (c.nGp R X ωb δ0 E0 V0) (x, V) := fun x V
      => c.nfieldAbs_slice R X ωb _ _ _ x V
  refine PortDisturbance.orbit_slice_port_stable hHG (c.contDiff_nfieldAbs R X ωb _ _ _).contDiffAt
    (c.contDiff_nfield R X ωb _ _ _).contDiffAt (c.nfield_eq_zero R X ωb hZ δ0 E0 V0) hΦ hΦ0 hvθ
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz' A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, hzero, add_zero]; exact hg

/-- The dynamic network model under a chart disturbance, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_net_chart_unstable (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω :
    ℝ} (hΩ : 0 < Ω)
    {r u : Fin 6 → ℂ} (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω
        : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u)
    (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ a : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ a =
      ((Ω : ℂ) * I) • a → a = (u ⬝ᵥ a) • r)
    (hstab : ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ a = μ • a →
      μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 6 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ
        ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) (0, 1)) + θ • ofv ![0, 0, 0,
          0, 0, -(ωb / X * V0)])
    (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 <
      ‖u ⬝ᵥ ((DxC (smDx (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)) z +
        v • (smM1 (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r)
            / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) Φ
          ((nxeq R X δ0 E0 V0, (0 : W → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 6 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) Φ
          ((nxeq R X δ0 E0 V0, (0 : W → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam (c.nHp R X ωb δ0 E0 V0) Φ) (nxeq R X δ0 E0
            V0, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hm : matX (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) = (c.njac R X ωb (nxeq R X δ0 E0
      V0, V0)) := c.matX_nfield R X ωb _ _ _ _
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 6) (m := 4) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hb := c.fderivW_nfieldAbs_ang R X ωb (lossyP R X ((δ0, E0), V0)) E0
    (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0) V0
  have hM := c.smMwV_nfieldAbs_ang R X ωb (lossyP R X ((δ0, E0), V0)) E0
    (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0) V0
  have hz' : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0,
      V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) (0, 1)) +
        θ • ofv (fderiv ℝ (c.nHp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, ![V0, 0]) (0, uAng)) := by
    rw [hm]; simp only [nHp]; rw [hb]; exact hz
  have hzero : θ • (smMwV (c.nHp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, ![V0, 0]) uAng).map
      (algebraMap ℝ ℂ) = 0 := by
    simp only [nHp]; rw [hM]; ext; simp
  have hHG : ∀ x V, (c.nHp R X ωb δ0 E0 V0) (x, ![V, 0]) = (c.nGp R X ωb δ0 E0 V0) (x, V) := fun x V
      => c.nfieldAbs_slice R X ωb _ _ _ x V
  refine PortDisturbance.orbit_slice_port_unstable hHG (c.contDiff_nfieldAbs R X ωb _ _
      _).contDiffAt
    (c.contDiff_nfield R X ωb _ _ _).contDiffAt (c.nfield_eq_zero R X ωb hZ δ0 E0 V0) hΦ hΦ0 hvθ
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz' A0' ?_
  rw [hL, hR, hzero, add_zero]; exact hg

/-- The dynamic network model under a chart disturbance, end-to-end with orbital stability. -/
@[tmio M, powerlib_domain] theorem orbit_net_chart_exp_stable (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω
    : ℝ} (hΩ : 0 < Ω)
    {r u : Fin 6 → ℂ} (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω
        : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u)
    (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ a : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ a =
      ((Ω : ℂ) * I) • a → a = (u ⬝ᵥ a) • r)
    (hstab : ∀ (μ : ℂ) (a : Fin 6 → ℂ), a ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map
        (algebraMap ℝ ℂ) *ᵥ a = μ • a →
      μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    {W : Type*} [Fintype W] {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0)
    (hΦ0 : Φ 0 = ![V0, 0]) {w : W → ℂ} {v θ : ℂ}
    (hvθ : ForcedOrbit.linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {z : Fin 6 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ
        ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) (0, 1)) + θ • ofv ![0, 0, 0,
          0, 0, -(ωb / X * V0)])
    (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)) z +
        v • (smM1 (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)) *ᵥ star r)
            / 2‖ ^ 2 <
      ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (reparam (c.nHp R X ωb δ0 E0 V0) Φ
          ((nxeq R X δ0 E0 V0, (0 : W → ℝ)).1 + y t, (nxeq R X δ0 E0 V0, (0 : W → ℝ)).2 +
            ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 6 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (c.nHp R X ωb δ0 E0 V0) Φ ((nxeq R X δ0 E0 V0, (0 :
            W → ℝ)).1 + a,
          (nxeq R X δ0 E0 V0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hm : matX (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) = (c.njac R X ωb (nxeq R X δ0 E0
      V0, V0)) := c.matX_nfield R X ωb _ _ _ _
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 6) (m := 4) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hb := c.fderivW_nfieldAbs_ang R X ωb (lossyP R X ((δ0, E0), V0)) E0
    (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0) V0
  have hM := c.smMwV_nfieldAbs_ang R X ωb (lossyP R X ((δ0, E0), V0)) E0
    (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0) V0
  have hz' : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0,
      V0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ (c.nGp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, V0) (0, 1)) +
        θ • ofv (fderiv ℝ (c.nHp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, ![V0, 0]) (0, uAng)) := by
    rw [hm]; simp only [nHp]; rw [hb]; exact hz
  have hzero : θ • (smMwV (c.nHp R X ωb δ0 E0 V0) (nxeq R X δ0 E0 V0, ![V0, 0]) uAng).map
      (algebraMap ℝ ℂ) = 0 := by
    simp only [nHp]; rw [hM]; ext; simp
  have hHG : ∀ x V, (c.nHp R X ωb δ0 E0 V0) (x, ![V, 0]) = (c.nGp R X ωb δ0 E0 V0) (x, V) := fun x V
      => c.nfieldAbs_slice R X ωb _ _ _ x V
  refine PortDisturbance.orbit_slice_port_exp_stable hHG (c.contDiff_nfieldAbs R X ωb _ _
      _).contDiffAt
    (c.contDiff_nfield R X ωb _ _ _).contDiffAt (c.nfield_eq_zero R X ωb hZ δ0 E0 V0) hΦ hΦ0 hvθ
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz' A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, hzero, add_zero]; exact hg

end powerlib.GFM.VoltageModulation.DynQV
