import theorem.GridTiedConverter.GFM.PSCOrbit
import theorem.GridTiedConverter.GFM.DVOCOrbit
import theorem.GridTiedConverter.GFM.DroopVoltageOrbit
import theorem.GridTiedConverter.GFM.MatchingVoltageOrbit
import theorem.ParametricResonance.SmoothOrbitStability

/-! # Five grid-forming cores under voltage modulation: exponential stability of the forced orbit

For each of the five voltage-modulated cores (PSC, dVOC, synchronizing core with a general power
map, droop with two filters, matching control), the stable branch of the end-to-end Floquet
statement is strengthened to a statement about the nonlinear system: for all small `ε > 0` the
forced periodic orbit exists and every solution of the driven system that starts close to it
converges to it exponentially (`SmoothOrbitStability`).

Model boundary.
* The models, operating points and hypotheses of `PSCOrbit.orbit_voltage_stable_spec`,
  `DVOCOrbit.orbit_voltage_stable`, `VoltageModulationSmooth.orbit_smooth_stable`,
  `DroopVoltageOrbit.orbit_droop_stable` and `MatchingVoltageOrbit.orbit_matching_stable_spec`
  (quasi-static network, scalar voltage input `V₀ + εV̂ cos 2Ωt`, state perturbation `εA₀'`);
  deviation coordinates `x = state − x₀`.
* The generic statements need the field to be `C³` only near the operating point; for dVOC this is
  `v_dc ≠ 0`, which holds at `v_dc = 1`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.2, §3 (the five cores); the voltage excitation and the nonlinear stability
statement are new.

Results.
* `PSCFull.Model.orbit_voltage_exp_stable` — PSC (real four-state model, no stable basis among
  the hypotheses).
* `DVOCCore.orbit_voltage_exp_stable` — dVOC with a DC bus.
* `VoltageModulation.Core.orbit_smooth_exp_stable` — synchronizing (VSG) core, `C³` power map.
* `VoltageModulation.Droop.orbit_droop_exp_stable` — droop with two filters.
* `Matching.MatchingCore.orbit_matching_exp_stable` — matching control (no stable basis among
  the hypotheses).

Corrections.
None: an extension (local exponential stability of the actual forced orbit).

Family and connection conclusions.
None: static evidence on the voltage-modulated cores (local exponential stability of the forced
orbit).
-/

noncomputable section
open Filter Topology Set
open scoped Matrix.Norms.Operator

namespace powerlib.GFM.PSCFull.Model
open Complex ComplexConjugate Matrix
variable (p : Model)

/-- PSC: the forced orbit of the voltage-modulated real model exists and is locally exponentially
stable for the nonlinear system (hypotheses of `orbit_voltage_stable_spec`). -/
@[tmio M, powerlib_domain] theorem orbit_voltage_exp_stable (δ0 : ℝ) (hZ : p.Z ≠ 0)
    (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    (hD2 : (p.coeffs δ0).D (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    (h12 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h22 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS (p.Jreal δ0)
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP (p.rmode δ0 Ω) *
        ParametricResonance.ForcedOrbit.critQ (p.umode δ0 Ω))).map (algebraMap ℝ ℂ)) < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (p.shift δ0 Ω A0').re < 0)
    (hg : ‖p.pumpV δ0 Ω Vh / 2‖ ^ 2 < ‖p.shift δ0 Ω A0'‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (p.rfield (p.Peq δ0) (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t v => p.rfield (p.Peq δ0) (p.xeq δ0 + v, p.V + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hr, hu, hur⟩ := p.modes (p.Peq δ0) δ0 Ω hk h1 h2 hD hDd
  rw [p.matX_eq_Jreal] at hr hu
  obtain ⟨P, Q, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_eig (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      _ hsr
  have hz := p.zorb_eq (p.Peq δ0) δ0 Ω Vh hk hD2 h12 h22
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable
    (p.contDiff_rfield (p.Peq δ0)).contDiffAt (p.rfield_eq_zero δ0 hZ hZ0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As ?_ hsrs hz A0' ?_ ?_
  · rw [p.matX_eq_Jreal, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  · rw [hL, hR]; exact hs
  · rw [hL, hR, p.pump_rfield]; exact hg

end powerlib.GFM.PSCFull.Model

namespace powerlib.GFM.DVOCCore
open Complex Matrix
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)
variable (d : DVOCCore)

/-- dVOC: the forced orbit exists and is locally exponentially stable (hypotheses of
`orbit_voltage_stable`). -/
@[tmio M, powerlib_domain] theorem orbit_voltage_exp_stable {V0 Ψ0 K P2 τ νδ νP νK : ℝ}
    (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hP2 : HasDerivAt (deriv d.p) P2 Ψ0) (hτ : P2 = -(τ * K)) (hδ : d.η * K = νδ)
    (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (hV0 : V0 ≠ 0) (hi : νP < νδ) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)).re < 0)
    (hg : ‖-(I * ((Vh / V0 : ℝ) : ℂ) / (6 * νK)) * (numV νδ νP νK τ / denD νδ νP) / 2‖ ^ 2 <
      ‖left νδ νP νK ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ right νP νK)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / 2) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (d.rfieldV V0 (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t v => d.rfieldV V0 (xeq Ψ0 + v, V0 + ε * (Vh * Real.cos (2 * t))) + ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hm := d.matX_hopf hp hpe hP hδ hPn hKn hνK hkp hki hV0
  have hmc : (matX (d.rfieldV V0) (xeq Ψ0, V0)).map (algebraMap ℝ ℂ) =
      Linear.complexify (hopfMatrix νδ νP νK) := by rw [hm]
  have h := ParametricResonance.ForcedOrbit.smooth_orbit_exp_three_stable
    (d.contDiffAt_rfieldV V0 hp (by simp [xeq])) (rfieldV_eq_zero d hV0 hpe)
    (Ω := 1) (Vh := Vh) one_pos (l3 := νP - νδ) (by linarith)
    (by rw [hmc]; simpa using right_eig hνK) (by rw [hmc]; simpa using left_eig hνK)
    (left_right hνK) (by rw [hm]; exact right3_eig hνK) (by rw [hm]; exact left3_eig hνK)
    (left3_right3 hνK) (d.zorb_hopf hp hpe hP hδ hPn hKn hνK hkp hki hV0 Vh) A0' hs
    (by rw [d.pump_hopf hp hpe hP hP2 hτ hδ hPn hKn hνK hV0 Vh]; exact hg)
  simpa only [mul_one] using h

end powerlib.GFM.DVOCCore

namespace powerlib.GFM.VoltageModulation.Core
open Complex Matrix
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)
variable (c : Core)

/-- Synchronizing core with a general power map: the forced orbit exists and is locally
exponentially stable (hypotheses of `orbit_smooth_stable`). -/
@[tmio M, powerlib_domain] theorem orbit_smooth_exp_stable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2)
    (hPδ0 : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.gV V0 Ω Vh / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (c.sfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t v => c.sfield P (P (δ0, V0)) (sxeq P δ0 V0 + v, V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hm : matX (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) = c.A0r := by
    rw [c.matX_sfield hP, c.sjac_eq hPδ]
  have hp := c.pump_voltage_hopf V0 Ω Vh hPδ0 hV0 hH hΩ.ne' hd2.ne' hH1 hH2
  rw [ParametricResonance.Element.pump] at hp
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_three_stable
    (c.contDiff_sfield hP _).contDiffAt (c.sfield_eq_zero P δ0 V0) hΩ (neg_neg_of_pos hd2)
    (by rw [hm]; exact hr) (by rw [hm]; exact hu) hur (by rw [hm]; exact hr3)
    (by rw [hm]; exact hu3) hur3 (c.zorb_sfield hP hΩ.ne' hω0 hH hH1 hH2 hPδ hPV Vh) A0' hs ?_
  rw [c.smA1_sfield hP hPδδ hPδV]
  have e : c.forcedV (2 * Ω * I) Vh 0 = c.forcedVδ (2 * Ω * I) Vh := rfl
  rw [e, hp]; exact hg

end powerlib.GFM.VoltageModulation.Core

namespace powerlib.GFM.VoltageModulation.Droop
open Complex Matrix
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)
open Core (Pd contDiff_Pd hasDerivAt_P_line)
variable (mp ω1 ωm : ℝ)

/-- Droop with two filters: the forced orbit exists and is locally exponentially stable
(hypotheses of `orbit_droop_stable`). -/
@[tmio M, powerlib_domain] theorem orbit_droop_exp_stable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0)
    (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)).re < 0)
    (hg : ‖(core mp ω1 ωm Pδ PV Pδδ PδV).gV V0 Ω Vh / 2‖ ^ 2 <
      ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (dfield mp ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t v => dfield mp ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0 + v, V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hd2c, hr, hu, hur, hr3, hu3, hur3, hz, hp⟩ := droop_data mp ω1 ωm hP hΩ hmp hω1 hd2
    hPδ0 hV0 hH1 hH2 hPδ hPV hPδδ hPδV Vh
  exact ParametricResonance.ForcedOrbit.smooth_orbit_exp_three_stable
    (contDiff_dfield mp ω1 ωm hP _).contDiffAt (dfield_eq_zero mp ω1 ωm P δ0 V0) hΩ
    (neg_neg_of_pos hd2c) hr hu hur hr3 hu3 hur3 hz A0' hs (by rw [hp]; exact hg)

end powerlib.GFM.VoltageModulation.Droop

namespace powerlib.GFM.Matching.MatchingCore
open Complex Matrix
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)
open powerlib.GFM.VoltageModulation.Core (Pd contDiff_Pd hasDerivAt_P_line)
variable (d : MatchingCore)

/-- Matching control: the forced orbit exists and is locally exponentially stable (hypotheses of
`orbit_matching_stable_spec`). -/
@[tmio M, powerlib_domain] theorem orbit_matching_exp_stable {ixV : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 Ω K KV Kδδ KδV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0)
    (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K) (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV)
    (hKδδ : fderiv ℝ (Pd ixV) (δ0, V0) (1, 0) = Kδδ)
    (hKδV : fderiv ℝ (Pd ixV) (δ0, V0) (0, 1) = KδV)
    (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0) {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS (d.jacobian K)
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP r *
        ParametricResonance.ForcedOrbit.critQ u)).map (algebraMap ℝ ℂ)) < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖d.mpumpV u r K Kδδ KδV KV Ω Vh / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (d.mfield ixV (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t v => d.mfield ixV (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0 + v, V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hm : matX (d.mfield ixV (d.G + ixV (δ0, V0))) (d.meq ixV δ0 V0, V0) = d.jacobian K := by
    rw [d.matX_mfield hP]; simp [meq, hK]
  have h1 : 1 + (d.τ : ℂ) * (((2 * Ω : ℝ) : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hf := d.mforced_eq K KV hωb hωf hC hτ h1 hD2
  have hb : (fun i => ((fderiv ℝ (d.mfield ixV (d.G + ixV (δ0, V0))) (d.meq ixV δ0 V0, V0)
      (0, 1) i : ℝ) : ℂ)) = ![0, 0, -((KV : ℂ) / d.C), 0] := by
    rw [d.fderivW_mfield hP hKV]
    funext i; fin_cases i <;> simp
  have hz : (((2 * Ω : ℝ) : ℂ) * I) • ((Vh : ℂ) • d.mforced K KV (((2 * Ω : ℝ) : ℂ) * I)) -
      (matX (d.mfield ixV (d.G + ixV (δ0, V0))) (d.meq ixV δ0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ
        ((Vh : ℂ) • d.mforced K KV (((2 * Ω : ℝ) : ℂ) * I)) =
      (Vh : ℂ) • (fun i => ((fderiv ℝ (d.mfield ixV (d.G + ixV (δ0, V0)))
        (d.meq ixV δ0 V0, V0) (0, 1) i : ℝ) : ℂ)) := by
    rw [hm, hb, ← hf, smul_sub, Matrix.mulVec_smul, smul_comm]
  obtain ⟨P, Q, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_eig (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      _ hsr
  have hA0' : Q * matX (d.mfield ixV (d.G + ixV (δ0, V0))) (d.meq ixV δ0 V0, V0) * P =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable
    (d.contDiff_mfield hP _).contDiffAt (d.mfield_eq_zero ixV δ0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, d.pump_mfield hP hKδδ hKδV]; exact hg

end powerlib.GFM.Matching.MatchingCore
