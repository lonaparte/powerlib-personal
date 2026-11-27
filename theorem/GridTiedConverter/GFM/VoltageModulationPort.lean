import theorem.GridTiedConverter.GFM.VoltageModulationPhasor
import theorem.ParametricResonance.PortDisturbance

/-! # The GFM synchronizing core under port disturbances: voltage, current and power

A disturbance is an external source at the grid port (`ParametricResonance.PortDisturbance`): the
grid-voltage magnitude and angle, and either the magnitude and angle of an injected current (VI
chart) or the injected active and reactive power (PQV chart). The synchronizing core
(`VoltageModulation.Core`, general `C³` power map `P(δ, V)` of the Thevenin source) is driven by
the magnitude and the angle of the Thevenin source `e` at the port (`ppfield`); for a chart with
Thevenin amplitudes `(V̂, θ̂)`:
* the relative angle `z_δ = z_V,δ V̂ − S(s) θ̂`;
* the single modulated element `(P_f, δ)`: `ω_c(P_δδ z_δ + P_δV V̂)`;
* the pump `g = V̂ g_V + θ̂ g_θ` (`pump_phasor`).

Model boundary.
* `VoltageModulation.Core` with `P` the power for the Thevenin source behind the port impedance
  (with the power measured at the converter port this holds by `PortDisturbance.port_thevenin`);
  a chart `e` of class `C³` at `0`, `e(0) = V₀∠0`; Hopf point as in `VoltageModulationPhasor`,
  decay and detuning `εA₀'` of order `ε`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1–§2.2, §3 (VSG core); the
port disturbances are new.

Results.
* `ppfield`, `ppfield_eq_zero`, `contDiffAt_ppfield`, `matXV_ppfield_eq` — the core driven by a
  chart.
* `hz_ppfield`, `smA1V_ppfield` — the forced response and `A₁` of a chart disturbance.
* `orbit_chart_stable`, `orbit_chart_unstable`, `orbit_chart_exp_stable` — end-to-end Floquet
  statements and exponential stability for every chart.
* `orbit_port_stable`, `orbit_port_unstable` — the VI chart.
* `orbit_pqv_stable`, `orbit_pqv_unstable` — the PQV chart.

Corrections.
None: an extension.

Family and connection conclusions.
* The GFL counterpart is `GFL.Parametric.PortModulation`; the other GFM models are in
  `GFM.VoltageModulationPortVariants`.
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace Core
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv harm matXV smA1V smJV fderivWC gridSrc reparam
  linCV)
open powerlib.ParametricResonance.PortDisturbance (Port PQVPort thPolarAbs)

variable (c : Core)
variable {W : Type*} [Fintype W]

/-- The synchronizing core driven by a disturbance chart `e` (the Thevenin source at the port as a
function of the channels): `psfield` driven by the magnitude and the angle of `e`. -/
def ppfield (P : ℝ × ℝ → ℝ) (δ0 V0 : ℝ) (e : (W → ℝ) → ℂ) :
    (Fin 3 → ℝ) × (W → ℝ) → Fin 3 → ℝ :=
  reparam (c.psfield P (P (δ0, V0))) (thPolarAbs e V0)

variable {P : ℝ × ℝ → ℝ} {δ0 V0 : ℝ} {e : (W → ℝ) → ℂ}

omit [Fintype W] in
@[tmio M, powerlib_domain] theorem ppfield_eq_zero (h0 : e 0 = V0) (hV : 0 < V0) :
    c.ppfield P δ0 V0 e (sxeq P δ0 V0, 0) = 0 := by
  simp only [ppfield, reparam]
  rw [PortDisturbance.thPolarAbs_zero h0 hV.ne', c.psfield_eq_zero]

@[tmio M, powerlib_domain] theorem contDiffAt_ppfield (hP : ContDiff ℝ 3 P)
    (he : ContDiffAt ℝ 3 e 0) (h0 : e 0 = V0) (hV : 0 < V0) :
    ContDiffAt ℝ 3 (c.ppfield P δ0 V0 e) (sxeq P δ0 V0, 0) :=
  ForcedOrbit.contDiffAt_reparam ((c.contDiff_psfield hP _).contDiffAt)
    (PortDisturbance.contDiffAt_thPolarAbs he h0 hV)

@[tmio M, powerlib_domain] theorem matXV_ppfield_eq (hP : ContDiff ℝ 3 P)
    (he : ContDiffAt ℝ 3 e 0) (h0 : e 0 = V0) (hV : 0 < V0) (hPδ : Pd P (δ0, V0) = c.Pδ) :
    matXV (c.ppfield P δ0 V0 e) (sxeq P δ0 V0, 0) = c.A0r := by
  rw [ppfield, ForcedOrbit.matXV_reparam ((c.contDiff_psfield hP _).differentiable (by norm_num) _)
      ((PortDisturbance.contDiffAt_thPolarAbs he h0 hV).differentiableAt (by norm_num)),
    PortDisturbance.thPolarAbs_zero h0 hV.ne', c.matXV_psfield_eq hP hPδ]

/-- The forced response to a chart disturbance with Thevenin amplitudes `(V̂, θ̂)`. -/
@[tmio M, powerlib_domain] theorem hz_ppfield (hP : ContDiff ℝ 3 P) (he : ContDiffAt ℝ 3 e 0)
    (h0 : e 0 = V0) (hV : 0 < V0) {Ω : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV) {w : W → ℂ}
    {v θ : ℂ} (hvθ : linCV (fderiv ℝ (thPolarAbs e V0) 0) w = gridSrc v θ) :
    (((2 * Ω : ℝ) : ℂ) * I) • (c.forcedV (2 * Ω * I) v + c.forcedθ (2 * Ω * I) θ + θ • ofv eδ) -
        (matXV (c.ppfield P δ0 V0 e) (sxeq P δ0 V0, 0)).map (algebraMap ℝ ℂ) *ᵥ
          (c.forcedV (2 * Ω * I) v + c.forcedθ (2 * Ω * I) θ + θ • ofv eδ) =
      fderivWC (c.ppfield P δ0 V0 e) (sxeq P δ0 V0, 0) w := by
  have hd : DifferentiableAt ℝ (thPolarAbs e V0) 0 :=
    (PortDisturbance.contDiffAt_thPolarAbs he h0 hV).differentiableAt (by norm_num)
  rw [c.matXV_ppfield_eq hP he h0 hV hPδ, ppfield, ForcedOrbit.fderivWC_reparam
      ((c.contDiff_psfield hP _).differentiable (by norm_num) _) hd.hasFDerivAt,
    hvθ, PortDisturbance.thPolarAbs_zero h0 hV.ne', ← c.matXV_psfield_eq hP hPδ]
  exact c.hz_psfield hP hΩ hω0 hH hH1 hH2 hPδ hPV _ _

/-- `A₁` of a chart disturbance: the single element `(P_f, δ)` by `ω_c(P_δδ z_δ,rel + P_δV V̂)`. -/
@[tmio M, powerlib_domain] theorem smA1V_ppfield (hP : ContDiff ℝ 3 P) (he : ContDiffAt ℝ 3 e 0)
    (h0 : e 0 = V0) (hV : 0 < V0) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) {w : W → ℂ} {v θ : ℂ}
    (hvθ : linCV (fderiv ℝ (thPolarAbs e V0) 0) w = gridSrc v θ) (z : Fin 3 → ℂ) :
    smA1V (c.ppfield P δ0 V0 e) (sxeq P δ0 V0, 0) w (z + θ • ofv eδ) = c.A1 (z 0) v := by
  have hd : DifferentiableAt ℝ (thPolarAbs e V0) 0 :=
    (PortDisturbance.contDiffAt_thPolarAbs he h0 hV).differentiableAt (by norm_num)
  have hG : ContDiffAt ℝ 2 (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, thPolarAbs e V0 0) :=
    (c.contDiff_psfield (hP.of_le (by norm_num)) _).contDiffAt
  rw [ppfield, ForcedOrbit.smA1V_reparam hG ((PortDisturbance.contDiffAt_thPolarAbs he h0 hV).of_le
      (by norm_num)) hd.hasFDerivAt, hvθ, PortDisturbance.thPolarAbs_zero h0 hV.ne']
  exact c.smA1V_psfield hP hPδδ hPδV z _ _

/-- The GFM synchronizing core under a port disturbance `ŵ` of any chart with Thevenin amplitudes
`(V̂, θ̂)`, end-to-end, stability: at the Hopf point, `Re λ₁ < 0` and `|g/2| < |λ₁|` with
`g = l A₁(z_V,δ V̂ + z_θ,δ θ̂, V̂) r̄` give for all small `ε > 0` the forced orbit with all Floquet
multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_chart_stable (hP : ContDiff ℝ 3 P)
    (he : ContDiffAt ℝ 3 e 0)
    (h0 : e 0 = V0) (hV : 0 < V0) {Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hd2 : 0 < c.d2) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) {w : W → ℂ} {v θ : ℂ}
    (hvθ : linCV (fderiv ℝ (thPolarAbs e V0) 0) w = gridSrc v θ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) v + c.forcedθδ (2 * Ω * I) θ) v)
        (c.left (Ω * I)) (c.right (Ω * I)) / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.ppfield P δ0 V0 e (sxeq P δ0 V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.ppfield P δ0 V0 e (sxeq P δ0 V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : Fin 3 → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (c.ppfield P δ0 V0 e) (sxeq P δ0 V0, 0) w (2 * Ω)
            A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u →
            ‖μ‖ < 1 := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hm := c.matXV_ppfield_eq hP he h0 hV hPδ
  have hA1 := c.smA1V_ppfield hP he h0 hV hPδδ hPδV hvθ
    (c.forcedV (2 * Ω * I) v + c.forcedθ (2 * Ω * I) θ)
  rw [ParametricResonance.Element.pump] at hg
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_stable_vec
    (c.contDiffAt_ppfield hP he h0 hV) (c.ppfield_eq_zero h0 hV) hΩ (neg_neg_of_pos hd2)
    (by rw [hm]; exact hr) (by rw [hm]; exact hu) hur (by rw [hm]; exact hr3)
    (by rw [hm]; exact hu3) hur3 (c.hz_ppfield hP he h0 hV hΩ.ne' hω0 hH hH1 hH2 hPδ hPV hvθ) A0'
    hs ?_
  rw [hA1]
  exact hg

/-- The GFM synchronizing core under a chart disturbance, end-to-end, parametric instability:
`|λ₁| < |g/2|`. -/
@[tmio M, powerlib_domain] theorem orbit_chart_unstable (hP : ContDiff ℝ 3 P)
    (he : ContDiffAt ℝ 3 e 0)
    (h0 : e 0 = V0) (hV : 0 < V0) {Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hd2 : 0 < c.d2) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) {w : W → ℂ} {v θ : ℂ}
    (hvθ : linCV (fderiv ℝ (thPolarAbs e V0) 0) w = gridSrc v θ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) v + c.forcedθδ (2 * Ω * I) θ) v)
        (c.left (Ω * I)) (c.right (Ω * I)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.ppfield P δ0 V0 e (sxeq P δ0 V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.ppfield P δ0 V0 e (sxeq P δ0 V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (c.ppfield P δ0 V0 e) (sxeq P δ0 V0, 0) w
          (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hm := c.matXV_ppfield_eq hP he h0 hV hPδ
  have hA1 := c.smA1V_ppfield hP he h0 hV hPδδ hPδV hvθ
    (c.forcedV (2 * Ω * I) v + c.forcedθ (2 * Ω * I) θ)
  rw [ParametricResonance.Element.pump] at hg
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_unstable_vec
    (c.contDiffAt_ppfield hP he h0 hV) (c.ppfield_eq_zero h0 hV) hΩ (neg_neg_of_pos hd2)
    (by rw [hm]; exact hr) (by rw [hm]; exact hu) hur (by rw [hm]; exact hr3)
    (by rw [hm]; exact hu3) hur3 (c.hz_ppfield hP he h0 hV hΩ.ne' hω0 hH hH1 hH2 hPδ hPV hvθ) A0'
    ?_
  rw [hA1]
  exact hg

/-- The GFM synchronizing core under a chart disturbance, end-to-end with orbital stability. -/
@[tmio M, powerlib_domain] theorem orbit_chart_exp_stable (hP : ContDiff ℝ 3 P)
    (he : ContDiffAt ℝ 3 e 0)
    (h0 : e 0 = V0) (hV : 0 < V0) {Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hd2 : 0 < c.d2) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) {w : W → ℂ} {v θ : ℂ}
    (hvθ : linCV (fderiv ℝ (thPolarAbs e V0) 0) w = gridSrc v θ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) v + c.forcedθδ (2 * Ω * I) θ) v)
        (c.left (Ω * I)) (c.right (Ω * I)) / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (c.ppfield P δ0 V0 e (sxeq P δ0 V0 + y t,
        0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t a => c.ppfield P δ0 V0 e (sxeq P δ0 V0 + a,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hm := c.matXV_ppfield_eq hP he h0 hV hPδ
  have hA1 := c.smA1V_ppfield hP he h0 hV hPδδ hPδV hvθ
    (c.forcedV (2 * Ω * I) v + c.forcedθ (2 * Ω * I) θ)
  rw [ParametricResonance.Element.pump] at hg
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_three_stable_vec
    (c.contDiffAt_ppfield hP he h0 hV) (c.ppfield_eq_zero h0 hV) hΩ (neg_neg_of_pos hd2)
    (by rw [hm]; exact hr) (by rw [hm]; exact hu) hur (by rw [hm]; exact hr3)
    (by rw [hm]; exact hu3) hur3 (c.hz_ppfield hP he h0 hV hΩ.ne' hω0 hH hH1 hH2 hPδ hPV hvθ) A0'
    hs ?_
  rw [hA1]
  exact hg

/-! ### The voltage–current chart and the PQV chart -/

/-- The GFM synchronizing core under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)`, end-to-end,
stability. -/
@[tmio M, powerlib_domain] theorem orbit_port_stable (hP : ContDiff ℝ 3 P) (pt : Port)
    (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2) (hPδ : Pd P (δ0, pt.V0) = c.Pδ)
    (hPV : fderiv ℝ P (δ0, pt.V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, pt.V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, pt.V0) (0, 1) = c.PδV) (w : Fin 4 → ℂ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) (pt.V0 * pt.effV w) +
        c.forcedθδ (2 * Ω * I) (pt.effθ w)) (pt.V0 * pt.effV w))
        (c.left (Ω * I)) (c.right (Ω * I)) / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.ppfield P δ0 pt.V0 pt.eth (sxeq P δ0 pt.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.ppfield P δ0 pt.V0 pt.eth (sxeq P δ0 pt.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : Fin 3 → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (c.ppfield P δ0 pt.V0 pt.eth) (sxeq P δ0 pt.V0, 0) w
            (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ u =
            μ • u → ‖μ‖ < 1 :=
  c.orbit_chart_stable hP pt.contDiff_eth.contDiffAt hN hV hΩ hω0 hH hd2 hH1 hH2 hPδ hPV
    hPδδ hPδV (pt.linCV_polarAbs hN hV w) A0' hs hg

/-- The GFM synchronizing core under the VI port disturbance, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_port_unstable (hP : ContDiff ℝ 3 P) (pt : Port)
    (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2) (hPδ : Pd P (δ0, pt.V0) = c.Pδ)
    (hPV : fderiv ℝ P (δ0, pt.V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, pt.V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, pt.V0) (0, 1) = c.PδV) (w : Fin 4 → ℂ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) (pt.V0 * pt.effV w) +
        c.forcedθδ (2 * Ω * I) (pt.effθ w)) (pt.V0 * pt.effV w))
        (c.left (Ω * I)) (c.right (Ω * I)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.ppfield P δ0 pt.V0 pt.eth (sxeq P δ0 pt.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.ppfield P δ0 pt.V0 pt.eth (sxeq P δ0 pt.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (c.ppfield P δ0 pt.V0 pt.eth) (sxeq P δ0 pt.V0, 0) w
          (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) :=
  c.orbit_chart_unstable hP pt.contDiff_eth.contDiffAt hN hV hΩ hω0 hH hd2 hH1 hH2 hPδ hPV
    hPδδ hPδV (pt.linCV_polarAbs hN hV w) A0' hg

/-- The GFM synchronizing core under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)`, end-to-end,
stability. -/
@[tmio M, powerlib_domain] theorem orbit_pqv_stable (hP : ContDiff ℝ 3 P) (pq : PQVPort)
    (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2) (hPδ : Pd P (δ0, pq.V0) = c.Pδ)
    (hPV : fderiv ℝ P (δ0, pq.V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, pq.V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, pq.V0) (0, 1) = c.PδV) (w : Fin 4 → ℂ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) (pq.V0 * pq.effV w) +
        c.forcedθδ (2 * Ω * I) (pq.effθ w)) (pq.V0 * pq.effV w))
        (c.left (Ω * I)) (c.right (Ω * I)) / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.ppfield P δ0 pq.V0 pq.eth (sxeq P δ0 pq.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.ppfield P δ0 pq.V0 pq.eth (sxeq P δ0 pq.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : Fin 3 → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (c.ppfield P δ0 pq.V0 pq.eth) (sxeq P δ0 pq.V0, 0) w
            (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ u =
            μ • u → ‖μ‖ < 1 :=
  c.orbit_chart_stable hP pq.contDiff_eth.contDiffAt hN hV hΩ hω0 hH hd2 hH1 hH2 hPδ hPV
    hPδδ hPδV (pq.linCV_polarAbs hN hV hU w) A0' hs hg

/-- The GFM synchronizing core under the PQV port disturbance, end-to-end, parametric
instability. -/
@[tmio M, powerlib_domain] theorem orbit_pqv_unstable (hP : ContDiff ℝ 3 P) (pq : PQVPort)
    (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2) (hPδ : Pd P (δ0, pq.V0) = c.Pδ)
    (hPV : fderiv ℝ P (δ0, pq.V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, pq.V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, pq.V0) (0, 1) = c.PδV) (w : Fin 4 → ℂ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) (pq.V0 * pq.effV w) +
        c.forcedθδ (2 * Ω * I) (pq.effθ w)) (pq.V0 * pq.effV w))
        (c.left (Ω * I)) (c.right (Ω * I)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.ppfield P δ0 pq.V0 pq.eth (sxeq P δ0 pq.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.ppfield P δ0 pq.V0 pq.eth (sxeq P δ0 pq.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (c.ppfield P δ0 pq.V0 pq.eth) (sxeq P δ0 pq.V0, 0) w
          (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) :=
  c.orbit_chart_unstable hP pq.contDiff_eth.contDiffAt hN hV hΩ hω0 hH hd2 hH1 hH2 hPδ hPV
    hPδδ hPδV (pq.linCV_polarAbs hN hV hU w) A0' hg

end Core
end VoltageModulation
end powerlib.GFM
