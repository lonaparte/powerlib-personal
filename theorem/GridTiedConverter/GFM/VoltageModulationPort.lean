import theorem.GridTiedConverter.GFM.VoltageModulationPhasor
import theorem.ParametricResonance.PortDisturbance

/-! # The GFM synchronizing core under port disturbances: voltage and current, magnitude and angle

The four port disturbances of `ParametricResonance.PortDisturbance` applied to the GFM
synchronizing core (`VoltageModulation.Core`, general `C³` power map `P(δ, V)` of the Thevenin
source): the grid-source magnitude and angle (voltage type) and the magnitude and angle of a
current injected at the port (current type), with complex amplitudes `ŵ = (ê, θ̂, ι̂, φ̂)`. The core
is driven by the magnitude and the angle of the Thevenin source `e_th` at the port (`ppfield`), so
every port disturbance acts as the Thevenin disturbance `(V̂, θ̂_th) = (V₀ effV ŵ, effθ ŵ)`:
* the relative angle `z_δ = z_V,δ V̂ − S(s) θ̂_th`;
* the single modulated element `(P_f, δ)`: `ω_c(P_δδ z_δ + P_δV V̂)`;
* the pump `g = V̂ g_V + θ̂_th g_θ`.

Model boundary.
* `VoltageModulation.Core` with `P` the power for the Thevenin source behind the port impedance
  (for the lossless link `P = E V sin δ/(X_c + X_g)` with the injection at the port between `X_c`
  and `X_g`); the port normalized `e_th(0) = V₀∠0`; Hopf point as in `VoltageModulationPhasor`,
  decay and detuning `εA₀'` of order `ε`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1–§2.2, §3 (VSG core); the
port disturbances are new.

Results.
* `ppfield`, `ppfield_eq_zero`, `contDiffAt_ppfield`, `matXV_ppfield_eq` — the model.
* `hz_ppfield`, `smA1V_ppfield` — the forced response and `A₁` of the port disturbance.
* `orbit_port_stable`, `orbit_port_unstable` — end-to-end Floquet statements.
* `pump_port` — `g = effV ŵ · V₀ g_V + effθ ŵ · g_θ`.

Corrections.
None: an extension.

Family and connection conclusions.
* The GFL counterpart is `GFL.Parametric.PortModulation`: the same port map and Thevenin
  amplitudes; GFL modulates five elements, the GFM core one.
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace Core
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv harm matXV smA1V smJV fderivWC gridSrc reparam
  linCV)
open powerlib.ParametricResonance.PortDisturbance (Port)

variable (c : Core)

/-- The synchronizing core under the four port-disturbance channels `(ê, θ̂, ι̂, φ̂)`: the phasor
field `psfield` driven by the Thevenin source at the port, `(|e_th|, arg e_th)`. -/
def ppfield (P : ℝ × ℝ → ℝ) (δ0 : ℝ) (pt : Port) : (Fin 3 → ℝ) × (Fin 4 → ℝ) → Fin 3 → ℝ :=
  reparam (c.psfield P (P (δ0, pt.V0))) pt.polarAbs

variable {P : ℝ × ℝ → ℝ} {δ0 : ℝ} {pt : Port}

@[tmio M, powerlib_domain] theorem ppfield_eq_zero (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) :
    c.ppfield P δ0 pt (sxeq P δ0 pt.V0, 0) = 0 := by
  simp only [ppfield, reparam]
  rw [pt.polarAbs_zero hN hV.ne', c.psfield_eq_zero]

@[tmio M, powerlib_domain] theorem contDiffAt_ppfield (hP : ContDiff ℝ 3 P) (hN : pt.eth 0 = pt.V0)
    (hV : 0 < pt.V0) {n : WithTop ℕ∞} (hn : n ≤ 3) :
    ContDiffAt ℝ n (c.ppfield P δ0 pt) (sxeq P δ0 pt.V0, 0) :=
  ForcedOrbit.contDiffAt_reparam ((c.contDiff_psfield (hP.of_le hn) _).contDiffAt)
    (pt.contDiffAt_polarAbs hN hV)

@[tmio M, powerlib_domain] theorem matXV_ppfield_eq (hP : ContDiff ℝ 3 P) (hN : pt.eth 0 = pt.V0)
    (hV : 0 < pt.V0) (hPδ : Pd P (δ0, pt.V0) = c.Pδ) :
    matXV (c.ppfield P δ0 pt) (sxeq P δ0 pt.V0, 0) = c.A0r := by
  rw [ppfield, ForcedOrbit.matXV_reparam ((c.contDiff_psfield hP _).differentiable (by norm_num) _)
      ((pt.contDiffAt_polarAbs hN hV (n := 1)).differentiableAt (by norm_num)),
    pt.polarAbs_zero hN hV.ne', c.matXV_psfield_eq hP hPδ]

/-- The forced response to the port disturbance `ŵ`: the phasor response with
`V̂ = V₀ effV ŵ`, `θ̂_th = effθ ŵ`. -/
@[tmio M, powerlib_domain] theorem hz_ppfield (hP : ContDiff ℝ 3 P) (hN : pt.eth 0 = pt.V0)
    (hV : 0 < pt.V0) {Ω : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, pt.V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, pt.V0) (0, 1) = c.PV)
    (w : Fin 4 → ℂ) :
    (((2 * Ω : ℝ) : ℂ) * I) • (c.forcedV (2 * Ω * I) (pt.V0 * pt.effV w) +
        c.forcedθ (2 * Ω * I) (pt.effθ w) + pt.effθ w • ofv eδ) -
        (matXV (c.ppfield P δ0 pt) (sxeq P δ0 pt.V0, 0)).map (algebraMap ℝ ℂ) *ᵥ
          (c.forcedV (2 * Ω * I) (pt.V0 * pt.effV w) + c.forcedθ (2 * Ω * I) (pt.effθ w) +
            pt.effθ w • ofv eδ) =
      fderivWC (c.ppfield P δ0 pt) (sxeq P δ0 pt.V0, 0) w := by
  have hd : DifferentiableAt ℝ pt.polarAbs 0 :=
    (pt.contDiffAt_polarAbs hN hV (n := 1)).differentiableAt (by norm_num)
  rw [c.matXV_ppfield_eq hP hN hV hPδ, ppfield, ForcedOrbit.fderivWC_reparam
      ((c.contDiff_psfield hP _).differentiable (by norm_num) _) hd.hasFDerivAt,
    pt.linCV_polarAbs hN hV, pt.polarAbs_zero hN hV.ne', ← c.matXV_psfield_eq hP hPδ]
  exact c.hz_psfield hP hΩ hω0 hH hH1 hH2 hPδ hPV _ _

/-- `A₁` of the port disturbance: the single element `(P_f, δ)` modulated by
`ω_c(P_δδ z_δ,rel + P_δV V₀ effV ŵ)`. -/
@[tmio M, powerlib_domain] theorem smA1V_ppfield (hP : ContDiff ℝ 3 P) (hN : pt.eth 0 = pt.V0)
    (hV : 0 < pt.V0) (hPδδ : fderiv ℝ (Pd P) (δ0, pt.V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, pt.V0) (0, 1) = c.PδV) (w : Fin 4 → ℂ) (z : Fin 3 → ℂ) :
    smA1V (c.ppfield P δ0 pt) (sxeq P δ0 pt.V0, 0) w (z + pt.effθ w • ofv eδ) =
      c.A1 (z 0) (pt.V0 * pt.effV w) := by
  have hd : DifferentiableAt ℝ pt.polarAbs 0 :=
    (pt.contDiffAt_polarAbs hN hV (n := 1)).differentiableAt (by norm_num)
  have hG : ContDiffAt ℝ 2 (c.psfield P (P (δ0, pt.V0))) (sxeq P δ0 pt.V0, pt.polarAbs 0) :=
    (c.contDiff_psfield (hP.of_le (by norm_num)) _).contDiffAt
  rw [ppfield, ForcedOrbit.smA1V_reparam hG (pt.contDiffAt_polarAbs hN hV) hd.hasFDerivAt,
    pt.linCV_polarAbs hN hV, pt.polarAbs_zero hN hV.ne']
  exact c.smA1V_psfield hP hPδδ hPδV z _ _

/-- The GFM synchronizing core under the port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)`, end-to-end,
stability: at the Hopf point, `Re λ₁ < 0` and `|g/2| < |λ₁|` with
`g = l A₁(z_V,δ V̂ + z_θ,δ θ̂_th, V̂) r̄`, `V̂ = V₀ effV ŵ`, `θ̂_th = effθ ŵ`, give for all small
`ε > 0` the forced orbit with all Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_port_stable (hP : ContDiff ℝ 3 P)
    (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) {Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0)
    (hH : c.H ≠ 0) (hd2 : 0 < c.d2)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, pt.V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, pt.V0) (0, 1) = c.PV)
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
        ∀ t, HasDerivAt y (c.ppfield P δ0 pt (sxeq P δ0 pt.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.ppfield P δ0 pt (sxeq P δ0 pt.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : Fin 3 → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (c.ppfield P δ0 pt) (sxeq P δ0 pt.V0, 0) w (2 * Ω)
            A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u →
            ‖μ‖ < 1 := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hm := c.matXV_ppfield_eq hP hN hV hPδ
  have hA1 := c.smA1V_ppfield hP hN hV hPδδ hPδV w
    (c.forcedV (2 * Ω * I) (pt.V0 * pt.effV w) + c.forcedθ (2 * Ω * I) (pt.effθ w))
  rw [ParametricResonance.Element.pump] at hg
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_stable_vec
    (c.contDiffAt_ppfield hP hN hV le_rfl) (c.ppfield_eq_zero hN hV) hΩ (neg_neg_of_pos hd2)
    (by rw [hm]; exact hr) (by rw [hm]; exact hu) hur (by rw [hm]; exact hr3)
    (by rw [hm]; exact hu3) hur3
    (c.hz_ppfield hP hN hV hΩ.ne' hω0 hH hH1 hH2 hPδ hPV w) A0' hs ?_
  rw [hA1]
  exact hg

/-- The GFM synchronizing core under the port disturbance `ŵ`, end-to-end, parametric
instability: `|λ₁| < |g/2|`. -/
@[tmio M, powerlib_domain] theorem orbit_port_unstable (hP : ContDiff ℝ 3 P)
    (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) {Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0)
    (hH : c.H ≠ 0) (hd2 : 0 < c.d2)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, pt.V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, pt.V0) (0, 1) = c.PV)
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
        ∀ t, HasDerivAt y (c.ppfield P δ0 pt (sxeq P δ0 pt.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.ppfield P δ0 pt (sxeq P δ0 pt.V0 + y t,
          0 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (c.ppfield P δ0 pt) (sxeq P δ0 pt.V0, 0) w
          (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hm := c.matXV_ppfield_eq hP hN hV hPδ
  have hA1 := c.smA1V_ppfield hP hN hV hPδδ hPδV w
    (c.forcedV (2 * Ω * I) (pt.V0 * pt.effV w) + c.forcedθ (2 * Ω * I) (pt.effθ w))
  rw [ParametricResonance.Element.pump] at hg
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_unstable_vec
    (c.contDiffAt_ppfield hP hN hV le_rfl) (c.ppfield_eq_zero hN hV) hΩ (neg_neg_of_pos hd2)
    (by rw [hm]; exact hr) (by rw [hm]; exact hu) hur (by rw [hm]; exact hr3)
    (by rw [hm]; exact hu3) hur3
    (c.hz_ppfield hP hN hV hΩ.ne' hω0 hH hH1 hH2 hPδ hPV w) A0' ?_
  rw [hA1]
  exact hg

/-- The GFM pump of the port disturbance over the channels: `g = V₀ effV ŵ · g_V + effθ ŵ · g_θ`
with the per-unit Thevenin pumps of `pump_phasor`. -/
@[tmio M, powerlib_domain] theorem pump_port (s l0 : ℂ) (hPδ : c.Pδ ≠ 0) (w : Fin 4 → ℂ) :
    Element.pump (c.A1 (c.forcedVδ s (pt.V0 * pt.effV w) + c.forcedθδ s (pt.effθ w))
        (pt.V0 * pt.effV w)) (c.left l0) (c.right l0) =
      pt.effV w * (pt.V0 * Element.pump (c.A1 (c.forcedVδ s 1) 1) (c.left l0) (c.right l0)) +
        pt.effθ w * Element.pump (c.A1 (c.forcedθδ s 1) 0) (c.left l0) (c.right l0) := by
  rw [c.pump_phasor s l0 _ _ hPδ]
  ring

end Core
end VoltageModulation
end powerlib.GFM
