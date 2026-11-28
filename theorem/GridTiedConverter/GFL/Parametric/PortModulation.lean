import theorem.GridTiedConverter.GFL.Parametric.GridModulation
import theorem.ParametricResonance.PortDisturbance

/-! # GFL converter under port disturbances: voltage, current and power, magnitude and angle

A disturbance is an external source at the grid port (`ParametricResonance.PortDisturbance`): the
grid-voltage magnitude and angle behind `jX_g`, and either the magnitude and angle of a current
injected at the PCC (VI chart) or the active and reactive power injected at the PCC (PQV chart).
The PLL and the dc-link power see the network only through the PCC voltage, i.e. through the
Thevenin source `e` at the PCC; the field is the field of `GridModulation` driven by the relative
magnitude and the angle of `e` (`pfield`). For a chart with Thevenin amplitudes `(v̂, θ̂)`:
* the forced response `z = v̂ z_V + θ̂ (z⁽¹⁾ + e₁)`;
* `A₁ = A₁^{(θ)}(v̂ z_V + θ̂ z⁽¹⁾) + v̂ A₀^{(V)}` on the five modulated elements;
* the pump `g = v̂ g_V + θ̂ g_θ`.

Model boundary.
* The GFL model of `AngleModulation`/`GridModulation`; a chart `e` of class `C³` at `0` with
  `e(0) = V₀∠0` (the Thevenin magnitude of the model). For the VI and PQV charts the grid impedance
  is `Z_g = jX_g`.
* The end-to-end statements at the Hopf point of the DVC mode with the decay and detuning `εA₀'`
  of order `ε`, as in `GridModulation`.

Source: slides "Hidden Instability of Grid-Following Converters Under Small Grid Angle
Variations" (KTH, 2026-11-27) (model); the port disturbances are new, in the form of technical
report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1.

Results.
* `pfield`, `contDiffAt_pfield`, `pfield_xs`, `matXV_pfield_xs` — the model driven by a chart.
* `hz_pfield`, `smA1V_pfield` — the forced response and `A₁` of a chart disturbance.
* `orbit_gfl_chart_stable`, `orbit_gfl_chart_unstable`, `orbit_gfl_chart_exp_stable` —
  end-to-end Floquet statements and exponential stability for every chart.
* `orbit_gfl_port_stable`, `orbit_gfl_port_unstable`, `orbit_gfl_port_exp_stable` — the VI chart
  (`Port.linCV_polar`).
* `orbit_gfl_pqv_stable`, `orbit_gfl_pqv_unstable`, `orbit_gfl_pqv_exp_stable` — the PQV chart
  (`PQVPort.linCV_polar`).

Corrections.
None: an extension.

Family and connection conclusions.
* The GFM counterparts are `GFM.VoltageModulationPort` (synchronizing core),
  `GFM.VoltageModulationPortVariants` and `GFM.VoltageModulationPortVariantsVIPQV`: the same charts
  and Thevenin amplitudes; the GFL converter modulates five elements, the GFM synchronizing core
  one.
-/

noncomputable section
namespace powerlib.GFL.Parametric.AngleModulation
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv harm matXV smA1V smJV fderivWC gridSrc reparam
  linCV)
open powerlib.ParametricResonance.PortDisturbance (Port PQVPort thPolar)
open scoped Matrix.Norms.Operator

namespace Params
variable (p : Params)
variable {W : Type*} [Fintype W]

/-- The GFL converter driven by a disturbance chart `e`, the Thevenin source at the PCC as a
function of the disturbance channels: the field of `GridModulation` driven by the relative
magnitude and the angle of `e`. -/
def pfield (e : (W → ℝ) → ℂ) : (Fin 4 → ℝ) × (W → ℝ) → Fin 4 → ℝ :=
  reparam p.gfield (thPolar e p.V0)

variable {e : (W → ℝ) → ℂ}

@[tmio M, powerlib_domain] theorem contDiffAt_pfield (he : ContDiffAt ℝ 3 e 0) (h0 : e 0 = p.V0)
    (hV : 0 < p.V0) : ContDiffAt ℝ 3 (p.pfield e) (p.xs, 0) := by
  refine ForcedOrbit.contDiffAt_reparam ?_ (PortDisturbance.contDiffAt_thPolar he h0 hV)
  rw [PortDisturbance.thPolar_zero h0 hV.ne']
  exact p.contDiffAt_gfield (by simp [xs])

omit [Fintype W] in
@[tmio M, powerlib_domain] theorem pfield_xs (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (h0 : e 0 = p.V0) (hV : 0 < p.V0) : p.pfield e (p.xs, 0) = 0 := by
  simp only [pfield, reparam]
  rw [PortDisturbance.thPolar_zero h0 hV.ne', p.gfield_xs hs]

@[tmio M, powerlib_domain] theorem matXV_pfield_xs (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (he : ContDiffAt ℝ 3 e 0) (h0 : e 0 = p.V0) (hV : 0 < p.V0) :
    matXV (p.pfield e) (p.xs, 0) = p.A0 := by
  have h00 := PortDisturbance.thPolar_zero h0 hV.ne'
  rw [pfield, ForcedOrbit.matXV_reparam (by
      rw [h00]; exact (p.contDiffAt_gfield (n := 1) (by simp [xs])).differentiableAt (by norm_num))
      ((PortDisturbance.contDiffAt_thPolar he h0 hV).differentiableAt (by norm_num)),
    h00, p.matXV_gfield_xs hs]

/-- The forced response to a disturbance `ŵ` of a chart with Thevenin amplitudes `(v̂, θ̂)`. -/
@[tmio M, powerlib_domain] theorem hz_pfield (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (he : ContDiffAt ℝ 3 e 0) (h0 : e 0 = p.V0) (hV : 0 < p.V0) {ω : ℝ}
    (hD : p.Dg (ω * I) ≠ 0) {w : W → ℂ} {v θ : ℂ}
    (hvθ : linCV (fderiv ℝ (thPolar e p.V0) 0) w = gridSrc v θ) :
    ((ω : ℂ) * I) • (v • p.zv (ω * I) + θ • (p.zc (ω * I) + e0c)) -
        (matXV (p.pfield e) (p.xs, 0)).map (algebraMap ℝ ℂ) *ᵥ
          (v • p.zv (ω * I) + θ • (p.zc (ω * I) + e0c)) =
      fderivWC (p.pfield e) (p.xs, 0) w := by
  have h00 := PortDisturbance.thPolar_zero h0 hV.ne'
  have hd : DifferentiableAt ℝ (thPolar e p.V0) 0 :=
    (PortDisturbance.contDiffAt_thPolar he h0 hV).differentiableAt (by norm_num)
  rw [p.matXV_pfield_xs hs he h0 hV, pfield, ForcedOrbit.fderivWC_reparam (by
      rw [h00]; exact (p.contDiffAt_gfield (n := 1) (by simp [xs])).differentiableAt (by norm_num))
      hd.hasFDerivAt, hvθ, h00, ← p.matXV_gfield_xs hs]
  exact p.hz_gfield hs hD _ _

/-- `A₁` of a chart disturbance: `A₁ = A₁^{(θ)}(z_rel) + v̂ A₀^{(V)}`. -/
@[tmio M, powerlib_domain] theorem smA1V_pfield (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (he : ContDiffAt ℝ 3 e 0) (h0 : e 0 = p.V0) (hV : 0 < p.V0) {w : W → ℂ} {v θ : ℂ}
    (hvθ : linCV (fderiv ℝ (thPolar e p.V0) 0) w = gridSrc v θ) (z : Fin 4 → ℂ) :
    smA1V (p.pfield e) (p.xs, 0) w (z + θ • e0c) = p.gA1 z + v • p.A0V.map (algebraMap ℝ ℂ) := by
  have h00 := PortDisturbance.thPolar_zero h0 hV.ne'
  have hd : DifferentiableAt ℝ (thPolar e p.V0) 0 :=
    (PortDisturbance.contDiffAt_thPolar he h0 hV).differentiableAt (by norm_num)
  rw [pfield, ForcedOrbit.smA1V_reparam (by rw [h00]; exact p.contDiffAt_gfield (by simp [xs]))
      ((PortDisturbance.contDiffAt_thPolar he h0 hV).of_le (by norm_num)) hd.hasFDerivAt, hvθ, h00]
  exact p.smA1V_gfield hs z _ _


/-- The GFL converter under a port disturbance `ŵ` of any chart with Thevenin amplitudes
`(v̂, θ̂)` (voltage or current magnitude and angle, active and reactive power), end-to-end,
stability: at the Hopf point of `A₀`, `Re λ₁ < 0` and `|g/2| < |λ₁|` with
`g = l [A₁^{(θ)}(v̂ z_V + θ̂ z⁽¹⁾) + v̂ A₀^{(V)}] r̄` give for all small `ε > 0` the forced orbit
with all Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_chart_stable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (he : ContDiffAt ℝ 3 e 0) (h0 : e 0 = p.V0)
    (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ (thPolar e p.V0) 0) w = gridSrc v θ)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + v • p.A0V.map (algebraMap ℝ ℂ)) *ᵥ
        star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.pfield e ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.pfield e ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : Fin 4 → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (p.pfield e) (p.xs, 0) w (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u → ‖μ‖ < 1 := by
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matXV (p.pfield e) (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matXV_pfield_xs hsd he h0 hV, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_pfield hsd he h0 hV (ω := 2 * Ω) hD2 hvθ
  have hzeq : v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • (p.zc (((2 * Ω : ℝ) : ℂ) * I) + e0c) =
      (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + θ • e0c := by
    rw [smul_add]; abel
  rw [hzeq] at hz
  have hA1 := p.smA1V_pfield hsd he h0 hV hvθ
    (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I))
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable_vec
    (p.contDiffAt_pfield he h0 hV) (p.pfield_xs hsd h0 hV) (by positivity : (0 : ℝ) < 2 * Ω) hPQ
    hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hLm, hRm]; exact hs
  · rw [hLm, hRm, hA1]; exact hg

/-- The GFL converter under a chart disturbance, end-to-end, parametric instability:
`|λ₁| < |g/2|`. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_chart_unstable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (he : ContDiffAt ℝ 3 e 0) (h0 : e 0 = p.V0)
    (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ (thPolar e p.V0) 0) w = gridSrc v θ)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + v • p.A0V.map (algebraMap ℝ ℂ)) *ᵥ
        star (p.gright (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.pfield e ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.pfield e ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (p.pfield e) (p.xs, 0) w (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matXV (p.pfield e) (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matXV_pfield_xs hsd he h0 hV, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_pfield hsd he h0 hV (ω := 2 * Ω) hD2 hvθ
  have hzeq : v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • (p.zc (((2 * Ω : ℝ) : ℂ) * I) + e0c) =
      (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + θ • e0c := by
    rw [smul_add]; abel
  rw [hzeq] at hz
  have hA1 := p.smA1V_pfield hsd he h0 hV hvθ
    (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I))
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable_vec
    (p.contDiffAt_pfield he h0 hV) (p.pfield_xs hsd h0 hV) (by positivity : (0 : ℝ) < 2 * Ω) hPQ
    hQP As hA0' hsrs hz A0' ?_
  rw [hLm, hRm, hA1]; exact hg

/-- The GFL converter under a chart disturbance, end-to-end with orbital stability: in the
stable case the forced orbit is locally exponentially stable. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_chart_exp_stable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (he : ContDiffAt ℝ 3 e 0) (h0 : e 0 = p.V0)
    (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ (thPolar e p.V0) 0) w = gridSrc v θ)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + v • p.A0V.map (algebraMap ℝ ℂ)) *ᵥ
        star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (p.pfield e ((p.xs, 0).1 + y t, (p.xs, 0).2 +
        ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => p.pfield e ((p.xs, 0).1 + a, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matXV (p.pfield e) (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matXV_pfield_xs hsd he h0 hV, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_pfield hsd he h0 hV (ω := 2 * Ω) hD2 hvθ
  have hzeq : v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • (p.zc (((2 * Ω : ℝ) : ℂ) * I) + e0c) =
      (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + θ • e0c := by
    rw [smul_add]; abel
  rw [hzeq] at hz
  have hA1 := p.smA1V_pfield hsd he h0 hV hvθ
    (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I))
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable_vec
    (p.contDiffAt_pfield he h0 hV) (p.pfield_xs hsd h0 hV) (by positivity : (0 : ℝ) < 2 * Ω) hPQ
    hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hLm, hRm]; exact hs
  · rw [hLm, hRm, hA1]; exact hg

/-! ### The voltage–current chart and the PQV chart -/

/-- The GFL converter under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` (grid-voltage magnitude
and angle, injected-current magnitude and angle) of a port `pt` with `Z_g = jX_g` and the
Thevenin magnitude `V₀` of the model, end-to-end, stability. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_port_stable (pt : Port) (hV0 : pt.V0 = p.V0)
    (hN : pt.eth 0 = pt.V0)
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hC : p.C ≠ 0) (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (w : Fin 4 → ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (pt.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        pt.effθ w • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + pt.effV w •
        p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.pfield pt.eth ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.pfield pt.eth ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : Fin 4 → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (p.pfield pt.eth) (p.xs, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u → ‖μ‖ < 1 := by
  have hvθ := pt.linCV_polar hN (hV0 ▸ hV) w
  rw [hV0] at hvθ
  exact p.orbit_gfl_chart_stable hsd pt.contDiff_eth.contDiffAt (by rw [hN, hV0]) hV hΩ hC
    hki hL hA hB h3 hq hvθ A0' hs hg

/-- The GFL converter under the VI port disturbance, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_port_unstable (pt : Port) (hV0 : pt.V0 = p.V0)
    (hN : pt.eth 0 = pt.V0)
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hC : p.C ≠ 0) (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (w : Fin 4 → ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (pt.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        pt.effθ w • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + pt.effV w •
        p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star (p.gright (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.pfield pt.eth ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.pfield pt.eth ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (p.pfield pt.eth) (p.xs, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hvθ := pt.linCV_polar hN (hV0 ▸ hV) w
  rw [hV0] at hvθ
  exact p.orbit_gfl_chart_unstable hsd pt.contDiff_eth.contDiffAt (by rw [hN, hV0]) hV hΩ
    hC hki hL hA hB h3 hq hvθ A0' hg

/-- The GFL converter under the VI port disturbance, end-to-end with local exponential orbital
stability of the forced orbit. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_port_exp_stable (pt : Port) (hV0 : pt.V0 = p.V0)
    (hN : pt.eth 0 = pt.V0)
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hC : p.C ≠ 0) (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (w : Fin 4 → ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (pt.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        pt.effθ w • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + pt.effV w •
        p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (p.pfield pt.eth ((p.xs, 0).1 + y t, (p.xs, 0).2 +
        ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => p.pfield pt.eth ((p.xs, 0).1 + a, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hvθ := pt.linCV_polar hN (hV0 ▸ hV) w
  rw [hV0] at hvθ
  exact p.orbit_gfl_chart_exp_stable hsd pt.contDiff_eth.contDiffAt (by rw [hN, hV0]) hV hΩ hC
    hki hL hA hB h3 hq hvθ A0' hs hg

/-- The GFL converter under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` (grid-voltage magnitude
and angle, injected active and reactive power) of a port `pq` with `Z_g = jX_g`, end-to-end,
stability. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_pqv_stable (pq : PQVPort) (hV0 : pq.V0 = p.V0)
    (hN : pq.eth 0 = pq.V0) (hU : pq.U0 ≠ 0)
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hC : p.C ≠ 0) (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (w : Fin 4 → ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (pq.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        pq.effθ w • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + pq.effV w •
        p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.pfield pq.eth ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.pfield pq.eth ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : Fin 4 → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (p.pfield pq.eth) (p.xs, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u → ‖μ‖ < 1 := by
  have hvθ := pq.linCV_polar hN (hV0 ▸ hV) hU w
  rw [hV0] at hvθ
  exact p.orbit_gfl_chart_stable hsd pq.contDiff_eth.contDiffAt (by rw [hN, hV0]) hV hΩ hC
    hki hL hA hB h3 hq hvθ A0' hs hg

/-- The GFL converter under the PQV port disturbance, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_pqv_unstable (pq : PQVPort) (hV0 : pq.V0 = p.V0)
    (hN : pq.eth 0 = pq.V0) (hU : pq.U0 ≠ 0)
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hC : p.C ≠ 0) (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (w : Fin 4 → ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (pq.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        pq.effθ w • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + pq.effV w •
        p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star (p.gright (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.pfield pq.eth ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.pfield pq.eth ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (p.pfield pq.eth) (p.xs, 0) w (2 * Ω) A0'
          ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hvθ := pq.linCV_polar hN (hV0 ▸ hV) hU w
  rw [hV0] at hvθ
  exact p.orbit_gfl_chart_unstable hsd pq.contDiff_eth.contDiffAt (by rw [hN, hV0]) hV hΩ
    hC hki hL hA hB h3 hq hvθ A0' hg

/-- The GFL converter under the PQV port disturbance, end-to-end with local exponential orbital
stability of the forced orbit. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_pqv_exp_stable (pq : PQVPort) (hV0 : pq.V0 = p.V0)
    (hN : pq.eth 0 = pq.V0) (hU : pq.U0 ≠ 0)
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hC : p.C ≠ 0) (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (w : Fin 4 → ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (pq.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        pq.effθ w • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + pq.effV w •
        p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (p.pfield pq.eth ((p.xs, 0).1 + y t, (p.xs, 0).2 +
        ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t a => p.pfield pq.eth ((p.xs, 0).1 + a, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hvθ := pq.linCV_polar hN (hV0 ▸ hV) hU w
  rw [hV0] at hvθ
  exact p.orbit_gfl_chart_exp_stable hsd pq.contDiff_eth.contDiffAt (by rw [hN, hV0]) hV hΩ hC
    hki hL hA hB h3 hq hvθ A0' hs hg

end Params
end powerlib.GFL.Parametric.AngleModulation
