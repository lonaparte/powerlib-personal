import theorem.GridTiedConverter.GFL.Parametric.GridModulation
import theorem.ParametricResonance.PortDisturbance

/-! # GFL converter under port disturbances: voltage and current, magnitude and angle

The four port disturbances of `ParametricResonance.PortDisturbance` applied to the GFL converter:
the grid-source magnitude and angle behind `jX_g` (voltage type) and the magnitude and angle of a
current injected at the PCC (current type), with complex amplitudes `ŵ = (ê, θ̂, ι̂, φ̂)` at the
drive frequency. The PLL and the dc-link power see the network only through the PCC voltage
`v_p = e_th + jX_g i`, i.e. through the Thevenin source `e_th = E e^{jθ_E} + jX_g J e^{jφ}`; the
field is the field of `GridModulation` driven by `e_th` (`pfield`). Every port disturbance acts as
the Thevenin disturbance `(v̂, θ̂_th) = (effV ŵ, effθ ŵ)`:
* the forced response `z = v̂ z_V + θ̂_th (z⁽¹⁾ + e₁)`;
* `A₁ = A₁^{(θ)}(v̂ z_V + θ̂_th z⁽¹⁾) + v̂ A₀^{(V)}` on the five modulated elements;
* the pump `g = v̂ g_V + θ̂_th g_θ`, over the channels `PortDisturbance.Port.pump_channels`.

Model boundary.
* The GFL model of `AngleModulation`/`GridModulation`; the port `gport` with `Z_g = jX_g` and the
  Thevenin magnitude `V₀` of the model, normalized `e_th(0) = V₀∠0` (`hN`).
* The end-to-end statements at the Hopf point of the DVC mode with the decay and detuning `εA₀'`
  of order `ε`, as in `GridModulation`.

Source: slides "Hidden Instability of Grid-Following Converters Under Small Grid Angle
Variations" (KTH, 2026-11-27) (model); the port disturbances are new, in the form of technical
report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1.

Results.
* `gport`, `pfield`, `contDiffAt_pfield`, `pfield_xs`, `matXV_pfield_xs` — the model.
* `hz_pfield`, `smA1V_pfield` — the forced response and `A₁` of the port disturbance.
* `orbit_gfl_port_stable`, `orbit_gfl_port_unstable` — end-to-end Floquet statements.
* `pump_port` — `g = v̂ g_V + θ̂_th g_θ`.

Corrections.
None: an extension.

Family and connection conclusions.
* The GFM counterpart is `GFM.VoltageModulationPort`: the same port map and the same Thevenin
  amplitudes, with one modulated element instead of five.
-/

noncomputable section
namespace powerlib.GFL.Parametric.AngleModulation
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv harm matXV smA1V smJV fderivWC gridSrc reparam
  linCV)
open powerlib.ParametricResonance.PortDisturbance (Port)
open scoped Matrix.Norms.Operator

namespace Params
variable (p : Params)

/-- The port of the GFL converter: grid source `E₀∠θ_{E0}` behind `jX_g`, injected current
`J₀∠φ₀` at the PCC, Thevenin source `V₀∠0`. -/
def gport (E0 θE0 J0 φ0 : ℝ) : Port := ⟨E0, θE0, J0, φ0, (p.Xg : ℂ) * I, p.V0⟩

/-- The GFL converter under the four port-disturbance channels `(ê, θ̂, ι̂, φ̂)`: the field of
`GridModulation` driven by the Thevenin source at the PCC. -/
def pfield (E0 θE0 J0 φ0 : ℝ) : (Fin 4 → ℝ) × (Fin 4 → ℝ) → Fin 4 → ℝ :=
  reparam p.gfield (p.gport E0 θE0 J0 φ0).polar

variable {E0 θE0 J0 φ0 : ℝ}

@[tmio M, powerlib_domain] theorem contDiffAt_pfield (hN : (p.gport E0 θE0 J0 φ0).eth 0 = p.V0)
    (hV : 0 < p.V0) {n : WithTop ℕ∞} : ContDiffAt ℝ n (p.pfield E0 θE0 J0 φ0) (p.xs, 0) := by
  refine ForcedOrbit.contDiffAt_reparam ?_ ((p.gport E0 θE0 J0 φ0).contDiffAt_polar hN hV)
  rw [(p.gport E0 θE0 J0 φ0).polar_zero hN hV.ne']
  exact p.contDiffAt_gfield (by simp [xs])

@[tmio M, powerlib_domain] theorem pfield_xs (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (hN : (p.gport E0 θE0 J0 φ0).eth 0 = p.V0) (hV : 0 < p.V0) :
    p.pfield E0 θE0 J0 φ0 (p.xs, 0) = 0 := by
  simp only [pfield, reparam]
  rw [(p.gport E0 θE0 J0 φ0).polar_zero hN hV.ne', p.gfield_xs hs]

@[tmio M, powerlib_domain] theorem matXV_pfield_xs (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (hN : (p.gport E0 θE0 J0 φ0).eth 0 = p.V0) (hV : 0 < p.V0) :
    matXV (p.pfield E0 θE0 J0 φ0) (p.xs, 0) = p.A0 := by
  have h0 := (p.gport E0 θE0 J0 φ0).polar_zero hN hV.ne'
  rw [pfield, ForcedOrbit.matXV_reparam (by
      rw [h0]; exact (p.contDiffAt_gfield (n := 1) (by simp [xs])).differentiableAt (by norm_num))
      (((p.gport E0 θE0 J0 φ0).contDiffAt_polar hN hV (n := 1)).differentiableAt (by norm_num)),
    h0, p.matXV_gfield_xs hs]

/-- The forced response to the port disturbance `ŵ`: the Thevenin response with
`v̂ = effV ŵ`, `θ̂_th = effθ ŵ`. -/
@[tmio M, powerlib_domain] theorem hz_pfield (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (hN : (p.gport E0 θE0 J0 φ0).eth 0 = p.V0) (hV : 0 < p.V0) {ω : ℝ}
    (hD : p.Dg (ω * I) ≠ 0) (w : Fin 4 → ℂ) :
    ((ω : ℂ) * I) • ((p.gport E0 θE0 J0 φ0).effV w • p.zv (ω * I) +
        (p.gport E0 θE0 J0 φ0).effθ w • (p.zc (ω * I) + e0c)) -
        (matXV (p.pfield E0 θE0 J0 φ0) (p.xs, 0)).map (algebraMap ℝ ℂ) *ᵥ
          ((p.gport E0 θE0 J0 φ0).effV w • p.zv (ω * I) +
            (p.gport E0 θE0 J0 φ0).effθ w • (p.zc (ω * I) + e0c)) =
      fderivWC (p.pfield E0 θE0 J0 φ0) (p.xs, 0) w := by
  set pt := p.gport E0 θE0 J0 φ0
  have h0 := pt.polar_zero hN hV.ne'
  have hd : DifferentiableAt ℝ pt.polar 0 :=
    (pt.contDiffAt_polar hN hV (n := 1)).differentiableAt (by norm_num)
  rw [p.matXV_pfield_xs hs hN hV, pfield, ForcedOrbit.fderivWC_reparam (by
      rw [h0]; exact (p.contDiffAt_gfield (n := 1) (by simp [xs])).differentiableAt (by norm_num))
      hd.hasFDerivAt, pt.linCV_polar hN hV, h0, ← p.matXV_gfield_xs hs]
  exact p.hz_gfield hs hD _ _

/-- `A₁` of the port disturbance: `A₁ = A₁^{(θ)}(z_rel) + v̂ A₀^{(V)}` with the Thevenin
amplitudes `v̂ = effV ŵ`, `θ̂_th = effθ ŵ`. -/
@[tmio M, powerlib_domain] theorem smA1V_pfield (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (hN : (p.gport E0 θE0 J0 φ0).eth 0 = p.V0) (hV : 0 < p.V0) (w : Fin 4 → ℂ)
    (z : Fin 4 → ℂ) :
    smA1V (p.pfield E0 θE0 J0 φ0) (p.xs, 0) w (z + (p.gport E0 θE0 J0 φ0).effθ w • e0c) =
      p.gA1 z + (p.gport E0 θE0 J0 φ0).effV w • p.A0V.map (algebraMap ℝ ℂ) := by
  set pt := p.gport E0 θE0 J0 φ0
  have h0 := pt.polar_zero hN hV.ne'
  have hd : DifferentiableAt ℝ pt.polar 0 :=
    (pt.contDiffAt_polar hN hV (n := 1)).differentiableAt (by norm_num)
  rw [pfield, ForcedOrbit.smA1V_reparam (by rw [h0]; exact p.contDiffAt_gfield (by simp [xs]))
      (pt.contDiffAt_polar hN hV) hd.hasFDerivAt, pt.linCV_polar hN hV, h0]
  exact p.smA1V_gfield hs z _ _

/-- The GFL converter under the port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` (grid-voltage magnitude and
angle, injected-current magnitude and angle, complex amplitudes at `2Ω`), end-to-end,
stability: at the Hopf point of `A₀`, `Re λ₁ < 0` and `|g/2| < |λ₁|` with
`g = l [A₁^{(θ)}(v̂ z_V + θ̂_th z⁽¹⁾) + v̂ A₀^{(V)}] r̄`, `v̂ = effV ŵ`, `θ̂_th = effθ ŵ`, give for
all small `ε > 0` the forced orbit with all Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_port_stable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hN : (p.gport E0 θE0 J0 φ0).eth 0 = p.V0)
    (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (w : Fin 4 → ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 ((p.gport E0 θE0 J0 φ0).effV w •
        p.zv (((2 * Ω : ℝ) : ℂ) * I) + (p.gport E0 θE0 J0 φ0).effθ w •
        p.zc (((2 * Ω : ℝ) : ℂ) * I)) + (p.gport E0 θE0 J0 φ0).effV w •
        p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.pfield E0 θE0 J0 φ0 ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.pfield E0 θE0 J0 φ0 ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : Fin 4 → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (p.pfield E0 θE0 J0 φ0) (p.xs, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u → ‖μ‖ < 1 := by
  set pt := p.gport E0 θE0 J0 φ0
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matXV (p.pfield E0 θE0 J0 φ0) (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matXV_pfield_xs hsd hN hV, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_pfield hsd hN hV (ω := 2 * Ω) hD2 w
  have hzeq : pt.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) + pt.effθ w • (p.zc (((2 * Ω : ℝ) : ℂ) * I) +
      e0c) = (pt.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) + pt.effθ w • p.zc (((2 * Ω : ℝ) : ℂ) * I)) +
        pt.effθ w • e0c := by
    rw [smul_add]; abel
  rw [hzeq] at hz
  have hA1 := p.smA1V_pfield hsd hN hV w
    (pt.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) + pt.effθ w • p.zc (((2 * Ω : ℝ) : ℂ) * I))
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable_vec
    (p.contDiffAt_pfield hN hV) (p.pfield_xs hsd hN hV) (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP
    As hA0' hsrs hz A0' ?_ ?_
  · rw [hLm, hRm]; exact hs
  · rw [hLm, hRm, hA1]; exact hg

/-- The GFL converter under the port disturbance `ŵ`, end-to-end, parametric instability:
`|λ₁| < |g/2|`. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_port_unstable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) (hN : (p.gport E0 θE0 J0 φ0).eth 0 = p.V0)
    (hV : 0 < p.V0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (w : Fin 4 → ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 ((p.gport E0 θE0 J0 φ0).effV w •
        p.zv (((2 * Ω : ℝ) : ℂ) * I) + (p.gport E0 θE0 J0 φ0).effθ w •
        p.zc (((2 * Ω : ℝ) : ℂ) * I)) + (p.gport E0 θE0 J0 φ0).effV w •
        p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star (p.gright (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.pfield E0 θE0 J0 φ0 ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.pfield E0 θE0 J0 φ0 ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable
          (fun t => smJV (p.pfield E0 θE0 J0 φ0) (p.xs, 0) w (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  set pt := p.gport E0 θE0 J0 φ0
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matXV (p.pfield E0 θE0 J0 φ0) (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matXV_pfield_xs hsd hN hV, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_pfield hsd hN hV (ω := 2 * Ω) hD2 w
  have hzeq : pt.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) + pt.effθ w • (p.zc (((2 * Ω : ℝ) : ℂ) * I) +
      e0c) = (pt.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) + pt.effθ w • p.zc (((2 * Ω : ℝ) : ℂ) * I)) +
        pt.effθ w • e0c := by
    rw [smul_add]; abel
  rw [hzeq] at hz
  have hA1 := p.smA1V_pfield hsd hN hV w
    (pt.effV w • p.zv (((2 * Ω : ℝ) : ℂ) * I) + pt.effθ w • p.zc (((2 * Ω : ℝ) : ℂ) * I))
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable_vec
    (p.contDiffAt_pfield hN hV) (p.pfield_xs hsd hN hV) (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP
    As hA0' hsrs hz A0' ?_
  rw [hLm, hRm, hA1]; exact hg

/-- The GFL pump of the port disturbance over the four channels: `g = Σ_k ŵ_k γ_k` with the
Thevenin pumps `g_V = l(A₁^{(θ)}(z_V) + A₀^{(V)})r̄` and `g_θ = l A₁^{(θ)}(z⁽¹⁾) r̄`
(`PortDisturbance.Port.pump_channels`). -/
@[tmio M, powerlib_domain] theorem pump_port (l r : Fin 4 → ℂ) (s : ℂ) (w : Fin 4 → ℂ) :
    l ⬝ᵥ ((p.gA1 ((p.gport E0 θE0 J0 φ0).effV w • p.zv s + (p.gport E0 θE0 J0 φ0).effθ w •
        p.zc s) + (p.gport E0 θE0 J0 φ0).effV w • p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star r) =
      (p.gport E0 θE0 J0 φ0).effV w * (l ⬝ᵥ ((p.gA1 (p.zv s) + p.A0V.map (algebraMap ℝ ℂ)) *ᵥ
        star r)) + (p.gport E0 θE0 J0 φ0).effθ w * (l ⬝ᵥ (p.gA1 (p.zc s) *ᵥ star r)) :=
  p.pump_superposition l r (p.zv s) (p.zc s) _ _

end Params
end powerlib.GFL.Parametric.AngleModulation
