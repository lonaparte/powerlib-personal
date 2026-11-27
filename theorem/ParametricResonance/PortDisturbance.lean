import theorem.ParametricResonance.SmoothForcedOrbitVec

/-! # Port disturbances of grid-tied converters: one form for every source and every model

A disturbance is an external source at the grid port. Its channels are the magnitude and the angle
of the grid voltage source behind the grid impedance `Z_g`, and either the magnitude and the angle
of a current injected at the port (VI chart) or the active and reactive power injected at the port
(PQV chart). A converter sees the network only through the Thevenin source at the port,
`e_th = E e^{jθ_E} + Z_g J` (`port_thevenin`), so every disturbance acts through the Thevenin
amplitudes `(v̂, θ̂_th)` of its chart; every grid-synchronized model then has the same
forced-orbit and Floquet statements.

Model boundary.
* Charts: `e : ℝ^W → ℂ` of class `C³` at `0`, `e(0) = V₀∠0`, `V₀ > 0`; the VI chart
  (`E = E₀(1 + ê)`, `θ_E = θ_{E0} + θ̂`, `J = J₀ + ι̂`, `φ = φ₀ + φ̂`) and the PQV chart
  (`J = (P − jQ) e^{jψ₀}/U₀`, the current injecting `P + jQ` at the reference port voltage
  `U₀∠ψ₀`).
* Models: a scalar-voltage model `G(x, V)` in relative-angle coordinates with the relative angle
  along `e` (`phasor G e`), or an absolute-frame model `H(x, (V, θ_g))` agreeing with `G` at
  `θ_g = 0`; `C³` at the operating point; modal coordinates or three-state eigen-data of
  `∂ₓG`; decay and detuning `εA₀'` of order `ε`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1 (input vector `û`,
`A₁ = Σ (∂A/∂x_l) z_l + G û`); the port formulation with voltage, current and power sources is new.

Results.
* `reparam`, `linCV`, `contDiffAt_reparam`, `matXV_reparam`, `fderivW_reparam`,
  `fderivWC_reparam`, `smDxV_reparam`, `smMwV_reparam`, `smA1V_reparam` — reparametrized inputs:
  the source transforms with the derivative of the chart.
* `thLog`, `thPolar`, `thPolarAbs`, `thLog_zero`, `thPolar_zero`, `thPolarAbs_zero`, `thPolar_eq`,
  `contDiffAt_thLog`, `contDiffAt_thPolar`, `contDiffAt_thPolarAbs`, `hasDerivAt_thLog_line`,
  `fderiv_thPolar`, `fderiv_thPolarAbs`, `linCV_thPolar`, `linCV_thPolarAbs` — Thevenin
  coordinates of a chart and its amplitudes `(Σ Re D_k ŵ_k, Σ Im D_k ŵ_k)`.
* `Port`, `Port.eth`, `Port.ca`, `Port.cc`, `Port.Dth`, `Port.effV`, `Port.effθ`, `Port.ca_add`,
  `Port.contDiff_eth`, `Port.hasDerivAt_eth_line`, `Port.linCV_polar`, `Port.linCV_polarAbs`,
  `Port.cc_lossless`, `Port.eff_active`, `Port.eff_reactive`, `Port.eff_no_injection`,
  `Port.pump_channels` — the VI chart: `v̂ = Re a ê − Im a θ̂ + Re c ι̂ − J₀ Im c φ̂`,
  `θ̂_th = Im a ê + Re a θ̂ + Im c ι̂ + J₀ Re c φ̂`; active and reactive dualities.
* `PQVPort`, `PQVPort.jinj`, `PQVPort.power_jinj`, `PQVPort.eth`, `PQVPort.ca`, `PQVPort.ck`,
  `PQVPort.Dth`, `PQVPort.effV`, `PQVPort.effθ`, `PQVPort.contDiff_eth`,
  `PQVPort.hasDerivAt_eth_line`, `PQVPort.linCV_polar`, `PQVPort.linCV_polarAbs`,
  `PQVPort.ck_lossless`, `PQVPort.eff_PQ_lossless`, `PQVPort.pump_channels` — the PQV chart:
  `v̂ = Re a ê − Im a θ̂ + Re κ P̂ + Im κ Q̂`, `θ̂_th = Im a ê + Re a θ̂ + Im κ P̂ − Re κ Q̂`,
  `κ = Z_g e^{jψ₀}/(U₀V₀)`; on a lossless grid with `ψ₀ = 0` the active power acts as an angle
  source and the reactive power as a magnitude source, both with `X/(U₀V₀)`.
* `port_thevenin` — the port current and voltage depend on the network only through `e_th`.
* `phasor`, `phasor_shift`, `contDiff_phasorArg`, `contDiffAt_phasor`, `matXV_phasor`,
  `fderivW_phasor`, `smDxV_phasor`, `smMwV_phasor`, `smA1V_phasor`, `forced_phasor` — the
  grid-phasor model of a scalar-voltage model.
* `phasor_port_data`, `orbit_phasor_port_stable`, `orbit_phasor_port_unstable`,
  `orbit_phasor_port_exp_stable`, `orbit_phasor_port_three_stable`,
  `orbit_phasor_port_three_unstable`, `orbit_phasor_port_three_exp_stable` — end-to-end for
  every grid-synchronized model and every chart: `(jωI − A₀) z_rel = v̂ b_V − jωθ̂ e`,
  `A₁ = D_x(∂ₓG) z_rel + v̂ D_V(∂ₓG)`.
* `matXV_slice`, `fderivW_slice`, `smDxV_slice`, `smMwV_slice`, `slice_port_data`,
  `orbit_slice_port_stable`, `orbit_slice_port_unstable`, `orbit_slice_port_exp_stable` —
  absolute-frame models: `(jωI − A₀) z = v̂ b_V + θ̂ b_θ`,
  `A₁ = D_x(∂ₓG) z + v̂ D_V(∂ₓG) + θ̂ D_θ(∂ₓH)`.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on port disturbances of grid-tied converters.
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbit
open Complex Matrix Set Filter Topology Metric
open scoped Matrix.Norms.Operator

section Reparam

variable {X U W : Type*} [Fintype X] [DecidableEq X] [Fintype U] [Fintype W]

/-- The field with its input reparametrized by `Φ`: `F(x, w) = G(x, Φ(w))`. -/
def reparam (G : (X → ℝ) × (U → ℝ) → X → ℝ) (Φ : (W → ℝ) → U → ℝ) :
    (X → ℝ) × (W → ℝ) → X → ℝ :=
  fun q => G (q.1, Φ q.2)

/-- A real-linear map between input spaces applied to a complex amplitude. -/
def linCV (L : (W → ℝ) →L[ℝ] (U → ℝ)) (w : W → ℂ) : U → ℂ :=
  fun k => ⟨L (fun j => (w j).re) k, L (fun j => (w j).im) k⟩

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem contDiffAt_reparam {G : (X → ℝ) × (U → ℝ) → X → ℝ}
    {Φ : (W → ℝ) → U → ℝ} {q : (X → ℝ) × (W → ℝ)} {n : WithTop ℕ∞}
    (hG : ContDiffAt ℝ n G (q.1, Φ q.2)) (hΦ : ContDiffAt ℝ n Φ q.2) :
    ContDiffAt ℝ n (reparam G Φ) q :=
  hG.comp q (contDiffAt_fst.prodMk (hΦ.comp q contDiffAt_snd))

/-- The partial Jacobian is that of `G` at `(x, Φ(w))`. -/
@[tmio T, powerlib_foundation] theorem matXV_reparam {G : (X → ℝ) × (U → ℝ) → X → ℝ}
    {Φ : (W → ℝ) → U → ℝ} {q : (X → ℝ) × (W → ℝ)} (hG : DifferentiableAt ℝ G (q.1, Φ q.2))
    (hΦ : DifferentiableAt ℝ Φ q.2) : matXV (reparam G Φ) q = matXV G (q.1, Φ q.2) := by
  have hF : DifferentiableAt ℝ (reparam G Φ) q :=
    hG.comp q (differentiableAt_fst.prodMk (hΦ.comp q differentiableAt_snd))
  refine matXV_of_line hF fun y => ?_
  have hl := hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (hasDerivAt_lineV (q.1, Φ q.2) ((y, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ))) (by simp)
  rw [← matXV_mulVec] at hl
  refine hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_def, reparam]
  congr 1
  ext <;> simp

omit [DecidableEq X] in
/-- The input direction: `∂_wF(q) a = ∂_uG(x, Φ(w)) Φ'(a)`. -/
@[tmio T, powerlib_foundation] theorem fderivW_reparam {G : (X → ℝ) × (U → ℝ) → X → ℝ}
    {Φ : (W → ℝ) → U → ℝ} {Φ' : (W → ℝ) →L[ℝ] (U → ℝ)} {q : (X → ℝ) × (W → ℝ)}
    (hG : DifferentiableAt ℝ G (q.1, Φ q.2)) (hΦ : HasFDerivAt Φ Φ' q.2) (a : W → ℝ) :
    fderiv ℝ (reparam G Φ) q (0, a) = fderiv ℝ G (q.1, Φ q.2) (0, Φ' a) := by
  have hF : DifferentiableAt ℝ (reparam G Φ) q :=
    hG.comp q (differentiableAt_fst.prodMk (hΦ.differentiableAt.comp q differentiableAt_snd))
  refine fderivW_of_lineV hF a ?_
  have hc : HasDerivAt (fun s : ℝ => ((q.1, Φ (q.2 + s • a)) : (X → ℝ) × (U → ℝ))) (0, Φ' a) 0 := by
    refine (hasDerivAt_const (0 : ℝ) q.1).prodMk ?_
    exact hΦ.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineV q.2 a) (by simp)
  have h := hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  exact h

omit [DecidableEq X] in
/-- The source transforms by the derivative of the reparametrization:
`∂_wF ŵ = ∂_uG (Φ' ŵ)`. -/
@[tmio T, powerlib_foundation] theorem fderivWC_reparam {G : (X → ℝ) × (U → ℝ) → X → ℝ}
    {Φ : (W → ℝ) → U → ℝ} {Φ' : (W → ℝ) →L[ℝ] (U → ℝ)} {q : (X → ℝ) × (W → ℝ)}
    (hG : DifferentiableAt ℝ G (q.1, Φ q.2)) (hΦ : HasFDerivAt Φ Φ' q.2) (w : W → ℂ) :
    fderivWC (reparam G Φ) q w = fderivWC G (q.1, Φ q.2) (linCV Φ' w) := by
  funext i
  simp only [fderivWC, fderivW_reparam hG hΦ, linCV]

/-- `D_x(∂ₓF)(q₀) = D_x(∂ₓG)(x₀, Φ(w₀))`. -/
@[tmio T, powerlib_foundation] theorem smDxV_reparam {G : (X → ℝ) × (U → ℝ) → X → ℝ}
    {Φ : (W → ℝ) → U → ℝ} {q0 : (X → ℝ) × (W → ℝ)} (hG : ContDiffAt ℝ 2 G (q0.1, Φ q0.2))
    (hΦ : ContDiffAt ℝ 2 Φ q0.2) (y : X → ℝ) :
    smDxV (reparam G Φ) q0 y = smDxV G (q0.1, Φ q0.2) y := by
  have hΦd : DifferentiableAt ℝ Φ q0.2 := hΦ.differentiableAt (by norm_num)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ G (q0.1 + t • y, Φ q0.2) := by
    have h1 : ∀ᶠ q in 𝓝 (q0.1, Φ q0.2), ContDiffAt ℝ 2 G q := hG.eventually (by simp)
    have hc : Continuous fun t : ℝ => ((q0.1 + t • y, Φ q0.2) : (X → ℝ) × (U → ℝ)) := by fun_prop
    have h2 := hc.tendsto 0
    simp only [zero_smul, add_zero] at h2
    exact (h2.eventually h1).mono fun t ht => ht.differentiableAt (by norm_num)
  refine smDxV_of_line (contDiffAt_reparam hG hΦ) y
    (Jr := fun t => matXV G ((q0.1, Φ q0.2).1 + t • y, (q0.1, Φ q0.2).2)) ?_ fun i j => ?_
  · filter_upwards [hev] with t ht
    exact matXV_reparam ht hΦd
  · have h := hasDerivAt_matXV_line hG ((y, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ)) i j
    have e : ∀ t : ℝ, ((q0.1, Φ q0.2) : (X → ℝ) × (U → ℝ)) + t • ((y, (0 : U → ℝ))) =
        ((q0.1, Φ q0.2).1 + t • y, (q0.1, Φ q0.2).2) := fun t => by ext <;> simp
    simp only [e] at h
    exact h

/-- `D_w(∂ₓF)(q₀) a = D_u(∂ₓG)(x₀, Φ(w₀)) Φ'(a)`. -/
@[tmio T, powerlib_foundation] theorem smMwV_reparam {G : (X → ℝ) × (U → ℝ) → X → ℝ}
    {Φ : (W → ℝ) → U → ℝ} {Φ' : (W → ℝ) →L[ℝ] (U → ℝ)} {q0 : (X → ℝ) × (W → ℝ)}
    (hG : ContDiffAt ℝ 2 G (q0.1, Φ q0.2)) (hΦ : ContDiffAt ℝ 2 Φ q0.2)
    (hΦ' : HasFDerivAt Φ Φ' q0.2) (a : W → ℝ) :
    smMwV (reparam G Φ) q0 a = smMwV G (q0.1, Φ q0.2) (Φ' a) := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ G (q0.1, Φ (q0.2 + t • a)) ∧
      DifferentiableAt ℝ Φ (q0.2 + t • a) := by
    have h1 : ∀ᶠ q in 𝓝 (q0.1, Φ q0.2), ContDiffAt ℝ 2 G q := hG.eventually (by simp)
    have h1' : ∀ᶠ w in 𝓝 q0.2, ContDiffAt ℝ 2 Φ w := hΦ.eventually (by simp)
    have hcΦ : ContinuousAt (fun t : ℝ => ((q0.1, Φ (q0.2 + t • a)) : (X → ℝ) × (U → ℝ))) 0 := by
      refine continuousAt_const.prodMk ?_
      have hl : ContinuousAt (fun t : ℝ => q0.2 + t • a) 0 := by fun_prop
      exact hΦ'.differentiableAt.continuousAt.comp_of_eq hl (by simp)
    have h2 : Tendsto (fun t : ℝ => ((q0.1, Φ (q0.2 + t • a)) : (X → ℝ) × (U → ℝ))) (𝓝 0)
        (𝓝 (q0.1, Φ q0.2)) := by simpa using hcΦ.tendsto
    have h3 : Tendsto (fun t : ℝ => q0.2 + t • a) (𝓝 0) (𝓝 q0.2) := by
      have : Continuous fun t : ℝ => q0.2 + t • a := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [h2.eventually h1, h3.eventually h1'] with t ht ht'
    exact ⟨ht.differentiableAt (by norm_num), ht'.differentiableAt (by norm_num)⟩
  refine smMwV_of_line (contDiffAt_reparam hG hΦ) a
    (Jr := fun t => matXV G (q0.1, Φ (q0.2 + t • a))) ?_ fun i j => ?_
  · filter_upwards [hev] with t ht
    exact matXV_reparam ht.1 ht.2
  · have hJ : DifferentiableAt ℝ (jacXV G) (q0.1, Φ q0.2) :=
      ((hG.fderiv_right (m := 1) (by norm_num)).clm_comp contDiffAt_const).differentiableAt
        (by norm_num)
    have hc : HasDerivAt (fun s : ℝ => ((q0.1, Φ (q0.2 + s • a)) : (X → ℝ) × (U → ℝ)))
        (0, Φ' a) 0 := by
      refine (hasDerivAt_const (0 : ℝ) q0.1).prodMk ?_
      exact hΦ'.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineV q0.2 a) (by simp)
    have hl := hJ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
    have h2 := (ContinuousLinearMap.apply ℝ (X → ℝ) (Pi.single j 1)).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hl
    have h3 := hasDerivAt_pi.1 h2 i
    simpa [matXV, smMwV, LinearMap.toMatrix'_apply, Function.comp_def] using h3

/-- The modulation transforms with the source: `A₁^F(ŵ, z) = A₁^G(Φ' ŵ, z)`. -/
@[tmio T, powerlib_foundation] theorem smA1V_reparam {G : (X → ℝ) × (U → ℝ) → X → ℝ}
    {Φ : (W → ℝ) → U → ℝ} {Φ' : (W → ℝ) →L[ℝ] (U → ℝ)} {q0 : (X → ℝ) × (W → ℝ)}
    (hG : ContDiffAt ℝ 2 G (q0.1, Φ q0.2)) (hΦ : ContDiffAt ℝ 2 Φ q0.2)
    (hΦ' : HasFDerivAt Φ Φ' q0.2) (w : W → ℂ) (z : X → ℂ) :
    smA1V (reparam G Φ) q0 w z = smA1V G (q0.1, Φ q0.2) (linCV Φ' w) z := by
  have hD : smDxV (reparam G Φ) q0 = smDxV G (q0.1, Φ q0.2) :=
    LinearMap.ext fun y => smDxV_reparam hG hΦ y
  ext i j
  simp only [smA1V, hD, Matrix.add_apply, linC, smMwV_reparam hG hΦ hΦ', linCV]

end Reparam

end powerlib.ParametricResonance.ForcedOrbit

namespace powerlib.ParametricResonance
open Complex Filter Topology Matrix

namespace PortDisturbance

/-! ### Thevenin coordinates of a source chart

A disturbance chart is a smooth map `e : ℝ^W → ℂ`, the Thevenin source at the port as a function
of the disturbance channels, normalized `e(0) = V₀∠0`. Its coordinates are the relative
magnitude and the angle (`thPolar`), or the magnitude and the angle (`thPolarAbs`), of `e`. -/

section Chart

variable {W : Type*} [Fintype W]

/-- `log(e/V₀)`: log-magnitude and angle of the Thevenin source relative to `V₀∠0`. -/
def thLog (e : (W → ℝ) → ℂ) (V0 : ℝ) (w : W → ℝ) : ℂ := Complex.log (e w / V0)

/-- The Thevenin source as relative magnitude and angle, `(|e|/V₀ − 1, arg e)`. -/
def thPolar (e : (W → ℝ) → ℂ) (V0 : ℝ) (w : W → ℝ) : Fin 2 → ℝ :=
  ![Real.exp (thLog e V0 w).re - 1, (thLog e V0 w).im]

/-- The Thevenin source as magnitude and angle, `(|e|, arg e)`. -/
def thPolarAbs (e : (W → ℝ) → ℂ) (V0 : ℝ) (w : W → ℝ) : Fin 2 → ℝ :=
  ![V0 * Real.exp (thLog e V0 w).re, (thLog e V0 w).im]

variable {e : (W → ℝ) → ℂ} {V0 : ℝ}

omit [Fintype W] in
@[tmio T, powerlib_foundation] theorem thLog_zero (h0 : e 0 = V0) (hV : V0 ≠ 0) :
    thLog e V0 0 = 0 := by
  have hV' : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV
  simp [thLog, h0, div_self hV']

omit [Fintype W] in
@[tmio T, powerlib_foundation] theorem thPolar_zero (h0 : e 0 = V0) (hV : V0 ≠ 0) :
    thPolar e V0 0 = 0 := by
  funext k; fin_cases k <;> simp [thPolar, thLog_zero h0 hV]

omit [Fintype W] in
@[tmio T, powerlib_foundation] theorem thPolarAbs_zero (h0 : e 0 = V0) (hV : V0 ≠ 0) :
    thPolarAbs e V0 0 = ![V0, 0] := by
  funext k; fin_cases k <;> simp [thPolarAbs, thLog_zero h0 hV]

omit [Fintype W] in
/-- The coordinates are the magnitude and the angle of the Thevenin source. -/
@[tmio T, powerlib_foundation] theorem thPolar_eq (hV : 0 < V0) (w : W → ℝ) (h : e w ≠ 0) :
    thPolar e V0 w = ![‖e w‖ / V0 - 1, Complex.arg (e w)] := by
  have hV' : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
  have hz : e w / V0 ≠ 0 := div_ne_zero h hV'
  have e1 : e w / V0 = ((V0⁻¹ : ℝ) : ℂ) * e w := by push_cast; field_simp
  funext k
  fin_cases k
  · simp only [thPolar, thLog, Complex.log_re]
    rw [Real.exp_log (norm_pos_iff.2 hz), norm_div, Complex.norm_real, Real.norm_of_nonneg hV.le]
    simp
  · simp only [thPolar, thLog, Complex.log_im]
    rw [e1, Complex.arg_real_mul _ (inv_pos.2 hV)]
    simp

@[tmio T, powerlib_foundation] theorem contDiffAt_thLog {n : WithTop ℕ∞} (he : ContDiffAt ℝ n e 0)
    (h0 : e 0 = V0) (hV : 0 < V0) : ContDiffAt ℝ n (thLog e V0) 0 := by
  have hV' : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
  have h1 : e 0 / V0 ∈ Complex.slitPlane := by
    rw [h0, div_self hV']; exact Complex.one_mem_slitPlane
  have hl := (Complex.contDiffAt_log h1 (n := n)).restrict_scalars ℝ
  exact hl.comp (0 : W → ℝ) (he.div_const _)

@[tmio T, powerlib_foundation] theorem contDiffAt_thPolar {n : WithTop ℕ∞}
    (he : ContDiffAt ℝ n e 0) (h0 : e 0 = V0) (hV : 0 < V0) :
    ContDiffAt ℝ n (thPolar e V0) 0 := by
  have hl := contDiffAt_thLog he h0 hV
  refine contDiffAt_pi.2 fun k => ?_
  fin_cases k
  · exact ((Real.contDiff_exp.contDiffAt.comp _ (Complex.reCLM.contDiff.contDiffAt.comp _ hl)).sub
      contDiffAt_const)
  · exact Complex.imCLM.contDiff.contDiffAt.comp _ hl

@[tmio T, powerlib_foundation] theorem contDiffAt_thPolarAbs {n : WithTop ℕ∞}
    (he : ContDiffAt ℝ n e 0) (h0 : e 0 = V0) (hV : 0 < V0) :
    ContDiffAt ℝ n (thPolarAbs e V0) 0 := by
  have hl := contDiffAt_thLog he h0 hV
  refine contDiffAt_pi.2 fun k => ?_
  fin_cases k
  · exact contDiffAt_const.mul
      (Real.contDiff_exp.contDiffAt.comp _ (Complex.reCLM.contDiff.contDiffAt.comp _ hl))
  · exact Complex.imCLM.contDiff.contDiffAt.comp _ hl

omit [Fintype W] in
/-- Along a direction with `d e = V₀ d`, `d log(e/V₀) = d`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_thLog_line (h0 : e 0 = V0) (hV : 0 < V0)
    {v : W → ℝ} {d : ℂ} (hd : HasDerivAt (fun s : ℝ => e (s • v)) (V0 * d) 0) :
    HasDerivAt (fun s : ℝ => thLog e V0 (s • v)) d 0 := by
  have hV' : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
  have h1 : e ((0 : ℝ) • v) / V0 = 1 := by simp [h0, div_self hV']
  have hl := (hd.div_const (V0 : ℂ)).clog_real (by rw [h1]; exact Complex.one_mem_slitPlane)
  rw [h1, div_one, mul_div_cancel_left₀ _ hV'] at hl
  exact hl

/-- The derivative of the relative coordinates: `thPolar' v = (Re d, Im d)`. -/
@[tmio T, powerlib_foundation] theorem fderiv_thPolar (he : ContDiffAt ℝ 1 e 0) (h0 : e 0 = V0)
    (hV : 0 < V0) {v : W → ℝ} {d : ℂ} (hd : HasDerivAt (fun s : ℝ => e (s • v)) (V0 * d) 0) :
    fderiv ℝ (thPolar e V0) 0 v = ![d.re, d.im] := by
  have hl := hasDerivAt_thLog_line h0 hV hd
  have h00 : (thLog e V0 ((0 : ℝ) • v)).re = 0 := by rw [zero_smul, thLog_zero h0 hV.ne']; simp
  have hline : HasDerivAt (fun s : ℝ => thPolar e V0 (s • v)) ![d.re, d.im] 0 := by
    refine hasDerivAt_pi.2 fun k => ?_
    fin_cases k
    · have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl).exp.sub_const 1
      simp only [Function.comp_def, Complex.reCLM_apply, h00, Real.exp_zero, one_mul] at hre
      simpa [thPolar] using hre
    · have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
      simpa [thPolar, Function.comp_def] using him
  have hdiff : DifferentiableAt ℝ (thPolar e V0) 0 :=
    (contDiffAt_thPolar he h0 hV).differentiableAt (by norm_num)
  have hs : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hs (by simp)).unique hline

/-- The derivative of the absolute coordinates: `thPolarAbs' v = (V₀ Re d, Im d)`. -/
@[tmio T, powerlib_foundation] theorem fderiv_thPolarAbs (he : ContDiffAt ℝ 1 e 0)
    (h0 : e 0 = V0) (hV : 0 < V0) {v : W → ℝ} {d : ℂ}
    (hd : HasDerivAt (fun s : ℝ => e (s • v)) (V0 * d) 0) :
    fderiv ℝ (thPolarAbs e V0) 0 v = ![V0 * d.re, d.im] := by
  have hl := hasDerivAt_thLog_line h0 hV hd
  have h00 : (thLog e V0 ((0 : ℝ) • v)).re = 0 := by rw [zero_smul, thLog_zero h0 hV.ne']; simp
  have hline : HasDerivAt (fun s : ℝ => thPolarAbs e V0 (s • v)) ![V0 * d.re, d.im] 0 := by
    refine hasDerivAt_pi.2 fun k => ?_
    fin_cases k
    · have hre := ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl).exp).const_mul V0
      simp only [Function.comp_def, Complex.reCLM_apply, h00, Real.exp_zero, one_mul] at hre
      simpa [thPolarAbs] using hre
    · have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
      simpa [thPolarAbs, Function.comp_def] using him
  have hdiff : DifferentiableAt ℝ (thPolarAbs e V0) 0 :=
    (contDiffAt_thPolarAbs he h0 hV).differentiableAt (by norm_num)
  have hs : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hs (by simp)).unique hline

/-- The amplitudes of a chart with a complex-linear first-order source `D`: if every direction has
`d e = V₀ (Σ_k v_k D_k)`, the disturbance `ŵ` acts as the Thevenin disturbance
`(Σ Re D_k ŵ_k, Σ Im D_k ŵ_k)`. -/
@[tmio T, powerlib_foundation] theorem linCV_thPolar (he : ContDiffAt ℝ 1 e 0) (h0 : e 0 = V0)
    (hV : 0 < V0) (D : W → ℂ)
    (hd : ∀ v : W → ℝ, HasDerivAt (fun s : ℝ => e (s • v)) (V0 * ∑ k, (v k : ℂ) * D k) 0)
    (w : W → ℂ) :
    ForcedOrbit.linCV (fderiv ℝ (thPolar e V0) 0) w =
      ForcedOrbit.gridSrc (∑ k, ((D k).re : ℂ) * w k) (∑ k, ((D k).im : ℂ) * w k) := by
  funext i
  fin_cases i <;> apply Complex.ext <;>
    simp [ForcedOrbit.linCV, fderiv_thPolar he h0 hV (hd _), ForcedOrbit.gridSrc,
      ForcedOrbit.ofv, ForcedOrbit.uMag, ForcedOrbit.uAng, Complex.re_sum, Complex.im_sum,
      Complex.mul_re, Complex.mul_im, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff, mul_comm]

/-- The same in the absolute coordinates: `(V₀ Σ Re D_k ŵ_k, Σ Im D_k ŵ_k)`. -/
@[tmio T, powerlib_foundation] theorem linCV_thPolarAbs (he : ContDiffAt ℝ 1 e 0)
    (h0 : e 0 = V0) (hV : 0 < V0) (D : W → ℂ)
    (hd : ∀ v : W → ℝ, HasDerivAt (fun s : ℝ => e (s • v)) (V0 * ∑ k, (v k : ℂ) * D k) 0)
    (w : W → ℂ) :
    ForcedOrbit.linCV (fderiv ℝ (thPolarAbs e V0) 0) w =
      ForcedOrbit.gridSrc (V0 * ∑ k, ((D k).re : ℂ) * w k) (∑ k, ((D k).im : ℂ) * w k) := by
  funext i
  fin_cases i <;> apply Complex.ext <;>
    simp [ForcedOrbit.linCV, fderiv_thPolarAbs he h0 hV (hd _), ForcedOrbit.gridSrc,
      ForcedOrbit.ofv, ForcedOrbit.uMag, ForcedOrbit.uAng, Complex.re_sum, Complex.im_sum,
      Complex.mul_re, Complex.mul_im, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff, mul_comm,
      Finset.mul_sum]

end Chart

/-! ### The voltage–current chart: magnitude and angle of the grid source and of an injected
current -/

/-- The port of a grid-tied converter: the grid source `E₀∠θ_{E0}` behind the grid impedance
`Z_g` and a current `J₀∠φ₀` injected at the port; `V₀` is the magnitude of the Thevenin source at
the port (the reference angle is that of the Thevenin source). -/
structure Port where
  /-- grid-source magnitude -/
  E0 : ℝ
  /-- grid-source angle -/
  θE0 : ℝ
  /-- injected-current magnitude -/
  J0 : ℝ
  /-- injected-current angle -/
  φ0 : ℝ
  /-- grid impedance between the port and the grid source -/
  Zg : ℂ
  /-- Thevenin-source magnitude at the port -/
  V0 : ℝ

namespace Port
variable (pt : Port)

/-- The Thevenin source at the port under the four disturbance channels
`w = (e, θ, ι, φ)`: grid-source magnitude `E₀(1 + e)` and angle `θ_{E0} + θ`, injected current
`J₀ + ι` and angle `φ₀ + φ`:
`e_th = E₀(1 + e) e^{j(θ_{E0} + θ)} + Z_g (J₀ + ι) e^{j(φ₀ + φ)}`. -/
def eth (w : Fin 4 → ℝ) : ℂ :=
  ((pt.E0 * (1 + w 0) : ℝ) : ℂ) * cexp (((pt.θE0 + w 1 : ℝ) : ℂ) * I) +
    pt.Zg * (((pt.J0 + w 2 : ℝ) : ℂ) * cexp (((pt.φ0 + w 3 : ℝ) : ℂ) * I))

/-- The voltage coefficient `a = E₀ e^{jθ_{E0}}/V₀`. -/
def ca : ℂ := (pt.E0 : ℂ) * cexp ((pt.θE0 : ℂ) * I) / pt.V0
/-- The current coefficient `c = Z_g e^{jφ₀}/V₀`. -/
def cc : ℂ := pt.Zg * cexp ((pt.φ0 : ℂ) * I) / pt.V0

/-- The first-order Thevenin source of the channels, `d e_th = V₀ Σ v_k D_k`:
`D = (a, ja, c, jJ₀c)`. -/
def Dth : Fin 4 → ℂ := ![pt.ca, pt.ca * I, pt.cc, pt.cc * pt.J0 * I]

/-- The relative-magnitude amplitude of the Thevenin source for the port disturbance `ŵ`:
`v̂ = Re a ê − Im a θ̂ + Re c ι̂ − J₀ Im c φ̂`. -/
def effV (w : Fin 4 → ℂ) : ℂ :=
  pt.ca.re * w 0 - pt.ca.im * w 1 + pt.cc.re * w 2 - pt.J0 * pt.cc.im * w 3

/-- The angle amplitude of the Thevenin source for the port disturbance `ŵ`:
`θ̂_th = Im a ê + Re a θ̂ + Im c ι̂ + J₀ Re c φ̂`. -/
def effθ (w : Fin 4 → ℂ) : ℂ :=
  pt.ca.im * w 0 + pt.ca.re * w 1 + pt.cc.im * w 2 + pt.J0 * pt.cc.re * w 3

/-- The normalization `e_th(0) = V₀` reads `a + J₀ c = 1`. -/
@[tmio M, powerlib_domain] theorem ca_add (hN : pt.eth 0 = pt.V0) (hV : pt.V0 ≠ 0) :
    pt.ca + pt.J0 * pt.cc = 1 := by
  have hV' : (pt.V0 : ℂ) ≠ 0 := by exact_mod_cast hV
  simp only [eth, Pi.zero_apply, add_zero, mul_one] at hN
  simp only [ca, cc]
  generalize cexp ((pt.θE0 : ℂ) * I) = A at hN ⊢
  generalize cexp ((pt.φ0 : ℂ) * I) = B at hN ⊢
  field_simp
  linear_combination hN

@[tmio M, powerlib_domain] theorem contDiff_eth {n : WithTop ℕ∞} : ContDiff ℝ n pt.eth := by
  have hof : ContDiff ℝ n (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hx : ∀ k : Fin 4, ContDiff ℝ n fun w : Fin 4 → ℝ => w k := fun k => contDiff_apply ℝ ℝ k
  have hex : ∀ (α : ℝ) (k : Fin 4), ContDiff ℝ n fun w : Fin 4 → ℝ =>
      cexp (((α + w k : ℝ) : ℂ) * I) := fun α k =>
    (Complex.contDiff_exp (𝕜 := ℝ)).comp ((hof.comp (contDiff_const.add (hx k))).mul contDiff_const)
  have t1 : ContDiff ℝ n fun w : Fin 4 → ℝ => ((pt.E0 * (1 + w 0) : ℝ) : ℂ) :=
    hof.comp (contDiff_const.mul (contDiff_const.add (hx 0)))
  have t3 : ContDiff ℝ n fun w : Fin 4 → ℝ => ((pt.J0 + w 2 : ℝ) : ℂ) :=
    hof.comp (contDiff_const.add (hx 2))
  exact (t1.mul (hex pt.θE0 1)).add (contDiff_const.mul (t3.mul (hex pt.φ0 3)))

/-- The Thevenin source along a direction: `d e_th = V₀ (a(v_e + jv_θ) + c(v_ι + jJ₀v_φ))`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_eth_line (hV : pt.V0 ≠ 0) (v : Fin 4 → ℝ) :
    HasDerivAt (fun s : ℝ => pt.eth (s • v)) (pt.V0 * ∑ k, (v k : ℂ) * pt.Dth k) 0 := by
  have hV' : (pt.V0 : ℂ) ≠ 0 := by exact_mod_cast hV
  have hr : ∀ (α β : ℝ), HasDerivAt (fun s : ℝ => ((α + s * β : ℝ) : ℂ)) (β : ℂ) 0 := fun α β => by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const β).const_add α
    simpa using this.ofReal_comp
  have he : ∀ (α β : ℝ), HasDerivAt (fun s : ℝ => cexp (((α + s * β : ℝ) : ℂ) * I))
      (cexp ((α : ℂ) * I) * ((β : ℂ) * I)) 0 := fun α β => by
    have := ((hr α β).mul_const I).cexp
    simpa using this
  have h1 : HasDerivAt (fun s : ℝ => ((pt.E0 * (1 + s * v 0) : ℝ) : ℂ))
      ((pt.E0 * v 0 : ℝ) : ℂ) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add 1).const_mul pt.E0)
    simpa using this.ofReal_comp
  have h := (h1.mul (he pt.θE0 (v 1))).add (((hr pt.J0 (v 2)).mul (he pt.φ0 (v 3))).const_mul pt.Zg)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp [eth, Pi.smul_apply, smul_eq_mul]
  · simp only [Fin.sum_univ_four, Dth, ca, cc, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    push_cast
    ring_nf

/-- The port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` acts on the converter as the Thevenin-source
disturbance `(v̂, θ̂_th) = (effV ŵ, effθ ŵ)` (relative magnitude, angle). -/
@[tmio M, powerlib_domain] theorem linCV_polar (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0)
    (w : Fin 4 → ℂ) :
    ForcedOrbit.linCV (fderiv ℝ (thPolar pt.eth pt.V0) 0) w =
      ForcedOrbit.gridSrc (pt.effV w) (pt.effθ w) := by
  rw [linCV_thPolar pt.contDiff_eth.contDiffAt hN hV pt.Dth (pt.hasDerivAt_eth_line hV.ne')]
  have h1 : ∑ k, ((pt.Dth k).re : ℂ) * w k = pt.effV w := by
    simp [Fin.sum_univ_four, Dth, effV, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
  have h2 : ∑ k, ((pt.Dth k).im : ℂ) * w k = pt.effθ w := by
    simp [Fin.sum_univ_four, Dth, effθ, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
  rw [h1, h2]

/-- The same with the absolute magnitude: `(V₀ effV ŵ, effθ ŵ)`. -/
@[tmio M, powerlib_domain] theorem linCV_polarAbs (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0)
    (w : Fin 4 → ℂ) :
    ForcedOrbit.linCV (fderiv ℝ (thPolarAbs pt.eth pt.V0) 0) w =
      ForcedOrbit.gridSrc (pt.V0 * pt.effV w) (pt.effθ w) := by
  rw [linCV_thPolarAbs pt.contDiff_eth.contDiffAt hN hV pt.Dth (pt.hasDerivAt_eth_line hV.ne')]
  have h1 : ∑ k, ((pt.Dth k).re : ℂ) * w k = pt.effV w := by
    simp [Fin.sum_univ_four, Dth, effV, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
  have h2 : ∑ k, ((pt.Dth k).im : ℂ) * w k = pt.effθ w := by
    simp [Fin.sum_univ_four, Dth, effθ, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
  rw [h1, h2]

/-! ### The channels on a lossless grid -/

/-- On a lossless grid `Z_g = jX`: `c = jX e^{jφ₀}/V₀`. -/
@[tmio M, powerlib_domain] theorem cc_lossless {X : ℝ} (hZ : pt.Zg = (X : ℂ) * I) :
    pt.cc.re = -(X * Real.sin pt.φ0) / pt.V0 ∧ pt.cc.im = X * Real.cos pt.φ0 / pt.V0 := by
  have e : pt.cc = ((X : ℂ) * I * cexp ((pt.φ0 : ℂ) * I)) / (pt.V0 : ℂ) := by rw [cc, hZ]
  rw [e, Complex.div_ofReal_re, Complex.div_ofReal_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

/-- An active injection (`φ₀ = 0`, in phase with the Thevenin voltage) on a lossless grid: the
current magnitude acts as an angle source `(X/V₀) ι̂`, the current angle as a magnitude source
`−(XJ₀/V₀) φ̂`. -/
@[tmio M, powerlib_domain] theorem eff_active {X : ℝ} (hZ : pt.Zg = (X : ℂ) * I)
    (hφ : pt.φ0 = 0) (w : Fin 4 → ℂ) :
    pt.effV w = pt.ca.re * w 0 - pt.ca.im * w 1 - pt.J0 * X / pt.V0 * w 3 ∧
      pt.effθ w = pt.ca.im * w 0 + pt.ca.re * w 1 + X / pt.V0 * w 2 := by
  obtain ⟨h1, h2⟩ := pt.cc_lossless hZ
  rw [hφ] at h1 h2
  simp only [Real.sin_zero, mul_zero, neg_zero, zero_div, Real.cos_zero, mul_one] at h1 h2
  refine ⟨?_, ?_⟩ <;> simp only [effV, effθ, h1, h2] <;> push_cast <;> ring

/-- A reactive injection (`φ₀ = −π/2`, lagging the Thevenin voltage) on a lossless grid: the
current magnitude acts as a magnitude source `(X/V₀) ι̂`, the current angle as an angle source
`(XJ₀/V₀) φ̂`. -/
@[tmio M, powerlib_domain] theorem eff_reactive {X : ℝ} (hZ : pt.Zg = (X : ℂ) * I)
    (hφ : pt.φ0 = -(Real.pi / 2)) (w : Fin 4 → ℂ) :
    pt.effV w = pt.ca.re * w 0 - pt.ca.im * w 1 + X / pt.V0 * w 2 ∧
      pt.effθ w = pt.ca.im * w 0 + pt.ca.re * w 1 + pt.J0 * X / pt.V0 * w 3 := by
  obtain ⟨h1, h2⟩ := pt.cc_lossless hZ
  simp only [hφ, Real.sin_neg, Real.sin_pi_div_two, Real.cos_neg, Real.cos_pi_div_two, mul_zero,
    zero_div] at h1 h2
  refine ⟨?_, ?_⟩ <;> simp only [effV, effθ, h1, h2] <;> push_cast <;> ring

/-- Without an operating injection (`J₀ = 0`) the voltage channels act directly, `a = 1`: the port
voltage disturbance is the Thevenin disturbance, and the current magnitude adds `c ι̂`. -/
@[tmio M, powerlib_domain] theorem eff_no_injection (hN : pt.eth 0 = pt.V0) (hV : pt.V0 ≠ 0)
    (hJ : pt.J0 = 0) (w : Fin 4 → ℂ) :
    pt.effV w = w 0 + pt.cc.re * w 2 ∧ pt.effθ w = w 1 + pt.cc.im * w 2 := by
  have ha := pt.ca_add hN hV
  rw [hJ] at ha
  simp only [ofReal_zero, zero_mul, add_zero] at ha
  have hr : pt.ca.re = 1 := by rw [ha]; simp
  have hi : pt.ca.im = 0 := by rw [ha]; simp
  refine ⟨?_, ?_⟩ <;> simp only [effV, effθ, hr, hi, hJ] <;> push_cast <;> ring

/-- The pump of a port disturbance for any converter with Thevenin pumps `g_V` (relative
magnitude) and `g_θ` (angle): `g = v̂ g_V + θ̂_th g_θ` expands over the four channels as
`ê(Re a g_V + Im a g_θ) + θ̂(Re a g_θ − Im a g_V) + ι̂(Re c g_V + Im c g_θ)`
`+ J₀φ̂(Re c g_θ − Im c g_V)`. -/
@[tmio M, powerlib_domain] theorem pump_channels (gV gθ : ℂ) (w : Fin 4 → ℂ) :
    pt.effV w * gV + pt.effθ w * gθ =
      w 0 * (pt.ca.re * gV + pt.ca.im * gθ) + w 1 * (pt.ca.re * gθ - pt.ca.im * gV) +
        w 2 * (pt.cc.re * gV + pt.cc.im * gθ) + pt.J0 * w 3 * (pt.cc.re * gθ - pt.cc.im * gV) := by
  simp only [effV, effθ]
  ring

end Port

/-! ### The PQV chart: grid-source magnitude and angle, injected active and reactive power -/

/-- The port with the disturbance source given by its power: the grid source `E₀∠θ_{E0}` behind
`Z_g` and the power `P₀ + jQ₀` injected at the reference port voltage `U₀∠ψ₀`; `V₀` is the
Thevenin magnitude at the port. -/
structure PQVPort where
  /-- grid-source magnitude -/
  E0 : ℝ
  /-- grid-source angle -/
  θE0 : ℝ
  /-- injected active power -/
  P0 : ℝ
  /-- injected reactive power -/
  Q0 : ℝ
  /-- reference port-voltage magnitude -/
  U0 : ℝ
  /-- reference port-voltage angle -/
  ψ0 : ℝ
  /-- grid impedance between the port and the grid source -/
  Zg : ℂ
  /-- Thevenin-source magnitude at the port -/
  V0 : ℝ

namespace PQVPort
variable (pq : PQVPort)

/-- The current that injects `P + jQ` at the reference voltage: `J = (P − jQ) e^{jψ₀}/U₀`. -/
def jinj (P Q : ℝ) : ℂ := ((P : ℂ) - (Q : ℂ) * I) * cexp ((pq.ψ0 : ℂ) * I) / pq.U0

/-- The injected current carries the power `P + jQ` at the reference voltage. -/
@[tmio M, powerlib_domain] theorem power_jinj (hU : pq.U0 ≠ 0) (P Q : ℝ) :
    ((pq.U0 : ℂ) * cexp ((pq.ψ0 : ℂ) * I)) * (starRingEnd ℂ) (pq.jinj P Q) = P + Q * I := by
  have hU' : (pq.U0 : ℂ) ≠ 0 := by exact_mod_cast hU
  have hc : (starRingEnd ℂ) (cexp ((pq.ψ0 : ℂ) * I)) = cexp (-((pq.ψ0 : ℂ) * I)) := by
    rw [← Complex.exp_conj]; simp
  simp only [jinj, map_div₀, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I, hc]
  rw [mul_comm ((pq.U0 : ℂ)) _]
  field_simp
  have hE : cexp ((pq.ψ0 : ℂ) * I) * cexp (-((pq.ψ0 : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination ((P : ℂ) + I * Q) * hE

/-- The Thevenin source under the channels `w = (ê, θ̂, P̂, Q̂)`:
`e_th = E₀(1 + ê) e^{j(θ_{E0} + θ̂)} + Z_g J(P₀ + P̂, Q₀ + Q̂)`. -/
def eth (w : Fin 4 → ℝ) : ℂ :=
  ((pq.E0 * (1 + w 0) : ℝ) : ℂ) * cexp (((pq.θE0 + w 1 : ℝ) : ℂ) * I) +
    pq.Zg * pq.jinj (pq.P0 + w 2) (pq.Q0 + w 3)

/-- The voltage coefficient `a = E₀ e^{jθ_{E0}}/V₀`. -/
def ca : ℂ := (pq.E0 : ℂ) * cexp ((pq.θE0 : ℂ) * I) / pq.V0
/-- The power coefficient `κ = Z_g e^{jψ₀}/(U₀V₀)`. -/
def ck : ℂ := pq.Zg * cexp ((pq.ψ0 : ℂ) * I) / (pq.U0 * pq.V0)

/-- The first-order Thevenin source of the channels: `D = (a, ja, κ, −jκ)`. -/
def Dth : Fin 4 → ℂ := ![pq.ca, pq.ca * I, pq.ck, -(pq.ck * I)]

/-- The relative-magnitude amplitude: `v̂ = Re a ê − Im a θ̂ + Re κ P̂ + Im κ Q̂`. -/
def effV (w : Fin 4 → ℂ) : ℂ :=
  pq.ca.re * w 0 - pq.ca.im * w 1 + pq.ck.re * w 2 + pq.ck.im * w 3

/-- The angle amplitude: `θ̂_th = Im a ê + Re a θ̂ + Im κ P̂ − Re κ Q̂`. -/
def effθ (w : Fin 4 → ℂ) : ℂ :=
  pq.ca.im * w 0 + pq.ca.re * w 1 + pq.ck.im * w 2 - pq.ck.re * w 3

@[tmio M, powerlib_domain] theorem contDiff_eth {n : WithTop ℕ∞} : ContDiff ℝ n pq.eth := by
  have hof : ContDiff ℝ n (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hx : ∀ k : Fin 4, ContDiff ℝ n fun w : Fin 4 → ℝ => w k := fun k => contDiff_apply ℝ ℝ k
  have t1 : ContDiff ℝ n fun w : Fin 4 → ℝ => ((pq.E0 * (1 + w 0) : ℝ) : ℂ) :=
    hof.comp (contDiff_const.mul (contDiff_const.add (hx 0)))
  have t2 : ContDiff ℝ n fun w : Fin 4 → ℝ => cexp (((pq.θE0 + w 1 : ℝ) : ℂ) * I) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp ((hof.comp (contDiff_const.add (hx 1))).mul contDiff_const)
  have t3 : ContDiff ℝ n fun w : Fin 4 → ℝ => pq.jinj (pq.P0 + w 2) (pq.Q0 + w 3) := by
    unfold jinj
    exact (((hof.comp (contDiff_const.add (hx 2))).sub
      ((hof.comp (contDiff_const.add (hx 3))).mul contDiff_const)).mul contDiff_const).div_const _
  exact (t1.mul t2).add (contDiff_const.mul t3)

@[tmio M, powerlib_domain] theorem hasDerivAt_eth_line (hV : pq.V0 ≠ 0) (hU : pq.U0 ≠ 0)
    (v : Fin 4 → ℝ) :
    HasDerivAt (fun s : ℝ => pq.eth (s • v)) (pq.V0 * ∑ k, (v k : ℂ) * pq.Dth k) 0 := by
  have hV' : (pq.V0 : ℂ) ≠ 0 := by exact_mod_cast hV
  have hU' : (pq.U0 : ℂ) ≠ 0 := by exact_mod_cast hU
  have hr : ∀ (α β : ℝ), HasDerivAt (fun s : ℝ => ((α + s * β : ℝ) : ℂ)) (β : ℂ) 0 := fun α β => by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const β).const_add α
    simpa using this.ofReal_comp
  have he : HasDerivAt (fun s : ℝ => cexp (((pq.θE0 + s * v 1 : ℝ) : ℂ) * I))
      (cexp ((pq.θE0 : ℂ) * I) * ((v 1 : ℂ) * I)) 0 := by
    have := ((hr pq.θE0 (v 1)).mul_const I).cexp
    simpa using this
  have h1 : HasDerivAt (fun s : ℝ => ((pq.E0 * (1 + s * v 0) : ℝ) : ℂ))
      ((pq.E0 * v 0 : ℝ) : ℂ) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add 1).const_mul pq.E0)
    simpa using this.ofReal_comp
  have hj : HasDerivAt (fun s : ℝ => pq.jinj (pq.P0 + s * v 2) (pq.Q0 + s * v 3))
      (((v 2 : ℂ) - (v 3 : ℂ) * I) * cexp ((pq.ψ0 : ℂ) * I) / pq.U0) 0 := by
    unfold jinj
    have := ((((hr pq.P0 (v 2)).sub ((hr pq.Q0 (v 3)).mul_const I)).mul_const
      (cexp ((pq.ψ0 : ℂ) * I))).div_const (pq.U0 : ℂ))
    simpa using this
  have h := (h1.mul he).add (hj.const_mul pq.Zg)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp [eth, Pi.smul_apply, smul_eq_mul]
  · simp only [Fin.sum_univ_four, Dth, ca, ck, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    push_cast
    ring_nf

/-- The PQV disturbance `ŵ = (ê, θ̂, P̂, Q̂)` acts as the Thevenin disturbance
`(v̂, θ̂_th) = (effV ŵ, effθ ŵ)`. -/
@[tmio M, powerlib_domain] theorem linCV_polar (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0)
    (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ) :
    ForcedOrbit.linCV (fderiv ℝ (thPolar pq.eth pq.V0) 0) w =
      ForcedOrbit.gridSrc (pq.effV w) (pq.effθ w) := by
  rw [linCV_thPolar pq.contDiff_eth.contDiffAt hN hV pq.Dth (pq.hasDerivAt_eth_line hV.ne' hU)]
  have h1 : ∑ k, ((pq.Dth k).re : ℂ) * w k = pq.effV w := by
    simp [Fin.sum_univ_four, Dth, effV, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
  have h2 : ∑ k, ((pq.Dth k).im : ℂ) * w k = pq.effθ w := by
    simp [Fin.sum_univ_four, Dth, effθ, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
  rw [h1, h2]

/-- The same with the absolute magnitude: `(V₀ effV ŵ, effθ ŵ)`. -/
@[tmio M, powerlib_domain] theorem linCV_polarAbs (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0)
    (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ) :
    ForcedOrbit.linCV (fderiv ℝ (thPolarAbs pq.eth pq.V0) 0) w =
      ForcedOrbit.gridSrc (pq.V0 * pq.effV w) (pq.effθ w) := by
  rw [linCV_thPolarAbs pq.contDiff_eth.contDiffAt hN hV pq.Dth
    (pq.hasDerivAt_eth_line hV.ne' hU)]
  have h1 : ∑ k, ((pq.Dth k).re : ℂ) * w k = pq.effV w := by
    simp [Fin.sum_univ_four, Dth, effV, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
  have h2 : ∑ k, ((pq.Dth k).im : ℂ) * w k = pq.effθ w := by
    simp [Fin.sum_univ_four, Dth, effθ, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring
  rw [h1, h2]

/-- On a lossless grid `Z_g = jX`: `κ = jX e^{jψ₀}/(U₀V₀)`. -/
@[tmio M, powerlib_domain] theorem ck_lossless {X : ℝ} (hZ : pq.Zg = (X : ℂ) * I) :
    pq.ck.re = -(X * Real.sin pq.ψ0) / (pq.U0 * pq.V0) ∧
      pq.ck.im = X * Real.cos pq.ψ0 / (pq.U0 * pq.V0) := by
  have e : pq.ck = ((X : ℂ) * I * cexp ((pq.ψ0 : ℂ) * I)) / ((pq.U0 * pq.V0 : ℝ) : ℂ) := by
    rw [ck, hZ]; push_cast; ring
  rw [e, Complex.div_ofReal_re, Complex.div_ofReal_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

/-- The classical decoupling on a lossless grid with the reference voltage in phase with the
Thevenin source (`ψ₀ = 0`): the active power acts as an angle source `X P̂/(U₀V₀)`, the reactive
power as a magnitude source `X Q̂/(U₀V₀)`. -/
@[tmio M, powerlib_domain] theorem eff_PQ_lossless {X : ℝ} (hZ : pq.Zg = (X : ℂ) * I)
    (hψ : pq.ψ0 = 0) (w : Fin 4 → ℂ) :
    pq.effV w = pq.ca.re * w 0 - pq.ca.im * w 1 + X / (pq.U0 * pq.V0) * w 3 ∧
      pq.effθ w = pq.ca.im * w 0 + pq.ca.re * w 1 + X / (pq.U0 * pq.V0) * w 2 := by
  obtain ⟨h1, h2⟩ := pq.ck_lossless hZ
  rw [hψ] at h1 h2
  simp only [Real.sin_zero, mul_zero, neg_zero, zero_div, Real.cos_zero, mul_one] at h1 h2
  refine ⟨?_, ?_⟩ <;> simp only [effV, effθ, h1, h2] <;> push_cast <;> ring

/-- The pump of a PQV disturbance over its channels for Thevenin pumps `g_V`, `g_θ`. -/
@[tmio M, powerlib_domain] theorem pump_channels (gV gθ : ℂ) (w : Fin 4 → ℂ) :
    pq.effV w * gV + pq.effθ w * gθ =
      w 0 * (pq.ca.re * gV + pq.ca.im * gθ) + w 1 * (pq.ca.re * gθ - pq.ca.im * gV) +
        w 2 * (pq.ck.re * gV + pq.ck.im * gθ) + w 3 * (pq.ck.im * gV - pq.ck.re * gθ) := by
  simp only [effV, effθ]
  ring

end PQVPort

/-! ### The Thevenin reduction at the port -/

/-- A converter with internal source `u` behind `Z_u` at a port where the grid source `e_g`
behind `Z_g` and the injected current `J` meet: the port current and the port voltage depend on
the network only through the Thevenin source `e_th = e_g + Z_g J`. -/
@[tmio M, powerlib_domain] theorem port_thevenin {u eg J Zu Zg i vp : ℂ} (hZ : Zu + Zg ≠ 0)
    (hi : u - vp = Zu * i) (hv : vp = eg + Zg * (i + J)) :
    i = (u - (eg + Zg * J)) / (Zu + Zg) ∧ vp = (Zg * u + Zu * (eg + Zg * J)) / (Zu + Zg) := by
  have hi' : i = (u - (eg + Zg * J)) / (Zu + Zg) := by
    rw [eq_div_iff hZ]
    linear_combination -hi - hv
  refine ⟨hi', ?_⟩
  rw [eq_div_iff hZ]
  rw [hi'] at hv
  rw [hv]
  field_simp
  ring

/-! ### Grid-synchronized models from their scalar-voltage form

A converter model in relative-angle coordinates driven by the grid-voltage magnitude,
`G(x, V)`, with the relative angle along `e`, becomes a grid-phasor model in the absolute angle by
`phasor G e (x, (V, θ_g)) = G(x − θ_g e, V)`, invariant under the joint rotation of the converter
angle and the grid angle. Composed with a disturbance chart `Φ` (`reparam (phasor G e) Φ`), every
port disturbance acts through the Thevenin amplitudes `(v̂, θ̂_th)` of `Φ`. -/

section Phasor

open ForcedOrbit

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The grid-phasor model of a scalar-voltage model `G` with the relative angle along `e`. -/
def phasor (G : (X → ℝ) × ℝ → X → ℝ) (e : X → ℝ) : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ :=
  fun q => G (q.1 - q.2 1 • e, q.2 0)

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem phasor_shift (G : (X → ℝ) × ℝ → X → ℝ) (e : X → ℝ)
    (q : (X → ℝ) × (Fin 2 → ℝ)) (s : ℝ) : phasor G e (q + s • (e, uAng)) = phasor G e q := by
  simp only [phasor]
  congr 1
  ext i
  · simp [uAng]; ring
  · simp [uAng]

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem contDiff_phasorArg {n : WithTop ℕ∞} (e : X → ℝ) :
    ContDiff ℝ n (fun q : (X → ℝ) × (Fin 2 → ℝ) => ((q.1 - q.2 1 • e, q.2 0) : (X → ℝ) × ℝ)) :=
  (contDiff_fst.sub (((contDiff_apply ℝ ℝ (1 : Fin 2)).comp contDiff_snd).smul
    contDiff_const)).prodMk ((contDiff_apply ℝ ℝ (0 : Fin 2)).comp contDiff_snd)

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem contDiffAt_phasor {G : (X → ℝ) × ℝ → X → ℝ} {e : X → ℝ}
    {x0 : X → ℝ} {u0 : ℝ} {n : WithTop ℕ∞} (hG : ContDiffAt ℝ n G (x0, u0)) :
    ContDiffAt ℝ n (phasor G e) (x0, ![u0, 0]) := by
  have h : ContDiffAt ℝ n G (((x0, ![u0, 0]) : (X → ℝ) × (Fin 2 → ℝ)).1 -
      ((x0, ![u0, 0]) : (X → ℝ) × (Fin 2 → ℝ)).2 1 • e,
      ((x0, ![u0, 0]) : (X → ℝ) × (Fin 2 → ℝ)).2 0) := by simpa using hG
  exact ContDiffAt.comp (f := fun q : (X → ℝ) × (Fin 2 → ℝ) => ((q.1 - q.2 1 • e, q.2 0) :
    (X → ℝ) × ℝ)) (x0, ![u0, 0]) h (contDiff_phasorArg e).contDiffAt

/-- The partial Jacobian is that of `G` at the relative state. -/
@[tmio T, powerlib_foundation] theorem matXV_phasor {G : (X → ℝ) × ℝ → X → ℝ} {e : X → ℝ}
    {q : (X → ℝ) × (Fin 2 → ℝ)} (hG : DifferentiableAt ℝ G (q.1 - q.2 1 • e, q.2 0)) :
    matXV (phasor G e) q = matX G (q.1 - q.2 1 • e, q.2 0) := by
  have hL : DifferentiableAt ℝ (fun q : (X → ℝ) × (Fin 2 → ℝ) =>
      ((q.1 - q.2 1 • e, q.2 0) : (X → ℝ) × ℝ)) q :=
    ((contDiff_phasorArg (n := 1) e).differentiable (by norm_num)) q
  refine matXV_of_line (hG.comp q hL) fun y => ?_
  set g : (X → ℝ) × ℝ := (q.1 - q.2 1 • e, q.2 0) with hg
  have hl := hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line g (y, 0)) (by simp)
  rw [← matX_mulVec] at hl
  refine hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_def, hg]
  show G _ = G _
  congr 1
  ext i
  · simp; ring
  · simp

omit [DecidableEq X] in
/-- The magnitude direction is that of `G`: `∂_V(phasor) = ∂_V G`. -/
@[tmio T, powerlib_foundation] theorem fderivW_phasor {G : (X → ℝ) × ℝ → X → ℝ} {e : X → ℝ}
    {x0 : X → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 1 G (x0, u0)) :
    fderiv ℝ (phasor G e) (x0, ![u0, 0]) (0, uMag) = fderiv ℝ G (x0, u0) (0, 1) := by
  refine fderivW_of_lineV ((contDiffAt_phasor hG).differentiableAt (by norm_num)) uMag ?_
  have hl := (hG.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (hasDerivAt_line (x0, u0) (0, 1)) (by simp)
  refine hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_def, phasor]
  congr 1
  ext i
  · simp [uMag]
  · simp [uMag]

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] private theorem eventually_diff_line {G : (X → ℝ) × ℝ → X → ℝ}
    {x0 : X → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 2 G (x0, u0)) (c : ℝ → (X → ℝ) × ℝ) (hc : Continuous c)
    (hc0 : c 0 = (x0, u0)) : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ G (c t) := by
  have h1 : ∀ᶠ q in 𝓝 (x0, u0), ContDiffAt ℝ 2 G q := hG.eventually (by simp)
  have h2 := hc.tendsto 0
  rw [hc0] at h2
  exact (h2.eventually h1).mono fun t ht => ht.differentiableAt (by norm_num)

@[tmio T, powerlib_foundation] theorem smDxV_phasor {G : (X → ℝ) × ℝ → X → ℝ} {e : X → ℝ}
    {x0 : X → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 2 G (x0, u0)) (y : X → ℝ) :
    smDxV (phasor G e) (x0, ![u0, 0]) y = smDx G (x0, u0) y := by
  refine smDxV_eq_smDx (contDiffAt_phasor hG) hG y ?_
  filter_upwards [eventually_diff_line hG (fun t => (x0 + t • y, u0)) (by fun_prop) (by simp)]
    with t ht
  rw [matXV_phasor (by simpa using ht)]
  simp

@[tmio T, powerlib_foundation] theorem smMwV_phasor {G : (X → ℝ) × ℝ → X → ℝ} {e : X → ℝ}
    {x0 : X → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 2 G (x0, u0)) :
    smMwV (phasor G e) (x0, ![u0, 0]) uMag = smM1 G (x0, u0) := by
  refine smMwV_eq_smM1 (contDiffAt_phasor hG) hG uMag ?_
  filter_upwards [eventually_diff_line hG (fun t => (x0, u0 + t)) (by fun_prop) (by simp)]
    with t ht
  rw [matXV_phasor (by simpa [uMag] using ht)]
  simp [uMag]

/-- The general source form for the phasor model:
`A₁(v̂, θ̂; z + θ̂ e) = D_x(∂ₓG) z + v̂ D_V(∂ₓG)`. -/
@[tmio T, powerlib_foundation] theorem smA1V_phasor {G : (X → ℝ) × ℝ → X → ℝ} {e : X → ℝ}
    {x0 : X → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 2 G (x0, u0)) (v θ : ℂ) (z : X → ℂ) :
    smA1V (phasor G e) (x0, ![u0, 0]) (gridSrc v θ) (z + θ • ofv e) =
      DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ) := by
  rw [smA1V_gridSrc (phasor_shift G e) (contDiffAt_phasor hG), smMwV_phasor hG]
  have hD : smDxV (phasor G e) (x0, ![u0, 0]) = smDx G (x0, u0) :=
    LinearMap.ext fun y => smDxV_phasor hG y
  rw [hD]

/-- The general source form for the phasor model, forced response. -/
@[tmio T, powerlib_foundation] theorem forced_phasor {G : (X → ℝ) × ℝ → X → ℝ} {e : X → ℝ}
    {x0 : X → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 1 G (x0, u0)) (v θ : ℂ) (ω : ℝ) (z : X → ℂ) :
    ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
        fderivWC (phasor G e) (x0, ![u0, 0]) (gridSrc v θ) ↔
      ((ω : ℂ) * I) • (z - θ • ofv e) -
          (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ (z - θ • ofv e) =
        v • ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * θ) • ofv e := by
  have hm : matXV (phasor G e) (x0, ![u0, 0]) = matX G (x0, u0) := by
    rw [matXV_phasor (by simpa using hG.differentiableAt (by norm_num))]; simp
  rw [← hm, forced_gridSrc (phasor_shift G e) ((contDiffAt_phasor hG).differentiableAt
    (by norm_num)), fderivW_phasor hG]

end Phasor

/-! ### End-to-end for every grid-synchronized model and every disturbance chart -/

section EndToEnd

open ForcedOrbit
open TwoToOne (base)
open BlockAveraging (expS physLeft physRight)
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X] {W : Type*} [Fintype W]

/-- The data shared by the end-to-end statements: for `F = reparam (phasor G e) Φ` at `(x₀, 0)`,
the Jacobian is `∂ₓG(x₀, u₀)`, the response `z_rel + θ̂ e` solves the forced equation, and
`A₁ = D_x(∂ₓG) z_rel + v̂ D_V(∂ₓG)`. -/
@[tmio T, powerlib_foundation] theorem phasor_port_data {G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ}
    {u0 : ℝ} (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : X → ℝ)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {ω : ℝ} {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * θ) • ofv e) :
    ContDiffAt ℝ 3 (reparam (phasor G e) Φ) (x0, 0) ∧ reparam (phasor G e) Φ (x0, 0) = 0 ∧
      matXV (reparam (phasor G e) Φ) (x0, 0) = matX G (x0, u0) ∧
      ((ω : ℂ) * I) • (z + θ • ofv e) -
          (matXV (reparam (phasor G e) Φ) (x0, 0)).map (algebraMap ℝ ℂ) *ᵥ (z + θ • ofv e) =
        fderivWC (reparam (phasor G e) Φ) (x0, 0) w ∧
      smA1V (reparam (phasor G e) Φ) (x0, 0) w (z + θ • ofv e) =
        DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ) := by
  have hph : ContDiffAt ℝ 3 (phasor G e) ((x0, (0 : W → ℝ)).1, Φ (x0, (0 : W → ℝ)).2) := by
    simp only [hΦ0]; exact contDiffAt_phasor hG
  have hΦd : HasFDerivAt Φ (fderiv ℝ Φ 0) 0 := (hΦ.differentiableAt (by norm_num)).hasFDerivAt
  have hm : matXV (reparam (phasor G e) Φ) (x0, 0) = matX G (x0, u0) := by
    rw [matXV_reparam (hph.differentiableAt (by norm_num)) (hΦ.differentiableAt (by norm_num))]
    simp only [hΦ0]
    rw [matXV_phasor (by simpa using hG.differentiableAt (by norm_num))]
    simp
  refine ⟨contDiffAt_reparam hph hΦ, ?_, hm, ?_, ?_⟩
  · simp only [reparam, phasor, hΦ0]; simpa using hG0
  · rw [hm, fderivWC_reparam (hph.differentiableAt (by norm_num)) hΦd, hvθ]
    simp only [hΦ0]
    refine (forced_phasor (hG.of_le (by norm_num)) v θ ω _).2 ?_
    rw [add_sub_cancel_right]; exact hz
  · rw [smA1V_reparam (hph.of_le (by norm_num)) (hΦ.of_le (by norm_num)) hΦd, hvθ]
    simp only [hΦ0]
    exact smA1V_phasor (hG.of_le (by norm_num)) v θ z

/-- End-to-end, stability, for every grid-synchronized model `G` (relative angle along `e`,
magnitude input) and every port-disturbance chart `Φ` with Thevenin amplitudes `(v̂, θ̂)`: with
modal coordinates of `∂ₓG(x₀, u₀)` (pair `±jω/2`, stable block), `z` the relative response
`(jωI − A₀) z = v̂ b_V − jωθ̂ e`, `Re λ₁ < 0` and `|g/2| < |λ₁|` with
`g = u [D_x(∂ₓG) z + v̂ D_V(∂ₓG)] r̄`, the forced orbit exists for all small `ε > 0` and every
Floquet multiplier lies inside the unit circle. -/
@[tmio T, powerlib_foundation] theorem orbit_phasor_port_stable {Y : Type*} [Fintype Y]
    [DecidableEq Y] {G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : X → ℝ)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * θ) • ofv e)
    (A0' : Matrix X X ℝ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ)) *ᵥ
        star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : X → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (phasor G e) Φ) (x0, 0) w ω A0' ε t (y t))
            (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u → ‖μ‖ < 1 := by
  obtain ⟨hF, hF0, hm, hzF, hA1⟩ := phasor_port_data hG hG0 e hΦ hΦ0 hvθ hz
  exact smooth_orbit_floquet_stable_vec hF hF0 hω hPQ hQP As (by rw [hm]; exact hA0) hsr hzF A0'
    hs (by rw [hA1]; exact hg)

/-- End-to-end, parametric instability, for every grid-synchronized model and every chart:
`|λ₁| < |g/2|`. -/
@[tmio T, powerlib_foundation] theorem orbit_phasor_port_unstable {Y : Type*} [Fintype Y]
    [DecidableEq Y] {G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : X → ℝ)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * θ) • ofv e)
    (A0' : Matrix X X ℝ)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ)) *ᵥ
        star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable
          (fun t => smJV (reparam (phasor G e) Φ) (x0, 0) w ω A0' ε t (y t))
          (2 * Real.pi / ω) := by
  obtain ⟨hF, hF0, hm, hzF, hA1⟩ := phasor_port_data hG hG0 e hΦ hΦ0 hvθ hz
  exact smooth_orbit_floquet_unstable_vec hF hF0 hω hPQ hQP As (by rw [hm]; exact hA0) hsr hzF A0'
    (by rw [hA1]; exact hg)

/-- End-to-end with orbital stability for every grid-synchronized model and every chart: in the
stable case the forced orbit is locally exponentially stable. -/
@[tmio T, powerlib_foundation] theorem orbit_phasor_port_exp_stable {Y : Type*} [Fintype Y]
    [DecidableEq Y] {G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : X → ℝ)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * θ) • ofv e)
    (A0' : Matrix X X ℝ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ)) *ᵥ
        star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + y t,
        (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + a,
          (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hF, hF0, hm, hzF, hA1⟩ := phasor_port_data hG hG0 e hΦ hΦ0 hvθ hz
  exact smooth_orbit_exp_stable_vec hF hF0 hω hPQ hQP As (by rw [hm]; exact hA0) hsr hzF A0'
    hs (by rw [hA1]; exact hg)

/-- Three-state models from their eigen-data (pair `±jΩ`, real pole `λ₃ < 0`, drive at `2Ω`),
stability, for every chart. -/
@[tmio T, powerlib_foundation] theorem orbit_phasor_port_three_stable
    {G : (Fin 3 → ℝ) × ℝ → Fin 3 → ℝ} {x0 : Fin 3 → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : Fin 3 → ℝ)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {Ω : ℝ} (hΩ : 0 < Ω)
    {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX G (x0, u0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX G (x0, u0) *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX G (x0, u0) = l3 • u3)
    (hur3 : u3 ⬝ᵥ r3 = 1) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ)) *ᵥ
        star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 3 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (phasor G e) Φ) (x0, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 := by
  obtain ⟨hF, hF0, hm, hzF, hA1⟩ := phasor_port_data hG hG0 e hΦ hΦ0 hvθ hz
  rw [← hm] at hr hu hr3 hu3
  exact smooth_orbit_floquet_three_stable_vec hF hF0 hΩ hl3 hr hu hur hr3 hu3 hur3 hzF A0' hs
    (by rw [hA1]; exact hg)

/-- Three-state models from their eigen-data, parametric instability, for every chart. -/
@[tmio T, powerlib_foundation] theorem orbit_phasor_port_three_unstable
    {G : (Fin 3 → ℝ) × ℝ → Fin 3 → ℝ} {x0 : Fin 3 → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : Fin 3 → ℝ)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {Ω : ℝ} (hΩ : 0 < Ω)
    {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX G (x0, u0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX G (x0, u0) *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX G (x0, u0) = l3 • u3)
    (hur3 : u3 ⬝ᵥ r3 = 1) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 <
      ‖u ⬝ᵥ ((DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ)) *ᵥ
        star r) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable
          (fun t => smJV (reparam (phasor G e) Φ) (x0, 0) w (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hF, hF0, hm, hzF, hA1⟩ := phasor_port_data hG hG0 e hΦ hΦ0 hvθ hz
  rw [← hm] at hr hu hr3 hu3
  exact smooth_orbit_floquet_three_unstable_vec hF hF0 hΩ hl3 hr hu hur hr3 hu3 hur3 hzF A0'
    (by rw [hA1]; exact hg)

/-- Three-state models from their eigen-data, end-to-end with orbital stability, for every
chart. -/
@[tmio T, powerlib_foundation] theorem orbit_phasor_port_three_exp_stable
    {G : (Fin 3 → ℝ) × ℝ → Fin 3 → ℝ} {x0 : Fin 3 → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : Fin 3 → ℝ)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {Ω : ℝ} (hΩ : 0 < Ω)
    {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX G (x0, u0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX G (x0, u0) *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX G (x0, u0) = l3 • u3)
    (hur3 : u3 ⬝ᵥ r3 = 1) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) - ((((2 * Ω : ℝ) : ℂ) * I) * θ) • ofv e)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ)) *ᵥ
        star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + y t,
        (x0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (phasor G e) Φ ((x0, (0 : W → ℝ)).1 + a,
          (x0, (0 : W → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hF, hF0, hm, hzF, hA1⟩ := phasor_port_data hG hG0 e hΦ hΦ0 hvθ hz
  rw [← hm] at hr hu hr3 hu3
  exact smooth_orbit_exp_three_stable_vec hF hF0 hΩ hl3 hr hu hur hr3 hu3 hur3 hzF A0' hs
    (by rw [hA1]; exact hg)

end EndToEnd

/-! ### Absolute-frame models agreeing with a scalar-voltage model at `θ_g = 0`

A converter model written in a fixed frame with the grid phasor `V∠θ_g` as input (for instance
with network currents in that frame) need not be invariant under the joint rotation; it suffices
that it agrees with the scalar-voltage model at `θ_g = 0`. Then the Jacobian, `b_V`, `D_x(∂ₓ·)`
and `D_V(∂ₓ·)` are those of the scalar model, and the angle channel enters through
`b_θ = ∂_θH` and `D_θ(∂ₓH)`. -/

section Slice

open ForcedOrbit
open TwoToOne (base)
open BlockAveraging (expS physLeft physRight)
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X] {W : Type*} [Fintype W]

@[tmio T, powerlib_foundation] theorem matXV_slice {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x : X → ℝ} {V : ℝ}
    (hH : DifferentiableAt ℝ H (x, ![V, 0])) (hG : DifferentiableAt ℝ G (x, V)) :
    matXV H (x, ![V, 0]) = matX G (x, V) := by
  refine matXV_of_line hH fun y => ?_
  have hl := hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line (x, V) (y, 0)) (by simp)
  rw [← matX_mulVec] at hl
  refine hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_def, hHG]
  congr 1
  ext <;> simp

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem fderivW_slice {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : DifferentiableAt ℝ H (x0, ![u0, 0])) (hG : DifferentiableAt ℝ G (x0, u0)) :
    fderiv ℝ H (x0, ![u0, 0]) (0, uMag) = fderiv ℝ G (x0, u0) (0, 1) := by
  refine fderivW_of_lineV hH uMag ?_
  have hl := hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line (x0, u0) (0, 1))
    (by simp)
  refine hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  have e : ![u0, 0] + s • uMag = ![u0 + s, 0] := by
    funext k; fin_cases k <;> simp [uMag]
  simp only [Function.comp_def, e, hHG]
  congr 1
  ext <;> simp

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] private theorem eventually_diff_curve
    {F : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {q : (X → ℝ) × (Fin 2 → ℝ)} (hF : ContDiffAt ℝ 2 F q) (c : ℝ → (X → ℝ) × (Fin 2 → ℝ))
    (hc : Continuous c) (hc0 : c 0 = q) : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ F (c t) := by
  have h1 : ∀ᶠ p in 𝓝 q, ContDiffAt ℝ 2 F p := hF.eventually (by simp)
  have h2 := hc.tendsto 0
  rw [hc0] at h2
  exact (h2.eventually h1).mono fun t ht => ht.differentiableAt (by norm_num)

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] private theorem eventually_diff_curveG
    {G : (X → ℝ) × ℝ → X → ℝ} {g : (X → ℝ) × ℝ}
    (hG : ContDiffAt ℝ 2 G g) (c : ℝ → (X → ℝ) × ℝ) (hc : Continuous c) (hc0 : c 0 = g) :
    ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ G (c t) := by
  have h1 : ∀ᶠ p in 𝓝 g, ContDiffAt ℝ 2 G p := hG.eventually (by simp)
  have h2 := hc.tendsto 0
  rw [hc0] at h2
  exact (h2.eventually h1).mono fun t ht => ht.differentiableAt (by norm_num)

@[tmio T, powerlib_foundation] theorem smDxV_slice {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 2 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 2 G (x0, u0)) (y : X → ℝ) :
    smDxV H (x0, ![u0, 0]) y = smDx G (x0, u0) y := by
  refine smDxV_eq_smDx hH hG y ?_
  filter_upwards [eventually_diff_curve hH (fun t => (x0 + t • y, ![u0, 0])) (by fun_prop)
    (by simp), eventually_diff_curveG hG (fun t => (x0 + t • y, u0)) (by fun_prop) (by simp)]
    with t h1 h2
  exact matXV_slice hHG h1 h2

@[tmio T, powerlib_foundation] theorem smMwV_slice {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 2 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 2 G (x0, u0)) :
    smMwV H (x0, ![u0, 0]) uMag = smM1 G (x0, u0) := by
  have e : ∀ t : ℝ, ![u0, 0] + t • uMag = ![u0 + t, 0] := fun t => by
    funext k; fin_cases k <;> simp [uMag]
  refine smMwV_eq_smM1 hH hG uMag ?_
  filter_upwards [eventually_diff_curve hH (fun t => (x0, ![u0, 0] + t • uMag)) (by fun_prop)
    (by simp), eventually_diff_curveG hG (fun t => (x0, u0 + t)) (by fun_prop) (by simp)]
    with t h1 h2
  rw [e] at h1 ⊢
  exact matXV_slice hHG h1 h2

/-- The data of the end-to-end statements for an absolute-frame model `H` with slice `G` and a
chart `Φ`: the response `z` of the absolute frame solves `(jωI − A₀) z = v̂ b_V + θ̂ b_θ`, and
`A₁ = D_x(∂ₓG) z + v̂ D_V(∂ₓG) + θ̂ D_θ(∂ₓH)`. -/
@[tmio T, powerlib_foundation] theorem slice_port_data {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 3 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {ω : ℝ} {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) + θ • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng))) :
    ContDiffAt ℝ 3 (reparam H Φ) (x0, 0) ∧ reparam H Φ (x0, 0) = 0 ∧
      matXV (reparam H Φ) (x0, 0) = matX G (x0, u0) ∧
      ((ω : ℂ) * I) • z - (matXV (reparam H Φ) (x0, 0)).map (algebraMap ℝ ℂ) *ᵥ z =
        fderivWC (reparam H Φ) (x0, 0) w ∧
      smA1V (reparam H Φ) (x0, 0) w z =
        DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ) +
          θ • (smMwV H (x0, ![u0, 0]) uAng).map (algebraMap ℝ ℂ) := by
  have hH' : ContDiffAt ℝ 3 H ((x0, (0 : W → ℝ)).1, Φ (x0, (0 : W → ℝ)).2) := by
    simp only [hΦ0]; exact hH
  have hΦd : HasFDerivAt Φ (fderiv ℝ Φ 0) 0 := (hΦ.differentiableAt (by norm_num)).hasFDerivAt
  have hm : matXV (reparam H Φ) (x0, 0) = matX G (x0, u0) := by
    rw [matXV_reparam (hH'.differentiableAt (by norm_num)) (hΦ.differentiableAt (by norm_num))]
    simp only [hΦ0]
    exact matXV_slice hHG (hH.differentiableAt (by norm_num)) (hG.differentiableAt (by norm_num))
  have hsrc : ∀ a b : ℂ, gridSrc a b = a • ofv uMag + b • ofv uAng := fun a b => rfl
  refine ⟨contDiffAt_reparam hH' hΦ, ?_, hm, ?_, ?_⟩
  · simp only [reparam, hΦ0, hHG]; exact hG0
  · rw [hm, fderivWC_reparam (hH'.differentiableAt (by norm_num)) hΦd, hvθ]
    simp only [hΦ0]
    have h1 : fderivWC H (x0, ![u0, 0]) (gridSrc v θ) =
        v • ofv (fderiv ℝ G (x0, u0) (0, 1)) + θ • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng)) := by
      rw [← fderivW_slice hHG (hH.differentiableAt (by norm_num)) (hG.differentiableAt
        (by norm_num))]
      funext i
      simp only [fderivWC, hsrc]
      have e1 : (fun k => ((v • ofv uMag + θ • ofv uAng) k).re) = v.re • uMag + θ.re • uAng := by
        funext k; simp [ofv]
      have e2 : (fun k => ((v • ofv uMag + θ • ofv uAng) k).im) = v.im • uMag + θ.im • uAng := by
        funext k; simp [ofv]
      have e3 : ∀ a b : ℝ, (((0 : X → ℝ), a • uMag + b • uAng) : (X → ℝ) × (Fin 2 → ℝ)) =
          a • ((0 : X → ℝ), uMag) + b • ((0 : X → ℝ), uAng) := fun a b => by ext <;> simp
      rw [e1, e2, e3, e3, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
      apply Complex.ext <;> simp [ofv]
    rw [h1]; exact hz
  · rw [smA1V_reparam (hH'.of_le (by norm_num)) (hΦ.of_le (by norm_num)) hΦd, hvθ]
    simp only [hΦ0]
    have hD : smDxV H (x0, ![u0, 0]) = smDx G (x0, u0) :=
      LinearMap.ext fun y => smDxV_slice hHG (hH.of_le (by norm_num)) (hG.of_le (by norm_num)) y
    have hM := smMwV_slice hHG (hH.of_le (by norm_num)) (hG.of_le (by norm_num))
    have e1 : (fun k => ((gridSrc v θ) k).re) = v.re • uMag + θ.re • uAng := by
      funext k; simp [gridSrc, ofv]
    have e2 : (fun k => ((gridSrc v θ) k).im) = v.im • uMag + θ.im • uAng := by
      funext k; simp [gridSrc, ofv]
    ext i j
    simp only [smA1V, hD, Matrix.add_apply, linC, e1, e2, map_add, map_smul, hM,
      Matrix.smul_apply, Matrix.map_apply]
    apply Complex.ext <;> simp <;> ring

/-- End-to-end, stability, for every absolute-frame model `H` agreeing with a scalar-voltage model
`G` at `θ_g = 0`, and every chart `Φ`. -/
@[tmio T, powerlib_foundation] theorem orbit_slice_port_stable {Y : Type*} [Fintype Y]
    [DecidableEq Y] {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ} {G : (X → ℝ) × ℝ → X → ℝ}
    (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 3 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) + θ • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng)))
    (A0' : Matrix X X ℝ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ) +
        θ • (smMwV H (x0, ![u0, 0]) uAng).map (algebraMap ℝ ℂ)) *ᵥ star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam H Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam H Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : X → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam H Φ) (x0, 0) w ω A0' ε t (y t))
            (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u → ‖μ‖ < 1 := by
  obtain ⟨hF, hF0, hm, hzF, hA1⟩ := slice_port_data hHG hH hG hG0 hΦ hΦ0 hvθ hz
  exact smooth_orbit_floquet_stable_vec hF hF0 hω hPQ hQP As (by rw [hm]; exact hA0) hsr hzF A0'
    hs (by rw [hA1]; exact hg)

/-- End-to-end, parametric instability, for absolute-frame models: `|λ₁| < |g/2|`. -/
@[tmio T, powerlib_foundation] theorem orbit_slice_port_unstable {Y : Type*} [Fintype Y]
    [DecidableEq Y] {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ} {G : (X → ℝ) × ℝ → X → ℝ}
    (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 3 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) + θ • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng)))
    (A0' : Matrix X X ℝ)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ) +
        θ • (smMwV H (x0, ![u0, 0]) uAng).map (algebraMap ℝ ℂ)) *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam H Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam H Φ ((x0, (0 : W → ℝ)).1 + y t,
            (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam H Φ) (x0, 0) w ω A0' ε t (y t))
          (2 * Real.pi / ω) := by
  obtain ⟨hF, hF0, hm, hzF, hA1⟩ := slice_port_data hHG hH hG hG0 hΦ hΦ0 hvθ hz
  exact smooth_orbit_floquet_unstable_vec hF hF0 hω hPQ hQP As (by rw [hm]; exact hA0) hsr hzF A0'
    (by rw [hA1]; exact hg)

/-- End-to-end with orbital stability for absolute-frame models. -/
@[tmio T, powerlib_foundation] theorem orbit_slice_port_exp_stable {Y : Type*} [Fintype Y]
    [DecidableEq Y] {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ} {G : (X → ℝ) × ℝ → X → ℝ}
    (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 3 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0)
    {Φ : (W → ℝ) → Fin 2 → ℝ} (hΦ : ContDiffAt ℝ 3 Φ 0) (hΦ0 : Φ 0 = ![u0, 0])
    {w : W → ℂ} {v θ : ℂ} (hvθ : linCV (fderiv ℝ Φ 0) w = gridSrc v θ) {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
      v • ofv (fderiv ℝ G (x0, u0) (0, 1)) + θ • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng)))
    (A0' : Matrix X X ℝ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + v • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ) +
        θ • (smMwV H (x0, ![u0, 0]) uAng).map (algebraMap ℝ ℂ)) *ᵥ star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (reparam H Φ ((x0, (0 : W → ℝ)).1 + y t,
        (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t a => reparam H Φ ((x0, (0 : W → ℝ)).1 + a,
          (x0, (0 : W → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hF, hF0, hm, hzF, hA1⟩ := slice_port_data hHG hH hG hG0 hΦ hΦ0 hvθ hz
  exact smooth_orbit_exp_stable_vec hF hF0 hω hPQ hQP As (by rw [hm]; exact hA0) hsr hzF A0'
    hs (by rw [hA1]; exact hg)

end Slice

end PortDisturbance

end powerlib.ParametricResonance
