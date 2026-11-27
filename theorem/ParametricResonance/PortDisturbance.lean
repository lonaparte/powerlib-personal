import theorem.ParametricResonance.SmoothForcedOrbitVec

/-! # Port disturbances: voltage and current, magnitude and angle

A grid-tied converter sees the network through its port. The disturbance at the port is either a
voltage-type source (the grid source `E∠θ_E` behind the grid impedance `Z_g`) or a current-type
source (a current `J∠φ` injected at the port), each with a magnitude and an angle channel. The
converter sees both only through the Thevenin source at the port,
`e_th = E e^{jθ_E} + Z_g J e^{jφ}`. This file gives
* the reparametrization of the input of a smooth field, `F(x, w) = G(x, Φ(w))`: the forced
  response, the modulation `A₁` and the end-to-end hypotheses transform with `Φ'(w₀)`;
* the port map `w = (ê, θ̂, ι̂, φ̂) ↦` (magnitude, angle) of `e_th`, its derivative, and the
  resulting Thevenin amplitudes `(v̂, θ̂_th) = (effV ŵ, effθ ŵ)` for complex `ŵ`;
* the channel dualities on a lossless grid: an active injected current acts through its magnitude
  as an angle source and through its angle as a magnitude source; a reactive one the other way.

Model boundary.
* `Φ : ℝ^W → ℝ^U`, `G` of class `C²` (`C³` for the end-to-end statements) at `(x₀, Φ(w₀))`.
* The port: `E = E₀(1 + e)`, `θ_E = θ_{E0} + θ`, `J = J₀ + ι` (absolute, so `J₀ = 0` is allowed),
  `φ = φ₀ + φ`; the Thevenin source at the operating point is normalized to `V₀∠0`, `V₀ > 0`
  (`eth 0 = V₀`). The converter models must depend on the network only through the Thevenin
  source at the port, behind the impedance `Z_g`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1 (input vector `û`,
`A₁ = Σ (∂A/∂x_l) z_l + G û`); the port formulation with voltage- and current-type sources is
new.

Results.
* `reparam`, `linCV`, `contDiffAt_reparam`, `matXV_reparam`, `fderivW_reparam`,
  `fderivWC_reparam`, `smDxV_reparam`, `smMwV_reparam`, `smA1V_reparam` — the reparametrized
  field: `∂_wF ŵ = ∂_uG(Φ'ŵ)`, `A₁^F(ŵ, z) = A₁^G(Φ'ŵ, z)`.
* `PortDisturbance.Port`, `eth`, `lth`, `polar`, `polarAbs`, `ca`, `cc`, `dth`, `effV`, `effθ`,
  `ca_add`, `lth_zero`, `polar_zero`, `polarAbs_zero`, `polar_eq`, `contDiff_eth`,
  `contDiffAt_lth`, `contDiffAt_polar`, `contDiffAt_polarAbs` — the port map.
* `hasDerivAt_eth_line`, `hasDerivAt_lth_line`, `hasDerivAt_polar_line`,
  `hasDerivAt_polarAbs_line`, `fderiv_polar`, `fderiv_polarAbs`, `linCV_polar`, `linCV_polarAbs`
  — the four channels act as the Thevenin disturbance
  `v̂ = Re a ê − Im a θ̂ + Re c ι̂ − J₀ Im c φ̂`, `θ̂_th = Im a ê + Re a θ̂ + Im c ι̂ + J₀ Re c φ̂`,
  `a = E₀e^{jθ_{E0}}/V₀`, `c = Z_g e^{jφ₀}/V₀`.
* `cc_lossless`, `eff_active`, `eff_reactive`, `eff_no_injection`, `pump_channels` — the channel
  dualities and the pump over the four channels.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the port disturbances of grid-tied converters.
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
open Complex

/-! ### The port disturbance -/

namespace PortDisturbance

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

/-- `log(e_th/V₀)`: log-magnitude and angle of the Thevenin source relative to `V₀∠0`. -/
def lth (w : Fin 4 → ℝ) : ℂ := Complex.log (pt.eth w / pt.V0)

/-- The Thevenin source as relative magnitude and angle, `(|e_th|/V₀ − 1, arg e_th)`. -/
def polar (w : Fin 4 → ℝ) : Fin 2 → ℝ := ![Real.exp (pt.lth w).re - 1, (pt.lth w).im]

/-- The Thevenin source as magnitude and angle, `(|e_th|, arg e_th)`. -/
def polarAbs (w : Fin 4 → ℝ) : Fin 2 → ℝ := ![pt.V0 * Real.exp (pt.lth w).re, (pt.lth w).im]

/-- The voltage coefficient `a = E₀ e^{jθ_{E0}}/V₀`. -/
def ca : ℂ := (pt.E0 : ℂ) * cexp ((pt.θE0 : ℂ) * I) / pt.V0
/-- The current coefficient `c = Z_g e^{jφ₀}/V₀`. -/
def cc : ℂ := pt.Zg * cexp ((pt.φ0 : ℂ) * I) / pt.V0

/-- The first-order Thevenin source of a direction `v`: `a(v_e + jv_θ) + c(v_ι + jJ₀v_φ)`. -/
def dth (v : Fin 4 → ℝ) : ℂ :=
  pt.ca * (v 0 + v 1 * I) + pt.cc * (v 2 + pt.J0 * v 3 * I)

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

@[tmio M, powerlib_domain] theorem lth_zero (hN : pt.eth 0 = pt.V0) (hV : pt.V0 ≠ 0) :
    pt.lth 0 = 0 := by
  have hV' : (pt.V0 : ℂ) ≠ 0 := by exact_mod_cast hV
  simp [lth, hN, div_self hV']

@[tmio M, powerlib_domain] theorem polar_zero (hN : pt.eth 0 = pt.V0) (hV : pt.V0 ≠ 0) :
    pt.polar 0 = 0 := by
  funext k; fin_cases k <;> simp [polar, pt.lth_zero hN hV]

@[tmio M, powerlib_domain] theorem polarAbs_zero (hN : pt.eth 0 = pt.V0) (hV : pt.V0 ≠ 0) :
    pt.polarAbs 0 = ![pt.V0, 0] := by
  funext k; fin_cases k <;> simp [polarAbs, pt.lth_zero hN hV]

/-- The coordinates are the magnitude and the angle of the Thevenin source. -/
@[tmio M, powerlib_domain] theorem polar_eq (hV : 0 < pt.V0) (w : Fin 4 → ℝ) (h : pt.eth w ≠ 0) :
    pt.polar w = ![‖pt.eth w‖ / pt.V0 - 1, Complex.arg (pt.eth w)] := by
  have hV' : (pt.V0 : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
  have hz : pt.eth w / pt.V0 ≠ 0 := div_ne_zero h hV'
  have e : pt.eth w / pt.V0 = ((pt.V0⁻¹ : ℝ) : ℂ) * pt.eth w := by
    push_cast; field_simp
  funext k
  fin_cases k
  · simp only [polar, lth, Complex.log_re]
    rw [Real.exp_log (norm_pos_iff.2 hz), norm_div, Complex.norm_real, Real.norm_of_nonneg hV.le]
    simp
  · simp only [polar, lth, Complex.log_im]
    rw [e, Complex.arg_real_mul _ (inv_pos.2 hV)]
    simp

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

@[tmio M, powerlib_domain] theorem contDiffAt_lth (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n pt.lth 0 := by
  have hV' : (pt.V0 : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
  have h1 : pt.eth 0 / pt.V0 ∈ Complex.slitPlane := by
    rw [hN, div_self hV']; exact Complex.one_mem_slitPlane
  have hl := (Complex.contDiffAt_log h1 (n := n)).restrict_scalars ℝ
  have hd : ContDiff ℝ n fun w => pt.eth w / pt.V0 := pt.contDiff_eth.div_const _
  exact hl.comp (0 : Fin 4 → ℝ) hd.contDiffAt

@[tmio M, powerlib_domain] theorem contDiffAt_polar (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n pt.polar 0 := by
  have hl := pt.contDiffAt_lth hN hV (n := n)
  refine contDiffAt_pi.2 fun k => ?_
  fin_cases k
  · exact ((Real.contDiff_exp.contDiffAt.comp _ (Complex.reCLM.contDiff.contDiffAt.comp _ hl)).sub
      contDiffAt_const)
  · exact Complex.imCLM.contDiff.contDiffAt.comp _ hl

@[tmio M, powerlib_domain] theorem contDiffAt_polarAbs (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n pt.polarAbs 0 := by
  have hl := pt.contDiffAt_lth hN hV (n := n)
  refine contDiffAt_pi.2 fun k => ?_
  fin_cases k
  · exact contDiffAt_const.mul
      (Real.contDiff_exp.contDiffAt.comp _ (Complex.reCLM.contDiff.contDiffAt.comp _ hl))
  · exact Complex.imCLM.contDiff.contDiffAt.comp _ hl

/-- The Thevenin source along a direction: `d e_th = V₀ (a(v_e + jv_θ) + c(v_ι + jJ₀v_φ))`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_eth_line (hV : pt.V0 ≠ 0) (v : Fin 4 → ℝ) :
    HasDerivAt (fun s : ℝ => pt.eth (s • v)) (pt.V0 * pt.dth v) 0 := by
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
  · simp only [dth, ca, cc]
    field_simp
    push_cast
    ring_nf

/-- The Thevenin coordinates along a direction: `d(polar) v = (Re d_th v, Im d_th v)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_lth_line (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0)
    (v : Fin 4 → ℝ) : HasDerivAt (fun s : ℝ => pt.lth (s • v)) (pt.dth v) 0 := by
  have hV' : (pt.V0 : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
  have h0 : pt.eth ((0 : ℝ) • v) / pt.V0 = 1 := by simp [hN, div_self hV']
  have hd : HasDerivAt (fun s : ℝ => pt.eth (s • v) / pt.V0) (pt.V0 * pt.dth v / pt.V0) 0 :=
    (pt.hasDerivAt_eth_line hV.ne' v).div_const _
  have hl := hd.clog_real (by rw [h0]; exact Complex.one_mem_slitPlane)
  rw [h0, div_one, mul_div_cancel_left₀ _ hV'] at hl
  exact hl

@[tmio M, powerlib_domain] theorem hasDerivAt_polar_line (hN : pt.eth 0 = pt.V0)
    (hV : 0 < pt.V0) (v : Fin 4 → ℝ) :
    HasDerivAt (fun s : ℝ => pt.polar (s • v)) ![(pt.dth v).re, (pt.dth v).im] 0 := by
  have hl := pt.hasDerivAt_lth_line hN hV v
  have h00 : (pt.lth ((0 : ℝ) • v)).re = 0 := by rw [zero_smul, pt.lth_zero hN hV.ne']; simp
  refine hasDerivAt_pi.2 fun k => ?_
  fin_cases k
  · have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl).exp.sub_const 1
    simp only [Function.comp_def, Complex.reCLM_apply, h00, Real.exp_zero, one_mul] at hre
    simpa [polar] using hre
  · have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    simpa [polar, Function.comp_def] using him

@[tmio M, powerlib_domain] theorem hasDerivAt_polarAbs_line (hN : pt.eth 0 = pt.V0)
    (hV : 0 < pt.V0) (v : Fin 4 → ℝ) :
    HasDerivAt (fun s : ℝ => pt.polarAbs (s • v)) ![pt.V0 * (pt.dth v).re, (pt.dth v).im] 0 := by
  have hl := pt.hasDerivAt_lth_line hN hV v
  have h00 : (pt.lth ((0 : ℝ) • v)).re = 0 := by rw [zero_smul, pt.lth_zero hN hV.ne']; simp
  refine hasDerivAt_pi.2 fun k => ?_
  fin_cases k
  · have hre := ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl).exp).const_mul pt.V0
    simp only [Function.comp_def, Complex.reCLM_apply, h00, Real.exp_zero, one_mul] at hre
    simpa [polarAbs] using hre
  · have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    simpa [polarAbs, Function.comp_def] using him

@[tmio M, powerlib_domain] theorem fderiv_polar (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0)
    (v : Fin 4 → ℝ) : fderiv ℝ pt.polar 0 v = ![(pt.dth v).re, (pt.dth v).im] := by
  have hd : DifferentiableAt ℝ pt.polar 0 :=
    (pt.contDiffAt_polar hN hV (n := 1)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  exact h1.unique (pt.hasDerivAt_polar_line hN hV v)

@[tmio M, powerlib_domain] theorem fderiv_polarAbs (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0)
    (v : Fin 4 → ℝ) : fderiv ℝ pt.polarAbs 0 v = ![pt.V0 * (pt.dth v).re, (pt.dth v).im] := by
  have hd : DifferentiableAt ℝ pt.polarAbs 0 :=
    (pt.contDiffAt_polarAbs hN hV (n := 1)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  exact h1.unique (pt.hasDerivAt_polarAbs_line hN hV v)

/-- The port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` acts on the converter as the Thevenin-source
disturbance `(v̂, θ̂_th) = (effV ŵ, effθ ŵ)` (relative magnitude, angle). -/
@[tmio M, powerlib_domain] theorem linCV_polar (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0)
    (w : Fin 4 → ℂ) :
    ForcedOrbit.linCV (fderiv ℝ pt.polar 0) w = ForcedOrbit.gridSrc (pt.effV w) (pt.effθ w) := by
  funext k
  fin_cases k <;> apply Complex.ext <;>
    simp [ForcedOrbit.linCV, pt.fderiv_polar hN hV, dth, effV, effθ, ForcedOrbit.gridSrc,
      ForcedOrbit.ofv, ForcedOrbit.uMag, ForcedOrbit.uAng, Complex.mul_re, Complex.mul_im,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring

/-- The same with the absolute magnitude: `(V₀ effV ŵ, effθ ŵ)`. -/
@[tmio M, powerlib_domain] theorem linCV_polarAbs (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0)
    (w : Fin 4 → ℂ) :
    ForcedOrbit.linCV (fderiv ℝ pt.polarAbs 0) w =
      ForcedOrbit.gridSrc (pt.V0 * pt.effV w) (pt.effθ w) := by
  funext k
  fin_cases k <;> apply Complex.ext <;>
    simp [ForcedOrbit.linCV, pt.fderiv_polarAbs hN hV, dth, effV, effθ, ForcedOrbit.gridSrc,
      ForcedOrbit.ofv, ForcedOrbit.uMag, ForcedOrbit.uAng, Complex.mul_re, Complex.mul_im,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring

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

end PortDisturbance

end powerlib.ParametricResonance
