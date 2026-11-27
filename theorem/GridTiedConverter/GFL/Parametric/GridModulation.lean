import theorem.GridTiedConverter.GFL.Parametric.AngleModulationIndex
import theorem.ParametricResonance.SmoothForcedOrbitVec

/-! # GFL converter under a general grid phasor source: voltage magnitude and angle

`GFL.Parametric.AngleModulation` takes the grid angle as the oscillation source. A grid source is a
phasor `V∠θ_g`; here both channels are modulated, `V = V₀(1 + ε Re{v̂ e^{jω_pt}})` and
`θ_g = θ_{g0} + ε Re{θ̂ e^{jω_pt}}` with any complex `v̂, θ̂` (a magnitude source, an angle
source, or both with any relative phase), through the multi-channel theorems of
`SmoothForcedOrbitVec`. The GFL field is grid-synchronized (`gfield_shift`), so the general source
form `ForcedOrbit.forced_gridSrc`, `ForcedOrbit.smA1V_gridSrc` applies:
* the relative response `z_rel = v̂ z_V + θ̂ z⁽¹⁾`, with the magnitude response
  `z_V = (sI − A₀)⁻¹ b_V` in closed form and the angle response `z⁽¹⁾` of `AngleModulation`;
* `A₁ = A₁^{(θ)}(z_rel) + v̂ A₀^{(V)}`: the angle part acts only through the relative response, and
  the magnitude modulates directly the five elements proportional to `V₀`;
* the pump `g = v̂ g_V + θ̂ g_θ`.

Model boundary.
* The GFL model of `AngleModulation` (PLL and dc-voltage loop, ideal current loop, `i_q = 0`,
  source behind `X_g`) with the source magnitude `V₀(1 + w₀)` and angle `w₁`, in the absolute PLL
  angle (`gfield`); `v_dc ≠ 0`.
* The end-to-end statements are at a Hopf point of the DVC mode as in `AngleModulationHopf`, with
  the decay and detuning `εA₀'` of order `ε`.

Source: slides "Hidden Instability of Grid-Following Converters Under Small Grid Angle
Variations" (KTH, 2026-11-27), pp. 2–27 (model, `A₀`, `A₁`, pump, index); the magnitude channel
and the two-channel source are new, in the form of technical report `GFM_five_unified_A0A1_Gamma`
(2026-11-07) §2.1 (`A₁ = Σ (∂A/∂x_l) z_l + G û`).

Results.
* `e2`, `gfield`, `scaleV`, `scaleV_one`, `gfield_angle`, `gfield_eq_scaled`, `gfield_shift`,
  `contDiffAt_gfield`, `matXV_gfield`, `matXV_gfield_xs`, `gfield_xs` — the model; with the
  magnitude channel at zero it is `afield`; the Jacobian is `J_p` at `V₀(1 + w₀)`.
* `bV`, `gfield_line_V`, `fderivW_gfield_V`, `fderivW_gfield_θ` — the input directions
  `b_V = −i_{d0}(k_{p,PLL}X_g, X_g, 3v_{d0}/2C, 0)` and `b_θ = −A₀e₁`.
* `NV`, `PV`, `zv`, `zv_eq`, `zv_noload`, `ofv_e0`, `hz_gfield` — the forced response; `b_V` and
  `z_V` vanish at no load.
* `smDxV_gfield`, `DxC_gfield`, `A0V`, `smMwV_gfield_V`, `smA1V_gfield` —
  `A₁ = A₁^{(θ)}(z_rel) + v̂ A₀^{(V)}`.
* `gA1_linear`, `A0V_entries`, `grid_modulated_entries`, `grid_ratio`, `pump_superposition` —
  both channels modulate the same five elements `(1,1), (2,1), (3,1), (3,3), (3,4)`;
  `A₁,ik/A₀,ik = v̂ + A₁^{(θ)}_ik(z_rel)/A₀,ik`; `g = v̂ g_V + θ̂ g_θ`.
* `A1_noload`, `A0V_ne_zero` — at no load `A₁ = v̂ A₀^{(V)} ≠ 0`: the magnitude channel pumps
  directly (the PLL gain `k_{p,PLL}v_d` and the dc-loop gains), the angle channel does not.
* `gfield_src_angle`, `harm_src_voltage` — the single-channel sources.
* `orbit_gfl_grid_stable`, `orbit_gfl_grid_unstable`, `orbit_gfl_grid_exp_stable` — end-to-end
  Floquet statements and exponential stability for the general source.

Corrections.
None: an extension.

Family and connection conclusions.
* With `v̂ = 0`, `θ̂ = 1` the statements are those of `AngleModulationHopf` (`gfield_src_angle`,
  `smA1V_gfield`).
* The GFM counterpart is `GFM.VoltageModulation.Core.psfield` (`GFM.VoltageModulationPhasor`):
  the same general source form, with one modulated element instead of five.
-/

noncomputable section
namespace powerlib.GFL.Parametric.AngleModulation
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smJ harm DxC matXV smDxV smMwV smA1V
  smJV fderivWC linC uMag uAng gridSrc)
open scoped Matrix.Norms.Operator

/-- `e₃ = (0, 0, 1, 0)`. -/
def e2 : Fin 4 → ℝ := ![0, 0, 1, 0]

namespace Params
variable (p : Params)

/-- The GFL field under the grid source `V₀(1 + w₀)∠w₁`, in the absolute PLL angle. -/
def gfield (q : (Fin 4 → ℝ) × (Fin 2 → ℝ)) : Fin 4 → ℝ :=
  ![p.kp * (-(p.V0 * (1 + q.2 0)) * Real.sin (q.1 0 - q.2 1) + p.Xg * p.idv q.1) + p.ki * q.1 1,
    -(p.V0 * (1 + q.2 0)) * Real.sin (q.1 0 - q.2 1) + p.Xg * p.idv q.1,
    3 / (2 * p.C) * (p.vd0 * p.id0 -
      p.V0 * (1 + q.2 0) * Real.cos (q.1 0 - q.2 1) * p.idv q.1 / q.1 2),
    q.1 2 - 1]

/-- The parameters with the source magnitude scaled, `V₀ ↦ c V₀`. -/
def scaleV (c : ℝ) : Params := { p with V0 := p.V0 * c }

@[tmio M, powerlib_domain] theorem scaleV_one : p.scaleV 1 = p := by
  cases p; simp [scaleV]

/-- With the magnitude channel at zero the field is the angle-modulation field. -/
@[tmio M, powerlib_domain] theorem gfield_angle (x : Fin 4 → ℝ) (θ : ℝ) :
    p.gfield (x, θ • uAng) = p.afield (x, θ) := by
  funext i
  fin_cases i <;> simp [gfield, afield, uAng]

/-- The field is the angle-modulation field of the scaled parameters plus a constant. -/
@[tmio M, powerlib_domain] theorem gfield_eq_scaled (q : (Fin 4 → ℝ) × (Fin 2 → ℝ)) :
    p.gfield q = (p.scaleV (1 + q.2 0)).afield (q.1, q.2 1) +
      (3 / (2 * p.C) * (p.vd0 - (p.scaleV (1 + q.2 0)).vd0) * p.id0) • e2 := by
  funext i
  fin_cases i <;> simp [gfield, afield, scaleV, idv, vd0, e2]
  ring

/-- Rotating the PLL angle and the grid angle together leaves the field unchanged. -/
@[tmio M, powerlib_domain] theorem gfield_shift (q : (Fin 4 → ℝ) × (Fin 2 → ℝ)) (s : ℝ) :
    p.gfield (q + s • (e0, uAng)) = p.gfield q := by
  funext i
  fin_cases i <;> simp [gfield, idv, e0, uAng, add_sub_add_right_eq_sub]

@[tmio M, powerlib_domain] theorem contDiffAt_gfield {n : WithTop ℕ∞}
    {q : (Fin 4 → ℝ) × (Fin 2 → ℝ)} (hq : q.1 2 ≠ 0) : ContDiffAt ℝ n p.gfield q := by
  have hx : ∀ i : Fin 4, ContDiff ℝ n fun q : (Fin 4 → ℝ) × (Fin 2 → ℝ) => q.1 i := fun i =>
    (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hw : ∀ i : Fin 2, ContDiff ℝ n fun q : (Fin 4 → ℝ) × (Fin 2 → ℝ) => q.2 i := fun i =>
    (contDiff_apply ℝ ℝ i).comp contDiff_snd
  have ha : ContDiff ℝ n fun q : (Fin 4 → ℝ) × (Fin 2 → ℝ) => q.1 0 - q.2 1 := (hx 0).sub (hw 1)
  have hV : ContDiff ℝ n fun q : (Fin 4 → ℝ) × (Fin 2 → ℝ) => p.V0 * (1 + q.2 0) :=
    contDiff_const.mul (contDiff_const.add (hw 0))
  have hid : ContDiff ℝ n fun q : (Fin 4 → ℝ) × (Fin 2 → ℝ) => p.idv q.1 := by
    unfold idv
    exact (contDiff_const.add (contDiff_const.mul ((hx 2).sub contDiff_const))).add
      (contDiff_const.mul (hx 3))
  have hq0 : ContDiff ℝ n fun q : (Fin 4 → ℝ) × (Fin 2 → ℝ) =>
      -(p.V0 * (1 + q.2 0)) * Real.sin (q.1 0 - q.2 1) + p.Xg * p.idv q.1 :=
    (hV.neg.mul (Real.contDiff_sin.comp ha)).add (contDiff_const.mul hid)
  refine contDiffAt_pi.2 fun i => ?_
  fin_cases i
  · exact ((contDiff_const.mul hq0).add (contDiff_const.mul (hx 1))).contDiffAt
  · exact hq0.contDiffAt
  · have hden : ContDiffAt ℝ n (fun q : (Fin 4 → ℝ) × (Fin 2 → ℝ) =>
        p.V0 * (1 + q.2 0) * Real.cos (q.1 0 - q.2 1) * p.idv q.1 / q.1 2) q :=
      (((hV.mul (Real.contDiff_cos.comp ha)).mul hid).contDiffAt).div (hx 2).contDiffAt hq
    exact contDiffAt_const.mul (contDiffAt_const.sub hden)
  · exact ((hx 2).sub contDiff_const).contDiffAt

/-- The partial Jacobian at any state with `v_dc ≠ 0`: the source's `J_p` with the magnitude
`V₀(1 + w₀)` at the relative angle `x₁ − w₁`. -/
@[tmio M, powerlib_domain] theorem matXV_gfield {q : (Fin 4 → ℝ) × (Fin 2 → ℝ)}
    (hq : q.1 2 ≠ 0) : matXV p.gfield q = (p.scaleV (1 + q.2 0)).jac (q.1 - q.2 1 • e0) := by
  set p' := p.scaleV (1 + q.2 0)
  refine ParametricResonance.ForcedOrbit.matXV_of_line
    ((p.contDiffAt_gfield (n := 1) hq).differentiableAt (by norm_num)) fun y => ?_
  have hq' : (q.1, q.2 1).1 2 ≠ 0 := hq
  have hd : DifferentiableAt ℝ p'.afield (q.1, q.2 1) :=
    (p'.contDiffAt_afield (n := 1) hq').differentiableAt (by norm_num)
  have hl := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (ParametricResonance.ForcedOrbit.hasDerivAt_line (q.1, q.2 1) (y, 0)) (by simp)
  have e : ∀ s : ℝ, (q.1, q.2 1) + s • ((y, (0 : ℝ)) : (Fin 4 → ℝ) × ℝ) = (q.1 + s • y, q.2 1) :=
    fun s => by ext <;> simp
  simp only [Function.comp_def, e] at hl
  rw [← ParametricResonance.ForcedOrbit.matX_mulVec, p'.matX_afield hq'] at hl
  have h2 := hl.add_const ((3 / (2 * p.C) * (p.vd0 - p'.vd0) * p.id0) • e2)
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [p.gfield_eq_scaled, p']

/-- At the operating point the Jacobian is `A₀`. -/
@[tmio M, powerlib_domain] theorem matXV_gfield_xs (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    matXV p.gfield (p.xs, 0) = p.A0 := by
  rw [p.matXV_gfield (by simp [xs])]
  simp only [Pi.zero_apply, add_zero, scaleV_one, zero_smul, sub_zero]
  exact p.jac_xs hs

@[tmio M, powerlib_domain] theorem gfield_xs (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    p.gfield (p.xs, 0) = 0 := by
  have h := p.gfield_angle p.xs 0
  rw [zero_smul] at h
  rw [h]
  have := p.field_xs hs
  rw [p.field_eq_afield _ 0] at this
  simpa using this

/-! ### The input directions -/

/-- The magnitude direction `∂F/∂v = −i_{d0}(k_{p,PLL}X_g, X_g, 3v_{d0}/2C, 0)`. -/
def bV : Fin 4 → ℝ := ![-(p.kp * p.Xg * p.id0), -(p.Xg * p.id0), -(p.kdc * p.vd0 * p.id0), 0]

@[tmio M, powerlib_domain] theorem gfield_line_V (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (s : ℝ) : p.gfield (p.xs, 0 + s • uMag) = s • p.bV := by
  funext i
  fin_cases i <;> simp [gfield, xs, uMag, bV, idv, vd0, kdc, mul_assoc, ← hs] <;> ring

@[tmio M, powerlib_domain] theorem fderivW_gfield_V (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    fderiv ℝ p.gfield (p.xs, 0) (0, uMag) = p.bV := by
  refine ParametricResonance.ForcedOrbit.fderivW_of_lineV
    ((p.contDiffAt_gfield (n := 1) (by simp [xs])).differentiableAt (by norm_num)) uMag ?_
  have h := (hasDerivAt_id (0 : ℝ)).smul_const p.bV
  simp only [one_smul] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [p.gfield_line_V hs, id]

/-- The angle direction `∂F/∂θ = −A₀ e₁` (rotational invariance). -/
@[tmio M, powerlib_domain] theorem fderivW_gfield_θ (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    fderiv ℝ p.gfield (p.xs, 0) (0, uAng) = -(p.A0 *ᵥ e0) := by
  rw [ParametricResonance.ForcedOrbit.fderivW_shift p.gfield_shift
    ((p.contDiffAt_gfield (n := 1) (by simp [xs])).differentiableAt (by norm_num)),
    p.matXV_gfield_xs hs]

/-! ### The forced response to a general grid source -/

/-- `N_V(s) = L_dc(s) + (3v_{d0}/2C)(k_pv s + k_iv)`. -/
def NV (s : ℂ) : ℂ := p.Ldc s + p.kdc * p.vd0 * (p.kpv * s + p.kiv)

/-- `P_V(s) = v_{d0} s² + (k_{p,PLL} s + k_{i,PLL})(v_{d0}² + X_g² i_{d0}²)`. -/
def PV (s : ℂ) : ℂ := p.vd0 * s ^ 2 + (p.kp * s + p.ki) * (p.vd0 ^ 2 + p.Xg ^ 2 * p.id0 ^ 2)

/-- The response to the magnitude channel, `z_V = (sI − A₀)⁻¹ b_V`, in closed form. -/
def zv (s : ℂ) : Fin 4 → ℂ :=
  ![-(p.Xg * p.id0 * (p.kp * s + p.ki) * p.NV s) / p.Dg s, -(p.Xg * p.id0 * s * p.NV s) / p.Dg s,
    -(p.kdc * p.id0 * s * p.PV s) / p.Dg s, -(p.kdc * p.id0 * p.PV s) / p.Dg s]

@[tmio M, powerlib_domain] theorem zv_eq {s : ℂ} (hD : p.Dg s ≠ 0) :
    s • p.zv s - p.A0.map (algebraMap ℝ ℂ) *ᵥ p.zv s = ofv p.bV := by
  funext i
  fin_cases i <;> simp [zv, A0, bV, ofv, mulVec, dotProduct, Fin.sum_univ_four] <;> field_simp <;>
    simp only [Dg, Ldc, Gam, A31, NV, PV, kdc] <;> push_cast <;> ring

/-- At no load the magnitude channel does not force the state: `b_V = 0`, `z_V = 0`. -/
@[tmio M, powerlib_domain] theorem zv_noload (h : p.id0 = 0) (s : ℂ) : p.bV = 0 ∧ p.zv s = 0 := by
  refine ⟨?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp [bV, zv, h]

@[tmio M, powerlib_domain] theorem ofv_e0 : ofv e0 = e0c := by
  funext i; fin_cases i <;> simp [ofv, e0, e0c]


/-- The forced response to the source `(v̂, θ̂)` in the absolute angle:
`z = v̂ z_V + θ̂ (z⁽¹⁾ + e₁)`; in the relative angle `z − θ̂e₁ = v̂ z_V + θ̂ z⁽¹⁾`. -/
@[tmio M, powerlib_domain] theorem hz_gfield (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) {ω : ℝ}
    (hD : p.Dg (ω * I) ≠ 0) (v θ : ℂ) :
    ((ω : ℂ) * I) • (v • p.zv (ω * I) + θ • (p.zc (ω * I) + e0c)) -
        (matXV p.gfield (p.xs, 0)).map (algebraMap ℝ ℂ) *ᵥ
          (v • p.zv (ω * I) + θ • (p.zc (ω * I) + e0c)) =
      fderivWC p.gfield (p.xs, 0) (gridSrc v θ) := by
  have hd : DifferentiableAt ℝ p.gfield (p.xs, 0) :=
    (p.contDiffAt_gfield (n := 1) (by simp [xs])).differentiableAt (by norm_num)
  rw [gridSrc, ParametricResonance.ForcedOrbit.forced_shift p.gfield_shift hd,
    ParametricResonance.ForcedOrbit.fderivWC_smul_ofv, p.fderivW_gfield_V hs, p.matXV_gfield_xs hs,
    ofv_e0]
  have h1 := p.zv_eq hD
  have h2 := p.zc_eq hD
  have e : v • p.zv (ω * I) + θ • (p.zc (ω * I) + e0c) - θ • e0c =
      v • p.zv (ω * I) + θ • p.zc (ω * I) := by rw [smul_add]; abel
  rw [e, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  calc ((ω : ℂ) * I) • (v • p.zv (ω * I) + θ • p.zc (ω * I)) -
        (v • (p.A0.map (algebraMap ℝ ℂ) *ᵥ p.zv (ω * I)) +
          θ • (p.A0.map (algebraMap ℝ ℂ) *ᵥ p.zc (ω * I))) =
      v • (((ω : ℂ) * I) • p.zv (ω * I) - p.A0.map (algebraMap ℝ ℂ) *ᵥ p.zv (ω * I)) +
        θ • (((ω : ℂ) * I) • p.zc (ω * I) - p.A0.map (algebraMap ℝ ℂ) *ᵥ p.zc (ω * I)) := by
        module
    _ = _ := by rw [h1, h2]; module

/-! ### `A₁` for a general grid source -/

/-- The second derivative along the state is that of the angle-modulation field. -/
@[tmio M, powerlib_domain] theorem smDxV_gfield (y : Fin 4 → ℝ) :
    smDxV p.gfield (p.xs, 0) y = smDx p.afield (p.xs, 0) y := by
  have hq : (p.xs, (0 : Fin 2 → ℝ)).1 2 ≠ 0 := by simp [xs]
  have hqa : (p.xs, (0 : ℝ)).1 2 ≠ 0 := by simp [xs]
  have hF2 : ContDiffAt ℝ 2 p.gfield (p.xs, 0) := p.contDiffAt_gfield hq
  have hA2 : ContDiffAt ℝ 2 p.afield (p.xs, 0) := p.contDiffAt_afield hqa
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (p.xs + t • y) 2 ≠ 0 := by
    have hc : Continuous fun t : ℝ => (p.xs + t • y) 2 := by fun_prop
    exact (hc.tendsto 0).eventually_ne (by simp [xs])
  refine ParametricResonance.ForcedOrbit.smDxV_of_line hF2 y
    (Jr := fun t => matX p.afield ((p.xs, (0 : ℝ)).1 + t • y, (p.xs, (0 : ℝ)).2)) ?_ ?_
  · filter_upwards [hev] with t ht
    rw [p.matXV_gfield ht, p.matX_afield ht]
    simp [scaleV_one]
  · intro i j
    have h := ParametricResonance.ForcedOrbit.hasDerivAt_matX_line hA2 (y, 0) i j
    have e : ∀ t : ℝ, (p.xs, (0 : ℝ)) + t • ((y, (0 : ℝ)) : (Fin 4 → ℝ) × ℝ) =
        ((p.xs, (0 : ℝ)).1 + t • y, (p.xs, (0 : ℝ)).2) := fun t => by ext <;> simp
    simp only [e] at h
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    simpa [Function.comp_def, ParametricResonance.ForcedOrbit.smDx] using h2

/-- The modulation along the relative response is the source's `A₁`: `D_x(∂ₓF) z = A₁(z)`. -/
@[tmio M, powerlib_domain] theorem DxC_gfield (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (z : Fin 4 → ℂ) : DxC (smDxV p.gfield (p.xs, 0)) z = p.gA1 z := by
  ext i j
  simp only [DxC, p.smDxV_gfield, p.smDx_afield]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [dJ, gA1, b1, b3, b4, ih, vh, hs, Complex.mul_re, Complex.mul_im,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-- The magnitude-proportional part of `A₀`: the five elements proportional to `V₀`. -/
def A0V : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-p.kp * p.vd0, 0, 0, 0;
    -p.vd0, 0, 0, 0;
    p.A31, 0, -(3 * p.vd0 * (p.kpv - p.id0)) / (2 * p.C), -(3 * p.vd0 * p.kiv) / (2 * p.C);
    0, 0, 0, 0]

/-- The direct modulation by the magnitude: `D_v(∂ₓF) = A₀^{(V)}`. -/
@[tmio M, powerlib_domain] theorem smMwV_gfield_V (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) :
    smMwV p.gfield (p.xs, 0) uMag = p.A0V := by
  have hF2 : ContDiffAt ℝ 2 p.gfield (p.xs, 0) := p.contDiffAt_gfield (by simp [xs])
  refine ParametricResonance.ForcedOrbit.smMwV_of_line hF2 uMag
    (Jr := fun t => p.A0 + t • p.A0V) (Filter.Eventually.of_forall fun t => ?_) fun i j => ?_
  · rw [p.matXV_gfield (by simp [xs])]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jac, scaleV, xs, A0, A0V, idv, uMag, A31, vd0, mul_assoc] <;>
      first | ring1 | linear_combination (3 / 2 * p.C⁻¹ * p.id0 * (1 + t)) * hs
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (p.A0V i j)).const_add (p.A0 i j)

/-- `A₁` for the source `(v̂, θ̂)`: `A₁ = A₁^{(θ)}(z_rel) + v̂ A₀^{(V)}`, with the relative
response `z_rel = z − θ̂ e₁` and the source's `A₁^{(θ)} = gA1`. -/
@[tmio M, powerlib_domain] theorem smA1V_gfield (hs : p.V0 * Real.sin p.δ0 = p.Xg * p.id0)
    (z : Fin 4 → ℂ) (v θ : ℂ) :
    smA1V p.gfield (p.xs, 0) (gridSrc v θ) (z + θ • e0c) =
      p.gA1 z + v • p.A0V.map (algebraMap ℝ ℂ) := by
  have hF2 : ContDiffAt ℝ 2 p.gfield (p.xs, 0) := p.contDiffAt_gfield (by simp [xs])
  rw [gridSrc, ParametricResonance.ForcedOrbit.smA1V_shift p.gfield_shift hF2, ofv_e0,
    add_sub_cancel_right, ParametricResonance.ForcedOrbit.smA1V, p.DxC_gfield hs,
    ParametricResonance.ForcedOrbit.linC_smul_ofv, p.smMwV_gfield_V hs]

/-! ### Structure of `A₁`: the two channels modulate the same five elements -/

/-- `A₁^{(θ)}` is linear in the response. -/
@[tmio M, powerlib_domain] theorem gA1_linear (a b : ℂ) (z z' : Fin 4 → ℂ) :
    p.gA1 (a • z + b • z') = a • p.gA1 z + b • p.gA1 z' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gA1, b1, b3, b4, ih, vh] <;> ring

/-- Each of the five modulated elements is proportional to `V₀`: `A₀^{(V)}` agrees with `A₀` on
them. -/
@[tmio M, powerlib_domain] theorem A0V_entries :
    p.A0V 0 0 = p.A0 0 0 ∧ p.A0V 1 0 = p.A0 1 0 ∧ p.A0V 2 0 = p.A0 2 0 ∧
      p.A0V 2 2 = p.A0 2 2 ∧ p.A0V 2 3 = p.A0 2 3 := by
  simp [A0V, A0]

/-- Outside the five elements `(1,1), (2,1), (3,1), (3,3), (3,4)` neither channel modulates. -/
@[tmio M, powerlib_domain] theorem grid_modulated_entries (z : Fin 4 → ℂ) (v : ℂ) {i j : Fin 4}
    (h : (i, j) ∉ ({(0, 0), (1, 0), (2, 0), (2, 2), (2, 3)} : Finset (Fin 4 × Fin 4))) :
    (p.gA1 z + v • p.A0V.map (algebraMap ℝ ℂ)) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [gA1, A0V]

/-- The relative modulation of a modulated element under the source `(v̂, θ̂)`:
`A₁,ik/A₀,ik = v̂ + A₁^{(θ)}_ik(z_rel)/A₀,ik`. -/
@[tmio M, powerlib_domain] theorem grid_ratio (z : Fin 4 → ℂ) (v : ℂ) {i j : Fin 4}
    (hA : (p.A0 i j : ℂ) ≠ 0) (hV : p.A0V i j = p.A0 i j) :
    (p.gA1 z + v • p.A0V.map (algebraMap ℝ ℂ)) i j / (p.A0 i j : ℂ) =
      v + p.gA1 z i j / (p.A0 i j : ℂ) := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, hV, smul_eq_mul]
  field_simp
  simp [algebraMap]
  ring

/-- The pump of the source `(v̂, θ̂)` is the superposition `g = v̂ g_V + θ̂ g_θ`, with
`g_V = l (A₁^{(θ)}(z_V) + A₀^{(V)}) r̄` and the angle pump `g_θ = l A₁^{(θ)}(z⁽¹⁾) r̄`. -/
@[tmio M, powerlib_domain] theorem pump_superposition (l r zV zθ : Fin 4 → ℂ) (v θ : ℂ) :
    l ⬝ᵥ ((p.gA1 (v • zV + θ • zθ) + v • p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star r) =
      v * (l ⬝ᵥ ((p.gA1 zV + p.A0V.map (algebraMap ℝ ℂ)) *ᵥ star r)) +
        θ * (l ⬝ᵥ (p.gA1 zθ *ᵥ star r)) := by
  rw [p.gA1_linear]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  ring

/-- At no load the angle channel does not pump and the magnitude channel pumps directly:
`A₁ = v̂ A₀^{(V)}` for every source and frequency. -/
@[tmio M, powerlib_domain] theorem A1_noload (h : p.id0 = 0) (v θ s : ℂ) :
    p.gA1 (v • p.zv s + θ • p.zc s) + v • p.A0V.map (algebraMap ℝ ℂ) =
      v • p.A0V.map (algebraMap ℝ ℂ) := by
  rw [p.gA1_linear, (p.zv_noload h s).2, p.gA1_zc_noload h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gA1, b1, b3, b4, ih, vh, h]

/-- At no load `A₀^{(V)} ≠ 0` when `v_{d0} ≠ 0`: the PLL gain `k_{p,PLL} v_d` is modulated by the
magnitude directly. -/
@[tmio M, powerlib_domain] theorem A0V_ne_zero (hv : p.vd0 ≠ 0) : p.A0V ≠ 0 := by
  intro h
  have := congrFun (congrFun h 1) 0
  simp [A0V] at this
  exact hv this

/-! ### The general source reduces to the single-channel sources -/

/-- The angle source `θ̂ = 1` is the drive of `AngleModulation`. -/
@[tmio M, powerlib_domain] theorem gfield_src_angle (x : Fin 4 → ℝ) (ε ω t : ℝ) :
    p.gfield (x, 0 + ε • harm (gridSrc 0 1) ω t) =
      p.afield (x, 0 + ε * (1 * Real.cos (ω * t))) := by
  have e : (0 : Fin 2 → ℝ) + ε • harm (gridSrc 0 1) ω t = (ε * Real.cos (ω * t)) • uAng := by
    funext k; fin_cases k <;> simp [harm, gridSrc, ofv, uMag, uAng]
  rw [e, p.gfield_angle]
  simp

/-- The magnitude source `v̂ = 1`: `V = V₀(1 + ε cos ω_pt)` at the grid angle `θ_{g0}`. -/
@[tmio M, powerlib_domain] theorem harm_src_voltage (ω t : ℝ) :
    harm (gridSrc 1 0) ω t = Real.cos (ω * t) • uMag := by
  funext k; fin_cases k <;> simp [harm, gridSrc, ofv, uMag, uAng]

/-! ### End-to-end at the Hopf point of the DVC mode -/

/-- The GFL converter under the grid source `V = V₀(1 + ε Re{v̂ e^{j2Ωt}})`,
`θ_g = θ_{g0} + ε Re{θ̂ e^{j2Ωt}}` (any complex `v̂, θ̂`), end-to-end, stability. At a Hopf point of
`A₀`, with the damping and detuning `εA₀'`, `Re λ₁ < 0` and `|g/2| < |λ₁|`
(`g = l [A₁^{(θ)}(v̂ z_V + θ̂ z⁽¹⁾) + v̂ A₀^{(V)}] r̄` at `2jΩ`) give, for all small `ε > 0`, the
forced orbit with all Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_grid_stable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (v θ : ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + v • p.A0V.map (algebraMap ℝ ℂ)) *ᵥ
        star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.gfield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm (gridSrc v θ) (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.gfield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm (gridSrc v θ) (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (w : Fin 4 → ℂ), w ≠ 0 →
          (Periodic.monodromy (fun t => smJV p.gfield (p.xs, 0) (gridSrc v θ) (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ w = μ • w → ‖μ‖ < 1 := by
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  have hq0 : (p.xs, (0 : Fin 2 → ℝ)).1 2 ≠ 0 := by simp [xs]
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matXV p.gfield (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matXV_gfield_xs hsd, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_gfield hsd (ω := 2 * Ω) hD2 v θ
  have hzeq : v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • (p.zc (((2 * Ω : ℝ) : ℂ) * I) + e0c) =
      (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + θ • e0c := by
    rw [smul_add]; abel
  rw [hzeq] at hz
  have hA1 := p.smA1V_gfield hsd
    (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) v θ
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable_vec
    (p.contDiffAt_gfield hq0) (p.gfield_xs hsd) (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0'
    hsrs hz A0' ?_ ?_
  · rw [hLm, hRm]; exact hs
  · rw [hLm, hRm, hA1]; exact hg

/-- The GFL converter under the grid source `(v̂, θ̂)`, end-to-end, parametric instability:
`|λ₁| < |g/2|`. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_grid_unstable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (v θ : ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + v • p.A0V.map (algebraMap ℝ ℂ)) *ᵥ
        star (p.gright (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (p.gfield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm (gridSrc v θ) (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (p.gfield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
          ε • harm (gridSrc v θ) (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable
          (fun t => smJV p.gfield (p.xs, 0) (gridSrc v θ) (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  have hq0 : (p.xs, (0 : Fin 2 → ℝ)).1 2 ≠ 0 := by simp [xs]
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matXV p.gfield (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matXV_gfield_xs hsd, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_gfield hsd (ω := 2 * Ω) hD2 v θ
  have hzeq : v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • (p.zc (((2 * Ω : ℝ) : ℂ) * I) + e0c) =
      (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + θ • e0c := by
    rw [smul_add]; abel
  rw [hzeq] at hz
  have hA1 := p.smA1V_gfield hsd
    (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) v θ
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable_vec
    (p.contDiffAt_gfield hq0) (p.gfield_xs hsd) (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0'
    hsrs hz A0' ?_
  rw [hLm, hRm, hA1]; exact hg

/-- The GFL converter under the grid source `(v̂, θ̂)`, end-to-end with orbital stability: in the
stable case the forced orbit is locally exponentially stable for the nonlinear driven system. -/
@[tmio M, powerlib_domain] theorem orbit_gfl_grid_exp_stable
    (hsd : p.V0 * Real.sin p.δ0 = p.Xg * p.id0) {Ω : ℝ} (hΩ : 0 < Ω) (hC : p.C ≠ 0)
    (hki : p.ki ≠ 0) (hL : p.Ldc (Ω * I) ≠ 0) (hA : p.da1 = p.da3 * Ω ^ 2)
    (hB : p.da0 = (p.da2 - Ω ^ 2) * Ω ^ 2) (h3 : 0 < p.da3) (hq : 0 < p.da2 - Ω ^ 2)
    (v θ : ℂ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))).re < 0)
    (hg : ‖p.gleft (Ω * I) ⬝ᵥ ((p.gA1 (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) +
        θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + v • p.A0V.map (algebraMap ℝ ℂ)) *ᵥ
        star (p.gright (Ω * I))) / 2‖ ^ 2 <
      ‖p.gleft (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.gright (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (p.gfield ((p.xs, 0).1 + y t, (p.xs, 0).2 +
        ε • harm (gridSrc v θ) (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t w => p.gfield ((p.xs, 0).1 + w, (p.xs, 0).2 +
          ε • harm (gridSrc v θ) (2 * Ω) t) + ε • (A0' *ᵥ w)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ := p.gspectral hC hΩ.ne' hki hL hA hB h3 hq
  obtain ⟨-, -, hD2⟩ := p.ghopf_facts hΩ.ne' hA hB h3
  have hq0 : (p.xs, (0 : Fin 2 → ℝ)).1 2 ≠ 0 := by simp [xs]
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hLm, hRm, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matXV p.gfield (p.xs, 0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [p.matXV_gfield_xs hsd, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := p.hz_gfield hsd (ω := 2 * Ω) hD2 v θ
  have hzeq : v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • (p.zc (((2 * Ω : ℝ) : ℂ) * I) + e0c) =
      (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) + θ • e0c := by
    rw [smul_add]; abel
  rw [hzeq] at hz
  have hA1 := p.smA1V_gfield hsd
    (v • p.zv (((2 * Ω : ℝ) : ℂ) * I) + θ • p.zc (((2 * Ω : ℝ) : ℂ) * I)) v θ
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable_vec
    (p.contDiffAt_gfield hq0) (p.gfield_xs hsd) (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0'
    hsrs hz A0' ?_ ?_
  · rw [hLm, hRm]; exact hs
  · rw [hLm, hRm, hA1]; exact hg

end Params
end powerlib.GFL.Parametric.AngleModulation
