import theorem.GridTiedConverter.GFM.VoltageModulationSmooth
import theorem.ParametricResonance.SmoothForcedOrbitVec

/-! # The GFM synchronizing core under a general grid phasor source

`VoltageModulationSmooth` drives the synchronizing core (general `C³` power map `P(δ, V)`) by the
grid-voltage magnitude alone, and `VoltageModulation` treats magnitude and angle separately. Here
the source is the grid phasor `V∠θ_g` with both channels, `V = V₀ + ε Re{v̂ e^{jω_pt}}`,
`θ_g = ε Re{θ̂ e^{jω_pt}}` with any complex `v̂, θ̂` (any relative phase), through the multi-channel
theorems of `SmoothForcedOrbitVec`. The core is a grid-synchronized field: rotating its angle and
the grid angle together leaves it unchanged (`psfield_shift`). The general source form then reads
* the relative response: `z_δ = z_V,δ v̂ + z_θ,δ θ̂` with `z_θ,δ = −S(s) θ̂`, `S = 1 − d₀/D(s)`;
* the modulation: the single element `(P_f, δ)` by `ω_c(P_δδ z_δ + P_δV v̂)` (`A1`);
* the pump: `g = v̂ g_V + θ̂ g_θ`.

Model boundary.
* States `(φ, Δω, P_f)` with the absolute angle `φ`: `φ̇ = ω₀Δω`, `2HΔω̇ = P* − P_f − DΔω`,
  `Ṗ_f = ω_c(P(φ − θ_g, V) − P_f)` (`psfield`); `P` of class `C³`; operating point
  `(δ₀, 0, P(δ₀, V₀))` with `V = V₀`, `θ_g = 0`; the core coefficients are the partial
  derivatives of `P` there.
* Hopf point `aω_c = Ω²`, `d₀ = d₂Ω²`, `d₂ > 0`, drive at `2Ω`, state perturbation `εA₀'`
  (decay and detuning of order `ε`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (`A₁ = Σ (∂A/∂x_l) z_l + G û`), §3 (VSG core); the
two-channel grid source is new.

Results.
* `eδ`, `psfield`, `psfield_mag`, `psfield_shift`, `contDiff_psfield`, `matXV_psfield`,
  `psfield_eq_zero`, `matXV_psfield_eq` — the model; with `θ_g = 0` it is `sfield`.
* `fderivW_psfield`, `smDxV_psfield`, `smMwV_psfield`, `smA1V_psfield` — `B_V`, and
  `A₁(v̂, θ̂; z) = A1(z_δ − θ̂, v̂)` (`ForcedOrbit.smA1V_gridSrc`).
* `forcedθδ`, `forcedθ`, `forcedθ_eq`, `forcedθδ_sens`, `charP_two_ne`, `hz_psfield` — the
  forced response; the relative angle forced by `θ̂` is `−S(s)θ̂`.
* `pump_phasor`, `pump_phasor_flat` — `g = v̂ g_V + θ̂ g_θ`; with `P_δδ = 0` only the magnitude
  channel pumps.
* `orbit_phasor_stable`, `orbit_phasor_unstable` — end-to-end Floquet statements for the general
  source.

Corrections.
None: an extension.

Family and connection conclusions.
* The GFL counterpart is `GFL.Parametric.GridModulation`: both converters satisfy the same
  general source form `ForcedOrbit.forced_gridSrc`, `ForcedOrbit.smA1V_gridSrc`; the GFM core
  modulates one element, the GFL converter five.
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace Core
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 harm DxC matXV smDxV smMwV smA1V
  smJV fderivWC uMag uAng gridSrc)

variable (c : Core)

/-- The angle state `e_δ = (1, 0, 0)`. -/
def eδ : Fin 3 → ℝ := ![1, 0, 0]

/-- The synchronizing core under the grid phasor `w = (V, θ_g)`, in the absolute angle `φ`:
`φ̇ = ω₀Δω`, `2HΔω̇ = P* − P_f − DΔω`, `Ṗ_f = ω_c(P(φ − θ_g, V) − P_f)`. -/
def psfield (P : ℝ × ℝ → ℝ) (Pset : ℝ) (q : (Fin 3 → ℝ) × (Fin 2 → ℝ)) : Fin 3 → ℝ :=
  c.sfield P Pset (q.1 - q.2 1 • eδ, q.2 0)

/-- With the angle channel at zero the field is the magnitude-driven core `sfield`. -/
@[tmio M, powerlib_domain] theorem psfield_mag (P : ℝ × ℝ → ℝ) (Pset : ℝ) (x : Fin 3 → ℝ)
    (V : ℝ) : c.psfield P Pset (x, ![V, 0]) = c.sfield P Pset (x, V) := by
  simp [psfield]

/-- Rotating the converter angle and the grid angle together leaves the field unchanged. -/
@[tmio M, powerlib_domain] theorem psfield_shift (P : ℝ × ℝ → ℝ) (Pset : ℝ)
    (q : (Fin 3 → ℝ) × (Fin 2 → ℝ)) (s : ℝ) :
    c.psfield P Pset (q + s • (eδ, uAng)) = c.psfield P Pset q := by
  simp only [psfield]
  congr 1
  ext i
  · fin_cases i <;> simp [eδ, uAng] <;> rfl
  · simp [uAng]

@[tmio M, powerlib_domain] theorem contDiff_psfield {P : ℝ × ℝ → ℝ} {n : WithTop ℕ∞}
    (hP : ContDiff ℝ n P) (Pset : ℝ) : ContDiff ℝ n (c.psfield P Pset) := by
  have hL : ContDiff ℝ n fun q : (Fin 3 → ℝ) × (Fin 2 → ℝ) =>
      ((q.1 - q.2 1 • eδ, q.2 0) : (Fin 3 → ℝ) × ℝ) :=
    (contDiff_fst.sub (((contDiff_apply ℝ ℝ (1 : Fin 2)).comp contDiff_snd).smul
      contDiff_const)).prodMk ((contDiff_apply ℝ ℝ (0 : Fin 2)).comp contDiff_snd)
  exact (c.contDiff_sfield hP Pset).comp hL

/-- The Jacobian at any state: `sjac` at the relative angle. -/
@[tmio M, powerlib_domain] theorem matXV_psfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (Pset : ℝ) (q : (Fin 3 → ℝ) × (Fin 2 → ℝ)) :
    matXV (c.psfield P Pset) q = c.sjac P (q.1 - q.2 1 • eδ, q.2 0) := by
  refine ParametricResonance.ForcedOrbit.matXV_of_line
    ((c.contDiff_psfield hP Pset).differentiable (by norm_num) _) fun y => ?_
  set g : (Fin 3 → ℝ) × ℝ := (q.1 - q.2 1 • eδ, q.2 0) with hg
  have hd : DifferentiableAt ℝ (c.sfield P Pset) g :=
    (c.contDiff_sfield hP Pset).differentiable (by norm_num) _
  have hl := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (ParametricResonance.ForcedOrbit.hasDerivAt_line g (y, 0)) (by simp)
  rw [← ParametricResonance.ForcedOrbit.matX_mulVec, c.matX_sfield hP] at hl
  refine hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_def, psfield, hg]
  congr 1
  ext i
  · simp; ring
  · simp

@[tmio M, powerlib_domain] theorem psfield_eq_zero (P : ℝ × ℝ → ℝ) (δ0 V0 : ℝ) :
    c.psfield P (P (δ0, V0)) (sxeq P δ0 V0, ![V0, 0]) = 0 := by
  rw [psfield_mag, sfield_eq_zero]

@[tmio M, powerlib_domain] theorem matXV_psfield_eq {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 : ℝ} (hPδ : Pd P (δ0, V0) = c.Pδ) :
    matXV (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0]) = c.A0r := by
  rw [c.matXV_psfield hP]
  simpa using c.sjac_eq hPδ

/-- `∂_V F = B_V` for the magnitude channel. -/
@[tmio M, powerlib_domain] theorem fderivW_psfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 : ℝ} (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV) :
    ofv (fderiv ℝ (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0]) (0, uMag)) = c.Bv := by
  have e : fderiv ℝ (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0]) (0, uMag) =
      fderiv ℝ (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) (0, 1) := by
    refine ParametricResonance.ForcedOrbit.fderivW_of_lineV
      ((c.contDiff_psfield hP _).differentiable (by norm_num) _) uMag ?_
    have hd : DifferentiableAt ℝ (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) :=
      (c.contDiff_sfield hP _).differentiable (by norm_num) _
    have hl := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (ParametricResonance.ForcedOrbit.hasDerivAt_line (sxeq P δ0 V0, V0) (0, 1)) (by simp)
    refine hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp_def, psfield]
    congr 1
    ext i
    · simp [uMag]
    · simp [uMag]
  rw [e, c.fderivW_sfield hP hPV]

@[tmio M, powerlib_domain] theorem smDxV_psfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 : ℝ} (y : Fin 3 → ℝ) :
    smDxV (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0]) y =
      smDx (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) y := by
  refine ParametricResonance.ForcedOrbit.smDxV_eq_smDx
    ((c.contDiff_psfield (n := 2) (hP.of_le (by norm_num)) _).contDiffAt)
    ((c.contDiff_sfield (n := 2) (hP.of_le (by norm_num)) _).contDiffAt) y
    (Filter.Eventually.of_forall fun t => ?_)
  rw [c.matXV_psfield hP, c.matX_sfield hP]
  simp

@[tmio M, powerlib_domain] theorem smMwV_psfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 : ℝ} :
    smMwV (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0]) uMag =
      smM1 (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) := by
  refine ParametricResonance.ForcedOrbit.smMwV_eq_smM1
    ((c.contDiff_psfield (n := 2) (hP.of_le (by norm_num)) _).contDiffAt)
    ((c.contDiff_sfield (n := 2) (hP.of_le (by norm_num)) _).contDiffAt) uMag
    (Filter.Eventually.of_forall fun t => ?_)
  rw [c.matXV_psfield hP, c.matX_sfield hP]
  simp [uMag]

/-- The general source form for the GFM core: `A₁(v̂, θ̂; z) = A₁(z_δ − θ̂, v̂)`, the single element
`(P_f, δ)` modulated by `P_δδ (z_δ − θ̂) + P_δV v̂`. -/
@[tmio M, powerlib_domain] theorem smA1V_psfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 : ℝ} (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (z : Fin 3 → ℂ) (v θ : ℂ) :
    smA1V (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0]) (gridSrc v θ) (z + θ • ofv eδ) =
      c.A1 (z 0) v := by
  have hF2 : ContDiffAt ℝ 2 (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0]) :=
    (c.contDiff_psfield (n := 2) (hP.of_le (by norm_num)) _).contDiffAt
  rw [ParametricResonance.ForcedOrbit.smA1V_gridSrc (c.psfield_shift P _) hF2,
    c.smMwV_psfield hP, c.smM1_sfield hP hPδV]
  have hdx : ∀ y, smDxV (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0]) y =
      !![0, 0, 0; 0, 0, 0; c.ωc * (y 0 * c.Pδδ), 0, 0] := fun y => by
    rw [c.smDxV_psfield hP, c.smDx_sfield hP hPδδ]
  ext i j
  simp only [DxC, hdx, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [A1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-! ### The relative response to the angle channel -/

/-- The relative angle forced by `θ̂`: `z_δ = −θ̂ s(s + a)(s + ω_c)/D(s) = −S(s) θ̂`. -/
def forcedθδ (s θ : ℂ) : ℂ := -(θ * (s * (s + c.a) * (s + c.ωc))) / c.charP s

/-- The relative response to `θ̂`: `(sI − A₀) z = −sθ̂ e_δ`. -/
def forcedθ (s θ : ℂ) : Fin 3 → ℂ :=
  ![c.forcedθδ s θ, s * θ * c.d0 / (c.ω0 * c.charP s),
    -(2 * c.H * s + c.D) * s * θ * c.d0 / (c.ω0 * c.charP s)]

@[tmio M, powerlib_domain] theorem forcedθ_eq {s : ℂ} (θ : ℂ) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hs : c.charP s ≠ 0) :
    (s • (1 : Matrix (Fin 3) (Fin 3) ℂ) - c.A0) *ᵥ c.forcedθ s θ = -(s * θ) • ofv eδ := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have key : s * (s + c.a) * (s + c.ωc) + c.d0 = c.charP s := by simp [charP]
  simp only [forcedθ, forcedθδ]
  generalize c.charP s = P at hs key
  funext i
  fin_cases i
  · simp [A0, eδ, ofv, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]
    field_simp
    linear_combination (norm := skip) (-(s * θ)) * key
    ring_nf
  · simp [A0, eδ, ofv, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply, a]
    field_simp; ring
  · simp [A0, eδ, ofv, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply, a, d0]
    field_simp; ring

/-- The relative angle is the negative loop sensitivity: `z_δ = −(1 − d₀/D(s)) θ̂`. -/
@[tmio M, powerlib_domain] theorem forcedθδ_sens {s : ℂ} (θ : ℂ) (hs : c.charP s ≠ 0) :
    c.forcedθδ s θ = -(1 - c.d0 / c.charP s) * θ := by
  simp only [forcedθδ]
  field_simp
  simp only [charP]
  ring

@[tmio M, powerlib_domain] theorem charP_two_ne {Ω : ℝ} (hΩ : Ω ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2) :
    c.charP (2 * Ω * I) ≠ 0 := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  rw [c.charP_factor Ω hH1 hH2]
  refine mul_ne_zero ?_ ?_
  · intro h; have := congrArg Complex.im h; simp at this; exact hΩ this
  · have : (2 * (Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = -3 * (Ω : ℂ) ^ 2 := by
      linear_combination 4 * (Ω : ℂ) ^ 2 * I_sq
    rw [this]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hΩc)

/-- The forced response to the grid source `(v̂, θ̂)` at `2jΩ`, in the absolute angle:
`z = z_V v̂ + z_θ θ̂ + θ̂ e_δ`. -/
@[tmio M, powerlib_domain] theorem hz_psfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV) (v θ : ℂ) :
    (((2 * Ω : ℝ) : ℂ) * I) • (c.forcedV (2 * Ω * I) v + c.forcedθ (2 * Ω * I) θ + θ • ofv eδ) -
        (matXV (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0])).map (algebraMap ℝ ℂ) *ᵥ
          (c.forcedV (2 * Ω * I) v + c.forcedθ (2 * Ω * I) θ + θ • ofv eδ) =
      fderivWC (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0]) (gridSrc v θ) := by
  have hd : DifferentiableAt ℝ (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0]) :=
    (c.contDiff_psfield hP _).differentiable (by norm_num) _
  have hcp := c.charP_two_ne hΩ hH1 hH2
  rw [ParametricResonance.ForcedOrbit.forced_gridSrc (c.psfield_shift P _) hd,
    c.fderivW_psfield hP hPV, c.matXV_psfield_eq hP hPδ, A0r_map, add_sub_cancel_right]
  have h1 := c.forcedV_eq v hω0 hH hcp
  have h2 := c.forcedθ_eq θ hω0 hH hcp
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h1 h2
  push_cast
  rw [Matrix.mulVec_add, smul_add]
  calc (2 * (Ω : ℂ) * I) • c.forcedV (2 * Ω * I) v + (2 * (Ω : ℂ) * I) • c.forcedθ (2 * Ω * I) θ -
        (c.A0 *ᵥ c.forcedV (2 * Ω * I) v + c.A0 *ᵥ c.forcedθ (2 * Ω * I) θ) =
      ((2 * (Ω : ℂ) * I) • c.forcedV (2 * Ω * I) v - c.A0 *ᵥ c.forcedV (2 * Ω * I) v) +
        ((2 * (Ω : ℂ) * I) • c.forcedθ (2 * Ω * I) θ - c.A0 *ᵥ c.forcedθ (2 * Ω * I) θ) := by abel
    _ = _ := by rw [h1, h2]; module

/-- The GFM pump of the source `(v̂, θ̂)`: the single element gives
`g = −(d₀/D'(λ)) (P_δδ z_δ,rel + P_δV v̂)/P_δ`, with `z_δ,rel = z_V,δ v̂ − S θ̂`. -/
@[tmio M, powerlib_domain] theorem pump_phasor (s l0 v θ : ℂ) (hPδ : c.Pδ ≠ 0) :
    Element.pump (c.A1 (c.forcedVδ s v + c.forcedθδ s θ) v) (c.left l0) (c.right l0) =
      v * Element.pump (c.A1 (c.forcedVδ s 1) 1) (c.left l0) (c.right l0) +
        θ * Element.pump (c.A1 (c.forcedθδ s 1) 0) (c.left l0) (c.right l0) := by
  rw [c.pump_eq _ _ _ hPδ, c.pump_eq _ _ _ hPδ, c.pump_eq _ _ _ hPδ]
  simp only [forcedVδ, forcedθδ]
  ring

/-- With a flat power curve at the operating point (`P_δδ = 0`; the lossless link at no load) the
angle channel does not pump: `g = −(d₀/D'(λ)) P_δV v̂/P_δ` whatever the response. -/
@[tmio M, powerlib_domain] theorem pump_phasor_flat (l0 v zδ : ℂ) (hPδ : c.Pδ ≠ 0)
    (h : c.Pδδ = 0) :
    Element.pump (c.A1 zδ v) (c.left l0) (c.right l0) =
      -(c.d0 / c.charD l0) * (c.PδV * v / c.Pδ) := by
  rw [c.pump_eq _ _ _ hPδ, h]
  simp

/-! ### End-to-end -/

/-- The GFM synchronizing core (general `C³` power map) under the grid source
`V = V₀ + ε Re{v̂ e^{j2Ωt}}`, `θ_g = ε Re{θ̂ e^{j2Ωt}}` (any complex `v̂, θ̂`), end-to-end,
stability: at the Hopf point, `Re λ₁ < 0` and `|g/2| < |λ₁|` with
`g = l A₁(z_V,δ v̂ + z_θ,δ θ̂, v̂) r̄` give, for all small `ε > 0`, the forced orbit with all
Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_stable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (v θ : ℂ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) v + c.forcedθδ (2 * Ω * I) θ) v)
        (c.left (Ω * I)) (c.right (Ω * I)) / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.psfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          ![V0, 0] + ε • harm (gridSrc v θ) (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.psfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          ![V0, 0] + ε • harm (gridSrc v θ) (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (w : Fin 3 → ℂ), w ≠ 0 →
          (Periodic.monodromy (fun t => smJV (c.psfield P (P (δ0, V0))) (sxeq P δ0 V0, ![V0, 0])
            (gridSrc v θ) (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map
            (algebraMap ℝ ℂ) *ᵥ w = μ • w → ‖μ‖ < 1 := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hm := c.matXV_psfield_eq hP hPδ
  have hA1 := c.smA1V_psfield hP hPδδ hPδV
    (c.forcedV (2 * Ω * I) v + c.forcedθ (2 * Ω * I) θ) v θ
  rw [ParametricResonance.Element.pump] at hg
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_stable_vec
    (c.contDiff_psfield hP _).contDiffAt (c.psfield_eq_zero P δ0 V0) hΩ (neg_neg_of_pos hd2)
    (by rw [hm]; exact hr) (by rw [hm]; exact hu) hur (by rw [hm]; exact hr3)
    (by rw [hm]; exact hu3) hur3
    (c.hz_psfield hP hΩ.ne' hω0 hH hH1 hH2 hPδ hPV v θ) A0' hs ?_
  rw [hA1]
  exact hg

/-- The GFM synchronizing core under the grid source `(v̂, θ̂)`, end-to-end, parametric
instability: `|λ₁| < |g/2|`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_unstable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (v θ : ℂ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) v + c.forcedθδ (2 * Ω * I) θ) v)
        (c.left (Ω * I)) (c.right (Ω * I)) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.psfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          ![V0, 0] + ε • harm (gridSrc v θ) (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.psfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          ![V0, 0] + ε • harm (gridSrc v θ) (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (c.psfield P (P (δ0, V0)))
          (sxeq P δ0 V0, ![V0, 0]) (gridSrc v θ) (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hm := c.matXV_psfield_eq hP hPδ
  have hA1 := c.smA1V_psfield hP hPδδ hPδV
    (c.forcedV (2 * Ω * I) v + c.forcedθ (2 * Ω * I) θ) v θ
  rw [ParametricResonance.Element.pump] at hg
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_unstable_vec
    (c.contDiff_psfield hP _).contDiffAt (c.psfield_eq_zero P δ0 V0) hΩ (neg_neg_of_pos hd2)
    (by rw [hm]; exact hr) (by rw [hm]; exact hu) hur (by rw [hm]; exact hr3)
    (by rw [hm]; exact hu3) hur3
    (c.hz_psfield hP hΩ.ne' hω0 hH hH1 hH2 hPδ hPV v θ) A0' ?_
  rw [hA1]
  exact hg

end Core
end VoltageModulation
end powerlib.GFM
