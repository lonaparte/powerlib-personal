import theorem.GridTiedConverter.GFM.VoltageModulationFloquet
import theorem.ParametricResonance.SmoothForcedOrbit

/-! # The voltage-modulated synchronizing core with a general power map: forced orbit and Floquet multipliers

`VoltageModulationOrbit` treats the VSG with constant EMF and a lossless link (the `sin`
nonlinearity). Here the power map is any `C³` function `P(δ, V)`, for instance with losses or with
an EMF magnitude given algebraically by a quasi-static Q–V droop; the coefficients of
`VoltageModulation.Core` are its partial derivatives at the operating point. `SmoothForcedOrbit`
then gives, at the Hopf point of the core, the forced orbit and the Floquet criterion
`|g_V/2| ≶ |λ₁|` with the closed-form pump `gV` of `VoltageModulationFloquet`.

Model boundary.
* States `(δ, Δω, P_f)`: `δ̇ = ω₀ Δω`, `2H Δω̇ = P* − P_f − D Δω`, `Ṗ_f = ω_c(P(δ, V) − P_f)`
  (`sfield`), `P` of class `C³`, `P* = P(δ₀, V₀)`, operating point `(δ₀, 0, P(δ₀, V₀))` (`sxeq`).
* `c.Pδ`, `c.PV`, `c.Pδδ`, `c.PδV` are `∂_δP`, `∂_VP`, `∂²_δP`, `∂_V∂_δP` at `(δ₀, V₀)`; Hopf
  point `a ω_c = Ω²`, `d₀ = d₂Ω²`, `d₂ > 0`, `P_δ ≠ 0`; drive `V₀ + ε V̂ cos 2Ωt`; state
  perturbation `ε A₀'` with any real `A₀'`.
* Dynamic Q–V loops and network dynamics are not part of the model. The exponential stability of
  the nonlinear solutions near the orbit is in `GFMOrbitStability`; the damping change and a
  saturated power map inactive at the operating point are in `GFMParameterShift`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2, §3 (VSG core); the voltage excitation is new.

Results.
* `sfield`, `Pd`, `contDiff_Pd`, `hasDerivAt_P_line`, `contDiff_sfield`, `sjac`, `matX_sfield` —
  the field and its Jacobian at every state.
* `sxeq`, `sfield_eq_zero`, `sjac_eq` (`∂ₓF(x₀) = A0r`), `fderivW_sfield` (`∂_V F = B_V`),
  `smDx_sfield`, `smM1_sfield`, `smA1_sfield` (`A₁ = A₁(z_δ, V̂)`), `zorb_sfield`.
* `orbit_smooth_stable`, `orbit_smooth_unstable` — the end-to-end Floquet statements.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the voltage-modulated synchronizing core (forced orbit, Floquet
multipliers).
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace Core
open Complex Matrix Filter Topology
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)

variable (c : Core)

/-- The nonlinear synchronizing core with a general power map `P(δ, V)`: states
`x = (δ, Δω, P_f)`, `δ̇ = ω₀ Δω`, `Δω̇ = (P* − P_f − D Δω)/(2H)`, `Ṗ_f = ω_c(P(δ, V) − P_f)`. -/
def sfield (P : ℝ × ℝ → ℝ) (Pset : ℝ) (q : (Fin 3 → ℝ) × ℝ) : Fin 3 → ℝ :=
  ![c.ω0 * q.1 1, (Pset - q.1 2 - c.D * q.1 1) / (2 * c.H), c.ωc * (P (q.1 0, q.2) - q.1 2)]

/-- `∂P/∂δ` as a function of `(δ, V)`. -/
def Pd (P : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ := fderiv ℝ P q (1, 0)

omit c in
@[tmio T, powerlib_foundation] theorem contDiff_Pd {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P) :
    ContDiff ℝ 2 (Pd P) :=
  (hP.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const

omit c in
@[tmio T, powerlib_foundation] theorem hasDerivAt_P_line {G : ℝ × ℝ → ℝ} {α β : ℝ}
    (hG : DifferentiableAt ℝ G (α, β)) (u w : ℝ) :
    HasDerivAt (fun s : ℝ => G (α + s * u, β + s * w)) (fderiv ℝ G (α, β) (u, w)) 0 := by
  have hl : HasDerivAt (fun s : ℝ => ((α + s * u, β + s * w) : ℝ × ℝ)) (u, w) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => α + s * u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).const_add α
    have h2 : HasDerivAt (fun s : ℝ => β + s * w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w).const_add β
    exact h1.prodMk h2
  exact hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

@[tmio M, powerlib_domain] theorem contDiff_sfield {P : ℝ × ℝ → ℝ} {n : WithTop ℕ∞}
    (hP : ContDiff ℝ n P) (Pset : ℝ) : ContDiff ℝ n (c.sfield P Pset) := by
  have hx : ∀ i : Fin 3, ContDiff ℝ n fun q : (Fin 3 → ℝ) × ℝ => q.1 i := fun i =>
    (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hPq : ContDiff ℝ n fun q : (Fin 3 → ℝ) × ℝ => P (q.1 0, q.2) :=
    hP.comp ((hx 0).prodMk contDiff_snd)
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_const.mul (hx 1)
  · exact ((contDiff_const.sub (hx 2)).sub (contDiff_const.mul (hx 1))).div_const _
  · exact contDiff_const.mul (hPq.sub (hx 2))

/-- The Jacobian of the nonlinear core at `(x, V)`. -/
def sjac (P : ℝ × ℝ → ℝ) (q : (Fin 3 → ℝ) × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, c.ω0, 0; 0, -c.D / (2 * c.H), -1 / (2 * c.H); c.ωc * Pd P (q.1 0, q.2), 0, -c.ωc]

@[tmio M, powerlib_domain] theorem matX_sfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (Pset : ℝ) (q : (Fin 3 → ℝ) × ℝ) : matX (c.sfield P Pset) q = c.sjac P q := by
  refine ParametricResonance.ForcedOrbit.matX_of_line
    ((c.contDiff_sfield hP Pset).differentiable (by norm_num) _) fun y => ?_
  have hl : ∀ i, HasDerivAt (fun s : ℝ => (q.1 + s • y) i) (y i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y i)).const_add (q.1 i)
  have hPl := hasDerivAt_P_line ((hP.differentiable (by norm_num)) (q.1 0, q.2)) (y 0) 0
  have hlin : fderiv ℝ P (q.1 0, q.2) (y 0, 0) = y 0 * Pd P (q.1 0, q.2) := by
    rw [Pd, show ((y 0, (0 : ℝ)) : ℝ × ℝ) = y 0 • ((1, 0) : ℝ × ℝ) by simp, map_smul,
      smul_eq_mul]
  have hPl' : HasDerivAt (fun s : ℝ => P ((q.1 + s • y) 0, q.2))
      (fderiv ℝ P (q.1 0, q.2) (y 0, 0)) 0 := by
    convert hPl using 1; funext s; simp
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · refine ((hl 1).const_mul c.ω0).congr_deriv ?_
    show _ = (c.sjac P q *ᵥ y) 0
    simp [sjac, mulVec, dotProduct, Fin.sum_univ_three]
  · refine ((((hasDerivAt_const (0 : ℝ) Pset).sub (hl 2)).sub
      ((hl 1).const_mul c.D)).div_const (2 * c.H)).congr_deriv ?_
    show _ = (c.sjac P q *ᵥ y) 1
    simp [sjac, mulVec, dotProduct, Fin.sum_univ_three]; ring
  · refine ((hPl'.sub (hl 2)).const_mul c.ωc).congr_deriv ?_
    show _ = (c.sjac P q *ᵥ y) 2
    rw [hlin]; simp [sjac, mulVec, dotProduct, Fin.sum_univ_three]; ring

/-- The operating point `x₀ = (δ₀, 0, P(δ₀, V₀))`. -/
def sxeq (P : ℝ × ℝ → ℝ) (δ0 V0 : ℝ) : Fin 3 → ℝ := ![δ0, 0, P (δ0, V0)]

@[tmio M, powerlib_domain] theorem sfield_eq_zero (P : ℝ × ℝ → ℝ) (δ0 V0 : ℝ) :
    c.sfield P (P (δ0, V0)) (sxeq P δ0 V0, V0) = 0 := by
  funext i
  fin_cases i <;> simp [sfield, sxeq]

@[tmio M, powerlib_domain] theorem sjac_eq {P : ℝ × ℝ → ℝ} {δ0 V0 : ℝ}
    (hPδ : Pd P (δ0, V0) = c.Pδ) : c.sjac P (sxeq P δ0 V0, V0) = c.A0r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sjac, A0r, sxeq, hPδ]

/-- `∂_V F(x₀, V₀) = B_V`. -/
@[tmio M, powerlib_domain] theorem fderivW_sfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 : ℝ} (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV) :
    ofv (fderiv ℝ (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) (0, 1)) = c.Bv := by
  have hPl := hasDerivAt_P_line ((hP.differentiable (by norm_num)) (δ0, V0)) 0 1
  have e : fderiv ℝ (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) (0, 1) =
      ![0, 0, c.ωc * c.PV] := by
    refine ParametricResonance.ForcedOrbit.fderivW_of_line
      ((c.contDiff_sfield hP _).differentiable (by norm_num) _) (hasDerivAt_pi.2 fun i => ?_)
    fin_cases i
    · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp [sfield, sxeq])
    · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp [sfield, sxeq])
    · have h := (hPl.sub_const (P (δ0, V0))).const_mul c.ωc
      rw [hPV] at h
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp [sfield, sxeq])
  rw [e]
  funext i
  fin_cases i <;> simp [ofv, Bv]

@[tmio M, powerlib_domain] theorem smDx_sfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 : ℝ} (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ) (y : Fin 3 → ℝ) :
    smDx (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) y =
      !![0, 0, 0; 0, 0, 0; c.ωc * (y 0 * c.Pδδ), 0, 0] := by
  have hPl := hasDerivAt_P_line (((contDiff_Pd hP).differentiable (by norm_num)) (δ0, V0))
    (y 0) 0
  have hlin : fderiv ℝ (Pd P) (δ0, V0) (y 0, 0) = y 0 * c.Pδδ := by
    rw [show ((y 0, (0 : ℝ)) : ℝ × ℝ) = y 0 • ((1, 0) : ℝ × ℝ) by simp, map_smul, smul_eq_mul,
      hPδδ]
  rw [hlin] at hPl
  refine ParametricResonance.ForcedOrbit.smDx_of_line
    ((c.contDiff_sfield (n := 2) (hP.of_le (by norm_num)) _).contDiffAt) y
    (Jr := fun t => c.sjac P (sxeq P δ0 V0 + t • y, V0))
    (Filter.Eventually.of_forall fun t => c.matX_sfield hP _ (sxeq P δ0 V0 + t • y, V0))
    fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) c.ω0
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.D / (2 * c.H))
  · exact hasDerivAt_const (0 : ℝ) (-1 / (2 * c.H))
  · exact (hPl.const_mul c.ωc).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp [sjac, sxeq])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.ωc)

@[tmio M, powerlib_domain] theorem smM1_sfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 : ℝ} (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) :
    smM1 (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) =
      !![0, 0, 0; 0, 0, 0; c.ωc * c.PδV, 0, 0] := by
  have hPl := hasDerivAt_P_line (((contDiff_Pd hP).differentiable (by norm_num)) (δ0, V0)) 0 1
  rw [hPδV] at hPl
  refine ParametricResonance.ForcedOrbit.smM1_of_line
    ((c.contDiff_sfield (n := 2) (hP.of_le (by norm_num)) _).contDiffAt)
    (Jr := fun t => c.sjac P (sxeq P δ0 V0, V0 + t))
    (Filter.Eventually.of_forall fun t => c.matX_sfield hP _ (sxeq P δ0 V0, V0 + t))
    fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) c.ω0
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.D / (2 * c.H))
  · exact hasDerivAt_const (0 : ℝ) (-1 / (2 * c.H))
  · exact (hPl.const_mul c.ωc).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp [sjac, sxeq])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.ωc)

/-- The modulation of the nonlinear core along `(z, V̂)` is the core's `A₁(z_δ, V̂)`. -/
@[tmio M, powerlib_domain] theorem smA1_sfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 : ℝ} (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (Vh : ℝ) (z : Fin 3 → ℂ) :
    smA1 (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) Vh z = c.A1 (z 0) Vh := by
  have hdx := c.smDx_sfield hP hPδδ
  have hm := c.smM1_sfield hP hPδV
  ext i j
  simp only [ParametricResonance.ForcedOrbit.smA1, ParametricResonance.ForcedOrbit.DxC, hdx, hm,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [A1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-- The first-order orbit `z = z_V(2jΩ) V̂` solves `(2jΩ − ∂ₓF) z = V̂ ∂_V F` at the Hopf point. -/
@[tmio M, powerlib_domain] theorem zorb_sfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV) (Vh : ℝ) :
    (((2 * Ω : ℝ) : ℂ) * I) • c.forcedV (2 * Ω * I) Vh -
        (matX (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ
          c.forcedV (2 * Ω * I) Vh =
      (Vh : ℂ) • fun i =>
        ((fderiv ℝ (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) (0, 1) i : ℝ) : ℂ) := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hcp : c.charP (2 * Ω * I) ≠ 0 := by
    rw [c.charP_factor Ω hH1 hH2]
    refine mul_ne_zero ?_ ?_
    · intro h; have := congrArg Complex.im h; simp at this; exact hΩ this
    · have : (2 * (Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = -3 * (Ω : ℂ) ^ 2 := by
        linear_combination 4 * (Ω : ℂ) ^ 2 * I_sq
      rw [this]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hΩc)
  have hf := c.forcedV_eq (Vh : ℂ) hω0 hH hcp
  have hb : (fun i => ((fderiv ℝ (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) (0, 1) i : ℝ) :
      ℂ)) = c.Bv := c.fderivW_sfield hP hPV
  rw [hb, c.matX_sfield hP, c.sjac_eq hPδ, A0r_map, ← hf, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  push_cast; ring_nf

/-- The nonlinear synchronizing core with a general `C³` power map `P(δ, V)` (constant EMF or not,
losses, quasi-static Q–V droop), grid-voltage modulation, end-to-end, stability. The core
coefficients are the partial derivatives of `P` at `(δ₀, V₀)`; at the Hopf point
(`a ω_c = Ω²`, `d₀ = d₂Ω²`, `d₂ > 0`) with `V = V₀ + ε V̂ cos 2Ωt` and the state-matrix
perturbation `ε A₀'`: `Re λ₁ < 0` and `|g_V/2| < |λ₁|` (`g_V = gV`) give, for all small `ε > 0`,
the forced periodic orbit (unique in the ball of radius `cε`) with all Floquet multipliers inside
the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_smooth_stable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2)
    (hPδ0 : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.gV V0 Ω Vh / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.sfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.sfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) Vh
            (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v =
            μ • v → ‖μ‖ < 1 := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hm : matX (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) = c.A0r := by
    rw [c.matX_sfield hP, c.sjac_eq hPδ]
  have hp := c.pump_voltage_hopf V0 Ω Vh hPδ0 hV0 hH hΩ.ne' hd2.ne' hH1 hH2
  rw [ParametricResonance.Element.pump] at hp
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_stable
    (c.contDiff_sfield hP _).contDiffAt (c.sfield_eq_zero P δ0 V0) hΩ (neg_neg_of_pos hd2)
    (by rw [hm]; exact hr) (by rw [hm]; exact hu) hur (by rw [hm]; exact hr3)
    (by rw [hm]; exact hu3) hur3 (c.zorb_sfield hP hΩ.ne' hω0 hH hH1 hH2 hPδ hPV Vh) A0' hs ?_
  rw [c.smA1_sfield hP hPδδ hPδV]
  have e : c.forcedV (2 * Ω * I) Vh 0 = c.forcedVδ (2 * Ω * I) Vh := rfl
  rw [e, hp]; exact hg

/-- The nonlinear synchronizing core with a general `C³` power map, end-to-end parametric
instability: `|λ₁| < |g_V/2|` makes the forced periodic orbit Floquet unstable. -/
@[tmio M, powerlib_domain] theorem orbit_smooth_unstable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2)
    (hPδ0 : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖c.gV V0 Ω Vh / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.sfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.sfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) Vh
          (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hm : matX (c.sfield P (P (δ0, V0))) (sxeq P δ0 V0, V0) = c.A0r := by
    rw [c.matX_sfield hP, c.sjac_eq hPδ]
  have hp := c.pump_voltage_hopf V0 Ω Vh hPδ0 hV0 hH hΩ.ne' hd2.ne' hH1 hH2
  rw [ParametricResonance.Element.pump] at hp
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_unstable
    (c.contDiff_sfield hP _).contDiffAt (c.sfield_eq_zero P δ0 V0) hΩ (neg_neg_of_pos hd2)
    (by rw [hm]; exact hr) (by rw [hm]; exact hu) hur (by rw [hm]; exact hr3)
    (by rw [hm]; exact hu3) hur3 (c.zorb_sfield hP hΩ.ne' hω0 hH hH1 hH2 hPδ hPV Vh) A0' ?_
  rw [c.smA1_sfield hP hPδδ hPδV]
  have e : c.forcedV (2 * Ω * I) Vh 0 = c.forcedVδ (2 * Ω * I) Vh := rfl
  rw [e, hp]; exact hg

end Core
end VoltageModulation
end powerlib.GFM
