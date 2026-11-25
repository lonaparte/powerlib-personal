import theorem.GridTiedConverter.GFM.Matching.MatchingPump
import theorem.GridTiedConverter.GFM.VoltageModulationSmooth

/-! # Matching control under grid-voltage modulation: forced orbit and Floquet multipliers

End-to-end statement for the four-state matching core of `MatchingPump` when the DC current drawn
by the converter depends on the grid-voltage magnitude, `i_x(δ, V)` of class `C³`. The Jacobian at
the operating point is `jacobian K`, `K = ∂i_x/∂δ`; the voltage enters only the DC-link equation,
and the modulation along the first-order orbit has the single element
`(v, δ): −(K_δδ z_δ + K_δV V̂)/C`. The forced response has a closed form through
`Cτ det(sI − A₀)` (`charPoly`), and the pump is `g_V = −(u_v r̄_δ/C) V̂ (K_δV + K_δδ z_δ(2jΩ))`.
With the eigenvectors of the pair `±jΩ` and a real basis of the stable subspace (hypotheses: the
four-state core has no closed-form eigen-data), `SmoothForcedOrbit` gives the forced orbit and the
Floquet criterion `|g_V/2| ≶ |λ₁|`.

Model boundary.
* States `(δ, v_f, v, i_s)`: `δ̇ = ω_b(v_f − 1)`, `v̇_f = ω_f(v − v_f)`,
  `C v̇ = i_s − G v − i_x(δ, V)`, `τ i̇_s = I* − k_dc(v − 1) − i_s` (`mfield`), quasi-static
  network through `i_x`; operating point `(δ₀, 1, 1, G + i_x(δ₀, V₀))` with
  `I* = G + i_x(δ₀, V₀)` (`meq`).
* `K`, `K_V`, `K_δδ`, `K_δV` the partial derivatives of `i_x` at `(δ₀, V₀)`; `ω_b, ω_f, C, τ ≠ 0`,
  `det(2jΩ − A₀) ≠ 0`; the pair `±jΩ` and the stable basis `W` (`‖e^{TA_s}‖ < 1`) are hypotheses;
  drive `V₀ + ε V̂ cos 2Ωt`; state perturbation `ε A₀'` with any real `A₀'`. Network dynamics and
  the `E = m_a v` effects are excluded; orbital stability is not derived.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2, §3 (matching core); the voltage excitation is new.

Results.
* `mfield`, `contDiff_mfield`, `matX_mfield` (`∂ₓF = jacobian (∂_δ i_x)` at every state), `meq`,
  `mfield_eq_zero`, `fderivW_mfield` (`∂_V F = (0, 0, −K_V/C, 0)`), `smDx_mfield`, `smM1_mfield`,
  `smA1_mfield` — the forced system.
* `Dm`, `mforced`, `mforced_eq` — the forced response
  `z_δ = −K_V ω_f ω_b(1 + τs)/(Cτ det(sI − A₀))`; `mpumpV`, `pump_mfield` — `u A₁ r̄ = g_V`.
* `matching_data`, `orbit_matching_stable`, `orbit_matching_unstable` — the end-to-end Floquet
  statements.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the voltage-modulated matching core (forced orbit, Floquet multipliers).
-/

noncomputable section
namespace powerlib.GFM.Matching
namespace MatchingCore
open Complex Matrix Filter Topology
open scoped Matrix.Norms.Operator
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)
open powerlib.GFM.VoltageModulation.Core (Pd contDiff_Pd hasDerivAt_P_line)

variable (d : MatchingCore)

/-- The matching core with a voltage-dependent DC current `i_x(δ, V)`: states
`(δ, v_f, v, i_s)`, `δ̇ = ω_b(v_f − 1)`, `v̇_f = ω_f(v − v_f)`, `C v̇ = i_s − G v − i_x(δ, V)`,
`τ i̇_s = I* − k_dc(v − 1) − i_s`. -/
def mfield (ixV : ℝ × ℝ → ℝ) (Istar : ℝ) (q : (Fin 4 → ℝ) × ℝ) : Fin 4 → ℝ :=
  ![d.ωb * (q.1 1 - 1), d.ωf * (q.1 2 - q.1 1), (q.1 3 - d.G * q.1 2 - ixV (q.1 0, q.2)) / d.C,
    (Istar - d.kdc * (q.1 2 - 1) - q.1 3) / d.τ]

@[tmio M, powerlib_domain] theorem contDiff_mfield {ixV : ℝ × ℝ → ℝ} {n : WithTop ℕ∞}
    (hP : ContDiff ℝ n ixV) (Istar : ℝ) : ContDiff ℝ n (d.mfield ixV Istar) := by
  have hx : ∀ i : Fin 4, ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => q.1 i := fun i =>
    (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hPq : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => ixV (q.1 0, q.2) :=
    hP.comp ((hx 0).prodMk contDiff_snd)
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_const.mul ((hx 1).sub contDiff_const)
  · exact contDiff_const.mul ((hx 2).sub (hx 1))
  · exact (((hx 3).sub (contDiff_const.mul (hx 2))).sub hPq).div_const _
  · exact ((contDiff_const.sub (contDiff_const.mul ((hx 2).sub contDiff_const))).sub
      (hx 3)).div_const _

@[tmio M, powerlib_domain] theorem matX_mfield {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV)
    (Istar : ℝ) (q : (Fin 4 → ℝ) × ℝ) :
    matX (d.mfield ixV Istar) q = d.jacobian (Pd ixV (q.1 0, q.2)) := by
  refine ParametricResonance.ForcedOrbit.matX_of_line
    ((d.contDiff_mfield hP Istar).differentiable (by norm_num) _) fun y => ?_
  have hl : ∀ i, HasDerivAt (fun s : ℝ => (q.1 + s • y) i) (y i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y i)).const_add (q.1 i)
  have hPl := hasDerivAt_P_line ((hP.differentiable (by norm_num)) (q.1 0, q.2)) (y 0) 0
  have hlin : fderiv ℝ ixV (q.1 0, q.2) (y 0, 0) = y 0 * Pd ixV (q.1 0, q.2) := by
    rw [Pd, show ((y 0, (0 : ℝ)) : ℝ × ℝ) = y 0 • ((1, 0) : ℝ × ℝ) by simp, map_smul,
      smul_eq_mul]
  have hPl' : HasDerivAt (fun s : ℝ => ixV ((q.1 + s • y) 0, q.2))
      (fderiv ℝ ixV (q.1 0, q.2) (y 0, 0)) 0 := by
    convert hPl using 1; funext s; simp
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · refine (((hl 1).sub_const 1).const_mul d.ωb).congr_deriv ?_
    show _ = (d.jacobian (Pd ixV (q.1 0, q.2)) *ᵥ y) 0
    simp [jacobian, mulVec, dotProduct, Fin.sum_univ_four]
  · refine (((hl 2).sub (hl 1)).const_mul d.ωf).congr_deriv ?_
    show _ = (d.jacobian (Pd ixV (q.1 0, q.2)) *ᵥ y) 1
    simp [jacobian, mulVec, dotProduct, Fin.sum_univ_four]; ring
  · refine ((((hl 3).sub ((hl 2).const_mul d.G)).sub hPl').div_const d.C).congr_deriv ?_
    show _ = (d.jacobian (Pd ixV (q.1 0, q.2)) *ᵥ y) 2
    rw [hlin]; simp [jacobian, mulVec, dotProduct, Fin.sum_univ_four]; ring
  · refine ((((hasDerivAt_const (0 : ℝ) Istar).sub (((hl 2).sub_const 1).const_mul d.kdc)).sub
      (hl 3)).div_const d.τ).congr_deriv ?_
    show _ = (d.jacobian (Pd ixV (q.1 0, q.2)) *ᵥ y) 3
    simp [jacobian, mulVec, dotProduct, Fin.sum_univ_four]; ring

/-- The operating point `x₀ = (δ₀, 1, 1, G + i_x(δ₀, V₀))` (with `I* = G + i_x(δ₀, V₀)`). -/
def meq (ixV : ℝ × ℝ → ℝ) (δ0 V0 : ℝ) : Fin 4 → ℝ := ![δ0, 1, 1, d.G + ixV (δ0, V0)]

@[tmio M, powerlib_domain] theorem mfield_eq_zero (ixV : ℝ × ℝ → ℝ) (δ0 V0 : ℝ) :
    d.mfield ixV (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0, V0) = 0 := by
  funext i
  fin_cases i <;> simp [mfield, meq]

@[tmio M, powerlib_domain] theorem fderivW_mfield {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 KV : ℝ} (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV) :
    fderiv ℝ (d.mfield ixV (d.G + ixV (δ0, V0))) (d.meq ixV δ0 V0, V0) (0, 1) =
      ![0, 0, -(KV / d.C), 0] := by
  have hPl := hasDerivAt_P_line ((hP.differentiable (by norm_num)) (δ0, V0)) 0 1
  rw [hKV] at hPl
  refine ParametricResonance.ForcedOrbit.fderivW_of_line
    ((d.contDiff_mfield hP _).differentiable (by norm_num) _) (hasDerivAt_pi.2 fun i => ?_)
  fin_cases i
  · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp [mfield, meq])
  · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp [mfield, meq])
  · have h := ((hasDerivAt_const (0 : ℝ) (d.G + ixV (δ0, V0) - d.G * 1)).sub hPl).div_const d.C
    refine (h.congr_deriv (by simp; ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp [mfield, meq])
  · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp [mfield, meq])

@[tmio M, powerlib_domain] theorem smDx_mfield {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 Kδδ : ℝ} (hKδδ : fderiv ℝ (Pd ixV) (δ0, V0) (1, 0) = Kδδ) (y : Fin 4 → ℝ) :
    smDx (d.mfield ixV (d.G + ixV (δ0, V0))) (d.meq ixV δ0 V0, V0) y =
      !![0, 0, 0, 0; 0, 0, 0, 0; -(y 0 * Kδδ / d.C), 0, 0, 0; 0, 0, 0, 0] := by
  have hPl := hasDerivAt_P_line (((contDiff_Pd hP).differentiable (by norm_num)) (δ0, V0))
    (y 0) 0
  have hlin : fderiv ℝ (Pd ixV) (δ0, V0) (y 0, 0) = y 0 * Kδδ := by
    rw [show ((y 0, (0 : ℝ)) : ℝ × ℝ) = y 0 • ((1, 0) : ℝ × ℝ) by simp, map_smul, smul_eq_mul,
      hKδδ]
  rw [hlin] at hPl
  refine ParametricResonance.ForcedOrbit.smDx_of_line
    ((d.contDiff_mfield (n := 2) (hP.of_le (by norm_num)) _).contDiffAt) y
    (Jr := fun t => d.jacobian (Pd ixV ((d.meq ixV δ0 V0 + t • y) 0, V0)))
    (Filter.Eventually.of_forall fun t => d.matX_mfield hP _ (d.meq ixV δ0 V0 + t • y, V0))
    fun i j => ?_
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hasDerivAt_const (0 : ℝ) _
    | exact ((hPl.div_const d.C).neg).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => by simp [jacobian, meq])

@[tmio M, powerlib_domain] theorem smM1_mfield {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 KδV : ℝ} (hKδV : fderiv ℝ (Pd ixV) (δ0, V0) (0, 1) = KδV) :
    smM1 (d.mfield ixV (d.G + ixV (δ0, V0))) (d.meq ixV δ0 V0, V0) =
      !![0, 0, 0, 0; 0, 0, 0, 0; -(KδV / d.C), 0, 0, 0; 0, 0, 0, 0] := by
  have hPl := hasDerivAt_P_line (((contDiff_Pd hP).differentiable (by norm_num)) (δ0, V0)) 0 1
  rw [hKδV] at hPl
  refine ParametricResonance.ForcedOrbit.smM1_of_line
    ((d.contDiff_mfield (n := 2) (hP.of_le (by norm_num)) _).contDiffAt)
    (Jr := fun t => d.jacobian (Pd ixV (δ0, V0 + t)))
    (Filter.Eventually.of_forall fun t => d.matX_mfield hP _ (d.meq ixV δ0 V0, V0 + t))
    fun i j => ?_
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hasDerivAt_const (0 : ℝ) _
    | exact ((hPl.div_const d.C).neg).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => by simp [jacobian])

/-- `C τ det(sI − A₀)` (`charPoly`). -/
def Dm (K : ℝ) (s : ℂ) : ℂ :=
  (1 + d.τ * s) * (s + d.ωf) * (d.C * s ^ 2 + d.G * s) + d.kdc * s * (s + d.ωf) +
    d.ωb * K * d.ωf * (1 + d.τ * s)

/-- The forced response to the voltage input `(0, 0, −K_V/C, 0)` (per unit `V̂`) at `s`:
`z_δ = −K_V ω_f ω_b (1 + τs)/(Cτ det(sI − A₀))`. -/
def mforced (K KV : ℝ) (s : ℂ) : Fin 4 → ℂ :=
  ![-((KV : ℂ) * d.ωf * d.ωb * (1 + d.τ * s)) / d.Dm K s,
    s * (-((KV : ℂ) * d.ωf * d.ωb * (1 + d.τ * s)) / d.Dm K s) / d.ωb,
    (s + d.ωf) * s * (-((KV : ℂ) * d.ωf * d.ωb * (1 + d.τ * s)) / d.Dm K s) / (d.ωf * d.ωb),
    -(d.kdc * ((s + d.ωf) * s * (-((KV : ℂ) * d.ωf * d.ωb * (1 + d.τ * s)) / d.Dm K s) /
      (d.ωf * d.ωb))) / (1 + d.τ * s)]

@[tmio M, powerlib_domain] theorem mforced_eq (K KV : ℝ) {s : ℂ} (hωb : d.ωb ≠ 0)
    (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (h1 : 1 + d.τ * s ≠ 0) (hD : d.Dm K s ≠ 0) :
    s • d.mforced K KV s - (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ d.mforced K KV s =
      ![0, 0, -((KV : ℂ) / d.C), 0] := by
  have hωb' : (d.ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  have hωf' : (d.ωf : ℂ) ≠ 0 := by exact_mod_cast hωf
  have hC' : (d.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hτ' : (d.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have hDdef : d.Dm K s = (1 + d.τ * s) * (s + d.ωf) * (d.C * s ^ 2 + d.G * s) +
      d.kdc * s * (s + d.ωf) + d.ωb * K * d.ωf * (1 + d.τ * s) := rfl
  have h1' : 1 + s * (d.τ : ℂ) ≠ 0 := by rwa [mul_comm]
  have key : (-((KV : ℂ) * d.ωf * d.ωb * (1 + d.τ * s)) / d.Dm K s) * d.Dm K s =
      -((KV : ℂ) * d.ωf * d.ωb * (1 + d.τ * s)) := div_mul_cancel₀ _ hD
  simp only [mforced]
  generalize -((KV : ℂ) * d.ωf * d.ωb * (1 + d.τ * s)) / d.Dm K s = w at key
  rw [hDdef] at key
  funext i
  fin_cases i
  · simp [jacobian, mulVec, dotProduct, Fin.sum_univ_four]; field_simp; ring
  · simp [jacobian, mulVec, dotProduct, Fin.sum_univ_four]; field_simp; ring
  · simp [jacobian, mulVec, dotProduct, Fin.sum_univ_four]
    field_simp
    linear_combination key
  · simp [jacobian, mulVec, dotProduct, Fin.sum_univ_four]; field_simp; ring

/-- The voltage pump of the matching core: `g_V = −(u_v r̄_δ/C) V̂ (K_δV + K_δδ z_δ(2jΩ))`, with
`u_v`, `r_δ` the `v`- and `δ`-components of the eigenvectors and `K_δδ = ∂²i_x/∂δ²`,
`K_δV = ∂²i_x/∂δ∂V`. -/
def mpumpV (u r : Fin 4 → ℂ) (K Kδδ KδV KV Ω Vh : ℝ) : ℂ :=
  -(u 2 * star (r 0) / d.C) * Vh * (KδV + Kδδ * d.mforced K KV (((2 * Ω : ℝ) : ℂ) * I) 0)

@[tmio M, powerlib_domain] theorem smA1_mfield {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 Kδδ KδV : ℝ} (hKδδ : fderiv ℝ (Pd ixV) (δ0, V0) (1, 0) = Kδδ)
    (hKδV : fderiv ℝ (Pd ixV) (δ0, V0) (0, 1) = KδV) (Vh : ℝ) (z : Fin 4 → ℂ) :
    smA1 (d.mfield ixV (d.G + ixV (δ0, V0))) (d.meq ixV δ0 V0, V0) Vh z =
      !![0, 0, 0, 0; 0, 0, 0, 0; -(((Kδδ : ℂ) * z 0 + Vh * KδV) / d.C), 0, 0, 0; 0, 0, 0, 0] := by
  have hdx := d.smDx_mfield hP hKδδ
  have hm := d.smM1_mfield hP hKδV
  ext i j
  simp only [ParametricResonance.ForcedOrbit.smA1, ParametricResonance.ForcedOrbit.DxC, hdx, hm,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

@[tmio M, powerlib_domain] theorem pump_mfield {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 K Kδδ KδV KV Ω : ℝ} (hKδδ : fderiv ℝ (Pd ixV) (δ0, V0) (1, 0) = Kδδ)
    (hKδV : fderiv ℝ (Pd ixV) (δ0, V0) (0, 1) = KδV) (Vh : ℝ) (u r : Fin 4 → ℂ) :
    u ⬝ᵥ (smA1 (d.mfield ixV (d.G + ixV (δ0, V0))) (d.meq ixV δ0 V0, V0) Vh
      ((Vh : ℂ) • d.mforced K KV (((2 * Ω : ℝ) : ℂ) * I)) *ᵥ star r) =
      d.mpumpV u r K Kδδ KδV KV Ω Vh := by
  rw [d.smA1_mfield hP hKδδ hKδV]
  simp [mpumpV, mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- The data of the matching core at the operating point: Jacobian, first-order orbit, and real
modal coordinates from the eigenvectors and a basis of the stable subspace. -/
@[tmio M, powerlib_domain] theorem matching_data {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 Ω K KV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0)
    (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K) (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV)
    (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0) {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {W : Matrix (Fin 4) (Fin 2) ℝ} {W' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : d.jacobian K * W = W * As) (hWW : W' * W = 1)
    (huW : u ᵥ* W.map (algebraMap ℝ ℂ) = 0) (hWr : W'.map (algebraMap ℝ ℂ) *ᵥ r = 0) (Vh : ℝ) :
    let F := d.mfield ixV (d.G + ixV (δ0, V0))
    let q0 := (d.meq ixV δ0 V0, V0)
    (((2 * Ω : ℝ) : ℂ) * I) • ((Vh : ℂ) • d.mforced K KV (((2 * Ω : ℝ) : ℂ) * I)) -
        (matX F q0).map (algebraMap ℝ ℂ) *ᵥ ((Vh : ℂ) • d.mforced K KV (((2 * Ω : ℝ) : ℂ) * I)) =
      (Vh : ℂ) • (fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ)) ∧
    ∃ (P : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) ℝ) (Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 4) ℝ),
      P * Q = 1 ∧ Q * P = 1 ∧
      Q * matX F q0 * P = Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As ∧
      ParametricResonance.BlockAveraging.physLeft Q = u ∧
      ParametricResonance.BlockAveraging.physRight P = r := by
  intro F q0
  have hm : matX F q0 = d.jacobian K := by
    simp only [F, q0]; rw [d.matX_mfield hP]; simp [meq, hK]
  have h1 : 1 + (d.τ : ℂ) * (((2 * Ω : ℝ) : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hf := d.mforced_eq K KV hωb hωf hC hτ h1 hD2
  have hb : (fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ)) = ![0, 0, -((KV : ℂ) / d.C), 0] := by
    simp only [F, q0]; rw [d.fderivW_mfield hP hKV]
    funext i; fin_cases i <;> simp
  refine ⟨?_, ?_⟩
  · rw [hm, hb, ← hf, smul_sub, Matrix.mulVec_smul, smul_comm]
  · have hW2 : matX F q0 * W = W * As := by rw [hm]; exact hW
    rw [hm] at hW2 ⊢
    obtain ⟨hQP, hPQ, hA0, hL, hR⟩ := ParametricResonance.ForcedOrbit.modal_of_basis
      finSumFinEquiv.symm hΩ.ne' hr hu hur hW2 hWW huW hWr
    refine ⟨_, _, hPQ, hQP, ?_, hL, hR⟩
    rw [hA0, mul_div_cancel_left₀ Ω two_ne_zero]

/-- Matching control with a voltage-dependent DC current `i_x(δ, V)` (`C³`), grid-voltage
modulation, end-to-end, stability. At an operating point whose core `A₀ = jacobian K`
(`K = ∂i_x/∂δ`) has the pair `±jΩ` (eigenvectors `r`, `u`, `u r = 1`) and a real basis `W` of its
stable subspace (`A₀ W = W A_s`, `W' W = I`, `u W = 0`, `W' r = 0`, `‖e^{T A_s}‖ < 1`), with
`V = V₀ + ε V̂ cos 2Ωt` and `ε A₀'`: `Re λ₁ < 0` and `|g_V/2| < |λ₁|`
(`g_V = −(u_v r̄_δ/C) V̂ (K_δV + K_δδ z_δ(2jΩ))`, `mpumpV`) give, for all small `ε > 0`, the forced
periodic orbit with all Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_matching_stable {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 Ω K KV Kδδ KδV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0)
    (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K) (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV)
    (hKδδ : fderiv ℝ (Pd ixV) (δ0, V0) (1, 0) = Kδδ)
    (hKδV : fderiv ℝ (Pd ixV) (δ0, V0) (0, 1) = KδV)
    (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0) {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {W : Matrix (Fin 4) (Fin 2) ℝ} {W' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : d.jacobian K * W = W * As) (hWW : W' * W = 1)
    (huW : u ᵥ* W.map (algebraMap ℝ ℂ) = 0) (hWr : W'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hq : ‖ParametricResonance.BlockAveraging.expS As (2 * Real.pi / (2 * Ω))‖ < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖d.mpumpV u r K Kδδ KδV KV Ω Vh / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (d.mfield ixV (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (d.mfield ixV (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ (d.mfield ixV (d.G + ixV (δ0, V0)))
            (d.meq ixV δ0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨hz, P, Q, hPQ, hQP, hA0, hL, hR⟩ := d.matching_data hP hΩ hωb hωf hC hτ hK hKV hD2
    hr hu hur hW hWW huW hWr Vh
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable
    (d.contDiff_mfield hP _).contDiffAt (d.mfield_eq_zero ixV δ0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0 hq hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, d.pump_mfield hP hKδδ hKδV]; exact hg

/-- Matching control with a voltage-dependent DC current, end-to-end parametric instability:
`|λ₁| < |g_V/2|` makes the forced periodic orbit Floquet unstable for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem orbit_matching_unstable {ixV : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 Ω K KV Kδδ KδV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0)
    (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K) (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV)
    (hKδδ : fderiv ℝ (Pd ixV) (δ0, V0) (1, 0) = Kδδ)
    (hKδV : fderiv ℝ (Pd ixV) (δ0, V0) (0, 1) = KδV)
    (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0) {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {W : Matrix (Fin 4) (Fin 2) ℝ} {W' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : d.jacobian K * W = W * As) (hWW : W' * W = 1)
    (huW : u ᵥ* W.map (algebraMap ℝ ℂ) = 0) (hWr : W'.map (algebraMap ℝ ℂ) *ᵥ r = 0)
    (hq : ‖ParametricResonance.BlockAveraging.expS As (2 * Real.pi / (2 * Ω))‖ < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖d.mpumpV u r K Kδδ KδV KV Ω Vh / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (d.mfield ixV (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (d.mfield ixV (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ (d.mfield ixV (d.G + ixV (δ0, V0)))
          (d.meq ixV δ0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hz, P, Q, hPQ, hQP, hA0, hL, hR⟩ := d.matching_data hP hΩ hωb hωf hC hτ hK hKV hD2
    hr hu hur hW hWW huW hWr Vh
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable
    (d.contDiff_mfield hP _).contDiffAt (d.mfield_eq_zero ixV δ0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0 hq hz A0' ?_
  rw [hL, hR, d.pump_mfield hP hKδδ hKδV]; exact hg

end MatchingCore
end powerlib.GFM.Matching
