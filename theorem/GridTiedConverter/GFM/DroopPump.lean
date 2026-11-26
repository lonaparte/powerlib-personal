import theorem.GridTiedConverter.GFM.DroopTwoFilter
import theorem.ParametricResonance.ElementDecomposition
import theorem.ParametricResonance.ThirdOrderCore
import theorem.ParametricResonance.ForcedResponse
import theorem.Grid.MeasurementPoint

/-! # The 2:1 pump coefficient of the droop core under a grid-angle modulation

From the three-state droop core with a grid-angle input to its first-order Floquet data: the
Jacobian `A₀`, the input vector `B`, the modulation `A₁` (a single modulated element, Lemma 1),
the forced response `z⁽¹⁾`, the eigentriple of a synchronizing mode, and the closed form
`g_m = ρ · w` of the pump coefficient, with its Hopf-point values (Tables 4, 6, 9, droop rows).

Model boundary.
* State `x = (δ, p_m, p_f) : Dynamics.State 3` (converter angle, measured power after the
  measurement low-pass `ω_m`, filtered power after the droop low-pass `ω_1`), grid angle `θ` as
  input, continuous time:
  `δ̇ = m_p (P* − p_f)`, `ṗ_m = ω_m (P(δ − θ) − p_m)`, `ṗ_f = ω_1 (p_m − p_f)` (`field`).
* The measured power is a static map `P(Ψ)` of the relative angle `Ψ = δ − θ` (quasi-static
  network; any network and measurement point: `P = K₀ sin Ψ` on a lossless line,
  `Grid.MeasurementPoint.measuredPower` for a series R–L link). `K = P'(Ψ₀)`, `P₂ = P''(Ψ₀)` at the
  operating angle. Network dynamics, Q–V droop, voltage and inner loops, current limiting, PLL,
  delay and PWM are excluded.
* First-order Floquet data as in `theorem/ParametricResonance/ElementDecomposition.lean`: the
  grid-angle drive `θ = ε Re{e^{jωt}}` enters both through `B = ∂f/∂θ` and through the Jacobian
  (`A₁ = DA[(z⁽¹⁾, 1)]`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (droop core), Table 4 (`w_loop = −d₀/D'(λ_m)`,
`(Ω_m/2)(β + j)/(1 + β²)`), §5.1–§5.3 (Table 5: the single modulable element `(p_m, δ)`;
Table 6: `S_m`; (18)), Table 9 (droop row: `ρ = S_m tan(δ₀ + φ_R)`, `ĝ = |ρ|/√(1 + β²)`).

Results.
* `hasFDerivAt_field`, `hasDerivAt_field_input` — `A₀ = jacobian K`, `B = (0, −ω_m K, 0)`.
* `jacAt_const`, `modulation_eq` — every entry of the Jacobian except `(p_m, δ)` is constant
  (Lemma 1), and `A₁ = ω_m P₂ (z_δ − 1) e_{p_m} e_δᵀ` (`modMatrix`).
* `charPoly` — `det(sI − A₀) = s(s + ω₁)(s + ω_m) + m_p ω₁ ω_m K`.
* `forced_eq`, `forcedAmplitude_eq_forced`, `one_sub_forced_zero` — the forced response
  `z⁽¹⁾(jω)`, with `−z_Ψ = 1 − z_δ = S(jω) = 1/(1 + L(jω))` the loop sensitivity of
  `theorem/ParametricResonance/ThirdOrderCore.lean`.
* `right_eig`, `left_eig`, `left_right` — the eigentriple of a simple root `λ` of the
  characteristic polynomial.
* `weight_eq` — `w_{p_m δ} = −d₀/D'(λ)` (Table 4); `contribution_eq_zero` — every other `Γ_ik`
  vanishes; `pump_eq` — `g = ρ · w` with `ρ = (P₂/K)(z_δ − 1) = −(P₂/K) S(jω)`.
* Hopf point (`λ = jΩ`, `ω₁ω_m = Ω²`, `d₀ = (ω₁ + ω_m)Ω²`, `ω = 2Ω`): `weight_hopf`
  (`w = (Ω/2)(β + j)/(1 + β²)`, `β = Ω/(ω₁ + ω_m)`), `sensitivity_hopf` (`S = (4 + 6jβ)/(3 + 6jβ)`),
  `normalizedPump_hopf` (`ĝ = |P₂/K| |S|/√(1 + β²)`).
* `vsm_jacobian_similar`, `coordMatrix_isUnit` — the VSG (VSM + power filter, `VSMLPF`) Jacobian
  is the droop-core Jacobian in the coordinates `L = coordMatrix` of
  `DroopTwoFilter.field_coord`: `J_VSG L = L J_droop` with `K = K₀ cos δ`, so the VSG pump
  coefficient equals the droop one (`ParametricResonance.Element.pump_similar`).
* `curvature_measuredPower` — at a measurement point of a series R–L link,
  `−P₂/K = tan(Ψ₀ + φ_R)`, `φ_R = arctan((R_u − R_d)/X)`, so `ρ = tan(Ψ₀ + φ_R) S` (18).

Family and connection conclusions.
None: static evidence (Jacobian, forced response, eigenvectors and the pump coefficient) of the
droop core; the stability conclusions of the core are those of `VSMLPF.family` through
`DroopTwoFilter.field_coord`.
-/

noncomputable section
namespace powerlib.GFM
open powerlib.Dynamics (State mk3 state3_ext toEuclideanCLM_apply3)
open Complex ComplexConjugate Matrix

/-- Parameters of the droop core with a grid-angle input and an arbitrary power map. -/
structure DroopCore where
  mp : ℝ
  ω1 : ℝ
  ωm : ℝ
  Pref : ℝ
  P : ℝ → ℝ

namespace DroopCore

variable (d : DroopCore)

/-- The droop core field with grid angle `θ`. -/
def field (θ : ℝ) (x : State 3) : State 3 :=
  mk3 (d.mp * (d.Pref - x 2)) (d.ωm * (d.P (x 0 - θ) - x 1)) (d.ω1 * (x 1 - x 2))

/-- The Jacobian with synchronizing coefficient `K = P'(Ψ)`. -/
def jacobian (K : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, -d.mp; d.ωm * K, -d.ωm, 0; 0, d.ω1, -d.ω1]

/-- The input vector `B = ∂f/∂θ`. -/
def inputVec (K : ℝ) : Fin 3 → ℝ := ![0, -(d.ωm * K), 0]

@[tmio M, powerlib_domain] theorem hasFDerivAt_field {θ K : ℝ} {x : State 3}
    (hP : HasDerivAt d.P K (x 0 - θ)) :
    HasFDerivAt (d.field θ) (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (d.jacobian K)) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  fin_cases i
  · have h := ((hasFDerivAt_const d.Pref x).sub h2).const_mul d.mp
    convert h using 1
    · funext y; simp [field]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3]
  · have hs := hP.comp_hasFDerivAt x (h0.sub_const θ)
    have h := (hs.sub h1).const_mul d.ωm
    convert h using 1
    · funext y; simp [field]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3]
      ring
  · have h := (h1.sub h2).const_mul d.ω1
    convert h using 1
    · funext y; simp [field]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3]
      ring

@[tmio M, powerlib_domain] theorem hasDerivAt_field_input {θ K : ℝ} {x : State 3}
    (hP : HasDerivAt d.P K (x 0 - θ)) (i : Fin 3) :
    HasDerivAt (fun θ => d.field θ x i) (d.inputVec K i) θ := by
  fin_cases i
  · simpa [field, inputVec] using hasDerivAt_const θ (d.mp * (d.Pref - x 2))
  · have h1 : HasDerivAt (fun θ : ℝ => x 0 - θ) (-1) θ := by
      simpa using (hasDerivAt_id θ).const_sub (x 0)
    have h := ((hP.comp θ h1).sub_const (x 1)).const_mul d.ωm
    convert h using 1
    · funext θ; simp [field]
    · simp [inputVec]
  · simpa [field, inputVec] using hasDerivAt_const θ (d.ω1 * (x 1 - x 2))

/-! ## The modulation `A₁` -/

/-- The Jacobian at the point `(x, θ)`: `J(P'(x₀ − θ))`. -/
def jacAt (q : State 3 × ℝ) : Matrix (Fin 3) (Fin 3) ℝ := d.jacobian (deriv d.P (q.1 0 - q.2))

/-- Lemma 1 for the droop core: every entry of the Jacobian except `(p_m, δ)` is constant. -/
@[tmio M, powerlib_domain] theorem jacAt_const {i k : Fin 3} (h : ¬ (i = 1 ∧ k = 0)) :
    ∃ c : ℝ, ∀ q, d.jacAt q i k = c := by
  fin_cases i <;> fin_cases k <;> simp at h ⊢ <;> simp [jacAt, jacobian]

/-- The modulation matrix `A₁ = ω_m P₂ (z_δ − 1) e_{p_m} e_δᵀ`. -/
def modMatrix (P2 : ℝ) (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; (d.ωm * P2 : ℝ) * (z 0 - 1), 0, 0; 0, 0, 0]

/-- `A₁` of the droop core along the forced direction `(z⁽¹⁾, θ̂ = 1)`. -/
@[tmio M, powerlib_domain] theorem modulation_eq {x : State 3} {θ P2 : ℝ}
    (hP2 : HasDerivAt (deriv d.P) P2 (x 0 - θ)) (z : Fin 3 → ℂ) :
    ParametricResonance.Element.modulation d.jacAt (x, θ)
        (WithLp.toLp 2 (fun i => (z i).re), 1) (WithLp.toLp 2 (fun i => (z i).im), 0) =
      d.modMatrix P2 z := by
  have hL := ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).hasFDerivAt.comp (x, θ)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, θ)))).sub (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, θ)))
  have h10 := (hP2.comp_hasFDerivAt (x, θ) hL).const_mul d.ωm
  ext i k
  by_cases hik : i = 1 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := hik
    have h10' : HasFDerivAt (fun q : State 3 × ℝ => d.jacAt q 1 0)
        (d.ωm • (P2 • (((PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).comp
          (ContinuousLinearMap.fst ℝ (State 3) ℝ)) - ContinuousLinearMap.snd ℝ (State 3) ℝ)))
        (x, θ) := by
      convert h10 using 1
      funext q; simp [jacAt, jacobian]
    simp only [ParametricResonance.Element.modulation, h10'.fderiv, modMatrix]
    apply Complex.ext <;> simp <;> ring
  · obtain ⟨c, hc⟩ := d.jacAt_const hik
    rw [ParametricResonance.Element.modulation_eq_zero_of_const hc]
    fin_cases i <;> fin_cases k <;> simp at hik ⊢ <;> simp [modMatrix]

/-! ## Characteristic polynomial and forced response -/

/-- `D(s) = s(s + ω₁)(s + ω_m) + m_p ω₁ ω_m K`. -/
def charPolyEval (K : ℝ) (s : ℂ) : ℂ :=
  s * (s + d.ω1) * (s + d.ωm) + ((d.mp * d.ω1 * d.ωm * K : ℝ) : ℂ)

@[tmio M, powerlib_domain] theorem charPoly (K : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (d.jacobian K) s).det = d.charPolyEval K s := by
  simp [Linear.characteristicMatrix, jacobian, charPolyEval, Matrix.det_fin_three]
  ring

/-- The forced response `z⁽¹⁾(s)` of the core to the grid angle, `s = jω`. -/
def forced (K : ℝ) (s : ℂ) : Fin 3 → ℂ :=
  let zδ := ((d.mp * d.ω1 * d.ωm * K : ℝ) : ℂ) / d.charPolyEval K s
  ![zδ, (d.ωm * K : ℝ) * (zδ - 1) / (s + d.ωm),
    (d.ω1 : ℂ) * ((d.ωm * K : ℝ) * (zδ - 1) / (s + d.ωm)) / (s + d.ω1)]

/-- `(sI − A₀) z⁽¹⁾ = B`. -/
@[tmio M, powerlib_domain] theorem forced_eq (K : ℝ) {s : ℂ} (hD : d.charPolyEval K s ≠ 0)
    (h1 : s + d.ω1 ≠ 0) (hm : s + d.ωm ≠ 0) :
    Linear.characteristicMatrix (d.jacobian K) s *ᵥ d.forced K s =
      (fun i => ((d.inputVec K i : ℝ) : ℂ)) := by
  funext i
  fin_cases i <;>
    simp [Linear.characteristicMatrix, jacobian, forced, inputVec, mulVec, dotProduct,
      Fin.sum_univ_three] <;>
    simp only [charPolyEval] at hD ⊢ <;> field_simp <;> push_cast <;> ring

/-- The forced response is the forced amplitude `(jωI − A₀)⁻¹ B` of the parametric-resonance
notes. -/
@[tmio M, powerlib_domain] theorem forcedAmplitude_eq_forced (K ω : ℝ)
    (hD : d.charPolyEval K ((ω : ℂ) * I) ≠ 0) (h1 : (ω : ℂ) * I + d.ω1 ≠ 0)
    (hm : (ω : ℂ) * I + d.ωm ≠ 0) :
    ParametricResonance.forcedAmplitude (d.jacobian K) ((fun i => ((d.inputVec K i : ℝ) : ℂ))) ω =
      d.forced K ((ω : ℂ) * I) := by
  have hdet : (Linear.characteristicMatrix (d.jacobian K) ((ω : ℂ) * I)).det ≠ 0 := by
    rwa [charPoly]
  have h := d.forced_eq K hD h1 hm
  rw [ParametricResonance.forcedAmplitude]
  have hu : IsUnit (Linear.characteristicMatrix (d.jacobian K) ((ω : ℂ) * I)).det :=
    isUnit_iff_ne_zero.mpr hdet
  rw [show (fun i => ((d.inputVec K i : ℝ) : ℂ)) =
      Linear.characteristicMatrix (d.jacobian K) ((ω : ℂ) * I) *ᵥ d.forced K ((ω : ℂ) * I) by
    rw [h], Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- `−z_Ψ = 1 − z_δ` is the loop sensitivity `S(s) = 1/(1 + L(s))` of the third-order core. -/
@[tmio M, powerlib_domain] theorem one_sub_forced_zero (K : ℝ) {s : ℂ}
    (hD : d.charPolyEval K s ≠ 0) :
    1 - d.forced K s 0 =
      ParametricResonance.ThirdOrder.loopSensitivity (d.ω1 + d.ωm) (d.ω1 * d.ωm)
        (d.mp * d.ω1 * d.ωm * K) s := by
  have hD' : s ^ 3 + ((d.ω1 + d.ωm : ℝ) : ℂ) * s ^ 2 + ((d.ω1 * d.ωm : ℝ) : ℂ) * s +
      ((d.mp * d.ω1 * d.ωm * K : ℝ) : ℂ) = d.charPolyEval K s := by
    simp only [charPolyEval]; push_cast; ring
  simp only [forced, Matrix.cons_val_zero, ParametricResonance.ThirdOrder.loopSensitivity, hD']
  field_simp
  simp only [charPolyEval]
  push_cast
  ring

/-! ## The eigentriple of a synchronizing mode -/

/-- `D'(λ) = 3λ² + 2(ω₁ + ω_m)λ + ω₁ω_m`. -/
def charPolyDeriv (s : ℂ) : ℂ := 3 * s ^ 2 + 2 * ((d.ω1 : ℂ) + d.ωm) * s + (d.ω1 : ℂ) * d.ωm

/-- Right eigenvector `(1, −λ(λ + ω₁)/(m_p ω₁), −λ/m_p)`. -/
def right (lam : ℂ) : Fin 3 → ℂ :=
  ![1, -(lam * (lam + d.ω1)) / ((d.mp : ℂ) * d.ω1), -lam / d.mp]

/-- Left eigenvector `c (ω_m K/λ, 1, (λ + ω_m)/ω₁)`, `c = −m_p ω₁/D'(λ)`. -/
def left (K : ℝ) (lam : ℂ) : Fin 3 → ℂ :=
  let c := -((d.mp : ℂ) * d.ω1) / d.charPolyDeriv lam
  ![c * ((d.ωm * K : ℝ) / lam), c, c * ((lam + d.ωm) / d.ω1)]

@[tmio M, powerlib_domain] theorem right_eig {K : ℝ} {lam : ℂ} (hmp : d.mp ≠ 0)
    (hω1 : d.ω1 ≠ 0) (hroot : d.charPolyEval K lam = 0) :
    Linear.complexify (d.jacobian K) *ᵥ d.right lam = lam • d.right lam := by
  have hmp' : (d.mp : ℂ) ≠ 0 := by exact_mod_cast hmp
  have hω1' : (d.ω1 : ℂ) ≠ 0 := by exact_mod_cast hω1
  simp only [charPolyEval] at hroot
  funext i
  fin_cases i <;>
    simp [Linear.complexify, jacobian, right, mulVec, dotProduct, Fin.sum_univ_three] <;>
    field_simp
  · push_cast at hroot; linear_combination hroot
  · ring

@[tmio M, powerlib_domain] theorem left_eig {K : ℝ} {lam : ℂ} (hω1 : d.ω1 ≠ 0) (hlam : lam ≠ 0)
    (hroot : d.charPolyEval K lam = 0) :
    vecMul (d.left K lam) (Linear.complexify (d.jacobian K)) = lam • d.left K lam := by
  have hω1' : (d.ω1 : ℂ) ≠ 0 := by exact_mod_cast hω1
  simp only [charPolyEval] at hroot
  push_cast at hroot
  simp only [left]
  generalize -((d.mp : ℂ) * d.ω1) / d.charPolyDeriv lam = c
  funext i
  fin_cases i <;>
    simp [Linear.complexify, jacobian, vecMul, dotProduct, Fin.sum_univ_three] <;>
    field_simp
  · ring
  · linear_combination (-c) * hroot

@[tmio M, powerlib_domain] theorem left_right {K : ℝ} {lam : ℂ} (hmp : d.mp ≠ 0)
    (hω1 : d.ω1 ≠ 0) (hlam : lam ≠ 0) (hroot : d.charPolyEval K lam = 0)
    (hD' : d.charPolyDeriv lam ≠ 0) :
    d.left K lam ⬝ᵥ d.right lam = 1 := by
  have hmp' : (d.mp : ℂ) ≠ 0 := by exact_mod_cast hmp
  have hω1' : (d.ω1 : ℂ) ≠ 0 := by exact_mod_cast hω1
  simp only [charPolyEval] at hroot
  push_cast at hroot
  simp only [left, right, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  field_simp
  simp only [charPolyDeriv]
  linear_combination (-1 : ℂ) * hroot

/-! ## The pump coefficient -/

/-- Table 4: the loop weight `w_{p_m δ} = −d₀/D'(λ)`. -/
@[tmio M, powerlib_domain] theorem weight_eq (K : ℝ) (lam : ℂ) :
    ParametricResonance.Element.weight (Linear.complexify (d.jacobian K)) (d.left K lam)
        (d.right lam) 1 0 =
      -((d.mp * d.ω1 * d.ωm * K : ℝ) : ℂ) / d.charPolyDeriv lam := by
  simp [ParametricResonance.Element.weight, Linear.complexify, jacobian, left, right]
  ring

/-- Lemma 1: every contribution except `Γ_{p_m δ}` vanishes. -/
@[tmio M, powerlib_domain] theorem contribution_eq_zero (P2 : ℝ) (z u r : Fin 3 → ℂ) {i k : Fin 3}
    (h : ¬ (i = 1 ∧ k = 0)) :
    ParametricResonance.Element.contribution (d.modMatrix P2 z) u r i k = 0 := by
  fin_cases i <;> fin_cases k <;> simp at h ⊢ <;>
    simp [ParametricResonance.Element.contribution, modMatrix]

/-- `g = ρ · w` with `ρ = (P₂/K)(z_δ − 1)` and `w = −d₀/D'(λ)` (`K ≠ 0`, `ω_m ≠ 0`). -/
@[tmio M, powerlib_domain] theorem pump_eq {K P2 : ℝ} (hK : K ≠ 0) (hωm : d.ωm ≠ 0)
    (z : Fin 3 → ℂ) (lam : ℂ) :
    ParametricResonance.Element.pump (d.modMatrix P2 z) (d.left K lam) (d.right lam) =
      ((P2 / K : ℝ) * (z 0 - 1)) *
        (-((d.mp * d.ω1 * d.ωm * K : ℝ) : ℂ) / d.charPolyDeriv lam) := by
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have hωm' : (d.ωm : ℂ) ≠ 0 := by exact_mod_cast hωm
  simp [ParametricResonance.Element.pump, modMatrix, left, right, mulVec, dotProduct,
    Fin.sum_univ_three]
  field_simp

/-! ## The Hopf point -/

/-- At the Hopf point (`ω₁ ω_m = Ω²`, `d₀ = (ω₁ + ω_m) Ω²`): `w = (Ω/2)(β + j)/(1 + β²)`. -/
@[tmio M, powerlib_domain] theorem weight_hopf {K Ω : ℝ} (hΩ : 0 < Ω) (hsum : 0 < d.ω1 + d.ωm)
    (h1 : d.ω1 * d.ωm = Ω ^ 2) (h0 : d.mp * d.ω1 * d.ωm * K = (d.ω1 + d.ωm) * Ω ^ 2) :
    ParametricResonance.Element.weight (Linear.complexify (d.jacobian K)) (d.left K (Ω * I))
        (d.right (Ω * I)) 1 0 =
      (Ω / 2 : ℝ) * (((Ω / (d.ω1 + d.ωm) : ℝ) : ℂ) + I) /
        (1 + ((Ω / (d.ω1 + d.ωm) : ℝ) : ℂ) ^ 2) := by
  rw [weight_eq, h0]
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hsc : ((d.ω1 + d.ωm : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsum.ne'
  have h1c : (d.ω1 : ℂ) * d.ωm = (Ω : ℂ) ^ 2 := by exact_mod_cast h1
  have hden : d.charPolyDeriv ((Ω : ℂ) * I) =
      2 * (Ω : ℂ) * I * (((d.ω1 + d.ωm : ℝ) : ℂ) + Ω * I) := by
    simp only [charPolyDeriv]
    push_cast
    linear_combination (3 * (Ω : ℂ) ^ 2 - 2 * Ω ^ 2) * I_sq + h1c
  have hne : ((d.ω1 + d.ωm : ℝ) : ℂ) + Ω * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne2 : (1 : ℂ) + ((Ω / (d.ω1 + d.ωm) : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < 1 + (Ω / (d.ω1 + d.ωm)) ^ 2 := by positivity
    exact_mod_cast this.ne'
  rw [hden]
  have hs : 0 < d.ω1 + d.ωm := hsum
  generalize d.ω1 + d.ωm = D2 at hs hsc hne hne2 ⊢
  apply Complex.ext <;>
    simp [pow_two, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im] <;>
    field_simp <;> ring

/-- At the Hopf point the 2:1 kinematic factor is `S(2jΩ) = (4 + 6jβ)/(3 + 6jβ)`. -/
@[tmio M, powerlib_domain] theorem sensitivity_hopf {K Ω : ℝ} (hΩ : 0 < Ω)
    (hsum : 0 < d.ω1 + d.ωm) (h1 : d.ω1 * d.ωm = Ω ^ 2)
    (h0 : d.mp * d.ω1 * d.ωm * K = (d.ω1 + d.ωm) * Ω ^ 2)
    (hD : d.charPolyEval K (2 * (Ω : ℂ) * I) ≠ 0) :
    1 - d.forced K (2 * (Ω : ℂ) * I) 0 =
      ParametricResonance.ThirdOrder.hopfFactor (Ω / (d.ω1 + d.ωm)) := by
  rw [d.one_sub_forced_zero K hD, h1, h0]
  exact ParametricResonance.ThirdOrder.loopSensitivity_hopf hsum hΩ

/-- Table 9 (droop row) at the Hopf point: `ĝ = 2|g|/Ω = |P₂/K| |S| /√(1 + β²)`. -/
@[tmio M, powerlib_domain] theorem normalizedPump_hopf {K P2 Ω : ℝ} (hK : K ≠ 0)
    (hωm : d.ωm ≠ 0) (hΩ : 0 < Ω) (hsum : 0 < d.ω1 + d.ωm) (h1 : d.ω1 * d.ωm = Ω ^ 2)
    (h0 : d.mp * d.ω1 * d.ωm * K = (d.ω1 + d.ωm) * Ω ^ 2)
    (hD : d.charPolyEval K (2 * (Ω : ℂ) * I) ≠ 0) :
    ParametricResonance.Element.normalizedPump
        (ParametricResonance.Element.pump (d.modMatrix P2 (d.forced K (2 * (Ω : ℂ) * I)))
          (d.left K (Ω * I)) (d.right (Ω * I))) Ω =
      |P2 / K| * ‖ParametricResonance.ThirdOrder.hopfFactor (Ω / (d.ω1 + d.ωm))‖ /
        √(1 + (Ω / (d.ω1 + d.ωm)) ^ 2) := by
  set β := Ω / (d.ω1 + d.ωm) with hβ
  rw [d.pump_eq hK hωm, ← weight_eq, d.weight_hopf hΩ hsum h1 h0]
  have hS := d.sensitivity_hopf hΩ hsum h1 h0 hD
  have hz : d.forced K (2 * (Ω : ℂ) * I) 0 - 1 =
      -ParametricResonance.ThirdOrder.hopfFactor β := by rw [← hS]; ring
  rw [hz]
  have hb : 0 < 1 + β ^ 2 := by positivity
  have hnw : ‖(Ω / 2 : ℝ) * ((β : ℂ) + I) / (1 + (β : ℂ) ^ 2)‖ = Ω / 2 / √(1 + β ^ 2) := by
    have e1 : ‖(β : ℂ) + I‖ = √(1 + β ^ 2) := by
      rw [show (β : ℂ) + I = (β : ℂ) + ((1 : ℝ) : ℂ) * I by simp, Complex.norm_add_mul_I]
      ring_nf
    have e2 : ‖(1 : ℂ) + (β : ℂ) ^ 2‖ = 1 + β ^ 2 := by
      rw [show (1 : ℂ) + (β : ℂ) ^ 2 = ((1 + β ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg hb.le]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), e1, e2]
    have hs : √(1 + β ^ 2) ^ 2 = 1 + β ^ 2 := Real.sq_sqrt hb.le
    have hs0 : 0 < √(1 + β ^ 2) := Real.sqrt_pos.mpr hb
    field_simp
    rw [hs]
  rw [ParametricResonance.Element.normalizedPump, norm_mul, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, hnw]
  field_simp

/-! ## The VSG reading -/

/-- The linear part of the droop–VSG coordinates `(δ, p_m, p_f) ↦ (δ, −m_p p_f, p_m)`. -/
def coordMatrix (mp : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, -mp; 0, 1, 0]

@[tmio M, powerlib_domain] theorem coordMatrix_isUnit {mp : ℝ} (hmp : mp ≠ 0) :
    IsUnit (coordMatrix mp) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [coordMatrix, Matrix.det_fin_three, hmp]

/-- The VSG Jacobian is the droop-core Jacobian in the droop–VSG coordinates. -/
@[tmio M, powerlib_domain] theorem vsm_jacobian_similar {mp ω1 ωm Pref K0 : ℝ} (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) (δ : ℝ) :
    (DroopTwoFilter.mk mp ω1 ωm Pref K0).toVSM.jacobian δ * coordMatrix mp =
      coordMatrix mp * (DroopCore.mk mp ω1 ωm Pref (fun Ψ => K0 * Real.sin Ψ)).jacobian
        (K0 * Real.cos δ) := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [VSMLPF.jacobian, DroopTwoFilter.toVSM, coordMatrix, jacobian, Matrix.mul_apply,
      Fin.sum_univ_three] <;> field_simp

/-! ## The curvature ratio at a measurement point -/

/-- With the measured power of a series R–L link as the power map, `−P''/P' = tan(Ψ + φ_R)`:
the droop core's relative modulation is `ρ = tan(Ψ₀ + φ_R) S(jω)` (18). -/
@[tmio M, powerlib_domain] theorem curvature_measuredPower (E V ω : ℝ)
    (Zu Zd : Passive.SeriesRLC) (hX : 0 < Zu.reactance ω + Zd.reactance ω) (Ψ : ℝ)
    (hcos : Real.cos (Ψ + Real.arctan ((Zu.R - Zd.R) / (Zu.reactance ω + Zd.reactance ω))) ≠ 0)
    (hK : deriv (fun Ψ => Grid.MeasurementPoint.measuredPower E V Ψ ω Zu Zd) Ψ ≠ 0) :
    -(deriv (deriv (fun Ψ => Grid.MeasurementPoint.measuredPower E V Ψ ω Zu Zd)) Ψ /
        deriv (fun Ψ => Grid.MeasurementPoint.measuredPower E V Ψ ω Zu Zd) Ψ) =
      Real.tan (Ψ + Real.arctan ((Zu.R - Zd.R) / (Zu.reactance ω + Zd.reactance ω))) := by
  rw [Grid.MeasurementPoint.measuredPower_curvature E V ω Zu Zd hX Ψ hcos]
  field_simp

end DroopCore

end powerlib.GFM
