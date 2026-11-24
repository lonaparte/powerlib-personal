import theorem.Criteria.Routh4
import theorem.Modal.Sensitivity
import theorem.Dynamics.Coordinates
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Matching control with a DC source: characteristic equation and the 2:1 kinematic factor

The four-state synchronization core of matching control with a controlled DC source, written in
the grid-voltage frame: its Jacobian, the exact characteristic equation of the source, the limits
in which the DC source acts as a spring on the absolute angle, and the 2:1 kinematic factor
`c_κ = (4 + 3κ)/(3(1 + κ))` of that spring-swing reading.

Model boundary.
* State `x = (δ, v_f, v, i_s) : Dynamics.State 4` (converter angle relative to the grid voltage,
  filtered DC voltage, DC-link voltage, DC-source current, all pu), the grid frequency deviation
  `θ̇_g` as input, continuous time:
  `δ̇ = ω_b (v_f − 1) − θ̇_g`, `v̇_f = ω_f (v − v_f)`, `C v̇ = i_s − G v − i_x(δ)`,
  `τ i̇_s = I* − k_dc (v − 1) − i_s` (`field`), with the DC current `i_x(δ)` drawn by the converter a
  static map of the angle (quasi-static network; the `E = m_a v` and network-frequency effects of
  the source, of relative order `μ_p`, are excluded), `K = i_x'(δ₀)`.
* Spring-swing reading: the absolute angle `θ_c` with `M θ̈_c + (k_s + K) θ_c = K θ_g`
  (`M = C/ω_b`, `k_s = k_dc/(τ ω_b)`), the limit of the core for a fast measurement filter and a
  DC source slow against the mode (`springSensitivity` and the limits below).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (matching core: `C λ² + k_dc λ/(1 + τλ) + ω_b K ω_f/(λ + ω_f) = 0`,
`Ω_m² ≈ ω_b K (1 + κ_dc)/C`, `κ_dc = k_dc/(τ ω_b K)`), Table 6 (matching row:
`c_κ = (4 + 3κ_dc)/(3(1 + κ_dc))`, `z⁽¹⁾_{θ_c} = −1/(3(1 + κ_dc))`, `|S_m| ∈ [1, 4/3]`).

Results.
* `hasFDerivAt_field`, `hasDerivAt_field_input` — the Jacobian (`jacobian K`) and the input
  vector `(−1, 0, 0, 0)` of the grid frequency.
* `charPoly` — `C τ det(sI − A₀) = (1 + τs)(s + ω_f)(C s² + G s) + k_dc s (s + ω_f) +
  ω_b K ω_f (1 + τ s)`; `charEq_iff` — for `(1 + τs)(s + ω_f) ≠ 0`, `s` is a root iff
  `C s² + G s + k_dc s/(1 + τs) + ω_b K ω_f/(s + ω_f) = 0` (the source's equation, with `G`).
* `tendsto_dcSource`, `tendsto_filter` — `k_s τ s/(1 + τ s) → k_s` as `τ → ∞` (`k_dc = k_s τ`,
  `s ≠ 0`) and `ω_f/(s + ω_f) → 1` as `ω_f → ∞`: in these limits the equation becomes
  `C s² + G s + k_s + ω_b K = 0`, the spring swing.
* `spring_frequency` — `(k_s/ω_b + K)/(C/ω_b) = ω_b K (1 + κ)/C` with `κ = k_s/(ω_b K)`.
* `springForced_eq`, `springForced_mode` — the spring swing's forced response
  `z_{θ_c}(s) = K/(M s² + k_s + K)`, equal to `−1/(3(1 + κ))` at `s = 2jΩ`, `Ω² = (k_s + K)/M`,
  `κ = k_s/K`; `springSensitivity_mode` — `S = 1 − z_{θ_c} = (4 + 3κ)/(3(1 + κ))`.
* `springSensitivity_bounds` — `1 < c_κ ≤ 4/3` for `κ ≥ 0`, and `c_κ` is strictly decreasing
  (`springSensitivity_strictAntiOn`).
* The damping budget (14) as first-order derivatives at the spring-swing point (`C s² + k_s + W`,
  `W = ω_b K`, roots `±jΩ`, `Ω² = (k_s + W)/C`, `κ = k_s/W`), from a differentiable root branch of
  `P + p Q` (`exists_root_branch_affine`): `damping_dcSource` — along `ε₁ = 1/τ` (with
  `k_dc = k_s τ`) the root branch has `dλ/dε₁ = −k_s/(2CΩ²)`, so `dσ/dε₁ = κ/(2(1 + κ))`;
  `damping_filter` — along `ε₂ = 1/ω_f`, `dλ/dε₂ = W/(2C)`, so `dσ/dε₂ = −Ω²/(2(1 + κ))`;
  `damping_conductance` — along `G`, `dλ/dG = −1/(2C)`, so `dσ/dG = 1/(2C)`. All three
  derivatives are real: the mode frequency `Ω_m² = ω_b K (1 + κ)/C` holds to first order. These are
  the first three terms of (14), `(1 + κ)σ/Ω ≈ κ/(2Ωτ) − Ω/(2ω_f) + (1 + κ)G/(2CΩ)`; the network
  resistance term is outside this model.

Family and connection conclusions.
None: static evidence on the matching core (Jacobian, characteristic equation, limits, kinematic
factor of the spring-swing reading).
-/

noncomputable section
namespace powerlib.GFM.Matching
open powerlib.Dynamics (State)
open Complex Matrix Filter Topology

/-- Parameters of the matching core with a controlled DC source. -/
structure MatchingCore where
  ωb : ℝ
  ωf : ℝ
  C : ℝ
  G : ℝ
  kdc : ℝ
  τ : ℝ
  Istar : ℝ
  ix : ℝ → ℝ

namespace MatchingCore

variable (d : MatchingCore)

/-- The matching core field with grid frequency deviation `θ̇_g`. -/
def field (θdot : ℝ) (x : State 4) : State 4 :=
  WithLp.toLp 2 ![d.ωb * (x 1 - 1) - θdot, d.ωf * (x 2 - x 1),
    (x 3 - d.G * x 2 - d.ix (x 0)) / d.C, (d.Istar - d.kdc * (x 2 - 1) - x 3) / d.τ]

/-- The Jacobian with synchronizing coefficient `K = i_x'(δ)`. -/
def jacobian (K : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, d.ωb, 0, 0; 0, -d.ωf, d.ωf, 0; -(K / d.C), 0, -(d.G / d.C), 1 / d.C;
    0, 0, -(d.kdc / d.τ), -(1 / d.τ)]

@[tmio M, powerlib_domain] theorem hasFDerivAt_field {θdot K : ℝ} {x : State 4}
    (hK : HasDerivAt d.ix K (x 0)) :
    HasFDerivAt (d.field θdot) (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (d.jacobian K)) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4) : State 4 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (1 : Fin 4) : State 4 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h2 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4) : State 4 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h3 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (3 : Fin 4) : State 4 →L[ℝ] ℝ).hasFDerivAt (x := x)
  fin_cases i
  · have h := ((h1.sub_const 1).const_mul d.ωb).sub_const θdot
    convert h using 1
    · funext y; simp [field]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
  · have h := (h2.sub h1).const_mul d.ωf
    convert h using 1
    · funext y; simp [field]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
      ring
  · have hs := hK.comp_hasFDerivAt x h0
    have h := HasFDerivAt.const_mul ((h3.sub (h2.const_mul d.G)).sub hs) d.C⁻¹
    convert h using 1
    · funext y; simp [field, div_eq_inv_mul]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
      ring
  · have h := HasFDerivAt.const_mul (((hasFDerivAt_const d.Istar x).sub
      ((h2.sub_const 1).const_mul d.kdc)).sub h3) d.τ⁻¹
    convert h using 1
    · funext y; simp [field, div_eq_inv_mul]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
      ring

/-- The grid frequency enters only the angle equation: `∂f/∂θ̇_g = (−1, 0, 0, 0)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_field_input (θdot : ℝ) (x : State 4) (i : Fin 4) :
    HasDerivAt (fun θdot => d.field θdot x i) (![-1, 0, 0, 0] i) θdot := by
  fin_cases i
  · simpa [field] using (hasDerivAt_id θdot).const_sub (d.ωb * (x 1 - 1))
  · simpa [field] using hasDerivAt_const θdot (d.ωf * (x 2 - x 1))
  · simpa [field] using hasDerivAt_const θdot ((x 3 - d.G * x 2 - d.ix (x 0)) / d.C)
  · simpa [field] using hasDerivAt_const θdot ((d.Istar - d.kdc * (x 2 - 1) - x 3) / d.τ)

/-- `C τ det(sI − A₀) = (1 + τs)(s + ω_f)(Cs² + Gs) + k_dc s(s + ω_f) + ω_b K ω_f (1 + τs)`. -/
@[tmio M, powerlib_domain] theorem charPoly (K : ℝ) (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) (s : ℂ) :
    (d.C : ℂ) * d.τ * (Linear.characteristicMatrix (d.jacobian K) s).det =
      (1 + d.τ * s) * (s + d.ωf) * (d.C * s ^ 2 + d.G * s) + d.kdc * s * (s + d.ωf) +
        d.ωb * K * d.ωf * (1 + d.τ * s) := by
  have hC' : (d.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hτ' : (d.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  rw [Criteria.det_fin_four]
  simp [Linear.characteristicMatrix, jacobian]
  field_simp
  ring

/-- The source's characteristic equation, with the DC conductance `G`. -/
@[tmio M, powerlib_domain] theorem charEq_iff (K : ℝ) (hC : d.C ≠ 0) (hτ : d.τ ≠ 0) {s : ℂ}
    (h1 : 1 + (d.τ : ℂ) * s ≠ 0) (h2 : s + d.ωf ≠ 0) :
    (Linear.characteristicMatrix (d.jacobian K) s).det = 0 ↔
      (d.C : ℂ) * s ^ 2 + d.G * s + d.kdc * s / (1 + d.τ * s) + d.ωb * K * d.ωf / (s + d.ωf) =
        0 := by
  have hC' : (d.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hτ' : (d.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have hp := d.charPoly K hC hτ s
  have key : (d.C : ℂ) * s ^ 2 + d.G * s + d.kdc * s / (1 + d.τ * s) + d.ωb * K * d.ωf / (s + d.ωf) =
      (d.C : ℂ) * d.τ * (Linear.characteristicMatrix (d.jacobian K) s).det /
        ((1 + d.τ * s) * (s + d.ωf)) := by
    have h1' : (1 : ℂ) + s * d.τ ≠ 0 := by rwa [mul_comm]
    have h2' : (d.ωf : ℂ) + s ≠ 0 := by rwa [add_comm]
    rw [eq_div_iff (mul_ne_zero h1 h2), hp]
    field_simp
  constructor
  · intro hD; rw [key, hD]; simp
  · intro h
    rw [key] at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hC' hτ')
    · exact absurd h (mul_ne_zero h1 h2)

end MatchingCore

/-! ## The DC source as a spring -/

/-- A DC source slow against the mode acts as a spring: `k_s τ s/(1 + τ s) → k_s` as `τ → ∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_dcSource (ks : ℝ) {s : ℂ} (hs : s ≠ 0) :
    Tendsto (fun τ : ℝ => (ks : ℂ) * τ * s / (1 + τ * s)) atTop (𝓝 (ks : ℂ)) := by
  have h1 : Tendsto (fun τ : ℝ => (τ : ℂ)⁻¹) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp (tendsto_id (α := ℝ))
    exact (Complex.continuous_ofReal.tendsto 0).comp this |>.congr (fun τ => by simp)
      |>.trans (by simp)
  have h2 : Tendsto (fun τ : ℝ => (ks : ℂ) * s / ((τ : ℂ)⁻¹ + s)) atTop
      (𝓝 ((ks : ℂ) * s / (0 + s))) :=
    tendsto_const_nhds.div (h1.add tendsto_const_nhds) (by simpa using hs)
  rw [zero_add, mul_div_assoc, div_self hs, mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hden : (τ : ℂ)⁻¹ + s ≠ 0 ∨ True := Or.inr trivial
  by_cases h : (1 : ℂ) + τ * s = 0
  · have h' : (τ : ℂ)⁻¹ + s = 0 := by
      rw [← mul_right_inj' hτ', mul_add, mul_inv_cancel₀ hτ', mul_zero]; exact h
    rw [h, h', div_zero, div_zero]
  · have h' : (τ : ℂ)⁻¹ + s ≠ 0 := by
      intro h0; apply h
      rw [← mul_right_inj' hτ', mul_add, mul_inv_cancel₀ hτ', mul_zero] at h0; exact h0
    field_simp

/-- A fast measurement filter: `ω_f/(s + ω_f) → 1` as `ω_f → ∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_filter (s : ℂ) :
    Tendsto (fun ωf : ℝ => (ωf : ℂ) / (s + ωf)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun ωf : ℝ => s * (ωf : ℂ)⁻¹) atTop (𝓝 (s * 0)) :=
    tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_inv_atTop_zero.comp (tendsto_id (α := ℝ))) |>.congr (fun ωf => by simp)
        |>.trans (by simp))
  rw [mul_zero] at h1
  have h2 : Tendsto (fun ωf : ℝ => 1 / (s * (ωf : ℂ)⁻¹ + 1)) atTop (𝓝 (1 / (0 + 1))) :=
    tendsto_const_nhds.div (h1.add tendsto_const_nhds) (by norm_num)
  rw [zero_add, div_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ωf hωf
  have hω : (ωf : ℂ) ≠ 0 := by exact_mod_cast hωf.ne'
  by_cases h : s + (ωf : ℂ) = 0
  · have h' : s * (ωf : ℂ)⁻¹ + 1 = 0 := by
      rw [← mul_right_inj' hω, mul_add, mul_comm (ωf : ℂ) (s * _), mul_assoc,
        inv_mul_cancel₀ hω, mul_one, mul_one, mul_zero]; exact h
    rw [h, h', div_zero, div_zero]
  · have h' : s * (ωf : ℂ)⁻¹ + 1 ≠ 0 := by
      intro h0; apply h
      rw [← mul_right_inj' hω, mul_add, mul_comm (ωf : ℂ) (s * _), mul_assoc,
        inv_mul_cancel₀ hω, mul_one, mul_one, mul_zero] at h0; exact h0
    field_simp

/-- The spring-swing frequency: `(k_s/ω_b + K)/(C/ω_b) = ω_b K (1 + κ)/C`, `κ = k_s/(ω_b K)`. -/
@[tmio T, powerlib_foundation] theorem spring_frequency {ωb C K ks : ℝ} (hωb : ωb ≠ 0)
    (hC : C ≠ 0) (hK : K ≠ 0) :
    (ks / ωb + K) / (C / ωb) = ωb * K * (1 + ks / (ωb * K)) / C := by
  field_simp
  ring

/-- Forced response of the spring swing `M θ̈ + (k_s + K) θ = K θ_g`. -/
def springForced (M ks K : ℝ) (s : ℂ) : ℂ := (K : ℂ) / (M * s ^ 2 + ks + K)

/-- The forced response solves `(M s² + k_s + K) z = K`. -/
@[tmio T, powerlib_foundation] theorem springForced_eq {M ks K : ℝ} {s : ℂ}
    (h : (M : ℂ) * s ^ 2 + ks + K ≠ 0) :
    ((M : ℂ) * s ^ 2 + ks + K) * springForced M ks K s = K := by
  rw [springForced]; field_simp

/-- At `s = 2jΩ`, `Ω² = (k_s + K)/M`: `z_{θ_c} = −1/(3(1 + κ))`, `κ = k_s/K`. -/
@[tmio T, powerlib_foundation] theorem springForced_mode {M ks K Ω : ℝ} (hM : M ≠ 0) (hK : K ≠ 0)
    (hpos : ks + K ≠ 0) (hΩ : Ω ^ 2 = (ks + K) / M) :
    springForced M ks K (2 * Ω * I) = -1 / (3 * (1 + ((ks / K : ℝ) : ℂ))) := by
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have hΩ' : (M : ℂ) * (Ω : ℂ) ^ 2 = ks + K := by
    have : M * Ω ^ 2 = ks + K := by rw [hΩ]; field_simp
    exact_mod_cast this
  have hd : (M : ℂ) * (2 * Ω * I) ^ 2 + ks + K = -3 * ((ks : ℂ) + K) := by
    linear_combination (4 * (M : ℂ) * Ω ^ 2) * I_sq - 4 * hΩ'
  have hpos' : (ks : ℂ) + K ≠ 0 := by exact_mod_cast hpos
  have h3 : (3 : ℂ) * (1 + ((ks / K : ℝ) : ℂ)) ≠ 0 := by
    have : (3 : ℝ) * (1 + ks / K) ≠ 0 := by
      rw [show (3 : ℝ) * (1 + ks / K) = 3 * (ks + K) / K by field_simp; ring]
      exact div_ne_zero (mul_ne_zero three_ne_zero hpos) hK
    exact_mod_cast this
  rw [springForced, hd, div_eq_div_iff (mul_ne_zero (by norm_num) hpos') h3]
  push_cast
  field_simp
  ring

/-- The spring-swing kinematic factor `c_κ = S = 1 − z_{θ_c} = (4 + 3κ)/(3(1 + κ))`. -/
@[tmio T, powerlib_foundation] theorem springSensitivity_mode {M ks K Ω : ℝ} (hM : M ≠ 0)
    (hK : K ≠ 0) (hpos : ks + K ≠ 0) (hΩ : Ω ^ 2 = (ks + K) / M) :
    1 - springForced M ks K (2 * Ω * I) =
      ((4 + 3 * (ks / K) : ℝ) : ℂ) / (3 * (1 + ((ks / K : ℝ) : ℂ))) := by
  rw [springForced_mode hM hK hpos hΩ]
  have h1 : (1 : ℂ) + ((ks / K : ℝ) : ℂ) ≠ 0 := by
    have : 1 + ks / K ≠ 0 := by
      rw [show 1 + ks / K = (ks + K) / K by field_simp; ring]
      exact div_ne_zero hpos hK
    exact_mod_cast this
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  field_simp
  push_cast
  field_simp
  ring

/-- `c_κ = (4 + 3κ)/(3(1 + κ))` lies in `(1, 4/3]` for `κ ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem springSensitivity_bounds {κ : ℝ} (hκ : 0 ≤ κ) :
    1 < (4 + 3 * κ) / (3 * (1 + κ)) ∧ (4 + 3 * κ) / (3 * (1 + κ)) ≤ 4 / 3 := by
  have h : 0 < 3 * (1 + κ) := by positivity
  constructor
  · rw [lt_div_iff₀ h]; linarith
  · rw [div_le_iff₀ h]; linarith

@[tmio T, powerlib_foundation] theorem springSensitivity_strictAntiOn :
    StrictAntiOn (fun κ : ℝ => (4 + 3 * κ) / (3 * (1 + κ))) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  simp only
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ## The damping budget (14) as first-order derivatives -/

/-- A simple root `λ₀` of `P` with `Q(λ₀) ≠ 0` continues to a differentiable root branch of
`P + p Q`, with `dλ/dp = −Q(λ₀)/P'(λ₀)`. -/
@[tmio T, powerlib_foundation] theorem exists_root_branch_affine {P Q : ℂ → ℂ} {P' Q' lam0 : ℂ}
    (hP : HasStrictDerivAt P P' lam0) (hQ : HasStrictDerivAt Q Q' lam0) (hP0 : P lam0 = 0)
    (hQ0 : Q lam0 ≠ 0) (hP' : P' ≠ 0) :
    ∃ lam : ℝ → ℂ, lam 0 = lam0 ∧ (∀ᶠ p in 𝓝 (0 : ℝ), P (lam p) + p * Q (lam p) = 0) ∧
      HasDerivAt lam (-Q lam0 / P') 0 := by
  have hf : HasStrictDerivAt (fun z => P z / Q z) (P' / Q lam0) lam0 := by
    have := hP.div hQ hQ0
    convert this using 1
    rw [hP0]; field_simp; ring
  have hf' : P' / Q lam0 ≠ 0 := div_ne_zero hP' hQ0
  obtain ⟨lam, h0, hev, hd⟩ := Modal.exists_root_branch (c := 1) (K0 := 0) hf hf'
    (by simp [hP0])
  refine ⟨lam, h0, ?_, ?_⟩
  · have hc : ContinuousAt (fun p => Q (lam p)) 0 := by
      have := hQ.hasDerivAt.continuousAt
      rw [← h0] at this
      exact this.comp hd.continuousAt
    have hne : ∀ᶠ p in 𝓝 (0 : ℝ), Q (lam p) ≠ 0 :=
      hc.eventually_ne (by rw [h0]; exact hQ0)
    filter_upwards [hev, hne] with p hp hq
    have : P (lam p) / Q (lam p) + (p : ℂ) = 0 := by simpa using hp
    field_simp at this
    linear_combination this
  · convert hd using 1
    field_simp

/-- (14), the DC-source term: along `ε₁ = 1/τ` the root branch of
`s(Cs² + W + k_s) + ε₁(Cs² + W)` through `jΩ` has `dλ/dε₁ = −k_s/(2CΩ²)`, real, so
`dσ/dε₁ = κ/(2(1 + κ))`. -/
@[tmio T, powerlib_foundation] theorem damping_dcSource {C W ks Ω : ℝ} (hC : 0 < C) (hks : 0 < ks)
    (hW : 0 < W) (hΩ : 0 < Ω) (hΩ2 : C * Ω ^ 2 = ks + W) :
    ∃ lam : ℝ → ℂ, lam 0 = Ω * I ∧
      (∀ᶠ ε₁ in 𝓝 (0 : ℝ), lam ε₁ * (C * lam ε₁ ^ 2 + W + ks) + ε₁ * (C * lam ε₁ ^ 2 + W) = 0) ∧
      HasDerivAt lam ((-(ks / (2 * C * Ω ^ 2)) : ℝ) : ℂ) 0 ∧
      -(-(ks / (2 * C * Ω ^ 2))) = (ks / W) / (2 * (1 + ks / W)) := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hΩ2c : (C : ℂ) * Ω ^ 2 = ks + W := by exact_mod_cast hΩ2
  have hP : HasStrictDerivAt (fun z : ℂ => z * (C * z ^ 2 + W + ks))
      (3 * C * (Ω * I) ^ 2 + W + ks) (Ω * I) := by
    have := ((hasStrictDerivAt_id (Ω * I : ℂ)).mul
      (((hasStrictDerivAt_pow 2 (Ω * I : ℂ)).const_mul (C : ℂ)).add_const ((W : ℂ) + ks)))
    convert this using 1
    · funext z; simp only [Pi.mul_apply, id]; ring
    · simp; ring
  have hQ : HasStrictDerivAt (fun z : ℂ => C * z ^ 2 + W) (C * (2 * (Ω * I))) (Ω * I) := by
    have := ((hasStrictDerivAt_pow 2 (Ω * I : ℂ)).const_mul (C : ℂ)).add_const (W : ℂ)
    convert this using 1; simp
  have hP0 : (Ω * I : ℂ) * (C * (Ω * I) ^ 2 + W + ks) = 0 := by
    linear_combination (Ω * I : ℂ) * (C * Ω ^ 2 * I_sq) - (Ω * I : ℂ) * hΩ2c
  have hQ0 : (C : ℂ) * (Ω * I) ^ 2 + W = -ks := by
    linear_combination (C * Ω ^ 2 : ℂ) * I_sq - hΩ2c
  have hP'v : 3 * (C : ℂ) * (Ω * I) ^ 2 + W + ks = -2 * C * Ω ^ 2 := by
    linear_combination (3 * C * Ω ^ 2 : ℂ) * I_sq - hΩ2c
  have hks' : (ks : ℂ) ≠ 0 := by exact_mod_cast hks.ne'
  obtain ⟨lam, h0, hev, hd⟩ := exists_root_branch_affine hP hQ hP0
    (by rw [hQ0]; exact neg_ne_zero.mpr hks')
    (by rw [hP'v]; exact mul_ne_zero (mul_ne_zero (by norm_num) hC') (pow_ne_zero 2 hΩc))
  refine ⟨lam, h0, hev, ?_, ?_⟩
  · convert hd using 1
    rw [hQ0, hP'v]; push_cast; ring
  · have hsum : 0 < W + ks := by linarith
    rw [neg_neg, show 2 * C * Ω ^ 2 = 2 * (ks + W) by linarith]
    field_simp
    ring

/-- (14), the measurement-filter term: along `ε₂ = 1/ω_f` the root branch of
`(Cs² + k_s + W) + ε₂ s(Cs² + k_s)` through `jΩ` has `dλ/dε₂ = W/(2C)`, real, so
`dσ/dε₂ = −Ω²/(2(1 + κ))`. -/
@[tmio T, powerlib_foundation] theorem damping_filter {C W ks Ω : ℝ} (hC : 0 < C) (hW : 0 < W)
    (hΩ : 0 < Ω) (hΩ2 : C * Ω ^ 2 = ks + W) :
    ∃ lam : ℝ → ℂ, lam 0 = Ω * I ∧
      (∀ᶠ ε₂ in 𝓝 (0 : ℝ), (C * lam ε₂ ^ 2 + ks + W) + ε₂ * (lam ε₂ * (C * lam ε₂ ^ 2 + ks)) = 0) ∧
      HasDerivAt lam (((W / (2 * C)) : ℝ) : ℂ) 0 ∧
      -(W / (2 * C)) = -(Ω ^ 2 / (2 * (1 + ks / W))) := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hΩ2c : (C : ℂ) * Ω ^ 2 = ks + W := by exact_mod_cast hΩ2
  have hP : HasStrictDerivAt (fun z : ℂ => C * z ^ 2 + ks + W) (C * (2 * (Ω * I))) (Ω * I) := by
    have := ((hasStrictDerivAt_pow 2 (Ω * I : ℂ)).const_mul (C : ℂ)).add_const ((ks : ℂ) + W)
    convert this using 1
    · funext z; ring
    · simp
  have hQ : HasStrictDerivAt (fun z : ℂ => z * (C * z ^ 2 + ks))
      (3 * C * (Ω * I) ^ 2 + ks) (Ω * I) := by
    have := ((hasStrictDerivAt_id (Ω * I : ℂ)).mul
      (((hasStrictDerivAt_pow 2 (Ω * I : ℂ)).const_mul (C : ℂ)).add_const (ks : ℂ)))
    convert this using 1
    · funext z; simp
    · simp; ring
  have hP0 : (C : ℂ) * (Ω * I) ^ 2 + ks + W = 0 := by
    linear_combination (C * Ω ^ 2 : ℂ) * I_sq - hΩ2c
  have hQ0 : (Ω * I : ℂ) * (C * (Ω * I) ^ 2 + ks) = -(W : ℂ) * (Ω * I) := by
    linear_combination (Ω * I : ℂ) * (C * Ω ^ 2 * I_sq) - (Ω * I : ℂ) * hΩ2c
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  obtain ⟨lam, h0, hev, hd⟩ := exists_root_branch_affine hP hQ hP0
    (by rw [hQ0]; exact mul_ne_zero (neg_ne_zero.mpr hW') (mul_ne_zero hΩc I_ne_zero))
    (mul_ne_zero hC' (mul_ne_zero two_ne_zero (mul_ne_zero hΩc I_ne_zero)))
  refine ⟨lam, h0, hev, ?_, ?_⟩
  · convert hd using 1
    rw [hQ0]; push_cast; field_simp
  · have hΩ2' : Ω ^ 2 = (ks + W) / C := by field_simp; linarith
    have hsum : 0 < W + ks := by nlinarith [mul_pos hC (sq_pos_of_pos hΩ)]
    rw [hΩ2']
    field_simp
    ring

/-- (14), the DC-conductance term: along `G` the root branch of `(Cs² + k_s + W) + G s` through
`jΩ` has `dλ/dG = −1/(2C)`, real, so `dσ/dG = 1/(2C)`. -/
@[tmio T, powerlib_foundation] theorem damping_conductance {C W ks Ω : ℝ} (hC : 0 < C)
    (hΩ : 0 < Ω) (hΩ2 : C * Ω ^ 2 = ks + W) :
    ∃ lam : ℝ → ℂ, lam 0 = Ω * I ∧
      (∀ᶠ G in 𝓝 (0 : ℝ), (C * lam G ^ 2 + ks + W) + G * lam G = 0) ∧
      HasDerivAt lam (((-(1 / (2 * C))) : ℝ) : ℂ) 0 := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hΩ2c : (C : ℂ) * Ω ^ 2 = ks + W := by exact_mod_cast hΩ2
  have hP : HasStrictDerivAt (fun z : ℂ => C * z ^ 2 + ks + W) (C * (2 * (Ω * I))) (Ω * I) := by
    have := ((hasStrictDerivAt_pow 2 (Ω * I : ℂ)).const_mul (C : ℂ)).add_const ((ks : ℂ) + W)
    convert this using 1
    · funext z; ring
    · simp
  have hP0 : (C : ℂ) * (Ω * I) ^ 2 + ks + W = 0 := by
    linear_combination (C * Ω ^ 2 : ℂ) * I_sq - hΩ2c
  obtain ⟨lam, h0, hev, hd⟩ := exists_root_branch_affine hP (hasStrictDerivAt_id (Ω * I : ℂ)) hP0
    (mul_ne_zero hΩc I_ne_zero)
    (mul_ne_zero hC' (mul_ne_zero two_ne_zero (mul_ne_zero hΩc I_ne_zero)))
  refine ⟨lam, h0, hev, ?_⟩
  convert hd using 1
  simp only [id]
  push_cast
  field_simp

end powerlib.GFM.Matching
