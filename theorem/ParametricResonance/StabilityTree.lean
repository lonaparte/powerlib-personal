import dependencies.Mathlib
import theorem.Attributes

/-! # Normal-form conventions, current-loop order and additive channels

Foundation layer: exact identities behind several remarks of the stability-tree and
parametric-oscillation project notes. None of them is a stability theorem about a converter.

1. Hopf normal-form scaling (`normalForm_rescale`): if `z` solves `ż = λz + c z|z|²`, then
   `w = κ z` (`κ > 0`) solves `ẇ = λw + (c/κ²) w|w|²`. The Guckenheimer–Holmes planar coordinate
   `x − x* = T[Re w, −Im w]ᵀ = Re(v w)` and Kuznetsov's `x − x* = z q + z̄ q̄ = 2 Re(z q)` agree
   for `q = v` when `w = 2z` (`gh_coordinate`), so the GH cubic coefficient is exactly `Re c₁/4`
   and the GH cycle radius is exactly twice Kuznetsov's (`radius_factor_two`).
2. First Lyapunov coefficient normalization (`lyap1_scale`): in Kuznetsov's projection formula
   `ℓ₁ = Re[⟨p, C(q,q,q̄)⟩ − 2⟨p, B(q, A⁻¹B(q,q̄))⟩ + ⟨p, B(q̄, (2jω₀ − A)⁻¹B(q,q))⟩]/(2ω₀)`,
   rescaling the eigenvector `q ↦ s q` (with `p` rescaled to keep `⟨p, q⟩ = 1`) multiplies `ℓ₁`
   by `|s|²`: `ℓ₁ ∝ ‖q‖²`, so values computed with different eigenvector normalizations are not
   comparable without renormalization.
3. Current-loop order (`firstOrderLag_error`, `piLoop_error`): with `G₁(s) = ω/(s + ω)` and the
   PI closed loop `G_PI(s) = (2ζωs + ω²)/(s² + 2ζωs + ω²)` (`k_pc = 2ζωL`, `k_ic = ω²L`),
   `1 − G₁ = s/(s + ω)` and `1 − G_PI = s²/(s² + 2ζωs + ω²)`; at any fixed `s`,
   `ω (1 − G₁(s)) → s` and `ω² (1 − G_PI(s)) → s²` as `ω → ∞`: the low-frequency error is of exact
   order `ω⁻¹` for the lag and `ω⁻²` for the PI loop.
4. Additive forcing (`jacobian_additive_forcing`): for `f_ε(x, t) = f(x) + ε g(t)` the state
   Jacobian is `Df(x)` for every `ε, t`; in particular the frozen Jacobian at a fixed operating
   point, and every quantity computed from it (frozen damping ratio, frozen spectrum), does not
   depend on `ε` by construction.
5. GFM channels (`gfmPref_affine`, `gfmPref_jacobian_indep`, `gfmAngle_mixed_partial`): in the
   three-state VSM + low-pass model (`δ, ω, P_f`, export-positive power), a `P_ref` modulation
   enters affinely with a constant coefficient, so `A_u = ∂_u ∂_z f = 0`; a grid-angle modulation
   enters through `K₀ sin(δ − u)`, whose mixed partial `∂_u ∂_δ = ω_c K₀ sin(δ − u)` is nonzero at
   a loaded operating point (`sin δ₀ ≠ 0`).

Source: work-sync projects/gfl-gfm-stability-tree/notes/concepts/frozen-and-basin.md (幅值坐标
声明: GH vs Kuznetsov "精确差因子 4", `r_c` 差因子 2; PI 环 `O(ω_cc⁻²)` vs 一阶滞后
`O(ω_cc⁻¹)`); .../nonautonomous-criteria.md (加性强迫不进雅可比; GFM `P_ref` 通道 `A_u = 0`);
projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/notes/concepts/
forced-orbit-and-bandwidth.md (`ℓ₁ ∝ ‖q‖²`; 冻结 `ζ` 对 `ε` 恒定); projects/vsc-parametric-
oscillation/notes/theory-draft.md §1.3 (GFM model).
-/

noncomputable section
namespace powerlib.ParametricResonance.StabilityTree

open Complex Filter Topology

/-! ## 1. Hopf normal-form scaling -/

/-- `w = κ z` turns `ż = λz + c z|z|²` into `ẇ = λw + (c/κ²) w|w|²`. -/
@[powerlib_foundation] theorem normalForm_rescale {lam c : ℂ} {κ : ℝ} (hκ : κ ≠ 0) {z : ℝ → ℂ}
    (hz : ∀ t, HasDerivAt z (lam * z t + c * z t * (‖z t‖ ^ 2 : ℝ)) t) (t : ℝ) :
    HasDerivAt (fun t => (κ : ℂ) * z t)
      (lam * ((κ : ℂ) * z t) + c / (κ : ℂ) ^ 2 * ((κ : ℂ) * z t) *
        (‖(κ : ℂ) * z t‖ ^ 2 : ℝ)) t := by
  have h := (hz t).const_mul (κ : ℂ)
  convert h using 1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  push_cast
  field_simp

/-- GH coordinate `T[Re w, −Im w]ᵀ = Re(v w)`, and with `w = 2z` it equals Kuznetsov's
`z q + z̄ q̄ = 2 Re(z q)` (`q = v`). -/
@[powerlib_foundation] theorem gh_coordinate (v z : ℂ) :
    v.re * (2 * z).re - v.im * (2 * z).im = (v * (2 * z)).re ∧
      (v * (2 * z)).re = (z * v + (starRingEnd ℂ) (z * v)).re := by
  constructor
  · simp [Complex.mul_re]
  · simp [Complex.mul_re, Complex.conj_re]; ring

/-- With the GH coefficient `a₁ = Re c₁/4`, the cycle radius `√(α/a₁)` is twice Kuznetsov's. -/
@[powerlib_foundation] theorem radius_factor_two {α l : ℝ} (hl : 0 < l) :
    √(α / (l / 4)) = 2 * √(α / l) := by
  rw [show α / (l / 4) = 2 ^ 2 * (α / l) by field_simp; ring, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

/-! ## 2. `ℓ₁ ∝ ‖q‖²` -/

section Lyap

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Kuznetsov's projection formula for the first Lyapunov coefficient, with the bilinear and
trilinear forms `B`, `C`, the resolvents `A⁻¹`, `(2jω₀ − A)⁻¹`, the functional `x ↦ ⟨p, x⟩`, and
`q̄` passed as an independent vector `qc`. -/
def lyap1 (B : V →ₗ[ℂ] V →ₗ[ℂ] V) (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V) (Ainv R2 : V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] ℂ) (ω₀ : ℝ) (q qc : V) : ℝ :=
  (1 / (2 * ω₀)) * (P (C q q qc) - 2 * P (B q (Ainv (B q qc))) + P (B qc (R2 (B q q)))).re

/-- Rescaling the eigenvector `q ↦ s q`, `q̄ ↦ s̄ q̄`, `p ↦ p/s̄` (so `⟨p, q⟩` is unchanged)
multiplies `ℓ₁` by `|s|²`. -/
@[powerlib_foundation] theorem lyap1_scale (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V) (Ainv R2 : V →ₗ[ℂ] V) (P : V →ₗ[ℂ] ℂ) (ω₀ : ℝ)
    (q qc : V) {s : ℂ} (hs : s ≠ 0) :
    lyap1 B C Ainv R2 (s⁻¹ • P) ω₀ (s • q) ((starRingEnd ℂ) s • qc) =
      ‖s‖ ^ 2 * lyap1 B C Ainv R2 P ω₀ q qc := by
  have hn : ((‖s‖ ^ 2 : ℝ) : ℂ) = s * (starRingEnd ℂ) s := by
    rw [Complex.mul_conj, Complex.sq_norm]
  have e1 : (s⁻¹ • P) (C (s • q) (s • q) ((starRingEnd ℂ) s • qc)) =
      ((‖s‖ ^ 2 : ℝ) : ℂ) * P (C q q qc) := by
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [hn]; field_simp; try ring
  have e2 : (s⁻¹ • P) (B (s • q) (Ainv (B (s • q) ((starRingEnd ℂ) s • qc)))) =
      ((‖s‖ ^ 2 : ℝ) : ℂ) * P (B q (Ainv (B q qc))) := by
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [hn]; field_simp; try ring
  have e3 : (s⁻¹ • P) (B ((starRingEnd ℂ) s • qc) (R2 (B (s • q) (s • q)))) =
      ((‖s‖ ^ 2 : ℝ) : ℂ) * P (B qc (R2 (B q q))) := by
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [hn]; field_simp; try ring
  simp only [lyap1]
  rw [e1, e2, e3, show ((‖s‖ ^ 2 : ℝ) : ℂ) * P (C q q qc) -
      2 * (((‖s‖ ^ 2 : ℝ) : ℂ) * P (B q (Ainv (B q qc)))) +
      ((‖s‖ ^ 2 : ℝ) : ℂ) * P (B qc (R2 (B q q))) =
      ((‖s‖ ^ 2 : ℝ) : ℂ) * (P (C q q qc) - 2 * P (B q (Ainv (B q qc))) +
        P (B qc (R2 (B q q)))) by ring, Complex.re_ofReal_mul]
  ring

end Lyap

/-! ## 3. Current-loop order: PI versus first-order lag -/

/-- First-order lag `G₁(s) = ω/(s + ω)`. -/
def lagLoop (ω : ℝ) (s : ℂ) : ℂ := ω / (s + ω)

/-- PI closed loop `G_PI(s) = (2ζωs + ω²)/(s² + 2ζωs + ω²)`. -/
def piLoop (ζ ω : ℝ) (s : ℂ) : ℂ := (2 * ζ * ω * s + ω ^ 2) / (s ^ 2 + 2 * ζ * ω * s + ω ^ 2)

@[powerlib_foundation] theorem one_sub_lagLoop {ω : ℝ} {s : ℂ} (h : s + ω ≠ 0) :
    1 - lagLoop ω s = s / (s + ω) := by
  rw [lagLoop]; field_simp; ring

@[powerlib_foundation] theorem one_sub_piLoop {ζ ω : ℝ} {s : ℂ}
    (h : s ^ 2 + 2 * ζ * ω * s + ω ^ 2 ≠ 0) :
    1 - piLoop ζ ω s = s ^ 2 / (s ^ 2 + 2 * ζ * ω * s + ω ^ 2) := by
  rw [piLoop, eq_div_iff h, sub_mul, one_mul, div_mul_cancel₀ _ h]
  ring

/-- The lag error is of exact order `ω⁻¹`: `ω (1 − G₁(s)) → s`. -/
@[powerlib_foundation] theorem firstOrderLag_error (s : ℂ) :
    Tendsto (fun ω : ℝ => (ω : ℂ) * (1 - lagLoop ω s)) atTop (𝓝 s) := by
  have hinv : Tendsto (fun ω : ℝ => s * ((ω : ℂ))⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun ω : ℝ => ((ω : ℂ))⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
      simpa using h
    simpa using this.const_mul s
  have hlim : Tendsto (fun ω : ℝ => s / (s * ((ω : ℂ))⁻¹ + 1)) atTop (𝓝 (s / (0 + 1))) :=
    tendsto_const_nhds.div (hinv.add tendsto_const_nhds) (by norm_num)
  rw [zero_add, div_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (‖s‖)] with ω hω
  have hω0 : (ω : ℂ) ≠ 0 := by
    have : 0 < ω := lt_of_le_of_lt (norm_nonneg s) hω
    exact_mod_cast this.ne'
  have hsω : s + ω ≠ 0 := by
    intro h
    have : ‖s‖ = ω := by
      rw [show s = -(ω : ℂ) by linear_combination h, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt (norm_nonneg s) hω)]
    linarith
  rw [one_sub_lagLoop hsω]
  field_simp

/-- The PI-loop error is of exact order `ω⁻²`: `ω² (1 − G_PI(s)) → s²`. -/
@[powerlib_foundation] theorem piLoop_error (ζ : ℝ) (s : ℂ) :
    Tendsto (fun ω : ℝ => (ω : ℂ) ^ 2 * (1 - piLoop ζ ω s)) atTop (𝓝 (s ^ 2)) := by
  have hinv : Tendsto (fun ω : ℝ => ((ω : ℂ))⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
    simpa using h
  have hden : Tendsto (fun ω : ℝ => s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹ + 1)
      atTop (𝓝 (s ^ 2 * 0 ^ 2 + 2 * ζ * s * 0 + 1)) :=
    (((tendsto_const_nhds.mul (hinv.pow 2)).add (tendsto_const_nhds.mul hinv)).add
      tendsto_const_nhds)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    zero_add] at hden
  have hlim := (tendsto_const_nhds (x := s ^ 2)).div hden one_ne_zero
  rw [div_one] at hlim
  apply hlim.congr'
  -- for large `ω` the denominator does not vanish
  have hev : ∀ᶠ ω : ℝ in atTop,
      ‖s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹‖ < 1 / 2 := by
    have h0 : Tendsto (fun ω : ℝ => s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹)
        atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := s ^ 2)).mul (hinv.pow 2)).add
        ((tendsto_const_nhds (x := 2 * ζ * s)).mul hinv)
      simpa using this
    exact (h0.norm).eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1 / 2))
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with ω hω hpos
  have hω0 : (ω : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hrep : s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹ + 1 =
      (s ^ 2 + 2 * ζ * ω * s + (ω : ℂ) ^ 2) / (ω : ℂ) ^ 2 := by
    field_simp; try ring
  have hD : s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹ + 1 ≠ 0 := by
    intro h
    have : s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹ = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hω
    norm_num at hω
  have hD' : s ^ 2 + 2 * ζ * ω * s + (ω : ℂ) ^ 2 ≠ 0 := by
    intro h
    apply hD
    rw [hrep, h, zero_div]
  show s ^ 2 / (s ^ 2 * ((ω : ℂ))⁻¹ ^ 2 + 2 * ζ * s * ((ω : ℂ))⁻¹ + 1) =
    (ω : ℂ) ^ 2 * (1 - piLoop ζ ω s)
  rw [hrep, one_sub_piLoop hD', div_div_eq_mul_div]
  ring

/-! ## 4. Additive forcing does not enter the Jacobian -/

/-- For `f_ε(x, t) = f(x) + ε g(t)` the state Jacobian is `Df(x)` for every `ε` and `t`. -/
@[powerlib_foundation] theorem jacobian_additive_forcing {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → E) (g : ℝ → E) (ε t : ℝ) (x : E) :
    fderiv ℝ (fun y => f y + ε • g t) x = fderiv ℝ f x :=
  fderiv_add_const _

/-! ## 5. GFM channels: `P_ref` versus grid angle -/

/-- VSM + low-pass GFM field `(δ̇, ω̇, Ṗ_f)` with a `P_ref` deviation `u` (export-positive). -/
def gfmPref (M D ωc K₀ P₀ u : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![z 1, (P₀ + u - z 2 - D * z 1) / M, ωc * (K₀ * Real.sin (z 0) - z 2)]

/-- The same model with a grid-angle deviation `u` entering through `sin(δ − u)`. -/
def gfmAngle (M D ωc K₀ P₀ u : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![z 1, (P₀ - z 2 - D * z 1) / M, ωc * (K₀ * Real.sin (z 0 - u) - z 2)]

/-- The `P_ref` channel is affine with a constant coefficient `(0, 1/M, 0)`. -/
@[powerlib_foundation] theorem gfmPref_affine (M D ωc K₀ P₀ u : ℝ) (z : Fin 3 → ℝ) :
    gfmPref M D ωc K₀ P₀ u z = gfmPref M D ωc K₀ P₀ 0 z + u • ![0, 1 / M, 0] := by
  ext i; fin_cases i <;> simp [gfmPref]; ring

/-- Hence `A_u = 0`: the state Jacobian of the `P_ref` channel does not depend on `u`. -/
@[powerlib_foundation] theorem gfmPref_jacobian_indep (M D ωc K₀ P₀ u : ℝ) (z : Fin 3 → ℝ) :
    fderiv ℝ (gfmPref M D ωc K₀ P₀ u) z = fderiv ℝ (gfmPref M D ωc K₀ P₀ 0) z := by
  have : gfmPref M D ωc K₀ P₀ u = fun y => gfmPref M D ωc K₀ P₀ 0 y + u • ![0, 1 / M, 0] :=
    funext (gfmPref_affine M D ωc K₀ P₀ u)
  rw [this, fderiv_add_const]

/-- Grid-angle channel: the `δ`-derivative of the filter row is `ω_c K₀ cos(δ − u)`, and its
`u`-derivative is `ω_c K₀ sin(δ − u)`, nonzero at a loaded point: `A_u ≠ 0`. -/
@[powerlib_foundation] theorem gfmAngle_mixed_partial (M D ωc K₀ P₀ u : ℝ) (z : Fin 3 → ℝ) :
    HasDerivAt (fun δ => gfmAngle M D ωc K₀ P₀ u (Function.update z 0 δ) 2)
        (ωc * K₀ * Real.cos (z 0 - u)) (z 0) ∧
      HasDerivAt (fun v => ωc * K₀ * Real.cos (z 0 - v)) (ωc * K₀ * Real.sin (z 0 - u)) u ∧
      (ωc * K₀ ≠ 0 → Real.sin (z 0) ≠ 0 → ωc * K₀ * Real.sin (z 0 - 0) ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (((Real.hasDerivAt_sin (z 0 - u)).comp (z 0)
      ((hasDerivAt_id (z 0)).sub_const u)).const_mul K₀).sub_const (z 2) |>.const_mul ωc
    convert h using 1
    · funext δ; simp [gfmAngle, Function.update]
    · simp; ring
  · have h := ((Real.hasDerivAt_cos (z 0 - u)).comp u
      ((hasDerivAt_id u).const_sub (z 0))).const_mul (ωc * K₀)
    convert h using 1
    simp; ring
  · intro h1 h2
    rw [sub_zero]
    exact mul_ne_zero h1 h2

end powerlib.ParametricResonance.StabilityTree
