import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Network modulation transfer: Thévenin map of a GFM–grid node seen by GFL branches

Foundation layer (category B).

Source: work-sync `projects/vsc-parametric-oscillation/references/gfm-driven-gfl-parametric-resonance/
notes/concepts/network-modulation-transfer.md` (sections "开路戴维南映射", "幅值和相角通道",
"小摆幅与有限摆幅", "带载单机与多机映射").

Model boundary.
* Balanced three-phase, positive-sequence fundamental phasors, lossless purely reactive
  network, quasi-static (phasor algebra, no network dynamics).
* Topology: the GFM internal EMF `E e^{jδ}` (`E` real) connects through `jX₂` to a common node
  `c`, the infinite bus `V_∞` (real) through `jX₃`, and GFL unit `i` through its own branch
  `jX_{1i}`. Currents `I_i` flow **into** GFL `i` (IN-positive), so the branch law is
  `V_i = V_c - jX_{1i} I_i` and KCL at `c` reads `Σᵢ I_i + (V_c - E e^{jδ})/(jX₂) + (V_c - V_∞)/(jX₃) = 0`.
* `δ` is a parameter (the GFM angle); its own dynamics are not modelled here.

Results.
* `vth_eq`: `V_th(δ) = a_V e^{jδ} + b_V = (X₃ E e^{jδ} + X₂ V_∞)/(X₂ + X₃)` with
  `β = X₃/(X₂+X₃)`, `a_V = βE`, `b_V = (1-β)V_∞`; `X_eq = X₂X₃/(X₂+X₃)`, `X_g = X₁ + X_eq`.
* `kcl_iff` / `terminal_voltages`: KCL ⇔ `V_c = V_th − jX_eq Σ I_k`, hence
  `V = V_th 𝟙 − j[diag(X_{1i}) + X_eq 𝟙𝟙ᵀ] I`; one branch: `V_GFL = V_th − jX_g I`.
* `norm_vth`: `V(δ) = √(a_V² + b_V² + 2a_V b_V cos δ)`; `hasDerivAt_norm_vth`:
  `dV/dδ = −a_V b_V sin δ / V` (premise `V(δ) ≠ 0`); `hasDerivAt_arg_vth`:
  `dθ_s/dδ = (a_V² + a_V b_V cos δ)/(a_V² + b_V² + 2a_V b_V cos δ)` for the principal argument
  (premise: `V_th(δ)` in the slit plane, i.e. not on `(-∞, 0]`).
* `kappa_eq`: `κ_δ = |dV/dδ|/V₀ = a_V b_V |sin δ₀| / V₀²` (`a_V, b_V ≥ 0`).
* Equal weights `a_V = b_V = 1/2`: `V(δ) = |cos(δ/2)|` and `κ_δ = |tan(δ₀/2)|/2`; at `δ₀ = 0`
  the swing `δ = δ̂ cos φ` gives `V = 1 − δ̂²/16 − (δ̂²/16) cos 2φ + r` with
  `|r| ≤ 5 δ̂⁴/1536` for `|δ̂| ≤ 2` (an explicit `O(δ̂⁴)` remainder).
* `commonMode` / `diffMode` / `det_modes`: with equal branch reactances `x`, the matrix
  `x I + X_eq 𝟙𝟙ᵀ` has the common-mode eigenvalue `x + N X_eq` (eigenvector `𝟙`) and the
  differential eigenvalue `x` on `{Σ vᵢ = 0}`; `det(sI − M) = (s − x)^{N−1}(s − x − N X_eq)`, so `x`
  has algebraic multiplicity `N − 1`.

* Fourier-coefficient level (note "小摆幅与有限摆幅"). For the swing `δ(φ) = δ₀ + δ̂ cos φ`
  (`φ = ω_p t`, one period `[0, 2π]`) and an amplitude map `F` (here `F = |V_th|`):
  `swingMean` `V̄ = (1/2π)∫ F(δ(φ)) dφ`, `swingCoeff` `V_n = (1/2π)∫ F(δ(φ)) e^{−jnφ} dφ`,
  `harmonicRatio` `ε_n = 2|V_n|/V̄` (`ε_V = ε_1`). `swingCoeff_eq`, `harmonicRatio_eq`: the
  swing is even in `φ`, so `V_n = a_n/2` is real (`cosCoeff` `a_n = (1/π)∫ F(δ(φ)) cos nφ dφ`)
  and `ε_n = |a_n|/V̄`.
  - Small swing, explicit constants: under a Taylor bound `|F(δ₀+h) − F(δ₀) − F' h| ≤ C h²`
    (`|h| ≤ h₀`; `exists_taylor_bound` derives it from `F ∈ C²` with `F' = F'(δ₀)`),
    `|V̄ − F(δ₀)| ≤ C δ̂²` (`swingMean_sub_le`), `|a_n − F' δ̂ [n = 1]| ≤ 2C δ̂²`
    (`cosCoeff_sub_le`), hence `|ε₁ − (|F'|/F(δ₀)) δ̂| ≤ (4C/F(δ₀) + 2|F'|C h₀/F(δ₀)²) δ̂²`
    (`harmonicRatio_one_sub_le`) and `ε_n ≤ (4C/F(δ₀)) δ̂²` for `n ≥ 2` (`harmonicRatio_le`).
  - `harmonicRatio_one_isBigO`, `harmonicRatio_isBigO`; for the Thévenin map `epsV_isBigO`:
    **`ε_V = κ_δ δ̂ + O(δ̂²)`** as `δ̂ → 0⁺` with `κ_δ = a_V b_V |sin δ₀|/V₀²` (`V₀ > 0`,
    `a_V, b_V ≥ 0`), and `epsN_isBigO`: `ε_n = O(δ̂²)` for every `n ≥ 2` (only the second-order
    rate is proved, not the sharper `O(δ̂ⁿ)`).
  - Finite swing (every amplitude): `harmonicRatio_le_two`, `epsN_le_two`: `0 ≤ ε_n ≤ 2`;
    `cosCoeff_odd_eq_zero`, `harmonicRatio_odd_eq_zero`, `epsN_odd_eq_zero_at_zero`: at a
    symmetric operating point (`F(δ₀ + h) = F(δ₀ − h)`, e.g. `δ₀ = 0`) every odd harmonic
    vanishes, `ε_{2k+1} = 0`, so only even harmonics can drive a tongue at `nω_p ≈ 2ω_cr`.
  The exact finite-swing values of `ε_n` (computed "from the actual periodic orbit") have no closed
  form and are not claimed; the candidate measure `𝓜` is a screening heuristic, not a theorem.
-/

noncomputable section
namespace powerlib.Network.ModulationTransfer
open Complex Matrix

/-! ## Open-circuit Thévenin map -/

/-- GFM voltage weight `β = X₃/(X₂ + X₃)`. -/
def beta (X2 X3 : ℝ) : ℝ := X3 / (X2 + X3)

/-- `a_V = β E`. -/
def aV (X2 X3 E : ℝ) : ℝ := beta X2 X3 * E

/-- `b_V = (1 − β) V_∞`. -/
def bV (X2 X3 Vinf : ℝ) : ℝ := (1 - beta X2 X3) * Vinf

/-- Open-circuit Thévenin voltage `V_th(δ) = a_V e^{jδ} + b_V`. -/
def vth (X2 X3 E Vinf δ : ℝ) : ℂ := (aV X2 X3 E : ℂ) * exp (δ * I) + (bV X2 X3 Vinf : ℂ)

/-- Parallel reactance `X_eq = X₂X₃/(X₂ + X₃)`. -/
def Xeq (X2 X3 : ℝ) : ℝ := X2 * X3 / (X2 + X3)

/-- Single-branch Thévenin reactance `X_g = X₁ + X_eq`. -/
def Xg (X1 X2 X3 : ℝ) : ℝ := X1 + Xeq X2 X3

@[powerlib_foundation] theorem one_sub_beta {X2 X3 : ℝ} (h : X2 + X3 ≠ 0) :
    1 - beta X2 X3 = X2 / (X2 + X3) := by
  unfold beta; field_simp; ring

@[powerlib_foundation] theorem vth_eq {X2 X3 E Vinf : ℝ} (h : X2 + X3 ≠ 0) (δ : ℝ) :
    vth X2 X3 E Vinf δ = (X3 * E * exp (δ * I) + X2 * Vinf) / (X2 + X3) := by
  have h' : (X2 : ℂ) + X3 ≠ 0 := by exact_mod_cast h
  unfold vth aV bV beta
  push_cast
  field_simp
  ring

/-! ## Loaded node: KCL and the multi-branch map -/

variable {N : ℕ}

/-- KCL at the common node with GFL currents `I` (IN-positive). -/
def KCL (X2 X3 E Vinf δ : ℝ) (Vc : ℂ) (Icur : Fin N → ℂ) : Prop :=
  (∑ k, Icur k) + (Vc - E * exp (δ * I)) / (I * X2) + (Vc - Vinf) / (I * X3) = 0

@[powerlib_foundation] theorem kcl_iff {X2 X3 E Vinf : ℝ} (h2 : X2 ≠ 0) (h3 : X3 ≠ 0)
    (h : X2 + X3 ≠ 0) (δ : ℝ) (Vc : ℂ) (Icur : Fin N → ℂ) :
    KCL X2 X3 E Vinf δ Vc Icur ↔
      Vc = vth X2 X3 E Vinf δ - I * Xeq X2 X3 * ∑ k, Icur k := by
  have h2' : (X2 : ℂ) ≠ 0 := by exact_mod_cast h2
  have h3' : (X3 : ℂ) ≠ 0 := by exact_mod_cast h3
  have h' : (X2 : ℂ) + X3 ≠ 0 := by exact_mod_cast h
  rw [vth_eq h]
  unfold KCL Xeq
  push_cast
  set S := ∑ k, Icur k
  set e := exp (δ * I)
  have hsum : S + (Vc - E * e) / (I * X2) + (Vc - Vinf) / (I * X3) =
      (I * X2 * X3 * S + X3 * (Vc - E * e) + X2 * (Vc - Vinf)) / (I * X2 * X3) := by
    field_simp
  have hden : I * (X2 : ℂ) * X3 ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero h2') h3'
  rw [hsum, div_eq_zero_iff, or_iff_left hden]
  constructor
  · intro hk
    have hv : Vc = (X3 * E * e + X2 * Vinf - I * X2 * X3 * S) / (X2 + X3) := by
      rw [eq_div_iff h']
      linear_combination hk
    rw [hv]
    field_simp
  · intro hv
    have hv' : Vc * (X2 + X3) = X3 * E * e + X2 * Vinf - I * X2 * X3 * S := by
      rw [hv]
      field_simp
    linear_combination hv'

/-- Terminal voltages of the GFL branches: `V = V_th 𝟙 − j[diag(X₁) + X_eq 𝟙𝟙ᵀ] I`. -/
@[powerlib_foundation] theorem terminal_voltages {X2 X3 E Vinf : ℝ} (h2 : X2 ≠ 0) (h3 : X3 ≠ 0)
    (h : X2 + X3 ≠ 0) (δ : ℝ) (X1 : Fin N → ℝ) (Vc : ℂ) (Icur V : Fin N → ℂ)
    (hkcl : KCL X2 X3 E Vinf δ Vc Icur) (hbr : ∀ i, V i = Vc - I * X1 i * Icur i) :
    V = (fun _ => vth X2 X3 E Vinf δ) -
      I • ((diagonal (fun i => (X1 i : ℂ)) + (Xeq X2 X3 : ℂ) • Matrix.of (fun _ _ => (1 : ℂ)))
        *ᵥ Icur) := by
  rw [kcl_iff h2 h3 h] at hkcl
  funext i
  rw [hbr i, hkcl]
  simp only [Pi.sub_apply, Pi.smul_apply, add_mulVec, smul_mulVec, mulVec_diagonal, Pi.add_apply,
    smul_eq_mul]
  have : (Matrix.of (fun _ _ => (1 : ℂ)) *ᵥ Icur) i = ∑ k, Icur k := by
    simp [mulVec, dotProduct]
  rw [this]
  ring

/-- One GFL branch: `V_GFL = V_th − j X_g I_in`. -/
@[powerlib_foundation] theorem single_branch {X1 X2 X3 E Vinf : ℝ} (h2 : X2 ≠ 0) (h3 : X3 ≠ 0)
    (h : X2 + X3 ≠ 0) (δ : ℝ) (Vc Iin Vgfl : ℂ) (hkcl : KCL X2 X3 E Vinf δ Vc (fun _ : Fin 1 => Iin))
    (hbr : Vgfl = Vc - I * X1 * Iin) :
    Vgfl = vth X2 X3 E Vinf δ - I * Xg X1 X2 X3 * Iin := by
  rw [kcl_iff h2 h3 h] at hkcl
  rw [hbr, hkcl]
  simp only [Finset.univ_unique, Finset.sum_singleton, Xg]
  push_cast
  ring

/-! ## Magnitude and phase channels -/

@[powerlib_foundation] theorem normSq_affine_exp (a b δ : ℝ) :
    normSq ((a : ℂ) * exp (δ * I) + b) = a ^ 2 + b ^ 2 + 2 * a * b * Real.cos δ := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  rw [normSq_apply]
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  have := Real.sin_sq_add_cos_sq δ
  nlinarith [this]

/-- `V(δ) = |V_th(δ)| = √(a_V² + b_V² + 2a_V b_V cos δ)`. -/
@[powerlib_foundation] theorem norm_vth (X2 X3 E Vinf δ : ℝ) :
    ‖vth X2 X3 E Vinf δ‖ =
      Real.sqrt (aV X2 X3 E ^ 2 + bV X2 X3 Vinf ^ 2 + 2 * aV X2 X3 E * bV X2 X3 Vinf * Real.cos δ) := by
  rw [← normSq_affine_exp, Complex.norm_def]
  rfl

/-- Amplitude channel: `dV/dδ = −a_V b_V sin δ / V` wherever `V(δ) ≠ 0`. -/
@[powerlib_foundation] theorem hasDerivAt_norm_vth (X2 X3 E Vinf δ : ℝ)
    (hV : ‖vth X2 X3 E Vinf δ‖ ≠ 0) :
    HasDerivAt (fun d => ‖vth X2 X3 E Vinf d‖)
      (-(aV X2 X3 E * bV X2 X3 Vinf * Real.sin δ) / ‖vth X2 X3 E Vinf δ‖) δ := by
  set a := aV X2 X3 E
  set b := bV X2 X3 Vinf
  have hfun : (fun d => ‖vth X2 X3 E Vinf d‖) =
      fun d => Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * Real.cos d) := by
    funext d; exact norm_vth X2 X3 E Vinf d
  rw [hfun]
  have hQ : HasDerivAt (fun d => a ^ 2 + b ^ 2 + 2 * a * b * Real.cos d)
      (2 * a * b * (-Real.sin δ)) δ := by
    have := ((Real.hasDerivAt_cos δ).const_mul (2 * a * b)).const_add (a ^ 2 + b ^ 2)
    simpa using this
  have hne : a ^ 2 + b ^ 2 + 2 * a * b * Real.cos δ ≠ 0 := by
    intro h0
    apply hV
    rw [norm_vth, h0, Real.sqrt_zero]
  have := hQ.sqrt hne
  convert this using 1
  rw [norm_vth]
  field_simp
  ring

@[powerlib_foundation] theorem im_logDeriv_affine_exp (a b δ : ℝ) :
    ((a : ℂ) * (exp (δ * I) * I) / ((a : ℂ) * exp (δ * I) + b)).im =
      (a ^ 2 + a * b * Real.cos δ) / (a ^ 2 + b ^ 2 + 2 * a * b * Real.cos δ) := by
  have hQ := normSq_affine_exp a b δ
  rw [div_im, hQ]
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]
  have hs := Real.sin_sq_add_cos_sq δ
  rw [← sub_div]
  congr 1
  ring_nf
  nlinarith [hs]

/-- Phase channel: for the principal argument `θ_s = arg V_th`,
`dθ_s/dδ = (a_V² + a_V b_V cos δ)/(a_V² + b_V² + 2a_V b_V cos δ)` (premise: `V_th(δ)` lies in the
slit plane; elsewhere the same formula holds for any continuous phase lift). -/
@[powerlib_foundation] theorem hasDerivAt_arg_vth (X2 X3 E Vinf δ : ℝ)
    (hslit : vth X2 X3 E Vinf δ ∈ slitPlane) :
    HasDerivAt (fun d => arg (vth X2 X3 E Vinf d))
      ((aV X2 X3 E ^ 2 + aV X2 X3 E * bV X2 X3 Vinf * Real.cos δ) /
        (aV X2 X3 E ^ 2 + bV X2 X3 Vinf ^ 2 + 2 * aV X2 X3 E * bV X2 X3 Vinf * Real.cos δ)) δ := by
  have h1 : HasDerivAt (fun d : ℝ => (d : ℂ) * I) I δ := by
    simpa using (hasDerivAt_id (δ : ℝ)).ofReal_comp.mul_const I
  have h3 : HasDerivAt (fun d : ℝ => vth X2 X3 E Vinf d)
      ((aV X2 X3 E : ℂ) * (exp (δ * I) * I)) δ :=
    ((h1.cexp).const_mul (aV X2 X3 E : ℂ)).add_const (bV X2 X3 Vinf : ℂ)
  have hlog := h3.clog_real hslit
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt δ hlog
  have harg : (fun d => arg (vth X2 X3 E Vinf d)) =
      Complex.imCLM ∘ fun d => log (vth X2 X3 E Vinf d) := by
    funext d; simp [log_im]
  rw [harg]
  convert him using 1
  rw [Complex.imCLM_apply]
  exact (im_logDeriv_affine_exp _ _ δ).symm

/-- Modulation index of the amplitude channel: `κ_δ = |dV/dδ|/V₀ = a_V b_V |sin δ₀| / V₀²`. -/
@[powerlib_foundation] theorem kappa_eq {a b V0 δ0 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hV : 0 < V0) :
    (1 / V0) * |-(a * b * Real.sin δ0) / V0| = a * b * |Real.sin δ0| / V0 ^ 2 := by
  rw [abs_div, abs_neg, abs_of_pos hV, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  field_simp

/-! ## Equal weights `a_V = b_V = 1/2` -/

/-- `a_V = b_V = 1/2`: `V(δ) = |cos(δ/2)|`. -/
@[powerlib_foundation] theorem norm_half_half (δ : ℝ) :
    ‖((1 / 2 : ℝ) : ℂ) * exp (δ * I) + ((1 / 2 : ℝ) : ℂ)‖ = |Real.cos (δ / 2)| := by
  rw [Complex.norm_def, normSq_affine_exp]
  have hc : Real.cos δ = 2 * Real.cos (δ / 2) ^ 2 - 1 := by
    have := Real.cos_sq (δ / 2)
    rw [show 2 * (δ / 2) = δ by ring] at this
    linarith
  rw [hc, ← Real.sqrt_sq_eq_abs]
  congr 1
  ring

/-- `a_V = b_V = 1/2`: `κ_δ = |tan(δ₀/2)|/2` (where `cos(δ₀/2) ≠ 0`). -/
@[powerlib_foundation] theorem kappa_half_half {δ0 : ℝ} (hc : Real.cos (δ0 / 2) ≠ 0) :
    (1 / 2) * (1 / 2) * |Real.sin δ0| / |Real.cos (δ0 / 2)| ^ 2 = |Real.tan (δ0 / 2)| / 2 := by
  have hs : Real.sin δ0 = 2 * Real.sin (δ0 / 2) * Real.cos (δ0 / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hc' : 0 < |Real.cos (δ0 / 2)| := abs_pos.mpr hc
  rw [hs, Real.tan_eq_sin_div_cos, abs_div, abs_mul, abs_mul,
    show |(2 : ℝ)| = 2 by norm_num]
  field_simp

/-- `δ₀ = 0`, `a_V = b_V = 1/2`, `δ = δ̂ cos φ`: `V = 1 − δ̂²/16 − (δ̂²/16) cos 2φ + O(δ̂⁴)`
with the explicit remainder bound `5 δ̂⁴/1536` for `|δ̂| ≤ 2`. -/
@[powerlib_foundation] theorem second_harmonic_expansion {dh : ℝ} (hd : |dh| ≤ 2) (φ : ℝ) :
    |‖((1 / 2 : ℝ) : ℂ) * exp ((dh * Real.cos φ : ℝ) * I) + ((1 / 2 : ℝ) : ℂ)‖ -
        (1 - dh ^ 2 / 16 - dh ^ 2 / 16 * Real.cos (2 * φ))| ≤ 5 * dh ^ 4 / 1536 := by
  rw [norm_half_half]
  set x := dh * Real.cos φ / 2 with hx
  have hxle : |x| ≤ 1 := by
    rw [hx, abs_div, abs_mul]
    have := Real.abs_cos_le_one φ
    have : |dh| * |Real.cos φ| ≤ 2 := by nlinarith [abs_nonneg dh, abs_nonneg (Real.cos φ)]
    rw [show |(2 : ℝ)| = 2 by norm_num]
    linarith [div_le_one_of_le₀ this (by norm_num : (0 : ℝ) ≤ 2)]
  have hcos_nonneg : 0 ≤ Real.cos x := by
    apply Real.cos_nonneg_of_mem_Icc
    have := Real.two_le_pi
    constructor <;> linarith [abs_le.mp hxle]
  rw [abs_of_nonneg hcos_nonneg]
  have hb := Real.cos_bound hxle
  have hc2 : Real.cos (2 * φ) = 2 * Real.cos φ ^ 2 - 1 := Real.cos_two_mul φ
  have hpoly : 1 - x ^ 2 / 2 = 1 - dh ^ 2 / 16 - dh ^ 2 / 16 * Real.cos (2 * φ) := by
    rw [hc2, hx]; ring
  rw [← hpoly]
  calc |Real.cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 * (5 / 96) := hb
    _ ≤ (|dh| / 2) ^ 4 * (5 / 96) := by
        gcongr
        rw [hx, abs_div, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
        have := Real.abs_cos_le_one φ
        have : |dh| * |Real.cos φ| ≤ |dh| := by
          nlinarith [abs_nonneg dh, abs_nonneg (Real.cos φ)]
        linarith
    _ = 5 * dh ^ 4 / 1536 := by
        rw [div_pow, (by decide : Even 4).pow_abs dh]
        ring

/-! ## Fourier coefficients of the amplitude under a periodic swing -/

section Fourier

open Filter Topology Asymptotics

/-- `∫₀^{2π} cos(m φ) dφ = 0` for a positive integer `m`. -/
@[powerlib_foundation] theorem integral_cos_nat_mul {m : ℕ} (hm : m ≠ 0) :
    ∫ φ in (0 : ℝ)..2 * Real.pi, Real.cos (m * φ) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm', integral_cos, mul_zero,
    Real.sin_zero, sub_zero]
  have : (m : ℝ) * (2 * Real.pi) = ((2 * m : ℕ) : ℝ) * Real.pi := by push_cast; ring
  rw [this, Real.sin_nat_mul_pi, smul_zero]

/-- `∫₀^{2π} cos φ cos(n φ) dφ` is `π` for `n = 1` and `0` otherwise. -/
@[powerlib_foundation] theorem integral_cos_mul_cos_nat (n : ℕ) :
    ∫ φ in (0 : ℝ)..2 * Real.pi, Real.cos φ * Real.cos (n * φ) =
      if n = 1 then Real.pi else 0 := by
  rcases n with _ | _ | m
  · simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, integral_cos, Real.sin_two_pi,
      Real.sin_zero, sub_zero]
    simp
  · simp only [zero_add, ite_true]
    have : (fun φ : ℝ => Real.cos φ * Real.cos (((1 : ℕ) : ℝ) * φ)) = fun φ => Real.cos φ ^ 2 := by
      funext φ; rw [Nat.cast_one, one_mul]; ring
    rw [this, integral_cos_sq]
    simp [Real.sin_two_pi]
  · have hprod : ∀ φ : ℝ, Real.cos φ * Real.cos (((m + 1 + 1 : ℕ) : ℝ) * φ) =
        (Real.cos (((m + 3 : ℕ) : ℝ) * φ) + Real.cos (((m + 1 : ℕ) : ℝ) * φ)) / 2 := by
      intro φ
      have h1 : ((m + 3 : ℕ) : ℝ) * φ = ((m + 1 + 1 : ℕ) : ℝ) * φ + φ := by push_cast; ring
      have h2 : ((m + 1 : ℕ) : ℝ) * φ = ((m + 1 + 1 : ℕ) : ℝ) * φ - φ := by push_cast; ring
      rw [h1, h2, Real.cos_add, Real.cos_sub]
      ring
    simp_rw [hprod]
    have i3 : Continuous fun φ : ℝ => Real.cos (((m + 3 : ℕ) : ℝ) * φ) := by fun_prop
    have i1 : Continuous fun φ : ℝ => Real.cos (((m + 1 : ℕ) : ℝ) * φ) := by fun_prop
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (i3.intervalIntegrable _ _)
      (i1.intervalIntegrable _ _), integral_cos_nat_mul (by omega), integral_cos_nat_mul (by omega)]
    simp

/-- Mean amplitude over one modulation period of the swing `δ(φ) = δ₀ + δ̂ cos φ`
(`φ = ω_p t`): `V̄ = (1/2π) ∫₀^{2π} F(δ(φ)) dφ`, for an amplitude map `F` (`F = ‖V_th‖`). -/
def swingMean (F : ℝ → ℝ) (δ0 dh : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ)

/-- `n`-th Fourier coefficient `V_n = (1/2π) ∫₀^{2π} F(δ(φ)) e^{−j n φ} dφ`. -/
def swingCoeff (F : ℝ → ℝ) (δ0 dh : ℝ) (n : ℕ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi,
    (F (δ0 + dh * Real.cos φ) : ℂ) * Complex.exp (-(((n : ℝ) * φ : ℝ) : ℂ) * Complex.I)

/-- Harmonic modulation ratio `ε_n = 2 |V_n| / V̄`; `ε_V = ε_1`. -/
def harmonicRatio (F : ℝ → ℝ) (δ0 dh : ℝ) (n : ℕ) : ℝ :=
  2 * ‖swingCoeff F δ0 dh n‖ / swingMean F δ0 dh

/-- Cosine coefficient `a_n = (1/π) ∫₀^{2π} F(δ(φ)) cos(n φ) dφ`. -/
def cosCoeff (F : ℝ → ℝ) (δ0 dh : ℝ) (n : ℕ) : ℝ :=
  Real.pi⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ) * Real.cos (n * φ)

/-- The swing is even in `φ`, so every sine moment vanishes. -/
@[powerlib_foundation] theorem integral_sin_moment_eq_zero (F : ℝ → ℝ) (δ0 dh : ℝ) (n : ℕ) :
    ∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ) * Real.sin (n * φ) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun φ => F (δ0 + dh * Real.cos φ) * Real.sin (n * φ)) (a := 0) (b := 2 * Real.pi)
    (2 * Real.pi)
  simp only [sub_self, sub_zero] at h
  have hsym : ∀ φ : ℝ, F (δ0 + dh * Real.cos (2 * Real.pi - φ)) * Real.sin (n * (2 * Real.pi - φ)) =
      -(F (δ0 + dh * Real.cos φ) * Real.sin (n * φ)) := by
    intro φ
    have hc : Real.cos (2 * Real.pi - φ) = Real.cos φ := by
      rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]; ring
    have hs : Real.sin (n * (2 * Real.pi - φ)) = -Real.sin (n * φ) := by
      have e : (n : ℝ) * (2 * Real.pi - φ) = ((2 * n : ℕ) : ℝ) * Real.pi - n * φ := by
        push_cast; ring
      rw [e, Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
      rcases Nat.even_or_odd (2 * n) with he | ho
      · rw [he.neg_one_pow]; ring
      · exact absurd ho (Nat.not_odd_iff_even.mpr (even_two_mul n))
    rw [hc, hs]; ring
  simp_rw [hsym, intervalIntegral.integral_neg] at h
  linarith

/-- `V_n = a_n / 2`: the Fourier coefficients of the swing are real. -/
@[powerlib_foundation] theorem swingCoeff_eq {F : ℝ → ℝ} (hF : Continuous F) (δ0 dh : ℝ)
    (n : ℕ) : swingCoeff F δ0 dh n = ((cosCoeff F δ0 dh n / 2 : ℝ) : ℂ) := by
  have hpt : ∀ φ : ℝ, (F (δ0 + dh * Real.cos φ) : ℂ) *
      Complex.exp (-(((n : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
      ((F (δ0 + dh * Real.cos φ) * Real.cos (n * φ) : ℝ) : ℂ) -
        ((F (δ0 + dh * Real.cos φ) * Real.sin (n * φ) : ℝ) : ℂ) * Complex.I := by
    intro φ
    rw [show -(((n : ℝ) * φ : ℝ) : ℂ) * Complex.I = ((-((n : ℝ) * φ) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have hc1 : Continuous fun φ : ℝ => F (δ0 + dh * Real.cos φ) * Real.cos (n * φ) := by fun_prop
  have hc2 : Continuous fun φ : ℝ => F (δ0 + dh * Real.cos φ) * Real.sin (n * φ) := by fun_prop
  unfold swingCoeff cosCoeff
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    integral_sin_moment_eq_zero]
  · push_cast
    field_simp
    simp
  · exact (Complex.continuous_ofReal.comp hc1).intervalIntegrable _ _
  · exact ((Complex.continuous_ofReal.comp hc2).mul continuous_const).intervalIntegrable _ _

/-- `ε_n = |a_n| / V̄`. -/
@[powerlib_foundation] theorem harmonicRatio_eq {F : ℝ → ℝ} (hF : Continuous F) (δ0 dh : ℝ)
    (n : ℕ) : harmonicRatio F δ0 dh n = |cosCoeff F δ0 dh n| / swingMean F δ0 dh := by
  rw [harmonicRatio, swingCoeff_eq hF, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_two]
  ring

section TaylorBounds

variable {F : ℝ → ℝ} {δ0 F' C h0 : ℝ}

/-- Pointwise remainder along the swing. -/
private theorem swing_remainder (hC : 0 ≤ C)
    (hT : ∀ h, |h| ≤ h0 → |F (δ0 + h) - F δ0 - F' * h| ≤ C * h ^ 2) {dh : ℝ} (hdh : |dh| ≤ h0)
    (φ : ℝ) : |F (δ0 + dh * Real.cos φ) - F δ0 - F' * (dh * Real.cos φ)| ≤ C * dh ^ 2 := by
  have hcos := Real.abs_cos_le_one φ
  have h1 : |dh * Real.cos φ| ≤ h0 := by
    rw [abs_mul]; nlinarith [abs_nonneg dh, abs_nonneg (Real.cos φ)]
  refine (hT _ h1).trans (mul_le_mul_of_nonneg_left ?_ hC)
  rw [mul_pow]
  have : Real.cos φ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (Real.cos φ)]
  nlinarith [sq_nonneg dh]

/-- **Mean, small swing**: `|V̄ − F(δ₀)| ≤ C δ̂²`. -/
@[powerlib_foundation] theorem swingMean_sub_le (hF : Continuous F) (hC : 0 ≤ C)
    (hT : ∀ h, |h| ≤ h0 → |F (δ0 + h) - F δ0 - F' * h| ≤ C * h ^ 2) {dh : ℝ} (hdh : |dh| ≤ h0) :
    |swingMean F δ0 dh - F δ0| ≤ C * dh ^ 2 := by
  have hc : Continuous fun φ : ℝ => F (δ0 + dh * Real.cos φ) := by fun_prop
  have hrem : ∫ φ in (0 : ℝ)..2 * Real.pi,
      (F (δ0 + dh * Real.cos φ) - F δ0 - F' * (dh * Real.cos φ)) =
      (∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ)) - 2 * Real.pi * F δ0 := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub, intervalIntegral.integral_const]
    · have : ∫ φ in (0 : ℝ)..2 * Real.pi, F' * (dh * Real.cos φ) = 0 := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_cos,
          Real.sin_two_pi, Real.sin_zero]
        ring
      rw [this, smul_eq_mul]
      ring
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (f := fun φ => F (δ0 + dh * Real.cos φ) - F δ0 - F' * (dh * Real.cos φ)) (C := C * dh ^ 2)
    (fun φ _ => by rw [Real.norm_eq_abs]; exact swing_remainder hC hT hdh φ)
  rw [hrem, Real.norm_eq_abs, sub_zero, abs_of_pos Real.two_pi_pos] at hb
  have hπ : 0 < 2 * Real.pi := Real.two_pi_pos
  have heq : swingMean F δ0 dh - F δ0 = (2 * Real.pi)⁻¹ *
      ((∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ)) - 2 * Real.pi * F δ0) := by
    unfold swingMean; field_simp
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hπ)]
  calc (2 * Real.pi)⁻¹ * |(∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ)) -
        2 * Real.pi * F δ0| ≤ (2 * Real.pi)⁻¹ * (C * dh ^ 2 * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hb (inv_pos.mpr hπ).le
    _ = C * dh ^ 2 := by field_simp

/-- **Harmonics, small swing**: `|a_n − F'(δ₀) δ̂ [n = 1]| ≤ 2 C δ̂²` for `n ≥ 1`. -/
@[powerlib_foundation] theorem cosCoeff_sub_le (hF : Continuous F) (hC : 0 ≤ C)
    (hT : ∀ h, |h| ≤ h0 → |F (δ0 + h) - F δ0 - F' * h| ≤ C * h ^ 2) {dh : ℝ} (hdh : |dh| ≤ h0)
    {n : ℕ} (hn : n ≠ 0) :
    |cosCoeff F δ0 dh n - (if n = 1 then F' * dh else 0)| ≤ 2 * C * dh ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hrem : ∫ φ in (0 : ℝ)..2 * Real.pi,
      (F (δ0 + dh * Real.cos φ) - F δ0 - F' * (dh * Real.cos φ)) * Real.cos (n * φ) =
      (∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ) * Real.cos (n * φ)) -
        Real.pi * (if n = 1 then F' * dh else 0) := by
    have e : ∀ φ : ℝ, (F (δ0 + dh * Real.cos φ) - F δ0 - F' * (dh * Real.cos φ)) *
        Real.cos (n * φ) = F (δ0 + dh * Real.cos φ) * Real.cos (n * φ) -
          F δ0 * Real.cos (n * φ) - (F' * dh) * (Real.cos φ * Real.cos (n * φ)) := by
      intro φ; ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_nat_mul hn, integral_cos_mul_cos_nat]
    · split_ifs <;> ring
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (f := fun φ => (F (δ0 + dh * Real.cos φ) - F δ0 - F' * (dh * Real.cos φ)) * Real.cos (n * φ))
    (C := C * dh ^ 2) (fun φ _ => by
      rw [Real.norm_eq_abs, abs_mul]
      have := swing_remainder hC hT hdh φ
      have hc := Real.abs_cos_le_one (n * φ)
      nlinarith [abs_nonneg (F (δ0 + dh * Real.cos φ) - F δ0 - F' * (dh * Real.cos φ)),
        abs_nonneg (Real.cos (n * φ))])
  rw [hrem, Real.norm_eq_abs, sub_zero, abs_of_pos Real.two_pi_pos] at hb
  have heq : cosCoeff F δ0 dh n - (if n = 1 then F' * dh else 0) = Real.pi⁻¹ *
      ((∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ) * Real.cos (n * φ)) -
        Real.pi * (if n = 1 then F' * dh else 0)) := by
    unfold cosCoeff; field_simp
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hπ)]
  calc Real.pi⁻¹ * |(∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ) * Real.cos (n * φ)) -
        Real.pi * (if n = 1 then F' * dh else 0)| ≤ Real.pi⁻¹ * (C * dh ^ 2 * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hb (inv_pos.mpr hπ).le
    _ = 2 * C * dh ^ 2 := by field_simp

end TaylorBounds

section SmallSwing

variable {F : ℝ → ℝ} {δ0 F' C h0 : ℝ}

/-- **`ε_V = κ δ̂ + O(δ̂²)` with an explicit constant.** Under the Taylor bound
`|F(δ₀ + h) − F(δ₀) − F' h| ≤ C h²` (`|h| ≤ h₀`), `F(δ₀) > 0`, for `0 ≤ δ̂ ≤ h₀` with
`C δ̂² ≤ F(δ₀)/2`: `|ε₁(δ̂) − (|F'|/F(δ₀)) δ̂| ≤ (4C/F(δ₀) + 2|F'| C h₀/F(δ₀)²) δ̂²`. -/
@[powerlib_foundation] theorem harmonicRatio_one_sub_le (hF : Continuous F) (hC : 0 ≤ C)
    (hpos : 0 < F δ0) (hT : ∀ h, |h| ≤ h0 → |F (δ0 + h) - F δ0 - F' * h| ≤ C * h ^ 2)
    {dh : ℝ} (hdh0 : 0 ≤ dh) (hdh : dh ≤ h0) (hsmall : C * dh ^ 2 ≤ F δ0 / 2) :
    |harmonicRatio F δ0 dh 1 - |F'| / F δ0 * dh| ≤
      (4 * C / F δ0 + 2 * |F'| * C * h0 / F δ0 ^ 2) * dh ^ 2 := by
  have habs : |dh| ≤ h0 := by rwa [abs_of_nonneg hdh0]
  have hm := swingMean_sub_le hF hC hT habs
  have ha := cosCoeff_sub_le hF hC hT habs (n := 1) one_ne_zero
  simp only [ite_true] at ha
  rw [harmonicRatio_eq hF, show |F'| / F δ0 * dh = (|F'| * dh) / F δ0 by ring]
  set m := swingMean F δ0 dh
  set a := cosCoeff F δ0 dh 1
  set F0 := F δ0
  have hm0 : F0 / 2 ≤ m := by
    have := (abs_le.mp hm).1; linarith
  have hmpos : 0 < m := by linarith
  have hh0 : 0 ≤ h0 := hdh0.trans hdh
  rw [div_sub_div _ _ hmpos.ne' hpos.ne', abs_div,
    abs_of_pos (mul_pos hmpos hpos)]
  have hnum : |(|a|) * F0 - m * (|F'| * dh)| ≤ 2 * C * F0 * dh ^ 2 + |F'| * C * h0 * dh ^ 2 := by
    have e : (|a|) * F0 - m * (|F'| * dh) = (|a| - |F'| * dh) * F0 + |F'| * dh * (F0 - m) := by
      ring
    rw [e]
    have h1 : |(|a|) - |F'| * dh| ≤ 2 * C * dh ^ 2 := by
      have := abs_abs_sub_abs_le_abs_sub a (F' * dh)
      rw [abs_mul, abs_of_nonneg hdh0] at this
      linarith
    have h2 : |F0 - m| ≤ C * dh ^ 2 := by rw [abs_sub_comm]; exact hm
    calc |(|a| - |F'| * dh) * F0 + |F'| * dh * (F0 - m)| ≤
          |(|a| - |F'| * dh) * F0| + |(|F'|) * dh * (F0 - m)| := abs_add_le _ _
      _ = |(|a|) - |F'| * dh| * F0 + |F'| * dh * |F0 - m| := by
          rw [abs_mul, abs_mul, abs_mul, abs_abs, abs_of_pos hpos, abs_of_nonneg hdh0]
      _ ≤ 2 * C * dh ^ 2 * F0 + |F'| * dh * (C * dh ^ 2) := by
          gcongr
      _ ≤ 2 * C * F0 * dh ^ 2 + |F'| * C * h0 * dh ^ 2 := by
          have : |F'| * dh * (C * dh ^ 2) ≤ |F'| * h0 * (C * dh ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdh (abs_nonneg _))
              (mul_nonneg hC (sq_nonneg _))
          nlinarith
  rw [div_le_iff₀ (mul_pos hmpos hpos)]
  calc |(|a|) * F0 - m * (|F'| * dh)| ≤ 2 * C * F0 * dh ^ 2 + |F'| * C * h0 * dh ^ 2 := hnum
    _ = (4 * C / F0 + 2 * |F'| * C * h0 / F0 ^ 2) * dh ^ 2 * (F0 / 2 * F0) := by
        field_simp; ring
    _ ≤ (4 * C / F0 + 2 * |F'| * C * h0 / F0 ^ 2) * dh ^ 2 * (m * F0) := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm0 hpos.le)
        apply mul_nonneg _ (sq_nonneg _)
        positivity

/-- **Higher harmonics are second order**: for `n ≥ 2`, `ε_n(δ̂) ≤ (4C/F(δ₀)) δ̂²` under the same
hypotheses (any sign of `δ̂`, `|δ̂| ≤ h₀`). -/
@[powerlib_foundation] theorem harmonicRatio_le (hF : Continuous F) (hC : 0 ≤ C)
    (hpos : 0 < F δ0) (hT : ∀ h, |h| ≤ h0 → |F (δ0 + h) - F δ0 - F' * h| ≤ C * h ^ 2)
    {dh : ℝ} (hdh : |dh| ≤ h0) (hsmall : C * dh ^ 2 ≤ F δ0 / 2) {n : ℕ} (hn : 2 ≤ n) :
    harmonicRatio F δ0 dh n ≤ 4 * C / F δ0 * dh ^ 2 := by
  have hm := swingMean_sub_le hF hC hT hdh
  have ha := cosCoeff_sub_le hF hC hT hdh (n := n) (by omega)
  have hn1 : n ≠ 1 := by omega
  simp only [hn1, ite_false, sub_zero] at ha
  have hm0 : F δ0 / 2 ≤ swingMean F δ0 dh := by
    have := (abs_le.mp hm).1; linarith
  have hmpos : 0 < swingMean F δ0 dh := by linarith
  rw [harmonicRatio_eq hF, div_le_iff₀ hmpos]
  calc |cosCoeff F δ0 dh n| ≤ 2 * C * dh ^ 2 := ha
    _ = 4 * C / F δ0 * dh ^ 2 * (F δ0 / 2) := by field_simp; ring
    _ ≤ 4 * C / F δ0 * dh ^ 2 * swingMean F δ0 dh := by
        apply mul_le_mul_of_nonneg_left hm0
        apply mul_nonneg _ (sq_nonneg _)
        positivity

/-- A `C²` amplitude map satisfies the Taylor bound near `δ₀` with `F' = F'(δ₀)`. -/
@[powerlib_foundation] theorem exists_taylor_bound (hF : ContDiffAt ℝ 2 F δ0) :
    ∃ C h0 : ℝ, 0 ≤ C ∧ 0 < h0 ∧
      ∀ h, |h| ≤ h0 → |F (δ0 + h) - F δ0 - deriv F δ0 * h| ≤ C * h ^ 2 := by
  obtain ⟨K, t, ht, hlip⟩ := (hF.derivWithin (m := 1) (by norm_num)).exists_lipschitzOnWith
  have hev : ∀ᶠ y in 𝓝 δ0, DifferentiableAt ℝ F y :=
    (hF.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hev)
  refine ⟨K, r / 2, K.2, half_pos hr, fun h hh => ?_⟩
  set g : ℝ → ℝ := fun s => F (δ0 + s) - F δ0 - deriv F δ0 * s
  have hin : ∀ s ∈ Metric.closedBall (0 : ℝ) |h|, δ0 + s ∈ Metric.ball δ0 r := by
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hs
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
    linarith
  have hderiv : ∀ s ∈ Metric.closedBall (0 : ℝ) |h|,
      HasDerivWithinAt g (deriv F (δ0 + s) - deriv F δ0) (Metric.closedBall 0 |h|) s := by
    intro s hs
    have hd := (hball (hin s hs)).2
    have h1 : HasDerivAt (fun s => F (δ0 + s)) (deriv F (δ0 + s)) s :=
      hd.hasDerivAt.comp_const_add δ0 s
    exact (((h1.sub_const (F δ0)).sub ((hasDerivAt_id s).const_mul (deriv F δ0))).congr_deriv
      (by ring)).hasDerivWithinAt
  have hbound : ∀ s ∈ Metric.closedBall (0 : ℝ) |h|,
      ‖deriv F (δ0 + s) - deriv F δ0‖ ≤ K * |h| := by
    intro s hs
    have h1 := hlip.dist_le_mul (δ0 + s) (hball (hin s hs)).1 δ0
      (hball (Metric.mem_ball_self hr)).1
    rw [dist_eq_norm, Real.dist_eq, add_sub_cancel_left] at h1
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hs
    calc ‖deriv F (δ0 + s) - deriv F δ0‖ ≤ K * |s| := h1
      _ ≤ K * |h| := mul_le_mul_of_nonneg_left hs K.2
  have := (convex_closedBall (0 : ℝ) |h|).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    hbound (Metric.mem_closedBall_self (abs_nonneg h))
    (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs])
  simp only [g, add_zero, sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at this
  calc |F (δ0 + h) - F δ0 - deriv F δ0 * h| ≤ K * |h| * |h| := this
    _ = K * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

end SmallSwing

section Asymptotic

variable {F : ℝ → ℝ} {δ0 : ℝ}

/-- **`ε_V = κ δ̂ + O(δ̂²)`** (Fourier-coefficient level) for a `C²` amplitude map with
`F(δ₀) > 0`: `ε₁(δ̂) − (|F'(δ₀)|/F(δ₀)) δ̂ = O(δ̂²)` as `δ̂ → 0⁺`. -/
@[powerlib_foundation] theorem harmonicRatio_one_isBigO (hF : Continuous F)
    (hF2 : ContDiffAt ℝ 2 F δ0) (hpos : 0 < F δ0) :
    (fun dh => harmonicRatio F δ0 dh 1 - |deriv F δ0| / F δ0 * dh) =O[𝓝[≥] 0]
      (fun dh => dh ^ 2) := by
  obtain ⟨C, h0, hC, hh0, hT⟩ := exists_taylor_bound hF2
  refine IsBigO.of_bound (4 * C / F δ0 + 2 * |deriv F δ0| * C * h0 / F δ0 ^ 2) ?_
  have h1 : ∀ᶠ dh in 𝓝[≥] (0 : ℝ), dh ≤ h0 :=
    nhdsWithin_le_nhds (Iic_mem_nhds hh0)
  have h2 : ∀ᶠ dh in 𝓝[≥] (0 : ℝ), C * dh ^ 2 < F δ0 / 2 := by
    apply nhdsWithin_le_nhds
    have hc : Continuous fun dh : ℝ => C * dh ^ 2 := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using half_pos hpos)
  filter_upwards [self_mem_nhdsWithin, h1, h2] with dh (hd0 : 0 ≤ dh) hd1 hd2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg dh)]
  exact harmonicRatio_one_sub_le hF hC hpos hT hd0 hd1 hd2.le

/-- **Higher harmonics, small swing**: `ε_n(δ̂) = O(δ̂²)` as `δ̂ → 0` for every `n ≥ 2`. -/
@[powerlib_foundation] theorem harmonicRatio_isBigO (hF : Continuous F) (hF2 : ContDiffAt ℝ 2 F δ0)
    (hpos : 0 < F δ0) {n : ℕ} (hn : 2 ≤ n) :
    (fun dh => harmonicRatio F δ0 dh n) =O[𝓝 0] (fun dh => dh ^ 2) := by
  obtain ⟨C, h0, hC, hh0, hT⟩ := exists_taylor_bound hF2
  refine IsBigO.of_bound (4 * C / F δ0) ?_
  have h1 : ∀ᶠ dh in 𝓝 (0 : ℝ), |dh| ≤ h0 := by
    have : Metric.closedBall (0 : ℝ) h0 ∈ 𝓝 (0 : ℝ) := Metric.closedBall_mem_nhds 0 hh0
    filter_upwards [this] with dh hd
    rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hd
  have h2 : ∀ᶠ dh in 𝓝 (0 : ℝ), C * dh ^ 2 < F δ0 / 2 := by
    have hc : Continuous fun dh : ℝ => C * dh ^ 2 := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using half_pos hpos)
  filter_upwards [h1, h2] with dh hd1 hd2
  have hm := swingMean_sub_le hF hC hT hd1
  have hmpos : 0 < swingMean F δ0 dh := by have := (abs_le.mp hm).1; linarith
  have hnn : 0 ≤ harmonicRatio F δ0 dh n := by
    rw [harmonicRatio_eq hF]; exact div_nonneg (abs_nonneg _) hmpos.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg (sq_nonneg dh)]
  exact harmonicRatio_le hF hC hpos hT hd1 hd2.le hn

end Asymptotic

/-! ### Finite swing -/

/-- **Finite swing, every amplitude**: for a nonnegative amplitude map with positive mean,
`0 ≤ ε_n ≤ 2` (`|V_n| ≤ V̄`). -/
@[powerlib_foundation] theorem harmonicRatio_le_two {F : ℝ → ℝ} (hF : Continuous F)
    (hnn : ∀ x, 0 ≤ F x) {δ0 dh : ℝ} (hm : 0 < swingMean F δ0 dh) (n : ℕ) :
    0 ≤ harmonicRatio F δ0 dh n ∧ harmonicRatio F δ0 dh n ≤ 2 := by
  rw [harmonicRatio_eq hF]
  refine ⟨div_nonneg (abs_nonneg _) hm.le, ?_⟩
  rw [div_le_iff₀ hm]
  have hπ : 0 < Real.pi := Real.pi_pos
  have hab : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h1 := intervalIntegral.abs_integral_le_integral_abs (a := 0) (b := 2 * Real.pi)
    (f := fun φ => F (δ0 + dh * Real.cos φ) * Real.cos (n * φ)) (μ := MeasureTheory.volume) hab
  have h2 : ∫ φ in (0 : ℝ)..2 * Real.pi, |F (δ0 + dh * Real.cos φ) * Real.cos (n * φ)| ≤
      ∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ) := by
    refine intervalIntegral.integral_mono_on hab (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun φ _ => ?_
    rw [abs_mul, abs_of_nonneg (hnn _)]
    exact mul_le_of_le_one_right (hnn _) (Real.abs_cos_le_one _)
  unfold cosCoeff swingMean
  rw [abs_mul, abs_of_pos (inv_pos.mpr hπ)]
  have : Real.pi⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ) =
      2 * ((2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi, F (δ0 + dh * Real.cos φ)) := by
    field_simp
  rw [← this]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (inv_pos.mpr hπ).le

/-- **Finite swing at a symmetric operating point**: if `F(δ₀ + h) = F(δ₀ − h)` (e.g. the
Thévenin amplitude at `δ₀ = 0`), every odd harmonic vanishes for every amplitude `δ̂`:
`V_{2k+1} = 0`, hence `ε_{2k+1} = 0`. -/
@[powerlib_foundation] theorem cosCoeff_odd_eq_zero {F : ℝ → ℝ} (hF : Continuous F) {δ0 : ℝ}
    (hsym : ∀ h, F (δ0 + h) = F (δ0 - h)) (dh : ℝ) (k : ℕ) :
    cosCoeff F δ0 dh (2 * k + 1) = 0 := by
  set g : ℝ → ℝ := fun φ => F (δ0 + dh * Real.cos φ) * Real.cos (((2 * k + 1 : ℕ) : ℝ) * φ)
  have hg : Continuous g := by fun_prop
  have hshift : ∀ φ, g (φ + Real.pi) = -g φ := by
    intro φ
    simp only [g]
    have hc : Real.cos (φ + Real.pi) = -Real.cos φ := Real.cos_add_pi φ
    have hn : Real.cos (((2 * k + 1 : ℕ) : ℝ) * (φ + Real.pi)) =
        -Real.cos (((2 * k + 1 : ℕ) : ℝ) * φ) := by
      rw [mul_add, Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
      rw [(Nat.odd_iff.mpr (by omega) : Odd (2 * k + 1)).neg_one_pow]
      ring
    rw [hc, hn, mul_neg, show δ0 + dh * -Real.cos φ = δ0 - dh * Real.cos φ by ring,
      ← hsym (dh * Real.cos φ)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := Real.pi)
    (c := 2 * Real.pi) (μ := MeasureTheory.volume) (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)
  have hsecond : ∫ φ in Real.pi..2 * Real.pi, g φ = -∫ φ in (0 : ℝ)..Real.pi, g φ := by
    have := intervalIntegral.integral_comp_add_right g (a := 0) (b := Real.pi) Real.pi
    rw [zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring] at this
    rw [← this]
    simp_rw [hshift, intervalIntegral.integral_neg]
  unfold cosCoeff
  have : ∫ φ in (0 : ℝ)..2 * Real.pi, g φ = 0 := by rw [← hsplit, hsecond]; ring
  simp only [g] at this
  rw [this, mul_zero]

/-- Odd harmonic ratios vanish at a symmetric operating point, for every amplitude. -/
@[powerlib_foundation] theorem harmonicRatio_odd_eq_zero {F : ℝ → ℝ} (hF : Continuous F) {δ0 : ℝ}
    (hsym : ∀ h, F (δ0 + h) = F (δ0 - h)) (dh : ℝ) (k : ℕ) :
    harmonicRatio F δ0 dh (2 * k + 1) = 0 := by
  rw [harmonicRatio_eq hF, cosCoeff_odd_eq_zero hF hsym, abs_zero, zero_div]

/-! ### The Thévenin amplitude map -/

@[powerlib_foundation] theorem continuous_norm_vth (X2 X3 E Vinf : ℝ) :
    Continuous fun δ => ‖vth X2 X3 E Vinf δ‖ := by
  unfold vth; fun_prop

@[powerlib_foundation] theorem contDiffAt_norm_vth {X2 X3 E Vinf δ0 : ℝ}
    (hV : ‖vth X2 X3 E Vinf δ0‖ ≠ 0) :
    ContDiffAt ℝ 2 (fun δ => ‖vth X2 X3 E Vinf δ‖) δ0 := by
  have hfun : (fun δ => ‖vth X2 X3 E Vinf δ‖) = fun δ => Real.sqrt (aV X2 X3 E ^ 2 +
      bV X2 X3 Vinf ^ 2 + 2 * aV X2 X3 E * bV X2 X3 Vinf * Real.cos δ) :=
    funext fun δ => norm_vth X2 X3 E Vinf δ
  rw [hfun]
  refine ContDiffAt.sqrt (by fun_prop) fun h => hV ?_
  rw [norm_vth, h, Real.sqrt_zero]

/-- **`ε_V = κ_δ δ̂ + O(δ̂²)`** for the open-circuit Thévenin map (note, "小摆幅与有限摆幅"):
with `V₀ = |V_th(δ₀)| > 0` and `a_V, b_V ≥ 0`, the fundamental modulation ratio
`ε_V = 2|V₁|/V̄` of the amplitude under `δ = δ₀ + δ̂ cos(ω_p t)` satisfies
`ε_V − κ_δ δ̂ = O(δ̂²)` as `δ̂ → 0⁺`, `κ_δ = a_V b_V |sin δ₀| / V₀²` — at the level of the actual
Fourier coefficients `V̄`, `V₁`, not only of the derivative `dV/dδ`. -/
@[powerlib_foundation] theorem epsV_isBigO {X2 X3 E Vinf δ0 : ℝ}
    (hV : ‖vth X2 X3 E Vinf δ0‖ ≠ 0) (ha : 0 ≤ aV X2 X3 E) (hb : 0 ≤ bV X2 X3 Vinf) :
    (fun dh => harmonicRatio (fun δ => ‖vth X2 X3 E Vinf δ‖) δ0 dh 1 -
      aV X2 X3 E * bV X2 X3 Vinf * |Real.sin δ0| / ‖vth X2 X3 E Vinf δ0‖ ^ 2 * dh)
      =O[𝓝[≥] 0] (fun dh => dh ^ 2) := by
  have hpos : 0 < ‖vth X2 X3 E Vinf δ0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hV)
  have h := harmonicRatio_one_isBigO (continuous_norm_vth X2 X3 E Vinf) (contDiffAt_norm_vth hV)
    hpos
  have hd := (hasDerivAt_norm_vth X2 X3 E Vinf δ0 hV).deriv
  have hk : |deriv (fun δ => ‖vth X2 X3 E Vinf δ‖) δ0| / ‖vth X2 X3 E Vinf δ0‖ =
      aV X2 X3 E * bV X2 X3 Vinf * |Real.sin δ0| / ‖vth X2 X3 E Vinf δ0‖ ^ 2 := by
    rw [hd, ← kappa_eq ha hb hpos]
    ring
  rwa [hk] at h

/-- Higher harmonics of the Thévenin amplitude are second order: `ε_n = O(δ̂²)`, `n ≥ 2`. -/
@[powerlib_foundation] theorem epsN_isBigO {X2 X3 E Vinf δ0 : ℝ}
    (hV : ‖vth X2 X3 E Vinf δ0‖ ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    (fun dh => harmonicRatio (fun δ => ‖vth X2 X3 E Vinf δ‖) δ0 dh n) =O[𝓝 0]
      (fun dh => dh ^ 2) :=
  harmonicRatio_isBigO (continuous_norm_vth X2 X3 E Vinf) (contDiffAt_norm_vth hV)
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hV)) hn

/-- Finite swing about `δ₀ = 0`: every odd harmonic of the Thévenin amplitude vanishes, for every
amplitude `δ̂` (the fundamental channel is closed; only even harmonics remain). -/
@[powerlib_foundation] theorem epsN_odd_eq_zero_at_zero (X2 X3 E Vinf dh : ℝ) (k : ℕ) :
    harmonicRatio (fun δ => ‖vth X2 X3 E Vinf δ‖) 0 dh (2 * k + 1) = 0 :=
  harmonicRatio_odd_eq_zero (continuous_norm_vth X2 X3 E Vinf)
    (fun h => by rw [norm_vth, norm_vth, zero_add, zero_sub, Real.cos_neg]) dh k

/-- Finite swing, every amplitude: `0 ≤ ε_n ≤ 2` for the Thévenin amplitude whenever its mean is
positive. -/
@[powerlib_foundation] theorem epsN_le_two {X2 X3 E Vinf δ0 dh : ℝ}
    (hm : 0 < swingMean (fun δ => ‖vth X2 X3 E Vinf δ‖) δ0 dh) (n : ℕ) :
    0 ≤ harmonicRatio (fun δ => ‖vth X2 X3 E Vinf δ‖) δ0 dh n ∧
      harmonicRatio (fun δ => ‖vth X2 X3 E Vinf δ‖) δ0 dh n ≤ 2 :=
  harmonicRatio_le_two (continuous_norm_vth X2 X3 E Vinf) (fun _ => norm_nonneg _) hm n

end Fourier

/-! ## Equal branches: common and differential modes -/

/-- `x I + X_eq 𝟙𝟙ᵀ` (equal GFL branch reactances `x`). -/
def modeMatrix (N : ℕ) (x Xe : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  x • (1 : Matrix (Fin N) (Fin N) ℝ) + Xe • Matrix.of (fun _ _ => (1 : ℝ))

@[powerlib_foundation] theorem commonMode (N : ℕ) (x Xe : ℝ) :
    modeMatrix N x Xe *ᵥ (fun _ => 1) = (x + N * Xe) • (fun _ => (1 : ℝ)) := by
  rw [modeMatrix, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
  funext i
  simp [mulVec, dotProduct]
  ring

@[powerlib_foundation] theorem diffMode (N : ℕ) (x Xe : ℝ) (v : Fin N → ℝ) (hv : ∑ k, v k = 0) :
    modeMatrix N x Xe *ᵥ v = x • v := by
  rw [modeMatrix, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
  funext i
  simp [mulVec, dotProduct, hv]

@[powerlib_foundation] private lemma det_scalar_sub_ones (N : ℕ) (c w : ℝ) :
    (c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) - w • Matrix.of (fun _ _ => (1 : ℝ))).det =
      c ^ N * (c - (N + 1) * w) := by
  by_cases hc : c = 0
  · subst hc
    rcases N with _ | N
    · simp [Matrix.det_unique]
    · simp only [zero_smul, zero_sub, zero_pow (Nat.succ_ne_zero N), zero_mul]
      apply Matrix.det_zero_of_row_eq (i := 0) (j := 1) (by simp)
      funext k; simp
  · have hrank : Matrix.of (fun _ _ => (1 : ℝ)) =
        replicateCol (Fin 1) (fun _ : Fin (N + 1) => (1 : ℝ)) *
          replicateRow (Fin 1) (fun _ : Fin (N + 1) => (1 : ℝ)) := by
      ext i j; simp [replicateCol, replicateRow, Matrix.mul_apply]
    have hfac : c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) - w • Matrix.of (fun _ _ => (1 : ℝ)) =
        c • (1 + replicateCol (Fin 1) (fun _ : Fin (N + 1) => (-(w / c))) *
          replicateRow (Fin 1) (fun _ : Fin (N + 1) => (1 : ℝ))) := by
      rw [hrank]
      ext i j
      simp [replicateCol, replicateRow, Matrix.mul_apply, Matrix.one_apply]
      split_ifs <;> field_simp <;> ring
    rw [hfac, Matrix.det_smul, Matrix.det_one_add_mul_comm, Matrix.det_unique]
    simp [Matrix.mul_apply, replicateCol, replicateRow]
    field_simp
    ring

/-- `det(sI − (xI + X_eq 𝟙𝟙ᵀ)) = (s − x)^{N−1}(s − x − N X_eq)` (`N ≥ 1` branches): the
differential eigenvalue `x` has algebraic multiplicity `N − 1`. -/
@[powerlib_foundation] theorem det_modes (N : ℕ) (x Xe s : ℝ) :
    (s • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) - modeMatrix (N + 1) x Xe).det =
      (s - x) ^ N * (s - x - (N + 1) * Xe) := by
  have : s • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) - modeMatrix (N + 1) x Xe =
      (s - x) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) - Xe • Matrix.of (fun _ _ => (1 : ℝ)) := by
    simp only [modeMatrix, sub_smul]; abel
  rw [this, det_scalar_sub_ones]

end powerlib.Network.ModulationTransfer
