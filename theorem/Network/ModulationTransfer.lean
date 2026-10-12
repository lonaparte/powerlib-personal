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

Not formalized: the finite-swing harmonic ratios `ε_n` and the `O(δ̂²)` remainder of
`ε_V = κ_δ δ̂` at the level of Fourier coefficients (only the derivative `dV/dδ`, which is the
first-order coefficient, and the explicit `δ₀ = 0` expansion are proved); the candidate
measure `𝓜` is a screening heuristic, not a theorem.
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
