import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.Expect

/-! # The cross-spectrum index

The deterministic algebra behind the cross-spectrum index of Xie and Trudnowski: the single-bin
scaled DFT of a sampled channel over three delayed windows, the cross-spectrum difference
`S = Ȳ₁Y₂ − Ȳ₂Y₃`, which cancels every deterministic on-bin sinusoid exactly, and the index
`C = |E{S̄_r S_g}|² / (E{|S_r|²} E{|S_g|²})`, a squared coherence between two channels over data
sections: `0 ≤ C ≤ 1`, `C = 1` exactly for proportional channels, with a quantitative bound when
a perturbation is added; and the modal structure (a common "random sinusoid" times a channel
residue) that makes the channels of an undamped natural mode proportional.

Scope.
* Sampled complex signals `y : ℤ → ℂ` (real channels are coerced), a window length `N ≥ 1`, a bin
  frequency `Ω` (rad/sample), window starts `k₀`, `k₀ + Δk`, `k₀ + 2Δk`; data sections are
  indexed by `Fin K`, and the expectation of (3-22) is the empirical mean over sections
  (`Finset.expect`).
* On-bin sinusoids: `ΩN ∈ 2πℤ` (the bin is exactly a DFT bin) and `2Ω ∉ 2πℤ` (the image bin
  `−Ω` is a different bin).
* Not formalized: the statistical claims of the source that `C ≅ 1` in expectation under a
  natural oscillation and `C < 1` under a forced one for specific noise models (the "extensive
  algebra" of Xie–Trudnowski), Kaiser windowing, off-bin leakage, bin selection and the
  independence of windows. What is proved are the exact algebraic facts these claims rest on:
  exact cancellation of the deterministic part, `C = 1` for rank-one channels, the explicit cross
  terms of a constant added to the DFTs, and the perturbation bound.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.5, eqs. (3-14)–(3-22)
(scaled single-bin DFT (3-20), cross-spectrum difference function (3-21), cross-spectrum index
(3-22), the "random sinusoid" term "Noise 1" of (3-18)); R. Xie and D. J. Trudnowski,
"Distinguishing between natural and forced oscillations using a cross-spectrum index", IEEE PES
GM 2017.

Results.
* `dft`, `dft_add`, `dft_const_mul`, `dft_onBin` — the scaled single-bin DFT (3-20) is linear,
  and an on-bin sinusoid `Re(a e^{jΩk})` has `Y = a/2` on every window (geometric sum of the image
  term).
* `crossDiff`, `crossDiff_const`, `crossDiff_add_const`, `crossDiff_mul` — `S(c, c, c) = 0`;
  adding a window-independent `c` gives `S(n) + c̄(n₂ − n₃) + c(n̄₁ − n̄₂)`; scaling the DFTs by
  `κ` scales `S` by `|κ|²`.
* `crossSpectrumDiff`, `crossSpectrumDiff_onBin`, `crossSpectrumDiff_onBin_add`,
  `crossSpectrumDiff_rankOne` — (3-21) vanishes for every deterministic on-bin sinusoid; for an
  on-bin sinusoid plus a signal `e` it is `S(e)` plus the explicit cross terms with `c = a/2`;
  `Y_g = κ Y_r` on all windows gives `S_g = |κ|² S_r`.
* `index`, `index_nonneg`, `index_le_one`, `index_eq_one_iff`, `index_smul`, `index_rankOne`,
  `one_sub_index_le` — (3-22) lies in `[0, 1]` (Cauchy–Schwarz, `norm_inner_le_norm`), equals `1`
  exactly when `(S_g,s)` is a nonzero multiple of `(S_r,s)` (`norm_inner_eq_norm_iff`), so for
  rank-one channels; and `1 − C(x, κx + e) ≤ ‖e‖² / ‖κx + e‖²`.
* `modal_conv`, `dft_twiceRe`, `residue`, `residue_eq_mul`, `dft_rankOne_of_modal` — the modal
  convolution `Σ_m 2 Re(β z^{k−m}) q[m]` of one mode with real noise is `2 Re(β s[k])` with the
  common random sinusoid `s[k] = Σ_m z^{k−m} q[m]`; the channel residue `β_r = (c_r u)(v b)` has
  only the factor `c_r u` depending on the channel; the DFT of `2 Re(β s)` is
  `β Y(s) + β̄ Y(s̄)`, so when the image term `Y(s̄)` vanishes the channels are rank one,
  `Y_g = (β_g/β_r) Y_r` — the algebraic reason for `C ≈ 1` in the natural case.
-/

noncomputable section
namespace powerlib.Signal.CrossSpectrum
open Complex Finset

/-! ## The scaled single-bin DFT -/

/-- The scaled single-bin DFT (3-20) over the window `k₀, …, k₀ + N − 1`:
`Y(y, k₀) = (1/N) Σ_{k<N} y[k₀ + k] e^{−jΩ(k₀+k)}`. -/
def dft (N : ℕ) (Ω : ℝ) (y : ℤ → ℂ) (k₀ : ℤ) : ℂ :=
  (1 / N : ℂ) * ∑ k ∈ range N, y (k₀ + k) * cexp (-(Ω * ((k₀ + k : ℤ) : ℂ) * I))

@[tmio T, powerlib_foundation] theorem dft_add (N : ℕ) (Ω : ℝ) (y₁ y₂ : ℤ → ℂ) (k₀ : ℤ) :
    dft N Ω (fun k => y₁ k + y₂ k) k₀ = dft N Ω y₁ k₀ + dft N Ω y₂ k₀ := by
  simp only [dft, add_mul, sum_add_distrib, mul_add]

@[tmio T, powerlib_foundation] theorem dft_const_mul (N : ℕ) (Ω : ℝ) (c : ℂ) (y : ℤ → ℂ)
    (k₀ : ℤ) : dft N Ω (fun k => c * y k) k₀ = c * dft N Ω y k₀ := by
  simp only [dft, mul_assoc, ← mul_sum]
  ring

@[tmio T, powerlib_foundation] private theorem re_mul_exp (a : ℂ) (θ : ℝ) :
    (((a * cexp (θ * I)).re : ℝ) : ℂ) * cexp (-(θ * I)) =
      a / 2 + (starRingEnd ℂ) a / 2 * cexp (-(2 * θ * I)) := by
  rw [Complex.re_eq_add_conj, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  have h1 : cexp (θ * I) * cexp (-(θ * I)) = 1 := by rw [← Complex.exp_add]; simp
  have h2 : cexp (θ * -I) * cexp (-(θ * I)) = cexp (-(2 * θ * I)) := by
    rw [← Complex.exp_add]; congr 1; ring
  linear_combination (a / 2) * h1 + ((starRingEnd ℂ) a / 2) * h2

/-- An on-bin sinusoid `y[k] = Re(a e^{jΩk})` (`ΩN ∈ 2πℤ`, `2Ω ∉ 2πℤ`) has the same scaled DFT
`Y = a/2` on every window. -/
@[tmio T, powerlib_foundation] theorem dft_onBin {N : ℕ} (hN : N ≠ 0) {Ω : ℝ}
    (hbin : ∃ ℓ : ℤ, Ω * N = 2 * Real.pi * ℓ) (h2 : ∀ ℓ : ℤ, 2 * Ω ≠ 2 * Real.pi * ℓ) (a : ℂ)
    (k₀ : ℤ) : dft N Ω (fun k => (((a * cexp (Ω * (k : ℂ) * I)).re : ℝ) : ℂ)) k₀ = a / 2 := by
  obtain ⟨ℓ, hℓ⟩ := hbin
  set w : ℂ := cexp (-(2 * Ω * I))
  have hw1 : w ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
    apply h2 (-m)
    have him := congrArg Complex.im hm
    simp at him
    push_cast
    linarith
  have hℓc : (Ω : ℂ) * N = 2 * Real.pi * ℓ := by exact_mod_cast hℓ
  have hwN : w ^ N = 1 := by
    rw [← Complex.exp_nat_mul, show (N : ℂ) * -(2 * Ω * I) = ((-2 * ℓ : ℤ) : ℂ) * (2 * Real.pi * I)
      by push_cast; linear_combination (-2 * I) * hℓc]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hgeom : ∑ k ∈ range N, w ^ k = 0 := by
    rw [geom_sum_eq hw1, hwN, sub_self, zero_div]
  have hterm : ∀ k : ℕ, (((a * cexp (Ω * ((k₀ + k : ℤ) : ℂ) * I)).re : ℝ) : ℂ) *
      cexp (-(Ω * ((k₀ + k : ℤ) : ℂ) * I)) =
      a / 2 + (starRingEnd ℂ) a / 2 * cexp (-(2 * Ω * k₀ * I)) * w ^ k := by
    intro k
    have := re_mul_exp a (Ω * ((k₀ + k : ℤ) : ℝ))
    have he : cexp (-(2 * (Ω * ((k₀ : ℂ) + k)) * I)) = cexp (-(2 * Ω * k₀ * I)) * w ^ k := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; ring
    push_cast at this ⊢
    rw [this, he]
    ring
  simp only [dft]
  rw [Finset.sum_congr rfl fun k _ => hterm k, sum_add_distrib, sum_const, card_range,
    ← mul_sum, hgeom, mul_zero, add_zero, nsmul_eq_mul]
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  field_simp

/-! ## The cross-spectrum difference function -/

/-- The cross-spectrum difference of three window DFTs: `S = Ȳ₁ Y₂ − Ȳ₂ Y₃` (3-21). -/
def crossDiff (Y₁ Y₂ Y₃ : ℂ) : ℂ := (starRingEnd ℂ) Y₁ * Y₂ - (starRingEnd ℂ) Y₂ * Y₃

/-- A window-independent DFT value cancels exactly. -/
@[tmio T, powerlib_foundation] theorem crossDiff_const (c : ℂ) : crossDiff c c c = 0 := by
  simp [crossDiff]

/-- Adding a window-independent `c` to the DFTs leaves `S` unchanged except for the cross terms
`c̄(n₂ − n₃) + c(n̄₁ − n̄₂)`. -/
@[tmio T, powerlib_foundation] theorem crossDiff_add_const (c n₁ n₂ n₃ : ℂ) :
    crossDiff (c + n₁) (c + n₂) (c + n₃) =
      crossDiff n₁ n₂ n₃ + (starRingEnd ℂ) c * (n₂ - n₃) +
        c * ((starRingEnd ℂ) n₁ - (starRingEnd ℂ) n₂) := by
  simp only [crossDiff, map_add]
  ring

/-- Scaling all three DFTs by `κ` scales `S` by `|κ|²`. -/
@[tmio T, powerlib_foundation] theorem crossDiff_mul (κ Y₁ Y₂ Y₃ : ℂ) :
    crossDiff (κ * Y₁) (κ * Y₂) (κ * Y₃) = (Complex.normSq κ : ℂ) * crossDiff Y₁ Y₂ Y₃ := by
  simp only [crossDiff, map_mul]
  rw [← Complex.mul_conj]
  ring

/-- The cross-spectrum difference function (3-21) of a channel `y` for the windows starting at
`k₀`, `k₀ + Δk`, `k₀ + 2Δk`. -/
def crossSpectrumDiff (N : ℕ) (Ω : ℝ) (y : ℤ → ℂ) (k₀ Δk : ℤ) : ℂ :=
  crossDiff (dft N Ω y k₀) (dft N Ω y (k₀ + Δk)) (dft N Ω y (k₀ + 2 * Δk))

/-- (3-21) vanishes for every deterministic on-bin sinusoid. -/
@[tmio T, powerlib_foundation] theorem crossSpectrumDiff_onBin {N : ℕ} (hN : N ≠ 0) {Ω : ℝ}
    (hbin : ∃ ℓ : ℤ, Ω * N = 2 * Real.pi * ℓ) (h2 : ∀ ℓ : ℤ, 2 * Ω ≠ 2 * Real.pi * ℓ) (a : ℂ)
    (k₀ Δk : ℤ) :
    crossSpectrumDiff N Ω (fun k => (((a * cexp (Ω * (k : ℂ) * I)).re : ℝ) : ℂ)) k₀ Δk = 0 := by
  rw [crossSpectrumDiff, dft_onBin hN hbin h2, dft_onBin hN hbin h2, dft_onBin hN hbin h2,
    crossDiff_const]

/-- An on-bin sinusoid plus a signal `e` (for instance noise): the deterministic part cancels and
only `S(e)` and the explicit cross terms with `c = a/2` remain. -/
@[tmio T, powerlib_foundation] theorem crossSpectrumDiff_onBin_add {N : ℕ} (hN : N ≠ 0) {Ω : ℝ}
    (hbin : ∃ ℓ : ℤ, Ω * N = 2 * Real.pi * ℓ) (h2 : ∀ ℓ : ℤ, 2 * Ω ≠ 2 * Real.pi * ℓ) (a : ℂ)
    (e : ℤ → ℂ) (k₀ Δk : ℤ) :
    crossSpectrumDiff N Ω (fun k => (((a * cexp (Ω * (k : ℂ) * I)).re : ℝ) : ℂ) + e k) k₀ Δk =
      crossSpectrumDiff N Ω e k₀ Δk +
        (starRingEnd ℂ) (a / 2) * (dft N Ω e (k₀ + Δk) - dft N Ω e (k₀ + 2 * Δk)) +
        a / 2 * ((starRingEnd ℂ) (dft N Ω e k₀) - (starRingEnd ℂ) (dft N Ω e (k₀ + Δk))) := by
  rw [crossSpectrumDiff, dft_add, dft_add, dft_add, dft_onBin hN hbin h2, dft_onBin hN hbin h2,
    dft_onBin hN hbin h2, crossDiff_add_const, crossSpectrumDiff]

/-- Rank-one channels: `Y_g = κ Y_r` on every window gives `S_g = |κ|² S_r`. -/
@[tmio T, powerlib_foundation] theorem crossSpectrumDiff_rankOne {N : ℕ} {Ω : ℝ} {yr yg : ℤ → ℂ}
    {κ : ℂ} (hY : ∀ j, dft N Ω yg j = κ * dft N Ω yr j) (k₀ Δk : ℤ) :
    crossSpectrumDiff N Ω yg k₀ Δk = (Complex.normSq κ : ℂ) * crossSpectrumDiff N Ω yr k₀ Δk := by
  rw [crossSpectrumDiff, hY, hY, hY, crossDiff_mul, crossSpectrumDiff]

/-! ## The cross-spectrum index -/

variable {K : ℕ}

/-- The cross-spectrum index (3-22) of two channels over the data sections `s ∈ Fin K`, with the
empirical expectation over sections: `C = |E{S̄_r S_g}|² / (E{|S_r|²} E{|S_g|²})`. -/
def index (Sr Sg : Fin K → ℂ) : ℝ :=
  ‖Finset.expect univ (fun s => (starRingEnd ℂ) (Sr s) * Sg s)‖ ^ 2 /
    (Finset.expect univ (fun s => ‖Sr s‖ ^ 2) * Finset.expect univ (fun s => ‖Sg s‖ ^ 2))

/-- The index is the squared coherence `|⟪S_r, S_g⟫|² / (‖S_r‖² ‖S_g‖²)` in `ℂ^K`. -/
@[tmio T, powerlib_foundation] private theorem index_eq_inner (Sr Sg : Fin K → ℂ) :
    index Sr Sg = ‖@inner ℂ _ _ (WithLp.toLp 2 Sr : EuclideanSpace ℂ (Fin K)) (WithLp.toLp 2 Sg)‖ ^ 2 /
      (‖(WithLp.toLp 2 Sr : EuclideanSpace ℂ (Fin K))‖ ^ 2 *
        ‖(WithLp.toLp 2 Sg : EuclideanSpace ℂ (Fin K))‖ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, PiLp.inner_apply]
  simp only [RCLike.inner_apply']
  rw [index, Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card, card_univ, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  · have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
    rw [norm_div, Complex.norm_natCast]
    field_simp

@[tmio T, powerlib_foundation] theorem index_nonneg (Sr Sg : Fin K → ℂ) : 0 ≤ index Sr Sg := by
  rw [index_eq_inner]; positivity

/-- Cauchy–Schwarz: `C ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem index_le_one (Sr Sg : Fin K → ℂ) : index Sr Sg ≤ 1 := by
  rw [index_eq_inner]
  set x : EuclideanSpace ℂ (Fin K) := WithLp.toLp 2 Sr
  set y : EuclideanSpace ℂ (Fin K) := WithLp.toLp 2 Sg
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  rcases (mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)).eq_or_lt with h0 | h0
  · rw [← h0, div_zero]; exact zero_le_one
  · rw [div_le_one h0, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `C = 1` exactly when the section values of the second channel are a nonzero multiple of those
of the first (both nonzero). -/
@[tmio T, powerlib_foundation] theorem index_eq_one_iff {Sr Sg : Fin K → ℂ} (hr : Sr ≠ 0)
    (hg : Sg ≠ 0) : index Sr Sg = 1 ↔ ∃ r : ℂ, r ≠ 0 ∧ Sg = r • Sr := by
  rw [index_eq_inner]
  set x : EuclideanSpace ℂ (Fin K) := WithLp.toLp 2 Sr
  set y : EuclideanSpace ℂ (Fin K) := WithLp.toLp 2 Sg
  have hx : x ≠ 0 := fun h => hr (by simpa [x] using congrArg WithLp.ofLp h)
  have hy : y ≠ 0 := fun h => hg (by simpa [y] using congrArg WithLp.ofLp h)
  have hpos : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    have := norm_pos_iff.mpr hx; have := norm_pos_iff.mpr hy; positivity
  rw [div_eq_one_iff_eq hpos.ne', ← mul_pow,
    sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    norm_inner_eq_norm_iff hx hy]
  constructor
  · rintro ⟨r, hr0, hrxy⟩
    exact ⟨r, hr0, by simpa [x, y] using congrArg WithLp.ofLp hrxy⟩
  · rintro ⟨r, hr0, hrxy⟩
    exact ⟨r, hr0, by simp [x, y, hrxy]⟩

@[tmio T, powerlib_foundation] theorem index_smul {Sr : Fin K → ℂ} (hr : Sr ≠ 0) {κ : ℂ}
    (hκ : κ ≠ 0) : index Sr (κ • Sr) = 1 :=
  (index_eq_one_iff hr (smul_ne_zero hκ hr)).mpr ⟨κ, hκ, rfl⟩

/-- Rank-one channels have `C = 1`: if `Y_g = κ Y_r` (`κ ≠ 0`) on every window of every section
and `(S_r,s)` is not identically zero. -/
@[tmio T, powerlib_foundation] theorem index_rankOne {N : ℕ} {Ω : ℝ} {yr yg : ℤ → ℂ} {κ : ℂ}
    (hκ : κ ≠ 0) (hY : ∀ j, dft N Ω yg j = κ * dft N Ω yr j) (k₀ : Fin K → ℤ) (Δk : ℤ)
    (hr : (fun s => crossSpectrumDiff N Ω yr (k₀ s) Δk) ≠ 0) :
    index (fun s => crossSpectrumDiff N Ω yr (k₀ s) Δk)
      (fun s => crossSpectrumDiff N Ω yg (k₀ s) Δk) = 1 := by
  have h : (fun s => crossSpectrumDiff N Ω yg (k₀ s) Δk) =
      (Complex.normSq κ : ℂ) • fun s => crossSpectrumDiff N Ω yr (k₀ s) Δk := by
    funext s
    rw [Pi.smul_apply, smul_eq_mul, crossSpectrumDiff_rankOne hY]
  rw [h]
  exact index_smul hr (by exact_mod_cast (Complex.normSq_pos.mpr hκ).ne')

/-- Perturbation bound: `1 − C(x, κx + e) ≤ ‖e‖² / ‖κx + e‖²`. -/
@[tmio T, powerlib_foundation] theorem one_sub_index_le {Sr : Fin K → ℂ} (hr : Sr ≠ 0) (κ : ℂ)
    (e : Fin K → ℂ) (hy : κ • Sr + e ≠ 0) :
    1 - index Sr (κ • Sr + e) ≤ (∑ s, ‖e s‖ ^ 2) / ∑ s, ‖(κ • Sr + e) s‖ ^ 2 := by
  rw [index_eq_inner]
  set x : EuclideanSpace ℂ (Fin K) := WithLp.toLp 2 Sr
  set y : EuclideanSpace ℂ (Fin K) := WithLp.toLp 2 (κ • Sr + e)
  have hx : x ≠ 0 := fun h => hr (by simpa [x] using congrArg WithLp.ofLp h)
  have hy' : y ≠ 0 := fun h => hy (by simpa [y] using congrArg WithLp.ofLp h)
  have hex : (∑ s, ‖e s‖ ^ 2) = ‖y - κ • x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [x, y]
  have hey : (∑ s, ‖(κ • Sr + e) s‖ ^ 2) = ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  rw [hex, hey]
  have hxn := norm_pos_iff.mpr hx
  have hyn := norm_pos_iff.mpr hy'
  -- Gram inequality: `‖x‖²‖y‖² − |⟪x, y⟫|² ≤ ‖x‖² ‖y − κx‖²`
  have hgram : ‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖@inner ℂ _ _ x y‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y - κ • x‖ ^ 2 := by
    have hsub := @norm_sub_sq ℂ _ _ _ _ y (κ • x)
    rw [inner_smul_right, norm_smul] at hsub
    have hc : ‖@inner ℂ _ _ x y‖ = ‖@inner ℂ _ _ y x‖ := by
      rw [← inner_conj_symm, Complex.norm_conj]
    rw [hsub, hc]
    set z := @inner ℂ _ _ y x
    set a := ‖x‖ ^ 2
    have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hk : ‖κ‖ ^ 2 = κ.re ^ 2 + κ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [mul_pow, hz, hk, RCLike.re_to_complex, Complex.mul_re]
    have ha : ‖x‖ ^ 2 = a := rfl
    nlinarith [sq_nonneg (z.re - a * κ.re), sq_nonneg (z.im + a * κ.im)]
  have key : ‖y - κ • x‖ ^ 2 / ‖y‖ ^ 2 + ‖@inner ℂ _ _ x y‖ ^ 2 / (‖x‖ ^ 2 * ‖y‖ ^ 2) =
      (‖x‖ ^ 2 * ‖y - κ • x‖ ^ 2 + ‖@inner ℂ _ _ x y‖ ^ 2) / (‖x‖ ^ 2 * ‖y‖ ^ 2) := by
    field_simp
  rw [sub_le_iff_le_add, key, le_div_iff₀ (by positivity)]
  linarith [hgram]

/-! ## The modal structure of a random sinusoid -/

/-- The common modal signal of one mode `z` driven by the real noise `q`:
`s[k] = Σ_{m ≤ k} z^{k−m} q[m]`. -/
def modalState (z : ℂ) (q : ℕ → ℝ) (k : ℕ) : ℂ := ∑ m ∈ range (k + 1), z ^ (k - m) * q m

/-- The modal convolution of channel `r`: with the real impulse response `h_r[k] = 2 Re(β_r z^k)`
of one complex mode pair, `Σ_{m ≤ k} h_r[k − m] q[m] = 2 Re(β_r s[k])`. -/
@[tmio T, powerlib_foundation] theorem modal_conv (β z : ℂ) (q : ℕ → ℝ) (k : ℕ) :
    ∑ m ∈ range (k + 1), 2 * (β * z ^ (k - m)).re * q m = 2 * (β * modalState z q k).re := by
  rw [modalState, mul_sum, Complex.re_sum, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [← mul_assoc, Complex.re_mul_ofReal]
  ring

/-- The modal residue `β_r = (c_r u)(v b)` of a channel `c_r` for the right eigenvector `u`, left
eigenvector `v` and noise input vector `b`. -/
def residue {n : ℕ} (c u v b : Fin n → ℂ) : ℂ := (c ⬝ᵥ u) * (v ⬝ᵥ b)

/-- Only the channel factor `c u` of the residue depends on the channel. -/
@[tmio T, powerlib_foundation] theorem residue_eq_mul {n : ℕ} {cr : Fin n → ℂ} (cg u v b : Fin n → ℂ)
    (hr : cr ⬝ᵥ u ≠ 0) : residue cg u v b = (cg ⬝ᵥ u) / (cr ⬝ᵥ u) * residue cr u v b := by
  simp only [residue]
  field_simp

/-- The DFT of the real channel `2 Re(β s)` is `β Y(s) + β̄ Y(s̄)`. -/
@[tmio T, powerlib_foundation] theorem dft_twiceRe (N : ℕ) (Ω : ℝ) (β : ℂ) (s : ℤ → ℂ) (k₀ : ℤ) :
    dft N Ω (fun k => ((2 * (β * s k).re : ℝ) : ℂ)) k₀ =
      β * dft N Ω s k₀ + (starRingEnd ℂ) β * dft N Ω (fun k => (starRingEnd ℂ) (s k)) k₀ := by
  have h : (fun k => ((2 * (β * s k).re : ℝ) : ℂ)) =
      fun k => β * s k + (starRingEnd ℂ) β * (starRingEnd ℂ) (s k) := by
    funext k
    rw [Complex.ofReal_mul, Complex.re_eq_add_conj, map_mul]
    push_cast
    ring
  rw [h, dft_add, dft_const_mul, dft_const_mul]

/-- Two channels `2 Re(β_r s)`, `2 Re(β_g s)` of the same random sinusoid `s` (`β_r ≠ 0`) are rank
one in the DFT domain when the image term `Y(s̄)` vanishes: `Y_g = (β_g/β_r) Y_r` on every
window, hence `S_g = |β_g/β_r|² S_r` (`crossSpectrumDiff_rankOne`) and `C = 1`
(`index_rankOne`). -/
@[tmio T, powerlib_foundation] theorem dft_rankOne_of_modal (N : ℕ) (Ω : ℝ) {βr : ℂ} (βg : ℂ)
    (hβ : βr ≠ 0) (s : ℤ → ℂ) (himg : ∀ j, dft N Ω (fun k => (starRingEnd ℂ) (s k)) j = 0)
    (j : ℤ) :
    dft N Ω (fun k => ((2 * (βg * s k).re : ℝ) : ℂ)) j =
      βg / βr * dft N Ω (fun k => ((2 * (βr * s k).re : ℝ) : ℂ)) j := by
  rw [dft_twiceRe, dft_twiceRe, himg, mul_zero, add_zero, mul_zero, add_zero]
  field_simp

end powerlib.Signal.CrossSpectrum
