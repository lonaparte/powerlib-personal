import theorem.Signal.CrossSpectrum
import theorem.Signal.MovingAverage
import theorem.SpecialFunctions.BesselI

/-! # Windowed single-bin DFTs: off-bin cancellation, leakage, the Kaiser window and bin choice

The windowed single-bin DFT `Y(k₀) = Σ_{k<N} w[k] y[k₀ + k] e^{−jΩ_b(k₀+k)}` of a sampled
record for an arbitrary window `w`, and the cross-spectrum difference `S = Ȳ₁Y₂ − Ȳ₂Y₃` of the
three windows starting at `k₀`, `k₀ + Δk`, `k₀ + 2Δk`. A single complex exponential at *any*
frequency gives window DFTs `Y_m = C ρ^m` with `|ρ| = 1`, so `S = 0` exactly for every window and
every frequency: the cancellation of TR-110 §3.5 does not need on-bin frequencies. A sum of two
exponentials (in particular a real sinusoid, the exponential and its image) leaves only explicit
cross terms, bounded by the product of the window transform at the two offsets from the bin
(leakage bound). For the rectangular window the image term is `O(1/N)` and the nearest bin
`|Ω − Ω_b| ≤ π/N` keeps at least `2/π` of the amplitude. The Kaiser window
`w[k] = I₀(β√(1 − (2k/(N−1) − 1)²))/I₀(β)` is symmetric, positive, at most `1`, equal to `1` at
the centre and strictly decreasing towards both edges.

Scope.
* Sampled complex signals `y : ℤ → ℂ`, an arbitrary complex window `w : ℕ → ℂ` of length `N`
  (the scale `1/N` of the scaled DFT (3-20) is part of the window), a bin frequency `Ω_b` and
  signal frequencies `Ω` in rad/sample (arbitrary reals: no on-bin condition), window starts
  `k₀`, `k₀ + Δk`, `k₀ + 2Δk` (arbitrary integers; overlapping windows allowed).
* Deterministic signals only: one or two complex exponentials (a real sinusoid is the exponential
  plus its image). Noise, the expectation of (3-22) and the statistics of the index are not
  treated here (the algebra of the index is in `theorem/Signal/CrossSpectrum.lean`).
* The Kaiser window is evaluated through the real power series of the modified Bessel function
  `I₀` (`besselI0_ofReal` links it to `SpecialFunctions.besselI0`); its shape parameter `β` is an
  arbitrary real (strict monotonicity needs `β ≠ 0`; `β = 0` is the rectangular window).
  Its leakage is bounded through its total variation (odd lengths `2M + 1 ≥ 3`); the side-lobe
  level as a function of `β` (Kaiser's empirical design formulas) is not quantified.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.5 (the cross-spectrum
method: "a Kaiser window", eq. (3-20) of the scaled single-bin DFT, (3-21) of the cross-spectrum
difference function, the choice of the DFT bin at the oscillation frequency); J. F. Kaiser,
"Nonrecursive digital filter design using the I₀-sinh window function", IEEE ISCAS 1974 (window
definition).

Results.
* `wdft`, `winTF`, `wcsd`, `dft_eq_wdft`, `crossSpectrumDiff_eq_wcsd` — the windowed DFT, the
  window transform `W(ν) = Σ_{k<N} w[k] e^{jνk}` and the windowed `S`; with the rectangular window
  `w ≡ 1/N` they are the scaled DFT (3-20) and (3-21) of `CrossSpectrum`.
* `wdft_add`, `wdft_const_mul`, `wdft_cexp`, `norm_wdft_cexp`, `wdft_cexp_shift` — linearity; the
  DFT of `a e^{jΩk}` is `a W(Ω − Ω_b) e^{j(Ω−Ω_b)k₀}`, of modulus `|a| |W(Ω − Ω_b)|` on every
  window, and the window `k₀ + mΔk` gives `C ρ^m` with `ρ = e^{j(Ω−Ω_b)Δk}`.
* `crossDiff_geom`, `wcsd_cexp` — `S(C, Cρ, Cρ²) = 0` for `|ρ| = 1`, hence `S = 0` for one
  exponential at any frequency and with any window.
* `crossTerms`, `crossDiff_add`, `wcsd_add`, `norm_crossTerms_le` — `S` of a sum is the sum of the
  two `S` plus the cross terms `P̄₁Q₂ + Q̄₁P₂ − P̄₂Q₃ − Q̄₂P₃`, of modulus at most `4 p q` when
  `|P_m| = p`, `|Q_m| = q`.
* `wcsd_two_cexp`, `norm_wcsd_two_cexp_le` — two exponentials: `S` equals the cross terms, and
  `|S| ≤ 4 |a₁||a₂| |W(Ω₁ − Ω_b)| |W(Ω₂ − Ω_b)|`.
* `re_cexp_eq`, `wcsd_realSin`, `norm_wcsd_realSin_le`, `wcsd_realSin_eq_zero` — a real
  sinusoid `Re(a e^{jΩk})`: `S` is the cross term between the exponential and its image,
  `|S| ≤ |a|² |W(Ω − Ω_b)| |W(−Ω − Ω_b)|`, and `S = 0` when the window transform vanishes at the
  image offset; `winTF_neg`, `norm_winTF_neg` (`|W(−ν)| = |W(ν)|` for a real window).
* Rectangular window: `winTF_rect` (`W(ν) = maResp N (−ν)`), `norm_winTF_rect_le_one`,
  `norm_winTF_rect_le` (`|W(ν)| ≤ 1/(N |sin(ν/2)|)`), `norm_crossSpectrumDiff_realSin_le`
  (off-bin leakage of (3-21): `|S| ≤ |a|² / (N |sin((Ω + Ω_b)/2)|)`), `two_div_pi_mul_abs_le`,
  `norm_winTF_rect_ge` (`|W(ν)| ≥ 2/π` for `|ν| ≤ π/N`).
* General windows: `norm_cexp_sub_one` (`|e^{jν} − 1| = 2|sin(ν/2)|`),
  `norm_winTF_le_variation` (summation by parts:
  `|W(ν)| ≤ (|w[N−1]| + Σ_k |w[k+1] − w[k]|)/|sin(ν/2)|`).
* Bin choice: `exists_bin_near` (some bin `2πℓ/N` has `|Ω − 2πℓ/N| ≤ π/N`),
  `exists_bin_norm_dft_ge` (at that bin the scaled DFT keeps at least `2/π` of `|a|` on every
  window).
* Kaiser window: `realI0`, `summable_realI0`, `besselI0_ofReal`, `realI0_zero`, `one_le_realI0`,
  `realI0_pos`, `realI0_le_realI0`, `realI0_lt_realI0` (`I₀` on the reals: `≥ 1`, increasing in
  `x²`); `kaiserShape`, `kaiser`, `kaiserShape_neg`, `kaiserShape_zero`, `kaiserShape_pos`,
  `kaiserShape_le_one`, `kaiserShape_strictAntiOn`, `kaiserShape_antitoneOn`,
  `kaiserShape_rect`, `kaiser_symm`, `kaiser_pos`, `kaiser_le_one`, `kaiser_center`,
  `kaiser_lt_of_lt_left`, `kaiser_lt_of_lt_right` (`β ≠ 0`), `kaiser_le_of_le_left`,
  `kaiser_le_of_le_right` (any `β`), `kaiser_conj`; leakage: `kaiser_variation` (total
  variation `2 − 2w[0]` for length `2M + 1`), `norm_winTF_kaiser_le`
  (`|W(ν)| ≤ (2 − 1/I₀(β))/|sin(ν/2)|`, independent of `N`), `one_div_le_kaiser`,
  `norm_winTF_kaiser_zero` (main lobe `|W(0)| ≥ N/I₀(β)`), `norm_wcsd_kaiser_le` (the
  cross-spectrum residual of an off-bin real sinusoid under the Kaiser window).

Sharpening (§3.5). The exact cancellation of the deterministic part of `S` holds for one complex
exponential at every frequency and with every window (`wcsd_cexp`); what an off-bin real
sinusoid leaves is only the cross term with its image, controlled by the window's leakage at
`Ω + Ω_b` (`norm_wcsd_realSin_le`), which for the rectangular window is `O(1/N)`
(`norm_crossSpectrumDiff_realSin_le`), and for the Kaiser window is bounded independently of
`N` while the main lobe grows like `N` (`norm_wcsd_kaiser_le`). The wave-1 on-bin cancellation
(`CrossSpectrum.crossSpectrumDiff_onBin`) is the case where this leakage vanishes.

Family and connection conclusions.
* None: this module defines no family; every result is an identity or inequality of explicit
  finite sums and power series.
-/

noncomputable section
namespace powerlib.Signal.Window
open Complex Finset
open scoped Nat
open powerlib.Signal.CrossSpectrum (crossDiff dft crossSpectrumDiff)

/-! ## The windowed single-bin DFT -/

/-- The windowed single-bin DFT over the window `k₀, …, k₀ + N − 1`:
`Y(k₀) = Σ_{k<N} w[k] y[k₀ + k] e^{−jΩ_b(k₀+k)}`. -/
def wdft (w : ℕ → ℂ) (N : ℕ) (Ωb : ℝ) (y : ℤ → ℂ) (k₀ : ℤ) : ℂ :=
  ∑ k ∈ range N, w k * y (k₀ + k) * cexp (-(Ωb * ((k₀ + k : ℤ) : ℂ) * I))

/-- The window transform `W(ν) = Σ_{k<N} w[k] e^{jνk}`. -/
def winTF (w : ℕ → ℂ) (N : ℕ) (ν : ℝ) : ℂ := ∑ k ∈ range N, w k * cexp (ν * (k : ℂ) * I)

/-- The windowed cross-spectrum difference `S = Ȳ₁Y₂ − Ȳ₂Y₃` of the windows starting at `k₀`,
`k₀ + Δk`, `k₀ + 2Δk`. -/
def wcsd (w : ℕ → ℂ) (N : ℕ) (Ωb : ℝ) (y : ℤ → ℂ) (k₀ Δk : ℤ) : ℂ :=
  crossDiff (wdft w N Ωb y k₀) (wdft w N Ωb y (k₀ + Δk)) (wdft w N Ωb y (k₀ + 2 * Δk))

/-- The scaled DFT (3-20) is the windowed DFT with the rectangular window `w ≡ 1/N`. -/
@[tmio T, powerlib_foundation] theorem dft_eq_wdft (N : ℕ) (Ω : ℝ) (y : ℤ → ℂ) (k₀ : ℤ) :
    dft N Ω y k₀ = wdft (fun _ => (1 / N : ℂ)) N Ω y k₀ := by
  simp only [dft, wdft, mul_sum, mul_assoc]

/-- The cross-spectrum difference (3-21) is the windowed one with the rectangular window. -/
@[tmio T, powerlib_foundation] theorem crossSpectrumDiff_eq_wcsd (N : ℕ) (Ω : ℝ) (y : ℤ → ℂ)
    (k₀ Δk : ℤ) : crossSpectrumDiff N Ω y k₀ Δk = wcsd (fun _ => (1 / N : ℂ)) N Ω y k₀ Δk := by
  simp only [crossSpectrumDiff, wcsd, dft_eq_wdft]

@[tmio T, powerlib_foundation] theorem wdft_add (w : ℕ → ℂ) (N : ℕ) (Ωb : ℝ) (y₁ y₂ : ℤ → ℂ)
    (k₀ : ℤ) : wdft w N Ωb (fun k => y₁ k + y₂ k) k₀ = wdft w N Ωb y₁ k₀ + wdft w N Ωb y₂ k₀ := by
  simp only [wdft, mul_add, add_mul, sum_add_distrib]

@[tmio T, powerlib_foundation] theorem wdft_const_mul (w : ℕ → ℂ) (N : ℕ) (Ωb : ℝ) (c : ℂ)
    (y : ℤ → ℂ) (k₀ : ℤ) : wdft w N Ωb (fun k => c * y k) k₀ = c * wdft w N Ωb y k₀ := by
  simp only [wdft, mul_sum]
  refine sum_congr rfl fun k _ => by ring

/-- The windowed DFT of a complex exponential at an arbitrary frequency:
`Y(k₀) = a W(Ω − Ω_b) e^{j(Ω−Ω_b)k₀}`. -/
@[tmio T, powerlib_foundation] theorem wdft_cexp (w : ℕ → ℂ) (N : ℕ) (Ωb Ω : ℝ) (a : ℂ)
    (k₀ : ℤ) :
    wdft w N Ωb (fun k => a * cexp (Ω * (k : ℂ) * I)) k₀ =
      a * winTF w N (Ω - Ωb) * cexp (((Ω - Ωb : ℝ) : ℂ) * (k₀ : ℂ) * I) := by
  simp only [wdft, winTF, mul_sum, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  have h : cexp (Ω * ((k₀ + k : ℤ) : ℂ) * I) * cexp (-(Ωb * ((k₀ + k : ℤ) : ℂ) * I)) =
      cexp (((Ω - Ωb : ℝ) : ℂ) * (k : ℂ) * I) * cexp (((Ω - Ωb : ℝ) : ℂ) * (k₀ : ℂ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc w k * (a * cexp (Ω * ((k₀ + k : ℤ) : ℂ) * I)) * cexp (-(Ωb * ((k₀ + k : ℤ) : ℂ) * I))
      = a * w k * (cexp (Ω * ((k₀ + k : ℤ) : ℂ) * I) *
          cexp (-(Ωb * ((k₀ + k : ℤ) : ℂ) * I))) := by ring
    _ = _ := by rw [h]; ring

/-- On every window the DFT of `a e^{jΩk}` has modulus `|a| |W(Ω − Ω_b)|`: the off-bin
attenuation is the window transform at the offset from the bin. -/
@[tmio T, powerlib_foundation] theorem norm_wdft_cexp (w : ℕ → ℂ) (N : ℕ) (Ωb Ω : ℝ) (a : ℂ)
    (j : ℤ) :
    ‖wdft w N Ωb (fun k => a * cexp (Ω * (k : ℂ) * I)) j‖ = ‖a‖ * ‖winTF w N (Ω - Ωb)‖ := by
  rw [wdft_cexp, norm_mul, norm_mul, show ((Ω - Ωb : ℝ) : ℂ) * (j : ℂ) * I =
    (((Ω - Ωb) * j : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The windows `k₀ + mΔk` give a geometric sequence `Y_m = C ρ^m` with
`C = a W(Ω − Ω_b) e^{j(Ω−Ω_b)k₀}` and the unimodular ratio `ρ = e^{j(Ω−Ω_b)Δk}`. -/
@[tmio T, powerlib_foundation] theorem wdft_cexp_shift (w : ℕ → ℂ) (N : ℕ) (Ωb Ω : ℝ) (a : ℂ)
    (k₀ Δk : ℤ) (m : ℕ) :
    wdft w N Ωb (fun k => a * cexp (Ω * (k : ℂ) * I)) (k₀ + m * Δk) =
      wdft w N Ωb (fun k => a * cexp (Ω * (k : ℂ) * I)) k₀ *
        cexp (((Ω - Ωb : ℝ) : ℂ) * (Δk : ℂ) * I) ^ m ∧
      ‖cexp (((Ω - Ωb : ℝ) : ℂ) * (Δk : ℂ) * I)‖ = 1 := by
  refine ⟨?_, by
    rw [show ((Ω - Ωb : ℝ) : ℂ) * (Δk : ℂ) * I = (((Ω - Ωb) * Δk : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]⟩
  rw [wdft_cexp, wdft_cexp, ← Complex.exp_nat_mul, mul_assoc _ (cexp _) (cexp _),
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ## Exact cancellation for one exponential at any frequency -/

/-- A geometric sequence of three DFT values with a unimodular ratio cancels exactly:
`S(C, Cρ, Cρ²) = 0` for `|ρ| = 1`. -/
@[tmio T, powerlib_foundation] theorem crossDiff_geom (C : ℂ) {ρ : ℂ} (hρ : ‖ρ‖ = 1) :
    crossDiff C (C * ρ) (C * ρ ^ 2) = 0 := by
  have h : (starRingEnd ℂ) ρ * ρ = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hρ]
    norm_num
  simp only [crossDiff, map_mul]
  linear_combination (-(starRingEnd ℂ) C * C * ρ) * h

/-- **Off-bin cancellation.** For one complex exponential `a e^{jΩk}` at any frequency `Ω` and with
any window `w`, the cross-spectrum difference vanishes exactly. -/
@[tmio T, powerlib_foundation] theorem wcsd_cexp (w : ℕ → ℂ) (N : ℕ) (Ωb Ω : ℝ) (a : ℂ)
    (k₀ Δk : ℤ) : wcsd w N Ωb (fun k => a * cexp (Ω * (k : ℂ) * I)) k₀ Δk = 0 := by
  obtain ⟨h1, hρ⟩ := wdft_cexp_shift w N Ωb Ω a k₀ Δk 1
  obtain ⟨h2, -⟩ := wdft_cexp_shift w N Ωb Ω a k₀ Δk 2
  rw [Nat.cast_one, one_mul, pow_one] at h1
  rw [wcsd, h1, show k₀ + 2 * Δk = k₀ + ((2 : ℕ) : ℤ) * Δk by norm_num, h2]
  exact crossDiff_geom _ hρ

/-! ## Two components: the cross terms -/

/-- The cross terms of `S` between two components with window DFTs `(P₁, P₂, P₃)` and
`(Q₁, Q₂, Q₃)`: `P̄₁Q₂ + Q̄₁P₂ − P̄₂Q₃ − Q̄₂P₃`. -/
def crossTerms (P₁ P₂ P₃ Q₁ Q₂ Q₃ : ℂ) : ℂ :=
  (starRingEnd ℂ) P₁ * Q₂ + (starRingEnd ℂ) Q₁ * P₂ - (starRingEnd ℂ) P₂ * Q₃ -
    (starRingEnd ℂ) Q₂ * P₃

/-- `S` of a sum of two components is the sum of their `S` plus the cross terms. -/
@[tmio T, powerlib_foundation] theorem crossDiff_add (P₁ P₂ P₃ Q₁ Q₂ Q₃ : ℂ) :
    crossDiff (P₁ + Q₁) (P₂ + Q₂) (P₃ + Q₃) =
      crossDiff P₁ P₂ P₃ + crossDiff Q₁ Q₂ Q₃ + crossTerms P₁ P₂ P₃ Q₁ Q₂ Q₃ := by
  simp only [crossDiff, crossTerms, map_add]
  ring

@[tmio T, powerlib_foundation] theorem wcsd_add (w : ℕ → ℂ) (N : ℕ) (Ωb : ℝ) (y₁ y₂ : ℤ → ℂ)
    (k₀ Δk : ℤ) :
    wcsd w N Ωb (fun k => y₁ k + y₂ k) k₀ Δk =
      wcsd w N Ωb y₁ k₀ Δk + wcsd w N Ωb y₂ k₀ Δk +
        crossTerms (wdft w N Ωb y₁ k₀) (wdft w N Ωb y₁ (k₀ + Δk)) (wdft w N Ωb y₁ (k₀ + 2 * Δk))
          (wdft w N Ωb y₂ k₀) (wdft w N Ωb y₂ (k₀ + Δk)) (wdft w N Ωb y₂ (k₀ + 2 * Δk)) := by
  rw [wcsd, wdft_add, wdft_add, wdft_add, crossDiff_add, wcsd, wcsd]

/-- The cross terms of components of constant moduli `p` and `q` are at most `4 p q`. -/
@[tmio T, powerlib_foundation] theorem norm_crossTerms_le {P₁ P₂ P₃ Q₁ Q₂ Q₃ : ℂ} {p q : ℝ}
    (hP₁ : ‖P₁‖ = p) (hP₂ : ‖P₂‖ = p) (hP₃ : ‖P₃‖ = p) (hQ₁ : ‖Q₁‖ = q) (hQ₂ : ‖Q₂‖ = q)
    (hQ₃ : ‖Q₃‖ = q) : ‖crossTerms P₁ P₂ P₃ Q₁ Q₂ Q₃‖ ≤ 4 * (p * q) := by
  have e : ∀ X Y : ℂ, ‖(starRingEnd ℂ) X * Y‖ = ‖X‖ * ‖Y‖ := fun X Y => by
    rw [norm_mul, Complex.norm_conj]
  unfold crossTerms
  calc _ ≤ ‖(starRingEnd ℂ) P₁ * Q₂ + (starRingEnd ℂ) Q₁ * P₂ - (starRingEnd ℂ) P₂ * Q₃‖ +
          ‖(starRingEnd ℂ) Q₂ * P₃‖ := norm_sub_le _ _
    _ ≤ ‖(starRingEnd ℂ) P₁ * Q₂ + (starRingEnd ℂ) Q₁ * P₂‖ + ‖(starRingEnd ℂ) P₂ * Q₃‖ +
          ‖(starRingEnd ℂ) Q₂ * P₃‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖(starRingEnd ℂ) P₁ * Q₂‖ + ‖(starRingEnd ℂ) Q₁ * P₂‖ + ‖(starRingEnd ℂ) P₂ * Q₃‖ +
          ‖(starRingEnd ℂ) Q₂ * P₃‖ := by gcongr; exact norm_add_le _ _
    _ = 4 * (p * q) := by rw [e, e, e, e, hP₁, hP₂, hP₃, hQ₁, hQ₂, hQ₃]; ring

/-- **Two exponentials.** For `y = a₁ e^{jΩ₁k} + a₂ e^{jΩ₂k}` only the cross terms remain. -/
@[tmio T, powerlib_foundation] theorem wcsd_two_cexp (w : ℕ → ℂ) (N : ℕ) (Ωb Ω₁ Ω₂ : ℝ)
    (a₁ a₂ : ℂ) (k₀ Δk : ℤ) :
    wcsd w N Ωb (fun k => a₁ * cexp (Ω₁ * (k : ℂ) * I) + a₂ * cexp (Ω₂ * (k : ℂ) * I)) k₀ Δk =
      crossTerms (wdft w N Ωb (fun k => a₁ * cexp (Ω₁ * (k : ℂ) * I)) k₀)
        (wdft w N Ωb (fun k => a₁ * cexp (Ω₁ * (k : ℂ) * I)) (k₀ + Δk))
        (wdft w N Ωb (fun k => a₁ * cexp (Ω₁ * (k : ℂ) * I)) (k₀ + 2 * Δk))
        (wdft w N Ωb (fun k => a₂ * cexp (Ω₂ * (k : ℂ) * I)) k₀)
        (wdft w N Ωb (fun k => a₂ * cexp (Ω₂ * (k : ℂ) * I)) (k₀ + Δk))
        (wdft w N Ωb (fun k => a₂ * cexp (Ω₂ * (k : ℂ) * I)) (k₀ + 2 * Δk)) := by
  rw [wcsd_add (y₁ := fun k => a₁ * cexp (Ω₁ * (k : ℂ) * I))
    (y₂ := fun k => a₂ * cexp (Ω₂ * (k : ℂ) * I)), wcsd_cexp, wcsd_cexp, zero_add, zero_add]

/-- **Leakage bound for two exponentials.**
`|S| ≤ 4 |a₁| |a₂| |W(Ω₁ − Ω_b)| |W(Ω₂ − Ω_b)|`: the residual of `S` is bounded by the product of
the window's response to the two components at the bin. -/
@[tmio T, powerlib_foundation] theorem norm_wcsd_two_cexp_le (w : ℕ → ℂ) (N : ℕ)
    (Ωb Ω₁ Ω₂ : ℝ) (a₁ a₂ : ℂ) (k₀ Δk : ℤ) :
    ‖wcsd w N Ωb (fun k => a₁ * cexp (Ω₁ * (k : ℂ) * I) + a₂ * cexp (Ω₂ * (k : ℂ) * I)) k₀ Δk‖ ≤
      4 * (‖a₁‖ * ‖a₂‖ * ‖winTF w N (Ω₁ - Ωb)‖ * ‖winTF w N (Ω₂ - Ωb)‖) := by
  rw [wcsd_two_cexp]
  refine (norm_crossTerms_le (norm_wdft_cexp _ _ _ _ _ _) (norm_wdft_cexp _ _ _ _ _ _)
    (norm_wdft_cexp _ _ _ _ _ _) (norm_wdft_cexp _ _ _ _ _ _) (norm_wdft_cexp _ _ _ _ _ _)
    (norm_wdft_cexp _ _ _ _ _ _)).trans (le_of_eq ?_)
  ring

/-! ## A real sinusoid: the exponential and its image -/

/-- `Re(a e^{jΩk}) = (a/2) e^{jΩk} + (ā/2) e^{−jΩk}`. -/
@[tmio T, powerlib_foundation] theorem re_cexp_eq (a : ℂ) (Ω : ℝ) (k : ℤ) :
    (((a * cexp (Ω * (k : ℂ) * I)).re : ℝ) : ℂ) =
      a / 2 * cexp (Ω * (k : ℂ) * I) +
        (starRingEnd ℂ) a / 2 * cexp (((-Ω : ℝ) : ℂ) * (k : ℂ) * I) := by
  rw [Complex.re_eq_add_conj, map_mul, ← Complex.exp_conj]
  have : (starRingEnd ℂ) (Ω * (k : ℂ) * I) = ((-Ω : ℝ) : ℂ) * (k : ℂ) * I := by
    simp only [map_mul, Complex.conj_ofReal, map_intCast, Complex.conj_I]
    push_cast
    ring
  rw [this]
  ring

/-- A real sinusoid at any frequency: `S` is the cross term between the exponential and its
image. -/
@[tmio T, powerlib_foundation] theorem wcsd_realSin (w : ℕ → ℂ) (N : ℕ) (Ωb Ω : ℝ) (a : ℂ)
    (k₀ Δk : ℤ) :
    wcsd w N Ωb (fun k => (((a * cexp (Ω * (k : ℂ) * I)).re : ℝ) : ℂ)) k₀ Δk =
      crossTerms (wdft w N Ωb (fun k => a / 2 * cexp (Ω * (k : ℂ) * I)) k₀)
        (wdft w N Ωb (fun k => a / 2 * cexp (Ω * (k : ℂ) * I)) (k₀ + Δk))
        (wdft w N Ωb (fun k => a / 2 * cexp (Ω * (k : ℂ) * I)) (k₀ + 2 * Δk))
        (wdft w N Ωb (fun k => (starRingEnd ℂ) a / 2 * cexp (((-Ω : ℝ) : ℂ) * (k : ℂ) * I)) k₀)
        (wdft w N Ωb (fun k => (starRingEnd ℂ) a / 2 * cexp (((-Ω : ℝ) : ℂ) * (k : ℂ) * I))
          (k₀ + Δk))
        (wdft w N Ωb (fun k => (starRingEnd ℂ) a / 2 * cexp (((-Ω : ℝ) : ℂ) * (k : ℂ) * I))
          (k₀ + 2 * Δk)) := by
  simp_rw [re_cexp_eq]
  exact wcsd_two_cexp w N Ωb Ω (-Ω) (a / 2) ((starRingEnd ℂ) a / 2) k₀ Δk

/-- **Leakage bound for a real sinusoid.** For `Re(a e^{jΩk})` at any frequency and with any
window, `|S| ≤ |a|² |W(Ω − Ω_b)| |W(−Ω − Ω_b)|`. -/
@[tmio T, powerlib_foundation] theorem norm_wcsd_realSin_le (w : ℕ → ℂ) (N : ℕ) (Ωb Ω : ℝ)
    (a : ℂ) (k₀ Δk : ℤ) :
    ‖wcsd w N Ωb (fun k => (((a * cexp (Ω * (k : ℂ) * I)).re : ℝ) : ℂ)) k₀ Δk‖ ≤
      ‖a‖ ^ 2 * ‖winTF w N (Ω - Ωb)‖ * ‖winTF w N (-Ω - Ωb)‖ := by
  simp_rw [re_cexp_eq]
  refine (norm_wcsd_two_cexp_le w N Ωb Ω (-Ω) (a / 2) ((starRingEnd ℂ) a / 2) k₀ Δk).trans
    (le_of_eq ?_)
  rw [norm_div, norm_div, Complex.norm_conj, Complex.norm_ofNat]
  ring

/-- If the window transform vanishes at the image offset `−Ω − Ω_b`, a real sinusoid cancels
exactly. -/
@[tmio T, powerlib_foundation] theorem wcsd_realSin_eq_zero {w : ℕ → ℂ} {N : ℕ} {Ωb Ω : ℝ}
    (h : winTF w N (-Ω - Ωb) = 0) (a : ℂ) (k₀ Δk : ℤ) :
    wcsd w N Ωb (fun k => (((a * cexp (Ω * (k : ℂ) * I)).re : ℝ) : ℂ)) k₀ Δk = 0 := by
  have := norm_wcsd_realSin_le w N Ωb Ω a k₀ Δk
  rw [h, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.mp this

/-- For a real window `W(−ν) = conj W(ν)`. -/
@[tmio T, powerlib_foundation] theorem winTF_neg {w : ℕ → ℂ} (hw : ∀ k, (starRingEnd ℂ) (w k) = w k)
    (N : ℕ) (ν : ℝ) : winTF w N (-ν) = (starRingEnd ℂ) (winTF w N ν) := by
  simp only [winTF, map_sum, map_mul, hw, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_natCast, Complex.conj_I]
  refine sum_congr rfl fun k _ => ?_
  congr 2
  push_cast
  ring

/-- For a real window `|W(−ν)| = |W(ν)|`, so the image leakage is `|W(Ω + Ω_b)|`. -/
@[tmio T, powerlib_foundation] theorem norm_winTF_neg {w : ℕ → ℂ}
    (hw : ∀ k, (starRingEnd ℂ) (w k) = w k) (N : ℕ) (ν : ℝ) :
    ‖winTF w N (-ν)‖ = ‖winTF w N ν‖ := by
  rw [winTF_neg hw, Complex.norm_conj]

/-! ## The rectangular window -/

/-- The rectangular window transform is the moving-average response at `−ν`. -/
@[tmio T, powerlib_foundation] theorem winTF_rect (N : ℕ) (ν : ℝ) :
    winTF (fun _ => (1 / N : ℂ)) N ν = maResp N (-ν) := by
  simp only [winTF, maResp, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  congr 2
  push_cast
  ring

@[tmio T, powerlib_foundation] theorem norm_winTF_rect_le_one (N : ℕ) (ν : ℝ) :
    ‖winTF (fun _ => (1 / N : ℂ)) N ν‖ ≤ 1 := by
  rw [winTF_rect]; exact norm_maResp_le N (-ν)

/-- Leakage of the rectangular window away from the main lobe:
`|W(ν)| ≤ 1/(N |sin(ν/2)|)` for `sin(ν/2) ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem norm_winTF_rect_le {N : ℕ} (hN : N ≠ 0) {ν : ℝ}
    (hs : Real.sin (ν / 2) ≠ 0) :
    ‖winTF (fun _ => (1 / N : ℂ)) N ν‖ ≤ 1 / (N * |Real.sin (ν / 2)|) := by
  have hs' : Real.sin (-ν / 2) ≠ 0 := by rw [neg_div, Real.sin_neg]; exact neg_ne_zero.mpr hs
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [winTF_rect, maResp_eq hN hs', norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hN', neg_div, Real.sin_neg,
    abs_neg]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)

/-- **Off-bin leakage of (3-21).** For the scaled DFT (rectangular window) and a real sinusoid
`Re(a e^{jΩk})` at any frequency, `|S| ≤ |a|² / (N |sin((Ω + Ω_b)/2)|)`: the residual of the
cancellation is `O(1/N)` away from the image bin. -/
@[tmio T, powerlib_foundation] theorem norm_crossSpectrumDiff_realSin_le {N : ℕ} (hN : N ≠ 0)
    {Ωb Ω : ℝ} (hs : Real.sin ((Ω + Ωb) / 2) ≠ 0) (a : ℂ) (k₀ Δk : ℤ) :
    ‖crossSpectrumDiff N Ωb (fun k => (((a * cexp (Ω * (k : ℂ) * I)).re : ℝ) : ℂ)) k₀ Δk‖ ≤
      ‖a‖ ^ 2 / (N * |Real.sin ((Ω + Ωb) / 2)|) := by
  rw [crossSpectrumDiff_eq_wcsd]
  refine (norm_wcsd_realSin_le _ N Ωb Ω a k₀ Δk).trans ?_
  have hw : ∀ k : ℕ, (starRingEnd ℂ) ((fun _ => (1 / N : ℂ)) k) = (1 / N : ℂ) := fun _ => by
    simp
  rw [show -Ω - Ωb = -(Ω + Ωb) by ring, norm_winTF_neg hw]
  have h1 := norm_winTF_rect_le_one N (Ω - Ωb)
  have h2 := norm_winTF_rect_le hN hs
  have ha := sq_nonneg ‖a‖
  calc ‖a‖ ^ 2 * ‖winTF (fun _ => (1 / N : ℂ)) N (Ω - Ωb)‖ *
        ‖winTF (fun _ => (1 / N : ℂ)) N (Ω + Ωb)‖
      ≤ ‖a‖ ^ 2 * 1 * (1 / (N * |Real.sin ((Ω + Ωb) / 2)|)) := by gcongr
    _ = _ := by ring

/-- Jordan's inequality in absolute value: `(2/π)|x| ≤ |sin x|` for `|x| ≤ π/2`. -/
@[tmio T, powerlib_foundation] theorem two_div_pi_mul_abs_le {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    2 / Real.pi * |x| ≤ |Real.sin x| := by
  have hπ : |x| ≤ Real.pi := hx.trans (by linarith [Real.pi_pos])
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hπ]
  exact Real.mul_le_sin (abs_nonneg x) hx

/-- **Scalloping bound.** Within half a bin, `|ν| ≤ π/N`, the rectangular window keeps at least
`2/π` of the amplitude: `|W(ν)| ≥ 2/π`. -/
@[tmio T, powerlib_foundation] theorem norm_winTF_rect_ge {N : ℕ} (hN : N ≠ 0) {ν : ℝ}
    (hν : |ν| ≤ Real.pi / N) : 2 / Real.pi ≤ ‖winTF (fun _ => (1 / N : ℂ)) N ν‖ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hπ := Real.pi_pos
  rcases eq_or_ne ν 0 with rfl | hν0
  · rw [winTF_rect, neg_zero, maResp_zero hN, norm_one, div_le_one hπ]
    linarith [Real.two_le_pi]
  have hx : |ν / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_two]
    have : Real.pi / N ≤ Real.pi := div_le_self hπ.le hN1
    linarith
  have hxN : |N * ν / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_two, Nat.abs_cast]
    have := (le_div_iff₀' hN0).mp hν
    linarith
  have hspos : 0 < |Real.sin (ν / 2)| := by
    have h := two_div_pi_mul_abs_le hx
    have : 0 < 2 / Real.pi * |ν / 2| := by
      have : 0 < |ν / 2| := abs_pos.mpr (div_ne_zero hν0 two_ne_zero)
      positivity
    linarith
  have hs' : Real.sin (-ν / 2) ≠ 0 := by
    rw [neg_div, Real.sin_neg, neg_ne_zero]; exact abs_pos.mp hspos
  rw [winTF_rect, maResp_eq hN hs', norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hN0, neg_div, Real.sin_neg,
    abs_neg, show (N : ℝ) * -ν / 2 = -(N * ν / 2) by ring, Real.sin_neg, abs_neg,
    le_div_iff₀ (by positivity)]
  have h1 := two_div_pi_mul_abs_le hxN
  have h2 := Real.abs_sin_le_abs (x := ν / 2)
  have h3 : |N * ν / 2| = N * |ν / 2| := by
    rw [show (N : ℝ) * ν / 2 = N * (ν / 2) by ring, abs_mul, Nat.abs_cast]
  rw [h3] at h1
  calc 2 / Real.pi * (N * |Real.sin (ν / 2)|) ≤ 2 / Real.pi * (N * |ν / 2|) := by gcongr
    _ ≤ |Real.sin (N * ν / 2)| := by linarith

/-! ## Leakage of a general window by summation by parts -/

/-- `|e^{jν} − 1| = 2 |sin(ν/2)|`. -/
@[tmio T, powerlib_foundation] theorem norm_cexp_sub_one (ν : ℝ) :
    ‖cexp (ν * I) - 1‖ = 2 * |Real.sin (ν / 2)| := by
  have h : ‖cexp (ν * I) - 1‖ ^ 2 = (2 * |Real.sin (ν / 2)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [sub_re, sub_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, one_re,
      one_im, sub_zero]
    rw [mul_pow, sq_abs]
    have h2 : Real.cos ν = 1 - 2 * Real.sin (ν / 2) ^ 2 := by
      rw [show ν = 2 * (ν / 2) by ring, Real.cos_two_mul, Real.cos_sq']
      ring_nf
    nlinarith [Real.sin_sq_add_cos_sq ν]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- **Leakage of an arbitrary window** (summation by parts): for `sin(ν/2) ≠ 0`,
`|W(ν)| ≤ (|w[N−1]| + Σ_{k<N−1} |w[k+1] − w[k]|) / |sin(ν/2)|`. -/
@[tmio T, powerlib_foundation] theorem norm_winTF_le_variation (w : ℕ → ℂ) (N : ℕ) {ν : ℝ}
    (hs : Real.sin (ν / 2) ≠ 0) :
    ‖winTF w N ν‖ ≤
      (‖w (N - 1)‖ + ∑ k ∈ range (N - 1), ‖w (k + 1) - w k‖) / |Real.sin (ν / 2)| := by
  set z : ℂ := cexp (ν * I)
  have hz1 : z - 1 ≠ 0 := by
    intro h
    have := norm_cexp_sub_one ν
    rw [show cexp (ν * I) - 1 = z - 1 from rfl, h, norm_zero] at this
    have : 0 < |Real.sin (ν / 2)| := abs_pos.mpr hs
    linarith
  have hspos : 0 < |Real.sin (ν / 2)| := abs_pos.mpr hs
  have hG : ∀ m, ‖∑ j ∈ range m, z ^ j‖ ≤ 1 / |Real.sin (ν / 2)| := fun m => by
    rw [geom_sum_eq (sub_ne_zero.mp hz1), norm_div, norm_cexp_sub_one ν, div_le_div_iff₀
      (by positivity) hspos]
    have : ‖z ^ m - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow, norm_one]; norm_num
    nlinarith
  have hW : winTF w N ν = ∑ k ∈ range N, w k • z ^ k := by
    simp only [winTF, smul_eq_mul, z, ← Complex.exp_nat_mul]
    refine sum_congr rfl fun k _ => by congr 2; ring
  rw [hW, sum_range_by_parts]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, add_div]
  refine add_le_add ?_ ?_
  · calc ‖w (N - 1)‖ * ‖∑ j ∈ range N, z ^ j‖ ≤ ‖w (N - 1)‖ * (1 / |Real.sin (ν / 2)|) :=
          mul_le_mul_of_nonneg_left (hG N) (norm_nonneg _)
      _ = _ := by ring
  · refine (norm_sum_le _ _).trans ?_
    rw [sum_div]
    refine sum_le_sum fun k _ => ?_
    rw [norm_smul]
    calc ‖w (k + 1) - w k‖ * ‖∑ j ∈ range (k + 1), z ^ j‖
        ≤ ‖w (k + 1) - w k‖ * (1 / |Real.sin (ν / 2)|) :=
          mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _)
      _ = _ := by ring

/-! ## Bin choice -/

/-- Some DFT bin `2πℓ/N` lies within half a bin of any frequency: `|Ω − 2πℓ/N| ≤ π/N`. -/
@[tmio T, powerlib_foundation] theorem exists_bin_near {N : ℕ} (hN : N ≠ 0) (Ω : ℝ) :
    ∃ ℓ : ℤ, |Ω - 2 * Real.pi * ℓ / N| ≤ Real.pi / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hπ := Real.pi_pos
  refine ⟨round (Ω * N / (2 * Real.pi)), ?_⟩
  have h := abs_sub_round (Ω * N / (2 * Real.pi))
  set r : ℝ := (round (Ω * N / (2 * Real.pi)) : ℝ)
  have e : Ω - 2 * Real.pi * r / N = (2 * Real.pi / N) * (Ω * N / (2 * Real.pi) - r) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (by positivity)]
  calc 2 * Real.pi / N * |Ω * N / (2 * Real.pi) - r| ≤ 2 * Real.pi / N * (1 / 2) := by gcongr
    _ = Real.pi / N := by ring

/-- **Nearest-bin choice.** For any frequency `Ω` there is a bin `Ω_b = 2πℓ/N` within `π/N` of
it at which the scaled DFT (3-20) of `a e^{jΩk}` keeps at least `2/π` of `|a|` on every
window. -/
@[tmio T, powerlib_foundation] theorem exists_bin_norm_dft_ge {N : ℕ} (hN : N ≠ 0) (Ω : ℝ)
    (a : ℂ) : ∃ ℓ : ℤ, |Ω - 2 * Real.pi * ℓ / N| ≤ Real.pi / N ∧
      ∀ j : ℤ, 2 / Real.pi * ‖a‖ ≤
        ‖dft N (2 * Real.pi * ℓ / N) (fun k => a * cexp (Ω * (k : ℂ) * I)) j‖ := by
  obtain ⟨ℓ, hℓ⟩ := exists_bin_near hN Ω
  refine ⟨ℓ, hℓ, fun j => ?_⟩
  rw [dft_eq_wdft, norm_wdft_cexp, mul_comm ‖a‖]
  exact mul_le_mul_of_nonneg_right (norm_winTF_rect_ge hN hℓ) (norm_nonneg a)

/-! ## The Kaiser window -/

/-- The modified Bessel function `I₀` on the reals: `I₀(x) = Σ_k (x²/4)^k/(k!)²`. -/
def realI0 (x : ℝ) : ℝ := ∑' k : ℕ, (x ^ 2 / 4) ^ k / ((k ! : ℝ) ^ 2)

@[tmio T, powerlib_foundation] theorem summable_realI0 (x : ℝ) :
    Summable fun k : ℕ => (x ^ 2 / 4) ^ k / ((k ! : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (Real.summable_pow_div_factorial (x ^ 2 / 4))
  have hk : (1 : ℝ) ≤ (k ! : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk0 : (0 : ℝ) < (k ! : ℝ) := by positivity
  exact div_le_div_of_nonneg_left (by positivity) hk0 (by nlinarith)

/-- `realI0` is the library's modified Bessel function on the real axis. -/
@[tmio T, powerlib_foundation] theorem besselI0_ofReal (x : ℝ) :
    SpecialFunctions.besselI0 (x : ℂ) = (realI0 x : ℂ) := by
  rw [SpecialFunctions.besselI0, SpecialFunctions.besselSeries0, realI0, Complex.ofReal_tsum]
  congr 1
  funext k
  push_cast
  ring

@[tmio T, powerlib_foundation] theorem realI0_zero : realI0 0 = 1 := by
  rw [realI0, tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

/-- `I₀(x) ≥ 1`. -/
@[tmio T, powerlib_foundation] theorem one_le_realI0 (x : ℝ) : 1 ≤ realI0 x := by
  have h := (summable_realI0 x).le_tsum 0 (fun k _ => by positivity)
  rw [realI0]
  simpa using h

@[tmio T, powerlib_foundation] theorem realI0_pos (x : ℝ) : 0 < realI0 x :=
  lt_of_lt_of_le one_pos (one_le_realI0 x)

/-- `I₀` is increasing in `x²`. -/
@[tmio T, powerlib_foundation] theorem realI0_le_realI0 {x y : ℝ} (h : x ^ 2 ≤ y ^ 2) :
    realI0 x ≤ realI0 y := by
  refine (summable_realI0 x).tsum_le_tsum (fun k => ?_) (summable_realI0 y)
  have hx : 0 ≤ x ^ 2 / 4 := by positivity
  gcongr

/-- `I₀` is strictly increasing in `x²`. -/
@[tmio T, powerlib_foundation] theorem realI0_lt_realI0 {x y : ℝ} (h : x ^ 2 < y ^ 2) :
    realI0 x < realI0 y := by
  have hx : 0 ≤ x ^ 2 / 4 := by positivity
  refine Summable.tsum_lt_tsum (i := 1) (fun k => ?_) ?_ (summable_realI0 x) (summable_realI0 y)
  · gcongr
  · simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_pow, div_one]
    linarith

/-- The Kaiser shape on the normalized position `u ∈ [−1, 1]`:
`I₀(β √(1 − u²)) / I₀(β)`. -/
def kaiserShape (β u : ℝ) : ℝ := realI0 (β * √(1 - u ^ 2)) / realI0 β

/-- The Kaiser window of length `N`: `w[k] = I₀(β √(1 − (2k/(N−1) − 1)²)) / I₀(β)`. -/
def kaiser (β : ℝ) (N k : ℕ) : ℝ := kaiserShape β (2 * k / ((N : ℝ) - 1) - 1)

@[tmio T, powerlib_foundation] theorem kaiserShape_neg (β u : ℝ) :
    kaiserShape β (-u) = kaiserShape β u := by
  simp only [kaiserShape, neg_sq]

/-- Unit value at the centre. -/
@[tmio T, powerlib_foundation] theorem kaiserShape_zero (β : ℝ) : kaiserShape β 0 = 1 := by
  rw [kaiserShape, show (1 : ℝ) - 0 ^ 2 = 1 by norm_num, Real.sqrt_one, mul_one,
    div_self (realI0_pos β).ne']

@[tmio T, powerlib_foundation] theorem kaiserShape_pos (β u : ℝ) : 0 < kaiserShape β u :=
  div_pos (realI0_pos _) (realI0_pos β)

/-- The shape never exceeds its central value `1` (any real `β`, any position). -/
@[tmio T, powerlib_foundation] theorem kaiserShape_le_one (β u : ℝ) : kaiserShape β u ≤ 1 := by
  rw [kaiserShape, div_le_one (realI0_pos β)]
  apply realI0_le_realI0
  have h0 : 0 ≤ √(1 - u ^ 2) := Real.sqrt_nonneg _
  have h1 : √(1 - u ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg u])
  rw [mul_pow]
  have : √(1 - u ^ 2) ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg β]

/-- For `β ≠ 0` the shape decreases strictly from the centre to the edge, on `[0, 1]`. -/
@[tmio T, powerlib_foundation] theorem kaiserShape_strictAntiOn {β : ℝ} (hβ : β ≠ 0) :
    StrictAntiOn (kaiserShape β) (Set.Icc 0 1) := by
  intro u hu u' hu' h
  rw [kaiserShape, kaiserShape]
  refine div_lt_div_of_pos_right (realI0_lt_realI0 ?_) (realI0_pos β)
  have e1 : 0 ≤ 1 - u' ^ 2 := by nlinarith [hu'.1, hu'.2]
  have e2 : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  rw [mul_pow, mul_pow, Real.sq_sqrt e1, Real.sq_sqrt e2]
  have hb : 0 < β ^ 2 := by positivity
  have : u ^ 2 < u' ^ 2 := by nlinarith [hu.1]
  nlinarith

/-- `β = 0` is the rectangular window. -/
@[tmio T, powerlib_foundation] theorem kaiserShape_rect (u : ℝ) : kaiserShape 0 u = 1 := by
  rw [kaiserShape, zero_mul, div_self (realI0_pos 0).ne']

/-- Symmetry `w[N − 1 − k] = w[k]`. -/
@[tmio T, powerlib_foundation] theorem kaiser_symm (β : ℝ) {N k : ℕ} (hk : k ≤ N - 1) :
    kaiser β N (N - 1 - k) = kaiser β N k := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : k = 0 := by omega
    subst this; rfl
  rw [kaiser, kaiser]
  have hc : ((N - 1 - k : ℕ) : ℝ) = (N : ℝ) - 1 - k := by
    rw [Nat.cast_sub hk, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hc]
  rcases eq_or_ne ((N : ℝ) - 1) 0 with h0 | h0
  · rw [h0, div_zero, div_zero]
  · rw [show 2 * ((N : ℝ) - 1 - k) / ((N : ℝ) - 1) - 1 = -(2 * k / ((N : ℝ) - 1) - 1) by
      field_simp; ring, kaiserShape_neg]

@[tmio T, powerlib_foundation] theorem kaiser_pos (β : ℝ) (N k : ℕ) : 0 < kaiser β N k :=
  kaiserShape_pos _ _

@[tmio T, powerlib_foundation] theorem kaiser_le_one (β : ℝ) (N k : ℕ) : kaiser β N k ≤ 1 :=
  kaiserShape_le_one _ _

/-- For odd length `N = 2M + 1 ≥ 3` the centre sample is the maximum `1`. -/
@[tmio T, powerlib_foundation] theorem kaiser_center (β : ℝ) {M : ℕ} (hM : M ≠ 0) :
    kaiser β (2 * M + 1) M = 1 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  rw [kaiser, show (((2 * M + 1 : ℕ) : ℝ) - 1) = 2 * M by push_cast; ring,
    show 2 * (M : ℝ) / (2 * M) - 1 = 0 by field_simp; ring, kaiserShape_zero]

/-- For `β ≠ 0` the window increases strictly on the left half: `k < k'`, `2k' ≤ N − 1`. -/
@[tmio T, powerlib_foundation] theorem kaiser_lt_of_lt_left {β : ℝ} (hβ : β ≠ 0) {N k k' : ℕ}
    (hkk : k < k') (hk' : 2 * k' ≤ N - 1) : kaiser β N k < kaiser β N k' := by
  have hN : (3 : ℝ) ≤ N := by exact_mod_cast (show 3 ≤ N by omega)
  have hD : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hk'R : 2 * (k' : ℝ) ≤ (N : ℝ) - 1 := by
    have : ((2 * k' : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hk'
    rw [Nat.cast_sub (by omega), Nat.cast_one] at this
    push_cast at this
    exact this
  have hkkR : (k : ℝ) < k' := by exact_mod_cast hkk
  rw [kaiser, kaiser, ← kaiserShape_neg β (2 * k / ((N : ℝ) - 1) - 1),
    ← kaiserShape_neg β (2 * k' / ((N : ℝ) - 1) - 1)]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine kaiserShape_strictAntiOn hβ ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_
  · rw [neg_nonneg, sub_nonpos, div_le_one hD]; linarith
  · rw [neg_le, le_sub_iff_add_le]; norm_num; positivity
  · rw [neg_nonneg, sub_nonpos, div_le_one hD]; linarith
  · rw [neg_le, le_sub_iff_add_le]; norm_num; positivity
  · rw [neg_lt_neg_iff, sub_lt_sub_iff_right]
    exact div_lt_div_of_pos_right (by linarith) hD

/-- For `β ≠ 0` the window decreases strictly on the right half: `N − 1 ≤ 2k`, `k < k' ≤ N − 1`. -/
@[tmio T, powerlib_foundation] theorem kaiser_lt_of_lt_right {β : ℝ} (hβ : β ≠ 0) {N k k' : ℕ}
    (hk : N - 1 ≤ 2 * k) (hkk : k < k') (hk' : k' ≤ N - 1) : kaiser β N k' < kaiser β N k := by
  rw [← kaiser_symm β hk', ← kaiser_symm β (hkk.le.trans hk')]
  exact kaiser_lt_of_lt_left hβ (by omega) (by omega)

/-- For every `β` the shape is non-increasing from the centre to the edge, on `[0, 1]`. -/
@[tmio T, powerlib_foundation] theorem kaiserShape_antitoneOn (β : ℝ) :
    AntitoneOn (kaiserShape β) (Set.Icc 0 1) := by
  intro u hu u' hu' h
  rw [kaiserShape, kaiserShape]
  refine div_le_div_of_nonneg_right (realI0_le_realI0 ?_) (realI0_pos β).le
  have e1 : 0 ≤ 1 - u' ^ 2 := by nlinarith [hu'.1, hu'.2]
  have e2 : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  rw [mul_pow, mul_pow, Real.sq_sqrt e1, Real.sq_sqrt e2]
  have : u ^ 2 ≤ u' ^ 2 := by nlinarith [hu.1]
  nlinarith [sq_nonneg β]

/-- For every `β` the window is non-decreasing on the left half: `k ≤ k'`, `2k' ≤ N − 1`. -/
@[tmio T, powerlib_foundation] theorem kaiser_le_of_le_left (β : ℝ) {N k k' : ℕ}
    (hkk : k ≤ k') (hk' : 2 * k' ≤ N - 1) : kaiser β N k ≤ kaiser β N k' := by
  rcases hkk.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hN : (3 : ℝ) ≤ N := by exact_mod_cast (show 3 ≤ N by omega)
  have hD : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hk'R : 2 * (k' : ℝ) ≤ (N : ℝ) - 1 := by
    have : ((2 * k' : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hk'
    rw [Nat.cast_sub (by omega), Nat.cast_one] at this
    push_cast at this
    exact this
  have hkkR : (k : ℝ) ≤ k' := by exact_mod_cast hkk
  rw [kaiser, kaiser, ← kaiserShape_neg β (2 * k / ((N : ℝ) - 1) - 1),
    ← kaiserShape_neg β (2 * k' / ((N : ℝ) - 1) - 1)]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine kaiserShape_antitoneOn β ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_
  · rw [neg_nonneg, sub_nonpos, div_le_one hD]; linarith
  · rw [neg_le, le_sub_iff_add_le]; norm_num; positivity
  · rw [neg_nonneg, sub_nonpos, div_le_one hD]; linarith
  · rw [neg_le, le_sub_iff_add_le]; norm_num; positivity
  · rw [neg_le_neg_iff, sub_le_sub_iff_right]
    exact div_le_div_of_nonneg_right (by linarith) hD.le

/-- For every `β` the window is non-increasing on the right half: `N − 1 ≤ 2k`, `k ≤ k' ≤ N − 1`. -/
@[tmio T, powerlib_foundation] theorem kaiser_le_of_le_right (β : ℝ) {N k k' : ℕ}
    (hk : N - 1 ≤ 2 * k) (hkk : k ≤ k') (hk' : k' ≤ N - 1) : kaiser β N k' ≤ kaiser β N k := by
  rw [← kaiser_symm β hk', ← kaiser_symm β (hkk.trans hk')]
  exact kaiser_le_of_le_left β (by omega) (by omega)

/-- The total variation of the Kaiser window of odd length `2M + 1 ≥ 3` is `2 − 2 w[0]`: it rises
from `w[0] = 1/I₀(β)` to `1` at the centre and falls back symmetrically. -/
@[tmio T, powerlib_foundation] theorem kaiser_variation (β : ℝ) {M : ℕ} (hM : M ≠ 0) :
    ∑ k ∈ range (2 * M), |kaiser β (2 * M + 1) (k + 1) - kaiser β (2 * M + 1) k| =
      2 - 2 * kaiser β (2 * M + 1) 0 := by
  set w := kaiser β (2 * M + 1)
  rw [two_mul, sum_range_add]
  have h1 : ∑ k ∈ range M, |w (k + 1) - w k| = w M - w 0 := by
    rw [← sum_range_sub w M]
    refine sum_congr rfl fun k hk => abs_of_nonneg (sub_nonneg.mpr ?_)
    exact kaiser_le_of_le_left β (Nat.le_succ k) (by have := mem_range.mp hk; omega)
  have h2 : ∑ k ∈ range M, |w (M + k + 1) - w (M + k)| = w M - w (M + M) := by
    have := sum_range_sub' (fun k => w (M + k)) M
    simp only [add_zero] at this
    rw [← this]
    refine sum_congr rfl fun k hk => ?_
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ?_)]
    · rfl
    · exact kaiser_le_of_le_right β (by omega) (Nat.le_succ _) (by have := mem_range.mp hk; omega)
  rw [h1, h2, show w (M + M) = w 0 by
    rw [show M + M = 2 * M + 1 - 1 - 0 by omega]; exact kaiser_symm β (by omega),
    show w M = 1 from kaiser_center β hM]
  ring

/-- **Kaiser leakage.** For odd length `2M + 1 ≥ 3` and `sin(ν/2) ≠ 0`, the Kaiser window
transform satisfies `|W(ν)| ≤ (2 − 1/I₀(β)) / |sin(ν/2)|`, independently of `N` (whereas
`W(0) = Σ w[k]`), so the image leakage relative to the main lobe is `O(1/N)`. -/
@[tmio T, powerlib_foundation] theorem norm_winTF_kaiser_le (β : ℝ) {M : ℕ} (hM : M ≠ 0) {ν : ℝ}
    (hs : Real.sin (ν / 2) ≠ 0) :
    ‖winTF (fun k => (kaiser β (2 * M + 1) k : ℂ)) (2 * M + 1) ν‖ ≤
      (2 - 1 / realI0 β) / |Real.sin (ν / 2)| := by
  refine (norm_winTF_le_variation _ _ hs).trans (div_le_div_of_nonneg_right ?_ (abs_nonneg _))
  have hv := kaiser_variation β hM
  have h0 : kaiser β (2 * M + 1) 0 = 1 / realI0 β := by
    rw [kaiser, show 2 * ((0 : ℕ) : ℝ) / (((2 * M + 1 : ℕ) : ℝ) - 1) - 1 = -1 by simp,
      kaiserShape, show (1 : ℝ) - (-1) ^ 2 = 0 by norm_num, Real.sqrt_zero, mul_zero, realI0_zero]
  have hlast : kaiser β (2 * M + 1) (2 * M + 1 - 1) = kaiser β (2 * M + 1) 0 := by
    rw [show 2 * M + 1 - 1 = 2 * M + 1 - 1 - 0 by omega]; exact kaiser_symm β (by omega)
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [show 2 * M + 1 - 1 = 2 * M by omega] at hlast ⊢
  rw [hlast, hv, abs_of_pos (kaiser_pos _ _ _), h0]
  linarith

/-- Every Kaiser sample is at least its edge value `1/I₀(β)`. -/
@[tmio T, powerlib_foundation] theorem one_div_le_kaiser (β : ℝ) (N k : ℕ) :
    1 / realI0 β ≤ kaiser β N k :=
  div_le_div_of_nonneg_right (one_le_realI0 _) (realI0_pos β).le

/-- The main lobe of the Kaiser window grows linearly with the length:
`|W(0)| = Σ_k w[k] ≥ N/I₀(β)`. -/
@[tmio T, powerlib_foundation] theorem norm_winTF_kaiser_zero (β : ℝ) (N : ℕ) :
    N / realI0 β ≤ ‖winTF (fun k => (kaiser β N k : ℂ)) N 0‖ := by
  have h : winTF (fun k => (kaiser β N k : ℂ)) N 0 = ((∑ k ∈ range N, kaiser β N k : ℝ) : ℂ) := by
    simp [winTF]
  rw [h, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg fun k _ => (kaiser_pos β N k).le)]
  calc (N : ℝ) / realI0 β = ∑ k ∈ range N, 1 / realI0 β := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ _ := sum_le_sum fun k _ => one_div_le_kaiser β N k

/-- **Kaiser cross-spectrum leakage.** For odd length `2M + 1 ≥ 3`, a real sinusoid
`Re(a e^{jΩk})` at any frequency and `sin((Ω + Ω_b)/2) ≠ 0`:
`|S| ≤ |a|² |W(Ω − Ω_b)| (2 − 1/I₀(β)) / |sin((Ω + Ω_b)/2)|`. -/
@[tmio T, powerlib_foundation] theorem norm_wcsd_kaiser_le (β : ℝ) {M : ℕ} (hM : M ≠ 0)
    {Ωb Ω : ℝ} (hs : Real.sin ((Ω + Ωb) / 2) ≠ 0) (a : ℂ) (k₀ Δk : ℤ) :
    ‖wcsd (fun k => (kaiser β (2 * M + 1) k : ℂ)) (2 * M + 1) Ωb
        (fun k => (((a * cexp (Ω * (k : ℂ) * I)).re : ℝ) : ℂ)) k₀ Δk‖ ≤
      ‖a‖ ^ 2 * ‖winTF (fun k => (kaiser β (2 * M + 1) k : ℂ)) (2 * M + 1) (Ω - Ωb)‖ *
        ((2 - 1 / realI0 β) / |Real.sin ((Ω + Ωb) / 2)|) := by
  refine (norm_wcsd_realSin_le _ _ Ωb Ω a k₀ Δk).trans ?_
  rw [show -Ω - Ωb = -(Ω + Ωb) by ring,
    norm_winTF_neg (fun k => Complex.conj_ofReal _)]
  gcongr
  exact norm_winTF_kaiser_le β hM hs

/-- The Kaiser window is real, so `|W(−ν)| = |W(ν)|` applies (`norm_winTF_neg`). -/
@[tmio T, powerlib_foundation] theorem kaiser_conj (β : ℝ) (N k : ℕ) :
    (starRingEnd ℂ) ((kaiser β N k : ℝ) : ℂ) = ((kaiser β N k : ℝ) : ℂ) :=
  Complex.conj_ofReal _

end powerlib.Signal.Window
