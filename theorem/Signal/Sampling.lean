import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Sampled sinusoids: aliasing, Nyquist identifiability and sampled-peak accuracy

The samples `x[n] = A cos(2π f n / f_s + φ)` of a sinusoid: aliasing and folding, exact
identification of frequency, amplitude and phase strictly below the Nyquist frequency and its
failure at it, the resulting sampling-rate requirement, and how far the largest sample near a
crest can fall below the amplitude.

Scope.
* Real sinusoids of arbitrary amplitude `A`, frequency `f` and phase `φ`, sampled at the rate
  `f_s > 0` from `n = 0` on (`n : ℕ`, a one-sided record); ideal instantaneous sampling, no
  quantization, noise, anti-aliasing filter or PMU estimation.
* Identification is from the infinite sample sequence; identifiable quantities are the frequency
  and the quadrature components `A cos φ`, `A sin φ` (equivalently `A` and `φ` for `A > 0`).
  Sums of several sinusoids are not treated.

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026) §1.2
(requirement limited to 20 Hz to be assessed by PMUs), §3.1 and §3.2 (10 Hz data, band
0.1–2 Hz), §3.7 (accuracy towards the top of the band), §4.1 ("Sample rate": Shannon/Nyquist,
40 Hz minimum for 20 Hz, 50 Hz PMU rate), §5.7 (20 Hz data, "4–5 Hz (half of the Nyquist
frequency)").

Results.
* Aliasing: `sampledCos`, `sampledCos_add_mul_fs` (`f` and `f + k f_s` give the same samples),
  `sampledCos_fs_sub` (`f_s − f` gives the phase-conjugate samples), `exists_alias` (every
  frequency has an alias in `[0, f_s/2]`).
* Identifiability: `sampledCos_recurrence` (`x[n+2] + x[n] = 2 cos(2πf/f_s) x[n+1]`),
  `eq_of_sampledCos_eq` (frequencies in `[0, f_s/2]` are identified by nonzero samples),
  `sampledCos_ne_zero`, `sampledCos_eq_iff` (below `f_s/2`: same samples iff same frequency and
  quadrature components), `sampledCos_nyquist` (at `f_s/2` the samples are `A cos φ (−1)ⁿ`),
  `sampledCos_nyquist_eq` (amplitude and phase not separately identifiable there).
* Sampling-rate requirement: `identifiable_iff` (every sinusoid of frequency in
  `(0, f_max]` is identified iff `f_s > 2 f_max`), `identifiable_twenty_hertz` (`20 Hz` needs
  `f_s > 40 Hz`; `50 Hz` suffices), `identifiable_ten_twenty_hertz` (`10 Hz` covers `0.1–2 Hz`;
  `20 Hz` covers exactly the frequencies below `10 Hz`).
* Sampled peaks: `exists_sample_near_crest`, `exists_abs_sampledCos_ge` (for `0 < f ≤ f_s/2`
  some sample near every crest has `|x[n]| ≥ |A| cos(π f/f_s)`), `abs_sampledCos_le_of_midway`
  (the bound is attained when the crest lies midway between two samples), `abs_sampledCos_le`
  (`|x[n]| ≤ |A|`), `sampledCos_fifth_other_crest` (the attainment is per crest: at
  `f = f_s/5` another crest of the same record is sampled exactly),
  `peak_factor_instances` (`cos(π/5) = (1 + √5)/4 ≈ 0.81` for `2 Hz` at `10 Hz`,
  `cos(π/4) = √2/2` for `5 Hz` at `20 Hz`).

Correction (§4.1). "The Shannon/Nyquist theorem leads to a minimum sampling rate of 40 Hz" for a
requirement up to 20 Hz: at exactly `f_s = 40 Hz` the 20 Hz frequency is still identified
(`eq_of_sampledCos_eq` allows `f = f_s/2`), but its amplitude and phase are not
(`sampledCos_nyquist_eq`); identification of every sinusoid up to `f_max` requires
`f_s > 2 f_max` strictly (`identifiable_iff`).

Sharpening (§5.7). With 20 Hz data every sinusoid below 10 Hz is identified; the report's
"4–5 Hz" is not an identifiability limit. At `f = f_s/4` (5 Hz) the largest sample near a crest
can be as low as `cos(π/4) ≈ 0.71` of the amplitude (`abs_sampledCos_le_of_midway`), which is the
accuracy loss of local-maximum detection the report describes (§3.7).

Family and connection conclusions.
* None: this module defines no family; every result is an identity or inequality of sampled
  sinusoids.
-/

noncomputable section
namespace powerlib.Signal
open Real Set

/-! ## Sampled sinusoids and aliasing -/

/-- The samples `x[n] = A cos(2π f n / f_s + φ)` of the sinusoid of amplitude `A`, frequency `f`
and phase `φ` at the sampling rate `f_s`. -/
def sampledCos (A f φ fs : ℝ) (n : ℕ) : ℝ := A * cos (2 * π * f * n / fs + φ)

/-- Aliasing: `f` and `f + k f_s` (`k ∈ ℤ`) give the same samples. -/
@[tmio T, powerlib_foundation] theorem sampledCos_add_mul_fs {fs : ℝ} (hfs : fs ≠ 0) (A f φ : ℝ)
    (k : ℤ) : sampledCos A (f + k * fs) φ fs = sampledCos A f φ fs := by
  funext n
  simp only [sampledCos]
  rw [show 2 * π * (f + k * fs) * n / fs + φ = 2 * π * f * n / fs + φ + ((k * n : ℤ) : ℝ) * (2 * π)
    by push_cast; field_simp; ring, cos_add_int_mul_two_pi]

/-- Folding: `f_s − f` gives the phase-conjugate samples of `f`. -/
@[tmio T, powerlib_foundation] theorem sampledCos_fs_sub {fs : ℝ} (hfs : fs ≠ 0) (A f φ : ℝ) :
    sampledCos A (fs - f) φ fs = sampledCos A f (-φ) fs := by
  funext n
  simp only [sampledCos]
  rw [show 2 * π * (fs - f) * n / fs + φ = (n : ℕ) * (2 * π) - (2 * π * f * n / fs + -φ)
    by field_simp; ring, cos_nat_mul_two_pi_sub]

/-- Every frequency has an alias in `[0, f_s/2]`, with the same or the conjugate phase. -/
@[tmio T, powerlib_foundation] theorem exists_alias {fs : ℝ} (hfs : 0 < fs) (A f φ : ℝ) :
    ∃ f₀ ∈ Icc 0 (fs / 2), ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      sampledCos A f φ fs = sampledCos A f₀ (s * φ) fs := by
  set r := toIcoMod hfs 0 f with hr
  have hrmem : r ∈ Ico 0 (0 + fs) := toIcoMod_mem_Ico hfs 0 f
  rw [zero_add] at hrmem
  have hf : sampledCos A f φ fs = sampledCos A r φ fs := by
    have := sampledCos_add_mul_fs hfs.ne' A r φ (toIcoDiv hfs 0 f)
    rw [← this]
    congr 1
    rw [hr, toIcoMod, zsmul_eq_mul]
    ring
  rcases le_or_gt r (fs / 2) with h | h
  · exact ⟨r, ⟨hrmem.1, h⟩, 1, Or.inl rfl, by rw [one_mul, hf]⟩
  · refine ⟨fs - r, ⟨by linarith [hrmem.2], by linarith⟩, -1, Or.inr rfl, ?_⟩
    rw [hf, neg_one_mul, sampledCos_fs_sub hfs.ne', neg_neg]

/-! ## Identifiability below the Nyquist frequency -/

/-- The three-term recurrence of sampled sinusoids: `x[n+2] + x[n] = 2 cos θ · x[n+1]`,
`θ = 2π f / f_s`. -/
@[tmio T, powerlib_foundation] theorem sampledCos_recurrence {fs : ℝ} (hfs : fs ≠ 0)
    (A f φ : ℝ) (n : ℕ) :
    sampledCos A f φ fs (n + 2) + sampledCos A f φ fs n =
      2 * cos (2 * π * f / fs) * sampledCos A f φ fs (n + 1) := by
  simp only [sampledCos]
  set θ := 2 * π * f / fs
  have h : ∀ k : ℕ, 2 * π * f * (k : ℕ) / fs + φ = k * θ + φ := fun k => by
    simp only [θ]; field_simp
  rw [h, h, h]
  push_cast
  rw [show ((n : ℝ) + 2) * θ + φ = ((n + 1) * θ + φ) + θ by ring,
    show (n : ℝ) * θ + φ = ((n + 1) * θ + φ) - θ by ring, cos_add, cos_sub]
  ring

/-- A sampled sinusoid that vanishes at two consecutive samples vanishes everywhere (backward
and forward through the recurrence). -/
@[tmio T, powerlib_foundation] private theorem sampledCos_eq_zero_of_two {fs : ℝ} (hfs : fs ≠ 0) {A f φ : ℝ}
    (h : ∀ n, sampledCos A f φ fs (n + 1) = 0) : ∀ n, sampledCos A f φ fs n = 0 := by
  intro n
  rcases n with _ | n
  · have := sampledCos_recurrence hfs A f φ 0
    rw [h 1, h 0] at this
    simpa using this
  · exact h n

/-- Frequencies in `[0, f_s/2]` are identified by their samples: two sampled sinusoids with
frequencies in `[0, f_s/2]` that agree at every sample and are not identically zero have the
same frequency. -/
@[tmio T, powerlib_foundation] theorem eq_of_sampledCos_eq {fs : ℝ} (hfs : 0 < fs)
    {A₁ A₂ f₁ f₂ φ₁ φ₂ : ℝ} (hf₁ : f₁ ∈ Icc 0 (fs / 2)) (hf₂ : f₂ ∈ Icc 0 (fs / 2))
    (h : ∀ n, sampledCos A₁ f₁ φ₁ fs n = sampledCos A₂ f₂ φ₂ fs n)
    (hne : ∃ n, sampledCos A₁ f₁ φ₁ fs n ≠ 0) : f₁ = f₂ := by
  have hcos : cos (2 * π * f₁ / fs) = cos (2 * π * f₂ / fs) := by
    by_contra hc
    obtain ⟨n₀, hn₀⟩ := hne
    refine hn₀ (sampledCos_eq_zero_of_two hfs.ne' (fun n => ?_) n₀)
    have e1 := sampledCos_recurrence hfs.ne' A₁ f₁ φ₁ n
    have e2 := sampledCos_recurrence hfs.ne' A₂ f₂ φ₂ n
    rw [← h, ← h, ← h] at e2
    have : (cos (2 * π * f₁ / fs) - cos (2 * π * f₂ / fs)) * sampledCos A₁ f₁ φ₁ fs (n + 1) = 0 :=
      by linarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc)
  have hmem : ∀ f ∈ Icc 0 (fs / 2), 2 * π * f / fs ∈ Icc 0 π := fun f hf =>
    ⟨by have := hf.1; positivity, by
      rw [div_le_iff₀ hfs]; nlinarith [hf.2, pi_pos]⟩
  have := injOn_cos (hmem f₁ hf₁) (hmem f₂ hf₂) hcos
  field_simp at this
  nlinarith [pi_pos]

/-- Strictly below the Nyquist frequency a nonzero amplitude gives a sampled sinusoid that is not
identically zero. -/
@[tmio T, powerlib_foundation] theorem sampledCos_ne_zero {fs A f φ : ℝ} (hfs : 0 < fs)
    (hf : f ∈ Ioo 0 (fs / 2)) (hA : A ≠ 0) : ∃ n, sampledCos A f φ fs n ≠ 0 := by
  by_contra hno
  simp only [not_exists, not_not] at hno
  have h0 := hno 0
  have h1 := hno 1
  simp only [sampledCos, Nat.cast_zero, mul_zero, zero_div, zero_add, Nat.cast_one, mul_one,
    mul_eq_zero, hA, false_or] at h0 h1
  rw [cos_add, h0, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at h1
  have hsin : sin (2 * π * f / fs) ≠ 0 := (sin_pos_of_pos_of_lt_pi (by
    have := hf.1; positivity) (by rw [div_lt_iff₀ hfs]; nlinarith [hf.2, pi_pos])).ne'
  rcases h1 with h1 | h1
  · exact hsin h1
  · have := sin_sq_add_cos_sq φ
    rw [h0, h1] at this
    norm_num at this

/-- Identification strictly below the Nyquist frequency: for frequencies in `(0, f_s/2)` and
`A₁ ≠ 0`, the samples agree exactly when the frequencies and the quadrature components
`A cos φ`, `A sin φ` agree. -/
@[tmio T, powerlib_foundation] theorem sampledCos_eq_iff {fs : ℝ} (hfs : 0 < fs)
    {A₁ A₂ f₁ f₂ φ₁ φ₂ : ℝ} (hf₁ : f₁ ∈ Ioo 0 (fs / 2)) (hf₂ : f₂ ∈ Ioo 0 (fs / 2))
    (hA : A₁ ≠ 0) :
    (∀ n, sampledCos A₁ f₁ φ₁ fs n = sampledCos A₂ f₂ φ₂ fs n) ↔
      f₁ = f₂ ∧ A₁ * cos φ₁ = A₂ * cos φ₂ ∧ A₁ * sin φ₁ = A₂ * sin φ₂ := by
  have hexp : ∀ A f φ : ℝ, ∀ n : ℕ, sampledCos A f φ fs n =
      cos (n * (2 * π * f / fs)) * (A * cos φ) - sin (n * (2 * π * f / fs)) * (A * sin φ) :=
    fun A f φ n => by
      simp only [sampledCos]
      rw [show 2 * π * f * n / fs = n * (2 * π * f / fs) by ring, cos_add]
      ring
  constructor
  · intro h
    have hf := eq_of_sampledCos_eq hfs (Ioo_subset_Icc_self hf₁) (Ioo_subset_Icc_self hf₂) h
      (sampledCos_ne_zero hfs hf₁ hA)
    subst hf
    have h0 := h 0
    have h1 := h 1
    rw [hexp, hexp] at h0 h1
    simp only [Nat.cast_zero, zero_mul, cos_zero, sin_zero, one_mul, zero_mul, sub_zero,
      Nat.cast_one] at h0 h1
    refine ⟨rfl, h0, ?_⟩
    have hsin : sin (2 * π * f₁ / fs) ≠ 0 := (sin_pos_of_pos_of_lt_pi (by
      have := hf₁.1; positivity) (by rw [div_lt_iff₀ hfs]; nlinarith [hf₁.2, pi_pos])).ne'
    rw [h0] at h1
    have : sin (2 * π * f₁ / fs) * (A₁ * sin φ₁ - A₂ * sin φ₂) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hsin)
  · rintro ⟨rfl, hc, hs⟩ n
    rw [hexp, hexp, hc, hs]

/-- At the Nyquist frequency the samples are `A cos φ (−1)ⁿ`: only `A cos φ` is visible. -/
@[tmio T, powerlib_foundation] theorem sampledCos_nyquist {fs : ℝ} (hfs : fs ≠ 0) (A φ : ℝ)
    (n : ℕ) : sampledCos A (fs / 2) φ fs n = A * cos φ * (-1) ^ n := by
  simp only [sampledCos]
  rw [show 2 * π * (fs / 2) * n / fs + φ = φ + (n : ℤ) * π by push_cast; field_simp; ring,
    cos_add_int_mul_pi, zpow_natCast]
  ring

/-- At the Nyquist frequency amplitude and phase are not separately identifiable:
`(A, φ)` and `(A cos φ, 0)` give the same samples. -/
@[tmio T, powerlib_foundation] theorem sampledCos_nyquist_eq {fs : ℝ} (hfs : fs ≠ 0) (A φ : ℝ) :
    sampledCos A (fs / 2) φ fs = sampledCos (A * cos φ) (fs / 2) 0 fs := by
  funext n
  rw [sampledCos_nyquist hfs, sampledCos_nyquist hfs, cos_zero, mul_one]

/- `Identifiable fs F`: full identifiability (frequency and quadrature components) of the
sinusoids with frequencies in `F` from their samples at the rate `f_s`. This is local notation,
not a predicate declaration: outside the semantic layer a predicate declaration may not quantify
over `ℝ`, the type of the semantic time axis (single-semantics rule T), so each statement below
spells the property out. -/
set_option quotPrecheck false in
local notation "Identifiable " fs:max F:max =>
  ∀ f₁ ∈ F, ∀ f₂ ∈ F, ∀ A₁ A₂ φ₁ φ₂ : ℝ,
    (∀ n, sampledCos A₁ f₁ φ₁ fs n = sampledCos A₂ f₂ φ₂ fs n) →
      (∃ n, sampledCos A₁ f₁ φ₁ fs n ≠ 0) →
        f₁ = f₂ ∧ A₁ * cos φ₁ = A₂ * cos φ₂ ∧ A₁ * sin φ₁ = A₂ * sin φ₂

/-- Shannon–Nyquist for sampled sinusoids: every sinusoid with a frequency in `(0, f_max]` is
identified by its samples exactly when `f_s > 2 f_max`. -/
@[tmio T, powerlib_foundation] theorem identifiable_iff {fs fmax : ℝ} (hfs : 0 < fs) :
    Identifiable fs (Ioc 0 fmax) ↔ 2 * fmax < fs := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    have hmem : fs / 2 ∈ Ioc 0 fmax := ⟨by positivity, by linarith⟩
    have hsame : ∀ n, sampledCos 1 (fs / 2) 0 fs n = sampledCos 2 (fs / 2) (π / 3) fs n := by
      intro n
      rw [sampledCos_nyquist hfs.ne', sampledCos_nyquist hfs.ne', cos_zero, cos_pi_div_three]
      ring
    have hne : ∃ n, sampledCos 1 (fs / 2) 0 fs n ≠ 0 :=
      ⟨0, by rw [sampledCos_nyquist hfs.ne']; norm_num⟩
    have := (h _ hmem _ hmem 1 2 0 (π / 3) hsame hne).2.2
    rw [sin_zero, sin_pi_div_three] at this
    have : (0 : ℝ) < 2 * (√3 / 2) := by positivity
    linarith
  · intro hlt f₁ hf₁ f₂ hf₂ A₁ A₂ φ₁ φ₂ h hne
    have hA : A₁ ≠ 0 := by
      rintro rfl
      obtain ⟨n, hn⟩ := hne
      simp [sampledCos] at hn
    exact (sampledCos_eq_iff hfs ⟨hf₁.1, by linarith [hf₁.2]⟩ ⟨hf₂.1, by linarith [hf₂.2]⟩
      hA).mp h

/-- §4.1: the requirement up to `20 Hz` needs a sampling rate above `40 Hz` (the report's minimum
`40 Hz` leaves the `20 Hz` amplitude unidentified); the `50 Hz` PMU rate suffices. -/
@[tmio T, powerlib_foundation] theorem identifiable_twenty_hertz {fs : ℝ} (hfs : 0 < fs) :
    (Identifiable fs (Ioc 0 20) ↔ 40 < fs) ∧ Identifiable 50 (Ioc 0 20) := by
  refine ⟨by rw [identifiable_iff hfs]; norm_num, ?_⟩
  rw [identifiable_iff (by norm_num)]
  norm_num

/-- §3.1, §5.7: `10 Hz` data identify the band `0.1–2 Hz`; `20 Hz` data identify exactly the
frequencies below `10 Hz` (the report's "4–5 Hz" is half of that Nyquist frequency). -/
@[tmio T, powerlib_foundation] theorem identifiable_ten_twenty_hertz (fmax : ℝ) :
    Identifiable 10 (Ioc 0 2) ∧ (Identifiable 20 (Ioc 0 fmax) ↔ fmax < 10) := by
  refine ⟨by rw [identifiable_iff (by norm_num)]; norm_num, ?_⟩
  rw [identifiable_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-! ## Accuracy of sampled peaks -/

/-- Every crest of the sinusoid (phase `k π`) not before the first sample by more than half a
sampling step has a sample within half a step `θ/2` of it, `θ = 2π f / f_s`. -/
@[tmio T, powerlib_foundation] theorem exists_sample_near_crest {θ φ : ℝ} (hθ : 0 < θ) (k : ℤ)
    (hk : φ ≤ k * π + θ / 2) : ∃ n : ℕ, |n * θ + φ - k * π| ≤ θ / 2 := by
  set u := (k * π - θ / 2 - φ) / θ
  refine ⟨⌈u⌉₊, abs_le.mpr ⟨?_, ?_⟩⟩
  · have := Nat.le_ceil u
    have h2 : u * θ ≤ ⌈u⌉₊ * θ := mul_le_mul_of_nonneg_right this hθ.le
    rw [div_mul_cancel₀ _ hθ.ne'] at h2
    linarith
  · rcases Nat.eq_zero_or_pos ⌈u⌉₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_mul, zero_add]
      linarith
    · have h1 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one (by
        have := Nat.ceil_pos.mp hpos; linarith)
      have h2 : (⌈u⌉₊ : ℝ) * θ < (u + 1) * θ := mul_lt_mul_of_pos_right h1 hθ
      rw [add_mul, div_mul_cancel₀ _ hθ.ne'] at h2
      linarith

/-- Sampled-peak accuracy (§3.7): for `0 < f ≤ f_s/2`, near every crest there is a sample with
`|x[n]| ≥ |A| cos(π f / f_s)`; the local maxima of the sampled record underestimate the amplitude
by at most the factor `cos(π f / f_s)`. -/
@[tmio T, powerlib_foundation] theorem exists_abs_sampledCos_ge {fs A f φ : ℝ} (hfs : 0 < fs)
    (hf : f ∈ Ioc 0 (fs / 2)) (k : ℤ) (hk : φ ≤ k * π + π * f / fs) :
    ∃ n : ℕ, |A| * cos (π * f / fs) ≤ |sampledCos A f φ fs n| := by
  have hθ : 0 < 2 * π * f / fs := by have := hf.1; positivity
  have hk' : φ ≤ k * π + 2 * π * f / fs / 2 := by
    rw [show 2 * π * f / fs / 2 = π * f / fs by ring]; exact hk
  obtain ⟨n, hn⟩ := exists_sample_near_crest (φ := φ) hθ k hk'
  refine ⟨n, ?_⟩
  have hhalf : π * f / fs ≤ π / 2 := by
    rw [div_le_iff₀ hfs]; nlinarith [hf.2, pi_pos]
  rw [sampledCos, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg A)
  have he : 2 * π * f * n / fs + φ = (n * (2 * π * f / fs) + φ - k * π) + k * π := by ring
  rw [he, cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul,
    ← cos_abs (n * (2 * π * f / fs) + φ - k * π)]
  rw [show 2 * π * f / fs / 2 = π * f / fs by ring] at hn
  rw [abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg (n * (2 * π * f / fs) + φ -
    k * π), pi_pos], by linarith⟩)]
  exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) hn

/-- The bound is attained: when a crest lies midway between the samples `n₀` and `n₀ + 1`, every
sample within the crest's half-period window has `|x[n]| ≤ |A| cos(π f / f_s)`, with equality at
`n₀`. -/
@[tmio T, powerlib_foundation] theorem abs_sampledCos_le_of_midway {fs A f : ℝ} (hfs : 0 < fs)
    (hf : f ∈ Ioc 0 (fs / 2)) (k : ℤ) (n₀ : ℕ) :
    let φ := k * π - (n₀ + 1 / 2) * (2 * π * f / fs)
    |sampledCos A f φ fs n₀| = |A| * cos (π * f / fs) ∧
      ∀ n : ℕ, |2 * π * f * n / fs + φ - k * π| ≤ π / 2 →
        |sampledCos A f φ fs n| ≤ |A| * cos (π * f / fs) := by
  intro φ
  have hθ : 0 < 2 * π * f / fs := by have := hf.1; positivity
  have hhalf : π * f / fs ≤ π / 2 := by
    rw [div_le_iff₀ hfs]; nlinarith [hf.2, pi_pos]
  have hph : ∀ n : ℕ, 2 * π * f * n / fs + φ = ((n - n₀ - 1 / 2) * (2 * π * f / fs)) + k * π :=
    fun n => by simp only [φ]; ring
  have habs : ∀ n : ℕ, |sampledCos A f φ fs n| = |A| * |cos ((n - n₀ - 1 / 2) * (2 * π * f / fs))| :=
    fun n => by
      rw [sampledCos, hph, cos_add_int_mul_pi, abs_mul, abs_mul, abs_neg_one_zpow, one_mul]
  refine ⟨?_, fun n hn => ?_⟩
  · have hpos : 0 < π * f / fs := by have := hf.1; positivity
    rw [habs, show ((n₀ : ℝ) - n₀ - 1 / 2) * (2 * π * f / fs) = -(π * f / fs) by ring, cos_neg,
      abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩)]
  · rw [habs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg A)
    set u := ((n : ℝ) - n₀ - 1 / 2) * (2 * π * f / fs)
    have hu : |u| ≤ π / 2 := by
      have := hph n
      rw [show u = 2 * π * f * n / fs + φ - k * π by rw [this]; ring]
      exact hn
    have hu2 : π * f / fs ≤ |u| := by
      have hm : (1 / 2 : ℝ) ≤ |(n : ℝ) - n₀ - 1 / 2| := by
        rcases le_or_gt n n₀ with h | h
        · have : (n : ℝ) ≤ n₀ := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (n₀ : ℝ) + 1 ≤ n := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      rw [abs_mul, abs_of_pos hθ]
      calc π * f / fs = (1 / 2) * (2 * π * f / fs) := by ring
        _ ≤ |(n : ℝ) - n₀ - 1 / 2| * (2 * π * f / fs) := mul_le_mul_of_nonneg_right hm hθ.le
    have hpos : 0 ≤ π * f / fs := by have := hf.1; positivity
    rw [← cos_abs u, abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg u], hu⟩)]
    exact cos_le_cos_of_nonneg_of_le_pi hpos (by linarith [pi_pos]) hu2

/-- No sample exceeds the amplitude: `|x[n]| ≤ |A|`. -/
@[tmio T, powerlib_foundation] theorem abs_sampledCos_le (A f φ fs : ℝ) (n : ℕ) :
    |sampledCos A f φ fs n| ≤ |A| := by
  rw [sampledCos, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg A) (abs_cos_le_one _)

/-- The attainment is per crest, not over the record: at `f = f_s/5` with the crest at phase `0`
midway between the samples `0` and `1` (`φ = −π/5`), the sample `n = 3` falls exactly on the
crest at phase `π`, so the record's largest sample is the full amplitude. -/
@[tmio T, powerlib_foundation] theorem sampledCos_fifth_other_crest {fs : ℝ} (hfs : fs ≠ 0)
    (A : ℝ) : sampledCos A (fs / 5) (-(π / 5)) fs 3 = -A := by
  rw [sampledCos, show 2 * π * (fs / 5) * ((3 : ℕ) : ℝ) / fs + -(π / 5) = π by
    push_cast; field_simp; ring, cos_pi, mul_neg_one]

/-- Instances of the peak-accuracy factor `cos(π f / f_s)`: `2 Hz` at `10 Hz` gives
`cos(π/5) = (1 + √5)/4`, `5 Hz` at `20 Hz` gives `cos(π/4) = √2/2`. -/
@[tmio T, powerlib_foundation] theorem peak_factor_instances :
    cos (π * 2 / 10) = (1 + √5) / 4 ∧ cos (π * 5 / 20) = √2 / 2 := by
  refine ⟨by rw [show π * 2 / 10 = π / 5 by ring, cos_pi_div_five], ?_⟩
  rw [show π * 5 / 20 = π / 4 by ring, cos_pi_div_four]

end powerlib.Signal
