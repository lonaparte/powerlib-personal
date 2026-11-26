import theorem.Signal.Detection
import Mathlib.Analysis.Convex.Deriv

/-! # Data processing of records: gap filling by linear interpolation and per-unit normalization

The two data-processing steps of the methodology before filtering: gaps filled by linear
interpolation between the nearest valid samples, and normalization to per unit. Interpolation is
exact on affine signals, stays between the valid values, never creates an exceedance of a limit
respected at the valid samples, and errs by at most `M h²/8` on a signal with `|f''| ≤ M`;
normalization by a positive base leaves every threshold verdict of the detector unchanged.

Scope.
* A gap `[t₀, t₁]`, `t₀ < t₁`, between two valid samples `y₀ = y(t₀)`, `y₁ = y(t₁)`; the filled
  value at `t` is `lerp t₀ t₁ y₀ y₁ t`. The error bound is for a twice differentiable real signal
  with `|f''| ≤ M` on the gap (HasDerivAt everywhere, the bound only on the gap); measurement noise
  and the effect of interpolation on the filtered record are not modelled.
* Per unit: a record `y` and a per-sample limit `L` divided by the same base `P > 0`; the local
  maxima and the exceedance pattern of `theorem/Signal/Detection.lean` are compared.

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026) §3.1
("These gaps can be filled by linear interpolation between the nearest valid samples. The data is
then normalised to per unit (pu) values."), §3.6 (NaN interpolation, normalisation), §5.2 ("the
production data is normalised with the site exchange agreement").

Results.
* `lerp`, `lerp_left`, `lerp_right`, `lerp_affine` (exact on affine signals),
  `lerp_eq_combination` (a convex combination of the endpoint values), `lerp_mem_Icc` (between
  `min` and `max` of the valid values).
* `abs_lerp_le_lerp` (`|ŷ| ≤ ℓ̂` when both valid samples are within limits that are interpolated
  alike), `abs_lerp_le` (a constant limit respected at the valid samples is respected on the whole
  gap: gap filling never creates a new exceedance).
* `abs_sub_lerp_le` (`|f(t) − ŷ(t)| ≤ M (t − t₀)(t₁ − t)/2 ≤ M (t₁ − t₀)²/8` for `|f''| ≤ M`, by
  convexity of `f − ŷ ∓ M (t − t₀)(t₁ − t)/2`, `convexOn_of_hasDerivWithinAt2_nonneg`).
* `lt_abs_div_iff` (`a < |y/P| ↔ a P < |y|`), `isLocalMaxAbs_div`, `peakExceeds_div` (per-unit
  normalization of record and limit keeps the peaks and the exceedance pattern, hence every
  envelope and verdict).

Family and connection conclusions.
* None: this module defines no family; every result is an identity or inequality of explicit
  interpolants and of records.
-/

noncomputable section
namespace powerlib.Signal
open Set

/-! ## Linear interpolation across a gap -/

/-- The linear interpolant through `(t₀, y₀)` and `(t₁, y₁)`, evaluated at `t`. -/
def lerp (t₀ t₁ y₀ y₁ t : ℝ) : ℝ := y₀ + (t - t₀) / (t₁ - t₀) * (y₁ - y₀)

@[tmio T, powerlib_foundation] theorem lerp_left (t₀ t₁ y₀ y₁ : ℝ) : lerp t₀ t₁ y₀ y₁ t₀ = y₀ := by
  simp [lerp]

@[tmio T, powerlib_foundation] theorem lerp_right {t₀ t₁ : ℝ} (h : t₀ ≠ t₁) (y₀ y₁ : ℝ) :
    lerp t₀ t₁ y₀ y₁ t₁ = y₁ := by
  rw [lerp, div_self (sub_ne_zero.mpr h.symm)]
  ring

/-- Linear interpolation is exact on affine signals. -/
@[tmio T, powerlib_foundation] theorem lerp_affine {t₀ t₁ : ℝ} (h : t₀ ≠ t₁) (α β t : ℝ) :
    lerp t₀ t₁ (α * t₀ + β) (α * t₁ + β) t = α * t + β := by
  have h' : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr h.symm
  rw [lerp]
  field_simp
  ring

/-- Between its nodes the interpolant is a convex combination of the endpoint values. -/
@[tmio T, powerlib_foundation] theorem lerp_eq_combination {t₀ t₁ : ℝ} (h : t₀ < t₁)
    (y₀ y₁ t : ℝ) :
    lerp t₀ t₁ y₀ y₁ t = (t₁ - t) / (t₁ - t₀) * y₀ + (t - t₀) / (t₁ - t₀) * y₁ := by
  have hd : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr h.ne'
  rw [lerp]
  field_simp
  ring

/-- The interpolant stays between the endpoint values on the gap. -/
@[tmio T, powerlib_foundation] theorem lerp_mem_Icc {t₀ t₁ t : ℝ} (h : t₀ < t₁)
    (ht : t ∈ Icc t₀ t₁) (y₀ y₁ : ℝ) :
    min y₀ y₁ ≤ lerp t₀ t₁ y₀ y₁ t ∧ lerp t₀ t₁ y₀ y₁ t ≤ max y₀ y₁ := by
  have hd : 0 < t₁ - t₀ := sub_pos.mpr h
  have ha : 0 ≤ (t₁ - t) / (t₁ - t₀) := div_nonneg (by linarith [ht.2]) hd.le
  have hb : 0 ≤ (t - t₀) / (t₁ - t₀) := div_nonneg (by linarith [ht.1]) hd.le
  have hab : (t₁ - t) / (t₁ - t₀) + (t - t₀) / (t₁ - t₀) = 1 := by field_simp; ring
  rw [lerp_eq_combination h]
  have hm0 := mul_le_mul_of_nonneg_left (min_le_left y₀ y₁) ha
  have hm1 := mul_le_mul_of_nonneg_left (min_le_right y₀ y₁) hb
  have hM0 := mul_le_mul_of_nonneg_left (le_max_left y₀ y₁) ha
  have hM1 := mul_le_mul_of_nonneg_left (le_max_right y₀ y₁) hb
  have e1 : (t₁ - t) / (t₁ - t₀) * min y₀ y₁ + (t - t₀) / (t₁ - t₀) * min y₀ y₁ = min y₀ y₁ := by
    rw [← add_mul, hab, one_mul]
  have e2 : (t₁ - t) / (t₁ - t₀) * max y₀ y₁ + (t - t₀) / (t₁ - t₀) * max y₀ y₁ = max y₀ y₁ := by
    rw [← add_mul, hab, one_mul]
  constructor <;> linarith

/-- Gap filling never creates an exceedance: if both valid samples are within a limit that is
itself interpolated (a constant limit, or a limit linear in an interpolated production), so is
the filled value; `|ŷ(t)| ≤ ℓ̂(t)`. -/
@[tmio T, powerlib_foundation] theorem abs_lerp_le_lerp {t₀ t₁ t : ℝ} (h : t₀ < t₁)
    (ht : t ∈ Icc t₀ t₁) {y₀ y₁ ℓ₀ ℓ₁ : ℝ} (h₀ : |y₀| ≤ ℓ₀) (h₁ : |y₁| ≤ ℓ₁) :
    |lerp t₀ t₁ y₀ y₁ t| ≤ lerp t₀ t₁ ℓ₀ ℓ₁ t := by
  have hd : 0 < t₁ - t₀ := sub_pos.mpr h
  have ha : 0 ≤ (t₁ - t) / (t₁ - t₀) := div_nonneg (by linarith [ht.2]) hd.le
  have hb : 0 ≤ (t - t₀) / (t₁ - t₀) := div_nonneg (by linarith [ht.1]) hd.le
  rw [lerp_eq_combination h, lerp_eq_combination h]
  refine abs_le.mpr ⟨?_, ?_⟩
  · nlinarith [neg_abs_le y₀, neg_abs_le y₁]
  · nlinarith [le_abs_self y₀, le_abs_self y₁]

/-- In particular a constant limit `ℓ` respected at both valid samples is respected on the whole
gap. -/
@[tmio T, powerlib_foundation] theorem abs_lerp_le {t₀ t₁ t : ℝ} (h : t₀ < t₁)
    (ht : t ∈ Icc t₀ t₁) {y₀ y₁ ℓ : ℝ} (h₀ : |y₀| ≤ ℓ) (h₁ : |y₁| ≤ ℓ) :
    |lerp t₀ t₁ y₀ y₁ t| ≤ ℓ := by
  have := abs_lerp_le_lerp h ht h₀ h₁
  rwa [show lerp t₀ t₁ ℓ ℓ t = ℓ by simp [lerp]] at this

/-- Interpolation error of a `C²` signal: if `|f''| ≤ M` on the gap `[t₀, t₁]`, the interpolant
of the valid samples `f t₀`, `f t₁` errs by at most `M (t − t₀)(t₁ − t)/2 ≤ M h²/8`,
`h = t₁ − t₀`. -/
@[tmio T, powerlib_foundation] theorem abs_sub_lerp_le {f f' f'' : ℝ → ℝ} {t₀ t₁ M : ℝ}
    (h : t₀ < t₁) (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc t₀ t₁, |f'' x| ≤ M) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    |f t - lerp t₀ t₁ (f t₀) (f t₁) t| ≤ M / 2 * ((t - t₀) * (t₁ - t)) ∧
      M / 2 * ((t - t₀) * (t₁ - t)) ≤ M * (t₁ - t₀) ^ 2 / 8 := by
  have hd : 0 < t₁ - t₀ := sub_pos.mpr h
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t₀ ⟨le_rfl, h.le⟩)
  set c := (f t₁ - f t₀) / (t₁ - t₀)
  -- `e = f − lerp`, `q = (M/2)(s − t₀)(t₁ − s)`
  let e : ℝ → ℝ := fun s => f s - lerp t₀ t₁ (f t₀) (f t₁) s
  let q : ℝ → ℝ := fun s => M / 2 * ((s - t₀) * (t₁ - s))
  have he : ∀ s, HasDerivAt e (f' s - c) s := fun s => by
    have hl : HasDerivAt (fun s => lerp t₀ t₁ (f t₀) (f t₁) s) c s := by
      have h1 : HasDerivAt (fun s : ℝ => f t₀ + (s - t₀) / (t₁ - t₀) * (f t₁ - f t₀))
          (1 / (t₁ - t₀) * (f t₁ - f t₀)) s :=
        ((((hasDerivAt_id' s).sub_const t₀).div_const (t₁ - t₀)).mul_const
          (f t₁ - f t₀)).const_add (f t₀)
      rw [show c = 1 / (t₁ - t₀) * (f t₁ - f t₀) by simp only [c]; ring]
      exact h1
    exact (hf s).sub hl
  have he' : ∀ s, HasDerivAt (fun s => f' s - c) (f'' s) s := fun s => (hf' s).sub_const c
  have hq : ∀ s, HasDerivAt q (M / 2 * (t₁ + t₀ - 2 * s)) s := fun s => by
    have h1 := (((hasDerivAt_id' s).sub_const t₀).mul
      ((hasDerivAt_id' s).const_sub t₁)).const_mul (M / 2)
    convert h1 using 1
    ring
  have hq' : ∀ s, HasDerivAt (fun s => M / 2 * (t₁ + t₀ - 2 * s)) (-M) s := fun s => by
    have h1 := (((hasDerivAt_id' s).const_mul 2).const_sub (t₁ + t₀)).const_mul (M / 2)
    convert h1 using 1
    ring
  have hint : interior (Icc t₀ t₁) = Ioo t₀ t₁ := interior_Icc
  have hcomb : ∀ g : ℝ → ℝ, g t₀ = 0 → g t₁ = 0 → ConvexOn ℝ (Icc t₀ t₁) g → g t ≤ 0 := by
    intro g h0 h1 hg
    have hsum : (t₁ - t) / (t₁ - t₀) + (t - t₀) / (t₁ - t₀) = 1 := by
      have := hd.ne'
      field_simp; ring
    have hx := hg.2 (left_mem_Icc.mpr h.le) (right_mem_Icc.mpr h.le)
      (div_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ t₁ - t) hd.le)
      (div_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - t₀) hd.le) hsum
    have hpt : ((t₁ - t) / (t₁ - t₀)) • t₀ + ((t - t₀) / (t₁ - t₀)) • t₁ = t := by
      have := hd.ne'
      simp only [smul_eq_mul]; field_simp; ring
    rw [hpt, h0, h1, smul_zero, smul_zero, add_zero] at hx
    exact hx
  have he0 : e t₀ = 0 := by simp [e, lerp_left]
  have he1 : e t₁ = 0 := by simp [e, lerp_right h.ne]
  have hq0 : q t₀ = 0 := by simp [q]
  have hq1 : q t₁ = 0 := by simp [q]
  -- `e − q` is convex, `−(e + q)` is convex
  have hconv1 : ConvexOn ℝ (Icc t₀ t₁) (fun s => e s - q s) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc t₀ t₁)
      (f' := fun s => (f' s - c) - M / 2 * (t₁ + t₀ - 2 * s)) (f'' := fun s => f'' s - -M)
      (fun s _ => ((he s).sub (hq s)).continuousAt.continuousWithinAt)
      (fun s _ => ((he s).sub (hq s)).hasDerivWithinAt)
      (fun s _ => ((he' s).sub (hq' s)).hasDerivWithinAt) fun s hs => ?_
    rw [hint] at hs
    have := hM s (Ioo_subset_Icc_self hs)
    have := neg_abs_le (f'' s)
    linarith
  have hconv2 : ConvexOn ℝ (Icc t₀ t₁) (fun s => -(e s + q s)) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc t₀ t₁)
      (f' := fun s => -((f' s - c) + M / 2 * (t₁ + t₀ - 2 * s))) (f'' := fun s => -(f'' s + -M))
      (fun s _ => ((he s).add (hq s)).neg.continuousAt.continuousWithinAt)
      (fun s _ => ((he s).add (hq s)).neg.hasDerivWithinAt)
      (fun s _ => ((he' s).add (hq' s)).neg.hasDerivWithinAt) fun s hs => ?_
    rw [hint] at hs
    have := hM s (Ioo_subset_Icc_self hs)
    have := le_abs_self (f'' s)
    linarith
  have h1 := hcomb _ (by simp [he0, hq0]) (by simp [he1, hq1]) hconv1
  have h2 := hcomb _ (by simp [he0, hq0]) (by simp [he1, hq1]) hconv2
  simp only [e, q] at h1 h2
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  nlinarith [sq_nonneg (2 * t - t₀ - t₁)]

/-! ## Per-unit normalization -/

/-- A threshold relative to a base `P > 0` is the same threshold in physical units:
`a < |y / P| ↔ a P < |y|`. -/
@[tmio T, powerlib_foundation] theorem lt_abs_div_iff {P : ℝ} (hP : 0 < P) (a y : ℝ) :
    a < |y / P| ↔ a * P < |y| := by
  rw [abs_div, abs_of_pos hP, lt_div_iff₀ hP]

/-- Per-unit normalization leaves the local maxima of a record unchanged. -/
@[tmio T, powerlib_foundation] theorem isLocalMaxAbs_div {P : ℝ} (hP : 0 < P) (y : ℕ → ℝ)
    (N : ℕ) : IsLocalMaxAbs (fun k => y k / P) N = IsLocalMaxAbs y N := by
  funext k
  simp only [IsLocalMaxAbs, abs_div, abs_of_pos hP, div_lt_div_iff_of_pos_right hP,
    div_le_div_iff_of_pos_right hP]

/-- Per-unit normalization of a record and its limit by the same base `P > 0` leaves the
exceedance pattern, hence every envelope, event, count and verdict, unchanged. -/
@[tmio T, powerlib_foundation] theorem peakExceeds_div {P : ℝ} (hP : 0 < P) (y L : ℕ → ℝ)
    (N : ℕ) :
    numPeaks (fun k => y k / P) N = numPeaks y N ∧
      peakExceeds (fun k => y k / P) (fun k => L k / P) N = peakExceeds y L N := by
  have hloc := isLocalMaxAbs_div hP y N
  have hidx : peakIndex (fun k => y k / P) N = peakIndex y N := by
    funext i; simp only [peakIndex, hloc]
  refine ⟨by unfold numPeaks; congr 1, ?_⟩
  funext i
  simp only [peakExceeds, hidx, abs_div, abs_of_pos hP, div_lt_div_iff_of_pos_right hP]

end powerlib.Signal
