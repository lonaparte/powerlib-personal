import theorem.LTI.StartUp
import Mathlib.Algebra.Order.Chebyshev

/-! # The slope test of TR-110 §3.2 on the exact forced start-up

TR-110 §3.2 tells a natural from a forced oscillation by the slope `S` of the least-squares line
through `(i, ln Y_i)`, `Y_i = X_i − X_{i−1}` the increments of the peak-to-peak values `X_i` of
successive periods: `S = σT` for both envelope models, negative for a forced start-up.
`theorem/LTI/StartUp.lean` proves this exactly for the natural start-up and for the envelope
model of a forced one, and gives the exact forced start-up
`x(t) = A₃(1 − e^{σt}) sin(ωt + φ₃) + (σ/ω) A₃ sin φ₃ e^{σt} sin ωt`. Its peak-to-peak values
have no closed form. This module proves what holds for them exactly, without computing a single
peak.

The deviation of the start-up from its steady state `A₃ sin(ωt + φ₃)` decays by the exact factor
`q = e^{σT}` per period, so `X_i = P(qⁱ)` for one fixed function `P` (the peak-to-peak value over
one period of the steady state plus `a` times the deviation), and `P` is convex in `a`. Hence the
increments satisfy `Y_{i+1} ≥ q Y_i` exactly, and `|Y_i| ≤ 2(1 − q)q^{i−1}|A₃|(1 + |σ/ω|)`. If the
first increment is positive, all are, and `ln Y_i = ln Y₁ + (i − 1)σT + η_i` with `η_i`
non-decreasing in `[0, Δ]`, `Δ = ln(2(1 − q)|A₃|(1 + |σ/ω|)/Y₁)`. The least-squares slope
therefore satisfies `σT ≤ S ≤ σT + √(3/(N² − 1)) Δ`: it never underestimates `σT`, and the
forced verdict `S < −ε` is guaranteed once `3Δ² < (N² − 1)(|σT| − ε)²`.

Scope.
* Generic part: real signals `x`, `w` with `w` continuous and `T`-periodic and the deviation
  shrinking geometrically, `x(t + T) − w(t + T) = q (x(t) − w(t))`, `q ≥ 0`, `x` continuous;
  peak-to-peak values `LTI.StartUp.peakToPeak` over the windows `[jT, (j + 1)T]`. Least-squares
  slopes `LTI.StartUp.olsSlope` over `i = 1, …, N` with abscissae `i`.
* Forced start-up: the equation `m ẍ + c ẋ + k x = f(t)` of `LTI.StartUp.forced_startUp`
  (`m ≠ 0`, `σ = −c/(2m) < 0`, input with steady state `A₃ sin(ωt + φ₃)` at the damped frequency
  `ω = ω_d > 0`, started from rest), `T = 2π/ω`. The slope test is applied to the exact peaks; the
  nonlinear saturation ending the start-up stage, noise and measured records are excluded.
* No model family; foundation results.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.2, eqs. (3-4)–(3-5),
Steps 1–3 ("`Y_i` actually equals `A(e^{σT} − 1)e^{(i−1)σT}`", slope `S = σT`, forced if
`S < −ε`).

Corrections and sharpenings.
* Step 2 ("`Y_i` actually equals `A(e^{σT} − 1)e^{(i−1)σT}`") is an identity of the envelope
  (3-5) (`LTI.StartUp.envelope_increment`). For the peak-to-peak values of the exact start-up
  (3-4) what holds exactly are the geometric bounds `q Y_i ≤ Y_{i+1}` and
  `|Y_i| ≤ 2(1 − q)q^{i−1}|A₃|(1 + |σ/ω|)` (`forced_increment_ge`, `forced_increment_le`).
* Step 3: on the exact start-up the slope is not `σT` but lies in
  `[σT, σT + √(3/(N² − 1)) Δ]` (`forced_slope_bounds`): it is never below `σT`, so the deviation
  from the envelope value is always towards "natural". The test answers "forced" whenever
  `Y₁ > 0` and `3Δ² < (N² − 1)(|σT| − ε)²` (`classify_forced_exact`), and never when `|σT| ≤ ε`
  (`classify_ne_forced_exact`).
* The hypothesis `Y₁ > 0` concerns the first two exact peaks. The envelope bound
  `LTI.StartUp.forced_startUp_error` does not decide it (its error `|σ/ω||A₃|e^{σt}` is of the
  order of `Y₁` itself), and it is not derived here; `Y_i > 0` for all `i ≥ 1` iff `Y₁ > 0`
  (`forced_increment_pos`).

Results.
* `periodPP` — `X_j = peakToPeak x (jT) ((j + 1)T)`.
* `shift_iterate`, `periodPP_eq` — `x(jT + τ) = w(τ) + q^j(x(τ) − w(τ))`, so
  `X_j = P(q^j)` with `P(a)` the peak-to-peak value of `w + a(x − w)` over `[0, T]`.
* `peakToPeak_combo_le`, `abs_peakToPeak_sub_le` — `P` is convex and `2 sup|x − w|`-Lipschitz.
* `periodPP_increment_ge`, `abs_periodPP_increment_le` — `q (X_{j+1} − X_j) ≤ X_{j+2} − X_{j+1}`
  and `|X_{j+1} − X_j| ≤ 2|q − 1| q^j sup_{[0,T]}|x − w|`.
* `olsSlope_congr`, `olsSlope_add_line`, `olsSlope_nonneg_of_monovary`, `olsSlope_sq_le`,
  `spread_Icc` — the slope depends only on the data on `s`; the slope of a line plus data `η` is
  the line's slope plus that of `η`; data monovarying with the
  abscissae have a nonnegative slope (Chebyshev's sum inequality); data in `[lo, hi]` have
  `slope² ≤ #s ((hi − lo)/2)² / Σ(u − ū)²` (Cauchy–Schwarz); `Σ_{i=1}^{N}(i − ī)² = N(N² − 1)/12`.
* `forced_shift`, `forced_deviation_le` — the exact forced start-up deviates from its steady state
  by a factor `e^{σT}` per period, and by at most `|A₃|(1 + |σ/ω|)` for `t ≥ 0`.
* `forced_increment_ge`, `forced_increment_le`, `forced_increment_pos` — the bounds on `Y_i`
  above and the propagation of positivity.
* `forced_slope_bounds`, `classify_forced_exact`, `classify_ne_forced_exact` — Step 3 on the exact
  start-up.
-/

noncomputable section
namespace powerlib.LTI.StartUp
open Set Function

/-! ## Peak-to-peak values of a geometrically shrinking deviation from a periodic signal -/

section Window

variable {x w : ℝ → ℝ} {T q : ℝ}

/-- The peak-to-peak value `X_j` over the `j`-th period `[jT, (j + 1)T]`. -/
def periodPP (x : ℝ → ℝ) (T : ℝ) (j : ℕ) : ℝ := peakToPeak x (j * T) ((j + 1) * T)

/-- A deviation shrinking by `q` per period from a `T`-periodic `w`:
`x(jT + τ) = w(τ) + q^j (x(τ) − w(τ))`. -/
@[tmio T, powerlib_foundation] theorem shift_iterate (hw : Periodic w T)
    (hsh : ∀ t, x (t + T) - w (t + T) = q * (x t - w t)) (j : ℕ) (τ : ℝ) :
    x (j * T + τ) = w τ + q ^ j * (x τ - w τ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hwj : w (j * T + τ) = w τ := by
      rw [add_comm]; exact (hw.nat_mul j) τ
    have h := hsh (j * T + τ)
    rw [hw (j * T + τ), hwj] at h
    have ih' : x (j * T + τ) - w τ = q ^ j * (x τ - w τ) := by rw [ih]; ring
    rw [ih'] at h
    rw [show ((j + 1 : ℕ) : ℝ) * T + τ = j * T + τ + T by push_cast; ring, pow_succ]
    linarith

/-- `X_j = P(q^j)`: the peak-to-peak value over the `j`-th period is that of
`w + q^j (x − w)` over `[0, T]`. -/
@[tmio T, powerlib_foundation] theorem periodPP_eq (hw : Periodic w T)
    (hsh : ∀ t, x (t + T) - w (t + T) = q * (x t - w t)) (j : ℕ) :
    periodPP x T j = peakToPeak (fun τ => w τ + q ^ j * (x τ - w τ)) 0 T := by
  have himg : x '' Icc (j * T) ((j + 1) * T) =
      (fun τ => w τ + q ^ j * (x τ - w τ)) '' Icc 0 T := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t - j * T, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      have := shift_iterate hw hsh j (t - j * T)
      rw [show (j : ℝ) * T + (t - j * T) = t by ring] at this
      exact this.symm
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨j * T + τ, ⟨by linarith [hτ.1], by linarith [hτ.2]⟩, ?_⟩
      exact shift_iterate hw hsh j τ
  rw [periodPP, peakToPeak, peakToPeak, himg]

variable {d : ℝ → ℝ}

@[tmio T, powerlib_foundation] private theorem bdd_image (hw : Continuous w) (hd : Continuous d)
    (a : ℝ) :
    BddAbove ((fun τ => w τ + a * d τ) '' Icc 0 T) ∧
      BddBelow ((fun τ => w τ + a * d τ) '' Icc 0 T) := by
  have hc : Continuous fun τ => w τ + a * d τ := hw.add (continuous_const.mul hd)
  exact ⟨isCompact_Icc.bddAbove_image hc.continuousOn,
    isCompact_Icc.bddBelow_image hc.continuousOn⟩

/-- Convexity of `P(a)`, the peak-to-peak value of `w + a d` over `[0, T]`:
`P(θa + (1 − θ)b) ≤ θP(a) + (1 − θ)P(b)` for `θ ∈ [0, 1]`. -/
@[tmio T, powerlib_foundation] theorem peakToPeak_combo_le (hT : 0 ≤ T) (hw : Continuous w)
    (hd : Continuous d) {a b θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    peakToPeak (fun τ => w τ + (θ * a + (1 - θ) * b) * d τ) 0 T ≤
      θ * peakToPeak (fun τ => w τ + a * d τ) 0 T +
        (1 - θ) * peakToPeak (fun τ => w τ + b * d τ) 0 T := by
  have hne : (Icc (0 : ℝ) T).Nonempty := nonempty_Icc.mpr hT
  obtain ⟨hAa, hBa⟩ := bdd_image (T := T) hw hd a
  obtain ⟨hAb, hBb⟩ := bdd_image (T := T) hw hd b
  have hθ1' : 0 ≤ 1 - θ := by linarith
  have hsup : sSup ((fun τ => w τ + (θ * a + (1 - θ) * b) * d τ) '' Icc 0 T) ≤
      θ * sSup ((fun τ => w τ + a * d τ) '' Icc 0 T) +
        (1 - θ) * sSup ((fun τ => w τ + b * d τ) '' Icc 0 T) := by
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨τ, hτ, rfl⟩
    have h1 := le_csSup hAa (mem_image_of_mem (fun τ => w τ + a * d τ) hτ)
    have h2 := le_csSup hAb (mem_image_of_mem (fun τ => w τ + b * d τ) hτ)
    have := mul_le_mul_of_nonneg_left h1 hθ0
    have := mul_le_mul_of_nonneg_left h2 hθ1'
    simp only at *
    nlinarith
  have hinf : θ * sInf ((fun τ => w τ + a * d τ) '' Icc 0 T) +
        (1 - θ) * sInf ((fun τ => w τ + b * d τ) '' Icc 0 T) ≤
      sInf ((fun τ => w τ + (θ * a + (1 - θ) * b) * d τ) '' Icc 0 T) := by
    refine le_csInf (hne.image _) ?_
    rintro _ ⟨τ, hτ, rfl⟩
    have h1 := csInf_le hBa (mem_image_of_mem (fun τ => w τ + a * d τ) hτ)
    have h2 := csInf_le hBb (mem_image_of_mem (fun τ => w τ + b * d τ) hτ)
    have := mul_le_mul_of_nonneg_left h1 hθ0
    have := mul_le_mul_of_nonneg_left h2 hθ1'
    simp only at *
    nlinarith
  rw [peakToPeak, peakToPeak, peakToPeak]
  linarith

/-- `P` is Lipschitz: `|P(a) − P(b)| ≤ 2|a − b| B` when `|d| ≤ B` on `[0, T]`. -/
@[tmio T, powerlib_foundation] theorem abs_peakToPeak_sub_le (hT : 0 ≤ T) (hw : Continuous w)
    (hd : Continuous d) {B : ℝ} (hB : ∀ τ ∈ Icc 0 T, |d τ| ≤ B) (a b : ℝ) :
    |peakToPeak (fun τ => w τ + a * d τ) 0 T - peakToPeak (fun τ => w τ + b * d τ) 0 T| ≤
      2 * |a - b| * B := by
  have hne : (Icc (0 : ℝ) T).Nonempty := nonempty_Icc.mpr hT
  have key : ∀ a b : ℝ, peakToPeak (fun τ => w τ + a * d τ) 0 T -
      peakToPeak (fun τ => w τ + b * d τ) 0 T ≤ 2 * |a - b| * B := by
    intro a b
    obtain ⟨hAb, hBb⟩ := bdd_image (T := T) hw hd b
    have hpt : ∀ τ ∈ Icc 0 T, |(a - b) * d τ| ≤ |a - b| * B := fun τ hτ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB τ hτ) (abs_nonneg _)
    have hsup : sSup ((fun τ => w τ + a * d τ) '' Icc 0 T) ≤
        sSup ((fun τ => w τ + b * d τ) '' Icc 0 T) + |a - b| * B := by
      refine csSup_le (hne.image _) ?_
      rintro _ ⟨τ, hτ, rfl⟩
      have h1 := le_csSup hAb (mem_image_of_mem (fun τ => w τ + b * d τ) hτ)
      have h2 := (abs_le.mp (hpt τ hτ)).2
      simp only at *
      linarith
    have hinf : sInf ((fun τ => w τ + b * d τ) '' Icc 0 T) - |a - b| * B ≤
        sInf ((fun τ => w τ + a * d τ) '' Icc 0 T) := by
      refine le_csInf (hne.image _) ?_
      rintro _ ⟨τ, hτ, rfl⟩
      have h1 := csInf_le hBb (mem_image_of_mem (fun τ => w τ + b * d τ) hτ)
      have h2 := (abs_le.mp (hpt τ hτ)).1
      simp only at *
      linarith
    rw [peakToPeak, peakToPeak]
    linarith
  rw [abs_le]
  constructor
  · have := key b a
    rw [abs_sub_comm] at this
    linarith
  · exact key a b

/-- The increments of the period peak-to-peak values decay at most geometrically:
`q (X_{j+1} − X_j) ≤ X_{j+2} − X_{j+1}` (convexity of `P` at `q^{j+2} < q^{j+1} < q^j`). -/
@[tmio T, powerlib_foundation] theorem periodPP_increment_ge (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hx : Continuous x) (hw : Continuous w) (hwT : Periodic w T)
    (hsh : ∀ t, x (t + T) - w (t + T) = q * (x t - w t)) (j : ℕ) :
    q * (periodPP x T (j + 1) - periodPP x T j) ≤
      periodPP x T (j + 2) - periodPP x T (j + 1) := by
  rw [periodPP_eq hwT hsh, periodPP_eq hwT hsh, periodPP_eq hwT hsh]
  have h1q : 0 < 1 + q := by linarith
  have hθ0 : 0 ≤ 1 / (1 + q) := by positivity
  have hθ1 : 1 / (1 + q) ≤ 1 := by rw [div_le_one h1q]; linarith
  have h := peakToPeak_combo_le (d := fun τ => x τ - w τ) hT hw (hx.sub hw)
    (a := q ^ (j + 2)) (b := q ^ j) hθ0 hθ1
  have hc : 1 / (1 + q) * q ^ (j + 2) + (1 - 1 / (1 + q)) * q ^ j = q ^ (j + 1) := by
    field_simp; ring
  rw [hc] at h
  have h' : (1 + q) * peakToPeak (fun τ => w τ + q ^ (j + 1) * (x τ - w τ)) 0 T ≤
      peakToPeak (fun τ => w τ + q ^ (j + 2) * (x τ - w τ)) 0 T +
        q * peakToPeak (fun τ => w τ + q ^ j * (x τ - w τ)) 0 T := by
    have h2 : (1 - 1 / (1 + q)) = q / (1 + q) := by field_simp; ring
    rw [h2] at h
    have := mul_le_mul_of_nonneg_left h h1q.le
    have e : (1 + q) * (1 / (1 + q) *
        peakToPeak (fun τ => w τ + q ^ (j + 2) * (x τ - w τ)) 0 T +
        q / (1 + q) * peakToPeak (fun τ => w τ + q ^ j * (x τ - w τ)) 0 T) =
        peakToPeak (fun τ => w τ + q ^ (j + 2) * (x τ - w τ)) 0 T +
          q * peakToPeak (fun τ => w τ + q ^ j * (x τ - w τ)) 0 T := by
      field_simp
    linarith
  linarith

/-- The increments are bounded geometrically: `|X_{j+1} − X_j| ≤ 2|q − 1| q^j B` when
`|x − w| ≤ B` on `[0, T]`. -/
@[tmio T, powerlib_foundation] theorem abs_periodPP_increment_le (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hx : Continuous x) (hw : Continuous w) (hwT : Periodic w T)
    (hsh : ∀ t, x (t + T) - w (t + T) = q * (x t - w t)) {B : ℝ}
    (hB : ∀ τ ∈ Icc 0 T, |x τ - w τ| ≤ B) (j : ℕ) :
    |periodPP x T (j + 1) - periodPP x T j| ≤ 2 * |q - 1| * q ^ j * B := by
  rw [periodPP_eq hwT hsh, periodPP_eq hwT hsh]
  have h := abs_peakToPeak_sub_le (d := fun τ => x τ - w τ) hT hw (hx.sub hw) hB
    (q ^ (j + 1)) (q ^ j)
  have e : |q ^ (j + 1) - q ^ j| = |q - 1| * q ^ j := by
    rw [pow_succ, show q ^ j * q - q ^ j = q ^ j * (q - 1) by ring, abs_mul,
      abs_of_nonneg (pow_nonneg hq j), mul_comm]
  rw [e] at h
  linarith

end Window

/-! ## Least-squares slopes of perturbed lines -/

section Slope

variable {ι : Type*}

@[tmio T, powerlib_foundation] private theorem sum_sub_expect (s : Finset ι) (u : ι → ℝ) :
    ∑ i ∈ s, (u i - Finset.expect s u) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.card_smul_expect, sub_self]

@[tmio T, powerlib_foundation] private theorem num_eq (s : Finset ι) (u z : ι → ℝ) (c : ℝ) :
    ∑ i ∈ s, (u i - Finset.expect s u) * (z i - Finset.expect s z) =
      ∑ i ∈ s, (u i - Finset.expect s u) * (z i - c) := by
  have h1 : ∀ c' : ℝ, ∑ i ∈ s, (u i - Finset.expect s u) * (z i - c') =
      ∑ i ∈ s, (u i - Finset.expect s u) * z i := by
    intro c'
    rw [show (∑ i ∈ s, (u i - Finset.expect s u) * (z i - c')) =
        ∑ i ∈ s, ((u i - Finset.expect s u) * z i - c' * (u i - Finset.expect s u)) by
      refine Finset.sum_congr rfl fun i _ => ?_; ring,
      Finset.sum_sub_distrib, ← Finset.mul_sum, sum_sub_expect, mul_zero, sub_zero]
  rw [h1, h1]

/-- The slope of a line plus data `η` is the line's slope plus the slope of `η`. -/
@[tmio T, powerlib_foundation] theorem olsSlope_add_line {s : Finset ι} {u : ι → ℝ}
    (h : ∑ i ∈ s, (u i - Finset.expect s u) ^ 2 ≠ 0) (z₀ S : ℝ) (η : ι → ℝ) :
    olsSlope s u (fun i => z₀ + S * u i + η i) = S + olsSlope s u η := by
  rw [olsSlope, olsSlope, num_eq s u _ 0, num_eq s u η 0]
  have e : ∑ i ∈ s, (u i - Finset.expect s u) * (z₀ + S * u i + η i - 0) =
      S * ∑ i ∈ s, (u i - Finset.expect s u) ^ 2 +
        ∑ i ∈ s, (u i - Finset.expect s u) * (η i - 0) := by
    have h2 : ∀ i ∈ s, (u i - Finset.expect s u) * (z₀ + S * u i + η i - 0) =
        S * (u i - Finset.expect s u) ^ 2 + (u i - Finset.expect s u) * (η i - 0) +
          (z₀ + S * Finset.expect s u) * (u i - Finset.expect s u) := fun i _ => by ring
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_sub_expect, mul_zero, add_zero]
  rw [e, add_div, mul_div_assoc, div_self h, mul_one]

/-- Data monovarying with the abscissae have a nonnegative least-squares slope
(Chebyshev's sum inequality). -/
@[tmio T, powerlib_foundation] theorem olsSlope_nonneg_of_monovary {s : Finset ι} {u η : ι → ℝ}
    (h : MonovaryOn η u s) : 0 ≤ olsSlope s u η := by
  rw [olsSlope]
  refine div_nonneg ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [num_eq s u η 0]
  rcases Finset.eq_empty_or_nonempty s with hs | hs
  · simp [hs]
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hcheb := h.sum_mul_sum_le_card_mul_sum
  have e : ∑ i ∈ s, (u i - Finset.expect s u) * (η i - 0) =
      ∑ i ∈ s, η i * u i - (∑ i ∈ s, η i) * (∑ i ∈ s, u i) / s.card := by
    rw [Finset.expect_eq_sum_div_card]
    simp only [sub_zero, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun i _ => mul_comm (u i) (η i), ← Finset.mul_sum]
    ring
  rw [e, sub_nonneg, div_le_iff₀ hcard]
  linarith

/-- Data in `[lo, hi]`: `slope² ≤ #s ((hi − lo)/2)² / Σ(u − ū)²` (Cauchy–Schwarz). -/
@[tmio T, powerlib_foundation] theorem olsSlope_sq_le {s : Finset ι} {u η : ι → ℝ} {lo hi : ℝ}
    (hη : ∀ i ∈ s, lo ≤ η i ∧ η i ≤ hi) (h : 0 < ∑ i ∈ s, (u i - Finset.expect s u) ^ 2) :
    olsSlope s u η ^ 2 ≤ s.card * ((hi - lo) / 2) ^ 2 / ∑ i ∈ s, (u i - Finset.expect s u) ^ 2 := by
  set V := ∑ i ∈ s, (u i - Finset.expect s u) ^ 2
  rw [olsSlope, num_eq s u η ((lo + hi) / 2), div_pow]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => u i - Finset.expect s u)
    (fun i => η i - (lo + hi) / 2)
  have hdev : ∑ i ∈ s, (η i - (lo + hi) / 2) ^ 2 ≤ s.card * ((hi - lo) / 2) ^ 2 := by
    have : ∀ i ∈ s, (η i - (lo + hi) / 2) ^ 2 ≤ ((hi - lo) / 2) ^ 2 := fun i hi' => by
      obtain ⟨h1, h2⟩ := hη i hi'
      exact sq_le_sq' (by linarith) (by linarith)
    calc ∑ i ∈ s, (η i - (lo + hi) / 2) ^ 2 ≤ ∑ _i ∈ s, ((hi - lo) / 2) ^ 2 :=
          Finset.sum_le_sum this
      _ = s.card * ((hi - lo) / 2) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [div_le_div_iff₀ (by positivity) h]
  calc (∑ i ∈ s, (u i - Finset.expect s u) * (η i - (lo + hi) / 2)) ^ 2 * V
      ≤ (V * ∑ i ∈ s, (η i - (lo + hi) / 2) ^ 2) * V := mul_le_mul_of_nonneg_right hcs h.le
    _ ≤ (V * (s.card * ((hi - lo) / 2) ^ 2)) * V := by gcongr
    _ = s.card * ((hi - lo) / 2) ^ 2 * V ^ 2 := by ring

/-- The least-squares slope depends only on the data on `s`. -/
@[tmio T, powerlib_foundation] theorem olsSlope_congr {s : Finset ι} {u z z' : ι → ℝ}
    (h : ∀ i ∈ s, z i = z' i) : olsSlope s u z = olsSlope s u z' := by
  rw [olsSlope, olsSlope, Finset.expect_congr rfl h]
  congr 1
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

/-- The spread of the abscissae `1, …, N`: `Σ_{i=1}^{N} (i − ī)² = N(N² − 1)/12`. -/
@[tmio T, powerlib_foundation] theorem spread_Icc (N : ℕ) :
    ∑ l ∈ Finset.Icc 1 N, ((l : ℝ) - Finset.expect (Finset.Icc 1 N) (fun l : ℕ => (l : ℝ))) ^ 2 =
      N * ((N : ℝ) ^ 2 - 1) / 12 := by
  have hS1 : ∀ M : ℕ, ∑ l ∈ Finset.Icc 1 M, (l : ℝ) = M * (M + 1) / 2 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast; ring
  have hS2 : ∀ M : ℕ, ∑ l ∈ Finset.Icc 1 M, (l : ℝ) ^ 2 = M * (M + 1) * (2 * M + 1) / 6 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast; ring
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hcard : ((Finset.Icc 1 N).card : ℝ) = N := by simp
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Finset.expect_eq_sum_div_card, hS1, hcard]
  have e : ∀ l ∈ Finset.Icc 1 N, ((l : ℝ) - N * (N + 1) / 2 / N) ^ 2 =
      (l : ℝ) ^ 2 - (N + 1) * (l : ℝ) + ((N : ℝ) + 1) ^ 2 / 4 := fun l _ => by
    field_simp; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hS2, hS1, Finset.sum_const, nsmul_eq_mul, hcard]
  field_simp
  ring

end Slope

/-! ## The exact forced start-up -/

section Forced

variable {m c k σ ω : ℝ}

/-- The exact forced start-up deviates from its steady state `A₃ sin(ωt + φ₃)` by the factor
`e^{σT}` per period `T = 2π/ω`. -/
@[tmio T, powerlib_foundation] theorem forced_shift (hω0 : ω ≠ 0) (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hω : ω ^ 2 = k / m - σ ^ 2) {A₃ φ₃ : ℝ} {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (t : ℝ) :
    x (t + 2 * Real.pi / ω) - A₃ * Real.sin (ω * (t + 2 * Real.pi / ω) + φ₃) =
      Real.exp (σ * (2 * Real.pi / ω)) * (x t - A₃ * Real.sin (ω * t + φ₃)) := by
  rw [forced_startUp hm hσ hω hω0 hss hx hv heq hx0 hv0 (t + 2 * Real.pi / ω),
    forced_startUp hm hσ hω hω0 hss hx hv heq hx0 hv0 t]
  have h1 : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
  have h2 : σ * (t + 2 * Real.pi / ω) = σ * t + σ * (2 * Real.pi / ω) := by ring
  rw [h1, h2, Real.exp_add, show ω * t + 2 * Real.pi + φ₃ = (ω * t + φ₃) + 2 * Real.pi by ring,
    Real.sin_add_two_pi, Real.sin_add_two_pi]
  ring

/-- For `σ ≤ 0` and `t ≥ 0` the deviation from the steady state is at most
`|A₃| (1 + |σ/ω|)`. -/
@[tmio T, powerlib_foundation] theorem forced_deviation_le (hω0 : ω ≠ 0) (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hω : ω ^ 2 = k / m - σ ^ 2) {A₃ φ₃ : ℝ} {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (hσ0 : σ ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    |x t - A₃ * Real.sin (ω * t + φ₃)| ≤ |A₃| * (1 + |σ / ω|) := by
  rw [forced_startUp hm hσ hω hω0 hss hx hv heq hx0 hv0 t]
  have he : Real.exp (σ * t) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hσ0 ht)
  have he0 := Real.exp_pos (σ * t)
  have e : A₃ * (1 - Real.exp (σ * t)) * Real.sin (ω * t + φ₃) +
      σ / ω * A₃ * Real.sin φ₃ * Real.exp (σ * t) * Real.sin (ω * t) -
        A₃ * Real.sin (ω * t + φ₃) =
      A₃ * Real.exp (σ * t) *
        (-Real.sin (ω * t + φ₃) + σ / ω * (Real.sin φ₃ * Real.sin (ω * t))) := by ring
  rw [e, abs_mul, abs_mul, abs_of_pos he0]
  have h1 : |-Real.sin (ω * t + φ₃) + σ / ω * (Real.sin φ₃ * Real.sin (ω * t))| ≤
      1 + |σ / ω| := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_neg]; exact Real.abs_sin_le_one _
    · rw [abs_mul, abs_mul]
      have := Real.abs_sin_le_one φ₃
      have := Real.abs_sin_le_one (ω * t)
      have : |Real.sin φ₃| * |Real.sin (ω * t)| ≤ 1 := by
        nlinarith [abs_nonneg (Real.sin φ₃), abs_nonneg (Real.sin (ω * t))]
      nlinarith [abs_nonneg (σ / ω)]
  have h2 : 0 ≤ |A₃| := abs_nonneg _
  calc |A₃| * Real.exp (σ * t) *
        |-Real.sin (ω * t + φ₃) + σ / ω * (Real.sin φ₃ * Real.sin (ω * t))|
      ≤ |A₃| * 1 * (1 + |σ / ω|) := by gcongr
    _ = |A₃| * (1 + |σ / ω|) := by ring

@[tmio T, powerlib_foundation] private theorem continuous_steady (A₃ φ₃ : ℝ) :
    Continuous fun t => A₃ * Real.sin (ω * t + φ₃) := by fun_prop

@[tmio T, powerlib_foundation] private theorem periodic_steady (hω0 : ω ≠ 0) (A₃ φ₃ : ℝ) :
    Periodic (fun t => A₃ * Real.sin (ω * t + φ₃)) (2 * Real.pi / ω) := by
  intro t
  simp only
  rw [show ω * (t + 2 * Real.pi / ω) + φ₃ = (ω * t + φ₃) + 2 * Real.pi by field_simp; ring,
    Real.sin_add_two_pi]

/-- Exact Step 2, lower bound: the increments of the exact forced start-up decay at most by
`e^{σT}` per period, `e^{σT}(X_{j+1} − X_j) ≤ X_{j+2} − X_{j+1}`. -/
@[tmio T, powerlib_foundation] theorem forced_increment_ge (hω0 : 0 < ω) (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hω : ω ^ 2 = k / m - σ ^ 2) {A₃ φ₃ : ℝ} {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (j : ℕ) :
    Real.exp (σ * (2 * Real.pi / ω)) *
        (periodPP x (2 * Real.pi / ω) (j + 1) - periodPP x (2 * Real.pi / ω) j) ≤
      periodPP x (2 * Real.pi / ω) (j + 2) - periodPP x (2 * Real.pi / ω) (j + 1) :=
  periodPP_increment_ge (w := fun t => A₃ * Real.sin (ω * t + φ₃)) (Real.exp_pos _).le
    (by positivity) (continuous_iff_continuousAt.2 fun t => (hx t).continuousAt)
    (continuous_steady A₃ φ₃) (periodic_steady hω0.ne' A₃ φ₃)
    (forced_shift hω0.ne' hm hσ hω hss hx hv heq hx0 hv0) j

/-- Exact Step 2, upper bound: for `σ < 0`,
`|X_{j+1} − X_j| ≤ 2(1 − e^{σT}) e^{jσT} |A₃|(1 + |σ/ω|)`. -/
@[tmio T, powerlib_foundation] theorem forced_increment_le (hω0 : 0 < ω) (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hω : ω ^ 2 = k / m - σ ^ 2) {A₃ φ₃ : ℝ} {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (hσ0 : σ < 0)
    (j : ℕ) :
    |periodPP x (2 * Real.pi / ω) (j + 1) - periodPP x (2 * Real.pi / ω) j| ≤
      2 * (1 - Real.exp (σ * (2 * Real.pi / ω))) * Real.exp (σ * (2 * Real.pi / ω)) ^ j *
        (|A₃| * (1 + |σ / ω|)) := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have hq1 : Real.exp (σ * (2 * Real.pi / ω)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h := abs_periodPP_increment_le (w := fun t => A₃ * Real.sin (ω * t + φ₃))
    (Real.exp_pos _).le hT.le (continuous_iff_continuousAt.2 fun t => (hx t).continuousAt)
    (continuous_steady A₃ φ₃) (periodic_steady hω0.ne' A₃ φ₃)
    (forced_shift hω0.ne' hm hσ hω hss hx hv heq hx0 hv0)
    (fun τ hτ => forced_deviation_le hω0.ne' hm hσ hω hss hx hv heq hx0 hv0 hσ0.le hτ.1) j
  rwa [abs_of_neg (by linarith : Real.exp (σ * (2 * Real.pi / ω)) - 1 < 0), neg_sub] at h

/-- Positivity propagates: `X_{j+1} − X_j ≥ e^{jσT}(X₁ − X₀)`; all increments are positive iff the
first one is. -/
@[tmio T, powerlib_foundation] theorem forced_increment_pos (hω0 : 0 < ω) (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hω : ω ^ 2 = k / m - σ ^ 2) {A₃ φ₃ : ℝ} {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (j : ℕ) :
    Real.exp (σ * (2 * Real.pi / ω)) ^ j *
        (periodPP x (2 * Real.pi / ω) 1 - periodPP x (2 * Real.pi / ω) 0) ≤
      periodPP x (2 * Real.pi / ω) (j + 1) - periodPP x (2 * Real.pi / ω) j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := forced_increment_ge hω0 hm hσ hω hss hx hv heq hx0 hv0 j
    have hq := (Real.exp_pos (σ * (2 * Real.pi / ω))).le
    rw [pow_succ]
    nlinarith

end Forced

/-! ## Step 3 on the exact forced start-up -/

section ForcedSlope

variable {m c k σ ω : ℝ}

/-- Step 3 on the exact forced start-up (`σ < 0`) with a positive first increment
`Y₁ = X₁ − X₀ > 0`: the least-squares slope `S` of `(i, ln Y_i)`, `i = 1, …, N` (`N ≥ 2`),
satisfies `σT ≤ S` and `(S − σT)² ≤ 3Δ²/(N² − 1)`, `Δ = ln(2(1 − e^{σT})|A₃|(1 + |σ/ω|)/Y₁)`. -/
@[tmio T, powerlib_foundation] theorem forced_slope_bounds (hω0 : 0 < ω) (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hω : ω ^ 2 = k / m - σ ^ 2) {A₃ φ₃ : ℝ} {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (hσ0 : σ < 0)
    (hpos : periodPP x (2 * Real.pi / ω) 0 < periodPP x (2 * Real.pi / ω) 1) {N : ℕ}
    (hN : 2 ≤ N) :
    let S := olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
      Real.log (peakToPeak x (i * (2 * Real.pi / ω)) ((i + 1) * (2 * Real.pi / ω)) -
        peakToPeak x ((i - 1) * (2 * Real.pi / ω)) (i * (2 * Real.pi / ω))))
    σ * (2 * Real.pi / ω) ≤ S ∧
      (S - σ * (2 * Real.pi / ω)) ^ 2 ≤
        3 * Real.log (2 * (1 - Real.exp (σ * (2 * Real.pi / ω))) * (|A₃| * (1 + |σ / ω|)) /
        (periodPP x (2 * Real.pi / ω) 1 - periodPP x (2 * Real.pi / ω) 0)) ^ 2 /
          ((N : ℝ) ^ 2 - 1) := by
  intro S
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  set q := Real.exp (σ * T) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  set X := periodPP x T with hXdef
  set Y₁ := X 1 - X 0 with hY₁def
  have hY₁ : 0 < Y₁ := sub_pos.mpr hpos
  set B := 2 * (1 - q) * (|A₃| * (1 + |σ / ω|)) with hBdef
  let η : ℕ → ℝ := fun i => Real.log (X i - X (i - 1)) - Real.log Y₁ - σ * T * ((i : ℝ) - 1)
  -- the data are the line `ln Y₁ + (i − 1)σT` plus `η`
  have hdata : ∀ i ∈ Finset.Icc 1 N,
      Real.log (peakToPeak x (i * T) ((i + 1) * T) - peakToPeak x ((i - 1) * T) (i * T)) =
        (Real.log Y₁ - σ * T) + σ * T * (i : ℝ) + η i := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by rw [Nat.cast_sub hi1, Nat.cast_one]
    have hX1 : peakToPeak x ((i - 1) * T) (i * T) = X (i - 1) := by
      simp only [hXdef, periodPP, hcast, sub_add_cancel]
    have hX2 : peakToPeak x (i * T) ((i + 1) * T) = X i := rfl
    simp only [η]
    rw [hX1, hX2]
    ring
  -- bounds and monotonicity of `η` on `i ≥ 1`
  have hYlow : ∀ j : ℕ, q ^ j * Y₁ ≤ X (j + 1) - X j := fun j =>
    forced_increment_pos hω0 hm hσ hω hss hx hv heq hx0 hv0 j
  have hYup : ∀ j : ℕ, X (j + 1) - X j ≤ B * q ^ j := fun j => by
    have := (abs_le.mp (forced_increment_le hω0 hm hσ hω hss hx hv heq hx0 hv0 hσ0 j)).2
    rw [hBdef]; linarith
  have hlogq : ∀ j : ℕ, Real.log (q ^ j) = σ * T * j := fun j => by
    rw [Real.log_pow, hqdef, Real.log_exp]; ring
  have hB : 0 < B := by
    have h1 := hYlow 0
    have h2 := hYup 0
    simp only [pow_zero, one_mul, mul_one, zero_add] at h1 h2
    linarith
  have hηj : ∀ j : ℕ, η (j + 1) = Real.log (X (j + 1) - X j) - Real.log Y₁ - σ * T * j := by
    intro j
    simp only [η, Nat.add_sub_cancel]
    push_cast
    ring
  have hηlo : ∀ j : ℕ, 0 ≤ η (j + 1) := fun j => by
    rw [hηj]
    have hpos' : 0 < q ^ j * Y₁ := by positivity
    have := Real.log_le_log hpos' (hYlow j)
    rw [Real.log_mul (by positivity) hY₁.ne', hlogq] at this
    linarith
  have hηhi : ∀ j : ℕ, η (j + 1) ≤ Real.log (B / Y₁) := fun j => by
    rw [hηj, Real.log_div hB.ne' hY₁.ne']
    have hpos' : 0 < X (j + 1) - X j := lt_of_lt_of_le (by positivity) (hYlow j)
    have := Real.log_le_log hpos' (hYup j)
    rw [Real.log_mul hB.ne' (by positivity), hlogq] at this
    linarith
  have hηmono : ∀ j : ℕ, η (j + 1) ≤ η (j + 2) := fun j => by
    rw [hηj, show η (j + 2) = Real.log (X (j + 2) - X (j + 1)) - Real.log Y₁ - σ * T * (j + 1) by
      rw [show j + 2 = (j + 1) + 1 by ring, hηj]; push_cast; ring]
    have hpos1 : 0 < X (j + 1) - X j := lt_of_lt_of_le (by positivity) (hYlow j)
    have hge := forced_increment_ge hω0 hm hσ hω hss hx hv heq hx0 hv0 j
    have hpos2 : 0 < q * (X (j + 1) - X j) := by positivity
    have := Real.log_le_log hpos2 hge
    rw [Real.log_mul hq0.ne' hpos1.ne', hqdef, Real.log_exp] at this
    linarith
  have hmono : ∀ i, 1 ≤ i → ∀ d : ℕ, η i ≤ η (i + d) := by
    intro i hi d
    induction d with
    | zero => simp
    | succ d ih =>
      refine ih.trans ?_
      have := hηmono (i + d - 1)
      rw [show i + d - 1 + 1 = i + d by omega, show i + d - 1 + 2 = i + (d + 1) by omega] at this
      exact this
  have hmv : MonovaryOn η (fun i : ℕ => (i : ℝ)) (Finset.Icc 1 N : Set ℕ) := by
    intro i hi j _ hij
    have hij' : i < j := by exact_mod_cast (show (i : ℝ) < j from hij)
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp (Finset.mem_coe.mp hi)).1
    have := hmono i hi1 (j - i)
    rwa [Nat.add_sub_cancel' hij'.le] at this
  have hrange : ∀ i ∈ Finset.Icc 1 N, 0 ≤ η i ∧ η i ≤ Real.log (B / Y₁) := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := (Finset.mem_Icc.mp hi).1; omega⟩
    exact ⟨hηlo j, hηhi j⟩
  have hspread := spread_Icc N
  have hN2 : (1 : ℝ) < (N : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hsp : 0 < ∑ l ∈ Finset.Icc 1 N,
      ((l : ℝ) - Finset.expect (Finset.Icc 1 N) (fun l : ℕ => (l : ℝ))) ^ 2 := by
    rw [hspread]
    have : 0 < (N : ℝ) ^ 2 - 1 := by linarith
    positivity
  have hS : S = σ * T + olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) η := by
    show olsSlope _ _ _ = _
    rw [olsSlope_congr hdata, olsSlope_add_line hsp.ne']
  have h0 := olsSlope_nonneg_of_monovary hmv
  have h2 := olsSlope_sq_le hrange hsp
  rw [hspread, Nat.card_Icc, Nat.add_sub_cancel] at h2
  refine ⟨by rw [hS]; linarith, ?_⟩
  rw [hS, add_sub_cancel_left]
  refine h2.trans (le_of_eq ?_)
  have hN' : (N : ℝ) ≠ 0 := hNpos.ne'
  have hN'' : (N : ℝ) ^ 2 - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Step 3 gives the correct verdict on the exact forced start-up once the record is long
enough: for `σ < 0`, a positive first increment, `0 ≤ ε < |σT|` and
`3Δ² < (N² − 1)(|σT| − ε)²`, the slope test answers "forced". -/
@[tmio T, powerlib_foundation] theorem classify_forced_exact (hω0 : 0 < ω) (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hω : ω ^ 2 = k / m - σ ^ 2) {A₃ φ₃ : ℝ} {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (hσ0 : σ < 0)
    (hpos : periodPP x (2 * Real.pi / ω) 0 < periodPP x (2 * Real.pi / ω) 1) {ε : ℝ}
    (hε : 0 ≤ ε) (hεσ : ε < -(σ * (2 * Real.pi / ω))) {N : ℕ} (hN : 2 ≤ N)
    (hlong : 3 * Real.log (2 * (1 - Real.exp (σ * (2 * Real.pi / ω))) * (|A₃| * (1 + |σ / ω|)) /
        (periodPP x (2 * Real.pi / ω) 1 - periodPP x (2 * Real.pi / ω) 0)) ^ 2 <
      ((N : ℝ) ^ 2 - 1) * (-(σ * (2 * Real.pi / ω)) - ε) ^ 2) :
    classify ε (olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
      Real.log (peakToPeak x (i * (2 * Real.pi / ω)) ((i + 1) * (2 * Real.pi / ω)) -
        peakToPeak x ((i - 1) * (2 * Real.pi / ω)) (i * (2 * Real.pi / ω))))) = .forced := by
  obtain ⟨h1, h2⟩ := forced_slope_bounds hω0 hm hσ hω hss hx hv heq hx0 hv0 hσ0 hpos hN
  rw [classify_eq_forced_iff hε]
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  set S := olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
      Real.log (peakToPeak x (i * (2 * Real.pi / ω)) ((i + 1) * (2 * Real.pi / ω)) -
        peakToPeak x ((i - 1) * (2 * Real.pi / ω)) (i * (2 * Real.pi / ω))))
  have h3 : (S - σ * (2 * Real.pi / ω)) ^ 2 < (-(σ * (2 * Real.pi / ω)) - ε) ^ 2 := by
    refine lt_of_le_of_lt h2 ?_
    rw [div_lt_iff₀ hN2]
    linarith
  have h4 := abs_lt_of_sq_lt_sq h3 (by linarith)
  have h5 := (abs_lt.mp h4).2
  linarith

/-- If `|σT| ≤ ε` the slope test never answers "forced" on the exact forced start-up (with a
positive first increment): its slope is at least `σT ≥ −ε`. -/
@[tmio T, powerlib_foundation] theorem classify_ne_forced_exact (hω0 : 0 < ω) (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hω : ω ^ 2 = k / m - σ ^ 2) {A₃ φ₃ : ℝ} {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (hσ0 : σ < 0)
    (hpos : periodPP x (2 * Real.pi / ω) 0 < periodPP x (2 * Real.pi / ω) 1) {ε : ℝ}
    (hεσ : -(σ * (2 * Real.pi / ω)) ≤ ε) {N : ℕ} (hN : 2 ≤ N) :
    classify ε (olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
      Real.log (peakToPeak x (i * (2 * Real.pi / ω)) ((i + 1) * (2 * Real.pi / ω)) -
        peakToPeak x ((i - 1) * (2 * Real.pi / ω)) (i * (2 * Real.pi / ω))))) ≠ .forced := by
  obtain ⟨h1, -⟩ := forced_slope_bounds hω0 hm hσ hω hss hx hv heq hx0 hv0 hσ0 hpos hN
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have hε : 0 ≤ ε := by nlinarith
  rw [Ne, classify_eq_forced_iff hε]
  linarith

end ForcedSlope

end powerlib.LTI.StartUp
