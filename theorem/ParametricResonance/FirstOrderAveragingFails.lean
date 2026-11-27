import theorem.ParametricResonance.ForcedPumpInteraction

/-! # First-order averaging fails on the time scale `1/ε` when the stiffness is quadratic

For the pumped oscillator with quadratic and cubic stiffness of
`theorem/ParametricResonance/QuadraticCubicNormalForm.lean`,
`ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = u(t)`, first-order averaging predicts the
oscillation `√ε Re(W₁ e^{jνt})` with the cubic coefficient `β₁ = 3α₃/(8ν)` — the quadratic
stiffness has no resonant part and is dropped — while the second-order amplitude equation has
`β₂ = β₁ − 5α₂²/(12ν³)` and is accurate to `O(ε)` on the time scale `1/ε`
(`QuadraticCubic.second_order_averaging`). The two averaged flows differ by the pure frequency
shift `jγ|W|²W`, `γ = 5α₂²/(12ν³)`, so their solutions from (almost) the same initial value
separate linearly in the slow time `εt` with the rate `γ|w(0)|³` (`separation`). Hence for
`α₂ ≠ 0`, `w(0) ≠ 0` the first-order prediction is wrong by a fixed fraction of the amplitude `√ε`
somewhere in `[0, L/ε]` (`first_order_fails`, `first_order_fails_sqrt`), whereas on the time scale
`1/√ε` it is accurate to `O(ε)`, a relative error `O(√ε)` (`first_order_short`). This makes
precise the remark of `QuadraticCubicNormalForm` that "first-order averaging controls the error
only on the time scale `1/√ε`".

Scope.
* The oscillator, scaling and hypotheses of `QuadraticCubic.second_order_averaging` (`ν > 0`,
  `0 < ε ≤ 1`, a solution `x` on all of `ℝ`, the input bound `|u| ≤ ε²M_u` while
  `|w| ≤ 2(R + 1)`, the branch condition, `errSecond … < 1`); the second-order averaged solution
  `W₂` from the transformed initial value and the first-order prediction `W₁` from the scaled
  initial amplitude `w(0)` are given on the window and stay in the disc of radius `R` (as in
  `QuadraticCubic.second_order_averaging`, existence of these solutions is a hypothesis).
* Exact statements: the bound and the Lipschitz constant of the cubic amplitude field on discs
  (`norm_ampField_le`, `norm_ampField_sub_le`), the frequency-shift difference
  (`ampField_sub_beta`), the drift and separation of averaged solutions (`norm_sub_le_drift`,
  `separation`), two readings a quarter period apart (`norm_le_abs_re_add_abs_re`).
* The lower bound is for the supremum over `[0, L/ε]` (attained at `L/ε` or a quarter period
  earlier, `L/ε ≥ π/(2ν)`), with an explicit leading constant `failConst` (positive for `α₂ ≠ 0`,
  `w(0) ≠ 0` and small `L`, `failConst_pos`) and an explicit correction `failErr = O(√ε)`
  (`failErr_le`); the upper bounds use Grönwall's lemma (Mathlib's
  `norm_le_gronwallBound_of_norm_deriv_right_le`).
* Generic mathematics, no model family.

Source: second-order averaging and the failure of first-order averaging for quadratic
nonlinearities (Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear Dynamical Systems*,
Ch. 2.9 (second-order averaging, the time scale of validity); Nayfeh–Mook, *Nonlinear
Oscillations*, Ch. 4 (the frequency correction `−5α₂²a²/(12ω₀³)` of a quadratic stiffness)); the
second-order theorem `QuadraticCubic.second_order_averaging`, its average
`QuadraticCubic.fieldAverage_secondField`, the near-identity bound `QuadraticCubic.norm_nearId_le`.

Sharpenings.
* The claim of `QuadraticCubicNormalForm` ("first-order averaging controls the error only on the
  time scale `1/√ε`, recorded, not formalized") is proved in both directions: on `[0, L/√ε]` the
  first-order error is `≤ C ε` (`first_order_short`); on `[0, L/ε]` it is `≥ (c/2)√ε` for all small
  `ε` (`first_order_fails_sqrt`), and `≤ C'√ε` (`first_order_upper`): first-order averaging gets
  the order of the amplitude right on `1/ε` but not the phase.
* The mechanism is the phase drift `ε γ|w|²t` between the two averaged rotations; the rate
  `γ|w(0)|³` of the separation is exact, the rest is a second-order term in the slow time.

Results.
* `ampBound`, `ampLip`, `norm_ampField_le`, `norm_ampField_sub_le`, `ampField_sub_beta` — the
  cubic amplitude field on discs; two cubic coefficients differ by `j(β₂ − β₁)|W|²W`.
* `norm_sub_le_drift`, `separation` — `|W(t) − W(s)| ≤ εM(t − s)`; the difference of the two
  averaged solutions is `D(0) + εt j(β₂ − β₁)|W₁(0)|²W₁(0)` up to `εt(ℓ₂(εtM₂ + |D(0)|) + ℓ₁εtM₁)`.
* `norm_le_abs_re_add_abs_re` — `|A| ≤ |Re(A e^{jνt})| + |Re(A e^{jν(t + π/(2ν))})|`.
* `failConst`, `failErr`, `failErrOne`, `failConst_pos`, `errSecond_le_sqrt`, `failErr_le` — the
  constants of the lower bound; `errSecond = O(√ε)`.
* `first_order_fails` — **first-order averaging fails on `1/ε`**: some `t ∈ [0, L/ε]` has
  `|x(t) − √ε Re(W₁(t) e^{jνt})| ≥ √ε (failConst … − failErr …)`.
* `first_order_fails_sqrt` — the same with `≥ (failConst/2)√ε` once `√ε failErrOne ≤ failConst/2`.
* `first_order_upper` — on `[0, L/ε]`,
  `|x − √ε Re(W₁ e^{jνt})| ≤ √ε (B + √ε c₁(2(R + 1))² + (√ε c₁|w(0)|² + LγR³)e^{ℓ₂L})`.
* `errSecond_short`, `first_order_short` — **first-order averaging is accurate on `1/√ε`**: on
  `[0, L/√ε]` the error is `≤ ε (errSecond … L 1 … + c₁(2(R + 1))² + (c₁|w(0)|² + LγR³)e^{ℓ₂L})`.
-/

noncomputable section
namespace powerlib.ParametricResonance.FirstOrderFails

open Complex Set
open DuffingMathieu (vdp accel)
open QuadraticCubic (phase nearId errSecond)
open Saturation (ampField)

/-- A bound `(|σ| + |Δ| + |c| + |β|R²)R` of the cubic amplitude field (`η = 0`) on the disc of
radius `R` (`norm_ampField_le`), with `cn = |c|`. -/
def ampBound (σ Δ cn β R : ℝ) : ℝ := (|σ| + |Δ| + cn + |β| * R ^ 2) * R

/-- A Lipschitz constant `|σ| + |Δ| + |c| + 3|β|R²` of the cubic amplitude field (`η = 0`) on the
disc of radius `R` (`norm_ampField_sub_le`), with `cn = |c|`. -/
def ampLip (σ Δ cn β R : ℝ) : ℝ := |σ| + |Δ| + cn + 3 * |β| * R ^ 2

variable {σ Δ β : ℝ} {c : ℂ}

@[tmio T, powerlib_foundation] private theorem ampField_eq' (σ Δ : ℝ) (c : ℂ) (β : ℝ) (W : ℂ) :
    ampField σ Δ c 0 β W = -((σ : ℂ) + Δ * I) * W + c * (starRingEnd ℂ) W +
      (β * I) * ((‖W‖ ^ 2 : ℝ) : ℂ) * W := by
  simp [ampField, slowFlowField]

@[tmio T, powerlib_foundation] private theorem norm_sigma_le (σ Δ : ℝ) :
    ‖(σ : ℂ) + Δ * I‖ ≤ |σ| + |Δ| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

/-- **The cubic amplitude field is bounded on discs:** `|F(W)| ≤ (|σ| + |Δ| + |c| + |β|R²)R` for
`|W| ≤ R`. -/
@[tmio T, powerlib_foundation] theorem norm_ampField_le {R : ℝ} {W : ℂ} (hW : ‖W‖ ≤ R) :
    ‖ampField σ Δ c 0 β W‖ ≤ ampBound σ Δ ‖c‖ β R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hW
  have h1 := norm_sigma_le σ Δ
  rw [ampField_eq']
  have t1 : ‖-((σ : ℂ) + Δ * I) * W‖ ≤ (|σ| + |Δ|) * R := by
    rw [norm_mul, norm_neg]; gcongr
  have t2 : ‖c * (starRingEnd ℂ) W‖ ≤ ‖c‖ * R := by
    rw [norm_mul, Complex.norm_conj]; gcongr
  have t3 : ‖(β * I) * ((‖W‖ ^ 2 : ℝ) : ℂ) * W‖ ≤ |β| * R ^ 2 * R := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    gcongr
  calc _ ≤ ‖-((σ : ℂ) + Δ * I) * W‖ + ‖c * (starRingEnd ℂ) W‖ +
        ‖(β * I) * ((‖W‖ ^ 2 : ℝ) : ℂ) * W‖ := norm_add₃_le
    _ ≤ (|σ| + |Δ|) * R + ‖c‖ * R + |β| * R ^ 2 * R := by linarith
    _ = ampBound σ Δ ‖c‖ β R := by unfold ampBound; ring

/-- **The cubic amplitude field is Lipschitz on discs:** `|F(W) − F(V)| ≤
(|σ| + |Δ| + |c| + 3|β|R²)|W − V|` for `|W|, |V| ≤ R`. -/
@[tmio T, powerlib_foundation] theorem norm_ampField_sub_le {R : ℝ} {W V : ℂ} (hW : ‖W‖ ≤ R)
    (hV : ‖V‖ ≤ R) :
    ‖ampField σ Δ c 0 β W - ampField σ Δ c 0 β V‖ ≤ ampLip σ Δ ‖c‖ β R * ‖W - V‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hW
  have h1 := norm_sigma_le σ Δ
  set d := ‖W - V‖ with hd
  have e : ampField σ Δ c 0 β W - ampField σ Δ c 0 β V =
      -((σ : ℂ) + Δ * I) * (W - V) + c * (starRingEnd ℂ) (W - V) +
        (β * I) * (((‖W‖ ^ 2 : ℝ) : ℂ) * (W - V) + ((‖W‖ ^ 2 - ‖V‖ ^ 2 : ℝ) : ℂ) * V) := by
    rw [ampField_eq', ampField_eq', map_sub]; push_cast; ring
  have hsq : |‖W‖ ^ 2 - ‖V‖ ^ 2| ≤ 2 * R * d := by
    rw [sq_sub_sq, abs_mul]
    have ha : |‖W‖ - ‖V‖| ≤ d := abs_norm_sub_norm_le W V
    have hb : |‖W‖ + ‖V‖| ≤ 2 * R := by
      rw [abs_of_nonneg (by positivity)]; linarith
    exact mul_le_mul hb ha (abs_nonneg _) (by positivity)
  have t1 : ‖-((σ : ℂ) + Δ * I) * (W - V)‖ ≤ (|σ| + |Δ|) * d := by
    rw [norm_mul, norm_neg]; gcongr
  have t2 : ‖c * (starRingEnd ℂ) (W - V)‖ ≤ ‖c‖ * d := by
    rw [norm_mul, Complex.norm_conj]
  have t3 : ‖(β * I) * (((‖W‖ ^ 2 : ℝ) : ℂ) * (W - V) + ((‖W‖ ^ 2 - ‖V‖ ^ 2 : ℝ) : ℂ) * V)‖ ≤
      |β| * (R ^ 2 * d + 2 * R * d * R) := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      gcongr
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
  rw [e]
  calc _ ≤ ‖-((σ : ℂ) + Δ * I) * (W - V)‖ + ‖c * (starRingEnd ℂ) (W - V)‖ +
        ‖(β * I) * (((‖W‖ ^ 2 : ℝ) : ℂ) * (W - V) + ((‖W‖ ^ 2 - ‖V‖ ^ 2 : ℝ) : ℂ) * V)‖ :=
        norm_add₃_le
    _ ≤ (|σ| + |Δ|) * d + ‖c‖ * d + |β| * (R ^ 2 * d + 2 * R * d * R) := by linarith
    _ = ampLip σ Δ ‖c‖ β R * d := by unfold ampLip; ring

/-- The two cubic coefficients differ by a pure frequency shift:
`F_{β₂}(W) − F_{β₁}(W) = j(β₂ − β₁)|W|²W`. -/
@[tmio T, powerlib_foundation] theorem ampField_sub_beta (σ Δ : ℝ) (c : ℂ) (β₁ β₂ : ℝ) (W : ℂ) :
    ampField σ Δ c 0 β₂ W - ampField σ Δ c 0 β₁ W =
      (((β₂ - β₁) : ℝ) : ℂ) * I * ((‖W‖ ^ 2 : ℝ) : ℂ) * W := by
  rw [ampField_eq', ampField_eq']; push_cast; ring


/-! ## Two averaged flows with different cubic coefficients -/

/-- **Slow drift of an averaged solution:** a solution of `Ẇ = εF(W)` in the disc of radius `R`
moves at most `ε M (t − s)` on `[s, t]`, `M = ampBound …`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_le_drift {ε T R : ℝ} (hε : 0 ≤ ε) {W : ℝ → ℂ}
    (hW : ∀ t ∈ Icc 0 T, HasDerivWithinAt W (ε • ampField σ Δ c 0 β (W t)) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, ‖W t‖ ≤ R) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ‖W t - W s‖ ≤ ε * ampBound σ Δ ‖c‖ β R * (t - s) := by
  have hsub : Icc s t ⊆ Icc 0 T := Icc_subset_Icc hs ht
  refine norm_image_sub_le_of_norm_deriv_le_segment' (f := W)
    (fun y hy => (hW y (hsub hy)).mono hsub) (fun y hy => ?_) t ⟨hst, le_rfl⟩
  rw [norm_smul, Real.norm_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left (norm_ampField_le (hb y (hsub (Ico_subset_Icc_self hy)))) hε

/-- **Separation of two averaged flows.** Let `W₁, W₂` solve `Ẇ = εF_{β₁}(W)`, `Ẇ = εF_{β₂}(W)`
(the cubic amplitude field with the same `σ, Δ, c` and `η = 0`) on `[0, T]` in the disc of radius
`R`. Then their difference grows linearly in the slow time `εt` with the rate
`F_{β₂}(W₁(0)) − F_{β₁}(W₁(0)) = j(β₂ − β₁)|W₁(0)|²W₁(0)`, up to a second-order term:
`|D(t) − D(0) − εt j(β₂ − β₁)|W₁(0)|²W₁(0)| ≤ εt (ℓ₂(εtM₂ + |D(0)|) + ℓ₁εtM₁)`, `D = W₂ − W₁`. -/
@[tmio T, powerlib_foundation] theorem separation {ε T R β₁ β₂ : ℝ} (hε : 0 ≤ ε)
    {W₁ W₂ : ℝ → ℂ}
    (hW₁ : ∀ t ∈ Icc 0 T, HasDerivWithinAt W₁ (ε • ampField σ Δ c 0 β₁ (W₁ t)) (Icc 0 T) t)
    (hW₂ : ∀ t ∈ Icc 0 T, HasDerivWithinAt W₂ (ε • ampField σ Δ c 0 β₂ (W₂ t)) (Icc 0 T) t)
    (hb₁ : ∀ t ∈ Icc 0 T, ‖W₁ t‖ ≤ R) (hb₂ : ∀ t ∈ Icc 0 T, ‖W₂ t‖ ≤ R) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(W₂ t - W₁ t) - (W₂ 0 - W₁ 0) -
        (ε * t) • ((((β₂ - β₁) : ℝ) : ℂ) * I * ((‖W₁ 0‖ ^ 2 : ℝ) : ℂ) * W₁ 0)‖ ≤
      ε * t * (ampLip σ Δ ‖c‖ β₂ R * (ε * t * ampBound σ Δ ‖c‖ β₂ R + ‖W₂ 0 - W₁ 0‖) +
        ampLip σ Δ ‖c‖ β₁ R * (ε * t * ampBound σ Δ ‖c‖ β₁ R)) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  set w₀ := W₁ 0
  set Δ₀ := (((β₂ - β₁) : ℝ) : ℂ) * I * ((‖w₀‖ ^ 2 : ℝ) : ℂ) * w₀ with hΔ₀
  set ℓ₁ := ampLip σ Δ ‖c‖ β₁ R
  set ℓ₂ := ampLip σ Δ ‖c‖ β₂ R
  set M₁ := ampBound σ Δ ‖c‖ β₁ R
  set M₂ := ampBound σ Δ ‖c‖ β₂ R
  have hR : 0 ≤ R := (norm_nonneg _).trans (hb₁ 0 h0T)
  have hℓ₁ : 0 ≤ ℓ₁ := by simp only [ℓ₁, ampLip]; positivity
  have hℓ₂ : 0 ≤ ℓ₂ := by simp only [ℓ₂, ampLip]; positivity
  have hM₂ : 0 ≤ M₂ := by simp only [M₂, ampBound]; positivity
  have hM₁ : 0 ≤ M₁ := by simp only [M₁, ampBound]; positivity
  set g : ℝ → ℂ := fun s => (W₂ s - W₁ s) - (W₂ 0 - W₁ 0) - (ε * s) • Δ₀ with hg
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hgd : ∀ s ∈ Icc 0 t, HasDerivWithinAt g
      (ε • ampField σ Δ c 0 β₂ (W₂ s) - ε • ampField σ Δ c 0 β₁ (W₁ s) - ε • Δ₀) (Icc 0 t) s := by
    intro s hs
    have h1 := ((hW₂ s (hsub hs)).mono hsub).sub ((hW₁ s (hsub hs)).mono hsub)
    have h2 := (((hasDerivAt_id s).const_mul ε).hasDerivWithinAt (s := Icc 0 t)).smul_const Δ₀
    have h3 := (h1.sub_const (W₂ 0 - W₁ 0)).sub h2
    convert h3 using 1
    · funext y; simp only [hg, Pi.sub_apply, id]
    · rw [mul_one]
  have hbound : ∀ s ∈ Ico 0 t, ‖ε • ampField σ Δ c 0 β₂ (W₂ s) - ε • ampField σ Δ c 0 β₁ (W₁ s) -
      ε • Δ₀‖ ≤ ε * (ℓ₂ * (ε * t * M₂ + ‖W₂ 0 - W₁ 0‖) + ℓ₁ * (ε * t * M₁)) := by
    intro s hs
    have hs' : s ∈ Icc 0 T := hsub (Ico_subset_Icc_self hs)
    have hΔ : Δ₀ = ampField σ Δ c 0 β₂ w₀ - ampField σ Δ c 0 β₁ w₀ :=
      (ampField_sub_beta σ Δ c β₁ β₂ w₀).symm
    have e : ε • ampField σ Δ c 0 β₂ (W₂ s) - ε • ampField σ Δ c 0 β₁ (W₁ s) - ε • Δ₀ =
        ε • ((ampField σ Δ c 0 β₂ (W₂ s) - ampField σ Δ c 0 β₂ w₀) -
          (ampField σ Δ c 0 β₁ (W₁ s) - ampField σ Δ c 0 β₁ w₀)) := by
      simp only [hΔ, smul_sub]; abel
    have d₂ := norm_sub_le_drift hε hW₂ hb₂ le_rfl hs'.1 hs'.2
    have d₁ := norm_sub_le_drift hε hW₁ hb₁ le_rfl hs'.1 hs'.2
    rw [sub_zero] at d₁ d₂
    have l₂ := norm_ampField_sub_le (σ := σ) (Δ := Δ) (c := c) (β := β₂) (hb₂ s hs') (hb₁ 0 h0T)
    have l₁ := norm_ampField_sub_le (σ := σ) (Δ := Δ) (c := c) (β := β₁) (hb₁ s hs') (hb₁ 0 h0T)
    have hw2 : ‖W₂ s - w₀‖ ≤ ε * t * M₂ + ‖W₂ 0 - W₁ 0‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (W₂ s) (W₂ 0) w₀
      have hst : ε * M₂ * s ≤ ε * t * M₂ := by
        have := hs.2.le; nlinarith [mul_nonneg hε hM₂]
      linarith
    have hw1 : ‖W₁ s - w₀‖ ≤ ε * t * M₁ := by
      have hst : ε * M₁ * s ≤ ε * t * M₁ := by
        have := hs.2.le; nlinarith [mul_nonneg hε hM₁]
      linarith
    rw [e, norm_smul, Real.norm_of_nonneg hε]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) hε
    · exact l₂.trans (mul_le_mul_of_nonneg_left hw2 hℓ₂)
    · exact l₁.trans (mul_le_mul_of_nonneg_left hw1 hℓ₁)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hgd hbound t ⟨ht.1, le_rfl⟩
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, sub_zero] at hmv
  calc ‖g t‖ ≤ ε * (ℓ₂ * (ε * t * M₂ + ‖W₂ 0 - W₁ 0‖) + ℓ₁ * (ε * t * M₁)) * t := hmv
    _ = _ := by ring

/-- A complex amplitude shows at least half its size in one of two readings a quarter period
apart: `|Re(A e^{jνt})| + |Re(A e^{jν(t + π/(2ν))})| ≥ |A|`. -/
@[tmio T, powerlib_foundation] theorem norm_le_abs_re_add_abs_re {ν : ℝ} (hν : 0 < ν) (A : ℂ)
    (t : ℝ) :
    ‖A‖ ≤ |(A * phase ν t).re| + |(A * phase ν (t + Real.pi / (2 * ν))).re| := by
  have hq : phase ν (Real.pi / (2 * ν)) = I := by
    have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
    rw [QuadraticCubic.phase, show ((ν * (Real.pi / (2 * ν)) : ℝ) : ℂ) * I =
      ((Real.pi / 2 : ℝ) : ℂ) * I by congr 1; push_cast; field_simp, Complex.exp_mul_I]
    simp
  have hp : phase ν (t + Real.pi / (2 * ν)) = phase ν t * I := by
    rw [ForcedPump.phase_add, hq]
  rw [hp, ← mul_assoc, Complex.mul_I_re, abs_neg]
  have hn : ‖A‖ = ‖A * phase ν t‖ := by
    rw [norm_mul, show ‖phase ν t‖ = 1 from Complex.norm_exp_ofReal_mul_I _, mul_one]
  rw [hn]
  exact Complex.norm_le_abs_re_add_abs_im _


/-! ## First-order averaging misses the quadratic stiffness on the time scale `1/ε` -/

/-- The leading constant of the error of first-order averaging,
`c = L(γw³ − L(ℓ₂M₂ + ℓ₁M₁))/2`, `γ = 5α₂²/(12ν³)`, for the initial scaled amplitude `|w(0)| = w`;
`M_i`, `ℓ_i` are the bound and the Lipschitz constant on the disc of radius `R` of the first-order
(`β₁ = 3α₃/(8ν)`) and second-order (`β₂ = β₁ − γ`) averaged fields (`failConst_pos`). -/
def failConst (b d k₁ α₂ α₃ ν R L w : ℝ) : ℝ :=
  L * (5 * α₂ ^ 2 / (12 * ν ^ 3) * w ^ 3 - L *
    (ampLip (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R *
      ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R +
     ampLip (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν)) (3 * α₃ / (8 * ν)) R *
      ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν)) (3 * α₃ / (8 * ν)) R)) / 2

/-- The correction to `failConst`: the error `B + √ε (5|α₂|/(6ν²))(2(R + 1))²` of second-order
averaging, the near-identity shift of the initial value, and the drift over a quarter period;
`O(√ε)` (`failErr_le`). -/
def failErr (b d k₁ α₂ α₃ ν R L ε Mu w : ℝ) : ℝ :=
  errSecond b d k₁ α₂ α₃ ν R L ε Mu + √ε * (5 * |α₂| / (6 * ν ^ 2)) * (2 * (R + 1)) ^ 2 +
    √ε * (5 * |α₂| / (6 * ν ^ 2)) * w ^ 2 *
      (1 + ampLip (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R * L) / 2 +
    ε * (ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν)) (3 * α₃ / (8 * ν)) R +
      ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R) * (Real.pi / (2 * ν))

@[tmio T, powerlib_foundation] private theorem norm_pump {ν : ℝ} (hν : 0 < ν) (k₁ : ℝ) :
    ‖I * ((k₁ / (4 * ν) : ℝ) : ℂ)‖ = |k₁| / (4 * ν) := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 4 * ν)]

@[tmio T, powerlib_foundation] private theorem abs_re_mul_phase_ge {ν : ℝ} (z z' : ℂ) (t : ℝ) :
    |(z' * phase ν t).re| - ‖z - z'‖ ≤ |(z * phase ν t).re| := by
  have h1 : (z * phase ν t).re = (z' * phase ν t).re + ((z - z') * phase ν t).re := by
    rw [← Complex.add_re]; ring_nf
  have h2 : |((z - z') * phase ν t).re| ≤ ‖z - z'‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, show ‖phase ν t‖ = 1 from Complex.norm_exp_ofReal_mul_I _, mul_one]
  rw [h1]
  have := abs_add_le ((z' * phase ν t).re + ((z - z') * phase ν t).re)
    (-((z - z') * phase ν t).re)
  rw [add_neg_cancel_right, abs_neg] at this
  linarith

/-- **First-order averaging fails on the time scale `1/ε` when `α₂ ≠ 0`.** In the setting of
`QuadraticCubic.second_order_averaging` (`ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = u`,
`ν > 0`, `0 < ε ≤ 1`, scaled amplitude `w = z/√ε`, the second-order averaged solution `W₂` from the
transformed initial value), let `W₁` be the first-order averaged prediction: the solution of
`Ẇ₁ = ε ampField (b/2) (d/(2ν)) (jk₁/(4ν)) 0 (3α₃/(8ν)) W₁` from `W₁(0) = w(0)` (the quadratic
stiffness ignored, as in first-order averaging), and let both stay in the disc `R` on `[0, L/ε]`,
`L/ε ≥ π/(2ν)`. Then at some `t ∈ [0, L/ε]`
`|x(t) − √ε Re(W₁(t) e^{jνt})| ≥ √ε (failConst … |w(0)| − failErr …)`, where `failConst` is a
fixed positive number for `α₂ ≠ 0`, `w(0) ≠ 0` and small `L` (`failConst_pos`) and
`failErr = O(√ε)` (`failErr_le`): the first-order prediction is wrong by a fixed fraction of the
amplitude `√ε` (the phase drift `ε(5α₂²/(12ν³))|w|²t` between the two averaged rotations). -/
@[tmio T, powerlib_foundation] theorem first_order_fails {ν : ℝ} (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) {x x' u : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x'
      (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) - α₂ * x t ^ 2 + u t) t)
    (hu : ∀ t ∈ Icc 0 (L / ε), ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)‖ ≤ 2 * (R + 1) →
      |u t| ≤ ε ^ 2 * Mu)
    {W₁ W₂ : ℝ → ℂ}
    (hW₂ : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt W₂
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (W₂ t)) (Icc 0 (L / ε)) t)
    (hb₂ : ∀ t ∈ Icc 0 (L / ε), ‖W₂ t‖ ≤ R)
    (h0₂ : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0)) 0 = W₂ 0)
    (hW₁ : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt W₁
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν)) (W₁ t)) (Icc 0 (L / ε)) t)
    (hb₁ : ∀ t ∈ Icc 0 (L / ε), ‖W₁ t‖ ≤ R)
    (h0₁ : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0) = W₁ 0)
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d k₁ α₂ α₃ ν R L ε Mu < 1) (hT : Real.pi / (2 * ν) ≤ L / ε) :
    ∃ t ∈ Icc 0 (L / ε), √ε * (failConst b d k₁ α₂ α₃ ν R L ‖W₁ 0‖ -
        failErr b d k₁ α₂ α₃ ν R L ε Mu ‖W₁ 0‖) ≤ |x t - √ε * (W₁ t * phase ν t).re| := by
  set T := L / ε with hTdef
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hT0 : 0 ≤ T := div_nonneg hL hε.le
  have hεT : ε * T = L := by rw [hTdef]; field_simp
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0⟩
  have hTT : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  set w₀ := W₁ 0 with hw₀
  set c₁ := 5 * |α₂| / (6 * ν ^ 2) with hc₁
  set γ := 5 * α₂ ^ 2 / (12 * ν ^ 3) with hγ
  set β₁ := 3 * α₃ / (8 * ν) with hβ₁
  set β₂ := 3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3) with hβ₂
  set cn := |k₁| / (4 * ν) with hcn
  set ℓ₁ := ampLip (b / 2) (d / (2 * ν)) cn β₁ R with hℓ₁
  set ℓ₂ := ampLip (b / 2) (d / (2 * ν)) cn β₂ R with hℓ₂
  set M₁ := ampBound (b / 2) (d / (2 * ν)) cn β₁ R with hM₁
  set M₂ := ampBound (b / 2) (d / (2 * ν)) cn β₂ R with hM₂
  have hℓ₂0 : 0 ≤ ℓ₂ := by simp only [hℓ₂, ampLip]; positivity
  have hM₁0 : 0 ≤ M₁ := by simp only [hM₁, ampBound]; positivity
  have hM₂0 : 0 ≤ M₂ := by simp only [hM₂, ampBound]; positivity
  have hγ0 : 0 ≤ γ := by positivity
  have hnc := norm_pump hν k₁
  -- the second-order averaged solution tracks the oscillation
  have hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0)‖ < 2 * (R + 1) := by
    rw [h0₁]; linarith [hb₁ 0 h0T]
  have hsec := QuadraticCubic.second_order_averaging hν hR hL hε hε1 hMu hx hx' hu hW₂ hb₂ h0₂
    hw0 hbranch hsmall
  set E₂ := errSecond b d k₁ α₂ α₃ ν R L ε Mu + √ε * c₁ * (2 * (R + 1)) ^ 2 with hE₂
  -- the initial values differ by the near-identity shift
  have hD0 : ‖W₂ 0 - W₁ 0‖ ≤ √ε * c₁ * ‖w₀‖ ^ 2 := by
    have e : W₂ 0 - W₁ 0 = -((√ε : ℂ) * nearId α₂ ν w₀ 0) := by
      rw [← h0₂, h0₁, hw₀]; ring
    rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left (QuadraticCubic.norm_nearId_le hν _ 0) hs0.le
  -- the separation at the end of the window
  have hsep := separation (σ := b / 2) (Δ := d / (2 * ν)) (c := I * ((k₁ / (4 * ν) : ℝ) : ℂ))
    hε.le hW₁ hW₂ hb₁ hb₂ hTT
  rw [hnc, hεT] at hsep
  set A := W₂ T - W₁ T with hA
  have hΔ₀ : ‖(L : ℝ) • ((((β₂ - β₁) : ℝ) : ℂ) * I * ((‖w₀‖ ^ 2 : ℝ) : ℂ) * w₀)‖ =
      L * (γ * ‖w₀‖ ^ 3) := by
    simp only [norm_smul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_pow, abs_norm, mul_one, abs_of_nonneg hL]
    rw [show β₂ - β₁ = -γ by rw [hβ₂, hβ₁, hγ]; ring, abs_neg, abs_of_nonneg hγ0]
    ring
  rw [← hcn, ← hℓ₁, ← hℓ₂, ← hM₁, ← hM₂] at hsep
  have hAlow : L * (γ * ‖w₀‖ ^ 3) - L * L * (ℓ₂ * M₂ + ℓ₁ * M₁) -
      √ε * c₁ * ‖w₀‖ ^ 2 * (1 + ℓ₂ * L) ≤ ‖A‖ := by
    set Δ₀ := (((β₂ - β₁) : ℝ) : ℂ) * I * ((‖w₀‖ ^ 2 : ℝ) : ℂ) * w₀ with hΔ₀def
    have h1 : ‖(L : ℝ) • Δ₀‖ ≤ ‖A‖ + ‖W₂ 0 - W₁ 0‖ + ‖A - (W₂ 0 - W₁ 0) - (L : ℝ) • Δ₀‖ := by
      have e : (L : ℝ) • Δ₀ = (A - (W₂ 0 - W₁ 0)) - (A - (W₂ 0 - W₁ 0) - (L : ℝ) • Δ₀) := by abel
      calc ‖(L : ℝ) • Δ₀‖ = ‖(A - (W₂ 0 - W₁ 0)) - (A - (W₂ 0 - W₁ 0) - (L : ℝ) • Δ₀)‖ := by
            rw [← e]
        _ ≤ ‖A - (W₂ 0 - W₁ 0)‖ + ‖A - (W₂ 0 - W₁ 0) - (L : ℝ) • Δ₀‖ := norm_sub_le _ _
        _ ≤ ‖A‖ + ‖W₂ 0 - W₁ 0‖ + ‖A - (W₂ 0 - W₁ 0) - (L : ℝ) • Δ₀‖ := by
            gcongr; exact norm_sub_le _ _
    rw [hΔ₀] at h1
    have h3 : L * (ℓ₂ * (L * M₂ + ‖W₂ 0 - W₁ 0‖) + ℓ₁ * (L * M₁)) ≤
        L * L * (ℓ₂ * M₂ + ℓ₁ * M₁) + √ε * c₁ * ‖w₀‖ ^ 2 * (ℓ₂ * L) := by
      have := mul_le_mul_of_nonneg_left hD0 (mul_nonneg hL hℓ₂0)
      nlinarith
    linarith [hsep]
  -- one of two readings a quarter period apart shows half of `A`
  have hq := norm_le_abs_re_add_abs_re hν A (T - Real.pi / (2 * ν))
  rw [sub_add_cancel] at hq
  have hdrift : ‖(W₂ (T - Real.pi / (2 * ν)) - W₁ (T - Real.pi / (2 * ν))) - A‖ ≤
      ε * (M₁ + M₂) * (Real.pi / (2 * ν)) := by
    have hp0 : 0 ≤ T - Real.pi / (2 * ν) := by linarith
    have hpT : T - Real.pi / (2 * ν) ≤ T := by
      have : 0 ≤ Real.pi / (2 * ν) := by positivity
      linarith
    have d₁ := norm_sub_le_drift (σ := b / 2) (Δ := d / (2 * ν))
      (c := I * ((k₁ / (4 * ν) : ℝ) : ℂ)) hε.le hW₁ hb₁ hp0 hpT le_rfl
    have d₂ := norm_sub_le_drift (σ := b / 2) (Δ := d / (2 * ν))
      (c := I * ((k₁ / (4 * ν) : ℝ) : ℂ)) hε.le hW₂ hb₂ hp0 hpT le_rfl
    rw [hnc, ← hcn, ← hM₁, sub_sub_cancel] at d₁
    rw [hnc, ← hcn, ← hM₂, sub_sub_cancel] at d₂
    rw [hA, show W₂ (T - Real.pi / (2 * ν)) - W₁ (T - Real.pi / (2 * ν)) - (W₂ T - W₁ T) =
      -(W₂ T - W₂ (T - Real.pi / (2 * ν))) + (W₁ T - W₁ (T - Real.pi / (2 * ν))) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    linarith
  have hread : ∃ t ∈ Icc 0 T, ‖A‖ / 2 - ε * (M₁ + M₂) * (Real.pi / (2 * ν)) ≤
      |((W₂ t - W₁ t) * phase ν t).re| := by
    have hpos : 0 ≤ ε * (M₁ + M₂) * (Real.pi / (2 * ν)) := by positivity
    by_cases hc : ‖A‖ / 2 ≤ |(A * phase ν T).re|
    · exact ⟨T, hTT, by rw [← hA]; linarith⟩
    · refine ⟨T - Real.pi / (2 * ν), ⟨by linarith, by
        have : 0 ≤ Real.pi / (2 * ν) := by positivity
        linarith⟩, ?_⟩
      have h1 := abs_re_mul_phase_ge (ν := ν)
        (W₂ (T - Real.pi / (2 * ν)) - W₁ (T - Real.pi / (2 * ν))) A (T - Real.pi / (2 * ν))
      linarith
  obtain ⟨t, ht, hre⟩ := hread
  refine ⟨t, ht, ?_⟩
  have hx2 := hsec t ht
  have hsplit : x t - √ε * (W₁ t * phase ν t).re =
      (x t - √ε * (W₂ t * phase ν t).re) + √ε * ((W₂ t - W₁ t) * phase ν t).re := by
    rw [sub_mul, Complex.sub_re]; ring
  have hlow : √ε * |((W₂ t - W₁ t) * phase ν t).re| - |x t - √ε * (W₂ t * phase ν t).re| ≤
      |x t - √ε * (W₁ t * phase ν t).re| := by
    rw [hsplit]
    have := abs_sub_abs_le_abs_sub (√ε * ((W₂ t - W₁ t) * phase ν t).re)
      (-(x t - √ε * (W₂ t * phase ν t).re))
    rw [abs_neg, sub_neg_eq_add, abs_mul, abs_of_pos hs0] at this
    linarith [this, show |√ε * ((W₂ t - W₁ t) * phase ν t).re + (x t -
      √ε * (W₂ t * phase ν t).re)| = |x t - √ε * (W₂ t * phase ν t).re +
        √ε * ((W₂ t - W₁ t) * phase ν t).re| by ring_nf]
  have hfin : √ε * (failConst b d k₁ α₂ α₃ ν R L ‖w₀‖ - failErr b d k₁ α₂ α₃ ν R L ε Mu ‖w₀‖) ≤
      √ε * |((W₂ t - W₁ t) * phase ν t).re| - √ε * E₂ := by
    have e : failConst b d k₁ α₂ α₃ ν R L ‖w₀‖ - failErr b d k₁ α₂ α₃ ν R L ε Mu ‖w₀‖ =
        (L * (γ * ‖w₀‖ ^ 3) - L * L * (ℓ₂ * M₂ + ℓ₁ * M₁) -
          √ε * c₁ * ‖w₀‖ ^ 2 * (1 + ℓ₂ * L)) / 2 - ε * (M₁ + M₂) * (Real.pi / (2 * ν)) - E₂ := by
      simp only [failConst, failErr, hE₂, hc₁, hγ, hℓ₁, hℓ₂, hM₁, hM₂, hβ₁, hβ₂, hcn]
      ring
    rw [e, mul_sub]
    have := mul_le_mul_of_nonneg_left (show (L * (γ * ‖w₀‖ ^ 3) - L * L * (ℓ₂ * M₂ + ℓ₁ * M₁) -
        √ε * c₁ * ‖w₀‖ ^ 2 * (1 + ℓ₂ * L)) / 2 - ε * (M₁ + M₂) * (Real.pi / (2 * ν)) ≤
        |((W₂ t - W₁ t) * phase ν t).re| by linarith) hs0.le
    linarith
  linarith


/-- The leading constant is positive for `α₂ ≠ 0`, `w(0) ≠ 0` and a window
`0 < L < γw³/(ℓ₂M₂ + ℓ₁M₁)`. -/
@[tmio T, powerlib_foundation] theorem failConst_pos {b d k₁ α₂ α₃ ν R L w : ℝ} (hL : 0 < L)
    (hsmall : L * (ampLip (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R *
      ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R +
     ampLip (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν)) (3 * α₃ / (8 * ν)) R *
      ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν)) (3 * α₃ / (8 * ν)) R) <
        5 * α₂ ^ 2 / (12 * ν ^ 3) * w ^ 3) :
    0 < failConst b d k₁ α₂ α₃ ν R L w := by
  unfold failConst
  have := sub_pos.mpr hsmall
  positivity

@[tmio T, powerlib_foundation] private theorem lipSecond_nonneg {ν : ℝ} (hν : 0 < ν)
    (b k₀ k₁ α₂ α₃ r : ℝ) : 0 ≤ QuadraticCubic.lipSecond b k₀ k₁ α₂ α₃ ν r := by
  unfold QuadraticCubic.lipSecond DuffingMathieu.lipConst; have := hν.le; positivity

@[tmio T, powerlib_foundation] private theorem remSecond_nonneg {ν : ℝ} (hν : 0 < ν)
    {b d k₁ α₂ α₃ R Mu : ℝ} (hR : 0 ≤ R) (hMu : 0 ≤ Mu) :
    0 ≤ QuadraticCubic.remSecond b d k₁ α₂ α₃ ν R Mu := by
  simp only [QuadraticCubic.remSecond, QuadraticCubic.lipSecond, DuffingMathieu.lipConst]
  have := hν.le; positivity

/-- **The second-order error is `O(√ε)`:** `errSecond … ε ≤ √ε · errSecond … 1` for
`0 < ε ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem errSecond_le_sqrt {ν : ℝ} (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) :
    errSecond b d k₁ α₂ α₃ ν R L ε Mu ≤ √ε * errSecond b d k₁ α₂ α₃ ν R L 1 Mu := by
  have hℓ := lipSecond_nonneg hν b (ν ^ 2 - d) k₁ α₂ α₃ (2 * (R + 1))
  have hq := remSecond_nonneg hν (b := b) (d := d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hR hMu
  have hεs : ε ≤ √ε := by
    calc ε = √ε * √ε := (Real.mul_self_sqrt hε.le).symm
      _ ≤ √ε * 1 := by gcongr; exact Real.sqrt_le_one.mpr hε1
      _ = √ε := mul_one _
  simp only [errSecond, Real.sqrt_one, mul_one, one_mul]
  set ℓ := QuadraticCubic.lipSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν (2 * (R + 1))
  set q := QuadraticCubic.remSecond b d k₁ α₂ α₃ ν R Mu
  have hA : 0 ≤ 2 * ℓ * (ℓ * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν) := by positivity
  have hE : 0 < Real.exp (ℓ * L) := Real.exp_pos _
  have h1 : (2 * ℓ * (ℓ * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν)) * ε ≤
      (2 * ℓ * (ℓ * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν)) * √ε := mul_le_mul_of_nonneg_left hεs hA
  have h2 : ((2 * ℓ * (ℓ * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν)) * ε + L * (√ε * q)) ≤
      √ε * ((2 * ℓ * (ℓ * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν)) + L * q) := by nlinarith
  calc _ ≤ √ε * ((2 * ℓ * (ℓ * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν)) + L * q) * Real.exp (ℓ * L) :=
        mul_le_mul_of_nonneg_right h2 hE.le
    _ = _ := by ring

/-- The `ε`-free correction constant: `failErr … ε … ≤ √ε · failErrOne …` (`failErr_le`). -/
def failErrOne (b d k₁ α₂ α₃ ν R L Mu w : ℝ) : ℝ :=
  errSecond b d k₁ α₂ α₃ ν R L 1 Mu + 5 * |α₂| / (6 * ν ^ 2) * (2 * (R + 1)) ^ 2 +
    5 * |α₂| / (6 * ν ^ 2) * w ^ 2 *
      (1 + ampLip (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R * L) / 2 +
    (ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν)) (3 * α₃ / (8 * ν)) R +
      ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R) * (Real.pi / (2 * ν))

/-- **The correction is `O(√ε)`:** `failErr … ε … ≤ √ε · failErrOne …` (`0 < ε ≤ 1`). -/
@[tmio T, powerlib_foundation] theorem failErr_le {ν : ℝ} (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu w : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) :
    failErr b d k₁ α₂ α₃ ν R L ε Mu w ≤ √ε * failErrOne b d k₁ α₂ α₃ ν R L Mu w := by
  have h1 := errSecond_le_sqrt hν (b := b) (d := d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hR hL hε hε1
    hMu
  have hεs : ε ≤ √ε := by
    calc ε = √ε * √ε := (Real.mul_self_sqrt hε.le).symm
      _ ≤ √ε * 1 := by gcongr; exact Real.sqrt_le_one.mpr hε1
      _ = √ε := mul_one _
  have hM : 0 ≤ (ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν)) (3 * α₃ / (8 * ν)) R +
      ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R) * (Real.pi / (2 * ν)) := by
    unfold ampBound; positivity
  have h3 := mul_le_mul_of_nonneg_right hεs hM
  simp only [failErr, failErrOne]
  nlinarith

/-- **First-order averaging fails by a fixed fraction of the amplitude, for all small `ε`.** In
the setting of `first_order_fails`, if moreover `√ε · failErrOne … ≤ failConst …/2`, then at some
`t ∈ [0, L/ε]` the first-order prediction is off by at least `(failConst/2)√ε`:
`|x(t) − √ε Re(W₁(t) e^{jνt})| ≥ (c/2)√ε`, `c = failConst … |w(0)| > 0` (`failConst_pos`), whereas
the second-order prediction is within `O(ε)` (`QuadraticCubic.second_order_averaging`). -/
@[tmio T, powerlib_foundation] theorem first_order_fails_sqrt {ν : ℝ} (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) {x x' u : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x'
      (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) - α₂ * x t ^ 2 + u t) t)
    (hu : ∀ t ∈ Icc 0 (L / ε), ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)‖ ≤ 2 * (R + 1) →
      |u t| ≤ ε ^ 2 * Mu)
    {W₁ W₂ : ℝ → ℂ}
    (hW₂ : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt W₂
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (W₂ t)) (Icc 0 (L / ε)) t)
    (hb₂ : ∀ t ∈ Icc 0 (L / ε), ‖W₂ t‖ ≤ R)
    (h0₂ : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0)) 0 = W₂ 0)
    (hW₁ : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt W₁
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν)) (W₁ t)) (Icc 0 (L / ε)) t)
    (hb₁ : ∀ t ∈ Icc 0 (L / ε), ‖W₁ t‖ ≤ R)
    (h0₁ : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0) = W₁ 0)
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d k₁ α₂ α₃ ν R L ε Mu < 1) (hT : Real.pi / (2 * ν) ≤ L / ε)
    (hεc : √ε * failErrOne b d k₁ α₂ α₃ ν R L Mu ‖W₁ 0‖ ≤
      failConst b d k₁ α₂ α₃ ν R L ‖W₁ 0‖ / 2) :
    ∃ t ∈ Icc 0 (L / ε), √ε * (failConst b d k₁ α₂ α₃ ν R L ‖W₁ 0‖ / 2) ≤
      |x t - √ε * (W₁ t * phase ν t).re| := by
  obtain ⟨t, ht, h⟩ := first_order_fails hν hR hL hε hε1 hMu hx hx' hu hW₂ hb₂ h0₂ hW₁ hb₁ h0₁
    hbranch hsmall hT
  refine ⟨t, ht, le_trans ?_ h⟩
  have h1 := failErr_le hν (b := b) (d := d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃)
    (w := ‖W₁ 0‖) hR hL hε hε1 hMu
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg ε)


/-! ## First-order averaging is accurate on the time scale `1/√ε` -/

@[tmio T, powerlib_foundation] private theorem gronwallBound_le' {δ K e x : ℝ} (hK : 0 ≤ K)
    (he : 0 ≤ e) :
    gronwallBound δ K e x ≤ (δ + e * x) * Real.exp (K * x) := by
  rcases eq_or_lt_of_le hK with h0 | hpos
  · rw [← h0, gronwallBound_K0]; simp
  · rw [gronwallBound_of_K_ne_0 hpos.ne']
    have key : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have h1 := Real.add_one_le_exp (-(K * x))
      have h2 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h3 := Real.exp_pos (K * x)
      nlinarith
    have h4 : e / K * (Real.exp (K * x) - 1) ≤ e * x * Real.exp (K * x) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      have := mul_le_mul_of_nonneg_left key he
      linarith
    linarith

/-- **First-order averaging up to the slow time `L`, from above.** In the setting of
`first_order_fails` (without the window condition), on `[0, L/ε]`
`|x(t) − √ε Re(W₁(t) e^{jνt})| ≤ √ε (B + √ε c₁(2(R + 1))² + (√ε c₁|w(0)|² + LγR³) e^{ℓ₂L})`,
`c₁ = 5|α₂|/(6ν²)`, `γ = 5α₂²/(12ν³)`, `ℓ₂` the Lipschitz constant of the second-order averaged
field on the disc `R` (Grönwall for `W₂ − W₁`, whose fields differ by `jγ|W|²W`): the first-order
prediction has the right order `√ε`, with a relative error `O(√ε) + O(L)`. -/
@[tmio T, powerlib_foundation] theorem first_order_upper {ν : ℝ} (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) {x x' u : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x'
      (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) - α₂ * x t ^ 2 + u t) t)
    (hu : ∀ t ∈ Icc 0 (L / ε), ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)‖ ≤ 2 * (R + 1) →
      |u t| ≤ ε ^ 2 * Mu)
    {W₁ W₂ : ℝ → ℂ}
    (hW₂ : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt W₂
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (W₂ t)) (Icc 0 (L / ε)) t)
    (hb₂ : ∀ t ∈ Icc 0 (L / ε), ‖W₂ t‖ ≤ R)
    (h0₂ : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0)) 0 = W₂ 0)
    (hW₁ : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt W₁
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν)) (W₁ t)) (Icc 0 (L / ε)) t)
    (hb₁ : ∀ t ∈ Icc 0 (L / ε), ‖W₁ t‖ ≤ R)
    (h0₁ : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0) = W₁ 0)
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d k₁ α₂ α₃ ν R L ε Mu < 1) :
    ∀ t ∈ Icc 0 (L / ε), |x t - √ε * (W₁ t * phase ν t).re| ≤
      √ε * (errSecond b d k₁ α₂ α₃ ν R L ε Mu + √ε * (5 * |α₂| / (6 * ν ^ 2)) * (2 * (R + 1)) ^ 2 +
        (√ε * (5 * |α₂| / (6 * ν ^ 2)) * ‖W₁ 0‖ ^ 2 + L * (5 * α₂ ^ 2 / (12 * ν ^ 3) * R ^ 3)) *
          Real.exp (ampLip (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
            (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R * L)) := by
  set T := L / ε with hTdef
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hT0 : 0 ≤ T := div_nonneg hL hε.le
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0⟩
  set c₁ := 5 * |α₂| / (6 * ν ^ 2) with hc₁
  set γ := 5 * α₂ ^ 2 / (12 * ν ^ 3) with hγ
  set β₂ := 3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3) with hβ₂
  set β₁ := 3 * α₃ / (8 * ν) with hβ₁
  have hnc := norm_pump hν k₁
  set ℓ₂ := ampLip (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν)) β₂ R with hℓ₂
  have hℓ₂0 : 0 ≤ ℓ₂ := by simp only [hℓ₂, ampLip]; positivity
  have hγ0 : 0 ≤ γ := by positivity
  have hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0)‖ < 2 * (R + 1) := by
    rw [h0₁]; linarith [hb₁ 0 h0T]
  have hsec := QuadraticCubic.second_order_averaging hν hR hL hε hε1 hMu hx hx' hu hW₂ hb₂ h0₂
    hw0 hbranch hsmall
  have hD0 : ‖W₂ 0 - W₁ 0‖ ≤ √ε * c₁ * ‖W₁ 0‖ ^ 2 := by
    have e : W₂ 0 - W₁ 0 = -((√ε : ℂ) * nearId α₂ ν (W₁ 0) 0) := by
      rw [← h0₂, h0₁]; ring
    rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left (QuadraticCubic.norm_nearId_le hν _ 0) hs0.le
  -- Grönwall for the difference of the two averaged solutions
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => W₂ t - W₁ t)
    (f' := fun t => ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 β₂ (W₂ t) -
      ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 β₁ (W₁ t))
    (δ := ‖W₂ 0 - W₁ 0‖) (K := ε * ℓ₂) (ε := ε * (γ * R ^ 3)) (a := 0) (b := T)
    (fun t ht => ((hW₂ t ht).continuousWithinAt.sub (hW₁ t ht).continuousWithinAt))
    (fun t ht => ((hW₂ t (Ico_subset_Icc_self ht)).sub
      (hW₁ t (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    le_rfl (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      have l₂ := norm_ampField_sub_le (σ := b / 2) (Δ := d / (2 * ν))
        (c := I * ((k₁ / (4 * ν) : ℝ) : ℂ)) (β := β₂) (hb₂ t ht') (hb₁ t ht')
      rw [hnc] at l₂
      have hcub : ‖ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 β₂ (W₁ t) -
          ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 β₁ (W₁ t)‖ ≤
          γ * R ^ 3 := by
        rw [ampField_sub_beta]
        simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_pow,
          abs_norm, mul_one]
        rw [show β₂ - β₁ = -γ by rw [hβ₂, hβ₁, hγ]; ring, abs_neg, abs_of_nonneg hγ0]
        have := hb₁ t ht'
        calc γ * ‖W₁ t‖ ^ 2 * ‖W₁ t‖ = γ * ‖W₁ t‖ ^ 3 := by ring
          _ ≤ γ * R ^ 3 := by gcongr
      have e : ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 β₂ (W₂ t) -
          ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 β₁ (W₁ t) =
          ε • ((ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 β₂ (W₂ t) -
            ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 β₂ (W₁ t)) +
          (ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 β₂ (W₁ t) -
            ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0 β₁ (W₁ t))) := by
        rw [smul_add, smul_sub, smul_sub]; abel
      show ‖_‖ ≤ ε * ℓ₂ * ‖W₂ t - W₁ t‖ + ε * (γ * R ^ 3)
      rw [e, norm_smul, Real.norm_of_nonneg hε.le]
      have := (norm_add_le _ _).trans (add_le_add l₂ hcub)
      calc ε * ‖_‖ ≤ ε * (ℓ₂ * ‖W₂ t - W₁ t‖ + γ * R ^ 3) :=
            mul_le_mul_of_nonneg_left this hε.le
        _ = ε * ℓ₂ * ‖W₂ t - W₁ t‖ + ε * (γ * R ^ 3) := by ring)
  intro t ht
  have hD : ‖W₂ t - W₁ t‖ ≤ (√ε * c₁ * ‖W₁ 0‖ ^ 2 + L * (γ * R ^ 3)) * Real.exp (ℓ₂ * L) := by
    have h1 := hgr t ht
    rw [sub_zero] at h1
    have hεt : ε * t ≤ L := by
      have := ht.2; rw [hTdef, le_div_iff₀ hε] at this; linarith
    refine h1.trans ((gronwallBound_le' (by positivity) (by positivity)).trans ?_)
    have hR3 : 0 ≤ γ * R ^ 3 := by positivity
    have a1 : ‖W₂ 0 - W₁ 0‖ + ε * (γ * R ^ 3) * t ≤ √ε * c₁ * ‖W₁ 0‖ ^ 2 + L * (γ * R ^ 3) := by
      nlinarith
    have a2 : Real.exp (ε * ℓ₂ * t) ≤ Real.exp (ℓ₂ * L) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul a1 a2 (Real.exp_pos _).le (by positivity)
  have hx2 := hsec t ht
  have hsplit : x t - √ε * (W₁ t * phase ν t).re =
      (x t - √ε * (W₂ t * phase ν t).re) + √ε * ((W₂ t - W₁ t) * phase ν t).re := by
    rw [sub_mul, Complex.sub_re]; ring
  have hre : |((W₂ t - W₁ t) * phase ν t).re| ≤ ‖W₂ t - W₁ t‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, show ‖phase ν t‖ = 1 from Complex.norm_exp_ofReal_mul_I _, mul_one]
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos hs0]
  have := mul_le_mul_of_nonneg_left (hre.trans hD) hs0.le
  rw [hℓ₂] at this
  linarith

/-- `errSecond` on the window `L√ε` (time scale `1/√ε`) is `O(ε)`:
`errSecond … (L√ε) ε … ≤ ε · errSecond … L 1 …` for `0 < ε ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem errSecond_short {ν : ℝ} (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) :
    errSecond b d k₁ α₂ α₃ ν R (L * √ε) ε Mu ≤ ε * errSecond b d k₁ α₂ α₃ ν R L 1 Mu := by
  have hℓ := lipSecond_nonneg hν b (ν ^ 2 - d) k₁ α₂ α₃ (2 * (R + 1))
  have hq := remSecond_nonneg hν (b := b) (d := d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hR hMu
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hs0 : 0 ≤ √ε := Real.sqrt_nonneg ε
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  simp only [errSecond, Real.sqrt_one, mul_one, one_mul]
  set ℓ := QuadraticCubic.lipSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν (2 * (R + 1))
  set q := QuadraticCubic.remSecond b d k₁ α₂ α₃ ν R Mu
  have hT : 0 ≤ 2 * Real.pi / ν := by positivity
  have hLs : L * √ε ≤ L := by nlinarith
  have hE : Real.exp (ℓ * (L * √ε)) ≤ Real.exp (ℓ * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLs hℓ)
  have hA : 2 * ℓ * (ℓ * (2 * (R + 1))) * (L * √ε) * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν) ≤
      2 * ℓ * (ℓ * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν) := by
    have : 0 ≤ 2 * ℓ * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν) := by positivity
    nlinarith
  have hA0 : 0 ≤ 2 * ℓ * (ℓ * (2 * (R + 1))) * (L * √ε) * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν) := by positivity
  have h1 : (2 * ℓ * (ℓ * (2 * (R + 1))) * (L * √ε) * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν)) * ε + L * √ε * (√ε * q) ≤
      ε * ((2 * ℓ * (ℓ * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν)) + L * q) := by
    have e : L * √ε * (√ε * q) = ε * (L * q) := by linear_combination (L * q) * hss
    rw [e]; nlinarith
  calc _ ≤ ε * ((2 * ℓ * (ℓ * (2 * (R + 1))) * L * (2 * Real.pi / ν) +
      2 * (ℓ * (2 * (R + 1))) * (2 * Real.pi / ν)) + L * q) * Real.exp (ℓ * L) := by
        refine mul_le_mul h1 hE (Real.exp_pos _).le ?_
        positivity
    _ = _ := by ring

/-- **First-order averaging is accurate on the time scale `1/√ε`.** In the setting of
`first_order_fails`, with the window `[0, L/√ε]` (averaged solutions in the disc `R` there and the
smallness of `errSecond` on the window `L√ε`), the first-order prediction is within `O(ε)`, a
relative error `O(√ε)`:
`|x(t) − √ε Re(W₁(t) e^{jνt})| ≤ ε (errSecond … L 1 … + c₁(2(R + 1))² + (c₁|w(0)|² + LγR³)e^{ℓ₂L})`.
Together with `first_order_fails` this is the precise form of "first-order averaging is valid only
on the time scale `1/√ε` when `α₂ ≠ 0`". -/
@[tmio T, powerlib_foundation] theorem first_order_short {ν : ℝ} (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) {x x' u : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x'
      (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) - α₂ * x t ^ 2 + u t) t)
    (hu : ∀ t ∈ Icc 0 (L / √ε), ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)‖ ≤ 2 * (R + 1) →
      |u t| ≤ ε ^ 2 * Mu)
    {W₁ W₂ : ℝ → ℂ}
    (hW₂ : ∀ t ∈ Icc 0 (L / √ε), HasDerivWithinAt W₂
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (W₂ t)) (Icc 0 (L / √ε)) t)
    (hb₂ : ∀ t ∈ Icc 0 (L / √ε), ‖W₂ t‖ ≤ R)
    (h0₂ : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0)) 0 = W₂ 0)
    (hW₁ : ∀ t ∈ Icc 0 (L / √ε), HasDerivWithinAt W₁
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν)) (W₁ t)) (Icc 0 (L / √ε)) t)
    (hb₁ : ∀ t ∈ Icc 0 (L / √ε), ‖W₁ t‖ ≤ R)
    (h0₁ : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0) = W₁ 0)
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d k₁ α₂ α₃ ν R (L * √ε) ε Mu < 1) :
    ∀ t ∈ Icc 0 (L / √ε), |x t - √ε * (W₁ t * phase ν t).re| ≤
      ε * (errSecond b d k₁ α₂ α₃ ν R L 1 Mu + 5 * |α₂| / (6 * ν ^ 2) * (2 * (R + 1)) ^ 2 +
        (5 * |α₂| / (6 * ν ^ 2) * ‖W₁ 0‖ ^ 2 + L * (5 * α₂ ^ 2 / (12 * ν ^ 3) * R ^ 3)) *
          Real.exp (ampLip (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
            (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R * L)) := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hwin : L * √ε / ε = L / √ε := by
    rw [div_eq_div_iff hε.ne' hs0.ne']; linear_combination L * hss
  rw [← hwin] at hu hW₂ hb₂ hW₁ hb₁ ⊢
  have h := first_order_upper hν hR (mul_nonneg hL hs0.le) hε hε1 hMu hx hx' hu hW₂ hb₂ h0₂ hW₁
    hb₁ h0₁ hbranch hsmall
  intro t ht
  refine (h t ht).trans ?_
  have hE := errSecond_short hν (b := b) (d := d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hR hL hε hε1
    hMu (Mu := Mu)
  set ℓ₂ := ampLip (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
    (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R with hℓ₂
  have hℓ₂0 : 0 ≤ ℓ₂ := by simp only [hℓ₂, ampLip]; positivity
  set c₁ := 5 * |α₂| / (6 * ν ^ 2)
  set G := 5 * α₂ ^ 2 / (12 * ν ^ 3) * R ^ 3
  have hc₁ : 0 ≤ c₁ := by positivity
  have hG : 0 ≤ G := by positivity
  have hexp : Real.exp (ℓ₂ * (L * √ε)) ≤ Real.exp (ℓ₂ * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by nlinarith) hℓ₂0)
  have hE1 : 0 ≤ errSecond b d k₁ α₂ α₃ ν R L 1 Mu := by
    have := errSecond_le_sqrt hν (b := b) (d := d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hR hL
      one_pos le_rfl hMu (Mu := Mu)
    simp only [errSecond]
    have hℓ := lipSecond_nonneg hν b (ν ^ 2 - d) k₁ α₂ α₃ (2 * (R + 1))
    have hq := remSecond_nonneg hν (b := b) (d := d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hR hMu
    positivity
  have t1 : √ε * errSecond b d k₁ α₂ α₃ ν R (L * √ε) ε Mu ≤
      ε * errSecond b d k₁ α₂ α₃ ν R L 1 Mu := by
    calc √ε * errSecond b d k₁ α₂ α₃ ν R (L * √ε) ε Mu ≤
        1 * (ε * errSecond b d k₁ α₂ α₃ ν R L 1 Mu) := by
          refine mul_le_mul hs1 hE ?_ zero_le_one
          have := errSecond_le_sqrt hν (b := b) (d := d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hR
            (mul_nonneg hL hs0.le) hε hε1 hMu (Mu := Mu)
          simp only [errSecond]
          have hℓ := lipSecond_nonneg hν b (ν ^ 2 - d) k₁ α₂ α₃ (2 * (R + 1))
          have hq := remSecond_nonneg hν (b := b) (d := d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hR
            hMu
          positivity
      _ = _ := one_mul _
  have t3 : √ε * ((√ε * c₁ * ‖W₁ 0‖ ^ 2 + L * √ε * G) * Real.exp (ℓ₂ * (L * √ε))) ≤
      ε * ((c₁ * ‖W₁ 0‖ ^ 2 + L * G) * Real.exp (ℓ₂ * L)) := by
    have e : √ε * ((√ε * c₁ * ‖W₁ 0‖ ^ 2 + L * √ε * G) * Real.exp (ℓ₂ * (L * √ε))) =
        ε * ((c₁ * ‖W₁ 0‖ ^ 2 + L * G) * Real.exp (ℓ₂ * (L * √ε))) := by
      linear_combination ((c₁ * ‖W₁ 0‖ ^ 2 + L * G) * Real.exp (ℓ₂ * (L * √ε))) * hss
    rw [e]
    gcongr
  have e2 : √ε * (√ε * c₁ * (2 * (R + 1)) ^ 2) = ε * (c₁ * (2 * (R + 1)) ^ 2) := by
    linear_combination (c₁ * (2 * (R + 1)) ^ 2) * hss
  calc √ε * (errSecond b d k₁ α₂ α₃ ν R (L * √ε) ε Mu + √ε * c₁ * (2 * (R + 1)) ^ 2 +
        (√ε * c₁ * ‖W₁ 0‖ ^ 2 + L * √ε * G) * Real.exp (ℓ₂ * (L * √ε)))
      = √ε * errSecond b d k₁ α₂ α₃ ν R (L * √ε) ε Mu + √ε * (√ε * c₁ * (2 * (R + 1)) ^ 2) +
          √ε * ((√ε * c₁ * ‖W₁ 0‖ ^ 2 + L * √ε * G) * Real.exp (ℓ₂ * (L * √ε))) := by ring
    _ ≤ ε * errSecond b d k₁ α₂ α₃ ν R L 1 Mu + ε * (c₁ * (2 * (R + 1)) ^ 2) +
          ε * ((c₁ * ‖W₁ 0‖ ^ 2 + L * G) * Real.exp (ℓ₂ * L)) := by
        rw [e2]; linarith
    _ = _ := by ring

end powerlib.ParametricResonance.FirstOrderFails
