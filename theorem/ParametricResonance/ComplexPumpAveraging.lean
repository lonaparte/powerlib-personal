import theorem.ParametricResonance.ForcedPumpInteraction

/-! # Second-order averaging for a complex pump from an arbitrary initial time

The rigorous second-order averaging theorem `QuadraticCubic.second_order_averaging` concerns the
real cosine pump `k₁ cos 2νt` on the window `[0, L/ε]`; `ForcedPump.forced_second_order` reduces a
complex pump `Re(κ e^{2jνt})` to it by a time shift that aligns the pump phase, and must therefore
start at an aligning time `t₀` (`κ e^{2jνt₀} = |κ|`). The true oscillator has only the discrete
time symmetry `t ↦ t + π/ν`, so a start at an arbitrary pump phase cannot be reached by a shift
and a rotation alone. The averaged equation, however, is autonomous, and a time shift of the
periodic field keeps its period average (`fieldAverage_comp_add_right`): KBM
(`Averaging.kbm_perturbed_local`) applies to the shifted cut-off second-order field, which gives
second-order averaging of the cosine pump on any window `[s₁, s₁ + L/ε]`
(`second_order_from`). With it, the time shift `t₀ = −arg κ/(2ν)` and the rotation
`W̄ ↦ e^{jνt₀}W̄` (`ForcedPump.accelC_shift`, `ForcedPump.ampField_rotate`,
`ForcedPump.nearId_rotate`, `ForcedPump.vdp_shift`) give the complex pump from any initial time
(`complex_second_order`), and the forced response at the pump frequency from any initial time, in
particular from `t = 0`, without an alignment hypothesis (`forced_second_order_from`).

Scope.
* The oscillator in coefficient form `ẍ + εbẋ + (ν² − εd + Re(εκ e^{2jνt}))x + α₂x² + α₃x³ = u(t)`
  (`ForcedPump.accelC`; real `κ = k₁` is `DuffingMathieu.accel`), real coefficients, complex `κ`,
  `ν > 0`, `0 < ε ≤ 1`, continuous time, a solution `(x, ẋ)` on all of `ℝ`, an arbitrary input
  `u(t)` bounded by `ε²M_u` while the scaled amplitude stays in the disc `2(R + 1)`; van der Pol
  amplitude `z = e^{−jνt}(x − jẋ/ν)`, `w = z/√ε`, transformed amplitude
  `W = w − √ε u(w, t)` (`QuadraticCubic.nearId`).
* The window `[t₁, t₁ + L/ε]` starts at an arbitrary time `t₁` (an arbitrary pump phase); the
  averaged solution `W̄` is given on the window in the disc `|W̄| ≤ R` from `W̄(t₁) = W(t₁)`, as in
  `QuadraticCubic.second_order_averaging` (existence of `W̄` is a hypothesis). The conclusions are
  the error bound of `QuadraticCubic.second_order_averaging` with `|κ|` in place of `|k₁|`, the
  tracking `|W − W̄| ≤ B` and the a-priori bound `|w| < 2(R + 1)` on the window.
* The forced corollary: the oscillator with the additive forcing `εf₀ cos 2νt` of
  `theorem/ParametricResonance/ForcedPumpInteraction.lean`, any phasor `X` with
  `(ν² − εd − 4ν² + 2jνεb)X = f₀`, the effective pump `κ = k₁ + 2α₂X`.
* Generic mathematics, no model family.

Source: second-order averaging of the pumped oscillator with quadratic and cubic stiffness
`QuadraticCubic.second_order_averaging`, `QuadraticCubic.hasDerivAt_transformed_scaled`,
`QuadraticCubic.cutSecond_hyp`, `QuadraticCubic.fieldAverage_secondField`
(`theorem/ParametricResonance/QuadraticCubicNormalForm.lean`); the complex pump, the time shift and
the rotations `ForcedPump.accelC_shift`, `ForcedPump.phase_align`, `ForcedPump.ampField_rotate`,
`ForcedPump.nearId_rotate`, `ForcedPump.vdp_shift`, the forced response
`ForcedPump.hasDerivAt_shift`, `ForcedPump.abs_shiftRem_le`
(`theorem/ParametricResonance/ForcedPumpInteraction.lean`); the perturbed KBM theorem on bounded
sets `Averaging.kbm_perturbed_local`; Mathlib's `Function.Periodic.intervalIntegral_add_eq`;
averaging with an arbitrary initial time (Sanders–Verhulst–Murdock, *Averaging Methods in
Nonlinear Dynamical Systems*, Ch. 2: the averaged equation is autonomous).

Sharpenings.
* `ForcedPump.forced_second_order` (and the constant-power swing built on it) needs a window that
  starts at an aligning time `t₀`, `κ e^{2jνt₀} = |κ|`; `forced_second_order_from` holds on every
  window, in particular from `t = 0`, with the same error bound.
* The a-priori bound `|w| < 2(R + 1)` on the window, internal to
  `QuadraticCubic.second_order_averaging`, is part of the conclusion of `second_order_from` and
  `complex_second_order`.

Results.
* `fieldAverage_comp_add_right` — the period average of a periodic field is invariant under a
  time shift.
* `second_order_from` — the cosine pump on `[s₁, s₁ + L/ε]` for any `s₁`: `|W − W̄| ≤ B`,
  `|w| < 2(R + 1)`, `|x − √ε Re(W̄ e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²))(2(R + 1))²)`.
* `complex_second_order` — the same for the complex pump `Re(εκ e^{2jνt})` on
  `[t₁, t₁ + L/ε]` for any `t₁`, with the averaged pump coefficient `jκ/(4ν)` and
  `B = errSecond b d |κ| …`.
* `forced_second_order_from` — the forced response as a second pump on `[t₁, t₁ + L/ε]` for any
  `t₁`: `|x − εRe(X e^{2jνt}) − √ε Re(W̄ e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²))(2(R + 1))²)`.
-/

noncomputable section
namespace powerlib.ParametricResonance.ComplexPump

open Complex Set
open DuffingMathieu (vdp accel vdpField)
open QuadraticCubic (phase nearId nearIdDeriv secondField cutSecond lipSecond remSecond errSecond)
open Saturation (ampField)
open ForcedPump (accelC pumpEff resp respVel forcedDen remForced)

/-! ## Time shifts of periodic fields -/

/-- **The period average does not see a time shift.** For a field `T`-periodic in time,
`⟨f(·, · + s₁)⟩ = ⟨f⟩`: `∫₀ᵀ f(x, s + s₁) ds = ∫_{s₁}^{s₁ + T} f(x, s) ds = ∫₀ᵀ f(x, s) ds`
(Mathlib's `Function.Periodic.intervalIntegral_add_eq`). -/
@[tmio T, powerlib_foundation] theorem fieldAverage_comp_add_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : E → ℝ → E} {T : ℝ}
    (hper : ∀ x t, f x (t + T) = f x t) (s₁ : ℝ) (x : E) :
    Averaging.fieldAverage (fun y s => f y (s + s₁)) T x = Averaging.fieldAverage f T x := by
  simp only [Averaging.fieldAverage]
  congr 1
  rw [intervalIntegral.integral_comp_add_right (fun s => f x s) s₁, zero_add, add_comm T s₁]
  have hp : Function.Periodic (f x) T := fun t => hper x t
  have h := hp.intervalIntegral_add_eq s₁ 0
  rw [zero_add] at h
  exact h

variable {b k₀ k₁ α₂ α₃ ν : ℝ}

/-- The time-shifted cut-off second-order field satisfies the hypotheses of KBM
(`QuadraticCubic.cutSecond_hyp` composed with `s ↦ s + s₁`). -/
@[tmio T, powerlib_foundation] private theorem cutSecond_shift_hyp (hν : 0 < ν) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (s₁ : ℝ) :
    0 < 2 * Real.pi / ν ∧ 0 ≤ lipSecond b k₀ k₁ α₂ α₃ ν (2 * ρ) ∧
      Continuous (Function.uncurry fun (w : ℂ) (s : ℝ) => cutSecond b k₀ k₁ α₂ α₃ ν ρ w (s + s₁)) ∧
      (∀ x t, cutSecond b k₀ k₁ α₂ α₃ ν ρ x (t + 2 * Real.pi / ν + s₁) =
        cutSecond b k₀ k₁ α₂ α₃ ν ρ x (t + s₁)) ∧
      (∀ x y t, ‖cutSecond b k₀ k₁ α₂ α₃ ν ρ x (t + s₁) - cutSecond b k₀ k₁ α₂ α₃ ν ρ y (t + s₁)‖ ≤
        lipSecond b k₀ k₁ α₂ α₃ ν (2 * ρ) * ‖x - y‖) ∧
      ∀ x t, ‖cutSecond b k₀ k₁ α₂ α₃ ν ρ x (t + s₁)‖ ≤
        lipSecond b k₀ k₁ α₂ α₃ ν (2 * ρ) * (2 * ρ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := QuadraticCubic.cutSecond_hyp (b := b) (k₀ := k₀) (k₁ := k₁)
    (α₂ := α₂) (α₃ := α₃) hν hρ
  refine ⟨h1, h2, ?_, fun x t => ?_, fun x y t => h5 x y _, fun x t => h6 x _⟩
  · have e : (Function.uncurry fun (w : ℂ) (s : ℝ) => cutSecond b k₀ k₁ α₂ α₃ ν ρ w (s + s₁)) =
        Function.uncurry (cutSecond b k₀ k₁ α₂ α₃ ν ρ) ∘ fun p : ℂ × ℝ => (p.1, p.2 + s₁) := by
      funext p; simp only [Function.uncurry, Function.comp_apply]
    rw [e]
    exact h3.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
  · rw [show t + 2 * Real.pi / ν + s₁ = (t + s₁) + 2 * Real.pi / ν by ring]
    exact h4 x _

@[tmio T, powerlib_foundation] private theorem lt_of_forbidden_from {φ : ℝ → ℝ} {s₁ t a c : ℝ}
    (hφ : ContinuousOn φ (Icc s₁ t)) (ha : 0 < a) (hac : 4 * a * c < 1) (h0 : φ s₁ < 2 * a)
    (hle : ∀ s ∈ Icc s₁ t, φ s ≤ a + c * φ s ^ 2) : ∀ s ∈ Icc s₁ t, φ s < 2 * a := by
  intro s hs
  by_contra hcon
  push Not at hcon
  have hsub : Icc s₁ s ⊆ Icc s₁ t := Icc_subset_Icc le_rfl hs.2
  obtain ⟨s', hs', hφs'⟩ := intermediate_value_Icc hs.1 (hφ.mono hsub) ⟨h0.le, hcon⟩
  have h := hle s' (hsub hs')
  rw [hφs'] at h
  nlinarith

@[tmio T, powerlib_foundation] private theorem norm_phase (ν t : ℝ) : ‖phase ν t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-! ## The cosine pump from an arbitrary initial time -/

/-- **Rigorous second-order averaging from an arbitrary initial time.** The setting of
`QuadraticCubic.second_order_averaging` (`ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = u`,
`ν > 0`, `0 < ε ≤ 1`, scaled amplitude `w = z/√ε`, transformed amplitude
`W = w − √ε u(w, t)`), with the window `[s₁, s₁ + L/ε]` starting at an arbitrary time `s₁`
(any phase of the pump): let `W̄` solve the second-order averaged equation
`W̄̇ = ε ampField (b/2) (d/(2ν)) (jk₁/(4ν)) 0 β_eff W̄` on the window in the disc `|W̄| ≤ R`, from
`W̄(s₁) = W(s₁)`, and assume `|w(s₁)| < 2(R + 1)`, the input bound `|u| ≤ ε²M_u` while
`|w| ≤ 2(R + 1)`, the branch condition and `B = errSecond … < 1`. Then on the window
* `|W(t) − W̄(t)| ≤ B` (the transformed amplitude tracks the averaged one);
* `|w(t)| < 2(R + 1)` (the a-priori bound: the scaled amplitude never leaves the disc);
* `|x(t) − √ε Re(W̄(t) e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²)) (2(R + 1))²)`.
The averaged equation is autonomous and the time shift `s ↦ s + s₁` keeps the period average
(`fieldAverage_comp_add_right`), so KBM (`Averaging.kbm_perturbed_local`) applies to the shifted
cut-off field. -/
@[tmio T, powerlib_foundation] theorem second_order_from (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu s₁ : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) {x x' u : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x'
      (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) - α₂ * x t ^ 2 + u t) t)
    (hu : ∀ t ∈ Icc s₁ (s₁ + L / ε), ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)‖ ≤ 2 * (R + 1) →
      |u t| ≤ ε ^ 2 * Mu)
    {Wbar : ℝ → ℂ}
    (hWbar : ∀ t ∈ Icc s₁ (s₁ + L / ε), HasDerivWithinAt Wbar
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (Wbar t)) (Icc s₁ (s₁ + L / ε)) t)
    (hbound : ∀ t ∈ Icc s₁ (s₁ + L / ε), ‖Wbar t‖ ≤ R)
    (h0 : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν s₁ (x s₁) (x' s₁) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν s₁ (x s₁) (x' s₁)) s₁ = Wbar s₁)
    (hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν s₁ (x s₁) (x' s₁)‖ < 2 * (R + 1))
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d k₁ α₂ α₃ ν R L ε Mu < 1) :
    ∀ t ∈ Icc s₁ (s₁ + L / ε),
      ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t) -
          (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)) t - Wbar t‖ ≤
        errSecond b d k₁ α₂ α₃ ν R L ε Mu ∧
      ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)‖ < 2 * (R + 1) ∧
      |x t - √ε * (Wbar t * phase ν t).re| ≤
        √ε * (errSecond b d k₁ α₂ α₃ ν R L ε Mu +
          √ε * (5 * |α₂| / (6 * ν ^ 2)) * (2 * (R + 1)) ^ 2) := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsε : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hR1 : 0 < R + 1 := by linarith
  set c₁ := 5 * |α₂| / (6 * ν ^ 2) with hc₁
  set c₂ := 5 * |α₂| / (3 * ν ^ 2) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set w : ℝ → ℂ := fun t => ((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t) with hwdef
  set W : ℝ → ℂ := fun t => w t - (√ε : ℂ) * nearId α₂ ν (w t) t with hWdef
  set U : ℝ → ℂ := fun t => -(I / ν * (u t : ℂ) * (phase ν t)⁻¹) with hUdef
  set q : ℝ → ℂ := fun t => ε • secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (w t) t -
      (ε * √ε : ℝ) • nearIdDeriv α₂ ν (w t) t (vdpField b (ν ^ 2 - d) k₁ α₃ ν (w t) t) +
      (((√ε : ℝ) : ℂ)⁻¹ * U t - nearIdDeriv α₂ ν (w t) t (U t)) -
      ε • secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (W t) t with hqdef
  have hW : ∀ t, HasDerivAt W (ε • secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (W t) t + q t) t := by
    intro t
    have h := QuadraticCubic.hasDerivAt_transformed_scaled (b := b) (k₁ := k₁) (α₂ := α₂)
      (α₃ := α₃) hν.ne' hε hx hx' t
    convert h using 1
    simp only [hqdef, hUdef]
    abel
  -- the transformation is small: `‖w − W‖ ≤ √ε c₁ ‖w‖²`
  have hwW : ∀ t, ‖w t - W t‖ ≤ √ε * c₁ * ‖w t‖ ^ 2 := by
    intro t
    rw [hWdef]
    simp only [sub_sub_cancel, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (QuadraticCubic.norm_nearId_le hν _ t) hs0.le
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hx'c : Continuous x' := continuous_iff_continuousAt.2 fun t => (hx' t).continuousAt
  have hwc : Continuous w := by
    simp only [hwdef, vdp]
    fun_prop
  -- while `W` stays in the disc of radius `R + 1`, `w` stays in that of radius `2(R + 1)`
  have hbr : ∀ t, s₁ ≤ t → (∀ s ∈ Icc s₁ t, ‖W s‖ ≤ R + 1) →
      ∀ s ∈ Icc s₁ t, ‖w s‖ < 2 * (R + 1) := by
    intro t _ hhist
    refine lt_of_forbidden_from (φ := fun s => ‖w s‖) (c := √ε * c₁) hwc.norm.continuousOn hR1
      hbranch hw0 fun s hs => ?_
    have h1 := norm_le_norm_add_norm_sub' (w s) (W s)
    have h2 := hwW s
    have h3 := hhist s hs
    show ‖w s‖ ≤ R + 1 + √ε * c₁ * ‖w s‖ ^ 2
    linarith
  -- the neglected terms are of order `ε^{3/2}`
  have hqb : ∀ t, ‖w t‖ ≤ 2 * (R + 1) → ‖W t‖ ≤ 2 * (R + 1) → |u t| ≤ ε ^ 2 * Mu →
      ‖q t‖ ≤ ε * (√ε * remSecond b d k₁ α₂ α₃ ν R Mu) := by
    intro t hw hW' hut
    set r := 2 * (R + 1)
    set ℓ₂ := lipSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν r
    set ℓ₁ := DuffingMathieu.lipConst b (ν ^ 2 - d) k₁ α₃ ν r
    have hr0 : 0 ≤ r := by positivity
    have hℓ₁ : 0 ≤ ℓ₁ := by
      simp only [ℓ₁, DuffingMathieu.lipConst]; have := hν.le; positivity
    have hℓ₂ : 0 ≤ ℓ₂ := by
      simp only [ℓ₂, lipSecond, DuffingMathieu.lipConst]; have := hν.le; positivity
    have e : q t = ε • (secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (w t) t -
        secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (W t) t) -
        (ε * √ε : ℝ) • nearIdDeriv α₂ ν (w t) t (vdpField b (ν ^ 2 - d) k₁ α₃ ν (w t) t) +
        (((√ε : ℝ) : ℂ)⁻¹ * U t - nearIdDeriv α₂ ν (w t) t (U t)) := by
      simp only [hqdef, smul_sub]; abel
    have hU : ‖U t‖ ≤ ε ^ 2 * Mu / ν := by
      simp only [hUdef, norm_neg, norm_mul, norm_div, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, norm_inv, Complex.norm_exp_ofReal_mul_I, phase, abs_of_pos hν]
      rw [inv_one, mul_one, one_div]
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hut hν.le
    have hF : ‖vdpField b (ν ^ 2 - d) k₁ α₃ ν (w t) t‖ ≤ ℓ₁ * r := by
      have h := DuffingMathieu.norm_vdpField_sub_le (b := b) (k₀ := ν ^ 2 - d) (k₁ := k₁)
        (γ := α₃) hν hw (by rw [norm_zero]; exact hr0) t
      rw [DuffingMathieu.vdpField_zero, sub_zero, sub_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_left hw hℓ₁)
    have t1 : ‖ε • (secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (w t) t -
        secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (W t) t)‖ ≤ ε * √ε * (ℓ₂ * c₁ * r ^ 2) := by
      rw [norm_smul, Real.norm_of_nonneg hε.le]
      have h := QuadraticCubic.norm_secondField_sub_le (b := b) (k₀ := ν ^ 2 - d) (k₁ := k₁)
        (α₂ := α₂) (α₃ := α₃) hν hw hW' t
      have h2 : ‖w t - W t‖ ≤ √ε * c₁ * r ^ 2 :=
        (hwW t).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw 2)
          (by positivity))
      calc ε * ‖secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (w t) t -
            secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (W t) t‖ ≤ ε * (ℓ₂ * (√ε * c₁ * r ^ 2)) := by
            gcongr; exact h.trans (mul_le_mul_of_nonneg_left h2 hℓ₂)
        _ = ε * √ε * (ℓ₂ * c₁ * r ^ 2) := by ring
    have t2 : ‖(ε * √ε : ℝ) • nearIdDeriv α₂ ν (w t) t
        (vdpField b (ν ^ 2 - d) k₁ α₃ ν (w t) t)‖ ≤ ε * √ε * (c₂ * ℓ₁ * r ^ 2) := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have h := QuadraticCubic.norm_nearIdDeriv_le (α₂ := α₂) hν (w t)
        (vdpField b (ν ^ 2 - d) k₁ α₃ ν (w t) t) t
      calc ε * √ε * ‖nearIdDeriv α₂ ν (w t) t (vdpField b (ν ^ 2 - d) k₁ α₃ ν (w t) t)‖
          ≤ ε * √ε * (c₂ * (r * (ℓ₁ * r))) := by
            gcongr; exact h.trans (mul_le_mul_of_nonneg_left (mul_le_mul hw hF (norm_nonneg _)
              hr0) hc₂0)
        _ = ε * √ε * (c₂ * ℓ₁ * r ^ 2) := by ring
    have t3 : ‖((√ε : ℝ) : ℂ)⁻¹ * U t‖ ≤ ε * √ε * (Mu / ν) := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      calc (√ε)⁻¹ * ‖U t‖ ≤ (√ε)⁻¹ * (ε ^ 2 * Mu / ν) := by gcongr
        _ = ε * √ε * (Mu / ν) := by
            have h2 : ε ^ 2 = ε * √ε * √ε := by rw [mul_assoc, hsε, sq]
            rw [h2]; field_simp
    have t4 : ‖nearIdDeriv α₂ ν (w t) t (U t)‖ ≤ ε * √ε * (c₂ * r * (Mu / ν)) := by
      have h := QuadraticCubic.norm_nearIdDeriv_le (α₂ := α₂) hν (w t) (U t) t
      have hε2 : ε ^ 2 ≤ ε * √ε := by
        rw [sq]; exact mul_le_mul_of_nonneg_left (by nlinarith [Real.sqrt_nonneg ε]) hε.le
      have hMν : 0 ≤ Mu / ν := div_nonneg hMu hν.le
      calc ‖nearIdDeriv α₂ ν (w t) t (U t)‖ ≤ c₂ * (r * (ε ^ 2 * Mu / ν)) :=
            h.trans (mul_le_mul_of_nonneg_left (mul_le_mul hw hU (norm_nonneg _) hr0) hc₂0)
        _ = c₂ * r * (Mu / ν) * ε ^ 2 := by ring
        _ ≤ c₂ * r * (Mu / ν) * (ε * √ε) := by
            apply mul_le_mul_of_nonneg_left hε2; positivity
        _ = ε * √ε * (c₂ * r * (Mu / ν)) := by ring
    rw [e]
    calc _ ≤ ‖ε • (secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (w t) t -
          secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (W t) t) -
          (ε * √ε : ℝ) • nearIdDeriv α₂ ν (w t) t (vdpField b (ν ^ 2 - d) k₁ α₃ ν (w t) t)‖ +
          ‖((√ε : ℝ) : ℂ)⁻¹ * U t - nearIdDeriv α₂ ν (w t) t (U t)‖ := norm_add_le _ _
      _ ≤ (‖ε • (secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (w t) t -
          secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (W t) t)‖ +
          ‖(ε * √ε : ℝ) • nearIdDeriv α₂ ν (w t) t (vdpField b (ν ^ 2 - d) k₁ α₃ ν (w t) t)‖) +
          (‖((√ε : ℝ) : ℂ)⁻¹ * U t‖ + ‖nearIdDeriv α₂ ν (w t) t (U t)‖) :=
          add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
      _ ≤ _ := by
          simp only [remSecond]
          nlinarith [t1, t2, t3, t4]
  -- KBM with the perturbation for the transformed amplitude on the shifted window
  have hg := cutSecond_shift_hyp (b := b) (k₀ := ν ^ 2 - d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hν
    hR1.le s₁
  have hfg : ∀ y ∈ {y : ℂ | ‖y‖ ≤ R + 1}, ∀ s,
      secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν y (s + s₁) =
        cutSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν (R + 1) y (s + s₁) := by
    intro y hy s
    simp only [cutSecond, DuffingMathieu.clampC_of_norm_le hy]
  have hrem : 0 ≤ remSecond b d k₁ α₂ α₃ ν R Mu := by
    simp only [remSecond, lipSecond, DuffingMathieu.lipConst]; have := hν.le; positivity
  have hmaps : MapsTo (fun s => s + s₁) (Icc 0 (L / ε)) (Icc s₁ (s₁ + L / ε)) :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hk := Averaging.kbm_perturbed_local
    (f := fun y s => secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν y (s + s₁))
    (g := fun y s => cutSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν (R + 1) y (s + s₁)) hg hfg hε hL
    (mul_nonneg hs0.le hrem) (ρ := 1)
    (x := fun s => W (s + s₁)) (xbar := fun s => Wbar (s + s₁)) (q := fun s => q (s + s₁))
    (fun s _ => ((hW (s + s₁)).comp_add_const s s₁).hasDerivWithinAt)
    (fun s hs hhist => by
      have ht := hmaps hs
      have hhist' : ∀ σ ∈ Icc s₁ (s + s₁), ‖W σ‖ ≤ R + 1 := fun σ hσ => by
        have h := hhist (σ - s₁) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
        simp only [Set.mem_ofPred_eq, sub_add_cancel] at h
        exact h
      have hw := hbr (s + s₁) ht.1 hhist' (s + s₁) ⟨ht.1, le_rfl⟩
      exact hqb (s + s₁) hw.le ((hhist' _ ⟨ht.1, le_rfl⟩).trans (by linarith))
        (hu _ ht hw.le))
    (fun s hs => by
      rw [fieldAverage_comp_add_right (fun y t => QuadraticCubic.secondField_periodic hν y t),
        QuadraticCubic.fieldAverage_secondField hν,
        show (ν ^ 2 - (ν ^ 2 - d)) / (2 * ν) = d / (2 * ν) by ring]
      have hsh : HasDerivWithinAt (fun s => s + s₁) 1 (Icc 0 (L / ε)) s :=
        ((hasDerivAt_id s).add_const s₁).hasDerivWithinAt
      have h := (hWbar (s + s₁) (hmaps hs)).scomp s hsh hmaps
      rw [one_smul] at h
      exact h)
    (fun s hs y hy => by
      show ‖y‖ ≤ R + 1
      have := norm_le_norm_add_norm_sub' y (Wbar (s + s₁))
      linarith [hbound (s + s₁) (hmaps hs)])
    (by simp only [zero_add, hWdef, hwdef]; exact h0) (by simpa [errSecond] using hsmall)
  -- back to the window
  have hB : ∀ s ∈ Icc s₁ (s₁ + L / ε), ‖W s - Wbar s‖ ≤ errSecond b d k₁ α₂ α₃ ν R L ε Mu := by
    intro s hs
    have h := hk (s - s₁) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simp only [sub_add_cancel] at h
    simpa [errSecond] using h
  intro t ht
  have hhist : ∀ s ∈ Icc s₁ t, ‖W s‖ ≤ R + 1 := by
    intro s hs
    have hs' : s ∈ Icc s₁ (s₁ + L / ε) := ⟨hs.1, hs.2.trans ht.2⟩
    have := norm_le_norm_add_norm_sub' (W s) (Wbar s)
    have := hB s hs'
    have := hbound s hs'
    linarith
  have hwt := hbr t ht.1 hhist t ⟨ht.1, le_rfl⟩
  refine ⟨hB t ht, hwt, ?_⟩
  have hwWb : ‖w t - Wbar t‖ ≤ errSecond b d k₁ α₂ α₃ ν R L ε Mu + √ε * c₁ * (2 * (R + 1)) ^ 2 := by
    calc ‖w t - Wbar t‖ ≤ ‖W t - Wbar t‖ + ‖w t - W t‖ := by
          rw [show w t - Wbar t = (W t - Wbar t) + (w t - W t) by ring]; exact norm_add_le _ _
      _ ≤ _ := add_le_add (hB t ht) ((hwW t).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hwt.le 2) (by positivity)))
  have hx_eq : x t = (vdp ν t (x t) (x' t) * phase ν t).re :=
    (DuffingMathieu.pos_vdp ν t (x t) (x' t)).symm
  have hz : vdp ν t (x t) (x' t) = ((√ε : ℝ) : ℂ) * w t := by simp only [hwdef]; field_simp
  rw [hx_eq, hz, show √ε * (Wbar t * phase ν t).re = ((((√ε : ℝ) : ℂ) * Wbar t) * phase ν t).re by
    rw [mul_assoc, Complex.re_ofReal_mul], ← Complex.sub_re, ← sub_mul, ← mul_sub]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  exact mul_le_mul_of_nonneg_left hwWb hs0.le

/-! ## A complex pump from an arbitrary initial time -/

/-- **Rigorous second-order averaging for a complex pump from an arbitrary initial time.** For
`ẍ + εbẋ + (ν² − εd + Re(εκ e^{2jνt}))x + α₂x² + α₃x³ = u(t)` (`ForcedPump.accelC`, a pump of any
complex amplitude `εκ`, `ν > 0`, `0 < ε ≤ 1`), scaled amplitude `w = z/√ε` and transformed
amplitude `W = w − √ε u(w, t)`, let `W̄` solve the second-order averaged equation with the complex
pump coefficient `jκ/(4ν)`,
`W̄̇ = ε ampField (b/2) (d/(2ν)) (jκ/(4ν)) 0 β_eff W̄`, `β_eff = 3α₃/(8ν) − 5α₂²/(12ν³)`, on the
window `[t₁, t₁ + L/ε]` (any initial time `t₁`, e.g. `t₁ = 0`) in the disc `|W̄| ≤ R`, from
`W̄(t₁) = W(t₁)`, with `|w(t₁)| < 2(R + 1)`, the input bound `|u| ≤ ε²M_u` while
`|w| ≤ 2(R + 1)`, the branch condition and `B = errSecond b d |κ| … < 1`. Then on the window
`|W − W̄| ≤ B`, `|w| < 2(R + 1)` and
`|x(t) − √ε Re(W̄(t) e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²)) (2(R + 1))²)`.
Proof: the time shift by `t₀ = −arg κ/(2ν)` turns the pump into the cosine pump `|κ| cos 2νs`
(`ForcedPump.accelC_shift`, `ForcedPump.phase_align`), the rotation `W̄ ↦ e^{jνt₀}W̄` turns the
pump coefficient into `j|κ|/(4ν)` (`ForcedPump.ampField_rotate`, `ForcedPump.nearId_rotate`,
`ForcedPump.vdp_shift`), and `second_order_from` applies from `s₁ = t₁ − t₀`. -/
@[tmio T, powerlib_foundation] theorem complex_second_order (hν : 0 < ν)
    {b d R L ε Mu t₁ : ℝ} {κ : ℂ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) {x x' u : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x'
      (accelC (ε * b) (ν ^ 2 - ε * d) ((ε : ℂ) * κ) α₃ ν t (x t) (x' t) - α₂ * x t ^ 2 + u t) t)
    (hu : ∀ t ∈ Icc t₁ (t₁ + L / ε), ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)‖ ≤ 2 * (R + 1) →
      |u t| ≤ ε ^ 2 * Mu)
    {Wbar : ℝ → ℂ}
    (hWbar : ∀ t ∈ Icc t₁ (t₁ + L / ε), HasDerivWithinAt Wbar
      (ε • ampField (b / 2) (d / (2 * ν)) (I * (κ / (4 * ν))) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (Wbar t)) (Icc t₁ (t₁ + L / ε)) t)
    (hbound : ∀ t ∈ Icc t₁ (t₁ + L / ε), ‖Wbar t‖ ≤ R)
    (h0 : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν t₁ (x t₁) (x' t₁) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t₁ (x t₁) (x' t₁)) t₁ = Wbar t₁)
    (hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t₁ (x t₁) (x' t₁)‖ < 2 * (R + 1))
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d ‖κ‖ α₂ α₃ ν R L ε Mu < 1) :
    ∀ t ∈ Icc t₁ (t₁ + L / ε),
      ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t) -
          (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)) t - Wbar t‖ ≤
        errSecond b d ‖κ‖ α₂ α₃ ν R L ε Mu ∧
      ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)‖ < 2 * (R + 1) ∧
      |x t - √ε * (Wbar t * phase ν t).re| ≤
        √ε * (errSecond b d ‖κ‖ α₂ α₃ ν R L ε Mu +
          √ε * (5 * |α₂| / (6 * ν ^ 2)) * (2 * (R + 1)) ^ 2) := by
  set t₀ := -Complex.arg κ / (2 * ν) with ht₀def
  have ht₀ : κ * phase ν t₀ ^ 2 = (‖κ‖ : ℂ) := ForcedPump.phase_align hν.ne' κ
  have h0' := QuadraticCubic.phase_ne_zero ν t₀
  have hnκ : ‖(ε : ℂ) * κ‖ = ε * ‖κ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
  have ht₀ε : ((ε : ℂ) * κ) * phase ν t₀ ^ 2 = (‖(ε : ℂ) * κ‖ : ℂ) := by
    rw [mul_assoc, ht₀, hnκ]; push_cast; ring
  set xs : ℝ → ℝ := fun s => x (s + t₀) with hxs_def
  set xs' : ℝ → ℝ := fun s => x' (s + t₀) with hxs'_def
  set us : ℝ → ℝ := fun s => u (s + t₀) with hus_def
  set Ws : ℝ → ℂ := fun s => phase ν t₀ * Wbar (s + t₀) with hWs_def
  set s₁ := t₁ - t₀ with hs₁
  have hs₁t : s₁ + t₀ = t₁ := by rw [hs₁]; ring
  have hxs : ∀ s, HasDerivAt xs (xs' s) s := fun s => (hx (s + t₀)).comp_add_const s t₀
  have hxs' : ∀ s, HasDerivAt xs' (accel (ε * b) (ν ^ 2 - ε * d) (ε * ‖κ‖) α₃ ν s (xs s) (xs' s) -
      α₂ * xs s ^ 2 + us s) s := by
    intro s
    have h := (hx' (s + t₀)).comp_add_const s t₀
    rw [ForcedPump.accelC_shift ht₀ε, hnκ] at h
    exact h
  -- the scaled and the transformed amplitudes of the shifted state are rotated
  have hw : ∀ s, ((√ε : ℝ) : ℂ)⁻¹ * vdp ν s (xs s) (xs' s) =
      phase ν t₀ * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν (s + t₀) (x (s + t₀)) (x' (s + t₀))) := by
    intro s
    rw [ForcedPump.vdp_shift ν s t₀]
    ring
  have hWrot : ∀ s, ((√ε : ℝ) : ℂ)⁻¹ * vdp ν s (xs s) (xs' s) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν s (xs s) (xs' s)) s =
      phase ν t₀ * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν (s + t₀) (x (s + t₀)) (x' (s + t₀)) -
        (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν (s + t₀) (x (s + t₀)) (x' (s + t₀)))
          (s + t₀)) := by
    intro s
    rw [hw s, ForcedPump.nearId_rotate]
    ring
  have hnorm : ∀ s, ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν s (xs s) (xs' s)‖ =
      ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν (s + t₀) (x (s + t₀)) (x' (s + t₀))‖ := by
    intro s
    rw [hw s, norm_mul, norm_phase, one_mul]
  have hmaps : MapsTo (fun s => s + t₀) (Icc s₁ (s₁ + L / ε)) (Icc t₁ (t₁ + L / ε)) :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmain := second_order_from (b := b) (d := d) (k₁ := ‖κ‖) (α₂ := α₂) (α₃ := α₃)
    (Mu := Mu) (s₁ := s₁) (Wbar := Ws) hν hR hL hε hε1 hMu hxs hxs'
    (fun s hs hw' => by
      rw [hnorm] at hw'
      exact hu (s + t₀) (hmaps hs) hw')
    (fun s hs => by
      have hsh : HasDerivWithinAt (fun s => s + t₀) 1 (Icc s₁ (s₁ + L / ε)) s :=
        ((hasDerivAt_id s).add_const t₀).hasDerivWithinAt
      have h := ((hWbar (s + t₀) (hmaps hs)).scomp s hsh hmaps).const_mul (phase ν t₀)
      have hrot : phase ν t₀ * ampField (b / 2) (d / (2 * ν)) (I * (κ / (4 * ν))) 0
          (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (Wbar (s + t₀)) =
          ampField (b / 2) (d / (2 * ν)) (I * ((‖κ‖ / (4 * ν) : ℝ) : ℂ)) 0
            (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (Ws s) := by
        have e1 : Wbar (s + t₀) = (phase ν t₀)⁻¹ * Ws s := by
          simp only [hWs_def]; field_simp
        rw [e1, ForcedPump.ampField_rotate]
        congr 1
        rw [show I * (κ / (4 * ν)) * phase ν t₀ ^ 2 = I * (κ * phase ν t₀ ^ 2) / (4 * ν) by ring,
          ht₀]
        push_cast; ring
      convert h using 1
      · rfl
      rw [one_smul, Complex.real_smul, Complex.real_smul, ← hrot]
      ring)
    (fun s hs => by
      simp only [hWs_def, norm_mul, norm_phase, one_mul]
      exact hbound (s + t₀) (hmaps hs))
    (by rw [hWrot, hs₁t, h0]; simp only [hWs_def, hs₁t])
    (by rw [hnorm, hs₁t]; exact hw0) hbranch hsmall
  intro t ht
  have hs : t - t₀ ∈ Icc s₁ (s₁ + L / ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨h1, h2, h3⟩ := hmain (t - t₀) hs
  rw [hWrot, sub_add_cancel] at h1
  rw [hnorm, sub_add_cancel] at h2
  simp only [hxs_def, hWs_def, sub_add_cancel] at h1 h3
  refine ⟨?_, h2, ?_⟩
  · rw [← mul_sub, norm_mul, norm_phase, one_mul] at h1
    exact h1
  · rw [show phase ν t₀ * Wbar t * phase ν (t - t₀) = Wbar t * phase ν t by
      rw [mul_comm (phase ν t₀), mul_assoc, ← ForcedPump.phase_add, add_sub_cancel]] at h3
    exact h3

/-! ## The forced response from an arbitrary initial time -/

/-- **Second-order averaging with the forced response, from an arbitrary initial time.** For
`ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = εf₀ cos 2νt + u(t)` (`ν > 0`,
`0 < ε ≤ 1`), `X` a solution of the phasor equation `(ν² − εd − 4ν² + 2jνεb)X = f₀`
(`ForcedPump.forcedDen`), `κ = k₁ + 2α₂X` (`ForcedPump.pumpEff`) and the shifted state
`y = x − εRe(X e^{2jνt})` with its scaled and transformed amplitudes `w`, `W`: let `W̄` solve the
second-order averaged equation with the pump coefficient `jκ/(4ν)` on `[t₁, t₁ + L/ε]` (any
initial time, no alignment of the pump phase; e.g. `t₁ = 0`) in the disc `|W̄| ≤ R`, from
`W̄(t₁) = W(t₁)`, with `|w(t₁)| < 2(R + 1)`, the input bound, the branch condition and
`B = errSecond b d |κ| α₂ α₃ ν R L ε (M_u + remForced …) < 1`. Then on the window
`|x(t) − εRe(X e^{2jνt}) − √ε Re(W̄(t) e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²)) (2(R + 1))²)`
(`ForcedPump.hasDerivAt_shift`, `ForcedPump.abs_shiftRem_le`, `complex_second_order`).
`ForcedPump.forced_second_order` is the case of a window that starts at an aligning time. -/
@[tmio T, powerlib_foundation] theorem forced_second_order_from (hν : 0 < ν)
    {b d f₀ R L ε Mu t₁ : ℝ} {X : ℂ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hMu : 0 ≤ Mu) (hX : forcedDen (ε * b) (ν ^ 2 - ε * d) ν * X = f₀)
    {x x' u : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x' (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) -
      α₂ * x t ^ 2 + ε * f₀ * Real.cos (2 * ν * t) + u t) t)
    (hu : ∀ t ∈ Icc t₁ (t₁ + L / ε), ‖((√ε : ℝ) : ℂ)⁻¹ *
        vdp ν t (x t - ε * resp ν X t) (x' t - ε * respVel ν X t)‖ ≤ 2 * (R + 1) →
      |u t| ≤ ε ^ 2 * Mu)
    {Wbar : ℝ → ℂ}
    (hWbar : ∀ t ∈ Icc t₁ (t₁ + L / ε), HasDerivWithinAt Wbar
      (ε • ampField (b / 2) (d / (2 * ν)) (I * (pumpEff k₁ α₂ X / (4 * ν))) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (Wbar t)) (Icc t₁ (t₁ + L / ε)) t)
    (hbound : ∀ t ∈ Icc t₁ (t₁ + L / ε), ‖Wbar t‖ ≤ R)
    (h0 : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν t₁ (x t₁ - ε * resp ν X t₁) (x' t₁ - ε * respVel ν X t₁) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ *
        vdp ν t₁ (x t₁ - ε * resp ν X t₁) (x' t₁ - ε * respVel ν X t₁)) t₁ = Wbar t₁)
    (hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t₁ (x t₁ - ε * resp ν X t₁) (x' t₁ - ε * respVel ν X t₁)‖ <
      2 * (R + 1))
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d ‖pumpEff k₁ α₂ X‖ α₂ α₃ ν R L ε
      (Mu + remForced k₁ α₂ α₃ R ‖X‖) < 1) :
    ∀ t ∈ Icc t₁ (t₁ + L / ε), |x t - ε * resp ν X t - √ε * (Wbar t * phase ν t).re| ≤
      √ε * (errSecond b d ‖pumpEff k₁ α₂ X‖ α₂ α₃ ν R L ε (Mu + remForced k₁ α₂ α₃ R ‖X‖) +
        √ε * (5 * |α₂| / (6 * ν ^ 2)) * (2 * (R + 1)) ^ 2) := by
  set κ := pumpEff k₁ α₂ X with hκ
  set y : ℝ → ℝ := fun t => x t - ε * resp ν X t with hy
  set y' : ℝ → ℝ := fun t => x' t - ε * respVel ν X t with hy'
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hrespε : ∀ t, resp ν ((ε : ℂ) * X) t = ε * resp ν X t := fun t => by
    simp only [resp, mul_assoc, Complex.re_ofReal_mul]
  have hvelε : ∀ t, respVel ν ((ε : ℂ) * X) t = ε * respVel ν X t := fun t => by
    simp only [respVel]; rw [← Complex.re_ofReal_mul]; congr 1; ring
  have hκε : pumpEff (ε * k₁) α₂ ((ε : ℂ) * X) = (ε : ℂ) * κ := by
    simp only [hκ, pumpEff]; push_cast; ring
  have hXε : forcedDen (ε * b) (ν ^ 2 - ε * d) ν * ((ε : ℂ) * X) = ((ε * f₀ : ℝ) : ℂ) := by
    rw [mul_left_comm, hX]; push_cast; ring
  have hyd : ∀ t, HasDerivAt y (y' t) t := fun t =>
    (hx t).sub ((ForcedPump.hasDerivAt_resp ν X t).const_mul ε)
  have hyd' : ∀ t, HasDerivAt y' (accelC (ε * b) (ν ^ 2 - ε * d) ((ε : ℂ) * κ) α₃ ν t (y t) (y' t) -
      α₂ * y t ^ 2 + (ForcedPump.shiftRem (ε * k₁) α₂ α₃ ν ((ε : ℂ) * X) t (y t) + u t)) t := by
    intro t
    have h := ForcedPump.hasDerivAt_shift (k₁ := ε * k₁) (α₂ := α₂) (α₃ := α₃) hXε (x := x)
      (x' := x') (u := u) hx' t
    simp only [hrespε, hvelε, hκε] at h
    exact h
  have hrem0 : 0 ≤ remForced k₁ α₂ α₃ R ‖X‖ := by unfold remForced; positivity
  have hmain := complex_second_order (b := b) (d := d) (κ := κ) (α₂ := α₂) (α₃ := α₃)
    (Mu := Mu + remForced k₁ α₂ α₃ R ‖X‖) (t₁ := t₁) (Wbar := Wbar) hν hR hL hε hε1
    (by linarith) hyd hyd'
    (fun t ht hw => by
      have hu' := hu t ht hw
      have hyb : |y t| ≤ √ε * (2 * (R + 1)) :=
        (ForcedPump.abs_le_scaled hε ν t _ (y' t)).trans (mul_le_mul_of_nonneg_left hw hs0.le)
      have hr := ForcedPump.abs_shiftRem_le (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) (ν := ν) hε hε1 hR
        X t hyb
      calc |ForcedPump.shiftRem (ε * k₁) α₂ α₃ ν ((ε : ℂ) * X) t (y t) + u t| ≤
            |ForcedPump.shiftRem (ε * k₁) α₂ α₃ ν ((ε : ℂ) * X) t (y t)| + |u t| :=
            abs_add_le _ _
        _ ≤ ε ^ 2 * remForced k₁ α₂ α₃ R ‖X‖ + ε ^ 2 * Mu := add_le_add hr hu'
        _ = ε ^ 2 * (Mu + remForced k₁ α₂ α₃ R ‖X‖) := by ring)
    hWbar hbound h0 hw0 hbranch hsmall
  intro t ht
  exact (hmain t ht).2.2

end powerlib.ParametricResonance.ComplexPump
