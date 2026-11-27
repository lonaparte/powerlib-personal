import theorem.ParametricResonance.QuadraticCubicNormalForm

/-! # Forced response and parametric pump: an additive forcing at the pump frequency

When the modulation that pumps an oscillator also forces it additively at the pump frequency,
`ẍ + bẋ + (k₀ + k₁ cos 2νt)x + α₂x² + α₃x³ = F cos 2νt + u(t)`, the forced response at `2ν` is not
resonant (the half-frequency oscillation is at `ν`), but through the quadratic stiffness it is a
second pump: with the exact forced response `x_f = Re(X e^{2jνt})`,
`(k₀ − 4ν² + 2jνb)X = F`, the shifted state `y = x − x_f` obeys the pumped oscillator with the
complex pump `Re(κ e^{2jνt})`, `κ = k₁ + 2α₂X` (`pumpEff`), up to forcing terms of higher order
(`hasDerivAt_shift`). The two pumps add as complex numbers. In the weakly nonlinear scaling
(`F = εf₀`) a time shift aligns `κ` with the cosine pump (`accelC_shift`, `phase_align`) and the
rigorous second-order averaging theorem `QuadraticCubic.second_order_averaging` applies: the
second-order 2:1 amplitude equation keeps `β_eff = 3α₃/(8ν) − 5α₂²/(12ν³)` and has the effective
pump coefficient `c_eff = jκ/(4ν)` (`forced_second_order`). The half-frequency threshold
`|c_eff| = σ` therefore moves: the forcing raises it iff `α₂f₀(k₁(k₀ − 4ν²) + α₂f₀) < 0` and lowers
it iff `> 0` (`pumpEff_lt_iff`, `lt_pumpEff_iff`, `threshold_raised`, `threshold_lowered`).

Scope.
* The oscillator in coefficient form with real `b, k₀, k₁, α₂, α₃, F`, continuous time, scalar
  position `x`, an arbitrary input `u(t)` (a remainder of the model); the acceleration is
  `DuffingMathieu.accel b k₀ k₁ α₃ ν t x ẋ − α₂x² + F cos 2νt + u`. Any `X` with
  `(k₀ − 4ν² + 2jνb)X = F` (`forcedDen`; unique iff `k₀ ≠ 4ν²` or `νb ≠ 0`, `forcedAmp`).
* Exact statements: the forced response (`resp_solves`), the shifted equation
  (`hasDerivAt_shift`), the time shift and the rotation equivariance of the cubic amplitude field,
  of the near-identity generator and of the van der Pol amplitude (`ampField_rotate`,
  `nearId_rotate`, `vdp_shift`), the closed forms of `|κ|²` and of `κ` to leading order.
* The averaging step is `QuadraticCubic.second_order_averaging` (damping, detuning `ν² − k₀`,
  pump `k₁` and forcing `F` of order `ε`, amplitude of order `√ε`, `0 < ε ≤ 1`, averaged solutions
  in a disc, time scale `1/ε`, starting at an aligning time `t₀`); the forced terms are `O(ε²)`
  (`abs_shiftRem_le`). Thresholds are statements about the averaged equation (level L2), via
  `Saturation.zero_stable_iff`.
* Generic mathematics, no model family.

Source: the forced response of a damped linear oscillator and its interaction with a parametric
pump through a quadratic nonlinearity (Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 4 (quadratic
nonlinearity, non-resonant hard excitation shifting the effective parameters) and Ch. 5
(parametric excitation, combined parametric and external excitation)); the second-order
2:1 amplitude equation `QuadraticCubic.second_order_averaging`, `QuadraticCubic.fieldAverage_secondField`;
the cubic amplitude field `Saturation.ampField` and its zero state `Saturation.zero_stable_iff`.

Sharpenings.
* The effective pump is complex, `κ = k₁ + 2α₂f₀/(k₀ − 4ν² + 2jνb)`, and
  `|κ|² = ((2α₂f₀ + k₁(k₀ − 4ν²))² + k₁²(2νb)²)/((k₀ − 4ν²)² + (2νb)²)` (`normSq_pumpEff_eq_sq`):
  the forced response can cancel the parametric pump only up to the damping term.
* To leading order in `ε` the forced response is real and of opposite sign to the quasi-static
  one: `X → −f₀/(3ν²)` and `κ = k₁ − 2α₂f₀/(3ν²) + O(ε)` (`pumpEff_leading`), so the forcing adds
  in phase (`α₂f₀ < 0`, `k₁ > 0`) or in antiphase (`α₂f₀ > 0`) with the parametric pump; a
  quasi-static reading (`X = f₀/ν²`) gets the sign of the correction wrong.
* `theorem/ParametricResonance/QuadraticCubicNormalForm.lean` treats a real cosine pump only; the
  general complex pump is reduced to it by a time shift and a rotation of the amplitude, not by a
  new averaging argument.

Results.
* `forcedDen`, `forcedAmp`, `pumpEff`, `resp`, `respVel`, `accelC`, `shiftRem` — the phasor
  equation, the forced response, the effective pump, the complex-pump oscillator, the remaining
  forced terms.
* `phase_add`, `re_phase_sq`, `hasDerivAt_resp`, `hasDerivAt_respVel`, `resp_solves`,
  `forcedDen_ne_zero`, `forcedDen_mul_forcedAmp` — the exact forced response.
* `accelC_ofReal`, `hasDerivAt_shift` — the exact equation of `y = x − x_f` with the pump `κ`.
* `accelC_shift`, `phase_align` — a time shift makes the complex pump a cosine pump.
* `ampField_rotate`, `nearId_rotate`, `vdp_shift` — rotation equivariance.
* `remForced`, `abs_resp_le`, `abs_shiftRem_le` — the forced terms are `O(ε²)`.
* `forced_second_order` — **rigorous second-order averaging with the forced response**: on
  `[t₀, t₀ + L/ε]`, `|x − εRe(X e^{2jνt}) − √ε Re(W̄ e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²))(2(R + 1))²)`,
  `W̄` the solution of the second-order averaged equation with pump coefficient `jκ/(4ν)`.
* `normSq_pumpEff`, `normSq_pumpEff_eq_sq`, `pumpEff_lt_iff`, `lt_pumpEff_iff`, `pumpEff_leading` —
  the size of the effective pump, when the forcing lowers or raises it, its leading order.
* `forced_zero_stable_iff`, `threshold_raised`, `threshold_lowered` — the averaged half-frequency
  threshold `|κ|² = 16ν²(σ² + Δ²)` and its shift by the forcing.
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedPump

open Complex Set
open DuffingMathieu (vdp accel)
open QuadraticCubic (phase nearId errSecond)
open Saturation (ampField)

/-- The denominator `k₀ − 4ν² + 2jνb` of the response of `ẍ + bẋ + k₀x` at the frequency `2ν`. -/
def forcedDen (b k₀ ν : ℝ) : ℂ := ((k₀ - 4 * ν ^ 2 : ℝ) : ℂ) + ((2 * ν * b : ℝ) : ℂ) * I

/-- The phasor `X̂ = f₀/(k₀ − 4ν² + 2jνb)` of the forced response to `f₀ cos 2νt`. -/
def forcedAmp (b k₀ ν f₀ : ℝ) : ℂ := (f₀ : ℂ) / forcedDen b k₀ ν

/-- The effective complex pump `κ = k₁ + 2α₂X`: the parametric modulation `k₁ cos 2νt` plus the
stiffness modulation `2α₂ Re(X e^{2jνt})` that the quadratic term makes of the forced response. -/
def pumpEff (k₁ α₂ : ℝ) (X : ℂ) : ℂ := (k₁ : ℂ) + 2 * (α₂ : ℂ) * X

/-- The forced response `Re(X e^{2jνt})`. -/
def resp (ν : ℝ) (X : ℂ) (t : ℝ) : ℝ := (X * phase ν t ^ 2).re

/-- Its velocity `Re(2jνX e^{2jνt})`. -/
def respVel (ν : ℝ) (X : ℂ) (t : ℝ) : ℝ := (2 * (ν : ℂ) * I * X * phase ν t ^ 2).re

/-- The acceleration of `ẍ + bẋ + (k₀ + Re(κ e^{2jνt}))x + γx³ = 0`, a pump of complex
amplitude `κ` (`accelC_ofReal`: for real `κ = k₁` it is `DuffingMathieu.accel`). -/
def accelC (b k₀ : ℝ) (κ : ℂ) (γ ν t x x' : ℝ) : ℝ :=
  -(b * x' + (k₀ + (κ * phase ν t ^ 2).re) * x + γ * x ^ 3)

/-- The terms of the shifted equation besides the complex pump: with `x_f = Re(X e^{2jνt})`,
`−(k₁ cos 2νt · x_f + α₂x_f² + α₃(3y²x_f + 3yx_f² + x_f³))` — forcing at `0`, `2ν`, `4ν`, `6ν` and
the products of the forced response with the cubic term. -/
def shiftRem (k₁ α₂ α₃ ν : ℝ) (X : ℂ) (t y : ℝ) : ℝ :=
  -(k₁ * Real.cos (2 * ν * t) * resp ν X t + α₂ * resp ν X t ^ 2 +
    α₃ * (3 * y ^ 2 * resp ν X t + 3 * y * resp ν X t ^ 2 + resp ν X t ^ 3))

variable {b k₀ k₁ α₂ α₃ ν : ℝ}

/-! ## The rotating phase -/

@[tmio T, powerlib_foundation] private theorem hasDerivAt_phase' (ν t : ℝ) :
    HasDerivAt (phase ν) (ν * I * phase ν t) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((ν * t : ℝ) : ℂ)) (ν : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul ν).ofReal_comp; simpa using this
  have h2 := (h1.mul_const I).cexp
  show HasDerivAt (fun x : ℝ => Complex.exp (((ν * x : ℝ) : ℂ) * I)) _ t
  convert h2 using 1
  simp only [phase]; ring

/-- The phase is a character: `e^{jν(s + t)} = e^{jνs} e^{jνt}`. -/
@[tmio T, powerlib_foundation] theorem phase_add (ν s t : ℝ) :
    phase ν (s + t) = phase ν s * phase ν t := by
  simp only [phase, ← Complex.exp_add]; congr 1; push_cast; ring

@[tmio T, powerlib_foundation] private theorem norm_phase' (ν t : ℝ) : ‖phase ν t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- `Re e^{2jνt} = cos 2νt`. -/
@[tmio T, powerlib_foundation] theorem re_phase_sq (ν t : ℝ) :
    (phase ν t ^ 2).re = Real.cos (2 * ν * t) := by
  rw [phase, ← Complex.exp_nat_mul, show ((2 : ℕ) : ℂ) * (((ν * t : ℝ) : ℂ) * I) =
    (((2 * ν * t) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_re]

/-! ## The exact forced response -/

@[tmio T, powerlib_foundation] private theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).re) f'.re t := by
  have C : HasFDerivAt Complex.re Complex.reCLM (f t) := Complex.reCLM.hasFDerivAt
  simpa using! (C.comp t h.hasFDerivAt).hasDerivAt

@[tmio T, powerlib_foundation] private theorem hasDerivAt_phase_sq_mul (ν : ℝ) (X : ℂ) (t : ℝ) :
    HasDerivAt (fun s => X * phase ν s ^ 2) (2 * (ν : ℂ) * I * X * phase ν t ^ 2) t := by
  have h := (((hasDerivAt_phase' ν t).pow 2).const_mul X)
  convert h using 1
  push_cast
  ring

@[tmio T, powerlib_foundation] theorem hasDerivAt_resp (ν : ℝ) (X : ℂ) (t : ℝ) :
    HasDerivAt (resp ν X) (respVel ν X t) t := by
  exact hasDerivAt_re (hasDerivAt_phase_sq_mul ν X t)

@[tmio T, powerlib_foundation] theorem hasDerivAt_respVel (ν : ℝ) (X : ℂ) (t : ℝ) :
    HasDerivAt (respVel ν X) (-(4 * ν ^ 2) * resp ν X t) t := by
  have h := hasDerivAt_re (hasDerivAt_phase_sq_mul ν (2 * (ν : ℂ) * I * X) t)
  convert h using 1
  · funext s; simp only [respVel]
  simp only [resp]
  rw [← Complex.re_ofReal_mul]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- **The forced response is exact.** If `X` solves the phasor equation
`(k₀ − 4ν² + 2jνb) X = F`, then `x_f = Re(X e^{2jνt})` solves `ẍ_f + bẋ_f + k₀x_f = F cos 2νt`
exactly. -/
@[tmio T, powerlib_foundation] theorem resp_solves {F : ℝ} {X : ℂ}
    (hX : forcedDen b k₀ ν * X = F) (t : ℝ) :
    HasDerivAt (respVel ν X)
      (-(b * respVel ν X t + k₀ * resp ν X t) + F * Real.cos (2 * ν * t)) t := by
  convert hasDerivAt_respVel ν X t using 1
  have hF : (F : ℝ) * Real.cos (2 * ν * t) = (forcedDen b k₀ ν * X * phase ν t ^ 2).re := by
    rw [hX, ← re_phase_sq, Complex.re_ofReal_mul]
  rw [hF]
  simp only [forcedDen, resp, respVel]
  simp only [add_mul, Complex.add_re]
  have e : (((2 * ν * b : ℝ) : ℂ) * I * X * phase ν t ^ 2).re =
      b * (2 * (ν : ℂ) * I * X * phase ν t ^ 2).re := by
    rw [← Complex.re_ofReal_mul]; congr 1; push_cast; ring
  rw [show ((k₀ - 4 * ν ^ 2 : ℝ) : ℂ) * X * phase ν t ^ 2 =
    ((k₀ - 4 * ν ^ 2 : ℝ) : ℂ) * (X * phase ν t ^ 2) by ring, Complex.re_ofReal_mul, e]
  ring

/-- The forced response exists away from undamped resonance at `2ν`. -/
@[tmio T, powerlib_foundation] theorem forcedDen_ne_zero (h : k₀ ≠ 4 * ν ^ 2) :
    forcedDen b k₀ ν ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp only [forcedDen, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, Complex.zero_re] at this
  exact h (by linarith)

@[tmio T, powerlib_foundation] theorem forcedDen_mul_forcedAmp (h : forcedDen b k₀ ν ≠ 0)
    (f₀ : ℝ) : forcedDen b k₀ ν * forcedAmp b k₀ ν f₀ = f₀ := by
  rw [forcedAmp]; field_simp


/-! ## The exact shift by the forced response -/

/-- For a real amplitude the complex pump is the cosine pump of `DuffingMathieu.accel`. -/
@[tmio T, powerlib_foundation] theorem accelC_ofReal (b k₀ k₁ γ ν t x x' : ℝ) :
    accelC b k₀ (k₁ : ℂ) γ ν t x x' = accel b k₀ k₁ γ ν t x x' := by
  simp only [accelC, accel, Complex.re_ofReal_mul, re_phase_sq]

@[tmio T, powerlib_foundation] private theorem re_pumpEff (k₁ α₂ ν : ℝ) (X : ℂ) (t : ℝ) :
    (pumpEff k₁ α₂ X * phase ν t ^ 2).re = k₁ * Real.cos (2 * ν * t) + 2 * α₂ * resp ν X t := by
  rw [pumpEff, add_mul, Complex.add_re, Complex.re_ofReal_mul, re_phase_sq,
    show 2 * (α₂ : ℂ) * X * phase ν t ^ 2 = ((2 * α₂ : ℝ) : ℂ) * (X * phase ν t ^ 2) by
      push_cast; ring, Complex.re_ofReal_mul, resp]

/-- **The exact shift by the forced response.** Let `x` solve
`ẍ + bẋ + (k₀ + k₁ cos 2νt)x + α₂x² + α₃x³ = F cos 2νt + u(t)` and let `X` solve the phasor
equation `(k₀ − 4ν² + 2jνb)X = F`. Then `y = x − Re(X e^{2jνt})` solves exactly
`ÿ + bẏ + (k₀ + Re(κ e^{2jνt}))y + α₂y² + α₃y³ = shiftRem + u(t)` with the complex pump
`κ = k₁ + 2α₂X` (`pumpEff`): the quadratic term turns the forced response into a stiffness
modulation at the pump frequency, which adds to the parametric one as a complex number. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_shift {F : ℝ} {X : ℂ}
    (hX : forcedDen b k₀ ν * X = F) {x x' u : ℝ → ℝ}
    (hx' : ∀ t, HasDerivAt x' (accel b k₀ k₁ α₃ ν t (x t) (x' t) - α₂ * x t ^ 2 +
      F * Real.cos (2 * ν * t) + u t) t) (t : ℝ) :
    HasDerivAt (fun t => x' t - respVel ν X t)
      (accelC b k₀ (pumpEff k₁ α₂ X) α₃ ν t (x t - resp ν X t) (x' t - respVel ν X t) -
        α₂ * (x t - resp ν X t) ^ 2 + (shiftRem k₁ α₂ α₃ ν X t (x t - resp ν X t) + u t)) t := by
  convert (hx' t).sub (resp_solves hX t) using 1
  rw [accelC, re_pumpEff, accel, shiftRem]
  ring

/-- **A time shift aligns the complex pump.** If `κ e^{2jνt₀} = |κ|`, the complex pump at time
`s + t₀` is the cosine pump `|κ| cos 2νs`. -/
@[tmio T, powerlib_foundation] theorem accelC_shift {κ : ℂ} {t₀ : ℝ}
    (h : κ * phase ν t₀ ^ 2 = (‖κ‖ : ℂ)) (b k₀ γ s x x' : ℝ) :
    accelC b k₀ κ γ ν (s + t₀) x x' = accel b k₀ ‖κ‖ γ ν s x x' := by
  rw [accelC, phase_add, mul_pow, show κ * (phase ν s ^ 2 * phase ν t₀ ^ 2) =
    (κ * phase ν t₀ ^ 2) * phase ν s ^ 2 by ring, h, Complex.re_ofReal_mul, re_phase_sq, accel]

/-- The aligning time exists: `κ e^{2jνt₀} = |κ|` for `t₀ = −arg κ/(2ν)` (`ν ≠ 0`), and then for
every `t₀ + kπ/ν`. -/
@[tmio T, powerlib_foundation] theorem phase_align (hν : ν ≠ 0) (κ : ℂ) :
    κ * phase ν (-Complex.arg κ / (2 * ν)) ^ 2 = (‖κ‖ : ℂ) := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have hp : phase ν (-Complex.arg κ / (2 * ν)) ^ 2 = Complex.exp (-((Complex.arg κ : ℂ) * I)) := by
    rw [phase, ← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
  rw [hp]
  calc κ * Complex.exp (-((Complex.arg κ : ℂ) * I)) =
      ((‖κ‖ : ℂ) * Complex.exp ((Complex.arg κ : ℂ) * I)) *
        Complex.exp (-((Complex.arg κ : ℂ) * I)) := by rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (‖κ‖ : ℂ) := by
      rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-! ## Rotations -/

@[tmio T, powerlib_foundation] private theorem conj_phase' (ν t : ℝ) :
    (starRingEnd ℂ) (phase ν t) = (phase ν t)⁻¹ := by
  rw [phase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_neg]
  ring_nf

/-- **The cubic amplitude field is equivariant under rotations:**
`e^{jντ} F_c(e^{−jντ} W) = F_{c e^{2jντ}}(W)` — rotating the amplitude rotates the pump
coefficient by twice the angle. -/
@[tmio T, powerlib_foundation] theorem ampField_rotate (σ Δ : ℝ) (c : ℂ) (η β ν τ : ℝ) (W : ℂ) :
    phase ν τ * ampField σ Δ c η β ((phase ν τ)⁻¹ * W) =
      ampField σ Δ (c * phase ν τ ^ 2) η β W := by
  have h0 := QuadraticCubic.phase_ne_zero ν τ
  have hn : ‖(phase ν τ)⁻¹ * W‖ = ‖W‖ := by
    rw [norm_mul, norm_inv, norm_phase', inv_one, one_mul]
  simp only [ampField, slowFlowField, hn, map_mul, map_inv₀, conj_phase', inv_inv]
  field_simp

/-- **The near-identity generator is equivariant:** `u(e^{jντ}w, t) = e^{jντ} u(w, t + τ)`. -/
@[tmio T, powerlib_foundation] theorem nearId_rotate (α₂ ν τ : ℝ) (w : ℂ) (t : ℝ) :
    nearId α₂ ν (phase ν τ * w) t = phase ν τ * nearId α₂ ν w (t + τ) := by
  have h0 := QuadraticCubic.phase_ne_zero ν τ
  have h1 := QuadraticCubic.phase_ne_zero ν t
  simp only [nearId, phase_add, map_mul, conj_phase', mul_inv]
  field_simp

/-- The van der Pol amplitude at the shifted time: `vdp(s) = e^{jνt₀} vdp(s + t₀)`. -/
@[tmio T, powerlib_foundation] theorem vdp_shift (ν s t₀ x x' : ℝ) :
    vdp ν s x x' = phase ν t₀ * vdp ν (s + t₀) x x' := by
  simp only [vdp, phase, ← mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring


/-! ## Rigorous second-order averaging with the forced response -/

/-- The bound `C_f` of the forced terms, `|shiftRem| ≤ ε² C_f` while `|y| ≤ √ε · 2(R + 1)`
(`abs_shiftRem_le`), for a forced response `ε Re(X e^{2jνt})` with `|X| = ξ`:
`C_f = |k₁|ξ + |α₂|ξ² + |α₃|(3r²ξ + 3rξ² + ξ³)`, `r = 2(R + 1)`. -/
def remForced (k₁ α₂ α₃ R ξ : ℝ) : ℝ :=
  |k₁| * ξ + |α₂| * ξ ^ 2 +
    |α₃| * (3 * (2 * (R + 1)) ^ 2 * ξ + 3 * (2 * (R + 1)) * ξ ^ 2 + ξ ^ 3)

@[tmio T, powerlib_foundation] theorem abs_resp_le (ν : ℝ) (X : ℂ) (t : ℝ) :
    |resp ν X t| ≤ ‖X‖ :=
  (Complex.abs_re_le_norm _).trans (by rw [norm_mul, norm_pow, norm_phase', one_pow, mul_one])

/-- **The forced terms are of order `ε²`** (`0 < ε ≤ 1`): for the scaled forced response
`ε Re(X e^{2jνt})` and `|y| ≤ √ε · 2(R + 1)`, `|shiftRem| ≤ ε² remForced k₁ α₂ α₃ R |X|`. -/
@[tmio T, powerlib_foundation] theorem abs_shiftRem_le {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 ≤ R) (X : ℂ) (t : ℝ) {y : ℝ} (hy : |y| ≤ √ε * (2 * (R + 1))) :
    |shiftRem (ε * k₁) α₂ α₃ ν ((ε : ℂ) * X) t y| ≤ ε ^ 2 * remForced k₁ α₂ α₃ R ‖X‖ := by
  set r := 2 * (R + 1) with hr
  set ρ := resp ν X t with hρ
  set ξ := ‖X‖ with hξ
  have hr0 : 0 ≤ r := by positivity
  have hρξ : |ρ| ≤ ξ := abs_resp_le ν X t
  have hξ0 : 0 ≤ ξ := norm_nonneg _
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hy1 : |y| ≤ r := hy.trans (by nlinarith)
  have hy2 : y ^ 2 ≤ ε * r ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg y) hy 2
    rwa [sq_abs, mul_pow, Real.sq_sqrt hε.le] at this
  have hre : resp ν ((ε : ℂ) * X) t = ε * ρ := by
    simp only [hρ, resp, mul_assoc, Complex.re_ofReal_mul]
  have e : shiftRem (ε * k₁) α₂ α₃ ν ((ε : ℂ) * X) t y =
      -(ε ^ 2 * (k₁ * Real.cos (2 * ν * t) * ρ) + ε ^ 2 * (α₂ * ρ ^ 2) +
        α₃ * (ε * (3 * y ^ 2 * ρ) + ε ^ 2 * (3 * y * ρ ^ 2) + ε ^ 3 * ρ ^ 3)) := by
    rw [shiftRem, hre]; ring
  have hc := Real.abs_cos_le_one (2 * ν * t)
  have t1 : |k₁ * Real.cos (2 * ν * t) * ρ| ≤ |k₁| * ξ := by
    rw [abs_mul, abs_mul]
    calc |k₁| * |Real.cos (2 * ν * t)| * |ρ| ≤ |k₁| * 1 * ξ := by gcongr
      _ = |k₁| * ξ := by ring
  have t2 : |α₂ * ρ ^ 2| ≤ |α₂| * ξ ^ 2 := by
    rw [abs_mul, abs_pow]; gcongr
  have t3 : |ε * (3 * y ^ 2 * ρ)| ≤ ε ^ 2 * (3 * r ^ 2 * ξ) := by
    rw [abs_mul, abs_of_pos hε, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
      abs_of_nonneg (sq_nonneg y)]
    calc ε * (3 * y ^ 2 * |ρ|) ≤ ε * (3 * (ε * r ^ 2) * ξ) := by gcongr
      _ = ε ^ 2 * (3 * r ^ 2 * ξ) := by ring
  have t4 : |ε ^ 2 * (3 * y * ρ ^ 2)| ≤ ε ^ 2 * (3 * r * ξ ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2), abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_pow]
    gcongr
  have t5 : |ε ^ 3 * ρ ^ 3| ≤ ε ^ 2 * ξ ^ 3 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ε ^ 3), abs_pow]
    have h3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
    gcongr
  have t345 : |α₃ * (ε * (3 * y ^ 2 * ρ) + ε ^ 2 * (3 * y * ρ ^ 2) + ε ^ 3 * ρ ^ 3)| ≤ (|α₃| *
      (ε ^ 2 * (3 * r ^ 2 * ξ) + ε ^ 2 * (3 * r * ξ ^ 2) + ε ^ 2 * ξ ^ 3)) := by
    rw [abs_mul]
    gcongr
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add t3 t4)) t5)
  have tA : |ε ^ 2 * (k₁ * Real.cos (2 * ν * t) * ρ)| ≤ ε ^ 2 * (|k₁| * ξ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2)]; gcongr
  have tB : |ε ^ 2 * (α₂ * ρ ^ 2)| ≤ ε ^ 2 * (|α₂| * ξ ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2)]; gcongr
  rw [e, abs_neg]
  calc _ ≤ |ε ^ 2 * (k₁ * Real.cos (2 * ν * t) * ρ) + ε ^ 2 * (α₂ * ρ ^ 2)| +
        |α₃ * (ε * (3 * y ^ 2 * ρ) + ε ^ 2 * (3 * y * ρ ^ 2) + ε ^ 3 * ρ ^ 3)| := abs_add_le _ _
    _ ≤ (ε ^ 2 * (|k₁| * ξ) + ε ^ 2 * (|α₂| * ξ ^ 2)) + (|α₃| *
        (ε ^ 2 * (3 * r ^ 2 * ξ) + ε ^ 2 * (3 * r * ξ ^ 2) + ε ^ 2 * ξ ^ 3)) :=
      add_le_add ((abs_add_le _ _).trans (add_le_add tA tB)) t345
    _ = ε ^ 2 * remForced k₁ α₂ α₃ R ξ := by simp only [remForced, hr]; ring

@[tmio T, powerlib_foundation] private theorem abs_le_scaled {ε : ℝ} (hε : 0 < ε) (ν t x x' : ℝ) :
    |x| ≤ √ε * ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t x x'‖ := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have e : x = (vdp ν t x x' * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re :=
    (DuffingMathieu.pos_vdp ν t x x').symm
  have hz : vdp ν t x x' = ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t x x') := by field_simp
  calc |x| = |(vdp ν t x x' * Complex.exp (((ν * t : ℝ) : ℂ) * I)).re| := by rw [← e]
    _ ≤ ‖vdp ν t x x' * Complex.exp (((ν * t : ℝ) : ℂ) * I)‖ := Complex.abs_re_le_norm _
    _ = √ε * ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t x x'‖ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      conv_lhs => rw [hz]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]

/-- **Rigorous second-order averaging of the pumped oscillator with an additive forcing at the
pump frequency.** For
`ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = εf₀ cos 2νt + u(t)` (`ν > 0`, `0 < ε ≤ 1`),
let `X` solve the phasor equation `(ν² − εd − 4ν² + 2jνεb)X = f₀` (`forcedDen`; the forced
response is `εRe(X e^{2jνt})`, non-resonant), `κ = k₁ + 2α₂X` the effective complex pump, and
`t₀` an aligning time, `κ e^{2jνt₀} = |κ|` (`phase_align`). With the shifted state
`y = x − εRe(X e^{2jνt})`, its scaled van der Pol amplitude `w = z_y/√ε` and transformed amplitude
`W = w − √ε u(w, t)` (`QuadraticCubic.nearId`), let `W̄` solve the second-order averaged equation
with the complex pump coefficient `c_eff = jκ/(4ν)`,
`W̄̇ = ε ampField (b/2) (d/(2ν)) (jκ/(4ν)) 0 β_eff W̄`, `β_eff = 3α₃/(8ν) − 5α₂²/(12ν³)`, on
`[t₀, t₀ + L/ε]` in the disc `|W̄| ≤ R`, from `W̄(t₀) = W(t₀)`. Assume `|w(t₀)| < 2(R + 1)`, the
input bound `|u| ≤ ε²M_u` while `|w| ≤ 2(R + 1)`, the branch condition and
`B = errSecond b d |κ| α₂ α₃ ν R L ε (M_u + remForced …) < 1`. Then on `[t₀, t₀ + L/ε]`
`|x(t) − εRe(X e^{2jνt}) − √ε Re(W̄(t) e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²)) (2(R + 1))²)`.
The forced response and the parametric modulation enter the averaged equation only through the
complex sum `κ = k₁ + 2α₂X`; the cubic coefficient is unchanged. Proof: the exact shift
(`hasDerivAt_shift`), the time shift by `t₀` (`accelC_shift`), and
`QuadraticCubic.second_order_averaging` with the real pump `|κ|`, rotated back
(`ampField_rotate`, `nearId_rotate`, `vdp_shift`). -/
@[tmio T, powerlib_foundation] theorem forced_second_order (hν : 0 < ν)
    {b d f₀ R L ε Mu t₀ : ℝ} {X : ℂ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hMu : 0 ≤ Mu) (hX : forcedDen (ε * b) (ν ^ 2 - ε * d) ν * X = f₀)
    (ht₀ : pumpEff k₁ α₂ X * phase ν t₀ ^ 2 = (‖pumpEff k₁ α₂ X‖ : ℂ))
    {x x' u : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x' (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) -
      α₂ * x t ^ 2 + ε * f₀ * Real.cos (2 * ν * t) + u t) t)
    (hu : ∀ t ∈ Icc t₀ (t₀ + L / ε), ‖((√ε : ℝ) : ℂ)⁻¹ *
        vdp ν t (x t - ε * resp ν X t) (x' t - ε * respVel ν X t)‖ ≤ 2 * (R + 1) →
      |u t| ≤ ε ^ 2 * Mu)
    {Wbar : ℝ → ℂ}
    (hWbar : ∀ t ∈ Icc t₀ (t₀ + L / ε), HasDerivWithinAt Wbar
      (ε • ampField (b / 2) (d / (2 * ν)) (I * (pumpEff k₁ α₂ X / (4 * ν))) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (Wbar t)) (Icc t₀ (t₀ + L / ε)) t)
    (hbound : ∀ t ∈ Icc t₀ (t₀ + L / ε), ‖Wbar t‖ ≤ R)
    (h0 : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν t₀ (x t₀ - ε * resp ν X t₀) (x' t₀ - ε * respVel ν X t₀) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ *
        vdp ν t₀ (x t₀ - ε * resp ν X t₀) (x' t₀ - ε * respVel ν X t₀)) t₀ = Wbar t₀)
    (hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t₀ (x t₀ - ε * resp ν X t₀) (x' t₀ - ε * respVel ν X t₀)‖ <
      2 * (R + 1))
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d ‖pumpEff k₁ α₂ X‖ α₂ α₃ ν R L ε
      (Mu + remForced k₁ α₂ α₃ R ‖X‖) < 1) :
    ∀ t ∈ Icc t₀ (t₀ + L / ε), |x t - ε * resp ν X t - √ε * (Wbar t * phase ν t).re| ≤
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
  -- the shifted state
  have hyd : ∀ t, HasDerivAt y (y' t) t := fun t =>
    (hx t).sub ((hasDerivAt_resp ν X t).const_mul ε)
  have hyd' : ∀ t, HasDerivAt y' (accelC (ε * b) (ν ^ 2 - ε * d) ((ε : ℂ) * κ) α₃ ν t (y t) (y' t) -
      α₂ * y t ^ 2 + (shiftRem (ε * k₁) α₂ α₃ ν ((ε : ℂ) * X) t (y t) + u t)) t := by
    intro t
    have h := hasDerivAt_shift (k₁ := ε * k₁) (α₂ := α₂) (α₃ := α₃) hXε (x := x) (x' := x')
      (u := u) hx' t
    simp only [hrespε, hvelε, hκε] at h
    exact h
  -- the time shift aligning the pump
  have hnκ : ‖(ε : ℂ) * κ‖ = ε * ‖κ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
  have ht₀ε : ((ε : ℂ) * κ) * phase ν t₀ ^ 2 = (‖(ε : ℂ) * κ‖ : ℂ) := by
    rw [mul_assoc, ht₀, hnκ]; push_cast; ring
  set xs : ℝ → ℝ := fun s => y (s + t₀) with hxs_def
  set xs' : ℝ → ℝ := fun s => y' (s + t₀) with hxs'_def
  set us : ℝ → ℝ := fun s =>
    shiftRem (ε * k₁) α₂ α₃ ν ((ε : ℂ) * X) (s + t₀) (y (s + t₀)) + u (s + t₀) with hus_def
  set Ws : ℝ → ℂ := fun s => phase ν t₀ * Wbar (s + t₀) with hWs_def
  have hxs : ∀ s, HasDerivAt xs (xs' s) s := fun s => (hyd (s + t₀)).comp_add_const s t₀
  have hxs' : ∀ s, HasDerivAt xs' (accel (ε * b) (ν ^ 2 - ε * d) (ε * ‖κ‖) α₃ ν s (xs s) (xs' s) -
      α₂ * xs s ^ 2 + us s) s := by
    intro s
    have h := (hyd' (s + t₀)).comp_add_const s t₀
    rw [accelC_shift ht₀ε, hnκ] at h
    exact h
  have hnorm : ∀ s, ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν s (xs s) (xs' s)‖ =
      ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν (s + t₀) (y (s + t₀)) (y' (s + t₀))‖ := by
    intro s
    rw [vdp_shift ν s t₀, norm_mul, norm_mul, norm_mul, norm_phase', one_mul]
  have hmaps : MapsTo (fun s => s + t₀) (Icc 0 (L / ε)) (Icc t₀ (t₀ + L / ε)) :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hrem0 : 0 ≤ remForced k₁ α₂ α₃ R ‖X‖ := by unfold remForced; positivity
  have hmain := QuadraticCubic.second_order_averaging (b := b) (d := d) (k₁ := ‖κ‖) (α₂ := α₂)
    (α₃ := α₃) (Mu := Mu + remForced k₁ α₂ α₃ R ‖X‖) (Wbar := Ws) hν hR hL hε hε1
    (by linarith) hxs hxs'
    (fun s hs hw => by
      rw [hnorm] at hw
      have hu' := hu (s + t₀) (hmaps hs) hw
      have hyb : |y (s + t₀)| ≤ √ε * (2 * (R + 1)) :=
        (abs_le_scaled hε ν (s + t₀) _ (y' (s + t₀))).trans
          (mul_le_mul_of_nonneg_left hw hs0.le)
      have hr := abs_shiftRem_le (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) (ν := ν) hε hε1 hR X (s + t₀)
        hyb
      calc |us s| ≤ |shiftRem (ε * k₁) α₂ α₃ ν ((ε : ℂ) * X) (s + t₀) (y (s + t₀))| +
            |u (s + t₀)| := abs_add_le _ _
        _ ≤ ε ^ 2 * remForced k₁ α₂ α₃ R ‖X‖ + ε ^ 2 * Mu := add_le_add hr hu'
        _ = ε ^ 2 * (Mu + remForced k₁ α₂ α₃ R ‖X‖) := by ring)
    (fun s hs => by
      have hsh : HasDerivWithinAt (fun s => s + t₀) 1 (Icc 0 (L / ε)) s :=
        ((hasDerivAt_id s).add_const t₀).hasDerivWithinAt
      have h := ((hWbar (s + t₀) (hmaps hs)).scomp s hsh hmaps).const_mul (phase ν t₀)
      have hrot : phase ν t₀ * ampField (b / 2) (d / (2 * ν)) (I * (κ / (4 * ν))) 0
          (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (Wbar (s + t₀)) =
          ampField (b / 2) (d / (2 * ν)) (I * ((‖κ‖ / (4 * ν) : ℝ) : ℂ)) 0
            (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (Ws s) := by
        have h0' := QuadraticCubic.phase_ne_zero ν t₀
        have e1 : Wbar (s + t₀) = (phase ν t₀)⁻¹ * Ws s := by
          simp only [hWs_def]; field_simp
        rw [e1, ampField_rotate]
        congr 1
        rw [show I * (κ / (4 * ν)) * phase ν t₀ ^ 2 = I * (κ * phase ν t₀ ^ 2) / (4 * ν) by ring,
          ht₀]
        push_cast; ring
      convert h using 1
      · rfl
      rw [one_smul, Complex.real_smul, Complex.real_smul, ← hrot]
      ring)
    (fun s hs => by
      simp only [hWs_def, norm_mul, norm_phase', one_mul]
      exact hbound (s + t₀) (hmaps hs))
    (by
      have e1 : vdp ν 0 (xs 0) (xs' 0) = phase ν t₀ * vdp ν t₀ (y t₀) (y' t₀) := by
        rw [vdp_shift ν 0 t₀]; simp only [hxs_def, hxs'_def, zero_add]
      rw [e1, mul_left_comm, nearId_rotate, zero_add]
      simp only [hWs_def, zero_add]
      rw [← h0]
      ring)
    (by rw [hnorm, zero_add]; exact hw0) hbranch hsmall
  intro t ht
  have hs : t - t₀ ∈ Icc 0 (L / ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h := hmain (t - t₀) hs
  simp only [hxs_def, hWs_def, sub_add_cancel] at h
  rw [show phase ν t₀ * Wbar t * phase ν (t - t₀) = Wbar t * phase ν t by
    rw [mul_comm (phase ν t₀), mul_assoc, ← phase_add, add_sub_cancel]] at h
  exact h


/-! ## The effective pump and the half-frequency threshold -/

@[tmio T, powerlib_foundation] private theorem normSq_forcedDen_ne_zero
    (h : forcedDen b k₀ ν ≠ 0) : (k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2 ≠ 0 := by
  intro h0
  apply h
  have h1 : k₀ - 4 * ν ^ 2 = 0 := by nlinarith [sq_nonneg (k₀ - 4 * ν ^ 2), sq_nonneg (2 * ν * b)]
  have h2 : 2 * ν * b = 0 := by nlinarith [sq_nonneg (k₀ - 4 * ν ^ 2), sq_nonneg (2 * ν * b)]
  rw [forcedDen, h1, h2]; simp

/-- **The size of the effective pump.** For the forced response `X̂ = f₀/(k₀ − 4ν² + 2jνb)`:
`|k₁ + 2α₂X̂|² = k₁² + 4α₂f₀(k₁(k₀ − 4ν²) + α₂f₀)/((k₀ − 4ν²)² + 4ν²b²)`. -/
@[tmio T, powerlib_foundation] theorem normSq_pumpEff (h : forcedDen b k₀ ν ≠ 0)
    (k₁ α₂ f₀ : ℝ) :
    ‖pumpEff k₁ α₂ (forcedAmp b k₀ ν f₀)‖ ^ 2 = k₁ ^ 2 +
      4 * α₂ * f₀ * (k₁ * (k₀ - 4 * ν ^ 2) + α₂ * f₀) /
        ((k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2) := by
  have hN := normSq_forcedDen_ne_zero h
  have hns : Complex.normSq (forcedDen b k₀ ν) = (k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2 := by
    rw [forcedDen, Complex.normSq_add_mul_I]
  have hXre : (forcedAmp b k₀ ν f₀).re =
      f₀ * (k₀ - 4 * ν ^ 2) / ((k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2) := by
    rw [forcedAmp, Complex.div_re, hns]
    simp only [forcedDen, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hXim : (forcedAmp b k₀ ν f₀).im =
      -(f₀ * (2 * ν * b)) / ((k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2) := by
    rw [forcedAmp, Complex.div_im, hns]
    simp only [forcedDen, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hre : (pumpEff k₁ α₂ (forcedAmp b k₀ ν f₀)).re = k₁ + 2 * α₂ * (forcedAmp b k₀ ν f₀).re := by
    simp [pumpEff]
  have him : (pumpEff k₁ α₂ (forcedAmp b k₀ ν f₀)).im = 2 * α₂ * (forcedAmp b k₀ ν f₀).im := by
    simp [pumpEff]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him, hXre, hXim]
  set N := (k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2 with hNdef
  field_simp
  rw [hNdef]
  ring

/-- **The effective pump as a sum of squares:**
`|k₁ + 2α₂X̂|² = ((2α₂f₀ + k₁(k₀ − 4ν²))² + k₁²(2νb)²)/((k₀ − 4ν²)² + (2νb)²)`. The forced response
cancels the pump only up to the damping term: `|κ| ≥ |k₁| · 2ν|b|/|k₀ − 4ν² + 2jνb|`, with equality
iff `2α₂f₀ = −k₁(k₀ − 4ν²)`. -/
@[tmio T, powerlib_foundation] theorem normSq_pumpEff_eq_sq (h : forcedDen b k₀ ν ≠ 0)
    (k₁ α₂ f₀ : ℝ) :
    ‖pumpEff k₁ α₂ (forcedAmp b k₀ ν f₀)‖ ^ 2 =
      ((2 * α₂ * f₀ + k₁ * (k₀ - 4 * ν ^ 2)) ^ 2 + k₁ ^ 2 * (2 * ν * b) ^ 2) /
        ((k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2) := by
  have hN := normSq_forcedDen_ne_zero h
  rw [normSq_pumpEff h, eq_div_iff hN, add_mul, div_mul_cancel₀ _ hN]
  ring

/-- **The forced response lowers the effective pump** iff `α₂f₀(k₁(k₀ − 4ν²) + α₂f₀) < 0`:
`|k₁ + 2α₂X̂| < |k₁|` exactly then. -/
@[tmio T, powerlib_foundation] theorem pumpEff_lt_iff (h : forcedDen b k₀ ν ≠ 0)
    (k₁ α₂ f₀ : ℝ) :
    ‖pumpEff k₁ α₂ (forcedAmp b k₀ ν f₀)‖ < |k₁| ↔
      α₂ * f₀ * (k₁ * (k₀ - 4 * ν ^ 2) + α₂ * f₀) < 0 := by
  have hN : 0 < (k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2 :=
    lt_of_le_of_ne (by positivity) (normSq_forcedDen_ne_zero h).symm
  rw [← sq_lt_sq₀ (norm_nonneg _) (abs_nonneg _), sq_abs, normSq_pumpEff h]
  constructor
  · intro h1
    have : 4 * α₂ * f₀ * (k₁ * (k₀ - 4 * ν ^ 2) + α₂ * f₀) /
        ((k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2) < 0 := by linarith
    rw [div_neg_iff] at this
    rcases this with ⟨_, h2⟩ | ⟨h2, _⟩
    · linarith
    · linarith
  · intro h1
    have : 4 * α₂ * f₀ * (k₁ * (k₀ - 4 * ν ^ 2) + α₂ * f₀) /
        ((k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2) < 0 := div_neg_of_neg_of_pos (by linarith) hN
    linarith

/-- **The forced response raises the effective pump** iff `α₂f₀(k₁(k₀ − 4ν²) + α₂f₀) > 0`. -/
@[tmio T, powerlib_foundation] theorem lt_pumpEff_iff (h : forcedDen b k₀ ν ≠ 0)
    (k₁ α₂ f₀ : ℝ) :
    |k₁| < ‖pumpEff k₁ α₂ (forcedAmp b k₀ ν f₀)‖ ↔
      0 < α₂ * f₀ * (k₁ * (k₀ - 4 * ν ^ 2) + α₂ * f₀) := by
  have hN : 0 < (k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2 :=
    lt_of_le_of_ne (by positivity) (normSq_forcedDen_ne_zero h).symm
  rw [← sq_lt_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, normSq_pumpEff h]
  constructor
  · intro h1
    have : 0 < 4 * α₂ * f₀ * (k₁ * (k₀ - 4 * ν ^ 2) + α₂ * f₀) /
        ((k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2) := by linarith
    have h2 := (div_pos_iff_of_pos_right hN).mp this
    linarith
  · intro h1
    have : 0 < 4 * α₂ * f₀ * (k₁ * (k₀ - 4 * ν ^ 2) + α₂ * f₀) /
        ((k₀ - 4 * ν ^ 2) ^ 2 + (2 * ν * b) ^ 2) := div_pos (by linarith) hN
    linarith

/-- **At leading order the forced response adds in phase or in antiphase.** In the scaling of
`forced_second_order`, `X̂_ε = f₀/(−3ν² − εd + 2jνεb)`, exactly
`k₁ + 2α₂X̂_ε = (k₁ − 2α₂f₀/(3ν²)) + ε · 2α₂f₀(2jνb − d)/(3ν²(−3ν² − εd + 2jνεb))`: the
effective pump is real up to `O(ε)`, `κ₀ = k₁ − 2α₂f₀/(3ν²)` (the response at `2ν ≈ 2ω` is
`−1/3` of the quasi-static one, `f₀/ν²`). -/
@[tmio T, powerlib_foundation] theorem pumpEff_leading (hν : ν ≠ 0) {ε b d : ℝ}
    (h : forcedDen (ε * b) (ν ^ 2 - ε * d) ν ≠ 0) (k₁ α₂ f₀ : ℝ) :
    pumpEff k₁ α₂ (forcedAmp (ε * b) (ν ^ 2 - ε * d) ν f₀) =
      ((k₁ - 2 * α₂ * f₀ / (3 * ν ^ 2) : ℝ) : ℂ) +
        (ε : ℂ) * (2 * α₂ * f₀ * (2 * ν * b * I - d) /
          (3 * ν ^ 2 * forcedDen (ε * b) (ν ^ 2 - ε * d) ν)) := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  set D := forcedDen (ε * b) (ν ^ 2 - ε * d) ν with hDdef
  have key : 3 * (ν : ℂ) ^ 2 + D = (ε : ℂ) * (2 * ν * b * I - d) := by
    simp only [hDdef, forcedDen]; push_cast; ring
  calc pumpEff k₁ α₂ (forcedAmp (ε * b) (ν ^ 2 - ε * d) ν f₀) =
      (k₁ : ℂ) + 2 * α₂ * (f₀ / D) := rfl
    _ = ((k₁ - 2 * α₂ * f₀ / (3 * ν ^ 2) : ℝ) : ℂ) +
        2 * α₂ * f₀ * (3 * ν ^ 2 + D) / (3 * ν ^ 2 * D) := by push_cast; field_simp; ring
    _ = _ := by rw [key]; ring

/-- **The averaged half-frequency threshold with the effective pump.** The zero state of the
averaged equation with pump coefficient `jκ/(4ν)` is locally exponentially stable iff `σ > 0` and
`|κ|² < 16ν²(σ² + Δ²)` (`Saturation.zero_stable_iff`): at exact tuning the threshold is
`|κ| = 4νσ`, the unforced one `|k₁| = 4νσ`. -/
@[tmio TM, powerlib_foundation] theorem forced_zero_stable_iff (hν : 0 < ν) (σ Δ β : ℝ)
    (κ : ℂ) :
    LocallyExponentiallyStable (Saturation.ampSystem σ Δ (I * (κ / (4 * ν))) 0 β) 0 ↔
      0 < σ ∧ ‖κ‖ ^ 2 < 16 * ν ^ 2 * (σ ^ 2 + Δ ^ 2) := by
  rw [Saturation.zero_stable_iff]
  have hn : ‖I * (κ / (4 * ν))‖ ^ 2 = ‖κ‖ ^ 2 / (16 * ν ^ 2) := by
    rw [norm_mul, Complex.norm_I, one_mul, norm_div, div_pow,
      show ‖(4 : ℂ) * ν‖ = 4 * ν by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hν.le]]
    ring
  rw [hn, div_lt_iff₀ (by positivity)]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- **The forced response raises the parametric threshold** when
`α₂f₀(k₁(k₀ − 4ν²) + α₂f₀) < 0`: every averaged zero state that is locally exponentially stable
without the forcing (pump `jk₁/(4ν)`) stays so with it (pump `jκ/(4ν)`). -/
@[tmio TM, powerlib_foundation] theorem threshold_raised (hν : 0 < ν)
    (h : forcedDen b k₀ ν ≠ 0) {α₂ f₀ : ℝ} (hc : α₂ * f₀ * (k₁ * (k₀ - 4 * ν ^ 2) + α₂ * f₀) < 0)
    (σ Δ β : ℝ) :
    LocallyExponentiallyStable (Saturation.ampSystem σ Δ (I * ((k₁ : ℂ) / (4 * ν))) 0 β) 0 →
      LocallyExponentiallyStable
        (Saturation.ampSystem σ Δ (I * (pumpEff k₁ α₂ (forcedAmp b k₀ ν f₀) / (4 * ν))) 0 β) 0 := by
  rw [forced_zero_stable_iff hν, forced_zero_stable_iff hν, Complex.norm_real, Real.norm_eq_abs]
  rintro ⟨h1, h2⟩
  have h3 := (pumpEff_lt_iff h k₁ α₂ f₀).mpr hc
  refine ⟨h1, lt_of_le_of_lt ?_ h2⟩
  rw [sq_abs]
  have := pow_le_pow_left₀ (norm_nonneg _) h3.le 2
  rwa [sq_abs] at this

/-- **The forced response lowers the parametric threshold** when
`α₂f₀(k₁(k₀ − 4ν²) + α₂f₀) > 0`: every averaged zero state that is locally exponentially stable
with the forcing is so without it. -/
@[tmio TM, powerlib_foundation] theorem threshold_lowered (hν : 0 < ν)
    (h : forcedDen b k₀ ν ≠ 0) {α₂ f₀ : ℝ} (hc : 0 < α₂ * f₀ * (k₁ * (k₀ - 4 * ν ^ 2) + α₂ * f₀))
    (σ Δ β : ℝ) :
    LocallyExponentiallyStable
        (Saturation.ampSystem σ Δ (I * (pumpEff k₁ α₂ (forcedAmp b k₀ ν f₀) / (4 * ν))) 0 β) 0 →
      LocallyExponentiallyStable (Saturation.ampSystem σ Δ (I * ((k₁ : ℂ) / (4 * ν))) 0 β) 0 := by
  rw [forced_zero_stable_iff hν, forced_zero_stable_iff hν, Complex.norm_real, Real.norm_eq_abs]
  rintro ⟨h1, h2⟩
  have h3 := (lt_pumpEff_iff h k₁ α₂ f₀).mpr hc
  refine ⟨h1, lt_of_le_of_lt ?_ h2⟩
  have := pow_le_pow_left₀ (abs_nonneg _) h3.le 2
  rwa [sq_abs] at this ⊢

end powerlib.ParametricResonance.ForcedPump
