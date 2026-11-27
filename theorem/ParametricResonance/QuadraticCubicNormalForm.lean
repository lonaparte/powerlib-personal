import theorem.ParametricResonance.DuffingMathieu
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Quadratic and cubic stiffness: the second-order 2:1 amplitude equation

For the parametrically pumped oscillator with quadratic and cubic stiffness,
`ẍ + bẋ + (k₀ + k₁ cos 2νt) x + α₂x² + α₃x³ = u(t)` (physical form `k₀ = ω²`, `k₁ = εω²`), the
quadratic terms have no resonant part at the half pump frequency `ν`: first-order averaging
removes them and is then blind to them, although at amplitude `a` they shift the frequency by
`O(α₂²a²/ν³)`, of the same order as the cubic shift `3α₃a²/(8ν)`. A near-identity change of the
van der Pol amplitude, `V = z − u(z, t)` with the explicit generator `u` (`nearId`, the zero-mean
primitive of the quadratic field), removes the quadratic terms exactly; the price is a cubic term
`cubicCorr = −D_z u[quadField]`, whose period average is the resonant frequency shift
`−5α₂²/(12ν³)`. The second-order 2:1 amplitude equation is therefore the cubic amplitude equation
of `theorem/ParametricResonance/SaturatedAmplitude.lean` with the effective coefficient
`β_eff = 3α₃/(8ν) − 5α₂²/(12ν³) = (9ν²α₃ − 10α₂²)/(24ν³)`: a quadratic stiffness always softens.

Scope.
* The oscillator in coefficient form with real `b, k₀, k₁, α₂, α₃`, `ν ≠ 0` (`ν > 0` for the
  averages), continuous time, scalar position `x`, an arbitrary input `u(t)` (any remainder of a
  truncated nonlinearity); the acceleration is `DuffingMathieu.accel b k₀ k₁ α₃ ν t x ẋ − α₂x² + u`.
  Van der Pol coordinates `z = e^{−jνt}(x − jẋ/ν)` and the field `DuffingMathieu.vdpField` of
  `theorem/ParametricResonance/DuffingMathieu.lean`; `phase ν t = e^{jνt}`.
* Exact statements: the transformation identity (`hasDerivAt_transformed`), the exact period
  average of the new field (`fieldAverage_secondField`), the scalings and bounds. In the weakly
  nonlinear scaling (`b`, `ν² − k₀`, `k₁` of order `ε`, amplitude of order `√ε`, `α₂, α₃` fixed)
  the transformed scaled amplitude `W = w − √ε u(w, t)`, `w = z/√ε`, obeys exactly
  `Ẇ = ε secondField(w) − ε√ε D_z u(w)[vdpField(w)] + (input terms)`
  (`hasDerivAt_transformed_scaled`): the neglected terms are of order `ε^{3/2}` on bounded sets
  (`norm_nearIdDeriv_le`), and `W − w` is of order `√ε` (`norm_nearId_le`). With `W` read in
  `secondField(W)` instead of `secondField(w)` the difference is of order `ε^{3/2}` as well
  (`secondField` is Lipschitz on bounded sets).
* Boundary (not formalized here): the averaging step from `Ẇ = ε secondField(W, t) + O(ε^{3/2})`
  to its average `ε ampField … β_eff` — a first-order averaging with an `O(ε^{1+κ})`
  perturbation, `κ = 1/2`, which is `Averaging.kbm_perturbed_order` (error `O(ε^{1/2})` in `W`
  on `[0, L/ε]`) once a cut-off of `secondField` and the a-priori bound of `w` through the implicit
  relation `w = W + √ε u(w, t)` are supplied. The relative error of the amplitude is then
  `O(√ε)`, against `O(1)` for first-order averaging, which drops the `α₂²` shift.
* Generic mathematics, no model family.

Source: second-order averaging / near-identity transformations of weakly nonlinear oscillators
with quadratic and cubic nonlinearity (Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 4 (the
frequency `ω₀ + (3α₃/(8ω₀) − 5α₂²/(12ω₀³)) a²` of the free oscillator) and Ch. 5 (parametric
excitation); Landau–Lifshitz, *Mechanics* §28, eq. (28.13)); Sanders–Verhulst–Murdock,
*Averaging Methods in Nonlinear Dynamical Systems*, Ch. 2.9 (second-order averaging); the van
der Pol field and its first-order average `DuffingMathieu.vdpField_eq`,
`DuffingMathieu.fieldAverage_vdpField`; the cubic amplitude equation `Saturation.ampField`.

Sharpenings.
* The exact second-order coefficient carries `ν` (the half pump frequency) where the classical
  free-oscillator formula carries `ω₀`: `β_eff = 3α₃/(8ν) − 5α₂²/(12ν³)`; at exact resonance
  `ν = ω₀` it is the Landau–Lifshitz coefficient.
* `β_eff > 0` (hardening) iff `10α₂² < 9ν²α₃`; with `α₃ ≤ 0` the oscillator softens for every
  `α₂`, and a hardening cubic stiffness is turned into a softening one by a quadratic stiffness
  with `10α₂² > 9ν²α₃` (`betaEff_pos_iff`).

Results.
* `phase`, `quadField`, `nearId`, `nearIdDeriv`, `cubicCorr`, `secondField` — the rotating phase,
  the quadratic field, the generator `u`, its state derivative, the second-order cubic term and
  the second-order field.
* `hasDerivAt_nearId` — `d/dt u(z(t), t) = quadField + D_z u[ż]`; `nearIdDeriv_add`;
  `nearIdDeriv_quadField` — `D_z u[quadField] = −cubicCorr`.
* `hasDerivAt_transformed` — exact: `V̇ = secondField z + U − D_z u(z)[vdpField z + U]` for
  `V = z − u(z, t)`, `U = −(j/ν) u(t) e^{−jνt}`.
* `continuous_cubicCorr`, `fieldAverage_cubicCorr` — `⟨cubicCorr⟩ = −j (5α₂²/(12ν³)) |z|² z`.
* `fieldAverage_secondField` — the second-order averaged field is
  `ampField (b/2) ((ν² − k₀)/(2ν)) (jk₁/(4ν)) 0 β_eff`.
* `betaEff_eq`, `betaEff_pos_iff` — `β_eff = (9ν²α₃ − 10α₂²)/(24ν³)`; hardening/softening.
* `phase_ne_zero`, `quadField_ofReal_mul`, `nearId_ofReal_mul`, `nearIdDeriv_ofReal_mul`,
  `cubicCorr_ofReal_mul`, `secondField_scaled` — degrees `2, 2, (1, 1), 3`; the weakly nonlinear
  scaling of `secondField`.
* `norm_nearId_le`, `norm_nearIdDeriv_le` — `|u| ≤ (5|α₂|/(6ν²))|z|²`,
  `|D_z u[h]| ≤ (5|α₂|/(3ν²))|z||h|`.
* `hasDerivAt_transformed_scaled` — the exact second-order normal form in the scaled variables,
  with the neglected terms displayed.
-/

noncomputable section
namespace powerlib.ParametricResonance.QuadraticCubic

open Complex Set
open DuffingMathieu (pos vel vdp accel vdpField)
open Saturation (ampField)

/-- The rotating phase `e^{jνt}`. -/
def phase (ν t : ℝ) : ℂ := Complex.exp (((ν * t : ℝ) : ℂ) * I)

/-- The quadratic part `(j/ν) α₂ x² e^{−jνt}` of the standard-form field of
`ẍ + … + α₂ x² = 0`, with `x = Re(z e^{jνt})` read off `z`. -/
def quadField (α₂ ν : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  I / ν * ((α₂ * pos ν z t ^ 2 : ℝ) : ℂ) * (phase ν t)⁻¹

/-- The generator of the near-identity transformation that removes the quadratic terms:
`u(z, t) = (α₂/(4ν²)) (z² e^{jνt} − 2|z|² e^{−jνt} − z̄² e^{−3jνt}/3)`, the zero-mean
`t`-primitive of `quadField`. -/
def nearId (α₂ ν : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  ((α₂ / (4 * ν ^ 2) : ℝ) : ℂ) * (z ^ 2 * phase ν t - 2 * z * (starRingEnd ℂ) z * (phase ν t)⁻¹ -
    (starRingEnd ℂ) z ^ 2 * (phase ν t)⁻¹ ^ 3 / 3)

/-- The (real-linear) derivative of `nearId` in the state, applied to `h`. -/
def nearIdDeriv (α₂ ν : ℝ) (z : ℂ) (t : ℝ) (h : ℂ) : ℂ :=
  ((α₂ / (4 * ν ^ 2) : ℝ) : ℂ) * (2 * z * h * phase ν t -
    2 * (h * (starRingEnd ℂ) z + z * (starRingEnd ℂ) h) * (phase ν t)⁻¹ -
    2 * (starRingEnd ℂ) z * (starRingEnd ℂ) h * (phase ν t)⁻¹ ^ 3 / 3)

/-- The cubic field generated at second order by the quadratic stiffness,
`−D_z u(z, t)[quadField z t] = −j (α₂²/(16ν³)) (4z³e^{2jνt} + (20/3)|z|²z + (4/3) z z̄² e^{−2jνt}
− (4/3) z̄³ e^{−4jνt})`. -/
def cubicCorr (α₂ ν : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  -(I * ((α₂ ^ 2 / (16 * ν ^ 3) : ℝ) : ℂ)) * (4 * z ^ 3 * phase ν t ^ 2 +
    20 / 3 * z ^ 2 * (starRingEnd ℂ) z + 4 / 3 * z * (starRingEnd ℂ) z ^ 2 * (phase ν t)⁻¹ ^ 2 -
    4 / 3 * (starRingEnd ℂ) z ^ 3 * (phase ν t)⁻¹ ^ 4)

/-- The second-order field: the van der Pol field of the cubic oscillator plus `cubicCorr`. -/
def secondField (b k₀ k₁ α₂ α₃ ν : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  vdpField b k₀ k₁ α₃ ν z t + cubicCorr α₂ ν z t

variable {b k₀ k₁ α₂ α₃ ν : ℝ}

@[tmio T, powerlib_foundation] theorem phase_ne_zero (ν t : ℝ) : phase ν t ≠ 0 :=
  Complex.exp_ne_zero _

@[tmio T, powerlib_foundation] private theorem conj_phase (ν t : ℝ) :
    (starRingEnd ℂ) (phase ν t) = (phase ν t)⁻¹ := by
  rw [phase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_neg]
  ring_nf

@[tmio T, powerlib_foundation] private theorem pos_eq (ν : ℝ) (z : ℂ) (t : ℝ) :
    ((pos ν z t : ℝ) : ℂ) = (z * phase ν t + (starRingEnd ℂ) z * (phase ν t)⁻¹) / 2 := by
  rw [pos, Complex.re_eq_add_conj, map_mul, ← phase, conj_phase]

@[tmio T, powerlib_foundation] private theorem hasDerivAt_phase (ν t : ℝ) :
    HasDerivAt (phase ν) (ν * I * phase ν t) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((ν * t : ℝ) : ℂ)) (ν : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul ν).ofReal_comp; simpa using this
  have h2 := (h1.mul_const I).cexp
  show HasDerivAt (fun x : ℝ => Complex.exp (((ν * x : ℝ) : ℂ) * I)) _ t
  convert h2 using 1
  simp only [phase]; ring

/-- **The `t`-derivative of the near-identity generator along a curve.** For a differentiable
`z(t)`: `d/dt u(z(t), t) = quadField z t + D_z u(z, t)[ż]` — the explicit `t`-dependence of `u`
is exactly the quadratic field (`u` is its primitive). -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_nearId (hν : ν ≠ 0) {z : ℝ → ℂ} {z' : ℂ}
    {t : ℝ} (hz : HasDerivAt z z' t) :
    HasDerivAt (fun t => nearId α₂ ν (z t) t)
      (quadField α₂ ν (z t) t + nearIdDeriv α₂ ν (z t) t z') t := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have hE := hasDerivAt_phase ν t
  have hE0 := phase_ne_zero ν t
  have hEi := hE.inv hE0
  have hzc : HasDerivAt (fun t => (starRingEnd ℂ) (z t)) ((starRingEnd ℂ) z') t := by
    simpa using hz.star
  have H := (((hz.pow 2).mul hE).sub (((hz.const_mul 2).mul hzc).mul hEi)).sub
    (((hzc.pow 2).mul (hEi.pow 3)).div_const 3)
  have H2 := H.const_mul ((α₂ / (4 * ν ^ 2) : ℝ) : ℂ)
  convert H2 using 1
  · funext s
    simp only [nearId, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.inv_apply]
  simp only [quadField, nearIdDeriv, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]
  push_cast
  rw [pos_eq]
  field_simp
  ring

@[tmio T, powerlib_foundation] theorem nearIdDeriv_add (α₂ ν : ℝ) (z : ℂ) (t : ℝ) (h₁ h₂ : ℂ) :
    nearIdDeriv α₂ ν z t (h₁ + h₂) = nearIdDeriv α₂ ν z t h₁ + nearIdDeriv α₂ ν z t h₂ := by
  simp only [nearIdDeriv, map_add]; ring

/-- **The cubic term generated by the quadratic stiffness.** The state derivative of the generator
applied to the quadratic field is minus `cubicCorr`: `D_z u(z, t)[quadField z t] =
j(α₂²/(16ν³))(4z³e^{2jνt} + (20/3)|z|²z + (4/3) z z̄² e^{−2jνt} − (4/3) z̄³ e^{−4jνt})`. -/
@[tmio T, powerlib_foundation] theorem nearIdDeriv_quadField (hν : ν ≠ 0) (z : ℂ) (t : ℝ) :
    nearIdDeriv α₂ ν z t (quadField α₂ ν z t) = -cubicCorr α₂ ν z t := by
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have hE0 := phase_ne_zero ν t
  have hq : (starRingEnd ℂ) (quadField α₂ ν z t) =
      -(I / ν) * ((α₂ * pos ν z t ^ 2 : ℝ) : ℂ) * phase ν t := by
    rw [quadField, map_mul, map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_ofReal, map_inv₀, conj_phase, inv_inv]
    ring
  rw [nearIdDeriv, hq, cubicCorr, quadField]
  push_cast
  rw [pos_eq]
  field_simp
  ring_nf

/-- **The exact near-identity transformation.** Let `x` solve the oscillator with quadratic and
cubic stiffness and an input `u`, `ẍ = −(bẋ + (k₀ + k₁ cos 2νt) x + α₃x³) − α₂x² + u(t)`, with
van der Pol amplitude `z = e^{−jνt}(x − jẋ/ν)`. Then `V = z − u(z, t)` (`nearId`) obeys exactly
`V̇ = secondField z t + U(t) − D_z u(z, t)[vdpField z t + U(t)]`, `U(t) = −(j/ν) u(t) e^{−jνt}`:
the quadratic terms are removed, `cubicCorr` appears, and every other term carries a factor
`D_z u = O(|z|)` (or is the input). No approximation is made. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_transformed (hν : ν ≠ 0) {x x' u : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x' (accel b k₀ k₁ α₃ ν t (x t) (x' t) - α₂ * x t ^ 2 + u t) t)
    (t : ℝ) :
    HasDerivAt (fun t => vdp ν t (x t) (x' t) - nearId α₂ ν (vdp ν t (x t) (x' t)) t)
      (secondField b k₀ k₁ α₂ α₃ ν (vdp ν t (x t) (x' t)) t - I / ν * (u t : ℂ) * (phase ν t)⁻¹ -
        nearIdDeriv α₂ ν (vdp ν t (x t) (x' t)) t
          (vdpField b k₀ k₁ α₃ ν (vdp ν t (x t) (x' t)) t - I / ν * (u t : ℂ) * (phase ν t)⁻¹))
      t := by
  have hz : ∀ t, HasDerivAt (fun t => vdp ν t (x t) (x' t))
      (vdpField b k₀ k₁ α₃ ν (vdp ν t (x t) (x' t)) t - I / ν * (u t : ℂ) * (phase ν t)⁻¹ +
        quadField α₂ ν (vdp ν t (x t) (x' t)) t) t := by
    intro t
    have h := DuffingMathieu.hasDerivAt_vdp (b := b) (k₀ := k₀) (k₁ := k₁) (γ := α₃)
      (u := fun t => -α₂ * x t ^ 2 + u t) hν hx (fun t => by
        have := hx' t; convert this using 1; ring) t
    convert h using 1
    rw [quadField, DuffingMathieu.pos_vdp, phase, ← Complex.exp_neg]
    push_cast
    ring
  have hN := hasDerivAt_nearId (α₂ := α₂) hν (hz t)
  convert (hz t).sub hN using 1
  rw [nearIdDeriv_add, nearIdDeriv_quadField hν, secondField]
  ring

/-! ## The exact second-order average -/

@[tmio T, powerlib_foundation] private theorem phase_pow (ν s : ℝ) (n : ℕ) :
    phase ν s ^ n = Complex.exp ((((n * ν) * s : ℝ) : ℂ) * I) := by
  rw [phase, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

@[tmio T, powerlib_foundation] private theorem phase_inv_pow (ν s : ℝ) (n : ℕ) :
    (phase ν s)⁻¹ ^ n = Complex.exp ((((-(n : ℝ) * ν) * s : ℝ) : ℂ) * I) := by
  rw [inv_pow, phase_pow, ← Complex.exp_neg]; congr 1; push_cast; ring

@[tmio T, powerlib_foundation] private theorem integral_exp_harmonic (hν : 0 < ν) (k : ℤ)
    (hk : k ≠ 0) (r : ℝ) (hr : r = k * ν) :
    ∫ s in (0 : ℝ)..(2 * Real.pi / ν), Complex.exp (((r * s : ℝ) : ℂ) * I) = 0 := by
  have hc : (r : ℂ) * I ≠ 0 :=
    mul_ne_zero (by rw [hr]; exact_mod_cast mul_ne_zero (Int.cast_ne_zero.mpr hk) hν.ne') I_ne_zero
  have e : (fun s : ℝ => Complex.exp (((r * s : ℝ) : ℂ) * I)) =
      fun s : ℝ => Complex.exp (((r : ℂ) * I) * s) := by
    funext s; congr 1; push_cast; ring
  rw [e, integral_exp_mul_complex hc]
  have h1 : Complex.exp (((r : ℂ) * I) * ((2 * Real.pi / ν : ℝ) : ℂ)) = 1 := by
    have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
    rw [show ((r : ℂ) * I) * ((2 * Real.pi / ν : ℝ) : ℂ) = k * (2 * Real.pi * I) by
      rw [hr]; push_cast; field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [h1]; simp

@[tmio T, powerlib_foundation] theorem continuous_cubicCorr (α₂ ν : ℝ) (z : ℂ) :
    Continuous (cubicCorr α₂ ν z) := by
  have hp : Continuous (phase ν) := by unfold phase; fun_prop
  have hpi : Continuous fun s => (phase ν s)⁻¹ := hp.inv₀ (phase_ne_zero ν)
  unfold cubicCorr
  fun_prop

/-- **The average of the second-order cubic term.** Over one period `2π/ν` only the resonant term
survives: `⟨cubicCorr⟩(z) = −j (5α₂²/(12ν³)) |z|² z`, a pure frequency shift. -/
@[tmio T, powerlib_foundation] theorem fieldAverage_cubicCorr (hν : 0 < ν) (z : ℂ) :
    Averaging.fieldAverage (cubicCorr α₂ ν) (2 * Real.pi / ν) z =
      -(I * ((5 * α₂ ^ 2 / (12 * ν ^ 3) : ℝ) : ℂ)) * ((‖z‖ ^ 2 : ℝ) : ℂ) * z := by
  set T := 2 * Real.pi / ν with hTdef
  have hT : 0 < T := by positivity
  set κ := -(I * ((α₂ ^ 2 / (16 * ν ^ 3) : ℝ) : ℂ))
  set A := κ * (20 / 3 * z ^ 2 * (starRingEnd ℂ) z)
  set c₂ := κ * (4 * z ^ 3)
  set cm₂ := κ * (4 / 3 * z * (starRingEnd ℂ) z ^ 2)
  set cm₄ := κ * (-(4 / 3) * (starRingEnd ℂ) z ^ 3)
  have e : (fun s => cubicCorr α₂ ν z s) = fun s =>
      A + c₂ * Complex.exp ((((2 * ν) * s : ℝ) : ℂ) * I) +
        cm₂ * Complex.exp ((((-2 * ν) * s : ℝ) : ℂ) * I) +
        cm₄ * Complex.exp ((((-4 * ν) * s : ℝ) : ℂ) * I) := by
    funext s
    have h2 := phase_pow ν s 2
    have h2' := phase_inv_pow ν s 2
    have h4' := phase_inv_pow ν s 4
    push_cast at h2 h2' h4'
    simp only [cubicCorr, h2, h2', h4', A, c₂, cm₂, cm₄, κ]
    push_cast
    ring_nf
  have i2 := integral_exp_harmonic hν 2 (by norm_num) (2 * ν) (by push_cast; ring)
  have i2' := integral_exp_harmonic hν (-2) (by norm_num) (-2 * ν) (by push_cast; ring)
  have i4' := integral_exp_harmonic hν (-4) (by norm_num) (-4 * ν) (by push_cast; ring)
  rw [Averaging.fieldAverage, e, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, i2, i2', i4']
  · simp only [mul_zero, add_zero, sub_zero]
    rw [smul_smul, inv_mul_cancel₀ hT.ne', one_smul]
    have hn : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
      rw [Complex.sq_norm, Complex.mul_conj]
    rw [hn]
    simp only [A, κ]
    push_cast
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- **The second-order averaged amplitude equation.** The period average of `secondField` is the
cubic 2:1 amplitude field `ampField (b/2) ((ν² − k₀)/(2ν)) (jk₁/(4ν)) 0 β_eff` with the effective
frequency-shift coefficient `β_eff = 3α₃/(8ν) − 5α₂²/(12ν³)`. -/
@[tmio T, powerlib_foundation] theorem fieldAverage_secondField (hν : 0 < ν) (z : ℂ) :
    Averaging.fieldAverage (secondField b k₀ k₁ α₂ α₃ ν) (2 * Real.pi / ν) z =
      ampField (b / 2) ((ν ^ 2 - k₀) / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) z := by
  have hv : Continuous fun s => vdpField b k₀ k₁ α₃ ν z s := by
    simp only [vdpField, accel, pos, vel]
    fun_prop
  have hsplit : Averaging.fieldAverage (secondField b k₀ k₁ α₂ α₃ ν) (2 * Real.pi / ν) z =
      Averaging.fieldAverage (vdpField b k₀ k₁ α₃ ν) (2 * Real.pi / ν) z +
        Averaging.fieldAverage (cubicCorr α₂ ν) (2 * Real.pi / ν) z := by
    simp only [Averaging.fieldAverage, secondField]
    rw [intervalIntegral.integral_add (hv.intervalIntegrable _ _)
      ((continuous_cubicCorr α₂ ν z).intervalIntegrable _ _), smul_add]
  rw [hsplit, DuffingMathieu.fieldAverage_vdpField hν, fieldAverage_cubicCorr hν]
  simp only [ampField]
  push_cast
  ring

/-- The effective frequency-shift coefficient as one fraction:
`3α₃/(8ν) − 5α₂²/(12ν³) = (9ν²α₃ − 10α₂²)/(24ν³)`. -/
@[tmio T, powerlib_foundation] theorem betaEff_eq (hν : ν ≠ 0) (α₂ α₃ : ℝ) :
    3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3) =
      (9 * ν ^ 2 * α₃ - 10 * α₂ ^ 2) / (24 * ν ^ 3) := by
  field_simp; ring

/-- **Hardening or softening at second order.** For `ν > 0` the effective coefficient is positive
(hardening) iff `10α₂² < 9ν²α₃` and negative (softening) iff `9ν²α₃ < 10α₂²`: a quadratic
stiffness always softens, by `5α₂²/(12ν³)`. -/
@[tmio T, powerlib_foundation] theorem betaEff_pos_iff (hν : 0 < ν) (α₂ α₃ : ℝ) :
    (0 < 3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3) ↔ 10 * α₂ ^ 2 < 9 * ν ^ 2 * α₃) ∧
      (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3) < 0 ↔ 9 * ν ^ 2 * α₃ < 10 * α₂ ^ 2) := by
  rw [betaEff_eq hν.ne']
  have h : 0 < 24 * ν ^ 3 := by positivity
  constructor
  · rw [div_pos_iff_of_pos_right h]; constructor <;> intro h' <;> linarith
  · rw [div_neg_iff]; constructor
    · rintro (⟨-, h'⟩ | ⟨h', -⟩)
      · linarith
      · linarith
    · intro h'; right; exact ⟨by linarith, h⟩

/-! ## Orders: scaling and bounds of the transformation -/

@[tmio T, powerlib_foundation] private theorem norm_phase (ν t : ℝ) : ‖phase ν t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

@[tmio T, powerlib_foundation] private theorem norm_phase_inv (ν t : ℝ) : ‖(phase ν t)⁻¹‖ = 1 := by
  rw [norm_inv, norm_phase, inv_one]

@[tmio T, powerlib_foundation] private theorem pos_ofReal_mul (ν μ : ℝ) (w : ℂ) (t : ℝ) :
    pos ν ((μ : ℂ) * w) t = μ * pos ν w t := by
  simp only [pos, mul_assoc, Complex.re_ofReal_mul]

/-- The quadratic field is of second degree: `quadField (μw) = μ² quadField w` (`μ` real). -/
@[tmio T, powerlib_foundation] theorem quadField_ofReal_mul (α₂ ν μ : ℝ) (w : ℂ) (t : ℝ) :
    quadField α₂ ν ((μ : ℂ) * w) t = (μ : ℂ) ^ 2 * quadField α₂ ν w t := by
  simp only [quadField, pos_ofReal_mul]; push_cast; ring

/-- The generator is of second degree: `u(μw, t) = μ² u(w, t)` (`μ` real). -/
@[tmio T, powerlib_foundation] theorem nearId_ofReal_mul (α₂ ν μ : ℝ) (w : ℂ) (t : ℝ) :
    nearId α₂ ν ((μ : ℂ) * w) t = (μ : ℂ) ^ 2 * nearId α₂ ν w t := by
  simp only [nearId, map_mul, Complex.conj_ofReal]; ring

/-- Its state derivative is bilinear: `D_z u(μw, t)[λh] = μλ D_z u(w, t)[h]` (`μ, λ` real). -/
@[tmio T, powerlib_foundation] theorem nearIdDeriv_ofReal_mul (α₂ ν μ l : ℝ) (w h : ℂ) (t : ℝ) :
    nearIdDeriv α₂ ν ((μ : ℂ) * w) t ((l : ℂ) * h) = (μ : ℂ) * l * nearIdDeriv α₂ ν w t h := by
  simp only [nearIdDeriv, map_mul, Complex.conj_ofReal]; ring

/-- The second-order cubic term is of third degree: `cubicCorr (μw) = μ³ cubicCorr w`. -/
@[tmio T, powerlib_foundation] theorem cubicCorr_ofReal_mul (α₂ ν μ : ℝ) (w : ℂ) (t : ℝ) :
    cubicCorr α₂ ν ((μ : ℂ) * w) t = (μ : ℂ) ^ 3 * cubicCorr α₂ ν w t := by
  simp only [cubicCorr, map_mul, Complex.conj_ofReal]; ring

/-- **The weakly nonlinear scaling of the second-order field.** Damping, detuning and pump of
order `ε` and an amplitude of order `√ε` (`z = √ε w`) with fixed `α₂, α₃`: the second-order field
is `√ε · ε · secondField b (ν² − d) k₁ α₂ α₃ ν w t` (`DuffingMathieu.vdpField_scaled`,
`cubicCorr_ofReal_mul`). -/
@[tmio T, powerlib_foundation] theorem secondField_scaled {ε : ℝ} (hε : 0 ≤ ε) (b d k₁ α₂ α₃ ν : ℝ)
    (w : ℂ) (t : ℝ) :
    secondField (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₂ α₃ ν ((√ε : ℂ) * w) t =
      (√ε : ℂ) * ((ε : ℂ) * secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν w t) := by
  rw [secondField, secondField, DuffingMathieu.vdpField_scaled hε, cubicCorr_ofReal_mul]
  have h3 : ((√ε : ℝ) : ℂ) ^ 3 = (√ε : ℂ) * (ε : ℂ) := by
    rw [pow_succ, ← Complex.ofReal_pow, Real.sq_sqrt hε]; ring
  rw [h3]; ring

/-- **Size of the transformation:** `|u(z, t)| ≤ (5|α₂|/(6ν²)) |z|²`. -/
@[tmio T, powerlib_foundation] theorem norm_nearId_le (hν : 0 < ν) (z : ℂ) (t : ℝ) :
    ‖nearId α₂ ν z t‖ ≤ 5 * |α₂| / (6 * ν ^ 2) * ‖z‖ ^ 2 := by
  have hc : ‖((α₂ / (4 * ν ^ 2) : ℝ) : ℂ)‖ = |α₂| / (4 * ν ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * ν ^ 2)]
  rw [nearId, norm_mul, hc]
  have h : ‖z ^ 2 * phase ν t - 2 * z * (starRingEnd ℂ) z * (phase ν t)⁻¹ -
      (starRingEnd ℂ) z ^ 2 * (phase ν t)⁻¹ ^ 3 / 3‖ ≤ 10 / 3 * ‖z‖ ^ 2 := by
    have e1 := norm_sub_le (z ^ 2 * phase ν t - 2 * z * (starRingEnd ℂ) z * (phase ν t)⁻¹)
      ((starRingEnd ℂ) z ^ 2 * (phase ν t)⁻¹ ^ 3 / 3)
    have e2 := norm_sub_le (z ^ 2 * phase ν t) (2 * z * (starRingEnd ℂ) z * (phase ν t)⁻¹)
    simp only [norm_mul, norm_div, norm_pow, norm_phase, norm_phase_inv, Complex.norm_conj,
      Complex.norm_ofNat, one_pow, mul_one] at e1 e2
    nlinarith [sq_nonneg ‖z‖]
  calc |α₂| / (4 * ν ^ 2) * ‖z ^ 2 * phase ν t - 2 * z * (starRingEnd ℂ) z * (phase ν t)⁻¹ -
        (starRingEnd ℂ) z ^ 2 * (phase ν t)⁻¹ ^ 3 / 3‖
      ≤ |α₂| / (4 * ν ^ 2) * (10 / 3 * ‖z‖ ^ 2) := by gcongr
    _ = 5 * |α₂| / (6 * ν ^ 2) * ‖z‖ ^ 2 := by field_simp; ring

/-- **Size of its state derivative:** `|D_z u(z, t)[h]| ≤ (5|α₂|/(3ν²)) |z| |h|`. -/
@[tmio T, powerlib_foundation] theorem norm_nearIdDeriv_le (hν : 0 < ν) (z h : ℂ) (t : ℝ) :
    ‖nearIdDeriv α₂ ν z t h‖ ≤ 5 * |α₂| / (3 * ν ^ 2) * (‖z‖ * ‖h‖) := by
  have hc : ‖((α₂ / (4 * ν ^ 2) : ℝ) : ℂ)‖ = |α₂| / (4 * ν ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * ν ^ 2)]
  rw [nearIdDeriv, norm_mul, hc]
  have h1 : ‖2 * z * h * phase ν t - 2 * (h * (starRingEnd ℂ) z + z * (starRingEnd ℂ) h) *
      (phase ν t)⁻¹ - 2 * (starRingEnd ℂ) z * (starRingEnd ℂ) h * (phase ν t)⁻¹ ^ 3 / 3‖ ≤
      20 / 3 * (‖z‖ * ‖h‖) := by
    have e1 := norm_sub_le (2 * z * h * phase ν t - 2 * (h * (starRingEnd ℂ) z +
      z * (starRingEnd ℂ) h) * (phase ν t)⁻¹)
      (2 * (starRingEnd ℂ) z * (starRingEnd ℂ) h * (phase ν t)⁻¹ ^ 3 / 3)
    have e2 := norm_sub_le (2 * z * h * phase ν t)
      (2 * (h * (starRingEnd ℂ) z + z * (starRingEnd ℂ) h) * (phase ν t)⁻¹)
    have e3 := norm_add_le (h * (starRingEnd ℂ) z) (z * (starRingEnd ℂ) h)
    simp only [norm_mul, norm_div, norm_pow, norm_phase, norm_phase_inv, Complex.norm_conj,
      Complex.norm_ofNat, one_pow, mul_one] at e1 e2 e3
    nlinarith [mul_nonneg (norm_nonneg z) (norm_nonneg h)]
  calc |α₂| / (4 * ν ^ 2) * ‖2 * z * h * phase ν t - 2 * (h * (starRingEnd ℂ) z +
        z * (starRingEnd ℂ) h) * (phase ν t)⁻¹ -
        2 * (starRingEnd ℂ) z * (starRingEnd ℂ) h * (phase ν t)⁻¹ ^ 3 / 3‖
      ≤ |α₂| / (4 * ν ^ 2) * (20 / 3 * (‖z‖ * ‖h‖)) := by gcongr
    _ = 5 * |α₂| / (3 * ν ^ 2) * (‖z‖ * ‖h‖) := by field_simp; ring

@[tmio T, powerlib_foundation] private theorem nearIdDeriv_sub (α₂ ν : ℝ) (z : ℂ) (t : ℝ)
    (h₁ h₂ : ℂ) :
    nearIdDeriv α₂ ν z t (h₁ - h₂) = nearIdDeriv α₂ ν z t h₁ - nearIdDeriv α₂ ν z t h₂ := by
  simp only [nearIdDeriv, map_sub]; ring

/-- **The second-order normal form in the weakly nonlinear scaling, exactly.** For
`ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = u(t)` (`ε > 0`, `ν ≠ 0`), with the scaled
amplitude `w = z/√ε` (`x = √ε Re(w e^{jνt})`, `z` the van der Pol amplitude) and the transformed
amplitude `W = w − √ε u(w, t)` (`nearId`):
`Ẇ = ε secondField b (ν² − d) k₁ α₂ α₃ ν w t − ε√ε D_z u(w, t)[vdpField b (ν² − d) k₁ α₃ ν w t]
  + (1/√ε) U(t) − D_z u(w, t)[U(t)]`, `U(t) = −(j/ν) u(t) e^{−jνt}`. The quadratic terms, of
order `√ε` in `ẇ`, are gone; the remaining field is `ε secondField` (whose average carries
`β_eff`, `fieldAverage_secondField`) up to the term of order `ε^{3/2}` (bounded on bounded sets by
`norm_nearIdDeriv_le`) and the input terms; `W − w = −√ε u(w, t)` is of order `√ε`
(`norm_nearId_le`). -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_transformed_scaled (hν : ν ≠ 0) {ε d : ℝ}
    (hε : 0 < ε) {x x' u : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x'
      (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) - α₂ * x t ^ 2 + u t) t)
    (t : ℝ) :
    HasDerivAt (fun t => ((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t) -
        (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)) t)
      (ε • secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)) t -
        (ε * √ε : ℝ) • nearIdDeriv α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)) t
          (vdpField b (ν ^ 2 - d) k₁ α₃ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)) t) +
        (((√ε : ℝ) : ℂ)⁻¹ * (-(I / ν * (u t : ℂ) * (phase ν t)⁻¹)) -
          nearIdDeriv α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)) t
            (-(I / ν * (u t : ℂ) * (phase ν t)⁻¹)))) t := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsε : ((√ε : ℝ) : ℂ) ^ 2 = (ε : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hε.le]
  have hz : ∀ s, vdp ν s (x s) (x' s) =
      ((√ε : ℝ) : ℂ) * (((√ε : ℝ) : ℂ)⁻¹ * vdp ν s (x s) (x' s)) := fun s => by field_simp
  have h := (hasDerivAt_transformed (b := ε * b) (k₀ := ν ^ 2 - ε * d) (k₁ := ε * k₁)
    (α₂ := α₂) (α₃ := α₃) hν hx hx' t).const_mul ((√ε : ℝ) : ℂ)⁻¹
  convert h using 1
  · funext s
    rw [hz s, nearId_ofReal_mul, ← hz s]
    field_simp
  · set w := ((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t) with hw
    set U := -(I / ν * (u t : ℂ) * (phase ν t)⁻¹) with hU
    rw [hz t, ← hw, secondField_scaled hε.le, DuffingMathieu.vdpField_scaled hε.le,
      nearIdDeriv_sub, show (√ε : ℂ) * ((ε : ℂ) * vdpField b (ν ^ 2 - d) k₁ α₃ ν w t) =
        ((√ε * ε : ℝ) : ℂ) * vdpField b (ν ^ 2 - d) k₁ α₃ ν w t by push_cast; ring,
      nearIdDeriv_ofReal_mul, show I / ν * (u t : ℂ) * (phase ν t)⁻¹ = ((1 : ℝ) : ℂ) * -U by
        rw [hU]; push_cast; ring, nearIdDeriv_ofReal_mul]
    simp only [Complex.real_smul]
    push_cast
    have hneg : nearIdDeriv α₂ ν w t (-U) = -nearIdDeriv α₂ ν w t U := by
      simp only [nearIdDeriv, map_neg]; ring
    rw [hneg, ← hsε]
    field_simp
    ring

end powerlib.ParametricResonance.QuadraticCubic
