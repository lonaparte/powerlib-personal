import theorem.ParametricResonance.DuffingMathieu
import theorem.Averaging.KBMPerturbed
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Quadratic and cubic stiffness: the second-order 2:1 amplitude equation

For the parametrically pumped oscillator with quadratic and cubic stiffness,
`ẍ + bẋ + (k₀ + k₁ cos 2νt) x + α₂x² + α₃x³ = u(t)` (physical form `k₀ = ω²`, `k₁ = εω²`), the
quadratic terms have no resonant part at the half pump frequency `ν`: first-order averaging
removes them and is then blind to them, although at amplitude `a` they shift the frequency by
`O(α₂²a²/ν³)`, of the same order as the cubic shift `3α₃a²/(8ν)`. A near-identity change of the
van der Pol amplitude, `V = z − u(z, t)` with the explicit generator `u(z, t)` (`nearId`, the
zero-mean primitive of the quadratic field; not to be confused with the input `u(t)`), removes the quadratic terms exactly; the price is a cubic term
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
  (`norm_nearIdDeriv_le`), and `W − w` is of order `√ε` (`norm_nearId_le`); `secondField` is
  Lipschitz on discs (`norm_secondField_sub_le`), so `secondField(w) − secondField(W)` is of
  order `√ε` as well.
* The averaging step is rigorous (`second_order_averaging`): `Ẇ = ε secondField(W, t) + q(t)`
  with `|q| ≤ ε^{3/2} M_q` while `W` stays in the disc `R + 1` (the a-priori bound
  `|w| < 2(R + 1)` through the implicit relation `w = W + √ε u(w, t)` is a continuity argument
  under the branch condition `4(R + 1)√ε (5|α₂|/(6ν²)) < 1`), and the perturbed averaging theorem
  `Averaging.kbm_perturbed_local` for the cut-off field `cutSecond` gives `|W − W̄| = O(√ε)` on
  `[0, L/ε]`; the oscillation is `√ε Re(W̄ e^{jνt}) + O(ε)`, a relative error `O(√ε)`. The input
  `u` (a remainder of the model) is admitted with `|u| ≤ ε² M_u` while `|w| ≤ 2(R + 1)`. The
  estimate is not uniform in time, and only averaged solutions in the disc `|W̄| ≤ R` are covered.
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
* `theorem/Averaging/KBM.lean` and `theorem/ParametricResonance/DuffingMathieu.lean` average to
  first order only; with a quadratic stiffness the quadratic field is of order `√ε` in the
  scaled amplitude, so first-order averaging controls the error only on the time scale `1/√ε`
  (recorded, not formalized), while the second-order equation with `β_eff` holds on the time
  scale `1/ε` (`second_order_averaging`).
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
* `norm_cubicCorr_sub_le`, `lipSecond`, `norm_secondField_sub_le`, `secondField_zero`,
  `continuous_secondField`, `secondField_periodic`, `cutSecond`, `cutSecond_hyp` — the second-order
  field is `lipSecond`-Lipschitz on discs (`lipConst … r + (5α₂²/(2ν³)) r²`), continuous,
  `2π/ν`-periodic; its cut-off satisfies the hypotheses of `Averaging.kbm_first_order`.
* `remSecond`, `errSecond`, `second_order_averaging` — **rigorous second-order averaging**: on
  `[0, L/ε]`, `|x(t) − √ε Re(W̄(t) e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²)) (2(R + 1))²)` with
  `B = errSecond … = ((2ℓMLT + 2MT) ε + L √ε M_q) e^{ℓL} = O(√ε)`, `W̄` the solution of the
  second-order averaged equation with `β_eff`.
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

/-! ## The second-order field on bounded sets -/

@[tmio T, powerlib_foundation] private theorem norm_mul3_sub_le {a₁ a₂ a₃ b₁ b₂ b₃ : ℂ} {r d : ℝ}
    (ha₂ : ‖a₂‖ ≤ r) (ha₃ : ‖a₃‖ ≤ r) (hb₁ : ‖b₁‖ ≤ r) (hb₂ : ‖b₂‖ ≤ r)
    (h₁ : ‖a₁ - b₁‖ ≤ d) (h₂ : ‖a₂ - b₂‖ ≤ d) (h₃ : ‖a₃ - b₃‖ ≤ d) :
    ‖a₁ * a₂ * a₃ - b₁ * b₂ * b₃‖ ≤ 3 * r ^ 2 * d := by
  have hr : 0 ≤ r := (norm_nonneg _).trans ha₂
  have hd : 0 ≤ d := (norm_nonneg _).trans h₁
  have e : a₁ * a₂ * a₃ - b₁ * b₂ * b₃ =
      (a₁ - b₁) * a₂ * a₃ + b₁ * (a₂ - b₂) * a₃ + b₁ * b₂ * (a₃ - b₃) := by ring
  rw [e]
  have t1 : ‖(a₁ - b₁) * a₂ * a₃‖ ≤ d * r * r := by
    rw [norm_mul, norm_mul]; gcongr
  have t2 : ‖b₁ * (a₂ - b₂) * a₃‖ ≤ r * d * r := by
    rw [norm_mul, norm_mul]; gcongr
  have t3 : ‖b₁ * b₂ * (a₃ - b₃)‖ ≤ r * r * d := by
    rw [norm_mul, norm_mul]; gcongr
  calc _ ≤ ‖(a₁ - b₁) * a₂ * a₃‖ + ‖b₁ * (a₂ - b₂) * a₃‖ + ‖b₁ * b₂ * (a₃ - b₃)‖ :=
        norm_add₃_le
    _ ≤ d * r * r + r * d * r + r * r * d := by linarith
    _ = 3 * r ^ 2 * d := by ring

/-- **Lipschitz bound of the second-order cubic term on a disc:** for `|z|, |y| ≤ r`,
`|cubicCorr z t − cubicCorr y t| ≤ (5α₂²/(2ν³)) r² |z − y|`. -/
@[tmio T, powerlib_foundation] theorem norm_cubicCorr_sub_le (hν : 0 < ν) {r : ℝ} {z y : ℂ}
    (hz : ‖z‖ ≤ r) (hy : ‖y‖ ≤ r) (t : ℝ) :
    ‖cubicCorr α₂ ν z t - cubicCorr α₂ ν y t‖ ≤ 5 * α₂ ^ 2 / (2 * ν ^ 3) * r ^ 2 * ‖z - y‖ := by
  set d := ‖z - y‖
  have hzc : ‖(starRingEnd ℂ) z‖ ≤ r := by rwa [Complex.norm_conj]
  have hyc : ‖(starRingEnd ℂ) y‖ ≤ r := by rwa [Complex.norm_conj]
  have hd : ‖z - y‖ ≤ d := le_rfl
  have hdc : ‖(starRingEnd ℂ) z - (starRingEnd ℂ) y‖ ≤ d := by
    rw [← map_sub, Complex.norm_conj]
  have m1 := norm_mul3_sub_le hz hz hy hy hd hd hd
  have m2 := norm_mul3_sub_le hz hzc hy hy hd hd hdc
  have m3 := norm_mul3_sub_le hzc hzc hy hyc hd hdc hdc
  have m4 := norm_mul3_sub_le hzc hzc hyc hyc hdc hdc hdc
  set k := α₂ ^ 2 / (16 * ν ^ 3) with hk
  have hk0 : 0 ≤ k := by positivity
  have e : cubicCorr α₂ ν z t - cubicCorr α₂ ν y t = -(I * (k : ℂ)) *
      (4 * (z * z * z - y * y * y) * phase ν t ^ 2 +
        20 / 3 * (z * z * (starRingEnd ℂ) z - y * y * (starRingEnd ℂ) y) +
        4 / 3 * (z * (starRingEnd ℂ) z * (starRingEnd ℂ) z - y * (starRingEnd ℂ) y *
          (starRingEnd ℂ) y) * (phase ν t)⁻¹ ^ 2 -
        4 / 3 * ((starRingEnd ℂ) z * (starRingEnd ℂ) z * (starRingEnd ℂ) z -
          (starRingEnd ℂ) y * (starRingEnd ℂ) y * (starRingEnd ℂ) y) * (phase ν t)⁻¹ ^ 4) := by
    simp only [cubicCorr, hk]; ring
  rw [e, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hk0]
  have hpn : ‖phase ν t‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hp2 : ‖phase ν t ^ 2‖ = 1 := by rw [norm_pow, hpn, one_pow]
  have hp2' : ‖(phase ν t)⁻¹ ^ 2‖ = 1 := by rw [norm_pow, norm_inv, hpn, inv_one, one_pow]
  have hp4' : ‖(phase ν t)⁻¹ ^ 4‖ = 1 := by rw [norm_pow, norm_inv, hpn, inv_one, one_pow]
  set A := z * z * z - y * y * y
  set B := z * z * (starRingEnd ℂ) z - y * y * (starRingEnd ℂ) y
  set C := z * (starRingEnd ℂ) z * (starRingEnd ℂ) z - y * (starRingEnd ℂ) y * (starRingEnd ℂ) y
  set D := (starRingEnd ℂ) z * (starRingEnd ℂ) z * (starRingEnd ℂ) z -
    (starRingEnd ℂ) y * (starRingEnd ℂ) y * (starRingEnd ℂ) y
  have hsum : ‖4 * A * phase ν t ^ 2 + 20 / 3 * B + 4 / 3 * C * (phase ν t)⁻¹ ^ 2 -
      4 / 3 * D * (phase ν t)⁻¹ ^ 4‖ ≤ 40 / 3 * (3 * r ^ 2 * d) := by
    have n1 : ‖4 * A * phase ν t ^ 2‖ ≤ 4 * (3 * r ^ 2 * d) := by
      rw [norm_mul, norm_mul, hp2, mul_one, Complex.norm_ofNat]; gcongr
    have n2 : ‖(20 / 3 : ℂ) * B‖ ≤ 20 / 3 * (3 * r ^ 2 * d) := by
      rw [norm_mul, show ‖(20 / 3 : ℂ)‖ = 20 / 3 by
        rw [show (20 / 3 : ℂ) = ((20 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by norm_num)]]
      gcongr
    have n3 : ‖(4 / 3 : ℂ) * C * (phase ν t)⁻¹ ^ 2‖ ≤ 4 / 3 * (3 * r ^ 2 * d) := by
      rw [norm_mul, norm_mul, hp2', mul_one, show ‖(4 / 3 : ℂ)‖ = 4 / 3 by
        rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by norm_num)]]
      gcongr
    have n4 : ‖(4 / 3 : ℂ) * D * (phase ν t)⁻¹ ^ 4‖ ≤ 4 / 3 * (3 * r ^ 2 * d) := by
      rw [norm_mul, norm_mul, hp4', mul_one, show ‖(4 / 3 : ℂ)‖ = 4 / 3 by
        rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by norm_num)]]
      gcongr
    calc _ ≤ ‖4 * A * phase ν t ^ 2 + 20 / 3 * B + 4 / 3 * C * (phase ν t)⁻¹ ^ 2‖ +
          ‖(4 / 3 : ℂ) * D * (phase ν t)⁻¹ ^ 4‖ := norm_sub_le _ _
      _ ≤ ‖4 * A * phase ν t ^ 2‖ + ‖(20 / 3 : ℂ) * B‖ + ‖(4 / 3 : ℂ) * C * (phase ν t)⁻¹ ^ 2‖ +
          ‖(4 / 3 : ℂ) * D * (phase ν t)⁻¹ ^ 4‖ := by
          gcongr; exact norm_add₃_le
      _ ≤ _ := by linarith
  calc k * ‖4 * A * phase ν t ^ 2 + 20 / 3 * B + 4 / 3 * C * (phase ν t)⁻¹ ^ 2 -
        4 / 3 * D * (phase ν t)⁻¹ ^ 4‖ ≤ k * (40 / 3 * (3 * r ^ 2 * d)) := by gcongr
    _ = 5 * α₂ ^ 2 / (2 * ν ^ 3) * r ^ 2 * d := by rw [hk]; field_simp; ring

/-- The Lipschitz constant `lipConst … r + (5α₂²/(2ν³)) r²` of `secondField` on the disc of
radius `r`. -/
def lipSecond (b k₀ k₁ α₂ α₃ ν r : ℝ) : ℝ :=
  DuffingMathieu.lipConst b k₀ k₁ α₃ ν r + 5 * α₂ ^ 2 / (2 * ν ^ 3) * r ^ 2

/-- The second-order field read through the clamp onto the square of half-side `ρ`. -/
def cutSecond (b k₀ k₁ α₂ α₃ ν ρ : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  secondField b k₀ k₁ α₂ α₃ ν (DuffingMathieu.clampC ρ w) t

/-- **Lipschitz bound of the second-order field on a disc.** -/
@[tmio T, powerlib_foundation] theorem norm_secondField_sub_le (hν : 0 < ν) {r : ℝ} {z y : ℂ}
    (hz : ‖z‖ ≤ r) (hy : ‖y‖ ≤ r) (t : ℝ) :
    ‖secondField b k₀ k₁ α₂ α₃ ν z t - secondField b k₀ k₁ α₂ α₃ ν y t‖ ≤
      lipSecond b k₀ k₁ α₂ α₃ ν r * ‖z - y‖ := by
  have h1 := DuffingMathieu.norm_vdpField_sub_le (b := b) (k₀ := k₀) (k₁ := k₁) (γ := α₃) hν hz
    hy t
  have h2 := norm_cubicCorr_sub_le (α₂ := α₂) hν hz hy t
  have e : secondField b k₀ k₁ α₂ α₃ ν z t - secondField b k₀ k₁ α₂ α₃ ν y t =
      (vdpField b k₀ k₁ α₃ ν z t - vdpField b k₀ k₁ α₃ ν y t) +
        (cubicCorr α₂ ν z t - cubicCorr α₂ ν y t) := by simp only [secondField]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  simp only [lipSecond, DuffingMathieu.lipConst]
  linarith

@[tmio T, powerlib_foundation] theorem secondField_zero (t : ℝ) :
    secondField b k₀ k₁ α₂ α₃ ν 0 t = 0 := by
  simp [secondField, DuffingMathieu.vdpField_zero, cubicCorr]

@[tmio T, powerlib_foundation] theorem continuous_secondField :
    Continuous fun q : ℂ × ℝ => secondField b k₀ k₁ α₂ α₃ ν q.1 q.2 := by
  have hp : Continuous fun q : ℂ × ℝ => phase ν q.2 := by unfold phase; fun_prop
  have hpi : Continuous fun q : ℂ × ℝ => (phase ν q.2)⁻¹ := hp.inv₀ fun q => phase_ne_zero ν q.2
  have hv := DuffingMathieu.continuous_vdpField (b := b) (k₀ := k₀) (k₁ := k₁) (γ := α₃) (ν := ν)
  unfold secondField cubicCorr
  fun_prop

@[tmio T, powerlib_foundation] theorem secondField_periodic (hν : 0 < ν) (z : ℂ) (t : ℝ) :
    secondField b k₀ k₁ α₂ α₃ ν z (t + 2 * Real.pi / ν) = secondField b k₀ k₁ α₂ α₃ ν z t := by
  have hp : phase ν (t + 2 * Real.pi / ν) = phase ν t := by
    have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
    rw [phase, phase, show ((ν * (t + 2 * Real.pi / ν) : ℝ) : ℂ) * I =
      ((ν * t : ℝ) : ℂ) * I + 2 * Real.pi * I by push_cast; field_simp, Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]
  simp only [secondField, cubicCorr, hp, DuffingMathieu.vdpField_periodic hν]

/-- **The cut-off second-order field satisfies the hypotheses of KBM**
(`Averaging.kbm_first_order`): period `2π/ν`, Lipschitz constant `ℓ = lipSecond … (2ρ)`, bound
`2ρℓ`. -/
@[tmio T, powerlib_foundation] theorem cutSecond_hyp (hν : 0 < ν) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 < 2 * Real.pi / ν ∧ 0 ≤ lipSecond b k₀ k₁ α₂ α₃ ν (2 * ρ) ∧
      Continuous (Function.uncurry (cutSecond b k₀ k₁ α₂ α₃ ν ρ)) ∧
      (∀ x t, cutSecond b k₀ k₁ α₂ α₃ ν ρ x (t + 2 * Real.pi / ν) =
        cutSecond b k₀ k₁ α₂ α₃ ν ρ x t) ∧
      (∀ x y t, ‖cutSecond b k₀ k₁ α₂ α₃ ν ρ x t - cutSecond b k₀ k₁ α₂ α₃ ν ρ y t‖ ≤
        lipSecond b k₀ k₁ α₂ α₃ ν (2 * ρ) * ‖x - y‖) ∧
      ∀ x t, ‖cutSecond b k₀ k₁ α₂ α₃ ν ρ x t‖ ≤ lipSecond b k₀ k₁ α₂ α₃ ν (2 * ρ) * (2 * ρ) := by
  have hℓ : 0 ≤ lipSecond b k₀ k₁ α₂ α₃ ν (2 * ρ) := by
    unfold lipSecond DuffingMathieu.lipConst; have := hν.le; positivity
  have hlip : ∀ x y t, ‖cutSecond b k₀ k₁ α₂ α₃ ν ρ x t - cutSecond b k₀ k₁ α₂ α₃ ν ρ y t‖ ≤
      lipSecond b k₀ k₁ α₂ α₃ ν (2 * ρ) * ‖x - y‖ := fun x y t =>
    (norm_secondField_sub_le hν (DuffingMathieu.norm_clampC_le hρ x)
      (DuffingMathieu.norm_clampC_le hρ y) t).trans
      (mul_le_mul_of_nonneg_left (DuffingMathieu.norm_clampC_sub_le ρ x y) hℓ)
  have hcont : Continuous (Function.uncurry (cutSecond b k₀ k₁ α₂ α₃ ν ρ)) := by
    have e : Function.uncurry (cutSecond b k₀ k₁ α₂ α₃ ν ρ) =
        (fun q : ℂ × ℝ => secondField b k₀ k₁ α₂ α₃ ν q.1 q.2) ∘
          fun q : ℂ × ℝ => (DuffingMathieu.clampC ρ q.1, q.2) := by
      funext q; simp only [Function.uncurry, cutSecond, Function.comp_apply]
    rw [e]
    exact continuous_secondField.comp
      (((DuffingMathieu.continuous_clampC ρ).comp continuous_fst).prodMk continuous_snd)
  refine ⟨by positivity, hℓ, hcont, fun x t => secondField_periodic hν _ t, hlip,
    fun x t => ?_⟩
  have h := norm_secondField_sub_le (b := b) (k₀ := k₀) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hν
    (DuffingMathieu.norm_clampC_le hρ x) (by rw [norm_zero]; positivity) t
  rw [secondField_zero, sub_zero, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (DuffingMathieu.norm_clampC_le hρ x) hℓ)

/-! ## Rigorous second-order averaging -/

/-- The bound `M_q` of the neglected terms of the transformed scaled amplitude, `‖q‖ ≤ ε^{3/2} M_q`,
on the disc of radius `r = 2(R + 1)` (input `|u| ≤ ε² M_u`). -/
def remSecond (b d k₁ α₂ α₃ ν R Mu : ℝ) : ℝ :=
  lipSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν (2 * (R + 1)) * (5 * |α₂| / (6 * ν ^ 2)) *
      (2 * (R + 1)) ^ 2 +
    5 * |α₂| / (3 * ν ^ 2) * DuffingMathieu.lipConst b (ν ^ 2 - d) k₁ α₃ ν (2 * (R + 1)) *
      (2 * (R + 1)) ^ 2 +
    Mu / ν + 5 * |α₂| / (3 * ν ^ 2) * (2 * (R + 1)) * (Mu / ν)

/-- The error bound of the transformed amplitude: KBM's bound
`((2ℓMLT + 2MT) ε + L √ε M_q) e^{ℓL}` for the cut-off second-order field
(`ℓ = lipSecond … (2(R + 1))`, `M = 2(R + 1)ℓ`, `T = 2π/ν`). -/
def errSecond (b d k₁ α₂ α₃ ν R L ε Mu : ℝ) : ℝ :=
  ((2 * lipSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν (2 * (R + 1)) *
        (lipSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν (2 * (R + 1)) * (2 * (R + 1))) * L *
          (2 * Real.pi / ν) +
      2 * (lipSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν (2 * (R + 1)) * (2 * (R + 1))) *
        (2 * Real.pi / ν)) * ε +
    L * (√ε * remSecond b d k₁ α₂ α₃ ν R Mu)) *
  Real.exp (lipSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν (2 * (R + 1)) * L)

@[tmio T, powerlib_foundation] private theorem lt_of_forbidden {φ : ℝ → ℝ} {t a c : ℝ}
    (hφ : ContinuousOn φ (Icc 0 t)) (ha : 0 < a) (hac : 4 * a * c < 1) (h0 : φ 0 < 2 * a)
    (hle : ∀ s ∈ Icc 0 t, φ s ≤ a + c * φ s ^ 2) : ∀ s ∈ Icc 0 t, φ s < 2 * a := by
  intro s hs
  by_contra hcon
  push Not at hcon
  have hsub : Icc 0 s ⊆ Icc 0 t := Icc_subset_Icc le_rfl hs.2
  obtain ⟨s', hs', hφs'⟩ := intermediate_value_Icc hs.1 (hφ.mono hsub) ⟨h0.le, hcon⟩
  have h := hle s' (hsub hs')
  rw [hφs'] at h
  nlinarith

/-- **Rigorous second-order averaging of the pumped oscillator with quadratic and cubic
stiffness.** For `ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = u(t)` (`ν > 0`,
`0 < ε ≤ 1`), with scaled amplitude `w = z/√ε` and transformed amplitude `W = w − √ε u(w, t)`
(`nearId`), let `W̄` solve the second-order averaged equation
`W̄̇ = ε ampField (b/2) (d/(2ν)) (jk₁/(4ν)) 0 β_eff W̄`, `β_eff = 3α₃/(8ν) − 5α₂²/(12ν³)`, on
`[0, L/ε]` in the disc `|W̄| ≤ R`, from `W̄(0) = W(0)`. Assume `|w(0)| < 2(R + 1)`, the input bound
`|u(t)| ≤ ε² M_u` while `|w(t)| ≤ 2(R + 1)`, the branch condition
`4(R + 1)√ε (5|α₂|/(6ν²)) < 1` and `B = errSecond … < 1`. Then on `[0, L/ε]`
`|x(t) − √ε Re(W̄(t) e^{jνt})| ≤ √ε (B + √ε (5|α₂|/(6ν²)) (2(R + 1))²)`: with
`B = O(√ε)`, the second-order amplitude equation gives the oscillation of amplitude `O(√ε)` up to
`O(ε)` on the time scale `1/ε` (`hasDerivAt_transformed_scaled`, `cutSecond_hyp`,
`Averaging.kbm_perturbed_local` with an `O(ε^{3/2})` perturbation). -/
@[tmio T, powerlib_foundation] theorem second_order_averaging (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) {x x' u : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (x' t) t)
    (hx' : ∀ t, HasDerivAt x'
      (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) - α₂ * x t ^ 2 + u t) t)
    (hu : ∀ t ∈ Icc 0 (L / ε), ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (x t) (x' t)‖ ≤ 2 * (R + 1) →
      |u t| ≤ ε ^ 2 * Mu)
    {Wbar : ℝ → ℂ}
    (hWbar : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt Wbar
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (Wbar t)) (Icc 0 (L / ε)) t)
    (hbound : ∀ t ∈ Icc 0 (L / ε), ‖Wbar t‖ ≤ R)
    (h0 : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0)) 0 = Wbar 0)
    (hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (x 0) (x' 0)‖ < 2 * (R + 1))
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d k₁ α₂ α₃ ν R L ε Mu < 1) :
    ∀ t ∈ Icc 0 (L / ε), |x t - √ε * (Wbar t * phase ν t).re| ≤
      √ε * (errSecond b d k₁ α₂ α₃ ν R L ε Mu +
        √ε * (5 * |α₂| / (6 * ν ^ 2)) * (2 * (R + 1)) ^ 2) := by
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs0' : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsε : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
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
    have h := hasDerivAt_transformed_scaled (b := b) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hν.ne' hε
      hx hx' t
    convert h using 1
    simp only [hqdef, hUdef]
    abel
  -- the transformation is small: `‖w − W‖ ≤ √ε c₁ ‖w‖²`
  have hwW : ∀ t, ‖w t - W t‖ ≤ √ε * c₁ * ‖w t‖ ^ 2 := by
    intro t
    rw [hWdef]
    simp only [sub_sub_cancel, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_nearId_le hν _ t) hs0.le
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hx'c : Continuous x' := continuous_iff_continuousAt.2 fun t => (hx' t).continuousAt
  have hwc : Continuous w := by
    simp only [hwdef, vdp]
    fun_prop
  -- while `W` stays in the disc of radius `R + 1`, `w` stays in that of radius `2(R + 1)`
  have hbr : ∀ t, 0 ≤ t → (∀ s ∈ Icc 0 t, ‖W s‖ ≤ R + 1) → ∀ s ∈ Icc 0 t, ‖w s‖ < 2 * (R + 1) := by
    intro t _ hhist
    refine lt_of_forbidden (φ := fun s => ‖w s‖) (c := √ε * c₁) hwc.norm.continuousOn hR1
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
      have h := norm_secondField_sub_le (b := b) (k₀ := ν ^ 2 - d) (k₁ := k₁) (α₂ := α₂)
        (α₃ := α₃) hν hw hW' t
      have h2 : ‖w t - W t‖ ≤ √ε * c₁ * r ^ 2 :=
        (hwW t).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw 2)
          (by positivity))
      calc ε * ‖secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (w t) t -
            secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν (W t) t‖ ≤ ε * (ℓ₂ * (√ε * c₁ * r ^ 2)) := by
            gcongr; exact h.trans (mul_le_mul_of_nonneg_left h2 hℓ₂)
        _ = ε * √ε * (ℓ₂ * c₁ * r ^ 2) := by ring
    have t2 : ‖(ε * √ε : ℝ) • nearIdDeriv α₂ ν (w t) t (vdpField b (ν ^ 2 - d) k₁ α₃ ν (w t) t)‖ ≤
        ε * √ε * (c₂ * ℓ₁ * r ^ 2) := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have h := norm_nearIdDeriv_le (α₂ := α₂) hν (w t) (vdpField b (ν ^ 2 - d) k₁ α₃ ν (w t) t) t
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
      have h := norm_nearIdDeriv_le (α₂ := α₂) hν (w t) (U t) t
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
  -- KBM with the perturbation for the transformed amplitude
  have hg := cutSecond_hyp (b := b) (k₀ := ν ^ 2 - d) (k₁ := k₁) (α₂ := α₂) (α₃ := α₃) hν
    hR1.le
  have hfg : ∀ y ∈ {y : ℂ | ‖y‖ ≤ R + 1}, ∀ t,
      secondField b (ν ^ 2 - d) k₁ α₂ α₃ ν y t =
        cutSecond b (ν ^ 2 - d) k₁ α₂ α₃ ν (R + 1) y t := by
    intro y hy t
    simp only [cutSecond, DuffingMathieu.clampC_of_norm_le hy]
  have hrem : 0 ≤ remSecond b d k₁ α₂ α₃ ν R Mu := by
    simp only [remSecond, lipSecond, DuffingMathieu.lipConst]; have := hν.le; positivity
  have hk := Averaging.kbm_perturbed_local hg hfg hε hL (mul_nonneg hs0.le hrem) (ρ := 1)
    (x := W) (xbar := Wbar) (q := q) (fun t _ => (hW t).hasDerivWithinAt)
    (fun t ht hhist => by
      have hw := hbr t ht.1 hhist t ⟨ht.1, le_rfl⟩
      exact hqb t hw.le ((hhist t ⟨ht.1, le_rfl⟩).trans (by linarith))
        (hu t ht hw.le))
    (fun t ht => by
      rw [fieldAverage_secondField hν, show (ν ^ 2 - (ν ^ 2 - d)) / (2 * ν) = d / (2 * ν) by ring]
      exact hWbar t ht)
    (fun t ht y hy => by
      show ‖y‖ ≤ R + 1
      have := norm_le_norm_add_norm_sub' y (Wbar t)
      linarith [hbound t ht])
    (by simp only [hWdef, hwdef]; exact h0) (by simpa [errSecond] using hsmall)
  -- back to the oscillation
  intro t ht
  have hB : ∀ s ∈ Icc 0 (L / ε), ‖W s - Wbar s‖ ≤ errSecond b d k₁ α₂ α₃ ν R L ε Mu := by
    intro s hs; simpa [errSecond] using hk s hs
  have hhist : ∀ s ∈ Icc 0 t, ‖W s‖ ≤ R + 1 := by
    intro s hs
    have hs' : s ∈ Icc 0 (L / ε) := ⟨hs.1, hs.2.trans ht.2⟩
    have := norm_le_norm_add_norm_sub' (W s) (Wbar s)
    have := hB s hs'
    have := hbound s hs'
    linarith
  have hwt := hbr t ht.1 hhist t ⟨ht.1, le_rfl⟩
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
  rw [norm_mul, norm_mul, show ‖phase ν t‖ = 1 from Complex.norm_exp_ofReal_mul_I _, mul_one,
    Complex.norm_real, Real.norm_of_nonneg hs0.le]
  exact mul_le_mul_of_nonneg_left hwWb hs0.le

end powerlib.ParametricResonance.QuadraticCubic
