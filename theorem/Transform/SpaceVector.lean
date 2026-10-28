import dependencies.Mathlib
import theorem.Attributes
import theorem.Transform.ParkABC

/-! # Space vectors for three-phase machines

Foundation layer for the `theorem/Drives/` family. Nothing here is a statement about a
particular machine or controller; the results are algebraic identities about complex space
vectors that the machine modules reuse.

Scope.
Conventions (shared by every `Drives` module unless a module states otherwise):
* A three-phase quantity `(x_a, x_b, x_c)` has the **amplitude-invariant** space vector
  `clarke x_a x_b x_c = (2/3) (x_a + a x_b + a² x_c)`, `a = e^{j2π/3}`. A balanced sinusoid of
  peak `X` maps to a vector of modulus `X`; three-phase power is `(3/2) Re(v · conj i)`.
* A frame rotating by the electrical angle `θ` sees `x_dq = e^{-jθ} x_αβ`; `x = x_d + j x_q`.
* Motor (IN-positive) convention: `v = r i + dψ/dt + jωψ` in a frame rotating at `ω`
  (work-sync `conventions §D` default). The synchronous-machine module is the only exception.
* `np` is the number of **pole pairs** (mechanical speed `Ω_m = ω / np`).

Source: work-sync `theory/T-direct-torque-control.md` §1.2–§1.3 (torque expression, inverter
voltage vectors), `theory/T-field-oriented-control.md` §1.1 / §1.9 (complex-vector form).

Results.
* `a`, `1 + a + a² = 0`, the components of `clarke`, and its common-mode invariance.
* The eight two-level inverter switching states give the six active vectors
  `(2/3) V_dc e^{j(k-1)π/3}` and two zero vectors (DTC / FCS-MPC voltage set).
* Rotation invariance of `Im(conj ψ · i)`.
* Power balance `Re(v conj i) = r|i|² + Re(ψ̇ conj i) + ω Im(conj ψ i)` and the torque
  coefficient: `T_e = (3/2) np Im(conj ψ · i)` is the unique coefficient for which
  `T_e · Ω_m` equals the speed-voltage power.

Correction (T-direct-torque-control.md §1.2): the note defines `p` as the number of pole
pairs but writes `T_e = (3/2)(p/2) Im{i ψ*}`. With pole pairs the coefficient is `(3/2) p`;
`(3/2)(p/2)` is correct only if `p` counts poles. See `torque_coefficient_unique`.
-/

noncomputable section
namespace powerlib.Transform.SpaceVector

open Complex ComplexConjugate

/-- `a = e^{j2π/3} = -1/2 + j√3/2`. -/
def a : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

@[tmio T, powerlib_foundation] theorem a_sq : a ^ 2 = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
  apply Complex.ext <;> simp [a, pow_two] <;> nlinarith [sqrt3_sq]

@[tmio T, powerlib_foundation] theorem one_add_a_add_a_sq : 1 + a + a ^ 2 = 0 := by
  rw [a_sq]
  apply Complex.ext <;> simp [a]
  ring

/-- Amplitude-invariant Clarke transform `(2/3)(x_a + a x_b + a² x_c)`. -/
def clarke (xa xb xc : ℝ) : ℂ := (2 / 3 : ℂ) * ((xa : ℂ) + a * xb + a ^ 2 * xc)

@[tmio T, simp, powerlib_foundation] theorem clarke_re (xa xb xc : ℝ) :
    (clarke xa xb xc).re = (2 / 3) * (xa - xb / 2 - xc / 2) := by
  rw [clarke, a_sq]
  simp [a]
  ring

@[tmio T, simp, powerlib_foundation] theorem clarke_im (xa xb xc : ℝ) :
    (clarke xa xb xc).im = Real.sqrt 3 / 3 * (xb - xc) := by
  rw [clarke, a_sq]
  simp [a]
  ring

/-- Common-mode invariance: adding the same voltage to all three legs leaves the space
vector unchanged. -/
@[tmio T, powerlib_foundation] theorem clarke_add_const (xa xb xc c : ℝ) :
    clarke (xa + c) (xb + c) (xc + c) = clarke xa xb xc := by
  apply Complex.ext <;> simp
  ring

/-- Amplitude invariance: a balanced positive-sequence set of peak `X` and angle `θ` has the
space vector `X e^{jθ}`. -/
@[tmio T, powerlib_foundation] theorem clarke_balanced (X θ : ℝ) :
    clarke (X * Real.cos θ) (X * Real.cos (θ - 2 * Real.pi / 3))
      (X * Real.cos (θ + 2 * Real.pi / 3)) =
      ⟨X * Real.cos θ, X * Real.sin θ⟩ := by
  have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; ring
  have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]
  apply Complex.ext
  · simp only [clarke_re, Real.cos_sub, Real.cos_add, hc, hs]
    ring
  · simp only [clarke_im, Real.cos_sub, Real.cos_add, hc, hs]
    have h3 := sqrt3_sq
    linear_combination (X * Real.sin θ / 3) * h3

/-! ## Two-level inverter voltage vectors -/

/-- Space vector of a two-level inverter switching state; each leg is at `V_dc` (switch
`true`) or `0` (switch `false`) with respect to the negative DC rail. -/
def inverterVector (Vdc : ℝ) (sa sb sc : Bool) : ℂ :=
  clarke (if sa then Vdc else 0) (if sb then Vdc else 0) (if sc then Vdc else 0)

/-- Active vector `v_k = (2/3) V_dc e^{j(k-1)π/3}`, `k = 1, …, 6`, written with exact
trigonometric values. -/
def activeVector (Vdc : ℝ) (k : ℕ) : ℂ :=
  ⟨2 / 3 * Vdc * Real.cos ((k - 1 : ℝ) * Real.pi / 3),
    2 / 3 * Vdc * Real.sin ((k - 1 : ℝ) * Real.pi / 3)⟩

@[tmio M, powerlib_foundation] theorem inverterVector_zero (Vdc : ℝ) :
    inverterVector Vdc false false false = 0 ∧ inverterVector Vdc true true true = 0 := by
  refine ⟨?_, ?_⟩
  · apply Complex.ext <;> simp [inverterVector]
  · apply Complex.ext <;> simp [inverterVector]
    ring

/-- The six active switching states produce the regular hexagon of vectors
`(2/3) V_dc e^{j(k-1)π/3}` (Takahashi–Noguchi numbering). -/
@[tmio M, powerlib_foundation] theorem inverterVector_active (Vdc : ℝ) :
    inverterVector Vdc true false false = activeVector Vdc 1 ∧
    inverterVector Vdc true true false = activeVector Vdc 2 ∧
    inverterVector Vdc false true false = activeVector Vdc 3 ∧
    inverterVector Vdc false true true = activeVector Vdc 4 ∧
    inverterVector Vdc false false true = activeVector Vdc 5 ∧
    inverterVector Vdc true false true = activeVector Vdc 6 := by
  have c2 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; ring
  have s2 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]
  have c4 : Real.cos (4 * Real.pi / 3) = -1 / 2 := by
    have : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
    rw [this, Real.cos_add_pi, Real.cos_pi_div_three]; ring
  have s4 : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    have : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
    rw [this, Real.sin_add_pi, Real.sin_pi_div_three]
  have c5 : Real.cos (5 * Real.pi / 3) = 1 / 2 := by
    have : 5 * Real.pi / 3 = -(Real.pi / 3) + 2 * Real.pi := by ring
    rw [this, Real.cos_add_two_pi, Real.cos_neg, Real.cos_pi_div_three]
  have s5 : Real.sin (5 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    have : 5 * Real.pi / 3 = -(Real.pi / 3) + 2 * Real.pi := by ring
    rw [this, Real.sin_add_two_pi, Real.sin_neg, Real.sin_pi_div_three]
  have h3 := sqrt3_sq
  have e1 : ((1 : ℕ) - 1 : ℝ) * Real.pi / 3 = 0 := by norm_num
  have e2 : ((2 : ℕ) - 1 : ℝ) * Real.pi / 3 = Real.pi / 3 := by norm_num
  have e3 : ((3 : ℕ) - 1 : ℝ) * Real.pi / 3 = 2 * Real.pi / 3 := by norm_num
  have e4 : ((4 : ℕ) - 1 : ℝ) * Real.pi / 3 = Real.pi := by norm_num
  have e5 : ((5 : ℕ) - 1 : ℝ) * Real.pi / 3 = 4 * Real.pi / 3 := by norm_num
  have e6 : ((6 : ℕ) - 1 : ℝ) * Real.pi / 3 = 5 * Real.pi / 3 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp only [inverterVector, activeVector, clarke_re, clarke_im, e1, e2, e3, e4, e5, e6,
      Real.cos_zero, Real.sin_zero, Real.cos_pi_div_three, Real.sin_pi_div_three, c2, s2,
      Real.cos_pi, Real.sin_pi, c4, s4, c5, s5, ↓reduceIte, Bool.false_eq_true] <;>
    ring

/-! ## Rotation, power and torque -/

/-- `Im(conj ψ · i)` is invariant under a common frame rotation `e^{jθ}`. -/
@[tmio T, powerlib_foundation] theorem cross_rotate (θ : ℝ) (ψ i : ℂ) :
    (conj (exp (θ * I) * ψ) * (exp (θ * I) * i)).im = (conj ψ * i).im := by
  have h : conj (exp (θ * I) * ψ) * (exp (θ * I) * i) =
      (conj (exp (θ * I)) * exp (θ * I)) * (conj ψ * i) := by
    rw [map_mul]; ring
  rw [h, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  simp

/-- `Im(conj ψ · i) = ψ_α i_β − ψ_β i_α` (also with `d, q` in place of `α, β`). -/
@[tmio T, simp, powerlib_foundation] theorem cross_eq (ψ i : ℂ) :
    (conj ψ * i).im = ψ.re * i.im - ψ.im * i.re := by
  simp [Complex.mul_im]
  ring

/-- Instantaneous power balance of a stator winding in a frame rotating at `ω`
(motor convention `v = r i + ψ̇ + jωψ`): input power = copper loss + magnetic-field term +
speed-voltage term `ω Im(conj ψ · i)`. Multiply by `3/2` for the amplitude-invariant
three-phase power. -/
@[tmio T, powerlib_foundation] theorem power_balance (r ω : ℝ) (v i ψ dψ : ℂ)
    (h : v = r * i + dψ + I * ω * ψ) :
    (v * conj i).re = r * Complex.normSq i + (dψ * conj i).re + ω * (conj ψ * i).im := by
  subst h
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Electromagnetic torque of a three-phase machine with `np` pole pairs. -/
def torque (np : ℝ) (ψ i : ℂ) : ℝ := 3 / 2 * np * (conj ψ * i).im

/-- `T_e · Ω_m` equals the amplitude-invariant speed-voltage power `(3/2) ω Im(conj ψ · i)`,
where `Ω_m = ω / np` is the mechanical speed. -/
@[tmio T, powerlib_foundation] theorem torque_mul_mechanicalSpeed (np ω : ℝ) (hnp : np ≠ 0) (ψ i : ℂ) :
    torque np ψ i * (ω / np) = 3 / 2 * ω * (conj ψ * i).im := by
  unfold torque
  field_simp

/-- The torque coefficient is forced by the power balance: if `c · Im(conj ψ · i) · Ω_m`
equals the speed-voltage power for some operating point with nonzero speed and torque
current, then `c = (3/2) np`. In particular `(3/2)(np/2)` (the note's coefficient with `p`
read as pole pairs) is wrong. -/
@[tmio T, powerlib_foundation] theorem torque_coefficient_unique (np ω c : ℝ) (hnp : np ≠ 0)
    (ψ i : ℂ) (hω : ω ≠ 0) (hx : (conj ψ * i).im ≠ 0)
    (h : c * (conj ψ * i).im * (ω / np) = 3 / 2 * ω * (conj ψ * i).im) :
    c = 3 / 2 * np := by
  field_simp at h
  linarith

/-- The half-coefficient `(3/2)(np/2)` does not satisfy the power balance. -/
@[tmio T, powerlib_foundation] theorem torque_halfCoefficient_ne (np ω : ℝ) (hnp : np ≠ 0)
    (ψ i : ℂ) (hω : ω ≠ 0) (hx : (conj ψ * i).im ≠ 0) :
    3 / 2 * (np / 2) * (conj ψ * i).im * (ω / np) ≠ 3 / 2 * ω * (conj ψ * i).im := by
  intro h
  have := torque_coefficient_unique np ω _ hnp ψ i hω hx h
  have : np = 0 := by linarith
  exact hnp this

end powerlib.Transform.SpaceVector
