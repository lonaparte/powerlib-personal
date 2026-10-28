import theorem.Delay.Pade
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Phase of the pure delay and of its Padé approximants; relative phase-error bounds

Closed-form phases of the pure delay and of its Padé approximants on the imaginary axis, and the
frequency bands in which the approximants stay within a 5 % relative phase error.

Model boundary.
* Scalar frequency responses of the delay models in `theorem/Delay/Pade.lean` only; continuous
  time, constant delay, positive frequency branch `τω > 0`. No closed loop, plant, PWM or
  sampling is involved, and the bounds say nothing about stability margins of any converter.
* On the imaginary axis `s = jω` (`ω : ℝ`, `τ : ℝ`, `x = τ ω`), with `Complex.arg` the
  principal argument in `(-π, π]`.
* Relative phase error: `relPhaseError G τ ω = (arg e^{-jωτ} - arg G(jω)) / arg e^{-jωτ}`, i.e.
  the phase deficit of the approximant relative to the exact linear phase lag `ωτ`.

Source: work-sync theory/T-control-delay.md §1.2 (`|G_del(jω)| = 1`, `∠G_del = -ωτ`),
§1.3 (adaptation-band table: Padé(1,1) `< 5 %` for `ωτ < 0.5`, Padé(2,2) `< 5 %` for
`ωτ < 1.5`); theory/T-gfl-impedance.md §1.2 (the same 5 % band).

Results.
* `arg_pureDelay_jω` — pure delay: `arg (e^{-jωτ}) = -τω` whenever `-π ≤ τω < π`.
* `arg_pade11_jω` — Padé(1,1): `arg (pade11 τ (jω)) = -2 arctan (τω/2)` for every `ω`.
* `arg_pade22_jω` — Padé(2,2): `arg (pade22 τ (jω)) = -2 arctan ((τω/2) / (1 - (τω)²/12))`
  whenever `(τω)² < 12`.
* `relPhaseError_pade11_lt` — `0 < τω < 1/2` ⇒ `0 ≤ relPhaseError pade11 < 1/20` (below 5 %);
  it uses `u - u³/3 ≤ arctan u` (`sub_cube_div_three_le_arctan`, proved by monotonicity).
* `relPhaseError_pade22_lt` — `0 < τω < 3/2` ⇒ `0 ≤ relPhaseError pade22 < 1/20` (below 5 %);
  it uses `d/dx [2 arctan (6x/(12 - x²))] = 12 (12 + x²)/(144 + 12x² + x⁴) > 19/20` on
  `(0, 3/2)`.
-/

noncomputable section
namespace powerlib.Delay
open Complex Real

/-- Relative phase deficit of an approximant `G` of `e^{-τ s}` at `s = jω`. -/
def relPhaseError (G : ℝ → ℂ → ℂ) (τ ω : ℝ) : ℝ :=
  (arg (pureDelay τ (ω * I)) - arg (G τ (ω * I))) / arg (pureDelay τ (ω * I))

/-! ## Arguments -/

@[tmio T, powerlib_foundation] theorem arg_pureDelay_jω {τ ω : ℝ} (h₁ : -π ≤ τ * ω) (h₂ : τ * ω < π) :
    arg (pureDelay τ (ω * I)) = -(τ * ω) := by
  rw [pureDelay_jω, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I (θ := -(τ * ω)) ⟨by linarith, by linarith⟩

/-- `arg ((a - b j)/(a + b j)) = -2 arctan (b/a)` for `a > 0`. -/
@[powerlib_foundation] theorem arg_conj_ratio {a : ℝ} (ha : 0 < a) (b : ℝ) :
    arg (((a : ℂ) - (b : ℂ) * I) / ((a : ℂ) + (b : ℂ) * I)) = -2 * arctan (b / a) := by
  set u := b / a with hu
  have hθ1 := neg_pi_div_two_lt_arctan u
  have hθ2 := arctan_lt_pi_div_two u
  have hsq : 0 < 1 + u ^ 2 := by positivity
  have hc : Real.cos (2 * arctan u) = (1 - u ^ 2) / (1 + u ^ 2) := by
    rw [Real.cos_two_mul, Real.cos_arctan, div_pow, Real.sq_sqrt hsq.le]
    field_simp
    ring
  have hs : Real.sin (2 * arctan u) = 2 * u / (1 + u ^ 2) := by
    rw [Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
    field_simp
    rw [Real.sq_sqrt hsq.le]
  have hden : ((a : ℂ) + (b : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hval : ((a : ℂ) - (b : ℂ) * I) / ((a : ℂ) + (b : ℂ) * I) =
      ((Real.cos (-2 * arctan u) : ℝ) : ℂ) + ((Real.sin (-2 * arctan u) : ℝ) : ℂ) * I := by
    rw [div_eq_iff hden, neg_mul, Real.cos_neg, Real.sin_neg, hc, hs]
    have ha0 : a ≠ 0 := ha.ne'
    apply Complex.ext <;>
    · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im, Complex.add_im,
        Complex.sub_im]
      rw [hu]
      field_simp
      ring
  rw [hval, Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_cos_add_sin_mul_I (θ := -2 * arctan u) ⟨by linarith, by linarith⟩

@[powerlib_foundation] theorem arg_pade11_jω (τ ω : ℝ) :
    arg (pade11 τ (ω * I)) = -2 * arctan (τ * ω / 2) := by
  rw [pade11, pade11Num_jω, pade11Den_jω]
  have := arg_conj_ratio (a := 1) one_pos (τ * ω / 2)
  simpa using this

@[powerlib_foundation] theorem arg_pade22_jω {τ ω : ℝ} (h : (τ * ω) ^ 2 < 12) :
    arg (pade22 τ (ω * I)) = -2 * arctan ((τ * ω / 2) / (1 - (τ * ω) ^ 2 / 12)) := by
  rw [pade22, pade22Num_jω, pade22Den_jω]
  exact arg_conj_ratio (by linarith) _

/-! ## Elementary arctan bounds -/

/-- `u - u³/3 ≤ arctan u` for `u ≥ 0`. -/
@[powerlib_foundation] theorem sub_cube_div_three_le_arctan {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 3 / 3 ≤ arctan u := by
  let g : ℝ → ℝ := fun v => arctan v - (v - v ^ 3 / 3)
  have hd : ∀ v, HasDerivAt g (1 / (1 + v ^ 2) - (1 - v ^ 2)) v := by
    intro v
    have h2 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3) (1 - v ^ 2) v := by
      have := (hasDerivAt_id' v).sub ((hasDerivAt_pow 3 v).div_const 3)
      convert this using 1
      push_cast
      ring
    exact (Real.hasDerivAt_arctan v).sub h2
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (fun v _ => (hd v).continuousAt.continuousWithinAt)
    · exact fun v _ => (hd v).differentiableAt.differentiableWithinAt
    · intro v _
      rw [(hd v).deriv]
      have hp : 0 < 1 + v ^ 2 := by positivity
      rw [show 1 / (1 + v ^ 2) - (1 - v ^ 2) = v ^ 4 / (1 + v ^ 2) by field_simp; ring]
      positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) hu hu
  simp only [g, arctan_zero] at this
  norm_num at this
  linarith

/-! ## Relative phase-error bounds -/

/-- Padé(1,1): for `0 < τω < 1/2` the relative phase deficit lies in `[0, 5 %)`. -/
@[powerlib_foundation] theorem relPhaseError_pade11_lt {τ ω : ℝ} (h₀ : 0 < τ * ω)
    (h₁ : τ * ω < 1 / 2) :
    0 ≤ relPhaseError pade11 τ ω ∧ relPhaseError pade11 τ ω < 1 / 20 := by
  set x := τ * ω with hx
  have hpi : (1 / 2 : ℝ) < π := by linarith [Real.two_le_pi]
  have hd : arg (pureDelay τ (ω * I)) = -x := arg_pureDelay_jω (by linarith) (by linarith)
  have hp : arg (pade11 τ (ω * I)) = -2 * arctan (x / 2) := arg_pade11_jω τ ω
  have hup := arctan_le_self (x := x / 2) (by linarith)
  have hlow := sub_cube_div_three_le_arctan (u := x / 2) (by linarith)
  have hval : relPhaseError pade11 τ ω = (x - 2 * arctan (x / 2)) / x := by
    rw [relPhaseError, hd, hp]
    field_simp
    ring
  rw [hval]
  constructor
  · apply div_nonneg _ h₀.le
    linarith
  · rw [div_lt_iff₀ h₀]
    have hx2 : x ^ 2 < 1 / 4 := by nlinarith
    have hcube : x ^ 3 / 12 < 1 / 20 * x := by
      have : x * x ^ 2 < x * (1 / 4) := mul_lt_mul_of_pos_left hx2 h₀
      nlinarith
    nlinarith

@[powerlib_foundation] private lemma hasDerivAt_pade22_phase {x : ℝ} (hx : x ^ 2 < 12) :
    HasDerivAt (fun y : ℝ => 2 * arctan ((y / 2) / (1 - y ^ 2 / 12)))
      (12 * (12 + x ^ 2) / (144 + 12 * x ^ 2 + x ^ 4)) x := by
  have hden : (1 - x ^ 2 / 12) ≠ 0 := by
    intro h; linarith
  have hw : HasDerivAt (fun y : ℝ => (y / 2) / (1 - y ^ 2 / 12))
      (((1 / 2) * (1 - x ^ 2 / 12) - (x / 2) * (-(2 * x / 12))) / (1 - x ^ 2 / 12) ^ 2) x := by
    have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    have h2 : HasDerivAt (fun y : ℝ => 1 - y ^ 2 / 12) (-(2 * x / 12)) x := by
      have := ((hasDerivAt_pow 2 x).div_const 12).const_sub 1
      convert this using 1
      push_cast
      ring
    exact h1.div h2 hden
  have h := (Real.hasDerivAt_arctan _).comp x hw
  refine (h.const_mul 2).congr_deriv ?_
  have hpos : 0 < 144 + 12 * x ^ 2 + x ^ 4 := by positivity
  have hd2 : (12 - x ^ 2) ≠ 0 := by intro h; linarith
  have hw2 : (1 + (x / 2 / (1 - x ^ 2 / 12)) ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- Padé(2,2): for `0 < τω < 3/2` the relative phase deficit lies in `[0, 5 %)`. -/
@[powerlib_foundation] theorem relPhaseError_pade22_lt {τ ω : ℝ} (h₀ : 0 < τ * ω)
    (h₁ : τ * ω < 3 / 2) :
    0 ≤ relPhaseError pade22 τ ω ∧ relPhaseError pade22 τ ω < 1 / 20 := by
  set x := τ * ω with hx
  have hx12 : x ^ 2 < 12 := by nlinarith
  have hpi : (3 / 2 : ℝ) < π := by linarith [Real.two_le_pi]
  have hd : arg (pureDelay τ (ω * I)) = -x := arg_pureDelay_jω (by linarith) (by linarith)
  have hp : arg (pade22 τ (ω * I)) = -2 * arctan ((x / 2) / (1 - x ^ 2 / 12)) :=
    arg_pade22_jω hx12
  let φ : ℝ → ℝ := fun y => 2 * arctan ((y / 2) / (1 - y ^ 2 / 12))
  let D : Set ℝ := Set.Icc 0 (3 / 2)
  have hsmall : ∀ y ∈ D, y ^ 2 < 12 := fun y hy => by nlinarith [hy.1, hy.2]
  have hcont : ContinuousOn φ D := fun y hy =>
    (hasDerivAt_pade22_phase (hsmall y hy)).continuousAt.continuousWithinAt
  have hint : interior D = Set.Ioo 0 (3 / 2) := interior_Icc
  -- lower bound: φ(y) - (19/20) y strictly increasing
  have hlow : StrictMonoOn (fun y => φ y - 19 / 20 * y) D := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (3 / 2))
    · exact hcont.sub (continuousOn_const.mul continuousOn_id)
    · intro y hy
      rw [hint] at hy
      have hy12 : y ^ 2 < 12 := by nlinarith [hy.1, hy.2]
      have hder : HasDerivAt (fun y => φ y - 19 / 20 * y)
          (12 * (12 + y ^ 2) / (144 + 12 * y ^ 2 + y ^ 4) - 19 / 20 * 1) y :=
        (hasDerivAt_pade22_phase hy12).sub ((hasDerivAt_id' y).const_mul (19 / 20))
      rw [hder.deriv]
      have hpos : 0 < 144 + 12 * y ^ 2 + y ^ 4 := by positivity
      rw [mul_one, sub_pos, lt_div_iff₀ hpos]
      have hy2 : y ^ 2 < 9 / 4 := by nlinarith [hy.1, hy.2]
      have hy4 : y ^ 4 < 81 / 16 := by
        have h0 : 0 ≤ y ^ 2 := sq_nonneg y
        nlinarith
      nlinarith
  -- upper bound: y - φ(y) monotone
  have hupp : MonotoneOn (fun y => y - φ y) D := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (3 / 2))
    · exact continuousOn_id.sub hcont
    · intro y hy
      rw [hint] at hy
      have hy12 : y ^ 2 < 12 := by nlinarith [hy.1, hy.2]
      have hder : HasDerivAt (fun y => y - φ y)
          (1 - 12 * (12 + y ^ 2) / (144 + 12 * y ^ 2 + y ^ 4)) y :=
        (hasDerivAt_id' y).sub (hasDerivAt_pade22_phase hy12)
      exact hder.differentiableAt.differentiableWithinAt
    · intro y hy
      rw [hint] at hy
      have hy12 : y ^ 2 < 12 := by nlinarith [hy.1, hy.2]
      have hder : HasDerivAt (fun y => y - φ y)
          (1 - 12 * (12 + y ^ 2) / (144 + 12 * y ^ 2 + y ^ 4)) y :=
        (hasDerivAt_id' y).sub (hasDerivAt_pade22_phase hy12)
      rw [hder.deriv]
      have hpos : 0 < 144 + 12 * y ^ 2 + y ^ 4 := by positivity
      rw [sub_nonneg, div_le_one hpos]
      nlinarith [sq_nonneg (y ^ 2)]
  have h0D : (0 : ℝ) ∈ D := ⟨le_refl _, by norm_num⟩
  have hxD : x ∈ D := ⟨h₀.le, h₁.le⟩
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hL := hlow h0D hxD h₀
  have hU := hupp h0D hxD h₀.le
  simp only [hφ0, mul_zero, sub_zero] at hL hU
  have hval : relPhaseError pade22 τ ω = (x - φ x) / x := by
    rw [relPhaseError, hd, hp]
    simp only [φ]
    field_simp
    ring
  rw [hval]
  constructor
  · exact div_nonneg (by linarith) h₀.le
  · rw [div_lt_iff₀ h₀]
    linarith

end powerlib.Delay
