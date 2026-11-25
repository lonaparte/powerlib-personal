import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The first-order lag filter driven by a signal, and estimates for tracking paths

Generic calculus for constructing controlled paths that follow a reference: the explicit solution
of the scalar lag filter `ż = ω (h − z)` driven by a continuous signal `h`, its lag bound for a
Lipschitz signal, quadratic estimates for the action of a control perturbed by the lag (crude,
and to first order in `1/ω`), an interpolation bound at a zero end, a quartic bump with
vanishing value and slope at both ends of `[0, 1]`, and two elementary bounds (a sine increment
near a point where `cos < 0`, a lower bound for `∫₀¹ e^{ωs} t²(1 − t)²`).

Scope.
* Real-valued functions of a real variable; no engineering import, no model family. The filter is
  the scalar, constant-coefficient case written in closed form (the matrix variation-of-constants
  formula with the Peano–Baker transition matrix is `theorem/Dynamics/VariationOfConstants.lean`).
* The statements are about given functions (`h`, `f`, `w`); no solution concept or behaviour is
  defined here.

Source: the variation-of-constants formula for `ż = ω(h − z)` (any ODE text, e.g. Hespanha,
*Linear Systems Theory*, Ch. 5); the tracking certificate is an exact polynomial identity (checked
with sympy in the audit scratch notes); used by
`theorem/GridTiedConverter/GFM/Noise/EscapeExponent.lean` for the fast-filter limit and the
first-order deficit of the escape exponent.

Results.
* `lagFilter ω z₀ h t = e^{−ωt}(z₀ + ω ∫₀ᵗ e^{ωs} h(s) ds)`: `hasDerivAt_lagFilter`
  (`ż = ω(h − z)` for continuous `h`), `lagFilter_zero`, `abs_lagFilter_sub_le`
  (`|z(t) − h(t)| ≤ |z₀ − h(0)| + 2G/ω` on `[0, T]` when `h` is `G`-Lipschitz there, `ω > 0`).
* `integral_sq_add_le`: `½∫₀ᵀ (f + w/σ)² ≤ ½∫₀ᵀ f² + T (U E/|σ| + E²/σ²)` for `|f| ≤ U`,
  `|w| ≤ E`.
* `lagFilter_const` (`z(t) = c + (z₀ − c) e^{−ωt}` for a constant signal) and
  `lagFilter_tracking`: for the lag `e = z − h` (`h` of right derivative `g`) and a weight `w`
  (right derivative `w'`), `e(T)² ≤ e(0)² + ∫g²/ω` and
  `∫(w + e)² ≤ ∫w² − (2/ω)∫w g + ∫w'²/ω² + 2∫g²/ω² + (2/ω)(w(0)e(0) − w(T)e(T))
  + (2/ω)(e(0)² − e(T)²)` (certificate `(w'/ω − e)² + 2(e + g/ω)² ≥ 0`, integration by parts):
  the action of a control perturbed by the lag is the unperturbed action minus `(2/ω)∫w g` up to
  `O(1/ω²)`.
* `sq_le_of_zero_end`: `x(a)² ≤ λ∫x² + ∫x'²/λ` on `[a, b]` when `x(b) = 0`, every `λ > 0`.
* `lagFilter_eq_add` (`z(t) = e^{−ωt} z₀ + z_{z₀ = 0}(t)`), `lagFilter_mono` (`h ≤ k` on `[0, t]`
  gives `z_h(t) ≤ z_k(t)`), `abs_lagFilter_sub_const_le` (`|z(t) − c| ≤ |z₀ − c| + ωtB` for
  `|h − c| ≤ B`).
* `hasDerivAt_vec_two`, `hasDerivWithinAt_vec_three`: derivatives of `![f, g]`, `![f, g, k]`
  from those of the components.
* `endBump t = t²(1 − t)²` with `endBumpVel`, `endBumpAcc` (`hasDerivAt_endBump`,
  `hasDerivAt_endBumpVel`), `endBump_bounds` (on `[0, 1]`: `0 ≤ b ≤ 1`, `|b'| ≤ 1`, `|b''| ≤ 2`),
  `integral_exp_mul_endBump_ge` (`∫₀¹ e^{ωs} b(s) ds ≥ e^ω/(36 ω³)`, `ω ≥ 2`).
* `sin_add_sub_sin_bounds`: for `|x| ≤ −cos θ/2`, `sin(θ + x) − sin θ ≤ (cos θ/2) x` when `x ≥ 0`
  and `≥ (cos θ/2) x` when `x ≤ 0`.
-/

noncomputable section
namespace powerlib.Dynamics

open Real Set Filter Topology

/-! ## The first-order lag filter driven by a continuous signal -/

/-- Solution of `ż = ω (h − z)`, `z(0) = z₀`: `z(t) = e^{−ωt} (z₀ + ω ∫₀ᵗ e^{ωs} h(s) ds)`. -/
def lagFilter (ω z₀ : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(ω * t)) * (z₀ + ω * ∫ s in (0 : ℝ)..t, Real.exp (ω * s) * h s)

@[tmio T, powerlib_foundation] theorem hasDerivAt_lagFilter {ω z₀ : ℝ} {h : ℝ → ℝ}
    (hh : Continuous h) (t : ℝ) :
    HasDerivAt (lagFilter ω z₀ h) (ω * (h t - lagFilter ω z₀ h t)) t := by
  have hc : Continuous fun s => Real.exp (ω * s) * h s := by fun_prop
  have hI := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hE : HasDerivAt (fun t => Real.exp (-(ω * t))) (Real.exp (-(ω * t)) * -ω) t := by
    have h' := ((hasDerivAt_id' t).const_mul (-ω)).exp
    have e : (fun x => Real.exp (-(ω * x))) = fun x => Real.exp (-ω * x) := by
      funext x; ring_nf
    rw [e]; convert h' using 1; ring_nf
  have h2 := hE.mul ((hI.const_mul ω).const_add z₀)
  have e : Real.exp (-(ω * t)) * Real.exp (ω * t) = 1 := by rw [← Real.exp_add]; simp
  exact h2.congr_deriv (by unfold lagFilter; linear_combination ω * h t * e)

@[tmio T, powerlib_foundation] theorem lagFilter_zero (ω z₀ : ℝ) (h : ℝ → ℝ) :
    lagFilter ω z₀ h 0 = z₀ := by
  simp [lagFilter]

/-- **Lag of the filter**: if `h` is `G`-Lipschitz on `[0, T]` (`ω > 0`), then on `[0, T]`
`|z(t) − h(t)| ≤ |z₀ − h(0)| + 2G/ω`. -/
@[tmio T, powerlib_foundation] theorem abs_lagFilter_sub_le {ω z₀ G T : ℝ} {h : ℝ → ℝ}
    (hω : 0 < ω) (hh : Continuous h) (hG : 0 ≤ G)
    (hL : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |h s - h t| ≤ G * |s - t|) {t : ℝ} (ht : t ∈ Icc 0 T) :
    |lagFilter ω z₀ h t - h t| ≤ |z₀ - h 0| + 2 * G / ω := by
  have ht0 : 0 ≤ t := ht.1
  set E := Real.exp (ω * t) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hEinv : Real.exp (-(ω * t)) = E⁻¹ := by rw [Real.exp_neg]
  -- `∫₀ᵗ e^{ωs} ds = (E − 1)/ω`
  have hint1 : ∫ s in (0 : ℝ)..t, Real.exp (ω * s) = (E - 1) / ω := by
    have hd : ∀ s ∈ uIcc 0 t, HasDerivAt (fun s => Real.exp (ω * s) / ω) (Real.exp (ω * s)) s :=
      fun s _ => by
        have := (((hasDerivAt_id' s).const_mul ω).exp).div_const ω
        convert this using 1; field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun s =>
      Real.exp (ω * s)).intervalIntegrable 0 t)]
    simp [hEdef]; ring
  -- `∫₀ᵗ e^{ωs} (t − s) ds = (E − 1)/ω² − t/ω`
  have hint2 : ∫ s in (0 : ℝ)..t, Real.exp (ω * s) * (t - s) = E / ω ^ 2 - t / ω - 1 / ω ^ 2 := by
    have hd : ∀ s ∈ uIcc 0 t, HasDerivAt
        (fun s => Real.exp (ω * s) * (t - s) / ω + Real.exp (ω * s) / ω ^ 2)
        (Real.exp (ω * s) * (t - s)) s := fun s _ => by
      have h1 := ((hasDerivAt_id' s).const_mul ω).exp
      have := ((h1.mul ((hasDerivAt_id' s).const_sub t)).div_const ω).add (h1.div_const (ω ^ 2))
      convert this using 1; field_simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun s =>
      Real.exp (ω * s) * (t - s)).intervalIntegrable 0 t)]
    simp [hEdef]; field_simp; ring
  -- the decomposition `z − h(t) = e^{−ωt}(z₀ − h(t)) + e^{−ωt} ω ∫ e^{ωs}(h(s) − h(t))`
  have hsplit : ∫ s in (0 : ℝ)..t, Real.exp (ω * s) * h s =
      (∫ s in (0 : ℝ)..t, Real.exp (ω * s) * (h s - h t)) + h t * ((E - 1) / ω) := by
    rw [← hint1, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      ((by fun_prop : Continuous fun s => Real.exp (ω * s) * (h s - h t)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s => h t * Real.exp (ω * s)).intervalIntegrable _ _)]
    congr 1; funext s; ring
  have hJ : |∫ s in (0 : ℝ)..t, Real.exp (ω * s) * (h s - h t)| ≤
      G * (E / ω ^ 2 - t / ω - 1 / ω ^ 2) := by
    rw [← hint2, ← intervalIntegral.integral_const_mul, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le ht0 (Filter.Eventually.of_forall
      fun s hs => ?_) ((by fun_prop : Continuous fun s =>
        G * (Real.exp (ω * s) * (t - s))).intervalIntegrable _ _)
    have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
    have hst := hL s hs' t ht
    rw [abs_sub_comm s t, abs_of_nonneg (show (0 : ℝ) ≤ t - s by linarith [hs.2])] at hst
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (ω * s) * |h s - h t| ≤ Real.exp (ω * s) * (G * (t - s)) :=
          mul_le_mul_of_nonneg_left hst (Real.exp_pos _).le
      _ = G * (Real.exp (ω * s) * (t - s)) := by ring
  have hh0 : |h t - h 0| ≤ G * t := by
    have := hL t ht 0 ⟨le_rfl, ht0.trans ht.2⟩; rwa [sub_zero, abs_of_nonneg ht0] at this
  set J := ∫ s in (0 : ℝ)..t, Real.exp (ω * s) * (h s - h t) with hJdef
  have hE1 : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_exp (by positivity))
  have hEi : 0 < E⁻¹ := inv_pos.mpr hEpos
  have hid : lagFilter ω z₀ h t - h t = E⁻¹ * (z₀ - h t) + E⁻¹ * ω * J := by
    simp only [lagFilter, hEinv, hsplit]; field_simp; ring
  have hzt : |z₀ - h t| ≤ |z₀ - h 0| + G * t := by
    calc |z₀ - h t| ≤ |z₀ - h 0| + |h 0 - h t| := abs_sub_le _ _ _
      _ ≤ |z₀ - h 0| + G * t := by rw [abs_sub_comm (h 0) (h t)]; linarith
  rw [hid]
  calc |E⁻¹ * (z₀ - h t) + E⁻¹ * ω * J|
      ≤ E⁻¹ * |z₀ - h t| + E⁻¹ * ω * |J| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hEi, abs_of_pos hω]
    _ ≤ E⁻¹ * (|z₀ - h 0| + G * t) + E⁻¹ * ω * (G * (E / ω ^ 2 - t / ω - 1 / ω ^ 2)) := by
        gcongr
    _ = E⁻¹ * |z₀ - h 0| + G / ω - G * E⁻¹ / ω := by field_simp; ring
    _ ≤ |z₀ - h 0| + 2 * G / ω := by
        have h1 : E⁻¹ * |z₀ - h 0| ≤ |z₀ - h 0| :=
          mul_le_of_le_one_left (abs_nonneg _) hE1
        have h2 : 0 ≤ G * E⁻¹ / ω := by positivity
        have h4 : G / ω ≤ 2 * G / ω := by
          rw [mul_div_assoc]; have : 0 ≤ G / ω := by positivity
          linarith
        calc E⁻¹ * |z₀ - h 0| + G / ω - G * E⁻¹ / ω ≤ E⁻¹ * |z₀ - h 0| + G / ω :=
              sub_le_self _ h2
          _ ≤ |z₀ - h 0| + 2 * G / ω := add_le_add h1 h4


@[tmio T, powerlib_foundation] theorem hasDerivAt_vec_two {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => ![f s, g s]) ![f', g'] t := by
  rw [hasDerivAt_pi]
  intro i; fin_cases i
  · simpa using hf
  · simpa using hg


@[tmio T, powerlib_foundation] theorem hasDerivWithinAt_vec_three {f g k : ℝ → ℝ}
    {f' g' k' t : ℝ} {S : Set ℝ} (hf : HasDerivWithinAt f f' S t) (hg : HasDerivWithinAt g g' S t)
    (hk : HasDerivWithinAt k k' S t) :
    HasDerivWithinAt (fun s => ![f s, g s, k s]) ![f', g', k'] S t := by
  rw [hasDerivWithinAt_pi]
  intro i; fin_cases i
  · simpa using hf
  · simpa using hg
  · simpa using hk


/-- **Quadratic action estimate**: `½∫(f + w/σ)² ≤ ½∫f² + T (U E/|σ| + E²/σ²)` when `|f| ≤ U`
and `|w| ≤ E` on `[0, T]`. -/
@[tmio T, powerlib_foundation] theorem integral_sq_add_le {T U E σ : ℝ} (hT : 0 ≤ T)
    {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hU : ∀ t ∈ Icc 0 T, |f t| ≤ U) (hE : ∀ t ∈ Icc 0 T, |w t| ≤ E) (hσ : σ ≠ 0) :
    1 / 2 * ∫ t in (0 : ℝ)..T, (f t + w t / σ) ^ 2 ≤
      1 / 2 * (∫ t in (0 : ℝ)..T, f t ^ 2) + T * (U * E / |σ| + E ^ 2 / σ ^ 2) := by
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hle : ∫ t in (0 : ℝ)..T, (f t + w t / σ) ^ 2 ≤
      ∫ t in (0 : ℝ)..T, (f t ^ 2 + (2 * (U * E / |σ|) + E ^ 2 / σ ^ 2)) := by
    apply intervalIntegral.integral_mono_on hT
    · exact ((hf.add (hw.div_const σ)).pow 2).intervalIntegrable_of_Icc hT
    · exact ((hf.pow 2).add continuousOn_const).intervalIntegrable_of_Icc hT
    · intro t ht
      have h1 := hU t ht
      have h2 := hE t ht
      have hfw : |f t * (w t / σ)| ≤ U * E / |σ| := by
        rw [abs_mul, abs_div, mul_div_assoc']
        exact div_le_div_of_nonneg_right
          (mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)) (abs_nonneg σ)
      have hw2 : (w t / σ) ^ 2 ≤ E ^ 2 / σ ^ 2 := by
        rw [div_pow]
        refine div_le_div_of_nonneg_right ?_ hσ2.le
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      nlinarith [abs_le.mp hfw]
  have hsplit : ∫ t in (0 : ℝ)..T, (f t ^ 2 + (2 * (U * E / |σ|) + E ^ 2 / σ ^ 2)) =
      (∫ t in (0 : ℝ)..T, f t ^ 2) + T * (2 * (U * E / |σ|) + E ^ 2 / σ ^ 2) := by
    rw [intervalIntegral.integral_add (f := fun t => f t ^ 2)
      (g := fun _ => 2 * (U * E / |σ|) + E ^ 2 / σ ^ 2)
      ((hf.pow 2).intervalIntegrable_of_Icc hT) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [hsplit] at hle
  have : 0 ≤ T * (E ^ 2 / σ ^ 2) := by positivity
  linarith


/-! ## A quartic end bump and auxiliary bounds -/

def endBump (t : ℝ) : ℝ := t ^ 2 * (1 - t) ^ 2

def endBumpVel (t : ℝ) : ℝ := 2 * t - 6 * t ^ 2 + 4 * t ^ 3

def endBumpAcc (t : ℝ) : ℝ := 2 - 12 * t + 12 * t ^ 2

@[tmio T, powerlib_foundation] theorem hasDerivAt_endBump (l δe t : ℝ) :
    HasDerivAt (fun t => δe + l * endBump t) (l * endBumpVel t) t := by
  have h := ((((hasDerivAt_pow 2 t).sub ((hasDerivAt_pow 3 t).const_mul 2)).add
    (hasDerivAt_pow 4 t)).const_mul l).const_add δe
  convert h using 1
  · funext s; simp only [endBump, Pi.add_apply, Pi.sub_apply]; ring
  · simp only [endBumpVel]; push_cast; ring

@[tmio T, powerlib_foundation] theorem hasDerivAt_endBumpVel (l t : ℝ) :
    HasDerivAt (fun t => l * endBumpVel t) (l * endBumpAcc t) t := by
  have h := ((((hasDerivAt_id' t).const_mul 2).sub ((hasDerivAt_pow 2 t).const_mul 6)).add
    ((hasDerivAt_pow 3 t).const_mul 4)).const_mul l
  convert h using 1
  · funext s; simp only [endBumpVel, Pi.add_apply, Pi.sub_apply]
  · simp only [endBumpAcc]; push_cast; ring

@[tmio T, powerlib_foundation] theorem endBump_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ endBump t ∧ endBump t ≤ 1 ∧ |endBumpVel t| ≤ 1 ∧ |endBumpAcc t| ≤ 2 := by
  obtain ⟨h0, h1⟩ := ht
  refine ⟨by unfold endBump; positivity, ?_, ?_, ?_⟩
  · unfold endBump; nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), sq_nonneg (t * (1 - t))]
  · unfold endBumpVel; rw [abs_le]; constructor <;>
      nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1)]
  · unfold endBumpAcc; rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t - 1 / 2)]

/-- `sin(θ + x) − sin θ ≤ −κ x/2` for `0 ≤ x ≤ κ/2`, `cos θ = −κ < 0` (and the mirror bound). -/
@[tmio T, powerlib_foundation] theorem sin_add_sub_sin_bounds {θ x : ℝ}
    (hx : |x| ≤ -Real.cos θ / 2) :
    (0 ≤ x → Real.sin (θ + x) - Real.sin θ ≤ Real.cos θ / 2 * x) ∧
      (x ≤ 0 → Real.cos θ / 2 * x ≤ Real.sin (θ + x) - Real.sin θ) := by
  have key : ∀ y, |y| ≤ |x| → Real.cos (θ + y) ≤ Real.cos θ / 2 := fun y hy => by
    have := Real.abs_cos_sub_cos_le (θ + y) θ
    rw [add_sub_cancel_left] at this
    linarith [(abs_le.mp this).2]
  have hd : ∀ y, HasDerivAt (fun y => Real.sin (θ + y)) (Real.cos (θ + y)) y := fun y => by
    simpa using ((hasDerivAt_id' y).const_add θ).sin
  constructor
  · intro h0
    rcases h0.lt_or_eq with hpos | rfl
    · obtain ⟨ξ, hξ, hs⟩ := exists_hasDerivAt_eq_slope (fun y => Real.sin (θ + y))
        (fun y => Real.cos (θ + y)) hpos (fun y _ => (hd y).continuousAt.continuousWithinAt)
        (fun y _ => hd y)
      have hξx : |ξ| ≤ |x| := by
        rw [abs_of_pos (hξ.1), abs_of_pos hpos]; exact hξ.2.le
      have := key ξ hξx
      rw [hs, add_zero, sub_zero] at this
      rwa [div_le_iff₀ hpos] at this
    · simp
  · intro h0
    rcases h0.lt_or_eq with hneg | rfl
    · obtain ⟨ξ, hξ, hs⟩ := exists_hasDerivAt_eq_slope (fun y => Real.sin (θ + y))
        (fun y => Real.cos (θ + y)) hneg (fun y _ => (hd y).continuousAt.continuousWithinAt)
        (fun y _ => hd y)
      have hξx : |ξ| ≤ |x| := by
        rw [abs_of_neg hξ.2, abs_of_neg hneg]; linarith [hξ.1]
      have := key ξ hξx
      rw [hs, add_zero, zero_sub, div_le_iff₀ (by linarith : (0 : ℝ) < -x)] at this
      linarith
    · simp

/-- `∫₀¹ e^{ωs} endBump(s) ds ≥ e^ω/(36 ω³)` for `ω ≥ 2`. -/
@[tmio T, powerlib_foundation] theorem integral_exp_mul_endBump_ge {ω : ℝ} (hω : 2 ≤ ω) :
    Real.exp ω / (36 * ω ^ 3) ≤ ∫ s in (0 : ℝ)..1, Real.exp (ω * s) * endBump s := by
  have hω0 : 0 < ω := by linarith
  have hinv : 1 / ω ≤ 1 / 2 := by rw [div_le_div_iff₀ hω0 (by norm_num)]; linarith
  have ha0 : 0 ≤ 1 - 1 / ω := by linarith
  have ha1 : 1 - 1 / ω ≤ 1 := by have : 0 < 1 / ω := by positivity
                                 linarith
  have hcont : Continuous fun s => Real.exp (ω * s) * endBump s := by unfold endBump; fun_prop
  have h1 : ∫ s in (1 - 1 / ω)..1, Real.exp (ω * s) * endBump s ≤
      ∫ s in (0 : ℝ)..1, Real.exp (ω * s) * endBump s :=
    intervalIntegral.integral_mono_interval ha0 ha1 le_rfl
      (Filter.Eventually.of_forall fun s => by unfold endBump; positivity)
      (hcont.intervalIntegrable _ _)
  have he1 : Real.exp ω / 3 ≤ Real.exp (ω - 1) := by
    rw [Real.exp_sub, div_le_div_iff₀ (by norm_num) (Real.exp_pos 1)]
    have := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos ω]
  have h2 : ∫ s in (1 - 1 / ω)..1, Real.exp ω / 12 * (1 - s) ^ 2 ≤
      ∫ s in (1 - 1 / ω)..1, Real.exp (ω * s) * endBump s := by
    refine intervalIntegral.integral_mono_on ha1 ((by fun_prop : Continuous fun s =>
      Real.exp ω / 12 * (1 - s) ^ 2).intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
      fun s hs => ?_
    have hs2 : 1 / 2 ≤ s := by linarith [hs.1]
    have hexp : Real.exp ω / 3 ≤ Real.exp (ω * s) := he1.trans (Real.exp_le_exp.2 (by
      have : ω * (1 - 1 / ω) = ω - 1 := by field_simp
      have := mul_le_mul_of_nonneg_left hs.1 hω0.le
      linarith))
    have hb : (1 - s) ^ 2 / 4 ≤ endBump s := by
      have h4 : 0 ≤ s ^ 2 - 1 / 4 := by nlinarith
      unfold endBump; nlinarith [mul_nonneg (sq_nonneg (1 - s)) h4]
    calc Real.exp ω / 12 * (1 - s) ^ 2 = Real.exp ω / 3 * ((1 - s) ^ 2 / 4) := by ring
      _ ≤ Real.exp (ω * s) * endBump s := mul_le_mul hexp hb (by positivity) (Real.exp_pos _).le
  have h3 : ∫ s in (1 - 1 / ω)..1, Real.exp ω / 12 * (1 - s) ^ 2 =
      Real.exp ω / (36 * ω ^ 3) := by
    have hd : ∀ s ∈ uIcc (1 - 1 / ω) 1, HasDerivAt (fun s => -(Real.exp ω / 12) * (1 - s) ^ 3 / 3)
        (Real.exp ω / 12 * (1 - s) ^ 2) s := fun s _ => by
      have := (((hasDerivAt_id' s).const_sub 1).pow 3).const_mul (-(Real.exp ω / 12)) |>.div_const 3
      convert this using 1; push_cast; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun s =>
      Real.exp ω / 12 * (1 - s) ^ 2).intervalIntegrable _ _)]
    field_simp; ring
  linarith

/-! ## Quadratic tracking estimates -/

/-- The filter driven by a constant: `lagFilter ω z₀ (fun _ => c) t = c + (z₀ − c) e^{−ωt}`. -/
@[tmio T, powerlib_foundation] theorem lagFilter_const (ω z₀ c t : ℝ) :
    lagFilter ω z₀ (fun _ => c) t = c + (z₀ - c) * Real.exp (-(ω * t)) := by
  by_cases hω : ω = 0
  · subst hω; simp [lagFilter]
  have hd : ∀ s ∈ uIcc 0 t, HasDerivAt (fun s => Real.exp (ω * s) * c / ω)
      (Real.exp (ω * s) * c) s := fun s _ => by
    have := ((((hasDerivAt_id' s).const_mul ω).exp).mul_const c).div_const ω
    convert this using 1; field_simp
  rw [lagFilter, intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop :
    Continuous fun s => Real.exp (ω * s) * c).intervalIntegrable 0 t)]
  have e : Real.exp (-(ω * t)) * Real.exp (ω * t) = 1 := by rw [← Real.exp_add]; simp
  simp only [mul_zero, Real.exp_zero, one_mul]
  field_simp
  linear_combination c * e

/-- **Quadratic tracking estimate for the lag filter**: for the lag `e = z − h` of
`z = lagFilter ω z₀ h` (`ω > 0`), with `h` of right derivative `g` and a weight `w` of right
derivative `w'` on `[0, T]` (`g`, `w`, `w'` continuous there), the end lag satisfies
`e(T)² ≤ e(0)² + ∫g²/ω` and
`∫(w + e)² ≤ ∫w² − (2/ω)∫w g + ∫w'²/ω² + 2∫g²/ω² + (2/ω)(w(0)e(0) − w(T)e(T))
  + (2/ω)(e(0)² − e(T)²)`
(`ė = −ωe − g`; pointwise certificate `(w'/ω − e)² + 2(e + g/ω)² ≥ 0`, then integration by parts
of `(w e)'` and `(e²)'`). -/
@[tmio T, powerlib_foundation] theorem lagFilter_tracking {ω z₀ T : ℝ} (hω : 0 < ω)
    (hT : 0 ≤ T) {h g w w' : ℝ → ℝ} (hh : Continuous h)
    (hg : ∀ t ∈ Ico 0 T, HasDerivWithinAt h (g t) (Ici t) t) (hgc : ContinuousOn g (Icc 0 T))
    (hw : ∀ t ∈ Ico 0 T, HasDerivWithinAt w (w' t) (Ici t) t) (hwc : ContinuousOn w (Icc 0 T))
    (hw'c : ContinuousOn w' (Icc 0 T)) :
    (lagFilter ω z₀ h T - h T) ^ 2 ≤ (z₀ - h 0) ^ 2 + (∫ t in (0 : ℝ)..T, g t ^ 2) / ω ∧
      ∫ t in (0 : ℝ)..T, (w t + (lagFilter ω z₀ h t - h t)) ^ 2 ≤
        (∫ t in (0 : ℝ)..T, w t ^ 2) - 2 / ω * (∫ t in (0 : ℝ)..T, w t * g t) +
          (∫ t in (0 : ℝ)..T, w' t ^ 2) / ω ^ 2 + 2 * (∫ t in (0 : ℝ)..T, g t ^ 2) / ω ^ 2 +
          2 / ω * (w 0 * (z₀ - h 0) - w T * (lagFilter ω z₀ h T - h T)) +
          2 / ω * ((z₀ - h 0) ^ 2 - (lagFilter ω z₀ h T - h T) ^ 2) := by
  set Z := lagFilter ω z₀ h with hZdef
  set e : ℝ → ℝ := fun t => Z t - h t with hedef
  have hZ : ∀ t, HasDerivAt Z (ω * (h t - Z t)) t := hasDerivAt_lagFilter hh
  have hZc : Continuous Z := continuous_iff_continuousAt.2 fun t => (hZ t).continuousAt
  have he0 : z₀ - h 0 = e 0 := by simp [e, Z, lagFilter_zero]
  have hec : ContinuousOn e (Icc 0 T) := (hZc.sub hh).continuousOn
  have he : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (-ω * e t - g t) (Ici t) t := by
    intro t ht
    have := (hZ t).hasDerivWithinAt.sub (hg t ht)
    convert this using 1; simp only [e]; ring
  show e T ^ 2 ≤ (z₀ - h 0) ^ 2 + _ ∧ ∫ t in (0 : ℝ)..T, (w t + e t) ^ 2 ≤ _
  rw [he0]
  have hD : ContinuousOn (fun t => -ω * e t - g t) (Icc 0 T) :=
    (continuousOn_const.mul hec).sub hgc
  -- the two exact integrals
  have hIee : ∫ t in (0 : ℝ)..T, 2 * e t * (-ω * e t - g t) = e T ^ 2 - e 0 ^ 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT (hec.pow 2)
      (fun t ht => ?_) (((continuousOn_const.mul hec).mul hD).intervalIntegrable_of_Icc hT)
    have := ((he t (Ioo_subset_Ico_self ht)).pow 2).mono Ioi_subset_Ici_self
    convert this using 1; simp
  have hIwe : ∫ t in (0 : ℝ)..T, (w' t * e t + w t * (-ω * e t - g t)) =
      w T * e T - w 0 * e 0 :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT (hwc.mul hec)
      (fun t ht => ((hw t (Ioo_subset_Ico_self ht)).mul (he t (Ioo_subset_Ico_self ht))).mono
        Ioi_subset_Ici_self)
      (((hw'c.mul hec).add (hwc.mul hD)).intervalIntegrable_of_Icc hT)
  have ig2 : IntervalIntegrable (fun t => g t ^ 2) MeasureTheory.volume 0 T :=
    (hgc.pow 2).intervalIntegrable_of_Icc hT
  constructor
  · -- `(e²)' ≤ g²/ω`
    have hle : ∫ t in (0 : ℝ)..T, 2 * e t * (-ω * e t - g t) ≤
        ∫ t in (0 : ℝ)..T, g t ^ 2 / ω := by
      refine intervalIntegral.integral_mono_on hT
        (((continuousOn_const.mul hec).mul hD).intervalIntegrable_of_Icc hT) (ig2.div_const ω)
        fun t _ => ?_
      have key : g t ^ 2 / ω - 2 * e t * (-ω * e t - g t) =
          (ω * e t + g t) ^ 2 / ω + ω * e t ^ 2 := by field_simp; ring
      have : 0 ≤ (ω * e t + g t) ^ 2 / ω + ω * e t ^ 2 := by positivity
      linarith
    rw [hIee, intervalIntegral.integral_div] at hle
    linarith
  · -- the pointwise certificate, integrated
    have iw2 : IntervalIntegrable (fun t => w t ^ 2) MeasureTheory.volume 0 T :=
      (hwc.pow 2).intervalIntegrable_of_Icc hT
    have iwg : IntervalIntegrable (fun t => w t * g t) MeasureTheory.volume 0 T :=
      (hwc.mul hgc).intervalIntegrable_of_Icc hT
    have iw'2 : IntervalIntegrable (fun t => w' t ^ 2) MeasureTheory.volume 0 T :=
      (hw'c.pow 2).intervalIntegrable_of_Icc hT
    have iwe : IntervalIntegrable (fun t => w' t * e t + w t * (-ω * e t - g t))
        MeasureTheory.volume 0 T := ((hw'c.mul hec).add (hwc.mul hD)).intervalIntegrable_of_Icc hT
    have iee : IntervalIntegrable (fun t => 2 * e t * (-ω * e t - g t)) MeasureTheory.volume 0 T :=
      ((continuousOn_const.mul hec).mul hD).intervalIntegrable_of_Icc hT
    have hle : ∫ t in (0 : ℝ)..T, (w t + e t) ^ 2 ≤ ∫ t in (0 : ℝ)..T,
        ((w t ^ 2 - 2 / ω * (w t * g t)) + (w' t ^ 2 / ω ^ 2 + 2 * g t ^ 2 / ω ^ 2) -
          (2 / ω * (w' t * e t + w t * (-ω * e t - g t)) +
            2 / ω * (2 * e t * (-ω * e t - g t)))) := by
      refine intervalIntegral.integral_mono_on hT
        (((hwc.add hec).pow 2).intervalIntegrable_of_Icc hT)
        (((iw2.sub (iwg.const_mul _)).add ((iw'2.div_const _).add
          ((ig2.const_mul 2).div_const _))).sub ((iwe.const_mul _).add (iee.const_mul _)))
        fun t _ => ?_
      have key : (w' t / ω - e t) ^ 2 + 2 * (e t + g t / ω) ^ 2 =
          ((w t ^ 2 - 2 / ω * (w t * g t)) + (w' t ^ 2 / ω ^ 2 + 2 * g t ^ 2 / ω ^ 2) -
            (2 / ω * (w' t * e t + w t * (-ω * e t - g t)) +
              2 / ω * (2 * e t * (-ω * e t - g t)))) - (w t + e t) ^ 2 := by
        field_simp; ring
      nlinarith [sq_nonneg (w' t / ω - e t), sq_nonneg (e t + g t / ω)]
    rw [intervalIntegral.integral_sub ((iw2.sub (iwg.const_mul _)).add ((iw'2.div_const _).add
        ((ig2.const_mul 2).div_const _))) ((iwe.const_mul _).add (iee.const_mul _)),
      intervalIntegral.integral_add (iw2.sub (iwg.const_mul _)) ((iw'2.div_const _).add
        ((ig2.const_mul 2).div_const _)),
      intervalIntegral.integral_add (iwe.const_mul _) (iee.const_mul _),
      intervalIntegral.integral_sub iw2 (iwg.const_mul _),
      intervalIntegral.integral_add (iw'2.div_const _) ((ig2.const_mul 2).div_const _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul, hIwe, hIee] at hle
    linarith

/-- **Interpolation at a zero end**: if `x(b) = 0` (`x` with right derivative `x'` on `[a, b]`,
both continuous there), then for every `λ > 0`, `x(a)² ≤ λ ∫ x² + (∫ x'²)/λ` over `[a, b]`
(`−2 x x' ≤ λ x² + x'²/λ`). -/
@[tmio T, powerlib_foundation] theorem sq_le_of_zero_end {a b l : ℝ} (hab : a ≤ b) (hl : 0 < l)
    {x x' : ℝ → ℝ} (hx : ∀ t ∈ Ico a b, HasDerivWithinAt x (x' t) (Ici t) t)
    (hxc : ContinuousOn x (Icc a b)) (hx'c : ContinuousOn x' (Icc a b)) (hb : x b = 0) :
    x a ^ 2 ≤ l * (∫ t in a..b, x t ^ 2) + (∫ t in a..b, x' t ^ 2) / l := by
  have hI : ∫ t in a..b, 2 * x t * x' t = x b ^ 2 - x a ^ 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab (hxc.pow 2)
      (fun t ht => ?_) (((continuousOn_const.mul hxc).mul hx'c).intervalIntegrable_of_Icc hab)
    have := ((hx t (Ioo_subset_Ico_self ht)).pow 2).mono Ioi_subset_Ici_self
    convert this using 1; simp
  have i1 : IntervalIntegrable (fun t => x t ^ 2) MeasureTheory.volume a b :=
    (hxc.pow 2).intervalIntegrable_of_Icc hab
  have i2 : IntervalIntegrable (fun t => x' t ^ 2) MeasureTheory.volume a b :=
    (hx'c.pow 2).intervalIntegrable_of_Icc hab
  have hle : ∫ t in a..b, -(2 * x t * x' t) ≤ ∫ t in a..b, (l * x t ^ 2 + x' t ^ 2 / l) := by
    refine intervalIntegral.integral_mono_on hab
      (((continuousOn_const.mul hxc).mul hx'c).neg.intervalIntegrable_of_Icc hab)
      ((i1.const_mul l).add (i2.div_const l)) fun t _ => ?_
    have key : l * x t ^ 2 + x' t ^ 2 / l + 2 * x t * x' t = (l * x t + x' t) ^ 2 / l := by
      field_simp; ring
    have : 0 ≤ (l * x t + x' t) ^ 2 / l := by positivity
    linarith
  rw [intervalIntegral.integral_neg, hI, hb, intervalIntegral.integral_add (i1.const_mul l)
    (i2.div_const l), intervalIntegral.integral_const_mul, intervalIntegral.integral_div] at hle
  linarith

/-! ## Comparison and drift of the filter -/

/-- The filter is affine in its initial value: `z(t) = e^{−ωt} z₀ + z_{z₀=0}(t)`. -/
@[tmio T, powerlib_foundation] theorem lagFilter_eq_add (ω z₀ : ℝ) (h : ℝ → ℝ) (t : ℝ) :
    lagFilter ω z₀ h t = Real.exp (-(ω * t)) * z₀ + lagFilter ω 0 h t := by
  simp only [lagFilter]; ring

/-- **Comparison**: `h ≤ k` on `[0, t]` (`ω, t ≥ 0`, both continuous) gives
`lagFilter ω z₀ h t ≤ lagFilter ω z₀ k t`. -/
@[tmio T, powerlib_foundation] theorem lagFilter_mono {ω z₀ t : ℝ} (hω : 0 ≤ ω) (ht : 0 ≤ t)
    {h k : ℝ → ℝ} (hh : Continuous h) (hk : Continuous k) (hhk : ∀ s ∈ Icc 0 t, h s ≤ k s) :
    lagFilter ω z₀ h t ≤ lagFilter ω z₀ k t := by
  simp only [lagFilter]
  gcongr
  exact intervalIntegral.integral_mono_on ht ((by fun_prop : Continuous fun s =>
    Real.exp (ω * s) * h s).intervalIntegrable _ _) ((by fun_prop : Continuous fun s =>
      Real.exp (ω * s) * k s).intervalIntegrable _ _)
    fun s hs => mul_le_mul_of_nonneg_left (hhk s hs) (Real.exp_pos _).le

/-- **Drift of the filter**: if `|h − c| ≤ B` on `[0, t]` (`ω, t ≥ 0`), then
`|z(t) − c| ≤ |z₀ − c| + ω t B`. -/
@[tmio T, powerlib_foundation] theorem abs_lagFilter_sub_const_le {ω z₀ t c B : ℝ} (hω : 0 ≤ ω)
    (ht : 0 ≤ t) {h : ℝ → ℝ} (hh : Continuous h) (hB : ∀ s ∈ Icc 0 t, |h s - c| ≤ B) :
    |lagFilter ω z₀ h t - c| ≤ |z₀ - c| + ω * t * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, ht⟩)
  have hc : lagFilter ω c (fun _ => c) t = c := by rw [lagFilter_const]; ring
  have hint : ∀ f : ℝ → ℝ, Continuous f →
      IntervalIntegrable (fun s => Real.exp (ω * s) * f s) MeasureTheory.volume 0 t :=
    fun f hf => (by fun_prop : Continuous fun s => Real.exp (ω * s) * f s).intervalIntegrable _ _
  have hsplit : lagFilter ω z₀ h t - c = Real.exp (-(ω * t)) * (z₀ - c) +
      Real.exp (-(ω * t)) * (ω * ∫ s in (0 : ℝ)..t, Real.exp (ω * s) * (h s - c)) := by
    have e : ∫ s in (0 : ℝ)..t, Real.exp (ω * s) * (h s - c) =
        (∫ s in (0 : ℝ)..t, Real.exp (ω * s) * h s) - ∫ s in (0 : ℝ)..t, Real.exp (ω * s) * c := by
      rw [← intervalIntegral.integral_sub (hint h hh) (hint _ continuous_const)]
      congr 1; funext s; ring
    have key : lagFilter ω z₀ h t - lagFilter ω c (fun _ => c) t =
        Real.exp (-(ω * t)) * (z₀ - c) +
          Real.exp (-(ω * t)) * (ω * ∫ s in (0 : ℝ)..t, Real.exp (ω * s) * (h s - c)) := by
      simp only [lagFilter]; rw [e]; ring
    rwa [hc] at key
  have hJ : |∫ s in (0 : ℝ)..t, Real.exp (ω * s) * (h s - c)| ≤ Real.exp (ω * t) * t * B := by
    rw [← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (C := Real.exp (ω * t) * B) (f := fun s => Real.exp (ω * s) * (h s - c)) fun s hs => by
        rw [uIoc_of_le ht] at hs
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hω))
          (hB s ⟨hs.1.le, hs.2⟩) (abs_nonneg _) (Real.exp_pos _).le
    rw [sub_zero, abs_of_nonneg ht] at this
    linarith
  rw [hsplit]
  have he : Real.exp (-(ω * t)) * Real.exp (ω * t) = 1 := by rw [← Real.exp_add]; simp
  have he1 : Real.exp (-(ω * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc |Real.exp (-(ω * t)) * (z₀ - c) + Real.exp (-(ω * t)) *
        (ω * ∫ s in (0 : ℝ)..t, Real.exp (ω * s) * (h s - c))|
      ≤ Real.exp (-(ω * t)) * |z₀ - c| + Real.exp (-(ω * t)) *
          (ω * |∫ s in (0 : ℝ)..t, Real.exp (ω * s) * (h s - c)|) := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hω]
    _ ≤ 1 * |z₀ - c| + Real.exp (-(ω * t)) * (ω * (Real.exp (ω * t) * t * B)) := by
        gcongr
    _ = |z₀ - c| + ω * t * B := by
        have : Real.exp (-(ω * t)) * (ω * (Real.exp (ω * t) * t * B)) =
            (Real.exp (-(ω * t)) * Real.exp (ω * t)) * (ω * t * B) := by ring
        rw [this, he]; ring

end powerlib.Dynamics
