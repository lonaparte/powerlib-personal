import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The first-order lag filter driven by a signal, and estimates for tracking paths

Generic calculus for constructing controlled paths that follow a reference: the explicit solution
of the scalar lag filter `ż = ω (h − z)` driven by a continuous signal `h`, its lag bound for a
Lipschitz signal, a quadratic estimate for the action of a perturbed control, a quartic bump with
vanishing value and slope at both ends of `[0, 1]`, and two elementary bounds (a sine increment
near a point where `cos < 0`, a lower bound for `∫₀¹ e^{ωs} t²(1 − t)²`).

Scope.
* Real-valued functions of a real variable; no engineering import, no model family. The filter is
  the scalar, constant-coefficient case written in closed form (the matrix variation-of-constants
  formula with the Peano–Baker transition matrix is `theorem/Dynamics/VariationOfConstants.lean`).
* The statements are about given functions (`h`, `f`, `w`); no solution concept or behaviour is
  defined here.

Source: the variation-of-constants formula for `ż = ω(h − z)` (any ODE text, e.g. Hespanha,
*Linear Systems Theory*, Ch. 5); used by `theorem/GridTiedConverter/GFM/Noise/EscapeExponent.lean`
for the fast-filter limit of the escape exponent.

Results.
* `lagFilter ω z₀ h t = e^{−ωt}(z₀ + ω ∫₀ᵗ e^{ωs} h(s) ds)`: `hasDerivAt_lagFilter`
  (`ż = ω(h − z)` for continuous `h`), `lagFilter_zero`, `abs_lagFilter_sub_le`
  (`|z(t) − h(t)| ≤ |z₀ − h(0)| + 2G/ω` on `[0, T]` when `h` is `G`-Lipschitz there, `ω > 0`).
* `integral_sq_add_le`: `½∫₀ᵀ (f + w/σ)² ≤ ½∫₀ᵀ f² + T (U E/|σ| + E²/σ²)` for `|f| ≤ U`,
  `|w| ≤ E`.
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

end powerlib.Dynamics
