import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Potential barrier of the tilted washboard `V(θ) = −c θ − A cos(θ + φ)` (foundation)

`V` is an antiderivative of `−(c − A sin(θ + φ))`; for the reduced GFL-PLL model
(`theorem/VSC/Reduced2D.lean`) it is the potential part of the Hamiltonian with `c = c₀`.
For `A > 0`, `|c| < A`, write `s = c/A`, `ψ_s = arcsin s` and
* `θ_s = ψ_s − φ` (stable zero, `cos(θ_s + φ) > 0`),
* `θ_u⁺ = π − ψ_s − φ`, `θ_u⁻ = −π − ψ_s − φ` (the two neighbouring saddles).

Results.
* `potential_sub_eq_neg_integral` : `V(θ₂) − V(θ₁) = −∫_{θ₁}^{θ₂} (c − A sin(t + φ)) dt`.
* `zero_mem_Ioo_iff` : `θ_s` is the only zero strictly between the two saddles.
* `barrierUp_eq` : `V(θ_u⁺) − V(θ_s) = 2√(A² − c²) − 2c·arccos(c/A)`;
  `barrierDown_eq` : `V(θ_u⁻) − V(θ_s) = 2√(A² − c²) + 2c·arccos(−c/A)`;
  `barrierDown_sub_barrierUp` : their difference is the tilt per period `2πc`.
* `min_barrier_eq` : the lower of the two barriers is
  `ΔV = 2√(A² − c²) − 2|c|·arccos(|c|/A)` — the closed form proposed in the previous review round is
  correct (as the *minimum* over the two neighbouring saddles).
* `barrierUp_pos`, `barrierDown_pos` : both barriers are positive.
* Fold asymptotics, with `u = arccos(|c|/A)`: `ΔV = A (2 sin u − 2u cos u)`,
  `(2/3)u³ − u⁵/15 ≤ 2 sin u − 2u cos u ≤ (2/3)u³` (`washboard_bounds`); the restoring slope at the
  stable point is `g = √(A² − c²)` with `g² = δ (2A − δ)`, `δ = A − |c|` (`slope_sq_eq`); and
  `(u²/2)(1 − u²/24)² ≤ δ/A ≤ u²/2` (`foldDistance_bounds`). Hence `g ∝ δ^{1/2}` and
  `ΔV ∝ δ^{3/2}` near the fold, with explicit two-sided bounds.

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/equilibria-and-bifurcation.md`
§5, §7 (basin depth = potential barrier), `sn-critical-scaling.md` §4 (exponents `g ∝ δ^{1/2}`,
`ΔH ∝ δ^{3/2}`; the note obtains them from a numerical log–log fit and a normal-form argument).
-/

noncomputable section
namespace powerlib.Potential.Barrier
open Real Set

/-- Tilted-washboard potential `V(θ) = −c θ − A cos(θ + φ)`. -/
def washboard (c A φ θ : ℝ) : ℝ := -(c * θ) - A * cos (θ + φ)

/-- `F(u) = 2 sin u − 2u cos u` (barrier per unit amplitude). -/
def barrierShape (u : ℝ) : ℝ := 2 * sin u - 2 * u * cos u

section
variable {c A φ : ℝ}

@[powerlib_foundation] theorem hasDerivAt_washboard (θ : ℝ) :
    HasDerivAt (washboard c A φ) (-(c - A * sin (θ + φ))) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => θ + φ) 1 θ := (hasDerivAt_id θ).add_const _
  have h2 := ((hasDerivAt_id θ).const_mul c).neg.sub ((h1.cos).const_mul A)
  convert h2 using 1
  · funext x; simp [washboard]
  · ring

/-- `V(θ₂) − V(θ₁) = −∫_{θ₁}^{θ₂} (c − A sin(t + φ)) dt`. -/
@[powerlib_foundation] theorem potential_sub_eq_neg_integral (θ₁ θ₂ : ℝ) :
    washboard c A φ θ₂ - washboard c A φ θ₁ =
      -∫ t in θ₁..θ₂, (c - A * sin (t + φ)) := by
  have hint : IntervalIntegrable (fun t => -(c - A * sin (t + φ))) MeasureTheory.volume θ₁ θ₂ :=
    (by fun_prop : Continuous fun t => -(c - A * sin (t + φ))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_washboard x) hint]

/-- Stable zero `θ_s = arcsin(c/A) − φ` (not reduced to a window). -/
def thetaS (c A φ : ℝ) : ℝ := arcsin (c / A) - φ
/-- Neighbouring saddle above, `θ_u⁺ = π − arcsin(c/A) − φ`. -/
def thetaUp (c A φ : ℝ) : ℝ := π - arcsin (c / A) - φ
/-- Neighbouring saddle below, `θ_u⁻ = −π − arcsin(c/A) − φ`. -/
def thetaDown (c A φ : ℝ) : ℝ := -π - arcsin (c / A) - φ

/-- Barrier towards the saddle above. -/
def barrierUp (c A φ : ℝ) : ℝ := washboard c A φ (thetaUp c A φ) - washboard c A φ (thetaS c A φ)
/-- Barrier towards the saddle below. -/
def barrierDown (c A φ : ℝ) : ℝ :=
  washboard c A φ (thetaDown c A φ) - washboard c A φ (thetaS c A φ)

@[powerlib_foundation] private lemma abs_div_le (hA : 0 < A) (hc : |c| ≤ A) : |c / A| ≤ 1 := by
  rw [abs_div, abs_of_pos hA, div_le_one hA]; exact hc

@[powerlib_foundation] theorem thetaS_zero (hA : 0 < A) (hc : |c| ≤ A) :
    c - A * sin (thetaS c A φ + φ) = 0 := by
  have hs := abs_div_le hA hc
  rw [thetaS, sub_add_cancel, sin_arcsin (abs_le.mp hs).1 (abs_le.mp hs).2]
  field_simp; ring

@[powerlib_foundation] theorem thetaUp_zero (hA : 0 < A) (hc : |c| ≤ A) :
    c - A * sin (thetaUp c A φ + φ) = 0 := by
  have hs := abs_div_le hA hc
  rw [thetaUp, sub_add_cancel, sin_pi_sub, sin_arcsin (abs_le.mp hs).1 (abs_le.mp hs).2]
  field_simp; ring

@[powerlib_foundation] theorem thetaDown_zero (hA : 0 < A) (hc : |c| ≤ A) :
    c - A * sin (thetaDown c A φ + φ) = 0 := by
  have hs := abs_div_le hA hc
  rw [thetaDown, sub_add_cancel, show -π - arcsin (c / A) = -(π + arcsin (c / A)) by ring,
    sin_neg, sin_add, sin_pi, cos_pi, sin_arcsin (abs_le.mp hs).1 (abs_le.mp hs).2]
  field_simp; ring

@[powerlib_foundation] private lemma A_sqrt (hA : 0 < A) :
    A * √(1 - (c / A) ^ 2) = √(A ^ 2 - c ^ 2) := by
  rw [← Real.sqrt_sq hA.le, ← Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA.le]
  congr 1
  field_simp

/-- `V(θ_u⁺) − V(θ_s) = 2√(A² − c²) − 2c arccos(c/A)`. -/
@[powerlib_foundation] theorem barrierUp_eq (hA : 0 < A) :
    barrierUp c A φ = 2 * √(A ^ 2 - c ^ 2) - 2 * c * arccos (c / A) := by
  have h := A_sqrt (c := c) hA
  rw [barrierUp, washboard, washboard, thetaUp, thetaS, sub_add_cancel, sub_add_cancel,
    cos_pi_sub, cos_arcsin, arccos_eq_pi_div_two_sub_arcsin]
  linear_combination 2 * h

/-- `V(θ_u⁻) − V(θ_s) = 2√(A² − c²) + 2c arccos(−c/A)`. -/
@[powerlib_foundation] theorem barrierDown_eq (hA : 0 < A) :
    barrierDown c A φ = 2 * √(A ^ 2 - c ^ 2) + 2 * c * arccos (-c / A) := by
  have h := A_sqrt (c := c) hA
  rw [barrierDown, washboard, washboard, thetaDown, thetaS, sub_add_cancel, sub_add_cancel,
    show -π - arcsin (c / A) = -(π + arcsin (c / A)) by ring, cos_neg, cos_add, cos_pi, sin_pi,
    cos_arcsin, neg_div, arccos_neg, arccos_eq_pi_div_two_sub_arcsin]
  linear_combination 2 * h

/-- The two barriers differ by the tilt over one period: `ΔV⁻ − ΔV⁺ = 2πc`. -/
@[powerlib_foundation] theorem barrierDown_sub_barrierUp (hA : 0 < A) :
    barrierDown c A φ - barrierUp c A φ = 2 * π * c := by
  rw [barrierUp_eq hA, barrierDown_eq hA, neg_div, arccos_neg]; ring

/-- The proposed closed form is the lower of the two barriers:
`min(ΔV⁺, ΔV⁻) = 2√(A² − c²) − 2|c| arccos(|c|/A)`. -/
@[powerlib_foundation] theorem min_barrier_eq (hA : 0 < A) :
    min (barrierUp c A φ) (barrierDown c A φ) =
      2 * √(A ^ 2 - c ^ 2) - 2 * |c| * arccos (|c| / A) := by
  have hd := barrierDown_sub_barrierUp (c := c) (φ := φ) hA
  rcases le_or_gt 0 c with hc | hc
  · rw [min_eq_left (by nlinarith [pi_pos]), barrierUp_eq hA, abs_of_nonneg hc]
  · rw [min_eq_right (by nlinarith [pi_pos]), barrierDown_eq hA, abs_of_neg hc, neg_div]
    ring

/-- `θ_s` is the only zero strictly between the two neighbouring saddles. -/
@[powerlib_foundation] theorem zero_mem_Ioo_iff (hA : 0 < A) (hc : |c| < A) {θ : ℝ}
    (hθ : θ ∈ Ioo (thetaDown c A φ) (thetaUp c A φ)) :
    c - A * sin (θ + φ) = 0 ↔ θ = thetaS c A φ := by
  constructor
  · intro hz
    have hs : |c / A| < 1 := by rw [abs_div, abs_of_pos hA, div_lt_one hA]; exact hc
    have h1 : arcsin (c / A) < π / 2 := arcsin_lt_pi_div_two.mpr (abs_lt.mp hs).2
    have h2 : -(π / 2) < arcsin (c / A) := neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp hs).1
    have hsin : sin (θ + φ) = sin (arcsin (c / A)) := by
      rw [sin_arcsin (abs_lt.mp hs).1.le (abs_lt.mp hs).2.le]; field_simp; linarith
    obtain ⟨hlo, hhi⟩ := hθ
    simp only [thetaDown, thetaUp] at hlo hhi
    have hpi := pi_pos
    obtain ⟨k, hk | hk⟩ := Real.sin_eq_sin_iff.mp hsin
    · -- arcsin s = 2kπ + θ + φ
      have hk0 : (k : ℝ) = 0 := by
        have a1 : (-1 : ℝ) < k := by nlinarith
        have a2 : (k : ℝ) < 1 := by nlinarith
        have b1 : (-1 : ℤ) < k := by exact_mod_cast a1
        have b2 : k < (1 : ℤ) := by exact_mod_cast a2
        have : k = 0 := by omega
        simp [this]
      rw [thetaS]; rw [hk0] at hk; linarith
    · exfalso
      have a1 : (-1 : ℝ) < k := by nlinarith
      have a2 : (k : ℝ) < 0 := by nlinarith
      have b1 : (-1 : ℤ) < k := by exact_mod_cast a1
      have b2 : k < (0 : ℤ) := by exact_mod_cast a2
      omega
  · rintro rfl; exact thetaS_zero hA hc.le

/-! ### Positivity and fold asymptotics -/

@[powerlib_foundation] theorem hasDerivAt_barrierShape (u : ℝ) :
    HasDerivAt barrierShape (2 * u * sin u) u := by
  have h := (((hasDerivAt_sin u).const_mul 2).sub
    (((hasDerivAt_id u).const_mul 2).mul (hasDerivAt_cos u)))
  convert h using 1
  · funext x; simp [barrierShape]
  · simp

@[powerlib_foundation] theorem barrierShape_pos {u : ℝ} (hu0 : 0 < u) (hu : u ≤ π) :
    0 < barrierShape u := by
  have hmono : StrictMonoOn barrierShape (Icc 0 π) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 π)
    · exact (fun x _ => (hasDerivAt_barrierShape x).continuousAt.continuousWithinAt)
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_barrierShape x).deriv]
      have := sin_pos_of_pos_of_lt_pi hx.1 hx.2
      nlinarith [hx.1]
  have h0 : barrierShape 0 = 0 := by simp [barrierShape]
  have := hmono ⟨le_refl 0, pi_pos.le⟩ ⟨hu0.le, hu⟩ hu0
  rwa [h0] at this

@[powerlib_foundation] theorem barrierUp_eq_shape (hA : 0 < A) (hc : |c| ≤ A) :
    barrierUp c A φ = A * barrierShape (arccos (c / A)) := by
  have hs := abs_div_le hA hc
  rw [barrierUp_eq hA, barrierShape, sin_arccos, cos_arccos (abs_le.mp hs).1 (abs_le.mp hs).2,
    ← A_sqrt hA]
  field_simp

@[powerlib_foundation] theorem barrierDown_eq_shape (hA : 0 < A) (hc : |c| ≤ A) :
    barrierDown c A φ = A * barrierShape (arccos (-c / A)) := by
  have hs : |-c / A| ≤ 1 := by rw [neg_div, abs_neg]; exact abs_div_le hA hc
  rw [barrierDown_eq hA, barrierShape, sin_arccos, cos_arccos (abs_le.mp hs).1 (abs_le.mp hs).2,
    neg_div, neg_sq, ← A_sqrt hA]
  field_simp
  ring

/-- Both barriers are positive inside the existence region. -/
@[powerlib_foundation] theorem barrierUp_pos (hA : 0 < A) (hc : |c| < A) : 0 < barrierUp c A φ := by
  have hs : |c / A| < 1 := by rw [abs_div, abs_of_pos hA, div_lt_one hA]; exact hc
  rw [barrierUp_eq_shape hA hc.le]
  exact mul_pos hA (barrierShape_pos (arccos_pos.mpr (abs_lt.mp hs).2) (arccos_le_pi _))

@[powerlib_foundation] theorem barrierDown_pos (hA : 0 < A) (hc : |c| < A) :
    0 < barrierDown c A φ := by
  have hs : |-c / A| < 1 := by
    rw [neg_div, abs_neg, abs_div, abs_of_pos hA, div_lt_one hA]; exact hc
  rw [barrierDown_eq_shape hA hc.le]
  exact mul_pos hA (barrierShape_pos (arccos_pos.mpr (abs_lt.mp hs).2) (arccos_le_pi _))

/-- The minimal barrier in terms of `u = arccos(|c|/A)`: `ΔV = A · (2 sin u − 2u cos u)`. -/
@[powerlib_foundation] theorem min_barrier_eq_shape (hA : 0 < A) (hc : |c| ≤ A) :
    min (barrierUp c A φ) (barrierDown c A φ) = A * barrierShape (arccos (|c| / A)) := by
  have hs : |(|c|) / A| ≤ 1 := by rw [abs_div, abs_abs, abs_of_pos hA, div_le_one hA]; exact hc
  have e : √(A ^ 2 - c ^ 2) = A * √(1 - (|c| / A) ^ 2) := by rw [A_sqrt (c := |c|) hA, sq_abs]
  have hdiv : A * (|c| / A) = |c| := by field_simp
  rw [min_barrier_eq hA, barrierShape, sin_arccos, cos_arccos (abs_le.mp hs).1 (abs_le.mp hs).2, e]
  linear_combination (2 * arccos (|c| / A)) * hdiv

/-- Two-sided bounds of the barrier shape near the fold:
`(2/3)u³ − u⁵/15 ≤ 2 sin u − 2u cos u ≤ (2/3)u³` for `u ≥ 0`. -/
@[powerlib_foundation] theorem washboard_bounds {u : ℝ} (hu : 0 ≤ u) :
    2 / 3 * u ^ 3 - u ^ 5 / 15 ≤ barrierShape u ∧ barrierShape u ≤ 2 / 3 * u ^ 3 := by
  have h0 : barrierShape 0 = 0 := by simp [barrierShape]
  constructor
  · have hd : ∀ x, HasDerivAt (fun x => barrierShape x - (2 / 3 * x ^ 3 - x ^ 5 / 15))
        (2 * x * sin x - (2 / 3 * (3 * x ^ 2) - 5 * x ^ 4 / 15)) x := by
      intro x
      have h := (hasDerivAt_barrierShape x).sub
        (((hasDerivAt_pow 3 x).const_mul (2 / 3)).sub ((hasDerivAt_pow 5 x).div_const 15))
      exact h.congr_deriv (by push_cast; ring)
    have hG : MonotoneOn (fun x => barrierShape x - (2 / 3 * x ^ 3 - x ^ 5 / 15)) (Ici 0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun x _ => (hd x).continuousAt.continuousWithinAt)
        (fun x _ => (hd x).hasDerivWithinAt) ?_
      intro x hx
      rw [interior_Ici] at hx
      have hx' : (0 : ℝ) < x := hx
      have := mul_lt_mul_of_pos_left (sin_gt_sub_cube hx') (by linarith : (0 : ℝ) < 2 * x)
      nlinarith
    have := hG (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
    simp only [h0] at this
    norm_num at this
    linarith
  · have hd : ∀ x, HasDerivAt (fun x => 2 / 3 * x ^ 3 - barrierShape x)
        (2 / 3 * (3 * x ^ 2) - 2 * x * sin x) x := by
      intro x
      have h := ((hasDerivAt_pow 3 x).const_mul (2 / 3)).sub (hasDerivAt_barrierShape x)
      exact h.congr_deriv (by push_cast; ring)
    have hG : MonotoneOn (fun x => 2 / 3 * x ^ 3 - barrierShape x) (Ici 0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun x _ => (hd x).continuousAt.continuousWithinAt)
        (fun x _ => (hd x).hasDerivWithinAt) ?_
      intro x hx
      rw [interior_Ici] at hx
      have hx' : (0 : ℝ) < x := hx
      have := mul_le_mul_of_nonneg_left (sin_le hx'.le) (by linarith : (0 : ℝ) ≤ 2 * x)
      nlinarith
    have := hG (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
    simp only [h0] at this
    norm_num at this
    linarith

/-- Restoring slope at the stable point versus the fold distance `δ = A − |c|`:
`g = √(A² − c²)` satisfies `g² = δ (2A − δ)`. -/
@[powerlib_foundation] theorem slope_sq_eq (hc : |c| ≤ A) :
    √(A ^ 2 - c ^ 2) ^ 2 = (A - |c|) * (2 * A - (A - |c|)) := by
  have h : 0 ≤ A ^ 2 - c ^ 2 := by
    rw [← sq_abs c]; nlinarith [abs_nonneg c]
  rw [Real.sq_sqrt h, ← sq_abs c]; ring

/-- Fold distance versus `u = arccos(|c|/A)`: `(u²/2)(1 − u²/24)² ≤ δ/A ≤ u²/2`. -/
@[powerlib_foundation] theorem foldDistance_bounds (hA : 0 < A) (hc : |c| ≤ A) :
    let u := arccos (|c| / A)
    u ^ 2 / 2 * (1 - u ^ 2 / 24) ^ 2 ≤ (A - |c|) / A ∧ (A - |c|) / A ≤ u ^ 2 / 2 := by
  intro u
  have hs : |(|c|) / A| ≤ 1 := by rw [abs_div, abs_abs, abs_of_pos hA, div_le_one hA]; exact hc
  have hcos : cos u = |c| / A := cos_arccos (abs_le.mp hs).1 (abs_le.mp hs).2
  have hδ : (A - |c|) / A = 1 - cos u := by rw [hcos]; field_simp
  rw [hδ]
  have hu0 : 0 ≤ u := arccos_nonneg _
  constructor
  · have h2 : 1 - cos u = 2 * sin (u / 2) ^ 2 := by
      have h4 := cos_two_mul (u / 2)
      have h3 := sin_sq_add_cos_sq (u / 2)
      rw [show 2 * (u / 2) = u by ring] at h4
      linarith
    rw [h2]
    rcases hu0.eq_or_lt with h | h
    · rw [← h]; simp
    · have hsg := sin_gt_sub_cube (half_pos h)
      have hu1 : u ≤ π / 2 := arccos_le_pi_div_two.mpr (div_nonneg (abs_nonneg c) hA.le)
      have hu2 : u ≤ 2 := by linarith [pi_le_four]
      have hp : 0 ≤ u / 2 - (u / 2) ^ 3 / 6 := by
        have hu3 : (u / 2) ^ 2 ≤ 1 := by nlinarith
        nlinarith
      have : (u / 2 - (u / 2) ^ 3 / 6) ^ 2 ≤ sin (u / 2) ^ 2 :=
        pow_le_pow_left₀ hp hsg.le 2
      nlinarith
  · linarith [one_sub_sq_div_two_le_cos (x := u)]

end

end powerlib.Potential.Barrier
