import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import theorem.Dynamics.State

/-! # Pendulum energies (foundation)

An energy of the form `1 − cos θ + W`, the pendulum potential of an angle coordinate `θ` plus a
remainder `W` in the other state coordinates, is the Lyapunov function of the undamped PLL
witnesses of the grid-following families (`theorem/GFL/RatePLL.lean`,
`theorem/GFL/PowerLoop/QuasiStatic.lean`, `theorem/GFL/DCLink/FourState.lean`). This module proves
once that such an energy has a strict minimum at the selected point on the strip `|θ| < 2π`, when
the remainder dominates a positive multiple of the squared distance in the other coordinates.

Scope.
* Static real analysis on `State n = EuclideanSpace ℝ (Fin n)`, any dimension `n`: an angle
  coordinate `i`, a point `c` with `c i = 0`, and a real remainder `w` bounded below by
  `a (‖y − c‖² − (y i)²)` with `a > 0` (the squared distance from `y` to `c` in the coordinates
  other than `i`). No field, no behavioural sentence and no model family is fixed here.

Source: the energy method for the pendulum (Khalil, *Nonlinear Systems*, 3rd ed., §4.1);
`theorem/PhasePlane/Pendulum.lean` treats the planar pendulum with the potential `ω₀²(1 − cos θ)`.

Results.
* `pendulumEnergy_pos`: `1 − cos (y i) + w > 0` at every `y ≠ c` with `|y i| < 2π`.

Family and connection conclusions.
* None: the module states the inequality once for arbitrary dimensions; model modules use it to
  discharge the positivity of a Lyapunov function inside their connection proofs.
-/

namespace powerlib.Dynamics

/-- A pendulum energy is positive away from its minimum. With the angle coordinate `i` of the point
`c` at zero, the energy `1 − cos (y i) + w` is positive at every state `y ≠ c` on the strip
`|y i| < 2π` whose remainder `w` dominates a positive multiple `a` of the squared distance from `y`
to `c` in the other coordinates, `‖y − c‖² − (y i)²`. -/
@[tmio T, powerlib_foundation] theorem pendulumEnergy_pos {n : ℕ} (i : Fin n) {c y : State n} {a w : ℝ}
    (ha : 0 < a) (hc : c i = 0) (hw : a * (‖y - c‖ ^ 2 - y i ^ 2) ≤ w)
    (hy : |y i| < 2 * Real.pi) (hne : y ≠ c) : 0 < 1 - Real.cos (y i) + w := by
  have hi : y i ^ 2 ≤ ‖y - c‖ ^ 2 := by
    have h := PiLp.norm_apply_le (y - c) i
    rw [PiLp.sub_apply, hc, sub_zero, Real.norm_eq_abs] at h
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  by_cases h0 : y i = 0
  · have hpos : 0 < ‖y - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    rw [h0] at hw ⊢
    rw [Real.cos_zero]
    nlinarith [mul_pos ha (pow_pos hpos 2)]
  · have hcos : Real.cos (y i) < 1 := lt_of_le_of_ne (Real.cos_le_one _) fun h =>
      h0 ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [neg_abs_le (y i)])
        (by linarith [le_abs_self (y i)])).mp h)
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hi)]

end powerlib.Dynamics
