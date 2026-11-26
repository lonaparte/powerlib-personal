import theorem.Dynamics.Lyapunov

/-! # The Lur'e–Postnikov integral of a saturation

The integral `Φ(u) = ∫₀ᵘ sat(s) ds` of the saturation `sat(s) = max a (min s b)` to an interval
`[a, b] ∋ 0`, in closed form, with its derivative and the bounds that make it a term of a
radially unbounded Lur'e–Postnikov (Popov) Lyapunov function.

Scope.
* Real functions of one real variable; the saturation interval `[a, b]` is arbitrary (`a ≤ b` for
  the derivative, `a ≤ 0 ≤ b` or `a < 0 < b` for the bounds). Static calculus: no dynamics, no
  model (foundation).

Source: V. M. Popov and A. I. Lur'e: the Lyapunov function `x'Px + q ∫₀^{c'x} φ(s) ds` for a
loop with a sector nonlinearity (H. K. Khalil, *Nonlinear Systems*, 3rd ed., §7.1, the proof of
the Popov criterion, Theorem 7.3); the closed form below is that integral for a saturation, built
from `(max t 0)²` (`Dynamics.hasDerivAt_sq_max_zero`, `theorem/Dynamics/Lyapunov.lean`).

Results.
* `satIntegral a b u = u²/2 − (u − b)₊²/2 − (a − u)₊²/2` (`(x)₊ = max x 0`): for `a ≤ b` it is
  `u²/2` on `[a, b]`, `b u − b²/2` above and `a u − a²/2` below.
* `hasDerivAt_satIntegral`: for `a ≤ b`, `Φ' = max a (min u b)`; `contDiff_satIntegral`: `Φ` is
  `C¹`; `satIntegral_zero`.
* `satIntegral_nonneg` (`a ≤ 0 ≤ b`), `satIntegral_pos` (`a < 0 < b`, `u ≠ 0`), and the linear
  lower bound `le_satIntegral`: `m |u| − m²/2 ≤ Φ(u)` for `0 ≤ m ≤ min b (−a)`, so `Φ` grows
  linearly at infinity.
-/

noncomputable section
namespace powerlib.Dynamics

/-- The integral of the saturation `max a (min s b)` from `0` to `u`, in closed form:
`u²/2 − (u − b)₊²/2 − (a − u)₊²/2`. -/
def satIntegral (a b u : ℝ) : ℝ := u ^ 2 / 2 - max (u - b) 0 ^ 2 / 2 - max (a - u) 0 ^ 2 / 2

/-- **The derivative of the saturation integral is the saturation** (`a ≤ b`). -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_satIntegral {a b : ℝ} (hab : a ≤ b) (u : ℝ) :
    HasDerivAt (satIntegral a b) (max a (min u b)) u := by
  have h1 := (hasDerivAt_sq_max_zero (u - b)).comp u ((hasDerivAt_id u).sub_const b)
  have h2 := (hasDerivAt_sq_max_zero (a - u)).comp u ((hasDerivAt_id u).const_sub a)
  have h := (((hasDerivAt_pow 2 u).div_const 2).sub (h1.div_const 2)).sub (h2.div_const 2)
  have heq : (2 : ℕ) * u ^ (2 - 1) / 2 - 2 * max (u - b) 0 * 1 / 2 -
      2 * max (a - u) 0 * (-1) / 2 = max a (min u b) := by
    rcases le_total u a with hua | hau
    · rw [max_eq_right (by linarith : u - b ≤ 0), max_eq_left (by linarith : 0 ≤ a - u),
        min_eq_left (by linarith : u ≤ b), max_eq_left hua]
      push_cast; ring
    · rcases le_total u b with hub | hbu
      · rw [max_eq_right (by linarith : u - b ≤ 0), max_eq_right (by linarith : a - u ≤ 0),
          min_eq_left hub, max_eq_right hau]
        push_cast; ring
      · rw [max_eq_left (by linarith : 0 ≤ u - b), max_eq_right (by linarith : a - u ≤ 0),
          min_eq_right hbu, max_eq_right hab]
        push_cast; ring
  rw [heq] at h
  exact h

/-- The saturation integral is `C¹` (`a ≤ b`): its derivative, the saturation, is continuous. -/
@[tmio T, powerlib_foundation] theorem contDiff_satIntegral {a b : ℝ} (hab : a ≤ b) :
    ContDiff ℝ 1 (satIntegral a b) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun u => (hasDerivAt_satIntegral hab u).differentiableAt, ?_⟩
  have h : deriv (satIntegral a b) = fun u => max a (min u b) :=
    funext fun u => (hasDerivAt_satIntegral hab u).deriv
  rw [h]
  exact continuous_const.max (continuous_id.min continuous_const)

/-- `Φ(0) = 0` (`a ≤ 0 ≤ b`). -/
@[tmio T, powerlib_foundation] theorem satIntegral_zero {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    satIntegral a b 0 = 0 := by
  simp [satIntegral, max_eq_right ha, hb]

/-- **Linear growth**: `m |u| − m²/2 ≤ Φ(u)` for `0 ≤ m ≤ b` and `m ≤ −a`. -/
@[tmio T, powerlib_foundation] theorem le_satIntegral {a b m : ℝ} (hm : 0 ≤ m) (hmb : m ≤ b)
    (hma : m ≤ -a) (u : ℝ) : m * |u| - m ^ 2 / 2 ≤ satIntegral a b u := by
  unfold satIntegral
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu, max_eq_right (by linarith : a - u ≤ 0)]
    rcases le_total u b with hub | hbu
    · rw [max_eq_right (by linarith : u - b ≤ 0)]
      nlinarith [sq_nonneg (u - m)]
    · rw [max_eq_left (by linarith : 0 ≤ u - b)]
      nlinarith [sq_nonneg (b - m)]
  · rw [abs_of_nonpos hu, max_eq_right (by linarith : u - b ≤ 0)]
    rcases le_total a u with hau | hua
    · rw [max_eq_right (by linarith : a - u ≤ 0)]
      nlinarith [sq_nonneg (u + m)]
    · rw [max_eq_left (by linarith : 0 ≤ a - u)]
      nlinarith [sq_nonneg (a + m)]

/-- `Φ ≥ 0` (`a ≤ 0 ≤ b`). -/
@[tmio T, powerlib_foundation] theorem satIntegral_nonneg {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (u : ℝ) : 0 ≤ satIntegral a b u := by
  have h := le_satIntegral le_rfl hb (by linarith) u (a := a)
  simpa using h

/-- `Φ(u) > 0` for `u ≠ 0` (`a < 0 < b`). -/
@[tmio T, powerlib_foundation] theorem satIntegral_pos {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {u : ℝ} (hu : u ≠ 0) : 0 < satIntegral a b u := by
  set m := min (min b (-a)) |u| with hm
  have hm0 : 0 < m := lt_min (lt_min hb (by linarith)) (abs_pos.mpr hu)
  have hmu : m ≤ |u| := min_le_right _ _
  have h := le_satIntegral hm0.le ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _)) u (a := a)
  nlinarith

end powerlib.Dynamics
