import dependencies.Mathlib
import theorem.Attributes

/-! # The backward heat equation is ill-posed

Foundation layer (category B).

Source: work-sync `theory/T-pde-systems.md` §1.8.2 ("反向时间 … `u_t = −ν u_xx`，高频成分指数爆炸 ⇒
反向 ill-posed").

Model boundary: one space dimension, `x ∈ [0, π]`, homogeneous Dirichlet data, constant
diffusivity `ν > 0`, classical (smooth) solutions; the statement is about continuous dependence
on the initial data in the sup norm.

Hadamard's counterexample: `uₙ(x, t) = e^{νn²t} sin(nx)/n` solves the backward heat equation
`∂ₜu = −ν ∂ₓₓu` with `uₙ(0, t) = uₙ(π, t) = 0` (`backward_heat_solution`, `boundary_zero`). Its
initial data satisfy `|uₙ(x, 0)| ≤ 1/n → 0` (`initial_small`), yet for every `t > 0`,
`uₙ(π/(2n), t) = e^{νn²t}/n → ∞` (`blowup`): arbitrarily small initial data produce
arbitrarily large solutions after any positive time, so the solution does not depend
continuously on the data (`not_continuous_dependence`).
-/

noncomputable section
namespace powerlib.Line.Heat
open Real Filter Topology

/-- `uₙ(x, t) = e^{νn²t} sin(nx)/n`. -/
def hadamard (ν : ℝ) (n : ℕ) (x t : ℝ) : ℝ := Real.exp (ν * n ^ 2 * t) * Real.sin (n * x) / n

/-- `∂ₜ uₙ = νn² uₙ`. -/
@[powerlib_foundation] theorem hasDerivAt_t (ν : ℝ) (n : ℕ) (x t : ℝ) :
    HasDerivAt (fun τ => hadamard ν n x τ) (ν * n ^ 2 * hadamard ν n x t) t := by
  unfold hadamard
  have h := ((hasDerivAt_id' t).const_mul (ν * n ^ 2)).exp
  have h2 := (h.mul_const (Real.sin (n * x))).div_const (n : ℝ)
  convert h2 using 1
  ring

/-- `∂ₓ uₙ = e^{νn²t} cos(nx)`. -/
@[powerlib_foundation] theorem hasDerivAt_x (ν : ℝ) {n : ℕ} (hn : n ≠ 0) (x t : ℝ) :
    HasDerivAt (fun y => hadamard ν n y t) (Real.exp (ν * n ^ 2 * t) * Real.cos (n * x)) x := by
  unfold hadamard
  have h := ((hasDerivAt_id' x).const_mul (n : ℝ)).sin
  have h2 := (h.const_mul (Real.exp (ν * n ^ 2 * t))).div_const (n : ℝ)
  convert h2 using 1
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- `∂ₓₓ uₙ = −n² uₙ`. -/
@[powerlib_foundation] theorem hasDerivAt_xx (ν : ℝ) {n : ℕ} (hn : n ≠ 0) (x t : ℝ) :
    HasDerivAt (fun y => Real.exp (ν * n ^ 2 * t) * Real.cos (n * y))
      (-(n : ℝ) ^ 2 * hadamard ν n x t) x := by
  unfold hadamard
  have h := ((hasDerivAt_id' x).const_mul (n : ℝ)).cos
  have h2 := h.const_mul (Real.exp (ν * n ^ 2 * t))
  convert h2 using 1
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- `uₙ` solves the backward heat equation `∂ₜu = −ν ∂ₓₓu`. -/
@[powerlib_foundation] theorem backward_heat_solution (ν : ℝ) (n : ℕ) (x t : ℝ) :
    ν * n ^ 2 * hadamard ν n x t = -ν * (-(n : ℝ) ^ 2 * hadamard ν n x t) := by
  ring

/-- Homogeneous Dirichlet data on `[0, π]`. -/
@[powerlib_foundation] theorem boundary_zero (ν : ℝ) (n : ℕ) (t : ℝ) :
    hadamard ν n 0 t = 0 ∧ hadamard ν n π t = 0 := by
  unfold hadamard
  constructor
  · simp
  · rw [Real.sin_nat_mul_pi]; simp

/-- Small initial data: `|uₙ(x, 0)| ≤ 1/n`. -/
@[powerlib_foundation] theorem initial_small (ν : ℝ) {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    |hadamard ν n x 0| ≤ 1 / n := by
  unfold hadamard
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [mul_zero, Real.exp_zero, one_mul, abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hpos.le

/-- Blow-up at every positive time: `uₙ(π/(2n), t) = e^{νn²t}/n → ∞`. -/
@[powerlib_foundation] theorem blowup {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    Tendsto (fun n : ℕ => hadamard ν n (π / (2 * n)) t) atTop atTop := by
  have hval : ∀ n : ℕ, n ≠ 0 → hadamard ν n (π / (2 * n)) t = Real.exp (ν * n ^ 2 * t) / n := by
    intro n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    unfold hadamard
    rw [show (n : ℝ) * (π / (2 * n)) = π / 2 by field_simp, Real.sin_pi_div_two, mul_one]
  -- `e^{c n²}/n ≥ e^{c n}/n ≥ c` eventually is too weak; use `e^{y} ≥ y²/2`.
  have hc : 0 < ν * t := mul_pos hν ht
  have hlow : ∀ n : ℕ, 1 ≤ n → ν * t * n / 2 ≤ Real.exp (ν * n ^ 2 * t) / n := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hnpos]
    have h1 := Real.add_one_le_exp (ν * n ^ 2 * t)
    have h2 : ν * t * n / 2 * n ≤ ν * n ^ 2 * t + 1 := by nlinarith
    linarith
  have htend : Tendsto (fun n : ℕ => ν * t * n / 2) atTop atTop := by
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    exact (this.const_mul_atTop (half_pos hc)).congr fun n => by ring
  refine tendsto_atTop_mono' atTop ?_ htend
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [hval n (by omega)]
  exact hlow n hn

/-- **Ill-posedness**: no estimate `sup |u(·, t)| ≤ C sup |u(·, 0)|` holds for the backward heat
equation, at any `t > 0` and any constant `C`. -/
@[powerlib_foundation] theorem not_continuous_dependence {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (C : ℝ) : ∃ n : ℕ, n ≠ 0 ∧ C * (1 / n) < hadamard ν n (π / (2 * n)) t := by
  have h := blowup hν ht
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_atTop.mp h) (|C| + 1))
  refine ⟨max N 1, by omega, ?_⟩
  have hge := hN (max N 1) (le_max_left _ _)
  have hn1 : (1 : ℝ) ≤ (max N 1 : ℕ) := by exact_mod_cast le_max_right N 1
  have : C * (1 / ((max N 1 : ℕ) : ℝ)) ≤ |C| := by
    calc C * (1 / ((max N 1 : ℕ) : ℝ)) ≤ |C| * (1 / ((max N 1 : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_right (le_abs_self C); positivity
    _ ≤ |C| * 1 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          rw [div_le_one (by positivity)]; exact hn1
    _ = |C| := mul_one _
  linarith

end powerlib.Line.Heat
