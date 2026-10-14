import dependencies.Mathlib
import theorem.Attributes

/-! # Tikhonov's theorem: corrections of the uniform `O(ε)` claim and of the boundary layer

Two counterexamples to statements of the Tikhonov note, with the corrected statements proved on
a scalar test system.

Model boundary.
* Test system (continuous time, scalar): slow `ẋ = 0`, fast `ε ẏ = -y`, so `g(x, y) = -y`, slow
  manifold `h ≡ 0`, boundary-layer matrix `-1` (exponentially attracting).
* Solution notion: a fast solution for the parameter `ε` is a global-in-time function
  `y : ℝ → ℝ` with `∀ t, HasDerivAt y (-(y t) / ε) t` (the fast state of `ε ẏ = -y`); it is
  written out in each statement that uses it.
* Scalar linear test systems that exhibit the logical errors; no general Tikhonov theorem is
  claimed here (the linear stability theorem is in `theorem/SingularPerturbation/Linear.lean`,
  the regular `O(ε)` estimate in `theorem/SingularPerturbation/Regular.lean`).

Source: work-sync theory/T-tikhonov.md §1.1 (main statement, boundary-layer system),
§1.3 (initial-layer correction); theory/T-singular-perturbation.md §1.5.

Results.
* `fastSolution_exp`, `fastSolution_eq` — every fast solution is `y(t) = y(0) e^{-t/ε}`.
* `tikhonov_uniform_claim_false` — the uniform `O(ε)` claim fails at `t = 0` (Correction 1).
* `fastSolution_le_after_layer` — for `t ≥ t_b > 0`, `|y(t) - h| ≤ (|y(0)| / t_b) ε`.
* `mixed_boundary_layer_tendsto`, `mixed_boundary_layer_not_tendsto_zero` — the note's mixed
  boundary-layer equation converges to `x̄`, not to `0` (Correction 2).
* `shifted_boundary_layer`, `shifted_boundary_layer_tendsto_zero` — `ỹ = y - h(x̄)` solves
  `dỹ/dτ = g(x̄, ỹ + h(x̄))`, and for `g(x̄, y) = x̄ - y` it decays to `0`.

Corrections.
* Correction 1 (T-tikhonov §1.1 main statement, also T-singular-perturbation §1.5):
  "`‖y(t) - h(x_s(t))‖ = O(ε)` on all of `[0, t_f]`" is false whenever `y(0) ≠ h(x(0))`: it
  already fails at `t = 0` (`tikhonov_uniform_claim_false`). Correct statement (formalized for
  the test system): every solution is `y(t) = y(0) e^{-t/ε}` and for `t ≥ t_b > 0`,
  `|y(t) - h| ≤ (|y(0)| / t_b) ε`, i.e. `O(ε)` uniformly only away from the initial layer;
  on the whole interval the boundary-layer term `y_b(t/ε)` must be added (here exactly).
* Correction 2 (T-tikhonov §1.1, boundary-layer system): the note writes
  `dy_b/dτ = g(x̄, y_b)` with `y_b(0) = y₀ - h(x₀)` and matching condition `y_b → 0`, mixing
  the original coordinate `y` (in `g`) with the shifted one `y - h` (in the initial value and
  limit). For `g(x̄, y) = x̄ - y` (`h(x̄) = x̄`), solutions of the written equation converge to
  `x̄`, not to `0` (`mixed_boundary_layer_tendsto`). Correct form: `ỹ = y - h(x̄)` satisfies
  `dỹ/dτ = g(x̄, ỹ + h(x̄))`, `ỹ(0) = y₀ - h(x₀)`, and then `ỹ → 0`.
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Set Filter Topology

/-- Solutions of `u' = -r (u - c)` are `c + (u(0) - c) e^{-r t}`. -/
@[powerlib_foundation] theorem linear_relaxation_eq {u : ℝ → ℝ} {r c : ℝ}
    (hu : ∀ t, HasDerivAt u (-r * (u t - c)) t) (t : ℝ) :
    u t = c + (u 0 - c) * Real.exp (-(r * t)) := by
  let w : ℝ → ℝ := fun s => (u s - c) * Real.exp (r * s)
  have hw : ∀ s, HasDerivAt w 0 s := by
    intro s
    have h1 := (hu s).sub_const c
    have h2 := ((hasDerivAt_id' s).const_mul r).exp
    exact (h1.mul h2).congr_deriv (by ring)
  have hconst : w t = w 0 := is_const_of_deriv_eq_zero (fun s => (hw s).differentiableAt)
    (fun s => (hw s).deriv) t 0
  simp only [w, mul_zero, Real.exp_zero, mul_one] at hconst
  have he : Real.exp (r * t) * Real.exp (-(r * t)) = 1 := by
    rw [← Real.exp_add]; simp
  calc u t = c + (u t - c) * (Real.exp (r * t) * Real.exp (-(r * t))) := by rw [he]; ring
    _ = c + (u 0 - c) * Real.exp (-(r * t)) := by rw [← hconst]; ring

/-! ## Correction 1: no uniform `O(ε)` bound up to `t = 0` -/

/-- `y₀ e^{-t/ε}` is a fast solution: it solves the fast equation `ε ẏ = -y` at every time. -/
@[powerlib_foundation] theorem fastSolution_exp (ε y₀ : ℝ) :
    ∀ t, HasDerivAt (fun t => y₀ * Real.exp (-(t / ε))) (-(y₀ * Real.exp (-(t / ε))) / ε) t := by
  intro t
  have h1 : HasDerivAt (fun x => -(x / ε)) (-(1 / ε)) t := ((hasDerivAt_id' t).div_const ε).neg
  exact (h1.exp.const_mul y₀).congr_deriv (by ring)

/-- Every fast solution (`∀ t, HasDerivAt y (-(y t) / ε) t`, the fast state of `ε ẏ = -y`) is
`y(0) e^{-t/ε}`. -/
@[powerlib_foundation] theorem fastSolution_eq {ε : ℝ} {y : ℝ → ℝ}
    (hy : ∀ t, HasDerivAt y (-(y t) / ε) t) (t : ℝ) : y t = y 0 * Real.exp (-(t / ε)) := by
  have h := linear_relaxation_eq (u := y) (r := 1 / ε) (c := 0)
    (fun s => (hy s).congr_deriv (by ring)) t
  rw [h]
  field_simp
  ring_nf

/-- The claim "`|y(t) - h(x_s(t))| ≤ C ε` on `[0, T]` for all small `ε`" is false for the
initial value `y(0) = 1` (here `h ≡ 0`): `y` ranges over the fast solutions of `ε ẏ = -y`,
`∀ t, HasDerivAt y (-(y t) / ε) t`. -/
@[powerlib_foundation] theorem tikhonov_uniform_claim_false {T : ℝ} (hT : 0 ≤ T) :
    ¬ ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∀ y : ℝ → ℝ, (∀ t, HasDerivAt y (-(y t) / ε) t) →
      y 0 = 1 → ∀ t ∈ Icc 0 T, |y t - 0| ≤ C * ε := by
  rintro ⟨C, ε₀, hε₀, h⟩
  set ε := min (ε₀ / 2) (1 / (2 * (|C| + 1))) with hεdef
  have hpos : 0 < ε := lt_min (by linarith) (by positivity)
  have hlt : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hb := h ε ⟨hpos, hlt⟩ _ (fastSolution_exp ε 1) (by simp) 0 ⟨le_rfl, hT⟩
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one, sub_zero, abs_one] at hb
  have hCε : C * ε ≤ |C| * (1 / (2 * (|C| + 1))) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hpos.le).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg C))
  have : |C| * (1 / (2 * (|C| + 1))) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith [abs_nonneg C]
  linarith

/-- Corrected statement: outside the initial layer `[0, t_b)` the error is `O(ε)`:
`|y(t) - h| ≤ (|y(0)| / t_b) ε` for `t ≥ t_b > 0`, for every fast solution `y` of `ε ẏ = -y`
(`∀ t, HasDerivAt y (-(y t) / ε) t`). -/
@[powerlib_foundation] theorem fastSolution_le_after_layer {ε tb : ℝ} (hε : 0 < ε) (htb : 0 < tb)
    {y : ℝ → ℝ} (hy : ∀ t, HasDerivAt y (-(y t) / ε) t) {t : ℝ} (ht : tb ≤ t) :
    |y t - 0| ≤ |y 0| / tb * ε := by
  rw [sub_zero, fastSolution_eq hy t, abs_mul, Real.abs_exp]
  have htpos : 0 < t := lt_of_lt_of_le htb ht
  have hu : 0 < t / ε := div_pos htpos hε
  have hexp : Real.exp (-(t / ε)) ≤ ε / t := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (div_pos hε htpos), inv_div]
    linarith [Real.add_one_le_exp (t / ε)]
  have h2 : ε / t ≤ ε / tb := div_le_div_of_nonneg_left hε.le htb ht
  calc |y 0| * Real.exp (-(t / ε)) ≤ |y 0| * (ε / tb) :=
        mul_le_mul_of_nonneg_left (hexp.trans h2) (abs_nonneg _)
    _ = |y 0| / tb * ε := by ring

/-! ## Correction 2: boundary-layer coordinates -/

/-- The boundary-layer equation as written in the note, `dy_b/dτ = g(x̄, y_b)` with
`g(x̄, y) = x̄ - y`: every solution converges to `x̄` (the original-coordinate equilibrium
`h(x̄) = x̄`), not to `0`. -/
@[powerlib_foundation] theorem mixed_boundary_layer_tendsto {xbar : ℝ} {yb : ℝ → ℝ}
    (h : ∀ τ, HasDerivAt yb (xbar - yb τ) τ) : Tendsto yb atTop (𝓝 xbar) := by
  have heq : ∀ τ, yb τ = xbar + (yb 0 - xbar) * Real.exp (-(1 * τ)) := fun τ =>
    linear_relaxation_eq (r := 1) (c := xbar) (fun s => by convert h s using 1; ring) τ
  have hexp : Tendsto (fun τ : ℝ => Real.exp (-(1 * τ))) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero
  have := (hexp.const_mul (yb 0 - xbar)).const_add xbar
  simp only [mul_zero, add_zero] at this
  exact this.congr fun τ => (heq τ).symm

@[powerlib_foundation] theorem mixed_boundary_layer_not_tendsto_zero {xbar : ℝ} (hx : xbar ≠ 0)
    {yb : ℝ → ℝ} (h : ∀ τ, HasDerivAt yb (xbar - yb τ) τ) : ¬ Tendsto yb atTop (𝓝 0) :=
  fun h0 => hx (tendsto_nhds_unique (mixed_boundary_layer_tendsto h) h0)

/-- Correct shifted coordinates: if `y` solves the frozen fast system `dy/dτ = g(x̄, y)`, then
`ỹ = y - h(x̄)` solves `dỹ/dτ = g(x̄, ỹ + h(x̄))`. -/
@[powerlib_foundation] theorem shifted_boundary_layer {g : ℝ → ℝ → ℝ} {h : ℝ → ℝ} {xbar : ℝ}
    {y : ℝ → ℝ} (hy : ∀ τ, HasDerivAt y (g xbar (y τ)) τ) (τ : ℝ) :
    HasDerivAt (fun s => y s - h xbar) (g xbar ((y τ - h xbar) + h xbar)) τ := by
  simpa using (hy τ).sub_const (h xbar)

/-- In shifted coordinates the boundary layer of `g(x̄, y) = x̄ - y` decays to `0`. -/
@[powerlib_foundation] theorem shifted_boundary_layer_tendsto_zero {xbar : ℝ} {yt : ℝ → ℝ}
    (h : ∀ τ, HasDerivAt yt (xbar - (yt τ + xbar)) τ) : Tendsto yt atTop (𝓝 0) := by
  have h' : ∀ τ, HasDerivAt yt (0 - yt τ) τ := fun τ => by convert h τ using 1; ring
  exact mixed_boundary_layer_tendsto h'

end powerlib.SingularPerturbation
