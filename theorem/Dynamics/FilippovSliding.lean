import theorem.NormalForm.Scalar
import theorem.PhasePlane.Planar
import Mathlib.Analysis.ODE.ExistUnique

/-! # Sliding motions on a switching hyperplane: Filippov's equivalent control

A field equal to `f₊` on one side of the hyperplane `Σ = {⟪n, x⟫ = β}` and to `f₋` on the other
is extended on `Σ` by Filippov's convex hull: a solution lying on `Σ` has its velocities in the
segment `[f₋(x), f₊(x)]`. The velocity of that segment tangent to `Σ` is the sliding vector field
`f_s = α f₊ + (1 − α) f₋` with Filippov's (Utkin's) equivalent control
`α = ⟪n, f₋⟫ / (⟪n, f₋⟫ − ⟪n, f₊⟫)`.

Scope.
* Generic: a real inner product space `E` (complete for the existence theorem; the plane
  `State 2` for the reduction to the switching line), a normal `n`, a level `β`, two pieces
  `f₊, f₋ : E → E` (no smoothness except where stated). Continuous time; curves `x : ℝ → E` and
  their derivatives are written out in the statements, no solution notion is defined. The
  sentences of the library are applied only to the reduced scalar field on the switching line.
* A Filippov solution on `Σ` is a curve on `Σ` with `ẋ(t) ∈ [f₋(x(t)), f₊(x(t))]` where it is
  differentiable; an absolutely continuous solution is differentiable almost everywhere, and the
  statements hold at every point of differentiability.
* Excluded: curved switching surfaces, more than two pieces, the reaching phase off `Σ`,
  uniqueness of Filippov solutions, the stability of a pseudo-equilibrium in the whole space.
  Off `Σ` the local sentences are those of one piece (`Dynamics.holds_congr_nhds`,
  `theorem/Dynamics/PiecewiseAffine.lean`).
* Read by the circular current limiter of `theorem/GridTiedConverter/GFM/Limiting/Switching.lean`,
  whose switching lines are degenerate (both modes have the normal component `ω`): there the
  equivalent control is undefined and the only motions on the surface are pseudo-equilibria.

Source: A. F. Filippov, *Differential Equations with Discontinuous Righthand Sides* (Kluwer,
1988), §2.4 (motion along a surface of discontinuity, the convex combination tangent to it);
V. I. Utkin, *Sliding Modes in Control and Optimization* (Springer, 1992), §2.3 (equivalent
control); work-sync `theory/T-current-limiting.md` §1.9 (Filippov solutions of the limiter's
mode switch).

Results.
* Closed form and tangency (static): `smul_slidingField`
  (`(⟪n, f₋⟫ − ⟪n, f₊⟫) f_s = ⟪n, f₋⟫ f₊ − ⟪n, f₊⟫ f₋`), `inner_slidingField` (`⟪n, f_s⟫ = 0`
  where the normal components differ).
* Filippov's segment (static): `slidingField_mem_segment` — in the closed sliding region
  `⟪n, f₊⟫ ⟪n, f₋⟫ ≤ 0` (normal components different) `f_s` lies in `[f₋, f₊]`;
  `eq_slidingField_of_mem_segment` — it is the only tangent velocity of the segment;
  `mul_inner_nonpos_of_mem_segment` — a tangent velocity exists only in the closed sliding
  region; `inner_eq_of_mem_segment` — where both pieces have the same normal component every
  velocity of the segment has it (a degenerate surface is crossed, except where that component
  vanishes).
* Solutions on the surface: `inner_eq_zero_of_mem_surface` (a curve on `Σ` on an open time set
  has tangent velocities) and `hasDerivAt_eq_slidingField` (a Filippov solution on `Σ` moves with
  the sliding field and stays in the closed sliding region).
* Existence: `exists_slidingSolution` — for `C¹` pieces at a strict sliding point
  (`⟪n, f₊⟫ ⟪n, f₋⟫ < 0`) there is a solution of `ẋ = f_s(x)` through it that stays on `Σ` and in
  the strict sliding region, with velocities in Filippov's segment: a sliding solution.
* The plane (`State 2`, switching line `x₀ + y n^⊥`): `eq_smul_perp` (a tangent vector is a
  multiple of `n^⊥`), the reduced sliding field `lineField` on the line, `hasDerivAt_line` (a
  solution of `ẏ = G(y)` is a sliding motion) and `hasDerivAt_coord` (a sliding motion has its line
  coordinate solving `ẏ = G(y)`); stability on the surface:
  `locallyExponentiallyStable_lift_lineField_iff` — for `C¹` pieces a point of the line where the
  normal components differ is a locally exponentially stable point of the sliding motion exactly
  when it is a pseudo-equilibrium `G(y*) = 0` with `G'(y*) < 0`.
-/

noncomputable section
namespace powerlib.Dynamics.Sliding

open Set Filter Topology
open scoped RealInnerProductSpace
open powerlib.Dynamics (State)

section Hyperplane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Filippov's equivalent control on a hyperplane with normal `n`: the weight
`α = ⟪n, f₋⟫ / (⟪n, f₋⟫ − ⟪n, f₊⟫)` of `f₊` in the velocity tangent to the hyperplane. -/
def eqControl (n : E) (fp fm : E → E) (x : E) : ℝ :=
  ⟪n, fm x⟫ / (⟪n, fm x⟫ - ⟪n, fp x⟫)

/-- The sliding vector field `α f₊ + (1 − α) f₋`. -/
def slidingField (n : E) (fp fm : E → E) (x : E) : E :=
  eqControl n fp fm x • fp x + (1 - eqControl n fp fm x) • fm x

variable {n : E} {fp fm : E → E} {x : E}

/-- **Closed form of the sliding field**:
`(⟪n, f₋⟫ − ⟪n, f₊⟫) f_s = ⟪n, f₋⟫ f₊ − ⟪n, f₊⟫ f₋`. -/
@[tmio T, powerlib_foundation] theorem smul_slidingField (hne : ⟪n, fm x⟫ ≠ ⟪n, fp x⟫) :
    (⟪n, fm x⟫ - ⟪n, fp x⟫) • slidingField n fp fm x = ⟪n, fm x⟫ • fp x - ⟪n, fp x⟫ • fm x := by
  have hd : ⟪n, fm x⟫ - ⟪n, fp x⟫ ≠ 0 := sub_ne_zero.mpr hne
  have h1 : (⟪n, fm x⟫ - ⟪n, fp x⟫) * eqControl n fp fm x = ⟪n, fm x⟫ := by
    rw [eqControl]; field_simp
  have h2 : (⟪n, fm x⟫ - ⟪n, fp x⟫) * (1 - eqControl n fp fm x) = -⟪n, fp x⟫ := by
    rw [mul_sub, h1]; ring
  rw [slidingField, smul_add, smul_smul, smul_smul, h1, h2, neg_smul, ← sub_eq_add_neg]

/-- **Tangency**: where the normal components of the two pieces differ, the sliding field is
tangent to the hyperplane. -/
@[tmio T, powerlib_foundation] theorem inner_slidingField (hne : ⟪n, fm x⟫ ≠ ⟪n, fp x⟫) :
    ⟪n, slidingField n fp fm x⟫ = 0 := by
  have hd : ⟪n, fm x⟫ - ⟪n, fp x⟫ ≠ 0 := sub_ne_zero.mpr hne
  have h := congrArg (fun v => ⟪n, v⟫) (smul_slidingField hne)
  simp only [inner_smul_right, inner_sub_right] at h
  have h0 : (⟪n, fm x⟫ - ⟪n, fp x⟫) * ⟪n, slidingField n fp fm x⟫ = 0 := by
    rw [h]; ring
  exact (mul_eq_zero.mp h0).resolve_left hd

/-- **The sliding field is a Filippov velocity**: in the closed sliding region
`⟪n, f₊⟫ ⟪n, f₋⟫ ≤ 0`, with different normal components, the equivalent control lies in `[0, 1]`
and the sliding field in the segment `[f₋, f₊]`. -/
@[tmio T, powerlib_foundation] theorem slidingField_mem_segment
    (hs : ⟪n, fp x⟫ * ⟪n, fm x⟫ ≤ 0) (hne : ⟪n, fm x⟫ ≠ ⟪n, fp x⟫) :
    slidingField n fp fm x ∈ segment ℝ (fm x) (fp x) := by
  have hα : 0 ≤ eqControl n fp fm x ∧ eqControl n fp fm x ≤ 1 := by
    rw [eqControl]
    rcases lt_or_gt_of_ne hne with h | h
    · have hd : ⟪n, fm x⟫ - ⟪n, fp x⟫ < 0 := sub_neg.mpr h
      have hm : ⟪n, fm x⟫ ≤ 0 := by nlinarith
      constructor
      · exact div_nonneg_of_nonpos hm hd.le
      · rw [div_le_one_of_neg hd]; nlinarith
    · have hd : 0 < ⟪n, fm x⟫ - ⟪n, fp x⟫ := sub_pos.mpr h
      have hm : 0 ≤ ⟪n, fm x⟫ := by nlinarith
      constructor
      · exact div_nonneg hm hd.le
      · rw [div_le_one hd]; nlinarith
  refine ⟨1 - eqControl n fp fm x, eqControl n fp fm x, by linarith, hα.1, by ring, ?_⟩
  rw [slidingField, add_comm]

/-- **Uniqueness of the equivalent control**: where the normal components differ, the sliding
field is the only velocity of Filippov's segment tangent to the hyperplane. -/
@[tmio T, powerlib_foundation] theorem eq_slidingField_of_mem_segment {v : E}
    (hv : v ∈ segment ℝ (fm x) (fp x)) (hvn : ⟪n, v⟫ = 0) (hne : ⟪n, fm x⟫ ≠ ⟪n, fp x⟫) :
    v = slidingField n fp fm x := by
  obtain ⟨a, b, -, -, hab, rfl⟩ := hv
  have hd : ⟪n, fm x⟫ - ⟪n, fp x⟫ ≠ 0 := sub_ne_zero.mpr hne
  simp only [inner_add_right, inner_smul_right] at hvn
  have hb : b = eqControl n fp fm x := by
    rw [eqControl, eq_div_iff hd]
    have ha : a = 1 - b := by linarith
    rw [ha] at hvn
    linarith
  have ha : a = 1 - eqControl n fp fm x := by linarith
  rw [slidingField, ha, hb, add_comm]

/-- **Tangent Filippov velocities only in the closed sliding region**: if a velocity of the
segment `[f₋, f₊]` is tangent to the hyperplane, the normal components have opposite signs (or
one vanishes). -/
@[tmio T, powerlib_foundation] theorem mul_inner_nonpos_of_mem_segment {v : E}
    (hv : v ∈ segment ℝ (fm x) (fp x)) (hvn : ⟪n, v⟫ = 0) :
    ⟪n, fp x⟫ * ⟪n, fm x⟫ ≤ 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hv
  simp only [inner_add_right, inner_smul_right] at hvn
  by_contra h
  push Not at h
  have h1 : 0 ≤ a * ⟪n, fm x⟫ ^ 2 := by positivity
  have h2 : 0 ≤ b * (⟪n, fp x⟫ * ⟪n, fm x⟫) := mul_nonneg hb h.le
  have h3 : a * ⟪n, fm x⟫ ^ 2 + b * (⟪n, fp x⟫ * ⟪n, fm x⟫) = 0 := by
    have := congrArg (· * ⟪n, fm x⟫) hvn
    simp only [zero_mul] at this
    linarith [this]
  have hb0 : b * (⟪n, fp x⟫ * ⟪n, fm x⟫) = 0 := by linarith
  have hb0' : b = 0 := (mul_eq_zero.mp hb0).resolve_right h.ne'
  have hm : ⟪n, fm x⟫ ≠ 0 := fun h0 => by simp [h0] at h
  have : a = 1 := by linarith
  rw [this, hb0'] at hvn
  simp only [one_mul, zero_mul, add_zero] at hvn
  exact hm hvn

/-- **A degenerate surface**: where both pieces have the same normal component, every velocity of
Filippov's segment has that normal component. -/
@[tmio T, powerlib_foundation] theorem inner_eq_of_mem_segment {v : E}
    (hv : v ∈ segment ℝ (fm x) (fp x)) (heq : ⟪n, fm x⟫ = ⟪n, fp x⟫) :
    ⟪n, v⟫ = ⟪n, fp x⟫ := by
  obtain ⟨a, b, -, -, hab, rfl⟩ := hv
  simp only [inner_add_right, inner_smul_right, heq]
  rw [← add_mul, hab, one_mul]

/-- A curve lying on the hyperplane `⟪n, x⟫ = β` on an open time set has tangent velocities
there. -/
@[tmio T, powerlib_foundation] theorem inner_eq_zero_of_mem_surface {β : ℝ} {c : ℝ → E}
    {I : Set ℝ} (hI : IsOpen I) (hon : ∀ s ∈ I, ⟪n, c s⟫ = β) {t : ℝ} (ht : t ∈ I) {v : E}
    (hv : HasDerivAt c v t) : ⟪n, v⟫ = 0 := by
  have h1 : HasDerivAt (fun s => ⟪n, c s⟫) ⟪n, v⟫ t := by
    have := (hasDerivAt_const t n).inner ℝ hv
    simpa using this
  have h2 : HasDerivAt (fun s => ⟪n, c s⟫) 0 t :=
    (hasDerivAt_const t β).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hI.mem_nhds ht) hon)
  exact h1.unique h2

/-- **Filippov solutions on the surface follow the sliding field.** A curve on the hyperplane on
an open time set whose velocity at `t` lies in Filippov's segment stays in the closed sliding
region there, and its velocity is the sliding field wherever the normal components differ. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_eq_slidingField {β : ℝ} {c : ℝ → E}
    {I : Set ℝ} (hI : IsOpen I) (hon : ∀ s ∈ I, ⟪n, c s⟫ = β) {t : ℝ} (ht : t ∈ I) {v : E}
    (hv : HasDerivAt c v t) (hseg : v ∈ segment ℝ (fm (c t)) (fp (c t))) :
    ⟪n, fp (c t)⟫ * ⟪n, fm (c t)⟫ ≤ 0 ∧
      (⟪n, fm (c t)⟫ ≠ ⟪n, fp (c t)⟫ → v = slidingField n fp fm (c t)) := by
  have h0 := inner_eq_zero_of_mem_surface hI hon ht hv
  exact ⟨mul_inner_nonpos_of_mem_segment hseg h0,
    fun hne => eq_slidingField_of_mem_segment hseg h0 hne⟩

/-- The sliding field is `C¹` at a point where `C¹` pieces have different normal components. -/
@[tmio T, powerlib_foundation] theorem contDiffAt_slidingField (hp : ContDiffAt ℝ 1 fp x)
    (hm : ContDiffAt ℝ 1 fm x) (hne : ⟪n, fm x⟫ ≠ ⟪n, fp x⟫) :
    ContDiffAt ℝ 1 (slidingField n fp fm) x := by
  have hσp : ContDiffAt ℝ 1 (fun y => ⟪n, fp y⟫) x := contDiffAt_const.inner ℝ hp
  have hσm : ContDiffAt ℝ 1 (fun y => ⟪n, fm y⟫) x := contDiffAt_const.inner ℝ hm
  have hα : ContDiffAt ℝ 1 (eqControl n fp fm) x :=
    hσm.div (hσm.sub hσp) (sub_ne_zero.mpr hne)
  exact (hα.smul hp).add ((contDiffAt_const.sub hα).smul hm)

/-- **Existence of sliding solutions.** At a strict sliding point `x₀` of the hyperplane
(`⟪n, f₊⟫ ⟪n, f₋⟫ < 0`) of `C¹` pieces, a solution of `ẋ = f_s(x)` through `x₀` stays on the
hyperplane and in the strict sliding region on an open time interval, with velocities in
Filippov's segment `[f₋, f₊]`: a sliding solution of the Filippov inclusion. -/
@[tmio T, powerlib_foundation] theorem exists_slidingSolution [CompleteSpace E] {x₀ : E} {β : ℝ}
    (hp : ContDiffAt ℝ 1 fp x₀) (hm : ContDiffAt ℝ 1 fm x₀) (hx₀ : ⟪n, x₀⟫ = β)
    (hs : ⟪n, fp x₀⟫ * ⟪n, fm x₀⟫ < 0) :
    ∃ c : ℝ → E, c 0 = x₀ ∧ ∃ ε > 0, ∀ t ∈ Ioo (-ε) ε, ⟪n, c t⟫ = β ∧
      HasDerivAt c (slidingField n fp fm (c t)) t ∧
      slidingField n fp fm (c t) ∈ segment ℝ (fm (c t)) (fp (c t)) ∧
      ⟪n, fp (c t)⟫ * ⟪n, fm (c t)⟫ < 0 := by
  have hne : ∀ {y : E}, ⟪n, fp y⟫ * ⟪n, fm y⟫ < 0 → ⟪n, fm y⟫ ≠ ⟪n, fp y⟫ := fun {y} h he => by
    rw [he] at h; nlinarith
  obtain ⟨c, hc0, ε, hε, hc⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (contDiffAt_slidingField hp hm (hne hs)) 0
  have hU : {y : E | ⟪n, fp y⟫ * ⟪n, fm y⟫ < 0} ∈ 𝓝 x₀ :=
    ((contDiffAt_const.inner ℝ hp).continuousAt.mul
      (contDiffAt_const.inner ℝ hm).continuousAt).preimage_mem_nhds (Iio_mem_nhds hs)
  have hcc : ContinuousAt c 0 := (hc 0 ⟨by linarith, by linarith⟩).continuousAt
  have hpre : c ⁻¹' {y : E | ⟪n, fp y⟫ * ⟪n, fm y⟫ < 0} ∈ 𝓝 (0 : ℝ) :=
    hcc.preimage_mem_nhds (hc0 ▸ hU)
  obtain ⟨ε', hε', hball⟩ := Metric.mem_nhds_iff.mp hpre
  set ε₁ := min ε ε' with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε hε'
  have hsub : Ioo (-ε₁) ε₁ ⊆ Ioo (0 - ε) (0 + ε) := by
    rw [zero_sub, zero_add]
    exact Ioo_subset_Ioo (by simp [hε₁]) (min_le_left _ _)
  have hreg : ∀ t ∈ Ioo (-ε₁) ε₁, ⟪n, fp (c t)⟫ * ⟪n, fm (c t)⟫ < 0 := by
    intro t ht
    have : t ∈ Metric.ball (0 : ℝ) ε' := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1, min_le_right ε ε'], by linarith [ht.2, min_le_right ε ε']⟩
    exact hball this
  have hder : ∀ t ∈ Ioo (-ε₁) ε₁, HasDerivAt (fun s => ⟪n, c s⟫) 0 t := by
    intro t ht
    have := (hasDerivAt_const t n).inner ℝ (hc t (hsub ht))
    simpa [inner_slidingField (hne (hreg t ht))] using this
  have hconst : ∀ t ∈ Ioo (-ε₁) ε₁, ⟪n, c t⟫ = β := by
    intro t ht
    have h0 : (0 : ℝ) ∈ Ioo (-ε₁) ε₁ := ⟨by linarith, hε₁0⟩
    rw [← hx₀, ← hc0]
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s hs => (hder s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hder s hs).deriv) ht h0
  exact ⟨c, hc0, ε₁, hε₁0, fun t ht => ⟨hconst t ht, hc t (hsub ht),
    slidingField_mem_segment (hreg t ht).le (hne (hreg t ht)), hreg t ht⟩⟩

end Hyperplane

/-! ## The plane: the sliding motion on the switching line -/

section Plane

/-- The normal turned by a quarter turn, `n^⊥ = (−n₁, n₀)`: the direction of the switching line. -/
def perp (n : State 2) : State 2 := PhasePlane.mk (-(n 1)) (n 0)

@[tmio T, powerlib_foundation] theorem inner_perp (n : State 2) : ⟪n, perp n⟫ = 0 := by
  simp [perp, PhasePlane.mk, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- In the plane a vector orthogonal to `n ≠ 0` is the multiple `(⟪n^⊥, v⟫/‖n‖²) n^⊥`. -/
@[tmio T, powerlib_foundation] theorem eq_smul_perp {n v : State 2} (hn : n ≠ 0)
    (hv : ⟪n, v⟫ = 0) : v = (⟪perp n, v⟫ / ‖n‖ ^ 2) • perp n := by
  have hn2 : ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp [sq_abs]
  have hpos : 0 < n 0 ^ 2 + n 1 ^ 2 := by
    rw [← hn2]; exact pow_pos (norm_pos_iff.mpr hn) 2
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial] at hv
  ext i
  fin_cases i
  · simp [perp, PhasePlane.mk, PiLp.inner_apply, Fin.sum_univ_two, hn2]
    field_simp
    linear_combination (n 0) * hv
  · simp [perp, PhasePlane.mk, PiLp.inner_apply, Fin.sum_univ_two, hn2]
    field_simp
    linear_combination (n 1) * hv

variable (n : State 2) (fp fm : State 2 → State 2) (x₀ : State 2)

/-- The sliding motion in the coordinate `y` of the line `x₀ + y n^⊥`:
`G(y) = ⟪n^⊥, f_s(x₀ + y n^⊥)⟫ / ‖n‖²`. -/
def lineField (y : ℝ) : ℝ :=
  ⟪perp n, slidingField n fp fm (x₀ + y • perp n)⟫ / ‖n‖ ^ 2

variable {n fp fm x₀}

/-- **Reduced solutions are sliding motions.** If `ẏ = G(y)` at `t` and the normal components
differ at `x₀ + y(t) n^⊥`, the curve `x₀ + y n^⊥` (on the hyperplane through `x₀`) moves with the
sliding field at `t`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_line (hn : n ≠ 0) {y : ℝ → ℝ} {t : ℝ}
    (hy : HasDerivAt y (lineField n fp fm x₀ (y t)) t)
    (hne : ⟪n, fm (x₀ + y t • perp n)⟫ ≠ ⟪n, fp (x₀ + y t • perp n)⟫) :
    HasDerivAt (fun s => x₀ + y s • perp n) (slidingField n fp fm (x₀ + y t • perp n)) t ∧
      ⟪n, x₀ + y t • perp n⟫ = ⟪n, x₀⟫ := by
  refine ⟨?_, by simp [inner_add_right, inner_smul_right, inner_perp]⟩
  have h := (hy.smul_const (perp n)).const_add x₀
  convert h using 1
  exact eq_smul_perp hn (inner_slidingField hne)

/-- **Sliding motions have reduced coordinates.** A point `c(t)` of the hyperplane through `x₀`
is `x₀ + y n^⊥` with `y = ⟪n^⊥, c − x₀⟫/‖n‖²`; where the curve moves with the sliding field,
`ẏ = G(y)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_coord (hn : n ≠ 0) {c : ℝ → State 2} {t : ℝ}
    (hon : ⟪n, c t⟫ = ⟪n, x₀⟫) (hc : HasDerivAt c (slidingField n fp fm (c t)) t) :
    c t = x₀ + (⟪perp n, c t - x₀⟫ / ‖n‖ ^ 2) • perp n ∧
      HasDerivAt (fun s => ⟪perp n, c s - x₀⟫ / ‖n‖ ^ 2)
        (lineField n fp fm x₀ (⟪perp n, c t - x₀⟫ / ‖n‖ ^ 2)) t := by
  have hct : c t = x₀ + (⟪perp n, c t - x₀⟫ / ‖n‖ ^ 2) • perp n := by
    have h0 : ⟪n, c t - x₀⟫ = 0 := by rw [inner_sub_right, hon, sub_self]
    rw [← eq_smul_perp hn h0, add_sub_cancel]
  refine ⟨hct, ?_⟩
  have hd : HasDerivAt (fun s => ⟪perp n, c s - x₀⟫ / ‖n‖ ^ 2)
      (⟪perp n, slidingField n fp fm (c t)⟫ / ‖n‖ ^ 2) t := by
    have := ((hasDerivAt_const t (perp n)).inner ℝ (hc.sub_const x₀)).div_const (‖n‖ ^ 2)
    simpa using this
  rw [lineField, ← hct]
  exact hd

/-- **Stability on the surface.** For `C¹` pieces and a point `x₀ + y* n^⊥` of the line where the
normal components differ, the sliding motion `ẏ = G(y)` is locally exponentially stable at `y*`
exactly when `y*` is a pseudo-equilibrium, `G(y*) = 0`, with `G'(y*) < 0`. -/
@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_lift_lineField_iff
    (hp : ContDiff ℝ 1 fp) (hm : ContDiff ℝ 1 fm) {y : ℝ}
    (hne : ⟪n, fm (x₀ + y • perp n)⟫ ≠ ⟪n, fp (x₀ + y • perp n)⟫) :
    LocallyExponentiallyStable (NormalForm.lift (lineField n fp fm x₀)) (NormalForm.embed y) ↔
      lineField n fp fm x₀ y = 0 ∧ deriv (lineField n fp fm x₀) y < 0 := by
  set U : Set ℝ := {z | ⟪n, fm (x₀ + z • perp n)⟫ ≠ ⟪n, fp (x₀ + z • perp n)⟫} with hUdef
  have hline : Continuous fun z : ℝ => x₀ + z • perp n := by fun_prop
  have hU : IsOpen U :=
    isOpen_ne_fun ((continuous_const.inner (hm.continuous.comp hline)))
      ((continuous_const.inner (hp.continuous.comp hline)))
  have hG : ∀ z ∈ U, ContDiffAt ℝ 1 (lineField n fp fm x₀) z := by
    intro z hz
    have hl : ContDiffAt ℝ 1 (fun z : ℝ => x₀ + z • perp n) z := by fun_prop
    have hs := (contDiffAt_slidingField hp.contDiffAt hm.contDiffAt hz).comp z hl
    exact (contDiffAt_const.inner ℝ hs).div_const _
  set V : Set (State 1) := (fun w : State 1 => w 0) ⁻¹' U with hVdef
  have hcoord : Continuous fun w : State 1 => w 0 := PiLp.continuous_apply 2 _ 0
  have hV : IsOpen V := hU.preimage hcoord
  have hyV : NormalForm.embed y ∈ V := by
    show NormalForm.embed y 0 ∈ U
    rw [NormalForm.embed_apply]
    exact hne
  have hC : ContDiffOn ℝ 1 (NormalForm.lift (lineField n fp fm x₀)) V := by
    intro w hw
    rw [NormalForm.lift_eq_comp]
    have hc0 : ContDiffAt ℝ 1 (fun w : State 1 => w 0) w := by fun_prop
    exact ((NormalForm.embedCLM.contDiff.contDiffAt).comp w
      ((hG _ hw).comp w hc0)).contDiffWithinAt
  have hd : DifferentiableAt ℝ (lineField n fp fm x₀) (NormalForm.embed y 0) := by
    simpa using (hG y hne).differentiableAt one_ne_zero
  have hJac := NormalForm.fderiv_lift (g := lineField n fp fm x₀) (x := NormalForm.embed y) hd
  simp only [NormalForm.embed_apply] at hJac
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local hV hyV _ hC hJac,
    NormalForm.lift_eq_zero_iff, Linear.isHurwitz_one_iff]

end Plane

end powerlib.Dynamics.Sliding
