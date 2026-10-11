import theorem.Criteria.Hurwitz2

/-! # Jacobian and smoothness helpers for vector fields on `Dynamics.State n`

Foundation layer: calculus utilities only, no model is fixed here.

The linearization theorems (`Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian`,
`Criteria.locallyExponentiallyStable_of_jacobian_fin_two`, …) take a field
`f : Dynamics.State n → Dynamics.State n` (`EuclideanSpace ℝ (Fin n)`), the hypothesis
`ContDiff ℝ 1 f`, and the identification
`fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A`.
This module reduces both to the scalar component functions `fun y => f y i`:

* `hasFDerivAt_toEuclideanCLM_of_components` / `fderiv_eq_toEuclideanCLM_of_components`:
  if each component has derivative `L i` with `L i v = ∑ j, A i j * v j`, the Jacobian is `A`
  (any dimension; a planar version also exists in `theorem/PhasePlane/Planar.lean`).
* `hasFDerivAt_coord`, `contDiff_coord` (`fun_prop`): coordinates are smooth linear maps.
* `contDiff_of_components`: smoothness of `f` from smoothness of its components.
* `contDiff_field_mk_two_example`: a `fun_prop` demonstration for a planar field built from
  `Real.sin` / `Real.cos` (pendulum / swing / PLL shape); `fderiv_field_mk_two_example_zero`
  computes the Jacobian of such a field with the component helper.

Source: powerlib Phase 0, P0a (shared criteria interface for the work-sync formalization).
-/

noncomputable section
namespace powerlib.Criteria
open Matrix

variable {n : ℕ}

/-- The `i`-th coordinate of `Dynamics.State n` as a continuous linear functional. -/
def coord (i : Fin n) : Dynamics.State n →L[ℝ] ℝ := EuclideanSpace.proj i

@[simp, powerlib_foundation] theorem coord_apply (i : Fin n) (x : Dynamics.State n) :
    coord i x = x i := rfl

@[powerlib_foundation] theorem hasFDerivAt_coord (i : Fin n) (x : Dynamics.State n) :
    HasFDerivAt (fun y : Dynamics.State n => y i) (coord i) x :=
  (coord i).hasFDerivAt

@[fun_prop, powerlib_foundation] theorem contDiff_coord {k : WithTop ℕ∞} (i : Fin n) :
    ContDiff ℝ k (fun y : Dynamics.State n => y i) :=
  (coord i).contDiff

/-- Componentwise derivatives determine the Jacobian matrix (any dimension). -/
@[powerlib_foundation] theorem hasFDerivAt_toEuclideanCLM_of_components
    {f : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n}
    (A : Matrix (Fin n) (Fin n) ℝ) (L : Fin n → Dynamics.State n →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivAt (fun y => f y i) (L i) x)
    (hA : ∀ i (v : Dynamics.State n), L i v = ∑ j, A i j * v j) :
    HasFDerivAt f (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  convert hL i using 1
  ext v
  simp [hA, Matrix.mulVec, dotProduct]

@[powerlib_foundation] theorem fderiv_eq_toEuclideanCLM_of_components
    {f : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n}
    (A : Matrix (Fin n) (Fin n) ℝ) (L : Fin n → Dynamics.State n →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivAt (fun y => f y i) (L i) x)
    (hA : ∀ i (v : Dynamics.State n), L i v = ∑ j, A i j * v j) :
    fderiv ℝ f x = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A :=
  (hasFDerivAt_toEuclideanCLM_of_components A L hL hA).fderiv

/-- Smoothness of a field on `Dynamics.State n` from smoothness of its components. -/
@[powerlib_foundation] theorem contDiff_of_components {f : Dynamics.State n → Dynamics.State n}
    {k : WithTop ℕ∞} (h : ∀ i, ContDiff ℝ k (fun y => f y i)) : ContDiff ℝ k f :=
  contDiff_euclidean.2 h

/-- `fun_prop` demonstration: a planar field with trigonometric terms (the shape of a
pendulum, swing equation or reduced PLL in `(angle, rate)` coordinates) is smooth. -/
@[powerlib_foundation] theorem contDiff_field_mk_two_example (a b c d : ℝ) :
    ContDiff ℝ 1 (fun y : Dynamics.State 2 =>
      (WithLp.toLp 2 ![y 1, c - a * Real.sin (y 0) - b * y 1 + d * Real.cos (y 0)] :
        Dynamics.State 2)) := by
  apply contDiff_of_components
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- Worked use of `fderiv_eq_toEuclideanCLM_of_components`: the planar field
`(y₀, y₁) ↦ (y₁, -a sin y₀ - b y₁)` has Jacobian `!![0, 1; -a, -b]` at the origin. -/
@[powerlib_foundation] theorem fderiv_field_mk_two_example_zero (a b : ℝ) :
    fderiv ℝ (fun y : Dynamics.State 2 =>
        (WithLp.toLp 2 ![y 1, -a * Real.sin (y 0) - b * y 1] : Dynamics.State 2)) 0 =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![0, 1; -a, -b] := by
  refine fderiv_eq_toEuclideanCLM_of_components _ ![coord 1, (-a) • coord 0 - b • coord 1]
    ?_ ?_
  · intro i
    fin_cases i
    · simpa using hasFDerivAt_coord (1 : Fin 2) (0 : Dynamics.State 2)
    · have h := (((Real.hasDerivAt_sin _).comp_hasFDerivAt (0 : Dynamics.State 2)
        (hasFDerivAt_coord (0 : Fin 2) 0)).const_mul (-a)).sub
        ((hasFDerivAt_coord (1 : Fin 2) (0 : Dynamics.State 2)).const_mul b)
      convert h using 1
      · funext y
        simp
      · ext v
        simp
  · intro i v
    fin_cases i <;> simp [Fin.sum_univ_two]
    ring

end powerlib.Criteria
