import theorem.Criteria.Hurwitz2
import theorem.Dynamics.State

/-! # Planar state-space helpers

Foundation layer used by the phase-plane and planar normal-form modules.

The planar state space is `State 2 = EuclideanSpace ℝ (Fin 2)` with coordinates `x 0`, `x 1`.
`mk a b` is the state with `x 0 = a`, `x 1 = b`. The helper `hasFDerivAt_of_components`
identifies the Fréchet derivative of a planar field with `Matrix.toEuclideanCLM A` from
componentwise derivatives, which is the shape required by the linearization theorems
`powerlib.Flow.locallyExponentiallyStable_of_isHurwitz_jacobian`,
`powerlib.Criteria.locallyExponentiallyStable_of_jacobian_fin_two`, etc.
These are calculus utilities only; no model is fixed here (no model family, all results
public foundation support).
-/

noncomputable section
namespace powerlib.PhasePlane
open Set Filter Topology Matrix
open powerlib.Dynamics (State)

/-- The planar state with coordinates `(a, b)`. -/
def mk (a b : ℝ) : State 2 := WithLp.toLp 2 ![a, b]

@[simp, powerlib_foundation] theorem mk_apply_zero (a b : ℝ) : mk a b 0 = a := rfl
@[simp, powerlib_foundation] theorem mk_apply_one (a b : ℝ) : mk a b 1 = b := rfl

@[simp, powerlib_foundation] theorem mk_coords (x : State 2) : mk (x 0) (x 1) = x := by
  ext i; fin_cases i <;> rfl

@[powerlib_foundation] theorem mk_eq_iff {a b c d : ℝ} : mk a b = mk c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun x : State 2 => x 0) h,
      by simpa using congrArg (fun x : State 2 => x 1) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp, powerlib_foundation] theorem mk_zero : mk 0 0 = 0 := by
  ext i; fin_cases i <;> rfl

@[powerlib_foundation] theorem mk_eq_zero_iff {a b : ℝ} : mk a b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [← mk_zero, mk_eq_iff]

@[powerlib_foundation] theorem ext_iff' {x y : State 2} : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 := by
  rw [← mk_coords x, ← mk_coords y, mk_eq_iff]; simp

@[powerlib_foundation] theorem eq_zero_iff {x : State 2} : x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  rw [ext_iff' (y := 0)]; simp

@[powerlib_foundation] theorem mk_sub (a b c d : ℝ) : mk a b - mk c d = mk (a - c) (b - d) := by
  ext i; fin_cases i <;> rfl

@[powerlib_foundation] theorem norm_sq_eq (x : State 2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

@[powerlib_foundation] theorem norm_mk_sq (a b : ℝ) : ‖mk a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_sq_eq]; rfl

@[powerlib_foundation] theorem norm_mk (a b : ℝ) : ‖mk a b‖ = √(a ^ 2 + b ^ 2) := by
  rw [← norm_mk_sq, Real.sqrt_sq (norm_nonneg _)]

@[powerlib_foundation] theorem abs_coord_le_norm (x : State 2) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have h := norm_sq_eq x
  have hn := norm_nonneg x
  apply abs_le_of_sq_le_sq' _ hn |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- The `i`-th coordinate as a continuous linear functional. -/
def coord (i : Fin 2) : State 2 →L[ℝ] ℝ := EuclideanSpace.proj i

@[simp, powerlib_foundation] theorem coord_apply (i : Fin 2) (x : State 2) : coord i x = x i := rfl

@[powerlib_foundation] theorem hasFDerivAt_coord (i : Fin 2) (x : State 2) :
    HasFDerivAt (fun y : State 2 => y i) (coord i) x :=
  (coord i).hasFDerivAt

/-- Componentwise derivatives determine the Jacobian matrix of a planar field. -/
@[powerlib_foundation] theorem hasFDerivAt_of_components {f : State 2 → State 2} {x : State 2}
    (A : Matrix (Fin 2) (Fin 2) ℝ) (L : Fin 2 → State 2 →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivAt (fun y => f y i) (L i) x)
    (hA : ∀ i (v : State 2), L i v = A i 0 * v 0 + A i 1 * v 1) :
    HasFDerivAt f (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  convert hL i using 1
  ext v
  simp [hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[powerlib_foundation] theorem fderiv_eq_of_components {f : State 2 → State 2} {x : State 2}
    (A : Matrix (Fin 2) (Fin 2) ℝ) (L : Fin 2 → State 2 →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivAt (fun y => f y i) (L i) x)
    (hA : ∀ i (v : State 2), L i v = A i 0 * v 0 + A i 1 * v 1) :
    fderiv ℝ f x = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A :=
  (hasFDerivAt_of_components A L hL hA).fderiv

/-- Smoothness of a planar field from smoothness of its two components. -/
@[powerlib_foundation] theorem contDiff_of_components {f : State 2 → State 2} {k : WithTop ℕ∞}
    (h0 : ContDiff ℝ k (fun y => f y 0)) (h1 : ContDiff ℝ k (fun y => f y 1)) :
    ContDiff ℝ k f := by
  rw [contDiff_euclidean]
  intro i; fin_cases i
  · exact h0
  · exact h1

@[fun_prop, powerlib_foundation] theorem contDiff_coord (i : Fin 2) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun y : State 2 => y i) :=
  (coord i).contDiff

/-- A planar curve is a solution iff its two coordinates satisfy the componentwise equations. -/
@[powerlib_foundation] theorem hasDerivWithinAt_iff_components {φ : ℝ → State 2} {v : State 2}
    {s : Set ℝ} {t : ℝ} :
    HasDerivWithinAt φ v s t ↔
      HasDerivWithinAt (fun τ => φ τ 0) (v 0) s t ∧ HasDerivWithinAt (fun τ => φ τ 1) (v 1) s t := by
  constructor
  · intro h
    exact ⟨(coord 0).hasFDerivAt.comp_hasDerivWithinAt t h,
      (coord 1).hasFDerivAt.comp_hasDerivWithinAt t h⟩
  · rintro ⟨h0, h1⟩
    have hφ : φ = fun τ => (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm ![φ τ 0, φ τ 1] := by
      funext τ; ext i; fin_cases i <;> rfl
    rw [hφ]
    have hv : v = (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm ![v 0, v 1] := by
      ext i; fin_cases i <;> rfl
    rw [hv]
    have hpi : HasDerivWithinAt (fun τ => ![φ τ 0, φ τ 1]) ![v 0, v 1] s t := by
      rw [hasDerivWithinAt_pi]
      intro i; fin_cases i
      · simpa using h0
      · simpa using h1
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
      |>.hasFDerivAt.comp_hasDerivWithinAt t hpi

end powerlib.PhasePlane
