import theorem.Criteria.Hurwitz2
import theorem.Dynamics.State
import theorem.Dynamics.Coordinates

/-! # Planar state-space helpers

Coordinates and norms on the planar state space `State 2 = EuclideanSpace ℝ (Fin 2)`, used by the
phase-plane and planar normal-form modules.

Scope.
* The planar state space is `State 2 = EuclideanSpace ℝ (Fin 2)` with coordinates `x 0`, `x 1`.
  The coordinate maps and the identification of the Fréchet derivative of a field with
  `Matrix.toEuclideanCLM A` from componentwise derivatives (`Dynamics.coord`,
  `Dynamics.hasFDerivAt_toEuclideanCLM_of_components`, any dimension) are in
  `theorem/Dynamics/Coordinates.lean`; this is the shape required by the linearization theorems
  `hurwitz_linearization_locally_exponentially_stable`,
  `powerlib.Criteria.locallyExponentiallyStable_of_jacobian_fin_two`, etc.
* These are calculus utilities only; no model is fixed here (no model family, all results
  public foundation support).

Source: library infrastructure (no work-sync note).

Results.
* `mk a b` is the state with `x 0 = a`, `x 1 = b` (`mk_apply_zero`, `mk_apply_one`, `mk_coords`,
  `ext_iff'`, `mk_eq_iff`, `mk_sub`); norms `norm_sq_eq`, `norm_mk_sq`, `norm_mk`,
  `norm_mk_sub_mk_le` (`‖mk a b − mk c d‖ ≤ |a − c| + |b − d|`).
* `toEuclideanCLM_apply_zero`, `toEuclideanCLM_apply_one` read off the two components of a
  `2 × 2` matrix acting on a planar state (instances of `Dynamics.toEuclideanCLM_apply`);
  `hasDerivWithinAt_iff_components` differentiates a planar curve componentwise.
* The complex form: `complexIso : ℂ ≃ₗᵢ[ℝ] State 2`, `z ↦ (Re z, Im z)`, a real linear isometry
  (`complexIso_apply_zero`, `complexIso_apply_one`, `complexIso_apply`, `complexIso_symm_apply`);
  `isIntegralCurveOn_complexIso_iff` (transport): when `F (complexIso z) = complexIso (G z)`, the
  curves `complexIso ∘ φ` solving `ẋ = F x` are exactly the images of the solutions `φ` of
  `ż = G z`, on every time set.
-/

noncomputable section
namespace powerlib.PhasePlane
open Set Filter Topology Matrix
open powerlib.Dynamics (State)

/-- The planar state with coordinates `(a, b)`. -/
def mk (a b : ℝ) : State 2 := WithLp.toLp 2 ![a, b]

@[tmio T, simp, powerlib_foundation] theorem mk_apply_zero (a b : ℝ) : mk a b 0 = a := rfl
@[tmio T, simp, powerlib_foundation] theorem mk_apply_one (a b : ℝ) : mk a b 1 = b := rfl

@[tmio T, simp, powerlib_foundation] theorem mk_coords (x : State 2) : mk (x 0) (x 1) = x := by
  ext i; fin_cases i <;> rfl

@[tmio T, powerlib_foundation] theorem mk_eq_iff {a b c d : ℝ} : mk a b = mk c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun x : State 2 => x 0) h,
      by simpa using congrArg (fun x : State 2 => x 1) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[tmio T, simp, powerlib_foundation] theorem mk_zero : mk 0 0 = 0 := by
  ext i; fin_cases i <;> rfl

@[tmio T, powerlib_foundation] theorem mk_eq_zero_iff {a b : ℝ} : mk a b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [← mk_zero, mk_eq_iff]

@[tmio T, powerlib_foundation] theorem ext_iff' {x y : State 2} : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 := by
  rw [← mk_coords x, ← mk_coords y, mk_eq_iff]; simp

@[tmio T, powerlib_foundation] theorem eq_zero_iff {x : State 2} : x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  rw [ext_iff' (y := 0)]; simp

@[tmio T, powerlib_foundation] theorem mk_sub (a b c d : ℝ) : mk a b - mk c d = mk (a - c) (b - d) := by
  ext i; fin_cases i <;> rfl

@[tmio T, powerlib_foundation] theorem norm_sq_eq (x : State 2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

@[tmio T, powerlib_foundation] theorem norm_mk_sq (a b : ℝ) : ‖mk a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_sq_eq]; rfl

@[tmio T, powerlib_foundation] theorem norm_mk (a b : ℝ) : ‖mk a b‖ = √(a ^ 2 + b ^ 2) := by
  rw [← norm_mk_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The distance between two planar states is at most the sum of the coordinate gaps. -/
@[tmio T, powerlib_foundation] theorem norm_mk_sub_mk_le (a b c d : ℝ) :
    ‖mk a b - mk c d‖ ≤ |a - c| + |b - d| := by
  refine ((Dynamics.norm_le_sum_abs _).trans_eq (Fin.sum_univ_two _)).trans (le_of_eq ?_)
  simp [mk]

@[tmio T, powerlib_foundation] theorem toEuclideanCLM_apply_zero (A : Matrix (Fin 2) (Fin 2) ℝ)
    (v : State 2) :
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A v) 0 = A 0 0 * v 0 + A 0 1 * v 1 := by
  rw [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two]

@[tmio T, powerlib_foundation] theorem toEuclideanCLM_apply_one (A : Matrix (Fin 2) (Fin 2) ℝ)
    (v : State 2) :
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A v) 1 = A 1 0 * v 0 + A 1 1 * v 1 := by
  rw [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two]

/-- A planar curve is a solution iff its two coordinates satisfy the componentwise equations. -/
@[tmio T, powerlib_foundation] theorem hasDerivWithinAt_iff_components {φ : ℝ → State 2} {v : State 2}
    {s : Set ℝ} {t : ℝ} :
    HasDerivWithinAt φ v s t ↔
      HasDerivWithinAt (fun τ => φ τ 0) (v 0) s t ∧
        HasDerivWithinAt (fun τ => φ τ 1) (v 1) s t := by
  constructor
  · intro h
    exact ⟨(Dynamics.coord 0).hasFDerivAt.comp_hasDerivWithinAt t h,
      (Dynamics.coord 1).hasFDerivAt.comp_hasDerivWithinAt t h⟩
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

/-! ## The complex form of the plane -/

/-- The plane as `ℂ`: `z ↦ (Re z, Im z)`, a real linear isometry (the coordinates in Mathlib's
orthonormal basis `{1, i}` of `ℂ`). -/
def complexIso : ℂ ≃ₗᵢ[ℝ] State 2 := Complex.orthonormalBasisOneI.repr

@[tmio T, simp, powerlib_foundation] theorem complexIso_apply_zero (z : ℂ) :
    complexIso z 0 = z.re := rfl

@[tmio T, simp, powerlib_foundation] theorem complexIso_apply_one (z : ℂ) :
    complexIso z 1 = z.im := rfl

@[tmio T, powerlib_foundation] theorem complexIso_apply (z : ℂ) :
    complexIso z = mk z.re z.im :=
  ext_iff'.2 ⟨rfl, rfl⟩

@[tmio T, simp, powerlib_foundation] theorem complexIso_symm_apply (x : State 2) :
    complexIso.symm x = ⟨x 0, x 1⟩ :=
  complexIso.symm_apply_eq.2 (ext_iff'.2 ⟨rfl, rfl⟩)

/-- Transport through the complex form: if the planar field `F` is the complex field `G` read
through `complexIso` (`F (complexIso z) = complexIso (G z)`), the curves `complexIso ∘ φ` that
solve `ẋ = F x` on a time set are exactly the images of the solutions `φ` of `ż = G z` there. -/
@[tmio T, powerlib_foundation] theorem isIntegralCurveOn_complexIso_iff {F : State 2 → State 2}
    {G : ℂ → ℂ} (hFG : ∀ z, F (complexIso z) = complexIso (G z)) (φ : ℝ → ℂ) (s : Set ℝ) :
    IsIntegralCurveOn (fun t => complexIso (φ t)) (fun _ x => F x) s ↔
      IsIntegralCurveOn φ (fun _ z => G z) s := by
  refine forall₂_congr fun t _ => ?_
  simp only [hFG]
  constructor
  · intro h
    simpa [Function.comp_def] using
      complexIso.symm.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivWithinAt t h
  · intro h
    exact complexIso.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivWithinAt t h

end powerlib.PhasePlane
