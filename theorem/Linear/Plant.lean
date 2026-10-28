import theorem.Flow.Basic

/-! # Linear plants

A finite-dimensional continuous-time linear plant `x' = A x + B u`, `y = C x + D u` with `n`
states and `p` ports; input and output have the same dimension, as for impedance and admittance
models. The state is a point of `ℝⁿ = EuclideanSpace ℝ (Fin n)`. Nothing about trajectories is
defined here: the behaviour of a plant is the Flow semantics of its vector field, and the field
for a constant input with an equilibrium is LeanForControl's affine linear vector field.

Scope.
* Generic: arbitrary real matrices `A, B, C, D` of compatible sizes, continuous time, constant
  inputs; no model.

Source: LeanForControl's `affineLinearVectorField` (`LinearSystems`); Mathlib's
`Matrix.toEuclideanCLM`.

Results.
* `Plant` (`A`, `B`, `C`, `D`), the matrix action `op` on Euclidean state space (`affine_apply`,
  `op_mul_apply`, `op_cancel`).
* `Plant.inputField` (the field under a constant input); `Plant.inputField_eq` (with an
  equilibrium `e` it is the affine linear field of `A` centred at `e`), `Plant.inputField_zero`.
-/

noncomputable section

namespace powerlib.Linear

open Matrix LinearSystems

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A linear plant with `n` states and `p` ports. -/
@[ext] structure Plant (n p : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  B : Matrix (Fin n) (Fin p) ℝ
  C : Matrix (Fin p) (Fin n) ℝ
  D : Matrix (Fin p) (Fin p) ℝ

/-- A square matrix acting on Euclidean state space. -/
abbrev op (A : Matrix (Fin n) (Fin n) ℝ) : ℝⁿ →L[ℝ] ℝⁿ :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A

@[tmio T, powerlib_foundation] theorem affine_apply (A : Matrix (Fin n) (Fin n) ℝ) (e x : ℝⁿ) :
    affineLinearVectorField A e x = op A (x - e) := rfl

@[powerlib_foundation] theorem op_mul_apply (X Y : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    op (X * Y) x = op X (op Y x) := by
  change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (X * Y) x = _
  rw [map_mul]
  rfl

@[powerlib_foundation] theorem op_cancel {T S : Matrix (Fin n) (Fin n) ℝ} (h : S * T = 1)
    (x : ℝⁿ) : op S (op T x) = x := by
  rw [← op_mul_apply, h]
  change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) 1 x = x
  rw [map_one]
  rfl

/-- The vector field of the plant under the constant input `u`. -/
def Plant.inputField (M : Plant n p) (u : Fin p → ℝ) : ℝⁿ → ℝⁿ :=
  fun x => op M.A x + WithLp.toLp 2 (M.B *ᵥ u)

/-- Under a constant input with an equilibrium `e`, the plant's field is the affine linear
field of `A` centred at `e`. -/
@[powerlib_foundation] theorem Plant.inputField_eq (M : Plant n p) {u : Fin p → ℝ} {e : ℝⁿ}
    (he : IsEquilibrium (M.inputField u) e) :
    M.inputField u = affineLinearVectorField M.A e := by
  have hb : WithLp.toLp 2 (M.B *ᵥ u) = -op M.A e := eq_neg_of_add_eq_zero_right he
  funext x
  rw [Plant.inputField, hb, affine_apply, map_sub, sub_eq_add_neg]

/-- With zero input the origin is an equilibrium and the field is linear. -/
@[powerlib_foundation] theorem Plant.inputField_zero (M : Plant n p) :
    M.inputField 0 = affineLinearVectorField M.A 0 := by
  funext x
  simp [Plant.inputField, affine_apply]

end powerlib.Linear
