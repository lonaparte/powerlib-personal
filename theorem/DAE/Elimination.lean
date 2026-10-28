import theorem.Linear.Transfer

/-! # Elimination of DAG-ordered algebraic variables (semi-explicit index-1 DAEs)

DAG-ordered algebraic constraints are solved by sequential substitution, which turns the DAE into
an equivalent ODE on the differential states; such DAEs have index 1.

Model boundary.
* Continuous time; `X` any type of differential states, `m` algebraic variables:
```
ẋ = f(x, y),      y = φ(x, y)      (constraint g(x, y) = y - φ(x, y) = 0),
```
  where `φ` is *DAG-ordered* (`IsDAG φ`): the `k`-th component of `φ(x, y)` depends only on `x`
  and on `y_j` with `j < k` (`y₁ = φ₁(x)`, `y₂ = φ₂(x, y₁)`, …).
* Deterministic, unforced (inputs and parameters may be absorbed into `f`, `φ`); no switching;
  the solution notion is a global-in-time `HasDerivAt` trajectory (`isIntegralCurveOn_dae_iff`:
  `HasDerivWithinAt` on an arbitrary time set `s`).

Source: work-sync theory/T-dae-elimination.md §1.3 (DAG substitution, boxed reduced ODE),
§1.4 (pointwise equivalence of DAE and ODE trajectories), §2.2 (d–q cancellation);
theory/T-dae-systems.md §1.3 (index-1 condition `det ∂g/∂y ≠ 0`);
theory/T-gfl-reduced-order-dynamics.md §1.2.8 (explicit algebraic layer, DAE → ODE).

Results.
* `solveDAG_spec`, `fixed_iff` — sequential substitution: `solveDAG φ x` (obtained by `m` passes
  of `y ↦ φ(x, y)`) is the unique solution of `y = φ(x, y)`, for every `x` (global, no
  implicit-function argument).
* `isDAGSolution_iff` — global trajectory equivalence: `(x, y)` solves the DAE on all of `ℝ`,
  i.e. `∀ t, HasDerivAt x (f (x t) (y t)) t ∧ y t = φ (x t) (y t)` (written out in the
  statement), iff `x` solves the ODE `ẋ = f(x, solveDAG φ x)` and `y(t) = solveDAG φ (x(t))` for
  every `t`.
* `jacobian_strictLower`, `det_constraint_jacobian_eq_one` — index 1: if `φ(x, ·)` is
  differentiable, its Jacobian is strictly lower triangular, hence `∂g/∂y = I - ∂φ/∂y` is unit
  lower triangular with determinant `1` (in particular invertible: the DAE is index 1).
* `isIntegralCurveOn_dae_iff` — explicit algebraic layer: a pair `(x, z)` solves
  `ẋ = F(x, z)`, `z = G(x)` on a set `s` iff `z = G ∘ x` on `s` and `x` is an integral curve of
  `ẋ = F(x, G(x))` on `s` (Mathlib's `IsIntegralCurveOn`; any DAG of explicit assignments
  composes into one such `G`).
* The d–q decoupling cancellation of §2.2 (`u_d = +ω̂ L̂ i_q`, `u_q = −ω̂ L̂ i_d` give zero
  decoupling power) is `CurrentControl.decoupling_power_cancel`.
-/

noncomputable section
namespace powerlib.DAE
open Matrix

variable {X : Type*} {m : ℕ}

/-- The `k`-th algebraic equation uses only `y_j` with `j < k`. -/
def IsDAG (φ : X → (Fin m → ℝ) → Fin m → ℝ) : Prop :=
  ∀ (x : X) (y y' : Fin m → ℝ) (k : Fin m), (∀ j : Fin m, j < k → y j = y' j) → φ x y k = φ x y' k

/-- Sequential substitution: `m` passes of `y ↦ φ(x, y)` starting from `0`. -/
def solveDAG (φ : X → (Fin m → ℝ) → Fin m → ℝ) (x : X) : Fin m → ℝ := (φ x)^[m] 0

@[powerlib_foundation] private lemma iterate_stable {φ : X → (Fin m → ℝ) → Fin m → ℝ}
    (hφ : IsDAG φ) (x : X) :
    ∀ k : ℕ, ∀ j : Fin m, j.val < k → ∀ k', k ≤ k' → (φ x)^[k'] 0 j = (φ x)^[k] 0 j := by
  intro k
  induction k with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    intro j hj k' hk'
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    apply hφ
    intro i hi
    exact ih i (by have : i.val < j.val := hi; omega) k'' (by omega)

/-- `solveDAG φ x` solves the algebraic constraint. -/
@[tmio T, powerlib_foundation] theorem solveDAG_spec {φ : X → (Fin m → ℝ) → Fin m → ℝ} (hφ : IsDAG φ)
    (x : X) : φ x (solveDAG φ x) = solveDAG φ x := by
  funext j
  have h := iterate_stable hφ x m j j.isLt (m + 1) (Nat.le_succ m)
  rw [Function.iterate_succ_apply'] at h
  exact h

/-- The algebraic constraint of a DAG-ordered system has exactly one solution. -/
@[powerlib_foundation] theorem eq_of_fixed {φ : X → (Fin m → ℝ) → Fin m → ℝ} (hφ : IsDAG φ)
    {x : X} {y y' : Fin m → ℝ} (hy : φ x y = y) (hy' : φ x y' = y') : y = y' := by
  have key : ∀ k : ℕ, ∀ j : Fin m, j.val < k → y j = y' j := by
    intro k
    induction k with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ k ih =>
      intro j hj
      rw [← hy, ← hy']
      exact hφ x y y' j fun i hi => ih i (by have : i.val < j.val := hi; omega)
  funext j
  exact key m j j.isLt

@[powerlib_foundation] theorem fixed_iff {φ : X → (Fin m → ℝ) → Fin m → ℝ} (hφ : IsDAG φ)
    (x : X) (y : Fin m → ℝ) : φ x y = y ↔ y = solveDAG φ x :=
  ⟨fun h => eq_of_fixed hφ h (solveDAG_spec hφ x), fun h => h ▸ solveDAG_spec hφ x⟩

/-- Global trajectory equivalence of the DAG-ordered DAE and its substituted ODE: `(x, y)` is a
global solution of the semi-explicit DAE `ẋ = f(x, y)`, `y = φ(x, y)` (left-hand side) iff `x`
solves the substituted ODE and `y = solveDAG φ x` pointwise. -/
@[powerlib_foundation] theorem isDAGSolution_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → (Fin m → ℝ) → E} {φ : E → (Fin m → ℝ) → Fin m → ℝ}
    (hφ : IsDAG φ) (x : ℝ → E) (y : ℝ → Fin m → ℝ) :
    (∀ t, HasDerivAt x (f (x t) (y t)) t ∧ y t = φ (x t) (y t)) ↔
      (∀ t, HasDerivAt x (f (x t) (solveDAG φ (x t))) t) ∧ ∀ t, y t = solveDAG φ (x t) := by
  constructor
  · intro h
    have hy : ∀ t, y t = solveDAG φ (x t) := fun t => (fixed_iff hφ _ _).mp (h t).2.symm
    exact ⟨fun t => hy t ▸ (h t).1, hy⟩
  · rintro ⟨hx, hy⟩ t
    refine ⟨(hy t).symm ▸ hx t, ?_⟩
    rw [hy t]
    exact (solveDAG_spec hφ _).symm

/-! ## Index 1: unit lower-triangular constraint Jacobian -/

/-- A DAG-ordered map has a strictly lower-triangular Jacobian in `y`. -/
@[powerlib_foundation] theorem jacobian_strictLower {φ : X → (Fin m → ℝ) → Fin m → ℝ}
    (hφ : IsDAG φ) {x : X} {y : Fin m → ℝ} {D : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)}
    (hD : HasFDerivAt (φ x) D y) {k j : Fin m} (hkj : k ≤ j) :
    D (Pi.single j 1) k = 0 := by
  let γ : ℝ → Fin m → ℝ := fun s => y + s • Pi.single j 1
  have hγ : HasDerivAt γ (Pi.single j 1) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j (1 : ℝ))).const_add y
    rw [one_smul] at this
    exact this
  have hγ0 : γ 0 = y := by simp [γ]
  have hD' : HasFDerivAt (φ x) D (γ 0) := by rw [hγ0]; exact hD
  have hcomp : HasDerivAt (fun s => φ x (γ s)) (D (Pi.single j 1)) 0 :=
    hD'.comp_hasDerivAt (0 : ℝ) hγ
  have hconst : (fun s => φ x (γ s) k) = fun _ => φ x y k := by
    funext s
    apply hφ
    intro i hi
    have : i ≠ j := ne_of_lt (lt_of_lt_of_le hi hkj)
    simp [γ, this]
  have hk := (hasDerivAt_pi.1 hcomp) k
  rw [show (fun s => φ x (γ s) k) = _ from hconst] at hk
  exact (hk.unique (hasDerivAt_const 0 _))

/-- `I - N` with `N` strictly lower triangular has determinant `1`. -/
@[powerlib_foundation] theorem det_one_sub_strictLower {R : Type*} [CommRing R]
    (N : Matrix (Fin m) (Fin m) R) (hN : ∀ k j : Fin m, k ≤ j → N k j = 0) :
    (1 - N).det = 1 := by
  rw [det_of_isLowerTriangular]
  · simp [hN _ _ le_rfl]
  · intro i j hij
    have hij' : i < j := hij
    simp [hij'.ne, hN i j hij'.le]

/-- Index 1 for DAG-ordered constraints: `det (∂g/∂y) = det (I - ∂φ/∂y) = 1`. -/
@[powerlib_foundation] theorem det_constraint_jacobian_eq_one {φ : X → (Fin m → ℝ) → Fin m → ℝ}
    (hφ : IsDAG φ) {x : X} {y : Fin m → ℝ} {D : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)}
    (hD : HasFDerivAt (φ x) D y) :
    (1 - LinearMap.toMatrix' (D : (Fin m → ℝ) →ₗ[ℝ] Fin m → ℝ)).det = 1 :=
  det_one_sub_strictLower _ fun k j hkj => by
    rw [LinearMap.toMatrix'_apply]
    exact jacobian_strictLower hφ hD hkj

/-! ## Explicit algebraic layer: DAE ≡ ODE -/

/-- A semi-explicit DAE `ẋ = F(x, z)`, `z = G(x)` with an explicit algebraic layer: a pair
`(x(t), z(t))` solves it on `s` iff `z = G ∘ x` on `s` and `x` solves `ẋ = F(x, G(x))` on `s`.
(Any DAG of explicit algebraic assignments composes into one such `G`.) -/
@[powerlib_foundation] theorem isIntegralCurveOn_dae_iff {E Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E → Z → E) (G : E → Z) (x : ℝ → E) (z : ℝ → Z) (s : Set ℝ) :
    ((∀ t ∈ s, z t = G (x t)) ∧ ∀ t ∈ s, HasDerivWithinAt x (F (x t) (z t)) s t) ↔
      ((∀ t ∈ s, z t = G (x t)) ∧
        IsIntegralCurveOn x (fun _ y => F y (G y)) s) := by
  constructor
  · rintro ⟨hz, hx⟩
    refine ⟨hz, fun t ht => ?_⟩
    have := hx t ht
    rwa [hz t ht] at this
  · rintro ⟨hz, hx⟩
    refine ⟨hz, fun t ht => ?_⟩
    rw [hz t ht]
    exact hx t ht

end powerlib.DAE
