import theorem.Linear.Transfer
import theorem.LTI.Decay

/-! # Linear semi-explicit DAEs: Schur-complement reduction, matrix pencil, stability

Index-1 linear semi-explicit DAEs reduce to their Schur-complement ODE: solution sets, pencil
eigenvalues, exponential stability, consistent initial values and the differentiation count.

Model boundary.
* Continuous time, constant matrices, `n` differential states, `m` algebraic variables, `p`
  inputs; state order `x` then `y`:
```
ẋ = Axx x + Axy y + Bx u,      0 = Ayx x + Ayy y + By u .
```
* A solution for the input signal `u` is a pair `(x, y)` such that for every `t : ℝ`, `x` has
  derivative `Axx x(t) + Axy y(t) + Bx u(t)` and the algebraic constraint holds at `t`:
```
∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ u t) t ∧
  d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ u t = 0
```
  (zero input: `u = 0`, written `d.Bx *ᵥ 0`, `d.By *ᵥ 0`). No regularity of `y` is assumed.
  Solutions are global in time, with coordinate-vector states `Fin n → ℝ`. This solution notion
  and the exponential stability below are written out in each statement that uses them; they
  are not separate definitions (single-semantics rule: behaviour is defined only in the semantic
  layer).
* Constant-coefficient linear DAE only; no switching, delay, PWM or PLL; the semantic predicates
  are about the given matrices. Nonlinear index-1 DAEs are in `theorem/DAE/Nonlinear.lean`.
* The DAE solution notion and its exponential stability lie outside the Flow sentence language,
  which concerns explicit ODEs; they are connected to that language through the reduced ODE.
  Coordinate solutions of `ẋ = A x` are linked to LeanForControl's affine linear field on
  `EuclideanSpace ℝ (Fin k)` (`LTI.isTrajectoryOn_toLp`), whose Hurwitz theory gives both
  directions of the coordinate decay test (`LTI.linear_decay_of_isHurwitz`,
  `LTI.isHurwitz_of_linear_decay`, in `theorem/LTI/Decay.lean`).

Source: work-sync theory/T-dae-systems.md §1.2–§1.4, §1.7, §1.9, §2.1;
theory/T-small-signal-stability.md §1.3–§1.4; theory/T-sdae-systems.md §1.1 (drift part).

Results.
* `isSolution_iff` — index-1 reduction (`Ayy` invertible, i.e. `IsUnit Ayy.det`): `(x, y)`
  solves the DAE iff `x` solves the reduced ODE `ẋ = A_red x + B_red u` with Schur complements
  `A_red = Axx - Axy Ayy⁻¹ Ayx`, `B_red = Bx - Axy Ayy⁻¹ By`, and `y = -Ayy⁻¹ (Ayx x + By u)`
  pointwise. This is a one-to-one correspondence of solution sets (the algebraic trajectory is
  a function of the differential one).
* `det_pencil`, `det_pencil_eq_zero_iff` — matrix pencil, under index 1: with `E = diag(I, 0)`
  and `J` the block Jacobian, `det (s E - J) = det (-Ayy) · det (s I - A_red)`
  (`Matrix.det_fromBlocks₂₂`), so the finite generalized eigenvalues are exactly the eigenvalues
  of `A_red`.
* `exponentiallyStable_iff_isHurwitz` — exponential stability of the DAE (zero input): for some
  `K > 0`, `r > 0`, every solution satisfies `‖x t‖ ≤ K e^{-r t} ‖x 0‖` and
  `‖y t‖ ≤ K e^{-r t} ‖x 0‖` for `t ≥ 0` (Euclidean norms). Under index 1 this holds iff
  `IsHurwitz A_red`.
* `initial_consistent`, `exists_unique_consistent` — consistent initial values: every solution
  satisfies the constraint at `t = 0`; under index 1 the consistent `y(0)` is unique, and every
  `x(0)` has a solution.
* `isSolution_stacked_ode`, `exists_inconsistent_initial` — one differentiation: under index 1
  every solution has differentiable `y` and the stacked state `(x, y)` satisfies an explicit
  linear ODE (constraint differentiated once), while for `m > 0` the undifferentiated system is
  not an ODE (some initial point has no solution).

Corrections.
* Index count, T-dae-systems §1.3: the note defines the index as the minimal number of
  differentiations of `g = 0` needed to obtain an explicit ODE, but its list says "index k:
  differentiate k − 1 times" — off by one. Formalized: for an index-1 system one differentiation
  is necessary and sufficient (`isSolution_stacked_ode`, `not_solution_of_inconsistent`); the
  list should read "index k: k differentiations".
* T-dae-systems §2.1, "Ybus connected ⇒ nonsingular": a network admittance matrix with no shunt
  (ground) branches is Laplacian-type, `Y 𝟏 = 0`, hence singular for every topology, connected
  or not (`Network.ybusNoShunt_det_eq_zero`); the two-bus line is a connected counterexample
  (`Network.ybus_two_bus_singular`). Nonsingularity needs a shunt path. Both are in
  `theorem/Network/WeightedLaplacian.lean`.
-/

noncomputable section
namespace powerlib.DAE
open Matrix LinearSystems

/-- Linear semi-explicit DAE `ẋ = Axx x + Axy y + Bx u`, `0 = Ayx x + Ayy y + By u`. -/
structure LinearDAE (n m p : ℕ) where
  Axx : Matrix (Fin n) (Fin n) ℝ
  Axy : Matrix (Fin n) (Fin m) ℝ
  Ayx : Matrix (Fin m) (Fin n) ℝ
  Ayy : Matrix (Fin m) (Fin m) ℝ
  Bx : Matrix (Fin n) (Fin p) ℝ
  By : Matrix (Fin m) (Fin p) ℝ

variable {n m p : ℕ}

/-- The singular "mass matrix" `E = diag(I, 0)` of a semi-explicit DAE. -/
def massMatrix (n m : ℕ) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ := fromBlocks 1 0 0 0

@[powerlib_foundation] theorem complexify_inv {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (h : IsUnit A.det) : Linear.complexify A⁻¹ = (Linear.complexify A)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Linear.complexify_mul, nonsing_inv_mul _ h]
  simp [Linear.complexify]

@[powerlib_foundation] theorem det_complexify {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    (Linear.complexify A).det = algebraMap ℝ ℂ A.det := by
  rw [RingHom.map_det]; rfl

namespace LinearDAE

variable (d : LinearDAE n m p)

/-- Schur complement `A_red = Axx - Axy Ayy⁻¹ Ayx`. -/
def schurA : Matrix (Fin n) (Fin n) ℝ := d.Axx - d.Axy * d.Ayy⁻¹ * d.Ayx

/-- Reduced input matrix `B_red = Bx - Axy Ayy⁻¹ By`. -/
def schurB : Matrix (Fin n) (Fin p) ℝ := d.Bx - d.Axy * d.Ayy⁻¹ * d.By

/-- The algebraic variable on the constraint manifold, `-Ayy⁻¹ (Ayx x + By u)`. -/
def algebraic (x : Fin n → ℝ) (u : Fin p → ℝ) : Fin m → ℝ :=
  -(d.Ayy⁻¹ *ᵥ (d.Ayx *ᵥ x + d.By *ᵥ u))

/-! ## Constraint solving and solution correspondence -/

@[powerlib_foundation] theorem constraint_iff (hA : IsUnit d.Ayy.det) (x : Fin n → ℝ)
    (y : Fin m → ℝ) (u : Fin p → ℝ) :
    d.Ayx *ᵥ x + d.Ayy *ᵥ y + d.By *ᵥ u = 0 ↔ y = d.algebraic x u := by
  constructor
  · intro h
    have hy : d.Ayy *ᵥ y = -(d.Ayx *ᵥ x + d.By *ᵥ u) := by
      rw [eq_neg_iff_add_eq_zero, ← h]; abel
    calc y = (d.Ayy⁻¹ * d.Ayy) *ᵥ y := by rw [nonsing_inv_mul _ hA, one_mulVec]
      _ = d.Ayy⁻¹ *ᵥ (d.Ayy *ᵥ y) := (mulVec_mulVec _ _ _).symm
      _ = d.algebraic x u := by rw [hy, mulVec_neg]; rfl
  · rintro rfl
    simp only [algebraic, mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
    abel

@[powerlib_foundation] theorem field_on_constraint (x : Fin n → ℝ) (u : Fin p → ℝ) :
    d.Axx *ᵥ x + d.Axy *ᵥ d.algebraic x u + d.Bx *ᵥ u = d.schurA *ᵥ x + d.schurB *ᵥ u := by
  simp only [algebraic, schurA, schurB, mulVec_neg, mulVec_add, sub_mulVec, ← mulVec_mulVec]
  abel

/-- Index-1 solution correspondence with the Schur-complement ODE: `(x, y)` is a global
solution of the DAE for the input `u` (left-hand side) iff `x` solves the reduced ODE and `y`
lies on the constraint manifold. -/
@[powerlib_foundation] theorem isSolution_iff (hA : IsUnit d.Ayy.det) (u : ℝ → Fin p → ℝ)
    (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) :
    (∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ u t) t ∧
      d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ u t = 0) ↔
      (∀ t, HasDerivAt x (d.schurA *ᵥ x t + d.schurB *ᵥ u t) t) ∧
        ∀ t, y t = d.algebraic (x t) (u t) := by
  constructor
  · intro h
    have hy : ∀ t, y t = d.algebraic (x t) (u t) := fun t =>
      (d.constraint_iff hA _ _ _).mp (h t).2
    refine ⟨fun t => ?_, hy⟩
    have := (h t).1
    rwa [hy t, field_on_constraint] at this
  · rintro ⟨hx, hy⟩ t
    refine ⟨?_, (d.constraint_iff hA _ _ _).mpr (hy t)⟩
    rw [hy t, field_on_constraint]
    exact hx t

/-- Zero-input version of `isSolution_iff`. -/
@[powerlib_foundation] theorem isSolution_zero_iff (hA : IsUnit d.Ayy.det)
    (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) :
    (∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ 0) t ∧
      d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ 0 = 0) ↔
      (∀ t, HasDerivAt x (d.schurA *ᵥ x t) t) ∧ ∀ t, y t = d.algebraic (x t) 0 := by
  rw [d.isSolution_iff hA]
  simp only [Pi.zero_apply, mulVec_zero, add_zero]

/-- Every reduced trajectory lifts to a DAE solution (zero input), with algebraic part
`y t = algebraic (x t) 0`. -/
@[powerlib_foundation] theorem isSolution_lift (hA : IsUnit d.Ayy.det) {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, HasDerivAt x (d.schurA *ᵥ x t) t) :
    ∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ d.algebraic (x t) 0 + d.Bx *ᵥ 0) t ∧
      d.Ayx *ᵥ x t + d.Ayy *ᵥ d.algebraic (x t) 0 + d.By *ᵥ 0 = 0 :=
  (d.isSolution_zero_iff hA _ _).mpr ⟨hx, fun _ => rfl⟩

/-! ## Consistent initial values -/

/-- Necessary condition: along every solution `(x, y)` of the DAE for the input `u`, the
constraint holds at the initial time. -/
@[powerlib_foundation] theorem initial_consistent {u : ℝ → Fin p → ℝ} {x : ℝ → Fin n → ℝ}
    {y : ℝ → Fin m → ℝ}
    (h : ∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ u t) t ∧
      d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ u t = 0) :
    d.Ayx *ᵥ x 0 + d.Ayy *ᵥ y 0 + d.By *ᵥ u 0 = 0 := (h 0).2

/-- An initial point violating the constraint carries no solution of the DAE. -/
@[powerlib_foundation] theorem not_solution_of_inconsistent {u : ℝ → Fin p → ℝ}
    {x : ℝ → Fin n → ℝ} {y : ℝ → Fin m → ℝ}
    (hc : d.Ayx *ᵥ x 0 + d.Ayy *ᵥ y 0 + d.By *ᵥ u 0 ≠ 0) :
    ¬ ∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ u t) t ∧
      d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ u t = 0 :=
  fun h => hc (d.initial_consistent h)

/-- Index 1: for `m > 0` some initial point `(x₀, y₀)` admits no solution, so the
undifferentiated DAE is not an explicit ODE in `(x, y)`. -/
@[powerlib_foundation] theorem exists_inconsistent_initial (hA : IsUnit d.Ayy.det) (hm : 0 < m) :
    ∃ y₀ : Fin m → ℝ, ∀ (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ), x 0 = 0 → y 0 = y₀ →
      ¬ (∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ 0) t ∧
        d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ 0 = 0) := by
  refine ⟨fun _ => 1, fun x y hx hy hs => ?_⟩
  have h := (d.constraint_iff hA _ _ _).mp (d.initial_consistent hs)
  rw [hx, hy] at h
  have h0 := congrFun h ⟨0, hm⟩
  simp [algebraic] at h0

/-- Index 1: the consistent algebraic initial value is unique and every `x₀` has a
(zero-input) solution. -/
@[powerlib_foundation] theorem exists_unique_consistent (hA : IsUnit d.Ayy.det) (x₀ : Fin n → ℝ) :
    (∃ (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ),
      (∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ 0) t ∧
        d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ 0 = 0) ∧ x 0 = x₀) ∧
      ∀ y₀ : Fin m → ℝ, d.Ayx *ᵥ x₀ + d.Ayy *ᵥ y₀ + d.By *ᵥ 0 = 0 → y₀ = d.algebraic x₀ 0 := by
  refine ⟨?_, fun y₀ h => (d.constraint_iff hA _ _ _).mp h⟩
  obtain ⟨x, hx, h0⟩ := LTI.exists_linear_trajectory d.schurA x₀
  exact ⟨x, _, d.isSolution_lift hA hx, h0⟩

/-! ## One differentiation of the constraint gives an explicit ODE -/

/-- Block matrix of the explicit ODE obtained after differentiating `0 = Ayx x + Ayy y` once:
`ẏ = -Ayy⁻¹ Ayx ẋ`. State order `x` then `y`. -/
def stackedField : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  fromBlocks d.Axx d.Axy (-(d.Ayy⁻¹ * d.Ayx * d.Axx)) (-(d.Ayy⁻¹ * d.Ayx * d.Axy))

/-- Index 1 = one differentiation: on every zero-input solution `(x, y)` (hypothesis `h`), `y`
is differentiable and the stacked state solves the explicit linear ODE `ż = stackedField z`. -/
@[powerlib_foundation] theorem isSolution_stacked_ode (hA : IsUnit d.Ayy.det)
    {x : ℝ → Fin n → ℝ} {y : ℝ → Fin m → ℝ}
    (h : ∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ 0) t ∧
      d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ 0 = 0) (t : ℝ) :
    HasDerivAt (fun s => Sum.elim (x s) (y s)) (d.stackedField *ᵥ Sum.elim (x t) (y t)) t := by
  have hy : ∀ s, y s = -((d.Ayy⁻¹ * d.Ayx) *ᵥ x s) := by
    intro s
    rw [(d.constraint_iff hA _ _ _).mp (h s).2]
    simp [algebraic, mulVec_mulVec]
  have hx := (h t).1
  simp only [Pi.zero_apply, mulVec_zero, add_zero] at hx
  have hyd : HasDerivAt y (-((d.Ayy⁻¹ * d.Ayx) *ᵥ (d.Axx *ᵥ x t + d.Axy *ᵥ y t))) t := by
    have hfun : y = fun s => -((d.Ayy⁻¹ * d.Ayx) *ᵥ x s) := funext hy
    have hL : HasDerivAt (fun s => (d.Ayy⁻¹ * d.Ayx) *ᵥ x s)
        ((d.Ayy⁻¹ * d.Ayx) *ᵥ (d.Axx *ᵥ x t + d.Axy *ᵥ y t)) t :=
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (d.Ayy⁻¹ * d.Ayx))).hasFDerivAt.comp_hasDerivAt
        t hx
    have hL' : HasDerivAt (fun s => -((d.Ayy⁻¹ * d.Ayx) *ᵥ x s))
        (-((d.Ayy⁻¹ * d.Ayx) *ᵥ (d.Axx *ᵥ x t + d.Axy *ᵥ y t))) t := hL.neg
    convert hL' using 1
  refine hasDerivAt_pi.2 fun i => ?_
  rcases i with i | i
  · have := hasDerivAt_pi.1 hx i
    simpa [stackedField, fromBlocks_mulVec] using this
  · have := hasDerivAt_pi.1 hyd i
    refine this.congr_deriv ?_
    rw [stackedField, fromBlocks_mulVec]
    simp only [Sum.elim_inr, Pi.add_apply, neg_mulVec, Pi.neg_apply, mulVec_add,
      mulVec_mulVec, Function.comp_def, Sum.elim_inl, Matrix.mul_assoc]
    ring

/-! ## Matrix pencil and its spectrum -/


/-- The block Jacobian `J = [[Axx, Axy], [Ayx, Ayy]]`. -/
def jacobian : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ := fromBlocks d.Axx d.Axy d.Ayx d.Ayy

/-- Pencil `s E - J` over `ℂ`. -/
def pencil (s : ℂ) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ :=
  s • Linear.complexify (massMatrix n m) - Linear.complexify d.jacobian

/-- `det (s E - J) = det (-Ayy) · det (s I - A_red)`. -/
@[powerlib_foundation] theorem det_pencil (hA : IsUnit d.Ayy.det) (s : ℂ) :
    (d.pencil s).det =
      (Linear.complexify (-d.Ayy)).det * (Linear.characteristicMatrix d.schurA s).det := by
  have hAn : IsUnit (-d.Ayy).det := by
    rw [det_neg]; exact (isUnit_neg_one.pow _).mul hA
  have hinvR : (-d.Ayy)⁻¹ = -(d.Ayy⁻¹) :=
    Matrix.inv_eq_left_inv (by rw [neg_mul_neg, nonsing_inv_mul _ hA])
  have hAc : IsUnit (Linear.complexify (-d.Ayy)).det := by
    rw [det_complexify]; exact hAn.map _
  let _ : Invertible (Linear.complexify (-d.Ayy)) := invertibleOfIsUnitDet _ hAc
  have hblocks : d.pencil s = fromBlocks (s • 1 - Linear.complexify d.Axx)
      (-Linear.complexify d.Axy) (-Linear.complexify d.Ayx) (Linear.complexify (-d.Ayy)) := by
    ext (i | i) (j | j) <;>
      simp [pencil, massMatrix, jacobian, Matrix.one_apply, Linear.complexify, apply_ite]
  rw [hblocks, det_fromBlocks₂₂]
  congr 1
  rw [invOf_eq_nonsing_inv, ← complexify_inv hAn, hinvR]
  show _ = (s • 1 - Linear.complexify d.schurA).det
  congr 1
  simp only [schurA, Linear.complexify_neg, Linear.complexify_sub, Linear.complexify_mul,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, sub_neg_eq_add]
  abel

@[powerlib_foundation] theorem det_pencil_eq_zero_iff (hA : IsUnit d.Ayy.det) (s : ℂ) :
    (d.pencil s).det = 0 ↔ (Linear.characteristicMatrix d.schurA s).det = 0 := by
  rw [d.det_pencil hA s, mul_eq_zero]
  have hAn : IsUnit (-d.Ayy).det := by
    rw [det_neg]; exact (isUnit_neg_one.pow _).mul hA
  have : (Linear.complexify (-d.Ayy)).det ≠ 0 := by
    rw [det_complexify]
    exact (hAn.map (algebraMap ℝ ℂ)).ne_zero
  simp [this]

/-- All finite generalized eigenvalues of the pencil lie in the open left half-plane iff the
Schur complement is spectrally stable. -/
@[powerlib_foundation] theorem pencil_stable_iff (hA : IsUnit d.Ayy.det) :
    (∀ s, (d.pencil s).det = 0 → s.re < 0) ↔ Linear.SpectrallyStable d.schurA := by
  simp only [Linear.SpectrallyStable, d.det_pencil_eq_zero_iff hA]

/-! ## Exponential stability -/

@[powerlib_foundation] theorem sqNorm_mulVec_le {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℝ)
    (v : Fin l → ℝ) :
    ∑ i, (M *ᵥ v) i ^ 2 ≤ (∑ i, ∑ j, M i j ^ 2) * ∑ j, v j ^ 2 := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simpa [mulVec, dotProduct] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M i) v

@[powerlib_foundation] theorem norm_mulVec_le {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℝ)
    (v : Fin l → ℝ) :
    ‖WithLp.toLp 2 (M *ᵥ v)‖ ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) * ‖WithLp.toLp 2 v‖ := by
  have hn : ∀ {r : ℕ} (w : Fin r → ℝ), ‖WithLp.toLp 2 w‖ ^ 2 = ∑ i, w i ^ 2 := fun w => by
    rw [EuclideanSpace.real_norm_sq_eq]
  have h := sqNorm_mulVec_le M v
  rw [← hn, ← hn] at h
  calc ‖WithLp.toLp 2 (M *ᵥ v)‖ = Real.sqrt (‖WithLp.toLp 2 (M *ᵥ v)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((∑ i, ∑ j, M i j ^ 2) * ‖WithLp.toLp 2 v‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := by
      have hS : 0 ≤ ∑ i, ∑ j, M i j ^ 2 := by positivity
      rw [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg _)]

/-- Index 1 and Hurwitz Schur complement ⇒ exponential stability of the zero-input DAE: every
solution has both components bounded by `K e^{-rate t} ‖x(0)‖` for `t ≥ 0`. -/
@[powerlib_foundation] theorem exponentiallyStable_of_isHurwitz (hA : IsUnit d.Ayy.det)
    (hH : LinearSystems.IsHurwitz d.schurA) :
    ∃ K > 0, ∃ rate > 0, ∀ (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ),
      (∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ 0) t ∧
        d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ 0 = 0) → ∀ t, 0 ≤ t →
      ‖WithLp.toLp 2 (x t)‖ ≤ K * Real.exp (-(rate * t)) * ‖WithLp.toLp 2 (x 0)‖ ∧
      ‖WithLp.toLp 2 (y t)‖ ≤ K * Real.exp (-(rate * t)) * ‖WithLp.toLp 2 (x 0)‖ := by
  obtain ⟨K, hK, r, hr, hdecay⟩ := LTI.linear_decay_of_isHurwitz hH
  set c := Real.sqrt (∑ i, ∑ j, (d.Ayy⁻¹ * d.Ayx) i j ^ 2)
  refine ⟨K * (1 + c), by positivity, r, hr, fun x y hs t ht => ?_⟩
  obtain ⟨hx, hy⟩ := (d.isSolution_zero_iff hA x y).mp hs
  have hxb := hdecay x hx t ht
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hE : 0 ≤ K * Real.exp (-(r * t)) * ‖WithLp.toLp 2 (x 0)‖ := by positivity
  constructor
  · calc ‖WithLp.toLp 2 (x t)‖ ≤ K * Real.exp (-(r * t)) * ‖WithLp.toLp 2 (x 0)‖ := hxb
      _ ≤ K * (1 + c) * Real.exp (-(r * t)) * ‖WithLp.toLp 2 (x 0)‖ := by nlinarith
  · have hyt : y t = -((d.Ayy⁻¹ * d.Ayx) *ᵥ x t) := by
      rw [hy t]; simp [algebraic, mulVec_mulVec]
    have hneg : ‖WithLp.toLp 2 (y t)‖ = ‖WithLp.toLp 2 ((d.Ayy⁻¹ * d.Ayx) *ᵥ x t)‖ := by
      rw [hyt, WithLp.toLp_neg, norm_neg]
    rw [hneg]
    calc ‖WithLp.toLp 2 ((d.Ayy⁻¹ * d.Ayx) *ᵥ x t)‖ ≤ c * ‖WithLp.toLp 2 (x t)‖ :=
          norm_mulVec_le _ _
      _ ≤ c * (K * Real.exp (-(r * t)) * ‖WithLp.toLp 2 (x 0)‖) :=
          mul_le_mul_of_nonneg_left hxb hc
      _ ≤ K * (1 + c) * Real.exp (-(r * t)) * ‖WithLp.toLp 2 (x 0)‖ := by nlinarith

/-- Conversely, exponential stability of the index-1 zero-input DAE (both components of every
solution bounded by `K e^{-rate t} ‖x(0)‖`) forces the Schur complement to be Hurwitz. -/
@[powerlib_foundation] theorem isHurwitz_of_exponentiallyStable (hA : IsUnit d.Ayy.det)
    (h : ∃ K > 0, ∃ rate > 0, ∀ (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ),
        (∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ 0) t ∧
          d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ 0 = 0) → ∀ t, 0 ≤ t →
        ‖WithLp.toLp 2 (x t)‖ ≤ K * Real.exp (-(rate * t)) * ‖WithLp.toLp 2 (x 0)‖ ∧
        ‖WithLp.toLp 2 (y t)‖ ≤ K * Real.exp (-(rate * t)) * ‖WithLp.toLp 2 (x 0)‖) :
    LinearSystems.IsHurwitz d.schurA := by
  obtain ⟨K, -, r, hr, hb⟩ := h
  exact LTI.isHurwitz_of_linear_decay hr fun x hx t ht => (hb x _ (d.isSolution_lift hA hx) t ht).1

/-- Index 1: exponential stability of the zero-input DAE (both components of every solution
bounded by `K e^{-rate t} ‖x(0)‖`, `K, rate > 0`) holds iff the Schur complement is Hurwitz. -/
@[powerlib_foundation] theorem exponentiallyStable_iff_isHurwitz (hA : IsUnit d.Ayy.det) :
    (∃ K > 0, ∃ rate > 0, ∀ (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ),
        (∀ t, HasDerivAt x (d.Axx *ᵥ x t + d.Axy *ᵥ y t + d.Bx *ᵥ 0) t ∧
          d.Ayx *ᵥ x t + d.Ayy *ᵥ y t + d.By *ᵥ 0 = 0) → ∀ t, 0 ≤ t →
        ‖WithLp.toLp 2 (x t)‖ ≤ K * Real.exp (-(rate * t)) * ‖WithLp.toLp 2 (x 0)‖ ∧
        ‖WithLp.toLp 2 (y t)‖ ≤ K * Real.exp (-(rate * t)) * ‖WithLp.toLp 2 (x 0)‖) ↔
      LinearSystems.IsHurwitz d.schurA :=
  ⟨d.isHurwitz_of_exponentiallyStable hA, d.exponentiallyStable_of_isHurwitz hA⟩

end LinearDAE

end powerlib.DAE
