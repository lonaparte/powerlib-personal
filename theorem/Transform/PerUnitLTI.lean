import theorem.Transform.Rebase

/-! # SI ↔ per-unit equivalence of linear models

Scope.
Per-unit transformation of a continuous-time linear model:
* state bases `b : ι → ℝ` (all nonzero): `x_SI = diag(b) x̂`;
* time base `ω_B > 0`: `τ = ω_B t`. Convention (A) (time in SI seconds) is `ω_B = 1`;
  convention (B) (per-unit time) is `ω_B = ω_s`;
* for input–output models, input bases `bu` and output bases `by`: `u = diag(bu) û`,
  `y = diag(by) ŷ`.
The per-unit matrices are `Â = ω_B⁻¹ D_x⁻¹ A D_x`, `B̂ = ω_B⁻¹ D_x⁻¹ B D_u`, `Ĉ = D_y⁻¹ C D_x`,
`D̂ = D_y⁻¹ D D_u`. This is the change of bases of `theorem/Transform/Rebase.lean` with diagonal
bases (state coordinates `D_x⁻¹` with inverse `D_x`, input `D_u`, output `D_y⁻¹`, time base
`ω_B`), and every result below is an instance of the general one.

Source: work-sync `theory/T-PU.md` §1.2 / §1.6 (state and time bases, conventions (A) and (B)),
§1.11 (per-unit impedance and loop gain), §2.8 (SI and p.u. implementations must agree);
`codes/README.md` "three-mode consistency" (SI / PU + SI time / PU + PU time) is the numerical
counterpart of these theorems.

Results.
Foundation results (generic, any matrices): solutions correspond exactly
(`solves_puMatrix_iff`, for curves given by their derivative at every time); spectral stability
and the Hurwitz property are invariant (`spectrallyStable_puMatrix_iff`,
`isHurwitz_puMatrix_iff`), hence every attractive sentence of the zero-input linear field
(`holds_puMatrix_iff`); the per-unit transfer matrix
is `Ĝ(ŝ) = D_y⁻¹ G(ω_B ŝ) D_u` (`transfer_puIO`). For a source–load interconnection
(`Circuits.Interconnection`) with voltage/current port bases, the return difference is only
re-parametrised (`returnDifference_perUnit`), so `ImpedanceStable` is invariant
(`impedanceStable_perUnit_iff`), and the closed-loop state matrix is the per-unit transform of
the SI one (`closedLoopBlocks_perUnit`), with the same Hurwitz property
(`isHurwitz_closedLoop_perUnit_iff`). These are change-of-units statements (static evidence).
The diagonal helpers `diagonal_inv_mul`, `diagonal_mul_inv`, `mulVec_cancel`, `mulVec_cancel'` supply
the invertibility of the bases.

Family and connection conclusions.
`den_perUnit`: on the interconnection
family `Circuits.Interconnection.family`, the denotation of every attractive sentence and of
sampled contraction is its own pull-back along the per-unit transformation
`ic ↦ perUnit ic b₁ b₂ vb ib ω_B` (nonzero state and port bases, positive time base; conventions
(A) and (B) alike): SI and per-unit descriptions are stable together, with no premise on the
subsystems. `den_perUnit_unitTime`: with time in SI seconds (convention (A), `ω_B = 1`), every flow
sentence. `den_perUnit_timeScale`: with any positive time base (convention (B) included), every flow
sentence with its decay rate scaled by `ω_B` (`Flow.Property.timeScale`): the per-unit model decays
at the rate `a` per unit of per-unit time exactly when the SI model decays at the rate `ω_B a` per
second. Port passivity depends on the port bases and is not claimed.
-/

noncomputable section
namespace powerlib.Transform.PerUnit
open Matrix Linear LinearSystems Rebase

/-! ## Diagonal helpers -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[powerlib_foundation] theorem diagonal_inv_mul {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) :
    diagonal b⁻¹ * diagonal b = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; simp [hb i]

@[powerlib_foundation] theorem diagonal_mul_inv {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) :
    diagonal b * diagonal b⁻¹ = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; simp [hb i]

@[powerlib_foundation] theorem mulVec_cancel {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) (v : ι → ℝ) :
    diagonal b *ᵥ (diagonal b⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, diagonal_mul_inv hb, Matrix.one_mulVec]

@[powerlib_foundation] theorem mulVec_cancel' {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) (v : ι → ℝ) :
    diagonal b⁻¹ *ᵥ (diagonal b *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, diagonal_inv_mul hb, Matrix.one_mulVec]

/-! ## Autonomous models -/

/-- Per-unit state matrix `ω_B⁻¹ D⁻¹ A D` for state bases `b` and time base `ω_B`. -/
def puMatrix (b : ι → ℝ) (ωB : ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  rebaseMatrix (diagonal b⁻¹) (diagonal b) ωB A

/-- SI solution ⇒ per-unit solution `x̂(τ) = D⁻¹ x(τ / ω_B)`. -/
@[powerlib_foundation] theorem solves_puMatrix_of {b : ι → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} {A : Matrix ι ι ℝ} {x : ℝ → ι → ℝ} (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t) :
    ∀ τ, HasDerivAt (fun τ => diagonal b⁻¹ *ᵥ x (τ / ωB))
      (puMatrix b ωB A *ᵥ (diagonal b⁻¹ *ᵥ x (τ / ωB))) τ :=
  solves_rebaseMatrix_of (diagonal_mul_inv hb) hx

/-- Per-unit solution ⇒ SI solution `x(t) = D x̂(ω_B t)`. -/
@[powerlib_foundation] theorem solves_of_puMatrix {b : ι → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} (hω : ωB ≠ 0) {A : Matrix ι ι ℝ} {y : ℝ → ι → ℝ}
    (hy : ∀ τ, HasDerivAt y (puMatrix b ωB A *ᵥ y τ) τ) :
    ∀ t, HasDerivAt (fun t => diagonal b *ᵥ y (ωB * t)) (A *ᵥ (diagonal b *ᵥ y (ωB * t))) t :=
  solves_of_rebaseMatrix (diagonal_mul_inv hb) hω hy

/-- Exact solution correspondence between the SI and per-unit linear fields. -/
@[powerlib_foundation] theorem solves_puMatrix_iff {b : ι → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} (hω : ωB ≠ 0) (A : Matrix ι ι ℝ) (x : ℝ → ι → ℝ) :
    (∀ t, HasDerivAt x (A *ᵥ x t) t) ↔
      ∀ τ, HasDerivAt (fun τ => diagonal b⁻¹ *ᵥ x (τ / ωB))
        (puMatrix b ωB A *ᵥ (diagonal b⁻¹ *ᵥ x (τ / ωB))) τ :=
  solves_rebaseMatrix_iff (diagonal_mul_inv hb) hω A x

@[powerlib_foundation] theorem spectrallyStable_puMatrix_iff {b : ι → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} (hω : 0 < ωB) (A : Matrix ι ι ℝ) :
    SpectrallyStable (puMatrix b ωB A) ↔ SpectrallyStable A :=
  spectrallyStable_rebaseMatrix_iff (diagonal_inv_mul hb) (diagonal_mul_inv hb) hω A

variable {n : ℕ}

@[powerlib_foundation] theorem isHurwitz_puMatrix_iff {b : Fin n → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} (hω : 0 < ωB) (A : Matrix (Fin n) (Fin n) ℝ) :
    IsHurwitz (puMatrix b ωB A) ↔ IsHurwitz A :=
  isHurwitz_rebaseMatrix_iff (diagonal_inv_mul hb) (diagonal_mul_inv hb) hω A

/-- SI and per-unit linear fields satisfy the attractive sentences together (any nonzero state
bases, any positive time base: conventions (A) and (B) alike). Generic foundation. -/
@[powerlib_foundation] theorem holds_puMatrix_iff {b : Fin n → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} (hω : 0 < ωB) (A : Matrix (Fin n) (Fin n) ℝ) {P : Flow.Property}
    (hP : P.Attractive) :
    P.holds (affineLinearVectorField (puMatrix b ωB A) 0) 0 ↔
      P.holds (affineLinearVectorField A 0) 0 :=
  holds_rebaseMatrix_iff (diagonal_inv_mul hb) (diagonal_mul_inv hb) hω A hP

/-! ## Input–output models and transfer matrices -/

variable {p : ℕ}

/-- Per-unit plant for state bases `bx`, input bases `bu`, output bases `by'`. -/
def puIO (bx : Fin n → ℝ) (bu by' : Fin p → ℝ) (ωB : ℝ) (m : Plant n p) : Plant n p :=
  plant m (diagonal bx⁻¹) (diagonal bx) ωB (diagonal bu) (diagonal by'⁻¹)

@[powerlib_foundation] theorem characteristicMatrix_puMatrix {bx : Fin n → ℝ}
    (hb : ∀ i, bx i ≠ 0) {ωB : ℝ} (hω : ωB ≠ 0) (A : Matrix (Fin n) (Fin n) ℝ) (s : ℂ) :
    characteristicMatrix (puMatrix bx ωB A) s =
      (ωB⁻¹ : ℂ) • (complexify (diagonal bx⁻¹) * characteristicMatrix A (s * ωB) *
        complexify (diagonal bx)) :=
  characteristicMatrix_rebaseMatrix (diagonal_inv_mul hb) hω A s

/-- Per-unit transfer matrix: `Ĝ(ŝ) = D_y⁻¹ G(ω_B ŝ) D_u`. -/
@[powerlib_foundation] theorem transfer_puIO {bx : Fin n → ℝ} (hb : ∀ i, bx i ≠ 0)
    (bu by' : Fin p → ℝ) {ωB : ℝ} (hω : ωB ≠ 0) (m : Plant n p) (s : ℂ) :
    transfer (puIO bx bu by' ωB m) s =
      complexify (diagonal by'⁻¹) * transfer m (s * ωB) * complexify (diagonal bu) :=
  transfer_rebase (diagonal_inv_mul hb) (diagonal_mul_inv hb) hω _ _ m s

/-! ## Source–load interconnections in per unit -/

section Interconnection

open powerlib.Circuits

variable {n₁ n₂ : ℕ}

/-- The per-unit bases of an interconnection: state bases `b₁`, `b₂`, port voltage bases `vb`,
port current bases `ib`, time base `ω_B`. -/
def perUnitBases (b₁ : Fin n₁ → ℝ) (b₂ : Fin n₂ → ℝ) (vb ib : Fin p → ℝ) (ωB : ℝ) :
    Bases n₁ n₂ p :=
  ⟨diagonal b₁⁻¹, diagonal b₁, diagonal b₂⁻¹, diagonal b₂, diagonal vb⁻¹, diagonal vb,
    diagonal ib⁻¹, diagonal ib, ωB⟩

/-- Per-unit interconnection: the source (current in, voltage out) uses input bases `ib` and
output bases `vb`; the load (voltage in, current out) the reverse; state bases `b₁`, `b₂`;
common time base `ω_B`. -/
def perUnit (ic : Interconnection n₁ n₂ p) (b₁ : Fin n₁ → ℝ) (b₂ : Fin n₂ → ℝ)
    (vb ib : Fin p → ℝ) (ωB : ℝ) : Interconnection n₁ n₂ p :=
  interconnection ic (perUnitBases b₁ b₂ vb ib ωB)

variable (ic : Interconnection n₁ n₂ p) {b₁ : Fin n₁ → ℝ} {b₂ : Fin n₂ → ℝ} {vb ib : Fin p → ℝ}
  {ωB : ℝ}

/-- The per-unit source and load are the per-unit transforms of the SI ones. -/
@[powerlib_foundation] theorem source_perUnit :
    (perUnit ic b₁ b₂ vb ib ωB).source = puIO b₁ ib vb ωB ic.source := rfl

@[powerlib_foundation] theorem load_perUnit :
    (perUnit ic b₁ b₂ vb ib ωB).load = puIO b₂ vb ib ωB ic.load := rfl

/-- The per-unit return difference is the SI return difference at `ω_B ŝ`. -/
@[powerlib_foundation] theorem returnDifference_perUnit (hb₁ : ∀ i, b₁ i ≠ 0)
    (hb₂ : ∀ i, b₂ i ≠ 0) (hv : ∀ k, vb k ≠ 0) (hi : ∀ k, ib k ≠ 0) (hω : ωB ≠ 0) (s : ℂ) :
    (perUnit ic b₁ b₂ vb ib ωB).returnDifference s = ic.returnDifference (s * ωB) :=
  returnDifference_rebase (diagonal_mul_inv hb₁) (diagonal_mul_inv hb₂) (diagonal_mul_inv hv)
    (diagonal_mul_inv hi) hω s

/-- Impedance stability is invariant under per-unit scaling (positive time base). -/
@[powerlib_foundation] theorem impedanceStable_perUnit_iff (hb₁ : ∀ i, b₁ i ≠ 0)
    (hb₂ : ∀ i, b₂ i ≠ 0) (hv : ∀ k, vb k ≠ 0) (hi : ∀ k, ib k ≠ 0) (hω : 0 < ωB) :
    (perUnit ic b₁ b₂ vb ib ωB).ImpedanceStable ↔ ic.ImpedanceStable :=
  impedanceStable_rebase_iff (diagonal_mul_inv hb₁) (diagonal_mul_inv hb₂) (diagonal_mul_inv hv)
    (diagonal_mul_inv hi) hω

/-- The per-unit closed loop is the per-unit transformation of the SI closed loop, with the
stacked state bases. -/
@[powerlib_foundation] theorem closedLoopBlocks_perUnit (hv : ∀ k, vb k ≠ 0)
    (hi : ∀ k, ib k ≠ 0) :
    (perUnit ic b₁ b₂ vb ib ωB).closedLoopBlocks =
      puMatrix (Sum.elim b₁ b₂) ωB ic.closedLoopBlocks := by
  rw [perUnit, closedLoopBlocks_rebase (diagonal_mul_inv hv) (diagonal_mul_inv hi), puMatrix,
    rebaseMatrix]
  have hinv : (Sum.elim b₁ b₂)⁻¹ = Sum.elim b₁⁻¹ b₂⁻¹ := by
    funext i; cases i <;> rfl
  rw [hinv, ← fromBlocks_diagonal, ← fromBlocks_diagonal]
  rfl

/-- Closed-loop pole stability is invariant under per-unit scaling, with no premise on the
subsystems. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem isHurwitz_closedLoop_perUnit_iff (hb₁ : ∀ i, b₁ i ≠ 0)
    (hb₂ : ∀ i, b₂ i ≠ 0) (hv : ∀ k, vb k ≠ 0) (hi : ∀ k, ib k ≠ 0) (hω : 0 < ωB) :
    IsHurwitz (perUnit ic b₁ b₂ vb ib ωB).closedLoop.A ↔ IsHurwitz ic.closedLoop.A :=
  isHurwitz_closedLoop_rebase_iff (diagonal_mul_inv hb₁) (diagonal_mul_inv hb₂)
    (diagonal_mul_inv hv) (diagonal_mul_inv hi) hω

end Interconnection

/-! ## The per-unit connection on the interconnection family -/

open powerlib.Circuits in
/-- SI and per-unit descriptions of a source–load interconnection are stable together: on the
interconnection family, the denotation of every attractive sentence and of sampled contraction
is its own pull-back along the per-unit transformation (nonzero state and port bases, positive
time base). -/
@[powerlib_domain] theorem den_perUnit {n₁ n₂ : ℕ} {b₁ : Fin n₁ → ℝ} {b₂ : Fin n₂ → ℝ}
    {vb ib : Fin p → ℝ} {ωB : ℝ} (hb₁ : ∀ i, b₁ i ≠ 0) (hb₂ : ∀ i, b₂ i ≠ 0)
    (hv : ∀ k, vb k ≠ 0) (hi : ∀ k, ib k ≠ 0) (hω : 0 < ωB) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% ((Interconnection.family (n₁ := n₁) (n₂ := n₂) (p := p)).den (.flow P) =
      (fun ic => perUnit ic b₁ b₂ vb ib ωB) ⁻¹' Interconnection.family.den (.flow P)) :=
  den_rebase (diagonal_mul_inv hb₁) (diagonal_mul_inv hb₂) (diagonal_mul_inv hv)
    (diagonal_mul_inv hi) hω hP

open powerlib.Circuits in
/-- With time in SI seconds (convention (A), `ω_B = 1`), SI and per-unit descriptions satisfy
every flow sentence together. -/
@[powerlib_domain] theorem den_perUnit_unitTime {n₁ n₂ : ℕ} {b₁ : Fin n₁ → ℝ}
    {b₂ : Fin n₂ → ℝ} {vb ib : Fin p → ℝ} (hb₁ : ∀ i, b₁ i ≠ 0) (hb₂ : ∀ i, b₂ i ≠ 0)
    (hv : ∀ k, vb k ≠ 0) (hi : ∀ k, ib k ≠ 0) (P : Flow.Property) :
    connection% ((Interconnection.family (n₁ := n₁) (n₂ := n₂) (p := p)).den (.flow P) =
      (fun ic => perUnit ic b₁ b₂ vb ib 1) ⁻¹' Interconnection.family.den (.flow P)) :=
  den_rebase_unitTime (diagonal_mul_inv hb₁) (diagonal_mul_inv hb₂) (diagonal_mul_inv hv)
    (diagonal_mul_inv hi) rfl P

open powerlib.Circuits in
/-- With any positive time base (conventions (A) and (B) alike), the per-unit description satisfies
a flow sentence `P` exactly when the SI description satisfies `P.timeScale ω_B`: decay at the rate
`a` per unit of `τ = ω_B t` is decay at the rate `ω_B a` per second, and every other sentence is
unchanged. -/
@[powerlib_domain] theorem den_perUnit_timeScale {n₁ n₂ : ℕ} {b₁ : Fin n₁ → ℝ} {b₂ : Fin n₂ → ℝ}
    {vb ib : Fin p → ℝ} {ωB : ℝ} (hb₁ : ∀ i, b₁ i ≠ 0) (hb₂ : ∀ i, b₂ i ≠ 0)
    (hv : ∀ k, vb k ≠ 0) (hi : ∀ k, ib k ≠ 0) (hω : 0 < ωB) (P : Flow.Property) :
    connection% ((Interconnection.family (n₁ := n₁) (n₂ := n₂) (p := p)).den
        (.flow (P.timeScale ωB)) =
      (fun ic => perUnit ic b₁ b₂ vb ib ωB) ⁻¹' Interconnection.family.den (.flow P)) :=
  den_rebase_timeScale (β := perUnitBases b₁ b₂ vb ib ωB) (diagonal_mul_inv hb₁)
    (diagonal_mul_inv hb₂) (diagonal_mul_inv hv) (diagonal_mul_inv hi) hω P

end powerlib.Transform.PerUnit
