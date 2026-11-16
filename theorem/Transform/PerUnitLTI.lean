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
`ω_B`): its laws are the general ones, applied at these bases.

Source: work-sync `theory/T-PU.md` §1.2 / §1.6 (state and time bases, conventions (A) and (B)),
§1.11 (per-unit impedance and loop gain), §2.8 (SI and p.u. implementations must agree);
`codes/README.md` "three-mode consistency" (SI / PU + SI time / PU + PU time) is the numerical
counterpart of these theorems.

Results.
* Every law of the per-unit transformation is the general law of `theorem/Transform/Rebase.lean`
  at the diagonal bases, used directly: `puMatrix b ω_B A` is
  `rebaseMatrix (diagonal b⁻¹) (diagonal b) ω_B A`, `puIO` is `Rebase.plant` and
  `perUnit ic b₁ b₂ vb ib ω_B` is `interconnection ic (perUnitBases b₁ b₂ vb ib ω_B)`; the
  invertibility obligations are `diagonal_inv_mul hb` and `diagonal_mul_inv hb`. So solutions
  correspond (`Rebase.solves_rebaseMatrix_iff`, for curves given by their derivative at every
  time); spectral stability and every attractive sentence of the zero-input linear field are
  invariant for `ω_B > 0` (`Rebase.spectrallyStable_rebaseMatrix_iff`,
  `Rebase.holds_rebaseMatrix_iff`); the per-unit transfer matrix is `Ĝ(ŝ) = D_y⁻¹ G(ω_B ŝ) D_u`
  (`Rebase.transfer_rebase`). For a source–load interconnection (`Grid.Interconnection`) with
  voltage/current port bases, the return difference is only re-parametrised
  (`Rebase.returnDifference_rebase`), so `ImpedanceStable` is invariant
  (`Rebase.impedanceStable_rebase_iff`).
* `source_perUnit`, `load_perUnit`: the per-unit source and load are the per-unit transforms of
  the SI ones; `closedLoopBlocks_perUnit`: the per-unit closed loop is the per-unit transform of
  the SI one, with the stacked state bases.
* The diagonal helpers `diagonal_inv_mul`, `diagonal_mul_inv`, `mulVec_cancel`, `mulVec_cancel'`
  supply the invertibility of the bases.

Family and connection conclusions. Scaffold: `theorem/Transform/Rebase.agda` (per-unit bases are
one of its changes of bases). On the interconnection family `Grid.Interconnection.family`, the
per-unit connection is `Rebase.den_rebase` and `Rebase.den_rebase_timeScale` at
`β = perUnitBases b₁ b₂ vb ib ω_B` (nonzero state and port bases, positive time base): the
denotation of every attractive sentence and of sampled contraction is its own pull-back along
`ic ↦ perUnit ic b₁ b₂ vb ib ω_B` (conventions (A) and (B) alike), so SI and per-unit
descriptions are stable together, with no premise on the subsystems; and every flow sentence is
pulled back with its decay rate scaled by `ω_B` (`Flow.Property.timeScale`, unchanged at
`ω_B = 1`, convention (A)): the per-unit model decays at the rate `a` per unit of per-unit time
exactly when the SI model decays at the rate `ω_B a` per second. Port passivity depends on the
port bases and is not claimed.
-/

noncomputable section
namespace powerlib.Transform.PerUnit
open Matrix Linear LinearSystems Rebase

/-! ## Diagonal helpers -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[tmio T, powerlib_foundation] theorem diagonal_inv_mul {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) :
    diagonal b⁻¹ * diagonal b = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; simp [hb i]

@[tmio T, powerlib_foundation] theorem diagonal_mul_inv {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) :
    diagonal b * diagonal b⁻¹ = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; simp [hb i]

@[tmio T, powerlib_foundation] theorem mulVec_cancel {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) (v : ι → ℝ) :
    diagonal b *ᵥ (diagonal b⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, diagonal_mul_inv hb, Matrix.one_mulVec]

@[tmio T, powerlib_foundation] theorem mulVec_cancel' {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) (v : ι → ℝ) :
    diagonal b⁻¹ *ᵥ (diagonal b *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, diagonal_inv_mul hb, Matrix.one_mulVec]

/-! ## Autonomous models -/

/-- Per-unit state matrix `ω_B⁻¹ D⁻¹ A D` for state bases `b` and time base `ω_B`. -/
def puMatrix (b : ι → ℝ) (ωB : ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  rebaseMatrix (diagonal b⁻¹) (diagonal b) ωB A

variable {n : ℕ}

/-! ## Input–output models -/

variable {p : ℕ}

/-- Per-unit plant for state bases `bx`, input bases `bu`, output bases `by'`. -/
def puIO (bx : Fin n → ℝ) (bu by' : Fin p → ℝ) (ωB : ℝ) (m : Plant n p) : Plant n p :=
  plant m (diagonal bx⁻¹) (diagonal bx) ωB (diagonal bu) (diagonal by'⁻¹)

/-! ## Source–load interconnections in per unit -/

section Interconnection

open powerlib.Grid

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
@[tmio M, powerlib_domain] theorem source_perUnit :
    (perUnit ic b₁ b₂ vb ib ωB).source = puIO b₁ ib vb ωB ic.source := rfl

@[tmio M, powerlib_domain] theorem load_perUnit :
    (perUnit ic b₁ b₂ vb ib ωB).load = puIO b₂ vb ib ωB ic.load := rfl

/-- The per-unit closed loop is the per-unit transformation of the SI closed loop, with the
stacked state bases. -/
@[tmio M, powerlib_domain] theorem closedLoopBlocks_perUnit (hv : ∀ k, vb k ≠ 0)
    (hi : ∀ k, ib k ≠ 0) :
    (perUnit ic b₁ b₂ vb ib ωB).closedLoopBlocks =
      puMatrix (Sum.elim b₁ b₂) ωB ic.closedLoopBlocks := by
  rw [perUnit, closedLoopBlocks_rebase (diagonal_mul_inv hv) (diagonal_mul_inv hi), puMatrix,
    rebaseMatrix]
  have hinv : (Sum.elim b₁ b₂)⁻¹ = Sum.elim b₁⁻¹ b₂⁻¹ := by
    funext i; cases i <;> rfl
  rw [hinv, ← fromBlocks_diagonal, ← fromBlocks_diagonal]
  rfl

end Interconnection

end powerlib.Transform.PerUnit
