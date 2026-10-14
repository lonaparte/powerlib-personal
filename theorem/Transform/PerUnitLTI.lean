import theorem.Circuits.Interconnection
import theorem.TMIO.ClaimElab

/-! # SI ↔ per-unit equivalence of linear models

Scope.
Per-unit transformation of a continuous-time linear model:
* state bases `b : ι → ℝ` (all nonzero): `x_SI = diag(b) x̂`;
* time base `ω_B > 0`: `τ = ω_B t`. Convention (A) (time in SI seconds) is `ω_B = 1`;
  convention (B) (per-unit time) is `ω_B = ω_s`;
* for input–output models, input bases `bu` and output bases `by`: `u = diag(bu) û`,
  `y = diag(by) ŷ`.
The per-unit matrices are `Â = ω_B⁻¹ D_x⁻¹ A D_x`, `B̂ = ω_B⁻¹ D_x⁻¹ B D_u`, `Ĉ = D_y⁻¹ C D_x`,
`D̂ = D_y⁻¹ D D_u`.

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

Family and connection conclusions.
`den_perUnit`: on the interconnection
family `Circuits.Interconnection.family`, the denotation of every attractive sentence and of
sampled contraction is its own pull-back along the per-unit transformation
`ic ↦ perUnit ic b₁ b₂ vb ib ω_B` (nonzero state and port bases, positive time base; conventions
(A) and (B) alike): SI and per-unit descriptions are stable together, with no premise on the
subsystems. Decay rates scale with `ω_B` and port passivity depends on the port bases; neither
is claimed.
-/

noncomputable section
namespace powerlib.Transform.PerUnit
open Matrix Linear LinearSystems

/-! ## Scalar and diagonal helpers -/

@[powerlib_foundation] theorem hasDerivAt_mulVec {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    {x : ℝ → ι → ℝ} {x' : ι → ℝ} {t : ℝ} (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => M *ᵥ x s) (M *ᵥ x') t := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).hasFDerivAt.comp_hasDerivAt t hx
  simpa [Function.comp_def] using h

@[powerlib_foundation] theorem inv_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ℂ} (hc : c ≠ 0) (M : Matrix ι ι ℂ) : (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases h : IsUnit M.det
  · have := Matrix.inv_smul' M (Units.mk0 c hc) h
    rw [Units.smul_def, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0] at this
    exact this
  · have h' : ¬ IsUnit (c • M).det := by
      rw [Matrix.det_smul]
      intro hu
      exact h ((IsUnit.mul_iff.mp hu).2)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h', Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[powerlib_foundation] theorem diagonal_inv_mul {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) :
    diagonal b⁻¹ * diagonal b = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; simp [hb i]

@[powerlib_foundation] theorem diagonal_mul_inv {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) :
    diagonal b * diagonal b⁻¹ = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; simp [hb i]

@[powerlib_foundation] theorem characteristicMatrix_smul {c : ℝ} (hc : c ≠ 0)
    (A : Matrix ι ι ℝ) (s : ℂ) :
    characteristicMatrix (c • A) s = (c : ℂ) • characteristicMatrix A (s / c) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  ext i j
  simp only [characteristicMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.one_apply, smul_eq_mul, Complex.coe_algebraMap]
  split_ifs <;> push_cast <;> field_simp

@[powerlib_foundation] theorem mulVec_cancel {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) (v : ι → ℝ) :
    diagonal b *ᵥ (diagonal b⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, diagonal_mul_inv hb, Matrix.one_mulVec]

@[powerlib_foundation] theorem mulVec_cancel' {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) (v : ι → ℝ) :
    diagonal b⁻¹ *ᵥ (diagonal b *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, diagonal_inv_mul hb, Matrix.one_mulVec]

/-- Scaling the state matrix by a positive constant does not change spectral stability. -/
@[powerlib_foundation] theorem spectrallyStable_smul_iff {c : ℝ} (hc : 0 < c) (A : Matrix ι ι ℝ) :
    SpectrallyStable (c • A) ↔ SpectrallyStable A := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hdet (s : ℂ) : (characteristicMatrix (c • A) s).det = 0 ↔
      (characteristicMatrix A (s / c)).det = 0 := by
    rw [characteristicMatrix_smul hc.ne', Matrix.det_smul]
    simp [hc']
  constructor
  · intro h s hs
    have h1 := h (s * c) ((hdet _).2 (by rwa [mul_div_cancel_right₀ _ hc']))
    have hre : (s * (c : ℂ)).re = s.re * c := by simp
    rw [hre] at h1
    exact (mul_neg_iff.mp h1).elim (fun h => absurd h.2 (not_lt.mpr hc.le)) (fun h => h.1)
  · intro h s hs
    have h1 := h _ ((hdet s).1 hs)
    have hre : (s / (c : ℂ)).re = s.re / c := by simp [Complex.div_ofReal_re]
    rw [hre] at h1
    exact (div_neg_iff.mp h1).elim (fun h => absurd h.2 (not_lt.mpr hc.le)) (fun h => h.1)

/-- A similarity on an arbitrary finite index conjugates the characteristic matrix. -/
@[powerlib_foundation] theorem characteristicMatrix_conj' {T S : Matrix ι ι ℝ} (hTS : T * S = 1)
    (A : Matrix ι ι ℝ) (s : ℂ) :
    characteristicMatrix (T * A * S) s =
      complexify T * characteristicMatrix A s * complexify S := by
  simp only [characteristicMatrix, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, complexify_mul_eq_one hTS]

/-- A similarity on an arbitrary finite index preserves spectral stability. -/
@[powerlib_foundation] theorem spectrallyStable_conj_iff {T S : Matrix ι ι ℝ} (hTS : T * S = 1)
    (hST : S * T = 1) (A : Matrix ι ι ℝ) :
    SpectrallyStable (T * A * S) ↔ SpectrallyStable A := by
  simp only [SpectrallyStable, characteristicMatrix_conj' hTS,
    Matrix.det_conj_of_mul_eq_one (complexify_mul_eq_one hTS) (complexify_mul_eq_one hST)]

/-! ## Autonomous models -/

/-- Per-unit state matrix `ω_B⁻¹ D⁻¹ A D` for state bases `b` and time base `ω_B`. -/
def puMatrix (b : ι → ℝ) (ωB : ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ωB⁻¹ • (diagonal b⁻¹ * A * diagonal b)

/-- SI solution ⇒ per-unit solution `x̂(τ) = D⁻¹ x(τ / ω_B)`. -/
@[powerlib_foundation] theorem solves_puMatrix_of {b : ι → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} {A : Matrix ι ι ℝ} {x : ℝ → ι → ℝ} (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t) :
    ∀ τ, HasDerivAt (fun τ => diagonal b⁻¹ *ᵥ x (τ / ωB))
      (puMatrix b ωB A *ᵥ (diagonal b⁻¹ *ᵥ x (τ / ωB))) τ := by
  intro τ
  have hτ : HasDerivAt (fun τ : ℝ => τ / ωB) ωB⁻¹ τ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id τ).mul_const ωB⁻¹
  have h := hasDerivAt_mulVec (diagonal b⁻¹) ((hx (τ / ωB)).scomp τ hτ)
  refine h.congr_deriv ?_
  simp only [puMatrix, Matrix.smul_mulVec, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec,
    mulVec_cancel hb]

/-- Per-unit solution ⇒ SI solution `x(t) = D x̂(ω_B t)`. -/
@[powerlib_foundation] theorem solves_of_puMatrix {b : ι → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} (hω : ωB ≠ 0) {A : Matrix ι ι ℝ} {y : ℝ → ι → ℝ}
    (hy : ∀ τ, HasDerivAt y (puMatrix b ωB A *ᵥ y τ) τ) :
    ∀ t, HasDerivAt (fun t => diagonal b *ᵥ y (ωB * t)) (A *ᵥ (diagonal b *ᵥ y (ωB * t))) t := by
  intro t
  have ht : HasDerivAt (fun t : ℝ => ωB * t) ωB t := by
    simpa using (hasDerivAt_id t).const_mul ωB
  have h := hasDerivAt_mulVec (diagonal b) ((hy (ωB * t)).scomp t ht)
  refine h.congr_deriv ?_
  simp only [puMatrix, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, mulVec_cancel hb, smul_smul,
    mul_inv_cancel₀ hω, one_smul]

/-- Exact solution correspondence between the SI and per-unit linear fields. -/
@[powerlib_foundation] theorem solves_puMatrix_iff {b : ι → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} (hω : ωB ≠ 0) (A : Matrix ι ι ℝ) (x : ℝ → ι → ℝ) :
    (∀ t, HasDerivAt x (A *ᵥ x t) t) ↔
      ∀ τ, HasDerivAt (fun τ => diagonal b⁻¹ *ᵥ x (τ / ωB))
        (puMatrix b ωB A *ᵥ (diagonal b⁻¹ *ᵥ x (τ / ωB))) τ := by
  refine ⟨solves_puMatrix_of hb, fun h => ?_⟩
  have h' := solves_of_puMatrix hb hω h
  simp only [mulVec_cancel hb, mul_div_cancel_left₀ _ hω] at h'
  exact h'

@[powerlib_foundation] theorem spectrallyStable_puMatrix_iff {b : ι → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} (hω : 0 < ωB) (A : Matrix ι ι ℝ) :
    SpectrallyStable (puMatrix b ωB A) ↔ SpectrallyStable A := by
  rw [puMatrix, spectrallyStable_smul_iff (inv_pos.mpr hω)]
  exact spectrallyStable_conj_iff (diagonal_inv_mul hb) (diagonal_mul_inv hb) A

variable {n : ℕ}

@[powerlib_foundation] theorem isHurwitz_puMatrix_iff {b : Fin n → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} (hω : 0 < ωB) (A : Matrix (Fin n) (Fin n) ℝ) :
    IsHurwitz (puMatrix b ωB A) ↔ IsHurwitz A := by
  rw [← spectrallyStable_iff_isHurwitz, ← spectrallyStable_iff_isHurwitz]
  exact spectrallyStable_puMatrix_iff hb hω A

/-- SI and per-unit linear fields satisfy the attractive sentences together (any nonzero state
bases, any positive time base: conventions (A) and (B) alike). Generic foundation. -/
@[powerlib_foundation] theorem holds_puMatrix_iff {b : Fin n → ℝ} (hb : ∀ i, b i ≠ 0)
    {ωB : ℝ} (hω : 0 < ωB) (A : Matrix (Fin n) (Fin n) ℝ) {P : Flow.Property}
    (hP : P.Attractive) :
    P.holds (affineLinearVectorField (puMatrix b ωB A) 0) 0 ↔
      P.holds (affineLinearVectorField A 0) 0 := by
  rw [holds_iff_isHurwitz 0 hP, holds_iff_isHurwitz 0 hP, isHurwitz_puMatrix_iff hb hω]

/-! ## Input–output models and transfer matrices -/

variable {p : ℕ}

/-- Per-unit plant for state bases `bx`, input bases `bu`, output bases `by'`. -/
def puIO (bx : Fin n → ℝ) (bu by' : Fin p → ℝ) (ωB : ℝ) (m : Plant n p) : Plant n p :=
  ⟨puMatrix bx ωB m.A, ωB⁻¹ • (diagonal bx⁻¹ * m.B * diagonal bu),
    diagonal by'⁻¹ * m.C * diagonal bx, diagonal by'⁻¹ * m.D * diagonal bu⟩

private lemma complexify_smul (c : ℝ) {m' n' : Type*} (M : Matrix m' n' ℝ) :
    complexify (c • M) = (c : ℂ) • complexify M := by
  ext i j; simp

private lemma complexify_mul_one {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ι → ℝ}
    (hb : ∀ i, b i ≠ 0) : complexify (diagonal b) * complexify (diagonal b⁻¹) = 1 := by
  rw [← complexify_mul, diagonal_mul_inv hb]; simp

private lemma complexify_inv_mul_one {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ι → ℝ}
    (hb : ∀ i, b i ≠ 0) : complexify (diagonal b⁻¹) * complexify (diagonal b) = 1 := by
  rw [← complexify_mul, diagonal_inv_mul hb]; simp

private lemma cancel_left {ι α : Type*} [Fintype ι] [DecidableEq ι] {b : ι → ℝ}
    (hb : ∀ i, b i ≠ 0) (X : Matrix ι α ℂ) :
    complexify (diagonal b) * (complexify (diagonal b⁻¹) * X) = X := by
  rw [← Matrix.mul_assoc, complexify_mul_one hb, Matrix.one_mul]

@[powerlib_foundation] theorem characteristicMatrix_puMatrix {bx : Fin n → ℝ}
    (hb : ∀ i, bx i ≠ 0) {ωB : ℝ} (hω : ωB ≠ 0) (A : Matrix (Fin n) (Fin n) ℝ) (s : ℂ) :
    characteristicMatrix (puMatrix bx ωB A) s =
      (ωB⁻¹ : ℂ) • (complexify (diagonal bx⁻¹) * characteristicMatrix A (s * ωB) *
        complexify (diagonal bx)) := by
  rw [puMatrix, characteristicMatrix_smul (inv_ne_zero hω),
    characteristicMatrix_conj (diagonal_inv_mul hb)]
  push_cast
  rw [div_inv_eq_mul]

/-- Per-unit transfer matrix: `Ĝ(ŝ) = D_y⁻¹ G(ω_B ŝ) D_u`. -/
@[powerlib_foundation] theorem transfer_puIO {bx : Fin n → ℝ} (hb : ∀ i, bx i ≠ 0)
    (bu by' : Fin p → ℝ) {ωB : ℝ} (hω : ωB ≠ 0) (m : Plant n p) (s : ℂ) :
    transfer (puIO bx bu by' ωB m) s =
      complexify (diagonal by'⁻¹) * transfer m (s * ωB) * complexify (diagonal bu) := by
  have hω' : (ωB : ℂ) ≠ 0 := by exact_mod_cast hω
  have hinv : (characteristicMatrix (puMatrix bx ωB m.A) s)⁻¹ =
      (ωB : ℂ) • (complexify (diagonal bx⁻¹) * (characteristicMatrix m.A (s * ωB))⁻¹ *
        complexify (diagonal bx)) := by
    rw [characteristicMatrix_puMatrix hb hω, inv_smul_matrix (inv_ne_zero hω'), inv_inv,
      inv_conj (complexify_inv_mul_one hb) (complexify_mul_one hb)]
  simp only [transfer, puIO, hinv, complexify_mul, complexify_smul, Matrix.mul_assoc,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, cancel_left hb, Matrix.mul_add, Matrix.add_mul]
  push_cast
  rw [inv_mul_cancel₀ hω', one_smul]

/-! ## Source–load interconnections in per unit -/

section Interconnection

open powerlib.Circuits

variable {n₁ n₂ : ℕ}

/-- Per-unit interconnection: the source (current in, voltage out) uses input bases `ib` and
output bases `vb`; the load (voltage in, current out) the reverse; state bases `b₁`, `b₂`;
common time base `ω_B`. -/
def perUnit (ic : Interconnection n₁ n₂ p) (b₁ : Fin n₁ → ℝ) (b₂ : Fin n₂ → ℝ)
    (vb ib : Fin p → ℝ) (ωB : ℝ) : Interconnection n₁ n₂ p :=
  ⟨puIO b₁ ib vb ωB ic.source, puIO b₂ vb ib ωB ic.load, by
    simp [puIO, ic.load_strictly_proper]⟩

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
    (perUnit ic b₁ b₂ vb ib ωB).returnDifference s = ic.returnDifference (s * ωB) := by
  simp only [Interconnection.returnDifference, Interconnection.sourceImpedance,
    Interconnection.loadAdmittance, perUnit, transfer_puIO hb₁ ib vb hω,
    transfer_puIO hb₂ vb ib hω]
  have hconj : 1 + complexify (diagonal vb⁻¹) * transfer ic.source (s * ωB) *
      complexify (diagonal ib) * (complexify (diagonal ib⁻¹) * transfer ic.load (s * ωB) *
        complexify (diagonal vb)) =
      complexify (diagonal vb⁻¹) * (1 + transfer ic.source (s * ωB) * transfer ic.load (s * ωB)) *
        complexify (diagonal vb) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, complexify_inv_mul_one hv,
      Matrix.mul_assoc, cancel_left hi]
  rw [hconj, Matrix.det_conj_of_mul_eq_one (complexify_inv_mul_one hv) (complexify_mul_one hv)]

/-- Impedance stability is invariant under per-unit scaling (positive time base). -/
@[powerlib_foundation] theorem impedanceStable_perUnit_iff (hb₁ : ∀ i, b₁ i ≠ 0)
    (hb₂ : ∀ i, b₂ i ≠ 0) (hv : ∀ k, vb k ≠ 0) (hi : ∀ k, ib k ≠ 0) (hω : 0 < ωB) :
    (perUnit ic b₁ b₂ vb ib ωB).ImpedanceStable ↔ ic.ImpedanceStable := by
  have hω' : (ωB : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  simp only [Interconnection.ImpedanceStable,
    returnDifference_perUnit ic hb₁ hb₂ hv hi hω.ne']
  constructor
  · intro h s hs
    have h' := h (s / ωB) (by rw [Complex.div_ofReal_re]; positivity)
    rwa [div_mul_cancel₀ _ hω'] at h'
  · intro h s hs
    exact h _ (by simp; positivity)

private lemma rcancel_left {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → ℝ} (hb : ∀ i, b i ≠ 0) (X : Matrix ι α ℝ) :
    diagonal b * (diagonal b⁻¹ * X) = X := by
  rw [← Matrix.mul_assoc, diagonal_mul_inv hb, Matrix.one_mul]

/-- The per-unit closed loop is the per-unit transformation of the SI closed loop, with the
stacked state bases. -/
@[powerlib_foundation] theorem closedLoopBlocks_perUnit (hv : ∀ k, vb k ≠ 0)
    (hi : ∀ k, ib k ≠ 0) :
    (perUnit ic b₁ b₂ vb ib ωB).closedLoopBlocks =
      puMatrix (Sum.elim b₁ b₂) ωB ic.closedLoopBlocks := by
  have hinv : (Sum.elim b₁ b₂)⁻¹ = Sum.elim b₁⁻¹ b₂⁻¹ := by
    funext i; cases i <;> rfl
  simp only [Interconnection.closedLoopBlocks, generated.closedLoopBlocks_spec]
  rw [puMatrix, hinv, ← fromBlocks_diagonal, ← fromBlocks_diagonal, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_smul]
  simp only [perUnit, puIO, puMatrix, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_assoc, Matrix.smul_mul, rcancel_left hi, rcancel_left hv, neg_zero, sub_zero,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, smul_sub, smul_neg]

/-- Closed-loop pole stability is invariant under per-unit scaling, with no premise on the
subsystems. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem isHurwitz_closedLoop_perUnit_iff (hb₁ : ∀ i, b₁ i ≠ 0)
    (hb₂ : ∀ i, b₂ i ≠ 0) (hv : ∀ k, vb k ≠ 0) (hi : ∀ k, ib k ≠ 0) (hω : 0 < ωB) :
    IsHurwitz (perUnit ic b₁ b₂ vb ib ωB).closedLoop.A ↔ IsHurwitz ic.closedLoop.A := by
  simp only [Interconnection.closedLoop_A, Interconnection.closedLoopA,
    ← spectrallyStable_iff_isHurwitz, spectrallyStable_reindex]
  rw [closedLoopBlocks_perUnit ic hv hi]
  exact spectrallyStable_puMatrix_iff (fun i => by cases i <;> simp [hb₁, hb₂]) hω _

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
      (fun ic => perUnit ic b₁ b₂ vb ib ωB) ⁻¹' Interconnection.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [Interconnection.family_isLinear.den_hurwitz hP]
  ext ic
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  exact (isHurwitz_closedLoop_perUnit_iff ic hb₁ hb₂ hv hi hω).symm

end powerlib.Transform.PerUnit
