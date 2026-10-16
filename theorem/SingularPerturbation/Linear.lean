import theorem.Linear.Stability
import theorem.Criteria.Lyapunov
import theorem.Criteria.Hurwitz

/-! # Linear singularly perturbed systems: Kokotović's two-time-scale stability theorem

A linear two-time-scale system with Hurwitz boundary-layer and reduced matrices is exponentially
stable for all sufficiently small `ε`, with an explicit `ε*`.

Model boundary.
* Continuous time, constant matrices, `n` slow states `x`, `m` fast states `z`, small parameter
  `ε > 0`, no input:
```
ẋ = A₁₁ x + A₁₂ z,        ε ż = A₂₁ x + A₂₂ z .
```
* `LinearSP.blockMatrix ε = [[A₁₁, A₁₂], [A₂₁/ε, A₂₂/ε]]` on `Fin n ⊕ Fin m`;
  `LinearSP.stateMatrix ε` is the same matrix with the state ordered `(x₁, …, xₙ, z₁, …, z_m)`
  (reindexed by `finSumFinEquiv`). Its behaviour is the Flow semantics of LeanForControl's affine
  linear field `affineLinearVectorField (stateMatrix ε) 0` on `EuclideanSpace ℝ (Fin (n + m))`.
* Linear, time invariant, autonomous, constant `ε`; the theorem is about the full two-time-scale
  linear system, not about any particular converter; every statement is about arbitrary
  matrices. Nonlinear and finite-horizon approximation statements are in other modules.

Source: work-sync theory/T-singular-perturbation.md §1.1–§1.4, theory/T-tikhonov.md §1.1–§1.2
(the stability hypotheses `Re λ(A_y) < 0` and the reduced slow system); the linear
two-time-scale theorem is Kokotović–Khalil–O'Reilly (1986) Ch. 2, cited in both notes.

Results.
* `exists_epsStar_exponentiallyStable` — if the boundary-layer matrix `A₂₂` is Hurwitz and the
  reduced (Schur-complement) matrix `A₀ = A₁₁ - A₁₂ A₂₂⁻¹ A₂₁` is Hurwitz, there is `ε* > 0` such
  that for every `ε ∈ (0, ε*)` the full matrix is Hurwitz and the zero-input system is globally
  exponentially stable (`Flow.GloballyExponentiallyStable` of the affine linear field, through
  `Linear.globallyExponentiallyStable_of_isHurwitz`).
* `isHurwitz_of_lt_epsStar` — the proof is Kokotović's composite Lyapunov argument, not spectral
  continuity: in the coordinates `η = z + A₂₂⁻¹ A₂₁ x`, `V = xᵀ P₀ x + ηᵀ P₂ η` with
  `P₀ A₀ + A₀ᵀ P₀ = -I`, `P₂ A₂₂ + A₂₂ᵀ P₂ = -I` (LeanForControl's Lyapunov solutions). Given
  these, `ε*` is explicit: `epsStar P₀ P₂ = 1 / (2 c + 1)` with
  `c = S (2S + 1)/2 + S₃`, `S = |P₀ A₁₂|₁ + |P₂ L A₀|₁`, `S₃ = |P₂ L A₁₂|₁`, `L = A₂₂⁻¹ A₂₁`,
  and `|N|₁ = Σᵢⱼ |Nᵢⱼ|`. Along the way: `V̇ ≤ -|x|²/4 - |η|²/2`.
* `isUnit_det_of_isHurwitz` — a Hurwitz matrix is invertible (the case `r = 0` of
  `Criteria.det_smul_sub_ne_zero_of_isHurwitz`). The general Lyapunov-inequality
  criterion (`Criteria.re_neg_of_lyapunov`: symmetric positive definite `P` with `wᵀ P M w < 0`
  for `w ≠ 0` forces every complex eigenvalue of `M` into the open left half-plane) is in
  `theorem/Criteria/Lyapunov.lean`.
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Matrix

/-! ## A Hurwitz matrix is invertible -/

/-- A Hurwitz matrix is invertible: `det(0 · 1 − A) ≠ 0`
(`Criteria.det_smul_sub_ne_zero_of_isHurwitz`). -/
@[powerlib_foundation] theorem isUnit_det_of_isHurwitz {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : LinearSystems.IsHurwitz A) : IsUnit A.det :=
  isUnit_iff_ne_zero.mpr fun h0 => Criteria.det_smul_sub_ne_zero_of_isHurwitz hA le_rfl (by
    rw [zero_smul, zero_sub, det_neg, h0, mul_zero])

/-! ## Elementary quadratic bounds -/

/-- `Σᵢⱼ |Nᵢⱼ|`. -/
def absSum {k l : Type*} [Fintype k] [Fintype l] (N : Matrix k l ℝ) : ℝ := ∑ i, ∑ j, |N i j|

@[powerlib_foundation] theorem absSum_nonneg {k l : Type*} [Fintype k] [Fintype l]
    (N : Matrix k l ℝ) : 0 ≤ absSum N :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

@[powerlib_foundation] private lemma sq_le_dotProduct_self {k : Type*} [Fintype k] (u : k → ℝ)
    (i : k) : u i ^ 2 ≤ u ⬝ᵥ u := by
  have : u ⬝ᵥ u = ∑ j, u j ^ 2 := by simp [dotProduct, sq]
  rw [this]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)

@[powerlib_foundation] theorem dotProduct_self_nonneg' {k : Type*} [Fintype k] (u : k → ℝ) :
    0 ≤ u ⬝ᵥ u := by
  simpa [dotProduct, sq] using Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (u j)

/-- `|uᵀ N w| ≤ |N|₁ (δ |u|² + |w|²/δ) / 2` for `δ > 0`. -/
@[powerlib_foundation] theorem abs_dotProduct_mulVec_le {k l : Type*} [Fintype k] [Fintype l]
    (N : Matrix k l ℝ) (u : k → ℝ) (w : l → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    |u ⬝ᵥ (N *ᵥ w)| ≤ absSum N * (δ * (u ⬝ᵥ u) + (w ⬝ᵥ w) / δ) / 2 := by
  have hpt : ∀ i j, |N i j * (u i * w j)| ≤ |N i j| * ((δ * (u ⬝ᵥ u) + (w ⬝ᵥ w) / δ) / 2) := by
    intro i j
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hu := sq_le_dotProduct_self u i
    have hw := sq_le_dotProduct_self w j
    have hamgm : 2 * |u i * w j| ≤ δ * u i ^ 2 + w j ^ 2 / δ := by
      have hid : δ * u i ^ 2 + w j ^ 2 / δ - 2 * (|u i| * |w j|) = (δ * |u i| - |w j|) ^ 2 / δ := by
        field_simp
        rw [sub_sq, mul_pow, sq_abs, sq_abs]
        ring
      have : 0 ≤ (δ * |u i| - |w j|) ^ 2 / δ := div_nonneg (sq_nonneg _) hδ.le
      rw [abs_mul]
      linarith
    have hmono : δ * u i ^ 2 + w j ^ 2 / δ ≤ δ * (u ⬝ᵥ u) + (w ⬝ᵥ w) / δ := by
      gcongr
    linarith
  calc |u ⬝ᵥ (N *ᵥ w)| = |∑ i, ∑ j, N i j * (u i * w j)| := by
        congr 1
        simp only [dotProduct, mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ ∑ i, |∑ j, N i j * (u i * w j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |N i j * (u i * w j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |N i j| * ((δ * (u ⬝ᵥ u) + (w ⬝ᵥ w) / δ) / 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = absSum N * (δ * (u ⬝ᵥ u) + (w ⬝ᵥ w) / δ) / 2 := by
        rw [mul_div_assoc]
        simp only [absSum, Finset.sum_mul]

/-- For `P = Pᵀ` with `P A + Aᵀ P = -I`: `xᵀ P A x = -|x|²/2`. -/
@[powerlib_foundation] theorem dotProduct_mulVec_lyapunov {k : ℕ} {A P : Matrix (Fin k) (Fin k) ℝ}
    (hP : Pᵀ = P) (hL : P * A + Aᵀ * P = -1) (x : Fin k → ℝ) :
    x ⬝ᵥ (P *ᵥ (A *ᵥ x)) = -(x ⬝ᵥ x) / 2 := by
  have h := congrArg (fun Q => x ⬝ᵥ (Q *ᵥ x)) hL
  simp only [add_mulVec, dotProduct_add, ← mulVec_mulVec, neg_mulVec, one_mulVec,
    dotProduct_neg] at h
  have h2 : x ⬝ᵥ (Aᵀ *ᵥ (P *ᵥ x)) = x ⬝ᵥ (P *ᵥ (A *ᵥ x)) := by
    rw [dotProduct_mulVec, vecMul_transpose, Criteria.dotProduct_mulVec_comm_of_symm hP x (A *ᵥ x)]
  rw [h2] at h
  linarith

/-! ## The linear singularly perturbed system -/

/-- `ẋ = A₁₁ x + A₁₂ z`, `ε ż = A₂₁ x + A₂₂ z`. -/
structure LinearSP (n m : ℕ) where
  A11 : Matrix (Fin n) (Fin n) ℝ
  A12 : Matrix (Fin n) (Fin m) ℝ
  A21 : Matrix (Fin m) (Fin n) ℝ
  A22 : Matrix (Fin m) (Fin m) ℝ

variable {n m : ℕ}

namespace LinearSP

variable (sp : LinearSP n m)

/-- `[[A₁₁, A₁₂], [A₂₁/ε, A₂₂/ε]]`. -/
def blockMatrix (ε : ℝ) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  fromBlocks sp.A11 sp.A12 (ε⁻¹ • sp.A21) (ε⁻¹ • sp.A22)

/-- The full state matrix with state order `(x, z)`. -/
def stateMatrix (ε : ℝ) : Matrix (Fin (n + m)) (Fin (n + m)) ℝ :=
  (sp.blockMatrix ε).reindex finSumFinEquiv finSumFinEquiv

/-- Quasi-steady-state gain `L = A₂₂⁻¹ A₂₁` (`z ≈ -L x` on the slow manifold). -/
def gain : Matrix (Fin m) (Fin n) ℝ := sp.A22⁻¹ * sp.A21

/-- Reduced slow matrix `A₀ = A₁₁ - A₁₂ A₂₂⁻¹ A₂₁`. -/
def reducedMatrix : Matrix (Fin n) (Fin n) ℝ := sp.A11 - sp.A12 * sp.A22⁻¹ * sp.A21

/-- The coupling constant `c` of the composite Lyapunov estimate. -/
def couplingConst (P0 : Matrix (Fin n) (Fin n) ℝ) (P2 : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  let S := absSum (P0 * sp.A12) + absSum (P2 * sp.gain * sp.reducedMatrix)
  S * (2 * S + 1) / 2 + absSum (P2 * sp.gain * sp.A12)

/-- Explicit `ε* = 1/(2c + 1)` for given Lyapunov solutions `P₀`, `P₂`. -/
def epsStar (P0 : Matrix (Fin n) (Fin n) ℝ) (P2 : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  1 / (2 * sp.couplingConst P0 P2 + 1)

/-- Coordinate change `(x, z) ↦ (x, η)`, `η = z + L x`. -/
def coordChange : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ := fromBlocks 1 0 sp.gain 1

/-- Composite Lyapunov matrix `Tᵀ diag(P₀, P₂) T`. -/
def compositeP (P0 : Matrix (Fin n) (Fin n) ℝ) (P2 : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  sp.coordChangeᵀ * fromBlocks P0 0 0 P2 * sp.coordChange

@[powerlib_foundation] theorem compositeP_symm {P0 : Matrix (Fin n) (Fin n) ℝ}
    {P2 : Matrix (Fin m) (Fin m) ℝ} (h0 : P0ᵀ = P0) (h2 : P2ᵀ = P2) :
    (sp.compositeP P0 P2)ᵀ = sp.compositeP P0 P2 := by
  simp only [compositeP, transpose_mul, transpose_transpose, fromBlocks_transpose, h0, h2,
    transpose_zero, Matrix.mul_assoc]

@[powerlib_foundation] theorem coordChange_mulVec (x : Fin n → ℝ) (η : Fin m → ℝ) :
    sp.coordChange *ᵥ Sum.elim x (η - sp.gain *ᵥ x) = Sum.elim x η := by
  rw [coordChange, fromBlocks_mulVec]
  simp

@[powerlib_foundation] theorem compositeP_form (P0 : Matrix (Fin n) (Fin n) ℝ)
    (P2 : Matrix (Fin m) (Fin m) ℝ) (u w : Fin n ⊕ Fin m → ℝ) :
    u ⬝ᵥ (sp.compositeP P0 P2 *ᵥ w) =
      (sp.coordChange *ᵥ u) ⬝ᵥ (fromBlocks P0 0 0 P2 *ᵥ (sp.coordChange *ᵥ w)) := by
  rw [compositeP, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

@[powerlib_foundation] theorem blockDiag_form (P0 : Matrix (Fin n) (Fin n) ℝ)
    (P2 : Matrix (Fin m) (Fin m) ℝ) (x x' : Fin n → ℝ) (η η' : Fin m → ℝ) :
    Sum.elim x η ⬝ᵥ (fromBlocks P0 0 0 P2 *ᵥ Sum.elim x' η') = x ⬝ᵥ (P0 *ᵥ x') + η ⬝ᵥ (P2 *ᵥ η') := by
  rw [fromBlocks_mulVec]
  simp [sumElim_dotProduct_sumElim]

/-- In `(x, η)` coordinates the full dynamics read `ẋ = A₀ x + A₁₂ η`,
`η̇ = L (A₀ x + A₁₂ η) + A₂₂ η / ε`. -/
@[powerlib_foundation] theorem coordChange_blockMatrix (hA22 : IsUnit sp.A22.det) (ε : ℝ)
    (x : Fin n → ℝ) (η : Fin m → ℝ) :
    sp.coordChange *ᵥ (sp.blockMatrix ε *ᵥ Sum.elim x (η - sp.gain *ᵥ x)) =
      Sum.elim (sp.reducedMatrix *ᵥ x + sp.A12 *ᵥ η)
        (sp.gain *ᵥ (sp.reducedMatrix *ᵥ x + sp.A12 *ᵥ η) + ε⁻¹ • (sp.A22 *ᵥ η)) := by
  have hslow : sp.A11 *ᵥ x + sp.A12 *ᵥ (η - sp.gain *ᵥ x) =
      sp.reducedMatrix *ᵥ x + sp.A12 *ᵥ η := by
    simp only [reducedMatrix, gain, sub_mulVec, mulVec_sub, ← mulVec_mulVec, Matrix.mul_assoc]
    abel
  have hfast : sp.A21 *ᵥ x + sp.A22 *ᵥ (η - sp.gain *ᵥ x) = sp.A22 *ᵥ η := by
    simp only [gain, mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hA22,
      Matrix.one_mul]
    abel
  rw [blockMatrix, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, smul_mulVec, ← smul_add]
  rw [hslow, hfast, coordChange, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, one_mulVec, zero_mulVec, add_zero]

/-- The composite Lyapunov estimate `V̇ ≤ -|x|²/4 - |η|²/2` for `0 < ε < ε*`. -/
@[powerlib_foundation] theorem dissipation_le (hA22 : IsUnit sp.A22.det)
    {P0 : Matrix (Fin n) (Fin n) ℝ} {P2 : Matrix (Fin m) (Fin m) ℝ}
    (h0 : P0ᵀ = P0) (h2 : P2ᵀ = P2)
    (hL0 : P0 * sp.reducedMatrix + sp.reducedMatrixᵀ * P0 = -1)
    (hL2 : P2 * sp.A22 + sp.A22ᵀ * P2 = -1)
    {ε : ℝ} (hε : 0 < ε) (hεs : ε < sp.epsStar P0 P2) (x : Fin n → ℝ) (η : Fin m → ℝ) :
    Sum.elim x (η - sp.gain *ᵥ x) ⬝ᵥ
        (sp.compositeP P0 P2 *ᵥ (sp.blockMatrix ε *ᵥ Sum.elim x (η - sp.gain *ᵥ x))) ≤
      -(x ⬝ᵥ x) / 4 - (η ⬝ᵥ η) / 2 := by
  rw [compositeP_form, coordChange_mulVec, coordChange_blockMatrix _ hA22, blockDiag_form]
  set A0 := sp.reducedMatrix
  set L := sp.gain
  set S1 := absSum (P0 * sp.A12)
  set S2 := absSum (P2 * L * A0)
  set S3 := absSum (P2 * L * sp.A12)
  set S := S1 + S2 with hS
  set c := sp.couplingConst P0 P2 with hc
  have hcdef : c = S * (2 * S + 1) / 2 + S3 := rfl
  have hS1 := absSum_nonneg (P0 * sp.A12)
  have hS2 := absSum_nonneg (P2 * L * A0)
  have hS3 := absSum_nonneg (P2 * L * sp.A12)
  have hSnn : 0 ≤ S := add_nonneg hS1 hS2
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  set δ := 1 / (2 * S + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hxx := dotProduct_self_nonneg' x
  have hηη := dotProduct_self_nonneg' η
  -- expand
  have e1 : x ⬝ᵥ (P0 *ᵥ (A0 *ᵥ x + sp.A12 *ᵥ η)) =
      -(x ⬝ᵥ x) / 2 + x ⬝ᵥ ((P0 * sp.A12) *ᵥ η) := by
    rw [mulVec_add, dotProduct_add, dotProduct_mulVec_lyapunov h0 hL0, mulVec_mulVec]
  have e2 : η ⬝ᵥ (P2 *ᵥ (L *ᵥ (A0 *ᵥ x + sp.A12 *ᵥ η) + ε⁻¹ • (sp.A22 *ᵥ η))) =
      η ⬝ᵥ ((P2 * L * A0) *ᵥ x) + η ⬝ᵥ ((P2 * L * sp.A12) *ᵥ η) - ε⁻¹ * ((η ⬝ᵥ η) / 2) := by
    have hl := dotProduct_mulVec_lyapunov h2 hL2 η
    simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul,
      ← mulVec_mulVec] at hl ⊢
    rw [hl]
    ring
  rw [e1, e2]
  -- cross terms
  have b1 := abs_dotProduct_mulVec_le (P0 * sp.A12) x η hδpos
  have b2 := abs_dotProduct_mulVec_le (P2 * L * A0) η x (inv_pos.mpr hδpos)
  have b3 := abs_dotProduct_mulVec_le (P2 * L * sp.A12) η η one_pos
  rw [div_inv_eq_mul] at b2
  have c1 := le_of_abs_le b1
  have c2 := le_of_abs_le b2
  have c3 := le_of_abs_le b3
  -- ε⁻¹ is large
  have hεinv : 2 * c + 1 < ε⁻¹ := by
    have hpos : 0 < 2 * c + 1 := by positivity
    have : ε < 1 / (2 * c + 1) := hεs
    rw [lt_div_iff₀ hpos] at this
    rw [lt_inv_comm₀ hpos hε, inv_eq_one_div, lt_div_iff₀ hpos]
    linarith
  -- coefficient bounds
  have hSδ : S * δ ≤ 1 / 2 := by
    rw [hδ, mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have hSinv : S / δ = S * (2 * S + 1) := by
    rw [hδ]; field_simp
  have key1 : S1 * (δ * (x ⬝ᵥ x) + (η ⬝ᵥ η) / δ) / 2 + S2 * (δ⁻¹ * (η ⬝ᵥ η) + (x ⬝ᵥ x) * δ) / 2 =
      (S * δ) * (x ⬝ᵥ x) / 2 + (S / δ) * (η ⬝ᵥ η) / 2 := by
    rw [hS]; field_simp; ring
  have key2 : S3 * (1 * (η ⬝ᵥ η) + (η ⬝ᵥ η) / 1) / 2 = S3 * (η ⬝ᵥ η) := by ring
  rw [hSinv] at key1
  have hx4 : (S * δ) * (x ⬝ᵥ x) / 2 ≤ (x ⬝ᵥ x) / 4 := by nlinarith
  have hη : (S * (2 * S + 1)) * (η ⬝ᵥ η) / 2 + S3 * (η ⬝ᵥ η) - ε⁻¹ * ((η ⬝ᵥ η) / 2) ≤
      -(η ⬝ᵥ η) / 2 := by
    have : (S * (2 * S + 1)) / 2 + S3 = c := hcdef.symm
    nlinarith
  linarith

/-- Kokotović's theorem with explicit `ε*`: for `0 < ε < ε* = 1/(2c+1)` the full matrix is
Hurwitz. -/
@[powerlib_foundation] theorem isHurwitz_of_lt_epsStar (hA22 : IsUnit sp.A22.det)
    {P0 : Matrix (Fin n) (Fin n) ℝ} {P2 : Matrix (Fin m) (Fin m) ℝ}
    (hP0 : P0.PosDef) (hP2 : P2.PosDef)
    (hL0 : P0 * sp.reducedMatrix + sp.reducedMatrixᵀ * P0 = -1)
    (hL2 : P2 * sp.A22 + sp.A22ᵀ * P2 = -1)
    {ε : ℝ} (hε : 0 < ε) (hεs : ε < sp.epsStar P0 P2) :
    LinearSystems.IsHurwitz (sp.stateMatrix ε) := by
  have h0 : P0ᵀ = P0 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP0.isHermitian.eq
  have h2 : P2ᵀ = P2 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP2.isHermitian.eq
  -- every state is `Sum.elim x (η - L x)`
  have hsplit : ∀ w : Fin n ⊕ Fin m → ℝ,
      w = Sum.elim (w ∘ Sum.inl) ((w ∘ Sum.inr + sp.gain *ᵥ (w ∘ Sum.inl)) -
        sp.gain *ᵥ (w ∘ Sum.inl)) := by
    intro w
    rw [add_sub_cancel_right, Sum.elim_comp_inl_inr]
  have hne : ∀ w : Fin n ⊕ Fin m → ℝ, w ≠ 0 →
      w ∘ Sum.inl ≠ 0 ∨ w ∘ Sum.inr + sp.gain *ᵥ (w ∘ Sum.inl) ≠ 0 := by
    intro w hw
    by_contra h
    push Not at h
    apply hw
    funext k
    rcases k with i | i
    · exact congrFun h.1 i
    · have h2 := congrFun h.2 i
      have h1 : w ∘ Sum.inl = 0 := h.1
      simp only [h1, mulVec_zero, add_zero, Pi.zero_apply, Function.comp_apply] at h2
      exact h2
  have hpos : ∀ w : Fin n ⊕ Fin m → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (sp.compositeP P0 P2 *ᵥ w) := by
    intro w hw
    have hT : sp.coordChange *ᵥ w =
        Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr + sp.gain *ᵥ (w ∘ Sum.inl)) := by
      conv_lhs => rw [hsplit w]
      exact sp.coordChange_mulVec _ _
    rw [compositeP_form, hT, blockDiag_form]
    have a1 : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (P0 *ᵥ x) := fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · simpa using (hP0.dotProduct_mulVec_pos hx).le
    have a2 : ∀ x : Fin m → ℝ, 0 ≤ x ⬝ᵥ (P2 *ᵥ x) := fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · simpa using (hP2.dotProduct_mulVec_pos hx).le
    rcases hne w hw with h | h
    · have := hP0.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith [a2 (w ∘ Sum.inr + sp.gain *ᵥ (w ∘ Sum.inl))]
    · have := hP2.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith [a1 (w ∘ Sum.inl)]
  have hdiss : ∀ w : Fin n ⊕ Fin m → ℝ, w ≠ 0 →
      w ⬝ᵥ (sp.compositeP P0 P2 *ᵥ (sp.blockMatrix ε *ᵥ w)) < 0 := by
    intro w hw
    have hd := sp.dissipation_le hA22 h0 h2 hL0 hL2 hε hεs (w ∘ Sum.inl)
      (w ∘ Sum.inr + sp.gain *ᵥ (w ∘ Sum.inl))
    rw [← hsplit w] at hd
    have hxx := dotProduct_self_nonneg' (w ∘ Sum.inl)
    have hηη := dotProduct_self_nonneg' (w ∘ Sum.inr + sp.gain *ᵥ (w ∘ Sum.inl))
    have hstrict : 0 < (w ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inl) ∨
        0 < (w ∘ Sum.inr + sp.gain *ᵥ (w ∘ Sum.inl)) ⬝ᵥ (w ∘ Sum.inr + sp.gain *ᵥ (w ∘ Sum.inl)) := by
      rcases hne w hw with h | h
      · left
        exact lt_of_le_of_ne (dotProduct_self_nonneg' _)
          (fun h0 => h (dotProduct_self_eq_zero.mp h0.symm))
      · right
        exact lt_of_le_of_ne (dotProduct_self_nonneg' _)
          (fun h0 => h (dotProduct_self_eq_zero.mp h0.symm))
    rcases hstrict with h | h <;> linarith
  -- transport to the reindexed matrix
  intro μ v hv heig
  have hv' : v ∘ finSumFinEquiv ≠ 0 := by
    intro h
    apply hv
    funext k
    have := congrFun h (finSumFinEquiv.symm k)
    simpa using this
  have heig' : (sp.blockMatrix ε).map (algebraMap ℝ ℂ) *ᵥ (v ∘ finSumFinEquiv) =
      μ • (v ∘ finSumFinEquiv) := by
    funext k
    have h := congrFun heig (finSumFinEquiv k)
    simp only [stateMatrix, reindex_apply, ← submatrix_map, submatrix_mulVec_equiv,
      Function.comp_apply, Equiv.symm_apply_apply, Pi.smul_apply] at h ⊢
    exact h
  simpa using Criteria.re_neg_of_lyapunov (sp.compositeP_symm h0 h2) hpos hdiss hv' heig'

/-- Kokotović's linear two-time-scale theorem: `A₂₂` and `A₀` Hurwitz ⇒ there is `ε* > 0`
such that the full system is globally exponentially stable for every `ε ∈ (0, ε*)`. -/
@[powerlib_foundation] theorem exists_epsStar_exponentiallyStable
    (hA22 : LinearSystems.IsHurwitz sp.A22) (hA0 : LinearSystems.IsHurwitz sp.reducedMatrix) :
    ∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      LinearSystems.IsHurwitz (sp.stateMatrix ε) ∧
        Flow.GloballyExponentiallyStable
          (LinearSystems.affineLinearVectorField (sp.stateMatrix ε) 0) 0 := by
  obtain ⟨P0, hP0, hL0, -⟩ :=
    LinearSystems.IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov hA0 1
      Matrix.PosDef.one
  obtain ⟨P2, hP2, hL2, -⟩ :=
    LinearSystems.IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov hA22 1
      Matrix.PosDef.one
  have hU := isUnit_det_of_isHurwitz hA22
  refine ⟨sp.epsStar P0 P2, ?_, fun ε hε hεs => ?_⟩
  · have hc : 0 ≤ sp.couplingConst P0 P2 := by
      simp only [couplingConst]
      have := absSum_nonneg (P0 * sp.A12)
      have := absSum_nonneg (P2 * sp.gain * sp.reducedMatrix)
      have := absSum_nonneg (P2 * sp.gain * sp.A12)
      positivity
    simp only [epsStar]
    positivity
  have hH := sp.isHurwitz_of_lt_epsStar hU hP0 hP2 hL0 hL2 hε hεs
  exact ⟨hH, Linear.globallyExponentiallyStable_of_isHurwitz 0 hH⟩

end LinearSP

end powerlib.SingularPerturbation
