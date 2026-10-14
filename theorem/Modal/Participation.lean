import theorem.Linear.Transfer

/-! # Modal decomposition data and participation factors

Modal data of a diagonalisable matrix and the participation factors: their sums, their role as
residues of the resolvent and transfer channels, invariance under state scaling, the geometric
form, and the PBH meaning of a vanishing residue.

Scope.
* A complex square matrix `A` (for a real state matrix, `Linear.complexify A`). `ModalBasis A`
  records a diagonalisation: the columns `v i` of `V` are right eigenvectors, the columns `ψ i`
  of `W` are left eigenvectors, and the biorthonormality `Wᵀ V = I` (`ψ_iᵀ v_j = δ_ij`) holds.
  The existence of such data is exactly diagonalisability of `A`; it is a hypothesis of every
  statement here (defective matrices are excluded).
* Matrix-level statements with no model family. The real LTI system of the transfer expansion is
  given by its matrices `A B C D` (state index `n`, `p` inputs and outputs) and
  `Linear.transferOf`.

Source: work-sync theory/T-participation-factor.md §1.1–§1.6, §1.10, §2.4–§2.5;
theory/T-small-signal-stability.md §1.5, §1.7, §1.9; conventions.md §2.

Results.
* `pf`, `sum_pf_modes`, `sum_pf_states` — `pf k i = v_{ki} ψ_{ki}` (Pérez-Arriaga). Row and
  column sums are `1` (§1.2).
* `resolvent_eq`, `pf_eq_residue`, `io_expansion`, `transfer_expansion` — resolvent partial
  fractions: `(sI − A)⁻¹ = Σ_i (s − λ_i)⁻¹ v_i ψ_iᵀ`; the `(k,k)` entry is
  `Σ_i p_{ki} / (s − λ_i)`, i.e. `p_{ki}` is the residue of the `(k,k)` channel (§1.1).
  Input/output residues `R^{(i)}_{ℓj} = (C v_i)_ℓ (ψ_iᵀ B)_j` and the expansion of a real LTI
  transfer matrix `G(s) = Σ_i R^{(i)} / (s − λ_i) + D` (§1.5, small-signal §1.9).
* `scale_pf`, `weightedPF_eq`, `sum_groupPF` — diagonal state scaling `x̃ = T x` gives a modal
  basis of `T A T⁻¹` with the same participation factors (§1.6). The "weighted PF" of §1.4 with
  diagonal weights is identically the original PF (as the note itself observes); grouped PFs sum
  to `1` over a partition of the states.
* `norm_pf_eq`, `geomPF_nonneg`, `geomPF_le_one` — geometric PF (§1.10):
  `|p_{ki}| = ‖v_i‖ ‖ψ_i‖ g_{ki}` with `0 ≤ g_{ki} ≤ 1`.
* `residue_eq_zero_iff` — for a simple eigenvalue, the SISO residue `(c v_i)(ψ_iᵀ b)` vanishes
  iff the mode is uncontrollable from `b` or unobservable from `c` in the PBH (Hautus)
  eigenvector sense (§2.5).
-/

noncomputable section
namespace powerlib.Modal
open Matrix
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Biorthonormal right/left eigenvector data of a diagonalisable complex matrix. -/
structure ModalBasis (A : Matrix n n ℂ) where
  /-- Right eigenvectors as columns. -/
  V : Matrix n n ℂ
  /-- Left eigenvectors as columns. -/
  W : Matrix n n ℂ
  /-- Eigenvalues. -/
  eig : n → ℂ
  right : A * V = V * diagonal eig
  biorth : Wᵀ * V = 1

namespace ModalBasis

variable {A : Matrix n n ℂ} (mb : ModalBasis A)

/-- Right eigenvector `v_i` (column `i` of `V`). -/
def v (i : n) : n → ℂ := fun k => mb.V k i

/-- Left eigenvector `ψ_i` (column `i` of `W`). -/
def ψ (i : n) : n → ℂ := fun k => mb.W k i

/-- Participation factor `p_{ki} = v_{ki} ψ_{ki}` of state `k` in mode `i`. -/
def pf (k i : n) : ℂ := mb.V k i * mb.W k i

@[powerlib_foundation] theorem V_mul_Wt : mb.V * mb.Wᵀ = 1 := mul_eq_one_comm.mp mb.biorth

@[powerlib_foundation] theorem decomp : A = mb.V * diagonal mb.eig * mb.Wᵀ := by
  calc A = A * (mb.V * mb.Wᵀ) := by rw [mb.V_mul_Wt, Matrix.mul_one]
    _ = mb.V * diagonal mb.eig * mb.Wᵀ := by rw [← Matrix.mul_assoc, mb.right]

@[powerlib_foundation] theorem left : mb.Wᵀ * A = diagonal mb.eig * mb.Wᵀ := by
  calc mb.Wᵀ * A = mb.Wᵀ * (mb.V * diagonal mb.eig * mb.Wᵀ) := congrArg (mb.Wᵀ * ·) mb.decomp
    _ = diagonal mb.eig * mb.Wᵀ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mb.biorth, Matrix.one_mul]

@[powerlib_foundation] theorem mulVec_v (i : n) : A *ᵥ mb.v i = mb.eig i • mb.v i := by
  ext k
  have h := congrFun (congrFun mb.right k) i
  rw [Matrix.mul_diagonal] at h
  simp only [Matrix.mul_apply] at h
  simpa [v, Matrix.mulVec, dotProduct, mul_comm] using h

@[powerlib_foundation] theorem vecMul_ψ (i : n) : vecMul (mb.ψ i) A = mb.eig i • mb.ψ i := by
  ext k
  have h := congrFun (congrFun mb.left i) k
  rw [Matrix.diagonal_mul] at h
  simp only [Matrix.mul_apply, transpose_apply] at h
  simpa [ψ, Matrix.vecMul, dotProduct] using h

@[powerlib_foundation] theorem ψ_dot_v (i j : n) :
    mb.ψ i ⬝ᵥ mb.v j = if i = j then 1 else 0 := by
  have h := congrFun (congrFun mb.biorth i) j
  simpa [Matrix.mul_apply, Matrix.one_apply, ψ, v, dotProduct] using h

@[powerlib_foundation] theorem v_ne_zero (i : n) : mb.v i ≠ 0 := by
  intro h
  have := mb.ψ_dot_v i i
  simp [h] at this

@[powerlib_foundation] theorem ψ_ne_zero (i : n) : mb.ψ i ≠ 0 := by
  intro h
  have := mb.ψ_dot_v i i
  simp [h] at this

/-! ## Normalisation (§1.2) -/

/-- Each state is shared by all modes: `Σ_i p_{ki} = 1`. -/
@[powerlib_foundation] theorem sum_pf_modes (k : n) : ∑ i, mb.pf k i = 1 := by
  have h := congrFun (congrFun mb.V_mul_Wt k) k
  simpa [Matrix.mul_apply, pf] using h

/-- Each mode is shared by all states: `Σ_k p_{ki} = 1`. -/
@[powerlib_foundation] theorem sum_pf_states (i : n) : ∑ k, mb.pf k i = 1 := by
  have h := congrFun (congrFun mb.biorth i) i
  simpa [Matrix.mul_apply, pf, mul_comm] using h

/-! ## Resolvent partial fractions and residues (§1.1, §1.5) -/

@[powerlib_foundation] theorem sub_eq_conj (s : ℂ) :
    s • (1 : Matrix n n ℂ) - A = mb.V * diagonal (fun i => s - mb.eig i) * mb.Wᵀ := by
  conv_lhs => rw [mb.decomp, ← mb.V_mul_Wt]
  rw [show diagonal (fun i => s - mb.eig i) = s • (1 : Matrix n n ℂ) - diagonal mb.eig from by
      ext i j; by_cases h : i = j <;> simp [h],
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- `(sI − A)⁻¹ = V diag((s − λ_i)⁻¹) Wᵀ` away from the spectrum. -/
@[powerlib_foundation] theorem resolvent_eq {s : ℂ} (hs : ∀ i, s ≠ mb.eig i) :
    (s • (1 : Matrix n n ℂ) - A)⁻¹ = mb.V * diagonal (fun i => (s - mb.eig i)⁻¹) * mb.Wᵀ := by
  apply Matrix.inv_eq_right_inv
  rw [mb.sub_eq_conj]
  calc mb.V * diagonal (fun i => s - mb.eig i) * mb.Wᵀ *
        (mb.V * diagonal (fun i => (s - mb.eig i)⁻¹) * mb.Wᵀ)
      = mb.V * (diagonal (fun i => s - mb.eig i) * (mb.Wᵀ * mb.V) *
          diagonal (fun i => (s - mb.eig i)⁻¹)) * mb.Wᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [mb.biorth, Matrix.mul_one, diagonal_mul_diagonal]
        rw [show (fun i => (s - mb.eig i) * (s - mb.eig i)⁻¹) = fun _ => (1 : ℂ) from
          funext fun i => mul_inv_cancel₀ (sub_ne_zero.mpr (hs i)), diagonal_one, Matrix.mul_one,
          mb.V_mul_Wt]

@[powerlib_foundation] theorem resolvent_apply {s : ℂ} (hs : ∀ i, s ≠ mb.eig i) (k l : n) :
    (s • (1 : Matrix n n ℂ) - A)⁻¹ k l = ∑ i, mb.V k i * mb.W l i / (s - mb.eig i) := by
  rw [mb.resolvent_eq hs, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, transpose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The `(k,k)` resolvent channel: `[(sI − A)⁻¹]_{kk} = Σ_i p_{ki} / (s − λ_i)`. -/
@[powerlib_foundation] theorem resolvent_diag {s : ℂ} (hs : ∀ i, s ≠ mb.eig i) (k : n) :
    (s • (1 : Matrix n n ℂ) - A)⁻¹ k k = ∑ i, mb.pf k i / (s - mb.eig i) := by
  rw [mb.resolvent_apply hs]; rfl

/-- Modal residue matrix `R^{(i)}_{ℓj} = (C v_i)_ℓ (ψ_iᵀ B)_j`. -/
def residue {κ κ' : Type*} (C : Matrix κ n ℂ) (B : Matrix n κ' ℂ) (i : n) : Matrix κ κ' ℂ :=
  fun l j => (C *ᵥ mb.v i) l * vecMul (mb.ψ i) B j

/-- The participation factor is the residue of the state-to-state channel `B = C = I`. -/
@[powerlib_foundation] theorem pf_eq_residue (k i : n) :
    mb.pf k i = mb.residue (1 : Matrix n n ℂ) 1 i k k := by
  simp [residue, pf, v, ψ]

/-- Partial-fraction expansion `C (sI − A)⁻¹ B = Σ_i R^{(i)} / (s − λ_i)`. -/
@[powerlib_foundation] theorem io_expansion {κ κ' : Type*} (C : Matrix κ n ℂ) (B : Matrix n κ' ℂ)
    {s : ℂ} (hs : ∀ i, s ≠ mb.eig i) :
    C * (s • (1 : Matrix n n ℂ) - A)⁻¹ * B = ∑ i, (s - mb.eig i)⁻¹ • mb.residue C B i := by
  rw [mb.resolvent_eq hs]
  have hassoc : C * (mb.V * diagonal (fun i => (s - mb.eig i)⁻¹) * mb.Wᵀ) * B =
      (C * mb.V) * diagonal (fun i => (s - mb.eig i)⁻¹) * (mb.Wᵀ * B) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc]
  ext l j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (C * mb.V) l i = (C *ᵥ mb.v i) l from rfl,
    show (mb.Wᵀ * B) i j = vecMul (mb.ψ i) B j from rfl]
  simp only [residue]
  ring

/-- Modal expansion of the transfer matrix of a real LTI model whose complexified state
matrix is diagonalisable: `G(s) = Σ_i R^{(i)} / (s − λ_i) + D`. -/
@[powerlib_foundation] theorem transfer_expansion {p : ℕ} (A : Matrix n n ℝ)
    (B : Matrix n (Fin p) ℝ) (C : Matrix (Fin p) n ℝ) (D : Matrix (Fin p) (Fin p) ℝ)
    (mb : ModalBasis (Linear.complexify A)) {s : ℂ} (hs : ∀ i, s ≠ mb.eig i) :
    Linear.transferOf A B C D s =
      ∑ i, (s - mb.eig i)⁻¹ • mb.residue (Linear.complexify C) (Linear.complexify B) i +
        Linear.complexify D := by
  rw [Linear.transferOf, ← mb.io_expansion _ _ hs]
  rfl

/-! ## Scaling invariance, weighted and grouped PF (§1.4, §1.6) -/

/-- Modal basis of the diagonally scaled matrix `T A T⁻¹`, `T = diag t`. -/
def scale (t : n → ℂ) (ht : ∀ i, t i ≠ 0) : ModalBasis (diagonal t * A * diagonal t⁻¹) where
  V := diagonal t * mb.V
  W := diagonal t⁻¹ * mb.W
  eig := mb.eig
  right := by
    have hinv : diagonal t⁻¹ * diagonal t = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; simp [ht i]
    calc diagonal t * A * diagonal t⁻¹ * (diagonal t * mb.V)
        = diagonal t * A * (diagonal t⁻¹ * diagonal t) * mb.V := by simp only [Matrix.mul_assoc]
      _ = diagonal t * (A * mb.V) := by rw [hinv, Matrix.mul_one, Matrix.mul_assoc]
      _ = diagonal t * mb.V * diagonal mb.eig := by rw [mb.right, Matrix.mul_assoc]
  biorth := by
    have hinv : diagonal t⁻¹ * diagonal t = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; simp [ht i]
    rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal t⁻¹),
      hinv, Matrix.one_mul, mb.biorth]

/-- Participation factors are invariant under diagonal state scaling (§1.6). -/
@[powerlib_foundation] theorem scale_pf (t : n → ℂ) (ht : ∀ i, t i ≠ 0) (k i : n) :
    (mb.scale t ht).pf k i = mb.pf k i := by
  simp only [pf, scale, diagonal_mul, Pi.inv_apply]
  field_simp [ht k]

/-- Weighted PF `w_k v_{ki} (W⁻¹ ψ_i)_k` with a diagonal weight. -/
def weightedPF (w : n → ℂ) (k i : n) : ℂ := w k * mb.V k i * (diagonal w⁻¹ *ᵥ mb.ψ i) k

/-- With diagonal nonzero weights the weighted PF equals the original PF (§1.4). -/
@[powerlib_foundation] theorem weightedPF_eq (w : n → ℂ) (hw : ∀ k, w k ≠ 0) (k i : n) :
    mb.weightedPF w k i = mb.pf k i := by
  simp only [weightedPF, mulVec_diagonal, Pi.inv_apply, pf, ψ]
  field_simp [hw k]

/-- Group participation over a partition `g : n → G` of the states sums to `1`. -/
@[powerlib_foundation] theorem sum_groupPF {G : Type*} [Fintype G] [DecidableEq G] (g : n → G)
    (i : n) : ∑ γ, ∑ k ∈ Finset.univ.filter (fun k => g k = γ), mb.pf k i = 1 := by
  rw [Finset.sum_fiberwise Finset.univ g (fun k => mb.pf k i)]
  exact mb.sum_pf_states i

/-! ## Geometric participation factor (§1.10) -/

/-- Euclidean norm of a complex vector. -/
def enorm2 (x : n → ℂ) : ℝ := ‖(WithLp.equiv 2 (n → ℂ)).symm x‖

/-- Geometric participation factor `|v_{ki}| |ψ_{ki}| / (‖v_i‖₂ ‖ψ_i‖₂)`. -/
def geomPF (k i : n) : ℝ := ‖mb.V k i‖ * ‖mb.W k i‖ / (enorm2 (mb.v i) * enorm2 (mb.ψ i))

omit [DecidableEq n] in
@[powerlib_foundation] theorem enorm2_pos {x : n → ℂ} (hx : x ≠ 0) : 0 < enorm2 x := by
  unfold enorm2
  rw [norm_pos_iff]
  intro h
  exact hx (by simpa using congrArg (WithLp.equiv 2 (n → ℂ)) h)

omit [DecidableEq n] in
@[powerlib_foundation] theorem norm_apply_le_enorm2 (x : n → ℂ) (k : n) : ‖x k‖ ≤ enorm2 x :=
  PiLp.norm_apply_le ((WithLp.equiv 2 (n → ℂ)).symm x) k

/-- `|p_{ki}| = ‖v_i‖₂ ‖ψ_i‖₂ g_{ki}`. -/
@[powerlib_foundation] theorem norm_pf_eq (k i : n) :
    ‖mb.pf k i‖ = enorm2 (mb.v i) * enorm2 (mb.ψ i) * mb.geomPF k i := by
  have h1 := enorm2_pos (mb.v_ne_zero i)
  have h2 := enorm2_pos (mb.ψ_ne_zero i)
  rw [geomPF, pf, norm_mul]
  field_simp

@[powerlib_foundation] theorem geomPF_nonneg (k i : n) : 0 ≤ mb.geomPF k i := by
  unfold geomPF
  have h1 := enorm2_pos (mb.v_ne_zero i)
  have h2 := enorm2_pos (mb.ψ_ne_zero i)
  positivity

@[powerlib_foundation] theorem geomPF_le_one (k i : n) : mb.geomPF k i ≤ 1 := by
  unfold geomPF
  have h1 := enorm2_pos (mb.v_ne_zero i)
  have h2 := enorm2_pos (mb.ψ_ne_zero i)
  rw [div_le_one (by positivity)]
  exact mul_le_mul (norm_apply_le_enorm2 (mb.v i) k) (norm_apply_le_enorm2 (mb.ψ i) k)
    (norm_nonneg _) h1.le

/-! ## Residue zero ⇔ uncontrollable or unobservable mode (§2.5) -/

/-- For a simple eigenvalue, every left eigenvector is a multiple of `ψ_i`. -/
@[powerlib_foundation] theorem left_eigvec_eq {i : n} (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i)
    {w : n → ℂ} (hw : vecMul w A = mb.eig i • w) : w = (w ⬝ᵥ mb.v i) • mb.ψ i := by
  have hzero : ∀ j, j ≠ i → w ⬝ᵥ mb.v j = 0 := by
    intro j hj
    have h1 : w ⬝ᵥ (A *ᵥ mb.v j) = mb.eig j * (w ⬝ᵥ mb.v j) := by
      rw [mb.mulVec_v, dotProduct_smul, smul_eq_mul]
    have h2 : w ⬝ᵥ (A *ᵥ mb.v j) = mb.eig i * (w ⬝ᵥ mb.v j) := by
      rw [Matrix.dotProduct_mulVec, hw, smul_dotProduct, smul_eq_mul]
    have h3 : (mb.eig j - mb.eig i) * (w ⬝ᵥ mb.v j) = 0 := by linear_combination h2 - h1
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (hsimple j hj))
  have hw' : w = vecMul (vecMul w mb.V) mb.Wᵀ := by
    rw [vecMul_vecMul, mb.V_mul_Wt, vecMul_one]
  ext k
  conv_lhs => rw [hw']
  change ∑ j, vecMul w mb.V j * mb.Wᵀ j k = _
  rw [Finset.sum_eq_single i (fun j _ hj => by
    rw [show vecMul w mb.V j = w ⬝ᵥ mb.v j from rfl, hzero j hj, zero_mul]) (by simp)]
  rfl

/-- For a simple eigenvalue, every right eigenvector is a multiple of `v_i`. -/
@[powerlib_foundation] theorem right_eigvec_eq {i : n} (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i)
    {x : n → ℂ} (hx : A *ᵥ x = mb.eig i • x) : x = (mb.ψ i ⬝ᵥ x) • mb.v i := by
  have hzero : ∀ j, j ≠ i → mb.ψ j ⬝ᵥ x = 0 := by
    intro j hj
    have h1 : mb.ψ j ⬝ᵥ (A *ᵥ x) = mb.eig i * (mb.ψ j ⬝ᵥ x) := by
      rw [hx, dotProduct_smul, smul_eq_mul]
    have h2 : mb.ψ j ⬝ᵥ (A *ᵥ x) = mb.eig j * (mb.ψ j ⬝ᵥ x) := by
      rw [Matrix.dotProduct_mulVec, mb.vecMul_ψ, smul_dotProduct, smul_eq_mul]
    have h3 : (mb.eig j - mb.eig i) * (mb.ψ j ⬝ᵥ x) = 0 := by linear_combination h1 - h2
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (hsimple j hj))
  have hx' : x = mb.V *ᵥ (mb.Wᵀ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, mb.V_mul_Wt, Matrix.one_mulVec]
  ext k
  conv_lhs => rw [hx']
  change ∑ j, mb.V k j * (mb.Wᵀ *ᵥ x) j = _
  rw [Finset.sum_eq_single i (fun j _ hj => by
    rw [show (mb.Wᵀ *ᵥ x) j = mb.ψ j ⬝ᵥ x from rfl, hzero j hj, mul_zero]) (by simp)]
  change mb.V k i * (mb.ψ i ⬝ᵥ x) = (mb.ψ i ⬝ᵥ x) * mb.V k i
  ring

/-- PBH form of a vanishing modal residue: for a simple eigenvalue `λ_i`, the SISO residue
`(c v_i)(ψ_iᵀ b)` is zero iff some left eigenvector of `λ_i` is orthogonal to `b`
(uncontrollable mode) or some right eigenvector of `λ_i` is annihilated by `c`
(unobservable mode). -/
@[powerlib_foundation] theorem residue_eq_zero_iff {i : n}
    (hsimple : ∀ j, j ≠ i → mb.eig j ≠ mb.eig i) (b c : n → ℂ) :
    (c ⬝ᵥ mb.v i) * (mb.ψ i ⬝ᵥ b) = 0 ↔
      (∃ w : n → ℂ, w ≠ 0 ∧ vecMul w A = mb.eig i • w ∧ w ⬝ᵥ b = 0) ∨
        (∃ x : n → ℂ, x ≠ 0 ∧ A *ᵥ x = mb.eig i • x ∧ c ⬝ᵥ x = 0) := by
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h0 | h0
    · exact Or.inr ⟨mb.v i, mb.v_ne_zero i, mb.mulVec_v i, h0⟩
    · exact Or.inl ⟨mb.ψ i, mb.ψ_ne_zero i, mb.vecMul_ψ i, h0⟩
  · rintro (⟨w, hw0, hw, hwb⟩ | ⟨x, hx0, hx, hcx⟩)
    · have he := mb.left_eigvec_eq hsimple hw
      have hc : w ⬝ᵥ mb.v i ≠ 0 := by
        intro h0; rw [h0, zero_smul] at he; exact hw0 he
      rw [he, smul_dotProduct, smul_eq_mul] at hwb
      rw [(mul_eq_zero.1 hwb).resolve_left hc, mul_zero]
    · have he := mb.right_eigvec_eq hsimple hx
      have hc : mb.ψ i ⬝ᵥ x ≠ 0 := by
        intro h0; rw [h0, zero_smul] at he; exact hx0 he
      rw [he, dotProduct_smul, smul_eq_mul] at hcx
      rw [(mul_eq_zero.1 hcx).resolve_left hc, zero_mul]

end ModalBasis

end powerlib.Modal
