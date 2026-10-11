import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SPH

/-! # Itô correction of the synchronous-machine SPHS (foundation)

Source: work-sync `theory/T-sync-machine-stochastic.md` §1.1 (sparse diffusion `Σ_v`, `Σ_T`,
eq. (1.2)), §1.3 (eqs. (1.4)–(1.6): `Δ_Itô^SM = ½[σ_{v,d}² (∇²H)_{Ψd Ψd} + σ_{v,q}² (∇²H)_{Ψq Ψq}
+ σ_T² (∇²H)_{pp}]`, `(L⁻¹)_{qq} = 1/L_q^eff`, `L_q^eff = L_q − L_aq²/L_kqkq`), and
`T-grid-disturbance-stochastic.md` §1.2.b (SM terminal noise is state-independent).

Model boundary.  Seven-state SM pH model `x = (Ψ_d, Ψ_q, Ψ_f, Ψ_kd, Ψ_kq, p, δ)`,
`H = ½ Ψᵀ L⁻¹ Ψ + p²/(2M) + V_el(δ)`, constant diffusion columns `σ_{v,d} e_{Ψd}`,
`σ_{v,q} e_{Ψq}`, `σ_T e_p`.  The Itô correction is the algebraic expression
`½ tr(Σ Σᵀ ∇²H)` (`SPH.itoCorrection`); nothing about SDE solutions or expectations is claimed.
For the magnetic block we use the axis-separated (block-diagonal) inductance
`L = diag(L_d-block (d, f, kd), L_q-block (q, kq))`, written with Mathlib's `fromBlocks`.

Correction (T-sync-machine-stochastic §1.3).  The note first writes
"`(∇²H)_{Ψq Ψq} = (L⁻¹)_{qq} = 1/L_q` because `Ψ_q` is decoupled", and later uses
`L_q^eff = L_q − L_aq²/L_kqkq`.  The first statement is wrong whenever the q damper is coupled:
`(L⁻¹)_{qq} = 1/(L_q − L_aq²/L_kqkq)` (`qBlock_inv_00`), and it equals `1/L_q` iff
`L_aq = 0` (`qBlock_inv_00_eq_inv_Lq_iff`).
-/

noncomputable section
namespace powerlib.Stochastic.SM

open Matrix
open powerlib.Stochastic.SPH

variable {n k : ℕ}

/-- Sparse constant diffusion: column `j` is `σ j` times the basis vector `e_{c j}`. -/
def sparseNoise (c : Fin k → Fin n) (σ : Fin k → ℝ) : Matrix (Fin n) (Fin k) ℝ :=
  fun i j => if i = c j then σ j else 0

/-- For a sparse diffusion with distinct target coordinates, the Itô correction only sees the
diagonal entries of the Hessian: `½ tr(Σ Σᵀ K) = ½ Σ_j σ_j² K_{c_j c_j}` (T-sync-machine (1.5)). -/
@[powerlib_foundation] theorem itoCorrection_sparseNoise {c : Fin k → Fin n}
    (σ : Fin k → ℝ) (K : Matrix (Fin n) (Fin n) ℝ) :
    itoCorrection (sparseNoise c σ) K = (1 / 2 : ℝ) * ∑ j, σ j ^ 2 * K (c j) (c j) := by
  unfold itoCorrection
  congr 1
  have e : sparseNoise c σ * (sparseNoise c σ)ᵀ * K
      = sparseNoise c σ * ((sparseNoise c σ)ᵀ * K) := Matrix.mul_assoc _ _ _
  rw [e, trace_mul_comm, trace]
  simp only [diag, mul_apply, transpose_apply, sparseNoise]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_zero]
  ring

/-- The SM diffusion `(Σ_v | Σ_T)` of eq. (1.2): `σ_{v,d}` on `Ψ_d` (0), `σ_{v,q}` on `Ψ_q` (1),
`σ_T` on `p` (5). -/
def smNoise (σvd σvq σT : ℝ) : Matrix (Fin 7) (Fin 3) ℝ :=
  sparseNoise ![0, 1, 5] ![σvd, σvq, σT]

/-- **SM Itô correction (1.5)**: only the three diagonal Hessian entries enter; in particular
it is independent of the electrical potential `V_el(δ)` and of the state when the Hessian
entries are constant. -/
@[powerlib_foundation] theorem smIto (σvd σvq σT : ℝ) (K : Matrix (Fin 7) (Fin 7) ℝ) :
    itoCorrection (smNoise σvd σvq σT) K
      = (1 / 2 : ℝ) * (σvd ^ 2 * K 0 0 + σvq ^ 2 * K 1 1 + σT ^ 2 * K 5 5) := by
  rw [smNoise, itoCorrection_sparseNoise, Fin.sum_univ_three]
  simp

/-- `Δ_Itô^SM ≥ 0` whenever the Hessian is positive semidefinite (convex `H`). -/
@[powerlib_foundation] theorem smIto_nonneg (σvd σvq σT : ℝ) {K : Matrix (Fin 7) (Fin 7) ℝ}
    (hK : K.PosSemidef) : 0 ≤ itoCorrection (smNoise σvd σvq σT) K :=
  itoCorrection_nonneg _ hK

/-- `Δ_Itô^SM ≥ 0` from the three diagonal entries alone (they are the only ones that enter);
e.g. `(L⁻¹)_{dd} > 0`, `(L⁻¹)_{qq} > 0` for `L ≻ 0` and `1/M > 0`. -/
@[powerlib_foundation] theorem smIto_nonneg_of_diag (σvd σvq σT : ℝ) {K : Matrix (Fin 7) (Fin 7) ℝ}
    (h0 : 0 ≤ K 0 0) (h1 : 0 ≤ K 1 1) (h5 : 0 ≤ K 5 5) :
    0 ≤ itoCorrection (smNoise σvd σvq σT) K := by
  rw [smIto]; positivity

/-! ## q-axis magnetic block and the effective inductance -/

/-- q-axis block `[[L_q, L_aq], [L_aq, L_kqkq]]` (stator q, damper kq). -/
def qBlock (Lq Laq Lkq : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Lq, Laq; Laq, Lkq]

/-- Schur complement: `(L_qblock⁻¹)_{qq} = 1/(L_q − L_aq²/L_kqkq)`. -/
@[powerlib_foundation] theorem qBlock_inv_00 {Lq Laq Lkq : ℝ} (hk : Lkq ≠ 0)
    (hdet : Lq * Lkq - Laq ^ 2 ≠ 0) :
    (qBlock Lq Laq Lkq)⁻¹ 0 0 = 1 / (Lq - Laq ^ 2 / Lkq) := by
  rw [qBlock, inv_def, det_fin_two_of, adjugate_fin_two_of]
  have : Lq * Lkq - Laq * Laq ≠ 0 := by rw [← sq]; exact hdet
  simp only [Matrix.smul_apply, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    smul_eq_mul, Ring.inverse_eq_inv']
  field_simp

/-- Correction: `(L⁻¹)_{qq} = 1/L_q` holds iff the q damper is decoupled (`L_aq = 0`). -/
@[powerlib_foundation] theorem qBlock_inv_00_eq_inv_Lq_iff {Lq Laq Lkq : ℝ}
    (hk : 0 < Lkq) (hdet : 0 < Lq * Lkq - Laq ^ 2) :
    (qBlock Lq Laq Lkq)⁻¹ 0 0 = 1 / Lq ↔ Laq = 0 := by
  rw [qBlock_inv_00 hk.ne' hdet.ne']
  have hpos : 0 < Lq - Laq ^ 2 / Lkq := by
    rw [sub_pos, div_lt_iff₀ hk]; linarith
  constructor
  · intro h
    have : Lq - Laq ^ 2 / Lkq = Lq := by
      have := congrArg (fun x => 1 / x) h
      simpa using this
    have : Laq ^ 2 / Lkq = 0 := by linarith
    have := (div_eq_zero_iff.mp this).resolve_right hk.ne'
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  · intro h; subst h; simp

/-- With a coupled damper the effective inductance is strictly smaller: `L_q^eff < L_q`. -/
@[powerlib_foundation] theorem qBlock_effective_lt {Lq Laq Lkq : ℝ} (hk : 0 < Lkq)
    (hc : Laq ≠ 0) : Lq - Laq ^ 2 / Lkq < Lq := by
  have : 0 < Laq ^ 2 / Lkq := div_pos (by positivity) hk
  linarith

/-- In the axis-separated inductance `L = fromBlocks L_d 0 0 L_q-block`, the `(q, q)` entry
of `L⁻¹` is the `(0,0)` entry of the q-block inverse (the d-axis coupling does not enter). -/
@[powerlib_foundation] theorem fromBlocks_inv_q {m : ℕ} (Ld : Matrix (Fin m) (Fin m) ℝ)
    (Lqb : Matrix (Fin 2) (Fin 2) ℝ) (hd : IsUnit Ld.det) (hq : IsUnit Lqb.det) :
    (fromBlocks Ld 0 0 Lqb)⁻¹ (Sum.inr 0) (Sum.inr 0) = Lqb⁻¹ 0 0 := by
  have hinv : (fromBlocks Ld 0 0 Lqb)⁻¹ = fromBlocks Ld⁻¹ 0 0 Lqb⁻¹ := by
    apply inv_eq_left_inv
    rw [fromBlocks_multiply]
    simp [nonsing_inv_mul _ hd, nonsing_inv_mul _ hq, fromBlocks_one]
  rw [hinv]; rfl

/-- `L ≻ 0` gives positive diagonal entries of `L⁻¹`, hence `Δ_Itô^SM ≥ 0`. -/
@[powerlib_foundation] theorem inv_diag_pos {m : ℕ} {L : Matrix (Fin m) (Fin m) ℝ} (hL : L.PosDef)
    (i : Fin m) : 0 < L⁻¹ i i :=
  hL.inv.diag_pos

end powerlib.Stochastic.SM
