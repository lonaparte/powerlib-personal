import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Matrix.Order
import theorem.Stochastic.LyapunovCovariance

/-! # Algebra of the Itô generator for stochastic port-Hamiltonian systems (foundation)

Source: work-sync `theory/T-sph.md` §1.2 (generator `𝓛φ = fᵀ∇φ + ½ tr(h hᵀ ∇²φ)`),
§1.3 (energy balance `𝓛H = uᵀy − ∇Hᵀ R ∇H + ½ tr(h hᵀ ∇²H)`, eq. (1.5)–(1.6)),
§1.4 (pointwise weak-passivity criterion (1.9)), §1.5 (Itô/Stratonovich), §1.13
(Cholesky merge `Σ_tot = h_N h_Nᵀ + B_S σ_S σ_Sᵀ B_Sᵀ`), §2.7(a) (linear RLC, noise resonance).

Scope (Rules §3).  The generator is treated as the **second-order differential expression**
`genL f h g K = f ⬝ g + ½ tr(h hᵀ K)` evaluated at one state, with `g = ∇φ(x)`, `K = ∇²φ(x)`.
All results are algebraic identities / inequalities about this expression and about matrices.
That `genL` is the generator of the solution of an Itô SDE (Itô's formula), and any expectation
statement such as (1.7)/(1.8), are **not** formalized here.

Contents.
* `genL_pH`: with `f = (J − R) g + G u` and `J` skew, `genL = u ⬝ y − g ⬝ R g + Δ`,
  `y = Gᵀ g`, `Δ = ½ tr(h hᵀ K)`.
* `itoCorrection_nonneg`: `K ⪰ 0 ⇒ Δ ≥ 0`; `genL_le_supply_iff`: the pointwise criterion
  `𝓛H ≤ uᵀy ⇔ Δ ≤ ∇Hᵀ R ∇H`.
* `exists_factor_of_posSemidef`: every `Σ ⪰ 0` is `σ̃ σ̃ᵀ` (continuous functional calculus
  square root, i.e. the spectral construction); `mergedCov_eq`: the explicit block factor
  `[h_N | B_S σ_S]` of `Σ_tot`; `mergedCov_posSemidef`.
* `rlc_fdt`: linear pH `A = (J − R) Q`, `h hᵀ = 2 T R`, `Q ≻ 0` ⇒ `P = T Q⁻¹` solves
  `A P + P Aᵀ + h hᵀ = 0`, and `½ tr(Q P) = (n/2) T` (`= T` for the two-state RLC).

Correction (T-sph §1.5).  The note says "the diffusion `h` is the same in (1.1) and (1.11)
⇔ `∂ₓh · h = 0`".  In the Itô ↔ Stratonovich conversion the **diffusion coefficient is always
the same** `h`; only the **drift** changes, by `c_k = ½ Σ_{j,ℓ} h_{ℓj} ∂_ℓ h_{kj}`.  Hence the
correct statement is "the two drifts coincide ⇔ `c = 0`" (`itoDrift_eq_iff`); `∂ₓh·h = 0`
is the condition for equal *drifts*, not for equal diffusions.
-/

noncomputable section
namespace powerlib.Stochastic.SPH

open Matrix
open scoped MatrixOrder

variable {n q : ℕ}

/-- Itô second-order correction `½ tr(h hᵀ K)` (noise index type `ι`). -/
def itoCorrection {ι : Type*} [Fintype ι] (h : Matrix (Fin n) ι ℝ)
    (K : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 2 : ℝ) * (h * hᵀ * K).trace

/-- Generator expression `fᵀ g + ½ tr(h hᵀ K)` at one state (`g = ∇φ`, `K = ∇²φ`). -/
def genL (f : Fin n → ℝ) (h : Matrix (Fin n) (Fin q) ℝ) (g : Fin n → ℝ)
    (K : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  f ⬝ᵥ g + itoCorrection h K

/-- A skew matrix contributes no power: `(J g) ⬝ g = 0`. -/
@[powerlib_foundation] theorem skew_dotProduct_self {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : Jᵀ = -J) (g : Fin n → ℝ) : (J *ᵥ g) ⬝ᵥ g = 0 := by
  have h1 : g ⬝ᵥ (Jᵀ *ᵥ g) = g ⬝ᵥ (J *ᵥ g) := by
    rw [mulVec_transpose, dotProduct_comm g (g ᵥ* J), ← dotProduct_mulVec]
  rw [hJ, neg_mulVec, dotProduct_neg] at h1
  have h2 := dotProduct_comm (J *ᵥ g) g
  linarith

/-- **Stochastic energy balance (T-sph (1.5))**, as an algebraic identity of the generator
expression: with `f = (J − R) ∇H + G u`, `J` skew and `y = Gᵀ ∇H`,
`𝓛H = uᵀ y − ∇Hᵀ R ∇H + ½ tr(h hᵀ ∇²H)`. -/
@[powerlib_foundation] theorem genL_pH {m : ℕ} {J R : Matrix (Fin n) (Fin n) ℝ}
    (hJ : Jᵀ = -J) (G : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ)
    (h : Matrix (Fin n) (Fin q) ℝ) (g : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ) :
    genL ((J - R) *ᵥ g + G *ᵥ u) h g K
      = u ⬝ᵥ (Gᵀ *ᵥ g) - g ⬝ᵥ (R *ᵥ g) + itoCorrection h K := by
  unfold genL
  have hGu : (G *ᵥ u) ⬝ᵥ g = u ⬝ᵥ (Gᵀ *ᵥ g) := by
    rw [mulVec_transpose, dotProduct_comm (G *ᵥ u) g, dotProduct_mulVec, dotProduct_comm]
  have hRg : (R *ᵥ g) ⬝ᵥ g = g ⬝ᵥ (R *ᵥ g) := dotProduct_comm _ _
  rw [sub_mulVec, add_dotProduct, sub_dotProduct, skew_dotProduct_self hJ, hGu, hRg]
  ring

/-- `∇²H ⪰ 0 ⇒ Δ_Itô ≥ 0` (T-sph (1.6)). -/
@[powerlib_foundation] theorem itoCorrection_nonneg {ι : Type*} [Fintype ι] (h : Matrix (Fin n) ι ℝ)
    {K : Matrix (Fin n) (Fin n) ℝ} (hK : K.PosSemidef) : 0 ≤ itoCorrection h K := by
  unfold itoCorrection
  have e : (h * hᵀ * K).trace = (hᵀ * K * h).trace := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  have hpsd : (hᵀ * K * h).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hK.conjTranspose_mul_mul_same h
  rw [e]
  exact mul_nonneg (by norm_num) hpsd.trace_nonneg

/-- Pointwise weak-passivity criterion (T-sph (1.9)): `𝓛H ≤ uᵀ y ⇔ Δ_Itô ≤ ∇Hᵀ R ∇H`. -/
@[powerlib_foundation] theorem genL_le_supply_iff {m : ℕ} {J R : Matrix (Fin n) (Fin n) ℝ}
    (hJ : Jᵀ = -J) (G : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ)
    (h : Matrix (Fin n) (Fin q) ℝ) (g : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ) :
    genL ((J - R) *ᵥ g + G *ᵥ u) h g K ≤ u ⬝ᵥ (Gᵀ *ᵥ g) ↔
      itoCorrection h K ≤ g ⬝ᵥ (R *ᵥ g) := by
  rw [genL_pH hJ]
  constructor <;> intro H <;> linarith

/-- Deterministic limit `h = 0`: no correction. -/
@[powerlib_foundation] theorem itoCorrection_zero (K : Matrix (Fin n) (Fin n) ℝ) :
    itoCorrection (0 : Matrix (Fin n) (Fin q) ℝ) K = 0 := by
  unfold itoCorrection; simp

/-! ## Merged diffusion `Σ_tot` (T-sph §1.13) -/

/-- Every positive-semidefinite real matrix has a factor `Σ = σ̃ σ̃ᵀ` (the CFC square root). -/
@[powerlib_foundation] theorem exists_factor_of_posSemidef {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) : ∃ σ : Matrix (Fin n) (Fin n) ℝ, σ * σᵀ = S := by
  obtain ⟨X, hX, -, hXX⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    hS.isHermitian (QuasispectrumRestricts.nnreal_of_nonneg hS.nonneg)
  refine ⟨X, ?_⟩
  have hXt : Xᵀ = X := by
    have := hX.star_eq
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [hXt, hXX]

/-- Merged covariance of a state-dependent N port and a forced-Wiener S port. -/
def mergedCov {qN qS : ℕ} (hN : Matrix (Fin n) (Fin qN) ℝ) (BS : Matrix (Fin n) (Fin qS) ℝ)
    (σS : Matrix (Fin qS) (Fin qS) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  hN * hNᵀ + BS * σS * σSᵀ * BSᵀ

/-- The explicit factor `σ̃ = [h_N | B_S σ_S]` of `Σ_tot`. -/
@[powerlib_foundation] theorem mergedCov_eq {qN qS : ℕ} (hN : Matrix (Fin n) (Fin qN) ℝ)
    (BS : Matrix (Fin n) (Fin qS) ℝ) (σS : Matrix (Fin qS) (Fin qS) ℝ) :
    fromCols hN (BS * σS) * (fromCols hN (BS * σS))ᵀ = mergedCov hN BS σS := by
  rw [transpose_fromCols, fromCols_mul_fromRows, mergedCov, transpose_mul]
  simp only [Matrix.mul_assoc]

@[powerlib_foundation] theorem mergedCov_posSemidef {qN qS : ℕ} (hN : Matrix (Fin n) (Fin qN) ℝ)
    (BS : Matrix (Fin n) (Fin qS) ℝ) (σS : Matrix (Fin qS) (Fin qS) ℝ) :
    (mergedCov hN BS σS).PosSemidef := by
  rw [← mergedCov_eq]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (fromCols hN (BS * σS))

/-- The Itô correction of the merged channel is the sum of the two channel corrections
(this is why the merged form cannot separate them, T-sph §1.13). -/
@[powerlib_foundation] theorem itoCorrection_merged {qN qS : ℕ} (hN : Matrix (Fin n) (Fin qN) ℝ)
    (BS : Matrix (Fin n) (Fin qS) ℝ) (σS : Matrix (Fin qS) (Fin qS) ℝ)
    (K : Matrix (Fin n) (Fin n) ℝ) :
    itoCorrection (fromCols hN (BS * σS)) K = itoCorrection hN K + itoCorrection (BS * σS) K := by
  unfold itoCorrection
  rw [transpose_fromCols, fromCols_mul_fromRows, add_mul, trace_add]
  ring

/-! ## Linear RLC: fluctuation–dissipation (T-sph §2.7(a)) -/

/-- Linear pH `ẋ = (J − R) Q x` with noise `h hᵀ = 2 T R`: the Gibbs covariance `P = T Q⁻¹`
solves the stationary covariance equation. -/
@[powerlib_foundation] theorem rlc_fdt {J R Q : Matrix (Fin n) (Fin n) ℝ} {T : ℝ}
    (hJ : Jᵀ = -J) (hR : Rᵀ = R) (hQ : Q.PosDef) :
    Lyapunov.SolvesCovLyapunov ((J - R) * Q) (T • Q⁻¹) ((2 * T) • R) := by
  have hQt : Qᵀ = Q := by
    have := hQ.isHermitian; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hdet : IsUnit Q.det := (isUnit_iff_ne_zero).mpr hQ.det_pos.ne'
  have hQQ : Q * Q⁻¹ = 1 := mul_nonsing_inv Q hdet
  have hQQ' : Q⁻¹ * Q = 1 := nonsing_inv_mul Q hdet
  unfold Lyapunov.SolvesCovLyapunov
  rw [transpose_mul, hQt, transpose_sub, hJ, hR]
  calc (J - R) * Q * (T • Q⁻¹) + T • Q⁻¹ * (Q * (-J - R)) + (2 * T) • R
      = T • ((J - R) * (Q * Q⁻¹)) + T • ((Q⁻¹ * Q) * (-J - R)) + (2 * T) • R := by
        simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = 0 := by
        rw [hQQ, hQQ', mul_one, one_mul, mul_smul]
        simp only [smul_sub, smul_neg, two_smul]
        abel

/-- Equipartition: `½ tr(Q · T Q⁻¹) = (n/2) T`; for the two-state RLC this is `T`. -/
@[powerlib_foundation] theorem rlc_equipartition {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef)
    (T : ℝ) : (1 / 2 : ℝ) * (Q * (T • Q⁻¹)).trace = (n / 2 : ℝ) * T := by
  have hdet : IsUnit Q.det := (isUnit_iff_ne_zero).mpr hQ.det_pos.ne'
  rw [mul_smul_comm, mul_nonsing_inv Q hdet, trace_smul, trace_one, Fintype.card_fin]
  simp only [smul_eq_mul]
  ring

@[powerlib_foundation] theorem rlc_equipartition_two {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.PosDef) (T : ℝ) : (1 / 2 : ℝ) * (Q * (T • Q⁻¹)).trace = T := by
  rw [rlc_equipartition hQ]; norm_num

/-! ## Itô / Stratonovich drift conversion (correction to T-sph §1.5) -/

/-- Stratonovich → Itô drift correction `c_k = ½ Σ_{j,ℓ} h_{ℓj} ∂_ℓ h_{kj}`, given the
Jacobian array `dh k j ℓ = ∂_ℓ h_{kj}` at the current state. -/
def stratCorrection (h : Matrix (Fin n) (Fin q) ℝ) (dh : Fin n → Fin q → Fin n → ℝ) :
    Fin n → ℝ :=
  fun k => (1 / 2 : ℝ) * ∑ j, ∑ l, h l j * dh k j l

/-- The Itô drift of a Stratonovich SDE `δx = μ_S dt + h δW` is `μ_S + c`; the diffusion
coefficient is `h` in both forms.  The two drifts coincide iff the correction vanishes. -/
@[powerlib_foundation] theorem itoDrift_eq_iff (μS : Fin n → ℝ) (h : Matrix (Fin n) (Fin q) ℝ)
    (dh : Fin n → Fin q → Fin n → ℝ) :
    μS + stratCorrection h dh = μS ↔ stratCorrection h dh = 0 := by
  constructor
  · intro H; simpa using H
  · intro H; rw [H, add_zero]

/-- State-independent diffusion (`∂h = 0`) gives no drift correction. -/
@[powerlib_foundation] theorem stratCorrection_const (h : Matrix (Fin n) (Fin q) ℝ) :
    stratCorrection h (fun _ _ _ => 0) = 0 := by
  funext k; simp [stratCorrection]

end powerlib.Stochastic.SPH
