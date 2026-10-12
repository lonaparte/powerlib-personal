import theorem.Transform.Park
import theorem.CurrentControl.SISO

/-! # Single series R–L branch in the αβ and dq frames

Source: work-sync `theory/T-park-transformation.md` §1.4 (dq-frame KVL with `±ωL` cross terms)
and `theory/T-impedance-modeling.md` §1.7 (dq impedance of an R–L grid branch).

Model boundary:
* System: ONE series R–L branch (one inductor `L`, one resistor `R`, balanced, identical in
  both phases), driven by a branch voltage `v`. Current direction IN-positive
  (`conventions.md` §D1). No converter, controller, PLL, delay, PWM or saturation.
* Time: continuous. Parameters: any real `R`, `L`; `ω` real and CONSTANT (ideal grid / frame
  frequency, `θ(t) = ω t`). The time-varying-`ω` trajectory correspondence is
  `alphaBetaRL_iff_dqRL` in `theorem/Transform/Park.lean`.
* αβ state `(i_α, i_β)`; dq state `(i_d, i_q)` with `i^{dq} = park(ω t) i^{αβ}`, both in
  `EuclideanSpace ℝ (Fin 2)`. dq field `ẋ = A x + L⁻¹ v`,
  `A = −(R/L) I − ω J = [[−R/L, ω], [−ω, −R/L]]` (`dqRLMatrix`); the αβ description is the
  case `ω = 0`.
* `dqRLPlant` is the input-driven dq model (input `v`, output `i`); its transfer matrix is the
  inverse of the dq impedance `Z_dq(s) = (sL + R) I + ωL J` (`T-impedance-modeling.md` §1.7).

## Family and connection conclusions

`family : Family DqBranch Spectral.Requirement 2 2` reads a branch `(R, L, ω)` as the port
system of `dqRLPlant` (`Spectral.linearFamily`); a flow sentence speaks about the zero-input
branch at the origin. Requirements: `R/L > 0` (`stable`, eigenvalues `−R/L ± jω`) and
`R/L < 0` (`unstable`). The αβ branch is the member `DqBranch.alphaBeta m = (R, L, 0)`.
* `chain_le_semantics`, `exact`: every translation sound; the attractive sentences and sampled
  contraction are carved out exactly by `R/L > 0`.
* `mem_den_iff` (formerly `dqRL_exponentiallyStable_iff`) and `mem_den_iff_resistance_pos`
  (formerly `dqRL_exponentiallyStable_iff_resistance_pos`): stable iff `R/L > 0`, iff `R > 0`
  when `L > 0`.
* `den_eq_alphaBeta` (connection comparison; formerly `alphaBeta_exponentiallyStable_iff_dq`
  with its two directions): the attractive denotation of the dq family is its own pull-back
  along `DqBranch.alphaBeta` — the αβ and dq descriptions are stable together, at every frame
  speed. The former proof transported trajectories through the norm-preserving rotation
  (`alphaBetaRL_of_dqRL`, `dqRL_of_alphaBetaRL` in `Transform/Park.lean`); the comparison is
  now read from the spectra (`spectrallyStable_dqRLMatrix_iff`), which do not depend on `ω`.
The spectra, the field identity and the dq impedance are static evidence. The former adapters
`isTrajectory_dqRLModel_iff`, `isTrajectory_alphaBetaRLModel_iff` between the deleted
`LTI.IsTrajectory` and Park's KVL predicates have no counterpart: the trajectory form of the
dq KVL is Park's `DqRL`, and the plant's field is `dqRLPlant_field`.
-/

noncomputable section
namespace powerlib.Transform
open Matrix Linear LinearSystems

/-- Zero-input dq-frame state matrix `−(R/L) I − ω J` of one R–L branch. -/
def dqRLMatrix (R L ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-(R / L), ω; -ω, -(R / L)]

@[powerlib_foundation] theorem dqRLMatrix_eq (R L ω : ℝ) :
    dqRLMatrix R L ω = -(R / L) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ω • J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dqRLMatrix, J]

/-! ## Spectrum -/

@[powerlib_foundation] theorem det_characteristicMatrix_dqRL (R L ω : ℝ) (s : ℂ) :
    (characteristicMatrix (dqRLMatrix R L ω) s).det = (s + (R / L : ℝ)) ^ 2 + (ω : ℂ) ^ 2 := by
  simp [characteristicMatrix, dqRLMatrix, det_fin_two]
  ring

private lemma re_eq_zero_of_sq_eq_neg_sq {z : ℂ} {ω : ℝ}
    (h : z ^ 2 + (ω : ℂ) ^ 2 = 0) : z.re = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq, Complex.mul_re, Complex.mul_im] at hre him
  have hxy : z.re * z.im = 0 := by linarith
  rcases mul_eq_zero.1 hxy with h0 | h0
  · exact h0
  · rw [h0] at hre
    nlinarith [sq_nonneg z.re, sq_nonneg ω]

/-- The eigenvalue `−R/L + jω` of the dq state matrix. -/
@[powerlib_foundation] theorem dqRL_root (R L ω : ℝ) :
    (characteristicMatrix (dqRLMatrix R L ω) (-(R / L : ℝ) + ω * Complex.I)).det = 0 := by
  rw [det_characteristicMatrix_dqRL]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The dq state matrix is spectrally stable iff `R/L > 0` (eigenvalues `−R/L ± jω`). -/
@[powerlib_foundation] theorem spectrallyStable_dqRLMatrix_iff (R L ω : ℝ) :
    SpectrallyStable (dqRLMatrix R L ω) ↔ 0 < R / L := by
  constructor
  · intro h
    have hs := h _ (dqRL_root R L ω)
    simpa using hs
  · intro hpos s hs
    rw [det_characteristicMatrix_dqRL] at hs
    have h0 := re_eq_zero_of_sq_eq_neg_sq hs
    simp at h0
    linarith

/-- The dq state matrix is Hurwitz iff `R/L > 0`, at every frame speed. Static evidence on the
model, not a connection conclusion. -/
@[powerlib_foundation] theorem isHurwitz_dqRLMatrix_iff (R L ω : ℝ) :
    IsHurwitz (dqRLMatrix R L ω) ↔ 0 < R / L := by
  rw [← spectrallyStable_iff_isHurwitz, spectrallyStable_dqRLMatrix_iff]

/-! ## Input-driven dq model and the dq impedance -/

/-- dq RL branch with voltage input and current output: `ẋ = A x + L⁻¹ v`, `y = x`. -/
def dqRLPlant (R L ω : ℝ) : Plant 2 2 := ⟨dqRLMatrix R L ω, L⁻¹ • 1, 1, 0⟩

/-- dq impedance of the branch, `Z_dq(s) = [[sL + R, −ωL], [ωL, sL + R]]`. -/
def dqImpedance (R L ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![s * L + R, -(ω * L); ω * L, s * L + R]

/-- The plant's field is the dq KVL `L i' = v − R i − ωL J i` of `T-park-transformation.md` §1.4. -/
@[powerlib_foundation] theorem dqRLPlant_field (R L ω : ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (v : Fin 2 → ℝ) :
    WithLp.ofLp ((dqRLPlant R L ω).inputField v x) =
      L⁻¹ • (v - R • WithLp.ofLp x) - ω • (J *ᵥ WithLp.ofLp x) := by
  ext k; fin_cases k <;>
    simp [dqRLPlant, Plant.inputField, op, dqRLMatrix, J, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

@[powerlib_foundation] theorem characteristicMatrix_dqRL_eq {R L : ℝ} (hL : L ≠ 0) (ω : ℝ)
    (s : ℂ) : characteristicMatrix (dqRLMatrix R L ω) s = (L⁻¹ : ℂ) • dqImpedance R L ω s := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [characteristicMatrix, dqRLMatrix, dqImpedance] <;>
    field_simp

/-- The dq admittance of the plant inverts the dq impedance wherever `s` is not a pole. -/
@[powerlib_foundation] theorem transfer_dqRLPlant_mul_dqImpedance {R L : ℝ} (hL : L ≠ 0)
    (ω : ℝ) {s : ℂ} (hs : (characteristicMatrix (dqRLMatrix R L ω) s).det ≠ 0) :
    transfer (dqRLPlant R L ω) s * dqImpedance R L ω s = 1 := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hB : complexify (L⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = (L⁻¹ : ℂ) • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hZ : (L⁻¹ : ℂ) • dqImpedance R L ω s = characteristicMatrix (dqRLMatrix R L ω) s :=
    (characteristicMatrix_dqRL_eq hL ω s).symm
  simp only [transfer, dqRLPlant, hB, complexify_zero, add_zero]
  rw [show complexify (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 by simp, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Matrix.mul_smul, hZ]
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs)

/-! ## The dq RL-branch family -/

/-- One series R–L branch read in the dq frame rotating at the constant speed `ω`. -/
@[ext] structure DqBranch where
  R : ℝ
  L : ℝ
  ω : ℝ

namespace DqBranch

/-- The plant of the branch: input the branch voltage, output the current. -/
def plant (m : DqBranch) : Plant 2 2 := dqRLPlant m.R m.L m.ω

@[powerlib_foundation] theorem isHurwitz_plant_iff (m : DqBranch) :
    IsHurwitz m.plant.A ↔ 0 < m.R / m.L := by
  change IsHurwitz (dqRLMatrix m.R m.L m.ω) ↔ _
  exact isHurwitz_dqRLMatrix_iff m.R m.L m.ω

@[powerlib_foundation] theorem exists_root_of_neg (m : DqBranch) (h : m.R / m.L < 0) :
    ∃ s : ℂ, (characteristicMatrix m.plant.A s).det = 0 ∧ 0 < s.re := by
  refine ⟨_, dqRL_root m.R m.L m.ω, ?_⟩
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  linarith

/-- The same branch in the stationary αβ frame (`ω = 0`). -/
def alphaBeta (m : DqBranch) : DqBranch := ⟨m.R, m.L, 0⟩

end DqBranch

/-- The dq RL-branch family: every branch read as the port system of its plant. -/
def family : Family DqBranch Spectral.Requirement 2 2 :=
  Spectral.linearFamily DqBranch.plant (fun m => 0 < m.R / m.L) (fun m => m.R / m.L < 0)

private theorem den_flow {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    family.den (.flow P) = {m | 0 < m.R / m.L} :=
  Spectral.linear_den (U := fun m : DqBranch => m.R / m.L < 0)
    (fun m => m.isHurwitz_plant_iff.symm) hP

/-- Every translation of the dq RL-branch family is sound. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_chain_le_semantics (fun m h => m.isHurwitz_plant_iff.mpr h)
    (fun m h => m.exists_root_of_neg h)

/-- The attractive sentences and sampled contraction of the dq branch are carved out exactly by
`R/L > 0`. -/
@[powerlib_domain] theorem exact {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun m => m.isHurwitz_plant_iff.symm) hP

/-- Zero-input dq-frame RL branch at constant frame speed `ω`: an attractive sentence (in
particular exponential stability) holds iff `R/L > 0`. -/
@[powerlib_domain] theorem mem_den_iff (m : DqBranch) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ family.den (.flow P) ↔ m ∈ {m : DqBranch | 0 < m.R / m.L}) := by
  unfold powerlib.TMIO.Statement
  rw [den_flow hP]

/-- With a positive inductance, the dq RL branch is stable iff `R > 0`. -/
@[powerlib_domain] theorem mem_den_iff_resistance_pos (m : DqBranch) (hL : 0 < m.L)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ family.den (.flow P) ↔ m ∈ {m : DqBranch | 0 < m.R}) := by
  unfold powerlib.TMIO.Statement
  rw [den_flow hP]
  exact div_pos_iff_of_pos_right hL

/-- The αβ and dq descriptions of the RL branch are stable together, at every frame speed: the
attractive denotation of the dq family is its pull-back along the αβ reading. -/
@[powerlib_domain] theorem den_eq_alphaBeta {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.den (.flow P) = DqBranch.alphaBeta ⁻¹' family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [den_flow hP]
  rfl

end powerlib.Transform
