import theorem.Transform.Park
import theorem.Hurwitz

/-! Single series R–L branch in the αβ and dq frames: zero-input exponential stability.

Source: work-sync `theory/T-park-transformation.md` §1.4 (dq-frame KVL with `±ωL` cross terms)
and `theory/T-impedance-modeling.md` §1.7 (dq impedance of an R–L grid branch).

Model boundary:
* System: ONE series R–L branch (one inductor `L`, one resistor `R`, balanced, identical in
  both phases), driven by a branch voltage `v`. Current direction IN-positive
  (`conventions.md` §D1). No converter, controller, PLL, delay, PWM or saturation.
* Time: continuous. Parameters: any real `R`, `L`; `ω` real and CONSTANT (ideal grid / frame
  frequency, `θ(t) = ω t`). The time-varying-`ω` trajectory correspondence is
  `alphaBetaRL_iff_dqRL` in `theorem/Transform/Park.lean`.
* αβ state `(i_α, i_β)`; dq state `(i_d, i_q)` with `i^{dq} = park(ω t) i^{αβ}`.
  Zero-input dq field `ẋ = A x`, `A = −(R/L) I − ω J = [[−R/L, ω], [−ω, −R/L]]`
  (`dqRLMatrix`); αβ field `ẋ = −(R/L) x`.
* Conclusions are trajectory-level (`LTI.ExponentiallyStable`, every global solution decays
  exponentially in the Euclidean norm). `dqRL_exponentiallyStable_iff`: stable iff `R/L > 0`.
  `alphaBeta_exponentiallyStable_iff_dq`: the αβ and dq descriptions are stable together; this
  is proved by transporting trajectories through the norm-preserving rotation, not through
  the eigenvalues.
* `dqRLPlant` is the input-driven dq model (input `v`, output `i`); its transfer matrix is the
  inverse of the dq impedance `Z_dq(s) = (sL + R) I + ωL J` (`T-impedance-modeling.md` §1.7).
-/

noncomputable section
namespace powerlib.Transform
open Matrix
open powerlib.LTI

/-- Zero-input dq-frame state matrix `−(R/L) I − ω J` of one R–L branch. -/
def dqRLMatrix (R L ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-(R / L), ω; -ω, -(R / L)]

/-- Zero-input dq-frame RL branch as an autonomous LTI model (state `(i_d, i_q)`). -/
def dqRLModel (R L ω : ℝ) : AutonomousModel 2 := ⟨dqRLMatrix R L ω⟩

/-- Zero-input αβ-frame RL branch as an autonomous LTI model (state `(i_α, i_β)`). -/
def alphaBetaRLModel (R L : ℝ) : AutonomousModel 2 := ⟨dqRLMatrix R L 0⟩

@[powerlib_foundation] theorem dqRLMatrix_eq (R L ω : ℝ) :
    dqRLMatrix R L ω = -(R / L) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ω • J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dqRLMatrix, J]

@[powerlib_foundation] theorem dqRLModel_field (R L ω : ℝ) (x : Fin 2 → ℝ) :
    (dqRLModel R L ω).field x = L⁻¹ • ((0 : Fin 2 → ℝ) - R • x) - ω • (J *ᵥ x) := by
  ext k; fin_cases k <;>
    simp [dqRLModel, AutonomousModel.field, dqRLMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

@[powerlib_foundation] theorem alphaBetaRLModel_field (R L : ℝ) (x : Fin 2 → ℝ) :
    (alphaBetaRLModel R L).field x = L⁻¹ • ((0 : Fin 2 → ℝ) - R • x) := by
  rw [show alphaBetaRLModel R L = dqRLModel R L 0 from rfl, dqRLModel_field]
  simp

/-- The LTI model is exactly the zero-input dq KVL of `T-park-transformation.md` §1.4. -/
@[powerlib_foundation] theorem isTrajectory_dqRLModel_iff (R L ω : ℝ) (i : ℝ → Fin 2 → ℝ) :
    IsTrajectory (dqRLModel R L ω) i ↔ DqRL R L (fun _ => ω) 0 i := by
  simp only [IsTrajectory, DqRL, dqRLModel_field, Pi.zero_apply]

/-- The LTI model is exactly the zero-input αβ KVL `L i̇ = −R i`. -/
@[powerlib_foundation] theorem isTrajectory_alphaBetaRLModel_iff (R L : ℝ) (i : ℝ → Fin 2 → ℝ) :
    IsTrajectory (alphaBetaRLModel R L) i ↔ AlphaBetaRL R L 0 i := by
  simp only [IsTrajectory, AlphaBetaRL, alphaBetaRLModel_field, Pi.zero_apply]

/-! ## Spectrum -/

@[powerlib_foundation] theorem det_characteristicMatrix_dqRL (R L ω : ℝ) (s : ℂ) :
    (characteristicMatrix (dqRLMatrix R L ω) s).det = (s + (R / L : ℝ)) ^ 2 + (ω : ℂ) ^ 2 := by
  simp [characteristicMatrix, dqRLMatrix, det_fin_two]
  ring

@[powerlib_foundation] private lemma re_eq_zero_of_sq_eq_neg_sq {z : ℂ} {ω : ℝ}
    (h : z ^ 2 + (ω : ℂ) ^ 2 = 0) : z.re = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq, Complex.mul_re, Complex.mul_im] at hre him
  have hxy : z.re * z.im = 0 := by linarith
  rcases mul_eq_zero.1 hxy with h0 | h0
  · exact h0
  · rw [h0] at hre
    nlinarith [sq_nonneg z.re, sq_nonneg ω]

/-- The dq state matrix is spectrally stable iff `R/L > 0` (eigenvalues `−R/L ± jω`). -/
@[powerlib_foundation] theorem spectrallyStable_dqRLMatrix_iff (R L ω : ℝ) :
    SpectrallyStable (dqRLMatrix R L ω) ↔ 0 < R / L := by
  constructor
  · intro h
    have hs := h (-(R / L : ℝ) + ω * Complex.I) (by
      rw [det_characteristicMatrix_dqRL]
      ring_nf
      rw [Complex.I_sq]
      ring)
    simpa using hs
  · intro hpos s hs
    rw [det_characteristicMatrix_dqRL] at hs
    have h0 := re_eq_zero_of_sq_eq_neg_sq hs
    simp at h0
    linarith

/-! ## Semantic stability -/

/-- **Domain.** Zero-input dq-frame RL branch at constant frame speed `ω`: every solution
decays exponentially iff `R/L > 0`. -/
@[powerlib_domain] theorem dqRL_exponentiallyStable_iff (R L ω : ℝ) :
    ExponentiallyStable (dqRLModel R L ω) ↔ 0 < R / L := by
  rw [exponentiallyStable_iff_spectrallyStable]
  exact spectrallyStable_dqRLMatrix_iff R L ω

/-- **Domain.** With a positive inductance, the dq RL branch is exponentially stable iff `R > 0`. -/
@[powerlib_domain] theorem dqRL_exponentiallyStable_iff_resistance_pos {R L : ℝ} (ω : ℝ)
    (hL : 0 < L) : ExponentiallyStable (dqRLModel R L ω) ↔ 0 < R := by
  rw [dqRL_exponentiallyStable_iff, div_pos_iff_of_pos_right hL]

@[powerlib_foundation] private lemma hasDerivAt_mul_const_left (ω t : ℝ) :
    HasDerivAt (fun s : ℝ => ω * s) ω t := by
  simpa using (hasDerivAt_id t).const_mul ω

/-- **Domain.** αβ exponential stability transfers to the dq frame (rotation preserves norm). -/
@[powerlib_domain] theorem dqRL_exponentiallyStable_of_alphaBeta {R L : ℝ} (ω : ℝ)
    (h : ExponentiallyStable (alphaBetaRLModel R L)) : ExponentiallyStable (dqRLModel R L ω) := by
  obtain ⟨K, hK, r, hr, hb⟩ := h
  refine ⟨K, hK, r, hr, fun x hx t ht => ?_⟩
  have hy : IsTrajectory (alphaBetaRLModel R L) (fun s => rot (ω * s) *ᵥ x s) := by
    have h' := alphaBetaRL_of_dqRL (θ := fun s => ω * s) (ω := fun _ => ω)
      (hasDerivAt_mul_const_left ω) ((isTrajectory_dqRLModel_iff R L ω x).1 hx)
    rw [show (fun s => rot (ω * s) *ᵥ (0 : ℝ → Fin 2 → ℝ) s) = 0 from
      funext fun s => Matrix.mulVec_zero _] at h'
    exact (isTrajectory_alphaBetaRLModel_iff R L _).2 h'
  have hbt := hb _ hy t ht
  simp only [euclidean] at hbt ⊢
  rwa [norm_rot_mulVec, norm_rot_mulVec] at hbt

/-- **Domain.** dq exponential stability transfers back to the αβ frame. -/
@[powerlib_domain] theorem alphaBeta_exponentiallyStable_of_dqRL {R L : ℝ} (ω : ℝ)
    (h : ExponentiallyStable (dqRLModel R L ω)) : ExponentiallyStable (alphaBetaRLModel R L) := by
  obtain ⟨K, hK, r, hr, hb⟩ := h
  refine ⟨K, hK, r, hr, fun x hx t ht => ?_⟩
  have hy : IsTrajectory (dqRLModel R L ω) (fun s => park (ω * s) *ᵥ x s) := by
    have h' := dqRL_of_alphaBetaRL (θ := fun s => ω * s) (ω := fun _ => ω)
      (hasDerivAt_mul_const_left ω) ((isTrajectory_alphaBetaRLModel_iff R L x).1 hx)
    rw [show (fun s => park (ω * s) *ᵥ (0 : ℝ → Fin 2 → ℝ) s) = 0 from
      funext fun s => Matrix.mulVec_zero _] at h'
    exact (isTrajectory_dqRLModel_iff R L ω _).2 h'
  have hbt := hb _ hy t ht
  simp only [euclidean] at hbt ⊢
  rwa [norm_park_mulVec, norm_park_mulVec] at hbt

/-- **Domain.** The αβ and dq descriptions of the RL branch are exponentially stable together. -/
@[powerlib_domain] theorem alphaBeta_exponentiallyStable_iff_dq (R L ω : ℝ) :
    ExponentiallyStable (alphaBetaRLModel R L) ↔ ExponentiallyStable (dqRLModel R L ω) :=
  ⟨dqRL_exponentiallyStable_of_alphaBeta ω, alphaBeta_exponentiallyStable_of_dqRL ω⟩

/-! ## Input-driven dq model and the dq impedance -/

/-- dq RL branch with voltage input and current output: `ẋ = A x + L⁻¹ v`, `y = x`. -/
def dqRLPlant (R L ω : ℝ) : Model (Fin 2) (Fin 2) := ⟨dqRLMatrix R L ω, L⁻¹ • 1, 1, 0⟩

/-- dq impedance of the branch, `Z_dq(s) = [[sL + R, −ωL], [ωL, sL + R]]`. -/
def dqImpedance (R L ω : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![s * L + R, -(ω * L); ω * L, s * L + R]

@[powerlib_foundation] theorem dqRLPlant_field (R L ω : ℝ) (x v : Fin 2 → ℝ) :
    (dqRLPlant R L ω).field x v = L⁻¹ • (v - R • x) - ω • (J *ᵥ x) := by
  ext k; fin_cases k <;>
    simp [dqRLPlant, Model.field, dqRLMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

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

end powerlib.Transform
