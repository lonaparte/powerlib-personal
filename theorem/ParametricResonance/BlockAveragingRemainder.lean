import theorem.ParametricResonance.BlockAveragingDetuned

/-! # First-order averaging with an `O(ε²)` remainder

`BlockAveragingDetuned` treats the variational matrix `A₀c + ε(A₀' + Re{A₁ e^{jωt}})` exactly. The
variational matrix along a real forced orbit also has terms of order `ε²` (curvature of the vector
field along the orbit, second harmonic and DC shift of the orbit). This file adds a remainder
`ε² R_ε(t)`, continuous in `t` and bounded uniformly for small `ε`, and shows that the first-order
criterion is unchanged: the remainder enters the monodromy at `O(ε²)`.

Scope.
* Block system `fullR = fullB + ε² R_ε(t)` (modal coordinates) and physical system
  `physJR = physJ + ε² R_ε(t)` on any finite state space; `R_ε` continuous for each
  `ε ∈ (0, ε₁]` and `‖R_ε(t)‖ ≤ C_R` there. All other hypotheses as in `BlockAveragingDetuned`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (`J_p = A₀ + ε Re{A₁ e^{jω_p t}}` along the forced
trajectory, `g_m = l_mᴴ A₁ r_m*`, first-order averaging), [8, 9] of that report.

Results.
* `Averaging.monodromy_expansion_pert` — `‖Φ(ε(F + εG)) − I − εT F̄‖ ≤ ε² K` with `K` depending only
  on the bounds of `F` and `G`.
* `fullR`, `GzR`, `FzR`, `psi_frame_R`, `GzcR`, `FzcR`, `FzcR_eq`, `continuous_GzcR`,
  `continuous_FzcR`, `continuous_fullR`, `exists_bound_psi`, `bound_GzcR`, `transition_fullR`,
  `monodromy_blocks_R` — the frame `Ψ` and the block estimates of the monodromy with the remainder.
* `averagingR_stable`, `averagingR_unstable` — the criterion in modal coordinates.
* `physJR`, `physJR_eq`, `modal_remainder`, `physical_stable_R`, `physical_unstable_R` — in
  physical coordinates; `three_stable_R`, `three_unstable_R` — for three-state cores from their
  eigen-data.

Corrections.
None.

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section

namespace powerlib.ParametricResonance.Averaging
open Matrix Set Filter Topology
open scoped Matrix.Norms.Operator Interval

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The monodromy expansion with an `O(ε)` perturbation of the standard form:
`‖Φ(ε(F + εG)) − I − εT F̄‖ ≤ ε² K` with `K` depending only on the bounds of `F` and `G`. -/
@[tmio T, powerlib_foundation] theorem monodromy_expansion_pert {F G : ℝ → Matrix X X ℝ}
    {M MG T ε : ℝ} (hF : Continuous F) (hG : Continuous G) (hM : ∀ t, ‖F t‖ ≤ M)
    (hMG : ∀ t, ‖G t‖ ≤ MG) (hM0 : 0 ≤ M) (hMG0 : 0 ≤ MG) (hT : 0 ≤ T)
    {Fbar : Matrix X X ℝ} (havg : ∫ r in (0 : ℝ)..T, F r = T • Fbar) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖Periodic.monodromy (fun t => ε • (F t + ε • G t)) T 0 - 1 - (ε * T) • Fbar‖ ≤
      ε ^ 2 * ((M + MG) * T * ((M + MG) * T * (‖(1 : Matrix X X ℝ)‖ *
        Real.exp ((M + MG) * T))) + T * MG) := by
  have hFG : Continuous (fun t => F t + ε • G t) := hF.add (hG.const_smul ε)
  have hA : Continuous (fun t => ε • (F t + ε • G t)) := hFG.const_smul ε
  have hM' : ∀ t, ‖F t + ε • G t‖ ≤ M + MG := fun t => by
    refine (norm_add_le _ _).trans (add_le_add (hM t) ?_)
    rw [norm_smul, Real.norm_of_nonneg hε]
    calc ε * ‖G t‖ ≤ 1 * MG := mul_le_mul hε1 (hMG t) (norm_nonneg _) zero_le_one
      _ = MG := one_mul _
  have hMε : ∀ t, ‖ε • (F t + ε • G t)‖ ≤ ε * (M + MG) := fun t => by
    rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left (hM' t) hε
  have h := Averaging.norm_transition_sub_integral_le hA hMε (by positivity) hT
  have hint : ∫ r in (0 : ℝ)..T, ε • (F r + ε • G r) =
      (ε * T) • Fbar + ε ^ 2 • ∫ r in (0 : ℝ)..T, G r := by
    have e2 : ∫ r in (0 : ℝ)..T, (F r + ε • G r) =
        (∫ r in (0 : ℝ)..T, F r) + ε • ∫ r in (0 : ℝ)..T, G r := by
      rw [← intervalIntegral.integral_smul]
      exact intervalIntegral.integral_add (hF.intervalIntegrable 0 T)
        ((hG.intervalIntegrable 0 T).smul ε)
    rw [intervalIntegral.integral_smul, e2, havg, smul_add, smul_smul, smul_smul, sq]
  rw [hint] at h
  have hGi : ‖∫ r in (0 : ℝ)..T, G r‖ ≤ MG * T := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
      (fun t _ => hMG t)
    rwa [sub_zero, abs_of_nonneg hT] at this
  rw [Periodic.monodromy, zero_add]
  have e : Periodic.transition (fun t => ε • (F t + ε • G t)) T 0 - 1 - (ε * T) • Fbar =
      (Periodic.transition (fun t => ε • (F t + ε • G t)) T 0 - 1 -
        ((ε * T) • Fbar + ε ^ 2 • ∫ r in (0 : ℝ)..T, G r)) + ε ^ 2 • ∫ r in (0 : ℝ)..T, G r := by
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have hexp : Real.exp (ε * (M + MG) * T) ≤ Real.exp ((M + MG) * T) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg (add_nonneg hM0 hMG0) hT])
  have h1 : 0 ≤ ‖(1 : Matrix X X ℝ)‖ := norm_nonneg _
  have hMT : 0 ≤ (M + MG) * T := mul_nonneg (add_nonneg hM0 hMG0) hT
  have b1 : ε * (M + MG) * T * (ε * (M + MG) * T * (‖(1 : Matrix X X ℝ)‖ *
      Real.exp (ε * (M + MG) * T))) ≤ ε ^ 2 * ((M + MG) * T * ((M + MG) * T *
        (‖(1 : Matrix X X ℝ)‖ * Real.exp ((M + MG) * T)))) := by
    calc ε * (M + MG) * T * (ε * (M + MG) * T * (‖(1 : Matrix X X ℝ)‖ *
          Real.exp (ε * (M + MG) * T)))
        = ε ^ 2 * ((M + MG) * T * ((M + MG) * T * (‖(1 : Matrix X X ℝ)‖ *
          Real.exp (ε * (M + MG) * T)))) := by ring
      _ ≤ _ := by gcongr
  have b2 : ‖ε ^ 2 • ∫ r in (0 : ℝ)..T, G r‖ ≤ ε ^ 2 * (T * MG) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith [h.trans b1, b2]

end powerlib.ParametricResonance.Averaging

namespace powerlib.ParametricResonance.BlockAveraging
open Complex Matrix Filter Topology Set
open scoped Matrix.Norms.Operator
open NormalForm (rot quarter)
open TwoToOne (base modReal stdForm left right)

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ### The block system with an `O(ε²)` remainder -/

/-- The block system with an `O(ε²)` time-periodic remainder `ε² R_ε(t)`. -/
def fullR (s d ω : ℝ) (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (ε t : ℝ) : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  fullB s d ω As A B ε t + ε ^ 2 • Rm ε t

/-- The remainder in the frame `Ψ`. -/
def GzR (ω : ℝ) (As : Matrix Y Y ℝ) (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε t : ℝ) :
    Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  PsiInv ω As t * Rm ε t * Psi ω As t

/-- The standard form with the remainder. -/
def FzR (s d ω : ℝ) (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (ε t : ℝ) : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  FzB s d ω As A B t + ε • GzR ω As Rm ε t

@[tmio T, powerlib_foundation] theorem psi_frame_R (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε t : ℝ) :
    fromBlocks ((ω / 2) • (rot (ω * t / 2) * quarter)) 0 0 (expS As t * As) +
        Psi ω As t * (ε • FzR s d ω As A B Rm ε t) = fullR s d ω As A B Rm ε t * Psi ω As t := by
  have hPP : Psi ω As t * GzR ω As Rm ε t = Rm ε t * Psi ω As t := by
    rw [GzR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, psi_mul_inv, Matrix.one_mul]
  rw [FzR, smul_add, Matrix.mul_add, ← add_assoc, psi_frame_B, fullR, Matrix.add_mul, smul_smul,
    Matrix.mul_smul, hPP, Matrix.smul_mul, sq]

/-- The frozen remainder and standard form. -/
def GzcR (ω T : ℝ) (As : Matrix Y Y ℝ) (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (ε t : ℝ) : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  GzR ω As Rm ε (clampT T t)

def FzcR (s d ω T : ℝ) (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (ε t : ℝ) : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  FzcB s d ω T As A B t + ε • GzcR ω T As Rm ε t

@[tmio T, powerlib_foundation] theorem FzcR_eq (s d ω T : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε t : ℝ) :
    FzcR s d ω T As A B Rm ε t = FzR s d ω As A B Rm ε (clampT T t) := rfl

@[tmio T, powerlib_foundation] theorem continuous_GzcR (ω T : ℝ) (As : Matrix Y Y ℝ)
    (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε : ℝ) (hRc : Continuous (Rm ε)) :
    Continuous (GzcR ω T As Rm ε) :=
  (((continuous_psiInv ω As).mul hRc).mul (continuous_psi ω As)).comp (continuous_clampT T)

@[tmio T, powerlib_foundation] theorem continuous_FzcR (s d ω T : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε : ℝ) (hRc : Continuous (Rm ε)) :
    Continuous (FzcR s d ω T As A B Rm ε) :=
  (continuous_FzcB s d ω T As A B).add ((continuous_GzcR ω T As Rm ε hRc).const_smul ε)

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] theorem continuous_fullR (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε : ℝ) (hRc : Continuous (Rm ε)) :
    Continuous (fullR s d ω As A B Rm ε) :=
  (continuous_fullB s d ω As A B ε).add
    (Continuous.smul (f := fun _ => ε ^ 2) (g := fun t => Rm ε t) continuous_const hRc)

@[tmio T, powerlib_foundation] theorem exists_bound_psi (ω : ℝ) (As : Matrix Y Y ℝ) (T : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ‖Psi ω As t‖ ≤ C ∧ ‖PsiInv ω As t‖ ≤ C := by
  obtain ⟨C1, h1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_psi ω As).continuousOn
  obtain ⟨C2, h2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_psiInv ω As).continuousOn
  refine ⟨max (max C1 C2) 0, le_max_right _ _, fun t ht => ⟨?_, ?_⟩⟩
  · exact (h1 t ht).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h2 t ht).trans ((le_max_right _ _).trans (le_max_left _ _))

@[tmio T, powerlib_foundation] theorem bound_GzcR (ω : ℝ) (As : Matrix Y Y ℝ)
    (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) {T CP CR ε : ℝ} (hT : 0 ≤ T) (hCP0 : 0 ≤ CP)
    (hCP : ∀ t ∈ Icc 0 T, ‖Psi ω As t‖ ≤ CP ∧ ‖PsiInv ω As t‖ ≤ CP)
    (hR : ∀ t, ‖Rm ε t‖ ≤ CR) (t : ℝ) :
    ‖GzcR ω T As Rm ε t‖ ≤ CP * CR * CP := by
  obtain ⟨h1, h2⟩ := hCP _ (clampT_mem hT t)
  have hR0 : 0 ≤ CR := (norm_nonneg _).trans (hR 0)
  rw [GzcR, GzR]
  calc ‖PsiInv ω As (clampT T t) * Rm ε (clampT T t) * Psi ω As (clampT T t)‖
      ≤ ‖PsiInv ω As (clampT T t)‖ * ‖Rm ε (clampT T t)‖ * ‖Psi ω As (clampT T t)‖ := by
        refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ CP * CR * CP := by gcongr; exact hR _

@[tmio T, powerlib_foundation] theorem transition_fullR (s d ω : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε : ℝ) (hRc : Continuous (Rm ε)) :
    Periodic.transition (fullR s d ω As A B Rm ε) T 0 =
      Psi ω As T * Periodic.transition (fun t => ε • FzcR s d ω T As A B Rm ε t) T 0 := by
  have hF : Continuous (fun t => ε • FzcR s d ω T As A B Rm ε t) :=
    (continuous_FzcR s d ω T As A B Rm ε hRc).const_smul ε
  have hA := continuous_fullR s d ω As A B Rm ε hRc
  obtain ⟨Bd, hBd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hA.continuousOn
  set Z := fun t => Periodic.transition (fun t => ε • FzcR s d ω T As A B Rm ε t) t 0 with hZ
  have hYs : IsIntegralCurveOn (fun t => Psi ω As t * Z t) (Periodic.matField (fullR s d ω As A B Rm ε))
      (uIcc 0 T) := by
    intro r hr
    rw [uIcc_of_le hT] at hr
    have h := (hasDerivAt_psi ω As r).mul (Dynamics.stm_hasDerivAt hF r 0)
    have key : fromBlocks ((ω / 2) • (rot (ω * r / 2) * quarter)) 0 0 (expS As r * As) * Z r +
        Psi ω As r * ((ε • FzcR s d ω T As A B Rm ε r) * Z r) =
        Periodic.matField (fullR s d ω As A B Rm ε) r (Psi ω As r * Z r) := by
      rw [Periodic.matField, FzcR_eq, clampT_of_mem hr, ← Matrix.mul_assoc, ← Matrix.add_mul,
        psi_frame_R, Matrix.mul_assoc]
    exact (h.congr_deriv key).hasDerivWithinAt
  have hu := LinearSystems.stateTransitionMatrix_mul_unique hA (M := Bd)
    (fun r hr => by rw [uIcc_of_le hT] at hr; exact hBd r hr) _
    (hYs.isIntegralSolution (hA.continuousOn.mul hYs.continuousOn)) hYs.continuousOn T
    right_mem_uIcc
  have h0 : Psi ω As 0 * Z 0 = 1 := by
    simp [hZ, Psi, expS, rot, LinearSystems.stateTransitionMatrix_self]
  rw [h0, Matrix.mul_one] at hu
  exact hu.symm

@[tmio T, powerlib_foundation] theorem monodromy_blocks_R (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    {ε1 CR : ℝ} (hRc : ∀ ε, 0 < ε → ε ≤ ε1 → Continuous (Rm ε))
    (hRb : ∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖Rm ε t‖ ≤ CR) (hq1 : ‖expS As (2 * Real.pi / ω)‖ ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ ε, 0 < ε → ε ≤ 1 → ε ≤ ε1 → ∃ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
      (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      Periodic.monodromy (fullR s d ω As A B Rm ε) (2 * Real.pi / ω) 0 = fromBlocks P Q R S ∧
      ‖P + 1 + (ε * (2 * Real.pi / ω)) •
          slowFlowMatrix (s - shiftRe B) (d - shiftIm B) (Element.pump A.toBlocks₁₁ left right / 2)‖ ≤ C * ε ^ 2 ∧
      ‖Q‖ ≤ C * ε ∧ ‖R‖ ≤ C * ε ∧ ‖S‖ ≤ ‖expS As (2 * Real.pi / ω)‖ + C * ε := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨M, hM0, hM⟩ := exists_bound_FzcB s d ω hT.le As A B
  set Fbar := T⁻¹ • ∫ t in (0 : ℝ)..T, FzcB s d ω T As A B t with hFbar
  have havg : ∫ t in (0 : ℝ)..T, FzcB s d ω T As A B t = T • Fbar := by
    rw [hFbar, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  have hFb : ‖Fbar‖ ≤ M := norm_average_le hT hM
  have hF11 : Fbar.toBlocks₁₁ = slowFlowMatrix (s - shiftRe B) (d - shiftIm B) (Element.pump A.toBlocks₁₁ left right / 2) :=
    average_toBlocks₁₁_B s d hω As A B
  obtain ⟨CP, hCP0, hCP⟩ := exists_bound_psi ω As T
  set MG := CP * max CR 0 * CP with hMG
  have hMG0 : 0 ≤ MG := by positivity
  set K := (M + MG) * T * ((M + MG) * T * (‖(1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)‖ *
    Real.exp ((M + MG) * T))) + T * MG with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨T * M + K, by positivity, fun ε hε hε1 hεε1 => ?_⟩
  have hG : ∀ t, ‖GzcR ω T As Rm ε t‖ ≤ MG := fun t =>
    bound_GzcR ω As Rm hT.le hCP0 hCP
      (fun t => (hRb ε hε hεε1 t).trans (le_max_left _ _)) t
  have hexp := Averaging.monodromy_expansion_pert (continuous_FzcB s d ω T As A B)
    (continuous_GzcR ω T As Rm ε (hRc ε hε hεε1)) hM hG hM0 hMG0 hT.le havg hε.le hε1
  set Φz := Periodic.monodromy (fun t => ε • FzcR s d ω T As A B Rm ε t) T 0 with hΦz
  set R2 := Φz - 1 - (ε * T) • Fbar with hR2
  have hR2n : ‖R2‖ ≤ K * ε ^ 2 := by
    rw [hR2, hΦz]
    refine hexp.trans (le_of_eq ?_)
    rw [hK]; ring
  have hΦzR : Φz = 1 + (ε * T) • Fbar + R2 := by rw [hR2]; abel
  have hpsiT : Psi ω As T = fromBlocks (-1) 0 0 (expS As T) := by
    have h : ω * T / 2 = Real.pi := by rw [hTdef]; field_simp
    rw [Psi, h]
    congr 1
    simp [rot]
  have hmono : Periodic.monodromy (fullR s d ω As A B Rm ε) T 0 = fromBlocks (-Φz.toBlocks₁₁)
      (-Φz.toBlocks₁₂) (expS As T * Φz.toBlocks₂₁) (expS As T * Φz.toBlocks₂₂) := by
    rw [Periodic.monodromy, zero_add, transition_fullR s d ω hT.le As A B Rm ε (hRc ε hε hεε1), hpsiT]
    have : Periodic.transition (fun t => ε • FzcR s d ω T As A B Rm ε t) T 0 = Φz := by
      rw [hΦz, Periodic.monodromy, zero_add]
    rw [this, ← fromBlocks_toBlocks Φz, fromBlocks_multiply]
    simp
  obtain ⟨b11, b12, b21, b22⟩ := norm_toBlocks_le R2
  obtain ⟨f11, f12, f21, f22⟩ := norm_toBlocks_le Fbar
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have h12 : Φz.toBlocks₁₂ = (ε * T) • Fbar.toBlocks₁₂ + R2.toBlocks₁₂ := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₁₂]
  have h21 : Φz.toBlocks₂₁ = (ε * T) • Fbar.toBlocks₂₁ + R2.toBlocks₂₁ := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₂₁]
  have h22 : Φz.toBlocks₂₂ = 1 + ((ε * T) • Fbar.toBlocks₂₂ + R2.toBlocks₂₂) := by
    rw [hΦzR]; ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply, add_assoc]
  have h11 : -Φz.toBlocks₁₁ + 1 + (ε * T) • slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
      (Element.pump A.toBlocks₁₁ left right / 2) = -R2.toBlocks₁₁ := by
    rw [hΦzR, ← hF11]
    ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]; ring
  have hblk : ∀ (Fb Rb : ℝ), Fb ≤ M → Rb ≤ K * ε ^ 2 → ε * T * Fb + Rb ≤ (T * M + K) * ε := by
    intro Fb Rb hFb' hRb
    have h1 : ε * T * Fb ≤ ε * T * M := by
      have : 0 ≤ ε * T := by positivity
      exact mul_le_mul_of_nonneg_left hFb' this
    have h2 : K * ε ^ 2 ≤ K * ε := mul_le_mul_of_nonneg_left hε2 hK0
    nlinarith
  refine ⟨_, _, _, _, hmono, ?_, ?_, ?_, ?_⟩
  · rw [h11, norm_neg]
    exact b11.trans (hR2n.trans (by nlinarith [sq_nonneg ε, mul_nonneg hT.le hM0]))
  · rw [h12, norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact hblk _ _ (f12.trans hFb) (b12.trans hR2n)
  · rw [h21]
    refine (linfty_opNorm_mul _ _).trans ?_
    have h : ‖(ε * T) • Fbar.toBlocks₂₁ + R2.toBlocks₂₁‖ ≤ (T * M + K) * ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact hblk _ _ (f21.trans hFb) (b21.trans hR2n)
    calc ‖expS As T‖ * ‖(ε * T) • Fbar.toBlocks₂₁ + R2.toBlocks₂₁‖ ≤ 1 * ((T * M + K) * ε) :=
          mul_le_mul hq1 h (norm_nonneg _) zero_le_one
      _ = (T * M + K) * ε := one_mul _
  · rw [h22, Matrix.mul_add, Matrix.mul_one]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (linfty_opNorm_mul _ _).trans ?_
    have h : ‖(ε * T) • Fbar.toBlocks₂₂ + R2.toBlocks₂₂‖ ≤ (T * M + K) * ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact hblk _ _ (f22.trans hFb) (b22.trans hR2n)
    calc ‖expS As T‖ * ‖(ε * T) • Fbar.toBlocks₂₂ + R2.toBlocks₂₂‖ ≤ 1 * ((T * M + K) * ε) :=
          mul_le_mul hq1 h (norm_nonneg _) zero_le_one
      _ = (T * M + K) * ε := one_mul _

/-! ### Averaging with the remainder -/

/-- First-order averaging with a stable remainder, stability: if the slow flow of the critical
pair is exponentially stable (`s > 0`, `|g/2|² < s² + d²`, `g = u A₁₁ r̄`) and the stable block
contracts over one period (`‖e^{TA_s}‖ < 1`), every Floquet multiplier of the complete `n`-state
system lies inside the unit circle for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem averagingR_stable {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) {ε1 CR : ℝ} (hε1 : 0 < ε1)
    (hRc : ∀ ε, 0 < ε → ε ≤ ε1 → Continuous (Rm ε))
    (hRb : ∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖Rm ε t‖ ≤ CR) (hs : 0 < s - shiftRe B)
    (hg : ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2 <
      (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2)
    (hq : ‖expS As (2 * Real.pi / ω)‖ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
      (Periodic.monodromy (fullR s d ω As A B Rm ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ v =
        μ • v → ‖μ‖ < 1 := by
  obtain ⟨C, hC, hblk⟩ := monodromy_blocks_R s d hω As A B Rm hRc hRb hq.le
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have h := block_stable (Y := Y) hT
    (Ms := slowFlowMatrix (s - shiftRe B) (d - shiftIm B) (Element.pump A.toBlocks₁₁ left right / 2))
    (by rw [trace_slowFlowMatrix]; linarith) (by rw [det_slowFlowMatrix]; linarith) hC hq
  filter_upwards [h, eventually_lt_nhdsGT one_pos, eventually_lt_nhdsGT hε1] with ε hε ⟨hε0, hεo⟩ ⟨_, hεe⟩
  obtain ⟨P, Q, R, S, heq, hP, hQ, hR, hS⟩ := hblk ε hε0 hεo.le hεe.le
  rw [heq]
  exact hε P Q R S hP hQ hR hS

/-- First-order averaging with a stable remainder, parametric instability: if the slow flow of the
critical pair has a positive real exponent (`s² + d² < |g/2|²`) and the stable block contracts
over one period, the complete `n`-state system has a real Floquet multiplier below `−1` for all
small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem averagingR_unstable {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (Rm : ℝ → ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) {ε1 CR : ℝ} (hε1 : 0 < ε1)
    (hRc : ∀ ε, 0 < ε → ε ≤ ε1 → Continuous (Rm ε))
    (hRb : ∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖Rm ε t‖ ≤ CR)
    (hg : (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2 < ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hq : ‖expS As (2 * Real.pi / ω)‖ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (fullR s d ω As A B Rm ε) (2 * Real.pi / ω) := by
  obtain ⟨C, hC, hblk⟩ := monodromy_blocks_R s d hω As A B Rm hRc hRb hq.le
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have h := block_unstable (Y := Y) hT
    (Ms := slowFlowMatrix (s - shiftRe B) (d - shiftIm B) (Element.pump A.toBlocks₁₁ left right / 2))
    (by rw [det_slowFlowMatrix]; linarith) hC hq
  filter_upwards [h, eventually_lt_nhdsGT one_pos, eventually_lt_nhdsGT hε1] with ε hε ⟨hε0, hεo⟩ ⟨_, hεe⟩
  obtain ⟨P, Q, R, S, heq, hP, hQ, hR, hS⟩ := hblk ε hε0 hεo.le hεe.le
  obtain ⟨μ, hμ, hdet⟩ := hε P Q R S hP hQ hR hS
  refine ⟨(μ : ℂ), ?_, ?_⟩
  · rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det, heq]
    have hmap : (μ : ℂ) • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) -
        (fromBlocks P Q R S).map (algebraMap ℝ ℂ) =
        (μ • (1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) - fromBlocks P Q R S).map (algebraMap ℝ ℂ) := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> simp
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_zero]
    exact not_isUnit_zero
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith

/-! ### Physical coordinates and three-state cores with the remainder -/

section Physical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The physical variational matrix with an `O(ε²)` remainder:
`A₀c + ε (A₀' + Re{A₁ e^{jωt}}) + ε² R_ε(t)`. -/
def physJR (A0c A0' : Matrix X X ℝ) (A1 : Matrix X X ℂ) (Rm : ℝ → ℝ → Matrix X X ℝ)
    (ω ε t : ℝ) : Matrix X X ℝ :=
  physJ A0c A0' A1 ω ε t + ε ^ 2 • Rm ε t

omit [DecidableEq Y] in
@[tmio T, powerlib_foundation] theorem physJR_eq {ω : ℝ} {P : Matrix X (Fin 2 ⊕ Y) ℝ}
    {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) {A0c : Matrix X X ℝ} {As : Matrix Y Y ℝ}
    (hA0 : Q * A0c * P = fromBlocks (base 0 (ω / 2)) 0 0 As) (A0' : Matrix X X ℝ)
    (A1 : Matrix X X ℂ) (Rm : ℝ → ℝ → Matrix X X ℝ) (ε t : ℝ) :
    physJR A0c A0' A1 Rm ω ε t = P * fullR 0 0 ω As
      (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P)
      (fun ε t => Q * Rm ε t * P) ε t * Q := by
  have hc : ∀ M : Matrix X X ℝ, P * (Q * M * P) * Q = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_assoc, hPQ,
      Matrix.mul_one]
  rw [physJR, physJ_eq hPQ hA0 A0' A1 ε t, fullR, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, hc]

@[tmio T, powerlib_foundation] theorem modal_remainder {P : Matrix X (Fin 2 ⊕ Y) ℝ}
    {Q : Matrix (Fin 2 ⊕ Y) X ℝ} {Rm : ℝ → ℝ → Matrix X X ℝ} {ε1 CR : ℝ}
    (hRc : ∀ ε, 0 < ε → ε ≤ ε1 → Continuous (Rm ε))
    (hRb : ∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖Rm ε t‖ ≤ CR) :
    (∀ ε, 0 < ε → ε ≤ ε1 → Continuous (fun t => Q * Rm ε t * P)) ∧
      ∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖Q * Rm ε t * P‖ ≤ ‖Q‖ * CR * ‖P‖ := by
  refine ⟨fun ε h0 h1 => (continuous_const.matrix_mul (hRc ε h0 h1)).matrix_mul continuous_const,
    fun ε h0 h1 t => ?_⟩
  calc ‖Q * Rm ε t * P‖ ≤ ‖Q * Rm ε t‖ * ‖P‖ := Matrix.linfty_opNorm_mul _ _
    _ ≤ ‖Q‖ * ‖Rm ε t‖ * ‖P‖ :=
        mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ ‖Q‖ * CR * ‖P‖ := by gcongr; exact hRb ε h0 h1 t

/-- Physical coordinates with remainder, stability: as `physical_stable`, for
`A₀c + ε(A₀' + Re{A₁ e^{jωt}}) + ε² R_ε(t)` with `R_ε` continuous and bounded uniformly in small
`ε`. -/
@[tmio T, powerlib_foundation] theorem physical_stable_R {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) {A0c : Matrix X X ℝ} (As : Matrix Y Y ℝ)
    (hA0 : Q * A0c * P = fromBlocks (base 0 (ω / 2)) 0 0 As) (A0' : Matrix X X ℝ)
    (A1 : Matrix X X ℂ) (Rm : ℝ → ℝ → Matrix X X ℝ) {ε1 CR : ℝ} (hε1 : 0 < ε1)
    (hRc : ∀ ε, 0 < ε → ε ≤ ε1 → Continuous (Rm ε))
    (hRb : ∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖Rm ε t‖ ≤ CR)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2)
    (hq : ‖expS As (2 * Real.pi / ω)‖ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
      (Periodic.monodromy (physJR A0c A0' A1 Rm ω ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hshift := shift_conj P Q A0'
  have hpump := pump_conj P Q A1
  have hn : ‖(shiftRe (Q * A0' * P) : ℂ) + (shiftIm (Q * A0' * P) : ℂ) * I‖ ^ 2 =
      shiftRe (Q * A0' * P) ^ 2 + shiftIm (Q * A0' * P) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [hshift] at hs hg
  rw [hn, ← hpump] at hg
  have hs' : 0 < 0 - shiftRe (Q * A0' * P) := by simp at hs; linarith
  have hg' : ‖Element.pump (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)).toBlocks₁₁
      left right / 2‖ ^ 2 < (0 - shiftRe (Q * A0' * P)) ^ 2 + (0 - shiftIm (Q * A0' * P)) ^ 2 := by
    simpa using hg
  obtain ⟨hRc', hRb'⟩ := modal_remainder (P := P) (Q := Q) hRc hRb
  have h := averagingR_stable hω As _ _ (fun ε t => Q * Rm ε t * P) hε1 hRc' hRb' hs' hg' hq
  have hT : 0 ≤ 2 * Real.pi / ω := by positivity
  filter_upwards [h, eventually_lt_nhdsGT hε1] with ε hε ⟨hε0, hεe⟩
  intro μ v hv hμ
  have hfun : physJR A0c A0' A1 Rm ω ε = fun t => P * fullR 0 0 ω As
      (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P)
      (fun ε t => Q * Rm ε t * P) ε t * Q :=
    funext fun t => physJR_eq hPQ hA0 A0' A1 Rm ε t
  rw [hfun, Periodic.monodromy, zero_add,
    transition_conj (continuous_fullR _ _ _ _ _ _ _ _ (hRc' ε hε0 hεe.le)) hPQ hQP hT] at hμ
  obtain ⟨hw, hw'⟩ := eig_conj hPQ hQP hv hμ
  exact hε μ _ hw (by rw [Periodic.monodromy, zero_add]; exact hw')

/-- Physical coordinates with remainder, parametric instability. -/
@[tmio T, powerlib_foundation] theorem physical_unstable_R {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) {A0c : Matrix X X ℝ} (As : Matrix Y Y ℝ)
    (hA0 : Q * A0c * P = fromBlocks (base 0 (ω / 2)) 0 0 As) (A0' : Matrix X X ℝ)
    (A1 : Matrix X X ℂ) (Rm : ℝ → ℝ → Matrix X X ℝ) {ε1 CR : ℝ} (hε1 : 0 < ε1)
    (hRc : ∀ ε, 0 < ε → ε ≤ ε1 → Continuous (Rm ε))
    (hRb : ∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖Rm ε t‖ ≤ CR)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2‖ ^ 2)
    (hq : ‖expS As (2 * Real.pi / ω)‖ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Periodic.FloquetUnstable (physJR A0c A0' A1 Rm ω ε) (2 * Real.pi / ω) := by
  have hshift := shift_conj P Q A0'
  have hpump := pump_conj P Q A1
  have hn : ‖(shiftRe (Q * A0' * P) : ℂ) + (shiftIm (Q * A0' * P) : ℂ) * I‖ ^ 2 =
      shiftRe (Q * A0' * P) ^ 2 + shiftIm (Q * A0' * P) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [hshift, hn, ← hpump] at hg
  have hg' : (0 - shiftRe (Q * A0' * P)) ^ 2 + (0 - shiftIm (Q * A0' * P)) ^ 2 <
      ‖Element.pump (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)).toBlocks₁₁
        left right / 2‖ ^ 2 := by
    simpa using hg
  obtain ⟨hRc', hRb'⟩ := modal_remainder (P := P) (Q := Q) hRc hRb
  have h := averagingR_unstable hω As _ _ (fun ε t => Q * Rm ε t * P) hε1 hRc' hRb' hg' hq
  have hT : 0 ≤ 2 * Real.pi / ω := by positivity
  filter_upwards [h, eventually_lt_nhdsGT hε1] with ε hε ⟨hε0, hεe⟩
  obtain ⟨ρ, hρ, hn1⟩ := hε
  refine ⟨ρ, ?_, hn1⟩
  have hfun : physJR A0c A0' A1 Rm ω ε = fun t => P * fullR 0 0 ω As
      (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P)
      (fun ε t => Q * Rm ε t * P) ε t * Q :=
    funext fun t => physJR_eq hPQ hA0 A0' A1 Rm ε t
  rw [hfun, Periodic.monodromy, zero_add,
    transition_conj (continuous_fullR _ _ _ _ _ _ _ _ (hRc' ε hε0 hεe.le)) hPQ hQP hT]
  rw [Periodic.monodromy, zero_add] at hρ
  exact spectrum_conj hQP hρ

end Physical

/-- Three-state cores with remainder, stability (`three_stable` for
`A₀c + ε(A₀' + Re{A₁ e^{2jΩt}}) + ε² R_ε(t)`). -/
@[tmio T, powerlib_foundation] theorem three_stable_R {Ω l3 : ℝ} (hΩ : 0 < Ω) (hl3 : l3 < 0)
    {A0c : Matrix (Fin 3) (Fin 3) ℝ} {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : A0c.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A0c.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : A0c *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* A0c = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (A1 : Matrix (Fin 3) (Fin 3) ℂ)
    (Rm : ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) {ε1 CR : ℝ} (hε1 : 0 < ε1)
    (hRc : ∀ ε, 0 < ε → ε ≤ ε1 → Continuous (Rm ε))
    (hRb : ∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖Rm ε t‖ ≤ CR)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ (A1 *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
      (Periodic.monodromy (physJR A0c A0' A1 Rm (2 * Ω) ε) (2 * Real.pi / (2 * Ω)) 0).map
          (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨hQP, hPQ, hQAP, hL, hR⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * A0c * modalP r r3 = fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact physical_stable_R hω hPQ hQP _ hA0 A0' A1 Rm hε1 hRc hRb (by rw [hL, hR]; exact hs)
    (by rw [hL, hR]; exact hg) hq

/-- Three-state cores with remainder, parametric instability. -/
@[tmio T, powerlib_foundation] theorem three_unstable_R {Ω l3 : ℝ} (hΩ : 0 < Ω) (hl3 : l3 < 0)
    {A0c : Matrix (Fin 3) (Fin 3) ℝ} {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : A0c.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A0c.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : A0c *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* A0c = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (A1 : Matrix (Fin 3) (Fin 3) ℂ)
    (Rm : ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) {ε1 CR : ℝ} (hε1 : 0 < ε1)
    (hRc : ∀ ε, 0 < ε → ε ≤ ε1 → Continuous (Rm ε))
    (hRb : ∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖Rm ε t‖ ≤ CR)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖u ⬝ᵥ (A1 *ᵥ star r) / 2‖ ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Periodic.FloquetUnstable (physJR A0c A0' A1 Rm (2 * Ω) ε) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hQP, hPQ, hQAP, hL, hR⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * A0c * modalP r r3 = fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact physical_unstable_R hω hPQ hQP _ hA0 A0' A1 Rm hε1 hRc hRb (by rw [hL, hR]; exact hg) hq

end powerlib.ParametricResonance.BlockAveraging
