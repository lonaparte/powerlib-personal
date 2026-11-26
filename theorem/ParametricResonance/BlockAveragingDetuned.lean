import theorem.ParametricResonance.BlockAveraging

/-! # First-order averaging around a critical point, in physical coordinates

`BlockAveraging` proves the 2:1 averaging criterion for a system already in real modal form with
the damping and detuning of the critical pair built into the base matrix. A physical family is
instead `A₀(ε) = A₀c + ε A₀'`: a critical matrix with the pair `±jω/2` and a stable remainder, plus
an `O(ε)` change (damping, detuning) that need not be in modal form. This file adds the constant
perturbation `ε B` to the block system (only the rotation-commuting part of `B₁₁` survives the
average: the slow flow is shifted by the first-order eigenvalue shift), transports everything to
physical coordinates through a constant real similarity, and constructs that similarity for
three-state cores from their eigenvectors. The result reads: with `λ₁ = u A₀' r` and
`g = u A₁ r̄` (`u r = 1`), `Re λ₁ < 0`, `|g/2| < |λ₁|` gives Floquet stability and `|λ₁| < |g/2|`
Floquet instability of `A₀c + ε(A₀' + Re{A₁ e^{jωt}})` for all small `ε > 0`.

Scope.
* Linear time-periodic systems `ẋ = (A₀c + ε(A₀' + Re{A₁ e^{jωt}})) x` (`physJ`) on any finite
  state space; the modal coordinates `P`, `Q = P⁻¹` are hypotheses (`Q A₀c P = diag(base(0, ω/2),
  A_s)`) and the stable block enters through the spectral radius `ρ(e^{TA_s}) < 1` (`T = 2π/ω`),
  as in `BlockAveraging`; `StableBasis` constructs `P`, `Q` from the critical eigenvectors.
* `modal_three` builds `P`, `Q` for three states from right/left eigenvectors of `jΩ` and of a real
  pole `λ₃`; `norm_expS_one` gives `‖e^{Tλ₃}‖ = e^{λ₃T} < 1` for `λ₃ < 0`, hence `ρ < 1`.
* The variational matrix is taken to first order in `ε`; the `O(ε²)` terms of a physical orbit's
  variational equation are added in `BlockAveragingRemainder`, and the forced orbit itself is
  constructed in `ForcedOrbit` (composition: `ForcedOrbitFloquet`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (`J_p = A₀ + ε Re{A₁ e^{jω_p t}}`, `g_m = l_mᴴ A₁ r_m*`,
first-order averaging, `σ_m`, `Δ_m`), [8, 9] of that report.

Results.
* `commPart`, `rot_conj`, `integral_rot_conj` — `R(−θ) B R(θ) = C + cos 2θ N + sin 2θ NJ`; over one
  period only the commuting part `C = a I + b J` survives.
* `fullB`, `FzB`, `psi_frame_B`, `transition_fullB`, `FzB_toBlocks₁₁`, `average_toBlocks₁₁_B`,
  `monodromy_blocks_B` — the block system with `ε B`; its averaged critical block is
  `M_slow(s − a, d − b, g/2)`, `a + jb` = `shiftRe`, `shiftIm` of `B`.
* `averagingB_stable`, `averagingB_unstable` — the criterion with the shifted damping and detuning.
* `modX_conj`, `transition_conj`, `eig_conj`, `spectrum_conj` — a constant real similarity
  conjugates the modulation, the transition matrix and the Floquet multipliers;
  `pump_conj`, `shift_conj` — `g = u A₁ r̄` and `λ₁ = u A₀' r = a + jb` in physical coordinates
  (`physLeft`, `physRight`).
* `physJ_eq`, `physical_stable`, `physical_unstable` — the criterion in physical coordinates.
* `real_right_eig`, `real_left_eig`, `modalP`, `modalQ`, `modal_three`, `norm_expS_one`,
  `three_stable`, `three_unstable` — three-state cores from their eigen-data.

Corrections.
None: the first-order 2:1 criterion of §2.2 holds for the complete system in physical coordinates,
with `σ = −ε Re(u A₀' r)` and `ω/2 − Ω = −ε Im(u A₀' r)` the first-order damping and detuning.

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.BlockAveraging
open Complex Matrix Filter Topology Set
open scoped Matrix.Norms.Operator
open NormalForm (rot quarter)
open TwoToOne (base modReal stdForm left right)

/-! ### A constant matrix in the rotating frame -/

/-- The rotation-commuting part `a I + b J` of a real `2 × 2` matrix,
`a = tr B/2`, `b = (B₁₀ − B₀₁)/2`, written as `M_slow(−a, −b, 0)`. -/
def commPart (B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  slowFlowMatrix (-((B 0 0 + B 1 1) / 2)) (-((B 1 0 - B 0 1) / 2)) 0

/-- `R(−θ) B R(θ) = C + cos 2θ N + sin 2θ N J` with `C` the commuting part and `N = B − C`. -/
@[tmio T, powerlib_foundation] theorem rot_conj (B : Matrix (Fin 2) (Fin 2) ℝ) (θ : ℝ) :
    rot (-θ) * B * rot θ = commPart B + Real.cos (2 * θ) • (B - commPart B) +
      Real.sin (2 * θ) • ((B - commPart B) * quarter) := by
  have hsc := Real.cos_sq_add_sin_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, quarter, commPart, slowFlowMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Real.cos_two_mul, Real.sin_two_mul, Real.cos_neg, Real.sin_neg] <;>
    first
      | linear_combination (B 1 1) * hsc
      | linear_combination (-B 1 0) * hsc
      | linear_combination (-B 0 1) * hsc
      | linear_combination (B 0 0) * hsc


/-- `∫₀ᵀ R(−ωt/2) B R(ωt/2) dt = T C(B)`, `T = 2π/ω`: only the commuting part survives. -/
@[tmio T, powerlib_foundation] theorem integral_rot_conj {ω : ℝ} (hω : 0 < ω)
    (B : Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), rot (-(ω * t / 2)) * B * rot (ω * t / 2) =
      (2 * Real.pi / ω) • commPart B := by
  have hc1 := TwoToOne.integral_cos_mul_period hω 1 one_ne_zero
  have hs1 := TwoToOne.integral_sin_mul_period hω 1 one_ne_zero
  simp only [Nat.cast_one, one_mul] at hc1 hs1
  have hfun : (fun t => rot (-(ω * t / 2)) * B * rot (ω * t / 2)) = fun t =>
      commPart B + Real.cos (ω * t) • (B - commPart B) +
        Real.sin (ω * t) • ((B - commPart B) * quarter) := by
    funext t; rw [rot_conj, show 2 * (ω * t / 2) = ω * t by ring]
  rw [hfun, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, hc1, hs1]
  simp

/-! ### The `n`-state model with a constant `O(ε)` perturbation -/

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The real part `a = tr B₁₁/2` of the first-order eigenvalue shift `u B r = a + jb`. -/
def shiftRe (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) : ℝ := (B.toBlocks₁₁ 0 0 + B.toBlocks₁₁ 1 1) / 2

/-- The imaginary part `b = (B₁₀ − B₀₁)/2` of the first-order eigenvalue shift. -/
def shiftIm (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) : ℝ := (B.toBlocks₁₁ 1 0 - B.toBlocks₁₁ 0 1) / 2

/-- The full system with a constant `O(ε)` perturbation `ε B` of the state matrix (damping and
detuning of a physical family `A₀(ε) = A₀c + ε A₀'`, in modal coordinates). -/
def fullB (s d ω : ℝ) (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε t : ℝ) : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  fullN s d ω As A ε t + ε • B

/-- The standard form in the frame `Ψ`. -/
def FzB (s d ω : ℝ) (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (t : ℝ) : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  Fz s d ω As A t + PsiInv ω As t * B * Psi ω As t

@[tmio T, powerlib_foundation] theorem psi_frame_B (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε t : ℝ) :
    fromBlocks ((ω / 2) • (rot (ω * t / 2) * quarter)) 0 0 (expS As t * As) +
        Psi ω As t * (ε • FzB s d ω As A B t) = fullB s d ω As A B ε t * Psi ω As t := by
  have hPP : Psi ω As t * (PsiInv ω As t * B * Psi ω As t) = B * Psi ω As t := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, psi_mul_inv, Matrix.one_mul]
  rw [FzB, smul_add, Matrix.mul_add, ← add_assoc, psi_frame, fullB, Matrix.add_mul,
    Matrix.mul_smul, hPP, Matrix.smul_mul]

/-- The standard form frozen outside `[0, T]`. -/
def FzcB (s d ω T : ℝ) (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (t : ℝ) : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ :=
  FzB s d ω As A B (clampT T t)

@[tmio T, powerlib_foundation] theorem continuous_FzB (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) :
    Continuous (FzB s d ω As A B) :=
  (continuous_Fz s d ω As A).add (((continuous_psiInv ω As).mul continuous_const).mul
    (continuous_psi ω As))

@[tmio T, powerlib_foundation] theorem continuous_FzcB (s d ω T : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) :
    Continuous (FzcB s d ω T As A B) :=
  (continuous_FzB s d ω As A B).comp (continuous_clampT T)

@[tmio T, powerlib_foundation] theorem exists_bound_FzcB (s d ω : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ t, ‖FzcB s d ω T As A B t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_FzB s d ω As A B).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  exact (hM _ (clampT_mem hT t)).trans (le_max_left _ _)

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] theorem continuous_fullB (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε : ℝ) :
    Continuous (fullB s d ω As A B ε) :=
  (continuous_fullN s d ω As A ε).add continuous_const

/-- On `[0, T]` the transition matrix of the full system is `Ψ(t)` times that of the frozen
standard form. -/
@[tmio T, powerlib_foundation] theorem transition_fullB (s d ω : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ε : ℝ) :
    Periodic.transition (fullB s d ω As A B ε) T 0 =
      Psi ω As T * Periodic.transition (fun t => ε • FzcB s d ω T As A B t) T 0 := by
  have hF : Continuous (fun t => ε • FzcB s d ω T As A B t) :=
    (continuous_FzcB s d ω T As A B).const_smul ε
  have hA := continuous_fullB s d ω As A B ε
  obtain ⟨Bd, hBd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hA.continuousOn
  set Z := fun t => Periodic.transition (fun t => ε • FzcB s d ω T As A B t) t 0 with hZ
  have hYs : IsIntegralCurveOn (fun t => Psi ω As t * Z t) (Periodic.matField (fullB s d ω As A B ε))
      (uIcc 0 T) := by
    intro r hr
    rw [uIcc_of_le hT] at hr
    have h := (hasDerivAt_psi ω As r).mul (Dynamics.stm_hasDerivAt hF r 0)
    have key : fromBlocks ((ω / 2) • (rot (ω * r / 2) * quarter)) 0 0 (expS As r * As) * Z r +
        Psi ω As r * ((ε • FzcB s d ω T As A B r) * Z r) =
        Periodic.matField (fullB s d ω As A B ε) r (Psi ω As r * Z r) := by
      rw [Periodic.matField, FzcB, clampT_of_mem hr, ← Matrix.mul_assoc, ← Matrix.add_mul,
        psi_frame_B, Matrix.mul_assoc]
    exact (h.congr_deriv key).hasDerivWithinAt
  have hu := LinearSystems.stateTransitionMatrix_mul_unique hA (M := Bd)
    (fun r hr => by rw [uIcc_of_le hT] at hr; exact hBd r hr) _
    (hYs.isIntegralSolution (hA.continuousOn.mul hYs.continuousOn)) hYs.continuousOn T
    right_mem_uIcc
  have h0 : Psi ω As 0 * Z 0 = 1 := by
    simp [hZ, Psi, expS, rot, LinearSystems.stateTransitionMatrix_self]
  rw [h0, Matrix.mul_one] at hu
  exact hu.symm

@[tmio T, powerlib_foundation] theorem FzB_toBlocks₁₁ (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (t : ℝ) :
    (FzB s d ω As A B t).toBlocks₁₁ =
      stdForm s d ω A.toBlocks₁₁ t + rot (-(ω * t / 2)) * B.toBlocks₁₁ * rot (ω * t / 2) := by
  have hadd : (FzB s d ω As A B t).toBlocks₁₁ = (Fz s d ω As A t).toBlocks₁₁ +
      (PsiInv ω As t * B * Psi ω As t).toBlocks₁₁ := rfl
  rw [hadd, Fz_toBlocks₁₁, PsiInv, Psi, ← fromBlocks_toBlocks B, fromBlocks_multiply,
    fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₁]
  simp

/-- The average of the frozen standard form: its critical block is the slow-flow matrix with the
damping and detuning shifted by the first-order eigenvalue shift `a + jb` of `B`. -/
@[tmio T, powerlib_foundation] theorem average_toBlocks₁₁_B (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) :
    ((2 * Real.pi / ω)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi / ω),
        FzcB s d ω (2 * Real.pi / ω) As A B t).toBlocks₁₁ =
      slowFlowMatrix (s - shiftRe B) (d - shiftIm B) (Element.pump A.toBlocks₁₁ left right / 2) := by
  set T := 2 * Real.pi / ω with hT
  have hT0 : 0 < T := by positivity
  have hint : (∫ t in (0 : ℝ)..T, FzcB s d ω T As A B t).toBlocks₁₁ =
      ∫ t in (0 : ℝ)..T, (stdForm s d ω A.toBlocks₁₁ t +
        rot (-(ω * t / 2)) * B.toBlocks₁₁ * rot (ω * t / 2)) := by
    have h := blk11.intervalIntegral_comp_comm
      ((continuous_FzcB s d ω T As A B).intervalIntegrable (μ := MeasureTheory.volume) 0 T)
    have h' : (∫ t in (0 : ℝ)..T, blk11 (FzcB s d ω T As A B t)) =
        ∫ t in (0 : ℝ)..T, (stdForm s d ω A.toBlocks₁₁ t +
          rot (-(ω * t / 2)) * B.toBlocks₁₁ * rot (ω * t / 2)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hT0.le] at ht
      show (FzcB s d ω T As A B t).toBlocks₁₁ = _
      rw [FzcB, clampT_of_mem ht, FzB_toBlocks₁₁]
    rw [← h']
    exact h.symm
  have hsmul : ∀ (c : ℝ) (M : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ),
      (c • M).toBlocks₁₁ = c • M.toBlocks₁₁ := fun _ _ => rfl
  have hc1 : Continuous (fun t => stdForm s d ω A.toBlocks₁₁ t) := TwoToOne.continuous_stdForm s d ω _
  have hc2 : Continuous (fun t : ℝ => rot (-(ω * t / 2)) * B.toBlocks₁₁ * rot (ω * t / 2)) := by
    unfold rot; fun_prop
  rw [hsmul, hint, intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _), hT, TwoToOne.integral_stdForm s d hω, integral_rot_conj hω,
    ← smul_add, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slowFlowMatrix, commPart, shiftRe, shiftIm] <;> ring

/-- The monodromy of the full system in blocks: `P = −(I + εT M_slow) + O(ε²)`, `Q, R = O(ε)`,
`S = e^{TA_s} + O(ε)`, `T = 2π/ω`. -/
@[tmio T, powerlib_foundation] theorem monodromy_blocks_B (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ε, 0 < ε → ε ≤ 1 → ∃ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
      (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
      Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω) 0 = fromBlocks P Q R S ∧
      ‖P + 1 + (ε * (2 * Real.pi / ω)) •
          slowFlowMatrix (s - shiftRe B) (d - shiftIm B) (Element.pump A.toBlocks₁₁ left right / 2)‖ ≤ C * ε ^ 2 ∧
      ‖Q‖ ≤ C * ε ∧ ‖R‖ ≤ C * ε ∧ ‖S - expS As (2 * Real.pi / ω)‖ ≤ C * ε := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨M, hM0, hM⟩ := exists_bound_FzcB s d ω hT.le As A B
  set Fbar := T⁻¹ • ∫ t in (0 : ℝ)..T, FzcB s d ω T As A B t with hFbar
  have havg : ∫ t in (0 : ℝ)..T, FzcB s d ω T As A B t = T • Fbar := by
    rw [hFbar, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  have hFb : ‖Fbar‖ ≤ M := norm_average_le hT hM
  have hF11 : Fbar.toBlocks₁₁ = slowFlowMatrix (s - shiftRe B) (d - shiftIm B) (Element.pump A.toBlocks₁₁ left right / 2) :=
    average_toBlocks₁₁_B s d hω As A B
  set K := M * T * (M * T * (‖(1 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)‖ * Real.exp (M * T)))
    with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set C0 := T * M + K with hC0
  have hC00 : 0 ≤ C0 := by positivity
  set e := ‖expS As T‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have hCC : C0 ≤ C0 * (1 + e) := le_mul_of_one_le_right hC00 (by linarith)
  have hCe : e * C0 ≤ C0 * (1 + e) := by
    rw [mul_comm e C0]; exact mul_le_mul_of_nonneg_left (by linarith) hC00
  refine ⟨C0 * (1 + e), by positivity, fun ε hε hε1 => ?_⟩
  have hexp := Averaging.monodromy_expansion (continuous_FzcB s d ω T As A B) hM hM0 hT.le havg
    hε.le hε1
  set Φz := Periodic.monodromy (fun t => ε • FzcB s d ω T As A B t) T 0 with hΦz
  set R2 := Φz - 1 - (ε * T) • Fbar with hR2
  rw [mul_comm] at hexp
  have hR2n : ‖R2‖ ≤ K * ε ^ 2 := hexp
  have hΦzR : Φz = 1 + (ε * T) • Fbar + R2 := by rw [hR2]; abel
  have hpsiT : Psi ω As T = fromBlocks (-1) 0 0 (expS As T) := by
    have h : ω * T / 2 = Real.pi := by rw [hTdef]; field_simp
    rw [Psi, h]
    congr 1
    simp [rot]
  have hmono : Periodic.monodromy (fullB s d ω As A B ε) T 0 = fromBlocks (-Φz.toBlocks₁₁)
      (-Φz.toBlocks₁₂) (expS As T * Φz.toBlocks₂₁) (expS As T * Φz.toBlocks₂₂) := by
    rw [Periodic.monodromy, zero_add, transition_fullB s d ω hT.le As A B ε, hpsiT]
    have : Periodic.transition (fun t => ε • FzcB s d ω T As A B t) T 0 = Φz := by
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
    refine b11.trans (hR2n.trans ?_)
    have h1 : K * ε ^ 2 ≤ C0 * ε ^ 2 :=
      mul_le_mul_of_nonneg_right (by rw [hC0]; exact le_add_of_nonneg_left (mul_nonneg hT.le hM0))
        (sq_nonneg ε)
    exact h1.trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg ε))
  · rw [h12, norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact (hblk _ _ (f12.trans hFb) (b12.trans hR2n)).trans
      (mul_le_mul_of_nonneg_right hCC hε.le)
  · rw [h21]
    refine (linfty_opNorm_mul _ _).trans ?_
    have h : ‖(ε * T) • Fbar.toBlocks₂₁ + R2.toBlocks₂₁‖ ≤ (T * M + K) * ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact hblk _ _ (f21.trans hFb) (b21.trans hR2n)
    calc ‖expS As T‖ * ‖(ε * T) • Fbar.toBlocks₂₁ + R2.toBlocks₂₁‖ ≤ e * (C0 * ε) :=
          mul_le_mul_of_nonneg_left h he0
      _ = e * C0 * ε := by ring
      _ ≤ C0 * (1 + e) * ε := mul_le_mul_of_nonneg_right hCe hε.le
  · rw [h22, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left]
    refine (linfty_opNorm_mul _ _).trans ?_
    have h : ‖(ε * T) • Fbar.toBlocks₂₂ + R2.toBlocks₂₂‖ ≤ (T * M + K) * ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact hblk _ _ (f22.trans hFb) (b22.trans hR2n)
    calc ‖expS As T‖ * ‖(ε * T) • Fbar.toBlocks₂₂ + R2.toBlocks₂₂‖ ≤ e * (C0 * ε) :=
          mul_le_mul_of_nonneg_left h he0
      _ = e * C0 * ε := by ring
      _ ≤ C0 * (1 + e) * ε := mul_le_mul_of_nonneg_right hCe hε.le

/-! ### First-order averaging with detuning and damping as an `O(ε)` perturbation -/

/-- First-order averaging with a stable remainder, stability: if the slow flow of the critical
pair is exponentially stable (`s > 0`, `|g/2|² < s² + d²`, `g = u A₁₁ r̄`) and the stable block
has one-period spectral radius `ρ(e^{TA_s}) < 1`, every Floquet multiplier of the complete `n`-state
system lies inside the unit circle for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem averagingB_stable {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (hs : 0 < s - shiftRe B)
    (hg : ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2 <
      (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
      (Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ v =
        μ • v → ‖μ‖ < 1 := by
  obtain ⟨C, hC, hblk⟩ := monodromy_blocks_B s d hω As A B
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have h := block_stable_spec (Y := Y) hT
    (Ms := slowFlowMatrix (s - shiftRe B) (d - shiftIm B) (Element.pump A.toBlocks₁₁ left right / 2))
    (by rw [trace_slowFlowMatrix]; linarith) (by rw [det_slowFlowMatrix]; linarith) hρ hC
  filter_upwards [h, eventually_lt_nhdsGT one_pos] with ε hε ⟨hε0, hε1⟩
  obtain ⟨P, Q, R, S, heq, hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
  rw [heq]
  exact hε P Q R S hP hQ hR hS

/-- First-order averaging with a stable remainder, parametric instability: if the slow flow of the
critical pair has a positive real exponent (`s² + d² < |g/2|²`) and the stable block contracts
over one period, the complete `n`-state system has a real Floquet multiplier below `−1` for all
small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem averagingB_unstable {s d ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (hg : (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2 < ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (fullB s d ω As A B ε) (2 * Real.pi / ω) := by
  obtain ⟨C, hC, hblk⟩ := monodromy_blocks_B s d hω As A B
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have h := block_unstable_spec (Y := Y) hT
    (Ms := slowFlowMatrix (s - shiftRe B) (d - shiftIm B) (Element.pump A.toBlocks₁₁ left right / 2))
    (by rw [det_slowFlowMatrix]; linarith) hρ hC
  filter_upwards [h, eventually_lt_nhdsGT one_pos] with ε hε ⟨hε0, hε1⟩
  obtain ⟨P, Q, R, S, heq, hP, hQ, hR, hS⟩ := hblk ε hε0 hε1.le
  obtain ⟨ρ, hρm, hρ1⟩ := hε P Q R S hP hQ hR hS
  exact ⟨ρ, by rw [heq]; exact hρm, hρ1⟩

/-! ### Physical coordinates: a constant real similarity -/

section Physical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The real modulation `Re{A₁ e^{jωt}}` on any state space. -/
def modX (A : Matrix X X ℂ) (ω t : ℝ) : Matrix X X ℝ :=
  fun i j => (A i j).re * Real.cos (ω * t) - (A i j).im * Real.sin (ω * t)

/-- The physical variational matrix `A₀c + ε (A₀' + Re{A₁ e^{jωt}})`: a critical state matrix
`A₀c`, its `O(ε)` change `A₀'` (damping and detuning), and the modulation. -/
def physJ (A0c A0' : Matrix X X ℝ) (A1 : Matrix X X ℂ) (ω ε t : ℝ) : Matrix X X ℝ :=
  A0c + ε • (A0' + modX A1 ω t)

omit [Fintype Y] [DecidableEq Y] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem modX_conj (P : Matrix X (Fin 2 ⊕ Y) ℝ)
    (Q : Matrix (Fin 2 ⊕ Y) X ℝ) (A : Matrix X X ℂ) (ω t : ℝ) [Fintype Y] :
    Q * modX A ω t * P =
      modN (Q.map (algebraMap ℝ ℂ) * A * P.map (algebraMap ℝ ℂ)) ω t := by
  ext i j
  simp [modN, modX, Matrix.mul_apply, Complex.re_sum, Complex.im_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The conjugation `M ↦ P M Q` as a continuous linear map. -/
def conjL (P : Matrix X (Fin 2 ⊕ Y) ℝ) (Q : Matrix (Fin 2 ⊕ Y) X ℝ) :
    Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ →L[ℝ] Matrix X X ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => P * M * Q
      map_add' := fun M N => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c M => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }

/-- A constant real similarity `P, Q = P⁻¹` conjugates the transition matrix. -/
@[tmio T, powerlib_foundation] theorem transition_conj {F : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ}
    (hF : Continuous F) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) {T : ℝ} (hT : 0 ≤ T) :
    Periodic.transition (fun t => P * F t * Q) T 0 = P * Periodic.transition F T 0 * Q := by
  have hA : Continuous (fun t => P * F t * Q) :=
    (continuous_const.matrix_mul hF).matrix_mul continuous_const
  obtain ⟨Bd, hBd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hA.continuousOn
  set Z := fun t => Periodic.transition F t 0 with hZ
  have hYs : IsIntegralCurveOn (fun t => P * Z t * Q)
      (Periodic.matField (fun t => P * F t * Q)) (uIcc 0 T) := by
    intro r _
    have h := (conjL P Q).hasFDerivAt.comp_hasDerivAt r (Dynamics.stm_hasDerivAt hF r 0)
    have key : conjL P Q (F r * LinearSystems.stateTransitionMatrix F r 0) =
        Periodic.matField (fun t => P * F t * Q) r (P * Z r * Q) := by
      show P * (F r * Z r) * Q = P * F r * Q * (P * Z r * Q)
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
    exact (h.congr_deriv key).hasDerivWithinAt
  have hu := LinearSystems.stateTransitionMatrix_mul_unique hA (M := Bd)
    (fun r hr => by rw [uIcc_of_le hT] at hr; exact hBd r hr) _
    (hYs.isIntegralSolution (hA.continuousOn.mul hYs.continuousOn)) hYs.continuousOn T
    right_mem_uIcc
  have h0 : P * Z 0 * Q = 1 := by
    simp [hZ, LinearSystems.stateTransitionMatrix_self, hPQ]
  rw [h0, Matrix.mul_one] at hu
  exact hu.symm

/-- A physical eigenpair of `P M Q` gives a modal eigenpair of `M`. -/
@[tmio T, powerlib_foundation] theorem eig_conj {P : Matrix X (Fin 2 ⊕ Y) ℝ}
    {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    {M : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} {μ : ℂ} {v : X → ℂ} (hv : v ≠ 0)
    (h : (P * M * Q).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    Q.map (algebraMap ℝ ℂ) *ᵥ v ≠ 0 ∧
      M.map (algebraMap ℝ ℂ) *ᵥ (Q.map (algebraMap ℝ ℂ) *ᵥ v) =
        μ • (Q.map (algebraMap ℝ ℂ) *ᵥ v) := by
  have hPQc : P.map (algebraMap ℝ ℂ) * Q.map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQPc : Q.map (algebraMap ℝ ℂ) * P.map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_mul, Matrix.map_mul] at h
  constructor
  · intro h0
    apply hv
    rw [← Matrix.one_mulVec v, ← hPQc, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  · calc M.map (algebraMap ℝ ℂ) *ᵥ (Q.map (algebraMap ℝ ℂ) *ᵥ v)
        = (Q.map (algebraMap ℝ ℂ) * P.map (algebraMap ℝ ℂ)) *ᵥ
            (M.map (algebraMap ℝ ℂ) *ᵥ (Q.map (algebraMap ℝ ℂ) *ᵥ v)) := by
          rw [hQPc, Matrix.one_mulVec]
      _ = Q.map (algebraMap ℝ ℂ) *ᵥ ((P.map (algebraMap ℝ ℂ) * M.map (algebraMap ℝ ℂ) *
            Q.map (algebraMap ℝ ℂ)) *ᵥ v) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = μ • (Q.map (algebraMap ℝ ℂ) *ᵥ v) := by rw [h, Matrix.mulVec_smul]

/-- Every modal Floquet multiplier is a physical one. -/
@[tmio T, powerlib_foundation] theorem spectrum_conj {P : Matrix X (Fin 2 ⊕ Y) ℝ}
    {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hQP : Q * P = 1)
    {M : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} {μ : ℂ}
    (h : μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ))) :
    μ ∈ spectrum ℂ ((P * M * Q).map (algebraMap ℝ ℂ)) := by
  set Pc := P.map (algebraMap ℝ ℂ)
  set Qc := Q.map (algebraMap ℝ ℂ)
  set Mc := M.map (algebraMap ℝ ℂ)
  have hQPc : Qc * Pc = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [spectrum.mem_iff] at h ⊢
  intro hu
  apply h
  rw [Matrix.map_mul, Matrix.map_mul] at hu
  obtain ⟨U, hU⟩ := hu
  set N := (U⁻¹ : (Matrix X X ℂ)ˣ).val
  have hUN : (algebraMap ℂ (Matrix X X ℂ) μ - Pc * Mc * Qc) * N = 1 := by
    rw [← hU]; exact U.mul_inv
  have hV : (algebraMap ℂ (Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) μ - Mc) * (Qc * N * Pc) = 1 := by
    have e : (algebraMap ℂ (Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) μ - Mc) * Qc =
        Qc * (algebraMap ℂ (Matrix X X ℂ) μ - Pc * Mc * Qc) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
        ← Matrix.mul_assoc Qc, ← Matrix.mul_assoc Qc, hQPc, Matrix.one_mul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.mul_assoc Qc, hUN, Matrix.mul_one, hQPc]
  exact ⟨⟨_, _, hV, mul_eq_one_comm.mp hV⟩, rfl⟩

/-- The physical left eigenvector `u = (ℓ, 0) Q` of the critical pair. -/
def physLeft (Q : Matrix (Fin 2 ⊕ Y) X ℝ) : X → ℂ :=
  Sum.elim left 0 ᵥ* Q.map (algebraMap ℝ ℂ)

/-- The physical right eigenvector `r = P (r₀, 0)` of the critical pair. -/
def physRight (P : Matrix X (Fin 2 ⊕ Y) ℝ) : X → ℂ :=
  P.map (algebraMap ℝ ℂ) *ᵥ Sum.elim right 0

omit [Fintype X] [DecidableEq X] [DecidableEq Y] in
@[tmio T, powerlib_foundation] theorem star_real_mulVec (P : Matrix X (Fin 2 ⊕ Y) ℝ)
    (w : Fin 2 ⊕ Y → ℂ) :
    star (P.map (algebraMap ℝ ℂ) *ᵥ w) = P.map (algebraMap ℝ ℂ) *ᵥ star w := by
  funext k
  simp [Matrix.mulVec, dotProduct, star_sum]

omit [DecidableEq X] [DecidableEq Y] in
/-- The pump coefficient is invariant: the critical block of `Q A₁ P` pumps with `g = u A₁ r̄`. -/
@[tmio T, powerlib_foundation] theorem pump_conj (P : Matrix X (Fin 2 ⊕ Y) ℝ)
    (Q : Matrix (Fin 2 ⊕ Y) X ℝ) (A1 : Matrix X X ℂ) :
    Element.pump (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)).toBlocks₁₁ left right =
      physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) := by
  rw [physLeft, physRight, star_real_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  simp [Element.pump, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.toBlocks₁₁,
    Matrix.mul_assoc]

omit [DecidableEq X] [DecidableEq Y] in
/-- The first-order eigenvalue shift: `u A₀' r = a + jb` with `a = shiftRe`, `b = shiftIm` of
`Q A₀' P`. -/
@[tmio T, powerlib_foundation] theorem shift_conj (P : Matrix X (Fin 2 ⊕ Y) ℝ)
    (Q : Matrix (Fin 2 ⊕ Y) X ℝ) (A0' : Matrix X X ℝ) :
    physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P) =
      (shiftRe (Q * A0' * P) : ℂ) + (shiftIm (Q * A0' * P) : ℂ) * I := by
  rw [physLeft, physRight, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.map_mul, ← Matrix.map_mul]
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, shiftRe, shiftIm, Matrix.toBlocks₁₁,
    left, right, Fin.sum_univ_two]
  ring_nf
  simp [I_sq]
  ring

omit [DecidableEq Y] in
/-- In modal coordinates the physical system is `fullB 0 0` with `A = Q A₁ P`, `B = Q A₀' P`. -/
@[tmio T, powerlib_foundation] theorem physJ_eq {ω : ℝ} {P : Matrix X (Fin 2 ⊕ Y) ℝ}
    {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) {A0c : Matrix X X ℝ} {As : Matrix Y Y ℝ}
    (hA0 : Q * A0c * P = fromBlocks (base 0 (ω / 2)) 0 0 As) (A0' : Matrix X X ℝ)
    (A1 : Matrix X X ℂ) (ε t : ℝ) :
    physJ A0c A0' A1 ω ε t = P * fullB 0 0 ω As
      (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P) ε t * Q := by
  have hc : ∀ M : Matrix X X ℝ, P * (Q * M * P) * Q = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_assoc, hPQ,
      Matrix.mul_one]
  have hb : base (ε * 0) (ω / 2 - ε * 0) = base 0 (ω / 2) := by simp
  rw [fullB, fullN, hb, ← hA0, ← modX_conj, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hc, hc, hc,
    physJ, smul_add]
  abel

/-- First-order averaging in physical coordinates, stability. The critical state matrix `A₀c`
has the pair `±jω/2` and a stable remainder `A_s` in real modal coordinates `P`, `Q = P⁻¹`
(`Q A₀c P = diag(base(0, ω/2), A_s)`); `u = (ℓ, 0) Q`, `r = P (r₀, 0)` are the eigenvectors
(`u r = 1`). With the first-order eigenvalue shift `λ₁ = u A₀' r` (so `σ = −ε Re λ₁`,
`ω/2 − Ω = −ε Im λ₁`) and the pump `g = u A₁ r̄`: if `Re λ₁ < 0` and `|g/2| < |λ₁|`, every Floquet
multiplier of `A₀c + ε(A₀' + Re{A₁ e^{jωt}})` lies inside the unit circle for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem physical_stable {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) {A0c : Matrix X X ℝ} (As : Matrix Y Y ℝ)
    (hA0 : Q * A0c * P = fromBlocks (base 0 (ω / 2)) 0 0 As) (A0' : Matrix X X ℝ)
    (A1 : Matrix X X ℂ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
      (Periodic.monodromy (physJ A0c A0' A1 ω ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ v =
        μ • v → ‖μ‖ < 1 := by
  have hshift := shift_conj P Q A0'
  have hpump := pump_conj P Q A1
  have hn : ‖(shiftRe (Q * A0' * P) : ℂ) + (shiftIm (Q * A0' * P) : ℂ) * I‖ ^ 2 =
      shiftRe (Q * A0' * P) ^ 2 + shiftIm (Q * A0' * P) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [hshift] at hs hg
  rw [hn] at hg
  rw [← hpump] at hg
  have hs' : 0 < 0 - shiftRe (Q * A0' * P) := by simp at hs; linarith
  have hg' : ‖Element.pump (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)).toBlocks₁₁
      left right / 2‖ ^ 2 < (0 - shiftRe (Q * A0' * P)) ^ 2 + (0 - shiftIm (Q * A0' * P)) ^ 2 := by
    simpa using hg
  have h := averagingB_stable hω As _ _ hs' hg' hρ
  have hT : 0 ≤ 2 * Real.pi / ω := by positivity
  filter_upwards [h] with ε hε
  intro μ v hv hμ
  have hfun : physJ A0c A0' A1 ω ε = fun t => P * fullB 0 0 ω As
      (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P) ε t * Q :=
    funext fun t => physJ_eq hPQ hA0 A0' A1 ε t
  rw [hfun, Periodic.monodromy, zero_add, transition_conj (continuous_fullB _ _ _ _ _ _ _) hPQ hQP hT]
    at hμ
  obtain ⟨hw, hw'⟩ := eig_conj hPQ hQP hv hμ
  exact hε μ _ hw (by rw [Periodic.monodromy, zero_add]; exact hw')

/-- First-order averaging in physical coordinates, parametric instability: with
`|λ₁| < |g/2|` (`λ₁ = u A₀' r`, `g = u A₁ r̄`) the physical system is Floquet unstable for all
small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem physical_unstable {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) {A0c : Matrix X X ℝ} (As : Matrix Y Y ℝ)
    (hA0 : Q * A0c * P = fromBlocks (base 0 (ω / 2)) 0 0 As) (A0' : Matrix X X ℝ)
    (A1 : Matrix X X ℂ)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Periodic.FloquetUnstable (physJ A0c A0' A1 ω ε) (2 * Real.pi / ω) := by
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
  have h := averagingB_unstable hω As _ _ hg' hρ
  have hT : 0 ≤ 2 * Real.pi / ω := by positivity
  filter_upwards [h] with ε hε
  obtain ⟨ρ, hρ, hn1⟩ := hε
  refine ⟨ρ, ?_, hn1⟩
  have hfun : physJ A0c A0' A1 ω ε = fun t => P * fullB 0 0 ω As
      (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P) ε t * Q :=
    funext fun t => physJ_eq hPQ hA0 A0' A1 ε t
  rw [hfun, Periodic.monodromy, zero_add, transition_conj (continuous_fullB _ _ _ _ _ _ _) hPQ hQP hT]
  rw [Periodic.monodromy, zero_add] at hρ
  exact spectrum_conj hQP hρ

end Physical

/-! ### Three-state cores: modal coordinates from the eigenvectors -/

section Three

/-- Real and imaginary parts of a right eigenvector of `jΩ`: `A x = −Ω y`, `A y = Ω x`. -/
@[tmio T, powerlib_foundation] theorem real_right_eig {A : Matrix (Fin 3) (Fin 3) ℝ} {r : Fin 3 → ℂ}
    {Ω : ℝ} (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r) :
    A *ᵥ (fun k => (r k).re) = -Ω • (fun k => (r k).im) ∧
      A *ᵥ (fun k => (r k).im) = Ω • (fun k => (r k).re) := by
  constructor <;> funext i <;> have h := congrFun hr i
  · have h1 := congrArg Complex.re h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; linarith
  · have h1 := congrArg Complex.im h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; linarith

/-- Real and imaginary parts of a left eigenvector of `jΩ`: `p A = −Ω q`, `q A = Ω p`. -/
@[tmio T, powerlib_foundation] theorem real_left_eig {A : Matrix (Fin 3) (Fin 3) ℝ} {u : Fin 3 → ℂ}
    {Ω : ℝ} (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) :
    (fun k => (u k).re) ᵥ* A = -Ω • (fun k => (u k).im) ∧
      (fun k => (u k).im) ᵥ* A = Ω • (fun k => (u k).re) := by
  constructor <;> funext i <;> have h := congrFun hu i
  · have h1 := congrArg Complex.re h
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three] at h1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]; linarith
  · have h1 := congrArg Complex.im h
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three] at h1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]; linarith

/-- `P = [Re r, −Im r, r₃]`. -/
def modalP (r : Fin 3 → ℂ) (r3 : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 2 ⊕ Fin 1) ℝ :=
  Matrix.of fun i j => Sum.elim ![(r i).re, -(r i).im] (fun _ => r3 i) j

/-- `Q = [2 Re u; 2 Im u; u₃]`. -/
def modalQ (u : Fin 3 → ℂ) (u3 : Fin 3 → ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 3) ℝ :=
  Matrix.of fun i j => Sum.elim ![2 * (u j).re, 2 * (u j).im] (fun _ => u3 j) i

/-- The modal coordinates of a three-state core with the pair `±jΩ` (right/left eigenvectors
`r`, `u`, `u r = 1`) and a real pole `λ₃` (eigenvectors `r₃`, `u₃`, `u₃ r₃ = 1`):
`Q P = I`, `P Q = I`, `Q A P = diag(base(0, Ω), λ₃)`, `(ℓ, 0) Q = u`, `P (r₀, 0) = r`.
The biorthogonality `u r̄ = u r₃ = u₃ r = 0` follows from the eigenvalue equations. -/
@[tmio T, powerlib_foundation] theorem modal_three {A : Matrix (Fin 3) (Fin 3) ℝ} {Ω l3 : ℝ}
    (hΩ : Ω ≠ 0) {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : A *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* A = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1) :
    modalQ u u3 * modalP r r3 = 1 ∧ modalP r r3 * modalQ u u3 = 1 ∧
      modalQ u u3 * A * modalP r r3 = fromBlocks (base 0 Ω) 0 0 !![l3] ∧
      physLeft (modalQ u u3) = u ∧ physRight (modalP r r3) = r := by
  obtain ⟨hx, hy⟩ := real_right_eig hr
  obtain ⟨hp, hq⟩ := real_left_eig hu
  set x : Fin 3 → ℝ := fun k => (r k).re with hxd
  set y : Fin 3 → ℝ := fun k => (r k).im with hyd
  set p : Fin 3 → ℝ := fun k => (u k).re with hpd
  set q : Fin 3 → ℝ := fun k => (u k).im with hqd
  have hre : p ⬝ᵥ x - q ⬝ᵥ y = 1 := by
    have h := congrArg Complex.re hur
    simp [dotProduct, Fin.sum_univ_three] at h
    simp [hxd, hyd, hpd, hqd, dotProduct, Fin.sum_univ_three]; linarith
  have him : p ⬝ᵥ y + q ⬝ᵥ x = 0 := by
    have h := congrArg Complex.im hur
    simp [dotProduct, Fin.sum_univ_three] at h
    simp [hxd, hyd, hpd, hqd, dotProduct, Fin.sum_univ_three]; linarith
  -- the eigenvalue equations evaluated two ways
  have e1 : -Ω * (q ⬝ᵥ x) = -Ω * (p ⬝ᵥ y) := by
    have h := Matrix.dotProduct_mulVec p A x
    rw [hx, hp, dotProduct_smul, smul_dotProduct] at h
    simpa [smul_eq_mul] using h.symm
  have e2 : -Ω * (q ⬝ᵥ y) = Ω * (p ⬝ᵥ x) := by
    have h := Matrix.dotProduct_mulVec p A y
    rw [hy, hp, dotProduct_smul, smul_dotProduct] at h
    simpa [smul_eq_mul] using h.symm
  have hqx : q ⬝ᵥ x = p ⬝ᵥ y := mul_left_cancel₀ (neg_ne_zero.2 hΩ) e1
  have hpx2 : p ⬝ᵥ x = -(q ⬝ᵥ y) := by
    have := mul_left_cancel₀ hΩ (show Ω * (p ⬝ᵥ x) = Ω * (-(q ⬝ᵥ y)) by linarith)
    exact this
  have hpx : p ⬝ᵥ x = 1 / 2 := by linarith
  have hqy : q ⬝ᵥ y = -(1 / 2) := by linarith
  have hpy : p ⬝ᵥ y = 0 := by linarith
  have hqx0 : q ⬝ᵥ x = 0 := by linarith
  -- the third pole
  have f1 : l3 * (p ⬝ᵥ r3) = -Ω * (q ⬝ᵥ r3) := by
    have h := Matrix.dotProduct_mulVec p A r3
    rw [hr3, hp, dotProduct_smul, smul_dotProduct] at h
    simpa [smul_eq_mul] using h
  have f2 : l3 * (q ⬝ᵥ r3) = Ω * (p ⬝ᵥ r3) := by
    have h := Matrix.dotProduct_mulVec q A r3
    rw [hr3, hq, dotProduct_smul, smul_dotProduct] at h
    simpa [smul_eq_mul] using h
  have g1 : l3 * (u3 ⬝ᵥ x) = -Ω * (u3 ⬝ᵥ y) := by
    have h := Matrix.dotProduct_mulVec u3 A x
    rw [hx, hu3, dotProduct_smul, smul_dotProduct] at h
    simpa [smul_eq_mul] using h.symm
  have g2 : l3 * (u3 ⬝ᵥ y) = Ω * (u3 ⬝ᵥ x) := by
    have h := Matrix.dotProduct_mulVec u3 A y
    rw [hy, hu3, dotProduct_smul, smul_dotProduct] at h
    simpa [smul_eq_mul] using h.symm
  have hpos : 0 < l3 ^ 2 + Ω ^ 2 := by positivity
  have hpr3 : p ⬝ᵥ r3 = 0 := by
    have : (p ⬝ᵥ r3) * (l3 ^ 2 + Ω ^ 2) = 0 := by linear_combination l3 * f1 - Ω * f2
    exact (mul_eq_zero.1 this).resolve_right hpos.ne'
  have hqr3 : q ⬝ᵥ r3 = 0 := by
    have : (q ⬝ᵥ r3) * (l3 ^ 2 + Ω ^ 2) = 0 := by linear_combination l3 * f2 + Ω * f1
    exact (mul_eq_zero.1 this).resolve_right hpos.ne'
  have hu3x : u3 ⬝ᵥ x = 0 := by
    have : (u3 ⬝ᵥ x) * (l3 ^ 2 + Ω ^ 2) = 0 := by linear_combination l3 * g1 - Ω * g2
    exact (mul_eq_zero.1 this).resolve_right hpos.ne'
  have hu3y : u3 ⬝ᵥ y = 0 := by
    have : (u3 ⬝ᵥ y) * (l3 ^ 2 + Ω ^ 2) = 0 := by linear_combination l3 * g2 + Ω * g1
    exact (mul_eq_zero.1 this).resolve_right hpos.ne'
  have hQP : modalQ u u3 * modalP r r3 = 1 := by
    simp only [dotProduct, Fin.sum_univ_three] at hpx hqy hpy hqx0 hpr3 hqr3 hu3x hu3y hur3
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [modalQ, modalP, Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [hxd, hyd, hpd, hqd] at hpx hqy hpy hqx0 hpr3 hqr3 hu3x hu3y <;> linarith
  have hPQ : modalP r r3 * modalQ u u3 = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv)).1 hQP
  have hAP : A * modalP r r3 = modalP r r3 * fromBlocks (base 0 Ω) 0 0 !![l3] := by
    ext i j
    have hxi := congrFun hx i
    have hyi := congrFun hy i
    have hri := congrFun hr3 i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] at hxi hyi hri
    rcases j with j | j <;> fin_cases j <;>
      simp [modalP, Matrix.mul_apply, Fin.sum_univ_three, base, fromBlocks, hxd, hyd] at hxi hyi hri ⊢ <;>
      linarith
  refine ⟨hQP, hPQ, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  · funext k
    simp [physLeft, modalQ, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, left]
    apply Complex.ext <;> simp
  · funext k
    simp [physRight, modalP, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, right]

/-- The stable block of a real pole contracts over one period: `‖e^{Tλ₃}‖ = e^{λ₃ T}`. -/
@[tmio T, powerlib_foundation] theorem norm_expS_one (l3 T : ℝ) :
    ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) T‖ = Real.exp (T * l3) := by
  have hd : (T • !![l3] : Matrix (Fin 1) (Fin 1) ℝ) = diagonal fun _ => T * l3 := by
    ext i j; fin_cases i; fin_cases j; simp
  have he : (NormedSpace.exp fun _ : Fin 1 => T * l3) = fun _ => Real.exp (T * l3) := by
    funext i; rw [Pi.exp_def, Real.exp_eq_exp_ℝ]
  rw [expS, hd, Matrix.exp_diagonal, Matrix.linfty_opNorm_diagonal, he, pi_norm_const,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Three-state cores, stability: a core with the pair `±jΩ` (eigenvectors `r`, `u`, `u r = 1`)
and a real pole `λ₃ < 0` (eigenvectors `r₃`, `u₃`, `u₃ r₃ = 1`), driven at `ω = 2Ω`. With
`λ₁ = u A₀' r` and `g = u A₁ r̄`: `Re λ₁ < 0`, `|g/2| < |λ₁|` give all Floquet multipliers of
`A₀c + ε(A₀' + Re{A₁ e^{2jΩt}})` inside the unit circle for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem three_stable {Ω l3 : ℝ} (hΩ : 0 < Ω) (hl3 : l3 < 0)
    {A0c : Matrix (Fin 3) (Fin 3) ℝ} {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : A0c.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A0c.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : A0c *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* A0c = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (A1 : Matrix (Fin 3) (Fin 3) ℂ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ (A1 *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
      (Periodic.monodromy (physJ A0c A0' A1 (2 * Ω) ε) (2 * Real.pi / (2 * Ω)) 0).map
          (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨hQP, hPQ, hQAP, hL, hR⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * A0c * modalP r r3 = fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact physical_stable hω hPQ hQP _ hA0 A0' A1 (by rw [hL, hR]; exact hs)
    (by rw [hL, hR]; exact hg) (spectralRadius_lt_one_of_norm _ hq)

/-- Three-state cores, parametric instability: `|λ₁| < |g/2|` gives Floquet instability for all
small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem three_unstable {Ω l3 : ℝ} (hΩ : 0 < Ω) (hl3 : l3 < 0)
    {A0c : Matrix (Fin 3) (Fin 3) ℝ} {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : A0c.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A0c.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : A0c *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* A0c = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (A1 : Matrix (Fin 3) (Fin 3) ℂ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖u ⬝ᵥ (A1 *ᵥ star r) / 2‖ ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Periodic.FloquetUnstable (physJ A0c A0' A1 (2 * Ω) ε) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hQP, hPQ, hQAP, hL, hR⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * A0c * modalP r r3 = fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact physical_unstable hω hPQ hQP _ hA0 A0' A1 (by rw [hL, hR]; exact hg) (spectralRadius_lt_one_of_norm _ hq)

end Three

end powerlib.ParametricResonance.BlockAveraging
