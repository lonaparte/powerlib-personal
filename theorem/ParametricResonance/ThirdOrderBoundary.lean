import theorem.ParametricResonance.ZeroDampingBranch

/-! # The 2:1 boundary at third order

TITLE-PLACEHOLDER
-/

noncomputable section
namespace powerlib.ParametricResonance.ThirdOrder

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator Interval
open Boundary (secondTerm mixedDet)

/-! ## The third-order expansion of the monodromy -/

section Expansion

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The third Picard term over `[0, t]`: `∫₀ᵗ A(r) N₂(r) dr`, `N₂(r) = ∫₀ʳ A(r') ∫₀^{r'} A` the
second Picard term over `[0, r]` (`Boundary.secondTerm`). -/
def thirdTerm (A : ℝ → Matrix X X ℝ) (t : ℝ) : Matrix X X ℝ :=
  ∫ r in (0 : ℝ)..t, A r * secondTerm A r

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem continuous_secondTerm {A : ℝ → Matrix X X ℝ}
    (hA : Continuous A) : Continuous (secondTerm A) := by
  have hprim : Continuous (fun r => ∫ u in (0 : ℝ)..r, A u) :=
    intervalIntegral.continuous_primitive (fun a b => hA.intervalIntegrable a b) 0
  exact intervalIntegral.continuous_primitive (fun a b => (hA.mul hprim).intervalIntegrable a b) 0

/-- `‖Φ(t, 0) − I − ∫₀ᵗ A − N₂(t) − N₃(t)‖ ≤ (Mt)⁴ ‖I‖ e^{Mt}`. -/
@[tmio T, powerlib_foundation] theorem norm_transition_sub_third_le {A : ℝ → Matrix X X ℝ}
    {M : ℝ} (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) (hM0 : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ‖Periodic.transition A t 0 - 1 - (∫ r in (0 : ℝ)..t, A r) - secondTerm A t - thirdTerm A t‖ ≤
      M * t * (M * t * (M * t * (M * t * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * t))))) := by
  have hprim : Continuous (fun r => ∫ u in (0 : ℝ)..r, A u) :=
    intervalIntegral.continuous_primitive (fun a b => hA.intervalIntegrable a b) 0
  have hsec : Continuous (secondTerm A) := continuous_secondTerm hA
  have hc1 : Continuous (fun r => A r * Periodic.transition A r 0) :=
    hA.mul (Averaging.continuous_transition hA)
  have hc2 : Continuous (fun r => A r * ∫ u in (0 : ℝ)..r, A u) := hA.mul hprim
  have hc3 : Continuous (fun r => A r * secondTerm A r) := hA.mul hsec
  have e : Periodic.transition A t 0 - 1 - (∫ r in (0 : ℝ)..t, A r) - secondTerm A t -
      thirdTerm A t = ∫ r in (0 : ℝ)..t,
        A r * (Periodic.transition A r 0 - 1 - (∫ u in (0 : ℝ)..r, A u) - secondTerm A r) := by
    have hpt : ∀ r, A r * (Periodic.transition A r 0 - 1 - (∫ u in (0 : ℝ)..r, A u) -
        secondTerm A r) = A r * Periodic.transition A r 0 - A r -
          A r * (∫ u in (0 : ℝ)..r, A u) - A r * secondTerm A r := fun r => by
      rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one]
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub (f := fun r => A r * Periodic.transition A r 0 - A r -
        A r * ∫ u in (0 : ℝ)..r, A u) (g := fun r => A r * secondTerm A r)
        (((hc1.sub hA).sub hc2).intervalIntegrable 0 t) (hc3.intervalIntegrable 0 t),
      intervalIntegral.integral_sub (f := fun r => A r * Periodic.transition A r 0 - A r)
        (g := fun r => A r * ∫ u in (0 : ℝ)..r, A u)
        ((hc1.sub hA).intervalIntegrable 0 t) (hc2.intervalIntegrable 0 t),
      intervalIntegral.integral_sub (hc1.intervalIntegrable 0 t) (hA.intervalIntegrable 0 t),
      Averaging.transition_eq_integral hA t, thirdTerm, secondTerm]
    abel
  rw [e]
  have hb : ∀ r ∈ Ι (0 : ℝ) t,
      ‖A r * (Periodic.transition A r 0 - 1 - (∫ u in (0 : ℝ)..r, A u) - secondTerm A r)‖ ≤
        M * (M * t * (M * t * (M * t * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * t))))) := by
    intro r hr
    rw [Set.uIoc_of_le ht] at hr
    refine (norm_mul_le _ _).trans (mul_le_mul (hM r) ?_ (norm_nonneg _) hM0)
    refine (Boundary.norm_transition_sub_second_le hA hM hM0 hr.1.le).trans ?_
    have h1 : 0 ≤ ‖(1 : Matrix X X ℝ)‖ := norm_nonneg _
    have hrt : r ≤ t := hr.2
    have : Real.exp (M * r) ≤ Real.exp (M * t) := Real.exp_le_exp.2 (by nlinarith)
    have : M * r ≤ M * t := by nlinarith
    have : 0 ≤ M * r := mul_nonneg hM0 hr.1.le
    gcongr
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht] at this
  linarith [this]

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] private theorem secondTerm_smul (F : ℝ → Matrix X X ℝ)
    (ε r : ℝ) : secondTerm (fun t => ε • F t) r = ε ^ 2 • secondTerm F r := by
  unfold secondTerm
  have : ∀ r : ℝ, (ε • F r) * ∫ u in (0 : ℝ)..r, ε • F u =
      (ε ^ 2) • (F r * ∫ u in (0 : ℝ)..r, F u) := fun r => by
    rw [intervalIntegral.integral_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
  simp_rw [this]
  rw [intervalIntegral.integral_smul]

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] private theorem thirdTerm_smul (F : ℝ → Matrix X X ℝ)
    (ε t : ℝ) : thirdTerm (fun t => ε • F t) t = ε ^ 3 • thirdTerm F t := by
  unfold thirdTerm
  have : ∀ r : ℝ, (ε • F r) * secondTerm (fun t => ε • F t) r =
      (ε ^ 3) • (F r * secondTerm F r) := fun r => by
    rw [secondTerm_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ring_nf
  simp_rw [this]
  rw [intervalIntegral.integral_smul]

/-- **The third-order expansion of the monodromy of `ẏ = εF(t) y`:**
`Φ_ε(T) = I + εT F̄ + ε² N₂ + ε³ N₃ + R_ε`, `N₂ = secondTerm F T`, `N₃ = thirdTerm F T`, with
`‖R_ε‖ ≤ ε⁴ (MT)⁴ ‖I‖ e^{MT}` for `0 ≤ ε ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem monodromy_expansion_three {F : ℝ → Matrix X X ℝ}
    {M T ε : ℝ} (hF : Continuous F) (hM : ∀ t, ‖F t‖ ≤ M) (hM0 : 0 ≤ M) (hT : 0 ≤ T)
    {Fbar : Matrix X X ℝ} (havg : ∫ r in (0 : ℝ)..T, F r = T • Fbar) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    ‖Periodic.monodromy (fun t => ε • F t) T 0 - 1 - (ε * T) • Fbar - ε ^ 2 • secondTerm F T -
        ε ^ 3 • thirdTerm F T‖ ≤
      ε ^ 4 * (M * T * (M * T * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ *
        Real.exp (M * T)))))) := by
  have hA : Continuous (fun t => ε • F t) := hF.const_smul ε
  have hMε : ∀ t, ‖ε • F t‖ ≤ ε * M := fun t => by
    rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left (hM t) hε
  have h := norm_transition_sub_third_le hA hMε (mul_nonneg hε hM0) hT
  rw [intervalIntegral.integral_smul, havg, smul_smul, secondTerm_smul, thirdTerm_smul] at h
  rw [Periodic.monodromy, zero_add]
  refine h.trans ?_
  have hexp : Real.exp (ε * M * T) ≤ Real.exp (M * T) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg hM0 hT])
  have h1 : 0 ≤ ‖(1 : Matrix X X ℝ)‖ := norm_nonneg _
  have hMT : 0 ≤ M * T := mul_nonneg hM0 hT
  calc ε * M * T * (ε * M * T * (ε * M * T * (ε * M * T * (‖(1 : Matrix X X ℝ)‖ *
        Real.exp (ε * M * T)))))
      = ε ^ 4 * (M * T * (M * T * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ *
          Real.exp (ε * M * T)))))) := by ring
    _ ≤ ε ^ 4 * (M * T * (M * T * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ *
          Real.exp (M * T)))))) := by gcongr

end Expansion

/-! ## Two-state algebra at fourth order -/

section Algebra

@[tmio T, powerlib_foundation] private theorem abs_det_le₂ (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |Z.det| ≤ 2 * ‖Z‖ ^ 2 := by
  rw [Matrix.det_fin_two]
  have h : ∀ i j k l, |Z i j * Z k l| ≤ ‖Z‖ ^ 2 := fun i j k l => by
    rw [abs_mul, sq]
    exact mul_le_mul (Averaging.entry_le_norm Z i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  calc |Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0| ≤ |Z 0 0 * Z 1 1| + |Z 0 1 * Z 1 0| := abs_sub _ _
    _ ≤ 2 * ‖Z‖ ^ 2 := by linarith [h 0 0 1 1, h 0 1 1 0]

@[tmio T, powerlib_foundation] private theorem abs_trace_le₂ (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |Z.trace| ≤ 2 * ‖Z‖ := by
  rw [Matrix.trace_fin_two]
  have h0 := Averaging.entry_le_norm Z 0 0
  have h1 := Averaging.entry_le_norm Z 1 1
  calc |Z 0 0 + Z 1 1| ≤ |Z 0 0| + |Z 1 1| := abs_add_le _ _
    _ ≤ 2 * ‖Z‖ := by linarith

@[tmio T, powerlib_foundation] private theorem abs_mixedDet_le₂ (M Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |mixedDet M Z| ≤ 4 * (‖M‖ * ‖Z‖) := by
  have e : mixedDet M Z = M 0 0 * Z 1 1 + M 1 1 * Z 0 0 - M 0 1 * Z 1 0 - M 1 0 * Z 0 1 := by
    simp [mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h : ∀ i j k l, |M i j * Z k l| ≤ ‖M‖ * ‖Z‖ := fun i j k l => by
    rw [abs_mul]
    exact mul_le_mul (Averaging.entry_le_norm M i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  rw [e]
  have a1 := abs_le.mp (h 0 0 1 1)
  have a2 := abs_le.mp (h 1 1 0 0)
  have a3 := abs_le.mp (h 0 1 1 0)
  have a4 := abs_le.mp (h 1 0 0 1)
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

@[tmio T, powerlib_foundation] private theorem mixedDet_one_left₂ (N : Matrix (Fin 2) (Fin 2) ℝ) :
    mixedDet 1 N = N.trace := by
  simp [mixedDet, Matrix.trace_fin_two]; ring

/-- **The trace of a conservative monodromy near `−I`.** For a real `2 × 2` matrix
`Φ = −(I + Y)` with `det Φ = 1`: `tr Φ + 2 = det Y` exactly. -/
@[tmio T, powerlib_foundation] theorem trace_neg_add_two {Y : Matrix (Fin 2) (Fin 2) ℝ}
    (h : (-(1 + Y)).det = 1) : (-(1 + Y)).trace + 2 = Y.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two] at h ⊢
  linarith

/-- **The determinant of `Y = εT M + ε² N₂ + ε³ N₃ + R` to fourth order:**
`det Y = ε² T² det M + ε³ T mixedDet(M, N₂) + ε⁴ (det N₂ + T mixedDet(M, N₃)) + O(ε⁵)`, with the
explicit constant `2(‖N₃‖ + C)² + 4‖N₂‖(‖N₃‖ + C) + 4T‖M‖C` for `‖R‖ ≤ Cε⁴`, `0 ≤ ε ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem det_expansion_four {M N₂ N₃ R : Matrix (Fin 2) (Fin 2) ℝ}
    {T C ε : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hR : ‖R‖ ≤ C * ε ^ 4) :
    |((ε * T) • M + ε ^ 2 • N₂ + ε ^ 3 • N₃ + R).det -
        (T ^ 2 * M.det * ε ^ 2 + T * mixedDet M N₂ * ε ^ 3 +
          (N₂.det + T * mixedDet M N₃) * ε ^ 4)| ≤
      (2 * (‖N₃‖ + C) ^ 2 + 4 * ‖N₂‖ * (‖N₃‖ + C) + 4 * T * ‖M‖ * C) * ε ^ 5 := by
  set W := ε ^ 3 • N₃ + R with hW
  have e : ((ε * T) • M + ε ^ 2 • N₂ + ε ^ 3 • N₃ + R).det -
      (T ^ 2 * M.det * ε ^ 2 + T * mixedDet M N₂ * ε ^ 3 + (N₂.det + T * mixedDet M N₃) * ε ^ 4) =
      W.det + ε ^ 2 * mixedDet N₂ W + ε * T * mixedDet M R := by
    simp only [hW, Matrix.det_fin_two, mixedDet, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e]
  have hε4 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one hε hε1 (by norm_num)
  have hWb : ‖W‖ ≤ (‖N₃‖ + C) * ε ^ 3 := by
    calc ‖W‖ ≤ ‖ε ^ 3 • N₃‖ + ‖R‖ := norm_add_le _ _
      _ = ε ^ 3 * ‖N₃‖ + ‖R‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ ε ^ 3 * ‖N₃‖ + C * ε ^ 3 := by
          gcongr; exact hR.trans (mul_le_mul_of_nonneg_left hε4 hC)
      _ = (‖N₃‖ + C) * ε ^ 3 := by ring
  have hε65 : ε ^ 6 ≤ ε ^ 5 := pow_le_pow_of_le_one hε hε1 (by norm_num)
  have h1 : |W.det| ≤ 2 * (‖N₃‖ + C) ^ 2 * ε ^ 5 := by
    calc |W.det| ≤ 2 * ‖W‖ ^ 2 := abs_det_le₂ W
      _ ≤ 2 * ((‖N₃‖ + C) * ε ^ 3) ^ 2 := by gcongr
      _ = 2 * (‖N₃‖ + C) ^ 2 * ε ^ 6 := by ring
      _ ≤ 2 * (‖N₃‖ + C) ^ 2 * ε ^ 5 := by gcongr
  have h2 : |ε ^ 2 * mixedDet N₂ W| ≤ 4 * ‖N₂‖ * (‖N₃‖ + C) * ε ^ 5 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
    calc ε ^ 2 * |mixedDet N₂ W| ≤ ε ^ 2 * (4 * (‖N₂‖ * ((‖N₃‖ + C) * ε ^ 3))) := by
          gcongr; exact (abs_mixedDet_le₂ N₂ W).trans (by gcongr)
      _ = 4 * ‖N₂‖ * (‖N₃‖ + C) * ε ^ 5 := by ring
  have h3 : |ε * T * mixedDet M R| ≤ 4 * T * ‖M‖ * C * ε ^ 5 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε * T)]
    calc ε * T * |mixedDet M R| ≤ ε * T * (4 * (‖M‖ * (C * ε ^ 4))) := by
          gcongr; exact (abs_mixedDet_le₂ M R).trans (by gcongr)
      _ = 4 * T * ‖M‖ * C * ε ^ 5 := by ring
  calc |W.det + ε ^ 2 * mixedDet N₂ W + ε * T * mixedDet M R|
      ≤ |W.det| + |ε ^ 2 * mixedDet N₂ W| + |ε * T * mixedDet M R| := abs_add_three _ _ _
    _ ≤ _ := by linarith

/-- The deviation `Y = P(ε) − I` of a family `P(ε) = I + εT M + ε² N₂ + ε³ N₃ + O(ε⁴)`: its norm
is `O(ε)`, its trace `εT tr M + O(ε²)`, and, on `det M = 0 = mixedDet(M, N₂)`, its determinant
`ε⁴ K + O(ε⁵)`, `K = det N₂ + T mixedDet(M, N₃)`. -/
@[tmio T, powerlib_foundation] private theorem deviation_bounds
    {P : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {M N₂ N₃ : Matrix (Fin 2) (Fin 2) ℝ} {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hP : ∀ ε, 0 < ε → ε ≤ 1 →
      ‖P ε - 1 - (ε * T) • M - ε ^ 2 • N₂ - ε ^ 3 • N₃‖ ≤ C * ε ^ 4)
    (hdet : M.det = 0) (hmix : mixedDet M N₂ = 0) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      ‖P ε - 1‖ ≤ (T * ‖M‖ + ‖N₂‖ + ‖N₃‖ + C) * ε ∧
      |(P ε - 1).trace - T * M.trace * ε| ≤ (2 * (‖N₂‖ + ‖N₃‖ + C)) * ε ^ 2 ∧
      |(P ε - 1).det - (N₂.det + T * mixedDet M N₃) * ε ^ 4| ≤
        (2 * (‖N₃‖ + C) ^ 2 + 4 * ‖N₂‖ * (‖N₃‖ + C) + 4 * T * ‖M‖ * C) * ε ^ 5 := by
  intro ε h0 h1
  set R := P ε - 1 - (ε * T) • M - ε ^ 2 • N₂ - ε ^ 3 • N₃ with hR
  have hRb : ‖R‖ ≤ C * ε ^ 4 := hP ε h0 h1
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
  have hε4 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
  have hY : P ε - 1 = (ε * T) • M + ε ^ 2 • N₂ + ε ^ 3 • N₃ + R := by rw [hR]; abel
  have hn2 : ‖ε ^ 2 • N₂‖ = ε ^ 2 * ‖N₂‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hn3 : ‖ε ^ 3 • N₃‖ = ε ^ 3 * ‖N₃‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hY]
    calc ‖(ε * T) • M + ε ^ 2 • N₂ + ε ^ 3 • N₃ + R‖
        ≤ ‖(ε * T) • M‖ + ‖ε ^ 2 • N₂‖ + ‖ε ^ 3 • N₃‖ + ‖R‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ε * T * ‖M‖ + ε ^ 2 * ‖N₂‖ + ε ^ 3 * ‖N₃‖ + ‖R‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity), hn2, hn3]
      _ ≤ ε * T * ‖M‖ + ε * ‖N₂‖ + ε * ‖N₃‖ + C * ε := by
          gcongr
          · exact hε3.trans hε2
          · exact hRb.trans (mul_le_mul_of_nonneg_left ((hε4.trans hε3).trans hε2) hC)
      _ = (T * ‖M‖ + ‖N₂‖ + ‖N₃‖ + C) * ε := by ring
  · rw [hY, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    have e : ε * T * M.trace + ε ^ 2 * N₂.trace + ε ^ 3 * N₃.trace + R.trace - T * M.trace * ε =
        ε ^ 2 * N₂.trace + ε ^ 3 * N₃.trace + R.trace := by ring
    rw [e]
    have t2 := abs_trace_le₂ N₂
    have t3 := abs_trace_le₂ N₃
    have tR := abs_trace_le₂ R
    calc |ε ^ 2 * N₂.trace + ε ^ 3 * N₃.trace + R.trace|
        ≤ |ε ^ 2 * N₂.trace| + |ε ^ 3 * N₃.trace| + |R.trace| := abs_add_three _ _ _
      _ = ε ^ 2 * |N₂.trace| + ε ^ 3 * |N₃.trace| + |R.trace| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 3)]
      _ ≤ ε ^ 2 * (2 * ‖N₂‖) + ε ^ 2 * (2 * ‖N₃‖) + 2 * (C * ε ^ 2) := by
          have hRt : |R.trace| ≤ 2 * (C * ε ^ 2) := tR.trans (by
            gcongr; exact hRb.trans (mul_le_mul_of_nonneg_left (hε4.trans hε3) hC))
          have h3' : ε ^ 3 * |N₃.trace| ≤ ε ^ 2 * (2 * ‖N₃‖) :=
            mul_le_mul hε3 t3 (abs_nonneg _) (by positivity)
          have h2' : ε ^ 2 * |N₂.trace| ≤ ε ^ 2 * (2 * ‖N₂‖) := by gcongr
          linarith
      _ = (2 * (‖N₂‖ + ‖N₃‖ + C)) * ε ^ 2 := by ring
  · have h := det_expansion_four (M := M) (N₂ := N₂) (N₃ := N₃) hT hC h0.le h1 hRb
    rw [hdet, hmix, mul_zero, zero_mul, mul_zero, zero_mul, zero_add, zero_add, ← hY] at h
    exact h

/-- **Conservative Jury conditions at fourth order.** For a family `P(ε) = I + εT M + ε² N₂ +
ε³ N₃ + O(ε⁴)` of real `2 × 2` matrices of determinant one (`T > 0`) with
`det M = 0 = mixedDet(M, N₂)` (the second-order test is void), the fourth-order coefficient
`K = det N₂ + T mixedDet(M, N₃)` of `det(P − I) = 2 − tr P` decides for all small `ε > 0`:
`K > 0` gives `|tr P(ε)| < 2` (elliptic) and `K < 0` gives `tr P(ε) > 2` (hyperbolic). -/
@[tmio T, powerlib_foundation] theorem conservative_jury_three
    {P : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {M N₂ N₃ : Matrix (Fin 2) (Fin 2) ℝ} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hP : ∀ ε, 0 < ε → ε ≤ 1 →
      ‖P ε - 1 - (ε * T) • M - ε ^ 2 • N₂ - ε ^ 3 • N₃‖ ≤ C * ε ^ 4)
    (hdetP : ∀ ε, 0 < ε → ε ≤ 1 → (P ε).det = 1) (hdet : M.det = 0)
    (hmix : mixedDet M N₂ = 0) :
    (0 < N₂.det + T * mixedDet M N₃ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), |(P ε).trace| < 2) ∧
      (N₂.det + T * mixedDet M N₃ < 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 < (P ε).trace) := by
  set K := N₂.det + T * mixedDet M N₃ with hK
  set C₅ := 2 * (‖N₃‖ + C) ^ 2 + 4 * ‖N₂‖ * (‖N₃‖ + C) + 4 * T * ‖M‖ * C with hC₅
  have hC₅0 : 0 ≤ C₅ := by positivity
  have hb := deviation_bounds hT.le hC hP hdet hmix
  -- `tr P − 2 = −det(P − I)` from `det P = 1`
  have htr : ∀ ε, 0 < ε → ε ≤ 1 → 2 - (P ε).trace = (P ε - 1).det := by
    intro ε h0 h1
    have h := Boundary.det_add_fin_two 1 (P ε - 1)
    rw [add_sub_cancel, Matrix.det_one, hdetP ε h0 h1, mixedDet_one_left₂] at h
    have ht : (P ε - 1).trace = (P ε).trace - 2 := by
      rw [Matrix.trace_sub, Matrix.trace_one]; norm_num
    linarith
  -- `tr P + 2 > 0` for small `ε`
  have hlow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (P ε).trace + 2 := by
    refine Averaging.eventually_pos_of_bound (b := 4) (C := |K| + C₅) 0 (by norm_num)
      (by positivity) fun ε h0 h1 => ?_
    obtain ⟨-, -, h3⟩ := hb ε h0 h1
    have e4 : ε ^ 4 ≤ ε := by
      calc ε ^ 4 ≤ ε ^ 1 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
        _ = ε := pow_one ε
    have e5 : ε ^ 5 ≤ ε := by
      calc ε ^ 5 ≤ ε ^ 1 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
        _ = ε := pow_one ε
    have e : (P ε).trace + 2 - 4 * ε ^ 0 =
        -(((P ε - 1).det - K * ε ^ 4) + K * ε ^ 4) := by
      rw [← htr ε h0 h1]; ring
    rw [e, abs_neg, zero_add, pow_one]
    calc |((P ε - 1).det - K * ε ^ 4) + K * ε ^ 4|
        ≤ |(P ε - 1).det - K * ε ^ 4| + |K * ε ^ 4| := abs_add_le _ _
      _ ≤ C₅ * ε + |K| * ε := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 4)]
          exact add_le_add (h3.trans (by gcongr)) (by gcongr)
      _ = (|K| + C₅) * ε := by ring
  refine ⟨fun hKp => ?_, fun hKn => ?_⟩
  · have h := Averaging.eventually_pos_of_bound (h := fun ε => 2 - (P ε).trace) (b := K)
      (C := C₅) 4 hKp hC₅0 fun ε h0 h1 => by
        rw [htr ε h0 h1]; exact (hb ε h0 h1).2.2
    filter_upwards [h, hlow] with ε h1 h2
    rw [abs_lt]; constructor <;> linarith
  · have h := Averaging.eventually_pos_of_bound (h := fun ε => (P ε).trace - 2) (b := -K)
      (C := C₅) 4 (by linarith) hC₅0 fun ε h0 h1 => by
        have e : (P ε).trace - 2 - -K * ε ^ 4 = -((P ε - 1).det - K * ε ^ 4) := by
          rw [← htr ε h0 h1]; ring
        rw [e, abs_neg]; exact (hb ε h0 h1).2.2
    filter_upwards [h] with ε h1
    linarith

/-- **Jury conditions at a simple critical exponent, at third order.** Let
`P(ε) = I + εT M + ε² N₂ + ε³ N₃ + O(ε⁴)` (`T > 0`) with `det M = 0 > tr M` (slow exponents `0`
and `tr M < 0`) and `mixedDet(M, N₂) = 0`, so that `Boundary.critical_jury` is void. Then
`det(I − P(ε)) = ε⁴ K + O(ε⁵)`, `K = det N₂ + T mixedDet(M, N₃)`, decides for all small `ε > 0`:
`K > 0` gives Schur stability and `K < 0` a real eigenvalue `> 1`. -/
@[tmio T, powerlib_foundation] theorem critical_jury_three
    {P : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {M N₂ N₃ : Matrix (Fin 2) (Fin 2) ℝ} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hP : ∀ ε, 0 < ε → ε ≤ 1 →
      ‖P ε - 1 - (ε * T) • M - ε ^ 2 • N₂ - ε ^ 3 • N₃‖ ≤ C * ε ^ 4)
    (hdet : M.det = 0) (htrM : M.trace < 0) (hmix : mixedDet M N₂ = 0) :
    (0 < N₂.det + T * mixedDet M N₃ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), LTI.SchurStable (P ε)) ∧
      (N₂.det + T * mixedDet M N₃ < 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∃ μ ∈ spectrum ℂ ((P ε).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) := by
  set K := N₂.det + T * mixedDet M N₃ with hK
  set C₅ := 2 * (‖N₃‖ + C) ^ 2 + 4 * ‖N₂‖ * (‖N₃‖ + C) + 4 * T * ‖M‖ * C with hC₅
  set L := T * ‖M‖ + ‖N₂‖ + ‖N₃‖ + C with hL
  have hC₅0 : 0 ≤ C₅ := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hb := deviation_bounds hT.le hC hP hdet hmix
  have hdetY : ∀ ε, (1 - P ε).det = (P ε - 1).det := fun ε => by
    rw [show (1 : Matrix (Fin 2) (Fin 2) ℝ) - P ε = -(P ε - 1) by abel, Matrix.det_neg]
    simp
  -- `det P < 1`: `1 − det P = −tr Y − det Y = −T tr M ε + O(ε²)`
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (P ε).det < 1 := by
    have h := Averaging.eventually_pos_of_bound
      (h := fun ε => -(P ε - 1).trace - (P ε - 1).det)
      (b := -(T * M.trace)) (C := 2 * (‖N₂‖ + ‖N₃‖ + C) + 2 * L ^ 2) 1 (by nlinarith)
      (by positivity) fun ε h0 h1 => by
        obtain ⟨hn, ht, -⟩ := hb ε h0 h1
        have hd : |(P ε - 1).det| ≤ 2 * L ^ 2 * ε ^ 2 := by
          calc |(P ε - 1).det| ≤ 2 * ‖P ε - 1‖ ^ 2 := abs_det_le₂ _
            _ ≤ 2 * (L * ε) ^ 2 := by gcongr
            _ = 2 * L ^ 2 * ε ^ 2 := by ring
        have e : -(P ε - 1).trace - (P ε - 1).det - -(T * M.trace) * ε ^ 1 =
            -((P ε - 1).trace - T * M.trace * ε) - (P ε - 1).det := by ring
        rw [e]
        calc |-((P ε - 1).trace - T * M.trace * ε) - (P ε - 1).det| ≤
              |(P ε - 1).trace - T * M.trace * ε| + |(P ε - 1).det| := by
              rw [← abs_neg ((P ε - 1).trace - T * M.trace * ε)]; exact abs_sub _ _
          _ ≤ (2 * (‖N₂‖ + ‖N₃‖ + C)) * ε ^ 2 + 2 * L ^ 2 * ε ^ 2 := add_le_add ht hd
          _ = (2 * (‖N₂‖ + ‖N₃‖ + C) + 2 * L ^ 2) * ε ^ (1 + 1) := by ring
    filter_upwards [h] with ε hε
    have hd := Boundary.det_add_fin_two 1 (P ε - 1)
    rw [add_sub_cancel, Matrix.det_one, mixedDet_one_left₂] at hd
    linarith
  -- `det(I + P) > 0`: `det(2I + Y) = 4 + 2 tr Y + det Y`
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (1 + P ε).det := by
    refine Averaging.eventually_pos_of_bound (h := fun ε => (1 + P ε).det) (b := 4)
      (C := 4 * L + 2 * L ^ 2) 0 (by norm_num) (by positivity) fun ε h0 h1 => ?_
    obtain ⟨hn, -, -⟩ := hb ε h0 h1
    have e : (1 + P ε) = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (P ε - 1) := by
      rw [two_smul]; abel
    have ht : |(P ε - 1).trace| ≤ 2 * (L * ε) := (abs_trace_le₂ _).trans (by gcongr)
    have hd : |(P ε - 1).det| ≤ 2 * L ^ 2 * ε := by
      calc |(P ε - 1).det| ≤ 2 * ‖P ε - 1‖ ^ 2 := abs_det_le₂ _
        _ ≤ 2 * (L * ε) ^ 2 := by gcongr
        _ = 2 * L ^ 2 * ε * ε := by ring
        _ ≤ 2 * L ^ 2 * ε * 1 := by gcongr
        _ = 2 * L ^ 2 * ε := by ring
    rw [e, Averaging.det_smul_one_add, pow_zero, mul_one, zero_add, pow_one]
    have e2 : (2 : ℝ) ^ 2 + 2 * (P ε - 1).trace + (P ε - 1).det - 4 =
        2 * (P ε - 1).trace + (P ε - 1).det := by ring
    rw [e2]
    calc |2 * (P ε - 1).trace + (P ε - 1).det| ≤ |2 * (P ε - 1).trace| + |(P ε - 1).det| :=
          abs_add_le _ _
      _ = 2 * |(P ε - 1).trace| + |(P ε - 1).det| := by rw [abs_mul, abs_two]
      _ ≤ 2 * (2 * (L * ε)) + 2 * L ^ 2 * ε := by gcongr
      _ = (4 * L + 2 * L ^ 2) * ε := by ring
  refine ⟨fun hKp => ?_, fun hKn => ?_⟩
  · have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (P ε - 1).det :=
      Averaging.eventually_pos_of_bound (b := K) (C := C₅) 4 hKp hC₅0
        fun ε h0 h1 => (hb ε h0 h1).2.2
    filter_upwards [e1, e2, e3] with ε h1 h2 h3
    exact Averaging.schurStable_of_jury h1 (by rw [hdetY]; exact h2) h3
  · have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < -(P ε - 1).det :=
      Averaging.eventually_pos_of_bound (h := fun ε => -(P ε - 1).det) (b := -K) (C := C₅) 4
        (by linarith) hC₅0 fun ε h0 h1 => by
          have := (hb ε h0 h1).2.2
          rw [show -(P ε - 1).det - -K * ε ^ 4 = -((P ε - 1).det - K * ε ^ 4) by ring, abs_neg]
          exact this
    filter_upwards [e2] with ε h2
    exact Averaging.exists_eig_gt_of_det_one_sub (by rw [hdetY]; linarith)

end Algebra

/-! ## The third Picard term on the first-order boundary -/

section Reduction

@[tmio T, powerlib_foundation] private theorem mixedDet_add_right₂
    (M N N' : Matrix (Fin 2) (Fin 2) ℝ) : mixedDet M (N + N') = mixedDet M N + mixedDet M N' := by
  simp [mixedDet, Matrix.mul_add, Matrix.trace_add]; ring

@[tmio T, powerlib_foundation] private theorem mixedDet_sub_right₂
    (M N N' : Matrix (Fin 2) (Fin 2) ℝ) : mixedDet M (N - N') = mixedDet M N - mixedDet M N' := by
  simp [mixedDet, Matrix.mul_sub, Matrix.trace_sub]; ring

@[tmio T, powerlib_foundation] private theorem mixedDet_smul_right₂
    (M N : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) : mixedDet M (c • N) = c * mixedDet M N := by
  simp [mixedDet, Matrix.trace_smul]; ring

/-- `mixedDet(M, M X) = det M · tr X = mixedDet(M, X M)` for `2 × 2` matrices (Cayley–Hamilton):
on `det M = 0` every product that starts or ends with `M` drops out of `mixedDet(M, ·)`. -/
@[tmio T, powerlib_foundation] theorem mixedDet_mul_self (M X : Matrix (Fin 2) (Fin 2) ℝ) :
    mixedDet M (M * X) = M.det * X.trace ∧ mixedDet M (X * M) = M.det * X.trace := by
  constructor <;>
    simp [mixedDet, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- `mixedDet(M, ·)` as a continuous linear functional. -/
def mixedDetL (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := mixedDet M
      map_add' := mixedDet_add_right₂ M
      map_smul' := fun c N => by rw [mixedDet_smul_right₂, smul_eq_mul, RingHom.id_apply] }

@[tmio T, powerlib_foundation] private theorem mixedDet_integral (M : Matrix (Fin 2) (Fin 2) ℝ)
    {f : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hf : Continuous f) (T : ℝ) :
    mixedDet M (∫ r in (0 : ℝ)..T, f r) = ∫ r in (0 : ℝ)..T, mixedDet M (f r) := by
  have h := (mixedDetL M).intervalIntegral_comp_comm
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 T)
  exact h.symm

/-- **The third Picard term on the first-order boundary.** For continuous `F` on `ℝ²` with
`∫₀ᵀ F = T M` and `det M = 0`, with the oscillating part of the primitive
`P̃(r) = ∫₀ʳ F − r M`:
`mixedDet(M, N₃) = −mixedDet(M, ∫₀ᵀ P̃(r) F(r) P̃(r) dr)`. Integration by parts gives
`N₃ = T M N₂ − ∫₀ᵀ P F P` (`P = ∫₀ʳ F`), and on `det M = 0` every term that starts or ends with
`M` drops out of `mixedDet(M, ·)` (`mixedDet_mul_self`): the triple integral reduces to a single
integral of the periodic part. -/
@[tmio T, powerlib_foundation] theorem mixedDet_thirdTerm_boundary
    {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hF : Continuous F) {T : ℝ}
    {M : Matrix (Fin 2) (Fin 2) ℝ} (havg : ∫ r in (0 : ℝ)..T, F r = T • M) (hdet : M.det = 0) :
    mixedDet M (thirdTerm F T) = -mixedDet M (∫ r in (0 : ℝ)..T,
      ((∫ u in (0 : ℝ)..r, F u) - r • M) * F r * ((∫ u in (0 : ℝ)..r, F u) - r • M)) := by
  set P : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun r => ∫ u in (0 : ℝ)..r, F u with hPdef
  have hPc : Continuous P :=
    intervalIntegral.continuous_primitive (fun a b => hF.intervalIntegrable a b) 0
  have hPd : ∀ r, HasDerivAt P (F r) r := fun r => (hF.integral_hasStrictDerivAt 0 r).hasDerivAt
  have hN₂d : ∀ r, HasDerivAt (secondTerm F) (F r * P r) r := fun r =>
    ((hF.mul hPc).integral_hasStrictDerivAt 0 r).hasDerivAt
  have hN₂c : Continuous (secondTerm F) := continuous_secondTerm hF
  -- integration by parts: `N₃ = P(T) N₂(T) − ∫ P F P`
  have hG : ∀ r ∈ uIcc (0 : ℝ) T, HasDerivAt (fun r => P r * secondTerm F r)
      (F r * secondTerm F r + P r * (F r * P r)) r := fun r _ => (hPd r).mul (hN₂d r)
  have hparts := intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    (((hF.mul hN₂c).add (hPc.mul (hF.mul hPc))).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_add (f := fun r => F r * secondTerm F r)
    (g := fun r => P r * (F r * P r)) ((hF.mul hN₂c).intervalIntegrable 0 T)
    ((hPc.mul (hF.mul hPc)).intervalIntegrable 0 T)] at hparts
  have hP0 : P 0 = 0 := by simp [hPdef]
  have hPT : P T = T • M := havg
  rw [hP0, Matrix.zero_mul, sub_zero, hPT] at hparts
  have h3 : thirdTerm F T = (T • M) * secondTerm F T - ∫ r in (0 : ℝ)..T, P r * (F r * P r) := by
    rw [thirdTerm, ← hparts]; abel
  -- the terms with `M` at either end drop out
  have hpt : ∀ r, mixedDet M (P r * (F r * P r)) =
      mixedDet M ((P r - r • M) * F r * (P r - r • M)) := fun r => by
    have e : P r * (F r * P r) = (P r - r • M) * F r * (P r - r • M) +
        (r • ((P r - r • M) * F r)) * M + M * (r • (F r * (P r - r • M)) + r ^ 2 • (F r * M)) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add,
        Matrix.mul_assoc, smul_sub, smul_smul]
      rw [sq]
      abel
    rw [e, mixedDet_add_right₂, mixedDet_add_right₂, (mixedDet_mul_self M _).1,
      (mixedDet_mul_self M _).2, hdet, zero_mul, zero_mul, add_zero, add_zero]
  have hc1 : Continuous fun r => P r * (F r * P r) := hPc.mul (hF.mul hPc)
  have hc2 : Continuous fun r => (P r - r • M) * F r * (P r - r • M) :=
    ((hPc.sub (continuous_id.smul continuous_const)).mul hF).mul
      (hPc.sub (continuous_id.smul continuous_const))
  rw [h3, mixedDet_sub_right₂, Matrix.smul_mul, mixedDet_smul_right₂, (mixedDet_mul_self M _).1,
    hdet, zero_mul, mul_zero, zero_sub, mixedDet_integral M hc1, mixedDet_integral M hc2]
  simp_rw [hpt]

end Reduction

/-! ## Exact transition matrices of two special standard forms -/

section Exact

open _root_.powerlib.ParametricResonance.NormalForm (quarter rot)

@[tmio T, powerlib_foundation] private theorem quarter_mul_quarter₂ :
    quarter * quarter = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quarter, Matrix.mul_apply, Fin.sum_univ_two]

@[tmio T, powerlib_foundation] private theorem quarter_mul_rot (θ : ℝ) :
    quarter * rot θ = rot θ * quarter := by
  simp only [rot, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- **A rotation-commuting standard form is solved exactly.** If `A(t) = α(t) I + β(t) J`
(continuous, bounded) with primitives `p' = α`, `q' = β`, `p(0) = q(0) = 0`, then
`Φ(t, 0) = e^{p(t)} R(q(t))` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem transition_rotation_commuting
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hA : Continuous A) (hB : ∀ r, ‖A r‖ ≤ B)
    {α β p q : ℝ → ℝ} (hAeq : ∀ r, A r = α r • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β r • quarter)
    (hp : ∀ r, HasDerivAt p (α r) r) (hq : ∀ r, HasDerivAt q (β r) r) (hp0 : p 0 = 0)
    (hq0 : q 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Periodic.transition A t 0 = Real.exp (p t) • rot (q t) := by
  have hY : IsIntegralCurveOn (fun r => Real.exp (p r) • rot (q r)) (Periodic.matField A)
      (Ici 0) := by
    intro r _
    have hrot : HasDerivAt (fun r => rot (q r)) (β r • (rot (q r) * quarter)) r := by
      have h := ((Real.hasDerivAt_cos (q r)).comp r (hq r)).smul_const
        (1 : Matrix (Fin 2) (Fin 2) ℝ) |>.add
        (((Real.hasDerivAt_sin (q r)).comp r (hq r)).smul_const quarter)
      refine h.congr_deriv ?_
      simp only [rot, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, quarter_mul_quarter₂,
        smul_neg, smul_add, smul_smul]
      module
    have hexp : HasDerivAt (fun r => Real.exp (p r)) (Real.exp (p r) * α r) r :=
      (Real.hasDerivAt_exp (p r)).comp r (hp r)
    have h := hexp.smul hrot
    have key : Real.exp (p r) • (β r • (rot (q r) * quarter)) +
        (Real.exp (p r) * α r) • rot (q r) = Periodic.matField A r (Real.exp (p r) • rot (q r)) := by
      simp only [Periodic.matField, hAeq r, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, quarter_mul_rot, smul_smul]
      module
    rw [key] at h
    exact h.hasDerivWithinAt
  have h := Periodic.transition_unique hA hB hY t ht
  simp only [hp0, hq0, Real.exp_zero, one_smul] at h
  have hr0 : rot 0 = 1 := by simp [rot]
  rw [hr0, Matrix.mul_one] at h
  exact h.symm

/-- **A standard form `κ M + α(t) I` with `M² = τ M` is solved exactly.** If `A(t) = κ M + α(t) I`
(continuous, bounded) with `M * M = τ M`, `p' = α`, `p(0) = 0`, and `f' = κ(1 + τ f)`,
`f(0) = 0`, then `Φ(t, 0) = e^{p(t)} (I + f(t) M)` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem transition_rank_one
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hA : Continuous A) (hB : ∀ r, ‖A r‖ ≤ B)
    {M : Matrix (Fin 2) (Fin 2) ℝ} {τ κ : ℝ} (hMM : M * M = τ • M) {α p f : ℝ → ℝ}
    (hAeq : ∀ r, A r = κ • M + α r • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hp : ∀ r, HasDerivAt p (α r) r) (hf : ∀ r, HasDerivAt f (κ * (1 + τ * f r)) r)
    (hp0 : p 0 = 0) (hf0 : f 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Periodic.transition A t 0 = Real.exp (p t) • (1 + f t • M) := by
  have hY : IsIntegralCurveOn (fun r => Real.exp (p r) • (1 + f r • M)) (Periodic.matField A)
      (Ici 0) := by
    intro r _
    have hexp : HasDerivAt (fun r => Real.exp (p r)) (Real.exp (p r) * α r) r :=
      (Real.hasDerivAt_exp (p r)).comp r (hp r)
    have hfM : HasDerivAt (fun r => 1 + f r • M) ((κ * (1 + τ * f r)) • M) r :=
      ((hf r).smul_const M).const_add 1
    have h := hexp.smul hfM
    have key : Real.exp (p r) • ((κ * (1 + τ * f r)) • M) +
        (Real.exp (p r) * α r) • (1 + f r • M) =
          Periodic.matField A r (Real.exp (p r) • (1 + f r • M)) := by
      simp only [Periodic.matField, hAeq r, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hMM, smul_smul, smul_add]
      module
    rw [key] at h
    exact h.hasDerivWithinAt
  have h := Periodic.transition_unique hA hB hY t ht
  simp only [hp0, hf0, Real.exp_zero, one_smul, zero_smul, add_zero, Matrix.mul_one] at h
  exact h.symm

end Exact

/-! ## The two-state 2:1 system: structure of the standard form -/

section Structure

open TwoToOne (full stdForm left right refl1 refl2)
open SecondOrder (antiPump)
open _root_.powerlib.ParametricResonance.NormalForm (quarter rot)

/-- The rotational fundamental coefficient `b = (a₁₀ − a₀₁)/2` of a modulation matrix `A₁`: the
coefficient of the quarter turn `J` in `A₁` (`A₁ = a I + b J + …`); in the rotating frame the
fundamental harmonic of the standard form contributes `Re{b e^{jωt}} J`. -/
def rotCoeff (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := (A 1 0 - A 0 1) / 2

/-- **Without the anti-resonant pump the second harmonic vanishes.** If `g' = 0`
(`SecondOrder.antiPump A = 0`), the rotating-frame matrix is
`F(t) = M + Re{a e^{jωt}} I + Re{b e^{jωt}} J`, `M = slowFlowMatrix s d (g/2)`,
`a = (a₀₀ + a₁₁)/2`, `b = rotCoeff A`: all its oscillating terms commute with `J`. -/
@[tmio T, powerlib_foundation] theorem stdForm_of_antiPump_eq_zero (s d ω : ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (h : antiPump A = 0) (t : ℝ) :
    stdForm s d ω A t = slowFlowMatrix s d (Element.pump A left right / 2) +
      (((A 0 0).re + (A 1 1).re) / 2 * Real.cos (ω * t) -
          ((A 0 0).im + (A 1 1).im) / 2 * Real.sin (ω * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      ((rotCoeff A).re * Real.cos (ω * t) - (rotCoeff A).im * Real.sin (ω * t)) • quarter := by
  rw [SecondOrder.antiPump_eq] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  have c1 : ((A 0 0).re - (A 1 1).re + (A 0 1).im + (A 1 0).im) / 4 = 0 := by linarith
  have c2 : ((A 0 1).re + (A 1 0).re - (A 0 0).im + (A 1 1).im) / 4 = 0 := by linarith
  have c3 : ((A 0 1).im + (A 1 0).im + (A 0 0).re - (A 1 1).re) / 4 = 0 := by linarith
  rw [TwoToOne.stdForm_eq, c1, c2, c3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotCoeff, quarter] <;> ring

/-- With `g = g' = 0` and `s = d = 0` the rotating-frame matrix is `Re{a e^{jωt}} I +
Re{b e^{jωt}} J`. -/
@[tmio T, powerlib_foundation] private theorem stdForm_commuting (ω : ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hg : Element.pump A left right = 0) (h : antiPump A = 0)
    (t : ℝ) :
    stdForm 0 0 ω A t =
      (((A 0 0).re + (A 1 1).re) / 2 * Real.cos (ω * t) -
          ((A 0 0).im + (A 1 1).im) / 2 * Real.sin (ω * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      ((rotCoeff A).re * Real.cos (ω * t) - (rotCoeff A).im * Real.sin (ω * t)) • quarter := by
  rw [stdForm_of_antiPump_eq_zero 0 0 ω h, hg, zero_div]
  have h0 : slowFlowMatrix 0 0 0 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [slowFlowMatrix]
  rw [h0, zero_add]

/-- The primitive of `c cos(ωt) − e sin(ωt)` vanishing at `0`. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_trigPrim {ω : ℝ} (hω : ω ≠ 0)
    (c e : ℝ) (r : ℝ) :
    HasDerivAt (fun t => (c * Real.sin (ω * t) - e * (1 - Real.cos (ω * t))) / ω)
      (c * Real.cos (ω * r) - e * Real.sin (ω * r)) r := by
  have h1 : HasDerivAt (fun t => ω * t) ω r := by simpa using (hasDerivAt_id r).const_mul ω
  have h := ((((Real.hasDerivAt_sin (ω * r)).comp r h1).const_mul c).sub
    ((((Real.hasDerivAt_cos (ω * r)).comp r h1).const_sub 1).const_mul e)).div_const ω
  refine h.congr_deriv ?_
  field_simp

@[tmio T, powerlib_foundation] private theorem trigPrim_period {ω : ℝ} (hω : 0 < ω) (c e : ℝ) :
    (c * Real.sin (ω * (2 * Real.pi / ω)) - e * (1 - Real.cos (ω * (2 * Real.pi / ω)))) / ω = 0 := by
  have h : ω * (2 * Real.pi / ω) = 2 * Real.pi := by field_simp
  rw [h, Real.sin_two_pi, Real.cos_two_pi]
  ring

end Structure

/-! ## The undamped two-state system on its boundary at third order -/

section Undamped

open TwoToOne (full stdForm left right)
open SecondOrder (antiPump)
open _root_.powerlib.ParametricResonance.NormalForm (quarter rot)

/-- **`tr Φ + 2 = det Y` for the undamped system.** For `TwoToOne.full 0 d ω A ε` (`s = 0`) the
monodromy is `Φ = −Φ_y = −(I + Y)` with `det Φ = 1` (Liouville), so
`tr Φ + 2 = det(Φ_y − I)` exactly, for every `ε`. -/
@[tmio T, powerlib_foundation] theorem zero_damping_trace_add_two (d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    (Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).trace + 2 =
      (Periodic.monodromy (fun t => ε • stdForm 0 d ω A t) (2 * Real.pi / ω) 0 - 1).det := by
  have hm := TwoToOne.monodromy_full 0 d hω A ε
  have hdet := (ZeroDamping.zero_damping_reciprocal d hω A ε).1
  set Py := Periodic.monodromy (fun t => ε • stdForm 0 d ω A t) (2 * Real.pi / ω) 0
  have e : Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0 = -(1 + (Py - 1)) := by
    rw [hm, add_sub_cancel]
  rw [e] at hdet ⊢
  exact trace_neg_add_two hdet

/-- **The undamped boundary decided at third order.** For `TwoToOne.full 0 d ω A ε` on the
boundary `d² = |g/2|²` with `d |g'|² = 0` (where the second-order test of
`ZeroDamping.zero_damping_trace` is void), with `F = TwoToOne.stdForm 0 d ω A`,
`M = slowFlowMatrix 0 d (g/2)`, `T = 2π/ω`, `N₂ = secondTerm F T`, `N₃ = thirdTerm F T`:
`tr Φ + 2 = ε⁴ K + O(ε⁵)`, `K = det N₂ + T mixedDet(M, N₃)`, and for all small `ε > 0`
`K > 0` gives `|tr Φ| < 2` (elliptic), `K < 0` gives `tr Φ < −2` (a real multiplier `< −1`). -/
@[tmio T, powerlib_foundation] theorem zero_damping_third_order {d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hb : d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2)
    (hdg : d * ‖antiPump A‖ ^ 2 = 0) :
    (0 < (secondTerm (stdForm 0 d ω A) (2 * Real.pi / ω)).det + 2 * Real.pi / ω *
        mixedDet (slowFlowMatrix 0 d (Element.pump A left right / 2))
          (thirdTerm (stdForm 0 d ω A) (2 * Real.pi / ω)) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        |(Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).trace| < 2) ∧
    ((secondTerm (stdForm 0 d ω A) (2 * Real.pi / ω)).det + 2 * Real.pi / ω *
        mixedDet (slowFlowMatrix 0 d (Element.pump A left right / 2))
          (thirdTerm (stdForm 0 d ω A) (2 * Real.pi / ω)) < 0 →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).trace < -2) := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  set g := Element.pump A left right with hg
  set F := stdForm 0 d ω A with hF
  set Mb := slowFlowMatrix 0 d (g / 2) with hMb
  obtain ⟨MF, hMF0, hMF⟩ := TwoToOne.exists_bound_stdForm 0 d hω A
  have havg : ∫ r in (0 : ℝ)..T, F r = T • Mb := TwoToOne.integral_stdForm 0 d hω A
  have hFc : Continuous F := TwoToOne.continuous_stdForm 0 d ω A
  set Py : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun ε => Periodic.monodromy (fun t => ε • F t) T 0
    with hPy
  have hmono : ∀ ε, Periodic.monodromy (full 0 d ω A ε) T 0 = -Py ε := fun ε =>
    TwoToOne.monodromy_full 0 d hω A ε
  have htrace : ∀ ε, (Periodic.monodromy (full 0 d ω A ε) T 0).trace = -(Py ε).trace :=
    fun ε => by rw [hmono, Matrix.trace_neg]
  have hdetPy : ∀ ε, 0 < ε → ε ≤ 1 → (Py ε).det = 1 := fun ε _ _ => by
    have h := (ZeroDamping.zero_damping_reciprocal d hω A ε).1
    rw [hmono, Matrix.det_neg, Fintype.card_fin] at h
    simpa using h
  set K₃ := MF * T * (MF * T * (MF * T * (MF * T * (‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ *
    Real.exp (MF * T))))) with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  have hexp : ∀ ε, 0 < ε → ε ≤ 1 → ‖Py ε - 1 - (ε * T) • Mb - ε ^ 2 • secondTerm F T -
      ε ^ 3 • thirdTerm F T‖ ≤ K₃ * ε ^ 4 := fun ε h0 h1 => by
    have h := monodromy_expansion_three (F := F) hFc hMF hMF0 hT.le havg h0.le h1
    rw [← hK₃] at h
    calc _ ≤ ε ^ 4 * K₃ := h
      _ = K₃ * ε ^ 4 := mul_comm _ _
  have hdetM : Mb.det = 0 := by rw [hMb, det_slowFlowMatrix, ← hb]; ring
  have hmix : mixedDet Mb (secondTerm F T) = 0 := by
    rw [hMb, hF, SecondOrder.mixedDet_secondTerm_stdForm 0 d hω A]
    have e : 2 * Real.pi / ω * d * ‖antiPump A‖ ^ 2 / (4 * ω) =
        2 * Real.pi / ω / (4 * ω) * (d * ‖antiPump A‖ ^ 2) := by ring
    rw [e, hdg]; ring
  obtain ⟨j1, j2⟩ := conservative_jury_three (P := Py) hT hK₃0 hexp hdetPy hdetM hmix
  refine ⟨fun h => ?_, fun h => ?_⟩
  · filter_upwards [j1 h] with ε hε
    rwa [htrace, abs_neg]
  · filter_upwards [j2 h] with ε hε
    rw [htrace]; linarith

/-- **The fourth-order coefficient at zero detuning.** For `s = d = 0` the boundary forces
`g = 0`; then `M = 0`, the second Picard term is `N₂ = −(T|g'|²/(8ω)) J`
(`SecondOrder.secondTerm_stdForm`) and `K = det N₂ + T mixedDet(M, N₃) = (T|g'|²/(8ω))²`. -/
@[tmio T, powerlib_foundation] theorem zero_detuning_coefficient {ω : ℝ} (hω : 0 < ω)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hg : Element.pump A left right = 0) :
    secondTerm (stdForm 0 0 ω A) (2 * Real.pi / ω) =
        -((2 * Real.pi / ω * ‖antiPump A‖ ^ 2 / (8 * ω)) • quarter) ∧
      (secondTerm (stdForm 0 0 ω A) (2 * Real.pi / ω)).det + 2 * Real.pi / ω *
          mixedDet (slowFlowMatrix 0 0 (Element.pump A left right / 2))
            (thirdTerm (stdForm 0 0 ω A) (2 * Real.pi / ω)) =
        (2 * Real.pi / ω * ‖antiPump A‖ ^ 2 / (8 * ω)) ^ 2 := by
  have h0 : slowFlowMatrix 0 0 0 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [slowFlowMatrix]
  have hN : secondTerm (stdForm 0 0 ω A) (2 * Real.pi / ω) =
      -((2 * Real.pi / ω * ‖antiPump A‖ ^ 2 / (8 * ω)) • quarter) := by
    rw [SecondOrder.secondTerm_stdForm 0 0 hω A, hg, zero_div, h0]
    simp
  refine ⟨hN, ?_⟩
  rw [hN, hg, zero_div, h0]
  simp [mixedDet, Matrix.det_fin_two, quarter]
  ring

/-- **Zero damping, zero detuning, `g' ≠ 0`: marginally stable.** For `TwoToOne.full 0 0 ω A ε` on
the boundary (`g = 0`) with anti-resonant pump `g' ≠ 0`, for all small `ε > 0`: every Floquet
multiplier is non-real on the unit circle, the monodromy is neither Schur stable nor Floquet
unstable, every solution is bounded and none decays (`K = (T|g'|²/(8ω))² > 0`). -/
@[tmio T, powerlib_foundation] theorem zero_detuning_marginal {ω : ℝ} (hω : 0 < ω)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hg : Element.pump A left right = 0) (hg' : antiPump A ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (full 0 0 ω A ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)), ‖μ‖ = 1 ∧ μ.im ≠ 0) ∧
        ¬ LTI.SchurStable (Periodic.monodromy (full 0 0 ω A ε) (2 * Real.pi / ω) 0) ∧
        ¬ Periodic.FloquetUnstable (full 0 0 ω A ε) (2 * Real.pi / ω) ∧
        (∃ K, ∀ t, 0 ≤ t → ∀ v : Fin 2 → ℝ,
          ‖Periodic.transition (full 0 0 ω A ε) t 0 *ᵥ v‖ ≤ K * ‖v‖) ∧
        ∃ c > 0, ∀ (n : ℕ) (v : Fin 2 → ℝ),
          c * ‖v‖ ≤ ‖Periodic.transition (full 0 0 ω A ε) (n * (2 * Real.pi / ω)) 0 *ᵥ v‖ := by
  have hb : (0 : ℝ) ^ 2 = ‖Element.pump A left right / 2‖ ^ 2 := by rw [hg]; simp
  have hK := (zero_detuning_coefficient hω hg).2
  have hpos : 0 < 2 * Real.pi / ω * ‖antiPump A‖ ^ 2 / (8 * ω) := by
    have := norm_pos_iff.mpr hg'
    positivity
  have htr := (zero_damping_third_order hω A hb (by ring)).1 (by rw [hK]; positivity)
  filter_upwards [htr] with ε hε
  exact ZeroDamping.elliptic_monodromy (TwoToOne.continuous_full 0 0 ω A ε)
    (TwoToOne.periodic_full 0 0 hω.ne' A ε) (by positivity)
    (ZeroDamping.zero_damping_reciprocal 0 hω A ε).1 hε

/-- **Zero damping, zero detuning, `g = g' = 0`: the monodromy is exactly `−I`.** Then the
rotating-frame matrix `Re{a e^{jωt}} I + Re{b e^{jωt}} J` commutes with itself at all times and
its transition matrix is `e^{εp(t)} R(εq(t))` with `p(T) = q(T) = 0`
(`transition_rotation_commuting`): for every `ε` the monodromy of `TwoToOne.full 0 0 ω A ε` is
`−I` (every solution `2T`-periodic). -/
@[tmio T, powerlib_foundation] theorem zero_detuning_exact {ω : ℝ} (hω : 0 < ω)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hg : Element.pump A left right = 0) (hg' : antiPump A = 0)
    (ε : ℝ) :
    Periodic.monodromy (full 0 0 ω A ε) (2 * Real.pi / ω) 0 = -1 := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨MF, hMF0, hMF⟩ := TwoToOne.exists_bound_stdForm 0 0 hω A
  set c₀ := ((A 0 0).re + (A 1 1).re) / 2
  set e₀ := ((A 0 0).im + (A 1 1).im) / 2
  set c₁ := (rotCoeff A).re
  set e₁ := (rotCoeff A).im
  have hB : ∀ r, ‖ε • stdForm 0 0 ω A r‖ ≤ |ε| * MF := fun r => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hMF r) (abs_nonneg ε)
  have h := transition_rotation_commuting (A := fun r => ε • stdForm 0 0 ω A r)
    ((TwoToOne.continuous_stdForm 0 0 ω A).const_smul ε) hB
    (α := fun r => ε * (c₀ * Real.cos (ω * r) - e₀ * Real.sin (ω * r)))
    (β := fun r => ε * (c₁ * Real.cos (ω * r) - e₁ * Real.sin (ω * r)))
    (p := fun r => ε * ((c₀ * Real.sin (ω * r) - e₀ * (1 - Real.cos (ω * r))) / ω))
    (q := fun r => ε * ((c₁ * Real.sin (ω * r) - e₁ * (1 - Real.cos (ω * r))) / ω))
    (fun r => by rw [stdForm_commuting ω hg hg' r, smul_add, smul_smul, smul_smul])
    (fun r => (hasDerivAt_trigPrim hω.ne' c₀ e₀ r).const_mul ε)
    (fun r => (hasDerivAt_trigPrim hω.ne' c₁ e₁ r).const_mul ε)
    (by simp) (by simp) hT.le
  rw [trigPrim_period hω, trigPrim_period hω, mul_zero, Real.exp_zero, one_smul] at h
  rw [TwoToOne.monodromy_full 0 0 hω A ε, Periodic.monodromy, zero_add, h]
  simp [rot]

end Undamped

end powerlib.ParametricResonance.ThirdOrder
