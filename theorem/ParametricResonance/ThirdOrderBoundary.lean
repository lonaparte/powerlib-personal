import theorem.ParametricResonance.ZeroDampingBranch

/-! # The 2:1 boundary at third order: the cases left open at second order

On the first-order boundary of the 2:1 criterion the second-order quantity `mixedDet(M, N₂)`
(`Boundary.critical_jury`, `ZeroDamping.conservative_jury`) decides unless it vanishes; for the
complete two-state system `TwoToOne.full s d ω A ε` it is `T d |g'|²/(4ω)` on the boundary
(`SecondOrder.mixedDet_secondTerm_stdForm`, anti-resonant pump `g' = SecondOrder.antiPump A`), so
the cases `d = 0` and `g' = 0` were open. This file carries the expansion one order further and
decides them.

* Generic: the third Picard term `N₃ = ∫₀ᵀ F(r) N₂(r) dr` and
  `Φ_ε(T) = I + εT F̄ + ε² N₂ + ε³ N₃ + O(ε⁴)` with an explicit bound
  (`monodromy_expansion_three`); for `2 × 2` matrices
  `det Y = ε²T² det M + ε³T mixedDet(M, N₂) + ε⁴(det N₂ + T mixedDet(M, N₃)) + O(ε⁵)`
  (`det_expansion_four`); for `Φ = −(I + Y)` of determinant one `tr Φ + 2 = det Y` exactly
  (`trace_neg_add_two`). On `det M = 0 = mixedDet(M, N₂)` the sign of
  `K = det N₂ + T mixedDet(M, N₃)` decides: elliptic/hyperbolic for determinant one
  (`conservative_jury_three`), Schur stable / a multiplier `> 1` at a simple critical exponent
  (`critical_jury_three`). On the boundary the triple integral reduces, by parts and
  Cayley–Hamilton, to a single one: `mixedDet(M, N₃) = −mixedDet(M, ∫₀ᵀ P̃ F P̃)` with the
  oscillating part `P̃(r) = ∫₀ʳ F − r M` of the primitive (`mixedDet_thirdTerm_boundary`).
* `s = 0, d = 0` (then `g = 0`, `M = 0`): `N₂ = −(T|g'|²/(8ω)) J`, `K = (T|g'|²/(8ω))²`
  (`zero_detuning_coefficient`); `g' ≠ 0`: marginally stable, bounded and non-decaying for all
  small `ε` (`zero_detuning_marginal`); `g' = 0`: the rotating-frame matrix commutes with itself
  at all times and the monodromy is exactly `−I` for every `ε` (`zero_detuning_exact`). The
  branch is never unstable.
* `g' = 0` (any `s ≥ 0` on the boundary): the second harmonic vanishes
  (`stdForm_of_antiPump_eq_zero`) and `K = 2T²|g/2|²|b|²/ω²` in closed form, `b = rotCoeff A =
  (a₁₀ − a₀₁)/2` the rotational fundamental coefficient (`antiFree_coefficient`). For `b ≠ 0`:
  `s = 0`, `d ≠ 0` marginally stable and bounded (`zero_damping_antiFree_marginal`); `s > 0` Schur
  stable (`antiFree_stable`). For `b = 0` the monodromy is known exactly (`antiFree_exact`):
  `−(I + εT M)` for `s = 0`, a Jordan block with unbounded (linearly growing) solutions
  (`zero_damping_antiFree_unbounded`), and `−(I + (1 − e^{−2sεT})/(2s) M)` for `s > 0`, with the
  multipliers `−1`, `−e^{−2sεT}`: neither Schur stable nor Floquet unstable (`antiFree_marginal`).
  Hence the second-order data `(s, d, g, g' = 0)` do not decide: explicit modulations with
  `b = 1` and `b = 0` give opposite verdicts (`antiFree_undecided`).
* `s > 0, d = 0, g' ≠ 0`: decided by the sign of `K` (`full_boundary_third_order`); the closed
  form of `K` there (the second harmonic interacts with the fundamental through triple products)
  is not derived in this file.

Scope.
* Generic: `ẏ = εF(t) y` on `ℝ^X` (finite `X`), `F` continuous and bounded (operator `L∞` norm),
  the transition matrix of `theorem/Periodic/Transition.lean`; `2 × 2` families
  `P(ε) = I + εT M + ε² N₂ + ε³ N₃ + O(ε⁴)` on `(0, 1]`; `secondTerm`, `mixedDet` of
  `theorem/ParametricResonance/BoundaryUndecided.lean`.
* Two-state system: `TwoToOne.full s d ω A ε` (critical pair `−εs ± j(ω/2 − εd)` in real modal
  form, modulation `ε Re{A e^{jωt}}`, `ω > 0`, `T = 2π/ω`) on its first-order boundary
  `s² + d² = |g/2|²`, `s ≥ 0`; statements for all sufficiently small `ε > 0` unless stated for
  every `ε`.
* Generic mathematics; no model family.

Source: the wave-6 question of this library (the boundary cases `d|g'|² = 0` left undecided by
`SecondOrder.full_boundary_closed_form` and `ZeroDamping.zero_damping_trace`); the small-parameter
(Picard) expansion of the monodromy and the Lyapunov criterion for Hill-type systems
(Yakubovich–Starzhinskii, *Linear Differential Equations with Periodic Coefficients*; Magnus–Winkler,
*Hill's Equation*; Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 5, transition curves beyond first
order); `Boundary.monodromy_expansion_two`, `SecondOrder.secondTerm_stdForm`,
`ZeroDamping.elliptic_monodromy`, `Periodic.transition_unique`.

Results.
* Expansion: `thirdTerm`, `continuous_secondTerm`, `norm_transition_sub_third_le`,
  `monodromy_expansion_three`.
* `2 × 2` algebra: `trace_neg_add_two`, `det_expansion_four`, `conservative_jury_three`,
  `critical_jury_three`, `mixedDet_mul_self`, `mixedDetL`, `mixedDet_thirdTerm_boundary`.
* Exact solutions: `transition_rotation_commuting` (`α I + β J`), `transition_rank_one`
  (`κ M + α I`, `M² = τ M`).
* Two-state system: `rotCoeff`, `stdForm_of_antiPump_eq_zero`, `zero_damping_trace_add_two`,
  `zero_damping_third_order`, `zero_detuning_coefficient`, `zero_detuning_marginal`,
  `zero_detuning_exact`, `antiFree_coefficient`, `zero_damping_antiFree_marginal`,
  `full_boundary_third_order`, `antiFree_stable`, `antiFree_exact`,
  `zero_damping_antiFree_unbounded`, `antiFree_marginal`, `antiFreeModulation`,
  `antiFreeModulation_data`, `antiFree_undecided`.

Corrections.
None: an extension (the cases left open at second order by
`theorem/ParametricResonance/ZeroDampingBranch.lean` and
`theorem/ParametricResonance/SecondOrderClosedForm.lean`). The undamped branch `d = 0` is never
unstable (elliptic for `g' ≠ 0`, exactly `−I` for `g' = 0`), and the branch `g' = 0` is never
Floquet unstable (`K ≥ 0`); it is decided by the rotational coefficient `b`.

Family and connection conclusions.
None: static evidence on periodic linear systems.
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

/-! ## The branch without anti-resonant pump: the fourth-order coefficient in closed form -/

section AntiFree

open TwoToOne (full stdForm left right)
open SecondOrder (antiPump stdSin stdCos)
open _root_.powerlib.ParametricResonance.NormalForm (quarter rot)

@[tmio T, powerlib_foundation] private theorem mixedDet_commuting_sandwich (s d p q α β : ℝ)
    (γ : ℂ) :
    mixedDet (slowFlowMatrix s d γ)
        ((p • (1 : Matrix (Fin 2) (Fin 2) ℝ) + q • quarter) *
          (slowFlowMatrix s d γ + α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • quarter) *
          (p • (1 : Matrix (Fin 2) (Fin 2) ℝ) + q • quarter)) =
      2 * (s ^ 2 + d ^ 2 - ‖γ‖ ^ 2) * (p ^ 2 - q ^ 2) - 4 * ‖γ‖ ^ 2 * q ^ 2 -
        2 * s * ((p ^ 2 - q ^ 2) * α - 2 * p * q * β) -
        2 * d * ((p ^ 2 - q ^ 2) * β + 2 * p * q * α) := by
  have e1 : p • (1 : Matrix (Fin 2) (Fin 2) ℝ) + q • quarter = !![p, -q; q, p] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [quarter]
  have e2 : slowFlowMatrix s d γ + α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • quarter =
      !![-s + γ.re + α, d + γ.im - β; -d + γ.im + β, -s - γ.re + α] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [slowFlowMatrix, quarter]; ring
  rw [e1, e2, Complex.sq_norm, Complex.normSq_apply]
  simp [mixedDet, slowFlowMatrix, Matrix.trace_fin_two]
  ring

@[tmio T, powerlib_foundation] private theorem integral_trig_sq {ω : ℝ} (hω : 0 < ω) (c e : ℝ) :
    ∫ r in (0 : ℝ)..(2 * Real.pi / ω), (c * Real.sin (ω * r) - e * (1 - Real.cos (ω * r))) ^ 2 =
      2 * Real.pi / ω * (c ^ 2 + 3 * e ^ 2) / 2 := by
  set T := 2 * Real.pi / ω with hT
  have i1 : ∫ r in (0 : ℝ)..T, Real.sin (ω * r) * Real.sin (ω * r) = T / 2 := by
    have h := SecondOrder.integral_sin_mul_sin_period hω (j := 1) one_ne_zero 1
    simpa using h
  have i2 : ∫ r in (0 : ℝ)..T, Real.cos (ω * r) * Real.cos (ω * r) = T / 2 := by
    have h := SecondOrder.integral_cos_mul_cos_period hω (j := 1) one_ne_zero 1
    simpa using h
  have i3 : ∫ r in (0 : ℝ)..T, Real.cos (ω * r) * Real.sin (ω * r) = 0 := by
    have h := SecondOrder.integral_cos_mul_sin_period hω 1 1
    simpa using h
  have i4 : ∫ r in (0 : ℝ)..T, Real.sin (ω * r) = 0 := by
    have h := SecondOrder.integral_sin_int_mul hω 1
    simpa using h
  have i5 : ∫ r in (0 : ℝ)..T, Real.cos (ω * r) = 0 := by
    have h := SecondOrder.integral_cos_int_mul hω 1
    simpa using h
  have e : (fun r => (c * Real.sin (ω * r) - e * (1 - Real.cos (ω * r))) ^ 2) = fun r =>
      c ^ 2 * (Real.sin (ω * r) * Real.sin (ω * r)) + e ^ 2 * (Real.cos (ω * r) * Real.cos (ω * r)) +
        2 * c * e * (Real.cos (ω * r) * Real.sin (ω * r)) - 2 * c * e * Real.sin (ω * r) -
        2 * e ^ 2 * Real.cos (ω * r) + e ^ 2 := by
    funext r; ring
  have c1 : Continuous fun r => Real.sin (ω * r) * Real.sin (ω * r) := by fun_prop
  have c2 : Continuous fun r => Real.cos (ω * r) * Real.cos (ω * r) := by fun_prop
  have c3 : Continuous fun r => Real.cos (ω * r) * Real.sin (ω * r) := by fun_prop
  have c4 : Continuous fun r => Real.sin (ω * r) := by fun_prop
  have c5 : Continuous fun r => Real.cos (ω * r) := by fun_prop
  rw [e, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      intervalIntegrable_const,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      ((c5.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      ((c4.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      ((c3.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_add ((c1.const_mul _).intervalIntegrable _ _)
      ((c2.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, i1, i2, i3, i4, i5, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  ring

/-- `∫₀ᵀ (p³/3 − p q²)' = 0` and `∫₀ᵀ (p² q − q³/3)' = 0` when `p`, `q` vanish at `0` and `T`. -/
@[tmio T, powerlib_foundation] private theorem integral_exact_cubics {p q α β : ℝ → ℝ} {T : ℝ}
    (hpd : ∀ r, HasDerivAt p (α r) r) (hqd : ∀ r, HasDerivAt q (β r) r) (hα : Continuous α)
    (hβ : Continuous β) (hp0 : p 0 = 0) (hq0 : q 0 = 0) (hpT : p T = 0) (hqT : q T = 0) :
    (∫ r in (0 : ℝ)..T, ((p r ^ 2 - q r ^ 2) * α r - 2 * p r * q r * β r)) = 0 ∧
      (∫ r in (0 : ℝ)..T, ((p r ^ 2 - q r ^ 2) * β r + 2 * p r * q r * α r)) = 0 := by
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun r => (hpd r).continuousAt
  have hqc : Continuous q := continuous_iff_continuousAt.2 fun r => (hqd r).continuousAt
  constructor
  · have key : ∀ r ∈ uIcc (0 : ℝ) T, HasDerivAt (fun r => p r ^ 3 / 3 - p r * q r ^ 2)
        ((p r ^ 2 - q r ^ 2) * α r - 2 * p r * q r * β r) r := fun r _ => by
      have h := (((hpd r).pow 3).div_const 3).sub ((hpd r).mul ((hqd r).pow 2))
      convert h using 1
      simp only [Pi.pow_apply]
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp [hp0, hq0, hpT, hqT]
  · have key : ∀ r ∈ uIcc (0 : ℝ) T, HasDerivAt (fun r => p r ^ 2 * q r - q r ^ 3 / 3)
        ((p r ^ 2 - q r ^ 2) * β r + 2 * p r * q r * α r) r := fun r _ => by
      have h := (((hpd r).pow 2).mul (hqd r)).sub (((hqd r).pow 3).div_const 3)
      convert h using 1
      simp only [Pi.pow_apply]
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp [hp0, hq0, hpT, hqT]

/-- **The fourth-order coefficient without anti-resonant pump.** For the two-state 2:1 system
with `g' = 0` on the boundary `s² + d² = |g/2|²` (any `s`): the second harmonic of the
rotating-frame matrix vanishes (`stdForm_of_antiPump_eq_zero`), the primitive's oscillating part
`P̃ = p I + q J` commutes with `J`, `mixedDet(M, N₃) = −mixedDet(M, ∫ P̃ F P̃) = 4|g/2|² ∫₀ᵀ q²`
(`mixedDet_thirdTerm_boundary`; the remaining terms are exact derivatives), `det N₂ =
−4T²|g/2|²(Im b)²/ω²`, and
`K = det N₂ + T mixedDet(M, N₃) = 2 T² |g/2|² |b|² / ω²`, `b = rotCoeff A = (a₁₀ − a₀₁)/2`. -/
@[tmio T, powerlib_foundation] theorem antiFree_coefficient (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (h : antiPump A = 0)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) :
    (secondTerm (stdForm s d ω A) (2 * Real.pi / ω)).det + 2 * Real.pi / ω *
        mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
          (thirdTerm (stdForm s d ω A) (2 * Real.pi / ω)) =
      2 * (2 * Real.pi / ω) ^ 2 * ‖Element.pump A left right / 2‖ ^ 2 * ‖rotCoeff A‖ ^ 2 /
        ω ^ 2 := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  set γ := Element.pump A left right / 2 with hγ
  set M := slowFlowMatrix s d γ with hM
  set F := stdForm s d ω A with hF
  set c₀ := ((A 0 0).re + (A 1 1).re) / 2 with hc₀
  set e₀ := ((A 0 0).im + (A 1 1).im) / 2 with hc₀
  set c₁ := (rotCoeff A).re with hc₁
  set e₁ := (rotCoeff A).im with he₁
  set p : ℝ → ℝ := fun r => (c₀ * Real.sin (ω * r) - e₀ * (1 - Real.cos (ω * r))) / ω with hp
  set q : ℝ → ℝ := fun r => (c₁ * Real.sin (ω * r) - e₁ * (1 - Real.cos (ω * r))) / ω with hq
  set α : ℝ → ℝ := fun r => c₀ * Real.cos (ω * r) - e₀ * Real.sin (ω * r) with hα
  set β : ℝ → ℝ := fun r => c₁ * Real.cos (ω * r) - e₁ * Real.sin (ω * r) with hβ
  have hFeq : ∀ r, F r = M + α r • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β r • quarter :=
    fun r => stdForm_of_antiPump_eq_zero s d ω h r
  have hFc : Continuous F := TwoToOne.continuous_stdForm s d ω A
  have hδ : s ^ 2 + d ^ 2 - ‖γ‖ ^ 2 = 0 := by rw [hb]; ring
  have hdet : M.det = 0 := by rw [hM, det_slowFlowMatrix, ← hb]; ring
  have havg : ∫ r in (0 : ℝ)..T, F r = T • M := TwoToOne.integral_stdForm s d hω A
  -- the primitive: `∫₀ʳ F = r M + p(r) I + q(r) J`
  have hprim : ∀ r, (∫ u in (0 : ℝ)..r, F u) - r • M =
      p r • (1 : Matrix (Fin 2) (Fin 2) ℝ) + q r • quarter := by
    intro r
    have hd : ∀ u ∈ uIcc (0 : ℝ) r, HasDerivAt (fun u => u • M + p u • (1 : Matrix (Fin 2)
        (Fin 2) ℝ) + q u • quarter) (F u) u := fun u _ => by
      have h1 := (((hasDerivAt_id u).smul_const M).add
        ((hasDerivAt_trigPrim hω.ne' c₀ e₀ u).smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ))).add
        ((hasDerivAt_trigPrim hω.ne' c₁ e₁ u).smul_const quarter)
      refine h1.congr_deriv ?_
      rw [hFeq u, one_smul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hFc.intervalIntegrable 0 r)]
    simp [hp, hq]
    abel
  -- `mixedDet(M, N₃) = 4|γ|² ∫ q²`
  have hpd : ∀ r, HasDerivAt p (α r) r := hasDerivAt_trigPrim hω.ne' c₀ e₀
  have hqd : ∀ r, HasDerivAt q (β r) r := hasDerivAt_trigPrim hω.ne' c₁ e₁
  have hcont : Continuous fun r => (p r • (1 : Matrix (Fin 2) (Fin 2) ℝ) + q r • quarter) * F r *
      (p r • (1 : Matrix (Fin 2) (Fin 2) ℝ) + q r • quarter) := by
    have hpc : Continuous p := by simp only [hp]; fun_prop
    have hqc : Continuous q := by simp only [hq]; fun_prop
    exact (((hpc.smul continuous_const).add (hqc.smul continuous_const)).mul hFc).mul
      ((hpc.smul continuous_const).add (hqc.smul continuous_const))
  have h3 := mixedDet_thirdTerm_boundary hFc havg hdet
  simp_rw [hprim] at h3
  rw [mixedDet_integral M hcont] at h3
  have hpt : ∀ r, mixedDet M ((p r • (1 : Matrix (Fin 2) (Fin 2) ℝ) + q r • quarter) * F r *
      (p r • (1 : Matrix (Fin 2) (Fin 2) ℝ) + q r • quarter)) =
      -4 * ‖γ‖ ^ 2 * q r ^ 2 -
        2 * s * ((p r ^ 2 - q r ^ 2) * α r - 2 * p r * q r * β r) -
        2 * d * ((p r ^ 2 - q r ^ 2) * β r + 2 * p r * q r * α r) := fun r => by
    rw [hFeq r, hM, mixedDet_commuting_sandwich, hδ]
    ring
  simp_rw [hpt] at h3
  have hαc : Continuous α := by simp only [hα]; fun_prop
  have hβc : Continuous β := by simp only [hβ]; fun_prop
  have hpc : Continuous p := by simp only [hp]; fun_prop
  have hqc : Continuous q := by simp only [hq]; fun_prop
  obtain ⟨x1, x2⟩ := integral_exact_cubics (T := T) hpd hqd hαc hβc (by simp [hp]) (by simp [hq])
    (trigPrim_period hω c₀ e₀) (trigPrim_period hω c₁ e₁)
  have iq : ∫ r in (0 : ℝ)..T, q r ^ 2 = T * (c₁ ^ 2 + 3 * e₁ ^ 2) / 2 / ω ^ 2 := by
    simp only [hq, div_pow]
    rw [intervalIntegral.integral_div, integral_trig_sq hω c₁ e₁]
  have cq : Continuous fun r => -4 * ‖γ‖ ^ 2 * q r ^ 2 := by fun_prop
  have cx1 : Continuous fun r => 2 * s * ((p r ^ 2 - q r ^ 2) * α r - 2 * p r * q r * β r) := by
    fun_prop
  have cx2 : Continuous fun r => 2 * d * ((p r ^ 2 - q r ^ 2) * β r + 2 * p r * q r * α r) := by
    fun_prop
  rw [intervalIntegral.integral_sub
      (f := fun r => -4 * ‖γ‖ ^ 2 * q r ^ 2 -
        2 * s * ((p r ^ 2 - q r ^ 2) * α r - 2 * p r * q r * β r))
      (g := fun r => 2 * d * ((p r ^ 2 - q r ^ 2) * β r + 2 * p r * q r * α r))
      ((cq.sub cx1).intervalIntegrable _ _) (cx2.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f := fun r => -4 * ‖γ‖ ^ 2 * q r ^ 2)
      (g := fun r => 2 * s * ((p r ^ 2 - q r ^ 2) * α r - 2 * p r * q r * β r))
      (cq.intervalIntegrable _ _) (cx1.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, iq, x1, x2] at h3
  -- `det N₂`
  have hS2 : stdSin A 2 = 0 := by
    rw [SecondOrder.antiPump_eq] at h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp at hre him
    have c2 : ((A 0 1).re + (A 1 0).re - (A 0 0).im + (A 1 1).im) / 4 = 0 := by linarith
    have c3 : ((A 0 1).im + (A 1 0).im + (A 0 0).re - (A 1 1).re) / 4 = 0 := by linarith
    simp only [stdSin, OfNat.ofNat_ne_one, ↓reduceIte, c2, c3, zero_smul, sub_zero]
  have hN₂ : secondTerm F T = (T ^ 2 / 2) • (M * M) + (T / ω) • (M * stdSin A 1 - stdSin A 1 * M) +
      (T / (2 * ω)) • (M * stdSin A 2 - stdSin A 2 * M) -
      (T * ‖antiPump A‖ ^ 2 / (8 * ω)) • quarter := SecondOrder.secondTerm_stdForm s d hω A
  rw [hS2, h, norm_zero] at hN₂
  simp only [Matrix.zero_mul, sub_zero, smul_zero, add_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div, zero_smul] at hN₂
  have hS1 : stdSin A 1 = !![-e₀, e₁; -e₁, -e₀] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [stdSin, quarter, rotCoeff, hc₀, he₁]
  have hMm : M = !![-s + γ.re, d + γ.im; -d + γ.im, -s - γ.re] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hM, slowFlowMatrix]
  have hdetN : (secondTerm F T).det = (T ^ 2 / 2) ^ 2 * (s ^ 2 + d ^ 2 - ‖γ‖ ^ 2) ^ 2 -
      4 * (T / ω) ^ 2 * e₁ ^ 2 * ‖γ‖ ^ 2 := by
    rw [hN₂, hS1, hMm, Complex.sq_norm, Complex.normSq_apply]
    simp [Matrix.det_fin_two]
    ring
  rw [hdetN, hδ, h3, Complex.sq_norm (rotCoeff A), Complex.normSq_apply]
  have hω0 : ω ≠ 0 := hω.ne'
  field_simp
  ring


@[tmio T, powerlib_foundation] private theorem slowFlow_mul_self {s d : ℝ} {γ : ℂ}
    (hb : s ^ 2 + d ^ 2 = ‖γ‖ ^ 2) :
    slowFlowMatrix s d γ * slowFlowMatrix s d γ = (-2 * s) • slowFlowMatrix s d γ := by
  rw [Complex.sq_norm, Complex.normSq_apply] at hb
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [slowFlowMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hb | linear_combination (-1) * hb

/-- The undamped and damped full systems: the rotating-frame expansion used below. -/
@[tmio T, powerlib_foundation] private theorem full_expansion (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ C, 0 ≤ C ∧ ∀ ε, 0 < ε → ε ≤ 1 →
      ‖Periodic.monodromy (fun t => ε • stdForm s d ω A t) (2 * Real.pi / ω) 0 - 1 -
          (ε * (2 * Real.pi / ω)) • slowFlowMatrix s d (Element.pump A left right / 2) -
          ε ^ 2 • secondTerm (stdForm s d ω A) (2 * Real.pi / ω) -
          ε ^ 3 • thirdTerm (stdForm s d ω A) (2 * Real.pi / ω)‖ ≤ C * ε ^ 4 := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  obtain ⟨MF, hMF0, hMF⟩ := TwoToOne.exists_bound_stdForm s d hω A
  refine ⟨MF * (2 * Real.pi / ω) * (MF * (2 * Real.pi / ω) * (MF * (2 * Real.pi / ω) *
    (MF * (2 * Real.pi / ω) * (‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ *
      Real.exp (MF * (2 * Real.pi / ω)))))), by positivity, fun ε h0 h1 => ?_⟩
  have h := monodromy_expansion_three (TwoToOne.continuous_stdForm s d ω A) hMF hMF0 hT.le
    (TwoToOne.integral_stdForm s d hω A) h0.le h1
  exact h.trans (le_of_eq (by ring))

/-- **Undamped, no anti-resonant pump, `b ≠ 0`: marginally stable.** For
`TwoToOne.full 0 d ω A ε` on the boundary `d² = |g/2|²` with `d ≠ 0`, `g' = 0` (so
`d|g'|² = 0` and the second-order test is void) and rotational fundamental coefficient
`b = rotCoeff A ≠ 0`: `K = 2T²|g/2|²|b|²/ω² > 0`, so for all small `ε > 0` the multipliers are
non-real on the unit circle, every solution is bounded and none decays. -/
@[tmio T, powerlib_foundation] theorem zero_damping_antiFree_marginal {d ω : ℝ} (hω : 0 < ω)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hb : d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2)
    (hd : d ≠ 0) (h : antiPump A = 0) (hrot : rotCoeff A ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)), ‖μ‖ = 1 ∧ μ.im ≠ 0) ∧
        ¬ LTI.SchurStable (Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0) ∧
        ¬ Periodic.FloquetUnstable (full 0 d ω A ε) (2 * Real.pi / ω) ∧
        (∃ K, ∀ t, 0 ≤ t → ∀ v : Fin 2 → ℝ,
          ‖Periodic.transition (full 0 d ω A ε) t 0 *ᵥ v‖ ≤ K * ‖v‖) ∧
        ∃ c > 0, ∀ (n : ℕ) (v : Fin 2 → ℝ),
          c * ‖v‖ ≤ ‖Periodic.transition (full 0 d ω A ε) (n * (2 * Real.pi / ω)) 0 *ᵥ v‖ := by
  have hK := antiFree_coefficient 0 d hω h (by rw [← hb]; ring)
  have hγ : 0 < ‖Element.pump A left right / 2‖ ^ 2 := by rw [← hb]; positivity
  have hr : 0 < ‖rotCoeff A‖ ^ 2 := by have := norm_pos_iff.mpr hrot; positivity
  have htr := (zero_damping_third_order hω A hb (by rw [h, norm_zero]; ring)).1
    (by rw [hK]; positivity)
  filter_upwards [htr] with ε hε
  exact ZeroDamping.elliptic_monodromy (TwoToOne.continuous_full 0 d ω A ε)
    (TwoToOne.periodic_full 0 d hω.ne' A ε) (by positivity)
    (ZeroDamping.zero_damping_reciprocal d hω A ε).1 hε

/-- **The damped boundary decided at third order.** For `TwoToOne.full s d ω A ε` with `s > 0`
on the boundary `s² + d² = |g/2|²` with `d |g'|² = 0` (where `SecondOrder.full_boundary_closed_form`
is void), with `F = TwoToOne.stdForm s d ω A`, `M = slowFlowMatrix s d (g/2)`, `T = 2π/ω`:
`det(I − Φ_y) = ε⁴ K + O(ε⁵)`, `K = det N₂ + T mixedDet(M, N₃)`, and for all small `ε > 0`
`K > 0` gives Schur stability and `K < 0` Floquet instability (`critical_jury_three`). -/
@[tmio T, powerlib_foundation] theorem full_boundary_third_order {s d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2)
    (hdg : d * ‖antiPump A‖ ^ 2 = 0) :
    (0 < (secondTerm (stdForm s d ω A) (2 * Real.pi / ω)).det + 2 * Real.pi / ω *
        mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
          (thirdTerm (stdForm s d ω A) (2 * Real.pi / ω)) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        LTI.SchurStable (Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0)) ∧
    ((secondTerm (stdForm s d ω A) (2 * Real.pi / ω)).det + 2 * Real.pi / ω *
        mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
          (thirdTerm (stdForm s d ω A) (2 * Real.pi / ω)) < 0 →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (full s d ω A ε) (2 * Real.pi / ω)) := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  obtain ⟨C, hC, hexp⟩ := full_expansion s d hω A
  have hdet : (slowFlowMatrix s d (Element.pump A left right / 2)).det = 0 := by
    rw [det_slowFlowMatrix, ← hb]; ring
  have htr : (slowFlowMatrix s d (Element.pump A left right / 2)).trace < 0 := by
    rw [trace_slowFlowMatrix]; linarith
  have hmix : mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
      (secondTerm (stdForm s d ω A) (2 * Real.pi / ω)) = 0 := by
    rw [SecondOrder.mixedDet_secondTerm_stdForm s d hω A, ← hb]
    have e : 2 * Real.pi / ω * d * ‖antiPump A‖ ^ 2 / (4 * ω) =
        2 * Real.pi / ω / (4 * ω) * (d * ‖antiPump A‖ ^ 2) := by ring
    rw [e, hdg]; ring
  obtain ⟨hst, hun⟩ := critical_jury_three hT hC hexp hdet htr hmix
  refine ⟨fun h => ?_, fun h => ?_⟩
  · filter_upwards [hst h] with ε hε
    rw [TwoToOne.monodromy_full s d hω A ε, NormalForm.schurStable_neg_iff]
    exact hε
  · filter_upwards [hun h] with ε ⟨μ, hμ, h1⟩
    refine ⟨-μ, ?_, by rw [norm_neg]; exact h1⟩
    rw [TwoToOne.monodromy_full s d hω A ε]
    obtain ⟨v, hv, hPv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
    refine LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, ?_⟩
    rw [Matrix.map_neg _ (fun a => map_neg (algebraMap ℝ ℂ) a), Matrix.neg_mulVec, hPv, neg_smul]

/-- **Damped, no anti-resonant pump, `b ≠ 0`: Schur stable.** For `TwoToOne.full s d ω A ε` with
`s > 0` on the boundary `s² + d² = |g/2|²`, `g' = 0` (so `d|g'|² = 0` and
`SecondOrder.full_boundary_closed_form` is void) and `b = rotCoeff A ≠ 0`: `det(I − Φ_y) =
ε⁴ K + O(ε⁵)` with `K = 2T²|g/2|²|b|²/ω² > 0`, so the monodromy is Schur stable for all small
`ε > 0` (`full_boundary_third_order`). -/
@[tmio T, powerlib_foundation] theorem antiFree_stable {s d ω : ℝ} (hω : 0 < ω)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) (h : antiPump A = 0)
    (hrot : rotCoeff A ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      LTI.SchurStable (Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0) := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have hK := antiFree_coefficient s d hω h hb
  have hγ : 0 < ‖Element.pump A left right / 2‖ ^ 2 := by rw [← hb]; positivity
  have hr : 0 < ‖rotCoeff A‖ ^ 2 := by have := norm_pos_iff.mpr hrot; positivity
  exact (full_boundary_third_order hω A hs hb (by rw [h, norm_zero]; ring)).1
    (by rw [hK]; positivity)

/-- **No anti-resonant pump and `b = 0`: the monodromy in closed form.** If `g' = 0` and
`rotCoeff A = 0`, the rotating-frame matrix is `M + Re{a e^{jωt}} I` (`M` the slow-flow matrix);
on the boundary `s² + d² = |g/2|²` (`M² = −2s M`) its transition matrix is
`e^{εp(t)}(I + f(t) M)` (`transition_rank_one`). Hence for every `ε` the monodromy of
`TwoToOne.full s d ω A ε` over `T = 2π/ω` is `−(I + εT M)` for `s = 0` and
`−(I + (1 − e^{−2sεT})/(2s) · M)` for `s > 0`. -/
@[tmio T, powerlib_foundation] theorem antiFree_exact {s d ω : ℝ} (hω : 0 < ω)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2)
    (h : antiPump A = 0) (hrot : rotCoeff A = 0) (ε : ℝ) :
    (s = 0 → Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0 =
      -(1 + (ε * (2 * Real.pi / ω)) • slowFlowMatrix s d (Element.pump A left right / 2))) ∧
    (0 < s → Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0 =
      -(1 + ((1 - Real.exp (-2 * s * ε * (2 * Real.pi / ω))) / (2 * s)) •
        slowFlowMatrix s d (Element.pump A left right / 2))) := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  set M := slowFlowMatrix s d (Element.pump A left right / 2) with hM
  obtain ⟨MF, hMF0, hMF⟩ := TwoToOne.exists_bound_stdForm s d hω A
  set c₀ := ((A 0 0).re + (A 1 1).re) / 2
  set e₀ := ((A 0 0).im + (A 1 1).im) / 2
  have hB : ∀ r, ‖ε • stdForm s d ω A r‖ ≤ |ε| * MF := fun r => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hMF r) (abs_nonneg ε)
  have hAeq : ∀ r, ε • stdForm s d ω A r = ε • M +
      (ε * (c₀ * Real.cos (ω * r) - e₀ * Real.sin (ω * r))) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro r
    rw [stdForm_of_antiPump_eq_zero s d ω h r, hrot]
    simp only [Complex.zero_re, Complex.zero_im, zero_mul, sub_zero, zero_smul, add_zero,
      smul_add, smul_smul]
    rfl
  have hp : ∀ r, HasDerivAt (fun r => ε * ((c₀ * Real.sin (ω * r) -
      e₀ * (1 - Real.cos (ω * r))) / ω)) (ε * (c₀ * Real.cos (ω * r) - e₀ * Real.sin (ω * r))) r :=
    fun r => (hasDerivAt_trigPrim hω.ne' c₀ e₀ r).const_mul ε
  have hMM := slowFlow_mul_self hb
  have hmono : ∀ f : ℝ → ℝ, (∀ r, HasDerivAt f (ε * (1 + (-2 * s) * f r)) r) → f 0 = 0 →
      Periodic.monodromy (full s d ω A ε) T 0 = -(1 + f T • M) := by
    intro f hf hf0
    have htr := transition_rank_one (A := fun r => ε • stdForm s d ω A r)
      ((TwoToOne.continuous_stdForm s d ω A).const_smul ε) hB hMM hAeq hp hf (by simp) hf0 hT.le
    rw [trigPrim_period hω, mul_zero, Real.exp_zero, one_smul] at htr
    rw [TwoToOne.monodromy_full s d hω A ε, Periodic.monodromy, zero_add, htr]
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · refine hmono (fun r => ε * r) (fun r => ?_) (by simp)
    rw [hs]
    simpa using (hasDerivAt_id r).const_mul ε
  · refine hmono (fun r => (1 - Real.exp (-2 * s * ε * r)) / (2 * s)) (fun r => ?_) (by simp)
    have h1 : HasDerivAt (fun r => -2 * s * ε * r) (-2 * s * ε) r := by
      simpa using (hasDerivAt_id r).const_mul (-2 * s * ε)
    have h2 := (((Real.hasDerivAt_exp _).comp r h1).const_sub 1).div_const (2 * s)
    refine h2.congr_deriv ?_
    field_simp
    ring

/-- **Undamped, no anti-resonant pump, `b = 0`: linear growth.** On the boundary `d² = |g/2|²`,
`d ≠ 0`, with `g' = 0` and `rotCoeff A = 0`, for every `ε > 0` the monodromy is the Jordan block
`−(I + εT M)` (`M ≠ 0` nilpotent): both multipliers equal `−1`, and the solutions are not
uniformly bounded (`‖Φ(nT, 0) v‖ → ∞` for some `v`). -/
@[tmio T, powerlib_foundation] theorem zero_damping_antiFree_unbounded {d ω : ℝ} (hω : 0 < ω)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hb : d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2)
    (hd : d ≠ 0) (h : antiPump A = 0) (hrot : rotCoeff A = 0) {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ K, ∀ (n : ℕ) (v : Fin 2 → ℝ),
      ‖Periodic.transition (full 0 d ω A ε) (n * (2 * Real.pi / ω)) 0 *ᵥ v‖ ≤ K * ‖v‖ := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  set γ := Element.pump A left right / 2 with hγ
  set M := slowFlowMatrix 0 d γ with hM
  have hb0 : (0 : ℝ) ^ 2 + d ^ 2 = ‖γ‖ ^ 2 := by rw [← hb]; ring
  have hΦ := (antiFree_exact hω hb0 h hrot ε).1 rfl
  have hMM : M * M = 0 := by
    have := slowFlow_mul_self hb0
    rw [mul_zero, zero_smul] at this
    exact this
  obtain ⟨MB, hMB⟩ := Periodic.exists_bound_of_periodic (TwoToOne.continuous_full 0 d ω A ε)
    (TwoToOne.periodic_full 0 d hω.ne' A ε) hT
  have hΦ' : Periodic.monodromy (full 0 d ω A ε) T 0 = -(1 + (ε * T) • M) := hΦ
  have hpowM : ∀ n : ℕ, (-(1 + (ε * T) • M)) ^ n =
      (-1 : ℝ) ^ n • (1 + ((n : ℝ) * (ε * T)) • M) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih]
      simp only [Matrix.smul_mul, Matrix.mul_neg, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_smul, hMM, smul_zero, add_zero, smul_add, smul_smul]
      push_cast
      module
  have hpow : ∀ n : ℕ, Periodic.transition (full 0 d ω A ε) (n * T) 0 =
      (-1 : ℝ) ^ n • (1 + ((n : ℝ) * (ε * T)) • M) := by
    intro n
    have h := Periodic.transition_add_nat_mul_period (TwoToOne.continuous_full 0 d ω A ε) hMB
      hT.le (TwoToOne.periodic_full 0 d hω.ne' A ε) 0 n
    rw [zero_add] at h
    rw [h, hΦ', hpowM]
  -- a vector with `M v ≠ 0`
  obtain ⟨v, i, hvi⟩ : ∃ (v : Fin 2 → ℝ) (i : Fin 2), (M *ᵥ v) i ≠ 0 := by
    by_cases h0 : d + γ.im = 0
    · refine ⟨![1, 0], 1, ?_⟩
      simp [hM, slowFlowMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      intro h1
      exact hd (by linarith)
    · refine ⟨![0, 1], 0, ?_⟩
      simpa [hM, slowFlowMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  rintro ⟨K, hK⟩
  have hεT : 0 < ε * T := mul_pos hε hT
  have hMv : 0 < |(M *ᵥ v) i| := abs_pos.mpr hvi
  obtain ⟨n, hn⟩ := exists_nat_gt ((K * ‖v‖ + ‖v‖) / (ε * T * |(M *ᵥ v) i|))
  have hb1 := hK n v
  rw [hpow n] at hb1
  have hlow : (n : ℝ) * (ε * T) * |(M *ᵥ v) i| - ‖v‖ ≤
      ‖((-1 : ℝ) ^ n • (1 + ((n : ℝ) * (ε * T)) • M)) *ᵥ v‖ := by
    have hcomp := norm_le_pi_norm (((-1 : ℝ) ^ n • (1 + ((n : ℝ) * (ε * T)) • M)) *ᵥ v) i
    rw [Real.norm_eq_abs] at hcomp
    have hvi' := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at hvi'
    have e : (((-1 : ℝ) ^ n • (1 + ((n : ℝ) * (ε * T)) • M)) *ᵥ v) i =
        (-1 : ℝ) ^ n * (v i + (n : ℝ) * (ε * T) * (M *ᵥ v) i) := by
      simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Pi.smul_apply,
        Pi.add_apply, smul_eq_mul]
    rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at hcomp
    have h1 := abs_add_le (v i + (n : ℝ) * (ε * T) * (M *ᵥ v) i) (-(v i))
    rw [show v i + (n : ℝ) * (ε * T) * (M *ᵥ v) i + -v i = (n : ℝ) * (ε * T) * (M *ᵥ v) i by ring,
      abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * (ε * T)), abs_neg] at h1
    linarith
  have hn' : K * ‖v‖ + ‖v‖ < (n : ℝ) * (ε * T * |(M *ᵥ v) i|) := by
    rwa [div_lt_iff₀ (by positivity)] at hn
  nlinarith

/-- **Damped, no anti-resonant pump, `b = 0`: exactly marginal.** For `s > 0` on the boundary with
`g' = 0` and `rotCoeff A = 0`, for every `ε > 0` the multipliers are exactly `−1` and
`−e^{−2sεT}`: the monodromy is neither Schur stable nor Floquet unstable. -/
@[tmio T, powerlib_foundation] theorem antiFree_marginal {s d ω : ℝ} (hω : 0 < ω)
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) (h : antiPump A = 0)
    (hrot : rotCoeff A = 0) {ε : ℝ} (hε : 0 < ε) :
    (-1 : ℂ) ∈ spectrum ℂ ((Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)) ∧
      (((-Real.exp (-2 * s * ε * (2 * Real.pi / ω)) : ℝ) : ℂ) ∈ spectrum ℂ
        ((Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ))) ∧
      ¬ LTI.SchurStable (Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0) ∧
      ¬ Periodic.FloquetUnstable (full s d ω A ε) (2 * Real.pi / ω) := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  set M := slowFlowMatrix s d (Element.pump A left right / 2) with hM
  set ρ := Real.exp (-2 * s * ε * T) with hρ
  set f := (1 - ρ) / (2 * s) with hf
  have hΦ := (antiFree_exact hω hb h hrot ε).2 hs
  have hdetM : M.det = 0 := by rw [hM, det_slowFlowMatrix, ← hb]; ring
  have htrM : M.trace = -2 * s := trace_slowFlowMatrix s d _
  have hfs : 1 - 2 * s * f = ρ := by rw [hf]; field_simp; ring
  set Φ := Periodic.monodromy (full s d ω A ε) T 0 with hΦdef
  have hΦ' : Φ = -(1 + f • M) := hΦ
  have htr : Φ.trace = -(1 + ρ) := by
    rw [hΦ', Matrix.trace_neg, Matrix.trace_add, Matrix.trace_one, Matrix.trace_smul, htrM,
      smul_eq_mul]
    simp
    linarith
  have hdet : Φ.det = ρ := by
    have e : (1 : Matrix (Fin 2) (Fin 2) ℝ) + f • M =
        (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + f • M := by rw [one_smul]
    rw [hΦ', Matrix.det_neg, Fintype.card_fin, e, Averaging.det_smul_one_add, Matrix.trace_smul,
      Matrix.det_smul, hdetM, htrM, smul_eq_mul]
    simp
    linarith
  have hroot : ∀ μ : ℂ, μ ∈ spectrum ℂ (Φ.map (algebraMap ℝ ℂ)) ↔ (μ + 1) * (μ + ρ) = 0 := by
    intro μ
    rw [Periodic.mem_spectrum_iff_root, htr, hdet]
    push_cast
    constructor <;> intro hμ <;> linear_combination hμ
  have hm1 : (-1 : ℂ) ∈ spectrum ℂ (Φ.map (algebraMap ℝ ℂ)) := by
    rw [hroot]; ring
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]; apply Real.exp_le_one_iff.mpr; nlinarith [mul_pos (mul_pos hs hε) hT]
  refine ⟨hm1, by rw [hroot]; push_cast; ring, ?_, ?_⟩
  · intro hS
    obtain ⟨v, hv, hμv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hm1
    have := hS (-1) v hv hμv
    simp at this
  · rintro ⟨μ, hμ, h1⟩
    rcases mul_eq_zero.mp ((hroot μ).mp hμ) with h0 | h0
    · rw [show μ = -1 by linear_combination h0] at h1; simp at h1
    · rw [show μ = -(ρ : ℂ) by linear_combination h0, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg hρ0.le] at h1
      linarith

/-- A modulation without anti-resonant pump: `A₁ = (g/2)(E₁ − jE₂) + b J` (pump `g`, anti-pump `0`,
rotational coefficient `b`). -/
def antiFreeModulation (g b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![g / 2, -b - I * (g / 2); b - I * (g / 2), -(g / 2)]

@[tmio T, powerlib_foundation] theorem antiFreeModulation_data (g b : ℂ) :
    Element.pump (antiFreeModulation g b) left right = g ∧
      antiPump (antiFreeModulation g b) = 0 ∧ rotCoeff (antiFreeModulation g b) = b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [TwoToOne.pump_base]; simp [antiFreeModulation]; ring_nf; simp [I_sq]; ring
  · rw [SecondOrder.antiPump_eq]; simp [antiFreeModulation]; ring_nf; simp [I_sq]
  · simp [rotCoeff, antiFreeModulation]

/-- **The second-order data do not decide the branch `g' = 0`.** For every boundary datum
`s ≥ 0`, `d`, `g ≠ 0` with `s² + d² = |g/2|²`, the modulations `A₁ = antiFreeModulation g 1` and
`A₀ = antiFreeModulation g 0` have the same slow flow (pump `g`), the same anti-resonant pump
`g' = 0` and hence the same second-order quantity `mixedDet(M, N₂) = 0`, but opposite verdicts
of the complete system `TwoToOne.full s d ω A ε`: for `s = 0`, `A₁` gives bounded solutions for
all small `ε > 0` and `A₀` unbounded ones for every `ε > 0`; for `s > 0`, `A₁` is Schur stable
for all small `ε > 0` and `A₀` is not Schur stable for any `ε > 0`. The deciding datum is the
rotational fundamental coefficient `b` (`K = 2T²|g/2|²|b|²/ω²`). -/
@[tmio T, powerlib_foundation] theorem antiFree_undecided {s d ω : ℝ} (hω : 0 < ω) {g : ℂ}
    (hs : 0 ≤ s) (hb : s ^ 2 + d ^ 2 = ‖g / 2‖ ^ 2) (hg : g ≠ 0) :
    Element.pump (antiFreeModulation g 1) left right =
        Element.pump (antiFreeModulation g 0) left right ∧
      antiPump (antiFreeModulation g 1) = antiPump (antiFreeModulation g 0) ∧
      (s = 0 → (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ K, ∀ t, 0 ≤ t → ∀ v : Fin 2 → ℝ,
          ‖Periodic.transition (full s d ω (antiFreeModulation g 1) ε) t 0 *ᵥ v‖ ≤ K * ‖v‖) ∧
        ∀ ε, 0 < ε → ¬ ∃ K, ∀ (n : ℕ) (v : Fin 2 → ℝ),
          ‖Periodic.transition (full s d ω (antiFreeModulation g 0) ε) (n * (2 * Real.pi / ω)) 0 *ᵥ
            v‖ ≤ K * ‖v‖) ∧
      (0 < s → (∀ᶠ ε in 𝓝[>] (0 : ℝ), LTI.SchurStable
          (Periodic.monodromy (full s d ω (antiFreeModulation g 1) ε) (2 * Real.pi / ω) 0)) ∧
        ∀ ε, 0 < ε → ¬ LTI.SchurStable
          (Periodic.monodromy (full s d ω (antiFreeModulation g 0) ε) (2 * Real.pi / ω) 0)) := by
  obtain ⟨p1, a1, r1⟩ := antiFreeModulation_data g 1
  obtain ⟨p0, a0, r0⟩ := antiFreeModulation_data g 0
  have hb1 : s ^ 2 + d ^ 2 = ‖Element.pump (antiFreeModulation g 1) left right / 2‖ ^ 2 := by
    rw [p1]; exact hb
  have hb0 : s ^ 2 + d ^ 2 = ‖Element.pump (antiFreeModulation g 0) left right / 2‖ ^ 2 := by
    rw [p0]; exact hb
  refine ⟨by rw [p1, p0], by rw [a1, a0], fun hs0 => ?_, fun hsp => ?_⟩
  · subst hs0
    have hd : d ≠ 0 := by
      intro hd0
      rw [hd0] at hb
      have : ‖g / 2‖ = 0 := by nlinarith [norm_nonneg (g / 2)]
      exact hg (by simpa using this)
    refine ⟨?_, fun ε hε => zero_damping_antiFree_unbounded hω (by rw [← hb0]; ring) hd a0 r0 hε⟩
    filter_upwards [zero_damping_antiFree_marginal hω (by rw [← hb1]; ring) hd a1
      (by rw [r1]; exact one_ne_zero)] with ε hε
    exact hε.2.2.2.1
  · exact ⟨antiFree_stable hω hsp hb1 a1 (by rw [r1]; exact one_ne_zero),
      fun ε hε => (antiFree_marginal hω hsp hb0 a0 r0 hε).2.2.1⟩

end AntiFree

end powerlib.ParametricResonance.ThirdOrder
