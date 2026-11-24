import theorem.GridTiedConverter.GFM.Line.VSM
import theorem.GridTiedConverter.GFM.VSMLPFLossy

/-! # The VSM with a power filter on a dynamic line, and the filter as a second time scale

The five-state VSM + power filter (droop + LPF) of
`theorem/GridTiedConverter/GFM/Line/Model.lean`: its characteristic polynomial from the
`fderiv` Jacobian, the sum and product rules against the reduced three-state model, and the
quasi-static reduction read as the lossy three-state model `GFM.VSMLPFLossy`
(`theorem/GridTiedConverter/GFM/VSMLPFLossy.lean`). Then the power filter of the reduced model
as a second time scale: the values of the reduced characteristic cubic at `−ω_c`, `−D/M` and
`−(ω_c + D/M)`, and the location of its real root.

Scope.
* Model boundary of `theorem/GridTiedConverter/GFM/Line/Model.lean`: state
  `(δ, ω, P_f, i_d, i_q) : State 5`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  R–L line; `Q = Q(δ*)`, `K = P'(δ*)`, `σ = R/L`, `ρ = σ² + (X/L)²`. The reduced model is the
  three-state `GFM.VSMLPF` of `theorem/GridTiedConverter/GFM/VSMLPF.lean` (lossless line) with
  `K = K₀ cos δ`.
* Level: static evidence on the models (characteristic polynomials, Jacobian invariants,
  reduction identities, real roots); no family is defined. The exact stability boundary of the
  five-state model is a quintic Routh condition, not stated here.

Source: study note `gfm/t4-timescale/REPORT.md` ("Exact linear structure", (d)) and its scripts
`t4_02_charpoly.py`, `t4_06_lpf_boundary.py`, `t4_07_filter_timescale.py` (discovery evidence
only).

Results.
* `VSMLPF.det_characteristicMatrix`, `VSMLPF.characteristic_polynomial`: at every state
  `M det(sI − J) = (M s³ + (D + M ω_c) s² + D ω_c s − ω_c Q_e)(s² + 2σ s + ρ) + ω_c E² X/L²`.
* Sum and product rules (`VSMLPF.Model.trace_jac`, `VSMLPF.Model.det_jac`): the trace and the
  determinant of the five-state Jacobian at the operating point are those of the reduced
  three-state Jacobian (`GFM.VSMLPF.jacobian` of the lossless parameters at `δ* − α`) and of the
  uncoupled line block, added and multiplied.
* `VSMLPF.reducedField_eq_lossy`: the slow rows on the quasi-steady set are the lossy three-state
  field `GFM.VSMLPFLossy ⟨M, D, ω_c, P_ref, c₀, A, α⟩` (lossless line:
  `VSMLPF.reducedField_eq_vsmlpf` of the model module).
* Filter limits of the reduced model (`filter_charPoly_values`):
  `p(−ω_c) = p(−D/M) = ω_c K`, `p(−(ω_c + D/M)) = ω_c (K − D ω_c − D²/M)` for
  `p(s) = M det(sI − J)`; hence (`filter_real_root`) for `M, D, ω_c, K > 0` and the stable side
  `K < D ω_c + D²/M` the cubic has a real root `λ ∈ (−(ω_c + D/M), −max(ω_c, D/M))` (faster than
  both limits) and the complementary pair has real-part sum `−b` with `0 < b < min(ω_c, D/M)`:
  the slow pair is less damped than both limits (swing `ω_c → ∞`, droop + LPF `M → 0`).
-/

noncomputable section
namespace powerlib.GFM.Line
open powerlib.Dynamics (State)
open Set

namespace VSMLPF

variable (g : VSMLPF)

/-! ## The five-state characteristic polynomial -/

/-- The monic characteristic polynomial of the Jacobian at any state, in product form. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix (δ id iq : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (g.jacobian δ id iq) s).det =
      (s ^ 3 + ((g.D / g.M + g.ωc : ℝ) : ℂ) * s ^ 2 + ((g.D * g.ωc / g.M : ℝ) : ℂ) * s -
          ((g.ωc * g.reactive δ id iq / g.M : ℝ) : ℂ)) *
        (s ^ 2 + ((2 * g.σ : ℝ) : ℂ) * s + (g.ρ : ℂ)) +
          ((g.ωc * g.E ^ 2 * g.X / (g.L ^ 2 * g.M) : ℝ) : ℂ) := by
  simp only [Linear.characteristicMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  simp [jacobian, Linear.complexify, Fin.succAbove, Fin.lt_def, Network.ρ,
    Network.σ]
  linear_combination ((g.ωc : ℂ) * (g.E : ℂ) ^ 2 * (g.X : ℂ) / ((g.L : ℂ) ^ 2 * (g.M : ℂ))) *
    Complex.sin_sq_add_cos_sq (δ : ℂ)

/-- **Characteristic polynomial**: at every state
`M det(sI − J) = (M s³ + (D + M ω_c) s² + D ω_c s − ω_c Q_e)(s² + 2σ s + ρ) + ω_c E² X/L²`. -/
@[tmio M, powerlib_domain] theorem characteristic_polynomial (hM : g.M ≠ 0) (δ id iq : ℝ)
    (s : ℂ) :
    (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ id iq) s).det =
      ((g.M : ℂ) * s ^ 3 + ((g.D + g.M * g.ωc : ℝ) : ℂ) * s ^ 2 + ((g.D * g.ωc : ℝ) : ℂ) * s -
          ((g.ωc * g.reactive δ id iq : ℝ) : ℂ)) *
        (s ^ 2 + ((2 * g.σ : ℝ) : ℂ) * s + (g.ρ : ℂ)) +
          ((g.ωc * g.E ^ 2 * g.X / g.L ^ 2 : ℝ) : ℂ) := by
  rw [det_characteristicMatrix]
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  push_cast
  field_simp

@[tmio M, powerlib_domain] private theorem trace_jacobian (δ id iq : ℝ) :
    (g.jacobian δ id iq).trace = -(g.D / g.M + g.ωc) - 2 * g.σ := by
  simp [jacobian, Matrix.trace, Fin.sum_univ_five, Network.σ]; ring

@[tmio M, powerlib_domain] private theorem det_jacobian (δ id iq : ℝ) :
    (g.jacobian δ id iq).det =
      -((g.ωc * g.E ^ 2 * g.X / (g.L ^ 2 * g.M)) - g.ωc * g.reactive δ id iq / g.M * g.ρ) := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply]
  simp [jacobian, Fin.succAbove, Fin.lt_def, Network.ρ, Network.σ]
  linear_combination (-(g.ωc * g.E ^ 2 * g.X / (g.L ^ 2 * g.M))) * Real.sin_sq_add_cos_sq δ

/-! ## Models at the operating point -/

/-- The lossy three-state parameters of the quasi-static reduction. -/
def toLossy : powerlib.GFM.VSMLPFLossy := ⟨g.M, g.D, g.ωc, g.Pref, g.c0, g.A, g.α⟩

/-- **Quasi-static reduction**: the slow rows on the quasi-steady set are the lossy three-state
field `GFM.VSMLPFLossy ⟨M, D, ω_c, P_ref, c₀, A, α⟩`. -/
@[tmio M, powerlib_domain] theorem reducedField_eq_lossy (hZ : 0 < g.absSq) :
    g.reducedField = g.toLossy.field := by
  funext y
  ext i
  fin_cases i
  · simp [reducedField, qss, powerlib.GFM.VSMLPFLossy.field, toLossy]
  · simp [reducedField, qss, powerlib.GFM.VSMLPFLossy.field, toLossy]
  · have hP := g.qssPower_eq_polar hZ (y 0)
    show g.ωc * (g.power (y 0) (g.is (y 0)).re (g.is (y 0)).im - y 2) =
      g.ωc * (g.c0 + g.A * Real.sin (y 0 - g.α) - y 2)
    rw [← hP]; rfl

/-- The Jacobian at the operating point `(δ*, 0, P_ref, i_s(δ*))`. -/
def Model.jac (m : Model) : Matrix (Fin 5) (Fin 5) ℝ :=
  m.g.jacobian m.δ (m.g.is m.δ).re (m.g.is m.δ).im

/-- The reduced three-state Jacobian: the lossless `GFM.VSMLPF` Jacobian of the reading of the
lossy model at `δ* − α`. -/
def Model.reducedJac (m : Model) : Matrix (Fin 3) (Fin 3) ℝ :=
  m.g.toLossy.toVSMLPF.jacobian (m.δ - m.g.α)

/-- **Sum rule**: `tr J = tr J_reduced + tr J_line`. -/
@[tmio M, powerlib_domain] theorem Model.trace_jac (m : Model) :
    m.jac.trace = m.reducedJac.trace + m.g.lineJacobian.trace := by
  rw [Model.jac, trace_jacobian, Model.reducedJac, powerlib.GFM.VSMLPF.trace_jacobian,
    Network.trace_lineJacobian]
  simp [toLossy, powerlib.GFM.VSMLPFLossy.toVSMLPF]; ring

/-- **Product rule**: `det J = det J_reduced · det J_line` (`L ≠ 0`, `|Z|² > 0`). -/
@[tmio M, powerlib_domain] theorem Model.det_jac (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    m.jac.det = m.reducedJac.det * m.g.lineJacobian.det := by
  have h1 := m.g.syncCoeff_add_qssReactive hZ m.δ
  have h2 := m.g.κ_mul_ρ hL hZ.ne'
  rw [Model.jac, det_jacobian, Model.reducedJac, powerlib.GFM.VSMLPF.det_jacobian,
    Network.det_lineJacobian]
  simp only [toLossy, powerlib.GFM.VSMLPFLossy.toVSMLPF]
  have hK : m.g.A * Real.cos (m.δ - m.g.α) = m.g.κ - m.g.qssReactive m.δ := by
    rw [← h1, Network.syncCoeff]; ring
  change _ = -(m.g.ωc * (m.g.A * Real.cos (m.δ - m.g.α))) / m.g.M * m.g.ρ
  rw [hK, show m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.g.qssReactive m.δ from rfl]
  have e : m.g.ωc * m.g.E ^ 2 * m.g.X / (m.g.L ^ 2 * m.g.M) = m.g.ωc * (m.g.κ * m.g.ρ) / m.g.M :=
    by rw [h2]; ring
  rw [e]; ring

end VSMLPF

/-! ## The power filter as a second time scale (reduced three-state model) -/

/-- **Filter limits**: for `p(s) = M det(sI − J)` of the three-state VSM + power filter at angle
`δ`, `K = K₀ cos δ`: `p(−ω_c) = ω_c K`, `p(−D/M) = ω_c K` and
`p(−(ω_c + D/M)) = ω_c (K − D ω_c − D²/M)`. -/
@[tmio M, powerlib_domain] theorem filter_charPoly_values (g : powerlib.GFM.VSMLPF)
    (hM : g.M ≠ 0) (δ : ℝ) :
    (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ) (-(g.ωc : ℂ))).det =
        ((g.ωc * (g.K0 * Real.cos δ) : ℝ) : ℂ) ∧
      (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ) (-((g.D / g.M : ℝ) : ℂ))).det =
        ((g.ωc * (g.K0 * Real.cos δ) : ℝ) : ℂ) ∧
      (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ)
          (-((g.ωc + g.D / g.M : ℝ) : ℂ))).det =
        ((g.ωc * (g.K0 * Real.cos δ - g.D * g.ωc - g.D ^ 2 / g.M) : ℝ) : ℂ) := by
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  refine ⟨?_, ?_, ?_⟩ <;> rw [g.characteristic_polynomial hM] <;> push_cast <;> field_simp <;>
    ring

/-- **Real root of the reduced model on the stable side**: for `M, D, ω_c > 0`, `K > 0` and
`K < D ω_c + D²/M`, the characteristic polynomial of the three-state VSM + power filter has a
real root `λ ∈ (−(ω_c + D/M), −max(ω_c, D/M))`, and the complementary quadratic
`s² + b s + c` has `0 < b < min(ω_c, D/M)` (the real-part sum `−b` of the slow pair lies in
`(−min(ω_c, D/M), 0)`). -/
@[tmio M, powerlib_domain] theorem filter_real_root (g : powerlib.GFM.VSMLPF) (hM : 0 < g.M)
    (hD : 0 < g.D) (hω : 0 < g.ωc) (δ : ℝ) (hK : 0 < g.K0 * Real.cos δ)
    (hs : g.K0 * Real.cos δ < g.D * g.ωc + g.D ^ 2 / g.M) :
    ∃ l : ℝ, l ∈ Ioo (-(g.ωc + g.D / g.M)) (-max g.ωc (g.D / g.M)) ∧
      ∃ b c : ℝ, 0 < b ∧ b < min g.ωc (g.D / g.M) ∧
        ∀ s : ℂ, (Linear.characteristicMatrix (g.jacobian δ) s).det =
          (s - l) * (s ^ 2 + (b : ℂ) * s + (c : ℂ)) := by
  set K := g.K0 * Real.cos δ with hKdef
  set a2 := g.D / g.M + g.ωc
  set a1 := g.D * g.ωc / g.M
  set a0 := g.ωc * K / g.M
  have hmonic : ∀ s : ℂ, (Linear.characteristicMatrix (g.jacobian δ) s).det =
      s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) := by
    intro s
    have h := g.characteristic_polynomial hM.ne' δ s
    have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    apply mul_left_cancel₀ hM'
    rw [h]; simp only [a2, a1, a0, hKdef]; push_cast; field_simp
  set f : ℝ → ℝ := fun x => x ^ 3 + a2 * x ^ 2 + a1 * x + a0 with hf
  have hDM : 0 < g.D / g.M := div_pos hD hM
  have hlo : f (-(g.ωc + g.D / g.M)) < 0 := by
    have e : f (-(g.ωc + g.D / g.M)) = g.ωc * (K - g.D * g.ωc - g.D ^ 2 / g.M) / g.M := by
      simp only [hf, a2, a1, a0]; field_simp; ring
    rw [e]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hω (by linarith)) hM
  have hhi : 0 < f (-max g.ωc (g.D / g.M)) := by
    have e1 : f (-g.ωc) = g.ωc * K / g.M := by simp only [hf, a2, a1, a0]; field_simp; ring
    have e2 : f (-(g.D / g.M)) = g.ωc * K / g.M := by
      simp only [hf, a2, a1, a0]; field_simp; ring
    rcases le_total g.ωc (g.D / g.M) with h | h
    · rw [max_eq_right h, e2]; positivity
    · rw [max_eq_left h, e1]; positivity
  have hab : -(g.ωc + g.D / g.M) ≤ -max g.ωc (g.D / g.M) := by
    rcases le_total g.ωc (g.D / g.M) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hcont : ContinuousOn f (Icc (-(g.ωc + g.D / g.M)) (-max g.ωc (g.D / g.M))) := by
    apply Continuous.continuousOn; simp only [hf]; fun_prop
  obtain ⟨l, hl, hfl⟩ := intermediate_value_Ioo hab hcont ⟨hlo, hhi⟩
  refine ⟨l, hl, a2 + l, a1 + l * a2 + l ^ 2, ?_, ?_, fun s => ?_⟩
  · have := hl.1; simp only [a2]; linarith
  · have := hl.2
    rcases le_total g.ωc (g.D / g.M) with h | h
    · rw [max_eq_right h] at this; rw [min_eq_left h]; simp only [a2]; linarith
    · rw [max_eq_left h] at this; rw [min_eq_right h]; simp only [a2]; linarith
  · rw [hmonic, Criteria.cubic_factor_of_root hfl s]

end powerlib.GFM.Line
