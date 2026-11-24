import theorem.WPT.Bifurcation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Parity–time symmetric power transfer: balanced gain and loss

The coil pair of an inductive link with a gain element (a negative resistance) in the primary that
exactly balances the loss of the secondary (its winding and the load): the parity–time (PT)
symmetric configuration of robust wireless power transfer. A free oscillation of the link is a
nonzero current pair solving its phasor equations without a source. In every such oscillation of
two coils with equal reactances the two currents have equal amplitude, so the gain element
delivers exactly the power the secondary dissipates and the load receives the fraction
`R_L/(R₂ + R_L)` of it — independent of the coupling and of the frequency. For two identical coils
tuned at `ω₀`, a free oscillation at a real frequency exists (the unbroken PT phase) **iff**
`γ² < 2` and `k² ≥ γ² − γ⁴/4`, with `γ = (R₂ + R_L)/(ω₀ L)` and `k = M/L`; the boundary is the
exceptional point. In normalized frequency its frequencies are the positive roots `u²` of the
quadratic of the zero-phase-angle frequencies of the series–series link
(`theorem/WPT/Bifurcation.lean`) with `x = γ²`.

Model boundary.
* The coil pair `w : Passive.Coupled` (boundary of `theorem/Passive/Coupled.lean`), the secondary
  terminated by the load `R_L`, one real angular frequency `ω`, RMS phasors in sinusoidal steady
  state. Balanced gain and loss: the primary resistance is `R₁ = −(R₂ + R_L)`, a linear negative
  resistance (`PT` hypotheses `hPT`).
* The nonlinear saturable gain (amplifier or nonlinear resistor) that selects the oscillation and
  balances gain and loss in a physical system is not modelled here; the statements are about the
  balanced linear circuit and its free oscillations (its realization by a bridge switching in
  phase with its current is in `theorem/WPT/PTGain.lean`). No transients, stability of the oscillation,
  harmonics or source.
* Equal reactances `X₁(ω) = X₂(ω)` for the amplitude and efficiency statements; identical coils
  `L₁ = L₂ = L` tuned at `ω₀ > 0` (`tunedCoils`) for the existence statement.

Source: parity–time symmetric robust wireless power transfer with a saturable gain element
(Assawaworrarit, Yu and Fan, *Nature* 546 (2017) 387–390); the eigenvalue condition of a pair of
coupled resonators with balanced gain and loss; Mathlib `Matrix.exists_mulVec_eq_zero_iff` (a
nonzero solution exists iff the determinant vanishes).

Results.
* `Oscillates` (the link `⟨w, R_L, ω⟩` of `theorem/WPT/Link.lean` solving its equations with zero
  source voltage), `loadedMatrix` (`Z(jω) + diag(0, R_L)`), `oscillates_iff_mulVec`,
  `exists_oscillation_iff_det` (a free oscillation exists iff `det = 0`).
* `normSq_eq` (balanced gain and loss, equal reactances, `ωM ≠ 0`: `|I₁|² = |I₂|²`),
  `gainPower_eq` (the gain power `(R₂ + R_L)|I₁|²` is the power dissipated in the secondary),
  `transferRatio_eq` (the load receives `R_L/(R₂ + R_L)` of the gain power, for every coupling and
  frequency).
* `det_loadedMatrix` (balanced gain and loss, equal reactances:
  `det = (ωM)² − (R₂ + R_L)² − X²`), `exists_pos_root_iff` (the quadratic
  `(1 − c) w² − (2 − x) w + 1`, `0 < c < 1`, has a positive root iff `x < 2` and `x − x²/4 ≤ c`),
  `exists_oscillation_iff` (the unbroken phase of identical tuned coils).
-/

noncomputable section

namespace powerlib.WPT.PT

open Complex Matrix

/-- A free oscillation: the link `⟨w, R_L, ω⟩` solves its phasor equations with zero source
voltage. -/
def Oscillates (w : Passive.Coupled) (RL ω : ℝ) (I₁ I₂ : ℂ) : Prop :=
  (⟨w, RL, ω⟩ : Link).Solves 0 I₁ I₂

/-- The loaded impedance matrix `Z(jω) + diag(0, R_L)`. -/
def loadedMatrix (w : Passive.Coupled) (RL ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  w.impedanceMatrix (ω * I) + !![0, 0; 0, (RL : ℂ)]

/-- A free oscillation is a null vector of the loaded impedance matrix. -/
@[tmio M, powerlib_domain] theorem oscillates_iff_mulVec (w : Passive.Coupled) (RL ω : ℝ)
    (I₁ I₂ : ℂ) : Oscillates w RL ω I₁ I₂ ↔ loadedMatrix w RL ω *ᵥ ![I₁, I₂] = 0 := by
  rw [Oscillates, Link.solves_iff]
  simp only [loadedMatrix, Passive.Coupled.impedanceMatrix, Matrix.add_mulVec, funext_iff,
    Fin.forall_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Pi.add_apply, Pi.zero_apply, Link.Z₁, Link.Z₂,
    Link.mutualReactance]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination -h1, by linear_combination -h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination -h1, by linear_combination -h2⟩

/-- A free oscillation exists exactly when the loaded impedance matrix is singular
(Mathlib `Matrix.exists_mulVec_eq_zero_iff`). -/
@[tmio M, powerlib_domain] theorem exists_oscillation_iff_det (w : Passive.Coupled) (RL ω : ℝ) :
    (∃ I₁ I₂ : ℂ, (I₁ ≠ 0 ∨ I₂ ≠ 0) ∧ Oscillates w RL ω I₁ I₂) ↔
      (loadedMatrix w RL ω).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨I₁, I₂, hne, h⟩
    refine ⟨![I₁, I₂], fun h0 => ?_, (oscillates_iff_mulVec w RL ω I₁ I₂).mp h⟩
    rcases hne with h' | h'
    · exact h' (by simpa using congrFun h0 0)
    · exact h' (by simpa using congrFun h0 1)
  · rintro ⟨v, hv, h⟩
    refine ⟨v 0, v 1, ?_, ?_⟩
    · by_contra hc
      obtain ⟨h0, h1⟩ := not_or.mp hc
      apply hv
      funext i
      fin_cases i
      exacts [not_not.mp h0, not_not.mp h1]
    · rw [oscillates_iff_mulVec]
      convert h using 2
      funext i
      fin_cases i <;> rfl

/-- Balanced gain and loss with equal reactances: in every free oscillation the two currents have
equal amplitude, `|I₁|² = |I₂|²` (`ωM ≠ 0`). -/
@[tmio M, powerlib_domain] theorem normSq_eq {w : Passive.Coupled} {RL ω : ℝ} {I₁ I₂ : ℂ}
    (hPT : w.primary.R = -(w.secondary.R + RL))
    (hX : w.primary.reactance ω = w.secondary.reactance ω) (hm : ω * w.M ≠ 0)
    (h : Oscillates w RL ω I₁ I₂) : normSq I₁ = normSq I₂ := by
  rw [Oscillates, Link.solves_iff] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Link.Z₁, Link.Z₂, Link.mutualReactance, Passive.SeriesRLC.impedance_jω, hPT, hX]
    at h1 h2
  have e1 : (((-(w.secondary.R + RL) : ℝ) : ℂ) + (w.secondary.reactance ω : ℂ) * I) * I₁ =
      -(((ω * w.M : ℝ) : ℂ) * I₂ * I) := by
    linear_combination -h1
  have e2 : (((w.secondary.R + RL : ℝ) : ℂ) + (w.secondary.reactance ω : ℂ) * I) * I₂ =
      -(((ω * w.M : ℝ) : ℂ) * I₁ * I) := by
    push_cast at h2 ⊢
    linear_combination -h2
  have n1 := congrArg normSq e1
  have n2 := congrArg normSq e2
  simp only [normSq_mul, normSq_add_mul_I, normSq_neg, normSq_ofReal, normSq_I, mul_one] at n1 n2
  have hm2 : 0 < (ω * w.M) * (ω * w.M) := mul_self_pos.mpr hm
  have key : ((w.secondary.R + RL) ^ 2 + w.secondary.reactance ω ^ 2 + (ω * w.M) * (ω * w.M)) *
      (normSq I₁ - normSq I₂) = 0 := by
    linear_combination n1 - n2
  have hpos : 0 < (w.secondary.R + RL) ^ 2 + w.secondary.reactance ω ^ 2 +
      (ω * w.M) * (ω * w.M) := by positivity
  linarith [(mul_eq_zero.mp key).resolve_left hpos.ne']

/-- The gain element supplies exactly the power the secondary dissipates:
`−R₁ |I₁|² = (R₂ + R_L) |I₂|²`. -/
@[tmio M, powerlib_domain] theorem gainPower_eq {w : Passive.Coupled} {RL ω : ℝ} {I₁ I₂ : ℂ}
    (hPT : w.primary.R = -(w.secondary.R + RL))
    (hX : w.primary.reactance ω = w.secondary.reactance ω) (hm : ω * w.M ≠ 0)
    (h : Oscillates w RL ω I₁ I₂) :
    -w.primary.R * normSq I₁ = (w.secondary.R + RL) * normSq I₂ := by
  rw [hPT, neg_neg, normSq_eq hPT hX hm h]

/-- The load receives the fraction `R_L/(R₂ + R_L)` of the gain power, for every coupling and every
frequency of oscillation (`I₂ ≠ 0`). -/
@[tmio M, powerlib_domain] theorem transferRatio_eq {w : Passive.Coupled} {RL ω : ℝ} {I₁ I₂ : ℂ}
    (hPT : w.primary.R = -(w.secondary.R + RL))
    (hX : w.primary.reactance ω = w.secondary.reactance ω) (hm : ω * w.M ≠ 0)
    (h : Oscillates w RL ω I₁ I₂) (hI₂ : I₂ ≠ 0) :
    RL * normSq I₂ / (-w.primary.R * normSq I₁) = RL / (w.secondary.R + RL) := by
  rw [hPT, neg_neg, normSq_eq hPT hX hm h,
    mul_div_mul_right _ _ (normSq_pos.mpr hI₂).ne']

/-- Balanced gain and loss with equal reactances: `det(Z(jω) + diag(0, R_L)) =
(ωM)² − (R₂ + R_L)² − X²`. -/
@[tmio M, powerlib_domain] theorem det_loadedMatrix {w : Passive.Coupled} {RL ω : ℝ}
    (hPT : w.primary.R = -(w.secondary.R + RL))
    (hX : w.primary.reactance ω = w.secondary.reactance ω) :
    (loadedMatrix w RL ω).det = (((ω * w.M) ^ 2 - (w.secondary.R + RL) ^ 2 -
      w.secondary.reactance ω ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [loadedMatrix, Passive.Coupled.impedanceMatrix, Matrix.add_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Passive.SeriesRLC.impedance_jω, hPT, hX]
  push_cast
  linear_combination ((w.secondary.reactance ω : ℂ) ^ 2 - (w.M : ℂ) ^ 2 * (ω : ℂ) ^ 2) * I_sq

/-- The quadratic `(1 − c) w² − (2 − x) w + 1` with `0 < c < 1` has a positive root **iff**
`x < 2` and `x − x²/4 ≤ c` (by `exists_root_iff` for the converse). -/
@[tmio T, powerlib_foundation] theorem exists_pos_root_iff {c x : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    (∃ v : ℝ, 0 < v ∧ (1 - c) * v ^ 2 - (2 - x) * v + 1 = 0) ↔ x < 2 ∧ x - x ^ 2 / 4 ≤ c := by
  constructor
  · rintro ⟨v, hv, hf⟩
    have ha : 0 < 1 - c := by linarith
    refine ⟨?_, ?_⟩
    · nlinarith [sq_nonneg v, mul_pos ha (pow_pos hv 2)]
    · nlinarith [sq_nonneg (2 * (1 - c) * v - (2 - x))]
  · intro h
    obtain ⟨v, hv, -, hf⟩ := (exists_root_iff hc0 hc1).mpr h
    exact ⟨v, hv, hf⟩

/-- The unbroken PT phase: two identical coils tuned at `ω₀ > 0` with balanced gain and loss have a
free oscillation at a real frequency **iff** `γ² < 2` and `γ² − γ⁴/4 ≤ k²`, with
`γ = (R₂ + R_L)/(ω₀ L)` and `k² = M²/L²`. -/
@[tmio M, powerlib_domain] theorem exists_oscillation_iff (w : Passive.Coupled) {RL ω₀ : ℝ}
    (hω₀ : 0 < ω₀) (hL : 0 < w.primary.L) (hLL : w.secondary.L = w.primary.L)
    (hPT : w.primary.R = -(w.secondary.R + RL)) (hM : w.M ≠ 0)
    (hk : w.M ^ 2 < w.primary.L ^ 2) :
    (∃ ω, 0 < ω ∧ ∃ I₁ I₂ : ℂ, (I₁ ≠ 0 ∨ I₂ ≠ 0) ∧ Oscillates (tunedCoils w ω₀) RL ω I₁ I₂) ↔
      ((w.secondary.R + RL) / (ω₀ * w.primary.L)) ^ 2 < 2 ∧
        ((w.secondary.R + RL) / (ω₀ * w.primary.L)) ^ 2 -
            (((w.secondary.R + RL) / (ω₀ * w.primary.L)) ^ 2) ^ 2 / 4 ≤
          w.M ^ 2 / w.primary.L ^ 2 := by
  have hL2 : 0 < w.primary.L ^ 2 := by positivity
  have hc0 : 0 < w.M ^ 2 / w.primary.L ^ 2 := div_pos (by positivity) hL2
  have hc1 : w.M ^ 2 / w.primary.L ^ 2 < 1 := (div_lt_one hL2).mpr hk
  rw [← exists_pos_root_iff hc0 hc1]
  -- the oscillation condition at a positive frequency, in the normalized frequency
  have hosc : ∀ ω, 0 < ω → ((∃ I₁ I₂ : ℂ, (I₁ ≠ 0 ∨ I₂ ≠ 0) ∧
      Oscillates (tunedCoils w ω₀) RL ω I₁ I₂) ↔
      (1 - w.M ^ 2 / w.primary.L ^ 2) * ((ω / ω₀) ^ 2) ^ 2 -
        (2 - ((w.secondary.R + RL) / (ω₀ * w.primary.L)) ^ 2) * (ω / ω₀) ^ 2 + 1 = 0) := by
    intro ω hω
    have hX : (tunedCoils w ω₀).primary.reactance ω = (tunedCoils w ω₀).secondary.reactance ω := by
      simp [tunedCoils, tunedElastance, Passive.SeriesRLC.reactance, hLL]
    have hX2 : (tunedCoils w ω₀).secondary.reactance ω =
        w.primary.L * (ω ^ 2 - ω₀ ^ 2) / ω := by
      simp only [tunedCoils, tunedElastance, Passive.SeriesRLC.reactance, hLL]
      field_simp
    rw [exists_oscillation_iff_det, det_loadedMatrix (w := tunedCoils w ω₀) hPT hX, hX2,
      Complex.ofReal_eq_zero]
    have hfac : (ω * w.M) ^ 2 - ((tunedCoils w ω₀).secondary.R + RL) ^ 2 -
        (w.primary.L * (ω ^ 2 - ω₀ ^ 2) / ω) ^ 2 =
        -(w.primary.L ^ 2 * ω₀ ^ 4 / ω ^ 2) *
          ((1 - w.M ^ 2 / w.primary.L ^ 2) * ((ω / ω₀) ^ 2) ^ 2 -
            (2 - ((w.secondary.R + RL) / (ω₀ * w.primary.L)) ^ 2) * (ω / ω₀) ^ 2 + 1) := by
      simp only [tunedCoils, tunedElastance]
      field_simp
      ring
    have hK : -(w.primary.L ^ 2 * ω₀ ^ 4 / ω ^ 2) ≠ 0 := by
      have : 0 < w.primary.L ^ 2 * ω₀ ^ 4 / ω ^ 2 := by positivity
      linarith
    have hM' : (tunedCoils w ω₀).M = w.M := rfl
    rw [hM', hfac, mul_eq_zero, or_iff_right hK]
  constructor
  · rintro ⟨ω, hω, hex⟩
    exact ⟨(ω / ω₀) ^ 2, by positivity, (hosc ω hω).mp hex⟩
  · rintro ⟨v, hv, hf⟩
    have hω : 0 < Real.sqrt v * ω₀ := by positivity
    refine ⟨Real.sqrt v * ω₀, hω, (hosc _ hω).mpr ?_⟩
    rw [mul_div_assoc, div_self hω₀.ne', mul_one, Real.sq_sqrt hv.le]
    exact hf

end powerlib.WPT.PT
