import Powerlib.SmallSignal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The averaged conjugate-mode envelope

This file proves statements about the specified two-dimensional averaged model.
It makes no approximation claim about the original nonlinear or periodic system.
The spectral results use no domain axiom. Only the final translation from
`Hurwitz` to `SmallSignalStable` uses the existing linear spectral criterion.
-/

noncomputable section

namespace Powerlib.Parametric

/-- Real coordinates of `c' = (-σ + i Δ)c + (ε/2)g conj(c)`. -/
def envelopeMatrix (σ Δ ε : ℝ) (g : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-σ + ε * g.re / 2, -Δ + ε * g.im / 2;
      Δ + ε * g.im / 2, -σ - ε * g.re / 2]

/-- The determinant margin of the envelope matrix. -/
def envelopeMargin (σ Δ ε : ℝ) (g : ℂ) : ℝ :=
  σ ^ 2 + Δ ^ 2 - ε ^ 2 * Complex.normSq g / 4

theorem envelope_det (σ Δ ε : ℝ) (g : ℂ) :
    (envelopeMatrix σ Δ ε g).det = envelopeMargin σ Δ ε g := by
  simp [envelopeMatrix, Matrix.det_fin_two, envelopeMargin, Complex.normSq_apply]
  <;> ring

/-- An evaluation formula for the actual characteristic polynomial over `ℂ`. -/
theorem envelope_eval_charpoly (σ Δ ε : ℝ) (g z : ℂ) :
    ((envelopeMatrix σ Δ ε g).map (algebraMap ℝ ℂ)).charpoly.eval z =
      z ^ 2 + (2 * σ : ℝ) * z + (envelopeMargin σ Δ ε g : ℂ) := by
  simp [Matrix.eval_charpoly, Matrix.det_fin_two, envelopeMatrix,
    Matrix.scalar, Matrix.diagonal, Matrix.map, envelopeMargin, Complex.normSq_apply]
  <;> push_cast
  <;> ring

theorem envelope_eigenvalue_iff (σ Δ ε : ℝ) (g z : ℂ) :
    HasEigenvalue (envelopeMatrix σ Δ ε g) z ↔
      z ^ 2 + (2 * σ : ℝ) * z + (envelopeMargin σ Δ ε g : ℂ) = 0 := by
  unfold HasEigenvalue
  rw [envelope_eval_charpoly]

/-- The principal square root of a real discriminant, represented in `ℂ`. -/
def realDiscriminantRoot (d : ℝ) : ℂ :=
  if 0 ≤ d then (Real.sqrt d : ℂ) else (Real.sqrt (-d) : ℂ) * Complex.I

theorem realDiscriminantRoot_sq (d : ℝ) :
    realDiscriminantRoot d ^ 2 = (d : ℂ) := by
  unfold realDiscriminantRoot
  split_ifs with hd
  · exact_mod_cast Real.sq_sqrt hd
  · have hn : 0 ≤ -d := by linarith [le_of_not_ge hd]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hn]
    push_cast
    ring

/-- The two envelope eigenvalues, including the imaginary-discriminant case. -/
theorem envelope_eigenvalues (σ Δ ε : ℝ) (g z : ℂ) :
    HasEigenvalue (envelopeMatrix σ Δ ε g) z ↔
      z = -(σ : ℂ) + realDiscriminantRoot (ε ^ 2 * Complex.normSq g / 4 - Δ ^ 2) ∨
      z = -(σ : ℂ) - realDiscriminantRoot (ε ^ 2 * Complex.normSq g / 4 - Δ ^ 2) := by
  rw [envelope_eigenvalue_iff]
  have hfactor :
      z ^ 2 + (2 * σ : ℝ) * z + (envelopeMargin σ Δ ε g : ℂ) =
        (z - (-(σ : ℂ) + realDiscriminantRoot
          (ε ^ 2 * Complex.normSq g / 4 - Δ ^ 2))) *
        (z - (-(σ : ℂ) - realDiscriminantRoot
          (ε ^ 2 * Complex.normSq g / 4 - Δ ^ 2))) := by
    calc
      _ = (z + (σ : ℂ)) ^ 2 -
          realDiscriminantRoot (ε ^ 2 * Complex.normSq g / 4 - Δ ^ 2) ^ 2 := by
        rw [realDiscriminantRoot_sq]
        unfold envelopeMargin
        push_cast
        ring
      _ = _ := by ring
  rw [hfactor, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- The real matrix agrees with the real and imaginary components of the
complex amplitude equation; conjugation is retained in the semantics. -/
theorem envelope_complex_coordinates (σ Δ ε : ℝ) (g c : ℂ) :
    (envelopeMatrix σ Δ ε g).mulVec ![c.re, c.im] =
      ![((-(σ : ℂ) + Complex.I * Δ) * c + (ε : ℂ) / 2 * g * star c).re,
        ((-(σ : ℂ) + Complex.I * Δ) * c + (ε : ℂ) / 2 * g * star c).im] := by
  ext i
  fin_cases i <;>
    simp [envelopeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

/-- At exact matching with real coupling, the two quadratures decouple. -/
theorem envelope_matched_quadratures (σ ε r X Y : ℝ) :
    (envelopeMatrix σ 0 ε (r : ℂ)).mulVec ![X, Y] =
      ![(-σ + ε * r / 2) * X, (-σ - ε * r / 2) * Y] := by
  ext i
  fin_cases i <;>
    simp [envelopeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- A unit complex phase removes the phase of the matched coupling. Taking
`u = exp (i φ/2)` and `g = r u²` gives the paper's quadrature rotation. -/
theorem matched_phase_rotation (σ ε r X Y : ℝ) (u : ℂ)
    (hu : u * star u = 1) :
    (-(σ : ℂ)) * (u * ((X : ℂ) + Complex.I * Y)) +
        (ε : ℂ) / 2 * ((r : ℂ) * u ^ 2) * star (u * ((X : ℂ) + Complex.I * Y)) =
      u * (((-σ + ε * r / 2) * X : ℝ) +
        Complex.I * (((-σ - ε * r / 2) * Y : ℝ) : ℂ)) := by
  simp only [star_mul, star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination ((ε : ℂ) / 2 * (r : ℂ) * u *
    ((X : ℂ) - Complex.I * Y)) * hu

/-- A real monic quadratic with positive linear and constant coefficients has
all its complex roots strictly in the left half-plane. -/
theorem quadratic_root_re_neg {σ d : ℝ} (hσ : 0 < σ) (hd : 0 < d)
    {z : ℂ} (hz : z ^ 2 + (2 * σ : ℝ) * z + (d : ℂ) = 0) : z.re < 0 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  by_cases hi : z.im = 0
  · rw [hi] at hre
    by_contra hn
    have hn' : 0 ≤ z.re := le_of_not_gt hn
    nlinarith [sq_nonneg z.re, mul_nonneg (le_of_lt hσ) hn']
  · have hprod : z.im * (z.re + σ) = 0 := by nlinarith [him]
    have hs : z.re + σ = 0 := (mul_eq_zero.mp hprod).resolve_left hi
    linarith

/-- If the constant coefficient is nonpositive, an explicit nonnegative real
root witnesses failure of strict spectral stability. -/
theorem quadratic_nonneg_root {σ d : ℝ} (hσ : 0 < σ) (hd : d ≤ 0) :
    ∃ r : ℝ, 0 ≤ r ∧
      (r : ℂ) ^ 2 + (2 * σ : ℝ) * (r : ℂ) + (d : ℂ) = 0 := by
  have hrad : 0 ≤ σ ^ 2 - d := by nlinarith [sq_nonneg σ]
  have hs := Real.sq_sqrt hrad
  have hle : σ ≤ Real.sqrt (σ ^ 2 - d) :=
    (Real.le_sqrt (le_of_lt hσ) hrad).mpr (by linarith)
  refine ⟨-σ + Real.sqrt (σ ^ 2 - d), by linarith, ?_⟩
  have hr : (-σ + Real.sqrt (σ ^ 2 - d)) ^ 2 +
      (2 * σ) * (-σ + Real.sqrt (σ ^ 2 - d)) + d = 0 := by nlinarith
  exact_mod_cast hr

/-- Exact Hurwitz decision for the envelope matrix, without a stability axiom. -/
theorem envelope_hurwitz_iff {σ : ℝ} (hσ : 0 < σ) (Δ ε : ℝ) (g : ℂ) :
    Hurwitz (envelopeMatrix σ Δ ε g) ↔
      ε ^ 2 * Complex.normSq g / 4 < σ ^ 2 + Δ ^ 2 := by
  constructor
  · intro h
    by_contra hn
    have hd : envelopeMargin σ Δ ε g ≤ 0 := by
      dsimp [envelopeMargin]
      linarith [le_of_not_gt hn]
    obtain ⟨r, hr, hz⟩ := quadratic_nonneg_root hσ hd
    have he := h (r : ℂ) ((envelope_eigenvalue_iff σ Δ ε g r).mpr hz)
    simp only [Complex.ofReal_re] at he
    linarith
  · intro h z hz
    apply quadratic_root_re_neg hσ (show 0 < envelopeMargin σ Δ ε g by
      dsimp [envelopeMargin]
      linarith)
    exact (envelope_eigenvalue_iff σ Δ ε g z).mp hz

/-- The exact boundary has eigenvalue zero. -/
theorem envelope_zero_eigenvalue_iff (σ Δ ε : ℝ) (g : ℂ) :
    HasEigenvalue (envelopeMatrix σ Δ ε g) 0 ↔
      ε ^ 2 * Complex.normSq g / 4 = σ ^ 2 + Δ ^ 2 := by
  rw [envelope_eigenvalue_iff]
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add,
    Complex.ofReal_eq_zero]
  dsimp [envelopeMargin]
  constructor <;> intro h <;> linarith

/-- Strictly beyond the boundary there is a positive real eigenvalue. -/
theorem envelope_positive_eigenvalue {σ : ℝ} (hσ : 0 < σ) (Δ ε : ℝ) (g : ℂ)
    (h : σ ^ 2 + Δ ^ 2 < ε ^ 2 * Complex.normSq g / 4) :
    ∃ z : ℂ, HasEigenvalue (envelopeMatrix σ Δ ε g) z ∧ 0 < z.re := by
  have hd : envelopeMargin σ Δ ε g < 0 := by
    dsimp [envelopeMargin]
    linarith
  obtain ⟨r, hr, hz⟩ := quadratic_nonneg_root hσ (le_of_lt hd)
  have hrpos : 0 < r := by
    have hre := congrArg Complex.re hz
    simp [pow_two, Complex.mul_re] at hre
    by_contra hn
    have hrzero : r = 0 := le_antisymm (le_of_not_gt hn) hr
    rw [hrzero] at hre
    simp only [mul_zero, zero_add] at hre
    linarith
  exact ⟨(r : ℂ), (envelope_eigenvalue_iff σ Δ ε g r).mpr hz, hrpos⟩

theorem envelope_positive_eigenvalue_iff {σ : ℝ} (hσ : 0 < σ)
    (Δ ε : ℝ) (g : ℂ) :
    (∃ z : ℂ, HasEigenvalue (envelopeMatrix σ Δ ε g) z ∧ 0 < z.re) ↔
      σ ^ 2 + Δ ^ 2 < ε ^ 2 * Complex.normSq g / 4 := by
  constructor
  · rintro ⟨z, hz, hp⟩
    have he := (envelope_eigenvalue_iff σ Δ ε g z).mp hz
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
    have hprod : z.im * (z.re + σ) = 0 := by nlinarith [him]
    have hi : z.im = 0 := (mul_eq_zero.mp hprod).resolve_right (by linarith)
    rw [hi] at hre
    dsimp [envelopeMargin] at hre
    nlinarith [sq_nonneg z.re, mul_pos hσ hp]
  · exact envelope_positive_eigenvalue hσ Δ ε g

/-- Coupling divided by damping and detuning; this is not an input-output gain. -/
def amplificationIndex (σ Δ : ℝ) (g : ℂ) : ℝ :=
  ‖g‖ / (2 * Real.sqrt (σ ^ 2 + Δ ^ 2))

theorem amplificationIndex_nonneg (σ Δ : ℝ) (g : ℂ) :
    0 ≤ amplificationIndex σ Δ g := by
  unfold amplificationIndex
  exact div_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem amplificationIndex_lt_one_iff {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 ≤ ε)
    (Δ : ℝ) (g : ℂ) :
    ε * amplificationIndex σ Δ g < 1 ↔
      ε ^ 2 * Complex.normSq g / 4 < σ ^ 2 + Δ ^ 2 := by
  have hq : 0 < σ ^ 2 + Δ ^ 2 := by nlinarith [sq_nonneg Δ]
  have hs := Real.sq_sqrt (le_of_lt hq)
  have hd : 0 < 2 * Real.sqrt (σ ^ 2 + Δ ^ 2) :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr hq)
  have hn : 0 ≤ ε * ‖g‖ := mul_nonneg hε (norm_nonneg _)
  rw [show ε * amplificationIndex σ Δ g =
    (ε * ‖g‖) / (2 * Real.sqrt (σ ^ 2 + Δ ^ 2)) by
      unfold amplificationIndex
      ring]
  rw [div_lt_one hd, ← sq_lt_sq₀ hn (le_of_lt hd), Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> nlinarith

theorem amplificationIndex_gt_one_iff {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 ≤ ε)
    (Δ : ℝ) (g : ℂ) :
    1 < ε * amplificationIndex σ Δ g ↔
      σ ^ 2 + Δ ^ 2 < ε ^ 2 * Complex.normSq g / 4 := by
  have hq : 0 < σ ^ 2 + Δ ^ 2 := by nlinarith [sq_nonneg Δ]
  have hs := Real.sq_sqrt (le_of_lt hq)
  have hd : 0 < 2 * Real.sqrt (σ ^ 2 + Δ ^ 2) :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr hq)
  have hn : 0 ≤ ε * ‖g‖ := mul_nonneg hε (norm_nonneg _)
  rw [show ε * amplificationIndex σ Δ g =
    (ε * ‖g‖) / (2 * Real.sqrt (σ ^ 2 + Δ ^ 2)) by
      unfold amplificationIndex
      ring]
  rw [one_lt_div hd, ← sq_lt_sq₀ (le_of_lt hd) hn, Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> nlinarith

theorem amplificationIndex_eq_one_iff {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 ≤ ε)
    (Δ : ℝ) (g : ℂ) :
    ε * amplificationIndex σ Δ g = 1 ↔
      ε ^ 2 * Complex.normSq g / 4 = σ ^ 2 + Δ ^ 2 := by
  have hlt := amplificationIndex_lt_one_iff hσ hε Δ g
  have hgt := amplificationIndex_gt_one_iff hσ hε Δ g
  constructor
  · intro h
    have hnlt : ¬ ε ^ 2 * Complex.normSq g / 4 < σ ^ 2 + Δ ^ 2 := by
      rw [← hlt, h]
      exact lt_irrefl _
    have hngt : ¬ σ ^ 2 + Δ ^ 2 < ε ^ 2 * Complex.normSq g / 4 := by
      rw [← hgt, h]
      exact lt_irrefl _
    exact le_antisymm (le_of_not_gt hngt) (le_of_not_gt hnlt)
  · intro h
    apply le_antisymm
    · apply le_of_not_gt
      intro hh
      have hc := hgt.mp hh
      linarith
    · apply le_of_not_gt
      intro hh
      have hc := hlt.mp hh
      linarith

theorem envelope_zero_eigenvalue_iff_index {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 ≤ ε) (Δ : ℝ) (g : ℂ) :
    HasEigenvalue (envelopeMatrix σ Δ ε g) 0 ↔
      ε * amplificationIndex σ Δ g = 1 := by
  rw [envelope_zero_eigenvalue_iff, amplificationIndex_eq_one_iff hσ hε]

theorem envelope_hurwitz_iff_index {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 ≤ ε)
    (Δ : ℝ) (g : ℂ) :
    Hurwitz (envelopeMatrix σ Δ ε g) ↔ ε * amplificationIndex σ Δ g < 1 := by
  rw [envelope_hurwitz_iff hσ, amplificationIndex_lt_one_iff hσ hε]

theorem envelope_positive_eigenvalue_iff_index {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 ≤ ε) (Δ : ℝ) (g : ℂ) :
    (∃ z : ℂ, HasEigenvalue (envelopeMatrix σ Δ ε g) z ∧ 0 < z.re) ↔
      1 < ε * amplificationIndex σ Δ g := by
  rw [envelope_positive_eigenvalue_iff hσ, amplificationIndex_gt_one_iff hσ hε]

/-- The reciprocal-index formula is used only for nonzero coupling. -/
theorem amplificationIndex_reciprocal {σ : ℝ} (hσ : 0 < σ) (Δ : ℝ)
    {g : ℂ} (hg : g ≠ 0) :
    0 < 1 / amplificationIndex σ Δ g ∧
      1 / amplificationIndex σ Δ g = 2 * Real.sqrt (σ ^ 2 + Δ ^ 2) / ‖g‖ := by
  have hq : 0 < σ ^ 2 + Δ ^ 2 := by nlinarith [sq_nonneg Δ]
  have ha : 0 < amplificationIndex σ Δ g :=
    div_pos (norm_pos_iff.mpr hg) (mul_pos (by norm_num) (Real.sqrt_pos.mpr hq))
  constructor
  · exact div_pos (by norm_num) ha
  · unfold amplificationIndex
    rw [one_div, inv_div]

/-- For nonzero coupling, the critical amplitude is a finite real number. -/
theorem amplificationIndex_threshold {σ : ℝ} (hσ : 0 < σ) (Δ ε : ℝ)
    {g : ℂ} (hg : g ≠ 0) :
    1 < ε * amplificationIndex σ Δ g ↔
      2 * Real.sqrt (σ ^ 2 + Δ ^ 2) / ‖g‖ < ε := by
  have hq : 0 < σ ^ 2 + Δ ^ 2 := by nlinarith [sq_nonneg Δ]
  have hd : 0 < 2 * Real.sqrt (σ ^ 2 + Δ ^ 2) :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr hq)
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  rw [show ε * amplificationIndex σ Δ g =
    (ε * ‖g‖) / (2 * Real.sqrt (σ ^ 2 + Δ ^ 2)) by
      unfold amplificationIndex
      ring]
  rw [one_lt_div hd, div_lt_iff₀ hgpos]

theorem amplificationIndex_matched {σ : ℝ} (hσ : 0 < σ) (g : ℂ) :
    amplificationIndex σ 0 g = ‖g‖ / (2 * σ) := by
  simp [amplificationIndex, Real.sqrt_sq (le_of_lt hσ)]

/-- Zero coupling has no finite spectral threshold. -/
theorem envelope_zero_coupling_hurwitz {σ : ℝ} (hσ : 0 < σ) (Δ ε : ℝ) :
    Hurwitz (envelopeMatrix σ Δ ε 0) := by
  rw [envelope_hurwitz_iff hσ]
  simp only [map_zero, mul_zero, zero_div]
  nlinarith [sq_nonneg Δ]

/-- This corollary, unlike the preceding spectral results, uses the existing
axiom connecting eigenvalues to exponential trajectory decay. -/
theorem envelope_smallSignalStable_iff {σ : ℝ} (hσ : 0 < σ)
    (Δ ε : ℝ) (g : ℂ) :
    SmallSignalStable (envelopeMatrix σ Δ ε g) ↔
      ε ^ 2 * Complex.normSq g / 4 < σ ^ 2 + Δ ^ 2 := by
  rw [linear_spectral_criterion, envelope_hurwitz_iff hσ]

end Powerlib.Parametric
