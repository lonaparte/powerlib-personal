import theorem.CurrentControl.Decoupling

/-! # IMC-tuned PI current loop and the IN/OUT sign of the current controller (domain)

Model boundary: the single-axis PI current loop of `PILoop.lean` (state `(i, ξ)`, series R–L
branch with `L > 0`, IN-positive current, PLL-aligned dq axis, ideal feedforward and
decoupling, no delay / PWM / limits, continuous time, constant reference `i*` as input).

## IMC tuning (T-gfl-control §1.4.1, Harnefors–Nee 1998)
`Kp = L ω_b`, `Ki = R ω_b` with bandwidth `ω_b > 0` (`imc`).
* `imc_charPoly`: `L s² + (R + L ω_b) s + R ω_b = (L s + R)(s + ω_b)`.
* `imc_transfer_eq`: off the two roots the closed-loop transfer is **exactly**
  `ω_b/(s + ω_b)` (the note writes `≈`): the plant pole `−R/L` is cancelled by the PI zero
  (`imc_numerator_root`), but it remains a characteristic root of the realization
  (`imc_cancelled_pole_root`).
* `imc_exponentiallyStable_iff`: internal (state) exponential stability holds iff
  `R/L > 0`, whatever `ω_b > 0`.
* `imc_transfer_stable_insufficient`: for `R ≤ 0` the transfer is still the stable first-order
  lag `ω_b/(s + ω_b)` but the loop is not exponentially stable — the hidden-mode pattern of
  `ImpedanceCriterion.impedanceStable_without_premises_insufficient`.

## Sign of the current controller (T-gfl-impedance §1.4)
IN-positive duty-cycle plant `L di/dt = −R i − V_dc d` (from `ΔI = Z_oc⁻¹ (ΔV − V_dc ΔD)` with
`ΔV = 0`, scalar, no dq coupling and no delay), controller `d = σ (Kp (i* − i) + Ki ξ)`.
* `signedField_correct`: `σ = −1` (the IN translation `−G_ci ε` of the note) is the PI loop
  with gains `V_dc Kp, V_dc Ki`: characteristic polynomial `L s² + (R + V_dc Kp) s + V_dc Ki`.
* `signedField_copied`: `σ = +1` (the OUT-literature form `+G_ci ε` copied unchanged) is the PI
  loop with gains `−V_dc Kp, −V_dc Ki`: characteristic polynomial
  `L s² + (R − V_dc Kp) s − V_dc Ki`.
* Negation theorems: with `V_dc > 0`, `Ki > 0` the copied form has a positive real
  characteristic root (`copied_exists_pos_root`), is not exponentially stable
  (`copied_not_exponentiallyStable`) and has a solution whose current does not track
  (`copied_not_tracks`).

Source: work-sync `theory/T-gfl-control.md` §1.4.1; `theory/T-gfl-impedance.md` §1.4 (sign
paragraph and sanity check).
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter
open scoped Topology

/-- IMC tuning: `Kp = L ω_b`, `Ki = R ω_b`. -/
def imc (L R ωb : ℝ) : PIParams := ⟨L, R, L * ωb, R * ωb⟩

section IMC

variable {L R ωb : ℝ}

@[powerlib_foundation] theorem imc_charPoly (L R ωb : ℝ) (s : ℂ) :
    (L : ℂ) * s ^ 2 + (R + L * ωb) * s + R * ωb = (L * s + R) * (s + ωb) := by ring

@[powerlib_foundation] theorem imc_det_characteristicMatrix (hL : L ≠ 0) (s : ℂ) :
    (LTI.characteristicMatrix (imc L R ωb).model.A s).det =
      ((L : ℂ) * s + R) * (s + ωb) / L := by
  rw [PIParams.det_characteristicMatrix _ hL]
  simp only [imc]
  push_cast
  ring

/-- The cancelled plant pole `−R/L` is still a characteristic root of the closed loop. -/
@[powerlib_domain] theorem imc_cancelled_pole_root (hL : L ≠ 0) :
    (LTI.characteristicMatrix (imc L R ωb).model.A ((-R / L : ℝ) : ℂ)).det = 0 := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [imc_det_characteristicMatrix hL]
  push_cast
  field_simp
  ring

/-- The PI zero sits on the plant pole: `Kp (−R/L) + Ki = 0`. -/
@[powerlib_foundation] theorem imc_numerator_root (hL : L ≠ 0) :
    (imc L R ωb).Kp * (-R / L) + (imc L R ωb).Ki = 0 := by
  simp only [imc]
  field_simp
  ring

/-- Exact IMC closed-loop transfer: `ω_b/(s + ω_b)` off the roots `−R/L`, `−ω_b`. -/
@[powerlib_domain] theorem imc_transfer_eq (hL : L ≠ 0) {s : ℂ} (h1 : (L : ℂ) * s + R ≠ 0)
    (h2 : s + ωb ≠ 0) :
    LTI.transfer (imc L R ωb).model s 0 0 = ωb / (s + ωb) := by
  have hs : ((imc L R ωb).L : ℂ) * s ^ 2 + ((imc L R ωb).R + (imc L R ωb).Kp) * s +
      (imc L R ωb).Ki ≠ 0 := by
    simp only [imc]
    push_cast
    rw [imc_charPoly]
    exact mul_ne_zero h1 h2
  rw [PIParams.transfer_eq _ hL hs]
  simp only [imc]
  push_cast
  rw [imc_charPoly]
  field_simp

/-- Internal stability after the cancellation holds iff `R/L > 0`. -/
@[powerlib_domain] theorem imc_exponentiallyStable_iff (hL : 0 < L) (hω : 0 < ωb) :
    LTI.ExponentiallyStable (imc L R ωb).model.autonomous ↔ 0 < R / L := by
  rw [PIParams.exponentiallyStable_iff _ hL, div_pos_iff_of_pos_right hL]
  simp only [imc]
  constructor
  · rintro ⟨-, h⟩
    exact pos_of_mul_pos_left h hω.le
  · intro hR
    exact ⟨by nlinarith, mul_pos hR hω⟩

/-- A stable first-order transfer function does not certify the IMC loop: for `R ≤ 0` the
transfer is `ω_b/(s + ω_b)` but the realization is not exponentially stable. -/
@[powerlib_domain] theorem imc_transfer_stable_insufficient (hL : 0 < L) (hω : 0 < ωb)
    (hR : R ≤ 0) :
    (∀ s : ℂ, (L : ℂ) * s + R ≠ 0 → s + ωb ≠ 0 →
        LTI.transfer (imc L R ωb).model s 0 0 = ωb / (s + ωb)) ∧
      ¬ LTI.ExponentiallyStable (imc L R ωb).model.autonomous := by
  refine ⟨fun s h1 h2 => imc_transfer_eq hL.ne' h1 h2, ?_⟩
  rw [imc_exponentiallyStable_iff hL hω]
  intro h
  have : R / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg hR hL.le
  linarith

end IMC

/-! ## IN-positive plant with a signed current controller -/

namespace PIParams

variable (p : PIParams)

/-- IN-positive duty plant `L di/dt = −R i − V_dc d` with `d = σ (Kp (i* − i) + Ki ξ)`. -/
def signedField (Vdc σ iref : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(-p.R * x 0 - Vdc * (σ * p.control iref x)) / p.L, iref - x 0]

/-- `σ = −1` (`−G_ci ε`): the PI loop with gains `V_dc Kp`, `V_dc Ki`. -/
@[powerlib_foundation] theorem signedField_correct (Vdc iref : ℝ) (x : Fin 2 → ℝ) :
    p.signedField Vdc (-1) iref x = (p.withGain Vdc).field iref x := by
  ext j
  fin_cases j <;> simp [signedField, field, control, withGain]
  ring

/-- `σ = +1` (`+G_ci ε` copied from OUT literature): gains `−V_dc Kp`, `−V_dc Ki`. -/
@[powerlib_foundation] theorem signedField_copied (Vdc iref : ℝ) (x : Fin 2 → ℝ) :
    p.signedField Vdc 1 iref x = (p.withGain (-Vdc)).field iref x := by
  ext j
  fin_cases j <;> simp [signedField, field, control, withGain]
  ring

/-- Characteristic polynomial of the copied form: `L s² + (R − V_dc Kp) s − V_dc Ki`. -/
@[powerlib_foundation] theorem copied_det_characteristicMatrix (hL : p.L ≠ 0) (Vdc : ℝ)
    (s : ℂ) :
    (LTI.characteristicMatrix (p.withGain (-Vdc)).model.A s).det =
      ((p.L : ℂ) * s ^ 2 + (p.R - Vdc * p.Kp) * s - Vdc * p.Ki) / p.L := by
  rw [p.withGain_det_characteristicMatrix hL]
  push_cast
  ring

@[powerlib_foundation] private lemma copied_det_neg (hL : 0 < p.L) {Vdc : ℝ} (hV : 0 < Vdc)
    (hKi : 0 < p.Ki) : (p.withGain (-Vdc)).model.A.det < 0 := by
  change (!![-(p.R + -Vdc * p.Kp) / p.L, -Vdc * p.Ki / p.L; -1, 0] :
    Matrix (Fin 2) (Fin 2) ℝ).det < 0
  rw [Matrix.det_fin_two_of]
  have : 0 < Vdc * p.Ki / p.L := div_pos (mul_pos hV hKi) hL
  have h : -Vdc * p.Ki / p.L = -(Vdc * p.Ki / p.L) := by ring
  rw [h]
  linarith

/-- The copied OUT form has a positive real closed-loop characteristic root. -/
@[powerlib_domain] theorem copied_exists_pos_root (hL : 0 < p.L) {Vdc : ℝ} (hV : 0 < Vdc)
    (hKi : 0 < p.Ki) :
    ∃ r : ℝ, 0 < r ∧ (LTI.characteristicMatrix (p.withGain (-Vdc)).model.A r).det = 0 := by
  obtain ⟨r, hr, v, hv, heig⟩ :=
    Criteria.exists_pos_real_eigenvalue_of_det_neg _ (p.copied_det_neg hL hV hKi)
  exact ⟨r, hr, Criteria.det_characteristicMatrix_eq_zero_of_eigenpair _ hv heig⟩

/-- The copied OUT form is not exponentially stable. -/
@[powerlib_domain] theorem copied_not_exponentiallyStable (hL : 0 < p.L) {Vdc : ℝ}
    (hV : 0 < Vdc) (hKi : 0 < p.Ki) :
    ¬ LTI.ExponentiallyStable (p.withGain (-Vdc)).model.autonomous := by
  rw [(p.withGain (-Vdc)).exponentiallyStable_iff hL]
  rintro ⟨-, h⟩
  simp only [withGain] at h
  nlinarith

/-- The copied OUT form does not track: some solution has `i(t) ↛ i*`. -/
@[powerlib_domain] theorem copied_not_tracks (hL : 0 < p.L) {Vdc : ℝ} (hV : 0 < Vdc)
    (hKi : 0 < p.Ki) (iref : ℝ) :
    ∃ x : ℝ → Fin 2 → ℝ, (∀ t, HasDerivAt x (p.signedField Vdc 1 iref (x t)) t) ∧
      ¬ Tendsto (fun t => x t 0) atTop (𝓝 iref) := by
  have hKi' : (p.withGain (-Vdc)).Ki < 0 := by
    simp only [withGain]
    nlinarith
  obtain ⟨x, hx, hn⟩ := (p.withGain (-Vdc)).not_tracks_of_Ki_neg hL hKi' iref
  refine ⟨x, fun t => ?_, hn⟩
  rw [signedField_copied]
  exact hx t

end PIParams

end powerlib.CurrentControl
