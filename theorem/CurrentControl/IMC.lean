import theorem.CurrentControl.Decoupling

/-! # IMC-tuned PI current loop and the IN/OUT sign of the current controller

Model boundary.
* IMC tuning: the single-axis PI current loop of `PILoop.lean` (state `(i, ξ)`, series R–L
  branch with `L > 0`, IN-positive current, PLL-aligned dq axis, ideal feedforward and
  decoupling, no delay / PWM / limits, continuous time, reference `i*` as input), read through
  its family `PIParams.family`: the closed-loop plant as a port system, whose flow sentences
  speak about the loop at the equilibrium of every constant reference. IMC gains `Kp = L ω_b`,
  `Ki = R ω_b` with bandwidth `ω_b > 0` (`imc`).
* Controller sign: IN-positive duty-cycle plant `L di/dt = −R i − V_dc d` (from
  `ΔI = Z_oc⁻¹ (ΔV − V_dc ΔD)` with `ΔV = 0`, scalar, no dq coupling and no delay), controller
  `d = σ (Kp (i* − i) + Ki ξ)`.
* The same IMC-tuned loop in a machine drive (RL plant, bandwidth `α`) is the family on
  `Drives.CascadeControl.IMCLoop` (`theorem/Drives/CascadeControl.lean`).

Source: work-sync `theory/T-gfl-control.md` §1.4.1; `theory/T-gfl-impedance.md` §1.4 (sign
paragraph and sanity check).

Results.
IMC tuning (T-gfl-control §1.4.1, Harnefors–Nee 1998):
* `imc_charPoly`: `L s² + (R + L ω_b) s + R ω_b = (L s + R)(s + ω_b)`.
* `imc_transfer_eq`: off the two roots the closed-loop transfer is **exactly**
  `ω_b/(s + ω_b)` (the note writes `≈`): the plant pole `−R/L` is cancelled by the PI zero
  (`imc_numerator_root`), but it remains a characteristic root of the realization
  (`imc_cancelled_pole_root`).
* `imc_mem_den_iff` (connection): internal (state) stability — every attractive sentence —
  holds iff `R/L > 0`, whatever `ω_b > 0`.
* `imc_transfer_stable_insufficient` (connection): for `R ≤ 0` the transfer is still the stable
  first-order lag `ω_b/(s + ω_b)` (`imc_transfer_eq`, static) but the loop satisfies no
  attractive sentence — the hidden-mode pattern of
  `Circuits.Interconnection.portData_not_certified`.

Sign of the current controller (T-gfl-impedance §1.4):
* `signedField_correct`: `σ = −1` (the IN translation `−G_ci ε` of the note) is the PI loop
  with gains `V_dc Kp, V_dc Ki`: characteristic polynomial `L s² + (R + V_dc Kp) s + V_dc Ki`.
* `signedField_copied`: `σ = +1` (the OUT-literature form `+G_ci ε` copied unchanged) is the PI
  loop with gains `−V_dc Kp, −V_dc Ki`: characteristic polynomial
  `L s² + (R − V_dc Kp) s − V_dc Ki`.
* Negation theorems: with `V_dc > 0`, `Ki > 0` the copied form has a positive real
  characteristic root (`copied_exists_pos_root`, static), is unstable
  (`copied_mem_den_unstable`, connection) and satisfies no attractive sentence
  (`copied_not_mem_den`, connection).

Family and connection conclusions.
No new family: both models are read through `PIParams.family` of `PILoop.lean`; the connection
statements are `imc_mem_den_iff`, `imc_transfer_stable_insufficient`, `copied_mem_den_unstable`
and `copied_not_mem_den`. The transfer functions, characteristic polynomials and field identities
are static evidence. That the copied form has a solution whose current does not track
(`copied_not_tracks`) is a trajectory-level result outside the sentence language, kept as private
implementation evidence.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter Linear LinearSystems
open scoped Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- IMC tuning: `Kp = L ω_b`, `Ki = R ω_b`. -/
def imc (L R ωb : ℝ) : PIParams := ⟨L, R, L * ωb, R * ωb⟩

section IMC

variable {L R ωb : ℝ}

@[tmio T, powerlib_foundation] theorem imc_charPoly (L R ωb : ℝ) (s : ℂ) :
    (L : ℂ) * s ^ 2 + (R + L * ωb) * s + R * ωb = (L * s + R) * (s + ωb) := by ring

@[powerlib_foundation] theorem imc_det_characteristicMatrix (hL : L ≠ 0) (s : ℂ) :
    (characteristicMatrix (imc L R ωb).model.A s).det =
      ((L : ℂ) * s + R) * (s + ωb) / L := by
  rw [PIParams.det_characteristicMatrix _ hL]
  simp only [imc]
  push_cast
  ring

/-- The cancelled plant pole `−R/L` is still a characteristic root of the closed loop. Static
evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem imc_cancelled_pole_root (hL : L ≠ 0) :
    (characteristicMatrix (imc L R ωb).model.A ((-R / L : ℝ) : ℂ)).det = 0 := by
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

/-- Exact IMC closed-loop transfer: `ω_b/(s + ω_b)` off the roots `−R/L`, `−ω_b`. Static
evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem imc_transfer_eq (hL : L ≠ 0) {s : ℂ} (h1 : (L : ℂ) * s + R ≠ 0)
    (h2 : s + ωb ≠ 0) :
    transfer (imc L R ωb).model s 0 0 = ωb / (s + ωb) := by
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

/-- Internal stability after the cancellation: the IMC loop satisfies an attractive sentence
(in particular global exponential stability) iff `R/L > 0`, whatever `ω_b > 0`. -/
@[tmio TM, powerlib_domain] theorem imc_mem_den_iff (hL : 0 < L) (hω : 0 < ωb) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (imc L R ωb ∈ PIParams.family.den (.flow P) ↔
      imc L R ωb ∈ {_m : PIParams | 0 < R / L}) := by
  have h := PIParams.mem_den_iff (imc L R ωb) hL hP
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  change 0 < R + L * ωb ∧ 0 < R * ωb ↔ 0 < R / L
  rw [div_pos_iff_of_pos_right hL]
  constructor
  · rintro ⟨-, h⟩
    exact pos_of_mul_pos_left h hω.le
  · intro hR
    exact ⟨by nlinarith, mul_pos hR hω⟩

/-- A stable first-order transfer function does not certify the IMC loop: for `R ≤ 0` the
transfer is still `ω_b/(s + ω_b)` (`imc_transfer_eq`, for every `R`) but the loop satisfies no
attractive sentence. -/
@[tmio TM, powerlib_domain] theorem imc_transfer_stable_insufficient (hL : 0 < L) (hω : 0 < ωb)
    (hR : R ≤ 0) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (imc L R ωb ∉ PIParams.family.den (.flow P)) := by
  have h := imc_mem_den_iff (R := R) hL hω hP
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  change ¬ 0 < R / L
  exact not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hR hL.le)

end IMC

/-! ## IN-positive plant with a signed current controller -/

namespace PIParams

variable (p : PIParams)

/-- IN-positive duty plant `L di/dt = −R i − V_dc d` with `d = σ (Kp (i* − i) + Ki ξ)`. -/
def signedField (Vdc σ iref : ℝ) (x : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![(-p.R * x 0 - Vdc * (σ * p.control iref x)) / p.L, iref - x 0]

/-- `σ = −1` (`−G_ci ε`): the PI loop with gains `V_dc Kp`, `V_dc Ki`. -/
@[powerlib_foundation] theorem signedField_correct (Vdc iref : ℝ) (x : ℝ²) :
    p.signedField Vdc (-1) iref x = (p.withGain Vdc).field iref x := by
  ext j
  fin_cases j <;> simp [signedField, field, control, withGain]
  ring

/-- `σ = +1` (`+G_ci ε` copied from OUT literature): gains `−V_dc Kp`, `−V_dc Ki`. -/
@[powerlib_foundation] theorem signedField_copied (Vdc iref : ℝ) (x : ℝ²) :
    p.signedField Vdc 1 iref x = (p.withGain (-Vdc)).field iref x := by
  ext j
  fin_cases j <;> simp [signedField, field, control, withGain]
  ring

/-- Characteristic polynomial of the copied form: `L s² + (R − V_dc Kp) s − V_dc Ki`. -/
@[powerlib_foundation] theorem copied_det_characteristicMatrix (hL : p.L ≠ 0) (Vdc : ℝ)
    (s : ℂ) :
    (characteristicMatrix (p.withGain (-Vdc)).model.A s).det =
      ((p.L : ℂ) * s ^ 2 + (p.R - Vdc * p.Kp) * s - Vdc * p.Ki) / p.L := by
  rw [p.withGain_det_characteristicMatrix hL]
  push_cast
  ring

/-- The copied form has a negative state-matrix determinant. Static evidence on the model, not a
connection conclusion. -/
@[powerlib_foundation] theorem copied_det_neg (hL : 0 < p.L) {Vdc : ℝ} (hV : 0 < Vdc)
    (hKi : 0 < p.Ki) : (p.withGain (-Vdc)).model.A.det < 0 := by
  change (!![-(p.R + -Vdc * p.Kp) / p.L, -Vdc * p.Ki / p.L; -1, 0] :
    Matrix (Fin 2) (Fin 2) ℝ).det < 0
  rw [Matrix.det_fin_two_of]
  have : 0 < Vdc * p.Ki / p.L := div_pos (mul_pos hV hKi) hL
  have h : -Vdc * p.Ki / p.L = -(Vdc * p.Ki / p.L) := by ring
  rw [h]
  linarith

/-- The copied OUT form has a positive real closed-loop characteristic root. Static evidence on
the model, not a connection conclusion. -/
@[powerlib_foundation] theorem copied_exists_pos_root (hL : 0 < p.L) {Vdc : ℝ} (hV : 0 < Vdc)
    (hKi : 0 < p.Ki) :
    ∃ r : ℝ, 0 < r ∧ (characteristicMatrix (p.withGain (-Vdc)).model.A r).det = 0 := by
  obtain ⟨r, hr, v, hv, heig⟩ :=
    Criteria.exists_pos_real_eigenvalue_of_det_neg _ (p.copied_det_neg hL hV hKi)
  exact ⟨r, hr, Criteria.det_characteristicMatrix_eq_zero_of_eigenpair _ hv heig⟩

/-- The copied OUT form is unstable. -/
@[tmio TM, powerlib_domain] theorem copied_mem_den_unstable (hL : 0 < p.L) {Vdc : ℝ} (hV : 0 < Vdc)
    (hKi : 0 < p.Ki) : connection% (p.withGain (-Vdc) ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨r, hr, hroot⟩ := p.copied_exists_pos_root hL hV hKi
  exact family_isLinear.mem_den_flow.mpr (Linear.unstable_of_root 0 hroot (by simpa using hr))

/-- The copied OUT form satisfies no attractive sentence (in particular it is not exponentially
stable). -/
@[tmio TM, powerlib_domain] theorem copied_not_mem_den (hL : 0 < p.L) {Vdc : ℝ} (hV : 0 < Vdc)
    (hKi : 0 < p.Ki) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (p.withGain (-Vdc) ∉ family.den (.flow P)) := by
  have h := mem_den_iff (p.withGain (-Vdc)) hL hP
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  rintro ⟨-, h⟩
  change 0 < -Vdc * p.Ki at h
  nlinarith

/-- The copied OUT form does not track: some solution has `i(t) ↛ i*`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem copied_not_tracks (hL : 0 < p.L) {Vdc : ℝ} (hV : 0 < Vdc) (hKi : 0 < p.Ki)
    (iref : ℝ) :
    ∃ x : ℝ → ℝ², (∀ t, HasDerivAt x (p.signedField Vdc 1 iref (x t)) t) ∧
      ¬ Tendsto (fun t => x t 0) atTop (𝓝 iref) := by
  have hKi' : (p.withGain (-Vdc)).Ki < 0 := by
    simp only [withGain]
    nlinarith
  obtain ⟨r, hr, v, hv, hAv⟩ :=
    Criteria.exists_pos_real_eigenvector_of_det_neg _ (p.copied_det_neg hL hV hKi)
  obtain ⟨x, hx, hn⟩ := LTI.exists_not_tendsto_of_eigenvector (p.withGain (-Vdc)).model
    ((p.withGain (-Vdc)).isEquilibrium hKi'.ne iref) hr hAv
    ((p.withGain (-Vdc)).first_ne_zero hr hv hAv) iref
  refine ⟨x, fun t => ?_, hn⟩
  rw [signedField_copied, ← model_field]
  exact hx t

end PIParams

end powerlib.CurrentControl
