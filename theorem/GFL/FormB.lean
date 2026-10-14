import theorem.GFL.PIPLL
import theorem.SpecialFunctions.TrigZeros

/-! # GFL form-B reduction: quasi-steady algebra and the phase-detector characteristic

Model boundary. Grid-following VSC with LC filter and an `R_g`–`L_g` line to an infinite bus
`(V_g, 0)` (system dq frame rotating at the constant grid frequency `ω_g`), SRF-PLL with PI gains
`K_p, K_i`, current references `i_d*, i_q*` frozen (outer loops frozen), IN-positive currents
(`conventions.md` §D1), Park matrix `T(θ) = [[cos θ, sin θ], [−sin θ, cos θ]]`. What is
formalized is the algebra of the form-B reduction of `T-gfl-dynamics` §1.4–§1.7:
* step 1 (`convCurrentD/Q`): ideal current tracking `i^c = i*`, rotated to the system frame,
  `i = T(−θ) i*`;
* steps 2–3 (`QuasiSteady`): the LC-capacitor and line equations with their time derivatives set
  to zero, `0 = i_d − i_gd + ω_g C_f v_cq`, `0 = i_q − i_gq − ω_g C_f v_cd`,
  `0 = v_cd − V_g − R_g i_gd + ω_g L_g i_gq`, `0 = v_cq − R_g i_gq − ω_g L_g i_gd`;
* step 4 (`formBPllInput`): the PLL input `v_cq^c = −sin θ v_cd + cos θ v_cq`.
The singular-perturbation (Tikhonov) justification of the reduction and its error are **not**
formalized; the reduced 2D model is `piPLLField p.formBChar K_p K_i δω` of
`theorem/GFL/PIPLL.lean`, valid as a model only under the note's assumptions (strong grid,
time-scale separation, frozen outer loops). Continuous time; no saturation, PWM or delay.

Results.
* `cc_projection` (B): the current-loop part of `ω_g C_f v_cq^c` is identically `−i_d*`.
* `pllInput_expansion` (B): for any line solution `i_g = α + β sin θ + γ cos θ`, the double-angle
  expansion with exactly the coefficients `c₀ … c₄` of §1.7.
* `quasiSteady_iff` (B): with `ω_g C_f ≠ 0` and the added premise
  `R_g² + (ω_g L_g − 1/(ω_g C_f))² ≠ 0`, the quasi-steady equations have exactly one solution,
  given in closed form.
* `lineCurrent_rotational` (B): that solution has `γ_q = −β_d`, `γ_d = β_q`, hence `c₃ = c₄ = 0`.
* `pllInput_of_quasiSteady` (B): along the quasi-steady manifold the PLL input is exactly
  `formBChar θ = (1/(ω_g C_f)) [c₀ + c₁ sin θ + c₂ cos θ]` (first-order trigonometric).
* `formB_equilibria_ncard_le_two` (A): the reduced form-B GFL-PLL has at most two equilibria
  per `2π` window of `θ` (for `V_g ≠ 0`, `K_i ≠ 0`).

Source: work-sync `theory/T-gfl-dynamics.md` §1.0 (frame rotations), §1.4–§1.9, §1.11, §1.14.
Already in powerlib: the two rotation matrices are mutually inverse — `Transform.park_mul_rot`,
`Transform.rot_mul_park` (`T(θ) = park θ`, `T(−θ) = rot θ`); not repeated here.
Correction (§1.6, added premise): the line/LC algebraic system is uniquely solvable only when
`R_g² + (ω_g L_g − 1/(ω_g C_f))² ≠ 0` (and `ω_g C_f ≠ 0`); the note does not state it.
Correction (§1.7–§1.8, §1.9 table, §1.11, §1.14 region E): the exact quasi-steady line solution
has the rotational structure `γ_q = −β_d`, `γ_d = β_q`, so `c₃ = (γ_q + β_d)/2 = 0` and
`c₄ = (γ_d − β_q)/2 = 0` identically: the form-B characteristic has **no** `sin 2θ`, `cos 2θ`
terms. Consequently the claims "4 equilibria per period (two stable, two saddles; region E)" and
"the `2θ` terms make the potential/basins asymmetric" are false for the form-B model of this note:
there are at most 2 equilibria per period. (The general double-angle bookkeeping of §1.7 is right;
only its conclusion that `c₃, c₄` are generically nonzero is wrong.)
Not formalized: §1.11 "every bounded trajectory is attracted by some basin" (not proved in the
note and possibly false); the Tikhonov error estimates.

Family and connection conclusions. This module states no behaviour and defines no family: every
result is algebra of the reduction or a count of zeros of the reduced field. The equilibrium count
`formB_equilibria_ncard_le_two` (formerly a domain theorem) is static evidence on the model, not a
connection conclusion. Behavioural conclusions about the reduced 2D model go through the PI-PLL
family of `theorem/GFL/PIPLLFamily.lean` with `h = formBChar` (`contDiff_formBChar`).
-/

noncomputable section
namespace powerlib.GFL
open Complex Polynomial Set
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Step 1: the current loop -/

/-- PLL input of form B: `q` component of the capacitor voltage in the controller frame,
`v_cq^c = −sin θ v_cd + cos θ v_cq` (`x^c = T(θ) x^sys`). -/
def formBPllInput (θ vcd vcq : ℝ) : ℝ := -Real.sin θ * vcd + Real.cos θ * vcq

/-- Parameters of the form-B reduction. -/
structure FormBParams where
  /-- Grid angular frequency (constant). -/
  ωg : ℝ
  /-- Filter capacitance, line inductance and resistance. -/
  Cf : ℝ
  Lg : ℝ
  Rg : ℝ
  /-- Infinite-bus voltage (system d axis). -/
  Vg : ℝ
  /-- Frozen current references (controller frame). -/
  idRef : ℝ
  iqRef : ℝ

namespace FormBParams

variable (p : FormBParams)

/-- `i_d(θ) = cos θ i_d* − sin θ i_q*` (system frame, `i = T(−θ) i*`). -/
def convCurrentD (θ : ℝ) : ℝ := Real.cos θ * p.idRef - Real.sin θ * p.iqRef

/-- `i_q(θ) = sin θ i_d* + cos θ i_q*`. -/
def convCurrentQ (θ : ℝ) : ℝ := Real.sin θ * p.idRef + Real.cos θ * p.iqRef

/-- The current-loop contribution to `ω_g C_f v_cq^c` is the constant `−i_d*` (§1.7 (a)). -/
@[powerlib_foundation] theorem cc_projection (θ : ℝ) :
    -Real.sin θ * p.convCurrentQ θ - Real.cos θ * p.convCurrentD θ = -p.idRef := by
  simp only [convCurrentD, convCurrentQ]
  linear_combination (-p.idRef) * Real.sin_sq_add_cos_sq θ

/-! ## Steps 2–4: quasi-steady LC and line, PLL input -/

/-- Quasi-steady LC-capacitor and line equations at phase offset `θ`. -/
def QuasiSteady (θ vcd vcq igd igq : ℝ) : Prop :=
  p.convCurrentD θ - igd + p.ωg * p.Cf * vcq = 0 ∧
  p.convCurrentQ θ - igq - p.ωg * p.Cf * vcd = 0 ∧
  vcd - p.Vg - p.Rg * igd + p.ωg * p.Lg * igq = 0 ∧
  vcq - p.Rg * igq - p.ωg * p.Lg * igd = 0

/-- `X = 1/(ω_g C_f) − ω_g L_g`. -/
def lineX : ℝ := 1 / (p.ωg * p.Cf) - p.ωg * p.Lg

/-- `Δ = R_g² + X²` (`= R_g² + (ω_g L_g − 1/(ω_g C_f))²`). -/
def lineDet : ℝ := p.Rg ^ 2 + p.lineX ^ 2

/-- `a(θ) = V_g − i_q(θ)/(ω_g C_f)`. -/
def driveA (θ : ℝ) : ℝ := p.Vg - p.convCurrentQ θ / (p.ωg * p.Cf)

/-- `b(θ) = i_d(θ)/(ω_g C_f)`. -/
def driveB (θ : ℝ) : ℝ := p.convCurrentD θ / (p.ωg * p.Cf)

/-- Closed-form line current, d axis: `(−R_g a + X b)/Δ`. -/
def lineCurrentD (θ : ℝ) : ℝ := (-p.Rg * p.driveA θ + p.lineX * p.driveB θ) / p.lineDet

/-- Closed-form line current, q axis: `(−X a − R_g b)/Δ`. -/
def lineCurrentQ (θ : ℝ) : ℝ := (-p.lineX * p.driveA θ - p.Rg * p.driveB θ) / p.lineDet

/-- Closed-form capacitor voltage, d axis: `(i_q − i_gq)/(ω_g C_f)`. -/
def capVoltageD (θ : ℝ) : ℝ := (p.convCurrentQ θ - p.lineCurrentQ θ) / (p.ωg * p.Cf)

/-- Closed-form capacitor voltage, q axis: `(i_gd − i_d)/(ω_g C_f)`. -/
def capVoltageQ (θ : ℝ) : ℝ := (p.lineCurrentD θ - p.convCurrentD θ) / (p.ωg * p.Cf)

/-- Unique solvability of the quasi-steady equations (premises `ω_g C_f ≠ 0`, `Δ ≠ 0`). -/
@[powerlib_foundation] theorem quasiSteady_iff (hωC : p.ωg * p.Cf ≠ 0) (hΔ : p.lineDet ≠ 0)
    (θ vcd vcq igd igq : ℝ) :
    p.QuasiSteady θ vcd vcq igd igq ↔
      igd = p.lineCurrentD θ ∧ igq = p.lineCurrentQ θ ∧
        vcd = p.capVoltageD θ ∧ vcq = p.capVoltageQ θ := by
  have hk1 (z : ℝ) : p.ωg * p.Cf * (z / (p.ωg * p.Cf)) = z := mul_div_cancel₀ z hωC
  constructor
  · rintro ⟨e1, e2, e3, e4⟩
    have hvcd : vcd = (p.convCurrentQ θ - igq) / (p.ωg * p.Cf) := by
      rw [eq_div_iff hωC]
      linarith
    have hvcq : vcq = (igd - p.convCurrentD θ) / (p.ωg * p.Cf) := by
      rw [eq_div_iff hωC]
      linarith
    -- the reduced 2×2 system `−R_g i_gd − X i_gq = a`, `X i_gd − R_g i_gq = b`
    have f3 : -p.Rg * igd - p.lineX * igq = p.driveA θ := by
      rw [hvcd] at e3
      simp only [driveA, lineX]
      linear_combination e3
    have f4 : p.lineX * igd - p.Rg * igq = p.driveB θ := by
      rw [hvcq] at e4
      simp only [driveB, lineX]
      linear_combination e4
    have hgd : igd = p.lineCurrentD θ := by
      simp only [lineCurrentD]
      rw [eq_div_iff hΔ, lineDet]
      linear_combination (-p.Rg) * f3 + p.lineX * f4
    have hgq : igq = p.lineCurrentQ θ := by
      simp only [lineCurrentQ]
      rw [eq_div_iff hΔ, lineDet]
      linear_combination (-p.lineX) * f3 - p.Rg * f4
    refine ⟨hgd, hgq, ?_, ?_⟩
    · rw [hvcd, hgq, capVoltageD]
    · rw [hvcq, hgd, capVoltageQ]
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    have f3 : -p.Rg * p.lineCurrentD θ - p.lineX * p.lineCurrentQ θ = p.driveA θ := by
      simp only [lineCurrentD, lineCurrentQ]
      field_simp
      simp only [lineDet]
      ring
    have f4 : p.lineX * p.lineCurrentD θ - p.Rg * p.lineCurrentQ θ = p.driveB θ := by
      simp only [lineCurrentD, lineCurrentQ]
      field_simp
      simp only [lineDet]
      ring
    simp only [driveA, driveB, lineX] at f3 f4
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [capVoltageQ, hk1]
      ring
    · rw [capVoltageD, hk1]
      ring
    · rw [capVoltageD]
      linear_combination f3
    · rw [capVoltageQ]
      linear_combination f4

/-! ## Trigonometric form of the line solution -/

/-- Coefficients of `i_g = α + β sin θ + γ cos θ`. -/
def αd : ℝ := -p.Rg * p.Vg / p.lineDet
def βd : ℝ := (p.Rg * p.idRef - p.lineX * p.iqRef) / (p.ωg * p.Cf * p.lineDet)
def γd : ℝ := (p.Rg * p.iqRef + p.lineX * p.idRef) / (p.ωg * p.Cf * p.lineDet)
def αq : ℝ := -p.lineX * p.Vg / p.lineDet
def βq : ℝ := (p.lineX * p.idRef + p.Rg * p.iqRef) / (p.ωg * p.Cf * p.lineDet)
def γq : ℝ := (p.lineX * p.iqRef - p.Rg * p.idRef) / (p.ωg * p.Cf * p.lineDet)

@[powerlib_foundation] theorem lineCurrentD_eq (hΔ : p.lineDet ≠ 0) (θ : ℝ) : p.lineCurrentD θ = p.αd + p.βd * Real.sin θ + p.γd * Real.cos θ := by
  simp only [lineCurrentD, driveA, driveB, convCurrentD, convCurrentQ, αd, βd, γd]
  field_simp
  ring

@[powerlib_foundation] theorem lineCurrentQ_eq (hΔ : p.lineDet ≠ 0) (θ : ℝ) : p.lineCurrentQ θ = p.αq + p.βq * Real.sin θ + p.γq * Real.cos θ := by
  simp only [lineCurrentQ, driveA, driveB, convCurrentD, convCurrentQ, αq, βq, γq]
  field_simp
  ring

/-- Rotational structure of the exact line solution: `γ_q = −β_d`, `γ_d = β_q`. -/
@[powerlib_foundation] theorem lineCurrent_rotational : p.γq = -p.βd ∧ p.γd = p.βq := by
  constructor
  · simp only [γq, βd]
    ring
  · simp only [γd, βq]
    ring

/-- Hence the double-angle coefficients of §1.7 vanish: `c₃ = (γ_q + β_d)/2 = 0`,
`c₄ = (γ_d − β_q)/2 = 0`. -/
@[powerlib_foundation] theorem doubleAngle_coefficients_zero :
    (p.γq + p.βd) / 2 = 0 ∧ (p.γd - p.βq) / 2 = 0 := by
  obtain ⟨h1, h2⟩ := p.lineCurrent_rotational
  rw [h1, h2]
  constructor <;> ring

end FormBParams

/-- The double-angle expansion of §1.7 for an arbitrary line solution
`i_g = α + β sin θ + γ cos θ`:
`−sin θ (i_q − i_gq) + cos θ (i_gd − i_d) = c₀ + c₁ sin θ + c₂ cos θ + c₃ sin 2θ + c₄ cos 2θ`,
`c₀ = −i_d* + (β_q + γ_d)/2`, `c₁ = α_q`, `c₂ = α_d`, `c₃ = (γ_q + β_d)/2`, `c₄ = (γ_d − β_q)/2`. -/
@[powerlib_foundation] theorem pllInput_expansion (p : FormBParams)
    (αd βd γd αq βq γq θ : ℝ) :
    -Real.sin θ * (p.convCurrentQ θ - (αq + βq * Real.sin θ + γq * Real.cos θ)) +
        Real.cos θ * ((αd + βd * Real.sin θ + γd * Real.cos θ) - p.convCurrentD θ) =
      (-p.idRef + (βq + γd) / 2) + αq * Real.sin θ + αd * Real.cos θ +
        (γq + βd) / 2 * Real.sin (2 * θ) + (γd - βq) / 2 * Real.cos (2 * θ) := by
  simp only [FormBParams.convCurrentD, FormBParams.convCurrentQ, Real.sin_two_mul,
    Real.cos_two_mul]
  linear_combination (-p.idRef + βq) * Real.sin_sq_add_cos_sq θ

namespace FormBParams

variable (p : FormBParams)

/-- The form-B phase-detector characteristic
`h(θ) = (1/(ω_g C_f)) [(−i_d* + β_q) + α_q sin θ + α_d cos θ]`. -/
def formBChar (θ : ℝ) : ℝ :=
  1 / (p.ωg * p.Cf) * ((-p.idRef + p.βq) + p.αq * Real.sin θ + p.αd * Real.cos θ)

/-- Along the quasi-steady manifold the PLL input is exactly `formBChar θ` (no `2θ` terms). -/
@[powerlib_foundation] theorem pllInput_of_quasiSteady (hωC : p.ωg * p.Cf ≠ 0)
    (hΔ : p.lineDet ≠ 0) {θ vcd vcq igd igq : ℝ} (h : p.QuasiSteady θ vcd vcq igd igq) :
    formBPllInput θ vcd vcq = p.formBChar θ := by
  obtain ⟨hgd, hgq, hvd, hvq⟩ := (p.quasiSteady_iff hωC hΔ θ vcd vcq igd igq).mp h
  have hexp := pllInput_expansion p p.αd p.βd p.γd p.αq p.βq p.γq θ
  obtain ⟨h1, h2⟩ := p.lineCurrent_rotational
  rw [← p.lineCurrentD_eq hΔ, ← p.lineCurrentQ_eq hΔ, h1, h2] at hexp
  rw [formBPllInput, hvd, hvq, capVoltageD, capVoltageQ, formBChar]
  have e : -Real.sin θ * ((p.convCurrentQ θ - p.lineCurrentQ θ) / (p.ωg * p.Cf)) +
      Real.cos θ * ((p.lineCurrentD θ - p.convCurrentD θ) / (p.ωg * p.Cf)) =
      1 / (p.ωg * p.Cf) * (-Real.sin θ * (p.convCurrentQ θ - p.lineCurrentQ θ) +
        Real.cos θ * (p.lineCurrentD θ - p.convCurrentD θ)) := by
    field_simp
  rw [e, hexp]
  ring

/-- `formBChar` as a trigonometric polynomial (coefficients in `trigPoly2` order:
constant, `cos θ`, `sin θ`, `cos 2θ`, `sin 2θ`). -/
@[powerlib_foundation] theorem formBChar_eq_trigPoly2 :
    p.formBChar = SpecialFunctions.trigPoly2 ((-p.idRef + p.βq) / (p.ωg * p.Cf))
      (p.αd / (p.ωg * p.Cf)) (p.αq / (p.ωg * p.Cf)) 0 0 := by
  funext θ
  simp only [formBChar, SpecialFunctions.trigPoly2]
  ring

@[powerlib_foundation] theorem contDiff_formBChar : ContDiff ℝ 1 p.formBChar := by
  rw [formBChar_eq_trigPoly2]
  exact SpecialFunctions.contDiff_trigPoly2 _ _ _ _ _

/-- With `V_g ≠ 0` (and `Δ ≠ 0`, `ω_g C_f ≠ 0`) the characteristic is not identically zero. -/
@[powerlib_foundation] theorem formBChar_coeffs_ne_zero (hωC : p.ωg * p.Cf ≠ 0)
    (hΔ : p.lineDet ≠ 0) (hVg : p.Vg ≠ 0) :
    ¬ ((-p.idRef + p.βq) / (p.ωg * p.Cf) = 0 ∧ p.αd / (p.ωg * p.Cf) = 0 ∧
      p.αq / (p.ωg * p.Cf) = 0) := by
  rintro ⟨-, h2, h3⟩
  have hd : p.αd = 0 := (div_eq_zero_iff.mp h2).resolve_right hωC
  have hq : p.αq = 0 := (div_eq_zero_iff.mp h3).resolve_right hωC
  have h1 : p.Rg * p.Vg = 0 := by
    have h : -p.Rg * p.Vg / p.lineDet = 0 := hd
    rcases div_eq_zero_iff.mp h with h | h
    · linarith
    · exact absurd h hΔ
  have h2 : p.lineX * p.Vg = 0 := by
    have h : -p.lineX * p.Vg / p.lineDet = 0 := hq
    rcases div_eq_zero_iff.mp h with h | h
    · linarith
    · exact absurd h hΔ
  have hR : p.Rg = 0 := (mul_eq_zero.mp h1).resolve_right hVg
  have hXz : p.lineX = 0 := (mul_eq_zero.mp h2).resolve_right hVg
  exact hΔ (by simp [lineDet, hR, hXz])

end FormBParams

/-- The reduced form-B GFL-PLL `θ̇ = K_p h_B(θ) + K_i η − δω`, `η̇ = h_B(θ)` (with `h_B` the exact
quasi-steady characteristic) has at most two equilibria with `θ` in any window `[a, a + 2π)`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem formB_equilibria_ncard_le_two (p : FormBParams) {Kp Ki δω : ℝ}
    (hωC : p.ωg * p.Cf ≠ 0) (hΔ : p.lineDet ≠ 0) (hVg : p.Vg ≠ 0) (hKi : Ki ≠ 0) (a : ℝ) :
    {x : ℝ² | piPLLField p.formBChar Kp Ki δω x = 0 ∧
      x 0 ∈ Ico a (a + 2 * Real.pi)}.ncard ≤ 2 := by
  have hne := p.formBChar_coeffs_ne_zero hωC hΔ hVg
  have hle := SpecialFunctions.trigPoly1_ncard_zeroSet_le_two hne a
  have hfin := SpecialFunctions.trigPoly2_zeroSet_finite (c₂ := 0) (s₂ := 0)
    (fun h => hne ⟨h.1, h.2.1, h.2.2.1⟩) a
  refine le_trans (ncard_le_ncard_of_injOn (fun x : ℝ² => x 0) ?_ ?_ hfin) hle
  · rintro x ⟨hx, hxa⟩
    refine ⟨hxa, ?_⟩
    have := ((piPLLField_eq_zero_iff hKi x).mp hx).1
    rwa [FormBParams.formBChar_eq_trigPoly2] at this
  · rintro x ⟨hx, -⟩ y ⟨hy, -⟩ hxy
    have h1 := ((piPLLField_eq_zero_iff hKi x).mp hx).2
    have h2 := ((piPLLField_eq_zero_iff hKi y).mp hy).2
    exact state_two_ext_iff.mpr ⟨hxy, by rw [h1, h2]⟩

end powerlib.GFL
