import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # GFL-VSC algebraic reduction chain and the closed form of the PLL error signal `h`

Foundation layer for the `vsc-stochastic-stability` project (single grid-following VSC with
LC filter, series R–L line and infinite bus). Everything in this module is an algebraic
identity about the quasi-steady algebra of the 10-state model; no dynamical approximation
(Tikhonov, averaging) is asserted or used.

Model boundary of the algebra.
* Frames. System dq frame (aligned with the nominal grid EMF) and controller (PLL) dq frame.
  System → controller is the Park matrix `T(θ_e) = [[cos θ_e, sin θ_e], [−sin θ_e, cos θ_e]]`
  (`conventions.md` §D4, project `decisions.md` §D1.2); controller → system is `T(−θ_e)`.
  `θ_e = θ̂_g − θ_g` (`decisions.md` §D1.1, the mathematical-text convention, not the code frame;
  the code frame is `θ_code = −θ_text`, see `theorem/VSC/Reduced2D.lean`).
* Direction. Converter port current `i` is OUT-positive (flows from the bridge into the filter /
  grid), as in the project's whole model (`decisions.md` §D1.6); this is the opposite of the
  workspace default IN-positive (`conventions.md` §D1): `I^IN = −i`, `P^absorb = −P_br`.
* Parameters: `L_f, R_f, C_f, L_g, R_g, ω_g, V_g` (filter, line, nominal grid frequency and
  EMF), frozen current references `i_d*, i_q*`, current-loop PI `K_p^cc, K_i^cc`, PLL PI `K_p, K_i`.
  `a = ω_g C_f R_g`, `b = ω_g² C_f L_g`, `Δ = (1 − b)² + a²`. Nondegeneracy hypotheses
  (`ω_g C_f ≠ 0`, `Δ ≠ 0`) are explicit in each statement.
* Quasi-steady algebra (`reduction-pipeline.md` §2–§4):
  current-loop integrator at rest ⇔ `i^c = i*` ⇔ `i = T(−θ_e) i*`;
  capacitor at rest ⇔ `v_c = ((i_q − i_gq), (i_gd − i_d)) / (ω_g C_f)`;
  line at rest (grid EMF `(E_d, E_q)` in the system frame) ⇔
  `[[1 − b, −a], [a, 1 − b]] i_g = (i_d + ω_g C_f E_q, i_q − ω_g C_f E_d)`.
* `h(θ_e) := v_cq^c` on that algebraic set (`reduced-2d-equation.md` §2), with the nominal EMF
  `(E_d, E_q) = (V_g, 0)`; `hE` keeps a general EMF for the noise-sensitivity identities.

Main results.
* `h_eq` : `h θ = c₀ − (V_g/Δ)((1 − b) sin θ + a cos θ)`,
  `c₀ = [((1 − b) i_d* + a i_q*)/Δ − i_d*]/(ω_g C_f)`.
* `h_eq_polar` : `h θ = c₀ − A sin(θ + φ)`, `A = V_g/√Δ`, `φ = arg((1 − b) + j a)` (`= atan2(a, 1 − b)`).
* `hasDerivAt_h`, `contDiff_h`.
* `hE_rotate` : rotating the grid EMF by `α` is the same as shifting `θ_e` by `α`
  (rotational covariance of the whole algebraic chain).
* `hasDerivAt_hE_q` (gauge identity, `sn-critical-scaling.md` §3): `∂h/∂E_q = −h′(θ)/V_g` exactly
  (with `g := −h′ > 0` at a stable point this is `σ_q = g/V_g`); `hasDerivAt_hE_d` with
  `σ_d = −c₀/V_g` at every equilibrium.

Sources: work-sync `projects/vsc-stochastic-stability/notes/concepts/reduction-pipeline.md`
§1–§4; `reduced-2d-equation.md` §1–§2; `sn-critical-scaling.md` §3.

Correction (`reduction-pipeline.md` §4): the boxed line system is printed with (2,1) entry `−a`.
The correct entry is `+a` (`lineMatrix`); with `−a` the line and capacitor equations force
`a · i_gd = 0` (`noteLineSystem_forces`). The project code `models.py::_ig_at_thetae` uses the
correct sign.

Correction (`reduced-2d-equation.md` §1–§2): the note states
`−sin θ · i_q − cos θ · i_d = −i_d* cos 2θ − i_q* sin 2θ` on `i = T(−θ) i*`. In fact the left side is
identically `−i_d*` (`current_part`); the double-angle form is false whenever `i_d* ≠ 0`
(`current_part_ne_doubleAngle`). Hence `h` has no `2θ` term: it is exactly a shifted sinusoid
(`h_eq_polar`). The note's "`2θ` term makes `h` non-sinusoidal / basin asymmetric" does not hold
for this model.

Correction (`sn-critical-scaling.md` §3): the note supports `σ_q = g/V_g` by a numerical check
`|σ_q V_g/g − 1| < 1e−5`; here it is an exact identity.
-/

noncomputable section
namespace powerlib.VSC
open Real Matrix

/-- Parameters of the single GFL-VSC (LC filter + R–L line + infinite bus), current loop and PLL. -/
structure Params where
  /-- Converter-side filter inductance `L_f`. -/
  Lf : ℝ
  /-- Converter-side filter resistance `R_f`. -/
  Rf : ℝ
  /-- Filter capacitance `C_f`. -/
  Cf : ℝ
  /-- Line inductance `L_g`. -/
  Lg : ℝ
  /-- Line resistance `R_g`. -/
  Rg : ℝ
  /-- Nominal grid angular frequency `ω_g`. -/
  ωg : ℝ
  /-- Grid EMF amplitude `V_g` (d-axis of the system frame). -/
  Vg : ℝ
  /-- Frozen d-axis current reference `i_d*`. -/
  idRef : ℝ
  /-- Frozen q-axis current reference `i_q*`. -/
  iqRef : ℝ
  /-- Current-loop proportional gain `K_p^cc`. -/
  Kpcc : ℝ
  /-- Current-loop integral gain `K_i^cc`. -/
  Kicc : ℝ
  /-- PLL proportional gain `K_p`. -/
  Kp : ℝ
  /-- PLL integral gain `K_i`. -/
  Ki : ℝ

/-! ### Park transformation components (`conventions.md` §D4) -/

/-- d-component of `T(θ) x` (system → controller). -/
def parkD (θ xd xq : ℝ) : ℝ := cos θ * xd + sin θ * xq

/-- q-component of `T(θ) x` (system → controller). -/
def parkQ (θ xd xq : ℝ) : ℝ := -sin θ * xd + cos θ * xq

/-- d-component of `T(−θ) x` (controller → system). -/
def iparkD (θ xd xq : ℝ) : ℝ := cos θ * xd - sin θ * xq

/-- q-component of `T(−θ) x` (controller → system). -/
def iparkQ (θ xd xq : ℝ) : ℝ := sin θ * xd + cos θ * xq

@[simp, powerlib_foundation] theorem parkD_ipark (θ x y : ℝ) :
    parkD θ (iparkD θ x y) (iparkQ θ x y) = x := by
  unfold parkD iparkD iparkQ; linear_combination x * sin_sq_add_cos_sq θ

@[simp, powerlib_foundation] theorem parkQ_ipark (θ x y : ℝ) :
    parkQ θ (iparkD θ x y) (iparkQ θ x y) = y := by
  unfold parkQ iparkD iparkQ; linear_combination y * sin_sq_add_cos_sq θ

@[simp, powerlib_foundation] theorem iparkD_park (θ x y : ℝ) :
    iparkD θ (parkD θ x y) (parkQ θ x y) = x := by
  unfold parkD parkQ iparkD; linear_combination x * sin_sq_add_cos_sq θ

@[simp, powerlib_foundation] theorem iparkQ_park (θ x y : ℝ) :
    iparkQ θ (parkD θ x y) (parkQ θ x y) = y := by
  unfold parkD parkQ iparkQ; linear_combination y * sin_sq_add_cos_sq θ

/-- The rotation preserves the dot product. -/
@[powerlib_foundation] theorem park_dot (θ x y u v : ℝ) :
    parkD θ x y * parkD θ u v + parkQ θ x y * parkQ θ u v = x * u + y * v := by
  unfold parkD parkQ; linear_combination (x * u + y * v) * sin_sq_add_cos_sq θ

/-- The rotation commutes with the generator `J (x, y) = (−y, x)`. -/
@[powerlib_foundation] theorem parkD_J (θ x y : ℝ) : parkD θ (-y) x = -parkQ θ x y := by
  unfold parkD parkQ; ring

@[powerlib_foundation] theorem parkQ_J (θ x y : ℝ) : parkQ θ (-y) x = parkD θ x y := by
  unfold parkD parkQ; ring

namespace Params

variable (p : Params)

/-- `a = ω_g C_f R_g`. -/
def a : ℝ := p.ωg * p.Cf * p.Rg

/-- `b = ω_g² C_f L_g`. -/
def b : ℝ := p.ωg ^ 2 * p.Cf * p.Lg

/-- `Δ = (1 − b)² + a²`, the determinant of the line system. -/
def Δ : ℝ := (1 - p.b) ^ 2 + p.a ^ 2

/-- `ω_g C_f`. -/
def wC : ℝ := p.ωg * p.Cf

/-- The corrected line-system matrix `[[1 − b, −a], [a, 1 − b]]`. -/
def lineMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1 - p.b, -p.a; p.a, 1 - p.b]

/-- The matrix printed in `reduction-pipeline.md` §4 (wrong (2,1) entry). -/
def noteLineMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1 - p.b, -p.a; -p.a, 1 - p.b]

@[powerlib_foundation] theorem det_lineMatrix : p.lineMatrix.det = p.Δ := by
  simp [lineMatrix, Δ, Matrix.det_fin_two]; ring

@[powerlib_foundation] theorem Δ_nonneg : 0 ≤ p.Δ := by
  unfold Δ; positivity

@[powerlib_foundation] theorem Δ_pos (h : p.Δ ≠ 0) : 0 < p.Δ :=
  lt_of_le_of_ne p.Δ_nonneg (Ne.symm h)

/-! ### Step 1: current loop at rest -/

/-- Converter current on the current-loop quasi-steady set, `i = T(−θ) i*` (d-axis). -/
def iD (θ : ℝ) : ℝ := iparkD θ p.idRef p.iqRef

/-- Converter current on the current-loop quasi-steady set, `i = T(−θ) i*` (q-axis). -/
def iQ (θ : ℝ) : ℝ := iparkQ θ p.idRef p.iqRef

/-- `reduction-pipeline.md` §2: the current-loop integrators are at rest
(`ξ̇^c = i* − T(θ) i = 0`) iff `i = T(−θ) i*`. -/
@[powerlib_foundation] theorem current_qss_iff (θ id iq : ℝ) :
    (p.idRef - parkD θ id iq = 0 ∧ p.iqRef - parkQ θ id iq = 0) ↔
      (id = p.iD θ ∧ iq = p.iQ θ) := by
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : parkD θ id iq = p.idRef := by linarith
    have e2 : parkQ θ id iq = p.iqRef := by linarith
    refine ⟨?_, ?_⟩
    · rw [iD, ← e1, ← e2, iparkD_park]
    · rw [iQ, ← e1, ← e2, iparkQ_park]
  · rintro ⟨rfl, rfl⟩
    simp [iD, iQ]

/-- `sin θ · i_q + cos θ · i_d = i_d*` on `i = T(−θ) i*`. -/
@[powerlib_foundation] theorem sin_iQ_add_cos_iD (θ : ℝ) :
    sin θ * p.iQ θ + cos θ * p.iD θ = p.idRef := by
  unfold iQ iD iparkQ iparkD; linear_combination p.idRef * sin_sq_add_cos_sq θ

/-- `cos θ · i_q − sin θ · i_d = i_q*` on `i = T(−θ) i*`. -/
@[powerlib_foundation] theorem cos_iQ_sub_sin_iD (θ : ℝ) :
    cos θ * p.iQ θ - sin θ * p.iD θ = p.iqRef := by
  unfold iQ iD iparkQ iparkD; linear_combination p.iqRef * sin_sq_add_cos_sq θ

/-- The current part of `v_cq^c`: `−sin θ · i_q − cos θ · i_d ≡ −i_d*` (no double-angle term). -/
@[powerlib_foundation] theorem current_part (θ : ℝ) :
    -sin θ * p.iQ θ + cos θ * (-p.iD θ) = -p.idRef := by
  linear_combination -(p.sin_iQ_add_cos_iD θ)

/-- Correction: the double-angle form printed in `reduced-2d-equation.md` §1 is false as soon as
`i_d* ≠ 0` (it fails at `θ = π/2`). -/
@[powerlib_foundation] theorem current_part_ne_doubleAngle (hid : p.idRef ≠ 0) :
    ¬ ∀ θ : ℝ, -sin θ * p.iQ θ + cos θ * (-p.iD θ) =
      -p.idRef * cos (2 * θ) - p.iqRef * sin (2 * θ) := by
  intro h
  have h1 := h (π / 2)
  rw [current_part] at h1
  have e1 : cos (2 * (π / 2)) = -1 := by rw [show 2 * (π / 2) = π by ring, cos_pi]
  have e2 : sin (2 * (π / 2)) = 0 := by rw [show 2 * (π / 2) = π by ring, sin_pi]
  rw [e1, e2] at h1
  exact hid (by linarith)

/-! ### Steps 2–3: capacitor and line at rest -/

/-- `reduction-pipeline.md` §3–§4 with a general grid EMF `(E_d, E_q)`: the capacitor
equations `C_f v̇_c = 0` and the line equations `L_g i̇_g = 0` hold iff `v_c` is given by the
capacitor formula and `i_g` solves the corrected line system. -/
@[powerlib_foundation] theorem lc_line_qss_iff (hwC : p.wC ≠ 0) (Ed Eq id iq vcd vcq igd igq : ℝ) :
    (id - igd + p.wC * vcq = 0 ∧ iq - igq - p.wC * vcd = 0 ∧
      vcd - Ed - p.Rg * igd + p.ωg * p.Lg * igq = 0 ∧
      vcq - Eq - p.Rg * igq - p.ωg * p.Lg * igd = 0) ↔
    (p.lineMatrix *ᵥ ![igd, igq] = ![id + p.wC * Eq, iq - p.wC * Ed] ∧
      vcd = (iq - igq) / p.wC ∧ vcq = (igd - id) / p.wC) := by
  have ha : p.a = p.wC * p.Rg := by simp [a, wC]
  have hb : p.b = p.wC * (p.ωg * p.Lg) := by simp [b, wC]; ring
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hvd : vcd = (iq - igq) / p.wC := by field_simp; linarith
    have hvq : vcq = (igd - id) / p.wC := by field_simp; linarith
    refine ⟨?_, hvd, hvq⟩
    ext i; fin_cases i
    · simp [lineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha, hb]
      linear_combination -h1 + p.wC * h4
    · simp [lineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha, hb]
      linear_combination -h2 - p.wC * h3
  · rintro ⟨hM, hvd, hvq⟩
    have hM0 := congrFun hM 0
    have hM1 := congrFun hM 1
    simp [lineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha, hb] at hM0 hM1
    have e1 : p.wC * vcq = igd - id := by rw [hvq]; field_simp
    have e2 : p.wC * vcd = iq - igq := by rw [hvd]; field_simp
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · have : p.wC * (vcd - Ed - p.Rg * igd + p.ωg * p.Lg * igq) = 0 := by
        linear_combination e2 - hM1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hwC
      · exact h
    · have : p.wC * (vcq - Eq - p.Rg * igq - p.ωg * p.Lg * igd) = 0 := by
        linear_combination e1 + hM0
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hwC
      · exact h

/-- Correction witness: the line system with the note's (2,1) entry `−a`, together with the
capacitor and line equations, forces `a · i_gd = 0`. -/
@[powerlib_foundation] theorem noteLineSystem_forces (hwC : p.wC ≠ 0) (Ed Eq id iq vcd vcq igd igq : ℝ)
    (hqss : id - igd + p.wC * vcq = 0 ∧ iq - igq - p.wC * vcd = 0 ∧
      vcd - Ed - p.Rg * igd + p.ωg * p.Lg * igq = 0 ∧
      vcq - Eq - p.Rg * igq - p.ωg * p.Lg * igd = 0)
    (hnote : p.noteLineMatrix *ᵥ ![igd, igq] = ![id + p.wC * Eq, iq - p.wC * Ed]) :
    p.a * igd = 0 := by
  obtain ⟨hM, -, -⟩ := (p.lc_line_qss_iff hwC Ed Eq id iq vcd vcq igd igq).mp hqss
  have h1 := congrFun hM 1
  have h2 := congrFun hnote 1
  simp [lineMatrix, noteLineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2
  linarith

/-- Solution of the corrected line system (Cramer's rule), d-axis. -/
def solD (id iq Ed Eq : ℝ) : ℝ :=
  ((1 - p.b) * (id + p.wC * Eq) + p.a * (iq - p.wC * Ed)) / p.Δ

/-- Solution of the corrected line system (Cramer's rule), q-axis. -/
def solQ (id iq Ed Eq : ℝ) : ℝ :=
  (-p.a * (id + p.wC * Eq) + (1 - p.b) * (iq - p.wC * Ed)) / p.Δ

@[powerlib_foundation] theorem lineMatrix_mulVec_iff (hΔ : p.Δ ≠ 0) (id iq Ed Eq igd igq : ℝ) :
    p.lineMatrix *ᵥ ![igd, igq] = ![id + p.wC * Eq, iq - p.wC * Ed] ↔
      (igd = p.solD id iq Ed Eq ∧ igq = p.solQ id iq Ed Eq) := by
  have hΔ' : (1 - p.b) ^ 2 + p.a ^ 2 ≠ 0 := hΔ
  constructor
  · intro hM
    have h0 := congrFun hM 0
    have h1 := congrFun hM 1
    simp [lineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    refine ⟨?_, ?_⟩
    · rw [solD, Δ, eq_div_iff hΔ']
      linear_combination (1 - p.b) * h0 + p.a * h1
    · rw [solQ, Δ, eq_div_iff hΔ']
      linear_combination -p.a * h0 + (1 - p.b) * h1
  · rintro ⟨rfl, rfl⟩
    ext i; fin_cases i
    · simp [lineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, solD, solQ, Δ]
      field_simp; ring
    · simp [lineMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, solD, solQ, Δ]
      field_simp; ring

/-! ### The algebraic chain as functions of `θ_e` -/

/-- Line current on the quasi-steady set, d-axis, grid EMF `(E_d, E_q)`. -/
def igD (θ Ed Eq : ℝ) : ℝ := p.solD (p.iD θ) (p.iQ θ) Ed Eq

/-- Line current on the quasi-steady set, q-axis, grid EMF `(E_d, E_q)`. -/
def igQ (θ Ed Eq : ℝ) : ℝ := p.solQ (p.iD θ) (p.iQ θ) Ed Eq

/-- Capacitor voltage on the quasi-steady set, d-axis. -/
def vcD (θ Ed Eq : ℝ) : ℝ := (p.iQ θ - p.igQ θ Ed Eq) / p.wC

/-- Capacitor voltage on the quasi-steady set, q-axis. -/
def vcQ (θ Ed Eq : ℝ) : ℝ := (p.igD θ Ed Eq - p.iD θ) / p.wC

/-- PLL error signal `v_cq^c` on the quasi-steady set, for a general grid EMF `(E_d, E_q)`. -/
def hE (θ Ed Eq : ℝ) : ℝ := parkQ θ (p.vcD θ Ed Eq) (p.vcQ θ Ed Eq)

/-- PLL error signal `h(θ_e) = v_cq^c(θ_e)` with the nominal grid EMF `(V_g, 0)`. -/
def h (θ : ℝ) : ℝ := p.hE θ p.Vg 0

/-- Constant term `c₀ = [((1 − b) i_d* + a i_q*)/Δ − i_d*]/(ω_g C_f)`. -/
def c0 : ℝ := (((1 - p.b) * p.idRef + p.a * p.iqRef) / p.Δ - p.idRef) / p.wC

/-- Amplitude `A = V_g/√Δ`. -/
def amp : ℝ := p.Vg / √p.Δ

/-- Phase `φ = arg((1 − b) + j a) = atan2(a, 1 − b)`. -/
def phase : ℝ := Complex.arg ⟨1 - p.b, p.a⟩

/-- Closed form of `h` with a general grid EMF:
`h_E(θ) = c₀ + [(1 − b)(cos θ E_q − sin θ E_d) − a(cos θ E_d + sin θ E_q)]/Δ`. -/
@[powerlib_foundation] theorem hE_eq (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ Ed Eq : ℝ) :
    p.hE θ Ed Eq = p.c0 +
      ((1 - p.b) * (cos θ * Eq - sin θ * Ed) - p.a * (cos θ * Ed + sin θ * Eq)) / p.Δ := by
  have L1 := p.sin_iQ_add_cos_iD θ
  have L2 := p.cos_iQ_sub_sin_iD θ
  have hu : p.wC * p.wC⁻¹ = 1 := mul_inv_cancel₀ hwC
  have hv : p.Δ * p.Δ⁻¹ = 1 := mul_inv_cancel₀ hΔ
  simp only [hE, parkQ, vcD, vcQ, igD, igQ, solD, solQ, c0, div_eq_mul_inv]
  set u := p.wC⁻¹
  set v := p.Δ⁻¹
  linear_combination (u * (v * (1 - p.b) - 1)) * L1 + (u * v * p.a) * L2 +
    (v * ((1 - p.b) * (cos θ * Eq - sin θ * Ed) - p.a * (cos θ * Ed + sin θ * Eq))) * hu

/-- Closed form of the PLL error signal: `h(θ) = c₀ − (V_g/Δ)((1 − b) sin θ + a cos θ)`. -/
@[powerlib_foundation] theorem h_eq (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    p.h θ = p.c0 - p.Vg / p.Δ * ((1 - p.b) * sin θ + p.a * cos θ) := by
  rw [h, p.hE_eq hwC hΔ]
  ring

@[powerlib_foundation] theorem sqrt_Δ_mul_self : √p.Δ * √p.Δ = p.Δ :=
  Real.mul_self_sqrt p.Δ_nonneg

@[powerlib_foundation] theorem sqrt_Δ_pos (hΔ : p.Δ ≠ 0) : 0 < √p.Δ :=
  Real.sqrt_pos.mpr (p.Δ_pos hΔ)

/-- `cos φ = (1 − b)/√Δ`. -/
@[powerlib_foundation] theorem cos_phase (hΔ : p.Δ ≠ 0) : cos p.phase = (1 - p.b) / √p.Δ := by
  have hz : (⟨1 - p.b, p.a⟩ : ℂ) ≠ 0 := by
    intro hz
    apply hΔ
    have h1 : (1 - p.b) = 0 := congrArg Complex.re hz
    have h2 : p.a = 0 := congrArg Complex.im hz
    simp [Δ, h1, h2]
  rw [phase, Complex.cos_arg hz, Complex.norm_def, Complex.normSq_mk, Δ]
  dsimp only; rw [sq, sq]

/-- `sin φ = a/√Δ`. -/
@[powerlib_foundation] theorem sin_phase : sin p.phase = p.a / √p.Δ := by
  rw [phase, Complex.sin_arg, Complex.norm_def, Complex.normSq_mk, Δ]
  dsimp only; rw [sq, sq]

/-- `(1 − b) sin θ + a cos θ = √Δ · sin(θ + φ)`. -/
@[powerlib_foundation] theorem sinusoid_eq (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    (1 - p.b) * sin θ + p.a * cos θ = √p.Δ * sin (θ + p.phase) := by
  have hs := p.sqrt_Δ_pos hΔ
  rw [sin_add, p.cos_phase hΔ, p.sin_phase]
  field_simp

/-- `(1 − b) cos θ − a sin θ = √Δ · cos(θ + φ)`. -/
@[powerlib_foundation] theorem cosinusoid_eq (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    (1 - p.b) * cos θ - p.a * sin θ = √p.Δ * cos (θ + p.phase) := by
  have hs := p.sqrt_Δ_pos hΔ
  rw [cos_add, p.cos_phase hΔ, p.sin_phase]
  field_simp

/-- `(V_g/Δ) √Δ = A`. -/
@[powerlib_foundation] theorem amp_eq (hΔ : p.Δ ≠ 0) : p.Vg / p.Δ * √p.Δ = p.amp := by
  have hs := p.sqrt_Δ_pos hΔ
  rw [amp, div_mul_eq_mul_div, div_eq_div_iff hΔ hs.ne', mul_assoc,
    Real.mul_self_sqrt p.Δ_nonneg]

/-- Polar closed form: `h(θ) = c₀ − A sin(θ + φ)`, `A = V_g/√Δ`, `φ = atan2(a, 1 − b)`. -/
@[powerlib_foundation] theorem h_eq_polar (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    p.h θ = p.c0 - p.amp * sin (θ + p.phase) := by
  rw [p.h_eq hwC hΔ, p.sinusoid_eq hΔ, ← p.amp_eq hΔ]
  ring

@[powerlib_foundation] theorem h_funext (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) :
    p.h = fun θ => p.c0 - p.amp * sin (θ + p.phase) :=
  funext (p.h_eq_polar hwC hΔ)

/-- `h′(θ) = −A cos(θ + φ)`. -/
@[powerlib_foundation] theorem hasDerivAt_h (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    HasDerivAt p.h (-(p.amp * cos (θ + p.phase))) θ := by
  rw [p.h_funext hwC hΔ]
  have h1 : HasDerivAt (fun θ : ℝ => θ + p.phase) 1 θ := (hasDerivAt_id θ).add_const _
  have h2 := (h1.sin).const_mul p.amp
  simpa using h2.const_sub p.c0

@[powerlib_foundation] theorem deriv_h (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    deriv p.h θ = -(p.amp * cos (θ + p.phase)) :=
  (p.hasDerivAt_h hwC hΔ θ).deriv

/-- `h′(θ) = −(V_g/Δ)((1 − b) cos θ − a sin θ)`. -/
@[powerlib_foundation] theorem deriv_h_eq (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ : ℝ) :
    deriv p.h θ = -(p.Vg / p.Δ * ((1 - p.b) * cos θ - p.a * sin θ)) := by
  rw [p.deriv_h hwC hΔ, p.cosinusoid_eq hΔ, ← p.amp_eq hΔ]
  ring

@[powerlib_foundation] theorem contDiff_h (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) {k : WithTop ℕ∞} :
    ContDiff ℝ k p.h := by
  rw [p.h_funext hwC hΔ]
  fun_prop

/-! ### EMF rotation covariance and noise sensitivities -/

/-- Rotating the grid EMF by `α` is the same as shifting the PLL angle by `α`:
`h_{V_g e^{jα}}(θ) = h(θ − α)`. -/
@[powerlib_foundation] theorem hE_rotate (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ α : ℝ) :
    p.hE θ (p.Vg * cos α) (p.Vg * sin α) = p.h (θ - α) := by
  rw [p.hE_eq hwC hΔ, p.h_eq hwC hΔ, sin_sub, cos_sub]
  ring

/-- `h_E` is affine in the q-axis EMF; its slope is `((1 − b) cos θ − a sin θ)/Δ`. -/
@[powerlib_foundation] theorem hasDerivAt_hE_q (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ Ed e : ℝ) :
    HasDerivAt (fun Eq => p.hE θ Ed Eq) (((1 - p.b) * cos θ - p.a * sin θ) / p.Δ) e := by
  have hf : (fun Eq => p.hE θ Ed Eq) = fun Eq =>
      (p.c0 + ((1 - p.b) * (-(sin θ * Ed)) - p.a * (cos θ * Ed)) / p.Δ) +
        (((1 - p.b) * cos θ - p.a * sin θ) / p.Δ) * Eq := by
    funext Eq; rw [p.hE_eq hwC hΔ]; ring
  rw [hf]
  simpa using ((hasDerivAt_id e).const_mul (((1 - p.b) * cos θ - p.a * sin θ) / p.Δ)).const_add
    (p.c0 + ((1 - p.b) * (-(sin θ * Ed)) - p.a * (cos θ * Ed)) / p.Δ)

/-- Gauge identity (`sn-critical-scaling.md` §3), exact: the q-axis EMF sensitivity of the PLL
error signal is `σ_q = ∂h/∂E_q = −h′(θ)/V_g` (text convention; `= g/V_g` with `g = −h′`). -/
@[powerlib_foundation] theorem sigma_q_eq (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hVg : p.Vg ≠ 0) (θ : ℝ) :
    HasDerivAt (fun Eq => p.hE θ p.Vg Eq) (-deriv p.h θ / p.Vg) 0 := by
  convert p.hasDerivAt_hE_q hwC hΔ θ p.Vg 0 using 1
  rw [p.deriv_h_eq hwC hΔ]
  field_simp

/-- The d-axis EMF sensitivity `σ_d = ∂h/∂E_d = −((1 − b) sin θ + a cos θ)/Δ`. -/
@[powerlib_foundation] theorem hasDerivAt_hE_d (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (θ e : ℝ) :
    HasDerivAt (fun Ed => p.hE θ Ed 0) (-((1 - p.b) * sin θ + p.a * cos θ) / p.Δ) e := by
  have hf : (fun Ed => p.hE θ Ed 0) = fun Ed =>
      p.c0 + (-((1 - p.b) * sin θ + p.a * cos θ) / p.Δ) * Ed := by
    funext Ed; rw [p.hE_eq hwC hΔ]; ring
  rw [hf]
  simpa using ((hasDerivAt_id e).const_mul (-((1 - p.b) * sin θ + p.a * cos θ) / p.Δ)).const_add
    p.c0

/-- At every zero of `h` (every PLL equilibrium) the amplitude sensitivity is `σ_d = −c₀/V_g`;
in particular it stays finite at the saddle-node. -/
@[powerlib_foundation] theorem sigma_d_at_zero (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hVg : p.Vg ≠ 0)
    {θ : ℝ} (hθ : p.h θ = 0) :
    HasDerivAt (fun Ed => p.hE θ Ed 0) (-p.c0 / p.Vg) p.Vg := by
  convert p.hasDerivAt_hE_d hwC hΔ θ p.Vg using 1
  rw [p.h_eq hwC hΔ] at hθ
  field_simp
  field_simp at hθ
  linarith

end Params

end powerlib.VSC
