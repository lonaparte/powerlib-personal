import theorem.Passive.Series
import theorem.Dynamics.Coordinates
import theorem.Dynamics.LaSalle.Periodic
import theorem.SpecialFunctions.PolynomialSigns
import theorem.SpecialFunctions.Sinusoid
import theorem.SpecialFunctions.TrigZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! # Grid-forming converter with Q–V droop and a virtual impedance: the terminal quartic

Domain module.

Model boundary.
* The reduced (quasi-static line) grid-forming converter with reactive-power–voltage droop and a
  virtual impedance: an internal EMF `E ∠ δ` behind the virtual impedance `Z_v = R_v + jX_v`
  (`virtual`), the converter terminal, and the grid branch `Z_g = R_g + jX_g` (`line`) to a stiff
  grid `V ∠ 0`; both are `Passive.SeriesRLC ⟨R, X, 0⟩` at the per-unit grid frequency `ω = 1`, in
  series `Z_t = Z_v + Z_g` (`total`, `|Z_t|² = ztsq`), in a dq frame rotating at the nominal
  frequency. The current is quasi-steady, `Ī = (Ē − V)/Z_t` (`current`), positive out of the
  converter; the terminal voltage is `v̄_t = Ē − Z_v Ī` (`terminalVoltage`) and both powers are
  measured at the terminal, `P_t + jQ_t = v̄_t Ī*` (`terminalPower`, `Pt`, `Qt`), export-positive
  (GFM family exception, as in `theorem/GridTiedConverter/GFM/VSMLPF.lean`).
* State `x = (δ, Δω, Q_f) : Dynamics.State 3`, in this order: EMF angle relative to the grid
  (rad), frequency deviation (rad/s), filtered terminal reactive power (pu). Continuous time,
  autonomous, constant set-points `P_ref`, `Q_ref`, `E₀` (no input):
  `δ̇ = Δω`, `M Δω̇ = P_ref − P_t(δ, E) − D Δω`, `Q̇_f = ω_q (Q_t(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)` (`field`, `emf`); the active power is not filtered. The model of
  `theorem/GridTiedConverter/GFM/QVDroop.lean` has no virtual impedance and measures the powers at
  the EMF.
* Parameters are free reals; every theorem lists its range. The physical range is `M > 0`,
  `ω_q > 0`, droop gain `n_q > 0`, `X_g > 0`, an inductive or zero virtual reactance `X_v ≥ 0`,
  `V > 0` and `E₀ + n_q Q_ref > 0`; `R_g`, `R_v` and `D` are arbitrary. The formal model admits an
  EMF of either sign; equilibria with `E > 0` are the physical ones. `dz = |Z_g|² − |Z_v|²`
  separates the generic case `|Z_v| ≠ |Z_g|` from the degenerate one `|Z_v| = |Z_g|`.
* Level: the equilibrium set and its count per period window `[a, a + 2π)` of the angle.
  Excluded: linearization and stability, the active-power filter, line dynamics, inner voltage
  and current loops, current limiting, PLL, delay, PWM.

Source: study note GFM equilibrium counting (topic t6 (b), virtual impedance: the terminal-power
identity `|Z_t|² S̄_t = Z_g E² − Z_v V² − Z_g ζ + Z_v ζ*` with `ζ = E V e^{jδ}`, the R-linear map of
`ζ` with determinant `|Z_g|² − |Z_v|²`, the quartic and its sign pattern, the degenerate case;
checked numerically there, derived here); Descartes' rule of signs (Mathlib
`Polynomial.roots_countP_pos_le_signVariations`, read through
`theorem/SpecialFunctions/PolynomialSigns.lean`); the zeros of a shifted sinusoid
(`theorem/SpecialFunctions/Sinusoid.lean`); injectivity of `θ ↦ e^{jθ}` on a window
(`SpecialFunctions.injOn_cexp_mul_I_Ico`).

Results.
* Terminal power, derived from the circuit: the identity
  `|Z_t|² S̄_t = Z_g E² − Z_v V² − Z_g ζ + Z_v ζ*`, `ζ = Ē V` (`ztsq_mul_terminalPower`), and with
  `u = E V cos δ`, `w = E V sin δ`, `|Z_t|² P_t = R_g E² − R_v V² + (R_v − R_g) u + (X_g + X_v) w`,
  `|Z_t|² Q_t = X_g E² − X_v V² + (X_v − X_g) u − (R_g + R_v) w` (`Pt_eq`, `Qt_eq`).
* Equilibria (`field_eq_zero_iff`, `balance_of_field_eq_zero`): `Δω = 0`, `P_t = P_ref` and
  `Q_t = Q_f`.
* Elimination: the balance `P_t = P_ref`, `Q_t = Q_ref + (E₀ − E)/n_q` (`qOf`) is the linear
  system `A (u, w) = (b₁(E), b₂(E))` (`b1`, `b2`, `balance_linear`) with `det A = dz`; it implies
  `dz u = U(E)`, `dz w = W(E)` with the adjugate combinations `U`, `W` (`balance_imp`), and is
  equivalent to them for `dz ≠ 0` (`balance_iff`). `U`, `W` are quadratics in `E` (`eval_Upoly`,
  `eval_Wpoly`) with the leading coefficients `u₂ = (|Z_t|² + dz)/2` (`two_mul_u2`),
  `w₂ = R_g X_v − R_v X_g`.
* The terminal quartic `F(E) = U(E)² + W(E)² − dz² V² E²` (`quartic`, `eval_quartic`; `dz²` times
  the study's `f`), its coefficients (`quartic_eq`), leading coefficient `|Z_g|² |Z_t|²`
  (`u2_sq_add_w2_sq`) and cubic coefficient `2 |Z_t|² (X_g(|Z_g|² + |Z_v|²) + 2 X_v |Z_g|²)/n_q`
  (`u2_mul_u1_add_w2_mul_w1`). The EMF of every balanced point is a root of `F`
  (`quartic_isRoot_of_balance`, `quartic_isRoot_of_field_eq_zero`); for `dz ≠ 0` the equilibria
  of a window with EMF in a set `T ∌ 0` are as many as the roots of `F` in `T`
  (`ncard_equilibriaWindow`, a bijection through the EMF, `eq_of_balance`, `injOn_emf`,
  `V ≠ 0`).
* At most two physical equilibria per window, for every virtual impedance with `X_v ≥ 0`
  (`encard_physical_le_two`; `encard` also gives finiteness): for `dz ≠ 0` the coefficients of `F`
  have the sign pattern `(+, ≥ 0, ?, ?, ≥ 0)` (`countP_pos_roots_le_two`, Descartes;
  `encard_physical_le_two_of_dz_ne_zero`); for the degenerate `dz = 0` every physical equilibrium
  has the one positive root of the quadratic `U(E) = 0` (`U_eq_zero_of_dz_eq_zero`,
  `eq_of_U_eq_zero`) as its EMF, and the active-power balance is then a shifted sinusoid in `δ`
  with at most two zeros per window (`encard_physical_le_two_of_dz_eq_zero`).
* Parity for `dz ≠ 0` in the physical range: `F(0) > 0` (`eval_zero_quartic_pos`), so the positive
  roots of `F` counted with multiplicity are `0` or `2` (`countP_pos_roots_eq_zero_or_two`).

Corrections and limits (study note, topic t6 (b)).
* The bound of four zeros per period of a second-order trigonometric polynomial
  (`theorem/SpecialFunctions/TrigZeros.lean`) is not the physical count here: at most two.
* Not formalized: the Jacobian and stability of these equilibria (the study tested them only for
  `Z_v = 0`, `theorem/GridTiedConverter/GFM/QVDroop.lean`).
-/

noncomputable section
namespace powerlib.GFM
open Real Set Polynomial
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext)

/-- Parameters of the reduced grid-forming converter with Q–V droop and a virtual impedance. -/
structure QVDroopVirtual where
  /-- Virtual inertia `M`. -/
  M : ℝ
  /-- Damping `D`. -/
  D : ℝ
  /-- Bandwidth `ω_q` of the reactive-power filter. -/
  ωq : ℝ
  /-- Q–V droop gain `n_q`. -/
  nq : ℝ
  /-- No-load EMF set-point `E₀`. -/
  E0 : ℝ
  /-- Reactive-power set-point `Q_ref`. -/
  Qref : ℝ
  /-- Active-power set-point `P_ref`. -/
  Pref : ℝ
  /-- Grid voltage magnitude `V`. -/
  V : ℝ
  /-- Grid-branch resistance `R_g`. -/
  Rg : ℝ
  /-- Grid-branch reactance `X_g`. -/
  Xg : ℝ
  /-- Virtual resistance `R_v`. -/
  Rv : ℝ
  /-- Virtual reactance `X_v`. -/
  Xv : ℝ

namespace QVDroopVirtual

variable (q : QVDroopVirtual)

/-! ## The circuit and the terminal power -/

/-- The virtual impedance as a series R–L branch at `ω = 1`. -/
def virtual : Passive.SeriesRLC := ⟨q.Rv, q.Xv, 0⟩

/-- The grid branch as a series R–L branch at `ω = 1`. -/
def line : Passive.SeriesRLC := ⟨q.Rg, q.Xg, 0⟩

/-- The series connection `Z_t = Z_v + Z_g`. -/
def total : Passive.SeriesRLC := q.virtual.series q.line

/-- The EMF phasor `Ē = E e^{jδ}`. -/
def emfPhasor (δ E : ℝ) : ℂ := E * Complex.exp (δ * Complex.I)

/-- The line current `Ī = (Ē − V)/Z_t(j)`. -/
def current (δ E : ℝ) : ℂ := (emfPhasor δ E - q.V) / q.total.impedance Complex.I

/-- The terminal voltage `v̄_t = Ē − Z_v(j) Ī`. -/
def terminalVoltage (δ E : ℝ) : ℂ :=
  emfPhasor δ E - q.virtual.impedance Complex.I * q.current δ E

/-- The terminal power `S̄_t = v̄_t Ī*` (export-positive). -/
def terminalPower (δ E : ℝ) : ℂ := q.terminalVoltage δ E * (starRingEnd ℂ) (q.current δ E)

/-- Active power at the terminal. -/
def Pt (δ E : ℝ) : ℝ := (q.terminalPower δ E).re

/-- Reactive power at the terminal. -/
def Qt (δ E : ℝ) : ℝ := (q.terminalPower δ E).im

/-- `|Z_t|² = (R_g + R_v)² + (X_g + X_v)²`. -/
def ztsq : ℝ := (q.Rg + q.Rv) ^ 2 + (q.Xg + q.Xv) ^ 2

/-- `dz = |Z_g|² − |Z_v|²`, the determinant of the elimination. -/
def dz : ℝ := q.Rg ^ 2 + q.Xg ^ 2 - (q.Rv ^ 2 + q.Xv ^ 2)

@[tmio M, powerlib_domain] theorem ztsq_pos (hXg : 0 < q.Xg) (hXv : 0 ≤ q.Xv) : 0 < q.ztsq := by
  have : 0 < (q.Xg + q.Xv) ^ 2 := by positivity
  unfold ztsq
  positivity

@[tmio M, powerlib_domain] private theorem virtual_impedance :
    q.virtual.impedance Complex.I = q.Rv + q.Xv * Complex.I := by
  simp [Passive.SeriesRLC.impedance, virtual]

@[tmio M, powerlib_domain] private theorem total_impedance :
    q.total.impedance Complex.I = (q.Rv + q.Rg : ℝ) + (q.Xv + q.Xg : ℝ) * Complex.I := by
  simp [Passive.SeriesRLC.impedance, total, Passive.SeriesRLC.series, virtual, line]

/-- The terminal-power identity: `|Z_t|² S̄_t = Z_g E² − Z_v V² − Z_g ζ + Z_v ζ*`,
`ζ = Ē V` (`Z_t ≠ 0`). -/
@[tmio M, powerlib_domain] theorem ztsq_mul_terminalPower (hZ : q.ztsq ≠ 0) (δ E : ℝ) :
    (q.ztsq : ℂ) * q.terminalPower δ E =
      (q.Rg + q.Xg * Complex.I) * E ^ 2 - (q.Rv + q.Xv * Complex.I) * q.V ^ 2 -
        (q.Rg + q.Xg * Complex.I) * (emfPhasor δ E * q.V) +
        (q.Rv + q.Xv * Complex.I) * ((starRingEnd ℂ) (emfPhasor δ E) * q.V) := by
  set Zt := q.total.impedance Complex.I with hZt
  set e := emfPhasor δ E with he
  set i := q.current δ E with hi
  have hn : Zt * (starRingEnd ℂ) Zt = (q.ztsq : ℂ) := by
    rw [Complex.mul_conj, hZt, total_impedance, Complex.normSq_add_mul_I]
    simp only [ztsq]
    push_cast
    ring
  have hZt0 : Zt ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hZ (by exact_mod_cast hn.symm)
  have hii : i * Zt = e - q.V := div_mul_cancel₀ _ hZt0
  have hic : (starRingEnd ℂ) i * (starRingEnd ℂ) Zt = (starRingEnd ℂ) e - q.V := by
    rw [← map_mul, hii, map_sub, Complex.conj_ofReal]
  have hee : e * (starRingEnd ℂ) e = (E : ℂ) ^ 2 := by
    rw [Complex.mul_conj, he, emfPhasor, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    push_cast
    ring
  have hZsum : Zt = (q.Rv + q.Xv * Complex.I) + (q.Rg + q.Xg * Complex.I) := by
    rw [hZt, total_impedance]
    push_cast
    ring
  rw [← hn, terminalPower, terminalVoltage, virtual_impedance]
  have key : Zt * (starRingEnd ℂ) Zt * ((e - (q.Rv + q.Xv * Complex.I) * i) *
      (starRingEnd ℂ) i) = (Zt * e - (q.Rv + q.Xv * Complex.I) * (i * Zt)) *
      ((starRingEnd ℂ) i * (starRingEnd ℂ) Zt) := by ring
  rw [key, hii, hic, hZsum]
  linear_combination (q.Rg + q.Xg * Complex.I) * hee

/-- Active power at the terminal: `|Z_t|² P_t = R_g E² − R_v V² + (R_v − R_g) E V cos δ +
(X_g + X_v) E V sin δ`. -/
@[tmio M, powerlib_domain] theorem Pt_eq (δ E : ℝ) :
    q.Pt δ E = (q.Rg * E ^ 2 - q.Rv * q.V ^ 2 + (q.Rv - q.Rg) * (E * q.V * cos δ) +
      (q.Xg + q.Xv) * (E * q.V * sin δ)) / q.ztsq := by
  by_cases hZ : q.ztsq = 0
  · have h0 : q.total.impedance Complex.I = 0 := by
      have h1 : q.Rg + q.Rv = 0 := by unfold ztsq at hZ; nlinarith [sq_nonneg (q.Xg + q.Xv)]
      have h2 : q.Xg + q.Xv = 0 := by unfold ztsq at hZ; nlinarith [sq_nonneg (q.Rg + q.Rv)]
      rw [total_impedance, show q.Rv + q.Rg = 0 by linarith, show q.Xv + q.Xg = 0 by linarith]
      simp
    simp [Pt, terminalPower, current, h0, hZ]
  · have h := congrArg Complex.re (q.ztsq_mul_terminalPower hZ δ E)
    simp only [emfPhasor, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
      Complex.conj_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one] at h
    rw [eq_div_iff hZ, Pt]
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at h
    linear_combination h

/-- Reactive power at the terminal: `|Z_t|² Q_t = X_g E² − X_v V² + (X_v − X_g) E V cos δ −
(R_g + R_v) E V sin δ`. -/
@[tmio M, powerlib_domain] theorem Qt_eq (δ E : ℝ) :
    q.Qt δ E = (q.Xg * E ^ 2 - q.Xv * q.V ^ 2 + (q.Xv - q.Xg) * (E * q.V * cos δ) -
      (q.Rg + q.Rv) * (E * q.V * sin δ)) / q.ztsq := by
  by_cases hZ : q.ztsq = 0
  · have h0 : q.total.impedance Complex.I = 0 := by
      have h1 : q.Rg + q.Rv = 0 := by unfold ztsq at hZ; nlinarith [sq_nonneg (q.Xg + q.Xv)]
      have h2 : q.Xg + q.Xv = 0 := by unfold ztsq at hZ; nlinarith [sq_nonneg (q.Rg + q.Rv)]
      rw [total_impedance, show q.Rv + q.Rg = 0 by linarith, show q.Xv + q.Xg = 0 by linarith]
      simp
    simp [Qt, terminalPower, current, h0, hZ]
  · have h := congrArg Complex.im (q.ztsq_mul_terminalPower hZ δ E)
    simp only [emfPhasor, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.sub_im, Complex.add_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one] at h
    rw [eq_div_iff hZ, Qt]
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at h
    linear_combination h

/-! ## The droop and the closed-loop field -/

/-- The EMF set by the droop, `E = E₀ − n_q (Q_f − Q_ref)`. -/
def emf (Qf : ℝ) : ℝ := q.E0 - q.nq * (Qf - q.Qref)

/-- The filtered reactive power that the droop maps to the EMF `E`, `Q_ref + (E₀ − E)/n_q`. -/
def qOf (E : ℝ) : ℝ := q.Qref + (q.E0 - E) / q.nq

@[tmio M, powerlib_domain] theorem emf_qOf (hnq : q.nq ≠ 0) (E : ℝ) : q.emf (q.qOf E) = E := by
  have h : q.nq * ((q.E0 - E) / q.nq) = q.E0 - E := by field_simp
  simp only [emf, qOf]
  linear_combination -h

@[tmio M, powerlib_domain] theorem qOf_emf (hnq : q.nq ≠ 0) (Qf : ℝ) : q.qOf (q.emf Qf) = Qf := by
  have h : q.nq * (Qf - q.Qref) / q.nq = Qf - q.Qref := by field_simp
  simp only [emf, qOf, sub_sub_cancel]
  linear_combination h

/-- The closed-loop vector field on `(δ, Δω, Q_f)`, powers measured at the terminal. -/
def field (x : State 3) : State 3 :=
  mk3 (x 1) ((q.Pref - q.Pt (x 0) (q.emf (x 2)) - q.D * x 1) / q.M)
    (q.ωq * (q.Qt (x 0) (q.emf (x 2)) - x 2))

@[tmio M, simp, powerlib_domain] theorem field_apply_zero (x : State 3) : q.field x 0 = x 1 := by
  simp [field]

@[tmio M, simp, powerlib_domain] theorem field_apply_one (x : State 3) :
    q.field x 1 = (q.Pref - q.Pt (x 0) (q.emf (x 2)) - q.D * x 1) / q.M := by simp [field]

@[tmio M, simp, powerlib_domain] theorem field_apply_two (x : State 3) :
    q.field x 2 = q.ωq * (q.Qt (x 0) (q.emf (x 2)) - x 2) := by simp [field]

/-- Equilibria: `Δω = 0`, the terminal balance `P_t(δ, E) = P_ref` and a settled filter
`Q_t(δ, E) = Q_f`, `E = E₀ − n_q (Q_f − Q_ref)`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_iff (hM : q.M ≠ 0) (hω : q.ωq ≠ 0)
    (x : State 3) :
    q.field x = 0 ↔
      x 1 = 0 ∧ q.Pt (x 0) (q.emf (x 2)) = q.Pref ∧ q.Qt (x 0) (q.emf (x 2)) = x 2 := by
  constructor
  · intro h
    have e1 := congrArg (fun y : State 3 => y 0) h
    have e2 := congrArg (fun y : State 3 => y 1) h
    have e3 := congrArg (fun y : State 3 => y 2) h
    simp only [field_apply_zero, field_apply_one, field_apply_two, PiLp.zero_apply] at e1 e2 e3
    rw [e1, mul_zero, sub_zero, div_eq_zero_iff, or_iff_left hM, sub_eq_zero] at e2
    rw [mul_eq_zero, or_iff_right hω, sub_eq_zero] at e3
    exact ⟨e1, e2.symm, e3⟩
  · rintro ⟨h1, h2, h3⟩
    apply state3_ext <;> simp [h1, h2, h3]

/-- A balanced point of an equilibrium: the terminal powers are `P_ref` and `qOf E`. -/
@[tmio M, powerlib_domain] theorem balance_of_field_eq_zero (hM : q.M ≠ 0) (hω : q.ωq ≠ 0)
    (hnq : q.nq ≠ 0) {x : State 3} (hx : q.field x = 0) :
    q.Pt (x 0) (q.emf (x 2)) = q.Pref ∧ q.Qt (x 0) (q.emf (x 2)) = q.qOf (q.emf (x 2)) := by
  obtain ⟨-, h1, h2⟩ := (q.field_eq_zero_iff hM hω x).mp hx
  exact ⟨h1, by rw [h2, q.qOf_emf hnq]⟩

/-! ## Elimination -/

/-- Right-hand side `b₁(E) = |Z_t|² P_ref − R_g E² + R_v V²` of the active-power balance. -/
def b1 (E : ℝ) : ℝ := q.ztsq * q.Pref - q.Rg * E ^ 2 + q.Rv * q.V ^ 2

/-- Right-hand side `b₂(E) = |Z_t|² qOf(E) − X_g E² + X_v V²` of the reactive-power balance. -/
def b2 (E : ℝ) : ℝ := q.ztsq * q.qOf E - q.Xg * E ^ 2 + q.Xv * q.V ^ 2

/-- First adjugate combination `U(E) = −((R_g + R_v) b₁ + (X_g + X_v) b₂)`. -/
def U (E : ℝ) : ℝ := -((q.Rg + q.Rv) * q.b1 E + (q.Xg + q.Xv) * q.b2 E)

/-- Second adjugate combination `W(E) = (X_g − X_v) b₁ + (R_v − R_g) b₂`. -/
def W (E : ℝ) : ℝ := (q.Xg - q.Xv) * q.b1 E + (q.Rv - q.Rg) * q.b2 E

/-- The balance is the linear system `A (u, w) = (b₁, b₂)` in `u = E V cos δ`, `w = E V sin δ`,
`A = [[R_v − R_g, X_g + X_v], [X_v − X_g, −(R_g + R_v)]]`, `det A = dz` (`|Z_t| ≠ 0`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem balance_linear (hZ : q.ztsq ≠ 0) (δ E : ℝ) :
    q.Pt δ E = q.Pref ∧ q.Qt δ E = q.qOf E ↔
      (q.Rv - q.Rg) * (E * q.V * cos δ) + (q.Xg + q.Xv) * (E * q.V * sin δ) = q.b1 E ∧
      (q.Xv - q.Xg) * (E * q.V * cos δ) - (q.Rg + q.Rv) * (E * q.V * sin δ) = q.b2 E := by
  rw [Pt_eq, Qt_eq, div_eq_iff hZ, div_eq_iff hZ]
  simp only [b1, b2]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Elimination through the adjugate: a balanced point has `dz E V cos δ = U(E)` and
`dz E V sin δ = W(E)` (`|Z_t| ≠ 0`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem balance_imp (hZ : q.ztsq ≠ 0) {δ E : ℝ}
    (h : q.Pt δ E = q.Pref ∧ q.Qt δ E = q.qOf E) :
    q.dz * (E * q.V * cos δ) = q.U E ∧ q.dz * (E * q.V * sin δ) = q.W E := by
  obtain ⟨h1, h2⟩ := (q.balance_linear hZ δ E).mp h
  simp only [U, W, dz]
  constructor
  · linear_combination (-(q.Rg + q.Rv)) * h1 - (q.Xg + q.Xv) * h2
  · linear_combination (q.Xg - q.Xv) * h1 + (q.Rv - q.Rg) * h2

/-- For `dz ≠ 0` (`|Z_v| ≠ |Z_g|`) the elimination is an equivalence: the balance holds iff
`dz E V cos δ = U(E)` and `dz E V sin δ = W(E)`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem balance_iff (hZ : q.ztsq ≠ 0) (hD : q.dz ≠ 0) (δ E : ℝ) :
    q.Pt δ E = q.Pref ∧ q.Qt δ E = q.qOf E ↔
      q.dz * (E * q.V * cos δ) = q.U E ∧ q.dz * (E * q.V * sin δ) = q.W E := by
  refine ⟨q.balance_imp hZ, fun ⟨hc, hs⟩ => (q.balance_linear hZ δ E).mpr ⟨?_, ?_⟩⟩
  · have h : q.dz * ((q.Rv - q.Rg) * (E * q.V * cos δ) + (q.Xg + q.Xv) * (E * q.V * sin δ) -
        q.b1 E) = 0 := by
      simp only [U, W, dz] at hc hs ⊢
      linear_combination (q.Rv - q.Rg) * hc + (q.Xg + q.Xv) * hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hD)
  · have h : q.dz * ((q.Xv - q.Xg) * (E * q.V * cos δ) - (q.Rg + q.Rv) * (E * q.V * sin δ) -
        q.b2 E) = 0 := by
      simp only [U, W, dz] at hc hs ⊢
      linear_combination (q.Xv - q.Xg) * hc - (q.Rg + q.Rv) * hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hD)

/-! ## The terminal quartic -/

/-- `q₀ = E₀/n_q + Q_ref`. -/
def q0 : ℝ := q.E0 / q.nq + q.Qref

/-- Leading coefficient of `U`. -/
def u2 : ℝ := (q.Rg + q.Rv) * q.Rg + (q.Xg + q.Xv) * q.Xg

/-- Linear coefficient of `U`. -/
def u1 : ℝ := (q.Xg + q.Xv) * q.ztsq / q.nq

/-- Constant coefficient of `U`. -/
def u0 : ℝ :=
  -((q.Rg + q.Rv) * (q.ztsq * q.Pref + q.Rv * q.V ^ 2) +
    (q.Xg + q.Xv) * (q.ztsq * q.q0 + q.Xv * q.V ^ 2))

/-- Leading coefficient of `W`. -/
def w2 : ℝ := q.Rg * q.Xv - q.Rv * q.Xg

/-- Linear coefficient of `W`. -/
def w1 : ℝ := (q.Rg - q.Rv) * q.ztsq / q.nq

/-- Constant coefficient of `W`. -/
def w0 : ℝ :=
  (q.Xg - q.Xv) * (q.ztsq * q.Pref + q.Rv * q.V ^ 2) +
    (q.Rv - q.Rg) * (q.ztsq * q.q0 + q.Xv * q.V ^ 2)

/-- `U` as a polynomial in `E`. -/
def Upoly : ℝ[X] := C q.u2 * Polynomial.X ^ 2 + C q.u1 * Polynomial.X + C q.u0

/-- `W` as a polynomial in `E`. -/
def Wpoly : ℝ[X] := C q.w2 * Polynomial.X ^ 2 + C q.w1 * Polynomial.X + C q.w0

@[tmio M, powerlib_domain] theorem eval_Upoly (E : ℝ) : q.Upoly.eval E = q.U E := by
  simp only [Upoly, eval_add, eval_mul, eval_pow, eval_C, eval_X, U, b1, b2, qOf, u2, u1, u0, q0]
  ring

@[tmio M, powerlib_domain] theorem eval_Wpoly (E : ℝ) : q.Wpoly.eval E = q.W E := by
  simp only [Wpoly, eval_add, eval_mul, eval_pow, eval_C, eval_X, W, b1, b2, qOf, w2, w1, w0, q0]
  ring

/-- `2 u₂ = |Z_t|² + dz`; in the degenerate case `dz = 0`, `u₂ = |Z_t|²/2`. -/
@[tmio M, powerlib_domain] theorem two_mul_u2 : 2 * q.u2 = q.ztsq + q.dz := by
  simp only [u2, ztsq, dz]
  ring

/-- The terminal quartic `F(E) = U(E)² + W(E)² − dz² V² E²`. -/
def quartic : ℝ[X] := q.Upoly ^ 2 + q.Wpoly ^ 2 - C (q.dz ^ 2 * q.V ^ 2) * Polynomial.X ^ 2

@[tmio M, powerlib_domain] theorem eval_quartic (E : ℝ) :
    q.quartic.eval E = q.U E ^ 2 + q.W E ^ 2 - q.dz ^ 2 * q.V ^ 2 * E ^ 2 := by
  simp only [quartic, eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X, eval_Upoly,
    eval_Wpoly]

/-- The coefficients of the terminal quartic. -/
@[tmio M, powerlib_domain] theorem quartic_eq :
    q.quartic = C (q.u2 ^ 2 + q.w2 ^ 2) * Polynomial.X ^ 4 +
      C (2 * (q.u2 * q.u1 + q.w2 * q.w1)) * Polynomial.X ^ 3 +
      C (q.u1 ^ 2 + 2 * q.u2 * q.u0 + q.w1 ^ 2 + 2 * q.w2 * q.w0 - q.dz ^ 2 * q.V ^ 2) *
        Polynomial.X ^ 2 +
      C (2 * (q.u1 * q.u0 + q.w1 * q.w0)) * Polynomial.X + C (q.u0 ^ 2 + q.w0 ^ 2) := by
  simp only [quartic, Upoly, Wpoly, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- The leading coefficient of the terminal quartic is `|Z_g|² |Z_t|²`. -/
@[tmio M, powerlib_domain] theorem u2_sq_add_w2_sq :
    q.u2 ^ 2 + q.w2 ^ 2 = (q.Rg ^ 2 + q.Xg ^ 2) * q.ztsq := by
  simp only [u2, w2, ztsq]
  ring

/-- The cubic coefficient of the terminal quartic is `2 |Z_t|² (X_g(|Z_g|² + |Z_v|²) +
2 X_v |Z_g|²)/n_q`. -/
@[tmio M, powerlib_domain] theorem u2_mul_u1_add_w2_mul_w1 :
    q.u2 * q.u1 + q.w2 * q.w1 = q.ztsq * (q.Xg * (q.Rg ^ 2 + q.Xg ^ 2 + (q.Rv ^ 2 + q.Xv ^ 2)) +
      2 * q.Xv * (q.Rg ^ 2 + q.Xg ^ 2)) / q.nq := by
  simp only [u2, u1, w2, w1]
  ring

/-- `F(0) = u₀² + w₀²`. -/
@[tmio M, powerlib_domain] theorem eval_zero_quartic : q.quartic.eval 0 = q.u0 ^ 2 + q.w0 ^ 2 := by
  rw [eval_quartic, ← eval_Upoly, ← eval_Wpoly]
  simp [Upoly, Wpoly]

@[tmio M, powerlib_domain] theorem leadingCoeff_pos (hXg : 0 < q.Xg) (hXv : 0 ≤ q.Xv) :
    0 < q.u2 ^ 2 + q.w2 ^ 2 := by
  rw [u2_sq_add_w2_sq]
  have := q.ztsq_pos hXg hXv
  positivity

@[tmio M, powerlib_domain] theorem natDegree_quartic (hXg : 0 < q.Xg) (hXv : 0 ≤ q.Xv) :
    q.quartic.natDegree = 4 := by
  rw [quartic_eq]
  compute_degree!
  exact (q.leadingCoeff_pos hXg hXv).ne'

@[tmio M, powerlib_domain] theorem quartic_ne_zero (hXg : 0 < q.Xg) (hXv : 0 ≤ q.Xv) :
    q.quartic ≠ 0 := by
  intro h
  have := q.natDegree_quartic hXg hXv
  rw [h, natDegree_zero] at this
  exact absurd this (by norm_num)

/-- The EMF of a balanced point is a root of the terminal quartic (`|Z_t| ≠ 0`, every `dz`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem quartic_isRoot_of_balance (hZ : q.ztsq ≠ 0) {δ E : ℝ}
    (h : q.Pt δ E = q.Pref ∧ q.Qt δ E = q.qOf E) : q.quartic.IsRoot E := by
  obtain ⟨hc, hs⟩ := q.balance_imp hZ h
  rw [IsRoot.def, eval_quartic, ← hc, ← hs]
  linear_combination (q.dz * E * q.V) ^ 2 * Real.sin_sq_add_cos_sq δ

/-- The EMF of every equilibrium is a root of the terminal quartic.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem quartic_isRoot_of_field_eq_zero (hM : q.M ≠ 0)
    (hω : q.ωq ≠ 0) (hnq : q.nq ≠ 0) (hZ : q.ztsq ≠ 0) {x : State 3} (hx : q.field x = 0) :
    q.quartic.IsRoot (q.emf (x 2)) :=
  q.quartic_isRoot_of_balance hZ (q.balance_of_field_eq_zero hM hω hnq hx)

/-- The positive roots of the terminal quartic, counted with multiplicity, are at most two when
`n_q > 0`, `X_g > 0`, `X_v ≥ 0`: the coefficients have the sign pattern `(+, ≥ 0, ?, ?, ≥ 0)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem countP_pos_roots_le_two (hnq : 0 < q.nq) (hXg : 0 < q.Xg)
    (hXv : 0 ≤ q.Xv) : q.quartic.roots.countP (0 < ·) ≤ 2 := by
  rw [quartic_eq]
  refine SpecialFunctions.countP_pos_roots_le_two_of_quartic (q.leadingCoeff_pos hXg hXv) ?_
    (by positivity)
  rw [u2_mul_u1_add_w2_mul_w1]
  have h1 : 0 ≤ q.Xg * (q.Rg ^ 2 + q.Xg ^ 2 + (q.Rv ^ 2 + q.Xv ^ 2)) :=
    mul_nonneg hXg.le (by positivity)
  have h2 : 0 ≤ 2 * q.Xv * (q.Rg ^ 2 + q.Xg ^ 2) := by positivity
  have := q.ztsq_pos hXg hXv
  positivity

/-! ## Counting per period window -/

/-- The equilibria with angle in the window `[a, a + 2π)` and EMF in `T`. -/
def equilibriaWindow (T : Set ℝ) (a : ℝ) : Set (State 3) :=
  {x | q.field x = 0 ∧ x 0 ∈ Ico a (a + 2 * π) ∧ q.emf (x 2) ∈ T}

/-- For `dz ≠ 0` and a nonzero EMF the balance fixes the angle in a window: `dz E V cos δ = U(E)`,
`dz E V sin δ = W(E)` fix `e^{jδ}` (`V ≠ 0`). Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem eq_of_balance (hZ : q.ztsq ≠ 0) (hD : q.dz ≠ 0)
    (hV : q.V ≠ 0) {a δ₁ δ₂ E : ℝ} (hE : E ≠ 0) (h₁ : δ₁ ∈ Ico a (a + 2 * π))
    (h₂ : δ₂ ∈ Ico a (a + 2 * π)) (hb₁ : q.Pt δ₁ E = q.Pref ∧ q.Qt δ₁ E = q.qOf E)
    (hb₂ : q.Pt δ₂ E = q.Pref ∧ q.Qt δ₂ E = q.qOf E) : δ₁ = δ₂ := by
  obtain ⟨hc₁, hs₁⟩ := q.balance_imp hZ hb₁
  obtain ⟨hc₂, hs₂⟩ := q.balance_imp hZ hb₂
  have hEV : E * q.V ≠ 0 := mul_ne_zero hE hV
  have hc : cos δ₁ = cos δ₂ :=
    mul_left_cancel₀ hEV (mul_left_cancel₀ hD (hc₁.trans hc₂.symm))
  have hs : sin δ₁ = sin δ₂ :=
    mul_left_cancel₀ hEV (mul_left_cancel₀ hD (hs₁.trans hs₂.symm))
  exact SpecialFunctions.injOn_cexp_mul_I_Ico a h₁ h₂ (Complex.ext (by simp [hc]) (by simp [hs]))

/-- For `dz ≠ 0` the EMF is injective on the equilibria of a window with EMF in `T ∌ 0`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem injOn_emf (hM : q.M ≠ 0) (hω : q.ωq ≠ 0) (hnq : q.nq ≠ 0)
    (hZ : q.ztsq ≠ 0) (hD : q.dz ≠ 0) (hV : q.V ≠ 0) {T : Set ℝ} (hT : (0 : ℝ) ∉ T) (a : ℝ) :
    InjOn (fun x : State 3 => q.emf (x 2)) (q.equilibriaWindow T a) := by
  rintro x ⟨hx, hxw, hxT⟩ y ⟨hy, hyw, -⟩ hxy
  have hE0 : q.emf (x 2) ≠ 0 := fun h => hT (h ▸ hxT)
  have hby := q.balance_of_field_eq_zero hM hω hnq hy
  simp only at hxy
  rw [← hxy] at hby
  refine state3_ext (q.eq_of_balance hZ hD hV hE0 hxw hyw
    (q.balance_of_field_eq_zero hM hω hnq hx) hby) ?_ ?_
  · rw [((q.field_eq_zero_iff hM hω x).mp hx).1, ((q.field_eq_zero_iff hM hω y).mp hy).1]
  · rw [← q.qOf_emf hnq (x 2), ← q.qOf_emf hnq (y 2), hxy]

/-- Counting law for `dz ≠ 0`: in every window `[a, a + 2π)` the equilibria with EMF in a set
`T ∌ 0` are as many as the roots of the terminal quartic in `T` (the EMF is a bijection;
`V ≠ 0`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem ncard_equilibriaWindow (hM : q.M ≠ 0) (hω : q.ωq ≠ 0)
    (hnq : q.nq ≠ 0) (hZ : q.ztsq ≠ 0) (hD : q.dz ≠ 0) (hV : q.V ≠ 0) {T : Set ℝ}
    (hT : (0 : ℝ) ∉ T) (a : ℝ) :
    (q.equilibriaWindow T a).ncard = {E | E ∈ T ∧ q.quartic.IsRoot E}.ncard := by
  refine Set.ncard_congr (fun x _ => q.emf (x 2))
    (fun x hx => ⟨hx.2.2, q.quartic_isRoot_of_field_eq_zero hM hω hnq hZ hx.1⟩)
    (fun x y hx hy hxy => q.injOn_emf hM hω hnq hZ hD hV hT a hx hy hxy) ?_
  rintro E ⟨hET, hroot⟩
  have hE0 : E ≠ 0 := fun h => hT (h ▸ hET)
  have hk : q.dz * E * q.V ≠ 0 := mul_ne_zero (mul_ne_zero hD hE0) hV
  have hsum : q.U E ^ 2 + q.W E ^ 2 = (q.dz * E * q.V) ^ 2 := by
    rw [IsRoot.def, eval_quartic] at hroot
    linear_combination hroot
  obtain ⟨θ₀, hc₀, hs₀⟩ := Dynamics.LaSalle.exists_cos_sin (a := q.U E / (q.dz * E * q.V))
    (b := q.W E / (q.dz * E * q.V))
    (by rw [div_pow, div_pow, ← add_div, hsum, div_self (pow_ne_zero 2 hk)])
  set θ := toIcoMod two_pi_pos a θ₀ with hθ
  obtain ⟨n, hn⟩ : ∃ n : ℤ, θ = θ₀ - n * (2 * π) := by
    refine ⟨toIcoDiv two_pi_pos a θ₀, ?_⟩
    have := self_sub_toIcoMod two_pi_pos a θ₀
    rw [zsmul_eq_mul] at this
    linarith
  have hc : cos θ = q.U E / (q.dz * E * q.V) := by rw [hn, Real.cos_sub_int_mul_two_pi, hc₀]
  have hs : sin θ = q.W E / (q.dz * E * q.V) := by rw [hn, Real.sin_sub_int_mul_two_pi, hs₀]
  have hx2 : q.emf ((mk3 θ 0 (q.qOf E)) 2) = E := by rw [mk3_two, q.emf_qOf hnq]
  refine ⟨mk3 θ 0 (q.qOf E), ⟨(q.field_eq_zero_iff hM hω _).mpr ⟨mk3_one _ _ _, ?_⟩,
    by rw [mk3_zero]; exact toIcoMod_mem_Ico _ _ _, by rwa [hx2]⟩, hx2⟩
  rw [hx2, mk3_zero, mk3_two]
  refine (q.balance_iff hZ hD θ E).mpr ⟨?_, ?_⟩
  · rw [hc]; field_simp
  · rw [hs]; field_simp

/-- At most two physical equilibria in every window for `dz ≠ 0` (`n_q > 0`, `X_g > 0`,
`X_v ≥ 0`, `V ≠ 0`); `encard` also gives finiteness. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem encard_physical_le_two_of_dz_ne_zero (hM : q.M ≠ 0)
    (hω : q.ωq ≠ 0) (hnq : 0 < q.nq) (hXg : 0 < q.Xg) (hXv : 0 ≤ q.Xv) (hD : q.dz ≠ 0)
    (hV : q.V ≠ 0) (a : ℝ) : (q.equilibriaWindow (Ioi 0) a).encard ≤ 2 := by
  have hZ := (q.ztsq_pos hXg hXv).ne'
  have hP := q.quartic_ne_zero hXg hXv
  set R := {E : ℝ | 0 < E ∧ q.quartic.IsRoot E}
  have hfin : R.Finite := (Polynomial.finite_setOfPred_isRoot hP).subset fun E hE => hE.2
  have himg : (fun x : State 3 => q.emf (x 2)) '' q.equilibriaWindow (Ioi 0) a ⊆ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hx.2.2, q.quartic_isRoot_of_field_eq_zero hM hω hnq.ne' hZ hx.1⟩
  have hR : R.ncard ≤ 2 := (SpecialFunctions.ncard_pos_isRoot_le_countP hP).trans
    (q.countP_pos_roots_le_two hnq hXg hXv)
  rw [← (q.injOn_emf hM hω hnq.ne' hZ hD hV (by simp) a).encard_image]
  refine (Set.encard_le_encard himg).trans ?_
  rw [← hfin.cast_ncard_eq]
  exact_mod_cast hR

/-! ## The degenerate case `|Z_v| = |Z_g|` -/

/-- For `dz = 0` a balanced point has `U(E) = 0` (the adjugate kills the balance).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem U_eq_zero_of_dz_eq_zero (hZ : q.ztsq ≠ 0) (hD : q.dz = 0)
    {δ E : ℝ} (h : q.Pt δ E = q.Pref ∧ q.Qt δ E = q.qOf E) : q.U E = 0 := by
  have := (q.balance_imp hZ h).1
  rw [hD, zero_mul] at this
  exact this.symm

/-- For `dz = 0` the quadratic `U(E) = 0` has at most one positive root: its leading
coefficient `|Z_t|²/2` and linear coefficient `(X_g + X_v)|Z_t|²/n_q` are positive.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem eq_of_U_eq_zero (hnq : 0 < q.nq) (hXg : 0 < q.Xg)
    (hXv : 0 ≤ q.Xv) (hD : q.dz = 0) {E E' : ℝ} (hE : 0 < E) (hE' : 0 < E') (h : q.U E = 0)
    (h' : q.U E' = 0) : E = E' := by
  have hZ := q.ztsq_pos hXg hXv
  have hu2 : 0 < q.u2 := by linarith [q.two_mul_u2]
  have hu1 : 0 < q.u1 := div_pos (mul_pos (by linarith) hZ) hnq
  rw [← eval_Upoly] at h h'
  simp only [Upoly, eval_add, eval_mul, eval_pow, eval_C, eval_X] at h h'
  have hprod : (E - E') * (q.u2 * (E + E') + q.u1) = 0 := by linear_combination h - h'
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact sub_eq_zero.mp h0
  · nlinarith

/-- At most two physical equilibria in every window for `dz = 0` (`n_q > 0`, `X_g > 0`,
`X_v ≥ 0`, `V ≠ 0`): all of them have the EMF `E*` of the one positive root of `U`
(`eq_of_U_eq_zero`), and at `E*` the active-power balance `(R_v − R_g) cos δ + (X_g + X_v) sin δ =
b₁(E*)/(E* V)` is a shifted sinusoid with at most two zeros per window
(`SpecialFunctions.sinusoidZeros_subset`). Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem encard_physical_le_two_of_dz_eq_zero (hM : q.M ≠ 0)
    (hω : q.ωq ≠ 0) (hnq : 0 < q.nq) (hXg : 0 < q.Xg) (hXv : 0 ≤ q.Xv) (hD : q.dz = 0)
    (hV : q.V ≠ 0) (a : ℝ) : (q.equilibriaWindow (Ioi 0) a).encard ≤ 2 := by
  have hZ := (q.ztsq_pos hXg hXv).ne'
  set S := q.equilibriaWindow (Ioi 0) a with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨x₀, hx₀⟩
  · simp [h0]
  set E := q.emf (x₀ 2) with hEdef
  have hE : 0 < E := hx₀.2.2
  have hbal : ∀ x ∈ S, q.Pt (x 0) (q.emf (x 2)) = q.Pref ∧
      q.Qt (x 0) (q.emf (x 2)) = q.qOf (q.emf (x 2)) :=
    fun x hx => q.balance_of_field_eq_zero hM hω hnq.ne' hx.1
  have hEq : ∀ x ∈ S, q.emf (x 2) = E := fun x hx =>
    q.eq_of_U_eq_zero hnq hXg hXv hD hx.2.2 hE (q.U_eq_zero_of_dz_eq_zero hZ hD (hbal x hx))
      (q.U_eq_zero_of_dz_eq_zero hZ hD (hbal x₀ hx₀))
  -- the active-power balance at `E` as a shifted sinusoid `k − A sin(δ + φ)`
  set α := q.Rv - q.Rg
  set β := q.Xg + q.Xv
  have hβ : 0 < β := by simp only [β]; linarith
  set A := √(α ^ 2 + β ^ 2) with hA
  have hA2 : A ^ 2 = α ^ 2 + β ^ 2 := Real.sq_sqrt (by positivity)
  have hApos : 0 < A := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨φ, hcφ, hsφ⟩ := Dynamics.LaSalle.exists_cos_sin (a := β / A) (b := α / A)
    (by rw [div_pow, div_pow, ← add_div, add_comm, ← hA2, div_self (pow_ne_zero 2 hApos.ne')])
  set k := q.b1 E / (E * q.V)
  have hEV : E * q.V ≠ 0 := mul_ne_zero hE.ne' hV
  have himg : (fun x : State 3 => x 0) '' S ⊆
      {SpecialFunctions.stableRoot k A φ a, SpecialFunctions.saddleRoot k A φ a} := by
    rintro _ ⟨x, hx, rfl⟩
    refine SpecialFunctions.sinusoidZeros_subset hApos ⟨hx.2.1, ?_⟩
    have h1 := ((q.balance_linear hZ _ _).mp (hbal x hx)).1
    rw [hEq x hx] at h1
    simp only
    rw [Real.sin_add, hcφ, hsφ]
    simp only [k, α, β] at h1 ⊢
    field_simp
    linear_combination -h1
  have hinj : InjOn (fun x : State 3 => x 0) S := by
    intro x hx y hy hxy
    refine state3_ext hxy ?_ ?_
    · rw [((q.field_eq_zero_iff hM hω x).mp hx.1).1, ((q.field_eq_zero_iff hM hω y).mp hy.1).1]
    · rw [← q.qOf_emf hnq.ne' (x 2), ← q.qOf_emf hnq.ne' (y 2), hEq x hx, hEq y hy]
  rw [← hinj.encard_image]
  refine (Set.encard_le_encard himg).trans ((Set.encard_insert_le _ _).trans ?_)
  rw [Set.encard_singleton]
  rfl

/-- **At most two physical equilibria per period**, for every virtual impedance with an inductive
or zero reactance: in the physical range (`n_q > 0`, `X_g > 0`, `X_v ≥ 0`, `V ≠ 0`, `M, ω_q ≠ 0`)
every window `[a, a + 2π)` holds at most two equilibria with `E > 0`, and finitely many
(`encard_physical_le_two_of_dz_ne_zero`, `encard_physical_le_two_of_dz_eq_zero`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem encard_physical_le_two (hM : q.M ≠ 0) (hω : q.ωq ≠ 0)
    (hnq : 0 < q.nq) (hXg : 0 < q.Xg) (hXv : 0 ≤ q.Xv) (hV : q.V ≠ 0) (a : ℝ) :
    (q.equilibriaWindow (Ioi 0) a).encard ≤ 2 := by
  by_cases hD : q.dz = 0
  · exact q.encard_physical_le_two_of_dz_eq_zero hM hω hnq hXg hXv hD hV a
  · exact q.encard_physical_le_two_of_dz_ne_zero hM hω hnq hXg hXv hD hV a

/-! ## Parity -/

/-- For `dz ≠ 0`, in the physical range `F(0) = u₀² + w₀² > 0`: `A (u₀, w₀) = dz b(0)` with
`b₂(0) = |Z_t|² q₀ + X_v V² > 0`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem eval_zero_quartic_pos (hnq : 0 < q.nq) (hXg : 0 < q.Xg)
    (hXv : 0 ≤ q.Xv) (hc : 0 < q.E0 + q.nq * q.Qref) (hD : q.dz ≠ 0) :
    0 < q.quartic.eval 0 := by
  rw [eval_zero_quartic]
  have hZ := q.ztsq_pos hXg hXv
  have hq : q.q0 * q.nq = q.E0 + q.nq * q.Qref := by
    simp only [q0, add_mul, div_mul_cancel₀ _ hnq.ne']
    ring
  have hq0 : 0 < q.q0 := by nlinarith
  have hB : 0 < q.ztsq * q.q0 + q.Xv * q.V ^ 2 := by positivity
  have hid : (q.Xv - q.Xg) * q.u0 - (q.Rg + q.Rv) * q.w0 =
      q.dz * (q.ztsq * q.q0 + q.Xv * q.V ^ 2) := by
    simp only [u0, w0, dz]
    ring
  by_contra hle
  have hu : q.u0 = 0 := by nlinarith [sq_nonneg q.u0, sq_nonneg q.w0]
  have hw : q.w0 = 0 := by nlinarith [sq_nonneg q.u0, sq_nonneg q.w0]
  rw [hu, hw, mul_zero, mul_zero, sub_zero] at hid
  exact mul_ne_zero hD hB.ne' hid.symm

@[tmio M, powerlib_domain] theorem leadingCoeff_quartic (hXg : 0 < q.Xg) (hXv : 0 ≤ q.Xv) :
    q.quartic.leadingCoeff = q.u2 ^ 2 + q.w2 ^ 2 := by
  rw [leadingCoeff, q.natDegree_quartic hXg hXv, quartic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

/-- Parity for `dz ≠ 0`: in the physical range the positive roots of the terminal quartic,
counted with multiplicity, are `0` or `2` (`F(0) > 0`, positive leading coefficient;
`SpecialFunctions.even_countP_pos_roots_iff`). Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem countP_pos_roots_eq_zero_or_two (hnq : 0 < q.nq)
    (hXg : 0 < q.Xg) (hXv : 0 ≤ q.Xv) (hc : 0 < q.E0 + q.nq * q.Qref) (hD : q.dz ≠ 0) :
    q.quartic.roots.countP (0 < ·) = 0 ∨ q.quartic.roots.countP (0 < ·) = 2 := by
  have h0 := q.eval_zero_quartic_pos hnq hXg hXv hc hD
  have he : Even (q.quartic.roots.countP (0 < ·)) := by
    refine (SpecialFunctions.even_countP_pos_roots_iff h0.ne').mpr ?_
    rw [q.leadingCoeff_quartic hXg hXv]
    exact mul_pos (q.leadingCoeff_pos hXg hXv) h0
  have h2 := q.countP_pos_roots_le_two hnq hXg hXv
  obtain ⟨k, hk⟩ := he
  omega

end QVDroopVirtual

end powerlib.GFM
