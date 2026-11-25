import theorem.GridTiedConverter.GFM.Port.DroopAdmittance
import theorem.PH.PositiveRealAxis

/-! # Passivity of the Q–V droop admittances on the whole imaginary axis

The port of the VSM with Q–V droop (`Line.VSMQ`,
`theorem/GridTiedConverter/GFM/Port/DroopAdmittance.lean`) is passive at one frequency iff an
explicit sign condition holds there; along `s = jω` those conditions are polynomial sign
conditions in `x = ω²`. This module decides passivity at every frequency at once, exactly, in
the model data.

Model boundary.
* The two realizations of `theorem/GridTiedConverter/GFM/Port/DroopAdmittance.lean`: the
  source-measured `VSMQ.portModel` and the PCC-measured `VSMQ.pccModel` (state
  `(δ, ω, i_d, i_q, Q_f)`, PCC voltage input, IN-positive port current output), at a fixed
  operating point `(δ₀, i₀, Q_f0)` (and PCC voltage `v₀`), equilibrium or not. Notation:
  `E' = E(Q_f0)`, `(i_a, i_b) = Rᵀ i₀` and `(v_a, v_b) = Rᵀ v₀` the current and the PCC
  voltage along and across the EMF, `P_c`, `Q_c` the powers at the source, `P_p` the PCC power.
* "Passive on the whole imaginary axis" is `PH.PositiveRealAt` of the transfer matrix at `jω`
  for every real `ω`; the theorems assume no pole on the axis (the closed-form denominators of
  the pointwise criteria and `det (jωI − A)` nonzero at every `ω`). No time-domain claim.
* Excluded: everything excluded there (limits, PLL, PWM, active-power filter, inner cascade).

Source: positive realness along the axis, work-sync `theory/T-ph.md` §1.10; the pointwise
criteria `VSMQ.positiveRealAt_transfer_iff`, `VSMQ.positiveRealAt_transfer_iff_of_nq_eq_zero`,
`VSMQ.positiveRealAt_transfer_pcc_iff`, `VSMQ.positiveRealAt_transfer_pcc_iff_of_nq_eq_zero` of
`theorem/GridTiedConverter/GFM/Port/DroopAdmittance.lean`; the sign laws
`PH.forall_nonneg_quadratic_iff`, `PH.forall_nonneg_iff_halfLineNonneg` of
`theorem/PH/PositiveRealAxis.lean`; the coefficients by exact computer algebra (sympy, checked
here by `ring`).

Results.
* Source-measured, constant EMF (`n_q = 0`, `ω_q ≠ 0`): passive at every `jω` iff `R ≥ 0`,
  `E⁴ ≤ 4 R² Q_c²` (DC) and either `2 M Q_c + D² ≥ 0` or `R² D² (4 M Q_c + D²) + M² E⁴ ≤ 0`
  (`forall_positiveRealAt_transfer_iff_of_nq_eq_zero`): `|M (jω)² + D jω − Q_c|²` is the
  quadratic `M² x² + (2 M Q_c + D²) x + Q_c²`, minimal at `x = 0` unless `2 M Q_c + D² < 0`.
* Source-measured, general droop, every parameter value (`M, L ≠ 0`):
  `4 R² |det W(jω)|² − hermDefect(jω)` is the cubic `srcAxis` in `x` (`srcAxis_eval`; leading
  coefficient `4 R² M²`); passive at every `jω` iff `R ≥ 0` and `PH.HalfLineNonneg srcAxis`
  (`forall_positiveRealAt_transfer_iff`): for `R > 0` the cubic condition (`d ≥ 0`, the DC value,
  and `b, c ≥ 0` or `disc ≤ 0` with `d > 0` or `c > 0`), for the lossless line `R = 0` the
  quadratic condition with `b = −E'² (n_q ω_q M)²`.
* PCC-measured, constant EMF (`n_q = 0`), `ω = 0` included: passive at every `jω` iff `R ≥ 0`
  and the two quadratics `h₁(x) = M² R x² + b₁ x + E² P_p` (`b₁ = pccHerm1Lin`) and
  `4 R h₁(x) − E² ((R i_a − X i_b + v_a)² + L² i_a² x)` are nonnegative on `x ≥ 0`, each in the
  closed form `c ≥ 0 ∧ (b ≥ 0 ∨ b² ≤ 4ac)`
  (`forall_positiveRealAt_transfer_pcc_iff_of_nq_eq_zero`).
* PCC-measured, general droop, `ω = 0` included, every parameter value: the trace is the
  quadratic `M² R x² + (h₀₁ + h₁₁) x + (h₀₀ + h₁₀)` and the determinant the cubic `pccAxis`
  (`pccAxis_eval`, from the pointwise `positiveRealAt_transfer_pcc_iff`); passive at every
  `jω` iff `R ≥ 0` with the quadratic condition on the trace and `PH.HalfLineNonneg pccAxis`
  (`forall_positiveRealAt_transfer_pcc_iff`; a negative leading coefficient
  `M² (4R (R + n_q ω_q L i_b) − L² n_q² ω_q² i_a²)` fails for large `ω`, a zero one drops the
  degree).
* Hypotheses: `M, L ≠ 0` and no pole on the axis only (plus `ω_q ≠ 0` for the source-measured
  `n_q = 0` statement); for the PCC-measured law no pole at `s = 0` forces `E' ≠ 0` and
  `ω_q ≠ 0` (`det_pccA`). Coefficient sizes, from `x⁰` up, expanded in the source-frame data:
  source cubic 10/15/6/1 terms; PCC trace 8/7/1, PCC determinant 17/47/25/3 terms.

Family and connection conclusions.
* None: frequency-wise static facts about the realizations (static evidence).
-/

noncomputable section
namespace powerlib.GFM.Line
open Matrix Linear
open powerlib.PH (forall_sq_iff forall_nonneg_quadratic_iff forall_nonneg_iff_halfLineNonneg
  HalfLineNonneg)

namespace VSMQ

variable (g : VSMQ)

/-! ## Powers measured at the source -/

/-- `s = jω` is off `s = −ω_q` when `ω_q ≠ 0`. -/
@[tmio M, powerlib_domain] private theorem jw_add_ne_zero {ωq : ℝ} (hq : ωq ≠ 0) (ω : ℝ) :
    (ω : ℂ) * Complex.I + (ωq : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  exact hq this

/-- **Constant EMF: passivity on the whole imaginary axis.** Without droop (`n_q = 0`,
`ω_q ≠ 0`) and with no pole on the axis, the source-measured port admittance is positive real
at every `jω` iff `R ≥ 0`, `E⁴ ≤ 4 R² Q_c²` and either `2 M Q_c + D² ≥ 0` or
`R² D² (4 M Q_c + D²) + M² E⁴ ≤ 0` (`Q_c` the reactive power at the source). Pointwise law
`positiveRealAt_transfer_iff_of_nq_eq_zero` (`E² |g(jω)| ≤ 2R`), then
`PH.forall_nonneg_quadratic_iff` on `4R² ((M x + Q_c)² + D² x) − E⁴`, `x = ω²`. -/
@[tmio M, powerlib_domain] theorem forall_positiveRealAt_transfer_iff_of_nq_eq_zero
    (hn : g.nq = 0) (hM : g.M ≠ 0) (hL : g.L ≠ 0) (hq : g.ωq ≠ 0) {δ id iq qf : ℝ}
    (hden : ∀ ω : ℝ, (g.M : ℂ) * (ω * Complex.I) ^ 2 + (g.D : ℂ) * (ω * Complex.I) -
      (g.reactive δ id iq : ℂ) ≠ 0)
    (hZ : ∀ ω : ℝ, (g.droopZ δ id iq qf (ω * Complex.I)).det ≠ 0)
    (hA : ∀ ω : ℝ, (characteristicMatrix (g.portModel δ id iq qf).A (ω * Complex.I)).det ≠ 0) :
    (∀ ω : ℝ, PH.PositiveRealAt (transfer (g.portModel δ id iq qf) (ω * Complex.I))) ↔
      0 ≤ g.R ∧ g.E ^ 4 ≤ 4 * g.R ^ 2 * g.reactive δ id iq ^ 2 ∧
        (0 ≤ 2 * g.M * g.reactive δ id iq + g.D ^ 2 ∨
          g.R ^ 2 * g.D ^ 2 * (4 * g.M * g.reactive δ id iq + g.D ^ 2) + g.M ^ 2 * g.E ^ 4 ≤
            0) := by
  set Q := g.reactive δ id iq with hQdef
  -- the pointwise criterion as a sign condition in `x = ω²`
  have hpt : ∀ ω : ℝ, PH.PositiveRealAt (transfer (g.portModel δ id iq qf) (ω * Complex.I)) ↔
      0 ≤ g.R ∧ 0 ≤ (4 * g.R ^ 2 * g.M ^ 2) * (ω ^ 2) ^ 2 +
        (4 * g.R ^ 2 * (2 * g.M * Q + g.D ^ 2)) * ω ^ 2 + (4 * g.R ^ 2 * Q ^ 2 - g.E ^ 4) := by
    intro ω
    rw [g.positiveRealAt_transfer_iff_of_nq_eq_zero hn hM hL (hden ω) (jw_add_ne_zero hq ω)
      (hZ ω) (hA ω)]
    set w : ℂ := (g.M : ℂ) * (ω * Complex.I) ^ 2 + (g.D : ℂ) * (ω * Complex.I) - (Q : ℂ)
      with hw
    have hw0 : w ≠ 0 := hden ω
    have hnw : ‖g.toVSM.syncGain δ id iq (ω * Complex.I)‖ = ‖w‖⁻¹ := by
      simp [VSM.syncGain, hw, hQdef]
    have hn2 : ‖w‖ ^ 2 = (g.M * ω ^ 2 + Q) ^ 2 + g.D ^ 2 * ω ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hw]
      simp [pow_two, Complex.mul_re, Complex.mul_im]
      ring
    have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hre : (↑ω * Complex.I).re = 0 := by simp
    rw [hnw, hre, mul_zero, add_zero, ← div_eq_mul_inv, div_le_iff₀ hwp]
    have hE2 : 0 ≤ g.E ^ 2 := sq_nonneg _
    constructor
    · intro h
      have hR : 0 ≤ g.R := by
        by_contra hR
        push Not at hR
        nlinarith [mul_pos (neg_pos.mpr hR) hwp]
      refine ⟨hR, ?_⟩
      have h2 : (g.E ^ 2) ^ 2 ≤ (2 * g.R * ‖w‖) ^ 2 := pow_le_pow_left₀ hE2 h 2
      nlinarith [h2, hn2]
    · rintro ⟨hR, h⟩
      have h2 : (g.E ^ 2) ^ 2 ≤ (2 * g.R * ‖w‖) ^ 2 := by nlinarith [hn2]
      exact (pow_le_pow_iff_left₀ hE2 (by positivity) two_ne_zero).mp h2
  rw [forall_congr' hpt, forall_sq_iff (P := fun x => 0 ≤ g.R ∧
    0 ≤ (4 * g.R ^ 2 * g.M ^ 2) * x ^ 2 + (4 * g.R ^ 2 * (2 * g.M * Q + g.D ^ 2)) * x +
      (4 * g.R ^ 2 * Q ^ 2 - g.E ^ 4))]
  have hsplit : (∀ x : ℝ, 0 ≤ x → 0 ≤ g.R ∧ 0 ≤ (4 * g.R ^ 2 * g.M ^ 2) * x ^ 2 +
      (4 * g.R ^ 2 * (2 * g.M * Q + g.D ^ 2)) * x + (4 * g.R ^ 2 * Q ^ 2 - g.E ^ 4)) ↔
      0 ≤ g.R ∧ ∀ x : ℝ, 0 ≤ x → 0 ≤ (4 * g.R ^ 2 * g.M ^ 2) * x ^ 2 +
        (4 * g.R ^ 2 * (2 * g.M * Q + g.D ^ 2)) * x + (4 * g.R ^ 2 * Q ^ 2 - g.E ^ 4) :=
    ⟨fun h => ⟨(h 0 le_rfl).1, fun x hx => (h x hx).2⟩, fun h x hx => ⟨h.1, h.2 x hx⟩⟩
  rw [hsplit, forall_nonneg_quadratic_iff]
  constructor
  · rintro ⟨hR, -, hc, hb⟩
    refine ⟨hR, by linarith, ?_⟩
    rcases hR.lt_or_eq with hR' | hR'
    · rcases hb with hb | hb
      · left
        exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 4 * g.R ^ 2)).mp hb
      · right
        have h16 : 0 < 16 * g.R ^ 2 := by positivity
        nlinarith [h16]
    · right
      rw [← hR'] at hc ⊢
      have : g.E ^ 4 ≤ 0 := by linarith
      nlinarith [sq_nonneg g.M, pow_two_nonneg (g.E ^ 2)]
  · rintro ⟨hR, hc, hb⟩
    refine ⟨hR, by positivity, by linarith, ?_⟩
    rcases hb with hb | hb
    · left; positivity
    · right
      nlinarith [sq_nonneg g.R, sq_nonneg (g.R ^ 2)]


/-- **The axis cubic of the source-measured criterion.** With `x = ω²`, `E' = E(Q_f)`,
`(i_a, i_b) = Rᵀ i₀` and `κ = 1 − n_q i_b`: `det W(jω) = w_r(x) + jω w_i(x)` with
`w_r = ω_q E' (i_b κ − n_q i_a²) − (M ω_q κ + D) x`, `w_i = E' i_b + D ω_q κ − M x`, and the
defect's inner term is `k₀ − n_q ω_q M x + jω (n_q ω_q D + E')`, `k₀ = E' ω_q (2 n_q i_b − 1)`;
`4 R² |det W|² − hermDefect` is the cubic `a x³ + b x² + c x + d` with `a = 4 R² M²` and `d` its
DC value (`srcAxis_eval`). -/
def srcAxis (δ id iq qf : ℝ) : Cubic ℝ :=
  let E := g.emfMag qf
  let ia := Transform.parkD δ id iq
  let ib := Transform.parkQ δ id iq
  let κ := 1 - g.nq * ib
  let wr0 := g.ωq * E * (ib * κ - g.nq * ia ^ 2)
  let wr1 := -(g.M * g.ωq * κ + g.D)
  let wi0 := E * ib + g.D * g.ωq * κ
  let k0 := E * g.ωq * (2 * g.nq * ib - 1)
  let k2 := g.nq * g.ωq * g.D + E
  ⟨4 * g.R ^ 2 * g.M ^ 2,
    4 * g.R ^ 2 * (wr1 ^ 2 - 2 * g.M * wi0) - E ^ 2 * (g.nq * g.ωq * g.M) ^ 2,
    4 * g.R ^ 2 * (2 * wr0 * wr1 + wi0 ^ 2) - E ^ 2 * (k2 ^ 2 - 2 * k0 * (g.nq * g.ωq * g.M)),
    4 * g.R ^ 2 * wr0 ^ 2 - E ^ 2 * ((2 * g.nq * g.ωq * E * ia) ^ 2 + k0 ^ 2)⟩

/-- **The source-measured criterion along the axis is the cubic `srcAxis`:**
`4 R² |det W(jω)|² − hermDefect(jω) = a x³ + b x² + c x + d` at `x = ω²`. -/
@[tmio M, powerlib_domain] theorem srcAxis_eval (δ id iq qf ω : ℝ) :
    4 * g.R ^ 2 * Complex.normSq (g.chanW δ id iq qf (ω * Complex.I)).det -
        g.hermDefect δ id iq qf (ω * Complex.I) =
      (g.srcAxis δ id iq qf).a * (ω ^ 2) ^ 3 + (g.srcAxis δ id iq qf).b * (ω ^ 2) ^ 2 +
        (g.srcAxis δ id iq qf).c * ω ^ 2 + (g.srcAxis δ id iq qf).d := by
  have hP : (g.net qf).power δ id iq = g.emfMag qf * Transform.parkD δ id iq := by
    rw [(g.net qf).power_eq δ id iq]; simp [net, Transform.parkD]
  have hQ : (g.net qf).reactive δ id iq = -(g.emfMag qf * Transform.parkQ δ id iq) := by
    rw [(g.net qf).reactive_eq δ id iq]; simp [net, Transform.parkQ]; ring
  have hs2 : ((ω : ℂ) * Complex.I) ^ 2 = ((-ω ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [mul_pow, Complex.I_sq]; ring
  rw [det_chanW, hermDefect, hP, hQ, hs2]
  simp only [srcAxis, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, Complex.ofReal_mul,
    ← Complex.ofReal_pow, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **Passivity of the droop admittance on the whole imaginary axis** (source-measured powers,
every parameter value, no pole on the axis): the port admittance is positive real at every `jω`
iff `R ≥ 0` and the axis cubic `srcAxis = a x³ + b x² + c x + d` (`a = 4 R² M²`) is nonnegative
on `x ≥ 0`, in closed form `PH.HalfLineNonneg`: for `R > 0` the cubic condition (`d ≥ 0` (DC
passivity, `positiveRealAt_transfer_zero_iff`) and `b, c ≥ 0` or `Cubic.discr ≤ 0` with `d > 0`
or `c > 0`), for the lossless line `R = 0` the degree drops (`a = 0`,
`b = −E'² (n_q ω_q M)² ≤ 0`) and the quadratic condition decides it. Pointwise law
`positiveRealAt_transfer_iff`, the cubic `srcAxis_eval`, the sign law
`PH.forall_nonneg_iff_halfLineNonneg`. -/
@[tmio M, powerlib_domain] theorem forall_positiveRealAt_transfer_iff (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) {δ id iq qf : ℝ}
    (hW : ∀ ω : ℝ, (g.chanW δ id iq qf (ω * Complex.I)).det ≠ 0)
    (hZ : ∀ ω : ℝ, (g.droopZ δ id iq qf (ω * Complex.I)).det ≠ 0)
    (hA : ∀ ω : ℝ, (characteristicMatrix (g.portModel δ id iq qf).A (ω * Complex.I)).det ≠ 0) :
    (∀ ω : ℝ, PH.PositiveRealAt (transfer (g.portModel δ id iq qf) (ω * Complex.I))) ↔
      0 ≤ g.R ∧ HalfLineNonneg (g.srcAxis δ id iq qf) := by
  set P := g.srcAxis δ id iq qf with hPdef
  have hpt : ∀ ω : ℝ, PH.PositiveRealAt (transfer (g.portModel δ id iq qf) (ω * Complex.I)) ↔
      0 ≤ g.R ∧ 0 ≤ P.a * (ω ^ 2) ^ 3 + P.b * (ω ^ 2) ^ 2 + P.c * ω ^ 2 + P.d := by
    intro ω
    rw [g.positiveRealAt_transfer_iff hM hL (hW ω) (hZ ω) (hA ω), hPdef, ← g.srcAxis_eval]
    have hre : (↑ω * Complex.I).re = 0 := by simp
    rw [hre, mul_zero, add_zero]
    constructor
    · rintro ⟨h0, h⟩; exact ⟨h0, by linarith⟩
    · rintro ⟨h0, h⟩; exact ⟨h0, by linarith⟩
  rw [forall_congr' hpt, forall_sq_iff (P := fun x => 0 ≤ g.R ∧
    0 ≤ P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d), ← forall_nonneg_iff_halfLineNonneg]
  exact ⟨fun h => ⟨(h 0 le_rfl).1, fun x hx => (h x hx).2⟩, fun h x hx => ⟨h.1, h.2 x hx⟩⟩

/-! ## Powers measured at the PCC -/

/-- No pole of the PCC-measured realization at `s = 0` forces `E' ≠ 0` and `ω_q ≠ 0`:
`det Â(0) = E' ω_q (R v_b + X v_a + n_q (v_a² + v_b²))` (`det_pccA`, `pccA_apply`). -/
@[tmio M, powerlib_domain] private theorem emfMag_ne_zero_of_pcc (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ id iq qf : ℝ} {v : Fin 2 → ℝ}
    (hA : (characteristicMatrix (g.pccModel δ id iq qf v).A ((0 : ℝ) * Complex.I)).det ≠ 0) :
    g.emfMag qf ≠ 0 ∧ g.ωq ≠ 0 := by
  have hne : (g.pccA δ qf v ((0 : ℝ) * Complex.I)).det ≠ 0 := by
    rw [g.det_pccA hM hL δ id iq qf v]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hL))
      (by exact_mod_cast hM)) hA
  rw [pccA_apply, Matrix.det_fin_two_of] at hne
  refine ⟨fun h0 => hne ?_, fun h0 => hne ?_⟩ <;> simp [h0]

/-- **Constant EMF, PCC-measured: passivity on the whole imaginary axis**, `ω = 0` included.
Without droop (`n_q = 0`) and with no pole on the axis (then `E ≠ 0`, `ω_q ≠ 0`), the PCC-measured
port admittance is positive real at every `jω` iff `R ≥ 0` and, with `P_p` the PCC power
(`pccPower`), `b₁ = pccHerm1Lin`, `u = R i_a − X i_b + v_a` (`lineEmfD`):
* `h₁(x) = M² R x² + b₁ x + E² P_p ≥ 0` on `x ≥ 0`: `E² P_p ≥ 0` and
  (`b₁ ≥ 0` or `b₁² ≤ 4 M² R E² P_p`);
* `4 R h₁(x) − E² (u² + L² i_a² x) ≥ 0` on `x ≥ 0`: `E² (4 R P_p − u²) ≥ 0` and
  (`4 R b₁ − E² L² i_a² ≥ 0` or `(4 R b₁ − E² L² i_a²)² ≤ 16 M² R² E² (4 R P_p − u²)`).
Pointwise law `positiveRealAt_transfer_pcc_iff_of_nq_eq_zero`, then
`PH.forall_nonneg_quadratic_iff` twice. -/
@[tmio M, powerlib_domain] theorem forall_positiveRealAt_transfer_pcc_iff_of_nq_eq_zero
    (hn : g.nq = 0) (hM : g.M ≠ 0) (hL : g.L ≠ 0) {δ id iq qf : ℝ} {v : Fin 2 → ℝ}
    (hA : ∀ ω : ℝ,
      (characteristicMatrix (g.pccModel δ id iq qf v).A (ω * Complex.I)).det ≠ 0) :
    (∀ ω : ℝ, PH.PositiveRealAt (transfer (g.pccModel δ id iq qf v) (ω * Complex.I))) ↔
      0 ≤ g.R ∧
        (0 ≤ g.E ^ 2 * pccPower δ id iq v ∧ (0 ≤ g.pccHerm1Lin δ id iq qf v ∨
          g.pccHerm1Lin δ id iq qf v ^ 2 ≤ 4 * (g.M ^ 2 * g.R) * (g.E ^ 2 * pccPower δ id iq v))) ∧
        (0 ≤ g.E ^ 2 * (4 * g.R * pccPower δ id iq v - g.lineEmfD δ id iq v ^ 2) ∧
          (0 ≤ 4 * g.R * g.pccHerm1Lin δ id iq qf v -
              g.E ^ 2 * g.L ^ 2 * Transform.parkD δ id iq ^ 2 ∨
            (4 * g.R * g.pccHerm1Lin δ id iq qf v -
                g.E ^ 2 * g.L ^ 2 * Transform.parkD δ id iq ^ 2) ^ 2 ≤
              4 * (4 * g.M ^ 2 * g.R ^ 2) *
                (g.E ^ 2 * (4 * g.R * pccPower δ id iq v - g.lineEmfD δ id iq v ^ 2)))) := by
  have hEm : g.emfMag qf = g.E := by simp [emfMag, hn]
  obtain ⟨hE, hq⟩ := g.emfMag_ne_zero_of_pcc hM hL (hA 0)
  rw [hEm] at hE
  set P := pccPower δ id iq v with hPdef
  set b := g.pccHerm1Lin δ id iq qf v with hbdef
  set u := g.lineEmfD δ id iq v with hudef
  set ia := Transform.parkD δ id iq with hia
  have hh1 : ∀ x : ℝ, g.pccHerm1 δ id iq qf v x = g.M ^ 2 * g.R * x ^ 2 + b * x + g.E ^ 2 * P := by
    intro x; simp only [pccHerm1, hEm, ← hPdef, ← hbdef]; ring
  have hpt : ∀ ω : ℝ, PH.PositiveRealAt (transfer (g.pccModel δ id iq qf v) (ω * Complex.I)) ↔
      (0 ≤ g.R ∧ 0 ≤ g.M ^ 2 * g.R * (ω ^ 2) ^ 2 + b * ω ^ 2 + g.E ^ 2 * P) ∧
        0 ≤ (4 * g.M ^ 2 * g.R ^ 2) * (ω ^ 2) ^ 2 + (4 * g.R * b - g.E ^ 2 * g.L ^ 2 * ia ^ 2) *
          ω ^ 2 + g.E ^ 2 * (4 * g.R * P - u ^ 2) := by
    intro ω
    rw [g.positiveRealAt_transfer_pcc_iff_of_nq_eq_zero hn hM hL hq hE (hA ω), hh1]
    constructor
    · rintro ⟨hR, h1, h2⟩
      exact ⟨⟨hR, h1⟩, by nlinarith⟩
    · rintro ⟨⟨hR, h1⟩, h2⟩
      exact ⟨hR, h1, by nlinarith⟩
  rw [forall_congr' hpt, forall_sq_iff (P := fun x => (0 ≤ g.R ∧
    0 ≤ g.M ^ 2 * g.R * x ^ 2 + b * x + g.E ^ 2 * P) ∧
      0 ≤ (4 * g.M ^ 2 * g.R ^ 2) * x ^ 2 + (4 * g.R * b - g.E ^ 2 * g.L ^ 2 * ia ^ 2) * x +
        g.E ^ 2 * (4 * g.R * P - u ^ 2))]
  constructor
  · intro h
    have hR : 0 ≤ g.R := (h 0 le_rfl).1.1
    refine ⟨hR, (forall_nonneg_quadratic_iff.mp fun x hx => (h x hx).1.2).2,
      (forall_nonneg_quadratic_iff.mp fun x hx => (h x hx).2).2⟩
  · rintro ⟨hR, h1, h2⟩ x hx
    exact ⟨⟨hR, forall_nonneg_quadratic_iff.mpr ⟨by positivity, h1⟩ x hx⟩,
      forall_nonneg_quadratic_iff.mpr ⟨by positivity, h2⟩ x hx⟩

/-- **The axis cubic of the PCC-measured determinant.** With `x = ω²` the pointwise criterion
`positiveRealAt_transfer_pcc_iff` has `h₀ = h₀₀ + h₀₁ x`, `h₁ = h₁₀ + h₁₁ x + M² R x²`,
`β_r = r₀ + r₁ x`, `β_i = i₀ + i₁ x` (`h₀₀ = pccHerm0 0`, `h₀₁ = R + n_q ω_q L i_b`,
`h₁₀ = pccHerm1 0`, `h₁₁ = pccHerm1Lin`, `r₀ = pccDefRe 0`,
`r₁ = n_q ω_q M (v_a − R i_a + X i_b) − L i_a (E' + n_q ω_q D)`, `i₀ = pccDefIm 0`,
`i₁ = L M n_q ω_q i_a`), and the determinant `4 h₀ h₁ − β_r² − x β_i²` is this cubic
(`pccAxis_eval`); its leading coefficient is `M² (4R (R + n_q ω_q L i_b) − L² n_q² ω_q² i_a²)`. -/
def pccAxis (δ id iq qf : ℝ) (v : Fin 2 → ℝ) : Cubic ℝ :=
  let ia := Transform.parkD δ id iq
  let ib := Transform.parkQ δ id iq
  let h00 := g.pccHerm0 δ id iq v 0
  let h01 := g.R + g.nq * g.ωq * g.L * ib
  let h10 := g.pccHerm1 δ id iq qf v 0
  let h11 := g.pccHerm1Lin δ id iq qf v
  let h12 := g.M ^ 2 * g.R
  let r0 := g.pccDefRe δ id iq qf v 0
  let r1 := g.nq * g.ωq * g.M * (Transform.parkD δ (v 0) (v 1) - g.R * ia + g.X * ib) -
    g.L * ia * (g.emfMag qf + g.nq * g.ωq * g.D)
  let i0 := g.pccDefIm δ id iq qf v 0
  let i1 := g.L * g.M * g.nq * g.ωq * ia
  ⟨4 * h01 * h12 - i1 ^ 2, 4 * (h00 * h12 + h01 * h11) - r1 ^ 2 - 2 * i0 * i1,
    4 * (h00 * h11 + h01 * h10) - 2 * r0 * r1 - i0 ^ 2, 4 * h00 * h10 - r0 ^ 2⟩

/-- **The PCC-measured determinant along the axis is the cubic `pccAxis`.** -/
@[tmio M, powerlib_domain] theorem pccAxis_eval (δ id iq qf : ℝ) (v : Fin 2 → ℝ) (x : ℝ) :
    4 * g.pccHerm0 δ id iq v x * g.pccHerm1 δ id iq qf v x - g.pccDefRe δ id iq qf v x ^ 2 -
        x * g.pccDefIm δ id iq qf v x ^ 2 =
      (g.pccAxis δ id iq qf v).a * x ^ 3 + (g.pccAxis δ id iq qf v).b * x ^ 2 +
        (g.pccAxis δ id iq qf v).c * x + (g.pccAxis δ id iq qf v).d := by
  simp only [pccAxis, pccHerm0, pccHerm1, pccDefRe, pccDefIm]
  ring

/-- **Passivity of the PCC-measured droop admittance on the whole imaginary axis**, `ω = 0`
included, every parameter value: with no pole on the axis (which forces `E' ≠ 0`, `ω_q ≠ 0`),
the admittance is positive real at every `jω` iff the trace quadratic
`M² R x² + t₁ x + t₀` (`t₁ = h₀₁ + h₁₁`, `t₀ = h₀₀ + h₁₀`) is nonnegative on `x ≥ 0`
(`R ≥ 0`, `t₀ ≥ 0` and `t₁ ≥ 0` or `t₁² ≤ 4 M² R t₀`; `R < 0` fails for large `ω`) and the
determinant cubic `pccAxis` is (`PH.HalfLineNonneg`: a negative leading coefficient
`M² (4R (R + n_q ω_q L i_b) − L² n_q² ω_q² i_a²)` fails for large `ω`, a zero one drops to the
quadratic condition). Laws `PH.forall_nonneg_quadratic_iff`,
`PH.forall_nonneg_iff_halfLineNonneg`. -/
@[tmio M, powerlib_domain] theorem forall_positiveRealAt_transfer_pcc_iff (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) {δ id iq qf : ℝ} {v : Fin 2 → ℝ}
    (hA : ∀ ω : ℝ,
      (characteristicMatrix (g.pccModel δ id iq qf v).A (ω * Complex.I)).det ≠ 0) :
    (∀ ω : ℝ, PH.PositiveRealAt (transfer (g.pccModel δ id iq qf v) (ω * Complex.I))) ↔
      (0 ≤ g.R ∧ 0 ≤ g.pccHerm0 δ id iq v 0 + g.pccHerm1 δ id iq qf v 0 ∧
        (0 ≤ g.R + g.nq * g.ωq * g.L * Transform.parkQ δ id iq + g.pccHerm1Lin δ id iq qf v ∨
          (g.R + g.nq * g.ωq * g.L * Transform.parkQ δ id iq + g.pccHerm1Lin δ id iq qf v) ^ 2 ≤
            4 * (g.M ^ 2 * g.R) * (g.pccHerm0 δ id iq v 0 + g.pccHerm1 δ id iq qf v 0))) ∧
        HalfLineNonneg (g.pccAxis δ id iq qf v) := by
  obtain ⟨hE, hq⟩ := g.emfMag_ne_zero_of_pcc hM hL (hA 0)
  set C := g.pccAxis δ id iq qf v with hCdef
  set t1 := g.R + g.nq * g.ωq * g.L * Transform.parkQ δ id iq + g.pccHerm1Lin δ id iq qf v
  set t0 := g.pccHerm0 δ id iq v 0 + g.pccHerm1 δ id iq qf v 0
  have htr : ∀ x : ℝ, g.pccHerm0 δ id iq v x + g.pccHerm1 δ id iq qf v x =
      g.M ^ 2 * g.R * x ^ 2 + t1 * x + t0 := by
    intro x; simp only [t1, t0, pccHerm0, pccHerm1]; ring
  have hpt : ∀ ω : ℝ, PH.PositiveRealAt (transfer (g.pccModel δ id iq qf v) (ω * Complex.I)) ↔
      0 ≤ g.M ^ 2 * g.R * (ω ^ 2) ^ 2 + t1 * ω ^ 2 + t0 ∧
        0 ≤ C.a * (ω ^ 2) ^ 3 + C.b * (ω ^ 2) ^ 2 + C.c * ω ^ 2 + C.d := by
    intro ω
    rw [g.positiveRealAt_transfer_pcc_iff hM hL hE (jw_add_ne_zero hq ω) (hA ω), htr, hCdef,
      ← g.pccAxis_eval]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  rw [forall_congr' hpt, forall_sq_iff (P := fun x => 0 ≤ g.M ^ 2 * g.R * x ^ 2 + t1 * x + t0 ∧
    0 ≤ C.a * x ^ 3 + C.b * x ^ 2 + C.c * x + C.d)]
  have hsplit : (∀ x : ℝ, 0 ≤ x → 0 ≤ g.M ^ 2 * g.R * x ^ 2 + t1 * x + t0 ∧
      0 ≤ C.a * x ^ 3 + C.b * x ^ 2 + C.c * x + C.d) ↔
      (∀ x : ℝ, 0 ≤ x → 0 ≤ g.M ^ 2 * g.R * x ^ 2 + t1 * x + t0) ∧
        ∀ x : ℝ, 0 ≤ x → 0 ≤ C.a * x ^ 3 + C.b * x ^ 2 + C.c * x + C.d :=
    ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
      fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩
  have hM2 : 0 < g.M ^ 2 := by positivity
  have hR : 0 ≤ g.M ^ 2 * g.R ↔ 0 ≤ g.R :=
    ⟨fun h => (mul_nonneg_iff_of_pos_left hM2).mp h, fun h => by positivity⟩
  rw [hsplit, forall_nonneg_quadratic_iff, forall_nonneg_iff_halfLineNonneg, hR]

end VSMQ

end powerlib.GFM.Line
