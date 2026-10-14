import theorem.PLL.Model
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Invariant coordinates: pendulum form of the SRF-PLL, amplitude–phase and normal modes

Coordinate and trajectory identities; the only stability claims are the two connection
statements on the PI-PLL family at the end.

* Pendulum form (T-invariant-coordinates §1.2, T-gfl-multiscale §1.8). For the `(θ, ξ)` field
  `xiField a b Δω` (`θ̇ = Δω − a sin θ + b ξ`, `ξ̇ = −sin θ`, constant `Δω`, `a = V K_p`,
  `b = V K_i`): every solution has `θ ∈ C²` with
  `θ̈ + a cos θ · θ̇ + b sin θ = 0`; conversely (`b ≠ 0`) every `C²` solution of the pendulum
  equation gives a solution of the first-order system with `ξ = (θ̇ − Δω + a sin θ)/b`.
  (The note's right-hand side `dΔω/dt` vanishes for the constant offset modelled here.)
* Amplitude–phase coordinates of a dq current (T-invariant-coordinates §1.3): for the dq R–L
  filter `L İ_d = V_d − V_d^c − R I_d + ωL I_q`, `L İ_q = V_q − V_q^c − R I_q − ωL I_d`
  (IN-positive, `conventions.md` §D1, constant frame frequency `ω` or any `ω(t)`),
  `d/dt(½|I|²) = (1/L)[(V_d I_d + V_q I_q) − (V_d^c I_d + V_q^c I_q)] − (R/L)|I|²` (the rotation
  term cancels), and, where `I = I_d + j I_q` lies in the slit plane (in particular
  `|I| ≠ 0`), `φ̇ = (1/(L|I|²))[(V_q I_d − V_d I_q) − (V_q^c I_d − V_d^c I_q)] − ω` for
  `φ = arg I`. Complex power `S̄ = V̄ Ī*`: `Re S̄ = V_d I_d + V_q I_q`, `Im S̄ = V_q I_d − V_d I_q`.
* Complex normal modes of an LC pair (T-invariant-coordinates §1.4):
  `a± = √L Ī ± j √C V̄` give `|a₊|² + |a₋|² = 2(L|I|² + C|V|²) = 2η₊` and
  `|a₊|² − |a₋|² = 4 √(LC) Im(Ī V̄*)`.

Source: work-sync `theory/T-invariant-coordinates.md` §1.2, §1.3, §1.4;
`theory/T-gfl-multiscale-modeling.md` §1.8.

Correction (§1.4): the difference of the normal-mode energies is
`|a₊|² − |a₋|² = 4√(L_f C_f) Im(Ī V̄*)`; the note's "∝ Im(L_f Ī V̄*)" has the wrong scale
factor (`L_f` instead of `√(L_f C_f)`). The note also labels `|a₊|² + |a₋|² = 2η₊`
"conserved": by `normalMode_sum` this is `4H` with `H = ½L|I|² + ½C|V|²`, so it is conserved
exactly when `H` is, i.e. (energy balance `Ḣ = P_src − P_conv`, the `theorem/PH` port-
Hamiltonian LC model) only while the port power vanishes, not in general.

Family and connection conclusions. No new family: the `(θ_err, ξ)` model with gains `(a, b)`
and offset `Δω`, read about `θ*`, is the member `GFL.PIPLL.srf 1 a b (−Δω) θ*` of the PI-PLL
family (`xi_piPLLField`; its selected point is `(θ*, −Δω / b)`). The two former domain theorems
are connection statements on that family (`xi_mem_den_locallyExponentiallyStable`,
`xi_mem_den_unstable_antiPhase`). Everything else is foundation: the pendulum form, the
amplitude–phase identities and the first-integral lemma hold for the stated (generic) signals
and fields.
-/

noncomputable section
namespace powerlib.PLL
open Matrix
open powerlib.Dynamics (State)
open powerlib.GFL (piPLLState piPLLField)
open powerlib.GFL.PIPLL (srf)

@[powerlib_foundation] private lemma hasDerivAt_coord {φ : ℝ → State 2} {φ' : State 2} {t : ℝ}
    (h : HasDerivAt φ φ' t) (i : Fin 2) : HasDerivAt (fun τ => φ τ i) (φ' i) t :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t h

@[powerlib_foundation] private lemma hasDerivAt_state {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun τ => piPLLState (f τ) (g τ)) (piPLLState f' g') t := by
  have h : HasDerivAt (fun τ => ![f τ, g τ]) ![f', g'] t := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using hf
    · simpa using hg
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t h

/-! ## Pendulum form -/

/-- First-order `(θ, ξ)` system ⇒ second-order pendulum: along any solution of `xiField`,
`θ̇ = Δω − a sin θ + b ξ` and `θ̈ = −a cos θ · θ̇ − b sin θ`. -/
@[powerlib_foundation] theorem xiField_pendulum {a b Δω : ℝ} {φ : ℝ → State 2}
    (hφ : ∀ t, HasDerivAt φ (xiField a b Δω (φ t)) t) (t : ℝ) :
    HasDerivAt (fun τ => φ τ 0) (Δω - a * Real.sin (φ t 0) + b * φ t 1) t ∧
      HasDerivAt (fun τ => Δω - a * Real.sin (φ τ 0) + b * φ τ 1)
        (-(a * Real.cos (φ t 0) * (Δω - a * Real.sin (φ t 0) + b * φ t 1)) -
          b * Real.sin (φ t 0)) t := by
  have h0 := hasDerivAt_coord (hφ t) 0
  have h1 := hasDerivAt_coord (hφ t) 1
  simp only [xiField] at h0 h1
  refine ⟨by simpa using h0, ?_⟩
  have hs := (h0.sin.const_mul a)
  have h := ((hasDerivAt_const t Δω).sub hs).add (h1.const_mul b)
  convert h using 1
  simp; ring

/-- Second-order pendulum ⇒ first-order system (`b ≠ 0`): a solution `θ` of
`θ̈ + a cos θ · θ̇ + b sin θ = 0` with `ξ := (θ̇ − Δω + a sin θ)/b` solves `xiField a b Δω`. -/
@[powerlib_foundation] theorem pendulum_xiField {a b Δω : ℝ} (hb : b ≠ 0) {θ θ' : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (θ' t) t)
    (hθ' : ∀ t, HasDerivAt θ' (-(a * Real.cos (θ t) * θ' t) - b * Real.sin (θ t)) t) (t : ℝ) :
    HasDerivAt (fun τ => piPLLState (θ τ) ((θ' τ - Δω + a * Real.sin (θ τ)) / b))
      (xiField a b Δω (piPLLState (θ t) ((θ' t - Δω + a * Real.sin (θ t)) / b))) t := by
  have hξ := ((((hθ' t).sub_const Δω).add ((hθ t).sin.const_mul a))).div_const b
  convert hasDerivAt_state (hθ t) hξ using 1
  rw [GFL.state_two_ext_iff]
  simp [xiField]
  constructor
  · field_simp; ring
  · field_simp; ring

/-! ## Amplitude–phase coordinates of a dq current -/

/-- Complex power `S̄ = V̄ Ī*` in dq components (IN-positive): `Re S̄ = V_d I_d + V_q I_q`,
`Im S̄ = V_q I_d − V_d I_q`. -/
@[powerlib_foundation] theorem complexPower_re_im (Vd Vq Id Iq : ℝ) :
    ((⟨Vd, Vq⟩ : ℂ) * (starRingEnd ℂ) ⟨Id, Iq⟩).re = Vd * Id + Vq * Iq ∧
      ((⟨Vd, Vq⟩ : ℂ) * (starRingEnd ℂ) ⟨Id, Iq⟩).im = Vq * Id - Vd * Iq := by
  constructor
  · simp
  · simp; ring

/-- Squared-amplitude balance of the dq R–L filter: the frame-rotation terms cancel. -/
@[powerlib_foundation] theorem hasDerivAt_half_sq_amplitude {L R : ℝ} (hL : L ≠ 0)
    {Id Iq Vd Vq Vcd Vcq ω : ℝ → ℝ} {t : ℝ}
    (hd : HasDerivAt Id ((Vd t - Vcd t - R * Id t + ω t * L * Iq t) / L) t)
    (hq : HasDerivAt Iq ((Vq t - Vcq t - R * Iq t - ω t * L * Id t) / L) t) :
    HasDerivAt (fun τ => (Id τ ^ 2 + Iq τ ^ 2) / 2)
      (((Vd t * Id t + Vq t * Iq t) - (Vcd t * Id t + Vcq t * Iq t)) / L -
        R / L * (Id t ^ 2 + Iq t ^ 2)) t := by
  have h := ((hd.pow 2).add (hq.pow 2)).div_const 2
  convert h using 1
  field_simp
  ring

/-- Phase derivative `d/dt arg(I_d + j I_q) = (I_d İ_q − I_q İ_d)/|I|²` wherever `I` lies in
the slit plane (`|I| ≠ 0` and not on the negative real axis; any other branch of the
phase differs locally by a constant). -/
@[powerlib_foundation] theorem hasDerivAt_arg_current {Id Iq : ℝ → ℝ} {dId dIq t : ℝ}
    (hd : HasDerivAt Id dId t) (hq : HasDerivAt Iq dIq t)
    (hslit : (⟨Id t, Iq t⟩ : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (fun τ => Complex.arg ⟨Id τ, Iq τ⟩)
      ((Id t * dIq - Iq t * dId) / (Id t ^ 2 + Iq t ^ 2)) t := by
  have hz : HasDerivAt (fun τ => (⟨Id τ, Iq τ⟩ : ℂ)) (⟨dId, dIq⟩ : ℂ) t := by
    have h1 := hd.ofReal_comp
    have h2 := hq.ofReal_comp.mul_const Complex.I
    have := h1.add h2
    convert this using 1
    · funext τ; apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
  have hlog := hz.clog_real hslit
  have him := (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hlog
  have hne : (⟨Id t, Iq t⟩ : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hn2 : Id t ^ 2 + Iq t ^ 2 ≠ 0 := by
    intro h0
    apply hne
    have h1 : Id t = 0 := by nlinarith [sq_nonneg (Id t), sq_nonneg (Iq t)]
    have h2 : Iq t = 0 := by nlinarith [sq_nonneg (Id t), sq_nonneg (Iq t)]
    apply Complex.ext <;> simp [h1, h2]
  convert him using 1
  · funext τ; simp [Complex.log_im]
  · simp only [Complex.imCLM_apply, Complex.div_im, Complex.normSq_mk]
    field_simp

/-- Phase dynamics of the dq R–L filter:
`φ̇ = (1/(L|I|²))[(V_q I_d − V_d I_q) − (V_q^c I_d − V_d^c I_q)] − ω`. -/
@[powerlib_foundation] theorem hasDerivAt_phase {L R : ℝ} (hL : L ≠ 0)
    {Id Iq Vd Vq Vcd Vcq ω : ℝ → ℝ} {t : ℝ}
    (hd : HasDerivAt Id ((Vd t - Vcd t - R * Id t + ω t * L * Iq t) / L) t)
    (hq : HasDerivAt Iq ((Vq t - Vcq t - R * Iq t - ω t * L * Id t) / L) t)
    (hslit : (⟨Id t, Iq t⟩ : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (fun τ => Complex.arg ⟨Id τ, Iq τ⟩)
      (((Vq t * Id t - Vd t * Iq t) - (Vcq t * Id t - Vcd t * Iq t)) /
          (L * (Id t ^ 2 + Iq t ^ 2)) - ω t) t := by
  have h := hasDerivAt_arg_current hd hq hslit
  have hne : (⟨Id t, Iq t⟩ : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hn2 : Id t ^ 2 + Iq t ^ 2 ≠ 0 := by
    intro h0
    apply hne
    have h1 : Id t = 0 := by nlinarith [sq_nonneg (Id t), sq_nonneg (Iq t)]
    have h2 : Iq t = 0 := by nlinarith [sq_nonneg (Id t), sq_nonneg (Iq t)]
    apply Complex.ext <;> simp [h1, h2]
  convert h using 1
  field_simp
  ring

/-! ## Complex normal modes of an LC pair -/

/-- `a± = √L Ī ± j √C V̄`: `|a₊|² + |a₋|² = 2(L|I|² + C|V|²)`. -/
@[powerlib_foundation] theorem normalMode_sum {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (I V : ℂ) :
    Complex.normSq (Real.sqrt L * I + Complex.I * (Real.sqrt C * V)) +
        Complex.normSq (Real.sqrt L * I - Complex.I * (Real.sqrt C * V)) =
      2 * (L * Complex.normSq I + C * Complex.normSq V) := by
  have hl := Real.sq_sqrt hL
  have hc := Real.sq_sqrt hC
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  linear_combination (2 * (I.re ^ 2 + I.im ^ 2)) * hl + (2 * (V.re ^ 2 + V.im ^ 2)) * hc

/-- `|a₊|² − |a₋|² = 4 √(LC) Im(Ī V̄*)`. -/
@[powerlib_foundation] theorem normalMode_diff {L C : ℝ} (hL : 0 ≤ L) (I V : ℂ) :
    Complex.normSq (Real.sqrt L * I + Complex.I * (Real.sqrt C * V)) -
        Complex.normSq (Real.sqrt L * I - Complex.I * (Real.sqrt C * V)) =
      4 * Real.sqrt (L * C) * (I * (starRingEnd ℂ) V).im := by
  rw [Real.sqrt_mul hL]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The note's scale factor is wrong: with `L ≠ C` (both positive) and `Im(Ī V̄*) ≠ 0`,
`|a₊|² − |a₋|²` is not `4 L Im(Ī V̄*)`. -/
@[powerlib_foundation] theorem normalMode_diff_ne_note {L C : ℝ} (hL : 0 < L) (hC : 0 < C)
    (hLC : L ≠ C) {I V : ℂ} (hIV : (I * (starRingEnd ℂ) V).im ≠ 0) :
    Complex.normSq (Real.sqrt L * I + Complex.I * (Real.sqrt C * V)) -
        Complex.normSq (Real.sqrt L * I - Complex.I * (Real.sqrt C * V)) ≠
      4 * L * (I * (starRingEnd ℂ) V).im := by
  rw [normalMode_diff hL.le]
  intro h
  have h1 : Real.sqrt (L * C) = L := by
    have := mul_right_cancel₀ hIV (by linarith : 4 * Real.sqrt (L * C) * _ = 4 * L * _)
    linarith
  have h2 : Real.sqrt (L * C) ^ 2 = L ^ 2 := by rw [h1]
  rw [Real.sq_sqrt (mul_nonneg hL.le hC.le), sq] at h2
  exact hLC (mul_left_cancel₀ hL.ne' h2).symm

/-! ## Local stability in `(θ_err, ξ)` coordinates -/

/-- The `(θ_err, ξ)` field is the untranslated field of the unit-amplitude SRF family member with
gains `(a, b)` and offset `−Δω`. -/
@[powerlib_foundation] theorem xi_piPLLField (a b Δω θ : ℝ) :
    piPLLField (srf 1 a b (-Δω) θ).h a b (-Δω) = xiField a b Δω := by
  rw [srf_piPLLField, xiField_eq_srfField]

/-- `(θ_err, ξ)` model (T-invariant-coordinates §1.2, T-gfl-multiscale §1.3): for
`a = V K_p > 0`, `b = V K_i > 0` the equilibria `(2kπ, −Δω/b)` are locally exponentially
stable. -/
@[powerlib_domain] theorem xi_mem_den_locallyExponentiallyStable {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (Δω : ℝ) (k : ℤ) :
    connection% (srf 1 a b (-Δω) (2 * k * Real.pi) ∈
      GFL.PIPLL.family.den (.flow .locallyExponentiallyStable)) :=
  srf_mem_den_locallyExponentiallyStable_inPhase (by simpa using ha) (by simpa using hb) (-Δω) k

/-- `(θ_err, ξ)` model: for `b > 0` the equilibria `((2k+1)π, −Δω/b)` are saddles, unstable. -/
@[powerlib_domain] theorem xi_mem_den_unstable_antiPhase {a b : ℝ} (hb : 0 < b) (Δω : ℝ)
    (k : ℤ) :
    connection% (srf 1 a b (-Δω) ((2 * k + 1) * Real.pi) ∈
      GFL.PIPLL.family.den (.flow .unstable)) :=
  srf_mem_den_unstable_antiPhase (Kp := a) (by simpa using hb) (-Δω) k

end powerlib.PLL
