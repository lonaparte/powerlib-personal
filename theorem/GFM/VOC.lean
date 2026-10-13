import theorem.Synchronous.EqualArea
import theorem.Dynamics.ConverseLinearization
import theorem.CurrentControl.SISO
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Andronov–Hopf virtual oscillator (AHO-VOC) at no load

Model boundary.
* Stationary `αβ` frame; the oscillator state `v = v_α + j v_β ∈ ℂ` (i.e. the state pair
  `(v_α, v_β)`, identified with `ℂ` as a real two-dimensional space); continuous time.
* No-load AHO dynamics (`i = 0`):
  `v̇ = (j ω_s − σ + κ_v (v*² − |v|²)) v`, i.e.
  `v̇_α = −σ v_α − ω_s v_β + κ_v (v*² − |v|²) v_α`,
  `v̇_β = ω_s v_α − σ v_β + κ_v (v*² − |v|²) v_β` (`aho_re`, `aho_im`).
* Parameters `κ_v > 0`, `σ < κ_v v*²`; write `c = κ_v v*² − σ > 0` and `r* = √(v*² − σ/κ_v)`.
* Excluded: output current coupling `−κ_i i` (zero load), filters, inner loops, PWM, delays,
  multi-converter networks (no dVOC network result is claimed).

Results (trajectory level, every solution on `[0, ∞)` with `v(0) ≠ 0`):
* `r*` is the unique positive zero of the radial field `(κ_v (v*² − r²) − σ) r`.
* `|v|²` solves the logistic equation `y' = 2 (c − κ_v y) y` and equals
  `1 / (κ_v/c + (1/|v(0)|² − κ_v/c) e^{−2ct})`; in particular `v(t) ≠ 0` for all `t ≥ 0`.
* `|v(t)| → r*`.
* Phase: `v(t) = (|v(t)| / |v(0)|) e^{j ω_s t} v(0)` — the phase rotates uniformly at `ω_s`.
* The circle `|v| = r*` is invariant and carries exactly the solutions `r* e^{j(ω_s t + φ₀)}`.

Algebra (foundation): polar decomposition of the loaded AHO and the dVOC complex frequency.

Family and connection conclusions.
* `AHO.family`: a complete system is the AHO parameter set itself, read as the no-load field in
  the real coordinates `(v_α, v_β) : Dynamics.State 2` (`AHO.realField`, identified with the
  complex field by `realField_eq`); the equilibrium of the sentences is the origin `v = 0`.
  Static requirements: growth `c = κ_v v*² − σ > 0`, decay `c < 0`, stiffness `κ_v ≥ 0`, and a
  decay-rate bound `r ≤ −c`.  Instability translates into growth (Jacobian `[[c, −ω_s], [ω_s, c]]`
  at the origin, trace `2c`); the local sentences into decay (linearization); the global
  sentences and sampled contraction into decay and stiffness (the energy `|v|²` decays at the
  rate `2|c|`, `Flow.QuadraticDecay`); the decay rate `r` into stiffness and `r ≤ −c`; passivity
  into nothing (exact); conservation into the whole, inconsistent, language.
  `AHO.chain_le_semantics` proves soundness; `AHO.exact_locallyExponentiallyStable` proves the
  local exponential translation exact (converse linearization: the Jacobian at the origin is
  Hurwitz iff `c < 0`). The asymptotic and Lyapunov translations are not exact: the critical
  oscillator `AHO.critical` (`ω_s = 0`, `σ = κ_v = v* = 1`, so `c = 0` and `ṙ = −r³`) is globally
  asymptotically stable through the strict Lyapunov function `|v|²`
  (`AHO.critical_mem_den_globallyAsymptoticallyStable`) without decay at the origin
  (`AHO.not_exact_globallyAsymptoticallyStable`, `AHO.not_exact_locallyAsymptoticallyStable`,
  `AHO.not_exact_lyapunovStable`): the cubic-damping boundary of the linearization. Their
  denotations are decided exactly (`AHO.mem_den_locallyAsymptoticallyStable_iff`: `c < 0`, or
  `c = 0` with `κ_v > 0`; `AHO.mem_den_lyapunovStable_iff`: `c < 0`, or `c = 0` with `κ_v ≥ 0`): at
  `c = 0` the energy obeys `d|v|²/dt = −2 κ_v |v|⁴`, a strict Lyapunov function for `κ_v > 0`,
  conserved for `κ_v = 0` (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`) and growing for
  `κ_v < 0` (`Dynamics.unstable_of_chetaev`).
* New connection conclusion for the module's own regime: under the standing assumptions the
  origin is unstable (`Admissible.mem_den_unstable`): solutions leave the origin, towards the limit
  cycle of the trajectory-level results.
* The limit-cycle results above (`normSq_formula`, `norm_tendsto_rstar`, `phase_rotation`,
  `norm_eq_rstar_of_start`, `limitCycle_isSolution`) are trajectory level and outside the sentence
  language (Rules §3a): they are private implementation evidence, as is the explicit logistic
  formula `inv_normSq_eq` (formerly public foundation; the parameter type `AHO` now carries a
  family, so its public behavioural statements must be connection statements).  `radial_zero_iff`
  is static evidence on the model; the pointwise chain rules `hasDerivWithinAt_normSq`,
  `hasDerivWithinAt_norm` stay public foundation.

Corrections.
* T-voc-dvoc §1.8 writes the dVOC complex frequency as
  `η̄ = jω_s + (η/v)(K e_θ / v + α(v*² − |v|²))`; from `v̇ = jω_s v + η(e_θ + α(v*² − |v|²) v)`
  the correct expression is `v̇/v = jω_s + η e_θ / v + η α (v*² − |v|²)` (`dvoc_complexFrequency`).
* The dVOC control law of §1.3 differs from Colombino et al. 2019; no dVOC multi-converter
  statement is formalized.

Source: work-sync theory/T-voc-dvoc.md §1.2, §1.3, §1.8; theory/T-gfm-control.md §1.5.
-/

noncomputable section
namespace powerlib.GFM
open Set Filter Topology Complex
open powerlib.Dynamics (State)

/-- AHO parameters. -/
structure AHO where
  ωs : ℝ
  σ : ℝ
  κv : ℝ
  vstar : ℝ

namespace AHO

variable (a : AHO)

/-- Radial growth coefficient `c = κ_v v*² − σ`. -/
def c : ℝ := a.κv * a.vstar ^ 2 - a.σ

/-- Limit-cycle radius `r* = √(v*² − σ/κ_v)`. -/
def rstar : ℝ := Real.sqrt (a.vstar ^ 2 - a.σ / a.κv)

/-- Real gain `κ_v (v*² − |v|²) − σ = c − κ_v |v|²`. -/
def gain (v : ℂ) : ℝ := a.c - a.κv * normSq v

/-- No-load AHO field `v̇ = (j ω_s + c − κ_v |v|²) v`. -/
def field (v : ℂ) : ℂ := (I * a.ωs + (a.gain v : ℂ)) * v

@[powerlib_foundation] theorem aho_re (v : ℂ) :
    (a.field v).re = -a.σ * v.re - a.ωs * v.im + a.κv * (a.vstar ^ 2 - normSq v) * v.re := by
  simp only [field, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [gain, c]; ring

@[powerlib_foundation] theorem aho_im (v : ℂ) :
    (a.field v).im = a.ωs * v.re - a.σ * v.im + a.κv * (a.vstar ^ 2 - normSq v) * v.im := by
  simp only [field, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [gain, c]; ring

/-- Standing assumptions `κ_v > 0`, `σ < κ_v v*²`. -/
structure Admissible : Prop where
  κv : 0 < a.κv
  gap : a.σ < a.κv * a.vstar ^ 2

variable {a}

@[powerlib_foundation] theorem Admissible.c_pos (h : a.Admissible) : 0 < a.c := by
  simp only [c]; linarith [h.gap]

@[powerlib_foundation] theorem Admissible.rstar_sq (h : a.Admissible) :
    a.rstar ^ 2 = a.c / a.κv := by
  have hk := h.κv
  rw [rstar, Real.sq_sqrt]
  · simp only [c]; field_simp
  · rw [sub_nonneg, div_le_iff₀ hk]; linarith [h.gap]

@[powerlib_foundation] theorem Admissible.rstar_pos (h : a.Admissible) : 0 < a.rstar := by
  apply Real.sqrt_pos.mpr
  rw [sub_pos, div_lt_iff₀ h.κv]; linarith [h.gap]

/-- `r*` is the unique positive zero of the radial field.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem radial_zero_iff (h : a.Admissible) {r : ℝ} (hr : 0 < r) :
    (a.κv * (a.vstar ^ 2 - r ^ 2) - a.σ) * r = 0 ↔ r = a.rstar := by
  have hk := h.κv
  rw [mul_eq_zero, or_iff_left hr.ne']
  constructor
  · intro h0
    have hsq : r ^ 2 = a.rstar ^ 2 := by
      rw [h.rstar_sq]; simp only [c]; field_simp; linarith
    exact (pow_left_inj₀ hr.le h.rstar_pos.le two_ne_zero).mp hsq
  · intro he
    have := h.rstar_sq
    rw [← he] at this
    rw [this]; simp only [c]; field_simp; ring

variable (a)

/-- `d|v|²/dt = 2 (c − κ_v |v|²) |v|²` along the field. -/
@[powerlib_foundation] theorem hasDerivWithinAt_normSq {φ : ℝ → ℂ} {s : Set ℝ} {t : ℝ}
    (hφ : HasDerivWithinAt φ (a.field (φ t)) s t) :
    HasDerivWithinAt (fun τ => normSq (φ τ))
      (2 * a.gain (φ t) * normSq (φ t)) s t := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hφ
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hφ
  have h := (hre.mul hre).add (him.mul him)
  convert h using 1
  · funext τ; simp [normSq_apply, Function.comp_def]
  · simp only [Function.comp_apply, reCLM_apply, imCLM_apply]
    rw [show (a.field (φ t)).re = a.gain (φ t) * (φ t).re - a.ωs * (φ t).im by
      simp only [field, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring,
      show (a.field (φ t)).im = a.ωs * (φ t).re + a.gain (φ t) * (φ t).im by
      simp only [field, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring]
    rw [normSq_apply]; ring

/-- On any interval where `|v|² > 0`, `1/|v|² = κ_v/c + (1/|v(0)|² − κ_v/c) e^{−2ct}`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem inv_normSq_eq (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) {T : ℝ}
    (hpos : ∀ t ∈ Icc 0 T, 0 < normSq (φ t)) :
    ∀ t ∈ Icc 0 T, 1 / normSq (φ t) =
      a.κv / a.c + (1 / normSq (φ 0) - a.κv / a.c) * Real.exp (-(2 * a.c * t)) := by
  have hc := h.c_pos
  set w : ℝ → ℝ := fun t => (1 / normSq (φ t) - a.κv / a.c) * Real.exp (2 * a.c * t) with hw
  have hcont : ContinuousOn (fun t => normSq (φ t)) (Icc 0 T) :=
    (Complex.continuous_normSq.comp_continuousOn hφ.continuousOn).mono Icc_subset_Ici_self
  have hconst := constant_of_has_deriv_right_zero (f := w) (a := 0) (b := T)
    (by
      apply ContinuousOn.mul _ (by fun_prop)
      apply ContinuousOn.sub _ continuousOn_const
      exact continuousOn_const.div hcont (fun t ht => (hpos t ht).ne'))
    (by
      intro x hx
      have hx' : x ∈ Ici (0 : ℝ) := hx.1
      have hy := (a.hasDerivWithinAt_normSq (hφ x hx')).mono (Ici_subset_Ici.mpr hx.1)
      have hyx := hpos x ⟨hx.1, hx.2.le⟩
      have hinv := (hy.inv hyx.ne').const_mul 1
      have he : HasDerivWithinAt (fun t => Real.exp (2 * a.c * t))
          (Real.exp (2 * a.c * x) * (2 * a.c)) (Ici x) x := by
        have := ((hasDerivAt_id x).const_mul (2 * a.c)).exp
        simpa using this.hasDerivWithinAt
      have hp := (hinv.sub_const (a.κv / a.c)).mul he
      convert hp using 1
      · funext t; simp [hw, div_eq_mul_inv]
      · simp only [gain, Pi.inv_apply]
        field_simp
        ring)
  intro t ht
  have h1 := hconst t ht
  simp only [hw, mul_zero, Real.exp_zero, mul_one] at h1
  have hEpos := Real.exp_pos (2 * a.c * t)
  have h2 : 1 / normSq (φ t) - a.κv / a.c =
      (1 / normSq (φ 0) - a.κv / a.c) * (Real.exp (2 * a.c * t))⁻¹ := by
    rw [← h1, mul_assoc, mul_inv_cancel₀ hEpos.ne', mul_one]
  rw [Real.exp_neg]
  linarith

/-- Solutions starting away from the origin never reach it, and `|v|²` is given by the explicit
logistic formula.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem normSq_formula (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) (h0 : φ 0 ≠ 0) :
    ∀ t ∈ Ici (0 : ℝ), 0 < normSq (φ t) ∧ 1 / normSq (φ t) =
      a.κv / a.c + (1 / normSq (φ 0) - a.κv / a.c) * Real.exp (-(2 * a.c * t)) := by
  have hc := h.c_pos
  have hk := h.κv
  have hy0 : 0 < normSq (φ 0) := normSq_pos.mpr h0
  set Z := max (a.κv / a.c) (1 / normSq (φ 0)) with hZ
  have hZpos : 0 < Z := lt_max_of_lt_left (div_pos hk hc)
  have hbound : ∀ t : ℝ, 0 ≤ t →
      a.κv / a.c + (1 / normSq (φ 0) - a.κv / a.c) * Real.exp (-(2 * a.c * t)) ≤ Z := by
    intro t ht
    have he1 : Real.exp (-(2 * a.c * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he0 : 0 < Real.exp (-(2 * a.c * t)) := Real.exp_pos _
    have h1 := le_max_left (a.κv / a.c) (1 / normSq (φ 0))
    have h2 := le_max_right (a.κv / a.c) (1 / normSq (φ 0))
    nlinarith
  have hcontAll : ContinuousOn (fun t => normSq (φ t)) (Ici 0) :=
    Complex.continuous_normSq.comp_continuousOn hφ.continuousOn
  have hposAll : ∀ T : ℝ, 0 ≤ T → ∀ t ∈ Icc 0 T, 0 < normSq (φ t) := by
    intro T _
    apply Synchronous.pos_on_Icc_of_propagate (hcontAll.mono Icc_subset_Ici_self) hy0
    intro t ht hbefore
    -- lower bound `1/Z` on `[0, t)`
    have hlow : ∀ s ∈ Ico 0 t, 1 / Z ≤ normSq (φ s) := by
      intro s hs
      have hf := a.inv_normSq_eq h hφ (T := s) (fun r hr => hbefore r ⟨hr.1, lt_of_le_of_lt hr.2
        hs.2⟩) s ⟨hs.1, le_rfl⟩
      have hb := hbound s hs.1
      have hys := hbefore s hs
      rw [← hf] at hb
      rw [div_le_iff₀ hZpos]
      rw [div_le_iff₀ hys] at hb
      linarith
    by_contra hneg
    push Not at hneg
    have hlt : normSq (φ t) < 1 / Z := lt_of_le_of_lt hneg (by positivity)
    have hy0Z : 1 / Z ≤ normSq (φ 0) := by
      rw [div_le_iff₀ hZpos]
      have := le_max_right (a.κv / a.c) (1 / normSq (φ 0))
      rw [← hZ, div_le_iff₀ hy0] at this
      linarith [mul_comm (normSq (φ 0)) Z]
    obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc' ht.1.le
      (hcontAll.mono Icc_subset_Ici_self)
      (show (normSq (φ t) + 1 / Z) / 2 ∈ Icc (normSq (φ t)) (normSq (φ 0)) from
        ⟨by linarith, by linarith⟩)
    simp only at hsv
    have hst : s ≠ t := by rintro rfl; linarith
    have := hlow s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    linarith
  intro t ht
  have hp := hposAll t ht t ⟨ht, le_rfl⟩
  exact ⟨hp, a.inv_normSq_eq h hφ (hposAll t ht) t ⟨ht, le_rfl⟩⟩

/-- Every solution with `v(0) ≠ 0` converges in amplitude to the limit-cycle radius.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem norm_tendsto_rstar (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) (h0 : φ 0 ≠ 0) :
    Tendsto (fun t => ‖φ t‖) atTop (𝓝 a.rstar) := by
  have hc := h.c_pos
  have hk := h.κv
  have hform := a.normSq_formula h hφ h0
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(2 * a.c * t))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_neg_atTop_nhds_zero.comp
    exact tendsto_id.const_mul_atTop (by positivity)
  have hinv : Tendsto (fun t => a.κv / a.c + (1 / normSq (φ 0) - a.κv / a.c) *
      Real.exp (-(2 * a.c * t))) atTop (𝓝 (a.κv / a.c)) := by
    simpa using (hexp.const_mul (1 / normSq (φ 0) - a.κv / a.c)).const_add (a.κv / a.c)
  have hy : Tendsto (fun t => normSq (φ t)) atTop (𝓝 (a.c / a.κv)) := by
    have h1 := hinv.inv₀ (div_pos hk hc).ne'
    rw [inv_div] at h1
    apply h1.congr'
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := (hform t ht).2
    rw [← this, one_div, inv_inv]
  have hnorm : (fun t => ‖φ t‖) = fun t => Real.sqrt (normSq (φ t)) := by
    funext t; rw [← Complex.norm_def]
  rw [hnorm, rstar, show a.vstar ^ 2 - a.σ / a.κv = a.c / a.κv by simp only [c]; field_simp]
  exact (Real.continuous_sqrt.tendsto _).comp hy

/-- `d‖v‖/dt = gain · ‖v‖` along the field (away from the origin). -/
@[powerlib_foundation] theorem hasDerivWithinAt_norm {φ : ℝ → ℂ} {s : Set ℝ} {t : ℝ}
    (hφ : HasDerivWithinAt φ (a.field (φ t)) s t) (hne : φ t ≠ 0) :
    HasDerivWithinAt (fun τ => ‖φ τ‖) (a.gain (φ t) * ‖φ t‖) s t := by
  have hy := a.hasDerivWithinAt_normSq hφ
  have hsq := hy.sqrt (normSq_pos.mpr hne).ne'
  have hn : (fun τ => ‖φ τ‖) = fun τ => Real.sqrt (normSq (φ τ)) := by
    funext τ; rw [← Complex.norm_def]
  rw [hn]
  convert hsq using 1
  rw [← Complex.norm_def]
  have hpos : 0 < ‖φ t‖ := norm_pos_iff.mpr hne
  rw [Complex.normSq_eq_norm_sq]
  field_simp

/-- Uniform phase rotation: `v(t) = (|v(t)|/|v(0)|) e^{j ω_s t} v(0)` for every solution with
`v(0) ≠ 0`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem phase_rotation (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) (h0 : φ 0 ≠ 0) :
    ∀ t ∈ Ici (0 : ℝ), φ t = ((‖φ t‖ / ‖φ 0‖ : ℝ) : ℂ) * exp (I * a.ωs * t) * φ 0 := by
  have hform := a.normSq_formula h hφ h0
  have hne : ∀ t ∈ Ici (0 : ℝ), φ t ≠ 0 := fun t ht =>
    normSq_pos.mp (hform t ht).1
  set u : ℝ → ℂ := fun t => φ t * exp (-(I * a.ωs * t)) * ((1 / ‖φ t‖ : ℝ) : ℂ) with hu
  have hconst : ∀ T : ℝ, 0 ≤ T → ∀ t ∈ Icc 0 T, u t = u 0 := by
    intro T _
    apply constant_of_has_deriv_right_zero
    · intro x hx
      have hx' : x ∈ Ici (0 : ℝ) := hx.1
      have hcφ : ContinuousWithinAt φ (Icc 0 T) x :=
        ((hφ x hx').continuousWithinAt).mono Icc_subset_Ici_self
      have hcn : ContinuousWithinAt (fun τ => ((1 / ‖φ τ‖ : ℝ) : ℂ)) (Icc 0 T) x := by
        apply Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        exact continuousWithinAt_const.div hcφ.norm (norm_ne_zero_iff.mpr (hne x hx'))
      exact (hcφ.mul (by fun_prop : Continuous fun τ : ℝ => exp (-(I * a.ωs * τ))).continuousWithinAt).mul hcn
    · intro x hx
      have hx' : x ∈ Ici (0 : ℝ) := hx.1
      have hd := (hφ x hx').mono (Ici_subset_Ici.mpr hx.1)
      have hN := a.hasDerivWithinAt_norm hd (hne x hx')
      have hNpos : 0 < ‖φ x‖ := norm_pos_iff.mpr (hne x hx')
      have hinvN := (hN.inv hNpos.ne').const_mul (1 : ℝ)
      have hinvC := hinvN.ofReal_comp
      have hE : HasDerivAt (fun τ : ℝ => exp (-(I * a.ωs * τ)))
          (exp (-(I * a.ωs * x)) * (-(I * a.ωs))) x := by
        have := (((hasDerivAt_id x).ofReal_comp).const_mul (-(I * a.ωs))).cexp
        convert this using 1
        · funext τ; simp
        · simp
      have hp := (hd.mul hE.hasDerivWithinAt).mul hinvC
      convert hp using 1
      · funext τ; simp [hu, div_eq_mul_inv]
      · simp only [field, one_mul, Pi.inv_apply, Pi.mul_apply]
        push_cast
        field_simp
        ring
  intro t ht
  have hut := hconst t ht t ⟨ht, le_rfl⟩
  simp only [hu, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] at hut
  have hN0 : 0 < ‖φ 0‖ := norm_pos_iff.mpr h0
  have hNt : 0 < ‖φ t‖ := norm_pos_iff.mpr (hne t ht)
  have hEE : exp (-(I * a.ωs * t)) * exp (I * a.ωs * t) = 1 := by
    rw [← Complex.exp_add]; simp
  have hNt' : ((‖φ t‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hNt.ne'
  have hN0' : ((‖φ 0‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have key := congrArg (fun z => z * ((‖φ t‖ : ℝ) : ℂ) * exp (I * a.ωs * t)) hut
  push_cast at key ⊢
  calc φ t = φ t * exp (-(I * a.ωs * t)) * (1 / (‖φ t‖ : ℂ)) * (‖φ t‖ : ℂ) *
        exp (I * a.ωs * t) := by
          field_simp
          rw [mul_assoc, hEE, mul_one]
    _ = φ 0 * (1 / (‖φ 0‖ : ℂ)) * (‖φ t‖ : ℂ) * exp (I * a.ωs * t) := key
    _ = (‖φ t‖ : ℂ) / (‖φ 0‖ : ℂ) * exp (I * a.ωs * t) * φ 0 := by
          field_simp

/-- The circle `|v| = r*` is invariant: a solution starting on it stays on it.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem norm_eq_rstar_of_start (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0))
    (h0 : ‖φ 0‖ = a.rstar) : ∀ t ∈ Ici (0 : ℝ), ‖φ t‖ = a.rstar := by
  have hc := h.c_pos
  have hk := h.κv
  have hne : φ 0 ≠ 0 := by
    intro hz; rw [hz, norm_zero] at h0; exact h.rstar_pos.ne' h0.symm
  have hform := a.normSq_formula h hφ hne
  have hy0 : normSq (φ 0) = a.c / a.κv := by
    rw [Complex.normSq_eq_norm_sq, h0, h.rstar_sq]
  intro t ht
  obtain ⟨hp, hf⟩ := hform t ht
  rw [hy0] at hf
  simp only [one_div, inv_div, sub_self, zero_mul, add_zero] at hf
  have hyt : normSq (φ t) = a.c / a.κv := by
    have := congrArg (·⁻¹) hf
    simpa [inv_div] using this
  have := Complex.normSq_eq_norm_sq (φ t)
  rw [hyt, ← h.rstar_sq] at this
  exact ((pow_left_inj₀ (norm_nonneg _) h.rstar_pos.le two_ne_zero).mp this.symm)

/-- The limit-cycle solutions `r* e^{j(ω_s t + φ₀)}` solve the AHO.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem limitCycle_isSolution (h : a.Admissible) (φ₀ : ℝ) :
    IsIntegralCurveOn
      (fun t : ℝ => (a.rstar : ℂ) * exp (I * (a.ωs * t + φ₀))) (fun _ v => a.field v) univ := by
  intro t _
  have hd : HasDerivAt (fun t : ℝ => (a.rstar : ℂ) * exp (I * (a.ωs * t + φ₀)))
      ((a.rstar : ℂ) * (exp (I * (a.ωs * t + φ₀)) * (I * a.ωs))) t := by
    have h1 : HasDerivAt (fun t : ℝ => I * ((a.ωs : ℂ) * (t : ℂ) + (φ₀ : ℂ))) (I * a.ωs) t := by
      have := (((hasDerivAt_id t).ofReal_comp).const_mul (a.ωs : ℂ)).add_const (φ₀ : ℂ)
      simpa using this.const_mul I
    exact h1.cexp.const_mul _
  apply hd.hasDerivWithinAt.congr_deriv
  have hn : normSq ((a.rstar : ℂ) * exp (I * (a.ωs * t + φ₀))) = a.c / a.κv := by
    rw [normSq_mul, normSq_ofReal, ← h.rstar_sq]
    have : normSq (exp (I * (a.ωs * t + φ₀))) = 1 := by
      rw [Complex.normSq_eq_norm_sq, show I * ((a.ωs : ℂ) * t + φ₀) = ((a.ωs * t + φ₀ : ℝ) : ℂ) * I
        by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
      simp
    rw [this]; ring
  simp only [field, gain, hn]
  have hk := h.κv
  rw [show a.c - a.κv * (a.c / a.κv) = 0 by field_simp; ring]
  simp
  ring


/-! ## The no-load AHO family: the origin in real coordinates -/

/-- The no-load AHO field in the real coordinates `(v_α, v_β)`. -/
def realField (x : State 2) : State 2 :=
  Synchronous.mkState ((a.c - a.κv * (x 0 ^ 2 + x 1 ^ 2)) * x 0 - a.ωs * x 1)
    (a.ωs * x 0 + (a.c - a.κv * (x 0 ^ 2 + x 1 ^ 2)) * x 1)

/-- The real field is the complex field `v̇ = (j ω_s + c − κ_v |v|²) v` in the coordinates
`v = v_α + j v_β`. -/
@[powerlib_foundation] theorem realField_eq (x : State 2) :
    a.realField x = Synchronous.mkState (a.field ⟨x 0, x 1⟩).re (a.field ⟨x 0, x 1⟩).im := by
  apply Synchronous.state_ext
  · simp only [realField, Synchronous.mkState_zero, aho_re, normSq_mk, c]
    ring
  · simp only [realField, Synchronous.mkState_one, aho_im, normSq_mk, c]
    ring

/-- The Jacobian of the real field at `x`. -/
def realJacobian (x : State 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a.c - a.κv * (3 * x 0 ^ 2 + x 1 ^ 2), -a.ωs - 2 * a.κv * x 0 * x 1;
     a.ωs - 2 * a.κv * x 0 * x 1, a.c - a.κv * (x 0 ^ 2 + 3 * x 1 ^ 2)]

@[powerlib_foundation] theorem contDiff_realField : ContDiff ℝ 1 a.realField := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [realField] <;> fun_prop

@[powerlib_foundation] theorem hasFDerivAt_realField (x : State 2) :
    HasFDerivAt a.realField (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (a.realJacobian x)) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hg := (hasFDerivAt_const a.c x).sub (((h0.pow 2).add (h1.pow 2)).const_mul a.κv)
  fin_cases i
  · have h := (hg.mul h0).sub (h1.const_mul a.ωs)
    convert h using 1
    · funext y; simp [realField]
    · apply ContinuousLinearMap.ext; intro v
      simp [realJacobian, Synchronous.toEuclideanCLM_apply_zero]
      ring
  · have h := (h0.const_mul a.ωs).add (hg.mul h1)
    convert h using 1
    · funext y; simp [realField]
    · apply ContinuousLinearMap.ext; intro v
      simp [realJacobian, Synchronous.toEuclideanCLM_apply_one]
      ring

@[simp, powerlib_foundation] theorem realField_zero : a.realField 0 = 0 := by
  apply Synchronous.state_ext <;> simp [realField]

@[powerlib_foundation] theorem realJacobian_zero :
    a.realJacobian 0 = !![a.c, -a.ωs; a.ωs, a.c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realJacobian]

/-- Static requirements on AHO parameter sets. -/
inductive Requirement
  /-- Growth at the origin: `c = κ_v v*² − σ > 0`. -/
  | growing
  /-- Decay at the origin: `c < 0`. -/
  | decaying
  /-- Nonnegative amplitude gain: `κ_v ≥ 0`. -/
  | stiff
  /-- The decay rate `r` does not exceed `−c`. -/
  | decayRate (r : ℝ)

/-- Satisfaction of a requirement by an AHO parameter set. -/
def Meets (a : AHO) : Requirement → Prop
  | .growing => 0 < a.c
  | .decaying => a.c < 0
  | .stiff => 0 ≤ a.κv
  | .decayRate r => r + a.c ≤ 0

/-- The translation of the sentences about the origin: instability into growth; the local
sentences into decay; the global sentences and sampled contraction into decay and stiffness; a
decay rate into stiffness and the rate bound; passivity into nothing; conservation into the whole
language, which no parameter set meets (unavailable translation coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.decaying}
  | .flow .globallyAsymptoticallyStable | .flow .globallyExponentiallyStable
  | .flow .contractive => {.decaying, .stiff}
  | .flow (.decay r) => {.stiff, .decayRate r}
  | .flow .unstable => {.growing}
  | .flow .conservative => Set.univ
  | .passive => ∅

/-- The no-load AHO family: each parameter set read as its real field about the origin. -/
def family : Family AHO Requirement 2 0 :=
  ⟨fun a => Port.System.autonomous a.realField, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous AHO.realField :=
  fun _ => rfl

variable {a}

/-! ### Implementation evidence (private) -/

/-- The energy `|v|² = v_α² + v_β²`. -/
private def energy (x : State 2) : ℝ := x 0 ^ 2 + x 1 ^ 2

private theorem hasFDerivAt_energy (x : State 2) :
    HasFDerivAt energy ((2 * x 0) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ) +
      (2 * x 1) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ)) x := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h := (h0.pow 2).add (h1.pow 2)
  convert h using 1
  · funext y; simp [energy]
  apply ContinuousLinearMap.ext; intro v
  simp

private theorem energy_eq (x : State 2) : energy x = ‖x - 0‖ ^ 2 := by
  rw [sub_zero, Synchronous.norm_sq_state, energy]

private theorem dissipation (hκ : 0 ≤ a.κv) (x : State 2) :
    fderiv ℝ energy x (a.realField x) ≤ -(-2 * a.c) * energy x := by
  rw [(hasFDerivAt_energy x).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, PiLp.proj_apply,
    smul_eq_mul, realField, Synchronous.mkState_zero, Synchronous.mkState_one, energy]
  nlinarith [mul_nonneg hκ (sq_nonneg (x 0 ^ 2 + x 1 ^ 2))]

private def quadraticDecay (hc : a.c < 0) (hκ : 0 ≤ a.κv) :
    Flow.QuadraticDecay a.realField energy 0 where
  lower := 1
  upper := 1
  rate := -2 * a.c
  lower_pos := one_pos
  upper_pos := one_pos
  rate_pos := by linarith
  smooth := by unfold energy; fun_prop
  equilibrium := a.realField_zero
  lower_bound x := by rw [energy_eq, one_mul]
  upper_bound x := by rw [energy_eq, one_mul]
  dissipation := dissipation hκ

private theorem ges (hc : a.c < 0) (hκ : 0 ≤ a.κv) :
    Flow.GloballyExponentiallyStable a.realField 0 :=
  (quadraticDecay hc hκ).globallyExponentiallyStable a.contDiff_realField

private theorem les (hc : a.c < 0) : LocallyExponentiallyStable a.realField 0 :=
  Criteria.locallyExponentiallyStable_of_jacobian_fin_two _ a.contDiff_realField
    a.realField_zero (a.hasFDerivAt_realField 0).fderiv
    (by rw [realJacobian_zero, Matrix.trace_fin_two_of]; linarith)
    (by rw [realJacobian_zero, Matrix.det_fin_two_of]; nlinarith [sq_nonneg a.ωs, sq_pos_of_neg hc])

private theorem unstable_of (hc : 0 < a.c) : Unstable a.realField 0 :=
  Criteria.unstable_of_jacobian_trace_pos_fin_two _ a.contDiff_realField a.realField_zero
    (a.hasFDerivAt_realField 0).fderiv
    (by rw [realJacobian_zero, Matrix.trace_fin_two_of]; linarith)

private theorem decay_of (hκ : 0 ≤ a.κv) {r : ℝ} (hr : r + a.c ≤ 0) :
    Flow.Decay a.realField 0 r := by
  have h : Flow.Decay a.realField 0 (-2 * a.c / 2) :=
    ⟨_, fun _ _ _ hφ _ ht => Flow.norm_bound_of_dissipation (lower := 1) (upper := 1)
      (by unfold energy; fun_prop) one_pos one_pos (fun x => by rw [energy_eq, one_mul])
      (fun x => by rw [energy_eq, one_mul]) (dissipation hκ) hφ ht⟩
  exact h.mono (by linarith)

/-! ### Soundness of the translation -/

/-- The whole requirement language is inconsistent: the origin cannot both grow and decay. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext a
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have h1 : 0 < a.c := h .growing
  have h2 : a.c < 0 := h .decaying
  linarith

/-- Every translation of the no-load AHO family is sound: linearization at the origin for the
local sentences and instability, the decaying energy `|v|²` for the global sentences, sampled
contraction and decay rates, and passivity without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s a hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets a q at hm
  rcases s with P | _
  · rw [family_isAutonomous.mem_den_flow]
    cases P
    case lyapunovStable => exact (les (hm .decaying (by simp [translate]))).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (les (hm .decaying (by simp [translate])))
    case locallyExponentiallyStable => exact les (hm .decaying (by simp [translate]))
    case globallyAsymptoticallyStable =>
      exact (ges (hm .decaying (by simp [translate])) (hm .stiff (by simp [translate]))).globallyAsymptoticallyStable
    case globallyExponentiallyStable =>
      exact ges (hm .decaying (by simp [translate])) (hm .stiff (by simp [translate]))
    case contractive =>
      exact (ges (hm .decaying (by simp [translate])) (hm .stiff (by simp [translate]))).sampledContraction
    case decay r =>
      exact decay_of (hm .stiff (by simp [translate])) (hm (.decayRate r) (by simp [translate]))
    case unstable => exact unstable_of (hm .growing (by simp [translate]))
    case conservative =>
      have h1 : 0 < a.c := hm .growing trivial
      have h2 : a.c < 0 := hm .decaying trivial
      exact absurd h1 (not_lt.mpr h2.le)
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- The local exponential translation is exact: the origin of the no-load AHO is locally
exponentially stable exactly when it decays, `c = κ_v v*² − σ < 0`. Converse linearization: local
exponential stability forces a Hurwitz Jacobian `[[c, −ω_s], [ω_s, c]]` (trace `2c`). -/
@[powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  ext a
  rw [TMIO.mem_realize, family_isAutonomous.mem_den_flow]
  change _ ↔ LocallyExponentiallyStable _ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_of_eq _ a.contDiff_realField
    a.realField_zero (a.hasFDerivAt_realField 0).fderiv, realJacobian_zero,
    Criteria.isHurwitz_fin_two_of_iff]
  simp only [family, translate, Set.mem_singleton_iff, forall_eq, Meets]
  constructor
  · intro hc
    exact ⟨by linarith, by nlinarith [sq_nonneg a.ωs, sq_pos_of_neg hc]⟩
  · rintro ⟨h, -⟩
    linarith

/-! ### Members -/

/-- Growth at the origin (`σ < κ_v v*²`) makes the origin unstable. -/
@[powerlib_domain] theorem mem_den_unstable (a : AHO) (hc : 0 < a.c) :
    connection% (a ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact family_isAutonomous.mem_den_flow.mpr (unstable_of hc)

/-- Under the standing assumptions `κ_v > 0`, `σ < κ_v v*²` of the limit-cycle results, the
origin of the no-load AHO is unstable. -/
@[powerlib_domain] theorem Admissible.mem_den_unstable (h : a.Admissible) :
    connection% (a ∈ family.den (.flow .unstable)) :=
  AHO.mem_den_unstable a h.c_pos

/-- Decay at the origin (`κ_v v*² < σ`) makes the origin locally exponentially stable, for every
sign of `κ_v`. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable (a : AHO) (hc : a.c < 0) :
    connection% (a ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact family_isAutonomous.mem_den_flow.mpr (les hc)

/-- Decay at the origin with `κ_v ≥ 0` makes the origin globally exponentially stable. -/
@[powerlib_domain] theorem mem_den_globallyExponentiallyStable (a : AHO) (hc : a.c < 0)
    (hκ : 0 ≤ a.κv) : connection% (a ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact family_isAutonomous.mem_den_flow.mpr (ges hc hκ)

/-- With `κ_v ≥ 0` every solution segment decays at every rate `r ≤ −c` (a growth bound when
`c > 0`). -/
@[powerlib_domain] theorem mem_den_decay (a : AHO) (hκ : 0 ≤ a.κv) {r : ℝ} (hr : r + a.c ≤ 0) :
    connection% (a ∈ family.den (.flow (.decay r))) := by
  unfold powerlib.TMIO.Statement
  exact family_isAutonomous.mem_den_flow.mpr (decay_of hκ hr)

/-! ### Boundary witness: cubic damping at `c = 0` -/

private theorem energy_lie (a : AHO) (x : State 2) :
    fderiv ℝ energy x (a.realField x) = 2 * a.c * energy x - 2 * a.κv * energy x ^ 2 := by
  rw [(hasFDerivAt_energy x).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, PiLp.proj_apply,
    smul_eq_mul, realField, Synchronous.mkState_zero, Synchronous.mkState_one, energy]
  ring

private theorem energy_pos {x : State 2} (hx : x ≠ 0) : 0 < energy x := by
  rw [energy_eq, sub_zero]
  have : 0 < ‖x‖ := norm_pos_iff.mpr hx
  positivity

/-- The critical AHO `ω_s = 0`, `σ = κ_v = v* = 1`: the linear growth rate vanishes, `c = 0`,
and the amplitude obeys the cubic damping `ṙ = −r³`. -/
def critical : AHO := ⟨0, 1, 1, 1⟩

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem critical_c : critical.c = 0 := by
  simp [critical, AHO.c]

/-- The energy `|v|²` is a strict global Lyapunov function of the critical AHO: its derivative
along the field is `−2 |v|⁴`. -/
private theorem critical_strictLyapunov : IsStrictLyapunovFunction critical.realField energy 0 where
  hcont := by unfold energy; fun_prop
  hV_c1 := by unfold energy; fun_prop
  hzero := by simp [energy]
  hpos x hx := energy_pos hx
  hequil := critical.realField_zero
  hLie_neg x hx := by
    rw [energy_lie, critical_c]
    have h := energy_pos hx
    have hk : critical.κv = 1 := rfl
    rw [hk]
    nlinarith
  hbounded_sublevel c := by
    refine (isCompact_closedBall (0 : State 2) (Real.sqrt (max c 0))).of_isClosed_subset
      (isClosed_le (by unfold energy; fun_prop) continuous_const) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have hx' : ‖x‖ ^ 2 ≤ max c 0 := by
      have := energy_eq x
      rw [sub_zero] at this
      rw [← this]
      exact (Set.mem_ofPred_eq ▸ hx).trans (le_max_left _ _)
    calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ Real.sqrt (max c 0) := Real.sqrt_le_sqrt hx'

/-- The critical AHO is globally asymptotically stable (cubic damping). -/
@[powerlib_domain] theorem critical_mem_den_globallyAsymptoticallyStable :
    connection% (critical ∈ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact family_isAutonomous.mem_den_flow.mpr
    (Flow.globallyAsymptoticallyStable_of_strictLyapunov two_pos critical.contDiff_realField
      critical_strictLyapunov)

private theorem critical_not_decaying : ¬ Meets critical .decaying := by
  change ¬ critical.c < 0
  rw [critical_c]
  exact lt_irrefl 0

/-- The global asymptotic translation is sound but not exact: the critical AHO is globally
asymptotically stable without decay at the origin (`c = 0`). -/
@[powerlib_domain] theorem not_exact_globallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := critical_mem_den_globallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  exact critical_not_decaying (hmem .decaying (by simp [family, translate]))

/-- The local asymptotic translation is sound but not exact (the same witness): local asymptotic
stability is not decided by the linearization. -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := critical_mem_den_globallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  have hmem' : critical ∈ family.den (.flow .locallyAsymptoticallyStable) :=
    family_isAutonomous.mem_den_flow.mpr
      (Flow.GloballyAsymptoticallyStable.localAsymptoticStable
        (family_isAutonomous.mem_den_flow.mp hmem))
  rw [← h, TMIO.mem_realize] at hmem'
  exact critical_not_decaying (hmem' .decaying (by simp [family, translate]))

/-- The Lyapunov translation is sound but not exact (the same witness). -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := critical_mem_den_globallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  have hmem' : critical ∈ family.den (.flow .lyapunovStable) :=
    family_isAutonomous.mem_den_flow.mpr (family_isAutonomous.mem_den_flow.mp hmem).2.2.1
  rw [← h, TMIO.mem_realize] at hmem'
  exact critical_not_decaying (hmem' .decaying (by simp [family, translate]))

/-! ### The local asymptotic and Lyapunov denotations -/

/-- With `c = 0` and `κ_v > 0`, `|v|²` is a strict global Lyapunov function (derivative
`−2 κ_v |v|⁴`). -/
private theorem strictLyapunov_of_critical {a : AHO} (hc : a.c = 0) (hκ : 0 < a.κv) :
    IsStrictLyapunovFunction a.realField energy 0 where
  hcont := by unfold energy; fun_prop
  hV_c1 := by unfold energy; fun_prop
  hzero := by simp [energy]
  hpos x hx := energy_pos hx
  hequil := a.realField_zero
  hLie_neg x hx := by
    rw [energy_lie, hc]
    have h := energy_pos hx
    nlinarith [mul_pos hκ (mul_pos h h)]
  hbounded_sublevel c := by
    refine (isCompact_closedBall (0 : State 2) (Real.sqrt (max c 0))).of_isClosed_subset
      (isClosed_le (by unfold energy; fun_prop) continuous_const) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have hx' : ‖x‖ ^ 2 ≤ max c 0 := by
      have := energy_eq x
      rw [sub_zero] at this
      rw [← this]
      exact (Set.mem_ofPred_eq ▸ hx).trans (le_max_left _ _)
    calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ Real.sqrt (max c 0) := Real.sqrt_le_sqrt hx'

private theorem energy_differentiable : Differentiable ℝ energy := fun x =>
  (hasFDerivAt_energy x).differentiableAt

private theorem seed (ε : ℝ) (hε : 0 < ε) :
    ‖Synchronous.mkState (ε / 2) 0 - 0‖ < ε ∧ 0 < energy (Synchronous.mkState (ε / 2) 0) := by
  have hne : Synchronous.mkState (ε / 2) 0 ≠ 0 := by
    intro h
    have := congrArg (fun y : State 2 => y 0) h
    simp at this
    linarith
  refine ⟨?_, energy_pos hne⟩
  rw [sub_zero]
  refine (Synchronous.norm_state_le _).trans_lt ?_
  simp only [Synchronous.mkState_zero, Synchronous.mkState_one, abs_zero, add_zero]
  rw [abs_of_pos (by linarith)]
  linarith

/-- The origin is locally asymptotically stable exactly when it decays (`c < 0`) or, at the
critical gain `c = 0`, the amplitude is cubically damped (`κ_v > 0`, `ṙ = −κ_v r³`): the
linearization decides `c ≠ 0`, and at `c = 0` the energy `|v|²` obeys `d|v|²/dt = −2 κ_v |v|⁴`
(strict Lyapunov function for `κ_v > 0`; nondecreasing for `κ_v ≤ 0`, so no nearby solution
converges, `Dynamics.not_localAsymptoticStable_of_lie_nonpos`). -/
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (a : AHO) :
    connection% (a ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      a ∈ {a : AHO | a.c < 0 ∨ (a.c = 0 ∧ 0 < a.κv)}) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow, Set.mem_ofPred_eq]
  change LocalAsymptoticStable _ _ ↔ _
  constructor
  · intro h
    rcases lt_trichotomy a.c 0 with hc | hc | hc
    · exact Or.inl hc
    · refine Or.inr ⟨hc, ?_⟩
      by_contra hκ
      push Not at hκ
      refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (V := fun x => -energy x)
        (ρ := 1) a.contDiff_realField energy_differentiable.neg one_pos (fun x _ => ?_)
        (fun ε hε => ⟨Synchronous.mkState (ε / 2) 0, (seed ε hε).1, ?_⟩) h
      · rw [fderiv_fun_neg, _root_.neg_apply, energy_lie, hc]
        nlinarith [mul_nonneg (neg_nonneg.mpr hκ) (sq_nonneg (energy x))]
      · simp [energy]
        positivity
    · exact absurd h.1 (unstable_of hc)
  · rintro (hc | ⟨hc, hκ⟩)
    · exact Flow.locallyExponentiallyStable_localAsymptoticStable (les hc)
    · exact (Flow.globallyAsymptoticallyStable_of_strictLyapunov two_pos a.contDiff_realField
        (strictLyapunov_of_critical hc hκ)).localAsymptoticStable

/-- The origin is Lyapunov stable exactly when it decays (`c < 0`) or `c = 0` with `κ_v ≥ 0`
(the energy `|v|²` does not increase); at `c = 0` with `κ_v < 0` the energy grows at the rate
`2 |κ_v| |v|⁴` (Chetaev's theorem, `Dynamics.unstable_of_chetaev`). -/
@[powerlib_domain] theorem mem_den_lyapunovStable_iff (a : AHO) :
    connection% (a ∈ family.den (.flow .lyapunovStable) ↔
      a ∈ {a : AHO | a.c < 0 ∨ (a.c = 0 ∧ 0 ≤ a.κv)}) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow, Set.mem_ofPred_eq]
  change LyapunovStable _ _ ↔ _
  constructor
  · intro h
    rcases lt_trichotomy a.c 0 with hc | hc | hc
    · exact Or.inl hc
    · refine Or.inr ⟨hc, ?_⟩
      by_contra hκ
      push Not at hκ
      refine Dynamics.unstable_of_chetaev (W := energy) (r := 1) a.contDiff_realField
        (by unfold energy; fun_prop) one_pos (fun ε hε => ⟨Synchronous.mkState (ε / 2) 0, ?_⟩)
        (fun x _ hx => ?_) h
      · exact seed ε hε
      · rw [energy_lie, hc]
        nlinarith [mul_pos (neg_pos.mpr hκ) (mul_pos hx hx)]
    · exact absurd h (unstable_of hc)
  · rintro (hc | ⟨hc, hκ⟩)
    · exact (les hc).lyapunovStable
    · exact lyapunov_stable (V := energy) (D := Set.univ) two_pos
        ⟨isOpen_univ, Set.mem_univ _, energy_differentiable.continuous, energy_differentiable,
          by simp [energy], fun x _ hx => energy_pos hx, fun x _ => by
            rw [energy_lie, hc]
            nlinarith [mul_nonneg hκ (sq_nonneg (energy x))]⟩

/-! ## Algebra (foundation) -/

/-- Polar decomposition of the loaded AHO `v̇ = (jω_s − σ + κ_v(v*² − r²)) v − κ_i i`:
with `v = r e^{jϕ}`, `ṙ = (κ_v(v*² − r²) − σ) r − Re(κ_i i e^{−jϕ})` and
`ϕ̇ = ω_s − Im(κ_i i e^{−jϕ}) / r`. -/
@[powerlib_foundation] theorem polar_decomposition {r ϕ : ℝ → ℝ} {r' ϕ' : ℝ} {t κi : ℝ} {i : ℂ}
    (hr : HasDerivAt r r' t) (hϕ : HasDerivAt ϕ ϕ' t) (hr0 : 0 < r t)
    (hv : HasDerivAt (fun τ => (r τ : ℂ) * exp (ϕ τ * I))
      ((I * a.ωs - a.σ + (a.κv * (a.vstar ^ 2 - r t ^ 2) : ℝ)) * ((r t : ℂ) * exp (ϕ t * I))
        - (κi : ℂ) * i) t) :
    r' = (a.κv * (a.vstar ^ 2 - r t ^ 2) - a.σ) * r t - ((κi : ℂ) * i * exp (-(ϕ t * I))).re ∧
      ϕ' = a.ωs - ((κi : ℂ) * i * exp (-(ϕ t * I))).im / r t := by
  have hchain : HasDerivAt (fun τ => (r τ : ℂ) * exp (ϕ τ * I))
      ((r' : ℂ) * exp (ϕ t * I) + (r t : ℂ) * (exp (ϕ t * I) * ((ϕ' : ℂ) * I))) t := by
    have h1 := hr.ofReal_comp
    have h2 := (hϕ.ofReal_comp.mul_const I).cexp
    exact h1.mul h2
  have heq := hv.unique hchain
  have hEE : exp (ϕ t * I) * exp (-(ϕ t * I)) = 1 := by rw [← Complex.exp_add]; simp
  have key : (r' : ℂ) + (r t : ℂ) * (ϕ' : ℂ) * I =
      (I * a.ωs - a.σ + (a.κv * (a.vstar ^ 2 - r t ^ 2) : ℝ)) * (r t : ℂ) -
        (κi : ℂ) * i * exp (-(ϕ t * I)) := by
    have := congrArg (· * exp (-(ϕ t * I))) heq
    calc (r' : ℂ) + (r t : ℂ) * (ϕ' : ℂ) * I =
        ((r' : ℂ) * exp (ϕ t * I) + (r t : ℂ) * (exp (ϕ t * I) * ((ϕ' : ℂ) * I))) *
          exp (-(ϕ t * I)) := by
          rw [show ((r' : ℂ) * exp (ϕ t * I) + (r t : ℂ) * (exp (ϕ t * I) * ((ϕ' : ℂ) * I))) *
              exp (-(ϕ t * I)) = ((r' : ℂ) + (r t : ℂ) * (ϕ' : ℂ) * I) *
                (exp (ϕ t * I) * exp (-(ϕ t * I))) by ring, hEE, mul_one]
      _ = _ := by
          rw [← this]
          rw [show ((I * a.ωs - a.σ + (a.κv * (a.vstar ^ 2 - r t ^ 2) : ℝ)) *
              ((r t : ℂ) * exp (ϕ t * I)) - (κi : ℂ) * i) * exp (-(ϕ t * I)) =
              (I * a.ωs - a.σ + (a.κv * (a.vstar ^ 2 - r t ^ 2) : ℝ)) * (r t : ℂ) *
                (exp (ϕ t * I) * exp (-(ϕ t * I))) - (κi : ℂ) * i * exp (-(ϕ t * I)) by ring,
            hEE, mul_one]
  set w := (κi : ℂ) * i * exp (-(ϕ t * I)) with hw
  have hre := congrArg Complex.re key
  have him := congrArg Complex.im key
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre him
  constructor
  · linarith
  · field_simp
    linarith

/-- dVOC complex frequency: if `v̇ = jω_s v + η(e_θ + α(v*² − |v|²) v)` and `v ≠ 0`, then
`v̇ / v = jω_s + η e_θ / v + η α (v*² − |v|²)`. -/
@[powerlib_foundation] theorem dvoc_complexFrequency {ωs η α vstar : ℝ} {v eθ vdot : ℂ}
    (hv : v ≠ 0)
    (hdyn : vdot = I * ωs * v + η * (eθ + (α * (vstar ^ 2 - normSq v) : ℝ) * v)) :
    vdot / v = I * ωs + η * eθ / v + η * α * ((vstar ^ 2 - normSq v : ℝ) : ℂ) := by
  rw [hdyn]
  field_simp
  push_cast
  ring

end AHO
end powerlib.GFM
