import theorem.Synchronous.EqualArea
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

/-- `r*` is the unique positive zero of the radial field. -/
@[powerlib_domain] theorem radial_zero_iff (h : a.Admissible) {r : ℝ} (hr : 0 < r) :
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

/-- On any interval where `|v|² > 0`, `1/|v|² = κ_v/c + (1/|v(0)|² − κ_v/c) e^{−2ct}`. -/
@[powerlib_foundation] theorem inv_normSq_eq (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) {T : ℝ}
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
logistic formula. -/
@[powerlib_domain] theorem normSq_formula (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) (h0 : φ 0 ≠ 0) :
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

/-- Every solution with `v(0) ≠ 0` converges in amplitude to the limit-cycle radius. -/
@[powerlib_domain] theorem norm_tendsto_rstar (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) (h0 : φ 0 ≠ 0) :
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
`v(0) ≠ 0`. -/
@[powerlib_domain] theorem phase_rotation (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) (h0 : φ 0 ≠ 0) :
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

/-- The circle `|v| = r*` is invariant: a solution starting on it stays on it. -/
@[powerlib_domain] theorem norm_eq_rstar_of_start (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0))
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

/-- The limit-cycle solutions `r* e^{j(ω_s t + φ₀)}` solve the AHO. -/
@[powerlib_domain] theorem limitCycle_isSolution (h : a.Admissible) (φ₀ : ℝ) :
    Dynamics.IsIntegralCurveOn
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

/-! ## Algebra (foundation) -/

variable {a}

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
