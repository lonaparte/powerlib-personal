import theorem.PhasePlane.Planar
import theorem.NormalForm.Hopf
import theorem.Family.Basic
import theorem.TMIO.ClaimElab
import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.Instability
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import theorem.Dynamics.Calculus
import theorem.Spectral.Global

/-! # Andronov–Hopf virtual oscillator (AHO-VOC) at no load

Model boundary.
* Stationary `αβ` frame; the oscillator state `v = v_α + j v_β ∈ ℂ` (i.e. the state pair
  `(v_α, v_β)`, identified with `ℂ` as a real two-dimensional space); continuous time.
* No-load AHO dynamics (`i = 0`):
  `v̇ = (j ω_s − σ + κ_v (v*² − |v|²)) v`, i.e.
  `v̇_α = −σ v_α − ω_s v_β + κ_v (v*² − |v|²) v_α`,
  `v̇_β = ω_s v_α − σ v_β + κ_v (v*² − |v|²) v_β` (`aho_re`, `aho_im`).
* Parameters `κ_v > 0`, `σ < κ_v v*²`; write `c = κ_v v*² − σ > 0` and `r* = √(v*² − σ/κ_v)`
  (`rstar_eq`; `rstar` is the radius `NormalForm.Hopf.radius` of `AHO.toHopf`).
* Excluded: output current coupling `−κ_i i` (zero load), filters, inner loops, PWM, delays,
  multi-converter networks (no dVOC network result is claimed).

Source: work-sync `theory/T-voc-dvoc.md` §1.2, §1.3, §1.8; `theory/T-gfm-control.md` §1.5.

Results.
Trajectory level, every solution on `[0, ∞)` with `v(0) ≠ 0`:
* `r*` is the unique positive zero of the radial field `(κ_v (v*² − r²) − σ) r`.
* `|v|²` solves the logistic equation `y' = 2 (c − κ_v y) y` and equals
  `1 / (κ_v/c + (1/|v(0)|² − κ_v/c) e^{−2ct})`; in particular `v(t) ≠ 0` for all `t ≥ 0`.
* `|v(t)| → r*`.
  The amplitude results and the invariant circle below are the scalar logistic equation and the
  supercritical Hopf normal form: in the coordinates `(v_α, v_β)` a solution solves
  `NormalForm.Hopf.field a.toHopf`, so `NormalForm.Logistic.pos`, `reciprocal_formula`,
  `NormalForm.Hopf.supercritical_norm_tendsto` and `circle_invariant` apply.
* Phase: `v(t) = (|v(t)| / |v(0)|) e^{j ω_s t} v(0)` — the phase rotates uniformly at `ω_s`.
* The circle `|v| = r*` is invariant and carries exactly the solutions `r* e^{j(ω_s t + φ₀)}`.
* Algebra: polar decomposition of the loaded AHO (domain) and the dVOC complex frequency
  (foundation).

Family and connection conclusions.
* `AHO.family`: a complete system is the AHO parameter set itself, read as the no-load field in
  the real coordinates `(v_α, v_β) : Dynamics.State 2` (`AHO.realField`, identified with the
  complex field through `PhasePlane.complexIso` by `realField_eq`); the equilibrium of the
  sentences is the origin `v = 0`. The real field is, by definition, the Hopf normal form
  `NormalForm.Hopf.field` of the parameters `AHO.toHopf = (μ, ω₀, l₁, κ) = (c, ω_s, −κ_v, 0)`
  (`theorem/NormalForm/Hopf.lean`): its smoothness, its equilibrium at the origin, its Jacobian
  there and the local exponential stability (`c < 0`) and instability (`c > 0`) of the origin are
  the normal form's (`NormalForm.Hopf.field_contDiff`, `field_zero`, `fderiv_field_zero`,
  `origin_stable`, `origin_unstable`).
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
* Connection conclusion for the module's own regime: under the standing assumptions the
  origin is unstable (`Admissible.mem_den_unstable`): solutions leave the origin, towards the limit
  cycle of the trajectory-level results.
* The limit-cycle results above (`normSq_solution_pos`, `normSq_formula`, `norm_tendsto_rstar`,
  `phase_rotation`, `norm_eq_rstar_of_start`, `limitCycle_isSolution`) are trajectory level and
  outside the sentence language (Rules §3a): they are private implementation evidence (the
  parameter type `AHO` carries a family, so its public behavioural statements must be connection
  statements).  `radial_zero_iff`
  is static evidence on the model; the pointwise chain rules `hasDerivWithinAt_normSq`,
  `hasDerivWithinAt_norm` stay public (static domain identities).

Corrections.
* T-voc-dvoc §1.8 writes the dVOC complex frequency as
  `η̄ = jω_s + (η/v)(K e_θ / v + α(v*² − |v|²))`; from `v̇ = jω_s v + η(e_θ + α(v*² − |v|²) v)`
  the correct expression is `v̇/v = jω_s + η e_θ / v + η α (v*² − |v|²)` (`dvoc_complexFrequency`).
* The dVOC control law of §1.3 differs from Colombino et al. 2019; no dVOC multi-converter
  statement is formalized.
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

/-- The AHO as a parameterization of the Hopf normal form (`theorem/NormalForm/Hopf.lean`):
`μ = c`, `ω₀ = ω_s`, cubic coefficient `l₁ + iκ = −κ_v`. -/
def toHopf : NormalForm.Hopf.Params := ⟨a.c, a.ωs, -a.κv, 0⟩

/-- Limit-cycle radius `r* = √(c/κ_v)`, the radius `NormalForm.Hopf.radius` of `toHopf`; for
`κ_v ≠ 0` it is `√(v*² − σ/κ_v)` (`rstar_eq`). -/
abbrev rstar : ℝ := NormalForm.Hopf.radius a.toHopf

@[tmio M, powerlib_domain] theorem rstar_eq (hk : a.κv ≠ 0) :
    a.rstar = Real.sqrt (a.vstar ^ 2 - a.σ / a.κv) := by
  simp only [rstar, NormalForm.Hopf.radius, toHopf, c, neg_div_neg_eq]
  rw [sub_div, mul_div_cancel_left₀ _ hk]

/-- Real gain `κ_v (v*² − |v|²) − σ = c − κ_v |v|²`. -/
def gain (v : ℂ) : ℝ := a.c - a.κv * normSq v

/-- No-load AHO field `v̇ = (j ω_s + c − κ_v |v|²) v`. -/
def field (v : ℂ) : ℂ := (I * a.ωs + (a.gain v : ℂ)) * v

@[tmio M, powerlib_domain] theorem aho_re (v : ℂ) :
    (a.field v).re = -a.σ * v.re - a.ωs * v.im + a.κv * (a.vstar ^ 2 - normSq v) * v.re := by
  simp only [field, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [gain, c]; ring

@[tmio M, powerlib_domain] theorem aho_im (v : ℂ) :
    (a.field v).im = a.ωs * v.re - a.σ * v.im + a.κv * (a.vstar ^ 2 - normSq v) * v.im := by
  simp only [field, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [gain, c]; ring

/-- Standing assumptions `κ_v > 0`, `σ < κ_v v*²`. -/
structure Admissible : Prop where
  κv : 0 < a.κv
  gap : a.σ < a.κv * a.vstar ^ 2

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

variable {a}

@[tmio M, powerlib_domain] theorem Admissible.c_pos (h : a.Admissible) :
    connection% (a ∈ TMIO.realize Meets {.growing}) := by
  simp only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, Meets, c]
  linarith [h.gap]

@[tmio M, powerlib_domain] theorem Admissible.rstar_sq (h : a.Admissible) :
    a.rstar ^ 2 = a.c / a.κv := by
  have hc : 0 < a.c / a.κv := div_pos (by simp only [c]; linarith [h.gap]) h.κv
  rw [rstar, NormalForm.Hopf.radius_sq _ (by simpa [toHopf, neg_div_neg_eq] using hc.le)]
  exact neg_div_neg_eq _ _

@[tmio M, powerlib_domain] theorem Admissible.rstar_pos (h : a.Admissible) : 0 < a.rstar :=
  Real.sqrt_pos.mpr (by
    simpa [toHopf, neg_div_neg_eq] using div_pos (by simp only [c]; linarith [h.gap]) h.κv)

/-- `r*` is the unique positive zero of the radial field.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem radial_zero_iff (h : a.Admissible) {r : ℝ} (hr : 0 < r) :
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

/-! ## Real coordinates: the Hopf normal form -/

/-- The no-load AHO field in the real coordinates `(v_α, v_β)`: the Hopf normal form of `toHopf`,
`(c − κ_v (v_α² + v_β²)) (v_α, v_β) + ω_s (−v_β, v_α)`. Its smoothness, equilibrium at the origin
and linearization there are those of the normal form (`NormalForm.Hopf.field_contDiff`,
`field_zero`, `fderiv_field_zero`: Jacobian `linPart = [[c, −ω_s], [ω_s, c]]`). -/
def realField (x : State 2) : State 2 := NormalForm.Hopf.field a.toHopf x

@[tmio M, powerlib_domain] private theorem realField_apply (x : State 2) :
    a.realField x = PhasePlane.mk ((a.c - a.κv * (x 0 ^ 2 + x 1 ^ 2)) * x 0 - a.ωs * x 1)
      (a.ωs * x 0 + (a.c - a.κv * (x 0 ^ 2 + x 1 ^ 2)) * x 1) := by
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩ <;>
    simp only [realField, NormalForm.Hopf.field_apply_zero, NormalForm.Hopf.field_apply_one,
      PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, toHopf] <;> ring

/-- The real field is the complex field `v̇ = (j ω_s + c − κ_v |v|²) v` in the coordinates
`v = v_α + j v_β` (`PhasePlane.complexIso`). -/
@[tmio M, powerlib_domain] theorem realField_eq (z : ℂ) :
    a.realField (PhasePlane.complexIso z) = PhasePlane.complexIso (a.field z) := by
  rw [realField_apply, PhasePlane.complexIso_apply (a.field z)]
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp only [PhasePlane.mk_apply_zero, PhasePlane.complexIso_apply_zero,
      PhasePlane.complexIso_apply_one, aho_re, Complex.normSq_apply, c]
    ring
  · simp only [PhasePlane.mk_apply_one, PhasePlane.complexIso_apply_zero,
      PhasePlane.complexIso_apply_one, aho_im, Complex.normSq_apply, c]
    ring

/-! ## Trajectories: the logistic amplitude and the limit cycle -/

/-- `d|v|²/dt = 2 (c − κ_v |v|²) |v|²` along the field. -/
@[tmio M, powerlib_domain] theorem hasDerivWithinAt_normSq {φ : ℝ → ℂ} {s : Set ℝ} {t : ℝ}
    (hφ : HasDerivWithinAt φ (a.field (φ t)) s t) :
    HasDerivWithinAt (fun τ => normSq (φ τ))
      (2 * a.gain (φ t) * normSq (φ t)) s t := by
  convert hφ.norm_sq using 1
  · funext τ; exact Complex.normSq_eq_norm_sq _
  · rw [Complex.inner, field, mul_assoc (I * _ + _), Complex.mul_conj]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

/-- Along a solution, `|v|²` solves the logistic equation `ρ̇ = 2cρ − 2κ_v ρ²`
(`NormalForm.Hopf.normSq_isIntegralCurveOn`). -/
@[tmio M, powerlib_domain] private theorem normSq_logistic {φ : ℝ → ℂ} {s : Set ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) s) :
    IsIntegralCurveOn (fun t => normSq (φ t))
      (fun _ r => NormalForm.Logistic.field a.c (-a.κv) r) s := by
  simpa only [LinearIsometryEquiv.norm_map, ← Complex.normSq_eq_norm_sq, toHopf] using
    NormalForm.Hopf.normSq_isIntegralCurveOn a.toHopf
      ((PhasePlane.isIntegralCurveOn_complexIso_iff a.realField_eq φ s).2 hφ)

/-- Solutions starting away from the origin never reach it (`NormalForm.Logistic.pos`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem normSq_solution_pos {φ : ℝ → ℂ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) (h0 : φ 0 ≠ 0) :
    ∀ t ∈ Ici (0 : ℝ), 0 < normSq (φ t) := fun t ht =>
  NormalForm.Logistic.pos (a.normSq_logistic (hφ.mono Icc_subset_Ici_self)) (normSq_pos.mpr h0)
    t ⟨ht, le_rfl⟩

/-- For solutions starting away from the origin, `|v|²` is given by the explicit logistic
formula `1/|v|² = κ_v/c + (1/|v(0)|² − κ_v/c) e^{−2ct}` (`NormalForm.Logistic.reciprocal_formula`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem normSq_formula (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) (h0 : φ 0 ≠ 0) :
    ∀ t ∈ Ici (0 : ℝ), 1 / normSq (φ t) =
      a.κv / a.c + (1 / normSq (φ 0) - a.κv / a.c) * Real.exp (-(2 * a.c * t)) := by
  intro t ht
  have hc : a.c ≠ 0 := (sub_pos.mpr h.gap).ne'
  have hf := NormalForm.Logistic.reciprocal_formula hc
    (a.normSq_logistic (hφ.mono Icc_subset_Ici_self)) (normSq_pos.mpr h0) t ⟨ht, le_rfl⟩
  rw [sub_zero, neg_mul, neg_mul, neg_div] at hf
  linear_combination hf

/-- Every solution with `v(0) ≠ 0` converges in amplitude to the limit-cycle radius
(`NormalForm.Hopf.supercritical_norm_tendsto`; the normal form's radius is `r*`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem norm_tendsto_rstar (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) (h0 : φ 0 ≠ 0) :
    Tendsto (fun t => ‖φ t‖) atTop (𝓝 a.rstar) := by
  simpa only [LinearIsometryEquiv.norm_map] using NormalForm.Hopf.supercritical_norm_tendsto
    a.toHopf (sub_pos.mpr h.gap) (neg_neg_of_pos h.κv)
    ((PhasePlane.isIntegralCurveOn_complexIso_iff a.realField_eq φ _).2 hφ)
    (PhasePlane.complexIso.map_eq_zero_iff.not.2 h0)

/-- `d‖v‖/dt = gain · ‖v‖` along the field (away from the origin). -/
@[tmio M, powerlib_domain] theorem hasDerivWithinAt_norm {φ : ℝ → ℂ} {s : Set ℝ} {t : ℝ}
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
@[tmio TM, powerlib_domain] private theorem phase_rotation {φ : ℝ → ℂ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0)) (h0 : φ 0 ≠ 0) :
    ∀ t ∈ Ici (0 : ℝ), φ t = ((‖φ t‖ / ‖φ 0‖ : ℝ) : ℂ) * exp (I * a.ωs * t) * φ 0 := by
  have hpos := a.normSq_solution_pos hφ h0
  have hne : ∀ t ∈ Ici (0 : ℝ), φ t ≠ 0 := fun t ht =>
    normSq_pos.mp (hpos t ht)
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
      exact (hcφ.mul
        (by fun_prop : Continuous fun τ : ℝ => exp (-(I * a.ωs * τ))).continuousWithinAt).mul hcn
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

/-- The circle `|v| = r*` is invariant: a solution starting on it stays on it
(`NormalForm.Hopf.circle_invariant`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem norm_eq_rstar_of_start (h : a.Admissible) {φ : ℝ → ℂ}
    (hφ : IsIntegralCurveOn φ (fun _ v => a.field v) (Ici 0))
    (h0 : ‖φ 0‖ = a.rstar) : ∀ t ∈ Ici (0 : ℝ), ‖φ t‖ = a.rstar := by
  have hc : 0 < a.c := sub_pos.mpr h.gap
  have hR : -a.toHopf.μ / a.toHopf.l₁ = a.rstar ^ 2 := by
    rw [h.rstar_sq]; exact neg_div_neg_eq _ _
  intro t ht
  have key := NormalForm.Hopf.circle_invariant a.toHopf hc.ne' (neg_ne_zero.mpr h.κv.ne')
    (hR ▸ pow_pos h.rstar_pos 2)
    (((PhasePlane.isIntegralCurveOn_complexIso_iff a.realField_eq φ _).2 hφ).mono
      Icc_subset_Ici_self)
    (by rw [LinearIsometryEquiv.norm_map, h0, hR]) t ⟨ht, le_rfl⟩
  rw [LinearIsometryEquiv.norm_map, hR] at key
  exact (pow_left_inj₀ (norm_nonneg _) h.rstar_pos.le two_ne_zero).mp key

/-- The limit-cycle solutions `r* e^{j(ω_s t + φ₀)}` solve the AHO.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem limitCycle_isSolution (h : a.Admissible) (φ₀ : ℝ) :
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
  | .envelope _ => ∅

/-- The no-load AHO family: each parameter set read as its real field about the origin. -/
def family : Family AHO Requirement 2 0 :=
  ⟨fun a => Port.System.autonomous a.realField, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous AHO.realField :=
  fun _ => rfl

variable {a}

/-! ### Implementation evidence (private) -/

/-- The energy `|v|² = v_α² + v_β²`. -/
private def energy (x : State 2) : ℝ := x 0 ^ 2 + x 1 ^ 2

@[tmio M, powerlib_domain] private theorem hasFDerivAt_energy (x : State 2) :
    HasFDerivAt energy
      ((2 * x 0) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ) +
        (2 * x 1) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ)) x := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h := (h0.pow 2).add (h1.pow 2)
  convert h using 1
  · funext y; simp [energy]
  apply ContinuousLinearMap.ext; intro v
  simp

@[tmio M, powerlib_domain] private theorem energy_eq (x : State 2) : energy x = ‖x - 0‖ ^ 2 := by
  rw [sub_zero, PhasePlane.norm_sq_eq, energy]

@[tmio M, powerlib_domain] private theorem dissipation (hκ : 0 ≤ a.κv) (x : State 2) :
    fderiv ℝ energy x (a.realField x) ≤ -(-2 * a.c) * energy x := by
  rw [(hasFDerivAt_energy x).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, PiLp.proj_apply,
    smul_eq_mul, realField_apply, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, energy]
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
  equilibrium := NormalForm.Hopf.field_zero a.toHopf
  lower_bound x := by rw [energy_eq, one_mul]
  upper_bound x := by rw [energy_eq, one_mul]
  dissipation := dissipation hκ

/-! ### Members -/

/-- Decay at the origin with `κ_v ≥ 0` makes the origin globally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem mem_den_globallyExponentiallyStable (a : AHO) (hc : a.c < 0)
    (hκ : 0 ≤ a.κv) : connection% (a ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Flow.GloballyExponentiallyStable a.realField 0
  exact (quadraticDecay hc hκ).globallyExponentiallyStable
    (NormalForm.Hopf.field_contDiff a.toHopf)

/-- Decay at the origin (`κ_v v*² < σ`) makes the origin locally exponentially stable, for every
sign of `κ_v`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (a : AHO) (hc : a.c < 0) :
    connection% (a ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  exact NormalForm.Hopf.origin_stable a.toHopf hc

/-- Growth at the origin (`σ < κ_v v*²`) makes the origin unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (a : AHO) (hc : 0 < a.c) :
    connection% (a ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  exact NormalForm.Hopf.origin_unstable a.toHopf hc

/-- With `κ_v ≥ 0` every solution segment decays at every rate `r ≤ −c` (a growth bound when
`c > 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_decay (a : AHO) (hκ : 0 ≤ a.κv) {r : ℝ}
    (hr : r + a.c ≤ 0) :
    connection% (a ∈ family.den (.flow (.decay r))) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Flow.Decay a.realField 0 r
  have h : Flow.Decay a.realField 0 (-2 * a.c / 2) :=
    ⟨_, fun _ _ _ hφ _ ht => Flow.norm_bound_of_dissipation (lower := 1) (upper := 1)
      (by unfold energy; fun_prop) one_pos one_pos (fun x => by rw [energy_eq, one_mul])
      (fun x => by rw [energy_eq, one_mul]) (dissipation hκ) hφ ht⟩
  exact h.mono (by linarith)

/-- Under the standing assumptions `κ_v > 0`, `σ < κ_v v*²` of the limit-cycle results, the
origin of the no-load AHO is unstable. -/
@[tmio TM, powerlib_domain] theorem Admissible.mem_den_unstable (h : a.Admissible) :
    connection% (a ∈ family.den (.flow .unstable)) :=
  AHO.mem_den_unstable a (by
    simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, Meets]
      using h.c_pos)

/-! ### Soundness of the translation -/

/-- The whole requirement language is inconsistent: the origin cannot both grow and decay. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun a h => ?_
  have h1 : 0 < a.c := h .growing
  have h2 : a.c < 0 := h .decaying
  linarith

/-- Every translation of the no-load AHO family is sound: linearization at the origin for the
local sentences and instability, the decaying energy `|v|²` for the global sentences, sampled
contraction and decay rates, and passivity without requirement (the global table,
`Spectral.chain_le_semantics_of_globalTable`). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_globalTable (F := family) (Rs := {.decaying})
    (Rg := {.decaying, .stiff}) (Ru := {.growing}) (Rc := Set.univ) (Rp := ∅)
    (Rd := fun r => {.stiff, .decayRate r}) (fun s => ?_) (fun a ha => ?_) (fun a ha => ?_)
    (fun r a ha => ?_) (fun a ha => ?_) (Spectral.realize_univ_subset_of_eq_empty realize_univ _)
    (fun a _ => by rw [family_isAutonomous.den_passive]; trivial) family_isAutonomous.den_envelope
  · rcases s with P | _ | _
    · cases P <;> rfl
    · rfl
    · rfl
  all_goals rw [(connection_proof% TMIO.mem_realize)] at ha; rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  · exact family_isAutonomous.mem_den_flow.mp
      (mem_den_locallyExponentiallyStable a (ha .decaying rfl))
  · exact family_isAutonomous.mem_den_flow.mp
      (mem_den_globallyExponentiallyStable a (ha .decaying (by simp)) (ha .stiff (by simp)))
  · exact family_isAutonomous.mem_den_flow.mp
      (mem_den_decay a (ha .stiff (by simp)) (ha (.decayRate r) (by simp)))
  · exact family_isAutonomous.mem_den_flow.mp (mem_den_unstable a (ha .growing rfl))

/-- The local exponential translation is exact: the origin of the no-load AHO is locally
exponentially stable exactly when it decays, `c = κ_v v*² − σ < 0`. Converse linearization: local
exponential stability forces a Hurwitz Jacobian `[[c, −ω_s], [ω_s, c]]` (trace `2c`). -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  ext a
  rw [(connection_proof% TMIO.mem_realize), (connection_proof% family_isAutonomous.mem_den_flow)]
  change _ ↔ LocallyExponentiallyStable _ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_of_eq _
    (show ContDiff ℝ 1 a.realField from NormalForm.Hopf.field_contDiff a.toHopf)
    (show a.realField 0 = 0 from NormalForm.Hopf.field_zero a.toHopf)
    (show fderiv ℝ a.realField 0 = _ from NormalForm.Hopf.fderiv_field_zero a.toHopf),
    NormalForm.Hopf.linPart, Criteria.isHurwitz_fin_two_of_iff]
  simp only [family, translate, Set.mem_singleton_iff, forall_eq, Meets, toHopf]
  constructor
  · intro hc
    exact ⟨by linarith, by nlinarith [sq_nonneg a.ωs, sq_pos_of_neg hc]⟩
  · rintro ⟨h, -⟩
    linarith

/-! ### Boundary witness: cubic damping at `c = 0` -/

@[tmio M, powerlib_domain] private theorem energy_lie (a : AHO) (x : State 2) :
    fderiv ℝ energy x (a.realField x) = 2 * a.c * energy x - 2 * a.κv * energy x ^ 2 := by
  rw [(hasFDerivAt_energy x).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, PiLp.proj_apply,
    smul_eq_mul, realField_apply, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, energy]
  ring

@[tmio M, powerlib_domain] private theorem energy_pos {x : State 2}
    (hx : x ≠ 0) : 0 < energy x := by
  rw [energy_eq, sub_zero]
  have : 0 < ‖x‖ := norm_pos_iff.mpr hx
  positivity

/-- The critical AHO `ω_s = 0`, `σ = κ_v = v* = 1`: the linear growth rate vanishes, `c = 0`,
and the amplitude obeys the cubic damping `ṙ = −r³`. -/
def critical : AHO := ⟨0, 1, 1, 1⟩

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem critical_c : critical.c = 0 := by
  simp [critical, AHO.c]

/-- With `c = 0` and `κ_v > 0` the field points inward, `⟪v, v̇⟫ = −κ_v |v|⁴ < 0` for `v ≠ 0`, so
`|v|²` is a strict global Lyapunov function (`Flow.globallyAsymptoticallyStable_of_inner_neg`). -/
@[tmio M, powerlib_domain] private theorem inner_neg_of_critical {a : AHO} (hc : a.c = 0)
    (hκ : 0 < a.κv) (x : State 2) (hx : x ≠ 0) : inner ℝ x (a.realField x) < 0 := by
  have e : inner ℝ x (a.realField x) = -(a.κv * energy x ^ 2) := by
    rw [realField_apply, hc]
    simp [PiLp.inner_apply, Fin.sum_univ_two, energy]
    ring
  rw [e]
  linarith [mul_pos hκ (pow_pos (energy_pos hx) 2)]

/-- The critical AHO is globally asymptotically stable (cubic damping). -/
@[tmio TM, powerlib_domain] theorem critical_mem_den_globallyAsymptoticallyStable :
    connection% (critical ∈ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact family_isAutonomous.mem_den_flow.mpr
    (Flow.globallyAsymptoticallyStable_of_inner_neg two_pos
      (NormalForm.Hopf.field_contDiff critical.toHopf) (NormalForm.Hopf.field_zero critical.toHopf)
      (inner_neg_of_critical critical_c (show (0 : ℝ) < critical.κv from one_pos)))

@[tmio M, powerlib_domain] private theorem critical_not_decaying : connection% (critical ∉ TMIO.realize Meets {.decaying}) := by
  unfold TMIO.Statement
  simp only [TMIO.mem_realize, Set.mem_singleton_iff, forall_eq]
  change ¬ critical.c < 0
  rw [critical_c]
  exact lt_irrefl 0

/-- The global asymptotic translation is sound but not exact: the critical AHO is globally
asymptotically stable without decay at the origin (`c = 0`). -/
@[tmio TM, powerlib_domain] theorem not_exact_globallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_witness critical_mem_den_globallyAsymptoticallyStable
    (q := .decaying) (by simp [family, translate]) (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family] using critical_not_decaying)

/-- The local asymptotic translation is sound but not exact (the same witness): local asymptotic
stability is not decided by the linearization. -/
@[tmio TM, powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hmem := critical_mem_den_globallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  exact Spectral.not_exact_of_witness (family_isAutonomous.mem_den_flow.mpr
    (Flow.GloballyAsymptoticallyStable.localAsymptoticStable
      (family_isAutonomous.mem_den_flow.mp hmem))) (q := .decaying)
    (by simp [family, translate]) (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family] using critical_not_decaying)

/-- The Lyapunov translation is sound but not exact (the same witness). -/
@[tmio TM, powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have hmem := critical_mem_den_globallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  exact Spectral.not_exact_of_witness (family_isAutonomous.mem_den_flow.mpr
    (family_isAutonomous.mem_den_flow.mp hmem).2.2.1) (q := .decaying)
    (by simp [family, translate]) (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family] using critical_not_decaying)

/-! ### The local asymptotic and Lyapunov denotations -/

@[tmio M, powerlib_domain] private theorem energy_differentiable :
    Differentiable ℝ energy := fun x =>
  (hasFDerivAt_energy x).differentiableAt

@[tmio M, powerlib_domain] private theorem seed (ε : ℝ) (hε : 0 < ε) :
    ‖PhasePlane.mk (ε / 2) 0 - 0‖ < ε ∧ 0 < energy (PhasePlane.mk (ε / 2) 0) := by
  have hne : PhasePlane.mk (ε / 2) 0 ≠ 0 := by
    intro h
    have := congrArg (fun y : State 2 => y 0) h
    simp at this
    linarith
  refine ⟨?_, energy_pos hne⟩
  rw [sub_zero]
  refine ((Dynamics.norm_le_sum_abs _).trans_eq (Fin.sum_univ_two _)).trans_lt ?_
  simp only [PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, abs_zero, add_zero]
  rw [abs_of_pos (by linarith)]
  linarith

/-- The origin is locally asymptotically stable exactly when it decays (`c < 0`) or, at the
critical gain `c = 0`, the amplitude is cubically damped (`κ_v > 0`, `ṙ = −κ_v r³`): the
linearization decides `c ≠ 0`, and at `c = 0` the energy `|v|²` obeys `d|v|²/dt = −2 κ_v |v|⁴`
(strict Lyapunov function for `κ_v > 0`; nondecreasing for `κ_v ≤ 0`, so no nearby solution
converges, `Dynamics.not_localAsymptoticStable_of_lie_nonpos`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (a : AHO) :
    connection% (a ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      a ∈ {a : AHO | a.c < 0 ∨ (a.c = 0 ∧ 0 < a.κv)}) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow), Set.mem_ofPred_eq]
  change LocalAsymptoticStable _ _ ↔ _
  constructor
  · intro h
    rcases lt_trichotomy a.c 0 with hc | hc | hc
    · exact Or.inl hc
    · refine Or.inr ⟨hc, ?_⟩
      by_contra hκ
      push Not at hκ
      refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (V := fun x => -energy x)
        (ρ := 1) (show ContDiff ℝ 1 a.realField from NormalForm.Hopf.field_contDiff a.toHopf)
        energy_differentiable.neg one_pos (fun x _ => ?_)
        (fun ε hε => ⟨PhasePlane.mk (ε / 2) 0, (seed ε hε).1, ?_⟩) h
      · rw [fderiv_fun_neg, _root_.neg_apply, energy_lie, hc]
        nlinarith [mul_nonneg (neg_nonneg.mpr hκ) (sq_nonneg (energy x))]
      · simp [energy]
        positivity
    · exact absurd h.1 ((family_isAutonomous.mem_den_flow.mp (mem_den_unstable a hc)))
  · rintro (hc | ⟨hc, hκ⟩)
    · exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (family_isAutonomous.mem_den_flow.mp (mem_den_locallyExponentiallyStable a hc))
    · exact (Flow.globallyAsymptoticallyStable_of_inner_neg two_pos
        (NormalForm.Hopf.field_contDiff a.toHopf) (NormalForm.Hopf.field_zero a.toHopf)
        (inner_neg_of_critical hc hκ)).localAsymptoticStable

/-- The origin is Lyapunov stable exactly when it decays (`c < 0`) or `c = 0` with `κ_v ≥ 0`
(the energy `|v|²` does not increase); at `c = 0` with `κ_v < 0` the energy grows at the rate
`2 |κ_v| |v|⁴` (Chetaev's theorem, `Dynamics.unstable_of_chetaev`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff (a : AHO) :
    connection% (a ∈ family.den (.flow .lyapunovStable) ↔
      a ∈ {a : AHO | a.c < 0 ∨ (a.c = 0 ∧ 0 ≤ a.κv)}) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow), Set.mem_ofPred_eq]
  change LyapunovStable _ _ ↔ _
  constructor
  · intro h
    rcases lt_trichotomy a.c 0 with hc | hc | hc
    · exact Or.inl hc
    · refine Or.inr ⟨hc, ?_⟩
      by_contra hκ
      push Not at hκ
      refine Dynamics.unstable_of_chetaev (W := energy) (r := 1)
        (show ContDiff ℝ 1 a.realField from NormalForm.Hopf.field_contDiff a.toHopf)
        (by unfold energy; fun_prop) one_pos (fun ε hε => ⟨PhasePlane.mk (ε / 2) 0, ?_⟩)
        (fun x _ hx => ?_) h
      · exact seed ε hε
      · rw [energy_lie, hc]
        nlinarith [mul_pos (neg_pos.mpr hκ) (mul_pos hx hx)]
    · exact absurd h ((family_isAutonomous.mem_den_flow.mp (mem_den_unstable a hc)))
  · rintro (hc | ⟨hc, hκ⟩)
    · exact (family_isAutonomous.mem_den_flow.mp
        (mem_den_locallyExponentiallyStable a hc)).lyapunovStable
    · exact lyapunov_stable (V := energy) (D := Set.univ) two_pos
        ⟨isOpen_univ, Set.mem_univ _, energy_differentiable.continuous, energy_differentiable,
          by simp [energy], fun x _ hx => energy_pos hx, fun x _ => by
            rw [energy_lie, hc]
            nlinarith [mul_nonneg hκ (sq_nonneg (energy x))]⟩

/-! ## Algebra (AHO polar form: domain; dVOC frequency: foundation) -/

/-- Polar decomposition of the loaded AHO `v̇ = (jω_s − σ + κ_v(v*² − r²)) v − κ_i i`:
with `v = r e^{jϕ}`, `ṙ = (κ_v(v*² − r²) − σ) r − Re(κ_i i e^{−jϕ})` and
`ϕ̇ = ω_s − Im(κ_i i e^{−jϕ}) / r`. -/
@[tmio M, powerlib_domain] theorem polar_decomposition {r ϕ : ℝ → ℝ} {r' ϕ' : ℝ} {t κi : ℝ} {i : ℂ}
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
@[tmio T, powerlib_foundation] theorem dvoc_complexFrequency {ωs η α vstar : ℝ} {v eθ vdot : ℂ}
    (hv : v ≠ 0)
    (hdyn : vdot = I * ωs * v + η * (eθ + (α * (vstar ^ 2 - normSq v) : ℝ) * v)) :
    vdot / v = I * ωs + η * eθ / v + η * α * ((vstar ^ 2 - normSq v : ℝ) : ℂ) := by
  rw [hdyn]
  field_simp
  push_cast
  ring

end AHO
end powerlib.GFM
