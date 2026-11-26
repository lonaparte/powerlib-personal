import theorem.PhasePlane.Planar
import theorem.NormalForm.Hopf
import theorem.Family.Basic
import theorem.TMIO.ClaimElab
import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.Instability
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import theorem.Dynamics.Calculus
import theorem.Spectral.Global
import theorem.Dynamics.DiffusiveSync
import theorem.Dynamics.VariableRate
import theorem.Dynamics.CascadeNode

/-! # Andronov–Hopf virtual oscillator (AHO-VOC): no load, admittance load, oscillator networks

Model boundary.
* Stationary `αβ` frame; the oscillator state `v = v_α + j v_β ∈ ℂ` (i.e. the state pair
  `(v_α, v_β)`, identified with `ℂ` as a real two-dimensional space); continuous time.
* No-load AHO dynamics (`i = 0`):
  `v̇ = (j ω_s − σ + κ_v (v*² − |v|²)) v`, i.e.
  `v̇_α = −σ v_α − ω_s v_β + κ_v (v*² − |v|²) v_α`,
  `v̇_β = ω_s v_α − σ v_β + κ_v (v*² − |v|²) v_β` (`aho_re`, `aho_im`).
* Parameters `κ_v > 0`, `σ < κ_v v*²`; write `c = κ_v v*² − σ > 0` and `r* = √(v*² − σ/κ_v)`
  (`rstar_eq`; `rstar` is the radius `NormalForm.Hopf.radius` of `AHO.toHopf`).
* Loaded oscillator: output current `i = Y v` of a constant admittance load `Y = g + jb` through
  the gain `κ_i`, `v̇ = (j ω_s − σ + κ_v (v*² − |v|²)) v − κ_i Y v` (`loadedField`).
* Networks: `n` identical oscillators with the current coupling `−η ∑ⱼ Lₖⱼ vⱼ`, `L` a real
  matrix, `η ≥ 0` (`networkField`): the dispatchable VOC with a rotation matched to a uniform
  line angle (`R(κ) Y` real) and no power set-points, or AHOs on a network seen through a real
  Laplacian current. Two units: one line of weight `w` (`twoLine`).
* Excluded: grid connections (infinite bus), line dynamics, dVOC power set-points
  (`K(κ) ≠ 0`, the network of `theorem/GridTiedConverter/GFM/DVOCNetwork.lean`) and mismatched
  rotations, filters, inner loops, PWM, delays.

Source: work-sync `theory/T-voc-dvoc.md` §1.2, §1.3, §1.5, §1.8; `theory/T-gfm-control.md` §1.5;
D. G. Aronson, G. B. Ermentrout, N. Kopell, *Physica D* 41 (1990) 403–449 (two diffusively coupled
Stuart–Landau oscillators: in-phase, anti-phase and unequal-amplitude states).

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
* Loaded oscillator (static): `loadedField_eq` — under a constant admittance load the AHO is the
  AHO `load` with frequency `ω_s − κ_i b` and damping `σ + κ_i g` (`load_c`: growth `c − κ_i g`);
  `load_admissible_iff` (the loaded limit cycle exists iff `κ_v > 0` and `κ_i g < c`),
  `load_rstar_sq` (`r*² = (c − κ_i g)/κ_v`).
* Networks: `inner_field_sub_le` (static: for `κ_v ≥ 0` the node field is one-sided Lipschitz,
  `⟪x − y, f(x) − f(y)⟫ ≤ c ‖x − y‖²`). Trajectory level (private implementation evidence, Rules
  §3a), through the foundation law `Dynamics.DiffusiveSync.disagreement_le`: every global solution
  of a network whose real coupling contracts the disagreement at the rate `λ` (`λ₂` for a
  symmetric Laplacian) has `∑ₖ ∑ⱼ |vₖ − vⱼ|² ≤ e^{2(c − ηλ)t}` times its initial value
  (`network_disagreement_le`; exponential synchronization for `ηλ > c`); two units synchronize
  for `2ηw > c` (`two_disagreement_le`) and, with `κ_v > 0`, have the anti-phase periodic solution
  `±r e^{jω_s t}`, `r² = (c − 2ηw)/κ_v`, for `2ηw < c` (`two_antiPhase`): the threshold
  `2ηw = c` is exact except at equality.
* Two units below the threshold, the explicit reduction. Static: `networkField_twoLine`, the
  derivatives of `R = Im(v₀ v̄₁) = ⟪j v₁, v₀⟫`, `D = ‖v₀ − v₁‖²`, `U = ‖v₀ + v₁‖²`,
  `S = ‖v₀‖² + ‖v₁‖²` along the field (`two_inner_rot`: `Ṙ = λR`, `λ = 2c − κ_v S − 2ηw`;
  `two_inner_sub`, `two_inner_add`, `two_inner_self`), and the in-line relative equilibria with
  unequal amplitudes `((σ + δ) z, (σ − δ) z)`, `κ_v σ² = (c − 3ηw)/4`, `κ_v δ² = (c + ηw)/4`
  (`two_networkField_mixed`, with `field_ofReal_mul_exp`). Trajectory level (private
  implementation evidence, through `Dynamics.VariableRate`): for `κ_v ≥ 0` the in-line set
  `Im(v₀ v̄₁) = 0` is invariant and off it `D(t) |R(0)| e^{2ηwt} ≤ D(0) |R(t)|`
  (`two_sync_rate`); the amplitudes stay bounded (`two_normSq_le`). Almost-global
  synchronization (`two_tendsto_of_inner_ne_zero`): with `κ_v > 0`, `ηw > 0` and every `c`,
  every solution not starting on the in-line hypersurface `Im(v₀ v̄₁) = 0` (a closed
  real-algebraic set of measure zero containing the anti-phase set) synchronizes exponentially.
  Off the anti-phase set `v₀ = −v₁` itself: a solution starting off it never reaches it and
  `D³/U` decays at the rate `4(3ηw − c)` (`two_offAntiPhase_rate`); for `κ_v > 0` and
  `c ≤ 3ηw` every such solution synchronizes (`two_tendsto_of_add_ne_zero`, the Barbalat law
  `Dynamics.VariableRate.tendsto_zero_of_hasDerivAt_le` on `Ψ = D³/U`, `Ψ' ≤ −κ_v D³`); for
  `ηw ≥ 0` and `3ηw < c` the in-line oscillation `((σ + δ), (σ − δ)) e^{jω_s t}` is off the
  anti-phase set and never synchronizes (`two_mixed`). So "for `2ηw < c` every solution not
  starting on the anti-phase set synchronizes" holds exactly in the window `2ηw < c ≤ 3ηw`
  (refuted for `c > 3ηw`); the exceptional set of the almost-global statement is the in-line
  hypersurface for every `c`.
* The network with power and voltage set-points (Colombino et al. 2019, with the paper's
  amplitude law `(v*_k − |v_k|)/v*_k`) is `theorem/GridTiedConverter/GFM/DVOCNetwork.lean`
  (set-point consistency, the synchronous set, convergence to the origin or to the synchronous
  set, the two-unit exceptional set) and `DVOCNetworkLocal.lean` (local exponential stability
  of the synchronous set through a family).

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
* The loaded oscillator is read as the family member `load κ_i Y` (`loadedField_eq`; same family,
  no change of representation): its origin is locally asymptotically stable — the oscillation is
  quenched — exactly when `c < κ_i g`, or `κ_i g = c` with `κ_v > 0`
  (`load_mem_den_locallyAsymptoticallyStable_iff`), Lyapunov stable exactly when `c < κ_i g`, or
  `κ_i g = c` with `κ_v ≥ 0` (`load_mem_den_lyapunovStable_iff`), locally exponentially stable
  exactly when `c < κ_i g` (`load_mem_den_locallyExponentiallyStable_iff`), and unstable for
  `κ_i g < c` (`load_mem_den_unstable`): a passive load larger than the growth margin quenches the
  oscillator, a reactive load only shifts its frequency to `ω_s − κ_i b`.
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
* The dVOC control law of §1.3 differs from Colombino et al. 2019. The multi-converter statement
  formalized here is the set-point-free network (synchronization for `ηλ > c`, exact for two
  units up to `2ηw = c`; two units almost-globally for every `c`, off the anti-phase set exactly
  for `c ≤ 3ηw`); §1.5's certificate with set-points is in `DVOCNetwork` and
  `DVOCNetworkLocal` (Colombino et al.'s control law, not §1.3's).
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
  all_goals
    rw [(connection_proof% TMIO.mem_realize)] at ha
    rw [(connection_proof% family_isAutonomous.mem_den_flow)]
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
    NormalForm.Hopf.linPart, Transform.complexSymm, Criteria.isHurwitz_fin_two_of_iff]
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

@[tmio M, powerlib_domain] private theorem critical_not_decaying :
    connection% (critical ∉ TMIO.realize Meets {.decaying}) := by
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
    (q := .decaying) (by simp [family, translate])
    (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family]
      using critical_not_decaying)

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
    (by simp [family, translate])
    (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family]
      using critical_not_decaying)

/-- The Lyapunov translation is sound but not exact (the same witness). -/
@[tmio TM, powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have hmem := critical_mem_den_globallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  exact Spectral.not_exact_of_witness (family_isAutonomous.mem_den_flow.mpr
    (family_isAutonomous.mem_den_flow.mp hmem).2.2.1) (q := .decaying)
    (by simp [family, translate])
    (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, family]
      using critical_not_decaying)

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

/-! ## The AHO under a constant admittance load -/

variable (a)

/-- The loaded AHO field `v̇ = (jω_s − σ + κ_v (v*² − |v|²)) v − κ_i i` with the output current of a
constant admittance load, `i = Y v` (`Y = g + jb`; a passive load has `g ≥ 0`). -/
def loadedField (κi : ℝ) (Y v : ℂ) : ℂ := a.field v - κi * (Y * v)

/-- The AHO parameters of the loaded oscillator: frequency `ω_s − κ_i b`, damping `σ + κ_i g`. -/
def load (κi : ℝ) (Y : ℂ) : AHO := ⟨a.ωs - κi * Y.im, a.σ + κi * Y.re, a.κv, a.vstar⟩

/-- **The loaded oscillator is an AHO**: the loaded field is the no-load field of `load`. Static
evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem loadedField_eq (κi : ℝ) (Y v : ℂ) :
    a.loadedField κi Y v = (a.load κi Y).field v := by
  apply Complex.ext <;>
    simp only [loadedField, load, field, gain, c, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;> ring

/-- The growth coefficient of the loaded oscillator, `c − κ_i g`. Static evidence on the model. -/
@[tmio M, simp, powerlib_domain] theorem load_c (κi : ℝ) (Y : ℂ) :
    (a.load κi Y).c = a.c - κi * Y.re := by
  simp only [load, c]
  ring

/-- The loaded oscillator meets the standing assumptions exactly when `κ_v > 0` and the load
damping stays below the growth, `κ_i g < c`; then its limit cycle has radius
`r*² = (c − κ_i g)/κ_v` (and frequency `ω_s − κ_i b`, the `ω_s` of `load`). Static evidence on the
model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem load_admissible_iff (κi : ℝ) (Y : ℂ) :
    (a.load κi Y).Admissible ↔ 0 < a.κv ∧ κi * Y.re < a.c := by
  constructor
  · intro h
    refine ⟨h.κv, ?_⟩
    have := h.gap
    simp only [load, c] at this ⊢
    linarith
  · rintro ⟨hk, hg⟩
    refine ⟨hk, ?_⟩
    simp only [load, c] at hg ⊢
    linarith

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem load_rstar_sq {κi : ℝ} {Y : ℂ}
    (h : (a.load κi Y).Admissible) :
    (a.load κi Y).rstar ^ 2 = (a.c - κi * Y.re) / a.κv := by
  rw [h.rstar_sq, load_c]
  rfl

/-- **Quenching by a load, exact.** The origin of the loaded oscillator is locally asymptotically
stable (the oscillation is quenched near the origin) exactly when the load damping reaches the
growth: `κ_i g > c`, or `κ_i g = c` with `κ_v > 0` (`mem_den_locallyAsymptoticallyStable_iff` of
`load`). -/
@[tmio TM, powerlib_domain] theorem load_mem_den_locallyAsymptoticallyStable_iff (κi : ℝ)
    (Y : ℂ) :
    connection% (a.load κi Y ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      (a.c < κi * Y.re ∨ (κi * Y.re = a.c ∧ 0 < a.κv))) := by
  have h := mem_den_locallyAsymptoticallyStable_iff (a.load κi Y)
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h, Set.mem_ofPred_eq, load_c]
  constructor <;> rintro (h | ⟨h1, h2⟩)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, h2⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, h2⟩

/-- **Oscillation under a load, exact.** The origin of the loaded oscillator is Lyapunov stable
exactly when `κ_i g > c`, or `κ_i g = c` with `κ_v ≥ 0`; otherwise (`κ_i g < c`, the standing
assumption of the limit cycle) it is unstable (`load_mem_den_unstable`). -/
@[tmio TM, powerlib_domain] theorem load_mem_den_lyapunovStable_iff (κi : ℝ) (Y : ℂ) :
    connection% (a.load κi Y ∈ family.den (.flow .lyapunovStable) ↔
      (a.c < κi * Y.re ∨ (κi * Y.re = a.c ∧ 0 ≤ a.κv))) := by
  have h := mem_den_lyapunovStable_iff (a.load κi Y)
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h, Set.mem_ofPred_eq, load_c]
  constructor <;> rintro (h | ⟨h1, h2⟩)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, h2⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, h2⟩

/-- The origin of the loaded oscillator is locally exponentially stable exactly when the load
damping exceeds the growth, `c < κ_i g` (`exact_locallyExponentiallyStable` at `load`). -/
@[tmio TM, powerlib_domain] theorem load_mem_den_locallyExponentiallyStable_iff (κi : ℝ)
    (Y : ℂ) :
    connection% (a.load κi Y ∈ family.den (.flow .locallyExponentiallyStable) ↔
      a.c < κi * Y.re) := by
  have h := exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at h ⊢
  rw [← h, (connection_proof% TMIO.mem_realize)]
  simp only [family, translate, Set.mem_singleton_iff, forall_eq, Meets, load_c]
  constructor <;> intro h <;> linarith

/-- With the load damping below the growth (`κ_i g < c`) the origin of the loaded oscillator is
unstable: solutions leave it towards the loaded limit cycle. -/
@[tmio TM, powerlib_domain] theorem load_mem_den_unstable {κi : ℝ} {Y : ℂ}
    (h : κi * Y.re < a.c) :
    connection% (a.load κi Y ∈ family.den (.flow .unstable)) :=
  mem_den_unstable (a.load κi Y) (by rw [load_c]; linarith)

/-! ## Networks of oscillators with a Laplacian current coupling -/

/-- **The AHO node is one-sided Lipschitz** (`κ_v ≥ 0`): `⟪x − y, f(x) − f(y)⟫ ≤ c ‖x − y‖²`;
the rotation `j ω_s` is skew and the cubic term is monotone,
`Re((x − y)* (|x|² x − |y|² y)) ≥ (|x|² − |y|²)²/2`. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem inner_field_sub_le (hκ : 0 ≤ a.κv) (x y : ℂ) :
    inner ℝ (x - y) (a.field x - a.field y) ≤ a.c * ‖x - y‖ ^ 2 := by
  rw [Complex.inner, ← Complex.normSq_eq_norm_sq]
  simp only [field, gain, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  set p := x.re
  set q := x.im
  set r := y.re
  set w := y.im
  have hmono : 0 ≤ (p ^ 2 + q ^ 2) ^ 2 + (r ^ 2 + w ^ 2) ^ 2 -
      (p ^ 2 + q ^ 2 + (r ^ 2 + w ^ 2)) * (p * r + q * w) := by
    nlinarith [sq_nonneg (p - r), sq_nonneg (q - w), sq_nonneg (p ^ 2 + q ^ 2 - r ^ 2 - w ^ 2),
      mul_nonneg (add_nonneg (add_nonneg (sq_nonneg p) (sq_nonneg q))
        (add_nonneg (sq_nonneg r) (sq_nonneg w))) (add_nonneg (sq_nonneg (p - r))
          (sq_nonneg (q - w)))]
  nlinarith [mul_nonneg hκ hmono]

/-- `n` identical oscillators with the current coupling `−η ∑ⱼ Lₖⱼ vⱼ` (the matched-rotation dVOC
without power set-points, or the AHO with a Laplacian network current `i = L v`). -/
def networkField {ι : Type*} [Fintype ι] (η : ℝ) (L : Matrix ι ι ℝ) (v : ι → ℂ) : ι → ℂ :=
  Dynamics.DiffusiveSync.netField a.field L η v

/-- The real coupling bound gives the complex one: the real and imaginary parts are coupled by
the same real matrix. -/
@[tmio T, powerlib_foundation] private theorem coupling_complex {ι : Type*} [Fintype ι]
    {L : Matrix ι ι ℝ} {lam : ℝ}
    (hL : ∀ u : ι → ℝ, lam * ∑ k, ∑ j, (u k - u j) ^ 2 ≤
      ∑ k, ∑ j, (u k - u j) * (∑ l, L k l * u l - ∑ l, L j l * u l)) (X : ι → ℂ) :
    lam * Dynamics.DiffusiveSync.disagreement X ≤
      ∑ k, ∑ j, inner ℝ (X k - X j) (∑ l, L k l • X l - ∑ l, L j l • X l) := by
  have hre := hL fun k => (X k).re
  have him := hL fun k => (X k).im
  have hW : Dynamics.DiffusiveSync.disagreement X =
      ∑ k, ∑ j, ((X k).re - (X j).re) ^ 2 + ∑ k, ∑ j, ((X k).im - (X j).im) ^ 2 := by
    simp only [Dynamics.DiffusiveSync.disagreement, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hI : ∑ k, ∑ j, inner ℝ (X k - X j) (∑ l, L k l • X l - ∑ l, L j l • X l) =
      ∑ k, ∑ j, ((X k).re - (X j).re) *
          (∑ l, L k l * (X l).re - ∑ l, L j l * (X l).re) +
        ∑ k, ∑ j, ((X k).im - (X j).im) *
          (∑ l, L k l * (X l).im - ∑ l, L j l * (X l).im) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.inner]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
      Complex.re_sum, Complex.im_sum, Complex.real_smul, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, zero_mul, sub_zero, add_zero]
    ring
  rw [hW, hI, mul_add]
  exact add_le_add hre him

/-- **Synchronization of an oscillator network** (implementation evidence: trajectory level,
Rules §3a). With `κ_v ≥ 0`, `η ≥ 0` and a real coupling contracting the disagreement at the rate
`λ` (for a symmetric Laplacian, `λ = λ₂`, the algebraic connectivity), every global solution has
`W(t) ≤ e^{2(c − η λ) t} W(0)`: the units synchronize exponentially when `η λ > c`
(`Dynamics.DiffusiveSync.disagreement_le` with `inner_field_sub_le`). -/
@[tmio TM, powerlib_domain] private theorem network_disagreement_le {ι : Type*} [Fintype ι]
    (hκ : 0 ≤ a.κv) {η lam : ℝ} (hη : 0 ≤ η) {L : Matrix ι ι ℝ}
    (hL : ∀ u : ι → ℝ, lam * ∑ k, ∑ j, (u k - u j) ^ 2 ≤
      ∑ k, ∑ j, (u k - u j) * (∑ l, L k l * u l - ∑ l, L j l * u l))
    {X : ℝ → ι → ℂ} (hX : ∀ t, HasDerivAt X (a.networkField η L (X t)) t) {t : ℝ} (ht : 0 ≤ t) :
    Dynamics.DiffusiveSync.disagreement (X t) ≤
      Real.exp (2 * (a.c - η * lam) * t) * Dynamics.DiffusiveSync.disagreement (X 0) :=
  Dynamics.DiffusiveSync.disagreement_le hη (a.inner_field_sub_le hκ) (coupling_complex hL) hX ht

/-- Two units coupled by one line of weight `w`. -/
def twoLine (w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![w, -w; -w, w]

/-- **Two units, synchronization** (implementation evidence: trajectory level). With `κ_v ≥ 0`,
`η ≥ 0` and `2 η w > c`, the disagreement of every global solution of two coupled units decays
exponentially at the rate `2(2ηw − c)` (the coupling contracts at `λ = 2w`). -/
@[tmio TM, powerlib_domain] private theorem two_disagreement_le (hκ : 0 ≤ a.κv) {η w : ℝ}
    (hη : 0 ≤ η) {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t) {t : ℝ} (ht : 0 ≤ t) :
    Dynamics.DiffusiveSync.disagreement (X t) ≤
      Real.exp (2 * (a.c - η * (2 * w)) * t) * Dynamics.DiffusiveSync.disagreement (X 0) :=
  a.network_disagreement_le hκ hη (fun u => by
    simp only [Fin.sum_univ_two, twoLine, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact le_of_eq (by ring)) hX ht

/-- **Two units, anti-phase oscillation** (implementation evidence: trajectory level). With
`κ_v > 0` and `2 η w < c` the anti-phase pair `v₀ = r e^{jω_s t} = −v₁`,
`r² = (c − 2ηw)/κ_v`, is a global solution whose disagreement stays `8 r² > 0`: the units never
synchronize, so `2 η w ≥ c` is necessary for synchronization of every solution and the threshold
of `two_disagreement_le` is exact up to the boundary `2 η w = c`. -/
@[tmio TM, powerlib_domain] private theorem two_antiPhase (hκ : 0 < a.κv) {η w : ℝ}
    (hc : 2 * η * w < a.c) :
    let r := Real.sqrt ((a.c - 2 * η * w) / a.κv)
    let X : ℝ → Fin 2 → ℂ := fun t => ![r * exp (a.ωs * t * I), -(r * exp (a.ωs * t * I))]
    (∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t) ∧
      ∀ t, Dynamics.DiffusiveSync.disagreement (X t) = 8 * r ^ 2 ∧ 0 < r := by
  intro r X
  have hr2 : r ^ 2 = (a.c - 2 * η * w) / a.κv :=
    Real.sq_sqrt (div_nonneg (by linarith) hκ.le)
  have hrpos : 0 < r := Real.sqrt_pos.mpr (div_pos (by linarith) hκ)
  have hnorm : ∀ t : ℝ, normSq ((r : ℂ) * exp (a.ωs * t * I)) = r ^ 2 := by
    intro t
    rw [Complex.normSq_mul, Complex.normSq_ofReal,
      show (a.ωs : ℂ) * (t : ℂ) * I = ((a.ωs * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    ring
  refine ⟨fun t => ?_, fun t => ⟨?_, hrpos⟩⟩
  · have hz : HasDerivAt (fun t : ℝ => (r : ℂ) * exp (a.ωs * t * I))
        ((r : ℂ) * (exp (a.ωs * t * I) * (a.ωs * I))) t := by
      have h1 : HasDerivAt (fun t : ℝ => (a.ωs : ℂ) * t * I) (a.ωs * I) t := by
        have := ((hasDerivAt_id (t : ℝ)).ofReal_comp.const_mul (a.ωs : ℂ)).mul_const I
        simpa using this
      exact h1.cexp.const_mul _
    have hfz : a.field ((r : ℂ) * exp (a.ωs * t * I)) =
        (I * a.ωs + ((2 * η * w : ℝ) : ℂ)) * ((r : ℂ) * exp (a.ωs * t * I)) := by
      rw [field, gain, hnorm, hr2]
      congr 3
      field_simp
      ring
    have hfz' : a.field (-((r : ℂ) * exp (a.ωs * t * I))) =
        -((I * a.ωs + ((2 * η * w : ℝ) : ℂ)) * ((r : ℂ) * exp (a.ωs * t * I))) := by
      rw [field, gain, Complex.normSq_neg, ← gain, ← hfz, field]
      ring
    refine hasDerivAt_pi.mpr fun k => ?_
    fin_cases k
    · change HasDerivAt (fun t : ℝ => (r : ℂ) * exp (a.ωs * t * I)) _ t
      convert hz using 1
      change a.field (X t 0) - η • ∑ j, twoLine w 0 j • X t j = _
      simp only [Fin.sum_univ_two]
      change a.field ((r : ℂ) * exp (a.ωs * t * I)) -
        η • (w • ((r : ℂ) * exp (a.ωs * t * I)) + (-w) • -((r : ℂ) * exp (a.ωs * t * I))) = _
      rw [hfz]
      simp only [Complex.real_smul]
      push_cast
      ring
    · change HasDerivAt (fun t : ℝ => -((r : ℂ) * exp (a.ωs * t * I))) _ t
      convert hz.neg using 1
      change a.field (X t 1) - η • ∑ j, twoLine w 1 j • X t j = _
      simp only [Fin.sum_univ_two]
      change a.field (-((r : ℂ) * exp (a.ωs * t * I))) -
        η • ((-w) • ((r : ℂ) * exp (a.ωs * t * I)) + w • -((r : ℂ) * exp (a.ωs * t * I))) = _
      rw [hfz']
      simp only [Complex.real_smul]
      push_cast
      ring
  · simp only [Dynamics.DiffusiveSync.disagreement, Fin.sum_univ_two, X, Matrix.cons_val_zero,
      Matrix.cons_val_one, sub_self, sub_neg_eq_add, ← Complex.normSq_eq_norm_sq]
    have h2 : ∀ z : ℂ, z + z = 2 * z := fun z => by ring
    have h2' : ∀ z : ℂ, -z - z = -(2 * z) := fun z => by ring
    rw [h2, h2', Complex.normSq_neg, Complex.normSq_mul, hnorm]
    norm_num
    ring

/-! ## Two units: the explicit reduction -/

/-- The two-unit network: `v̇₀ = f(v₀) − ηw (v₀ − v₁)`, `v̇₁ = f(v₁) − ηw (v₁ − v₀)`. Static
evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem networkField_twoLine (η w : ℝ) (V : Fin 2 → ℂ) :
    a.networkField η (twoLine w) V 0 = a.field (V 0) - ((η * w : ℝ) : ℂ) * (V 0 - V 1) ∧
      a.networkField η (twoLine w) V 1 = a.field (V 1) - ((η * w : ℝ) : ℂ) * (V 1 - V 0) := by
  simp only [networkField, Dynamics.DiffusiveSync.netField, Fin.sum_univ_two, twoLine,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Complex.real_smul]
  push_cast
  constructor <;> ring

@[tmio T, powerlib_foundation] private theorem sq_norm' (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring

/-- The derivative of `R = ⟪j v₁, v₀⟫ = Im(v₀ v̄₁)` along the two-unit field:
`Ṙ = (2c − κ_v (‖v₀‖² + ‖v₁‖²) − 2ηw) R`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem two_inner_rot (η w : ℝ) (V : Fin 2 → ℂ) :
    inner ℝ (I * V 1) (a.networkField η (twoLine w) V 0) +
        inner ℝ (I * a.networkField η (twoLine w) V 1) (V 0) =
      (2 * a.c - a.κv * (‖V 0‖ ^ 2 + ‖V 1‖ ^ 2) - 2 * (η * w)) * inner ℝ (I * V 1) (V 0) := by
  obtain ⟨h0, h1⟩ := a.networkField_twoLine η w V
  rw [h0, h1]
  simp only [Complex.inner, field, gain, sq_norm', Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The derivative of `D = ‖v₀ − v₁‖²` along the two-unit field:
`Ḋ = (2c − κ_v (‖v₀‖² + ‖v₁‖²) − 4ηw) D − κ_v (‖v₀‖² − ‖v₁‖²)²`. Static evidence on the model, not
a connection conclusion. -/
@[tmio M, powerlib_domain] theorem two_inner_sub (η w : ℝ) (V : Fin 2 → ℂ) :
    2 * inner ℝ (V 0 - V 1) (a.networkField η (twoLine w) V 0 - a.networkField η (twoLine w) V 1) =
      (2 * a.c - a.κv * (‖V 0‖ ^ 2 + ‖V 1‖ ^ 2) - 4 * (η * w)) * ‖V 0 - V 1‖ ^ 2 -
        a.κv * (‖V 0‖ ^ 2 - ‖V 1‖ ^ 2) ^ 2 := by
  obtain ⟨h0, h1⟩ := a.networkField_twoLine η w V
  rw [h0, h1]
  simp only [Complex.inner, field, gain, sq_norm', Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The derivative of `U = ‖v₀ + v₁‖²` along the two-unit field:
`U̇ = (2c − κ_v (‖v₀‖² + ‖v₁‖²)) U − κ_v (‖v₀‖² − ‖v₁‖²)²`. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem two_inner_add (η w : ℝ) (V : Fin 2 → ℂ) :
    2 * inner ℝ (V 0 + V 1) (a.networkField η (twoLine w) V 0 + a.networkField η (twoLine w) V 1) =
      (2 * a.c - a.κv * (‖V 0‖ ^ 2 + ‖V 1‖ ^ 2)) * ‖V 0 + V 1‖ ^ 2 -
        a.κv * (‖V 0‖ ^ 2 - ‖V 1‖ ^ 2) ^ 2 := by
  obtain ⟨h0, h1⟩ := a.networkField_twoLine η w V
  rw [h0, h1]
  simp only [Complex.inner, field, gain, sq_norm', Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The derivative of `S = ‖v₀‖² + ‖v₁‖²` along the two-unit field:
`Ṡ = 2cS − 2κ_v (‖v₀‖⁴ + ‖v₁‖⁴) − 2ηw ‖v₀ − v₁‖²`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem two_inner_self (η w : ℝ) (V : Fin 2 → ℂ) :
    2 * inner ℝ (V 0) (a.networkField η (twoLine w) V 0) +
        2 * inner ℝ (V 1) (a.networkField η (twoLine w) V 1) =
      2 * a.c * (‖V 0‖ ^ 2 + ‖V 1‖ ^ 2) - 2 * a.κv * ((‖V 0‖ ^ 2) ^ 2 + (‖V 1‖ ^ 2) ^ 2) -
        2 * (η * w) * ‖V 0 - V 1‖ ^ 2 := by
  obtain ⟨h0, h1⟩ := a.networkField_twoLine η w V
  rw [h0, h1]
  simp only [Complex.inner, field, gain, sq_norm', Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring


variable {a}

/-- Along a solution of the two-unit network, the derivatives of the reduction quantities. -/
@[tmio TM, powerlib_domain] private theorem two_derivs {η w : ℝ} {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t) (t : ℝ) :
    let F := a.networkField η (twoLine w) (X t)
    HasDerivAt (fun s => ‖X s 0 - X s 1‖ ^ 2) (2 * inner ℝ (X t 0 - X t 1) (F 0 - F 1)) t ∧
    HasDerivAt (fun s => ‖X s 0 + X s 1‖ ^ 2) (2 * inner ℝ (X t 0 + X t 1) (F 0 + F 1)) t ∧
    HasDerivAt (fun s => ‖X s 0‖ ^ 2 + ‖X s 1‖ ^ 2)
      (2 * inner ℝ (X t 0) (F 0) + 2 * inner ℝ (X t 1) (F 1)) t ∧
    HasDerivAt (fun s => inner ℝ (I * X s 1) (X s 0))
      (inner ℝ (I * X t 1) (F 0) + inner ℝ (I * F 1) (X t 0)) t := by
  intro F
  have h0 : HasDerivAt (fun s => X s 0) (F 0) t := hasDerivAt_pi.mp (hX t) 0
  have h1 : HasDerivAt (fun s => X s 1) (F 1) t := hasDerivAt_pi.mp (hX t) 1
  refine ⟨(h0.sub h1).norm_sq, (h0.add h1).norm_sq, h0.norm_sq.add h1.norm_sq, ?_⟩
  exact (h1.const_mul I).inner ℝ h0

@[tmio TM, powerlib_domain] private theorem two_continuous {η w : ℝ} {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t) :
    Continuous fun t => ‖X t 0‖ ^ 2 + ‖X t 1‖ ^ 2 := by
  have hc : Continuous X := continuous_iff_continuousAt.mpr fun t => (hX t).continuousAt
  have h0 : Continuous fun t => X t 0 := (continuous_apply 0).comp hc
  have h1 : Continuous fun t => X t 1 := (continuous_apply 1).comp hc
  fun_prop

/-- `‖v₀ − v₁‖² ≤ 2 (‖v₀‖² + ‖v₁‖²)`, `‖v₀ + v₁‖² ≤ 2 (‖v₀‖² + ‖v₁‖²)`,
`(‖v₀‖² − ‖v₁‖²)² ≤ ‖v₀ + v₁‖² ‖v₀ − v₁‖²`. -/
@[tmio T, powerlib_foundation] private theorem two_norm_facts (x y : ℂ) :
    ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) ∧ ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) ∧
      (‖x‖ ^ 2 - ‖y‖ ^ 2) ^ 2 ≤ ‖x + y‖ ^ 2 * ‖x - y‖ ^ 2 ∧
      ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hpar : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    simp only [sq_norm']; simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im]; ring
  have hin : inner ℝ (x + y) (x - y) = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
    rw [Complex.inner]; simp only [sq_norm', Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]; ring
  have hcs := abs_real_inner_le_norm (x + y) (x - y)
  rw [hin] at hcs
  refine ⟨by nlinarith [sq_nonneg ‖x + y‖], by nlinarith [sq_nonneg ‖x - y‖], ?_, hpar⟩
  have := mul_self_le_mul_self (abs_nonneg _) hcs
  rw [← sq, sq_abs] at this
  nlinarith [this]

/-- **Two units, the amplitudes stay bounded** (implementation evidence: trajectory level). With
`κ_v > 0`, `‖v₀‖² + ‖v₁‖² ≤ max (‖v₀(0)‖² + ‖v₁(0)‖²) ((2c + 4|ηw| + 1)²/(4κ_v))` on `[0, ∞)`. -/
@[tmio TM, powerlib_domain] private theorem two_normSq_le (hκ : 0 < a.κv) {η w : ℝ}
    {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t) {t : ℝ} (ht : 0 ≤ t) :
    ‖X t 0‖ ^ 2 + ‖X t 1‖ ^ 2 ≤ max (‖X 0 0‖ ^ 2 + ‖X 0 1‖ ^ 2)
      ((2 * a.c + 4 * |η * w| + 1) ^ 2 / (4 * a.κv)) := by
  have hb := Dynamics.le_max_of_hasDerivWithinAt_le (a := 1)
    (b := (2 * a.c + 4 * |η * w| + 1) ^ 2 / (4 * a.κv)) (t₀ := 0) (t₁ := t) one_pos
    (two_continuous hX).continuousOn (fun s _ => ((two_derivs hX s).2.2.1).hasDerivWithinAt)
    (fun s _ => ?_) t ⟨ht, le_rfl⟩
  · simpa using hb
  · rw [a.two_inner_self η w (X s)]
    obtain ⟨hD, -, -, -⟩ := two_norm_facts (X s 0) (X s 1)
    set S := ‖X s 0‖ ^ 2 + ‖X s 1‖ ^ 2
    have hS2 : S ^ 2 ≤ 2 * ((‖X s 0‖ ^ 2) ^ 2 + (‖X s 1‖ ^ 2) ^ 2) := by
      nlinarith [sq_nonneg (‖X s 0‖ ^ 2 - ‖X s 1‖ ^ 2)]
    have hg : -(2 * (η * w) * ‖X s 0 - X s 1‖ ^ 2) ≤ 4 * |η * w| * S := by
      have h1 : -(η * w) ≤ |η * w| := neg_le_abs _
      have h2 : 0 ≤ ‖X s 0 - X s 1‖ ^ 2 := sq_nonneg _
      nlinarith [abs_nonneg (η * w)]
    have hsq : 0 ≤ a.κv * (S - (2 * a.c + 4 * |η * w| + 1) / (2 * a.κv)) ^ 2 :=
      mul_nonneg hκ.le (sq_nonneg _)
    have hexp : a.κv * (S - (2 * a.c + 4 * |η * w| + 1) / (2 * a.κv)) ^ 2 =
        a.κv * S ^ 2 - (2 * a.c + 4 * |η * w| + 1) * S +
          (2 * a.c + 4 * |η * w| + 1) ^ 2 / (4 * a.κv) := by
      field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hS2 hκ.le]


/-- **Two units, relative synchronization off the in-line set** (implementation evidence:
trajectory level). With `κ_v ≥ 0`, along every global solution the quantity
`R = Im(v₀ v̄₁) = ⟪j v₁, v₀⟫` obeys `Ṙ = λ R` and the squared difference `D = ‖v₀ − v₁‖²` obeys
`Ḋ ≤ (λ − 2ηw) D` with the same rate `λ = 2c − κ_v (‖v₀‖² + ‖v₁‖²) − 2ηw`: so
`D(t) |R(0)| e^{2ηwt} ≤ D(0) |R(t)|`, and `R(t) ≠ 0` when `R(0) ≠ 0` (the set `Im(v₀ v̄₁) = 0`,
where the two phasors are in line, is invariant, and so is its complement). -/
@[tmio TM, powerlib_domain] private theorem two_sync_rate (hκ : 0 ≤ a.κv) {η w : ℝ}
    {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t) {t : ℝ} (ht : 0 ≤ t) :
    ‖X t 0 - X t 1‖ ^ 2 * |inner ℝ (I * X 0 1) (X 0 0)| * Real.exp (2 * (η * w) * t) ≤
        ‖X 0 0 - X 0 1‖ ^ 2 * |inner ℝ (I * X t 1) (X t 0)| ∧
      (inner ℝ (I * X 0 1) (X 0 0) ≠ 0 → inner ℝ (I * X t 1) (X t 0) ≠ 0) := by
  set lam : ℝ → ℝ := fun s => 2 * a.c - a.κv * (‖X s 0‖ ^ 2 + ‖X s 1‖ ^ 2) - 2 * (η * w)
  have hlam : Continuous lam := by
    have := two_continuous hX; fun_prop
  have hR := Dynamics.VariableRate.eq_mul_exp_integral
    (g := fun s => inner ℝ (I * X s 1) (X s 0)) hlam
    (fun s _ => (two_derivs hX s).2.2.2) (fun s _ => a.two_inner_rot η w (X s)) ht
  have hD := Dynamics.VariableRate.le_mul_exp_integral
    (g := fun s => ‖X s 0 - X s 1‖ ^ 2 * Real.exp (2 * (η * w) * s)) hlam
    (fun s _ => (two_derivs hX s).1.mul
      (((hasDerivAt_id s).const_mul (2 * (η * w))).exp)) (fun s _ => ?_) ht
  · simp only [mul_zero, Real.exp_zero, mul_one] at hD
    refine ⟨?_, fun h0 => by rw [hR]; exact mul_ne_zero h0 (Real.exp_pos _).ne'⟩
    rw [hR, abs_mul, abs_of_pos (Real.exp_pos _)]
    have := mul_le_mul_of_nonneg_right hD (abs_nonneg (inner ℝ (I * X 0 1) (X 0 0)))
    nlinarith [this]
  · simp only [id, mul_one]
    have h := a.two_inner_sub η w (X s)
    have hpos := Real.exp_pos (2 * (η * w) * s)
    have hQ : 0 ≤ a.κv * (‖X s 0‖ ^ 2 - ‖X s 1‖ ^ 2) ^ 2 := mul_nonneg hκ (sq_nonneg _)
    simp only [lam]
    nlinarith [mul_le_mul_of_nonneg_right
      (show 2 * inner ℝ (X s 0 - X s 1) (a.networkField η (twoLine w) (X s) 0 -
        a.networkField η (twoLine w) (X s) 1) + 2 * (η * w) * ‖X s 0 - X s 1‖ ^ 2 ≤
        (2 * a.c - a.κv * (‖X s 0‖ ^ 2 + ‖X s 1‖ ^ 2) - 2 * (η * w)) * ‖X s 0 - X s 1‖ ^ 2
        by linarith) hpos.le]

/-- `W(X) = 2 ‖X₀ − X₁‖²` for two units. -/
@[tmio T, powerlib_foundation] private theorem two_disagreement_eq (V : Fin 2 → ℂ) :
    Dynamics.DiffusiveSync.disagreement V = 2 * ‖V 0 - V 1‖ ^ 2 := by
  simp only [Dynamics.DiffusiveSync.disagreement, Fin.sum_univ_two, sub_self, norm_zero]
  rw [← neg_sub (V 0) (V 1), norm_neg]
  ring

/-- **Two units, almost-global synchronization** (implementation evidence: trajectory level).
With `κ_v > 0` and `ηw > 0`, for every `c` (also where the anti-phase oscillation of
`two_antiPhase` exists), every global solution that does not start on the invariant in-line set
`Im(v₀ v̄₁) = 0` synchronizes exponentially: `W(t) ≤ W(0) S_max e^{−2ηwt}/|Im(v₀ v̄₁)(0)| → 0`,
`S_max` the amplitude bound of `two_normSq_le`. The exceptional set is a proper real-algebraic
hypersurface of `ℂ²`, of measure zero. -/
@[tmio TM, powerlib_domain] private theorem two_tendsto_of_inner_ne_zero (hκ : 0 < a.κv) {η w : ℝ}
    (hηw : 0 < η * w)
    {X : ℝ → Fin 2 → ℂ} (hX : ∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t)
    (hR : inner ℝ (I * X 0 1) (X 0 0) ≠ 0) :
    Tendsto (fun t => Dynamics.DiffusiveSync.disagreement (X t)) atTop (𝓝 0) := by
  set Smax := max (‖X 0 0‖ ^ 2 + ‖X 0 1‖ ^ 2) ((2 * a.c + 4 * |η * w| + 1) ^ 2 / (4 * a.κv))
  set C := 2 * (‖X 0 0 - X 0 1‖ ^ 2 * Smax / |inner ℝ (I * X 0 1) (X 0 0)|)
  have hR0 : 0 < |inner ℝ (I * X 0 1) (X 0 0)| := abs_pos.mpr hR
  have hbound : ∀ t, 0 ≤ t → Dynamics.DiffusiveSync.disagreement (X t) ≤
      C * Real.exp (-(2 * (η * w)) * t) := by
    intro t ht
    rw [two_disagreement_eq]
    have h1 := (two_sync_rate hκ.le hX ht).1
    have h2 : |inner ℝ (I * X t 1) (X t 0)| ≤ Smax := by
      have hcs := abs_real_inner_le_norm (I * X t 1) (X t 0)
      rw [norm_mul, Complex.norm_I, one_mul] at hcs
      have := two_normSq_le hκ hX ht
      nlinarith [sq_nonneg (‖X t 1‖ - ‖X t 0‖), norm_nonneg (X t 0), norm_nonneg (X t 1)]
    have hE : Real.exp (-(2 * (η * w)) * t) * Real.exp (2 * (η * w) * t) = 1 := by
      rw [← Real.exp_add]; simp
    have hEpos := Real.exp_pos (2 * (η * w) * t)
    have hEpos' := Real.exp_pos (-(2 * (η * w)) * t)
    have h3 : ‖X t 0 - X t 1‖ ^ 2 * |inner ℝ (I * X 0 1) (X 0 0)| ≤
        ‖X 0 0 - X 0 1‖ ^ 2 * Smax * Real.exp (-(2 * (η * w)) * t) := by
      have h4 := mul_le_mul_of_nonneg_right h1 hEpos'.le
      rw [mul_assoc (‖X t 0 - X t 1‖ ^ 2 * _), mul_comm (Real.exp _) (Real.exp _), hE,
        mul_one] at h4
      refine h4.trans ?_
      gcongr
    have h5 : ‖X t 0 - X t 1‖ ^ 2 ≤ ‖X 0 0 - X 0 1‖ ^ 2 * Smax *
        Real.exp (-(2 * (η * w)) * t) / |inner ℝ (I * X 0 1) (X 0 0)| := by
      rw [le_div_iff₀ hR0]; exact h3
    calc 2 * ‖X t 0 - X t 1‖ ^ 2 ≤ 2 * (‖X 0 0 - X 0 1‖ ^ 2 * Smax *
          Real.exp (-(2 * (η * w)) * t) / |inner ℝ (I * X 0 1) (X 0 0)|) := by linarith
      _ = C * Real.exp (-(2 * (η * w)) * t) := by simp only [C]; ring
  have hexp : Tendsto (fun t => C * Real.exp (-(2 * (η * w)) * t)) atTop (𝓝 0) := by
    have : Tendsto (fun t => Real.exp (-(2 * (η * w)) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    simpa using this.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · exact Eventually.of_forall fun t => by
      rw [two_disagreement_eq]; positivity
  · exact eventually_atTop.mpr ⟨0, hbound⟩


/-- Along a global solution with `v₀(0) + v₁(0) ≠ 0` (off the anti-phase set) and `κ_v ≥ 0`, the
sum `U = ‖v₀ + v₁‖²` stays positive, and `Ψ = D³/U` (`D = ‖v₀ − v₁‖²`) obeys
`Ψ' ≤ −4(3ηw − c) Ψ − κ_v D³` on `[0, ∞)`. -/
@[tmio TM, powerlib_domain] private theorem two_psi (hκ : 0 ≤ a.κv) {η w : ℝ} {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t)
    (hs : X 0 0 + X 0 1 ≠ 0) :
    (∀ t, 0 ≤ t → 0 < ‖X t 0 + X t 1‖ ^ 2) ∧
      ∀ t, 0 ≤ t → ∃ Ψ', HasDerivAt (fun s => (‖X s 0 - X s 1‖ ^ 2) ^ 3 / ‖X s 0 + X s 1‖ ^ 2)
        Ψ' t ∧ Ψ' ≤ -(4 * (3 * (η * w) - a.c)) *
          ((‖X t 0 - X t 1‖ ^ 2) ^ 3 / ‖X t 0 + X t 1‖ ^ 2) - a.κv * (‖X t 0 - X t 1‖ ^ 2) ^ 3 := by
  have hcont := two_continuous hX
  have hc : Continuous X := continuous_iff_continuousAt.mpr fun t => (hX t).continuousAt
  have h0c : Continuous fun t => X t 0 := (continuous_apply 0).comp hc
  have h1c : Continuous fun t => X t 1 := (continuous_apply 1).comp hc
  set mu : ℝ → ℝ := fun s => 2 * a.c - a.κv * (‖X s 0‖ ^ 2 + ‖X s 1‖ ^ 2) -
    a.κv * ‖X s 0 - X s 1‖ ^ 2
  have hmu : Continuous mu := by fun_prop
  have hU : ∀ t, 0 ≤ t → 0 < ‖X t 0 + X t 1‖ ^ 2 := by
    intro t ht
    have h := Dynamics.VariableRate.mul_exp_integral_le (g := fun s => ‖X s 0 + X s 1‖ ^ 2) hmu
      (fun s _ => (two_derivs hX s).2.1) (fun s _ => ?_) ht
    · have h0 : 0 < ‖X 0 0 + X 0 1‖ ^ 2 := by positivity
      exact lt_of_lt_of_le (mul_pos h0 (Real.exp_pos _)) h
    · rw [a.two_inner_add η w (X s)]
      obtain ⟨-, -, hQ, -⟩ := two_norm_facts (X s 0) (X s 1)
      simp only [mu]
      nlinarith [mul_le_mul_of_nonneg_left hQ hκ]
  refine ⟨hU, fun t ht => ?_⟩
  obtain ⟨hD, hUd, -, -⟩ := two_derivs hX t
  have hUt := hU t ht
  refine ⟨_, (hD.pow 3).div hUd hUt.ne', ?_⟩
  rw [a.two_inner_sub η w (X t), a.two_inner_add η w (X t)]
  obtain ⟨-, -, hQ, hpar⟩ := two_norm_facts (X t 0) (X t 1)
  set D := ‖X t 0 - X t 1‖ ^ 2
  set U := ‖X t 0 + X t 1‖ ^ 2
  set Q := (‖X t 0‖ ^ 2 - ‖X t 1‖ ^ 2) ^ 2
  set S := ‖X t 0‖ ^ 2 + ‖X t 1‖ ^ 2
  have hD0 : 0 ≤ D := sq_nonneg _
  have hQ0 : 0 ≤ Q := sq_nonneg _
  have key : 3 * ((2 * a.c - a.κv * S - 4 * (η * w)) * D - a.κv * Q) * U -
      D * ((2 * a.c - a.κv * S) * U - a.κv * Q) ≤
        -(4 * (3 * (η * w) - a.c)) * U * D - a.κv * U ^ 2 * D := by
    have e : 2 * S = U + D := by linarith
    have h1 : a.κv * D * Q ≤ a.κv * D * (U * D) := mul_le_mul_of_nonneg_left hQ (mul_nonneg hκ hD0)
    have h2 : 0 ≤ a.κv * U * Q := mul_nonneg (mul_nonneg hκ hUt.le) hQ0
    have expand : 3 * ((2 * a.c - a.κv * S - 4 * (η * w)) * D - a.κv * Q) * U -
        D * ((2 * a.c - a.κv * S) * U - a.κv * Q) -
          (-(4 * (3 * (η * w) - a.c)) * U * D - a.κv * U ^ 2 * D) =
        -a.κv * U * D ^ 2 - 3 * (a.κv * U * Q) + a.κv * D * Q -
          a.κv * U * D * (2 * S - U - D) := by ring
    have hz : 2 * S - U - D = 0 := by linarith
    rw [hz, mul_zero, sub_zero] at expand
    nlinarith [expand, h1, h2]
  rw [div_le_iff₀ (by positivity)]
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg _
  have e2 : (-(4 * (3 * (η * w) - a.c)) * (D ^ 3 / U) - a.κv * D ^ 3) * U ^ 2 =
      D ^ 2 * (-(4 * (3 * (η * w) - a.c)) * U * D - a.κv * U ^ 2 * D) := by
    field_simp
  rw [e2]
  have := mul_le_mul_of_nonneg_left key hD2
  norm_num
  have hD3 : (‖X t 0 - X t 1‖ ^ 2) ^ 3 = D ^ 3 := rfl
  rw [hD3]
  nlinarith [this]

/-- **Two units, the anti-phase complement** (implementation evidence: trajectory level). With
`κ_v ≥ 0`, every global solution with `v₀(0) + v₁(0) ≠ 0` never reaches the anti-phase set
(`v₀ + v₁ ≠ 0` for `t ≥ 0`) and satisfies
`‖v₀ − v₁‖⁶ ‖v₀(0) + v₁(0)‖² e^{4(3ηw − c)t} ≤ ‖v₀(0) − v₁(0)‖⁶ ‖v₀ + v₁‖²`: for `c < 3ηw` the
difference decays exponentially relative to the sum. -/
@[tmio TM, powerlib_domain] private theorem two_offAntiPhase_rate (hκ : 0 ≤ a.κv) {η w : ℝ}
    {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t)
    (hs : X 0 0 + X 0 1 ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    X t 0 + X t 1 ≠ 0 ∧
      (‖X t 0 - X t 1‖ ^ 2) ^ 3 * ‖X 0 0 + X 0 1‖ ^ 2 *
          Real.exp (4 * (3 * (η * w) - a.c) * t) ≤
        (‖X 0 0 - X 0 1‖ ^ 2) ^ 3 * ‖X t 0 + X t 1‖ ^ 2 := by
  obtain ⟨hU, hΨ⟩ := two_psi hκ hX hs
  have hUt := hU t ht
  refine ⟨fun h => by rw [h, norm_zero] at hUt; simp at hUt, ?_⟩
  set r := 4 * (3 * (η * w) - a.c)
  choose! Ψ' hΨd hΨle using hΨ
  have hg := Dynamics.VariableRate.le_mul_exp_integral
    (g := fun s => (‖X s 0 - X s 1‖ ^ 2) ^ 3 / ‖X s 0 + X s 1‖ ^ 2 * Real.exp (r * s))
    (g' := fun s => Ψ' s * Real.exp (r * s) + (‖X s 0 - X s 1‖ ^ 2) ^ 3 / ‖X s 0 + X s 1‖ ^ 2 *
      (Real.exp (r * s) * r))
    (lam := fun _ => 0) continuous_const
    (fun s hs => by
      have := (hΨd s hs).fun_mul ((hasDerivAt_id s).const_mul r).exp
      simpa using this) (fun s hs => ?_) ht
  · simp only [intervalIntegral.integral_zero, Real.exp_zero, mul_one, mul_zero] at hg
    have hU0 := hU 0 le_rfl
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hUt hU0] at hg
    nlinarith [hg]
  · have h1 := hΨle s hs
    have hE := Real.exp_pos (r * s)
    have hD3 : 0 ≤ a.κv * (‖X s 0 - X s 1‖ ^ 2) ^ 3 := mul_nonneg hκ (by positivity)
    simp only [zero_mul]
    nlinarith [mul_le_mul_of_nonneg_right h1 hE.le]

/-- **Two units, synchronization off the anti-phase set** (implementation evidence: trajectory
level). With `κ_v > 0` and `c ≤ 3ηw`, every global solution that does not start on the anti-phase
set `v₀ = −v₁` synchronizes, `W(t) → 0`: `Ψ = D³/U` is nonincreasing with `Ψ' ≤ −κ_v D³`, so `D³`
is integrable on `[0, ∞)`, and `D³` has a derivative bounded below on the bounded solution
(`Dynamics.VariableRate.tendsto_zero_of_hasDerivAt_le`). -/
@[tmio TM, powerlib_domain] private theorem two_tendsto_of_add_ne_zero (hκ : 0 < a.κv) {η w : ℝ}
    (hc : a.c ≤ 3 * (η * w)) {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t)
    (hs : X 0 0 + X 0 1 ≠ 0) :
    Tendsto (fun t => Dynamics.DiffusiveSync.disagreement (X t)) atTop (𝓝 0) := by
  obtain ⟨hU, hΨ⟩ := two_psi hκ.le hX hs
  choose! Ψ' hΨd hΨle using hΨ
  set Smax := max (‖X 0 0‖ ^ 2 + ‖X 0 1‖ ^ 2) ((2 * a.c + 4 * |η * w| + 1) ^ 2 / (4 * a.κv))
  have hS0 : 0 ≤ Smax := le_max_of_le_left (by positivity)
  set K := (2 * |a.c| + a.κv * Smax + 4 * |η * w|) * (2 * Smax) + a.κv * Smax ^ 2
  have hK : 0 ≤ K := by positivity
  have hD3 : Tendsto (fun t => (‖X t 0 - X t 1‖ ^ 2) ^ 3) atTop (𝓝 0) := by
    refine Dynamics.VariableRate.tendsto_zero_of_hasDerivAt_le (k := a.κv)
      (L := 3 * (2 * Smax) ^ 2 * K) hκ hΨd (fun t ht => ?_) (fun t ht => ?_)
      (fun t _ => ((two_derivs hX t).1.pow 3)) (fun t _ => by positivity) (fun t ht => ?_)
    · have h1 := hΨle t ht
      have h2 : 0 ≤ 4 * (3 * (η * w) - a.c) *
          ((‖X t 0 - X t 1‖ ^ 2) ^ 3 / ‖X t 0 + X t 1‖ ^ 2) :=
        mul_nonneg (by linarith) (div_nonneg (by positivity) (hU t ht).le)
      linarith
    · exact div_nonneg (by positivity) (hU t ht).le
    · rw [a.two_inner_sub η w (X t)]
      obtain ⟨hDle, -, -, -⟩ := two_norm_facts (X t 0) (X t 1)
      have hSt : ‖X t 0‖ ^ 2 + ‖X t 1‖ ^ 2 ≤ Smax := two_normSq_le hκ hX ht
      set D := ‖X t 0 - X t 1‖ ^ 2
      set S := ‖X t 0‖ ^ 2 + ‖X t 1‖ ^ 2
      have hD0 : 0 ≤ D := sq_nonneg _
      have hS : 0 ≤ S := by positivity
      have hDS : D ≤ 2 * Smax := by linarith
      have hQ : (‖X t 0‖ ^ 2 - ‖X t 1‖ ^ 2) ^ 2 ≤ Smax ^ 2 := by
        have h1 : |‖X t 0‖ ^ 2 - ‖X t 1‖ ^ 2| ≤ Smax := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖X t 0‖, sq_nonneg ‖X t 1‖]
        nlinarith [sq_abs (‖X t 0‖ ^ 2 - ‖X t 1‖ ^ 2), abs_nonneg (‖X t 0‖ ^ 2 - ‖X t 1‖ ^ 2)]
      have hA : |2 * a.c - a.κv * S - 4 * (η * w)| ≤ 2 * |a.c| + a.κv * Smax + 4 * |η * w| := by
        have h1 : |2 * a.c - a.κv * S - 4 * (η * w)| ≤
            |2 * a.c| + |a.κv * S| + |4 * (η * w)| := by
          have := abs_sub (2 * a.c - a.κv * S) (4 * (η * w))
          have := abs_sub (2 * a.c) (a.κv * S)
          linarith
        have h2 : |(2 : ℝ) * a.c| = 2 * |a.c| := by rw [abs_mul, abs_two]
        have h3 : |a.κv * S| = a.κv * S := abs_of_nonneg (mul_nonneg hκ.le hS)
        have h4 : |(4 : ℝ) * (η * w)| = 4 * |η * w| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        rw [h2, h3, h4] at h1
        nlinarith [mul_le_mul_of_nonneg_left hSt hκ.le]
      have hDd : -K ≤ (2 * a.c - a.κv * S - 4 * (η * w)) * D -
          a.κv * (‖X t 0‖ ^ 2 - ‖X t 1‖ ^ 2) ^ 2 := by
        have h1 : -(2 * |a.c| + a.κv * Smax + 4 * |η * w|) * (2 * Smax) ≤
            (2 * a.c - a.κv * S - 4 * (η * w)) * D := by
          have := neg_abs_le (2 * a.c - a.κv * S - 4 * (η * w))
          have h2 : -(2 * |a.c| + a.κv * Smax + 4 * |η * w|) ≤ 2 * a.c - a.κv * S - 4 * (η * w) :=
            by linarith
          have h3 : 0 ≤ 2 * |a.c| + a.κv * Smax + 4 * |η * w| := by positivity
          nlinarith
        have h4 : a.κv * (‖X t 0‖ ^ 2 - ‖X t 1‖ ^ 2) ^ 2 ≤ a.κv * Smax ^ 2 :=
          mul_le_mul_of_nonneg_left hQ hκ.le
        simp only [K]
        linarith
      have hD2 : D ^ 2 ≤ (2 * Smax) ^ 2 := pow_le_pow_left₀ hD0 hDS 2
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hD2 hK, mul_nonneg (sq_nonneg D) (by linarith : 0 ≤
        (2 * a.c - a.κv * S - 4 * (η * w)) * D - a.κv * (‖X t 0‖ ^ 2 - ‖X t 1‖ ^ 2) ^ 2 + K)]
  have hD : Tendsto (fun t => ‖X t 0 - X t 1‖ ^ 2) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop] at hD3 ⊢
    intro ε hε
    obtain ⟨T, hT⟩ := hD3 (ε ^ 3) (by positivity)
    refine ⟨T, fun t ht => ?_⟩
    have h1 := hT t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1 ⊢
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ hε.le h 3
    linarith
  simpa [two_disagreement_eq] using hD.const_mul 2


/-- On a phasor `ρ e^{jθ}` of real amplitude `ρ` the node field is the multiplication by
`j ω_s + c − κ_v ρ²`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_ofReal_mul_exp (a : AHO) (ρ θ : ℝ) :
    a.field ((ρ : ℂ) * exp (θ * I)) =
      (I * a.ωs + ((a.c - a.κv * ρ ^ 2 : ℝ) : ℂ)) * ((ρ : ℂ) * exp (θ * I)) := by
  rw [field, gain, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  congr 3
  ring

/-- **Two units, the in-line relative equilibria with unequal amplitudes.** With
`κ_v σ² = (c − 3ηw)/4` and `κ_v δ² = (c + ηw)/4` the pair `((σ + δ) z, (σ − δ) z)`, `|z| = 1`, is
rotated by the network field at the rate `ω_s`: `F = j ω_s (v₀, v₁)`. Static evidence on the model,
not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem two_networkField_mixed (a : AHO) {η w σ δ : ℝ}
    (hσ : a.κv * σ ^ 2 = (a.c - 3 * (η * w)) / 4) (hδ : a.κv * δ ^ 2 = (a.c + η * w) / 4)
    (θ : ℝ) :
    a.networkField η (twoLine w)
        ![((σ + δ : ℝ) : ℂ) * exp (θ * I), ((σ - δ : ℝ) : ℂ) * exp (θ * I)] =
      ![I * a.ωs * (((σ + δ : ℝ) : ℂ) * exp (θ * I)),
        I * a.ωs * (((σ - δ : ℝ) : ℂ) * exp (θ * I))] := by
  obtain ⟨h0, h1⟩ := a.networkField_twoLine η w
    ![((σ + δ : ℝ) : ℂ) * exp (θ * I), ((σ - δ : ℝ) : ℂ) * exp (θ * I)]
  have e0 : (a.c - a.κv * (σ + δ) ^ 2) * (σ + δ) - 2 * (η * w) * δ = 0 := by
    linear_combination (-(σ + 3 * δ)) * hσ + (-(3 * σ + δ)) * hδ
  have e1 : (a.c - a.κv * (σ - δ) ^ 2) * (σ - δ) + 2 * (η * w) * δ = 0 := by
    linear_combination (-(σ - 3 * δ)) * hσ + (-(3 * σ - δ)) * hδ
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 ⊢
    rw [h0, field_ofReal_mul_exp]
    have : ((a.c - a.κv * (σ + δ) ^ 2 : ℝ) : ℂ) * ((σ + δ : ℝ) : ℂ) -
        ((η * w : ℝ) : ℂ) * (((σ + δ : ℝ) : ℂ) - ((σ - δ : ℝ) : ℂ)) = 0 := by
      have := congrArg (fun r : ℝ => (r : ℂ)) e0
      push_cast at this ⊢
      linear_combination this
    linear_combination exp (θ * I) * this
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] at h1 ⊢
    rw [h1, field_ofReal_mul_exp]
    have : ((a.c - a.κv * (σ - δ) ^ 2 : ℝ) : ℂ) * ((σ - δ : ℝ) : ℂ) -
        ((η * w : ℝ) : ℂ) * (((σ - δ : ℝ) : ℂ) - ((σ + δ : ℝ) : ℂ)) = 0 := by
      have := congrArg (fun r : ℝ => (r : ℂ)) e1
      push_cast at this ⊢
      linear_combination this
    linear_combination exp (θ * I) * this

/-- **Two units, an unequal-amplitude oscillation off the anti-phase set** (implementation
evidence: trajectory level). With `κ_v > 0`, `ηw ≥ 0` and `3ηw < c`, the pair
`v₀ = (σ + δ) e^{jω_s t}`, `v₁ = (σ − δ) e^{jω_s t}`, `σ = √((c − 3ηw)/(4κ_v)) > 0`,
`δ = √((c + ηw)/(4κ_v)) > 0`, is a global solution with `v₀ + v₁ = 2σ e^{jω_s t} ≠ 0` and constant
disagreement `W = 2(c + ηw)/κ_v > 0`: it is not on the anti-phase set and never synchronizes, so
the threshold `c ≤ 3ηw` of `two_tendsto_of_add_ne_zero` is exact. -/
@[tmio TM, powerlib_domain] private theorem two_mixed (hκ : 0 < a.κv) {η w : ℝ} (hηw : 0 ≤ η * w)
    (hc : 3 * (η * w) < a.c) :
    let σ := Real.sqrt ((a.c - 3 * (η * w)) / (4 * a.κv))
    let δ := Real.sqrt ((a.c + η * w) / (4 * a.κv))
    let X : ℝ → Fin 2 → ℂ := fun t =>
      ![((σ + δ : ℝ) : ℂ) * exp ((a.ωs * t : ℝ) * I), ((σ - δ : ℝ) : ℂ) * exp ((a.ωs * t : ℝ) * I)]
    (∀ t, HasDerivAt X (a.networkField η (twoLine w) (X t)) t) ∧
      ∀ t, X t 0 + X t 1 ≠ 0 ∧
        Dynamics.DiffusiveSync.disagreement (X t) = 2 * (a.c + η * w) / a.κv := by
  intro σ δ X
  have hσ2 : σ ^ 2 = (a.c - 3 * (η * w)) / (4 * a.κv) :=
    Real.sq_sqrt (div_nonneg (by linarith) (by linarith))
  have hδ2 : δ ^ 2 = (a.c + η * w) / (4 * a.κv) :=
    Real.sq_sqrt (div_nonneg (by linarith) (by linarith))
  have hσpos : 0 < σ := Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
  have hσ : a.κv * σ ^ 2 = (a.c - 3 * (η * w)) / 4 := by rw [hσ2]; field_simp
  have hδ : a.κv * δ ^ 2 = (a.c + η * w) / 4 := by rw [hδ2]; field_simp
  refine ⟨fun t => ?_, fun t => ⟨?_, ?_⟩⟩
  · have hz : ∀ ρ : ℝ, HasDerivAt (fun t : ℝ => (ρ : ℂ) * exp ((a.ωs * t : ℝ) * I))
        (I * a.ωs * ((ρ : ℂ) * exp ((a.ωs * t : ℝ) * I))) t := by
      intro ρ
      have h1 : HasDerivAt (fun t : ℝ => ((a.ωs * t : ℝ) : ℂ) * I) (a.ωs * I) t := by
        have := ((hasDerivAt_id (t : ℝ)).ofReal_comp.const_mul (a.ωs : ℂ)).mul_const I
        convert this using 1
        · funext s; simp only [id]; push_cast; ring
        · simp
      convert (h1.cexp.const_mul (ρ : ℂ)) using 1
      ring
    rw [show X t = ![((σ + δ : ℝ) : ℂ) * exp ((a.ωs * t : ℝ) * I),
      ((σ - δ : ℝ) : ℂ) * exp ((a.ωs * t : ℝ) * I)] from rfl,
      a.two_networkField_mixed hσ hδ]
    refine hasDerivAt_pi.mpr fun k => ?_
    fin_cases k
    · exact hz (σ + δ)
    · exact hz (σ - δ)
  · change ((σ + δ : ℝ) : ℂ) * exp ((a.ωs * t : ℝ) * I) +
      ((σ - δ : ℝ) : ℂ) * exp ((a.ωs * t : ℝ) * I) ≠ 0
    rw [← add_mul]
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    push_cast
    rw [show (σ : ℂ) + δ + (σ - δ) = ((2 * σ : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by positivity : (2 * σ : ℝ) ≠ 0)
  · rw [two_disagreement_eq]
    change 2 * ‖((σ + δ : ℝ) : ℂ) * exp ((a.ωs * t : ℝ) * I) -
      ((σ - δ : ℝ) : ℂ) * exp ((a.ωs * t : ℝ) * I)‖ ^ 2 = _
    rw [← sub_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      show ((σ + δ : ℝ) : ℂ) - ((σ - δ : ℝ) : ℂ) = ((2 * δ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [mul_pow, hδ2]
    field_simp
    ring

end AHO
end powerlib.GFM
