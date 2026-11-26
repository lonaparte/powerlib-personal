import theorem.PowerSystem.Synchronous.ParametricSwing
import theorem.ParametricResonance.Signature

/-! # Natural, forced and parametric oscillations of TR-110's swing model: a sound classification

TR-110 separates forced oscillations (a stable system driven by a periodic input) from natural
ones (a poorly damped or undamped mode) and offers no class for parametric oscillations (a
periodically varying parameter, here the synchronizing coefficient `K_s(t)`). This module adds
that class for the linearized swing model and proves, within the linear periodic model class,
signatures of each mechanism and decision rules whose verdicts are sound. The key fact is the
harmonic balance of a sustained oscillation with constant `K_s`: every Fourier coefficient obeys
`c_m(ΔP_m) = (K_s − MΩ_m² + jΩ_m D) c_m(Δδ)`, so with nonzero damping a constant-`K_s` model
(natural or forced) has no frequency of its own: content of `Δδ` at a frequency absent from
`ΔP_m` can only come from a varying `K_s`.

Model boundary.
* One generator, TR-110's linearized swing equation (3-8)–(3-10) at an operating point,
  continuous time, angle deviation `Δδ` (state `(Δδ, Δδ̇)` for the state-space statements):
  `M Δδ̈ + D Δδ̇ + K_s(t) Δδ = ΔP_m(t)`, `M = 2H/ω₀`, `D = (K_d + K_D)/ω₀`, with the parameters
  `Params` of `theorem/PowerSystem/Synchronous/OscillationPhasor.lean` (`p.Ks` the constant or
  mean synchronizing coefficient) and the time-varying coefficient of
  `theorem/PowerSystem/Synchronous/ParametricSwing.lean` (`frozen`, `modulated_iff`: the report's
  form (3-8)–(3-9) is this equation).
* Mechanisms as data (`Mechanism`): natural (`K_s` constant, `ΔP_m = 0`), forced (`K_s`
  constant, `ΔP_m(t)` given), parametric (`K_s(t) = K_s(1 + p(t))`, `ΔP_m = 0`). Periodicity,
  continuity, nonconstancy and the sign of the damping are hypotheses of the statements, not
  fields. Damping, `H`, `ω₀`, `K_d`, `K_D` are constant; AVR, PSS, network dynamics,
  nonlinearity and measurement (Prony) are excluded as in TR-110 §3.3.
* Solutions of the natural and forced models (continuous coefficients) are global `C²` curves.
  The square-wave instance has a discontinuous `K_s(t)`; its solutions are continuous on `[0, ∞)`
  with right derivatives (`theorem/ParametricResonance/Meissner.lean`), and the rules are applied
  to it by excluding every constant-`K_s` `C²` explanation of its angle.
* Observables used by the rules: the Fourier coefficients of `Δδ` and of `ΔP_m` over a common
  window (rules P, N), for rule P½ the candidate pump frequency `Ω = 2π/T` and the periodicity of
  `ΔP_m` at `T`; the sign of the frozen damping (`D ≠ 0`, `ξ > 0`) from the model or from
  ringdowns; for rules F and N the knowledge that `K_s` is constant. Measured records are not
  formalized (Rules §2a).

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.1 (natural versus
forced; intrinsic damping), §3.2 (start-up method), §3.3 (swing model (3-6)–(3-13), phase-angle
method), §3.4–§3.5 (harmonics of the steady state); the parametric mechanism of
`theorem/PowerSystem/Synchronous/ParametricSwing.lean`,
`theorem/ParametricResonance/EnergyBalance.lean`, `theorem/ParametricResonance/Wirtinger.lean`,
`theorem/ParametricResonance/Signature.lean` and `theorem/ParametricResonance/Meissner.lean`.

Corrections and sharpenings.
* TR-110's two methods misread a parametric oscillation as natural: its start-up slope is
  `ln |μ| > 0` (`parametric_startUp`), and on a sustained half-frequency oscillation the in-phase
  part of the fundamental phasors is bounded by the harmonic tail although `K_d > 0`
  (`parametric_signature`, from `ParametricSwing.halfFrequency_inPhase_le`). Positive frozen
  damping with a sustained oscillation is not specific to forced oscillations
  (`squareWave_instance`). What separates the three mechanisms is the frequency relation:
  content at a frequency absent from `ΔP_m` (rule P), in particular at `(k + ½)Ω` with
  `ΔP_m` at `Ωℤ` (rule P½).
* The boundaries of the half-frequency oscillation, each stated where it is exact: for a
  sinusoidal pump the energy bound `|ε| ≥ ξΩ/ω_n` (`2ξ` at `Ω = 2ω_n`,
  `ParametricSwing.halfFrequency_depth_ge`) holds for every depth and lies below the first-order
  boundary `4√(ξ² + d²)` (`ParametricSwing.firstOrder_stable`,
  `ParametricSwing.firstOrder_unstable`; `energyBound_lt_firstOrder`); for a square-wave pump
  the exact boundary is `|τ| = 2 cosh(ξω_n T)` (`squareWave_boundary`), and at the tongue
  centre the fundamental
  `4|ε|/π` of the modulation must exceed `4ξ√(ν₁ν₂)/ω_n` (`squareWave_centre_fundamental`), the
  first-order value `4ξ` up to a factor tending to `1`.

Results.
* `Mechanism`, `Mechanism.Ks`, `Mechanism.Pm` — the three mechanisms as data.
* `harmonic_balance` — `c_m(ΔP_m) = p.mechPhasor Ω_m (c_m(Δδ))`, `Ω_m = 2πm/L`, for every
  solution with constant `K_s` that closes over `[0, L]`; `coeff_eq_zero_of_const` — with
  `D ≠ 0`, a harmonic `m ≠ 0` absent from `ΔP_m` is absent from `Δδ`.
* `halfFrequency_eq_zero_of_const` — with `D ≠ 0` and `T`-periodic `ΔP_m`, a constant-`K_s`
  model has no nonzero `T`-antiperiodic solution on `[0, ∞)` (harmonic balance on every odd
  harmonic, antiperiodicity on the even ones, Parseval).
* Rules: `classify_parametric` (rule P: `D ≠ 0`, sustained, a harmonic `m ≠ 0` absent from
  `ΔP_m` ⇒ parametric with a nonconstant pump), `classify_halfFrequency` (rule P½: `D ≠ 0`,
  `ΔP_m` `T`-periodic, a nonzero `T`-antiperiodic oscillation ⇒ parametric),
  `classify_forced` (rule F: `D ≠ 0`, constant `K_s`, sustained ⇒ forced, `∫ ΔP_m Δδ̇ = D ∫ Δδ̇²`,
  every harmonic present in `ΔP_m`), `classify_natural` (rule N: constant `K_s`, a harmonic absent
  from `ΔP_m` ⇒ `K_d + K_D = 0` and `2HΩ_m² = ω₀K_s`).
* Signatures: `natural_signature` (`ξ = 0`, harmonics only at `ω_n`); `forced_signature`
  (`|c_m(Δδ)| = |c_m(ΔP_m)|/|K_s − MΩ_m² + jΩ_m D|`, `∫ ΔP_m Δω = (K_d + K_D) ∫ Δω² > 0`);
  `forced_tendsto_coeff_odd` (forced regime: half-integer content of every solution decays);
  at every sinusoidal steady state of the forced model the phase-angle method reads `ξ`
  correctly (`OscillationPhasor.Params.dampingRatio_eq_angleDamping`);
  `parametric_signature` (no `Ωℤ` content, pump work `K_d ∫ Δω² = (1/(2ω₀)) ∫ K̇_s Δδ² > 0`,
  phase-angle bound); `parametric_startUp` (start-up slope `ln |μ|`, verdict never forced).
* Worked instance: `frozen_stateMatrix`, `natFreq_sq`, `oscDamping_eq`, `squareWave_stateMatrix`
  (the square-wave swing model is the Meissner equation with `c = ξω_n`, `ω₀ = ω_n`);
  `squareWave_boundary` (period map, `det M = e^{−2ξω_n T}`, instability iff
  `2 cosh(ξω_n T) < |τ|`, `ν_{1,2}² = ω_n²(1 ± ε − ξ²)`); `squareWave_centre_fundamental`;
  `energyBound_lt_firstOrder`; `squareWave_instance` (for `(40π² + 1)ξ² ≤ 1` and
  `T = 2π/(3ν)`, `ν = ω_n√(2(1 − ξ²)/5)`: a depth `ε_b ∈ (0, 3(1 − ξ²)/5)` with Hurwitz frozen
  matrices, a nonzero sustained `T`-antiperiodic solution without `Ωℤ` content, and no
  constant-`K_s` explanation of its angle — rule P½ classifies it correctly).
-/

noncomputable section
namespace powerlib.ForcedOscillation.Classification

open Complex Set Function Filter Topology Matrix
open powerlib.Synchronous.OscillationPhasor powerlib.Synchronous.ParametricSwing
open powerlib.SpecialFunctions.PeriodicWaves (coeff kernelExp coeff_eq_integral coeff_const_mul
  squareWave amp amp_squareWave_of_odd)

/-! ## The three mechanisms as data -/

/-- The excitation mechanism of an oscillation of the swing model (3-8)–(3-9): none (natural),
an additive mechanical power deviation `ΔP_m(t)` (forced), or a relative variation `p(t)` of the
synchronizing coefficient, `K_s(t) = K_s (1 + p(t))`, with `ΔP_m = 0` (parametric). -/
inductive Mechanism where
  | natural
  | forced (Pm : ℝ → ℝ)
  | parametric (pump : ℝ → ℝ)

namespace Mechanism

/-- The synchronizing coefficient `K_s(t)` of the mechanism (`p.Ks` its constant or mean value). -/
def Ks (p : Params) : Mechanism → ℝ → ℝ
  | natural => fun _ => p.Ks
  | forced _ => fun _ => p.Ks
  | parametric pump => fun t => p.Ks * (1 + pump t)

/-- The mechanical power deviation `ΔP_m(t)` of the mechanism. -/
def Pm : Mechanism → ℝ → ℝ
  | natural => fun _ => 0
  | forced Pm => Pm
  | parametric _ => fun _ => 0

end Mechanism

variable {p : Params}

/-! ## Harmonic balance of a sustained oscillation with constant synchronizing coefficient -/

/-- **Harmonic balance.** For a solution of `M Δδ̈ + D Δδ̇ + K_s Δδ = ΔP_m` (constant `K_s`,
continuous `ΔP_m`) that closes over `[0, L]` (`Δδ`, `Δδ̇` equal at `0` and `L`), every Fourier
coefficient obeys the phasor relation of the sinusoidal steady state:
`c_m(ΔP_m) = F(Ω_m, c_m(Δδ)) = (K_s − M Ω_m² + jΩ_m D) c_m(Δδ)`, `Ω_m = 2πm/L`
(`OscillationPhasor.Params.mechPhasor`). -/
@[tmio M, powerlib_domain] theorem harmonic_balance (hM : p.M ≠ 0) {L : ℝ} (hL : 0 < L)
    {Pm δ δ' δ'' : ℝ → ℝ} (hPm : Continuous Pm) (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + p.Ks * δ t = Pm t) (h0 : δ L = δ 0)
    (h1 : δ' L = δ' 0) (m : ℤ) :
    coeff hL Pm m = p.mechPhasor (2 * Real.pi * m / L) (coeff hL δ m) := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun t => (hδ t).continuousAt
  have hδ'c : Continuous δ' := continuous_iff_continuousAt.2 fun t => (hδ' t).continuousAt
  have hδ''e : δ'' = fun t => (Pm t - p.D * δ' t - p.Ks * δ t) / p.M := by
    funext t
    field_simp
    linarith [heq t]
  have hδ''c : Continuous δ'' := by rw [hδ''e]; fun_prop
  have hk : -kernelExp L m = ((2 * Real.pi * m / L : ℝ) : ℂ) * I := by
    simp only [kernelExp]; push_cast; ring
  have c1 := LTI.HarmonicTransfer.coeff_deriv hL hδ hδ'c h0 m
  have c2 := LTI.HarmonicTransfer.coeff_deriv hL hδ' hδ''c h1 m
  rw [hk] at c1 c2
  have hPm' : Pm = fun t => (p.M * δ'' t + p.D * δ' t) + p.Ks * δ t := by
    funext t; exact (heq t).symm
  have hsplit := LTI.HarmonicTransfer.coeff_add hL (f := fun t => p.M * δ'' t + p.D * δ' t)
    (g := fun t => p.Ks * δ t) (by fun_prop) (by fun_prop) m
  have hsplit' := LTI.HarmonicTransfer.coeff_add hL (f := fun t => p.M * δ'' t)
    (g := fun t => p.D * δ' t) (by fun_prop) (by fun_prop) m
  rw [hPm', hsplit, hsplit', coeff_const_mul, coeff_const_mul, coeff_const_mul, c2, c1,
    Params.mechPhasor]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- With nonzero damping (`ξ ≠ 0`) and a constant synchronizing coefficient, a harmonic
`m ≠ 0` of a sustained oscillation is present only if it is present in `ΔP_m`: the oscillation
has no frequency of its own. -/
@[tmio M, powerlib_domain] theorem coeff_eq_zero_of_const (hM : p.M ≠ 0) (hω₀ : p.ω₀ ≠ 0)
    (hD : p.D ≠ 0) {L : ℝ} (hL : 0 < L) {Pm δ δ' δ'' : ℝ → ℝ} (hPm : Continuous Pm)
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + p.Ks * δ t = Pm t) (h0 : δ L = δ 0)
    (h1 : δ' L = δ' 0) {m : ℤ} (hm : m ≠ 0) (hPm0 : coeff hL Pm m = 0) : coeff hL δ m = 0 := by
  by_contra hne
  have hΩ : 2 * Real.pi * m / L ≠ 0 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have := Real.pi_pos.ne'
    have := hL.ne'
    positivity
  have hF := (harmonic_balance hM hL hPm hδ hδ' heq h0 h1 m).symm.trans hPm0
  have hK := ((p.mechPhasor_eq_zero_iff hω₀ hΩ hne).mp hF).1
  apply hD
  rw [Params.D, hK, zero_div]

/-! ## The half-frequency rule: no constant-stiffness explanation -/

@[tmio T, powerlib_foundation] private theorem deriv_antiperiodic {T : ℝ} {δ δ' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hanti : ∀ t, 0 ≤ t → δ (t + T) = -δ t) {t : ℝ}
    (ht : 0 < t) : δ' (t + T) = -δ' t := by
  have h1 := (hδ (t + T)).comp_add_const t T
  have hev : (fun s => δ (s + T)) =ᶠ[𝓝 t] fun s => -δ s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hanti s (le_of_lt hs)
  exact h1.unique ((hδ t).neg.congr_of_eventuallyEq hev)

/-- **Half-frequency rule (exclusion).** With nonzero damping, a model with constant
synchronizing coefficient — natural (`ΔP_m = 0`) or forced by a `T`-periodic `ΔP_m` (content at
`Ωℤ` only, `Ω = 2π/T`) — has no nonzero `T`-antiperiodic oscillation on `[0, ∞)`: every solution
with `Δδ(t + T) = −Δδ(t)` for `t ≥ 0` vanishes there. A sustained oscillation at the half-integer
frequencies `(k + ½)Ω` is therefore neither natural nor forced. -/
@[tmio M, powerlib_domain] theorem halfFrequency_eq_zero_of_const (hM : p.M ≠ 0)
    (hω₀ : p.ω₀ ≠ 0) (hD : p.D ≠ 0) {T : ℝ} (hT : 0 < T) {Pm δ δ' δ'' : ℝ → ℝ}
    (hPm : Continuous Pm) (hPmT : Periodic Pm T) (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + p.Ks * δ t = Pm t)
    (hanti : ∀ t, 0 ≤ t → δ (t + T) = -δ t) : ∀ t, 0 ≤ t → δ t = 0 := by
  intro t₀ ht₀
  by_contra hne
  set s := t₀ + T with hs
  have hs0 : 0 < s := by linarith
  have hL : (0 : ℝ) < 2 * T := by linarith
  -- the window `[s, s + 2T]`
  set g : ℝ → ℝ := fun u => δ (s + u) with hg
  have hgd : ∀ u, HasDerivAt g (δ' (s + u)) u := fun u => (hδ (s + u)).comp_const_add s u
  have hgd' : ∀ u, HasDerivAt (fun u => δ' (s + u)) (δ'' (s + u)) u := fun u =>
    (hδ' (s + u)).comp_const_add s u
  have hgeq : ∀ u, p.M * δ'' (s + u) + p.D * δ' (s + u) + p.Ks * g u = Pm (s + u) :=
    fun u => heq (s + u)
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun t => (hδ t).continuousAt
  have hgc : Continuous g := hδc.comp (continuous_const.add continuous_id)
  have hg0 : g (2 * T) = g 0 := by
    simp only [hg, add_zero]
    rw [show s + 2 * T = (s + T) + T by ring, hanti _ (by linarith), hanti _ hs0.le, neg_neg]
  have hg1 : δ' (s + 2 * T) = δ' (s + 0) := by
    rw [add_zero, show s + 2 * T = (s + T) + T by ring, deriv_antiperiodic hδ hanti (by linarith),
      deriv_antiperiodic hδ hanti hs0, neg_neg]
  have hPc : Continuous fun u => Pm (s + u) := hPm.comp (continuous_const.add continuous_id)
  -- every coefficient of the window vanishes
  have hall : ∀ m : ℤ, coeff hL g m = 0 := by
    intro m
    rcases Int.even_or_odd m with he | ho
    · have h := ParametricResonance.Signature.coeff_eq_zero_of_antiperiodic (f := g) hT
        hgc.continuousOn (fun u hu => by
          simp only [hg]
          rw [show s + (u + T) = (s + u) + T by ring,
            hanti _ (by linarith [show (0 : ℝ) ≤ u from hu])])
        he
      exact h
    · have hPodd := ParametricResonance.Signature.coeff_eq_zero_of_periodic
        (f := fun u => Pm (s + u)) hT hPc.continuousOn (fun u _ => by
          rw [show s + (u + T) = (s + u) + T by ring, hPmT]) ho
      exact coeff_eq_zero_of_const hM hω₀ hD hL hPc hgd hgd' hgeq hg0 hg1
        (by rintro rfl; exact (Int.not_even_iff_odd.mpr ho) ⟨0, by norm_num⟩) hPodd
  -- Parseval: the window carries no energy, but `g(T) = δ(t₀) ≠ 0`
  have hpar := ParametricResonance.Wirtinger.hasSum_sq_coeff hL hgc
  have hzero : ((2 * T)⁻¹ * ∫ u in (0 : ℝ)..2 * T, g u ^ 2) = 0 := by
    refine hpar.unique ?_
    simp [hall]
  have hgT : g T ≠ 0 := by
    simp only [hg]
    rw [hs, show t₀ + T + T = t₀ + T + T by ring, hanti _ (by linarith), hanti _ ht₀, neg_neg]
    exact hne
  have hpos : 0 < ∫ u in (0 : ℝ)..2 * T, g u ^ 2 :=
    intervalIntegral.integral_pos hL (by fun_prop) (fun u _ => sq_nonneg _)
      ⟨T, ⟨hT.le, by linarith⟩, by positivity⟩
  have : (2 * T)⁻¹ * ∫ u in (0 : ℝ)..2 * T, g u ^ 2 > 0 := by positivity
  linarith

/-! ## Sound decision rules -/

@[tmio M, powerlib_domain] private theorem M_ne_zero (hp : p.Pos) : p.M ≠ 0 := by
  have := hp.H; have := hp.ω₀
  rw [Params.M]; positivity

@[tmio T, powerlib_foundation] private theorem closes {L : ℝ} {δ δ' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hper : Periodic δ L) : δ L = δ 0 ∧ δ' L = δ' 0 := by
  have h1 := ParametricResonance.EnergyBalance.periodic_of_hasDerivAt hδ hper 0
  have h0 := hper 0
  rw [zero_add] at h0 h1
  exact ⟨h0, h1⟩

/-- **Rule P (parametric).** Nonzero damping, and a sustained (`L`-periodic) oscillation with
a harmonic `m ≠ 0` that is absent from the mechanical power: whatever the mechanism, it is
parametric, with a synchronizing coefficient that genuinely varies in time. -/
@[tmio M, powerlib_domain] theorem classify_parametric (hp : p.Pos) (hD : p.D ≠ 0)
    (e : Mechanism) (hPm : Continuous e.Pm) {L : ℝ} (hL : 0 < L) {δ δ' δ'' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + e.Ks p t * δ t = e.Pm t) (hper : Periodic δ L)
    {m : ℤ} (hm : m ≠ 0) (hδm : coeff hL δ m ≠ 0) (hPm0 : coeff hL e.Pm m = 0) :
    ∃ pump : ℝ → ℝ, e = .parametric pump ∧ ∃ t, pump t ≠ pump 0 := by
  obtain ⟨h0, h1⟩ := closes hδ hper
  have key : ∀ k, (∀ t, e.Ks p t = k) → False := by
    intro k hk
    have heq' : ∀ t, ({ p with Ks := k } : Params).M * δ'' t +
        ({ p with Ks := k } : Params).D * δ' t + ({ p with Ks := k } : Params).Ks * δ t =
          e.Pm t := fun t => by
      show p.M * δ'' t + p.D * δ' t + k * δ t = e.Pm t
      rw [← hk t]; exact heq t
    exact hδm (coeff_eq_zero_of_const (p := { p with Ks := k }) (M_ne_zero (p := p) hp)
      hp.ω₀.ne' hD hL hPm hδ hδ' heq' h0 h1 hm hPm0)
  cases e with
  | natural => exact (key p.Ks fun _ => rfl).elim
  | forced Pm => exact (key p.Ks fun _ => rfl).elim
  | parametric pump =>
    refine ⟨pump, rfl, ?_⟩
    by_contra h
    push Not at h
    exact key (p.Ks * (1 + pump 0)) fun t => by simp only [Mechanism.Ks, h t]

/-- **Rule P½ (half-frequency).** Nonzero damping, a mechanical power with content at `Ωℤ`
only (`T`-periodic, `Ω = 2π/T` the candidate pump frequency), and a nonzero oscillation that is
`T`-antiperiodic on `[0, ∞)` (content at `(k + ½)Ω` only): the mechanism is parametric with a
time-varying synchronizing coefficient. -/
@[tmio M, powerlib_domain] theorem classify_halfFrequency (hp : p.Pos) (hD : p.D ≠ 0)
    (e : Mechanism) (hPm : Continuous e.Pm) {T : ℝ} (hT : 0 < T) (hPmT : Periodic e.Pm T)
    {δ δ' δ'' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + e.Ks p t * δ t = e.Pm t)
    (hanti : ∀ t, 0 ≤ t → δ (t + T) = -δ t) (hne : ∃ t, 0 ≤ t ∧ δ t ≠ 0) :
    ∃ pump : ℝ → ℝ, e = .parametric pump ∧ ∃ t, pump t ≠ pump 0 := by
  obtain ⟨t₀, ht₀, hne⟩ := hne
  have key : ∀ k, (∀ t, e.Ks p t = k) → False := by
    intro k hk
    have heq' : ∀ t, ({ p with Ks := k } : Params).M * δ'' t +
        ({ p with Ks := k } : Params).D * δ' t + ({ p with Ks := k } : Params).Ks * δ t =
          e.Pm t := fun t => by
      show p.M * δ'' t + p.D * δ' t + k * δ t = e.Pm t
      rw [← hk t]; exact heq t
    exact hne (halfFrequency_eq_zero_of_const (p := { p with Ks := k }) (M_ne_zero (p := p) hp)
      hp.ω₀.ne' hD hT hPm hPmT hδ hδ' heq' hanti t₀ ht₀)
  cases e with
  | natural => exact (key p.Ks fun _ => rfl).elim
  | forced Pm => exact (key p.Ks fun _ => rfl).elim
  | parametric pump =>
    refine ⟨pump, rfl, ?_⟩
    by_contra h
    push Not at h
    exact key (p.Ks * (1 + pump 0)) fun t => by simp only [Mechanism.Ks, h t]

/-- **Rule F (forced).** Nonzero damping, a constant synchronizing coefficient and a sustained
(nonconstant `L`-periodic) oscillation: the mechanism is forced, the mechanical power supplies
exactly the dissipated energy, `∫₀ᴸ ΔP_m Δδ̇ = D ∫₀ᴸ Δδ̇²`, and every harmonic `m ≠ 0` of the
oscillation is present in `ΔP_m`. -/
@[tmio M, powerlib_domain] theorem classify_forced (hp : p.Pos) (hD : p.D ≠ 0) (e : Mechanism)
    (hPm : Continuous e.Pm) {L : ℝ} (hL : 0 < L) {δ δ' δ'' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + e.Ks p t * δ t = e.Pm t) (hper : Periodic δ L)
    (hnc : ∃ t, δ t ≠ δ 0) (hconst : ∀ t, e.Ks p t = e.Ks p 0) :
    ∃ Pm : ℝ → ℝ, e = .forced Pm ∧
      ∫ t in (0 : ℝ)..L, Pm t * δ' t = p.D * ∫ t in (0 : ℝ)..L, δ' t ^ 2 ∧
      ∀ m : ℤ, m ≠ 0 → coeff hL δ m ≠ 0 → coeff hL Pm m ≠ 0 := by
  obtain ⟨h0, h1⟩ := closes hδ hper
  have hfree : ∀ k, (∀ t, e.Ks p t = k) → (∀ t, e.Pm t = 0) → False := by
    intro k hk hz
    exact hD (ParametricResonance.EnergyBalance.natural_damping_eq_zero (k := k) hδ hδ'
      (fun t => by rw [← hk t, ← hz t]; exact heq t) hL hper hnc)
  cases e with
  | natural => exact (hfree p.Ks (fun _ => rfl) fun _ => rfl).elim
  | parametric pump => exact (hfree _ hconst fun _ => rfl).elim
  | forced Pm =>
    refine ⟨Pm, rfl, ParametricResonance.EnergyBalance.forced_balance (k := p.Ks) hδ hδ' hPm heq
      hper, fun m hm hδm hPm0 => hδm ?_⟩
    exact coeff_eq_zero_of_const (M_ne_zero hp) hp.ω₀.ne' hD hL hPm hδ hδ' heq h0 h1 hm hPm0

/-- **Rule N (natural).** A constant synchronizing coefficient and a sustained oscillation with a
harmonic `m ≠ 0` absent from the mechanical power: the oscillation is an undamped natural mode,
`K_d + K_D = 0` (`ξ = 0`) and `2HΩ_m² = ω₀ K_s`, `Ω_m = 2πm/L` (the natural frequency). -/
@[tmio M, powerlib_domain] theorem classify_natural (hp : p.Pos) (e : Mechanism)
    (hPm : Continuous e.Pm) {L : ℝ} (hL : 0 < L) {δ δ' δ'' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + e.Ks p t * δ t = e.Pm t) (hper : Periodic δ L)
    (hconst : ∀ t, e.Ks p t = e.Ks p 0) {m : ℤ} (hm : m ≠ 0) (hδm : coeff hL δ m ≠ 0)
    (hPm0 : coeff hL e.Pm m = 0) :
    p.Kd + p.KD = 0 ∧ 2 * p.H * (2 * Real.pi * m / L) ^ 2 = p.ω₀ * e.Ks p 0 := by
  obtain ⟨h0, h1⟩ := closes hδ hper
  have heq' : ∀ t, ({ p with Ks := e.Ks p 0 } : Params).M * δ'' t +
      ({ p with Ks := e.Ks p 0 } : Params).D * δ' t +
        ({ p with Ks := e.Ks p 0 } : Params).Ks * δ t = e.Pm t := fun t => by
    show p.M * δ'' t + p.D * δ' t + e.Ks p 0 * δ t = e.Pm t
    rw [← hconst t]; exact heq t
  have hF := (harmonic_balance (p := { p with Ks := e.Ks p 0 }) (M_ne_zero (p := p) hp) hL hPm
    hδ hδ' heq' h0 h1 m).symm.trans hPm0
  have hΩ : 2 * Real.pi * m / L ≠ 0 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have := Real.pi_pos.ne'
    have := hL.ne'
    positivity
  exact (Params.mechPhasor_eq_zero_iff (p := { p with Ks := e.Ks p 0 }) hp.ω₀.ne' hΩ hδm).mp hF

/-! ## Signatures of the three mechanisms -/

/-- **Natural signature.** A sustained (nonconstant `L`-periodic) natural oscillation has
`ξ = 0`, and its harmonics `m ≠ 0` lie at the natural frequency, `Ω_m² = ω_n²`
(`ω_n = √(ω₀K_s/(2H))`): no excitation frequency exists. -/
@[tmio M, powerlib_domain] theorem natural_signature (hp : p.Pos) {L : ℝ} (hL : 0 < L)
    {δ δ' δ'' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + Mechanism.natural.Ks p t * δ t =
      Mechanism.natural.Pm t) (hper : Periodic δ L) (hnc : ∃ t, δ t ≠ δ 0) :
    p.dampingRatio = 0 ∧
      ∀ m : ℤ, m ≠ 0 → coeff hL δ m ≠ 0 → (2 * Real.pi * m / L) ^ 2 = natFreq p ^ 2 := by
  refine ⟨natural_dampingRatio_eq_zero hp hδ hδ' (fun t => (p.swing_iff (δ t) (δ' t) (δ'' t) 0).mpr
    (heq t)) hL hper (by
      obtain ⟨t, ht⟩ := hnc
      exact ⟨t, ht⟩), fun m hm hδm => ?_⟩
  have h := (classify_natural hp .natural continuous_const hL hδ hδ' heq hper (fun _ => rfl) hm
    hδm (by
      rw [coeff_eq_integral]
      simp [Mechanism.Pm])).2
  have hH := hp.H
  have hK : 0 ≤ p.ω₀ * p.Ks / (2 * p.H) := by have := hp.ω₀; have := hp.Ks; positivity
  rw [natFreq, Real.sq_sqrt hK, eq_div_iff (by positivity)]
  simp only [Mechanism.Ks] at h
  linear_combination h

/-- **Forced signature.** A sustained oscillation of the forced mechanism (constant `K_s`,
continuous `ΔP_m`) with positive damping `K_d + K_D > 0`: every harmonic satisfies
`c_m(ΔP_m) = (K_s − MΩ_m² + jΩ_m D) c_m(Δδ)`, so `|c_m(Δδ)| = |c_m(ΔP_m)|/|K_s − MΩ_m² + jΩ_m D|`
(linear in `ΔP_m`, present only where `ΔP_m` is), and the energy enters through `ΔP_m`:
`∫₀ᴸ ΔP_m Δω = (K_d + K_D) ∫₀ᴸ Δω² > 0`. -/
@[tmio M, powerlib_domain] theorem forced_signature (hp : p.Pos) (hξ : 0 < p.Kd + p.KD)
    {Pm : ℝ → ℝ} (hPm : Continuous Pm) {L : ℝ} (hL : 0 < L) {δ δ' δ'' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + (Mechanism.forced Pm).Ks p t * δ t =
      (Mechanism.forced Pm).Pm t) (hper : Periodic δ L) (hnc : ∃ t, δ t ≠ δ 0) :
    (∀ m : ℤ, ‖coeff hL δ m‖ = ‖coeff hL Pm m‖ /
        ‖((p.Ks - p.M * (2 * Real.pi * m / L) ^ 2 : ℝ) : ℂ) +
          ((2 * Real.pi * m / L * p.D : ℝ) : ℂ) * I‖) ∧
      ∫ t in (0 : ℝ)..L, Pm t * speedDev p δ' t =
        (p.Kd + p.KD) * ∫ t in (0 : ℝ)..L, speedDev p δ' t ^ 2 ∧
      0 < ∫ t in (0 : ℝ)..L, Pm t * speedDev p δ' t := by
  obtain ⟨h0, h1⟩ := closes hδ hper
  have hω := hp.ω₀
  have hD : 0 < p.D := div_pos hξ hω
  refine ⟨fun m => ?_, ?_, ?_⟩
  · have hb := harmonic_balance (M_ne_zero hp) hL hPm hδ hδ' heq h0 h1 m
    have hZ : ((p.Ks - p.M * (2 * Real.pi * m / L) ^ 2 : ℝ) : ℂ) +
        ((2 * Real.pi * m / L * p.D : ℝ) : ℂ) * I ≠ 0 := by
      intro hz
      have him : 2 * Real.pi * m / L * p.D = 0 := by
        have := congrArg Complex.im hz
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, Complex.zero_im] at this
        linarith
      have hre : p.Ks - p.M * (2 * Real.pi * m / L) ^ 2 = 0 := by
        have := congrArg Complex.re hz
        simp only [Complex.add_re, Complex.ofReal_im, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, Complex.zero_re] at this
        linarith
      rcases mul_eq_zero.mp him with h | h
      · rw [h] at hre
        simp at hre
        exact hp.Ks.ne' hre
      · exact hD.ne' h
    have := forced_amplitude (p := p) (Dδ := coeff hL δ m) hZ
    rw [this, ← hb]
  · have hb := ParametricResonance.EnergyBalance.forced_balance (k := p.Ks) hδ hδ' hPm heq hper
    simp only [speedDev]
    have e1 : ∫ t in (0 : ℝ)..L, Pm t * (δ' t / p.ω₀) =
        (∫ t in (0 : ℝ)..L, Pm t * δ' t) / p.ω₀ := by
      rw [← intervalIntegral.integral_div]; congr 1; funext t; ring
    have e2 : ∫ t in (0 : ℝ)..L, (δ' t / p.ω₀) ^ 2 = (∫ t in (0 : ℝ)..L, δ' t ^ 2) / p.ω₀ ^ 2 := by
      rw [← intervalIntegral.integral_div]; congr 1; funext t; ring
    rw [e1, e2, hb, Params.D]
    field_simp
  · have hpos := ParametricResonance.EnergyBalance.forced_supply_pos (k := p.Ks) hδ hδ' hPm heq hL
      hper hnc hD
    simp only [speedDev]
    have e1 : ∫ t in (0 : ℝ)..L, Pm t * (δ' t / p.ω₀) =
        (∫ t in (0 : ℝ)..L, Pm t * δ' t) / p.ω₀ := by
      rw [← intervalIntegral.integral_div]; congr 1; funext t; ring
    rw [e1]
    exact div_pos hpos hω

/-- **Forced regime.** With positive damping and a `T`-periodic mechanical power (content at `Ωℤ`
only), the half-integer coefficients of every solution over the windows `[s, s + 2T]` tend to `0`:
a forced oscillation never sustains content at `(k + ½)Ω` (the state-space form (3-10) is Hurwitz,
`ParametricResonance.Signature.lti_tendsto_coeff_odd`). -/
@[tmio M, powerlib_domain] theorem forced_tendsto_coeff_odd (hp : p.Pos) (hξ : 0 < p.Kd + p.KD)
    {Pm : ℝ → ℝ} (hPm : Continuous Pm) {T : ℝ} (hT : 0 < T) (hPmT : Periodic Pm T)
    {δ δ' δ'' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + p.Ks * δ t = Pm t) {m : ℤ} (hm : Odd m) :
    Tendsto (fun s => coeff (mul_pos two_pos hT) (fun t => δ (s + t)) m) atTop (𝓝 0) := by
  have hM := M_ne_zero hp
  have hMpos : 0 < p.M := by have := hp.H; have := hp.ω₀; rw [Params.M]; positivity
  have hDpos : 0 < p.D := div_pos hξ hp.ω₀
  have hA : LinearSystems.IsHurwitz p.stateMatrix := by
    rw [Criteria.isHurwitz_fin_two_iff, Params.stateMatrix_eq, Matrix.trace_fin_two_of,
      Matrix.det_fin_two_of]
    constructor
    · have : 0 < p.D / p.M := div_pos hDpos hMpos
      rw [neg_div]; linarith
    · have : 0 < p.Ks / p.M := div_pos hp.Ks hMpos
      rw [neg_div, neg_div]; linarith
  have hx : ∀ t, HasDerivAt (fun t => ![δ t, δ' t])
      (p.stateMatrix *ᵥ ![δ t, δ' t] + ![0, Pm t / p.M]) t := by
    intro t
    have hs := (p.swing_iff_stateSpace hM (δ t) (δ' t) (δ'' t) (Pm t)).mp
      ((p.swing_iff (δ t) (δ' t) (δ'' t) (Pm t)).mpr (heq t))
    rw [← hs, hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hδ t
    · simpa using hδ' t
  have hg : Continuous fun t => ![(0 : ℝ), Pm t / p.M] := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using continuous_const
    · simpa using hPm.div_const p.M
  have hgP : Periodic (fun t => ![(0 : ℝ), Pm t / p.M]) T := fun t => by
    simp only [hPmT t]
  simpa using ParametricResonance.Signature.lti_tendsto_coeff_odd hA hT hg hgP hx 0 hm

/-- **Parametric signature at the principal boundary.** A nonzero `T`-antiperiodic solution
(a sustained oscillation at half the pump frequency) of the parametric mechanism
`K_s(t) = K_s (1 + p(t))` with a `C¹` `T`-periodic pump, `ΔP_m = 0`, `K_D = 0`, `K_d > 0`:
it has no Fourier content at `Ωℤ` over any window `[s, s + 2T]`; the energy is supplied by the
pump work, `K_d ∫ Δω² = (1/(2ω₀)) ∫ K̇_s Δδ² > 0`; and the in-phase part of the fundamental
phasors of `ΔP_e`, `Δω` is bounded by the harmonic tail (the phase-angle method reads
`φ ≈ π/2`, i.e. `ξ ≈ 0`, although `K_d > 0`). -/
@[tmio M, powerlib_domain] theorem parametric_signature (hp : p.Pos) (hKD : p.KD = 0)
    (hKd : 0 < p.Kd) {pump pump' : ℝ → ℝ} (hpump : ∀ t, HasDerivAt pump (pump' t) t)
    (hpump' : Continuous pump') {T : ℝ} (hT : 0 < T) (hpT : Periodic pump T)
    {δ δ' δ'' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + (Mechanism.parametric pump).Ks p t * δ t =
      (Mechanism.parametric pump).Pm t)
    (hanti : Antiperiodic δ T) (hne : ∃ t, δ t ≠ 0) :
    (∀ s : ℝ, ∀ m : ℤ, Even m → coeff (mul_pos two_pos hT) (fun t => δ (s + t)) m = 0) ∧
      p.Kd * ∫ t in (0 : ℝ)..2 * T, speedDev p δ' t ^ 2 =
        (∫ t in (0 : ℝ)..2 * T, p.Ks * pump' t * δ t ^ 2) / (2 * p.ω₀) ∧
      0 < ∫ t in (0 : ℝ)..2 * T, p.Ks * pump' t * δ t ^ 2 ∧
      |‖coeff (mul_pos two_pos hT) (elecPower p (Mechanism.Ks p (.parametric pump)) δ δ') 1‖ *
          ‖coeff (mul_pos two_pos hT) (speedDev p δ') 1‖ *
          Real.cos (lagAngle (coeff (mul_pos two_pos hT) (speedDev p δ') 1)
            (coeff (mul_pos two_pos hT)
              (elecPower p (Mechanism.Ks p (.parametric pump)) δ δ') 1))| ≤
        ∑' n : ℕ, ‖coeff (mul_pos two_pos hT)
            (elecPower p (Mechanism.Ks p (.parametric pump)) δ δ') ((n : ℤ) + 2)‖ *
          ‖coeff (mul_pos two_pos hT) (speedDev p δ') ((n : ℤ) + 2)‖ := by
  have hω := hp.ω₀
  have hKs : ∀ t, HasDerivAt (Mechanism.Ks p (.parametric pump)) (p.Ks * pump' t) t := by
    intro t
    have h := ((hpump t).const_add 1).const_mul p.Ks
    simpa [Mechanism.Ks] using h
  have hKs' : Continuous fun t => p.Ks * pump' t := continuous_const.mul hpump'
  have hKsT : Periodic (Mechanism.Ks p (.parametric pump)) T := fun t => by
    simp only [Mechanism.Ks, hpT t]
  have heq' : ∀ t, 2 * p.H / p.ω₀ * δ'' t + p.KD / p.ω₀ * δ' t =
      0 - elecPower p (Mechanism.Ks p (.parametric pump)) δ δ' t :=
    (modulated_iff _ (fun _ => 0) δ δ' δ'').mpr heq
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun t => (hδ t).continuousAt
  have hδL := hanti.periodic_two_mul
  have hKsL : Periodic (Mechanism.Ks p (.parametric pump)) (2 * T) := by
    rw [two_mul]; exact hKsT.add_period hKsT
  have hbal := parametric_power_balance hω.ne' hKs hKs' hδ hδ' heq' hδL hKsL
  rw [hKD, add_zero] at hbal
  refine ⟨fun s m hm => ?_, hbal, ?_, halfFrequency_inPhase_le hω.ne' hKD (mul_pos two_pos hT)
    hKs hKs' hδ hδ' heq' hanti hKsT⟩
  · refine ParametricResonance.Signature.coeff_eq_zero_of_antiperiodic
      (f := fun t => δ (s + t)) hT (hδc.comp (continuous_const.add continuous_id)).continuousOn
      (fun t _ => ?_) hm
    show δ (s + (t + T)) = -δ (s + t)
    rw [show s + (t + T) = (s + t) + T by ring, hanti]
  · -- the oscillation is nonconstant, so `∫ Δω² > 0`
    have hnc : ∃ t, δ t ≠ δ 0 := by
      obtain ⟨t, ht⟩ := hne
      by_cases h0 : δ 0 = 0
      · exact ⟨t, by rw [h0]; exact ht⟩
      · exact ⟨T, by rw [show T = 0 + T by ring, hanti 0]; intro h; exact h0 (by linarith)⟩
    have hpos := ParametricResonance.EnergyBalance.integral_sq_deriv_pos hδ
      (continuous_iff_continuousAt.2 fun t => (hδ' t).continuousAt) (by linarith) hδL hnc
    have hW : 0 < ∫ t in (0 : ℝ)..2 * T, speedDev p δ' t ^ 2 := by
      have e : ∫ t in (0 : ℝ)..2 * T, speedDev p δ' t ^ 2 =
          (∫ t in (0 : ℝ)..2 * T, δ' t ^ 2) / p.ω₀ ^ 2 := by
        rw [← intervalIntegral.integral_div]; congr 1; funext t; simp only [speedDev]; ring
      rw [e]; positivity
    have : 0 < (∫ t in (0 : ℝ)..2 * T, p.Ks * pump' t * δ t ^ 2) / (2 * p.ω₀) := by
      rw [← hbal]; positivity
    have h2 : 0 < 2 * p.ω₀ := by positivity
    exact (div_pos_iff_of_pos_right h2).mp this

section StartUp

open scoped Matrix.Norms.Operator

/-- **The start-up method misreads a parametric oscillation as natural.** A real Floquet mode
`x(t) = Φ(t, 0) w`, `M w = μ w`, `|μ| > 1`, of the parametric swing model (continuous
`T`-periodic pump, state `(Δδ, Δδ̇)`): TR-110's start-up slope of the angle `Δδ` is `ln |μ| > 0`,
so the threshold classifier never answers "forced" and answers "natural" iff `ε < ln |μ|`. -/
@[tmio M, powerlib_domain] theorem parametric_startUp {pump : ℝ → ℝ}
    (hpump : Continuous pump) {T : ℝ} (hT : 0 < T) (hpT : Periodic pump T) {μ : ℝ}
    (hμ : 1 < |μ|) {w : Fin 2 → ℝ}
    (hw : Periodic.monodromy (fun t => (frozen p (Mechanism.Ks p (.parametric pump)) t).stateMatrix)
      T 0 *ᵥ w = μ • w)
    (hne : ∃ t ∈ Icc 0 T, (Periodic.transition
      (fun t => (frozen p (Mechanism.Ks p (.parametric pump)) t).stateMatrix) t 0 *ᵥ w) 0 ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 2 ≤ N) :
    let δ := fun t => (Periodic.transition
      (fun t => (frozen p (Mechanism.Ks p (.parametric pump)) t).stateMatrix) t 0 *ᵥ w) 0
    let S := LTI.StartUp.olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
      Real.log (LTI.StartUp.peakToPeak δ (i * T) ((i + 1) * T) -
        LTI.StartUp.peakToPeak δ ((i - 1) * T) (i * T)))
    LTI.StartUp.classify ε S ≠ .forced ∧
      (LTI.StartUp.classify ε S = .natural ↔ ε < Real.log |μ|) := by
  intro δ S
  set A := fun t => (frozen p (Mechanism.Ks p (.parametric pump)) t).stateMatrix with hAdef
  have hAc : Continuous A := by
    have h : A = fun t => !![0, 1; -(p.Ks * (1 + pump t)) / p.M, -p.D / p.M] := by
      funext t
      rw [hAdef]
      simp only [Params.stateMatrix_eq]
      rfl
    rw [h]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hAP : Periodic A T := fun t => by
    simp only [hAdef, frozen, Mechanism.Ks, hpT t]
  have hΦ : Continuous fun t => Periodic.transition A t 0 := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (Dynamics.stm_hasDerivAt hAc t 0).continuousAt
  have hδc : Continuous δ := (continuous_apply 0).comp (hΦ.matrix_mulVec continuous_const)
  have hmode : ∀ t, 0 ≤ t → δ (t + T) = μ * δ t := by
    intro t ht
    have h := Periodic.transition_mulVec_add_period hAc hAP hT hw ht
    have := congrFun h 0
    simpa [δ] using this
  exact ParametricResonance.Signature.classify_floquet hT hμ hδc.continuousOn hmode hne hε hN

end StartUp

/-! ## A worked instance: the square-wave synchronizing coefficient -/

/-- The state matrix (3-10) with a time-varying synchronizing coefficient is the damped
oscillator matrix with damping `D/(2M)` and stiffness `K_s(t)/M`. -/
@[tmio M, powerlib_domain] theorem frozen_stateMatrix (Ks : ℝ → ℝ) (t : ℝ) :
    (frozen p Ks t).stateMatrix = Periodic.oscMatrix (p.D / (2 * p.M)) (Ks t / p.M) := by
  rw [Params.stateMatrix_eq, Periodic.oscMatrix]
  show !![0, 1; -Ks t / p.M, -p.D / p.M] = !![0, 1; -(Ks t / p.M), -(2 * (p.D / (2 * p.M)))]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

@[tmio M, powerlib_domain] private theorem natFreq_pos (hp : p.Pos) : 0 < natFreq p := by
  have := hp.H; have := hp.ω₀; have := hp.Ks
  exact Real.sqrt_pos.mpr (by positivity)

@[tmio M, powerlib_domain] theorem natFreq_sq (hp : p.Pos) : natFreq p ^ 2 = p.Ks / p.M := by
  have := hp.H; have := hp.ω₀; have := hp.Ks
  rw [natFreq, Real.sq_sqrt (by positivity), Params.M]
  field_simp

/-- The damping of the oscillator form is `D/(2M) = ξ ω_n`. -/
@[tmio M, powerlib_domain] theorem oscDamping_eq (hp : p.Pos) :
    p.D / (2 * p.M) = p.dampingRatio * natFreq p := by
  have hn : 0 < natFreq p := natFreq_pos hp
  have hK := hp.Ks
  have hM : 0 < p.M := by have := hp.H; have := hp.ω₀; rw [Params.M]; positivity
  have h := dampingRatio_div_natFreq hp
  have e : p.dampingRatio = p.D / (2 * p.Ks) * natFreq p := by
    rw [← h]; field_simp
  rw [e, mul_assoc, ← sq, natFreq_sq hp]
  field_simp

/-- The swing model with the square-wave synchronizing coefficient
`K_s(t) = K_s (1 + squareWave ε T t)` is the Meissner equation with damping `c = ξ ω_n` and
`ω₀ = ω_n` (`ParametricResonance.Meissner.stiffness`). -/
@[tmio M, powerlib_domain] theorem squareWave_stateMatrix (hp : p.Pos) (ε T t : ℝ) :
    (frozen p (Mechanism.Ks p (.parametric (squareWave ε T))) t).stateMatrix =
      Periodic.oscMatrix (p.dampingRatio * natFreq p)
        (ParametricResonance.Meissner.stiffness (natFreq p) ε T t) := by
  rw [frozen_stateMatrix, oscDamping_eq hp, ParametricResonance.Meissner.stiffness, natFreq_sq hp]
  simp only [Mechanism.Ks]
  congr 1
  ring

/-- **The exact square-wave boundary in TR-110's variables.** For the swing model with
`K_s(t) = K_s (1 + squareWave ε T t)` and `ν_{1,2}² = ω_n²(1 ± ε − ξ²)`: the Meissner monodromy
`M` maps `y(nT)` to `y((n + 1)T)` for every solution of the state equation, `det M = e^{−2ξω_n T}`,
and some multiplier lies outside the unit circle iff `2 cosh(ξ ω_n T) < |τ|`,
`τ = 2 cos θ₁ cos θ₂ − (ν₁/ν₂ + ν₂/ν₁) sin θ₁ sin θ₂`, `θ_i = ν_i T/2`. -/
@[tmio M, powerlib_domain] theorem squareWave_boundary (hp : p.Pos) (hξ : 0 ≤ p.dampingRatio)
    {ε T ν₁ ν₂ : ℝ} (hT : 0 < T) (hν₁ : ν₁ ^ 2 = natFreq p ^ 2 * (1 + ε - p.dampingRatio ^ 2))
    (hν₂ : ν₂ ^ 2 = natFreq p ^ 2 * (1 - ε - p.dampingRatio ^ 2)) (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) :
    (∀ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Ici 0) →
      (∀ t, 0 ≤ t → HasDerivWithinAt y
        ((frozen p (Mechanism.Ks p (.parametric (squareWave ε T))) t).stateMatrix *ᵥ y t)
          (Ici t) t) →
      ∀ n : ℕ, y ((n + 1) * T) = ParametricResonance.Meissner.meissnerMonodromy
        (p.dampingRatio * natFreq p) (natFreq p) ε T *ᵥ y (n * T)) ∧
      (ParametricResonance.Meissner.meissnerMonodromy (p.dampingRatio * natFreq p) (natFreq p) ε
        T).det = Real.exp (-(2 * (p.dampingRatio * natFreq p)) * T) ∧
      ((∃ μ ∈ spectrum ℂ ((ParametricResonance.Meissner.meissnerMonodromy
          (p.dampingRatio * natFreq p) (natFreq p) ε T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔
        2 * Real.cosh (p.dampingRatio * natFreq p * T) <
          |ParametricResonance.Meissner.reducedTrace ν₁ ν₂ T|) := by
  have hn : 0 ≤ natFreq p := Real.sqrt_nonneg _
  refine ⟨fun y hyc hyd n => ?_, ParametricResonance.Meissner.det_meissnerMonodromy _ _ _ _, ?_⟩
  · simp only [squareWave_stateMatrix hp] at hyd
    exact ParametricResonance.Meissner.solution_period hT hyc hyd n
  · exact ParametricResonance.Meissner.floquetUnstable_iff (by rw [hν₁]; ring) (by rw [hν₂]; ring)
      h₁ h₂ (mul_nonneg hξ hn) hT

/-- **The square wave against the sinusoidal thresholds.** At the centre of the principal
tongue (`Ω = ν₁ + ν₂`), instability of the square-wave swing model requires the fundamental of
the modulation, of amplitude `4|ε|/π`, to exceed `4ξ √(ν₁ν₂)/ω_n`: the first-order sinusoidal
threshold `4ξ` (`ParametricSwing.firstOrder_unstable` at zero detuning) up to the factor
`√(ν₁ν₂)/ω_n → 1`. -/
@[tmio M, powerlib_domain] theorem squareWave_centre_fundamental (hp : p.Pos)
    (hξ : 0 ≤ p.dampingRatio) {ε T ν₁ ν₂ : ℝ} (hT : 0 < T) (hε : 0 ≤ ε)
    (hν₁ : ν₁ ^ 2 = natFreq p ^ 2 * (1 + ε - p.dampingRatio ^ 2))
    (hν₂ : ν₂ ^ 2 = natFreq p ^ 2 * (1 - ε - p.dampingRatio ^ 2)) (h₁ : 0 < ν₁) (h₂ : 0 < ν₂)
    (hTc : T = 2 * Real.pi / (ν₁ + ν₂))
    (hu : ∃ μ ∈ spectrum ℂ ((ParametricResonance.Meissner.meissnerMonodromy
      (p.dampingRatio * natFreq p) (natFreq p) ε T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) :
    4 * p.dampingRatio * √(ν₁ * ν₂) / natFreq p < amp hT (squareWave ε T) 1 := by
  have hn : 0 < natFreq p := natFreq_pos hp
  have h := ParametricResonance.Meissner.centre_threshold_lower (by rw [hν₁]; ring)
    (by rw [hν₂]; ring) h₁ h₂ (mul_nonneg hξ hn.le) hε hTc hu
  rw [show (1 : ℕ) = 1 from rfl, amp_squareWave_of_odd hT ε odd_one, abs_of_nonneg hε]
  push_cast
  have hpi := Real.pi_pos
  rw [div_lt_div_iff₀ hn (by positivity)]
  nlinarith

/-- The energy bound of a sustained half-frequency oscillation at `Ω = 2ω_n`, `|ε| ≥ 2ξ`
(`ParametricSwing.halfFrequency_depth_ge_two`), lies strictly below the first-order boundary
`4√(ξ² + d²)` (`ParametricSwing.firstOrder_unstable`), for every detuning `d`. -/
@[tmio T, powerlib_foundation] theorem energyBound_lt_firstOrder {ξ : ℝ} (hξ : 0 < ξ) (d : ℝ) :
    2 * ξ < 4 * √(ξ ^ 2 + d ^ 2) := by
  have h : ξ ≤ √(ξ ^ 2 + d ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg d])
  linarith

/-- **A sustained parametric oscillation that the rules classify correctly.** Let the swing
model have positive damping with `(40π² + 1) ξ² ≤ 1` (`ξ ≲ 0.05`), and pump the synchronizing
coefficient with a square wave of period `T = 2π/(3ν)`, `ν = ω_n √(2(1 − ξ²)/5)`. There is a
depth `ε_b ∈ (0, 3(1 − ξ²)/5)` at which: every frozen state matrix is Hurwitz; a nonzero solution
of the state equation exists that is `T`-antiperiodic (sustained, at half the pump frequency) and
has no Fourier content at `Ωℤ` over any window `[s, s + 2T]`; and no model with constant
synchronizing coefficient `k` (any value) and a `T`-periodic mechanical power — natural or
forced — has a `C²` solution that agrees with its angle on `[0, ∞)`. -/
@[tmio M, powerlib_domain] theorem squareWave_instance (hp : p.Pos) (hξ : 0 < p.dampingRatio)
    (hξs : (40 * Real.pi ^ 2 + 1) * p.dampingRatio ^ 2 ≤ 1) {ν T : ℝ}
    (hν : ν = natFreq p * √(2 * (1 - p.dampingRatio ^ 2) / 5)) (hT : T = 2 * Real.pi / (3 * ν)) :
    ∃ εb ∈ Ioo 0 (3 * (1 - p.dampingRatio ^ 2) / 5),
      (∀ t, LinearSystems.IsHurwitz
        (frozen p (Mechanism.Ks p (.parametric (squareWave εb T))) t).stateMatrix) ∧
      ∃ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Ici 0) ∧
        (∀ t, 0 ≤ t → HasDerivWithinAt y
          ((frozen p (Mechanism.Ks p (.parametric (squareWave εb T))) t).stateMatrix *ᵥ y t)
            (Ici t) t) ∧
        y 0 ≠ 0 ∧ (∀ t, 0 ≤ t → y (t + T) = -y t) ∧
        (∀ (hL : 0 < 2 * T) (s : ℝ), 0 ≤ s → ∀ (i : Fin 2) (m : ℤ), Even m →
          coeff hL (fun t => y (s + t) i) m = 0) ∧
        ∀ (k : ℝ) (Pm δ δ' δ'' : ℝ → ℝ), Continuous Pm → Periodic Pm T →
          (∀ t, HasDerivAt δ (δ' t) t) → (∀ t, HasDerivAt δ' (δ'' t) t) →
          (∀ t, p.M * δ'' t + p.D * δ' t + k * δ t = Pm t) →
          ¬ ∀ t, 0 ≤ t → δ t = y t 0 := by
  set ξ := p.dampingRatio with hξdef
  set ω := natFreq p with hωdef
  have hω : 0 < ω := natFreq_pos hp
  have hpi := Real.pi_pos
  have hξ2 : ξ ^ 2 < 1 := by
    have : 0 < 40 * Real.pi ^ 2 * ξ ^ 2 := by positivity
    nlinarith
  have hr : 0 < 2 * (1 - ξ ^ 2) / 5 := by
    have : 0 < 1 - ξ ^ 2 := by linarith
    positivity
  have hνpos : 0 < ν := by rw [hν]; exact mul_pos hω (Real.sqrt_pos.mpr hr)
  set c := ξ * ω with hcdef
  have hc : 0 < c := mul_pos hξ hω
  have hcν : 4 * Real.pi * c ≤ ν := by
    rw [hν, hcdef, show 4 * Real.pi * (ξ * ω) = ω * (4 * Real.pi * ξ) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hω.le
    rw [Real.le_sqrt (by positivity) hr.le]
    nlinarith
  have hνsq : ν ^ 2 = ω ^ 2 * (2 * (1 - ξ ^ 2) / 5) := by
    rw [hν, mul_pow, Real.sq_sqrt hr.le]
  have hω₀eq : √((5 * ν ^ 2 + 2 * c ^ 2) / 2) = ω := by
    rw [show (5 * ν ^ 2 + 2 * c ^ 2) / 2 = ω ^ 2 by rw [hνsq, hcdef]; ring,
      Real.sqrt_sq hω.le]
  have hεs : 3 * ν ^ 2 / (5 * ν ^ 2 + 2 * c ^ 2) = 3 * (1 - ξ ^ 2) / 5 := by
    rw [hνsq, hcdef]
    field_simp
    ring
  obtain ⟨εb, hεb, hHur, y, hyc, hyd, hy0, hanti, hcoef⟩ :=
    ParametricResonance.Signature.frozen_damping_boundary hc hνpos hcν
  rw [hεs] at hεb
  rw [hω₀eq] at hHur hyd
  rw [← hT] at hHur hyd hanti
  have hsq : ∀ t, (frozen p (Mechanism.Ks p (.parametric (squareWave εb T))) t).stateMatrix =
      Periodic.oscMatrix c (ParametricResonance.Meissner.stiffness ω εb T t) := fun t =>
    squareWave_stateMatrix hp εb T t
  have hT0 : 0 < T := by rw [hT]; positivity
  refine ⟨εb, hεb, fun t => by rw [hsq]; exact hHur t, y, hyc, fun t ht => by
    rw [hsq]; exact hyd t ht, hy0, hanti,
    fun hL s hs i m hm => by subst hT; exact hcoef s hs i m hm, ?_⟩
  intro k Pm δ δ' δ'' hPm hPmT hδ hδ' heq hagree
  have hD : p.D ≠ 0 := by
    have hpos : 0 < p.Kd + p.KD := by
      rw [hξdef, Params.dampingRatio_eq hp] at hξ
      have : 0 < 2 * √(2 * p.H * p.ω₀ * p.Ks) := by
        have := hp.H; have := hp.ω₀; have := hp.Ks; positivity
      exact (div_pos_iff_of_pos_right this).mp hξ
    rw [Params.D]
    exact (div_pos hpos hp.ω₀).ne'
  have heq' : ∀ t, ({ p with Ks := k } : Params).M * δ'' t +
      ({ p with Ks := k } : Params).D * δ' t + ({ p with Ks := k } : Params).Ks * δ t = Pm t :=
    fun t => heq t
  have hanti' : ∀ t, 0 ≤ t → δ (t + T) = -δ t := by
    intro t ht
    rw [hagree _ (by linarith), hagree t ht, hanti t ht, Pi.neg_apply]
  have hzero := halfFrequency_eq_zero_of_const (p := { p with Ks := k }) (M_ne_zero (p := p) hp)
    hp.ω₀.ne' hD hT0 hPm hPmT hδ hδ' heq' hanti'
  -- then `y 0 = 0`: its angle vanishes on `[0, ∞)`, hence so does the right derivative
  apply hy0
  have h00 : y 0 0 = 0 := by rw [← hagree 0 le_rfl]; exact hzero 0 le_rfl
  have hd := hasDerivWithinAt_pi.mp (hyd 0 le_rfl) 0
  have hd0 : HasDerivWithinAt (fun t => y t 0) 0 (Ici 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Ici (0 : ℝ)) (0 : ℝ)).congr
      (fun t ht => by rw [← hagree t ht]; exact hzero t ht) (by rw [h00])
  have huniq := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hd hd0
  have h01 : y 0 1 = 0 := by
    have e : (Periodic.oscMatrix c (ParametricResonance.Meissner.stiffness ω εb T 0) *ᵥ y 0) 0 =
        y 0 1 := by
      simp [Periodic.oscMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [← e]; exact huniq
  funext i
  fin_cases i
  · exact h00
  · exact h01

end powerlib.ForcedOscillation.Classification
