import theorem.PowerSystem.ForcedOscillation.Classification
import theorem.ParametricResonance.SubharmonicContent

/-! # The half-frequency rule P½ for TR-110's swing model, read through its spectrum

Rule P½ of `theorem/PowerSystem/ForcedOscillation/Classification.lean`
(`Classification.classify_halfFrequency`) decides "parametric" from a nonzero `T`-antiperiodic
oscillation of the linearized swing model while the mechanical power has content at `Ωℤ` only
(`Ω = 2π/T`). Its premise is a property of the signal in time. The spectral converse of
`theorem/ParametricResonance/SubharmonicContent.lean` turns it into a statement about the
observed spectrum over a window of two pump periods: an antiperiodic response has no line at
`kΩ`, and it is nonzero iff it has a line at some half-integer frequency `(k + ½)Ω`; such a line
then classifies the mechanism as parametric. A nonzero antiperiodic response shows the line in
every window `[s, s + 2T]`, `s ≥ 0`. On the exact square-wave boundary of the swing model
(`Classification.squareWave_boundary`: no Floquet multiplier outside the unit circle) such a
response exists (`Subharmonic.meissner_boundary_subharmonic`), and no model with constant
synchronizing coefficient explains its angle.

Model boundary.
* TR-110's linearized swing equation (3-8)–(3-10) at an operating point, as in `Classification`:
  `M Δδ̈ + D Δδ̇ + K_s(t) Δδ = ΔP_m(t)`, `M = 2H/ω₀`, `D = (K_d + K_D)/ω₀`, `Params.Pos`, with the
  mechanisms `Classification.Mechanism` (natural, forced, parametric); continuous time, angle
  deviation `Δδ`, global `C²` solutions for the rule; for the square-wave instance the state
  `(Δδ, Δδ̇)` with right derivatives on `[0, ∞)` (discontinuous `K_s(t)`).
* Observables: the Fourier coefficients `SpecialFunctions.PeriodicWaves.coeff` of the angle over
  a window `[s, s + 2T]` (`t ↦ Δδ(s + t)` on `[0, 2T]`; index `m` at frequency `mΩ/2`, even `m`
  the integer multiples `kΩ`, odd `m` the half-integer frequencies `(k + ½)Ω`), the candidate pump
  period `T`, the periodicity of `ΔP_m` at `T`, and `D ≠ 0` (`ξ > 0` for the square wave).
  Measured records are not formalized (Rules §2a); the statements hold for every signal of the
  model class.
* Excluded as in `Classification`: AVR, PSS, network dynamics, nonlinearity, Prony estimation.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.1, §3.3–§3.5 (natural
versus forced oscillations, swing model, harmonics of the steady state), as extended by the
parametric class and rule P½ (`Classification.classify_halfFrequency`,
`Classification.halfFrequency_eq_zero_of_const`); the spectral converse
`Subharmonic.antiperiodic_ne_zero_iff`, `Subharmonic.coeff_even_eq_zero_iff`; the square-wave
boundary `Classification.squareWave_boundary`, `Classification.squareWave_stateMatrix` and the
boundary mode `Subharmonic.meissner_boundary_subharmonic`.

Results.
* `halfFrequency_rule` — over every window `[s, s + 2T]`, `s ≥ 0`, an antiperiodic solution of
  the swing model has no `kΩ` content; it is nonzero on the window iff some `(k + ½)Ω`
  coefficient is nonzero; and such a coefficient (with `D ≠ 0`, `ΔP_m` `T`-periodic) makes the
  mechanism parametric with a nonconstant pump.
* `halfFrequency_every_window` — a nonzero antiperiodic solution shows a half-integer line and no
  integer line in every window `[s, s + 2T]`, `s ≥ 0`, and is parametric.
* `squareWave_boundary_response` — on the exact square-wave boundary
  `τ = −2 cosh(ξω_n T)` no Floquet multiplier lies outside the unit circle, and the swing model
  has a nonzero `T`-antiperiodic state response whose angle has no `kΩ` content, a nonzero
  `(k + ½)Ω` coefficient, and agrees on `[0, ∞)` with no `C²` solution of a constant-`K_s` model
  (natural or forced with `T`-periodic `ΔP_m`).
-/

noncomputable section
namespace powerlib.ForcedOscillation.Classification

open Complex Set Function Filter Topology Matrix
open powerlib.Synchronous.OscillationPhasor powerlib.Synchronous.ParametricSwing
open powerlib.SpecialFunctions.PeriodicWaves (coeff squareWave)

variable {p : Params}

/-- **Rule P½ in the spectrum of a window.** For a solution of the swing model that is
`T`-antiperiodic on `[0, ∞)`, over every window `[s, s + 2T]`, `s ≥ 0`: every coefficient at the
integer multiples `kΩ` vanishes; the solution is nonzero on the window iff some coefficient at a
half-integer frequency `(k + ½)Ω` is nonzero; and if one is (with `D ≠ 0` and `ΔP_m`
`T`-periodic), the mechanism is parametric with a time-varying synchronizing coefficient. -/
@[tmio M, powerlib_domain] theorem halfFrequency_rule (hp : p.Pos) (hD : p.D ≠ 0) (e : Mechanism)
    (hPm : Continuous e.Pm) {T : ℝ} (hT : 0 < T) (hPmT : Periodic e.Pm T) {δ δ' δ'' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + e.Ks p t * δ t = e.Pm t)
    (hanti : ∀ t, 0 ≤ t → δ (t + T) = -δ t) {s : ℝ} (hs : 0 ≤ s) :
    (∀ k : ℤ, coeff (mul_pos two_pos hT) (fun t => δ (s + t)) (2 * k) = 0) ∧
      ((∃ t ∈ Icc 0 (2 * T), δ (s + t) ≠ 0) ↔
        ∃ k : ℤ, coeff (mul_pos two_pos hT) (fun t => δ (s + t)) (2 * k + 1) ≠ 0) ∧
      ((∃ k : ℤ, coeff (mul_pos two_pos hT) (fun t => δ (s + t)) (2 * k + 1) ≠ 0) →
        ∃ pump : ℝ → ℝ, e = .parametric pump ∧ ∃ t, pump t ≠ pump 0) := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun t => (hδ t).continuousAt
  have hfc : ContinuousOn (fun t => δ (s + t)) (Icc 0 (2 * T)) :=
    (hδc.comp (continuous_const.add continuous_id)).continuousOn
  have hfa : ∀ t ∈ Icc 0 T, δ (s + (t + T)) = -δ (s + t) := fun t ht => by
    rw [show s + (t + T) = (s + t) + T by ring, hanti _ (by linarith [ht.1])]
  have hiff := ParametricResonance.Subharmonic.antiperiodic_ne_zero_iff hT hfc hfa
  refine ⟨(ParametricResonance.Subharmonic.coeff_even_eq_zero_iff hT hfc).mpr hfa, hiff,
    fun hk => ?_⟩
  obtain ⟨t, ht, hne⟩ := hiff.mpr hk
  exact classify_halfFrequency hp hD e hPm hT hPmT hδ hδ' heq hanti
    ⟨s + t, by linarith [ht.1], hne⟩

@[tmio T, powerlib_foundation] private theorem abs_shift_eq {δ : ℝ → ℝ} {T : ℝ}
    (hanti : ∀ t, 0 ≤ t → δ (t + T) = -δ t) {u : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T) (n : ℕ) :
    |δ (u + n * T)| = |δ u| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show u + ((n + 1 : ℕ) : ℝ) * T = (u + n * T) + T by push_cast; ring,
      hanti _ (by positivity), abs_neg, ih]

/-- **A nonzero antiperiodic response shows its half-frequency line in every window.** If a
`T`-antiperiodic solution of the swing model is nonzero at some `t ≥ 0`, then over every window
`[s, s + 2T]`, `s ≥ 0`, its angle has no coefficient at `kΩ` and a nonzero one at some `(k + ½)Ω`;
with `D ≠ 0` and `ΔP_m` `T`-periodic the mechanism is parametric with a nonconstant pump. -/
@[tmio M, powerlib_domain] theorem halfFrequency_every_window (hp : p.Pos) (hD : p.D ≠ 0)
    (e : Mechanism) (hPm : Continuous e.Pm) {T : ℝ} (hT : 0 < T) (hPmT : Periodic e.Pm T)
    {δ δ' δ'' : ℝ → ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, p.M * δ'' t + p.D * δ' t + e.Ks p t * δ t = e.Pm t)
    (hanti : ∀ t, 0 ≤ t → δ (t + T) = -δ t) (hne : ∃ t, 0 ≤ t ∧ δ t ≠ 0) :
    (∀ s, 0 ≤ s → (∀ k : ℤ, coeff (mul_pos two_pos hT) (fun t => δ (s + t)) (2 * k) = 0) ∧
        ∃ k : ℤ, coeff (mul_pos two_pos hT) (fun t => δ (s + t)) (2 * k + 1) ≠ 0) ∧
      ∃ pump : ℝ → ℝ, e = .parametric pump ∧ ∃ t, pump t ≠ pump 0 := by
  obtain ⟨t₀, ht₀, hne₀⟩ := hne
  refine ⟨fun s hs => ?_, classify_halfFrequency hp hD e hPm hT hPmT hδ hδ' heq hanti
    ⟨t₀, ht₀, hne₀⟩⟩
  obtain ⟨h1, h2, -⟩ := halfFrequency_rule hp hD e hPm hT hPmT hδ hδ' heq hanti hs
  refine ⟨h1, h2.mp ?_⟩
  -- a point `u ∈ [s, s + T]` of the orbit `t₀ + ℤT` (inside `[0, ∞)`), where `|δ u| = |δ t₀|`
  have hpos : 0 < |δ t₀| := abs_pos.mpr hne₀
  obtain ⟨u, hu, hδu⟩ : ∃ u ∈ Icc s (s + T), |δ u| = |δ t₀| := by
    rcases le_or_gt s t₀ with hst | hst
    · set n := ⌊(t₀ - s) / T⌋₊ with hn
      have h1 : (n : ℝ) * T ≤ t₀ - s := by
        have := Nat.floor_le (div_nonneg (sub_nonneg.mpr hst) hT.le)
        calc (n : ℝ) * T ≤ (t₀ - s) / T * T := mul_le_mul_of_nonneg_right this hT.le
          _ = t₀ - s := by field_simp
      have h2 : t₀ - s < ((n : ℝ) + 1) * T := by
        have := Nat.lt_floor_add_one ((t₀ - s) / T)
        calc t₀ - s = (t₀ - s) / T * T := by field_simp
          _ < ((n : ℝ) + 1) * T := mul_lt_mul_of_pos_right this hT
      refine ⟨t₀ - n * T, ⟨by linarith, by linarith⟩, ?_⟩
      have := abs_shift_eq hanti (u := t₀ - n * T) (by linarith) hT.le n
      rw [sub_add_cancel] at this
      exact this.symm
    · set n := ⌈(s - t₀) / T⌉₊ with hn
      have h1 : s - t₀ ≤ (n : ℝ) * T := by
        have := Nat.le_ceil ((s - t₀) / T)
        calc s - t₀ = (s - t₀) / T * T := by field_simp
          _ ≤ (n : ℝ) * T := mul_le_mul_of_nonneg_right this hT.le
      have h2 : (n : ℝ) * T < s - t₀ + T := by
        have := Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.mpr hst.le) hT.le)
        calc (n : ℝ) * T < ((s - t₀) / T + 1) * T := mul_lt_mul_of_pos_right this hT
          _ = s - t₀ + T := by field_simp
      exact ⟨t₀ + n * T, ⟨by linarith, by linarith⟩, abs_shift_eq hanti ht₀ hT.le n⟩
  refine ⟨u - s, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
  rw [add_sub_cancel]
  intro h0
  rw [h0, abs_zero] at hδu
  linarith

/-- **A sustained half-frequency response on the exact square-wave boundary.** For the swing
model with `K_s(t) = K_s(1 + squareWave ε T t)`, `ξ > 0`, `ν_{1,2}² = ω_n²(1 ± ε − ξ²)` and the
boundary `τ = −2 cosh(ξω_n T)` (`τ = Meissner.reducedTrace ν₁ ν₂ T`): no Floquet multiplier lies
outside the unit circle, and there is a nonzero state response `y` (right derivatives on
`[0, ∞)`) with `y(t + T) = −y(t)` whose angle `y₀` has, over `[0, 2T]`, no coefficient at `kΩ`
and a nonzero coefficient at some `(k + ½)Ω`; no model with constant synchronizing coefficient
`k` and `T`-periodic mechanical power — natural or forced — has a `C²` solution that agrees with
this angle on `[0, ∞)`. -/
@[tmio M, powerlib_domain] theorem squareWave_boundary_response (hp : p.Pos)
    (hξ : 0 < p.dampingRatio) {ε T ν₁ ν₂ : ℝ} (hT : 0 < T)
    (hν₁ : ν₁ ^ 2 = natFreq p ^ 2 * (1 + ε - p.dampingRatio ^ 2))
    (hν₂ : ν₂ ^ 2 = natFreq p ^ 2 * (1 - ε - p.dampingRatio ^ 2)) (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0)
    (hb : ParametricResonance.Meissner.reducedTrace ν₁ ν₂ T =
      -(2 * Real.cosh (p.dampingRatio * natFreq p * T))) :
    (¬ ∃ μ ∈ spectrum ℂ ((ParametricResonance.Meissner.meissnerMonodromy
        (p.dampingRatio * natFreq p) (natFreq p) ε T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ∧
      ∃ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Ici 0) ∧
        (∀ t, 0 ≤ t → HasDerivWithinAt y
          ((frozen p (Mechanism.Ks p (.parametric (squareWave ε T))) t).stateMatrix *ᵥ y t)
            (Ici t) t) ∧
        y 0 ≠ 0 ∧ (∀ t, 0 ≤ t → y (t + T) = -y t) ∧
        (∀ k : ℤ, coeff (mul_pos two_pos hT) (fun t => y t 0) (2 * k) = 0) ∧
        (∃ k : ℤ, coeff (mul_pos two_pos hT) (fun t => y t 0) (2 * k + 1) ≠ 0) ∧
        ∀ (k : ℝ) (Pm δ δ' δ'' : ℝ → ℝ), Continuous Pm → Periodic Pm T →
          (∀ t, HasDerivAt δ (δ' t) t) → (∀ t, HasDerivAt δ' (δ'' t) t) →
          (∀ t, p.M * δ'' t + p.D * δ' t + k * δ t = Pm t) →
          ¬ ∀ t, 0 ≤ t → δ t = y t 0 := by
  set c := p.dampingRatio * natFreq p with hcdef
  have hn : 0 ≤ natFreq p := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := mul_nonneg hξ.le hn
  obtain ⟨-, -, hiff⟩ := squareWave_boundary hp hξ.le hT hν₁ hν₂ h₁ h₂
  have hstab : ¬ ∃ μ ∈ spectrum ℂ ((ParametricResonance.Meissner.meissnerMonodromy c
      (natFreq p) ε T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖ := by
    rw [hiff, hb, abs_neg, abs_of_pos (by positivity)]
    exact lt_irrefl _
  obtain ⟨y, hyc, hyd, hy0, hanti, heven, hodd⟩ :=
    ParametricResonance.Subharmonic.meissner_boundary_subharmonic (c := c) (ω₀ := natFreq p)
      (ε := ε)
      (by rw [hν₁]; ring) (by rw [hν₂]; ring) h₁ h₂ hT hb
  have hsq : ∀ t, (frozen p (Mechanism.Ks p (.parametric (squareWave ε T))) t).stateMatrix =
      Periodic.oscMatrix c (ParametricResonance.Meissner.stiffness (natFreq p) ε T t) := fun t =>
    squareWave_stateMatrix hp ε T t
  refine ⟨hstab, y, hyc, fun t ht => by rw [hsq]; exact hyd t ht, hy0, hanti, heven, hodd, ?_⟩
  intro k Pm δ δ' δ'' hPm hPmT hδ hδ' heq hagree
  have hD : p.D ≠ 0 := by
    have hpos : 0 < p.Kd + p.KD := by
      have hξ' := hξ
      rw [Params.dampingRatio_eq hp] at hξ'
      have : 0 < 2 * √(2 * p.H * p.ω₀ * p.Ks) := by
        have := hp.H; have := hp.ω₀; have := hp.Ks; positivity
      exact (div_pos_iff_of_pos_right this).mp hξ'
    rw [Params.D]
    exact (div_pos hpos hp.ω₀).ne'
  have hM : p.M ≠ 0 := by
    have := hp.H; have := hp.ω₀
    rw [Params.M]; positivity
  have heq' : ∀ t, ({ p with Ks := k } : Params).M * δ'' t +
      ({ p with Ks := k } : Params).D * δ' t + ({ p with Ks := k } : Params).Ks * δ t = Pm t :=
    fun t => heq t
  have hanti' : ∀ t, 0 ≤ t → δ (t + T) = -δ t := by
    intro t ht
    rw [hagree _ (by linarith), hagree t ht, hanti t ht, Pi.neg_apply]
  have hzero := halfFrequency_eq_zero_of_const (p := { p with Ks := k }) hM hp.ω₀.ne' hD hT hPm
    hPmT hδ hδ' heq' hanti'
  -- then `y 0 = 0`: its angle vanishes on `[0, ∞)`, hence so does its right derivative
  apply hy0
  have h00 : y 0 0 = 0 := by rw [← hagree 0 le_rfl]; exact hzero 0 le_rfl
  have hd := hasDerivWithinAt_pi.mp (hyd 0 le_rfl) 0
  have hd0 : HasDerivWithinAt (fun t => y t 0) 0 (Ici 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Ici (0 : ℝ)) (0 : ℝ)).congr
      (fun t ht => by rw [← hagree t ht]; exact hzero t ht) (by rw [h00])
  have huniq := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hd hd0
  have h01 : y 0 1 = 0 := by
    have e : (Periodic.oscMatrix c (ParametricResonance.Meissner.stiffness (natFreq p) ε T 0) *ᵥ
        y 0) 0 = y 0 1 := by
      simp [Periodic.oscMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [← e]; exact huniq
  funext i
  fin_cases i
  · exact h00
  · exact h01

end powerlib.ForcedOscillation.Classification
