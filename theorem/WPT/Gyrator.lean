import theorem.WPT.CurrentLimits

/-! # Power, reactive power, flux and soft switching of the lossless resonant link

The lossless resonant link driven by two bridges is a gyrator (`CurrentLimits.currents_lossless`):
`V₁ = jωM I₂`, `V₂ = jωM I₁`. Everything the bridges see is then a function of the one complex
number `z = I₁ Ī₂`: the transferred power is `P = ωM Im z`, and both bridges see the same reactive
power `Q = ωM Re z`, so `P² + Q² = (ωM)² |I₁|² |I₂|²`. Soft switching (zero-voltage switching
of both bridges, read in the fundamental-harmonic picture as an inductive bridge port, `Q > 0`) is
therefore paid for twice: it takes current magnitude away from the power, so with bridge radii
`ρ₁`, `ρ₂` the power under a reactive margin `Q_min` is at most `√((ρ₁ρ₂/|ωM|)² − Q_min²)`, attained;
and it adds flux, since `|ψ₁|² = L₁²|I₁|² + M²|I₂|² + 2(L₁/ω)Q`. With a flux limit `|ψ₁| ≤ Ψ₁` on
the primary coil the power obeys `P² + Q_min² ≤ ((ωΨ₁² − 2L₁Q_min)/(2L₁))²`: at `Q_min = 0` the
transferable power is at most `ωΨ₁²/(2L₁)`, whatever the coupling, attained by quadrature currents
with `L₁|I₁| = |M||I₂|`.

Model boundary.
* The lossless resonant link of `theorem/WPT/CurrentLimits.lean`: the coil pair
  `w : Passive.Coupled` with lossless windings `R₁ = R₂ = 0`, both coils resonant
  `X₁(ω) = X₂(ω) = 0`, `ωM ≠ 0`, both ports driven by the fundamental phasors `V₁`, `V₂` of two
  bridges (`CurrentLimits.Driven`), RMS phasors in sinusoidal steady state.
* Fundamental-harmonic approximation throughout. The soft-switching condition is its usual
  fundamental reading: a bridge switches at zero voltage when its port is inductive,
  `Im(V_k Ī_k) > 0`; the commutation interval, dead time, device capacitances and the
  harmonic content of the bridge currents, which decide zero-voltage switching exactly, are not
  modelled. The flux limit is a bound on the fundamental flux-linkage phasor of a coil
  (`Passive.Coupled.flux₁`); the nonlinear magnetization curve is not modelled.

Source: the fundamental-harmonic analysis of the series–series link driven by two active bridges
and its zero-voltage-switching condition (inductive bridge load), as for the dual-active-bridge
converter; the coil pair of `theorem/Passive/Coupled.lean` (`normSq_flux₁`, `normSq_flux₂`) and the
gyrator law of `theorem/WPT/CurrentLimits.lean`.

Results.
* `voltages_eq` (`V₁ = jωM I₂`, `V₂ = jωM I₁`), `power₁_eq` (`Re(V₁Ī₁) = ωM Im(I₁Ī₂)`),
  `power₂_eq` (`Re(V₂Ī₂) = −ωM Im(I₁Ī₂)`: what one bridge delivers the other absorbs),
  `reactive₁_eq`, `reactive₂_eq` (both bridges see `Im(V_kĪ_k) = ωM Re(I₁Ī₂)`),
  `power_sq_add_reactive_sq` (`P² + Q² = (ωM)²|I₁|²|I₂|²`).
* Soft switching: `power_sq_le_of_reactive` (with `‖V_k‖ ≤ ρ_k` and `Q ≥ Q_min ≥ 0`:
  `P² + Q_min² ≤ (ρ₁ρ₂/|ωM|)²`), `exists_power_reactive` (attained, with `Q = Q_min`).
* Flux: `normSq_flux₁_eq`, `normSq_flux₂_eq` (`|ψ₁|² = L₁²|I₁|² + M²|I₂|² + 2(L₁/ω)Q` and the
  secondary counterpart: an inductive margin adds flux, a capacitive one removes it),
  `power_sq_le_of_flux₁` (`|ψ₁| ≤ Ψ₁`, `Q ≥ Q_min ≥ 0`, `ω, L₁ > 0`:
  `P² + Q_min² ≤ ((ωΨ₁² − 2L₁Q_min)/(2L₁))²`), `abs_power_eq_of_flux₁` (quadrature currents with
  `L₁|I₁| = |M||I₂|` and `|ψ₁| = Ψ₁` transfer exactly `|P| = ωΨ₁²/(2L₁)`).
-/

noncomputable section

namespace powerlib.WPT.Gyrator

open Complex ComplexConjugate CurrentLimits

variable {w : Passive.Coupled} {ω : ℝ} {V₁ V₂ I₁ I₂ : ℂ}

/-- The lossless resonant link: `V₁ = jωM I₂`, `V₂ = jωM I₁`. -/
@[tmio M, powerlib_domain] theorem voltages_eq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    V₁ = ((ω * w.M : ℝ) : ℂ) * I * I₂ ∧ V₂ = ((ω * w.M : ℝ) : ℂ) * I * I₁ := by
  obtain ⟨h1, h2⟩ := (driven_iff w ω V₁ V₂ I₁ I₂).mp h
  rw [hX₁, hR₁] at h1
  rw [hX₂, hR₂] at h2
  simp only [Complex.ofReal_zero, zero_mul, zero_add, add_zero] at h1 h2
  exact ⟨h1, h2⟩

/-- The transferred power is `Re(V₁ Ī₁) = ωM Im(I₁ Ī₂)`. -/
@[tmio M, powerlib_domain] theorem power₁_eq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₁ * conj I₁).re = ω * w.M * (I₁ * conj I₂).im := by
  rw [(voltages_eq hX₁ hX₂ hR₁ hR₂ h).1]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The secondary bridge absorbs what the primary delivers: `Re(V₂ Ī₂) = −ωM Im(I₁ Ī₂)`. -/
@[tmio M, powerlib_domain] theorem power₂_eq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₂ * conj I₂).re = -(ω * w.M * (I₁ * conj I₂).im) := by
  rw [(voltages_eq hX₁ hX₂ hR₁ hR₂ h).2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The primary bridge sees the reactive power `Im(V₁ Ī₁) = ωM Re(I₁ Ī₂)`. -/
@[tmio M, powerlib_domain] theorem reactive₁_eq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₁ * conj I₁).im = ω * w.M * (I₁ * conj I₂).re := by
  rw [(voltages_eq hX₁ hX₂ hR₁ hR₂ h).1]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The secondary bridge sees the same reactive power `Im(V₂ Ī₂) = ωM Re(I₁ Ī₂)`. -/
@[tmio M, powerlib_domain] theorem reactive₂_eq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₂ * conj I₂).im = ω * w.M * (I₁ * conj I₂).re := by
  rw [(voltages_eq hX₁ hX₂ hR₁ hR₂ h).2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- `P² + Q² = (ωM)² |I₁|² |I₂|²`. -/
@[tmio M, powerlib_domain] theorem power_sq_add_reactive_sq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₁ * conj I₁).re ^ 2 + (V₁ * conj I₁).im ^ 2 =
      (ω * w.M) ^ 2 * (normSq I₁ * normSq I₂) := by
  rw [power₁_eq hX₁ hX₂ hR₁ hR₂ h, reactive₁_eq hX₁ hX₂ hR₁ hR₂ h]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/-! ## Soft switching -/

/-- A reactive margin costs power: with bridge radii `ρ₁`, `ρ₂` and `Q ≥ Q_min ≥ 0`,
`P² + Q_min² ≤ (ρ₁ρ₂/|ωM|)²`. -/
@[tmio M, powerlib_domain] theorem power_sq_le_of_reactive {ρ₁ ρ₂ Qmin : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hQ0 : 0 ≤ Qmin) (hQ : Qmin ≤ (V₁ * conj I₁).im) :
    (V₁ * conj I₁).re ^ 2 + Qmin ^ 2 ≤ (ρ₁ * ρ₂ / |ω * w.M|) ^ 2 := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  obtain ⟨ha, hb⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  have key := power_sq_add_reactive_sq hX₁ hX₂ hR₁ hR₂ h
  simp only [Complex.normSq_eq_norm_sq] at key
  have hρ₂ : 0 ≤ ρ₂ / |ω * w.M| := (norm_nonneg I₁).trans ha
  have hρ₁ : 0 ≤ ρ₁ / |ω * w.M| := (norm_nonneg I₂).trans hb
  have hA : ‖I₁‖ ^ 2 ≤ (ρ₂ / |ω * w.M|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hB : ‖I₂‖ ^ 2 ≤ (ρ₁ / |ω * w.M|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hprod : ‖I₁‖ ^ 2 * ‖I₂‖ ^ 2 ≤ (ρ₂ / |ω * w.M|) ^ 2 * (ρ₁ / |ω * w.M|) ^ 2 :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have hm2 : (ω * w.M) ^ 2 = |ω * w.M| ^ 2 := (sq_abs _).symm
  have hgoal : (ω * w.M) ^ 2 * ((ρ₂ / |ω * w.M|) ^ 2 * (ρ₁ / |ω * w.M|) ^ 2) =
      (ρ₁ * ρ₂ / |ω * w.M|) ^ 2 := by
    rw [hm2]
    field_simp
  have hQ2 : Qmin ^ 2 ≤ (V₁ * conj I₁).im ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
  nlinarith [mul_le_mul_of_nonneg_left hprod (sq_nonneg (ω * w.M))]

/-- The soft-switching power limit is attained: for `0 ≤ Q_min ≤ ρ₁ρ₂/|ωM|` some admissible
bridge phasors run at the reactive power `Q_min` and transfer `√((ρ₁ρ₂/|ωM|)² − Q_min²)`. -/
@[tmio M, powerlib_domain] theorem exists_power_reactive {ρ₁ ρ₂ Qmin : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hQ0 : 0 ≤ Qmin) (hQ1 : Qmin ≤ ρ₁ * ρ₂ / |ω * w.M|) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      (V₁ * conj I₁).im = Qmin ∧
        (V₁ * conj I₁).re = Real.sqrt ((ρ₁ * ρ₂ / |ω * w.M|) ^ 2 - Qmin ^ 2) := by
  set m := ω * w.M with hmdef
  have hma : 0 < |m| := abs_pos.mpr hm
  set Pv := Real.sqrt ((ρ₁ * ρ₂ / |m|) ^ 2 - Qmin ^ 2) with hPv
  have hX : 0 ≤ (ρ₁ * ρ₂ / |m|) ^ 2 - Qmin ^ 2 := by
    have : Qmin ^ 2 ≤ (ρ₁ * ρ₂ / |m|) ^ 2 := pow_le_pow_left₀ hQ0 hQ1 2
    linarith
  have hPv2 : Pv ^ 2 = (ρ₁ * ρ₂ / |m|) ^ 2 - Qmin ^ 2 := Real.sq_sqrt hX
  set A := ρ₂ / |m| with hA
  have hApos : 0 < A := div_pos hρ₂ hma
  set z : ℂ := ((Qmin / m : ℝ) : ℂ) + ((Pv / m : ℝ) : ℂ) * I with hz
  set J₁ : ℂ := (A : ℂ)
  set J₂ : ℂ := conj z / (A : ℂ)
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
  have hzJ : J₁ * conj J₂ = z := by
    simp only [J₁, J₂, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    field_simp
  have hJ₁ : ‖J₁‖ ≤ ρ₂ / |m| := by
    show ‖(A : ℂ)‖ ≤ ρ₂ / |m|
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
  have hJ₂ : ‖J₂‖ ≤ ρ₁ / |m| := by
    have hnz : ‖z‖ ^ 2 = (ρ₁ * ρ₂ / |m|) ^ 2 / m ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hz, Complex.normSq_add_mul_I, div_pow, div_pow, hPv2]
      field_simp
      ring
    have hn : ‖J₂‖ ^ 2 = (ρ₁ / |m|) ^ 2 := by
      simp only [J₂, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        div_pow, hnz, hA]
      have hm2 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
      rw [hm2]
      field_simp
      simp only [abs_abs, sq_abs]
      ring
    exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hρ₁.le hma.le)).mp hn.le
  obtain ⟨V₁, V₂, h₁, h₂, h⟩ :=
    (reachable_iff w ω J₁ J₂ hX₁ hX₂ hR₁ hR₂ hm).mpr ⟨hJ₁, hJ₂⟩
  refine ⟨V₁, V₂, J₁, J₂, h₁, h₂, h, ?_, ?_⟩
  · rw [reactive₁_eq hX₁ hX₂ hR₁ hR₂ h, hzJ, ← hmdef, hz]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    field_simp
    ring
  · rw [power₁_eq hX₁ hX₂ hR₁ hR₂ h, hzJ, ← hmdef, hz]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    field_simp
    ring

/-! ## Flux -/

/-- The primary flux in terms of the reactive power: `|ψ₁|² = L₁²|I₁|² + M²|I₂|² + 2(L₁/ω)Q`. -/
@[tmio M, powerlib_domain] theorem normSq_flux₁_eq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hω : ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    normSq (w.flux₁ I₁ I₂) = w.primary.L ^ 2 * normSq I₁ + w.M ^ 2 * normSq I₂ +
      2 * (w.primary.L / ω) * (V₁ * conj I₁).im := by
  rw [Passive.Coupled.normSq_flux₁, reactive₁_eq hX₁ hX₂ hR₁ hR₂ h]
  field_simp

/-- The secondary flux in terms of the reactive power: `|ψ₂|² = M²|I₁|² + L₂²|I₂|² + 2(L₂/ω)Q`. -/
@[tmio M, powerlib_domain] theorem normSq_flux₂_eq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0)
    (hω : ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    normSq (w.flux₂ I₁ I₂) = w.M ^ 2 * normSq I₁ + w.secondary.L ^ 2 * normSq I₂ +
      2 * (w.secondary.L / ω) * (V₂ * conj I₂).im := by
  rw [Passive.Coupled.normSq_flux₂, reactive₂_eq hX₁ hX₂ hR₁ hR₂ h]
  field_simp

/-- The flux limit caps the power: with `|ψ₁| ≤ Ψ₁`, a reactive margin `Q ≥ Q_min ≥ 0` and
`ω, L₁ > 0`, `P² + Q_min² ≤ ((ωΨ₁² − 2L₁Q_min)/(2L₁))²`; at `Q_min = 0` the power is at most
`ωΨ₁²/(2L₁)`, whatever the coupling. -/
@[tmio M, powerlib_domain] theorem power_sq_le_of_flux₁ {Ψ₁ Qmin : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (h : Driven w ω V₁ V₂ I₁ I₂) (hψ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2)
    (hQ0 : 0 ≤ Qmin) (hQ : Qmin ≤ (V₁ * conj I₁).im) :
    (V₁ * conj I₁).re ^ 2 + Qmin ^ 2 ≤ ((ω * Ψ₁ ^ 2 - 2 * w.primary.L * Qmin) /
      (2 * w.primary.L)) ^ 2 := by
  have hflux := normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h
  have key := power_sq_add_reactive_sq hX₁ hX₂ hR₁ hR₂ h
  simp only [Complex.normSq_eq_norm_sq] at hflux key hψ
  set a := ‖I₁‖
  set b := ‖I₂‖
  set Q := (V₁ * conj I₁).im
  set P := (V₁ * conj I₁).re
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  -- AM–GM on the flux: `2 L₁ |M| a b ≤ L₁²a² + M²b²`
  have hamgm : 2 * w.primary.L * |w.M| * (a * b) ≤
      w.primary.L ^ 2 * a ^ 2 + w.M ^ 2 * b ^ 2 := by
    nlinarith [sq_nonneg (w.primary.L * a - |w.M| * b), sq_abs w.M]
  have hQflux : 2 * (w.primary.L / ω) * Qmin ≤ 2 * (w.primary.L / ω) * Q :=
    mul_le_mul_of_nonneg_left hQ (by positivity)
  have hab : 2 * w.primary.L * |w.M| * (a * b) ≤ Ψ₁ ^ 2 - 2 * (w.primary.L / ω) * Qmin := by
    linarith
  -- `u = |ωM| a b` is at most `Y`
  set Y := (ω * Ψ₁ ^ 2 - 2 * w.primary.L * Qmin) / (2 * w.primary.L) with hY
  have hu : |ω * w.M| * (a * b) ≤ Y := by
    rw [abs_mul, abs_of_pos hω, hY, le_div_iff₀ (by positivity)]
    have : ω * (2 * w.primary.L * |w.M| * (a * b)) ≤
        ω * (Ψ₁ ^ 2 - 2 * (w.primary.L / ω) * Qmin) := mul_le_mul_of_nonneg_left hab hω.le
    have e : ω * (Ψ₁ ^ 2 - 2 * (w.primary.L / ω) * Qmin) = ω * Ψ₁ ^ 2 - 2 * w.primary.L * Qmin := by
      field_simp
    nlinarith
  have hu0 : 0 ≤ |ω * w.M| * (a * b) := by positivity
  have hu2 : (|ω * w.M| * (a * b)) ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hu0 hu 2
  have hQ2 : Qmin ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
  have hsq : (|ω * w.M| * (a * b)) ^ 2 = (ω * w.M) ^ 2 * (a ^ 2 * b ^ 2) := by
    rw [mul_pow, sq_abs]
    ring
  nlinarith

/-- The flux-limited power is attained: quadrature currents (`Q = 0`) with `L₁|I₁| = |M||I₂|`
and `|ψ₁| = Ψ₁` transfer exactly `|P| = ωΨ₁²/(2L₁)`. -/
@[tmio M, powerlib_domain] theorem abs_power_eq_of_flux₁ {Ψ₁ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (h : Driven w ω V₁ V₂ I₁ I₂) (hQ : (V₁ * conj I₁).im = 0)
    (hbal : w.primary.L * ‖I₁‖ = |w.M| * ‖I₂‖) (hψ : normSq (w.flux₁ I₁ I₂) = Ψ₁ ^ 2) :
    |(V₁ * conj I₁).re| = ω * Ψ₁ ^ 2 / (2 * w.primary.L) := by
  have hflux := normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h
  have key := power_sq_add_reactive_sq hX₁ hX₂ hR₁ hR₂ h
  simp only [Complex.normSq_eq_norm_sq] at hflux key hψ
  rw [hQ, mul_zero, add_zero] at hflux
  rw [hQ] at key
  have hMb : w.M ^ 2 * ‖I₂‖ ^ 2 = w.primary.L ^ 2 * ‖I₁‖ ^ 2 := by
    have : (|w.M| * ‖I₂‖) ^ 2 = (w.primary.L * ‖I₁‖) ^ 2 := by rw [hbal]
    rw [mul_pow, mul_pow, sq_abs] at this
    exact this
  have ha2 : ‖I₁‖ ^ 2 = Ψ₁ ^ 2 / (2 * w.primary.L ^ 2) := by
    rw [eq_div_iff (by positivity)]
    linarith
  have hP2 : (V₁ * conj I₁).re ^ 2 = (ω * w.primary.L * ‖I₁‖ ^ 2) ^ 2 := by
    have : (ω * w.M) ^ 2 * (‖I₁‖ ^ 2 * ‖I₂‖ ^ 2) = ω ^ 2 * ‖I₁‖ ^ 2 * (w.M ^ 2 * ‖I₂‖ ^ 2) := by
      ring
    rw [zero_pow two_ne_zero, add_zero] at key
    rw [key, this, hMb]
    ring
  rw [← Real.sqrt_sq_eq_abs, hP2, Real.sqrt_sq (by positivity), ha2]
  field_simp

end powerlib.WPT.Gyrator
