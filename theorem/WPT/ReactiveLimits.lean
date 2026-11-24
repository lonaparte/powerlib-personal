import theorem.WPT.Gyrator

/-! # Power limits of the lossless link without a sign condition on the reactive power

Power limits of the link with lossless windings in which the bridges may run inductive or
capacitive. The series capacitor of a coil carries no real power, so the real power a bridge
delivers passes through the induced voltage `jωψ` of its coil: `Re(V_k Ī_k) = Re(jω ψ_k Ī_k)`
at every tuning, and therefore `|P| ≤ |ω| |ψ_k| |I_k|` on either side. With the bridge radii this
gives, whatever the reactive power, `|P| ≤ ρ₁ρ₂/|ωM|`, `|P| ≤ Ψ₁ ρ₂/|M|` under a primary flux limit
and `|P| ≤ Ψ₂ ρ₁/|M|` under a secondary flux limit.

Model boundary.
* The coil pair `w : Passive.Coupled` with lossless windings, at one angular frequency, both ports
  driven by bridge fundamentals (`CurrentLimits.Driven`), RMS phasors in sinusoidal steady state;
  the flux limits bound the fundamental flux-linkage phasors `Passive.Coupled.flux₁`, `flux₂`.
  The flux identities hold at every tuning; the bridge corollaries use the resonant tuning of
  `theorem/WPT/CurrentLimits.lean`.
* Fundamental-harmonic approximation; no sign condition on the reactive power (soft switching is
  not required). Lossy windings are `theorem/WPT/LossyLimits.lean`.

Source: the coil pair of `theorem/Passive/Coupled.lean`, the two-port equations of
`theorem/WPT/CurrentLimits.lean` and the gyrator law (`CurrentLimits.currents_lossless`).

Results.
* `power₁_eq_flux` (`Re(V₁ Ī₁) = Re(jω ψ₁ Ī₁)` with a lossless primary, every tuning),
  `power₂_eq_flux` (the same on the secondary), `abs_power₁_le_flux`, `abs_power₂_le_flux`
  (`|Re(V_k Ī_k)| ≤ |ω| ‖ψ_k‖ ‖I_k‖`).
* `abs_power_le_flux₁`, `abs_power_le_flux₂` (lossless resonant link, bridges `‖V_k‖ ≤ ρ_k`, any
  reactive power: `|P| ≤ Ψ₁ ρ₂/|M|` under `‖ψ₁‖ ≤ Ψ₁`, `|P| ≤ Ψ₂ ρ₁/|M|` under `‖ψ₂‖ ≤ Ψ₂`).
-/

noncomputable section

namespace powerlib.WPT.ReactiveLimits

open Complex ComplexConjugate CurrentLimits

variable {w : Passive.Coupled} {ω : ℝ} {V₁ V₂ I₁ I₂ : ℂ}

/-- With a lossless primary, at every tuning, the real power the primary bridge delivers passes
through the induced voltage of the coil: `Re(V₁ Ī₁) = Re(jω ψ₁ Ī₁)`. -/
@[tmio M, powerlib_domain] theorem power₁_eq_flux (hR₁ : w.primary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₁ * conj I₁).re = ((ω : ℂ) * I * w.flux₁ I₁ I₂ * conj I₁).re := by
  obtain ⟨h1, -⟩ := (driven_iff w ω V₁ V₂ I₁ I₂).mp h
  rw [h1, hR₁]
  simp only [Passive.Coupled.flux₁, Passive.SeriesRLC.reactance, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- With a lossless secondary, at every tuning: `Re(V₂ Ī₂) = Re(jω ψ₂ Ī₂)`. -/
@[tmio M, powerlib_domain] theorem power₂_eq_flux (hR₂ : w.secondary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₂ * conj I₂).re = ((ω : ℂ) * I * w.flux₂ I₁ I₂ * conj I₂).re := by
  obtain ⟨-, h2⟩ := (driven_iff w ω V₁ V₂ I₁ I₂).mp h
  rw [h2, hR₂]
  simp only [Passive.Coupled.flux₂, Passive.SeriesRLC.reactance, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- `|Re(V₁ Ī₁)| ≤ |ω| ‖ψ₁‖ ‖I₁‖` with a lossless primary, at every tuning. -/
@[tmio M, powerlib_domain] theorem abs_power₁_le_flux (hR₁ : w.primary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    |(V₁ * conj I₁).re| ≤ |ω| * ‖w.flux₁ I₁ I₂‖ * ‖I₁‖ := by
  rw [power₁_eq_flux hR₁ h]
  calc |((ω : ℂ) * I * w.flux₁ I₁ I₂ * conj I₁).re|
      ≤ ‖(ω : ℂ) * I * w.flux₁ I₁ I₂ * conj I₁‖ := Complex.abs_re_le_norm _
    _ = |ω| * ‖w.flux₁ I₁ I₂‖ * ‖I₁‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_conj,
        Real.norm_eq_abs, mul_one]

/-- `|Re(V₂ Ī₂)| ≤ |ω| ‖ψ₂‖ ‖I₂‖` with a lossless secondary, at every tuning. -/
@[tmio M, powerlib_domain] theorem abs_power₂_le_flux (hR₂ : w.secondary.R = 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    |(V₂ * conj I₂).re| ≤ |ω| * ‖w.flux₂ I₁ I₂‖ * ‖I₂‖ := by
  rw [power₂_eq_flux hR₂ h]
  calc |((ω : ℂ) * I * w.flux₂ I₁ I₂ * conj I₂).re|
      ≤ ‖(ω : ℂ) * I * w.flux₂ I₁ I₂ * conj I₂‖ := Complex.abs_re_le_norm _
    _ = |ω| * ‖w.flux₂ I₁ I₂‖ * ‖I₂‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_conj,
        Real.norm_eq_abs, mul_one]

/-- The lossless resonant link under a primary flux limit, whatever the reactive power:
`|P| ≤ Ψ₁ ρ₂/|M|`. -/
@[tmio M, powerlib_domain] theorem abs_power_le_flux₁ {ρ₁ ρ₂ Ψ₁ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ : ‖w.flux₁ I₁ I₂‖ ≤ Ψ₁) :
    |(V₁ * conj I₁).re| ≤ Ψ₁ * ρ₂ / |w.M| := by
  have hω : ω ≠ 0 := left_ne_zero_of_mul hm
  have hM : w.M ≠ 0 := right_ne_zero_of_mul hm
  obtain ⟨ha, -⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  have hb := abs_power₁_le_flux hR₁ h
  have hΨ : 0 ≤ Ψ₁ := (norm_nonneg _).trans hψ
  calc |(V₁ * conj I₁).re| ≤ |ω| * ‖w.flux₁ I₁ I₂‖ * ‖I₁‖ := hb
    _ ≤ |ω| * Ψ₁ * (ρ₂ / |ω * w.M|) := by gcongr
    _ = Ψ₁ * ρ₂ / |w.M| := by
      rw [abs_mul]
      field_simp

/-- The lossless resonant link under a secondary flux limit, whatever the reactive power:
`|P| ≤ Ψ₂ ρ₁/|M|`. -/
@[tmio M, powerlib_domain] theorem abs_power_le_flux₂ {ρ₁ ρ₂ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ : ‖w.flux₂ I₁ I₂‖ ≤ Ψ₂) :
    |(V₁ * conj I₁).re| ≤ Ψ₂ * ρ₁ / |w.M| := by
  have hω : ω ≠ 0 := left_ne_zero_of_mul hm
  have hM : w.M ≠ 0 := right_ne_zero_of_mul hm
  obtain ⟨-, hb'⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  have hbal := power_balance w ω h
  rw [hR₁, hR₂, zero_mul, zero_mul, add_zero] at hbal
  have hb := abs_power₂_le_flux hR₂ h
  have hΨ : 0 ≤ Ψ₂ := (norm_nonneg _).trans hψ
  have he : |(V₁ * conj I₁).re| = |(V₂ * conj I₂).re| := by
    rw [show (V₁ * conj I₁).re = -(V₂ * conj I₂).re by linarith, abs_neg]
  calc |(V₁ * conj I₁).re| = |(V₂ * conj I₂).re| := he
    _ ≤ |ω| * ‖w.flux₂ I₁ I₂‖ * ‖I₂‖ := hb
    _ ≤ |ω| * Ψ₂ * (ρ₁ / |ω * w.M|) := by gcongr
    _ = Ψ₂ * ρ₁ / |w.M| := by
      rw [abs_mul]
      field_simp

end powerlib.WPT.ReactiveLimits
