import theorem.WPT.Gyrator
import theorem.SpecialFunctions.ProductBound

/-! # The joint power limit of the lossless resonant link: bridges, primary flux and soft switching

The exact largest power of the lossless resonant link when the bridge voltages, the primary flux
and a soft-switching margin all constrain it at once. The individual limits are not attained by
the same currents: the bridges are used up at `|I₁| = ρ₂/|ωM|`, `|I₂| = ρ₁/|ωM|`, the flux limit
at `L₁|I₁| = |M||I₂|`, so the smaller of the two individual bounds is only an upper bound. The
joint optimum follows from the realization of every `(|I₁|, |I₂|, P, Q)` with
`P² + Q² = (ωM)²|I₁|²|I₂|²` (`Gyrator.exists_realization`): with inductive ports `Q ≥ Q_min ≥ 0`
the reactive power is best held at `Q_min`, and the problem is the largest product `|I₁||I₂|` in the
box of the bridges cut by the flux ellipse `L₁²|I₁|² + M²|I₂|² ≤ Ψ₁² − 2(L₁/ω)Q_min`
(`SpecialFunctions.productMax`, piecewise: the ellipse optimum when it lies in the box, else a face
or the corner of the box). The largest power is `√((ωM)² S² − Q_min²)` with that product `S`,
exactly. Without a sign condition on `Q`, the special case in which the flux limit does not bind
at the bridge optimum is exact as well: the power limit is then `ρ₁ρ₂/|ωM|`.

Model boundary.
* The lossless resonant link of `theorem/WPT/Gyrator.lean` (lossless windings, both coils resonant,
  `ωM ≠ 0`, both ports driven by bridge fundamentals `‖V_k‖ ≤ ρ_k`), `ω > 0`, `L₁ > 0`, a bound
  `|ψ₁| ≤ Ψ₁` on the primary fundamental flux linkage, and for the joint optimum a reactive
  margin `Q ≥ Q_min ≥ 0` (inductive bridge ports, the fundamental reading of zero-voltage
  switching). Fundamental-harmonic approximation; the boundary of `theorem/WPT/Gyrator.lean`.
* Not covered here: the joint optimum with capacitive operation allowed (`Q < 0`) when the flux
  limit binds, which is no longer a product over a box and an ellipse (with `Q < 0` the primary
  flux limit alone bounds no power, `Gyrator.exists_power_gt_of_flux₁`), and the secondary flux
  limit; both are in `theorem/WPT/ReactiveLimits.lean`; both flux limits with the margin are in
  `theorem/WPT/SoftLimits.lean`. Lossy windings are not covered.

Source: the realization of currents of the gyrator, `Gyrator.exists_realization`, the flux identity
`Gyrator.normSq_flux₁_eq`, the box–ellipse optimum `SpecialFunctions.isGreatest_productMax`
(`theorem/SpecialFunctions/ProductBound.lean`) and the bridge limit `CurrentLimits.power_le`.

Results.
* `fluxBudget` (`K = Ψ₁² − 2(L₁/ω)Q_min`), `productLimit` (the largest current product `S`, the
  `productMax` of `L₁`, `|M|`, `K` and the bridge radii `ρ₂/|ωM|`, `ρ₁/|ωM|`).
* `power_sq_le` (every admissible operating point with `|ψ₁| ≤ Ψ₁` and `Q ≥ Q_min ≥ 0` has
  `P² + Q_min² ≤ (ωM)² S²`), `exists_power_eq` (attained at `Q = Q_min` with
  `P = √((ωM)² S² − Q_min²)`), `isGreatest_power` (the exact largest power).
* `isGreatest_power_of_flux_slack` (no sign condition on `Q`: if the flux limit holds at the bridge
  optimum, `L₁²(ρ₂/|ωM|)² + M²(ρ₁/|ωM|)² ≤ Ψ₁²`, the exact largest power is `ρ₁ρ₂/|ωM|`).
-/

noncomputable section

namespace powerlib.WPT.JointLimits

open Complex ComplexConjugate CurrentLimits Gyrator

/-- The flux budget `K = Ψ₁² − 2(L₁/ω)Q_min` left to the currents by a reactive margin. -/
def fluxBudget (w : Passive.Coupled) (ω Ψ₁ Qmin : ℝ) : ℝ := Ψ₁ ^ 2 - 2 * (w.primary.L / ω) * Qmin

/-- The largest current product `|I₁||I₂|` in the box of the bridges cut by the flux ellipse. -/
def productLimit (w : Passive.Coupled) (ω ρ₁ ρ₂ Ψ₁ Qmin : ℝ) : ℝ :=
  SpecialFunctions.productMax w.primary.L |w.M| (fluxBudget w ω Ψ₁ Qmin) (ρ₂ / |ω * w.M|)
    (ρ₁ / |ω * w.M|)

variable {w : Passive.Coupled} {ω ρ₁ ρ₂ Ψ₁ Qmin : ℝ}

/-- Every admissible operating point with `|ψ₁| ≤ Ψ₁` and `Q ≥ Q_min ≥ 0` has
`P² + Q_min² ≤ (ωM)² S²`. -/
@[tmio M, powerlib_domain] theorem power_sq_le {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2) (hQ0 : 0 ≤ Qmin) (hQ : Qmin ≤ (V₁ * conj I₁).im) :
    (V₁ * conj I₁).re ^ 2 + Qmin ^ 2 ≤ (ω * w.M) ^ 2 * productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin ^ 2 := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  obtain ⟨ha, hb⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  have hflux := normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h
  have key := power_sq_add_reactive_sq hX₁ hX₂ hR₁ hR₂ h
  simp only [Complex.normSq_eq_norm_sq] at hflux key hψ
  have hQflux : 2 * (w.primary.L / ω) * Qmin ≤ 2 * (w.primary.L / ω) * (V₁ * conj I₁).im :=
    mul_le_mul_of_nonneg_left hQ (by positivity)
  have hE : w.primary.L ^ 2 * ‖I₁‖ ^ 2 + |w.M| ^ 2 * ‖I₂‖ ^ 2 ≤ fluxBudget w ω Ψ₁ Qmin := by
    rw [sq_abs, fluxBudget]
    linarith
  have hab := SpecialFunctions.mul_le_productMax hL₁ (abs_pos.mpr hM) (norm_nonneg I₁) ha
    (norm_nonneg I₂) hb hE
  have hab2 : (‖I₁‖ * ‖I₂‖) ^ 2 ≤ productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin ^ 2 :=
    pow_le_pow_left₀ (by positivity) hab 2
  have hQ2 : Qmin ^ 2 ≤ (V₁ * conj I₁).im ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
  have : (ω * w.M) ^ 2 * (‖I₁‖ ^ 2 * ‖I₂‖ ^ 2) ≤
      (ω * w.M) ^ 2 * productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin ^ 2 :=
    mul_le_mul_of_nonneg_left (by rw [← mul_pow]; exact hab2) (sq_nonneg _)
  linarith

/-- The joint limit is attained: with a nonnegative flux budget and `Q_min ≤ |ωM| S`, admissible
bridge phasors run at `Q = Q_min` within the flux limit and transfer `√((ωM)² S² − Q_min²)`. -/
@[tmio M, powerlib_domain] theorem exists_power_eq
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hQ0 : 0 ≤ Qmin)
    (hK : 0 ≤ fluxBudget w ω Ψ₁ Qmin)
    (hQS : Qmin ≤ |ω * w.M| * productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ (V₁ * conj I₁).im = Qmin ∧
        (V₁ * conj I₁).re =
          Real.sqrt ((ω * w.M) ^ 2 * productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin ^ 2 - Qmin ^ 2) := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  obtain ⟨⟨a, b⟩, ⟨ha, haA, hb, hbB, hE⟩, hab⟩ :=
    SpecialFunctions.exists_mul_eq_productMax hL₁ (abs_pos.mpr hM) hK
      (div_nonneg hρ₂ hma.le) (div_nonneg hρ₁ hma.le)
  simp only at ha haA hb hbB hE hab
  set S := productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin with hS
  have hab' : a * b = S := hab
  have hX : 0 ≤ (ω * w.M) ^ 2 * S ^ 2 - Qmin ^ 2 := by
    have : Qmin ^ 2 ≤ (|ω * w.M| * S) ^ 2 := pow_le_pow_left₀ hQ0 hQS 2
    rw [mul_pow, sq_abs] at this
    linarith
  have hPQ : Real.sqrt ((ω * w.M) ^ 2 * S ^ 2 - Qmin ^ 2) ^ 2 + Qmin ^ 2 =
      (ω * w.M) ^ 2 * (a ^ 2 * b ^ 2) := by
    rw [Real.sq_sqrt hX, ← hab']
    ring
  obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hI₁, hI₂, hP, hQ⟩ :=
    exists_realization hX₁ hX₂ hR₁ hR₂ hm ha hb haA hbB hPQ
  refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, ?_, hQ, hP⟩
  rw [normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h, hQ, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, hI₁, hI₂]
  rw [sq_abs, fluxBudget] at hE
  linarith

/-- The exact largest power under the bridges, the primary flux limit and the reactive margin. -/
@[tmio M, powerlib_domain] theorem isGreatest_power
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hQ0 : 0 ≤ Qmin)
    (hK : 0 ≤ fluxBudget w ω Ψ₁ Qmin)
    (hQS : Qmin ≤ |ω * w.M| * productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ Qmin ≤ (V₁ * conj I₁).im ∧ P = (V₁ * conj I₁).re}
      (Real.sqrt ((ω * w.M) ^ 2 * productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin ^ 2 - Qmin ^ 2)) := by
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, hQ, hP⟩ :=
      exists_power_eq hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hρ₁ hρ₂ hQ0 hK hQS
    exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, hQ.ge, hP.symm⟩
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, hQ, rfl⟩
    have hb := power_sq_le hX₁ hX₂ hR₁ hR₂ hω hL₁ hM h h₁ h₂ hψ hQ0 hQ
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

/-- Without a sign condition on the reactive power: if the primary flux limit holds at the bridge
optimum, `L₁²(ρ₂/|ωM|)² + M²(ρ₁/|ωM|)² ≤ Ψ₁²`, the exact largest power is the bridge limit
`ρ₁ρ₂/|ωM|`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_of_flux_slack
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hM : w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hslack : w.primary.L ^ 2 * (ρ₂ / |ω * w.M|) ^ 2 + w.M ^ 2 * (ρ₁ / |ω * w.M|) ^ 2 ≤ Ψ₁ ^ 2) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ P = (V₁ * conj I₁).re} (ρ₁ * ρ₂ / |ω * w.M|) := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  constructor
  · -- the bridge corner at `Q = 0`
    have hPQ : (ρ₁ * ρ₂ / |ω * w.M|) ^ 2 + 0 ^ 2 =
        (ω * w.M) ^ 2 * ((ρ₂ / |ω * w.M|) ^ 2 * (ρ₁ / |ω * w.M|) ^ 2) := by
      rw [← sq_abs (ω * w.M)]
      field_simp
      ring
    obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hI₁, hI₂, hP, hQ⟩ :=
      exists_realization hX₁ hX₂ hR₁ hR₂ hm (div_nonneg hρ₂ hma.le) (div_nonneg hρ₁ hma.le)
        le_rfl le_rfl hPQ
    refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, ?_, hP.symm⟩
    rw [normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h, hQ, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hI₁, hI₂, mul_zero, add_zero]
    exact hslack
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, -, rfl⟩
    exact power_le w ω hX₁ hX₂ hR₁ hR₂ hm h h₁ h₂

end powerlib.WPT.JointLimits
