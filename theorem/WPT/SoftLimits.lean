import theorem.WPT.JointLimits
import theorem.SpecialFunctions.EllipseProduct

/-! # The soft-switching power limit of the lossless resonant link under both flux limits

The exact largest power of the lossless resonant link when the bridge voltages, the flux linkages
of both coils and a soft-switching margin constrain it at once. Zero-voltage switching of both
bridges is read, in the fundamental-harmonic picture, as inductive bridge ports with a margin,
`Q ≥ Q_min ≥ 0`; for the lossless resonant link the secondary port sees the same reactive power as
the primary (`Gyrator.reactive₂_eq`), so one margin on `Q = Im(V₁ Ī₁)` covers both bridges.

Every `(|I₁|, |I₂|, P, Q)` with `P² + Q² = (ωM)²|I₁|²|I₂|²` in the bridge box
`|I₁| ≤ ρ₂/|ωM|`, `|I₂| ≤ ρ₁/|ωM|` is realized (`Gyrator.exists_realization`). An inductive
margin adds flux, `|ψ₁|² = L₁²|I₁|² + M²|I₂|² + 2(L₁/ω)Q` and
`|ψ₂|² = M²|I₁|² + L₂²|I₂|² + 2(L₂/ω)Q`, so with `Q ≥ Q_min` each flux limit leaves the currents an
ellipse with a budget shrunk by the margin, `K₁ = Ψ₁² − 2(L₁/ω)Q_min` and
`K₂ = Ψ₂² − 2(L₂/ω)Q_min`. A reactive power above the margin only costs power
(`P² = (ωM)²|I₁|²|I₂|² − Q²`) and adds flux, so the reactive power is best held at `Q = Q_min`: the
largest power is `√((ωM)² S² − Q_min²)`, with `S` the largest current product `|I₁||I₂|` in the
bridge box cut by the flux ellipses, and it is attained at `Q = Q_min` by currents with
`|I₁||I₂| = S`.

With the secondary flux limit alone, `S = productLimit₂` (`SpecialFunctions.productMax` of the
ellipse `M²|I₁|² + L₂²|I₂|² ≤ K₂`): the mirror image of `theorem/WPT/JointLimits.lean`, which treats
the primary flux limit alone. With both flux limits, `S = softLimit`, the largest product in the
bridge box cut by both ellipses (`SpecialFunctions.boxEllipseMax`); by definition it is the
smallest of three relaxations (`softLimit_eq`): the bridges with the primary flux
(`JointLimits.productLimit`), the bridges with the secondary flux (`productLimit₂`), and the two
flux ellipses without the bridges (`SpecialFunctions.ellipseMax`). Its regimes are the bridge corner
`|I₁| = ρ₂/|ωM|`, `|I₂| = ρ₁/|ωM|` with both flux limits slack; one flux limit binding (the optimum
`L₁|I₁| = |M||I₂|` of the primary ellipse, or `|M||I₁| = L₂|I₂|` of the secondary one, or a point of
that ellipse on a bridge face) with the other flux limit slack; and the crossing of the two flux
ellipses, where both flux limits bind and the optimum generically leaves both bridge voltages below
their limits. The last regime is the one that neither single-flux limit records; that the smallest
relaxation is attained is Helly's theorem (`SpecialFunctions.exists_mul_eq_boxEllipseMax`).
Together with `theorem/WPT/JointLimits.lean` (bridges, primary flux and margin) this completes the
soft-switching power limits of the link: either flux limit alone, and both at once.

Model boundary.
* The lossless resonant link of `theorem/WPT/Gyrator.lean` (lossless windings `R₁ = R₂ = 0`, both
  coils resonant `X₁(ω) = X₂(ω) = 0`, `ωM ≠ 0`, both ports driven by bridge fundamentals
  `‖V_k‖ ≤ ρ_k`, `CurrentLimits.Driven`), `ω > 0`, `L₁ > 0` (primary flux) and `L₂ > 0` (secondary
  flux), bounds `|ψ₁| ≤ Ψ₁`, `|ψ₂| ≤ Ψ₂` on the fundamental flux-linkage phasors
  `Passive.Coupled.flux₁`, `flux₂`, and the reactive margin `Q ≥ Q_min ≥ 0` (inductive bridge
  ports, the fundamental reading of zero-voltage switching of both bridges). Attainment assumes
  nonnegative flux budgets and `Q_min ≤ |ωM| S`; by the upper bound, no admissible operating point
  meets the margin when `Q_min > |ωM| S`.
* Fundamental-harmonic approximation; the boundary of `theorem/WPT/Gyrator.lean`: the commutation
  interval, dead time, device capacitances, the harmonic content of the bridge currents and the
  nonlinear magnetization curve are not modelled.
* Not covered here: capacitive operation (`Q < 0`), for which the flux limits are treated without
  a sign condition in `theorem/WPT/ReactiveLimits.lean`, and lossy windings.

Source: the realization of currents of the gyrator, `Gyrator.exists_realization`, the flux
identities `Gyrator.normSq_flux₁_eq`, `Gyrator.normSq_flux₂_eq` and the equal reactive powers
`Gyrator.reactive₁_eq`, `Gyrator.reactive₂_eq` (`theorem/WPT/Gyrator.lean`); the box–ellipse
optimum `SpecialFunctions.isGreatest_productMax` (`theorem/SpecialFunctions/ProductBound.lean`) and
the box–two-ellipse optimum `SpecialFunctions.isGreatest_boxEllipseMax`
(`theorem/SpecialFunctions/EllipseProduct.lean`); the flux budget `JointLimits.fluxBudget` of
`theorem/WPT/JointLimits.lean`; the fundamental-harmonic reading of zero-voltage switching as an
inductive bridge load, as in `theorem/WPT/Gyrator.lean`.

Results.
* `fluxBudget₂` (`K₂ = Ψ₂² − 2(L₂/ω)Q_min`), `productLimit₂` (the largest current product with the
  bridges and the secondary flux, the `productMax` of `|M|`, `L₂`, `K₂` and the bridge radii
  `ρ₂/|ωM|`, `ρ₁/|ωM|`), `softLimit` (the largest current product with the bridges and both flux
  limits, the `boxEllipseMax` of `L₁`, `|M|`, `K₁`, `|M|`, `L₂`, `K₂` and the bridge radii).
* `softLimit_eq` (`softLimit` is the smallest of `JointLimits.productLimit`, `productLimit₂` and the
  `ellipseMax` of the two flux ellipses).
* Secondary flux: `power_sq_le₂` (every admissible operating point with `|ψ₂| ≤ Ψ₂` and
  `Q ≥ Q_min ≥ 0` has `P² + Q_min² ≤ (ωM)² productLimit₂²`), `isGreatest_power₂` (the exact largest
  power `√((ωM)² productLimit₂² − Q_min²)`).
* Both flux limits: `power_sq_le_soft` (every admissible operating point with `|ψ₁| ≤ Ψ₁`,
  `|ψ₂| ≤ Ψ₂` and `Q ≥ Q_min ≥ 0` has `P² + Q_min² ≤ (ωM)² softLimit²`), `exists_power_eq_soft`
  (attained at `Q = Q_min` with `P = √((ωM)² softLimit² − Q_min²)`), `isGreatest_power_soft` (the
  exact largest power).
-/

noncomputable section

namespace powerlib.WPT.SoftLimits

open Complex ComplexConjugate CurrentLimits Gyrator

/-- The secondary flux budget `K₂ = Ψ₂² − 2(L₂/ω)Q_min` left to the currents by a reactive
margin. -/
def fluxBudget₂ (w : Passive.Coupled) (ω Ψ₂ Qmin : ℝ) : ℝ :=
  Ψ₂ ^ 2 - 2 * (w.secondary.L / ω) * Qmin

/-- The largest current product `|I₁||I₂|` in the box of the bridges cut by the secondary flux
ellipse `M²|I₁|² + L₂²|I₂|² ≤ K₂`. -/
def productLimit₂ (w : Passive.Coupled) (ω ρ₁ ρ₂ Ψ₂ Qmin : ℝ) : ℝ :=
  SpecialFunctions.productMax |w.M| w.secondary.L (fluxBudget₂ w ω Ψ₂ Qmin) (ρ₂ / |ω * w.M|)
    (ρ₁ / |ω * w.M|)

/-- The largest current product `|I₁||I₂|` in the box of the bridges cut by both flux ellipses
`L₁²|I₁|² + M²|I₂|² ≤ K₁` and `M²|I₁|² + L₂²|I₂|² ≤ K₂`. -/
def softLimit (w : Passive.Coupled) (ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin : ℝ) : ℝ :=
  SpecialFunctions.boxEllipseMax w.primary.L |w.M| (JointLimits.fluxBudget w ω Ψ₁ Qmin) |w.M|
    w.secondary.L (fluxBudget₂ w ω Ψ₂ Qmin) (ρ₂ / |ω * w.M|) (ρ₁ / |ω * w.M|)

variable {w : Passive.Coupled} {ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin : ℝ}

/-- The soft limit is the smallest of the three relaxations: the bridges with the primary flux,
the bridges with the secondary flux, and the two flux ellipses without the bridges. -/
@[tmio M, powerlib_domain] theorem softLimit_eq :
    softLimit w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin =
      min (min (JointLimits.productLimit w ω ρ₁ ρ₂ Ψ₁ Qmin) (productLimit₂ w ω ρ₁ ρ₂ Ψ₂ Qmin))
        (SpecialFunctions.ellipseMax w.primary.L |w.M| (JointLimits.fluxBudget w ω Ψ₁ Qmin) |w.M|
          w.secondary.L (fluxBudget₂ w ω Ψ₂ Qmin)) :=
  rfl

/-- With `Q ≥ Q_min`, the primary flux limit leaves the currents the ellipse
`L₁²|I₁|² + M²|I₂|² ≤ K₁`. -/
@[tmio M, powerlib_domain] private theorem budget₁_of_flux {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (h : Driven w ω V₁ V₂ I₁ I₂) (hψ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2)
    (hQ : Qmin ≤ (V₁ * conj I₁).im) :
    w.primary.L ^ 2 * ‖I₁‖ ^ 2 + |w.M| ^ 2 * ‖I₂‖ ^ 2 ≤ JointLimits.fluxBudget w ω Ψ₁ Qmin := by
  have hflux := normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h
  simp only [Complex.normSq_eq_norm_sq] at hflux hψ
  have hQflux : 2 * (w.primary.L / ω) * Qmin ≤ 2 * (w.primary.L / ω) * (V₁ * conj I₁).im :=
    mul_le_mul_of_nonneg_left hQ (by positivity)
  rw [sq_abs, JointLimits.fluxBudget]
  linarith

/-- With `Q ≥ Q_min`, the secondary flux limit leaves the currents the ellipse
`M²|I₁|² + L₂²|I₂|² ≤ K₂` (the secondary port sees the same reactive power). -/
@[tmio M, powerlib_domain] private theorem budget₂_of_flux {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₂ : 0 < w.secondary.L)
    (h : Driven w ω V₁ V₂ I₁ I₂) (hψ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2)
    (hQ : Qmin ≤ (V₁ * conj I₁).im) :
    |w.M| ^ 2 * ‖I₁‖ ^ 2 + w.secondary.L ^ 2 * ‖I₂‖ ^ 2 ≤ fluxBudget₂ w ω Ψ₂ Qmin := by
  have hflux := normSq_flux₂_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h
  rw [reactive₂_eq hX₁ hX₂ hR₁ hR₂ h, ← reactive₁_eq hX₁ hX₂ hR₁ hR₂ h] at hflux
  simp only [Complex.normSq_eq_norm_sq] at hflux hψ
  have hQflux : 2 * (w.secondary.L / ω) * Qmin ≤ 2 * (w.secondary.L / ω) * (V₁ * conj I₁).im :=
    mul_le_mul_of_nonneg_left hQ (by positivity)
  rw [sq_abs, fluxBudget₂]
  linarith

/-- At `Q = Q_min`, currents in the primary flux ellipse meet the primary flux limit. -/
@[tmio M, powerlib_domain] private theorem flux₁_le_of_budget {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : ω ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (hQ : (V₁ * conj I₁).im = Qmin)
    (hE : w.primary.L ^ 2 * ‖I₁‖ ^ 2 + |w.M| ^ 2 * ‖I₂‖ ^ 2 ≤
      JointLimits.fluxBudget w ω Ψ₁ Qmin) :
    normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 := by
  rw [normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω h, hQ, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  rw [sq_abs, JointLimits.fluxBudget] at hE
  linarith

/-- At `Q = Q_min`, currents in the secondary flux ellipse meet the secondary flux limit. -/
@[tmio M, powerlib_domain] private theorem flux₂_le_of_budget {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : ω ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (hQ : (V₁ * conj I₁).im = Qmin)
    (hE : |w.M| ^ 2 * ‖I₁‖ ^ 2 + w.secondary.L ^ 2 * ‖I₂‖ ^ 2 ≤ fluxBudget₂ w ω Ψ₂ Qmin) :
    normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 := by
  rw [normSq_flux₂_eq hX₁ hX₂ hR₁ hR₂ hω h, reactive₂_eq hX₁ hX₂ hR₁ hR₂ h,
    ← reactive₁_eq hX₁ hX₂ hR₁ hR₂ h, hQ, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [sq_abs, fluxBudget₂] at hE
  linarith

/-- A current product at most `S` and a reactive margin `Q ≥ Q_min ≥ 0` give
`P² + Q_min² ≤ (ωM)² S²`. -/
@[tmio M, powerlib_domain] private theorem power_sq_le_of_mul_le {S : ℝ} {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (h : Driven w ω V₁ V₂ I₁ I₂)
    (hQ0 : 0 ≤ Qmin) (hQ : Qmin ≤ (V₁ * conj I₁).im) (hab : ‖I₁‖ * ‖I₂‖ ≤ S) :
    (V₁ * conj I₁).re ^ 2 + Qmin ^ 2 ≤ (ω * w.M) ^ 2 * S ^ 2 := by
  have key := power_sq_add_reactive_sq hX₁ hX₂ hR₁ hR₂ h
  simp only [Complex.normSq_eq_norm_sq] at key
  have hab2 : (‖I₁‖ * ‖I₂‖) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (by positivity) hab 2
  have hQ2 : Qmin ^ 2 ≤ (V₁ * conj I₁).im ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
  have : (ω * w.M) ^ 2 * (‖I₁‖ ^ 2 * ‖I₂‖ ^ 2) ≤ (ω * w.M) ^ 2 * S ^ 2 :=
    mul_le_mul_of_nonneg_left (by rw [← mul_pow]; exact hab2) (sq_nonneg _)
  linarith

/-- Realization at the margin: currents of magnitudes `a`, `b` in the bridge box with `a b = S`
and `0 ≤ Q_min ≤ |ωM| S` are driven by admissible bridge phasors at `Q = Q_min` with
`P = √((ωM)² S² − Q_min²)`. -/
@[tmio M, powerlib_domain] private theorem exists_realization_margin {S a b : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haA : a ≤ ρ₂ / |ω * w.M|) (hbB : b ≤ ρ₁ / |ω * w.M|)
    (hab : a * b = S) (hQ0 : 0 ≤ Qmin) (hQS : Qmin ≤ |ω * w.M| * S) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧ ‖I₁‖ = a ∧ ‖I₂‖ = b ∧
      (V₁ * conj I₁).im = Qmin ∧
        (V₁ * conj I₁).re = Real.sqrt ((ω * w.M) ^ 2 * S ^ 2 - Qmin ^ 2) := by
  have hX : 0 ≤ (ω * w.M) ^ 2 * S ^ 2 - Qmin ^ 2 := by
    have : Qmin ^ 2 ≤ (|ω * w.M| * S) ^ 2 := pow_le_pow_left₀ hQ0 hQS 2
    rw [mul_pow, sq_abs] at this
    linarith
  have hPQ : Real.sqrt ((ω * w.M) ^ 2 * S ^ 2 - Qmin ^ 2) ^ 2 + Qmin ^ 2 =
      (ω * w.M) ^ 2 * (a ^ 2 * b ^ 2) := by
    rw [Real.sq_sqrt hX, ← hab]
    ring
  obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hI₁, hI₂, hP, hQ⟩ :=
    exists_realization hX₁ hX₂ hR₁ hR₂ hm ha hb haA hbB hPQ
  exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hI₁, hI₂, hQ, hP⟩

/-! ## The secondary flux limit -/

/-- Every admissible operating point with `|ψ₂| ≤ Ψ₂` and `Q ≥ Q_min ≥ 0` has
`P² + Q_min² ≤ (ωM)² productLimit₂²`. -/
@[tmio M, powerlib_domain] theorem power_sq_le₂ {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₂ : 0 < w.secondary.L)
    (hM : w.M ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) (hQ0 : 0 ≤ Qmin) (hQ : Qmin ≤ (V₁ * conj I₁).im) :
    (V₁ * conj I₁).re ^ 2 + Qmin ^ 2 ≤ (ω * w.M) ^ 2 * productLimit₂ w ω ρ₁ ρ₂ Ψ₂ Qmin ^ 2 := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  obtain ⟨ha, hb⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  exact power_sq_le_of_mul_le hX₁ hX₂ hR₁ hR₂ h hQ0 hQ
    (SpecialFunctions.mul_le_productMax (abs_pos.mpr hM) hL₂ (norm_nonneg I₁) ha (norm_nonneg I₂)
      hb (budget₂_of_flux hX₁ hX₂ hR₁ hR₂ hω hL₂ h hψ hQ))

/-- The exact largest power under the bridges, the secondary flux limit and the reactive margin:
with a nonnegative flux budget and `Q_min ≤ |ωM| productLimit₂`, it is
`√((ωM)² productLimit₂² − Q_min²)`, attained at `Q = Q_min`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power₂
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₂ : 0 < w.secondary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hQ0 : 0 ≤ Qmin)
    (hK : 0 ≤ fluxBudget₂ w ω Ψ₂ Qmin)
    (hQS : Qmin ≤ |ω * w.M| * productLimit₂ w ω ρ₁ ρ₂ Ψ₂ Qmin) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ Qmin ≤ (V₁ * conj I₁).im ∧ P = (V₁ * conj I₁).re}
      (Real.sqrt ((ω * w.M) ^ 2 * productLimit₂ w ω ρ₁ ρ₂ Ψ₂ Qmin ^ 2 - Qmin ^ 2)) := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  constructor
  · obtain ⟨⟨a, b⟩, ⟨ha, haA, hb, hbB, hE⟩, hab⟩ :=
      SpecialFunctions.exists_mul_eq_productMax (abs_pos.mpr hM) hL₂ hK
        (div_nonneg hρ₂ hma.le) (div_nonneg hρ₁ hma.le)
    obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hI₁, hI₂, hQ, hP⟩ :=
      exists_realization_margin (S := productLimit₂ w ω ρ₁ ρ₂ Ψ₂ Qmin) hX₁ hX₂ hR₁ hR₂ hm ha hb
        haA hbB hab hQ0 hQS
    refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, ?_, hQ.ge, hP.symm⟩
    exact flux₂_le_of_budget hX₁ hX₂ hR₁ hR₂ hω.ne' h hQ (by rw [hI₁, hI₂]; exact hE)
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ, hQ, rfl⟩
    have hb := power_sq_le₂ hX₁ hX₂ hR₁ hR₂ hω hL₂ hM h h₁ h₂ hψ hQ0 hQ
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

/-! ## Both flux limits -/

/-- Every admissible operating point with `|ψ₁| ≤ Ψ₁`, `|ψ₂| ≤ Ψ₂` and `Q ≥ Q_min ≥ 0` has
`P² + Q_min² ≤ (ωM)² softLimit²`. -/
@[tmio M, powerlib_domain] theorem power_sq_le_soft {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hL₂ : 0 < w.secondary.L) (hM : w.M ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁)
    (h₂ : ‖V₂‖ ≤ ρ₂) (hψ₁ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2)
    (hψ₂ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) (hQ0 : 0 ≤ Qmin) (hQ : Qmin ≤ (V₁ * conj I₁).im) :
    (V₁ * conj I₁).re ^ 2 + Qmin ^ 2 ≤ (ω * w.M) ^ 2 * softLimit w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin ^ 2 := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hMa : 0 < |w.M| := abs_pos.mpr hM
  obtain ⟨ha, hb⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  exact power_sq_le_of_mul_le hX₁ hX₂ hR₁ hR₂ h hQ0 hQ
    (SpecialFunctions.mul_le_boxEllipseMax hL₁ hMa hMa hL₂ (norm_nonneg I₁) ha (norm_nonneg I₂) hb
      (budget₁_of_flux hX₁ hX₂ hR₁ hR₂ hω hL₁ h hψ₁ hQ)
      (budget₂_of_flux hX₁ hX₂ hR₁ hR₂ hω hL₂ h hψ₂ hQ))

/-- The soft limit is attained: with nonnegative flux budgets and `Q_min ≤ |ωM| softLimit`,
admissible bridge phasors run at `Q = Q_min` within both flux limits and transfer
`√((ωM)² softLimit² − Q_min²)`. -/
@[tmio M, powerlib_domain] theorem exists_power_eq_soft
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hL₂ : 0 < w.secondary.L) (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hQ0 : 0 ≤ Qmin)
    (hK₁ : 0 ≤ JointLimits.fluxBudget w ω Ψ₁ Qmin) (hK₂ : 0 ≤ fluxBudget₂ w ω Ψ₂ Qmin)
    (hQS : Qmin ≤ |ω * w.M| * softLimit w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin) :
    ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧
        (V₁ * conj I₁).im = Qmin ∧
          (V₁ * conj I₁).re =
            Real.sqrt ((ω * w.M) ^ 2 * softLimit w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin ^ 2 - Qmin ^ 2) := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hMa : 0 < |w.M| := abs_pos.mpr hM
  obtain ⟨⟨a, b⟩, ⟨ha, haA, hb, hbB, hE₁, hE₂⟩, hab⟩ :=
    SpecialFunctions.exists_mul_eq_boxEllipseMax hL₁ hMa hMa hL₂ hK₁ hK₂
      (div_nonneg hρ₂ hma.le) (div_nonneg hρ₁ hma.le)
  obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hI₁, hI₂, hQ, hP⟩ :=
    exists_realization_margin (S := softLimit w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin) hX₁ hX₂ hR₁ hR₂ hm ha hb
      haA hbB hab hQ0 hQS
  refine ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, ?_, ?_, hQ, hP⟩
  · exact flux₁_le_of_budget hX₁ hX₂ hR₁ hR₂ hω.ne' h hQ (by rw [hI₁, hI₂]; exact hE₁)
  · exact flux₂_le_of_budget hX₁ hX₂ hR₁ hR₂ hω.ne' h hQ (by rw [hI₁, hI₂]; exact hE₂)

/-- The exact largest power under the bridges, both flux limits and the reactive margin:
`√((ωM)² softLimit² − Q_min²)`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_soft
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hL₂ : 0 < w.secondary.L) (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hQ0 : 0 ≤ Qmin)
    (hK₁ : 0 ≤ JointLimits.fluxBudget w ω Ψ₁ Qmin) (hK₂ : 0 ≤ fluxBudget₂ w ω Ψ₂ Qmin)
    (hQS : Qmin ≤ |ω * w.M| * softLimit w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧
          Qmin ≤ (V₁ * conj I₁).im ∧ P = (V₁ * conj I₁).re}
      (Real.sqrt ((ω * w.M) ^ 2 * softLimit w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin ^ 2 - Qmin ^ 2)) := by
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hQ, hP⟩ :=
      exists_power_eq_soft hX₁ hX₂ hR₁ hR₂ hω hL₁ hL₂ hM hρ₁ hρ₂ hQ0 hK₁ hK₂ hQS
    exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hQ.ge, hP.symm⟩
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hQ, rfl⟩
    have hb := power_sq_le_soft hX₁ hX₂ hR₁ hR₂ hω hL₁ hL₂ hM h h₁ h₂ hψ₁ hψ₂ hQ0 hQ
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

end powerlib.WPT.SoftLimits
