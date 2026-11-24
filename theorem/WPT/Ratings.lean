import theorem.WPT.ReactiveLimits

/-! # Device current ratings and winding thermal ratings of the lossless resonant link

Besides its voltage, a bridge is limited by the current its switches carry. In the
fundamental-harmonic picture the current through the conducting switches of the bridge on coil `k`
is the winding current `I_k`, so a switch RMS current rating is a bound `‖I_k‖ ≤ J_k` on the
winding current phasor. On the lossless resonant link the bridges set the currents crosswise (the
gyrator law `V₁ = jωM I₂`, `V₂ = jωM I₁`, `Gyrator.voltages_eq`), so `‖V₁‖ = |ωM| ‖I₂‖` and
`‖V₂‖ = |ωM| ‖I₁‖`: the current rating of one coil is a voltage limit of the other bridge. The
bridge radii together with the current ratings are exactly bridges of the smaller rated radii
`ρ₁⋆ = min(ρ₁, |ωM| J₂)`, `ρ₂⋆ = min(ρ₂, |ωM| J₁)`; a primary bridge voltage above `|ωM| J₂` would
drive more than the rated secondary current and is never usable. Every exact limit stated with
bridge radii therefore holds with the rated radii in their place (`exists_rated_iff`): the exact
power becomes `ρ₁⋆ρ₂⋆/|ωM|`, and the exact power under a primary flux bound becomes
`ReactiveLimits.limit₁` at the rated radii.

A winding thermal rating is a current rating: the copper loss `R‖I‖²` of a winding with `R > 0`
stays at most `P_max` exactly when `‖I‖ ≤ √(P_max/R)`.

Model boundary.
* The lossless resonant link of `theorem/WPT/CurrentLimits.lean`: the coil pair
  `w : Passive.Coupled` with lossless windings `R₁ = R₂ = 0`, both coils resonant
  `X₁(ω) = X₂(ω) = 0`, `ωM ≠ 0`, both ports driven by the fundamental voltage phasors `V₁`, `V₂` of
  two bridges (`CurrentLimits.Driven`), RMS phasors in sinusoidal steady state, bridge radii
  `‖V_k‖ ≤ ρ_k`. The flux-bound corollary adds `ω > 0`, `L₁ > 0`, `M ≠ 0` and the primary flux
  bound of `theorem/WPT/ReactiveLimits.lean`.
* Current ratings are bounds `‖I_k‖ ≤ J_k` on the RMS fundamental phasors of the winding currents.
  Reading them as switch RMS current ratings is the fundamental-harmonic approximation: harmonic
  currents, the sharing of a leg current between transistor and antiparallel diode, switching
  transients and peak-current ratings are not modelled, nor are device temperatures and losses
  (bridge conduction loss is `theorem/WPT/BridgeLosses.lean`).
* `copperLoss_le_iff` concerns one winding with `R > 0` at an arbitrary current phasor; a winding
  with `R > 0` is no longer lossless, and its electrical equations are those of the lossy link
  (`theorem/WPT/LossyLimits.lean`). Applying a thermal rating to the currents of the lossless link
  (resistance neglected in the currents but not in the heating) is the usual low-loss estimate, a
  reading and not a theorem here. Thermal dynamics (time constants, cooling) are not modelled:
  the rating bounds the steady-state copper loss.

Source: the fundamental-harmonic analysis of the series–series link driven by two active bridges
(Steigerwald, *IEEE Trans. Power Electron.* 3 (1988) 174–182, for the fundamental-harmonic
analysis of resonant converters) with the switch current ratings of the bridges; the gyrator law
`Gyrator.voltages_eq` (`theorem/WPT/Gyrator.lean`), the reachable bidisk
`CurrentLimits.reachable_iff` and the power limit `CurrentLimits.power_le`,
`CurrentLimits.exists_power_eq` (`theorem/WPT/CurrentLimits.lean`), and the flux-limited power
`ReactiveLimits.isGreatest_power₁` (`theorem/WPT/ReactiveLimits.lean`).

Results.
* `ratedRadius₁` (`ρ₁⋆ = min(ρ₁, |ωM| J₂)`), `ratedRadius₂` (`ρ₂⋆ = min(ρ₂, |ωM| J₁)`).
* `reachable_current_rated_iff` (with current ratings the reachable currents of the lossless
  resonant link are exactly the bidisk `‖I₁‖ ≤ min(ρ₂/|ωM|, J₁)`, `‖I₂‖ ≤ min(ρ₁/|ωM|, J₂)`).
* `ratings_iff_ratedRadius` (at an operating point of the lossless resonant link:
  `‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ ‖I₁‖ ≤ J₁ ∧ ‖I₂‖ ≤ J₂ ↔ ‖V₁‖ ≤ ρ₁⋆ ∧ ‖V₂‖ ≤ ρ₂⋆`), `exists_rated_iff`
  (for every further condition `C` on the operating point, the operating points admissible under
  bridges and ratings satisfying `C` exist iff those admissible under the rated radii do).
* `isGreatest_ratedPower` (bridges and current ratings: the exact largest power is
  `ρ₁⋆ρ₂⋆/|ωM|`), `isGreatest_ratedPower₁` (with a primary flux bound `‖ψ₁‖² ≤ Ψ₁²` as well,
  whatever the reactive power: the exact largest power is `√(ReactiveLimits.limit₁)` at the rated
  radii).
* `copperLoss_le_iff` (a winding with `R > 0` and `P_max ≥ 0`: `R‖I‖² ≤ P_max ↔ ‖I‖ ≤ √(P_max/R)`).
-/

noncomputable section

namespace powerlib.WPT.Ratings

open Complex ComplexConjugate CurrentLimits

/-- The rated primary radius `ρ₁⋆ = min(ρ₁, |ωM| J₂)`: the primary bridge voltage that the bridge
can apply and that keeps the secondary current within its rating `J₂`. -/
def ratedRadius₁ (w : Passive.Coupled) (ω ρ₁ J₂ : ℝ) : ℝ := min ρ₁ (|ω * w.M| * J₂)

/-- The rated secondary radius `ρ₂⋆ = min(ρ₂, |ωM| J₁)`: the secondary bridge voltage that the
bridge can apply and that keeps the primary current within its rating `J₁`. -/
def ratedRadius₂ (w : Passive.Coupled) (ω ρ₂ J₁ : ℝ) : ℝ := min ρ₂ (|ω * w.M| * J₁)

variable {w : Passive.Coupled} {ω ρ₁ ρ₂ J₁ J₂ : ℝ}

/-- With switch current ratings `‖I_k‖ ≤ J_k`, the reachable currents of the lossless resonant
link are exactly the bidisk `‖I₁‖ ≤ min(ρ₂/|ωM|, J₁)`, `‖I₂‖ ≤ min(ρ₁/|ωM|, J₂)`. -/
@[tmio M, powerlib_domain] theorem reachable_current_rated_iff (I₁ I₂ : ℂ)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0) :
    (∃ V₁ V₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧ ‖I₁‖ ≤ J₁ ∧ ‖I₂‖ ≤ J₂) ↔
      ‖I₁‖ ≤ min (ρ₂ / |ω * w.M|) J₁ ∧ ‖I₂‖ ≤ min (ρ₁ / |ω * w.M|) J₂ := by
  rw [le_min_iff, le_min_iff]
  constructor
  · rintro ⟨V₁, V₂, h₁, h₂, h, j₁, j₂⟩
    obtain ⟨r₁, r₂⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
    exact ⟨⟨r₁, j₁⟩, ⟨r₂, j₂⟩⟩
  · rintro ⟨⟨r₁, j₁⟩, ⟨r₂, j₂⟩⟩
    obtain ⟨V₁, V₂, h₁, h₂, h⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mpr ⟨r₁, r₂⟩
    exact ⟨V₁, V₂, h₁, h₂, h, j₁, j₂⟩

/-- The transfer principle: at an operating point of the lossless resonant link, the bridge radii
and the current ratings hold together iff the bridge voltages lie within the rated radii,
`‖V₁‖ ≤ min(ρ₁, |ωM| J₂)`, `‖V₂‖ ≤ min(ρ₂, |ωM| J₁)` (since `‖V₁‖ = |ωM| ‖I₂‖`,
`‖V₂‖ = |ωM| ‖I₁‖`). -/
@[tmio M, powerlib_domain] theorem ratings_iff_ratedRadius {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ ‖I₁‖ ≤ J₁ ∧ ‖I₂‖ ≤ J₂) ↔
      ‖V₁‖ ≤ ratedRadius₁ w ω ρ₁ J₂ ∧ ‖V₂‖ ≤ ratedRadius₂ w ω ρ₂ J₁ := by
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  obtain ⟨e₁, e₂⟩ := Gyrator.voltages_eq hX₁ hX₂ hR₁ hR₂ h
  have n₁ : ‖V₁‖ = |ω * w.M| * ‖I₂‖ := by
    rw [e₁, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have n₂ : ‖V₂‖ = |ω * w.M| * ‖I₁‖ := by
    rw [e₂, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have c₁ : ‖V₁‖ ≤ |ω * w.M| * J₂ ↔ ‖I₂‖ ≤ J₂ := by rw [n₁, mul_le_mul_iff_right₀ hma]
  have c₂ : ‖V₂‖ ≤ |ω * w.M| * J₁ ↔ ‖I₁‖ ≤ J₁ := by rw [n₂, mul_le_mul_iff_right₀ hma]
  rw [ratedRadius₁, ratedRadius₂, le_min_iff, le_min_iff, c₁, c₂]
  tauto

/-- Every limit stated with bridge radii holds with the rated radii: for every further condition
`C` on the operating point, there is an operating point of the lossless resonant link within the
bridge radii and the current ratings satisfying `C` iff there is one within the rated radii
`ρ₁⋆`, `ρ₂⋆` satisfying `C`. -/
@[tmio M, powerlib_domain] theorem exists_rated_iff (C : ℂ → ℂ → ℂ → ℂ → Prop)
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0) :
    (∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ ‖I₁‖ ≤ J₁ ∧ ‖I₂‖ ≤ J₂ ∧
        Driven w ω V₁ V₂ I₁ I₂ ∧ C V₁ V₂ I₁ I₂) ↔
      ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ratedRadius₁ w ω ρ₁ J₂ ∧ ‖V₂‖ ≤ ratedRadius₂ w ω ρ₂ J₁ ∧
        Driven w ω V₁ V₂ I₁ I₂ ∧ C V₁ V₂ I₁ I₂ := by
  constructor
  · rintro ⟨V₁, V₂, I₁, I₂, h₁, h₂, j₁, j₂, h, hC⟩
    obtain ⟨r₁, r₂⟩ := (ratings_iff_ratedRadius hX₁ hX₂ hR₁ hR₂ hm h).mp ⟨h₁, h₂, j₁, j₂⟩
    exact ⟨V₁, V₂, I₁, I₂, r₁, r₂, h, hC⟩
  · rintro ⟨V₁, V₂, I₁, I₂, r₁, r₂, h, hC⟩
    obtain ⟨h₁, h₂, j₁, j₂⟩ := (ratings_iff_ratedRadius hX₁ hX₂ hR₁ hR₂ hm h).mpr ⟨r₁, r₂⟩
    exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, j₁, j₂, h, hC⟩

/-- The exact largest power of the lossless resonant link under the bridge radii and the switch
current ratings: `ρ₁⋆ρ₂⋆/|ωM|` with the rated radii `ρ₁⋆ = min(ρ₁, |ωM| J₂)`,
`ρ₂⋆ = min(ρ₂, |ωM| J₁)`. -/
@[tmio M, powerlib_domain] theorem isGreatest_ratedPower
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ ‖I₁‖ ≤ J₁ ∧ ‖I₂‖ ≤ J₂ ∧
        Driven w ω V₁ V₂ I₁ I₂ ∧ P = (V₁ * conj I₁).re}
      (ratedRadius₁ w ω ρ₁ J₂ * ratedRadius₂ w ω ρ₂ J₁ / |ω * w.M|) := by
  have hr₁ : 0 ≤ ratedRadius₁ w ω ρ₁ J₂ := le_min hρ₁ (by positivity)
  have hr₂ : 0 ≤ ratedRadius₂ w ω ρ₂ J₁ := le_min hρ₂ (by positivity)
  rw [show {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ ‖I₁‖ ≤ J₁ ∧ ‖I₂‖ ≤ J₂ ∧
      Driven w ω V₁ V₂ I₁ I₂ ∧ P = (V₁ * conj I₁).re} =
      {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ratedRadius₁ w ω ρ₁ J₂ ∧
        ‖V₂‖ ≤ ratedRadius₂ w ω ρ₂ J₁ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧ P = (V₁ * conj I₁).re} from
    Set.ext fun P => exists_rated_iff (fun V₁ _ I₁ _ => P = (V₁ * conj I₁).re) hX₁ hX₂ hR₁ hR₂ hm]
  constructor
  · obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hP⟩ := exists_power_eq w ω hX₁ hX₂ hR₁ hR₂ hm hr₁ hr₂
    exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hP.symm⟩
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, rfl⟩
    exact power_le w ω hX₁ hX₂ hR₁ hR₂ hm h h₁ h₂

/-- The exact largest power of the lossless resonant link under the bridge radii, the switch
current ratings and the primary flux bound `‖ψ₁‖² ≤ Ψ₁²`, whatever the reactive power:
`√(ReactiveLimits.limit₁)` evaluated at the rated radii `ρ₁⋆`, `ρ₂⋆`. -/
@[tmio M, powerlib_domain] theorem isGreatest_ratedPower₁ {Ψ₁ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hM : w.M ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ ‖I₁‖ ≤ J₁ ∧ ‖I₂‖ ≤ J₂ ∧
        Driven w ω V₁ V₂ I₁ I₂ ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ P = (V₁ * conj I₁).re}
      (Real.sqrt (ReactiveLimits.limit₁ w ω (ratedRadius₁ w ω ρ₁ J₂)
        (ratedRadius₂ w ω ρ₂ J₁) Ψ₁)) := by
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hr₁ : 0 ≤ ratedRadius₁ w ω ρ₁ J₂ := le_min hρ₁ (by positivity)
  have hr₂ : 0 ≤ ratedRadius₂ w ω ρ₂ J₁ := le_min hρ₂ (by positivity)
  rw [show {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ ‖I₁‖ ≤ J₁ ∧ ‖I₂‖ ≤ J₂ ∧
      Driven w ω V₁ V₂ I₁ I₂ ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ P = (V₁ * conj I₁).re} =
      {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ratedRadius₁ w ω ρ₁ J₂ ∧
        ‖V₂‖ ≤ ratedRadius₂ w ω ρ₂ J₁ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
          normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ P = (V₁ * conj I₁).re} from
    Set.ext fun P => exists_rated_iff
      (fun V₁ _ I₁ I₂ => normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ P = (V₁ * conj I₁).re)
      hX₁ hX₂ hR₁ hR₂ hm]
  exact ReactiveLimits.isGreatest_power₁ hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hr₁ hr₂

/-- A winding thermal rating is a current rating: the copper loss `R‖I‖²` of a winding with
`R > 0` stays at most `P_max ≥ 0` exactly when the current phasor obeys `‖I‖ ≤ √(P_max/R)`. -/
@[tmio M, powerlib_domain] theorem copperLoss_le_iff {b : Passive.SeriesRLC} (hR : 0 < b.R)
    {Pmax : ℝ} (hP : 0 ≤ Pmax) (I' : ℂ) :
    b.R * ‖I'‖ ^ 2 ≤ Pmax ↔ ‖I'‖ ≤ Real.sqrt (Pmax / b.R) := by
  rw [Real.le_sqrt (norm_nonneg _) (div_nonneg hP hR.le), le_div_iff₀ hR, mul_comm]

end powerlib.WPT.Ratings
