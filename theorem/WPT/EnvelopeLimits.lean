import theorem.WPT.ReactiveLimits
import theorem.WPT.FluxLimits
import theorem.SpecialFunctions.Helly

/-! # The exact power limit of the lossless resonant link under both bridges and both flux limits

The largest power the lossless resonant link transfers when both bridge voltages and both coil
fluxes are bounded at once, `‖V₁‖ ≤ ρ₁`, `‖V₂‖ ≤ ρ₂`, `|ψ₁| ≤ Ψ₁`, `|ψ₂| ≤ Ψ₂`, with the reactive
power free in sign, for every value of the parameters. It is the smallest of the optima of the
four relaxations that drop one of the four constraints (`envelopeLimit`):
* `ReactiveLimits.limit₁` (both bridges and the primary flux: the secondary flux dropped),
* `ReactiveLimits.limit₂` (both bridges and the secondary flux),
* `FluxLimits.bridgeLimit₁` (both fluxes and the primary bridge),
* `FluxLimits.bridgeLimit₂` (both fluxes and the secondary bridge).
These are the four regimes of the optimum: the primary flux binds (with the bridges), the
secondary flux binds (with the bridges), both fluxes bind with the primary bridge, or both fluxes
bind with the secondary bridge. For coupling `k < 1` (`L₁L₂ − M² > 0`, assumed throughout) the
statement covers every parameter value with no case condition, and in that range it supersedes
`ReactiveLimits.isGreatest_power_both₁`, `ReactiveLimits.isGreatest_power_both₂`, which are exact
only when the optimizer of one flux bound meets the other.

The proof lifts an operating point to `(α, β, c) = (|I₁|², |I₂|², Q/ω)` with `Q = Im(V₁Ī₁)`. There
`P² = ω²(M²αβ − c²)` (`Gyrator.power_sq_add_reactive_sq`), both flux limits are linear,
`L₁²α + M²β + 2L₁c ≤ Ψ₁²` and `M²α + L₂²β + 2L₂c ≤ Ψ₂²` (`Gyrator.normSq_flux₁_eq`,
`Gyrator.normSq_flux₂_eq`), and so are the bridges, `α ≤ (ρ₂/|ωM|)²`, `β ≤ (ρ₁/|ωM|)²`. The level
set `P² ≥ ω² t` is the convex cone `α, β ≥ 0`, `t + c² ≤ M²αβ` (`t ≥ 0`). Five convex sets in
`ℝ³`: dropping the cone leaves the origin, dropping a constraint leaves the lift of the optimizer of
the corresponding relaxation, whose power reaches the envelope. Helly's theorem
(`SpecialFunctions.nonempty_iInter_of_drop_one`) gives a common point; lowering `α` until the cone
is tight keeps the linear constraints (their `α`-coefficients are nonnegative), and the phases are
free (`Gyrator.exists_realization`), so the envelope is attained.

Model boundary.
* The lossless resonant link of `theorem/WPT/Gyrator.lean`: the coil pair `w : Passive.Coupled`
  with lossless windings `R₁ = R₂ = 0`, both coils resonant `X₁(ω) = X₂(ω) = 0`, both ports
  driven by the fundamental phasors `V₁`, `V₂` of two bridges (`CurrentLimits.Driven`), RMS
  phasors in sinusoidal steady state; `ω > 0`, `L₁, L₂ > 0`, `M ≠ 0` and coupling `k < 1`, written
  `L₁L₂ − M² > 0`; for attainment `ρ₁, ρ₂ ≥ 0`. The flux bounds may have either sign (only `Ψ_k²`
  enters).
* The bridge limits bound the fundamentals `‖V_k‖ ≤ ρ_k`; the flux limits bound the fundamental
  flux-linkage phasors (`Passive.Coupled.flux₁`, `flux₂`) as `normSq ψ_k ≤ Ψ_k²`; the nonlinear
  magnetization curve is not modelled. No sign condition on the reactive power (soft switching
  is not required). Fundamental-harmonic approximation; lossy windings are not covered.

Source: the four relaxations `ReactiveLimits.isGreatest_power₁`, `ReactiveLimits.isGreatest_power₂`
(`theorem/WPT/ReactiveLimits.lean`), `FluxLimits.isGreatest_power_bridge₁`,
`FluxLimits.isGreatest_power_bridge₂` (`theorem/WPT/FluxLimits.lean`); the gyrator identities and
realization of `theorem/WPT/Gyrator.lean`; Helly's theorem (E. Helly, 1923) in the drop-one form
of `theorem/SpecialFunctions/Helly.lean`; the convexity of the rotated second-order cone
`{t + c² ≤ m αβ, α, β ≥ 0}`, from `(t + cc')² ≤ (t + c²)(t + c'²)` and AM–GM.

Results.
* `envelopeLimit` (definition): the smallest of `limit₁`, `limit₂`, `bridgeLimit₁`, `bridgeLimit₂`.
* `power_sq_le_envelope`: every operating point within both bridges and both flux limits has
  `P² ≤ envelopeLimit`.
* `isGreatest_power_envelope`: the exact largest power under both bridges and both flux limits is
  `√envelopeLimit`.
-/

noncomputable section

namespace powerlib.WPT.EnvelopeLimits

open Complex ComplexConjugate CurrentLimits

/-- The squared power limit under both bridges and both flux bounds: the smallest of the optima
of the four relaxations that drop one constraint. -/
def envelopeLimit (w : Passive.Coupled) (ω ρ₁ ρ₂ Ψ₁ Ψ₂ : ℝ) : ℝ :=
  min (min (ReactiveLimits.limit₁ w ω ρ₁ ρ₂ Ψ₁) (ReactiveLimits.limit₂ w ω ρ₁ ρ₂ Ψ₂))
    (min (FluxLimits.bridgeLimit₁ w ω ρ₁ Ψ₁ Ψ₂) (FluxLimits.bridgeLimit₂ w ω ρ₂ Ψ₁ Ψ₂))

variable {w : Passive.Coupled} {ω ρ₁ ρ₂ Ψ₁ Ψ₂ : ℝ}

/-- Under both bridges and both flux bounds, whatever the reactive power:
`P² ≤ envelopeLimit`. -/
@[tmio M, powerlib_domain] theorem power_sq_le_envelope {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hL₂ : 0 < w.secondary.L) (hM : w.M ≠ 0) (hD : 0 < w.primary.L * w.secondary.L - w.M ^ 2)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ₁ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2) (hψ₂ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) :
    (V₁ * conj I₁).re ^ 2 ≤ envelopeLimit w ω ρ₁ ρ₂ Ψ₁ Ψ₂ :=
  le_min (ReactiveLimits.power_sq_le_both hX₁ hX₂ hR₁ hR₂ hω hL₁ hL₂ hM h h₁ h₂ hψ₁ hψ₂)
    (le_min (FluxLimits.power_sq_le_bridgeLimit₁ hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hD h h₁ hψ₁ hψ₂)
      (FluxLimits.power_sq_le_bridgeLimit₂ hX₁ hX₂ hR₁ hR₂ hω hL₂ hM hD h h₂ hψ₁ hψ₂))

/-- The rotated second-order cone `{(α, β, c) | α, β ≥ 0, t + c² ≤ m α β}` is convex for
`t, m ≥ 0`. -/
@[tmio T, powerlib_foundation] private theorem convex_cone {t m : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m) :
    Convex ℝ {x : ℝ × ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ t + x.2.2 ^ 2 ≤ m * (x.1 * x.2.1)} := by
  rintro ⟨α, β, c⟩ ⟨hα, hβ, hx⟩ ⟨α', β', c'⟩ ⟨hα', hβ', hy⟩ a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at *
  obtain rfl : b = 1 - a := by linarith
  refine ⟨add_nonneg (mul_nonneg ha hα) (mul_nonneg hb hα'),
    add_nonneg (mul_nonneg ha hβ) (mul_nonneg hb hβ'), ?_⟩
  have hprod : (t + c ^ 2) * (t + c' ^ 2) ≤ (m * (α * β')) * (m * (α' * β)) := by
    calc (t + c ^ 2) * (t + c' ^ 2) ≤ (m * (α * β)) * (m * (α' * β')) :=
          mul_le_mul hx hy (by positivity) (by positivity)
      _ = (m * (α * β')) * (m * (α' * β)) := by ring
  have hS : 0 ≤ m * (α * β') + m * (α' * β) := by positivity
  -- `(t + cc')² ≤ (t + c²)(t + c'²) ≤ (mαβ')(mα'β) ≤ ((mαβ' + mα'β)/2)²`
  have hsq : (2 * (t + c * c')) ^ 2 ≤ (m * (α * β') + m * (α' * β)) ^ 2 := by
    nlinarith [sq_nonneg (m * (α * β') - m * (α' * β)), mul_nonneg ht (sq_nonneg (c - c'))]
  have key : 2 * (t + c * c') ≤ m * (α * β') + m * (α' * β) := (abs_le_of_sq_le_sq' hsq hS).2
  nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg a),
    mul_le_mul_of_nonneg_left hy (sq_nonneg (1 - a)),
    mul_le_mul_of_nonneg_left key (mul_nonneg ha hb)]

/-- The exact largest power under both bridges and both flux bounds, whatever the reactive power,
for every parameter value: `√envelopeLimit`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_envelope
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hω : 0 < ω) (hL₁ : 0 < w.primary.L)
    (hL₂ : 0 < w.secondary.L) (hM : w.M ≠ 0) (hD : 0 < w.primary.L * w.secondary.L - w.M ^ 2)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧
          P = (V₁ * conj I₁).re} (Real.sqrt (envelopeLimit w ω ρ₁ ρ₂ Ψ₁ Ψ₂)) := by
  refine ⟨?_, ?_⟩
  swap
  · rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, rfl⟩
    exact (le_abs_self _).trans (Real.abs_le_sqrt
      (power_sq_le_envelope hX₁ hX₂ hR₁ hR₂ hω hL₁ hL₂ hM hD h h₁ h₂ hψ₁ hψ₂))
  have hm : ω * w.M ≠ 0 := mul_ne_zero hω.ne' hM
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hA : 0 ≤ ρ₂ / |ω * w.M| := div_nonneg hρ₂ hma.le
  have hB : 0 ≤ ρ₁ / |ω * w.M| := div_nonneg hρ₁ hma.le
  -- the four relaxed limits are nonnegative, and the envelope is below each of them
  have n₁ : 0 ≤ ReactiveLimits.limit₁ w ω ρ₁ ρ₂ Ψ₁ := mul_nonneg (by positivity)
    (SpecialFunctions.reactiveMax_nonneg (by positivity) (by positivity) (sq_nonneg _))
  have n₂ : 0 ≤ ReactiveLimits.limit₂ w ω ρ₁ ρ₂ Ψ₂ := mul_nonneg (by positivity)
    (SpecialFunctions.reactiveMax_nonneg (by positivity) (by positivity) (sq_nonneg _))
  have n₃ : 0 ≤ FluxLimits.bridgeLimit₁ w ω ρ₁ Ψ₁ Ψ₂ := mul_nonneg (by positivity)
    (SpecialFunctions.reactiveMax_nonneg (by positivity) (by positivity) (by positivity))
  have n₄ : 0 ≤ FluxLimits.bridgeLimit₂ w ω ρ₂ Ψ₁ Ψ₂ := mul_nonneg (by positivity)
    (SpecialFunctions.reactiveMax_nonneg (by positivity) (by positivity) (by positivity))
  set E := envelopeLimit w ω ρ₁ ρ₂ Ψ₁ Ψ₂
  have hE0 : 0 ≤ E := le_min (le_min n₁ n₂) (le_min n₃ n₄)
  have hE₁ : E ≤ ReactiveLimits.limit₁ w ω ρ₁ ρ₂ Ψ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hE₂ : E ≤ ReactiveLimits.limit₂ w ω ρ₁ ρ₂ Ψ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hE₃ : E ≤ FluxLimits.bridgeLimit₁ w ω ρ₁ Ψ₁ Ψ₂ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hE₄ : E ≤ FluxLimits.bridgeLimit₂ w ω ρ₂ Ψ₁ Ψ₂ :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨t, htdef⟩ : ∃ t, t = E / ω ^ 2 := ⟨_, rfl⟩
  have ht : 0 ≤ t := htdef ▸ div_nonneg hE0 (sq_nonneg ω)
  -- the lift `(|I₁|², |I₂|², Q/ω)` of an operating point: power and fluxes in its coordinates
  have lift : ∀ {V₁ V₂ I₁ I₂ : ℂ}, Driven w ω V₁ V₂ I₁ I₂ →
      (V₁ * conj I₁).re ^ 2 =
          ω ^ 2 * (w.M ^ 2 * (normSq I₁ * normSq I₂) - ((V₁ * conj I₁).im / ω) ^ 2) ∧
        normSq (w.flux₁ I₁ I₂) = w.primary.L ^ 2 * normSq I₁ + w.M ^ 2 * normSq I₂ +
          2 * w.primary.L * ((V₁ * conj I₁).im / ω) ∧
        normSq (w.flux₂ I₁ I₂) = w.M ^ 2 * normSq I₁ + w.secondary.L ^ 2 * normSq I₂ +
          2 * w.secondary.L * ((V₁ * conj I₁).im / ω) := by
    intro V₁ V₂ I₁ I₂ h
    have key := Gyrator.power_sq_add_reactive_sq hX₁ hX₂ hR₁ hR₂ h
    have hf₁ := Gyrator.normSq_flux₁_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h
    have hf₂ := Gyrator.normSq_flux₂_eq hX₁ hX₂ hR₁ hR₂ hω.ne' h
    rw [Gyrator.reactive₂_eq hX₁ hX₂ hR₁ hR₂ h, ← Gyrator.reactive₁_eq hX₁ hX₂ hR₁ hR₂ h] at hf₂
    have hQ : ω ^ 2 * ((V₁ * conj I₁).im / ω) ^ 2 = (V₁ * conj I₁).im ^ 2 := by field_simp
    refine ⟨by linear_combination key + hQ, ?_, ?_⟩
    · rw [hf₁]
      ring
    · rw [hf₂]
      ring
  -- membership of the lift in the five sets
  have m₀ : ∀ {V₁ V₂ I₁ I₂ : ℂ}, Driven w ω V₁ V₂ I₁ I₂ → ‖V₂‖ ≤ ρ₂ →
      normSq I₁ ≤ (ρ₂ / |ω * w.M|) ^ 2 := fun h h₂ => by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((FluxLimits.norm_voltage₂_le_iff hX₁ hX₂ hR₁ hR₂ hm h).mp h₂) 2
  have m₁ : ∀ {V₁ V₂ I₁ I₂ : ℂ}, Driven w ω V₁ V₂ I₁ I₂ → ‖V₁‖ ≤ ρ₁ →
      normSq I₂ ≤ (ρ₁ / |ω * w.M|) ^ 2 := fun h h₁ => by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((FluxLimits.norm_voltage₁_le_iff hX₁ hX₂ hR₁ hR₂ hm h).mp h₁) 2
  have m₂ : ∀ {V₁ V₂ I₁ I₂ : ℂ}, Driven w ω V₁ V₂ I₁ I₂ → normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 →
      w.primary.L ^ 2 * normSq I₁ + w.M ^ 2 * normSq I₂ +
        2 * w.primary.L * ((V₁ * conj I₁).im / ω) ≤ Ψ₁ ^ 2 := fun h hψ =>
    (lift h).2.1 ▸ hψ
  have m₃ : ∀ {V₁ V₂ I₁ I₂ : ℂ}, Driven w ω V₁ V₂ I₁ I₂ → normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 →
      w.M ^ 2 * normSq I₁ + w.secondary.L ^ 2 * normSq I₂ +
        2 * w.secondary.L * ((V₁ * conj I₁).im / ω) ≤ Ψ₂ ^ 2 := fun h hψ =>
    (lift h).2.2 ▸ hψ
  have m₄ : ∀ {V₁ V₂ I₁ I₂ : ℂ}, Driven w ω V₁ V₂ I₁ I₂ → E ≤ (V₁ * conj I₁).re ^ 2 →
      0 ≤ normSq I₁ ∧ 0 ≤ normSq I₂ ∧
        t + ((V₁ * conj I₁).im / ω) ^ 2 ≤ w.M ^ 2 * (normSq I₁ * normSq I₂) := by
    intro V₁ V₂ I₁ I₂ h hP
    refine ⟨Complex.normSq_nonneg _, Complex.normSq_nonneg _, ?_⟩
    have hP' := (lift h).1 ▸ hP
    have hdiv : E / ω ^ 2 ≤ w.M ^ 2 * (normSq I₁ * normSq I₂) - ((V₁ * conj I₁).im / ω) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    rw [htdef]
    linarith
  -- an optimizer whose power reaches the envelope
  have reach : ∀ {L : ℝ} {V₁ I₁ : ℂ}, 0 ≤ L → E ≤ L → Real.sqrt L = (V₁ * conj I₁).re →
      E ≤ (V₁ * conj I₁).re ^ 2 := fun hL hEL hP => by
    rw [← hP, Real.sq_sqrt hL]
    exact hEL
  -- the five convex sets in `ℝ³`
  let F : Fin 5 → Set (ℝ × ℝ × ℝ) := ![{x | x.1 ≤ (ρ₂ / |ω * w.M|) ^ 2},
    {x | x.2.1 ≤ (ρ₁ / |ω * w.M|) ^ 2},
    {x | w.primary.L ^ 2 * x.1 + w.M ^ 2 * x.2.1 + 2 * w.primary.L * x.2.2 ≤ Ψ₁ ^ 2},
    {x | w.M ^ 2 * x.1 + w.secondary.L ^ 2 * x.2.1 + 2 * w.secondary.L * x.2.2 ≤ Ψ₂ ^ 2},
    {x | 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ t + x.2.2 ^ 2 ≤ w.M ^ 2 * (x.1 * x.2.1)}]
  have half : ∀ c₁ c₂ c₃ K : ℝ,
      Convex ℝ {x : ℝ × ℝ × ℝ | c₁ * x.1 + c₂ * x.2.1 + c₃ * x.2.2 ≤ K} :=
    fun _ _ _ K => convex_halfSpace_le
      ⟨fun _ _ => by simp only [Prod.fst_add, Prod.snd_add]; ring,
        fun _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩ K
  have hconv : ∀ i, Convex ℝ (F i) := by
    intro i
    fin_cases i
    · exact convex_halfSpace_le ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _
    · exact convex_halfSpace_le ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _
    · exact half _ _ _ _
    · exact half _ _ _ _
    · exact convex_cone ht (sq_nonneg _)
  have hdrop : ∀ j, ∃ x, ∀ i, i ≠ j → x ∈ F i := by
    intro j
    fin_cases j
    · -- without the secondary bridge: the optimizer of `bridgeLimit₁`
      obtain ⟨V₁, V₂, I₁, I₂, h₁, h, hψ₁, hψ₂, hP⟩ :=
        (FluxLimits.isGreatest_power_bridge₁ (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂) hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hD
          hρ₁).1
      refine ⟨(normSq I₁, normSq I₂, (V₁ * conj I₁).im / ω), fun i hi => ?_⟩
      fin_cases i
      · exact absurd rfl hi
      · exact m₁ h h₁
      · exact m₂ h hψ₁
      · exact m₃ h hψ₂
      · exact m₄ h (reach n₃ hE₃ hP)
    · -- without the primary bridge: the optimizer of `bridgeLimit₂`
      obtain ⟨V₁, V₂, I₁, I₂, h₂, h, hψ₁, hψ₂, hP⟩ :=
        (FluxLimits.isGreatest_power_bridge₂ (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂) hX₁ hX₂ hR₁ hR₂ hω hL₂ hM hD
          hρ₂).1
      refine ⟨(normSq I₁, normSq I₂, (V₁ * conj I₁).im / ω), fun i hi => ?_⟩
      fin_cases i
      · exact m₀ h h₂
      · exact absurd rfl hi
      · exact m₂ h hψ₁
      · exact m₃ h hψ₂
      · exact m₄ h (reach n₄ hE₄ hP)
    · -- without the primary flux: the optimizer of `limit₂`
      obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₂, hP⟩ :=
        (ReactiveLimits.isGreatest_power₂ (Ψ₂ := Ψ₂) hX₁ hX₂ hR₁ hR₂ hω hL₂ hM hρ₁ hρ₂).1
      refine ⟨(normSq I₁, normSq I₂, (V₁ * conj I₁).im / ω), fun i hi => ?_⟩
      fin_cases i
      · exact m₀ h h₂
      · exact m₁ h h₁
      · exact absurd rfl hi
      · exact m₃ h hψ₂
      · exact m₄ h (reach n₂ hE₂ hP)
    · -- without the secondary flux: the optimizer of `limit₁`
      obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hP⟩ :=
        (ReactiveLimits.isGreatest_power₁ (Ψ₁ := Ψ₁) hX₁ hX₂ hR₁ hR₂ hω hL₁ hM hρ₁ hρ₂).1
      refine ⟨(normSq I₁, normSq I₂, (V₁ * conj I₁).im / ω), fun i hi => ?_⟩
      fin_cases i
      · exact m₀ h h₂
      · exact m₁ h h₁
      · exact m₂ h hψ₁
      · exact absurd rfl hi
      · exact m₄ h (reach n₁ hE₁ hP)
    · -- without the power level: the origin
      refine ⟨(0, 0, 0), fun i hi => ?_⟩
      fin_cases i
      · exact sq_nonneg (ρ₂ / |ω * w.M|)
      · exact sq_nonneg (ρ₁ / |ω * w.M|)
      · show w.primary.L ^ 2 * 0 + w.M ^ 2 * 0 + 2 * w.primary.L * 0 ≤ Ψ₁ ^ 2
        simpa using sq_nonneg Ψ₁
      · show w.M ^ 2 * 0 + w.secondary.L ^ 2 * 0 + 2 * w.secondary.L * 0 ≤ Ψ₂ ^ 2
        simpa using sq_nonneg Ψ₂
      · exact absurd rfl hi
  obtain ⟨⟨α, β, c⟩, hx⟩ := SpecialFunctions.nonempty_iInter_of_drop_one (d := 3) (by simp) F
    hconv hdrop
  have h₀ : α ≤ (ρ₂ / |ω * w.M|) ^ 2 := hx 0
  have h₁ : β ≤ (ρ₁ / |ω * w.M|) ^ 2 := hx 1
  have h₂ : w.primary.L ^ 2 * α + w.M ^ 2 * β + 2 * w.primary.L * c ≤ Ψ₁ ^ 2 := hx 2
  have h₃ : w.M ^ 2 * α + w.secondary.L ^ 2 * β + 2 * w.secondary.L * c ≤ Ψ₂ ^ 2 := hx 3
  obtain ⟨hα, hβ, h₄⟩ : 0 ≤ α ∧ 0 ≤ β ∧ t + c ^ 2 ≤ w.M ^ 2 * (α * β) := hx 4
  -- lower `α` until the cone is tight: `M² α' β = t + c²`, `α' ≤ α`
  obtain ⟨α', hα'def⟩ : ∃ α', α' = (t + c ^ 2) / (w.M ^ 2 * β) := ⟨_, rfl⟩
  have hα'0 : 0 ≤ α' := hα'def ▸ div_nonneg (by positivity) (by positivity)
  have hα'α : α' ≤ α := hα'def ▸ div_le_of_le_mul₀ (by positivity) hα (by linarith)
  have hcone : w.M ^ 2 * (α' * β) = t + c ^ 2 := by
    rcases eq_or_lt_of_le hβ with hβ0 | hβpos
    · rw [← hβ0, mul_zero, mul_zero] at h₄
      rw [← hβ0, mul_zero, mul_zero]
      linarith [sq_nonneg c]
    · rw [hα'def]
      field_simp
  have ha : Real.sqrt α' ≤ ρ₂ / |ω * w.M| := by
    calc Real.sqrt α' ≤ Real.sqrt ((ρ₂ / |ω * w.M|) ^ 2) := Real.sqrt_le_sqrt (hα'α.trans h₀)
      _ = ρ₂ / |ω * w.M| := Real.sqrt_sq hA
  have hb : Real.sqrt β ≤ ρ₁ / |ω * w.M| := by
    calc Real.sqrt β ≤ Real.sqrt ((ρ₁ / |ω * w.M|) ^ 2) := Real.sqrt_le_sqrt h₁
      _ = ρ₁ / |ω * w.M| := Real.sqrt_sq hB
  have hPQ : Real.sqrt E ^ 2 + (ω * c) ^ 2 =
      (ω * w.M) ^ 2 * (Real.sqrt α' ^ 2 * Real.sqrt β ^ 2) := by
    rw [Real.sq_sqrt hE0, Real.sq_sqrt hα'0, Real.sq_sqrt hβ,
      show (ω * w.M) ^ 2 * (α' * β) = ω ^ 2 * (w.M ^ 2 * (α' * β)) by ring, hcone, htdef]
    field_simp
  obtain ⟨V₁, V₂, I₁, I₂, hV₁, hV₂, h, hI₁, hI₂, hP, hQ⟩ :=
    Gyrator.exists_realization hX₁ hX₂ hR₁ hR₂ hm (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ha hb
      hPQ
  have hn₁ : normSq I₁ = α' := by rw [Complex.normSq_eq_norm_sq, hI₁, Real.sq_sqrt hα'0]
  have hn₂ : normSq I₂ = β := by rw [Complex.normSq_eq_norm_sq, hI₂, Real.sq_sqrt hβ]
  have hc : (V₁ * conj I₁).im / ω = c := by rw [hQ]; field_simp
  refine ⟨V₁, V₂, I₁, I₂, hV₁, hV₂, h, ?_, ?_, hP.symm⟩
  · rw [(lift h).2.1, hn₁, hn₂, hc]
    linarith [mul_le_mul_of_nonneg_left hα'α (sq_nonneg w.primary.L)]
  · rw [(lift h).2.2, hn₁, hn₂, hc]
    linarith [mul_le_mul_of_nonneg_left hα'α (sq_nonneg w.M)]

end powerlib.WPT.EnvelopeLimits
