import theorem.ParametricResonance.SlowFlowBranches
import theorem.Periodic.Persistence
import theorem.Periodic.LevelsNonlinear

/-! # The first-order boundary of a pumped operating point: decided only by `O(ε²)` terms

The first-order (averaged, level L2) verdict on a 2:1-pumped mode is the sign of
`|g/2|² − (s² + d²)` (`Branches.slowFlow_unstable_iff`, `TwoToOne.averaging_stable`,
`TwoToOne.averaging_unstable`; at a forced operating point the threshold `|V̂||g₁| ≶ 2|λ₁|` of
`Periodic.Levels.orbit_stable_below_threshold` / `orbit_unstable_above_threshold`). On the
boundary `s² + d² = |g/2|²`, `s ≥ 0`, it says nothing:

* in the exact resonant normal form `ż = (−σ + jΩ) z + c e^{jωt} z̄` the boundary is marginal: the
  multiplier `−1` is present, none lies outside the unit circle, and the monodromy is not Schur
  stable;
* the first-order data do not decide: adding the damping `±ε²κ` (a multiple `∓ε²κ I` of the
  identity, `κ > 0`) to the normal form of a boundary datum gives, for every `ε > 0`, a Schur-stable
  and a Floquet-unstable system with the same first-order data; for the complete two-state system
  `TwoToOne.full` the same holds for all small `ε > 0` once `κ` exceeds an explicit bound;
* the decisive quantity is the `O(ε²)` correction to the critical slow exponent. In the normal form
  with second-order data `σ = ε(s + εs₂)`, `ω/2 − Ω = ε(d + εd₂)`, `c = ε(ĝ + εc₂)` the gap is
  exactly `|c|² − σ² − (ω/2 − Ω)² = ε³(2D + εQ)`, `D = Re(ĝ̄ c₂) − s s₂ − d d₂`,
  `Q = |c₂|² − s₂² − d₂²`, and (for `s + εs₂ > 0`) Schur stability holds iff `2D + εQ < 0`,
  Floquet instability iff `2D + εQ > 0` (read through `−σ + √(σ² + gap)`, the critical slow
  exponent is `ε² D/s + O(ε³)`; this expansion is not formalized). For the complete two-state
  system the role of `D/s` is played by
  `λ₂ = −mixedDet(M, N₂)/(2sT) + θ`, with `M` the slow-flow matrix, `N₂ = ∫₀ᵀ F(t) ∫₀ᵗ F` the second
  Picard term of the rotating-frame matrix `F` (`TwoToOne.stdForm`), `mixedDet M N = tr M tr N −
  tr(MN)` and `θ` an added `ε²θ I`: `λ₂ < 0` gives Schur stability and `λ₂ > 0` Floquet instability
  for all small `ε > 0` (`full_boundary_shift`). What is proved is the sign of
  `det(I − Φ_y(T)) = ε³ T mixedDet(M, N₂) + O(ε⁴)`; through `det(I − Φ_y(T)) = (1 − μ₁)(1 − μ₂)`
  with `1 − μ₂ ≈ 2εsT` this reads as the critical exponent `ε² λ₂ + O(ε³)` (a reading here; the
  expansion of the critical multipliers and exponent is proved in
  `theorem/ParametricResonance/CriticalExponent.lean`, `critical_multipliers`,
  `full_critical_exponent`).

What is and is not decided at the forced operating point of `Periodic.LevelsNonlinear`. Its
theorems decide the forced orbit for `|V̂||g₁| < 2|λ₁|` (with `Re λ₁ < 0`) and for
`|V̂||g₁| > 2|λ₁|`, for all small `ε`, at levels L1 and L0; the trichotomy leaves exactly the
boundary `|V̂||g₁| = 2|λ₁|` (`forced_threshold_boundary_iff`). For the two-state model
(`TwoToOne.full`, first-order eigenvalue shift `λ₁ = −s − jd`, pump `g`,
`two_state_first_order`) this boundary is the slow-flow boundary, and there both verdicts occur
among `O(ε²)` completions of the variational matrix (`full_boundary_completions`), decided by
`λ₂`. For the `n`-state forced orbit the `O(ε²)` part of its variational matrix (third Taylor
coefficients of the field, second-order forced response, coupling to the stable block) and its
second-order averaging are not formalized here: no theorem in this module decides the nonlinear
forced orbit on the boundary; this is done, from the second and third derivatives of a `C⁴` field,
in `theorem/ParametricResonance/SmoothForcedOrbitSecond.lean` (`smooth_orbit_boundary`,
`smooth_orbit_at_threshold`, levels L1 and L0). Given the second-order data of an `n`-state block
monodromy (critical block `N`, couplings `Q₁`, `R₁`, stable block `E`), the boundary is decided by
the sign of `mixedDet(M, N + Q₁(I + E)⁻¹R₁)` in `theorem/ParametricResonance/BlockBoundary.lean`;
the closed form of `mixedDet(M, N₂)` for the two-state standard form is
`theorem/ParametricResonance/SecondOrderClosedForm.lean`, and the case `s = 0` is
`theorem/ParametricResonance/ZeroDampingBranch.lean`. Even an exactly marginal variational
equation would leave the step L1 → L0 open (multiplier `−1`: the flip normal form of
`theorem/Periodic/CriticalMultiplier.lean`, reduced to it for a periodic orbit with a stable
complement in `theorem/Periodic/FlipReduction.lean`, with the period map derived from the field
in `theorem/Periodic/FlipOrbit.lean`).

Scope.
* Normal form: `NormalForm.nfMatrix σ Ω ω c` (state `(Re z, Im z)`, pump frequency `ω > 0`, period
  `T = 2π/ω`, monodromy `Periodic.monodromy … T 0`), slow-flow parameters `σ`, `Δ = ω/2 − Ω`,
  `c`; first-order data `(s, d, ĝ)` in the scaling `σ = εs`, `Δ = εd`, `c = εĝ`.
* Complete two-state system: `TwoToOne.full s d ω A ε` (`σ = εs`, `ω/2 − Ω = εd`, modulation
  `ε Re{A e^{jωt}}`, slow-flow pump `ĝ = g/2`, `g = Element.pump A left right`), with an added
  `ε²θ I`; statements for all sufficiently small `ε > 0`, `s > 0` (a simple critical slow
  exponent; at `s = 0` the two slow exponents collide).
* Generic expansions: `ẋ = A(t) x` on `ℝ^X` with continuous bounded `A` (operator `L∞` norm), the
  transition matrix of `theorem/Periodic/Transition.lean`; the second-order Picard expansion of
  `Φ(t, 0)`. Two-state Jury conditions of `theorem/ParametricResonance/PeriodicAveraging.lean`.
* Generic mathematics; no model family.

Source: the wave-4 question of this library (the boundary cases the linear levels leave
undecided: the first-order boundary at a pumped / forced operating point); second-order averaging
and the Picard expansion of the monodromy (Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 5,
parametrically excited systems, transition curves beyond first order; Yakubovich–Starzhinskii,
*Linear Differential Equations with Periodic Coefficients*, the small-parameter method);
`NormalForm.schurStable_monodromy_nf_iff`,
`Branches.nf_floquetUnstable_iff`, `Branches.nf_spectrum`, `TwoToOne.monodromy_full`,
`TwoToOne.integral_stdForm`, `Periodic.transition_sub_smul_one`.

Results.
* Normal form: `nfMatrix_sub_smul_one`, `nfMatrix_add_smul_one` (damping is a scalar shift);
  `nf_boundary_marginal` (on the boundary: multiplier `−1`, not Schur stable, not Floquet
  unstable); `nf_completions` (for every boundary datum, `κ > 0`, `ε > 0`: `−ε²κ I` gives Schur
  stability, `+ε²κ I` Floquet instability); `nf_gap_eq` (the exact gap `ε³(2D + εQ)`);
  `nf_second_order_iff` (exact verdicts by the sign of `2D + εQ`); `nf_second_order` (for `s > 0`:
  `D > 0` unstable, `D < 0` stable, for all small `ε`).
* Generic: `secondTerm`, `norm_transition_sub_second_le`
  (`‖Φ(t, 0) − I − ∫A − ∫A∫A‖ ≤ (Mt)³ ‖I‖ e^{Mt}`), `monodromy_expansion_two`
  (`Φ_ε(T) = I + εT F̄ + ε² N₂ + O(ε³)`); `mixedDet`, `det_add_fin_two`, `mixedDet_one_right`;
  `critical_jury` (a family `P(ε) = I + εT M + ε² N + O(ε³)` with `det M = 0 > tr M` is Schur stable
  for small `ε` if `mixedDet M N > 0` and has a multiplier `> 1` if `mixedDet M N < 0`).
* Two-state system: `full_boundary_shift` (the verdict of `full + ε²θ I` on the boundary by the sign
  of `mixedDet(M, N₂) − 2sθT`), `full_boundary_decided` (`θ = 0`), `full_boundary_completions`
  (`2sκT > |mixedDet(M, N₂)|`: `full − ε²κ I` Schur stable, `full + ε²κ I` Floquet unstable).
* Forced operating point: `forced_threshold_boundary_iff` (the boundary of the threshold of
  `Periodic.Levels`), `two_state_first_order` (for `TwoToOne.full`: `A₀' = base s (−d)`,
  `λ₁ = −s − jd`, and the slow-flow boundary is `|g| = 2|λ₁|`).

Corrections.
None: an extension (the boundary of the first-order criterion and its decision at second order).

Family and connection conclusions.
None: static evidence on periodic linear systems.
-/

noncomputable section
namespace powerlib.ParametricResonance.Boundary

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator Interval
open _root_.powerlib.ParametricResonance.NormalForm (nfMatrix)

/-! ## The exact normal form on the first-order boundary -/

/-- Added damping is a scalar shift: `A(t) − δ I` is the normal form with `σ + δ`. -/
@[tmio T, powerlib_foundation] theorem nfMatrix_sub_smul_one (σ Ω ω : ℝ) (c : ℂ) (δ t : ℝ) :
    nfMatrix σ Ω ω c t - δ • (1 : Matrix (Fin 2) (Fin 2) ℝ) = nfMatrix (σ + δ) Ω ω c t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nfMatrix] <;> ring

/-- Added anti-damping: `A(t) + δ I` is the normal form with `σ − δ`. -/
@[tmio T, powerlib_foundation] theorem nfMatrix_add_smul_one (σ Ω ω : ℝ) (c : ℂ) (δ t : ℝ) :
    nfMatrix σ Ω ω c t + δ • (1 : Matrix (Fin 2) (Fin 2) ℝ) = nfMatrix (σ - δ) Ω ω c t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nfMatrix] <;> ring

/-- **The first-order boundary is marginal in the normal form.** For `σ ≥ 0` and
`σ² + (ω/2 − Ω)² = |c|²` the slow exponent `0` gives the Floquet multiplier `−1`, the monodromy is
not Schur stable, and no multiplier lies outside the unit circle: neither Floquet criterion
applies. -/
@[tmio T, powerlib_foundation] theorem nf_boundary_marginal {σ Ω ω : ℝ} (hω : 0 < ω) {c : ℂ}
    (hσ : 0 ≤ σ) (hb : σ ^ 2 + (ω / 2 - Ω) ^ 2 = ‖c‖ ^ 2) :
    (-1 : ℂ) ∈ spectrum ℂ ((Periodic.monodromy (nfMatrix σ Ω ω c) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)) ∧
      ¬ LTI.SchurStable (Periodic.monodromy (nfMatrix σ Ω ω c) (2 * Real.pi / ω) 0) ∧
      ¬ Periodic.FloquetUnstable (nfMatrix σ Ω ω c) (2 * Real.pi / ω) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Branches.nf_spectrum σ Ω hω c]
    refine ⟨0, ?_, ?_⟩
    · rw [slowFlow_root_iff]
      have : ‖c‖ ^ 2 - (ω / 2 - Ω) ^ 2 = σ ^ 2 := by linarith
      rw [this]
      push_cast
      ring
    · rw [Branches.exp_add_half_pump 0 hω.ne']
      simp
  · rw [NormalForm.schurStable_monodromy_nf_iff σ Ω hω]
    rintro ⟨-, h⟩
    linarith
  · rw [Branches.nf_floquetUnstable_iff σ Ω hω]
    rintro (⟨h, -⟩ | ⟨⟨-, h⟩, -⟩)
    · linarith
    · linarith

/-- **The first-order data do not decide.** For every first-order datum `(s, d, ĝ)` on the
boundary (`s ≥ 0`, `s² + d² = |ĝ|²`) of the normal form `σ = εs`, `ω/2 − Ω = εd`, `c = εĝ`, and
every `κ > 0`, `ε > 0`: the completion with the damping `ε²κ` (the matrix `A(t) − ε²κ I`) is Schur
stable and the completion with the anti-damping `ε²κ` (`A(t) + ε²κ I`) is Floquet unstable. -/
@[tmio T, powerlib_foundation] theorem nf_completions {s d ω κ ε : ℝ} (hω : 0 < ω) {g : ℂ}
    (hs : 0 ≤ s) (hb : s ^ 2 + d ^ 2 = ‖g‖ ^ 2) (hκ : 0 < κ) (hε : 0 < ε) :
    LTI.SchurStable (Periodic.monodromy (fun t => nfMatrix (ε * s) (ω / 2 - ε * d) ω (ε * g) t -
        (ε ^ 2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (2 * Real.pi / ω) 0) ∧
      Periodic.FloquetUnstable (fun t => nfMatrix (ε * s) (ω / 2 - ε * d) ω (ε * g) t +
        (ε ^ 2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (2 * Real.pi / ω) := by
  have hc : ‖(ε : ℂ) * g‖ ^ 2 = ε ^ 2 * (s ^ 2 + d ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le, mul_pow, hb]
  have hΔ : ω / 2 - (ω / 2 - ε * d) = ε * d := by ring
  refine ⟨?_, ?_⟩
  · have e : (fun t => nfMatrix (ε * s) (ω / 2 - ε * d) ω (ε * g) t -
        (ε ^ 2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        nfMatrix (ε * s + ε ^ 2 * κ) (ω / 2 - ε * d) ω (ε * g) := by
      funext t; exact nfMatrix_sub_smul_one _ _ _ _ _ t
    rw [e, NormalForm.schurStable_monodromy_nf_iff _ _ hω, hc, hΔ]
    have h3 : 0 < 2 * (ε ^ 3 * s * κ) + ε ^ 4 * κ ^ 2 := by positivity
    have h4 : (ε * s + ε ^ 2 * κ) ^ 2 + (ε * d) ^ 2 - ε ^ 2 * (s ^ 2 + d ^ 2) =
        2 * (ε ^ 3 * s * κ) + ε ^ 4 * κ ^ 2 := by ring
    constructor
    · positivity
    · linarith
  · have e : (fun t => nfMatrix (ε * s) (ω / 2 - ε * d) ω (ε * g) t +
        (ε ^ 2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        nfMatrix (ε * s - ε ^ 2 * κ) (ω / 2 - ε * d) ω (ε * g) := by
      funext t; exact nfMatrix_add_smul_one _ _ _ _ _ t
    rw [e, Branches.nf_floquetUnstable_iff _ _ hω, hc, hΔ]
    by_cases hneg : ε * s - ε ^ 2 * κ < 0
    · exact Or.inl ⟨hneg, fun h => absurd h.1 (not_le.mpr hneg)⟩
    · push Not at hneg
      refine Or.inr ⟨⟨hneg, ?_⟩, not_lt.mpr hneg⟩
      have hκ2 : 0 < ε ^ 2 * κ := by positivity
      have hlt : ε * s - ε ^ 2 * κ < ε * s := by linarith
      have h5 : (ε * s - ε ^ 2 * κ) ^ 2 < (ε * s) ^ 2 := pow_lt_pow_left₀ hlt hneg (by norm_num)
      have h6 : ε ^ 2 * (s ^ 2 + d ^ 2) = (ε * s) ^ 2 + (ε * d) ^ 2 := by ring
      linarith

/-- **The exact gap at second order.** On the first-order boundary `s² + d² = |ĝ|²`, with the
second-order data `σ = ε(s + εs₂)`, `Δ = ε(d + εd₂)`, `c = ε(ĝ + εc₂)`:
`|c|² − σ² − Δ² = ε³ (2D + εQ)`, `D = Re(ĝ̄ c₂) − s s₂ − d d₂`, `Q = |c₂|² − s₂² − d₂²`. -/
@[tmio T, powerlib_foundation] theorem nf_gap_eq (s d s₂ d₂ ε : ℝ) (g c₂ : ℂ)
    (hb : s ^ 2 + d ^ 2 = ‖g‖ ^ 2) :
    ‖(ε : ℂ) * (g + ε * c₂)‖ ^ 2 - (ε * (s + ε * s₂)) ^ 2 - (ε * (d + ε * d₂)) ^ 2 =
      ε ^ 3 * (2 * ((starRingEnd ℂ g * c₂).re - s * s₂ - d * d₂) +
        ε * (‖c₂‖ ^ 2 - s₂ ^ 2 - d₂ ^ 2)) := by
  have hb' : s ^ 2 + d ^ 2 = g.re * g.re + g.im * g.im := by
    rw [hb, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  linear_combination (-(ε ^ 2)) * hb'

/-- **The exact second-order verdict of the normal form.** On the first-order boundary, with the
second-order data of `nf_gap_eq` and `s + εs₂ > 0`, `ε > 0`: the monodromy is Schur stable iff
`2D + εQ < 0`, and the normal form is Floquet unstable iff `2D + εQ > 0`. -/
@[tmio T, powerlib_foundation] theorem nf_second_order_iff {s d s₂ d₂ ω ε : ℝ} (hω : 0 < ω)
    {g c₂ : ℂ} (hb : s ^ 2 + d ^ 2 = ‖g‖ ^ 2) (hε : 0 < ε) (hσ : 0 < s + ε * s₂) :
    (LTI.SchurStable (Periodic.monodromy (nfMatrix (ε * (s + ε * s₂))
        (ω / 2 - ε * (d + ε * d₂)) ω (ε * (g + ε * c₂))) (2 * Real.pi / ω) 0) ↔
        2 * ((starRingEnd ℂ g * c₂).re - s * s₂ - d * d₂) + ε * (‖c₂‖ ^ 2 - s₂ ^ 2 - d₂ ^ 2) < 0) ∧
      (Periodic.FloquetUnstable (nfMatrix (ε * (s + ε * s₂)) (ω / 2 - ε * (d + ε * d₂)) ω
          (ε * (g + ε * c₂))) (2 * Real.pi / ω) ↔
        0 < 2 * ((starRingEnd ℂ g * c₂).re - s * s₂ - d * d₂) +
          ε * (‖c₂‖ ^ 2 - s₂ ^ 2 - d₂ ^ 2)) := by
  have hgap := nf_gap_eq s d s₂ d₂ ε g c₂ hb
  have hΔ : ω / 2 - (ω / 2 - ε * (d + ε * d₂)) = ε * (d + ε * d₂) := by ring
  have hε3 : 0 < ε ^ 3 := pow_pos hε 3
  have hσ' : 0 < ε * (s + ε * s₂) := mul_pos hε hσ
  set G := 2 * ((starRingEnd ℂ g * c₂).re - s * s₂ - d * d₂) + ε * (‖c₂‖ ^ 2 - s₂ ^ 2 - d₂ ^ 2)
    with hG
  refine ⟨?_, ?_⟩
  · rw [NormalForm.schurStable_monodromy_nf_iff _ _ hω, hΔ]
    constructor
    · rintro ⟨-, h⟩
      by_contra hc
      push Not at hc
      nlinarith
    · intro h
      exact ⟨hσ', by nlinarith⟩
  · rw [Branches.nf_floquetUnstable_iff _ _ hω, hΔ]
    constructor
    · rintro (⟨h, -⟩ | ⟨⟨-, h⟩, -⟩)
      · linarith
      · by_contra hc
        push Not at hc
        nlinarith
    · intro h
      exact Or.inr ⟨⟨hσ'.le, by nlinarith⟩, not_lt.mpr hσ'.le⟩

/-- **The decisive quantity of the normal form.** On the first-order boundary with `s > 0`, the
second-order coefficient `D = Re(ĝ̄ c₂) − s s₂ − d d₂` decides for all small `ε > 0`: `D > 0` gives
Floquet instability, `D < 0` Schur stability (read as the critical slow exponent
`ε² D/s + O(ε³)`, an expansion not formalized). -/
@[tmio T, powerlib_foundation] theorem nf_second_order {s d s₂ d₂ ω : ℝ} (hω : 0 < ω)
    {g c₂ : ℂ} (hb : s ^ 2 + d ^ 2 = ‖g‖ ^ 2) (hs : 0 < s) :
    (0 < (starRingEnd ℂ g * c₂).re - s * s₂ - d * d₂ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Periodic.FloquetUnstable (nfMatrix (ε * (s + ε * s₂)) (ω / 2 - ε * (d + ε * d₂)) ω
          (ε * (g + ε * c₂))) (2 * Real.pi / ω)) ∧
      ((starRingEnd ℂ g * c₂).re - s * s₂ - d * d₂ < 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        LTI.SchurStable (Periodic.monodromy (nfMatrix (ε * (s + ε * s₂))
          (ω / 2 - ε * (d + ε * d₂)) ω (ε * (g + ε * c₂))) (2 * Real.pi / ω) 0)) := by
  set D := (starRingEnd ℂ g * c₂).re - s * s₂ - d * d₂ with hD
  set Q := ‖c₂‖ ^ 2 - s₂ ^ 2 - d₂ ^ 2 with hQ
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ 0 < s + ε * s₂ ∧ ε * |Q| < |D| ∨ D = 0 := by
    by_cases hD0 : D = 0
    · exact Filter.Eventually.of_forall fun _ => Or.inr hD0
    have hpos : 0 < min (s / (|s₂| + 1)) (|D| / (|Q| + 1)) :=
      lt_min (by positivity) (div_pos (abs_pos.mpr hD0) (by positivity))
    filter_upwards [Ioo_mem_nhdsGT hpos] with ε ⟨h0, h1⟩
    refine Or.inl ⟨h0, ?_, ?_⟩
    · have h2 : ε * (|s₂| + 1) < s := by
        have := h1.trans_le (min_le_left _ _)
        rwa [lt_div_iff₀ (by positivity)] at this
      have := neg_abs_le s₂
      nlinarith
    · have h2 : ε * (|Q| + 1) < |D| := by
        have := h1.trans_le (min_le_right _ _)
        rwa [lt_div_iff₀ (by positivity)] at this
      nlinarith
  refine ⟨fun hDp => ?_, fun hDn => ?_⟩
  · filter_upwards [hsmall] with ε hε
    rcases hε with ⟨h0, hσ, hq⟩ | h0
    · refine ((nf_second_order_iff hω hb h0 hσ).2).mpr ?_
      have := neg_abs_le Q
      have : |D| = D := abs_of_pos hDp
      nlinarith
    · exact absurd h0 hDp.ne'
  · filter_upwards [hsmall] with ε hε
    rcases hε with ⟨h0, hσ, hq⟩ | h0
    · refine ((nf_second_order_iff hω hb h0 hσ).1).mpr ?_
      have := le_abs_self Q
      have : |D| = -D := abs_of_neg hDn
      nlinarith
    · exact absurd h0 hDn.ne

/-! ## The second-order expansion of the monodromy -/

section Expansion

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The second Picard term over `[0, t]`: `∫₀ᵗ A(r) (∫₀ʳ A(u) du) dr`. -/
def secondTerm (A : ℝ → Matrix X X ℝ) (t : ℝ) : Matrix X X ℝ :=
  ∫ r in (0 : ℝ)..t, A r * ∫ u in (0 : ℝ)..r, A u

/-- `‖Φ(t, 0) − I − ∫₀ᵗ A − ∫₀ᵗ A ∫₀ʳ A‖ ≤ (M t)³ ‖I‖ e^{Mt}`. -/
@[tmio T, powerlib_foundation] theorem norm_transition_sub_second_le {A : ℝ → Matrix X X ℝ}
    {M : ℝ} (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) (hM0 : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ‖Periodic.transition A t 0 - 1 - (∫ r in (0 : ℝ)..t, A r) - secondTerm A t‖ ≤
      M * t * (M * t * (M * t * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * t)))) := by
  have hprim : Continuous (fun r => ∫ u in (0 : ℝ)..r, A u) :=
    intervalIntegral.continuous_primitive (fun a b => hA.intervalIntegrable a b) 0
  have hc1 : Continuous (fun r => A r * Periodic.transition A r 0) :=
    hA.mul (Averaging.continuous_transition hA)
  have hc2 : Continuous (fun r => A r * ∫ u in (0 : ℝ)..r, A u) := hA.mul hprim
  have hc3 : Continuous (fun r => A r * Periodic.transition A r 0 - A r) := hc1.sub hA
  have e : Periodic.transition A t 0 - 1 - (∫ r in (0 : ℝ)..t, A r) - secondTerm A t =
      ∫ r in (0 : ℝ)..t, A r * (Periodic.transition A r 0 - 1 - ∫ u in (0 : ℝ)..r, A u) := by
    rw [Averaging.transition_eq_integral hA t, add_sub_cancel_left, secondTerm,
      ← intervalIntegral.integral_sub (hc1.intervalIntegrable 0 t) (hA.intervalIntegrable 0 t),
      ← intervalIntegral.integral_sub (hc3.intervalIntegrable 0 t) (hc2.intervalIntegrable 0 t)]
    congr 1
    funext r
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one]
  rw [e]
  have hb : ∀ r ∈ Ι (0 : ℝ) t,
      ‖A r * (Periodic.transition A r 0 - 1 - ∫ u in (0 : ℝ)..r, A u)‖ ≤
        M * (M * t * (M * t * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * t)))) := by
    intro r hr
    rw [Set.uIoc_of_le ht] at hr
    refine (norm_mul_le _ _).trans (mul_le_mul (hM r) ?_ (norm_nonneg _) hM0)
    refine (Averaging.norm_transition_sub_integral_le hA hM hM0 hr.1.le).trans ?_
    have h1 : 0 ≤ ‖(1 : Matrix X X ℝ)‖ := norm_nonneg _
    have hrt : r ≤ t := hr.2
    have : Real.exp (M * r) ≤ Real.exp (M * t) := Real.exp_le_exp.2 (by nlinarith)
    have : M * r ≤ M * t := by nlinarith
    have : 0 ≤ M * r := mul_nonneg hM0 hr.1.le
    gcongr
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht] at this
  linarith [this]

/-- **The second-order expansion of the monodromy of `ẏ = εF(t) y`:**
`Φ_ε(T) = I + εT F̄ + ε² N₂ + R_ε`, `N₂ = secondTerm F T`, with
`‖R_ε‖ ≤ ε³ (MT)³ ‖I‖ e^{MT}` for `0 ≤ ε ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem monodromy_expansion_two {F : ℝ → Matrix X X ℝ}
    {M T ε : ℝ} (hF : Continuous F) (hM : ∀ t, ‖F t‖ ≤ M) (hM0 : 0 ≤ M) (hT : 0 ≤ T)
    {Fbar : Matrix X X ℝ} (havg : ∫ r in (0 : ℝ)..T, F r = T • Fbar) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    ‖Periodic.monodromy (fun t => ε • F t) T 0 - 1 - (ε * T) • Fbar - ε ^ 2 • secondTerm F T‖ ≤
      ε ^ 3 * (M * T * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * T))))) := by
  have hA : Continuous (fun t => ε • F t) := hF.const_smul ε
  have hMε : ∀ t, ‖ε • F t‖ ≤ ε * M := fun t => by
    rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left (hM t) hε
  have h := norm_transition_sub_second_le hA hMε (mul_nonneg hε hM0) hT
  have hsec : secondTerm (fun t => ε • F t) T = ε ^ 2 • secondTerm F T := by
    unfold secondTerm
    have : ∀ r : ℝ, (ε • F r) * ∫ u in (0 : ℝ)..r, ε • F u =
        (ε ^ 2) • (F r * ∫ u in (0 : ℝ)..r, F u) := fun r => by
      rw [intervalIntegral.integral_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
    simp_rw [this]
    rw [intervalIntegral.integral_smul]
  rw [intervalIntegral.integral_smul, havg, smul_smul, hsec] at h
  rw [Periodic.monodromy, zero_add]
  refine h.trans ?_
  have hexp : Real.exp (ε * M * T) ≤ Real.exp (M * T) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg hM0 hT])
  have h1 : 0 ≤ ‖(1 : Matrix X X ℝ)‖ := norm_nonneg _
  have hMT : 0 ≤ M * T := mul_nonneg hM0 hT
  calc ε * M * T * (ε * M * T * (ε * M * T * (‖(1 : Matrix X X ℝ)‖ *
        Real.exp (ε * M * T))))
      = ε ^ 3 * (M * T * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ *
          Real.exp (ε * M * T))))) := by ring
    _ ≤ ε ^ 3 * (M * T * (M * T * (M * T * (‖(1 : Matrix X X ℝ)‖ * Real.exp (M * T))))) := by
        gcongr

end Expansion

/-! ## Two-state Jury conditions at a simple critical slow exponent -/

section Jury

/-- `tr(adj M · N) = tr M tr N − tr(M N)` for `2 × 2` matrices: the mixed term of
`det(M + N) = det M + det N + mixedDet M N`. -/
def mixedDet (M N : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := M.trace * N.trace - (M * N).trace

@[tmio T, powerlib_foundation] theorem det_add_fin_two (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    (M + N).det = M.det + N.det + mixedDet M N := by
  simp [Matrix.det_fin_two, mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

@[tmio T, powerlib_foundation] theorem mixedDet_one_right (M : Matrix (Fin 2) (Fin 2) ℝ) :
    mixedDet M 1 = M.trace := by
  simp [mixedDet, Matrix.trace_fin_two]; ring

@[tmio T, powerlib_foundation] private theorem mixedDet_one_left (N : Matrix (Fin 2) (Fin 2) ℝ) :
    mixedDet 1 N = N.trace := by
  simp [mixedDet, Matrix.trace_fin_two]; ring

@[tmio T, powerlib_foundation] private theorem mixedDet_add_right
    (M N N' : Matrix (Fin 2) (Fin 2) ℝ) : mixedDet M (N + N') = mixedDet M N + mixedDet M N' := by
  simp [mixedDet, Matrix.mul_add, Matrix.trace_add]; ring

@[tmio T, powerlib_foundation] private theorem mixedDet_smul_right (M N : Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ) : mixedDet M (c • N) = c * mixedDet M N := by
  simp [mixedDet, Matrix.trace_smul]; ring

@[tmio T, powerlib_foundation] private theorem mixedDet_smul_left (M N : Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ) : mixedDet (c • M) N = c * mixedDet M N := by
  simp [mixedDet, Matrix.trace_smul]; ring

@[tmio T, powerlib_foundation] private theorem abs_trace_fin_two_le (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |Z.trace| ≤ 2 * ‖Z‖ := by
  rw [Matrix.trace_fin_two]
  have h0 := Averaging.entry_le_norm Z 0 0
  have h1 := Averaging.entry_le_norm Z 1 1
  calc |Z 0 0 + Z 1 1| ≤ |Z 0 0| + |Z 1 1| := abs_add_le _ _
    _ ≤ 2 * ‖Z‖ := by linarith

@[tmio T, powerlib_foundation] private theorem abs_det_fin_two_le (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |Z.det| ≤ 2 * ‖Z‖ ^ 2 := by
  rw [Matrix.det_fin_two]
  have h : ∀ i j k l, |Z i j * Z k l| ≤ ‖Z‖ ^ 2 := fun i j k l => by
    rw [abs_mul, sq]
    exact mul_le_mul (Averaging.entry_le_norm Z i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  calc |Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0| ≤ |Z 0 0 * Z 1 1| + |Z 0 1 * Z 1 0| := abs_sub _ _
    _ ≤ 2 * ‖Z‖ ^ 2 := by linarith [h 0 0 1 1, h 0 1 1 0]

@[tmio T, powerlib_foundation] private theorem abs_mixedDet_le (M Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |mixedDet M Z| ≤ 4 * (‖M‖ * ‖Z‖) := by
  have e : mixedDet M Z = M 0 0 * Z 1 1 + M 1 1 * Z 0 0 - M 0 1 * Z 1 0 - M 1 0 * Z 0 1 := by
    simp [mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h : ∀ i j k l, |M i j * Z k l| ≤ ‖M‖ * ‖Z‖ := fun i j k l => by
    rw [abs_mul]
    exact mul_le_mul (Averaging.entry_le_norm M i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  rw [e]
  have a1 := abs_le.mp (h 0 0 1 1)
  have a2 := abs_le.mp (h 1 1 0 0)
  have a3 := abs_le.mp (h 0 1 1 0)
  have a4 := abs_le.mp (h 1 0 0 1)
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

/-- Eventual positivity from an asymptotic bound on `(0, ε₁]`. -/
@[tmio T, powerlib_foundation] private theorem eventually_pos_of_bound_on {h : ℝ → ℝ}
    {b C ε₁ : ℝ} (k : ℕ) (hb : 0 < b) (hC : 0 ≤ C) (hε₁ : 0 < ε₁)
    (hbound : ∀ ε, 0 < ε → ε ≤ ε₁ → |h ε - b * ε ^ k| ≤ C * ε ^ (k + 1)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < h ε := by
  have hδ : 0 < min ε₁ (b / (C + 1)) := lt_min hε₁ (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  obtain ⟨h0, h1⟩ := hε
  have hε1 : ε ≤ ε₁ := (h1.trans_le (min_le_left _ _)).le
  have hεb : ε < b / (C + 1) := h1.trans_le (min_le_right _ _)
  have hk : 0 < ε ^ k := pow_pos h0 k
  have hb' := hbound ε h0 hε1
  have : C * ε ^ (k + 1) < b * ε ^ k := by
    rw [pow_succ]
    have : C * ε < b := by
      rw [lt_div_iff₀ (by positivity)] at hεb
      nlinarith
    nlinarith
  have := (abs_le.mp hb').1
  linarith

/-- **Jury conditions at a simple critical slow exponent.** Let a family of real `2 × 2` matrices
satisfy `P(ε) = I + εT M + ε² N + O(ε³)` (`‖·‖ ≤ C ε³` on `(0, ε₁]`, `T > 0`) with
`det M = 0 > tr M` (slow exponents `0` and `tr M < 0`). Then `det(I − P(ε)) =
ε³ T mixedDet M N + O(ε⁴)` decides: `mixedDet M N > 0` gives Schur stability, and
`mixedDet M N < 0` a real eigenvalue `> 1`, for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem critical_jury {P : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {T C ε₁ : ℝ} (hT : 0 < T) (hC : 0 ≤ C) (hε₁ : 0 < ε₁)
    (hε₁1 : ε₁ ≤ 1)
    (hP : ∀ ε, 0 < ε → ε ≤ ε₁ → ‖P ε - 1 - (ε * T) • M - ε ^ 2 • N‖ ≤ C * ε ^ 3)
    (hdet : M.det = 0) (htr : M.trace < 0) :
    (0 < mixedDet M N → ∀ᶠ ε in 𝓝[>] (0 : ℝ), LTI.SchurStable (P ε)) ∧
      (mixedDet M N < 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∃ μ ∈ spectrum ℂ ((P ε).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) := by
  set L := T * ‖M‖ + ‖N‖ + C with hL
  have hL0 : 0 ≤ L := by positivity
  -- the deviation `Y = P − I` and its parts
  have hY : ∀ ε, 0 < ε → ε ≤ ε₁ →
      ‖P ε - 1‖ ≤ L * ε ∧
      |(P ε - 1).trace - T * M.trace * ε| ≤ (2 * ‖N‖ + 2 * C) * ε ^ 2 ∧
      |(P ε - 1).det - T * mixedDet M N * ε ^ 3| ≤
        (2 * (‖N‖ + C) ^ 2 + 4 * T * ‖M‖ * C) * ε ^ 4 := by
    intro ε h0 h1
    have hε1 : ε ≤ 1 := h1.trans hε₁1
    set R := P ε - 1 - (ε * T) • M - ε ^ 2 • N with hR
    have hRb : ‖R‖ ≤ C * ε ^ 3 := hP ε h0 h1
    have hε2 : ε ^ 2 ≤ ε := by nlinarith
    have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one h0.le hε1 (by norm_num)
    have hY : P ε - 1 = (ε * T) • M + (ε ^ 2 • N + R) := by rw [hR]; abel
    refine ⟨?_, ?_, ?_⟩
    · rw [hY]
      calc ‖(ε * T) • M + (ε ^ 2 • N + R)‖ ≤ ‖(ε * T) • M‖ + (‖ε ^ 2 • N‖ + ‖R‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ = ε * T * ‖M‖ + (ε ^ 2 * ‖N‖ + ‖R‖) := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
              Real.norm_of_nonneg (by positivity)]
        _ ≤ ε * T * ‖M‖ + (ε * ‖N‖ + C * ε) := by
            gcongr
            exact hRb.trans (mul_le_mul_of_nonneg_left (hε3.trans hε2) hC)
        _ = L * ε := by rw [hL]; ring
    · rw [hY, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
        smul_eq_mul, smul_eq_mul]
      have hRt := abs_trace_fin_two_le R
      have hNt := abs_trace_fin_two_le N
      have e : ε * T * M.trace + (ε ^ 2 * N.trace + R.trace) - T * M.trace * ε =
          ε ^ 2 * N.trace + R.trace := by ring
      rw [e]
      calc |ε ^ 2 * N.trace + R.trace| ≤ |ε ^ 2 * N.trace| + |R.trace| := abs_add_le _ _
        _ = ε ^ 2 * |N.trace| + |R.trace| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
        _ ≤ ε ^ 2 * (2 * ‖N‖) + 2 * (C * ε ^ 3) := by gcongr; linarith
        _ ≤ ε ^ 2 * (2 * ‖N‖) + 2 * (C * ε ^ 2) := by gcongr
        _ = (2 * ‖N‖ + 2 * C) * ε ^ 2 := by ring
    · rw [hY, det_add_fin_two, Matrix.det_smul, hdet, mul_zero, zero_add, mixedDet_smul_left,
        mixedDet_add_right, mixedDet_smul_right]
      set Z := ε ^ 2 • N + R with hZ
      have hZb : ‖Z‖ ≤ (‖N‖ + C) * ε ^ 2 := by
        calc ‖Z‖ ≤ ‖ε ^ 2 • N‖ + ‖R‖ := norm_add_le _ _
          _ = ε ^ 2 * ‖N‖ + ‖R‖ := by
              rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          _ ≤ ε ^ 2 * ‖N‖ + C * ε ^ 2 := by
              gcongr; exact hRb.trans (mul_le_mul_of_nonneg_left hε3 hC)
          _ = (‖N‖ + C) * ε ^ 2 := by ring
      have hdZ : |Z.det| ≤ 2 * (‖N‖ + C) ^ 2 * ε ^ 4 := by
        calc |Z.det| ≤ 2 * ‖Z‖ ^ 2 := abs_det_fin_two_le Z
          _ ≤ 2 * ((‖N‖ + C) * ε ^ 2) ^ 2 := by gcongr
          _ = 2 * (‖N‖ + C) ^ 2 * ε ^ 4 := by ring
      have hmR : |ε * T * mixedDet M R| ≤ 4 * T * ‖M‖ * C * ε ^ 4 := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε * T)]
        calc ε * T * |mixedDet M R| ≤ ε * T * (4 * (‖M‖ * (C * ε ^ 3))) := by
              gcongr
              exact (abs_mixedDet_le M R).trans (by gcongr)
          _ = 4 * T * ‖M‖ * C * ε ^ 4 := by ring
      have e : Z.det + ε * T * (ε ^ 2 * mixedDet M N + mixedDet M R) -
          T * mixedDet M N * ε ^ 3 = Z.det + ε * T * mixedDet M R := by ring
      rw [e]
      calc |Z.det + ε * T * mixedDet M R| ≤ |Z.det| + |ε * T * mixedDet M R| := abs_add_le _ _
        _ ≤ 2 * (‖N‖ + C) ^ 2 * ε ^ 4 + 4 * T * ‖M‖ * C * ε ^ 4 := add_le_add hdZ hmR
        _ = (2 * (‖N‖ + C) ^ 2 + 4 * T * ‖M‖ * C) * ε ^ 4 := by ring
  -- `det P < 1`: `1 − det P = −tr Y − det Y = −T tr M ε + O(ε²)`
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (P ε).det < 1 := by
    have h := eventually_pos_of_bound_on (h := fun ε => -(P ε - 1).trace - (P ε - 1).det)
      (b := -(T * M.trace)) (C := 2 * ‖N‖ + 2 * C + 2 * L ^ 2) 1 (by nlinarith) (by positivity)
      hε₁ fun ε h0 h1 => by
        obtain ⟨hn, ht, -⟩ := hY ε h0 h1
        have hd : |(P ε - 1).det| ≤ 2 * L ^ 2 * ε ^ 2 := by
          calc |(P ε - 1).det| ≤ 2 * ‖P ε - 1‖ ^ 2 := abs_det_fin_two_le _
            _ ≤ 2 * (L * ε) ^ 2 := by gcongr
            _ = 2 * L ^ 2 * ε ^ 2 := by ring
        have e : -(P ε - 1).trace - (P ε - 1).det - -(T * M.trace) * ε ^ 1 =
            -((P ε - 1).trace - T * M.trace * ε) - (P ε - 1).det := by ring
        rw [e]
        calc |-((P ε - 1).trace - T * M.trace * ε) - (P ε - 1).det| ≤
              |(P ε - 1).trace - T * M.trace * ε| + |(P ε - 1).det| := by
              rw [← abs_neg ((P ε - 1).trace - T * M.trace * ε)]; exact abs_sub _ _
          _ ≤ (2 * ‖N‖ + 2 * C) * ε ^ 2 + 2 * L ^ 2 * ε ^ 2 := add_le_add ht hd
          _ = (2 * ‖N‖ + 2 * C + 2 * L ^ 2) * ε ^ (1 + 1) := by ring
    filter_upwards [h] with ε hε
    have hd := det_add_fin_two 1 (P ε - 1)
    rw [add_sub_cancel, Matrix.det_one, mixedDet_one_left] at hd
    linarith
  -- `det(I + P) > 0`: `det(2I + Y) = 4 + 2 tr Y + det Y`
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (1 + P ε).det := by
    have h := eventually_pos_of_bound_on (h := fun ε => (1 + P ε).det) (b := 4)
      (C := 4 * L + 2 * L ^ 2) 0 (by norm_num) (by positivity) hε₁ fun ε h0 h1 => by
        obtain ⟨hn, -, -⟩ := hY ε h0 h1
        have hε1 : ε ≤ 1 := h1.trans hε₁1
        have e : (1 + P ε) = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (P ε - 1) := by
          rw [two_smul]; abel
        have ht : |(P ε - 1).trace| ≤ 2 * (L * ε) :=
          (abs_trace_fin_two_le _).trans (by gcongr)
        have hd : |(P ε - 1).det| ≤ 2 * L ^ 2 * ε := by
          calc |(P ε - 1).det| ≤ 2 * ‖P ε - 1‖ ^ 2 := abs_det_fin_two_le _
            _ ≤ 2 * (L * ε) ^ 2 := by gcongr
            _ = 2 * L ^ 2 * ε * ε := by ring
            _ ≤ 2 * L ^ 2 * ε * 1 := by gcongr
            _ = 2 * L ^ 2 * ε := by ring
        rw [e, Averaging.det_smul_one_add, pow_zero, mul_one, zero_add, pow_one]
        have e2 : (2 : ℝ) ^ 2 + 2 * (P ε - 1).trace + (P ε - 1).det - 4 =
            2 * (P ε - 1).trace + (P ε - 1).det := by ring
        rw [e2]
        calc |2 * (P ε - 1).trace + (P ε - 1).det| ≤ |2 * (P ε - 1).trace| + |(P ε - 1).det| :=
              abs_add_le _ _
          _ = 2 * |(P ε - 1).trace| + |(P ε - 1).det| := by rw [abs_mul, abs_two]
          _ ≤ 2 * (2 * (L * ε)) + 2 * L ^ 2 * ε := by gcongr
          _ = (4 * L + 2 * L ^ 2) * ε := by ring
    exact h
  have hdetY : ∀ ε, (1 - P ε).det = (P ε - 1).det := fun ε => by
    rw [show (1 : Matrix (Fin 2) (Fin 2) ℝ) - P ε = -(P ε - 1) by abel, Matrix.det_neg]
    simp
  refine ⟨fun hmix => ?_, fun hmix => ?_⟩
  · have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (P ε - 1).det :=
      eventually_pos_of_bound_on (b := T * mixedDet M N)
        (C := 2 * (‖N‖ + C) ^ 2 + 4 * T * ‖M‖ * C) 3 (by positivity) (by positivity) hε₁
        fun ε h0 h1 => (hY ε h0 h1).2.2
    filter_upwards [e1, e2, e3] with ε h1 h2 h3
    exact Averaging.schurStable_of_jury h1 (by rw [hdetY]; exact h2) h3
  · have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < -(P ε - 1).det :=
      eventually_pos_of_bound_on (h := fun ε => -(P ε - 1).det) (b := -(T * mixedDet M N))
        (C := 2 * (‖N‖ + C) ^ 2 + 4 * T * ‖M‖ * C) 3 (by nlinarith) (by positivity) hε₁
        fun ε h0 h1 => by
          have := (hY ε h0 h1).2.2
          rw [show -(P ε - 1).det - -(T * mixedDet M N) * ε ^ 3 =
            -((P ε - 1).det - T * mixedDet M N * ε ^ 3) by ring, abs_neg]
          exact this
    filter_upwards [e2] with ε h2
    exact Averaging.exists_eig_gt_of_det_one_sub (by rw [hdetY]; linarith)

end Jury

/-! ## The complete two-state system on the first-order boundary -/

section Full

open TwoToOne (full left right stdForm)

@[tmio T, powerlib_foundation] private theorem neg_mem_spectrum_neg {P : Matrix (Fin 2) (Fin 2) ℝ}
    {μ : ℂ} (h : μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ))) :
    -μ ∈ spectrum ℂ ((-P).map (algebraMap ℝ ℂ)) := by
  obtain ⟨v, hv, hPv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp h
  refine LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, ?_⟩
  rw [Matrix.map_neg _ (fun a => map_neg (algebraMap ℝ ℂ) a), Matrix.neg_mulVec, hPv, neg_smul]

/-- **The complete two-state system on the first-order boundary, with an added `ε²θ I`.** For the
two-state system `ẋ = (A₀ + ε Re{A e^{jωt}}) x` with `σ = εs`, `ω/2 − Ω = εd` (`TwoToOne.full`),
`s > 0`, on the first-order boundary `s² + d² = |g/2|²` (slow flow `M`: `det M = 0`,
`tr M = −2s`), plus `ε²θ I`: with the second Picard term `N₂` of the rotating-frame matrix over
`T = 2π/ω`, `mixedDet(M, N₂) − 2sθT > 0` gives Schur-stable monodromy and `< 0` Floquet
instability, for all small `ε > 0`. (Read through `det(I − Φ) = (1 − μ₁)(1 − μ₂)`, this is the
sign of the critical Floquet exponent `ε² (θ − mixedDet(M, N₂)/(2sT)) + O(ε³)`, which no
first-order datum fixes; only the sign statement is proved here, the expansion at `θ = 0` is
`CriticalExponent.full_critical_exponent`.) -/
@[tmio T, powerlib_foundation] theorem full_boundary_shift {s d ω θ : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) :
    (0 < mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
          (secondTerm (stdForm s d ω A) (2 * Real.pi / ω)) - 2 * s * θ * (2 * Real.pi / ω) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), LTI.SchurStable (Periodic.monodromy
          (fun t => full s d ω A ε t + (ε ^ 2 * θ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (2 * Real.pi / ω) 0)) ∧
      (mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
          (secondTerm (stdForm s d ω A) (2 * Real.pi / ω)) - 2 * s * θ * (2 * Real.pi / ω) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable
          (fun t => full s d ω A ε t + (ε ^ 2 * θ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (2 * Real.pi / ω)) := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  set g := Element.pump A left right with hg
  set F := stdForm s d ω A with hF
  set Mb := slowFlowMatrix s d (g / 2) with hMb
  set N₂ := secondTerm F T with hN₂
  obtain ⟨MF, hMF0, hMF⟩ := TwoToOne.exists_bound_stdForm s d hω A
  have havg : ∫ r in (0 : ℝ)..T, F r = T • Mb := TwoToOne.integral_stdForm s d hω A
  have hFc : Continuous F := TwoToOne.continuous_stdForm s d ω A
  set Py : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun ε => Periodic.monodromy (fun t => ε • F t) T 0
    with hPy
  set Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun ε => Real.exp (ε ^ 2 * θ * T) • Py ε with hQ
  -- the monodromy of the shifted system is `−Q`
  have hmono : ∀ ε, Periodic.monodromy
      (fun t => full s d ω A ε t + (ε ^ 2 * θ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) T 0 = -Q ε := by
    intro ε
    obtain ⟨Mf, hMf⟩ := Periodic.exists_bound_of_periodic (TwoToOne.continuous_full s d ω A ε)
      (TwoToOne.periodic_full s d hω.ne' A ε) hT
    have e : (fun t => full s d ω A ε t + (ε ^ 2 * θ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        fun r => full s d ω A ε r - (-(ε ^ 2 * θ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      funext r; rw [neg_smul, sub_neg_eq_add]
    have h := Periodic.transition_sub_smul_one (TwoToOne.continuous_full s d ω A ε) hMf
      (-(ε ^ 2 * θ)) (s := 0) (t := T) hT.le
    rw [e, Periodic.monodromy, zero_add, h]
    have hm := TwoToOne.monodromy_full s d hω A ε
    rw [Periodic.monodromy, zero_add] at hm
    rw [hm, hQ]
    simp only [sub_zero, neg_mul, neg_neg, smul_neg]
    rfl
  -- the expansion of `Q`
  set K₂ := MF * T * (MF * T * (MF * T * (‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ * Real.exp (MF * T))))
    with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  set C' := 3 * K₂ + θ ^ 2 * T ^ 2 * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ +
    2 * |θ| * T * (T * ‖Mb‖ + ‖N₂‖) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set ε₁ := min 1 (1 / (|θ| * T + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min one_pos (by positivity)
  have hexp : ∀ ε, 0 < ε → ε ≤ ε₁ →
      ‖Q ε - 1 - (ε * T) • Mb - ε ^ 2 • (N₂ + (θ * T) • (1 : Matrix (Fin 2) (Fin 2) ℝ))‖ ≤
        C' * ε ^ 3 := by
    intro ε h0 h1
    have hε1 : ε ≤ 1 := h1.trans (min_le_left _ _)
    have hεθ : ε * (|θ| * T + 1) ≤ 1 := by
      have := h1.trans (min_le_right _ _)
      rwa [le_div_iff₀ (by positivity)] at this
    set x := ε ^ 2 * θ * T with hx
    have hxabs : |x| ≤ ε ^ 2 * (|θ| * T) := by
      rw [hx, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2),
        abs_of_pos hT]; ring_nf; rfl
    have hx1 : |x| ≤ 1 := by
      have hε2 : ε ^ 2 ≤ ε := by nlinarith
      have : ε ^ 2 * (|θ| * T) ≤ ε * (|θ| * T) := by gcongr
      nlinarith [abs_nonneg θ]
    have hq1 : |Real.exp x - 1| ≤ 2 * (ε ^ 2 * (|θ| * T)) :=
      (Real.abs_exp_sub_one_le hx1).trans (by linarith)
    have hq3 : |Real.exp x| ≤ 3 := by
      have := (abs_le.mp ((Real.abs_exp_sub_one_le hx1).trans
        (by linarith : 2 * |x| ≤ 2))).2
      rw [abs_of_pos (Real.exp_pos x)]
      linarith
    have hq2 : |Real.exp x - 1 - x| ≤ θ ^ 2 * T ^ 2 * ε ^ 3 := by
      refine (Real.abs_exp_sub_one_sub_id_le hx1).trans ?_
      have : x ^ 2 = θ ^ 2 * T ^ 2 * ε ^ 4 := by rw [hx]; ring
      rw [this]
      have : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one h0.le hε1 (by norm_num)
      gcongr
    have hP2 := monodromy_expansion_two (F := F) hFc hMF hMF0 hT.le havg h0.le hε1
    have hid : Q ε - 1 - (ε * T) • Mb - ε ^ 2 • (N₂ + (θ * T) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        Real.exp x • (Py ε - 1 - (ε * T) • Mb - ε ^ 2 • N₂) +
          (Real.exp x - 1 - x) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (Real.exp x - 1) • ((ε * T) • Mb + ε ^ 2 • N₂) := by
      rw [hQ, hx]; simp only; module
    rw [hid]
    have hab : ‖(ε * T) • Mb + ε ^ 2 • N₂‖ ≤ ε * (T * ‖Mb‖ + ‖N₂‖) := by
      have hε2 : ε ^ 2 ≤ ε := by nlinarith
      calc ‖(ε * T) • Mb + ε ^ 2 • N₂‖ ≤ ‖(ε * T) • Mb‖ + ‖ε ^ 2 • N₂‖ := norm_add_le _ _
        _ = ε * T * ‖Mb‖ + ε ^ 2 * ‖N₂‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
              Real.norm_of_nonneg (by positivity)]
        _ ≤ ε * T * ‖Mb‖ + ε * ‖N₂‖ := by gcongr
        _ = ε * (T * ‖Mb‖ + ‖N₂‖) := by ring
    calc ‖Real.exp x • (Py ε - 1 - (ε * T) • Mb - ε ^ 2 • N₂) +
          (Real.exp x - 1 - x) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (Real.exp x - 1) • ((ε * T) • Mb + ε ^ 2 • N₂)‖
        ≤ ‖Real.exp x • (Py ε - 1 - (ε * T) • Mb - ε ^ 2 • N₂)‖ +
          ‖(Real.exp x - 1 - x) • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ +
          ‖(Real.exp x - 1) • ((ε * T) • Mb + ε ^ 2 • N₂)‖ := norm_add₃_le
      _ = |Real.exp x| * ‖Py ε - 1 - (ε * T) • Mb - ε ^ 2 • N₂‖ +
          |Real.exp x - 1 - x| * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ +
          |Real.exp x - 1| * ‖(ε * T) • Mb + ε ^ 2 • N₂‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ 3 * (ε ^ 3 * K₂) + θ ^ 2 * T ^ 2 * ε ^ 3 * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ +
          2 * (ε ^ 2 * (|θ| * T)) * (ε * (T * ‖Mb‖ + ‖N₂‖)) := by
          gcongr
      _ = C' * ε ^ 3 := by rw [hC']; ring
  have hdet : Mb.det = 0 := by rw [hMb, det_slowFlowMatrix, ← hb]; ring
  have htr : Mb.trace < 0 := by rw [hMb, trace_slowFlowMatrix]; linarith
  have hmix : mixedDet Mb (N₂ + (θ * T) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      mixedDet Mb N₂ - 2 * s * θ * T := by
    rw [mixedDet_add_right, mixedDet_smul_right, mixedDet_one_right, hMb, trace_slowFlowMatrix]
    ring
  obtain ⟨hst, hun⟩ := critical_jury (P := Q) hT hC'0 hε₁0 (min_le_left _ _) hexp hdet htr
  rw [hmix] at hst hun
  refine ⟨fun h => ?_, fun h => ?_⟩
  · filter_upwards [hst h] with ε hε
    rw [hmono, NormalForm.schurStable_neg_iff]
    exact hε
  · filter_upwards [hun h] with ε ⟨μ, hμ, h1⟩
    refine ⟨-μ, ?_, by rw [norm_neg]; exact h1⟩
    rw [hmono]
    exact neg_mem_spectrum_neg hμ

/-- **The first-order boundary decided at second order** (`θ = 0`): on the boundary
`s² + d² = |g/2|²`, `s > 0`, the complete two-state system is Schur stable for all small `ε > 0`
if `mixedDet(M, N₂) > 0` and Floquet unstable if `mixedDet(M, N₂) < 0` (`N₂` the second Picard term
of the rotating-frame matrix): the decisive quantity is a second-order average, not a datum of
the slow flow. -/
@[tmio T, powerlib_foundation] theorem full_boundary_decided {s d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) :
    (0 < mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
          (secondTerm (stdForm s d ω A) (2 * Real.pi / ω)) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          LTI.SchurStable (Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0)) ∧
      (mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
          (secondTerm (stdForm s d ω A) (2 * Real.pi / ω)) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (full s d ω A ε) (2 * Real.pi / ω)) := by
  obtain ⟨h1, h2⟩ := full_boundary_shift (θ := 0) hω A hs hb
  simp only [mul_zero, zero_mul, sub_zero, zero_smul, add_zero] at h1 h2
  exact ⟨h1, h2⟩

/-- **For every first-order datum on the boundary, `O(ε²)` completions decide either way.** On the
boundary `s² + d² = |g/2|²`, `s > 0`, for every `κ` with `2sκT > |mixedDet(M, N₂)|`
(`T = 2π/ω`): the complete two-state system with the added damping `ε²κ` (`full − ε²κ I`) is Schur
stable, and with the added anti-damping (`full + ε²κ I`) Floquet unstable, for all small `ε > 0`.
All three systems (`full`, `full ∓ ε²κ I`) have the same first-order slow flow. -/
@[tmio T, powerlib_foundation] theorem full_boundary_completions {s d ω κ : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2)
    (hκ : |mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
      (secondTerm (stdForm s d ω A) (2 * Real.pi / ω))| < 2 * s * κ * (2 * Real.pi / ω)) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), LTI.SchurStable (Periodic.monodromy
        (fun t => full s d ω A ε t - (ε ^ 2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (2 * Real.pi / ω) 0)) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable
        (fun t => full s d ω A ε t + (ε ^ 2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (2 * Real.pi / ω) := by
  have habs := abs_lt.mp hκ
  refine ⟨?_, (full_boundary_shift (θ := κ) hω A hs hb).2 (by linarith)⟩
  have h := (full_boundary_shift (θ := -κ) hω A hs hb).1 (by linarith)
  have e : ∀ ε : ℝ, (fun t => full s d ω A ε t + (ε ^ 2 * -κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      fun t => full s d ω A ε t - (ε ^ 2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := fun ε => by
    funext t; rw [mul_neg, neg_smul, ← sub_eq_add_neg]
  simp only [e] at h
  exact h

end Full

/-! ## The forced operating point -/

/-- **The boundary of the forced-operating-point threshold.** The first-order criterion of
`Periodic.Levels` (`orbit_stable_below_threshold`: `|V̂||g₁| < 2|λ₁|`,
`orbit_unstable_above_threshold`: `|V̂||g₁| > 2|λ₁|`) leaves exactly the boundary, which is the
slow-flow boundary `|V̂ g₁/2|² = |λ₁|²`. -/
@[tmio T, powerlib_foundation] theorem forced_threshold_boundary_iff (lam g₁ : ℂ) (Vh : ℝ) :
    ‖(Vh : ℂ) * g₁ / 2‖ ^ 2 = ‖lam‖ ^ 2 ↔ |Vh| * ‖g₁‖ = 2 * ‖lam‖ := by
  have h1 := Periodic.Levels.pump_sq_lt_iff lam g₁ Vh
  have h2 := Periodic.Levels.sq_lt_pump_iff lam g₁ Vh
  constructor
  · intro h
    rcases lt_trichotomy (|Vh| * ‖g₁‖) (2 * ‖lam‖) with h' | h' | h'
    · exact absurd (h1.mpr h') (by rw [h]; exact lt_irrefl _)
    · exact h'
    · exact absurd (h2.mpr h') (by rw [h]; exact lt_irrefl _)
  · intro h
    rcases lt_trichotomy (‖(Vh : ℂ) * g₁ / 2‖ ^ 2) (‖lam‖ ^ 2) with h' | h' | h'
    · exact absurd (h1.mp h') (by rw [h]; exact lt_irrefl _)
    · exact h'
    · exact absurd (h2.mp h') (by rw [h]; exact lt_irrefl _)

/-- **The two-state model as a forced operating point.** `TwoToOne.full` is
`A₀ + ε (A₀' + Re{A e^{jωt}})` with `A₀ = base 0 (ω/2)` (the pair `±jω/2`) and
`A₀' = base s (−d)`; the first-order eigenvalue shift of the pair is `λ₁ = u A₀' r = −s − jd`, and
the slow-flow boundary `s² + d² = |g/2|²` is the threshold boundary `|g| = 2|λ₁|` of
`forced_threshold_boundary_iff` (with `V̂ g₁ = g`). -/
@[tmio T, powerlib_foundation] theorem two_state_first_order (s d ω : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ε t : ℝ) :
    TwoToOne.full s d ω A ε t =
        TwoToOne.base 0 (ω / 2) + ε • (TwoToOne.base s (-d) + TwoToOne.modReal A ω t) ∧
      TwoToOne.left ⬝ᵥ (Linear.complexify (TwoToOne.base s (-d)) *ᵥ TwoToOne.right) =
        -(s : ℂ) - (d : ℂ) * I ∧
      (s ^ 2 + d ^ 2 = ‖Element.pump A TwoToOne.left TwoToOne.right / 2‖ ^ 2 ↔
        ‖Element.pump A TwoToOne.left TwoToOne.right‖ = 2 * ‖-(s : ℂ) - (d : ℂ) * I‖) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [TwoToOne.full, TwoToOne.base, TwoToOne.modReal] <;> ring
  · rw [TwoToOne.base_right s (-d), dotProduct_smul, TwoToOne.base_normalized]
    push_cast
    ring
  · have hl : ‖-(s : ℂ) - (d : ℂ) * I‖ ^ 2 = s ^ 2 + d ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have h := forced_threshold_boundary_iff (-(s : ℂ) - (d : ℂ) * I)
      (Element.pump A TwoToOne.left TwoToOne.right) 1
    rw [Complex.ofReal_one, one_mul, abs_one, one_mul, hl] at h
    rw [eq_comm]
    exact h

end powerlib.ParametricResonance.Boundary
