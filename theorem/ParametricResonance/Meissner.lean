import theorem.Periodic.TwoStateBoundary
import theorem.LTI.Oscillator2
import theorem.SpecialFunctions.PeriodicWaves
import theorem.Linear.EigenMap
import theorem.Averaging.StateSpaceAveraging
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The Meissner equation: an exactly solvable parametric resonance boundary

The damped oscillator with a square-wave stiffness,
`ẍ + 2c ẋ + k(t) x = 0`, `k(t) = ω₀²(1 + ε)` on the first half period and `ω₀²(1 − ε)` on the
second (period `T = 2π/Ω`), has a closed-form monodromy matrix. With `x = e^{−ct} y` each half
period is a harmonic oscillator `ÿ + ν_i² y = 0`, `ν_i² = ω₀²(1 ± ε) − c²`, so
`M = e^{−cT} S (R₂ R₁) S⁻¹` with `S = [[1, 0], [−c, 1]]`, `det(R₂ R₁) = 1` and
`tr(R₂ R₁) = 2 cos θ₁ cos θ₂ − (ν₁/ν₂ + ν₂/ν₁) sin θ₁ sin θ₂ = τ`, `θ_i = ν_i T/2`. The exact
parametric boundary is `|τ| = 2 cosh(cT)`: Floquet instability iff `|τ| > 2 cosh(cT)`, the
multiplier `−1` (antiperiodic, half-frequency response) iff `τ = −2 cosh(cT)`, the multiplier
`+1` (periodic response) iff `τ = 2 cosh(cT)`. Without modulation the system is stable for every
pump frequency when `c > 0`; at the centre of the principal tongue the threshold is an explicit
closed form whose leading term is `ε_c = πζ`.

Scope.
* The scalar equation in the state `(x, ẋ) ∈ ℝ²`: `ẏ = A(t) y`, `A(t) = oscMatrix c (k(t))`
  (`Periodic.oscMatrix`), `k(t) = ω₀²(1 + squareWave ε T t)` (`stiffness`; the square wave of
  `theorem/SpecialFunctions/PeriodicWaves.lean`, `ε` on `[0, T/2)`, `−ε` on `[T/2, T)` modulo
  `T`), constant damping `c ≥ 0`, period `T > 0`, continuous time. Both half periods are
  oscillatory: `ν_i > 0` with `ν₁² = ω₀²(1 + ε) − c²`, `ν₂² = ω₀²(1 − ε) − c²` (hypotheses).
* The coefficient jumps, so solutions are continuous curves with right derivatives
  `HasDerivWithinAt y (A t *ᵥ y t) (Ici t) t` for every `t ≥ 0` (the state `(x, ẋ)` is
  continuous, `ẍ` jumps at the switching instants); these conditions are written out in the
  statements. The monodromy matrix is the product of the two half-period exponentials
  (`meissnerMonodromy`), and `solution_period` proves that it maps `y(nT)` to `y((n + 1)T)`
  for every such solution. The Floquet multipliers are its complex spectrum.
* Generic mathematics; no model family.

Source: the Meissner equation (Meissner 1918; Richards, *Analysis of Periodically Time-Varying
Systems*, 1983) as the exactly solvable square-wave case of the Hill equation; the
reduction `x = e^{−ct} y` and the boundary `|tr M| = 1 + det M` of
`theorem/Periodic/TwoStateBoundary.lean`. The tongue-centre threshold `ε_c ≈ πζ` is consistent
with the sinusoidal (Mathieu) threshold `h_c ≈ 4ζ` of the first-order 2:1 criterion
(`ParametricResonance.Element.canonical_threshold_iff` with
`ParametricResonance.Element.mathieu_normalizedPump`): the fundamental of the square wave of
amplitude `ε` has amplitude `4ε/π` (`SpecialFunctions.PeriodicWaves.amp_squareWave_of_odd`),
and `(4/π) ε_c = 4ζ`.

Sharpenings.
* The principal-tongue threshold "`ε_c ≈ πζ` for small `ε`, `ζ`" is replaced by the exact
  tongue-centre criterion `centre_threshold_iff`,
  `ε |sin θ₁| > πζ · (√(ν₁ν₂)/ω₀) · (sinh x / x)`, `x = πc/(ν₁ + ν₂)`, `c = ζω₀`, whose three
  correction factors tend to `1`, and by the explicit necessary condition
  `centre_threshold_lower`, `ε > πζ √(ν₁ν₂)/ω₀`. No limit is formalized.

Results.
* `eq_exp_mulVec_of_rightDeriv` — a continuous curve on `[a, b]` with right derivative `B y` on
  `[a, b)` is `e^{(t − a)B} y(a)` (Mathlib `ODE_solution_unique_of_mem_Icc_right`,
  `Averaging.hasDerivAt_exp_mulVec`).
* `stiffness_of_mem_first`, `stiffness_of_mem_second` — the stiffness on `[nT, nT + T/2)` and
  `[nT + T/2, (n + 1)T)`.
* `meissnerMonodromy`, `meissnerMonodromy_eq_exp` — `M = e^{(T/2)B₂} e^{(T/2)B₁}`, the period
  map `Averaging.periodMap (1/2) T B₁ B₂` of the two-topology switched system with duty ratio
  `1/2` (`theorem/Averaging/StateSpaceAveraging.lean`), `B_{1,2} = oscMatrix c (ω₀²(1 ± ε))`.
* `solution_period`, `isIntegralCurveOn_first`, `isIntegralCurveOn_second`, `solution_nat_mul` —
  every solution satisfies `y((n + 1)T) = M y(nT)`; on each closed half period it is an integral
  curve of the frozen system, i.e. a switched trajectory, so `y(nT) = Mⁿ y(0)`
  (`Averaging.switched_sample`).
* `meissnerFlow`, `meissnerFlow_of_mem_first`, `meissnerFlow_of_mem_second`, `meissnerFlow_zero`,
  `meissnerFlow_add_period` — the fundamental matrix `Ψ(t)` on `[0, ∞)` (built from `⌊t/T⌋`),
  `Ψ(0) = I`, `Ψ(t + T) = Ψ(t) M`; `flow_solution` — `Ψ(t) w` is a solution through `w`
  (existence); `solution_eq_flow` — every solution is `Ψ(t) y(0)` (uniqueness);
  `solution_add_period` — `y(t + T) = Ψ(t) M y(0)`, so eigenvectors of `M` start Floquet
  modes.
* `shear`, `rot`, `exp_oscMatrix` — `e^{h A} = e^{−ch} S R(ν, νh) S⁻¹` for `A = oscMatrix c k`,
  `ν² = k − c²` (`LTI.exp_smul_of_sq_eq`).
* `meissnerMonodromy_eq`, `det_rot_mul_rot`, `trace_rot_mul_rot` — `M = e^{−cT} S M_y S⁻¹`,
  `M_y = R(ν₂, θ₂) R(ν₁, θ₁)`, `det M_y = 1`, `tr M_y = reducedTrace ν₁ ν₂ T`.
* `det_meissnerMonodromy`, `trace_meissnerMonodromy` — `det M = e^{−2cT}` (Liouville,
  `Periodic.det_exp_smul`), `tr M = e^{−cT} τ`.
* `floquetUnstable_iff` — Floquet instability iff `2 cosh(cT) < |τ|` (`c ≥ 0`);
  `undamped_floquetUnstable_iff` — for `c = 0` iff `2 < |τ|`.
* `schurStable_iff` — for `c > 0`: every multiplier inside the unit circle iff
  `|τ| < 2 cosh(cT)`; `neg_one_mem_spectrum_iff`, `one_mem_spectrum_iff` — `−1` is a multiplier
  iff `τ = −2 cosh(cT)`, `+1` iff `τ = 2 cosh(cT)`.
* `antiperiodic_of_boundary` — on the boundary `τ = −2 cosh(cT)` there is a real initial state
  `w ≠ 0` with `M w = −w`, a solution through it, and every solution through it is
  `T`-antiperiodic: `y(t + T) = −y(t)` for `t ≥ 0`; `periodic_of_boundary` — on `τ = 2 cosh(cT)`
  the same with `M w = w` and `T`-periodic solutions.
* `reducedTrace_self`, `unmodulated_schurStable` — `ε = 0`: `τ = 2 cos(νT)`; with `c > 0`
  Schur stable for every `T > 0`.
* `reducedTrace_centre`, `centre_floquetUnstable_iff`, `centre_threshold_iff`,
  `centre_threshold_lower` — at the tongue centre `Ω = ν₁ + ν₂` (`θ₁ + θ₂ = π`):
  `τ = −2 − ((ν₁ − ν₂)²/(ν₁ν₂)) sin² θ₁`; instability iff
  `(ν₁ − ν₂)² sin² θ₁ > 4 ν₁ν₂ sinh²(cT/2)`, i.e. iff
  `ε ω₀² |sin θ₁| > √(ν₁ν₂) (ν₁ + ν₂) sinh(πc/(ν₁ + ν₂))`; hence instability at the centre
  requires `ε ω₀² > π c √(ν₁ν₂)` (with `c = ζω₀`: `ε > πζ √(ν₁ν₂)/ω₀`), and every correction
  factor (`|sin θ₁|`, `√(ν₁ν₂)/ω₀`, `sinh x/x`) tends to `1` as `ε, ζ → 0`.
-/

noncomputable section
namespace powerlib.ParametricResonance.Meissner

open Set Matrix Function Filter Topology
open powerlib.Periodic (oscMatrix)
open powerlib.SpecialFunctions.PeriodicWaves (squareWave)

/-! ## Right-differentiable solutions of a constant linear system -/

section RightDeriv

open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A continuous curve on `[a, b]` whose right derivative is `B y(t)` on `[a, b)` is
`y(t) = e^{(t − a)B} y(a)`. -/
@[tmio T, powerlib_foundation] theorem eq_exp_mulVec_of_rightDeriv (B : Matrix n n ℝ)
    {y : ℝ → n → ℝ} {a b : ℝ} (hc : ContinuousOn y (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt y (B *ᵥ y t) (Ici t) t) :
    ∀ t ∈ Icc a b, y t = NormedSpace.exp ((t - a) • B) *ᵥ y a := by
  have hg := Averaging.hasDerivAt_exp_mulVec B a (y a)
  let F : (n → ℝ) →L[ℝ] (n → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' B)
  have hlip : ∀ t ∈ Ico a b, LipschitzOnWith ‖F‖₊ (fun x : n → ℝ => B *ᵥ x) univ := by
    intro t _
    have h := F.lipschitzWith.lipschitzOnWith (s := univ)
    have hF : (⇑F) = fun x : n → ℝ => B *ᵥ x := by
      funext x
      simp [F]
    rwa [hF] at h
  have hgc : ContinuousOn (fun t => NormedSpace.exp ((t - a) • B) *ᵥ y a) (Icc a b) :=
    (continuous_iff_continuousAt.2 fun t => (hg t).continuousAt).continuousOn
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ x => B *ᵥ x)
    (s := fun _ => univ) hlip hc hd (fun _ _ => mem_univ _) hgc
    (fun t _ => (hg t).hasDerivWithinAt) (fun _ _ => mem_univ _)
    (by simp [NormedSpace.exp_zero])
  exact fun t ht => heq ht

end RightDeriv

/-! ## The square-wave stiffness and the monodromy matrix -/

/-- The square-wave stiffness `k(t) = ω₀²(1 + ε)` on `[nT, nT + T/2)` and `ω₀²(1 − ε)` on
`[nT + T/2, (n + 1)T)`. -/
def stiffness (ω₀ ε T t : ℝ) : ℝ := ω₀ ^ 2 * (1 + squareWave ε T t)

section MonodromyDef

open scoped Matrix.Norms.Operator

/-- The monodromy matrix of the Meissner equation: the flow over the first half period
(stiffness `ω₀²(1 + ε)`) followed by the flow over the second (stiffness `ω₀²(1 − ε)`), i.e. the
period map of the two-topology switched linear system with duty ratio `1/2`
(`Averaging.periodMap`). -/
def meissnerMonodromy (c ω₀ ε T : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Averaging.periodMap (1 / 2) T (oscMatrix c (ω₀ ^ 2 * (1 + ε))) (oscMatrix c (ω₀ ^ 2 * (1 - ε)))

end MonodromyDef

/-- `M = e^{(T/2)B₂} e^{(T/2)B₁}`. -/
@[tmio T, powerlib_foundation] theorem meissnerMonodromy_eq_exp (c ω₀ ε T : ℝ) :
    meissnerMonodromy c ω₀ ε T = NormedSpace.exp ((T / 2) • oscMatrix c (ω₀ ^ 2 * (1 - ε))) *
      NormedSpace.exp ((T / 2) • oscMatrix c (ω₀ ^ 2 * (1 + ε))) := by
  show NormedSpace.exp (((1 - 1 / 2 : ℝ) * T) • oscMatrix c (ω₀ ^ 2 * (1 - ε))) *
    NormedSpace.exp (((1 / 2 : ℝ) * T) • oscMatrix c (ω₀ ^ 2 * (1 + ε))) = _
  rw [show (1 - 1 / 2 : ℝ) * T = T / 2 by ring, show (1 / 2 : ℝ) * T = T / 2 by ring]

@[tmio T, powerlib_foundation] private theorem fract_eq_of_mem {T t : ℝ} (hT : 0 < T) (n : ℕ)
    (ht : t ∈ Ico (n * T) ((n + 1) * T)) : Int.fract (t / T) = t / T - n := by
  rw [Int.fract_eq_iff]
  refine ⟨?_, ?_, ⟨n, by push_cast; ring⟩⟩
  · rw [sub_nonneg, le_div_iff₀ hT]; exact ht.1
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hT]; linarith [ht.2]

/-- On the first half period `[nT, nT + T/2)` the stiffness is `ω₀²(1 + ε)`. -/
@[tmio T, powerlib_foundation] theorem stiffness_of_mem_first {ω₀ ε T t : ℝ} (hT : 0 < T)
    (n : ℕ) (ht : t ∈ Ico (n * T) (n * T + T / 2)) : stiffness ω₀ ε T t = ω₀ ^ 2 * (1 + ε) := by
  have hf := fract_eq_of_mem hT n ⟨ht.1, by linarith [ht.2]⟩
  have hlt : t / T - n < 1 / 2 := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hT]; linarith [ht.2]
  rw [stiffness, squareWave, hf]
  simp only [hlt, ↓reduceIte]

/-- On the second half period `[nT + T/2, (n + 1)T)` the stiffness is `ω₀²(1 − ε)`. -/
@[tmio T, powerlib_foundation] theorem stiffness_of_mem_second {ω₀ ε T t : ℝ} (hT : 0 < T)
    (n : ℕ) (ht : t ∈ Ico (n * T + T / 2) ((n + 1) * T)) :
    stiffness ω₀ ε T t = ω₀ ^ 2 * (1 - ε) := by
  have hf := fract_eq_of_mem hT n ⟨by linarith [ht.1], ht.2⟩
  have hge : ¬ t / T - n < 1 / 2 := by
    rw [not_lt, le_sub_iff_add_le, le_div_iff₀ hT]; linarith [ht.1]
  rw [stiffness, squareWave, hf]
  simp only [hge, ↓reduceIte]
  ring

section Solutions

variable {c ω₀ ε T : ℝ} {y : ℝ → Fin 2 → ℝ}

/-- On the first half period a solution is `e^{(t − nT) B₁} y(nT)`. -/
@[tmio T, powerlib_foundation] private theorem solution_first (hT : 0 < T)
    (hcont : ContinuousOn y (Ici 0))
    (hy : ∀ t, 0 ≤ t →
      HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) (n : ℕ) :
    ∀ t ∈ Icc (n * T) (n * T + T / 2), y t =
      NormedSpace.exp ((t - n * T) • oscMatrix c (ω₀ ^ 2 * (1 + ε))) *ᵥ y (n * T) := by
  have hnT : (0 : ℝ) ≤ n * T := by positivity
  exact eq_exp_mulVec_of_rightDeriv (oscMatrix c (ω₀ ^ 2 * (1 + ε)))
    (hcont.mono fun t ht => mem_Ici.mpr (hnT.trans ht.1)) (fun t ht => by
      rw [← stiffness_of_mem_first hT n ht]
      exact hy t (hnT.trans ht.1))

/-- On the second half period a solution is `e^{(t − nT − T/2) B₂} y(nT + T/2)`. -/
@[tmio T, powerlib_foundation] private theorem solution_second (hT : 0 < T)
    (hcont : ContinuousOn y (Ici 0))
    (hy : ∀ t, 0 ≤ t →
      HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) (n : ℕ) :
    ∀ t ∈ Icc (n * T + T / 2) ((n + 1) * T), y t =
      NormedSpace.exp ((t - (n * T + T / 2)) • oscMatrix c (ω₀ ^ 2 * (1 - ε))) *ᵥ
        y (n * T + T / 2) := by
  have hnT : (0 : ℝ) ≤ n * T := by positivity
  exact eq_exp_mulVec_of_rightDeriv (oscMatrix c (ω₀ ^ 2 * (1 - ε)))
    (hcont.mono fun t ht => mem_Ici.mpr (by linarith [ht.1])) (fun t ht => by
      rw [← stiffness_of_mem_second hT n ht]
      exact hy t (by linarith [ht.1]))

/-- **The monodromy matrix maps one period to the next.** Every solution of the Meissner
equation (continuous on `[0, ∞)`, right derivative `A(t) y(t)` at every `t ≥ 0`) satisfies
`y((n + 1)T) = M y(nT)`. -/
@[tmio T, powerlib_foundation] theorem solution_period (hT : 0 < T)
    (hcont : ContinuousOn y (Ici 0))
    (hy : ∀ t, 0 ≤ t →
      HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) (n : ℕ) :
    y ((n + 1) * T) = meissnerMonodromy c ω₀ ε T *ᵥ y (n * T) := by
  rw [solution_second hT hcont hy n ((n + 1) * T) ⟨by linarith, le_rfl⟩,
    solution_first hT hcont hy n (n * T + T / 2) ⟨by linarith, le_rfl⟩, Matrix.mulVec_mulVec,
    show (n + 1) * T - (n * T + T / 2) = T / 2 by ring, show n * T + T / 2 - n * T = T / 2 by ring,
    meissnerMonodromy_eq_exp]

/-- On the first half period a solution is an integral curve of `ẏ = B₁ y` on the closed
interval (one-sided derivatives at the switching instants). -/
@[tmio T, powerlib_foundation] theorem isIntegralCurveOn_first (hT : 0 < T)
    (hcont : ContinuousOn y (Ici 0))
    (hy : ∀ t, 0 ≤ t →
      HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) (n : ℕ) :
    IsIntegralCurveOn y (fun _ v => oscMatrix c (ω₀ ^ 2 * (1 + ε)) *ᵥ v)
      (Icc (n * T) (n * T + T / 2)) := by
  intro t ht
  have h := ((Averaging.hasDerivAt_exp_mulVec (oscMatrix c (ω₀ ^ 2 * (1 + ε))) (n * T)
    (y (n * T)) t).hasDerivWithinAt (s := Icc (n * T) (n * T + T / 2))).congr
    (fun u hu => solution_first hT hcont hy n u hu) (solution_first hT hcont hy n t ht)
  rwa [← solution_first hT hcont hy n t ht] at h

/-- On the second half period a solution is an integral curve of `ẏ = B₂ y` on the closed
interval. -/
@[tmio T, powerlib_foundation] theorem isIntegralCurveOn_second (hT : 0 < T)
    (hcont : ContinuousOn y (Ici 0))
    (hy : ∀ t, 0 ≤ t →
      HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) (n : ℕ) :
    IsIntegralCurveOn y (fun _ v => oscMatrix c (ω₀ ^ 2 * (1 - ε)) *ᵥ v)
      (Icc (n * T + T / 2) ((n + 1) * T)) := by
  intro t ht
  have h := ((Averaging.hasDerivAt_exp_mulVec (oscMatrix c (ω₀ ^ 2 * (1 - ε)))
    (n * T + T / 2) (y (n * T + T / 2)) t).hasDerivWithinAt
      (s := Icc (n * T + T / 2) ((n + 1) * T))).congr
    (fun u hu => solution_second hT hcont hy n u hu) (solution_second hT hcont hy n t ht)
  rwa [← solution_second hT hcont hy n t ht] at h

/-- `y(nT) = Mⁿ y(0)` for every solution: a Meissner solution is a trajectory of the
two-topology switched system with duty ratio `1/2` (`Averaging.switched_sample`). -/
@[tmio T, powerlib_foundation] theorem solution_nat_mul (hT : 0 < T)
    (hcont : ContinuousOn y (Ici 0))
    (hy : ∀ t, 0 ≤ t →
      HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) (n : ℕ) :
    y (n * T) = meissnerMonodromy c ω₀ ε T ^ n *ᵥ y 0 := by
  have hx : ∀ k : ℕ,
      IsIntegralCurveOn y (fun _ v => oscMatrix c (ω₀ ^ 2 * (1 + ε)) *ᵥ v)
        (Icc (k * T) (k * T + 1 / 2 * T)) ∧
      IsIntegralCurveOn y (fun _ v => oscMatrix c (ω₀ ^ 2 * (1 - ε)) *ᵥ v)
        (Icc (k * T + 1 / 2 * T) ((k + 1) * T)) := by
    intro k
    rw [show (k : ℝ) * T + 1 / 2 * T = k * T + T / 2 by ring]
    exact ⟨isIntegralCurveOn_first hT hcont hy k, isIntegralCurveOn_second hT hcont hy k⟩
  exact Averaging.switched_sample (by norm_num) (by norm_num) hT.le hx n

end Solutions

/-! ## The fundamental matrix: existence, uniqueness, period law -/

section Flow

variable {c ω₀ ε T : ℝ}

/-- The fundamental matrix of the Meissner equation on `[0, ∞)`: with `n = ⌊t/T⌋` and
`s = t − nT`, `Ψ(t) = e^{s B₁} Mⁿ` on the first half period and
`e^{(s − T/2) B₂} e^{(T/2) B₁} Mⁿ` on the second (`B₁`, `B₂` the two constant state matrices). -/
def meissnerFlow (c ω₀ ε T t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (if t - ⌊t / T⌋₊ * T < T / 2 then
      NormedSpace.exp ((t - ⌊t / T⌋₊ * T) • oscMatrix c (ω₀ ^ 2 * (1 + ε)))
    else NormedSpace.exp ((t - ⌊t / T⌋₊ * T - T / 2) • oscMatrix c (ω₀ ^ 2 * (1 - ε))) *
      NormedSpace.exp ((T / 2) • oscMatrix c (ω₀ ^ 2 * (1 + ε)))) *
    meissnerMonodromy c ω₀ ε T ^ ⌊t / T⌋₊

@[tmio T, powerlib_foundation] private theorem floor_div_eq (hT : 0 < T) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ico (n * T) ((n + 1) * T)) : ⌊t / T⌋₊ = n := by
  have h0 : (0 : ℝ) ≤ n * T := by positivity
  rw [Nat.floor_eq_iff (div_nonneg (h0.trans ht.1) hT.le)]
  exact ⟨(le_div_iff₀ hT).mpr ht.1, (div_lt_iff₀ hT).mpr ht.2⟩

@[tmio T, powerlib_foundation] private theorem mem_Ico_floor (hT : 0 < T) {t : ℝ} (ht : 0 ≤ t) :
    t ∈ Ico ((⌊t / T⌋₊ : ℕ) * T) (((⌊t / T⌋₊ : ℕ) + 1) * T) := by
  have h1 := Nat.floor_le (div_nonneg ht hT.le)
  have h2 := Nat.lt_floor_add_one (t / T)
  exact ⟨(le_div_iff₀ hT).mp h1, (div_lt_iff₀ hT).mp h2⟩

/-- The fundamental matrix on the first half period `[nT, nT + T/2]`. -/
@[tmio T, powerlib_foundation] theorem meissnerFlow_of_mem_first (hT : 0 < T) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (n * T) (n * T + T / 2)) :
    meissnerFlow c ω₀ ε T t = NormedSpace.exp ((t - n * T) • oscMatrix c (ω₀ ^ 2 * (1 + ε))) *
      meissnerMonodromy c ω₀ ε T ^ n := by
  have hfl : ⌊t / T⌋₊ = n := floor_div_eq hT n ⟨ht.1, by linarith [ht.2]⟩
  rw [meissnerFlow, hfl]
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · have hc : t - n * T < T / 2 := by linarith
    simp only [hc, ↓reduceIte]
  · have hc : ¬ (t - n * T < T / 2) := by linarith
    simp only [hc, ↓reduceIte]
    rw [heq, show n * T + T / 2 - n * T - T / 2 = 0 by ring, zero_smul, NormedSpace.exp_zero,
      one_mul, show n * T + T / 2 - n * T = T / 2 by ring]

/-- The fundamental matrix on the second half period `[nT + T/2, (n + 1)T]`. -/
@[tmio T, powerlib_foundation] theorem meissnerFlow_of_mem_second (hT : 0 < T) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (n * T + T / 2) ((n + 1) * T)) :
    meissnerFlow c ω₀ ε T t =
      NormedSpace.exp ((t - (n * T + T / 2)) • oscMatrix c (ω₀ ^ 2 * (1 - ε))) *
        NormedSpace.exp ((T / 2) • oscMatrix c (ω₀ ^ 2 * (1 + ε))) *
          meissnerMonodromy c ω₀ ε T ^ n := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · have hfl : ⌊t / T⌋₊ = n := floor_div_eq hT n ⟨by linarith [ht.1], hlt⟩
    rw [meissnerFlow, hfl]
    have hc : ¬ (t - n * T < T / 2) := by linarith [ht.1]
    simp only [hc, ↓reduceIte]
    rw [show t - n * T - T / 2 = t - (n * T + T / 2) by ring]
  · have hfl : ⌊t / T⌋₊ = n + 1 := floor_div_eq hT (n + 1)
      ⟨by rw [heq]; push_cast; rfl, by rw [heq]; push_cast; nlinarith⟩
    rw [meissnerFlow, hfl]
    have hc : t - ((n + 1 : ℕ) : ℝ) * T < T / 2 := by rw [heq]; push_cast; linarith
    simp only [hc, ↓reduceIte]
    rw [heq, show (n + 1) * T - ((n + 1 : ℕ) : ℝ) * T = 0 by push_cast; ring, zero_smul,
      NormedSpace.exp_zero, one_mul, show (n + 1) * T - (n * T + T / 2) = T / 2 by ring,
      pow_succ', meissnerMonodromy_eq_exp, Matrix.mul_assoc]

@[tmio T, powerlib_foundation] theorem meissnerFlow_zero (hT : 0 < T) :
    meissnerFlow c ω₀ ε T 0 = 1 := by
  have h := meissnerFlow_of_mem_first (c := c) (ω₀ := ω₀) (ε := ε) hT 0 (t := 0)
    ⟨by simp, by simp; positivity⟩
  simpa using h

/-- **Period law.** `Ψ(t + T) = Ψ(t) M` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem meissnerFlow_add_period (hT : 0 < T) {t : ℝ}
    (ht : 0 ≤ t) :
    meissnerFlow c ω₀ ε T (t + T) = meissnerFlow c ω₀ ε T t * meissnerMonodromy c ω₀ ε T := by
  have hfl : ⌊(t + T) / T⌋₊ = ⌊t / T⌋₊ + 1 := by
    rw [add_div, div_self hT.ne', Nat.floor_add_one (div_nonneg ht hT.le)]
  have hs : t + T - ((⌊t / T⌋₊ + 1 : ℕ) : ℝ) * T = t - ⌊t / T⌋₊ * T := by push_cast; ring
  rw [meissnerFlow, meissnerFlow, hfl, hs, pow_succ (meissnerMonodromy c ω₀ ε T),
    Matrix.mul_assoc]

/-- **Every solution is given by the fundamental matrix:** `y(t) = Ψ(t) y(0)` for `t ≥ 0`
(uniqueness of solutions). -/
@[tmio T, powerlib_foundation] theorem solution_eq_flow (hT : 0 < T) {y : ℝ → Fin 2 → ℝ}
    (hcont : ContinuousOn y (Ici 0))
    (hy : ∀ t, 0 ≤ t →
      HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) {t : ℝ}
    (ht : 0 ≤ t) : y t = meissnerFlow c ω₀ ε T t *ᵥ y 0 := by
  set n := ⌊t / T⌋₊
  have hn := mem_Ico_floor hT ht
  have hyn := solution_nat_mul hT hcont hy n
  by_cases hhalf : t ≤ n * T + T / 2
  · rw [meissnerFlow_of_mem_first hT n ⟨hn.1, hhalf⟩, ← Matrix.mulVec_mulVec, ← hyn]
    exact solution_first hT hcont hy n t ⟨hn.1, hhalf⟩
  · push Not at hhalf
    have h1 := solution_first hT hcont hy n (n * T + T / 2) ⟨by linarith, le_rfl⟩
    rw [show n * T + T / 2 - n * T = T / 2 by ring] at h1
    rw [meissnerFlow_of_mem_second hT n ⟨hhalf.le, hn.2.le⟩, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← hyn, ← h1]
    exact solution_second hT hcont hy n t ⟨hhalf.le, hn.2.le⟩

/-- `y(t + T) = Ψ(t) M y(0)` for every solution: an eigenvector `M w = μ w` starts a Floquet
mode `y(t + T) = μ y(t)`. -/
@[tmio T, powerlib_foundation] theorem solution_add_period (hT : 0 < T) {y : ℝ → Fin 2 → ℝ}
    (hcont : ContinuousOn y (Ici 0))
    (hy : ∀ t, 0 ≤ t →
      HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) {t : ℝ}
    (ht : 0 ≤ t) :
    y (t + T) = meissnerFlow c ω₀ ε T t *ᵥ (meissnerMonodromy c ω₀ ε T *ᵥ y 0) := by
  rw [solution_eq_flow hT hcont hy (by linarith), meissnerFlow_add_period hT ht,
    Matrix.mulVec_mulVec]

section Exist

open scoped Matrix.Norms.Operator

/-- **Existence.** `t ↦ Ψ(t) w` is a solution through `w`: continuous on `[0, ∞)`, right
derivative `A(t) Ψ(t) w` at every `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem flow_solution (hT : 0 < T) (w : Fin 2 → ℝ) :
    ContinuousOn (fun t => meissnerFlow c ω₀ ε T t *ᵥ w) (Ici 0) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt (fun t => meissnerFlow c ω₀ ε T t *ᵥ w)
        (oscMatrix c (stiffness ω₀ ε T t) *ᵥ (meissnerFlow c ω₀ ε T t *ᵥ w)) (Ici t) t) ∧
      meissnerFlow c ω₀ ε T 0 *ᵥ w = w := by
  set B₁ := oscMatrix c (ω₀ ^ 2 * (1 + ε))
  set B₂ := oscMatrix c (ω₀ ^ 2 * (1 - ε))
  set M := meissnerMonodromy c ω₀ ε T
  -- the two branch solutions of the `n`-th period
  set g₁ : ℕ → ℝ → Fin 2 → ℝ := fun n u =>
    NormedSpace.exp ((u - n * T) • B₁) *ᵥ (M ^ n *ᵥ w) with hg₁
  set g₂ : ℕ → ℝ → Fin 2 → ℝ := fun n u =>
    NormedSpace.exp ((u - (n * T + T / 2)) • B₂) *ᵥ
      (NormedSpace.exp ((T / 2) • B₁) *ᵥ (M ^ n *ᵥ w)) with hg₂
  have e₁ : ∀ (n : ℕ) (u : ℝ), u ∈ Icc (n * T) (n * T + T / 2) →
      meissnerFlow c ω₀ ε T u *ᵥ w = g₁ n u := by
    intro n u hu
    rw [meissnerFlow_of_mem_first hT n hu, ← Matrix.mulVec_mulVec]
  have e₂ : ∀ (n : ℕ) (u : ℝ), u ∈ Icc (n * T + T / 2) ((n + 1) * T) →
      meissnerFlow c ω₀ ε T u *ᵥ w = g₂ n u := by
    intro n u hu
    rw [meissnerFlow_of_mem_second hT n hu, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have d₁ : ∀ (n : ℕ) (u : ℝ), HasDerivAt (g₁ n) (B₁ *ᵥ g₁ n u) u := fun n u =>
    Averaging.hasDerivAt_exp_mulVec B₁ _ _ u
  have d₂ : ∀ (n : ℕ) (u : ℝ), HasDerivAt (g₂ n) (B₂ *ᵥ g₂ n u) u := fun n u =>
    Averaging.hasDerivAt_exp_mulVec B₂ _ _ u
  have hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt (fun t => meissnerFlow c ω₀ ε T t *ᵥ w)
      (oscMatrix c (stiffness ω₀ ε T t) *ᵥ (meissnerFlow c ω₀ ε T t *ᵥ w)) (Ici t) t := by
    intro t ht
    set n := ⌊t / T⌋₊
    have hn := mem_Ico_floor hT ht
    by_cases hhalf : t < n * T + T / 2
    · have hev : (fun t => meissnerFlow c ω₀ ε T t *ᵥ w) =ᶠ[𝓝[Ici t] t] g₁ n := by
        filter_upwards [Ico_mem_nhdsGE hhalf] with u hu
        exact e₁ n u ⟨hn.1.trans hu.1, hu.2.le⟩
      have hx := e₁ n t ⟨hn.1, hhalf.le⟩
      rw [stiffness_of_mem_first hT n ⟨hn.1, hhalf⟩, hx]
      exact (d₁ n t).hasDerivWithinAt.congr_of_eventuallyEq hev hx
    · push Not at hhalf
      have hev : (fun t => meissnerFlow c ω₀ ε T t *ᵥ w) =ᶠ[𝓝[Ici t] t] g₂ n := by
        filter_upwards [Ico_mem_nhdsGE hn.2] with u hu
        exact e₂ n u ⟨hhalf.trans hu.1, hu.2.le⟩
      have hx := e₂ n t ⟨hhalf, hn.2.le⟩
      rw [stiffness_of_mem_second hT n ⟨hhalf, hn.2⟩, hx]
      exact (d₂ n t).hasDerivWithinAt.congr_of_eventuallyEq hev hx
  refine ⟨?_, hderiv, by rw [meissnerFlow_zero hT, Matrix.one_mulVec]⟩
  intro t ht
  have hR : ContinuousWithinAt (fun t => meissnerFlow c ω₀ ε T t *ᵥ w) (Ici t) t :=
    (hderiv t ht).continuousWithinAt
  rcases (mem_Ici.mp ht).eq_or_lt with h0 | hpos
  · rw [← h0] at hR ⊢
    exact hR
  -- left continuity at `t > 0`: the curve agrees with a branch on `[a, t]`, `a < t`
  have hL : ContinuousWithinAt (fun t => meissnerFlow c ω₀ ε T t *ᵥ w) (Iic t) t := by
    have key : ∃ a < t, ∃ g : ℝ → Fin 2 → ℝ, Continuous g ∧
        ∀ u ∈ Icc a t, meissnerFlow c ω₀ ε T u *ᵥ w = g u := by
      set n := ⌊t / T⌋₊
      have hn : t ∈ Ico ((n : ℝ) * T) ((n + 1) * T) := mem_Ico_floor hT ht
      rcases hn.1.eq_or_lt with hs | hs
      · -- `t = nT`, `n ≥ 1`: the second branch of period `n − 1`
        obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := by
          rcases Nat.eq_zero_or_eq_succ_pred n with h | h
          · rw [h] at hs; simp at hs; linarith
          · exact ⟨_, h⟩
        refine ⟨k * T + T / 2, ?_, g₂ k, continuous_iff_continuousAt.2 fun u =>
          (d₂ k u).continuousAt, fun u hu => e₂ k u ⟨hu.1, ?_⟩⟩
        · rw [← hs, hk]; push_cast; linarith
        · have : t = (k + 1) * T := by rw [← hs, hk]; push_cast; ring
          linarith [hu.2]
      · by_cases hhalf : t ≤ n * T + T / 2
        · exact ⟨n * T, hs, g₁ n, continuous_iff_continuousAt.2 fun u => (d₁ n u).continuousAt,
            fun u hu => e₁ n u ⟨hu.1, hu.2.trans hhalf⟩⟩
        · push Not at hhalf
          exact ⟨n * T + T / 2, hhalf, g₂ n, continuous_iff_continuousAt.2 fun u =>
            (d₂ n u).continuousAt, fun u hu => e₂ n u ⟨hu.1, hu.2.trans hn.2.le⟩⟩
    obtain ⟨a, ha, g, hg, heq⟩ := key
    have hc : ContinuousWithinAt (fun t => meissnerFlow c ω₀ ε T t *ᵥ w) (Icc a t) t :=
      hg.continuousWithinAt.congr (fun u hu => heq u hu) (heq t ⟨ha.le, le_rfl⟩)
    exact hc.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE ha)
  exact (continuousAt_iff_continuous_left_right.2 ⟨hL, hR⟩).continuousWithinAt

end Exist

end Flow

/-! ## Closed form of the half-period maps -/

/-- The shear `S = [[1, 0], [−c, 1]]`: `(x, ẋ) = e^{−ct} S (y, ẏ)` for `x = e^{−ct} y`. -/
def shear (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -c, 1]

/-- The flow `[[cos θ, sin θ/ν], [−ν sin θ, cos θ]]` of `ÿ + ν² y = 0` over the phase `θ`. -/
def rot (ν θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ / ν; -(ν * Real.sin θ), Real.cos θ]

/-- The trace `2 cos θ₁ cos θ₂ − (ν₁/ν₂ + ν₂/ν₁) sin θ₁ sin θ₂` of the reduced monodromy,
`θ_i = ν_i T/2`. -/
def reducedTrace (ν₁ ν₂ T : ℝ) : ℝ :=
  2 * Real.cos (ν₁ * T / 2) * Real.cos (ν₂ * T / 2) -
    (ν₁ / ν₂ + ν₂ / ν₁) * Real.sin (ν₁ * T / 2) * Real.sin (ν₂ * T / 2)

@[tmio T, powerlib_foundation] theorem shear_neg_mul_shear (c : ℝ) : shear (-c) * shear c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, Matrix.mul_apply, Fin.sum_univ_two]

/-- `e^{h A} = e^{−ch} S R(ν, νh) S⁻¹` for `A = [[0, 1], [−k, −2c]]` with `ν² = k − c²`,
`ν ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem exp_oscMatrix {c k ν : ℝ} (hν : ν ^ 2 = k - c ^ 2)
    (hν0 : ν ≠ 0) (h : ℝ) :
    NormedSpace.exp (h • oscMatrix c k) =
      Real.exp (-(c * h)) • (shear c * rot ν (ν * h) * shear (-c)) := by
  have hsq : (oscMatrix c k + c • 1) * (oscMatrix c k + c • 1) =
      -(ν ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [oscMatrix, Matrix.mul_apply, Fin.sum_univ_two, hν] <;> ring
  rw [LTI.exp_smul_of_sq_eq hν0 hsq h]
  have hk : k = ν ^ 2 + c ^ 2 := by linarith
  subst hk
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oscMatrix, shear, rot] <;> field_simp <;> ring

/-- `M = e^{−cT} S (R(ν₂, θ₂) R(ν₁, θ₁)) S⁻¹`, `θ_i = ν_i T/2`. -/
@[tmio T, powerlib_foundation] theorem meissnerMonodromy_eq {c ω₀ ε T ν₁ ν₂ : ℝ}
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) :
    meissnerMonodromy c ω₀ ε T = Real.exp (-(c * T)) •
      (shear c * (rot ν₂ (ν₂ * T / 2) * rot ν₁ (ν₁ * T / 2)) * shear (-c)) := by
  rw [meissnerMonodromy_eq_exp, exp_oscMatrix hν₂ h₂, exp_oscMatrix hν₁ h₁, smul_mul_smul_comm,
    ← Real.exp_add, show -(c * (T / 2)) + -(c * (T / 2)) = -(c * T) by ring,
    show ν₂ * (T / 2) = ν₂ * T / 2 by ring, show ν₁ * (T / 2) = ν₁ * T / 2 by ring]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (shear (-c)) (shear c), shear_neg_mul_shear, Matrix.one_mul]

/-- `det(R(ν₂, θ₂) R(ν₁, θ₁)) = 1`. -/
@[tmio T, powerlib_foundation] theorem det_rot_mul_rot {ν₁ ν₂ : ℝ} (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0)
    (θ₁ θ₂ : ℝ) : (rot ν₂ θ₂ * rot ν₁ θ₁).det = 1 := by
  have e : ∀ {ν : ℝ}, ν ≠ 0 → ∀ θ, (rot ν θ).det = 1 := by
    intro ν hν θ
    simp only [rot, Matrix.det_fin_two_of]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [Matrix.det_mul, e h₂, e h₁, one_mul]

/-- `tr(R(ν₂, θ₂) R(ν₁, θ₁)) = 2 cos θ₁ cos θ₂ − (ν₁/ν₂ + ν₂/ν₁) sin θ₁ sin θ₂`. -/
@[tmio T, powerlib_foundation] theorem trace_rot_mul_rot (ν₁ ν₂ T : ℝ) :
    (rot ν₂ (ν₂ * T / 2) * rot ν₁ (ν₁ * T / 2)).trace = reducedTrace ν₁ ν₂ T := by
  simp only [rot, reducedTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- `det M = e^{−2cT}` (Liouville's formula for the two half-period exponentials). -/
@[tmio T, powerlib_foundation] theorem det_meissnerMonodromy (c ω₀ ε T : ℝ) :
    (meissnerMonodromy c ω₀ ε T).det = Real.exp (-(2 * c) * T) := by
  rw [meissnerMonodromy_eq_exp, Matrix.det_mul, Periodic.det_exp_smul, Periodic.det_exp_smul,
    Periodic.trace_oscMatrix, Periodic.trace_oscMatrix, ← Real.exp_add]
  ring_nf

/-- `tr M = e^{−cT} τ`, `τ = reducedTrace ν₁ ν₂ T`. -/
@[tmio T, powerlib_foundation] theorem trace_meissnerMonodromy {c ω₀ ε T ν₁ ν₂ : ℝ}
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) :
    (meissnerMonodromy c ω₀ ε T).trace = Real.exp (-(c * T)) * reducedTrace ν₁ ν₂ T := by
  rw [meissnerMonodromy_eq hν₁ hν₂ h₁ h₂, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, shear_neg_mul_shear, Matrix.one_mul, trace_rot_mul_rot]

/-! ## The exact parametric boundary -/

section Boundary

variable {c ω₀ ε T ν₁ ν₂ : ℝ}

@[tmio T, powerlib_foundation] private theorem one_add_exp_eq (c T : ℝ) :
    1 + Real.exp (-(2 * c) * T) = Real.exp (-(c * T)) * (2 * Real.cosh (c * T)) := by
  rw [Real.cosh_eq, mul_div_cancel₀ _ two_ne_zero, mul_add, ← Real.exp_add, ← Real.exp_add,
    show -(c * T) + c * T = 0 by ring, show -(c * T) + -(c * T) = -(2 * c) * T by ring,
    Real.exp_zero]

/-- **The exact boundary.** The Meissner system is Floquet unstable (some multiplier outside the
unit circle) iff `2 cosh(cT) < |τ|`, `τ = 2 cos θ₁ cos θ₂ − (ν₁/ν₂ + ν₂/ν₁) sin θ₁ sin θ₂`. -/
@[tmio T, powerlib_foundation] theorem floquetUnstable_iff
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) (hc : 0 ≤ c) (hT : 0 < T) :
    (∃ μ ∈ spectrum ℂ ((meissnerMonodromy c ω₀ ε T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔
      2 * Real.cosh (c * T) < |reducedTrace ν₁ ν₂ T| := by
  have hdet := det_meissnerMonodromy c ω₀ ε T
  have h0 : 0 < (meissnerMonodromy c ω₀ ε T).det := by rw [hdet]; positivity
  have h1 : (meissnerMonodromy c ω₀ ε T).det ≤ 1 := by
    rw [hdet, Real.exp_le_one_iff]; nlinarith
  rw [Periodic.exists_one_lt_norm_iff h0 h1, hdet, trace_meissnerMonodromy hν₁ hν₂ h₁ h₂,
    abs_mul, abs_of_pos (Real.exp_pos _), one_add_exp_eq]
  exact mul_lt_mul_iff_right₀ (Real.exp_pos _)

/-- Undamped corollary (`c = 0`): instability iff `2 < |τ|`. -/
@[tmio T, powerlib_foundation] theorem undamped_floquetUnstable_iff
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε)) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε))
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) (hT : 0 < T) :
    (∃ μ ∈ spectrum ℂ ((meissnerMonodromy 0 ω₀ ε T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔
      2 < |reducedTrace ν₁ ν₂ T| := by
  have h := floquetUnstable_iff (c := 0) (ω₀ := ω₀) (ε := ε) (T := T)
    (by rw [hν₁]; ring) (by rw [hν₂]; ring) h₁ h₂ le_rfl hT
  simpa using h

/-- For `c > 0`: every multiplier lies strictly inside the unit circle iff `|τ| < 2 cosh(cT)`. -/
@[tmio T, powerlib_foundation] theorem schurStable_iff
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) (hc : 0 < c) (hT : 0 < T) :
    LTI.SchurStable (meissnerMonodromy c ω₀ ε T) ↔
      |reducedTrace ν₁ ν₂ T| < 2 * Real.cosh (c * T) := by
  have hdet := det_meissnerMonodromy c ω₀ ε T
  have h1 : (meissnerMonodromy c ω₀ ε T).det < 1 := by
    rw [hdet, Real.exp_lt_one_iff]; nlinarith
  rw [Periodic.schurStable_iff_abs_trace_lt h1, hdet, trace_meissnerMonodromy hν₁ hν₂ h₁ h₂,
    abs_mul, abs_of_pos (Real.exp_pos _), one_add_exp_eq]
  exact mul_lt_mul_iff_right₀ (Real.exp_pos _)

/-- `−1` is a multiplier (antiperiodic, half-frequency response) iff `τ = −2 cosh(cT)`. -/
@[tmio T, powerlib_foundation] theorem neg_one_mem_spectrum_iff
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) :
    (-1 : ℂ) ∈ spectrum ℂ ((meissnerMonodromy c ω₀ ε T).map (algebraMap ℝ ℂ)) ↔
      reducedTrace ν₁ ν₂ T = -(2 * Real.cosh (c * T)) := by
  rw [Periodic.neg_one_mem_spectrum_iff, det_meissnerMonodromy,
    trace_meissnerMonodromy hν₁ hν₂ h₁ h₂, one_add_exp_eq,
    show -(Real.exp (-(c * T)) * (2 * Real.cosh (c * T))) =
      Real.exp (-(c * T)) * -(2 * Real.cosh (c * T)) by ring]
  exact mul_right_inj' (Real.exp_pos _).ne'

/-- `+1` is a multiplier (periodic response) iff `τ = 2 cosh(cT)`. -/
@[tmio T, powerlib_foundation] theorem one_mem_spectrum_iff
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) :
    (1 : ℂ) ∈ spectrum ℂ ((meissnerMonodromy c ω₀ ε T).map (algebraMap ℝ ℂ)) ↔
      reducedTrace ν₁ ν₂ T = 2 * Real.cosh (c * T) := by
  rw [Periodic.one_mem_spectrum_iff, det_meissnerMonodromy,
    trace_meissnerMonodromy hν₁ hν₂ h₁ h₂, one_add_exp_eq]
  exact mul_right_inj' (Real.exp_pos _).ne'

/-- **The subharmonic mode on the boundary.** If `τ = −2 cosh(cT)` there is a real `w ≠ 0` with
`M w = −w`; a solution through `w` exists, and every solution through `w` is `T`-antiperiodic,
`y(t + T) = −y(t)` for `t ≥ 0`: a sustained oscillation of period `2T` (half the pump
frequency) although `c ≥ 0` damps every frozen stiffness. -/
@[tmio T, powerlib_foundation] theorem antiperiodic_of_boundary
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) (hT : 0 < T)
    (hb : reducedTrace ν₁ ν₂ T = -(2 * Real.cosh (c * T))) :
    ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ meissnerMonodromy c ω₀ ε T *ᵥ w = -w ∧
      (∃ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Ici 0) ∧
        (∀ t, 0 ≤ t →
          HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) ∧
        y 0 = w) ∧
      ∀ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Ici 0) →
        (∀ t, 0 ≤ t →
          HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) →
        y 0 = w → ∀ t, 0 ≤ t → y (t + T) = -y t := by
  have htr : (meissnerMonodromy c ω₀ ε T).trace = -(1 + (meissnerMonodromy c ω₀ ε T).det) := by
    rw [det_meissnerMonodromy, trace_meissnerMonodromy hν₁ hν₂ h₁ h₂, one_add_exp_eq, hb]
    ring
  have hdet : (1 + meissnerMonodromy c ω₀ ε T).det = 0 := by
    have e : (1 + meissnerMonodromy c ω₀ ε T).det =
        1 + (meissnerMonodromy c ω₀ ε T).trace + (meissnerMonodromy c ω₀ ε T).det := by
      simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring
    rw [e, htr]; ring
  obtain ⟨w, hw, hMw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hMw' : meissnerMonodromy c ω₀ ε T *ᵥ w = -w := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at hMw
    exact (eq_neg_of_add_eq_zero_right hMw)
  obtain ⟨hc, hd, h0⟩ := flow_solution (c := c) (ω₀ := ω₀) (ε := ε) hT w
  refine ⟨w, hw, hMw', ⟨_, hc, hd, h0⟩, fun y hcont hy hy0 t ht => ?_⟩
  rw [solution_add_period hT hcont hy ht, hy0, hMw', Matrix.mulVec_neg,
    solution_eq_flow hT hcont hy ht, hy0]

/-- **The harmonic mode on the other boundary.** If `τ = 2 cosh(cT)` there is a real `w ≠ 0`
with `M w = w`; a solution through `w` exists, and every solution through `w` is `T`-periodic. -/
@[tmio T, powerlib_foundation] theorem periodic_of_boundary
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) (hT : 0 < T)
    (hb : reducedTrace ν₁ ν₂ T = 2 * Real.cosh (c * T)) :
    ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ meissnerMonodromy c ω₀ ε T *ᵥ w = w ∧
      (∃ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Ici 0) ∧
        (∀ t, 0 ≤ t →
          HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) ∧
        y 0 = w) ∧
      ∀ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Ici 0) →
        (∀ t, 0 ≤ t →
          HasDerivWithinAt y (oscMatrix c (stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) →
        y 0 = w → ∀ t, 0 ≤ t → y (t + T) = y t := by
  have htr : (meissnerMonodromy c ω₀ ε T).trace = 1 + (meissnerMonodromy c ω₀ ε T).det := by
    rw [det_meissnerMonodromy, trace_meissnerMonodromy hν₁ hν₂ h₁ h₂, one_add_exp_eq, hb]
  have hdet : (1 - meissnerMonodromy c ω₀ ε T).det = 0 := by
    have e : (1 - meissnerMonodromy c ω₀ ε T).det =
        1 - (meissnerMonodromy c ω₀ ε T).trace + (meissnerMonodromy c ω₀ ε T).det := by
      simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring
    rw [e, htr]; ring
  obtain ⟨w, hw, hMw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hMw' : meissnerMonodromy c ω₀ ε T *ᵥ w = w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMw
    exact hMw.symm
  obtain ⟨hc, hd, h0⟩ := flow_solution (c := c) (ω₀ := ω₀) (ε := ε) hT w
  refine ⟨w, hw, hMw', ⟨_, hc, hd, h0⟩, fun y hcont hy hy0 t ht => ?_⟩
  rw [solution_add_period hT hcont hy ht, hy0, hMw', solution_eq_flow hT hcont hy ht, hy0]

/-- Without modulation (`ν₁ = ν₂ = ν`) the reduced trace is `2 cos(νT)`. -/
@[tmio T, powerlib_foundation] theorem reducedTrace_self {ν : ℝ} (hν0 : ν ≠ 0) (T : ℝ) :
    reducedTrace ν ν T = 2 * Real.cos (ν * T) := by
  have h2 := Real.cos_two_mul (ν * T / 2)
  rw [show 2 * (ν * T / 2) = ν * T by ring] at h2
  rw [reducedTrace, div_self hν0, h2]
  linear_combination (-2) * Real.sin_sq_add_cos_sq (ν * T / 2)

/-- **No modulation, no parametric instability.** For `ε = 0` and `c > 0` (and
`ω₀² > c²`) every multiplier lies strictly inside the unit circle, for every period `T > 0`
(every pump frequency). -/
@[tmio T, powerlib_foundation] theorem unmodulated_schurStable {ν : ℝ}
    (hν : ν ^ 2 = ω₀ ^ 2 - c ^ 2) (hν0 : ν ≠ 0) (hc : 0 < c) (hT : 0 < T) :
    LTI.SchurStable (meissnerMonodromy c ω₀ 0 T) := by
  have hν' : ν ^ 2 = ω₀ ^ 2 * (1 + 0) - c ^ 2 := by rw [hν]; ring
  have hν'' : ν ^ 2 = ω₀ ^ 2 * (1 - 0) - c ^ 2 := by rw [hν]; ring
  rw [schurStable_iff hν' hν'' hν0 hν0 hc hT, reducedTrace_self hν0, abs_mul, abs_two]
  have h1 : |Real.cos (ν * T)| ≤ 1 := Real.abs_cos_le_one _
  have h2 : 1 < Real.cosh (c * T) := Real.one_lt_cosh.mpr (by positivity)
  linarith

end Boundary

/-! ## The centre of the principal tongue -/

section Centre

variable {c ω₀ ε T ν₁ ν₂ : ℝ}

/-- At the tongue centre `θ₁ + θ₂ = π` (`T = 2π/(ν₁ + ν₂)`):
`τ = −2 − ((ν₁ − ν₂)²/(ν₁ν₂)) sin² θ₁`. -/
@[tmio T, powerlib_foundation] theorem reducedTrace_centre (h₁ : 0 < ν₁) (h₂ : 0 < ν₂)
    (hT : T = 2 * Real.pi / (ν₁ + ν₂)) :
    reducedTrace ν₁ ν₂ T =
      -2 - (ν₁ - ν₂) ^ 2 / (ν₁ * ν₂) * Real.sin (ν₁ * T / 2) ^ 2 := by
  have hsum : ν₂ * T / 2 = Real.pi - ν₁ * T / 2 := by
    rw [hT]; field_simp; ring
  rw [reducedTrace, hsum, Real.cos_pi_sub, Real.sin_pi_sub]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (ν₁ * T / 2)]

/-- At the tongue centre: instability iff `(ν₁ − ν₂)² sin² θ₁ > 4 ν₁ν₂ sinh²(cT/2)`. -/
@[tmio T, powerlib_foundation] theorem centre_floquetUnstable_iff
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : 0 < ν₁) (h₂ : 0 < ν₂) (hc : 0 ≤ c) (hT : T = 2 * Real.pi / (ν₁ + ν₂)) :
    (∃ μ ∈ spectrum ℂ ((meissnerMonodromy c ω₀ ε T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔
      4 * (ν₁ * ν₂) * Real.sinh (c * T / 2) ^ 2 < (ν₁ - ν₂) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2 := by
  have hT0 : 0 < T := by rw [hT]; positivity
  rw [floquetUnstable_iff hν₁ hν₂ h₁.ne' h₂.ne' hc hT0, reducedTrace_centre h₁ h₂ hT]
  have hp : 0 < ν₁ * ν₂ := mul_pos h₁ h₂
  have hnn : 0 ≤ (ν₁ - ν₂) ^ 2 / (ν₁ * ν₂) * Real.sin (ν₁ * T / 2) ^ 2 := by positivity
  rw [show -2 - (ν₁ - ν₂) ^ 2 / (ν₁ * ν₂) * Real.sin (ν₁ * T / 2) ^ 2 =
      -(2 + (ν₁ - ν₂) ^ 2 / (ν₁ * ν₂) * Real.sin (ν₁ * T / 2) ^ 2) by ring, abs_neg,
    abs_of_nonneg (by positivity)]
  have hcosh : Real.cosh (c * T) = 1 + 2 * Real.sinh (c * T / 2) ^ 2 := by
    rw [show c * T = 2 * (c * T / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]
    ring_nf
  rw [hcosh, div_mul_eq_mul_div, ← sub_pos]
  constructor
  · intro h
    have : 0 < (ν₁ - ν₂) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2 / (ν₁ * ν₂) -
        4 * Real.sinh (c * T / 2) ^ 2 := by linarith
    rw [← sub_pos]
    have e : (ν₁ - ν₂) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2 - 4 * (ν₁ * ν₂) *
        Real.sinh (c * T / 2) ^ 2 = (ν₁ * ν₂) * ((ν₁ - ν₂) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2 /
          (ν₁ * ν₂) - 4 * Real.sinh (c * T / 2) ^ 2) := by field_simp
    rw [e]
    positivity
  · intro h
    have e : 2 + (ν₁ - ν₂) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2 / (ν₁ * ν₂) -
        2 * (1 + 2 * Real.sinh (c * T / 2) ^ 2) = ((ν₁ - ν₂) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2 -
          4 * (ν₁ * ν₂) * Real.sinh (c * T / 2) ^ 2) / (ν₁ * ν₂) := by field_simp; ring
    rw [e]
    exact div_pos (by linarith) hp

/-- **The tongue-centre threshold in the modulation depth.** At `Ω = ν₁ + ν₂`
(`T = 2π/(ν₁ + ν₂)`), instability iff
`ε ω₀² |sin θ₁| > √(ν₁ν₂) (ν₁ + ν₂) sinh(πc/(ν₁ + ν₂))`. -/
@[tmio T, powerlib_foundation] theorem centre_threshold_iff
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : 0 < ν₁) (h₂ : 0 < ν₂) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hT : T = 2 * Real.pi / (ν₁ + ν₂)) :
    (∃ μ ∈ spectrum ℂ ((meissnerMonodromy c ω₀ ε T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔
      √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (Real.pi * c / (ν₁ + ν₂)) <
        ε * ω₀ ^ 2 * |Real.sin (ν₁ * T / 2)| := by
  rw [centre_floquetUnstable_iff hν₁ hν₂ h₁ h₂ hc hT]
  have hs : 0 < ν₁ + ν₂ := by linarith
  have hp : 0 < ν₁ * ν₂ := mul_pos h₁ h₂
  have hdiff : ν₁ - ν₂ = 2 * ε * ω₀ ^ 2 / (ν₁ + ν₂) := by
    field_simp
    nlinarith
  have hcT : c * T / 2 = Real.pi * c / (ν₁ + ν₂) := by rw [hT]; field_simp
  rw [hcT, hdiff]
  have hsh : 0 ≤ Real.sinh (Real.pi * c / (ν₁ + ν₂)) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hsq : √(ν₁ * ν₂) ^ 2 = ν₁ * ν₂ := Real.sq_sqrt hp.le
  -- compare the squares of two nonnegative quantities
  set L := √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (Real.pi * c / (ν₁ + ν₂))
  set R := ε * ω₀ ^ 2 * |Real.sin (ν₁ * T / 2)|
  have hL : 0 ≤ L := by positivity
  have hR : 0 ≤ R := by positivity
  have e1 : 4 * (ν₁ * ν₂) * Real.sinh (Real.pi * c / (ν₁ + ν₂)) ^ 2 =
      4 * L ^ 2 / (ν₁ + ν₂) ^ 2 := by
    simp only [L]; rw [mul_pow, mul_pow, hsq]; field_simp
  have e2 : (2 * ε * ω₀ ^ 2 / (ν₁ + ν₂)) ^ 2 * Real.sin (ν₁ * T / 2) ^ 2 =
      4 * R ^ 2 / (ν₁ + ν₂) ^ 2 := by
    simp only [R]; rw [mul_pow, mul_pow, sq_abs]; field_simp; ring
  rw [e1, e2, div_lt_div_iff_of_pos_right (by positivity), mul_lt_mul_iff_right₀ four_pos]
  exact pow_lt_pow_iff_left₀ hL hR two_ne_zero

/-- **Leading term `ε_c = πζ`.** Instability at the tongue centre requires
`ε ω₀² > π c √(ν₁ν₂)` (with `c = ζω₀`: `ε > πζ √(ν₁ν₂)/ω₀`), from `sinh x ≥ x` and
`|sin θ₁| ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem centre_threshold_lower
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : 0 < ν₁) (h₂ : 0 < ν₂) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hT : T = 2 * Real.pi / (ν₁ + ν₂))
    (hu : ∃ μ ∈ spectrum ℂ ((meissnerMonodromy c ω₀ ε T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) :
    Real.pi * c * √(ν₁ * ν₂) < ε * ω₀ ^ 2 := by
  have h := (centre_threshold_iff hν₁ hν₂ h₁ h₂ hc hε hT).mp hu
  have hs : 0 < ν₁ + ν₂ := by linarith
  have hx : Real.pi * c / (ν₁ + ν₂) ≤ Real.sinh (Real.pi * c / (ν₁ + ν₂)) :=
    Real.self_le_sinh_iff.mpr (by positivity)
  have hsin : |Real.sin (ν₁ * T / 2)| ≤ 1 := Real.abs_sin_le_one _
  have hεω : 0 ≤ ε * ω₀ ^ 2 := by positivity
  have hsq : 0 ≤ √(ν₁ * ν₂) := Real.sqrt_nonneg _
  calc Real.pi * c * √(ν₁ * ν₂) = √(ν₁ * ν₂) * (ν₁ + ν₂) * (Real.pi * c / (ν₁ + ν₂)) := by
        field_simp
    _ ≤ √(ν₁ * ν₂) * (ν₁ + ν₂) * Real.sinh (Real.pi * c / (ν₁ + ν₂)) := by gcongr
    _ < ε * ω₀ ^ 2 * |Real.sin (ν₁ * T / 2)| := h
    _ ≤ ε * ω₀ ^ 2 := by nlinarith

end Centre

end powerlib.ParametricResonance.Meissner
