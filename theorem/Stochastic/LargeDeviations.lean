import dependencies.Mathlib
import theorem.Attributes
import theorem.SingularPerturbation.SupNorm
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalProbability

/-! # Large deviations: definitions, Chernoff bound, Freidlin–Wentzell action, quasi-potential

The large-deviation principle, the Chernoff upper bound, Cramér's lower bound for i.i.d. sums,
the Freidlin–Wentzell action and the quasi-potential of a gradient drift.

Scope.
* Probability theory / calculus of variations, not an engineering result.
* No statement here asserts that a particular diffusion satisfies an LDP (Freidlin–Wentzell's
  theorem is not formalized); the action and the quasi-potential are deterministic variational
  objects.

Source: work-sync theory/T-large-deviations.md (LDP definition with rate function `I`, upper
bound over `cl A`, lower bound over `int A`; Cramér / Chernoff), theory/T-freidlin-wentzell.md
(action `S_{0T}(φ) = ½ ∫₀ᵀ ‖φ̇ − b(φ)‖²_{a(φ)⁻¹} dt`, `a = σσᵀ`), theory/T-quasi-potential.md
(`V_qp(x) = inf_{T, φ(0) ∈ 𝒜, φ(T) = x} S_{0T}(φ)`).

Results.
* Large-deviation principle with speed `ε → 0⁺` for a family of measures on a topological
  space, with the bounds stated for **Borel** sets `A` and a **lower semicontinuous** rate
  function (the hypotheses the note leaves implicit; written out in the statement, see the
  section header); `dirac_satisfiesLDP`: the constant family `δ_{x₀}` satisfies it with rate `0`
  at `x₀` and `∞` elsewhere (non-vacuity check).
* `chernoff_bound` (wrapper of Mathlib `ProbabilityTheory.measure_ge_le_exp_mul_mgf`),
  `chernoff_iid` — `P(Σ_{i<n} Xᵢ ≥ n a) ≤ (e^{−ta} M(t))ⁿ` for independent summands with common
  moment generating function — the exponential (Cramér) upper bound.
* `fwAction`, `fwAction_nonneg` — the Freidlin–Wentzell action for `C¹` paths with a positive
  definite diffusion matrix (the note's hypothesis "`a` invertible, `φ` absolutely continuous"
  is replaced by the explicit `C¹`/positive-definite class used here).
* `gradient_action_identity`, `gradient_action_ge`, `gradient_action_eq_iff` — for a gradient
  drift `b = −∇U` and unit diffusion, completing the square gives
  `S_{0T}(φ) = ½∫‖φ̇ − ∇U(φ)‖² + 2(U(φ(T)) − U(φ(0)))`, hence `S ≥ 2ΔU` with equality iff `φ`
  follows the reversed gradient flow; `quasiPotential_ge`: `V_qp(x) ≥ 2(U(x) − U(x_𝒜))`.
* `quasiPotential_le_of_heteroclinic`, `quasiPotential_eq_of_heteroclinic` — the matching upper
  bound, hence `V_qp(x) = 2(U(x) − U(x_𝒜))`, when an uphill orbit of the reversed gradient flow
  `ψ̇ = ∇U(ψ)` runs from `x_𝒜` (at `s → −∞`) to `x` (at `s → +∞`) — the minimum-to-saddle case,
  where the optimal path needs infinite time at both ends. The proof builds explicit
  near-optimal finite-time paths: smooth (`Real.smoothTransition`) corrections on `[0, 1]` and
  `[T − 1, T]` glued to a long piece of the orbit; the action excess is at most `n ε₀²`, with
  `ε₀` controlled by the continuity of `∇U` at the two endpoints. Hypotheses: `U` differentiable
  with continuous gradient `gU`; no Lipschitz or nondegeneracy assumption.
  `doubleWell_quasiPotential` (non-vacuity): for `U(y) = y⁴/4 − y²/2` the explicit orbit
  `ψ(s) = 1/√(1 + e^{2s})` gives `V_qp(1 → 0) = 1/2`.
* Cramér lower bound at **exposed points** (exponential tilting + Chebyshev under the tilted
  law, no change of measure on path space): for i.i.d. `Xᵢ` with cumulant generating function
  `Λ`, `θ` interior to the effective domain and `x = Λ'(θ)`,
  `cramer_lower_exposed`: `x ∈ G` open ⇒ eventually `(1/n) log P(S_n/n ∈ G) ≥ −(θx − Λ(θ)) − ε`;
  `cramerRate` (Legendre transform of `Λ` over its effective domain), `cgf_tangent_le`
  (`Λ(t) ≥ Λ(θ) + (t − θ)Λ'(θ)`), `cramerRate_eq` (`I(Λ'(θ)) = θΛ'(θ) − Λ(θ)`);
  `cramer_lower_bound`: `−inf {I(x) : x ∈ G exposed} ≤ liminf (1/n) log P(S_n/n ∈ G)`.
* Bounded summands (`|X₀| ≤ C` a.s.): `exists_deriv_cgf_eq` — every `x` with `P(X₀ < x) > 0`
  and `P(X₀ > x) > 0` is exposed (`Λ` is finite and analytic on `ℝ`, `E[(X₀ − x) e^{θX₀}]`
  changes sign, intermediate value theorem); `cramer_lower_bound_bounded` (interior points of
  the hull); the endpoint cases `P(X₀ > x) = 0` / `P(X₀ < x) = 0` (which contain every point
  outside the hull) via `P(S_n/n ∈ G) ≥ P(X₀ ∈ (x − δ, x])ⁿ` and
  `I(x) ≥ −log P(X₀ ∈ (x − δ, x])` (no boundedness needed there) and the reflection `X ↦ −X`;
  **`cramer_lower_bound_of_bounded`**: Cramér's lower bound
  `−inf_{x ∈ G} I(x) ≤ liminf (1/n) log P(S_n/n ∈ G)` for every open `G` (written
  `⨆ x ∈ G, −I(x) ≤ liminf …`).
* General i.i.d. summands (no boundedness or moment assumption; Dembo–Zeitouni Thm 2.2.3):
  **`cramer_lower_bound_general`**: `−inf_{x ∈ G} I(x) ≤ liminf (1/n) log P(S_n/n ∈ G)` for
  every open `G`, at every `x` (non-exposed points, non-steep `Λ`, `Λ = ∞` off `0`, `I(x) = ∞`
  included). Proof by truncation: for each level `M`, `cramer_lower_bound_of_bounded` is applied
  to i.i.d. copies of `X₀` conditioned on `|X₀| ≤ M` (coordinates of the product measure
  `Measure.infinitePi` of the conditioned law `ProbabilityTheory.cond`), and
  `P(S_n/n ∈ G) ≥ P(|X₀| ≤ M)ⁿ ν_M^{⊗n}(S_n/n ∈ G)` (product measure restricted to the box);
  this yields tilts `t` with `E[e^{t(X₀ − x)}; |X₀| ≤ M] ≤ e^{ℓ + ε}` (`ℓ` the `liminf`). When
  both `P(X₀ < x)` and `P(X₀ > x)` are positive the truncated exponential moments are coercive
  in `t` uniformly in `M`, so the sublevel sets are nested nonempty compacts; their common point
  `t` satisfies `E[e^{t(X₀ − x)}] ≤ e^ℓ` by monotone convergence `M → ∞`, i.e. `−I(x) ≤ ℓ`. The
  remaining cases `P(X₀ > x) = 0` / `P(X₀ < x) = 0` are the endpoint lemmas above.
  The rate `I = cramerRate X₀` is the Legendre transform over the effective domain, i.e. the
  classical `sup_{t ∈ ℝ} (t x − Λ(t))` with `Λ = +∞` off the domain.
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Real Set Topology Matrix
open scoped ENNReal Classical

/-! ## Large-deviation principle

A family of measures `P ε` satisfies the **large-deviation principle** with speed `ε → 0⁺` and
rate function `I` (Borel sets, lower semicontinuous rate) when `I` is lower semicontinuous and,
for every measurable `A`,
`limsup_{ε → 0⁺} ε log P_ε(A) ≤ −inf_{x ∈ cl A} I(x)` (upper bound) and
`−inf_{x ∈ int A} I(x) ≤ liminf_{ε → 0⁺} ε log P_ε(A)` (lower bound).
The principle is written out in the statement of `dirac_satisfiesLDP`. -/

/-- Rate function of a point mass: `0` at `x₀`, `∞` elsewhere. -/
def diracRate {E : Type*} (x₀ : E) (x : E) : ℝ≥0∞ := if x = x₀ then 0 else ⊤

/-- **Non-vacuity**: the constant family `δ_{x₀}` satisfies the large-deviation principle with
speed `ε → 0⁺` and rate function `diracRate x₀` (on a T1 space): the rate is lower semicontinuous,
and for every Borel set `A` the upper bound `limsup_{ε → 0⁺} ε log δ_{x₀}(A) ≤ −inf_{cl A} I` and
the lower bound `−inf_{int A} I ≤ liminf_{ε → 0⁺} ε log δ_{x₀}(A)` hold. -/
@[tmio T, powerlib_foundation] theorem dirac_satisfiesLDP {E : Type*} [TopologicalSpace E] [T1Space E]
    [MeasurableSpace E] [MeasurableSingletonClass E] (x₀ : E) :
    LowerSemicontinuous (diracRate x₀) ∧
      (∀ A : Set E, MeasurableSet A →
        limsup (fun ε : ℝ => (ε : EReal) * ENNReal.log (Measure.dirac x₀ A)) (𝓝[>] 0) ≤
          -(⨅ x ∈ closure A, ((diracRate x₀ x : ℝ≥0∞) : EReal))) ∧
      (∀ A : Set E, MeasurableSet A →
        -(⨅ x ∈ interior A, ((diracRate x₀ x : ℝ≥0∞) : EReal)) ≤
          liminf (fun ε : ℝ => (ε : EReal) * ENNReal.log (Measure.dirac x₀ A)) (𝓝[>] 0)) := by
  have hval : ∀ A : Set E, MeasurableSet A → ∀ ε : ℝ, 0 < ε →
      (ε : EReal) * ENNReal.log (Measure.dirac x₀ A) = if x₀ ∈ A then 0 else ⊥ := by
    intro A hA ε hε
    rw [Measure.dirac_apply' _ hA]
    by_cases h : x₀ ∈ A
    · simp [h]
    · simp [h, EReal.coe_mul_bot_of_pos hε]
  have hinf : ∀ S : Set E, (⨅ x ∈ S, ((diracRate x₀ x : ℝ≥0∞) : EReal)) =
      if x₀ ∈ S then 0 else ⊤ := by
    intro S
    by_cases h : x₀ ∈ S
    · simp only [h, ↓reduceIte]
      refine le_antisymm (iInf₂_le_of_le x₀ h (by simp [diracRate])) ?_
      refine le_iInf₂ fun x _ => ?_
      unfold diracRate; split_ifs <;> simp
    · simp only [h, ↓reduceIte]
      refine le_antisymm le_top (le_iInf₂ fun x hx => ?_)
      have : x ≠ x₀ := fun e => h (e ▸ hx)
      simp [diracRate, this]
  refine ⟨?_, fun A hA => ?_, fun A hA => ?_⟩
  · -- lower semicontinuity: `{x | t < I x}` is open
    intro x t ht
    by_cases hx : x = x₀
    · subst hx; simp [diracRate] at ht
    · have hopen : IsOpen ({x₀}ᶜ : Set E) := isOpen_compl_singleton
      filter_upwards [hopen.mem_nhds hx] with y hy
      simp only [mem_compl_iff, mem_singleton_iff] at hy
      simpa [diracRate, hy] using (lt_of_lt_of_le ht (by simp [diracRate, hx]) : t < ⊤)
  · have hev : (fun ε : ℝ => (ε : EReal) * ENNReal.log (Measure.dirac x₀ A)) =ᶠ[𝓝[>] 0]
        fun _ => if x₀ ∈ A then 0 else ⊥ :=
      eventually_nhdsWithin_of_forall fun ε hε => hval A hA ε hε
    rw [limsup_congr hev, limsup_const, hinf]
    by_cases h : x₀ ∈ A
    · simp [h, subset_closure h]
    · simp [h]
  · have hev : (fun ε : ℝ => (ε : EReal) * ENNReal.log (Measure.dirac x₀ A)) =ᶠ[𝓝[>] 0]
        fun _ => if x₀ ∈ A then 0 else ⊥ :=
      eventually_nhdsWithin_of_forall fun ε hε => hval A hA ε hε
    rw [liminf_congr hev, liminf_const, hinf]
    by_cases h : x₀ ∈ interior A
    · simp [h, interior_subset h]
    · simp [h]

/-! ## Chernoff / Cramér upper bound -/

/-- **Chernoff bound** (Mathlib `ProbabilityTheory.measure_ge_le_exp_mul_mgf`). -/
@[powerlib_foundation] theorem chernoff_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {t : ℝ} (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε) * mgf X μ t :=
  measure_ge_le_exp_mul_mgf ε ht h_int

/-- **Exponential bound for i.i.d.-type sums**: independent summands with common moment
generating function `M(t)` satisfy `P(Σ_{i<n} Xᵢ ≥ n a) ≤ (e^{−ta} M(t))ⁿ`. -/
@[powerlib_foundation] theorem chernoff_iid {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) {t a M : ℝ} (ht : 0 ≤ t) (hM : ∀ i, mgf (X i) μ t = M)
    (hint : ∀ i, Integrable (fun ω => exp (t * X i ω)) μ) (n : ℕ) :
    μ.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω} ≤ (exp (-t * a) * M) ^ n := by
  have hsum : Integrable (fun ω => exp (t * (∑ i ∈ Finset.range n, X i) ω)) μ := by
    have h := hindep.integrable_exp_mul_sum (s := Finset.range n) hmeas (fun i _ => hint i)
    simpa using h
  have h := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ Finset.range n, X i) (n * a) ht hsum
  rw [hindep.mgf_sum hmeas, Finset.prod_congr rfl (fun i _ => hM i), Finset.prod_const,
    Finset.card_range] at h
  have e : exp (-t * (n * a)) = exp (-t * a) ^ n := by rw [← exp_nat_mul]; ring_nf
  rw [e, ← mul_pow] at h
  simpa [Finset.sum_apply] using h

/-! ## Freidlin–Wentzell action -/

variable {n : ℕ}

/-- **Freidlin–Wentzell action** of a path `φ` with derivative `φd` on `[0, T]`, drift `b`,
diffusion matrix `a` (`a = σσᵀ`): `S = ½ ∫₀ᵀ (φ̇ − b(φ))ᵀ a(φ)⁻¹ (φ̇ − b(φ)) dt`. -/
def fwAction (b : (Fin n → ℝ) → Fin n → ℝ) (a : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (φ φd : ℝ → Fin n → ℝ) (T : ℝ) : ℝ :=
  1 / 2 * ∫ t in (0 : ℝ)..T,
    (φd t - b (φ t)) ⬝ᵥ ((a (φ t))⁻¹ *ᵥ (φd t - b (φ t)))

/-- The action is nonnegative when the diffusion matrix is positive definite along the path. -/
@[powerlib_foundation] theorem fwAction_nonneg {b : (Fin n → ℝ) → Fin n → ℝ}
    {a : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {φ φd : ℝ → Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : ∀ t ∈ Icc 0 T, (a (φ t)).PosDef) : 0 ≤ fwAction b a φ φd T := by
  unfold fwAction
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg hT
  intro t ht
  have := (ha t ht).inv.posSemidef.dotProduct_mulVec_nonneg (φd t - b (φ t))
  simpa using this

/-! ## Gradient systems: completing the square -/

/-- Action with unit diffusion `a = I`: `½ ∫ ‖φ̇ − b(φ)‖²`. -/
def unitAction (b : (Fin n → ℝ) → Fin n → ℝ) (φ φd : ℝ → Fin n → ℝ) (T : ℝ) : ℝ :=
  1 / 2 * ∫ t in (0 : ℝ)..T, (φd t - b (φ t)) ⬝ᵥ (φd t - b (φ t))

/-- With `a = I` the Freidlin–Wentzell action is `unitAction`. -/
@[powerlib_foundation] theorem fwAction_one (b : (Fin n → ℝ) → Fin n → ℝ) (φ φd : ℝ → Fin n → ℝ)
    (T : ℝ) : fwAction b (fun _ => 1) φ φd T = unitAction b φ φd T := by
  simp [fwAction, unitAction]

/-- **Completing the square (gradient drift `b = −∇U`, unit diffusion)**: if `U ∘ φ` has
derivative `∇U(φ) · φ̇` along the path (chain rule) and the integrands are continuous,
`S_{0T}(φ) = ½∫₀ᵀ ‖φ̇ − ∇U(φ)‖² + 2 (U(φ(T)) − U(φ(0)))`. -/
@[powerlib_foundation] theorem gradient_action_identity {U : (Fin n → ℝ) → ℝ}
    {gU : (Fin n → ℝ) → Fin n → ℝ} {φ φd : ℝ → Fin n → ℝ} {T : ℝ}
    (hchain : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => U (φ s)) (gU (φ t) ⬝ᵥ φd t) t)
    (hcont : Continuous fun t => gU (φ t) ⬝ᵥ φd t)
    (hc1 : Continuous fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t))) :
    unitAction (fun x => -gU x) φ φd T =
      1 / 2 * (∫ t in (0 : ℝ)..T, (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t))) +
        2 * (U (φ T) - U (φ 0)) := by
  have hftc : ∫ t in (0 : ℝ)..T, gU (φ t) ⬝ᵥ φd t = U (φ T) - U (φ 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hchain (hcont.intervalIntegrable _ _)
  have hpt : ∀ t, (φd t - -gU (φ t)) ⬝ᵥ (φd t - -gU (φ t)) =
      (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) + 4 * (gU (φ t) ⬝ᵥ φd t) := by
    intro t
    simp only [sub_neg_eq_add, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
      dotProduct_comm (φd t) (gU (φ t))]
    ring
  unfold unitAction
  simp_rw [hpt]
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
    ((hcont.const_mul 4).intervalIntegrable _ _), intervalIntegral.integral_const_mul, hftc]
  ring

/-- **`S ≥ 2ΔU`** along every admissible path (`T ≥ 0`). -/
@[powerlib_foundation] theorem gradient_action_ge {U : (Fin n → ℝ) → ℝ}
    {gU : (Fin n → ℝ) → Fin n → ℝ} {φ φd : ℝ → Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hchain : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => U (φ s)) (gU (φ t) ⬝ᵥ φd t) t)
    (hcont : Continuous fun t => gU (φ t) ⬝ᵥ φd t)
    (hc1 : Continuous fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t))) :
    2 * (U (φ T) - U (φ 0)) ≤ unitAction (fun x => -gU x) φ φd T := by
  rw [gradient_action_identity hchain hcont hc1]
  have : 0 ≤ ∫ t in (0 : ℝ)..T, (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) :=
    intervalIntegral.integral_nonneg hT fun t _ => by
      simpa using dotProduct_self_star_nonneg (φd t - gU (φ t))
  linarith

/-- **Equality case**: `S = 2ΔU` iff the path follows the reversed gradient flow `φ̇ = ∇U(φ)` on
`[0, T]` (`T > 0`). -/
@[powerlib_foundation] theorem gradient_action_eq_iff {U : (Fin n → ℝ) → ℝ}
    {gU : (Fin n → ℝ) → Fin n → ℝ} {φ φd : ℝ → Fin n → ℝ} {T : ℝ} (hT : 0 < T)
    (hchain : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => U (φ s)) (gU (φ t) ⬝ᵥ φd t) t)
    (hcont : Continuous fun t => gU (φ t) ⬝ᵥ φd t)
    (hc1 : Continuous fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t))) :
    unitAction (fun x => -gU x) φ φd T = 2 * (U (φ T) - U (φ 0)) ↔
      ∀ t ∈ Icc 0 T, φd t = gU (φ t) := by
  rw [gradient_action_identity hchain hcont hc1]
  have hnn : ∀ t, 0 ≤ (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) := fun t => by
    simpa using dotProduct_self_star_nonneg (φd t - gU (φ t))
  set f : ℝ → ℝ := fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) with hfdef
  constructor
  · intro h
    have hz : ∫ t in (0 : ℝ)..T, f t = 0 := by simp only [hfdef]; linarith
    intro t0 ht0
    by_contra hne
    have hpos0 : 0 < f t0 := by
      rcases (hnn t0).lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd (sub_eq_zero.mp (dotProduct_self_eq_zero.mp heq.symm)) hne
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hc1 t0 (f t0 / 2) (by linarith)
    set c := max 0 (t0 - δ / 2)
    set d := min T (t0 + δ / 2)
    have hcd : c < d := by
      simp only [c, d, max_lt_iff, lt_min_iff]
      refine ⟨⟨by linarith [ht0.1, ht0.2], by linarith [ht0.1, ht0.2]⟩,
        ⟨by linarith [ht0.1, ht0.2], by linarith [ht0.1, ht0.2]⟩⟩
    have hfpos : ∀ t ∈ Ioo c d, 0 < f t := by
      intro t ht
      have h1 : dist t t0 < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2, le_max_right 0 (t0 - δ / 2),
          min_le_right T (t0 + δ / 2)]
      have := hball t h1
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have hcd_pos : 0 < ∫ t in c..d, f t :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hc1.intervalIntegrable _ _) hfpos hcd
    have hmono : ∫ t in c..d, f t ≤ ∫ t in (0 : ℝ)..T, f t :=
      intervalIntegral.integral_mono_interval (le_max_left _ _) hcd.le (min_le_left _ _)
        (Eventually.of_forall hnn) (hc1.intervalIntegrable _ _)
    linarith
  · intro h
    have hz : ∫ t in (0 : ℝ)..T, f t = 0 := by
      have : ∫ t in (0 : ℝ)..T, f t = ∫ t in (0 : ℝ)..T, (0 : ℝ) :=
        intervalIntegral.integral_congr fun t ht => by
          rw [uIcc_of_le hT.le] at ht
          simp only [hfdef, h t ht, sub_self, dotProduct_zero]
      rw [this, intervalIntegral.integral_zero]
    simp only [hfdef] at hz
    rw [hz]; ring

/-! ## Quasi-potential -/

/-- **Quasi-potential** (unit diffusion) from an attractor point `xA`:
`V_qp(x) = inf { S_{0T}(φ) : T ≥ 0, φ(0) = xA, φ(T) = x }` over paths with continuous action
integrand along which the chain rule for `U` holds (`ℝ≥0∞`-valued, `∞` if no admissible path). -/
def quasiPotential (U : (Fin n → ℝ) → ℝ) (gU : (Fin n → ℝ) → Fin n → ℝ) (xA x : Fin n → ℝ) :
    ℝ≥0∞ :=
  ⨅ (T : ℝ) (φ : ℝ → Fin n → ℝ) (φd : ℝ → Fin n → ℝ)
    (_ : 0 ≤ T ∧ φ 0 = xA ∧ φ T = x ∧
      (∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => U (φ s)) (gU (φ t) ⬝ᵥ φd t) t) ∧
      Continuous (fun t => gU (φ t) ⬝ᵥ φd t) ∧
      Continuous (fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)))),
    ENNReal.ofReal (unitAction (fun y => -gU y) φ φd T)

/-- **Gradient systems (T-quasi-potential)**: `V_qp(x) ≥ 2 (U(x) − U(x_𝒜))`. -/
@[powerlib_foundation] theorem quasiPotential_ge (U : (Fin n → ℝ) → ℝ)
    (gU : (Fin n → ℝ) → Fin n → ℝ) (xA x : Fin n → ℝ) :
    ENNReal.ofReal (2 * (U x - U xA)) ≤ quasiPotential U gU xA x := by
  unfold quasiPotential
  refine le_iInf fun T => le_iInf fun φ => le_iInf fun φd => le_iInf fun h => ?_
  obtain ⟨hT, h0, hTx, hchain, hcont, hc1⟩ := h
  apply ENNReal.ofReal_le_ofReal
  have := gradient_action_ge hT hchain hcont hc1
  rwa [h0, hTx] at this

/-! ## Upper bound for the quasi-potential of a gradient system -/

/-- The derivative of the smooth transition vanishes outside `(0, 1)`. -/
private theorem deriv_smoothTransition_eq_zero {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · refine IsLocalMin.deriv_eq_zero (Eventually.of_forall fun y => ?_)
    rw [Real.smoothTransition.zero_of_nonpos ht]
    exact Real.smoothTransition.nonneg y
  · refine IsLocalMax.deriv_eq_zero (Eventually.of_forall fun y => ?_)
    rw [Real.smoothTransition.one_of_one_le ht]
    exact Real.smoothTransition.le_one y

private theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

private theorem hasDerivAt_smoothTransition (t : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) t).hasDerivAt

/-- A uniform bound for the derivative of the smooth transition. -/
private theorem exists_bound_deriv_smoothTransition :
    ∃ M, 0 ≤ M ∧ ∀ t, |deriv Real.smoothTransition t| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_deriv_smoothTransition.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hC t ht).trans (le_max_left _ _)
  · have : t ≤ 0 ∨ 1 ≤ t := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · exact Or.inl h.le
      · exact Or.inr h.le
    rw [deriv_smoothTransition_eq_zero this, abs_zero]
    exact le_max_right _ _

/-- **Core estimate**: the explicit path that starts at `xA`, corrects onto the reversed gradient
orbit `ψ` during `[0, 1]`, follows `ψ` and corrects onto `x` during `[T − 1, T]` has action at most
`2 (U(x) − U(xA)) + n ε₀²` when the residual is at most `ε₀` on the two correction windows. -/
private theorem quasiPotential_le_of_window {U : (Fin n → ℝ) → ℝ}
    {gU : (Fin n → ℝ) → Fin n → ℝ} (hU : Differentiable ℝ U)
    (hgrad : ∀ y v, fderiv ℝ U y v = gU y ⬝ᵥ v) (hgc : Continuous gU)
    {ψ : ℝ → Fin n → ℝ} (hψ : ∀ s, HasDerivAt ψ (gU (ψ s)) s) {xA x : Fin n → ℝ} {a T ε₀ : ℝ}
    (hT : 2 ≤ T)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, ‖gU (ψ (a + t)) -
        gU (ψ (a + t) + (1 - Real.smoothTransition t) • (xA - ψ a)) -
        deriv Real.smoothTransition t • (xA - ψ a)‖ ≤ ε₀)
    (h₂ : ∀ t ∈ Icc (T - 1) T, ‖gU (ψ (a + t)) -
        gU (ψ (a + t) + Real.smoothTransition (t - (T - 1)) • (x - ψ (a + T))) +
        deriv Real.smoothTransition (t - (T - 1)) • (x - ψ (a + T))‖ ≤ ε₀) :
    quasiPotential U gU xA x ≤ ENNReal.ofReal (2 * (U x - U xA) + n * ε₀ ^ 2) := by
  set σ := Real.smoothTransition with hσ
  set σ' := deriv Real.smoothTransition with hσ'
  set e₁ := xA - ψ a with he₁
  set e₂ := x - ψ (a + T) with he₂
  set c := T - 1 with hc
  have hc1 : 1 ≤ c := by linarith
  set φ : ℝ → Fin n → ℝ := fun t => ψ (a + t) + (1 - σ t) • e₁ + σ (t - c) • e₂ with hφdef
  set φd : ℝ → Fin n → ℝ := fun t => gU (ψ (a + t)) + (-σ' t) • e₁ + σ' (t - c) • e₂
    with hφddef
  have hφ : ∀ t, HasDerivAt φ (φd t) t := by
    intro t
    have h1 : HasDerivAt (fun s => ψ (a + s)) (gU (ψ (a + t))) t := (hψ (a + t)).comp_const_add a t
    have h2 : HasDerivAt (fun s => (1 - σ s) • e₁) ((-σ' t) • e₁) t :=
      ((hasDerivAt_smoothTransition t).const_sub 1).smul_const e₁
    have h3 : HasDerivAt (fun s => σ (s - c) • e₂) (σ' (t - c) • e₂) t :=
      ((hasDerivAt_smoothTransition (t - c)).comp_sub_const t c).smul_const e₂
    exact (h1.add h2).add h3
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun s => (hψ s).continuousAt
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  have hφdc : Continuous φd :=
    ((hgc.comp (hψc.comp (continuous_const.add continuous_id))).add
      (continuous_deriv_smoothTransition.neg.smul continuous_const)).add
      ((continuous_deriv_smoothTransition.comp (continuous_id.sub continuous_const)).smul
        continuous_const)
  have hchain : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => U (φ s)) (gU (φ t) ⬝ᵥ φd t) t := by
    intro t _
    have := (hU (φ t)).hasFDerivAt.comp_hasDerivAt t (hφ t)
    rwa [hgrad] at this
  have hcont : Continuous fun t => gU (φ t) ⬝ᵥ φd t := (hgc.comp hφc).dotProduct hφdc
  have hc1' : Continuous fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) :=
    (hφdc.sub (hgc.comp hφc)).dotProduct (hφdc.sub (hgc.comp hφc))
  have hσ0 : ∀ t, t ≤ 0 → σ t = 0 := fun t ht => Real.smoothTransition.zero_of_nonpos ht
  have hσ1 : ∀ t, 1 ≤ t → σ t = 1 := fun t ht => Real.smoothTransition.one_of_one_le ht
  have hσ'0 : ∀ t, t ≤ 0 ∨ 1 ≤ t → σ' t = 0 := fun t ht => deriv_smoothTransition_eq_zero ht
  have h0 : φ 0 = xA := by
    simp only [hφdef, add_zero, hσ0 0 le_rfl, hσ0 (0 - c) (by linarith), sub_zero, one_smul,
      zero_smul, he₁]
    abel
  have hTx : φ T = x := by
    simp only [hφdef, hσ1 T (by linarith), hσ1 (T - c) (by linarith), sub_self, zero_smul,
      one_smul, add_zero, he₂]
    abel
  -- the residual on the three pieces
  set F : ℝ → ℝ := fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) with hF
  have hFn : ∀ t, ‖φd t - gU (φ t)‖ ≤ ε₀ → F t ≤ n * ε₀ ^ 2 := by
    intro t ht
    refine (SingularPerturbation.dotProduct_self_le_card_mul_norm_sq _).trans ?_
    have : ‖φd t - gU (φ t)‖ ^ 2 ≤ ε₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg n)
  have hF1 : ∀ t ∈ Icc (0 : ℝ) 1, F t ≤ n * ε₀ ^ 2 := by
    intro t ht
    apply hFn
    have e : φd t - gU (φ t) = gU (ψ (a + t)) - gU (ψ (a + t) + (1 - σ t) • e₁) - σ' t • e₁ := by
      simp only [hφdef, hφddef, hσ0 (t - c) (by linarith [ht.2]),
        hσ'0 (t - c) (Or.inl (by linarith [ht.2])), zero_smul, add_zero, neg_smul]
      abel
    rw [e]; exact h₁ t ht
  have hF2 : ∀ t ∈ Icc 1 c, F t = 0 := by
    intro t ht
    have e : φd t - gU (φ t) = 0 := by
      simp only [hφdef, hφddef, hσ0 (t - c) (by linarith [ht.2]), hσ1 t ht.1,
        hσ'0 (t - c) (Or.inl (by linarith [ht.2])), hσ'0 t (Or.inr ht.1), zero_smul, add_zero,
        neg_zero, sub_self]
    simp only [hF, e, dotProduct_zero]
  have hF3 : ∀ t ∈ Icc c T, F t ≤ n * ε₀ ^ 2 := by
    intro t ht
    apply hFn
    have e : φd t - gU (φ t) =
        gU (ψ (a + t)) - gU (ψ (a + t) + σ (t - c) • e₂) + σ' (t - c) • e₂ := by
      simp only [hφdef, hφddef, hσ1 t (by linarith [ht.1]), hσ'0 t (Or.inr (by linarith [ht.1])),
        sub_self, zero_smul, add_zero, neg_zero]
      abel
    rw [e]; exact h₂ t ht
  have hFi : ∀ p q : ℝ, IntervalIntegrable F volume p q := fun p q => hc1'.intervalIntegrable p q
  have hint : ∫ t in (0 : ℝ)..T, F t ≤ 2 * (n * ε₀ ^ 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hFi 0 1) (hFi 1 T),
      ← intervalIntegral.integral_add_adjacent_intervals (hFi 1 c) (hFi c T)]
    have i1 : ∫ t in (0 : ℝ)..1, F t ≤ n * ε₀ ^ 2 := by
      have := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) (hFi 0 1)
        (intervalIntegrable_const (c := (n : ℝ) * ε₀ ^ 2)) hF1
      simpa using this
    have i2 : ∫ t in (1 : ℝ)..c, F t = 0 := by
      have : Set.EqOn F (fun _ => (0 : ℝ)) (Set.uIcc 1 c) := by
        intro t ht
        rw [Set.uIcc_of_le hc1] at ht
        exact hF2 t ht
      rw [intervalIntegral.integral_congr this, intervalIntegral.integral_zero]
    have i3 : ∫ t in c..T, F t ≤ n * ε₀ ^ 2 := by
      have := intervalIntegral.integral_mono_on (by linarith : c ≤ T) (hFi c T)
        (intervalIntegrable_const (c := (n : ℝ) * ε₀ ^ 2)) hF3
      simpa [hc] using this
    linarith
  have haction := gradient_action_identity (U := U) (gU := gU) (φ := φ) (φd := φd) (T := T)
    hchain hcont hc1'
  rw [h0, hTx] at haction
  have hle : unitAction (fun y => -gU y) φ φd T ≤ 2 * (U x - U xA) + n * ε₀ ^ 2 := by
    rw [haction]
    have : ∫ t in (0 : ℝ)..T, (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) ≤ 2 * (n * ε₀ ^ 2) := hint
    linarith
  calc quasiPotential U gU xA x ≤ ENNReal.ofReal (unitAction (fun y => -gU y) φ φd T) := by
        unfold quasiPotential
        exact (iInf_le _ T).trans ((iInf_le _ φ).trans ((iInf_le _ φd).trans
          (iInf_le_of_le ⟨by linarith, h0, hTx, hchain, hcont, hc1'⟩ le_rfl)))
    _ ≤ ENNReal.ofReal (2 * (U x - U xA) + n * ε₀ ^ 2) := ENNReal.ofReal_le_ofReal hle

/-- **Gradient systems, upper bound `V_qp ≤ 2ΔU` (minimum → saddle)**.  Let `U` be
differentiable with continuous gradient `gU` (`DU(y) v = gU(y) ⬝ᵥ v`), and let `ψ` be a solution
of the **reversed** gradient flow `ψ̇ = +∇U(ψ)` on all of `ℝ` with `ψ(s) → x_𝒜` as `s → −∞` and
`ψ(s) → x` as `s → +∞` (a heteroclinic orbit from the minimum `x_𝒜` to the saddle `x`, traversed
uphill).  Then `V_qp(x) ≤ 2 (U(x) − U(x_𝒜))`.  The orbit takes infinite time at both ends, so the
infimum is approached, not attained: for each `δ > 0` the path that leaves `x_𝒜` along a smooth
`[0, 1]` correction, follows `ψ`, and joins `x` along a second smooth correction has action
`≤ 2ΔU + δ` (`quasiPotential_le_of_window`). -/
@[powerlib_foundation] theorem quasiPotential_le_of_heteroclinic {U : (Fin n → ℝ) → ℝ}
    {gU : (Fin n → ℝ) → Fin n → ℝ} (hU : Differentiable ℝ U)
    (hgrad : ∀ y v, fderiv ℝ U y v = gU y ⬝ᵥ v) (hgc : Continuous gU)
    {ψ : ℝ → Fin n → ℝ} (hψ : ∀ s, HasDerivAt ψ (gU (ψ s)) s) {xA x : Fin n → ℝ}
    (hA : Tendsto ψ atBot (𝓝 xA)) (hx : Tendsto ψ atTop (𝓝 x)) :
    quasiPotential U gU xA x ≤ ENNReal.ofReal (2 * (U x - U xA)) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_smoothTransition
  -- it suffices to reach `2ΔU + δ` for every `δ > 0`
  have key : ∀ δ : ℝ, 0 < δ →
      quasiPotential U gU xA x ≤ ENNReal.ofReal (2 * (U x - U xA) + δ) := by
    intro δ hδ
    set K : ℝ := ((n : ℝ) + 1) * (2 + M) ^ 2 with hK
    have hKpos : 0 < K := by positivity
    set η : ℝ := min 1 (δ / K) with hη
    have hηpos : 0 < η := lt_min one_pos (div_pos hδ hKpos)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηK : η ≤ δ / K := min_le_right _ _
    obtain ⟨ρ₁, hρ₁, hc₁⟩ := Metric.continuous_iff.mp hgc xA η hηpos
    obtain ⟨ρ₂, hρ₂, hc₂⟩ := Metric.continuous_iff.mp hgc x η hηpos
    obtain ⟨a₀, ha₀⟩ := eventually_atBot.mp
      ((Metric.tendsto_nhds.mp hA) (min (ρ₁ / 2) η) (lt_min (by linarith) hηpos))
    obtain ⟨b₀, hb₀⟩ := eventually_atTop.mp
      ((Metric.tendsto_nhds.mp hx) (min (ρ₂ / 2) η) (lt_min (by linarith) hηpos))
    set a := a₀ - 1 with ha
    set T := max 2 (b₀ - a + 1) with hTdef
    have hT2 : 2 ≤ T := le_max_left _ _
    have hTb : b₀ - a + 1 ≤ T := le_max_right _ _
    have hσ01 : ∀ t, 0 ≤ Real.smoothTransition t ∧ Real.smoothTransition t ≤ 1 :=
      fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
    -- window estimate near an endpoint `p` of the orbit
    have window : ∀ (p : Fin n → ℝ) (ρ : ℝ), (∀ y, dist y p < ρ → dist (gU y) (gU p) < η) →
        ∀ (z e : Fin n → ℝ) (θ d : ℝ), dist z p < min (ρ / 2) η → ‖e‖ < min (ρ / 2) η →
        0 ≤ θ → θ ≤ 1 → |d| ≤ M → ‖gU z - gU (z + θ • e) + d • e‖ ≤ (2 + M) * η := by
      intro p ρ hc z e θ d hz he hθ0 hθ1 hd
      have hz1 : dist z p < ρ / 2 := hz.trans_le (min_le_left _ _)
      have he1 : ‖e‖ < ρ / 2 := he.trans_le (min_le_left _ _)
      have he2 : ‖e‖ ≤ η := he.le.trans (min_le_right _ _)
      have hy : dist (z + θ • e) p < ρ := by
        rw [dist_eq_norm] at hz1 ⊢
        calc ‖z + θ • e - p‖ = ‖(z - p) + θ • e‖ := by congr 1; abel
          _ ≤ ‖z - p‖ + ‖θ • e‖ := norm_add_le _ _
          _ = ‖z - p‖ + |θ| * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ ‖z - p‖ + 1 * ‖e‖ := by
              gcongr; rw [abs_of_nonneg hθ0]; exact hθ1
          _ < ρ / 2 + 1 * (ρ / 2) := by gcongr
          _ = ρ := by ring
      have g1 := hc z (lt_of_lt_of_le hz1 (by linarith [dist_nonneg (x := z) (y := p)]))
      have g2 := hc _ hy
      rw [dist_eq_norm] at g1 g2
      calc ‖gU z - gU (z + θ • e) + d • e‖
          = ‖(gU z - gU p) - (gU (z + θ • e) - gU p) + d • e‖ := by congr 1; abel
        _ ≤ ‖gU z - gU p‖ + ‖gU (z + θ • e) - gU p‖ + ‖d • e‖ :=
            (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
        _ = ‖gU z - gU p‖ + ‖gU (z + θ • e) - gU p‖ + |d| * ‖e‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ η + η + M * η := by
            gcongr
        _ = (2 + M) * η := by ring
    have h₁ : ∀ t ∈ Icc (0 : ℝ) 1, ‖gU (ψ (a + t)) -
        gU (ψ (a + t) + (1 - Real.smoothTransition t) • (xA - ψ a)) -
        deriv Real.smoothTransition t • (xA - ψ a)‖ ≤ (2 + M) * η := by
      intro t ht
      have e : gU (ψ (a + t)) - gU (ψ (a + t) + (1 - Real.smoothTransition t) • (xA - ψ a)) -
          deriv Real.smoothTransition t • (xA - ψ a) =
          gU (ψ (a + t)) - gU (ψ (a + t) + (1 - Real.smoothTransition t) • (xA - ψ a)) +
          (-deriv Real.smoothTransition t) • (xA - ψ a) := by rw [neg_smul]; abel
      rw [e]
      refine window xA ρ₁ hc₁ _ _ _ _ (ha₀ _ (by linarith [ht.2])) ?_ (by linarith [(hσ01 t).2])
        (by linarith [(hσ01 t).1]) (by rw [abs_neg]; exact hM t)
      rw [← dist_eq_norm, dist_comm]
      exact ha₀ _ (by linarith)
    have h₂ : ∀ t ∈ Icc (T - 1) T, ‖gU (ψ (a + t)) -
        gU (ψ (a + t) + Real.smoothTransition (t - (T - 1)) • (x - ψ (a + T))) +
        deriv Real.smoothTransition (t - (T - 1)) • (x - ψ (a + T))‖ ≤ (2 + M) * η := by
      intro t ht
      refine window x ρ₂ hc₂ _ _ _ _ (hb₀ _ (by linarith [ht.1])) ?_ (hσ01 _).1 (hσ01 _).2
        (hM _)
      rw [← dist_eq_norm, dist_comm]
      exact hb₀ _ (by linarith)
    refine (quasiPotential_le_of_window hU hgrad hgc hψ hT2 h₁ h₂).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have : (n : ℝ) * ((2 + M) * η) ^ 2 ≤ δ := by
      have hη2 : η ^ 2 ≤ η := by nlinarith
      have h1 : (n : ℝ) * ((2 + M) * η) ^ 2 ≤ K * η := by
        rw [hK, mul_pow]
        have : (0 : ℝ) ≤ (2 + M) ^ 2 := by positivity
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have h2 : K * η ≤ δ := by
        have := mul_le_mul_of_nonneg_left hηK hKpos.le
        rwa [mul_div_cancel₀ _ hKpos.ne'] at this
      linarith
    linarith
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  calc quasiPotential U gU xA x ≤ ENNReal.ofReal (2 * (U x - U xA) + ε) := key ε hε
    _ ≤ ENNReal.ofReal (2 * (U x - U xA)) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (2 * (U x - U xA)) + ε := by rw [ENNReal.ofReal_coe_nnreal]

/-- **Gradient systems: `V_qp = 2ΔU` (minimum → saddle)**: with the hypotheses of
`quasiPotential_le_of_heteroclinic`, the quasi-potential equals `2 (U(x) − U(x_𝒜))`
(lower bound `quasiPotential_ge`). -/
@[powerlib_foundation] theorem quasiPotential_eq_of_heteroclinic {U : (Fin n → ℝ) → ℝ}
    {gU : (Fin n → ℝ) → Fin n → ℝ} (hU : Differentiable ℝ U)
    (hgrad : ∀ y v, fderiv ℝ U y v = gU y ⬝ᵥ v) (hgc : Continuous gU)
    {ψ : ℝ → Fin n → ℝ} (hψ : ∀ s, HasDerivAt ψ (gU (ψ s)) s) {xA x : Fin n → ℝ}
    (hA : Tendsto ψ atBot (𝓝 xA)) (hx : Tendsto ψ atTop (𝓝 x)) :
    quasiPotential U gU xA x = ENNReal.ofReal (2 * (U x - U xA)) :=
  le_antisymm (quasiPotential_le_of_heteroclinic hU hgrad hgc hψ hA hx)
    (quasiPotential_ge U gU xA x)

/-! ## Example: the double well `U(y) = y⁴/4 − y²/2` -/

/-- Double-well potential on `ℝ` (as `Fin 1 → ℝ`): minima at `±1`, saddle (local maximum) at `0`. -/
def dwU (y : Fin 1 → ℝ) : ℝ := y 0 ^ 4 / 4 - y 0 ^ 2 / 2

/-- Its gradient `U'(y) = y³ − y`. -/
def dwGrad (y : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => y 0 ^ 3 - y 0

/-- The uphill heteroclinic orbit `ψ(s) = 1/√(1 + e^{2s})` from the minimum `1` (`s → −∞`) to the
saddle `0` (`s → +∞`): `ψ̇ = ψ³ − ψ = U'(ψ)`. -/
def dwOrbit (s : ℝ) : Fin 1 → ℝ := fun _ => (√(1 + exp (2 * s)))⁻¹

private theorem dw_hasFDerivAt (y : Fin 1 → ℝ) :
    HasFDerivAt dwU ((y 0 ^ 3 - y 0) • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 1 => ℝ) 0) y := by
  have hp : HasFDerivAt (fun z : Fin 1 → ℝ => z 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) y := hasFDerivAt_apply 0 y
  have hf : HasDerivAt (fun s : ℝ => s ^ 4 / 4 - s ^ 2 / 2) (y 0 ^ 3 - y 0) (y 0) := by
    have := ((hasDerivAt_pow 4 (y 0)).div_const 4).sub ((hasDerivAt_pow 2 (y 0)).div_const 2)
    convert this using 1; push_cast; ring
  exact hf.comp_hasFDerivAt y hp

private theorem dw_differentiable : Differentiable ℝ dwU := fun y =>
  (dw_hasFDerivAt y).differentiableAt

private theorem dw_grad (y v : Fin 1 → ℝ) : fderiv ℝ dwU y v = dwGrad y ⬝ᵥ v := by
  rw [(dw_hasFDerivAt y).fderiv]
  simp [dwGrad, dotProduct]

private theorem dw_grad_continuous : Continuous dwGrad := by
  unfold dwGrad
  exact continuous_pi fun _ => by fun_prop

private theorem dwOrbit_hasDerivAt (s : ℝ) : HasDerivAt dwOrbit (dwGrad (dwOrbit s)) s := by
  rw [hasDerivAt_pi]
  intro _
  set w := 1 + exp (2 * s) with hw
  have hwpos : 0 < w := by positivity
  have h2s : HasDerivAt (fun t : ℝ => 2 * t) 2 s := by
    simpa using (hasDerivAt_id s).const_mul 2
  have h1 : HasDerivAt (fun t => 1 + exp (2 * t)) (exp (2 * s) * 2) s := h2s.exp.const_add 1
  have hsq := h1.sqrt hwpos.ne'
  have hsw : 0 < √w := Real.sqrt_pos.mpr hwpos
  have hinv := hsq.inv hsw.ne'
  refine hinv.congr_deriv ?_
  simp only [dwGrad, dwOrbit]
  have hw2 : √w ^ 2 = w := Real.sq_sqrt hwpos.le
  rw [← hw]
  field_simp
  rw [hw2, hw]
  ring

private theorem dwOrbit_atBot : Tendsto dwOrbit atBot (𝓝 (fun _ => 1)) := by
  rw [tendsto_pi_nhds]
  intro _
  have h1 : Tendsto (fun s : ℝ => 1 + exp (2 * s)) atBot (𝓝 1) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by norm_num : (0:ℝ) < 2)))
    simpa using this.const_add 1
  have h2 := (h1.sqrt).inv₀ (by simp)
  simpa [dwOrbit] using h2

private theorem dwOrbit_atTop : Tendsto dwOrbit atTop (𝓝 (fun _ => 0)) := by
  rw [tendsto_pi_nhds]
  intro _
  have h1 : Tendsto (fun s : ℝ => 1 + exp (2 * s)) atTop atTop := by
    have := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
    exact tendsto_atTop_add_const_left _ 1 this
  exact (Real.tendsto_sqrt_atTop.comp h1).inv_tendsto_atTop

/-- **Non-vacuity of `quasiPotential_eq_of_heteroclinic`**: for the double well
`U(y) = y⁴/4 − y²/2`, the quasi-potential from the minimum `1` to the saddle `0` is
`2 (U(0) − U(1)) = 1/2`. -/
@[powerlib_foundation] theorem doubleWell_quasiPotential :
    quasiPotential dwU dwGrad (fun _ => 1) (fun _ => 0) = ENNReal.ofReal (1 / 2) := by
  rw [quasiPotential_eq_of_heteroclinic dw_differentiable dw_grad dw_grad_continuous
    dwOrbit_hasDerivAt dwOrbit_atBot dwOrbit_atTop]
  congr 1
  simp [dwU]
  norm_num

/-! ## Cramér lower bound at exposed points -/

section Cramer

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Identically distributed summands have the same exponential integrability. -/
private theorem integrable_exp_iff_of_identDistrib (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (i : ℕ) (t : ℝ) :
    Integrable (fun ω => exp (t * X i ω)) μ ↔ Integrable (fun ω => exp (t * X 0 ω)) μ :=
  ((hid i).comp (measurable_const_mul t).exp).integrable_iff

private theorem mgf_eq_of_identDistrib (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) (i : ℕ)
    (t : ℝ) : mgf (X i) μ t = mgf (X 0) μ t :=
  ((hid i).comp (measurable_const_mul t).exp).integral_eq

private theorem mgf_sum_eq [IsProbabilityMeasure μ] (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) (t : ℝ) :
    mgf (∑ i ∈ Finset.range n, X i) μ t = mgf (X 0) μ t ^ n := by
  rw [hindep.mgf_sum hmeas, Finset.prod_congr rfl fun i _ => mgf_eq_of_identDistrib hid i t,
    Finset.prod_const, Finset.card_range]

private theorem cgf_sum_eq [IsProbabilityMeasure μ] (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    cgf (∑ i ∈ Finset.range n, X i) μ = fun t => n * cgf (X 0) μ t := by
  funext t
  rw [cgf, mgf_sum_eq hindep hmeas hid, Real.log_pow, cgf]

private theorem interior_subset_sum [IsProbabilityMeasure μ] (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    interior (integrableExpSet (X 0) μ) ⊆
      interior (integrableExpSet (∑ i ∈ Finset.range n, X i) μ) := by
  refine interior_mono fun t ht => ?_
  exact hindep.integrable_exp_mul_sum hmeas fun i _ =>
    (integrable_exp_iff_of_identDistrib hid i t).mpr ht

/-- `(Y − c)² e^{θY}` is integrable for `θ` in the interior of the exponential-integrability set. -/
private theorem integrable_sq_mul_exp {Y : Ω → ℝ} {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet Y μ)) (c : ℝ) :
    Integrable (fun ω => (Y ω - c) ^ 2 * exp (θ * Y ω)) μ := by
  have h2 := integrable_pow_mul_exp_of_mem_interior_integrableExpSet hθ 2
  have h1 := integrable_pow_mul_exp_of_mem_interior_integrableExpSet hθ 1
  have h0 := integrable_pow_mul_exp_of_mem_interior_integrableExpSet hθ 0
  refine ((h2.sub (h1.const_mul (2 * c))).add (h0.const_mul (c ^ 2))).congr
    (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, pow_one, pow_zero, one_mul]
  ring

/-- Tilted second moment of the sum: `E[(S_n − n Λ'(θ))² e^{θ S_n}] = n Λ''(θ) M(θ)ⁿ`. -/
private theorem tilted_second_moment [IsProbabilityMeasure μ] (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet (X 0) μ)) :
    ∫ ω, ((∑ i ∈ Finset.range n, X i) ω - n * deriv (cgf (X 0) μ) θ) ^ 2 *
        exp (θ * (∑ i ∈ Finset.range n, X i) ω) ∂μ =
      n * iteratedDeriv 2 (cgf (X 0) μ) θ * mgf (X 0) μ θ ^ n := by
  have hθS := interior_subset_sum hindep hmeas hid n hθ
  have h := iteratedDeriv_two_cgf_eq_integral hθS
  have hc := cgf_sum_eq hindep hmeas hid n
  have hd : deriv (cgf (∑ i ∈ Finset.range n, X i) μ) θ = n * deriv (cgf (X 0) μ) θ := by
    rw [hc, deriv_const_mul_field']
  have hdd : iteratedDeriv 2 (cgf (∑ i ∈ Finset.range n, X i) μ) θ =
      n * iteratedDeriv 2 (cgf (X 0) μ) θ := by
    rw [hc, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one,
      deriv_const_mul_field', deriv_const_mul_field']
  rw [hdd, hd, mgf_sum_eq hindep hmeas hid] at h
  have hM : 0 < mgf (X 0) μ θ ^ n :=
    pow_pos (mgf_pos (interior_subset (s := integrableExpSet (X 0) μ) hθ)) n
  exact ((eq_div_iff hM.ne').mp h).symm

/-- **Finite-`n` estimate** (exponential tilting + Chebyshev under the tilted law): with
`x = Λ'(θ)`, `v = Λ''(θ)`,
`P(|S_n − n x| < n δ) ≥ e^{−n(θ x + |θ| δ)} M(θ)ⁿ (1 − v/(n δ²))`. -/
private theorem cramer_core [IsProbabilityMeasure μ] (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet (X 0) μ)) {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    exp (-(n * (θ * deriv (cgf (X 0) μ) θ + |θ| * δ))) * mgf (X 0) μ θ ^ n *
        (1 - iteratedDeriv 2 (cgf (X 0) μ) θ / δ ^ 2 / n) ≤
      μ.real {ω | |(∑ i ∈ Finset.range n, X i) ω - n * deriv (cgf (X 0) μ) θ| < n * δ} := by
  set S := ∑ i ∈ Finset.range n, X i with hSdef
  set x := deriv (cgf (X 0) μ) θ with hx
  set v := iteratedDeriv 2 (cgf (X 0) μ) θ with hv
  set M := mgf (X 0) μ θ with hMdef
  set A := {ω | |S ω - n * x| < n * δ} with hAdef
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnδ : 0 < (n : ℝ) * δ := mul_pos hn' hδ
  have hθS := interior_subset_sum hindep hmeas hid n hθ
  have hSm : Measurable S := by
    have : Measurable fun ω => ∑ i ∈ Finset.range n, X i ω :=
      Finset.measurable_sum _ fun i _ => hmeas i
    convert this using 1
    ext ω; simp [hSdef, Finset.sum_apply]
  have hA : MeasurableSet A :=
    measurableSet_lt (continuous_abs.measurable.comp (hSm.sub_const _)) measurable_const
  have hexpS : Integrable (fun ω => exp (θ * S ω)) μ :=
    interior_subset (s := integrableExpSet S μ) hθS
  set K := exp (n * (θ * x + |θ| * δ)) with hK
  have hpt : ∀ ω, exp (θ * S ω) ≤
      K * A.indicator 1 ω + 1 / (n * δ) ^ 2 * ((S ω - n * x) ^ 2 * exp (θ * S ω)) := by
    intro ω
    have hq0 : 0 ≤ 1 / (n * δ) ^ 2 * ((S ω - n * x) ^ 2 * exp (θ * S ω)) := by positivity
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have hlt : |S ω - n * x| < n * δ := hω
      have h0 : |θ| * |S ω - n * x| ≤ |θ| * (n * δ) :=
        mul_le_mul_of_nonneg_left hlt.le (abs_nonneg θ)
      have h1 : θ * (S ω - n * x) ≤ |θ| * (n * δ) := by
        refine (le_abs_self _).trans ?_
        rw [abs_mul]; exact h0
      have : θ * S ω ≤ n * (θ * x + |θ| * δ) := by linarith
      have := exp_le_exp.mpr this
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, zero_add]
      have hge : n * δ ≤ |S ω - n * x| := not_lt.mp hω
      have hsq : (n * δ) ^ 2 ≤ (S ω - n * x) ^ 2 := by
        rw [← sq_abs (S ω - n * x)]; exact pow_le_pow_left₀ hnδ.le hge 2
      have hratio : 1 ≤ 1 / (n * δ) ^ 2 * (S ω - n * x) ^ 2 := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]; linarith
      have he := (exp_pos (θ * S ω)).le
      nlinarith
  have hint1 : Integrable (fun ω => K * A.indicator 1 ω) μ :=
    ((integrable_indicator_iff hA).mpr (integrable_const (1 : ℝ)).integrableOn).const_mul K
  have hint2 : Integrable (fun ω => 1 / (n * δ) ^ 2 * ((S ω - n * x) ^ 2 * exp (θ * S ω))) μ :=
    (integrable_sq_mul_exp (Y := S) hθS (n * x)).const_mul _
  have hint : ∫ ω, exp (θ * S ω) ∂μ ≤
      ∫ ω, (K * A.indicator 1 ω + 1 / (n * δ) ^ 2 * ((S ω - n * x) ^ 2 * exp (θ * S ω))) ∂μ :=
    integral_mono hexpS (hint1.add hint2) hpt
  rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul,
    integral_indicator_one hA] at hint
  have hmom := tilted_second_moment hindep hmeas hid n hθ
  rw [← hSdef] at hmom
  rw [hmom] at hint
  have hmgf : ∫ ω, exp (θ * S ω) ∂μ = M ^ n := by
    rw [← mgf_sum_eq hindep hmeas hid n θ, hSdef]; rfl
  rw [hmgf] at hint
  -- `Mⁿ ≤ K P(A) + n v Mⁿ / (n δ)²`
  have hKpos : 0 < K := exp_pos _
  have hKinv : exp (-(n * (θ * x + |θ| * δ))) = K⁻¹ := by rw [hK, exp_neg]
  rw [hKinv]
  have e : K⁻¹ * M ^ n * (1 - v / δ ^ 2 / n) =
      K⁻¹ * (M ^ n - 1 / (n * δ) ^ 2 * (n * v * M ^ n)) := by
    field_simp
  rw [e]
  calc K⁻¹ * (M ^ n - 1 / (n * δ) ^ 2 * (n * v * M ^ n)) ≤ K⁻¹ * (K * μ.real A) := by
        gcongr; linarith
    _ = μ.real A := by field_simp

/-- **Cramér lower bound at an exposed point, quantitative form.**  Let `X₀, X₁, …` be i.i.d.
real random variables, `Λ = cgf X₀` their cumulant generating function, `θ` an interior point of
the effective domain of `Λ` and `x = Λ'(θ)` (the mean of the law tilted by `e^{θX}`).  If `x`
lies in the open set `G`, then for every `ε > 0`, eventually
`P(S_n / n ∈ G) > 0` and `(1/n) log P(S_n / n ∈ G) ≥ −(θ x − Λ(θ)) − ε`. -/
@[powerlib_foundation] theorem cramer_lower_exposed [IsProbabilityMeasure μ]
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet (X 0) μ)) {G : Set ℝ} (hG : IsOpen G)
    (hxG : deriv (cgf (X 0) μ) θ ∈ G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 0 < μ.real {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G} ∧
      -(θ * deriv (cgf (X 0) μ) θ - cgf (X 0) μ θ) - ε ≤
        (n : ℝ)⁻¹ * Real.log (μ.real {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G}) := by
  set x := deriv (cgf (X 0) μ) θ with hx
  set v := iteratedDeriv 2 (cgf (X 0) μ) θ with hv
  set M := mgf (X 0) μ θ with hMdef
  set Λ := cgf (X 0) μ θ with hΛ
  have hM : 0 < M := mgf_pos (interior_subset (s := integrableExpSet (X 0) μ) hθ)
  have hMΛ : M = exp Λ := by rw [hΛ, cgf, exp_log hM]
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hG x hxG
  set δ := min (ρ / 2) (ε / (2 * (|θ| + 1))) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  have hθδ : |θ| * δ ≤ ε / 2 := by
    have h1 : δ ≤ ε / (2 * (|θ| + 1)) := min_le_right _ _
    have h2 : |θ| * δ ≤ |θ| * (ε / (2 * (|θ| + 1))) := mul_le_mul_of_nonneg_left h1 (abs_nonneg θ)
    have h3 : |θ| * (ε / (2 * (|θ| + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg θ]
    linarith
  have hv0 := tendsto_const_div_atTop_nhds_zero_nat (v / δ ^ 2)
  have hl0 := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  filter_upwards [eventually_ge_atTop 1, (tendsto_order.1 hv0).2 (1 / 2) (by norm_num),
    (tendsto_order.1 hl0).2 (ε / 2) (by linarith)] with n hn1 hvn hln
  have hn : 0 < n := hn1
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcore := cramer_core hindep hmeas hid hθ hn hδ
  rw [← hx, ← hv, ← hMdef] at hcore
  -- the window event is contained in `{S_n / n ∈ G}`
  have hsub : {ω | |(∑ i ∈ Finset.range n, X i) ω - n * x| < n * δ} ⊆
      {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Finset.sum_apply] at hω ⊢
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have : (∑ i ∈ Finset.range n, X i ω) / n - x = ((∑ i ∈ Finset.range n, X i ω) - n * x) / n := by
      field_simp
    rw [this, abs_div, abs_of_pos hn', div_lt_iff₀ hn']
    calc |∑ i ∈ Finset.range n, X i ω - n * x| < n * δ := hω
      _ ≤ ρ * n := by
          have : δ ≤ ρ / 2 := min_le_left _ _
          nlinarith
  have hmono := measureReal_mono (μ := μ) hsub
  -- lower bound on the probability
  set p := μ.real {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G} with hp
  have hlow : 1 / 2 * exp (-(n * (θ * x + |θ| * δ - Λ))) ≤ p := by
    refine le_trans ?_ (hcore.trans hmono)
    rw [hMΛ, ← exp_nat_mul]
    have he : exp (-(n * (θ * x + |θ| * δ))) * exp (n * Λ) =
        exp (-(n * (θ * x + |θ| * δ - Λ))) := by rw [← exp_add]; ring_nf
    rw [he]
    have : (1 : ℝ) / 2 ≤ 1 - v / δ ^ 2 / n := by linarith
    have hep := (exp_pos (-(n * (θ * x + |θ| * δ - Λ)))).le
    nlinarith
  have hpos : 0 < 1 / 2 * exp (-(n * (θ * x + |θ| * δ - Λ))) := by positivity
  have hlog : Real.log (1 / 2 * exp (-(n * (θ * x + |θ| * δ - Λ)))) ≤ Real.log p :=
    Real.log_le_log hpos hlow
  rw [Real.log_mul (by norm_num) (exp_pos _).ne', Real.log_exp, one_div, Real.log_inv] at hlog
  -- divide by `n`
  have hdiv : (n : ℝ)⁻¹ * (-Real.log 2 + -(n * (θ * x + |θ| * δ - Λ))) ≤ (n : ℝ)⁻¹ * Real.log p :=
    mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hn'.le)
  have e : (n : ℝ)⁻¹ * (-Real.log 2 + -(n * (θ * x + |θ| * δ - Λ))) =
      -(θ * x - Λ) - |θ| * δ - Real.log 2 / n := by
    field_simp; ring
  rw [e] at hdiv
  exact ⟨hpos.trans_le hlow, by linarith⟩

/-- **Cramér rate function**: the Legendre transform of the cumulant generating function over its
effective domain, `I(x) = sup_{t : E e^{tY} < ∞} (t x − Λ(t))` (`EReal`-valued). -/
def cramerRate {Ω : Type*} {mΩ : MeasurableSpace Ω} (Y : Ω → ℝ) (μ : Measure Ω) (x : ℝ) :
    EReal :=
  ⨆ t ∈ integrableExpSet Y μ, ((t * x - cgf Y μ t : ℝ) : EReal)

/-- **Tangent-line inequality** for the cumulant generating function at an interior point:
`Λ(t) ≥ Λ(θ) + (t − θ) Λ'(θ)` on the effective domain (`e^y ≥ 1 + y` under the tilted law). -/
@[powerlib_foundation] theorem cgf_tangent_le [IsProbabilityMeasure μ] {Y : Ω → ℝ} {θ t : ℝ}
    (hθ : θ ∈ interior (integrableExpSet Y μ)) (ht : t ∈ integrableExpSet Y μ) :
    cgf Y μ θ + (t - θ) * deriv (cgf Y μ) θ ≤ cgf Y μ t := by
  have hθi : Integrable (fun ω => exp (θ * Y ω)) μ :=
    interior_subset (s := integrableExpSet Y μ) hθ
  have hti : Integrable (fun ω => exp (t * Y ω)) μ := ht
  have h1 : Integrable (fun ω => Y ω * exp (θ * Y ω)) μ := by
    simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet hθ 1
  have hM : 0 < mgf Y μ θ := mgf_pos hθi
  set x := deriv (cgf Y μ) θ with hx
  have hxM : ∫ ω, Y ω * exp (θ * Y ω) ∂μ = x * mgf Y μ θ := by
    rw [hx, deriv_cgf hθ, div_mul_cancel₀ _ hM.ne']
  -- pointwise: `e^{tY} ≥ e^{(t−θ)x} e^{θY} (1 + (t − θ)(Y − x))`
  have hpt : ∀ ω, exp ((t - θ) * x) * (exp (θ * Y ω) + (t - θ) * (Y ω * exp (θ * Y ω)) -
      (t - θ) * x * exp (θ * Y ω)) ≤ exp (t * Y ω) := by
    intro ω
    have h := Real.add_one_le_exp ((t - θ) * (Y ω - x))
    have e : exp (t * Y ω) = exp ((t - θ) * x) * exp (θ * Y ω) * exp ((t - θ) * (Y ω - x)) := by
      rw [← exp_add, ← exp_add]; ring_nf
    rw [e]
    have hp : 0 ≤ exp ((t - θ) * x) * exp (θ * Y ω) := by positivity
    have := mul_le_mul_of_nonneg_left h hp
    nlinarith [this]
  have hlhs : Integrable (fun ω => exp ((t - θ) * x) * (exp (θ * Y ω) +
      (t - θ) * (Y ω * exp (θ * Y ω)) - (t - θ) * x * exp (θ * Y ω))) μ :=
    ((hθi.add (h1.const_mul _)).sub (hθi.const_mul _)).const_mul _
  have hint := integral_mono hlhs hti hpt
  have hA1 : Integrable (fun ω => exp (θ * Y ω) + (t - θ) * (Y ω * exp (θ * Y ω))) μ :=
    hθi.add (h1.const_mul _)
  have hA2 : Integrable (fun ω => (t - θ) * x * exp (θ * Y ω)) μ := hθi.const_mul _
  rw [integral_const_mul, integral_sub hA1 hA2, integral_add hθi (h1.const_mul _),
    integral_const_mul, integral_const_mul, hxM] at hint
  have hMt : exp ((t - θ) * x) * mgf Y μ θ ≤ mgf Y μ t := by
    have e : exp ((t - θ) * x) * (∫ ω, exp (θ * Y ω) ∂μ + (t - θ) * (x * mgf Y μ θ) -
        (t - θ) * x * ∫ ω, exp (θ * Y ω) ∂μ) = exp ((t - θ) * x) * mgf Y μ θ := by
      rw [show ∫ ω, exp (θ * Y ω) ∂μ = mgf Y μ θ from rfl]; ring
    rw [e] at hint
    exact hint
  have hlog := Real.log_le_log (by positivity) hMt
  rw [Real.log_mul (exp_pos _).ne' hM.ne', Real.log_exp] at hlog
  rw [cgf, cgf]
  linarith

/-- **The rate function at an exposed point**: if `θ` is interior to the effective domain and
`x = Λ'(θ)`, the Legendre supremum is attained at `θ`: `I(x) = θ x − Λ(θ)`. -/
@[powerlib_foundation] theorem cramerRate_eq [IsProbabilityMeasure μ] {Y : Ω → ℝ} {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet Y μ)) :
    cramerRate Y μ (deriv (cgf Y μ) θ) =
      ((θ * deriv (cgf Y μ) θ - cgf Y μ θ : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup₂_le fun t ht => ?_
    have := cgf_tangent_le hθ ht
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  · exact le_iSup₂_of_le (f := fun t (_ : t ∈ integrableExpSet Y μ) =>
      ((t * deriv (cgf Y μ) θ - cgf Y μ t : ℝ) : EReal)) θ
      (interior_subset (s := integrableExpSet Y μ) hθ) le_rfl

private theorem ereal_le_of_forall_sub_le {a : ℝ} {ℓ : EReal}
    (h : ∀ ε : ℝ, 0 < ε → ((a - ε : ℝ) : EReal) ≤ ℓ) : (a : EReal) ≤ ℓ := by
  induction ℓ using EReal.rec with
  | bot => exact absurd (h 1 one_pos) (by rw [le_bot_iff]; exact EReal.coe_ne_bot _)
  | coe r =>
    rw [EReal.coe_le_coe_iff]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := EReal.coe_le_coe_iff.mp (h ε hε)
    linarith
  | top => exact le_top

/-- **Cramér lower bound (exposed points), large-deviation form.**  For i.i.d. real `Xᵢ` and an
open set `G`,
`−inf {I(x) : x ∈ G exposed} ≤ liminf_{n → ∞} (1/n) log P(S_n / n ∈ G)`,
where `I` is the Legendre transform `cramerRate` of the cumulant generating function and the
exposed points are `x = Λ'(θ)` with `θ` interior to the effective domain of `Λ`. -/
@[powerlib_foundation] theorem cramer_lower_bound [IsProbabilityMeasure μ]
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {G : Set ℝ} (hG : IsOpen G) :
    (⨆ θ ∈ interior (integrableExpSet (X 0) μ), ⨆ (_ : deriv (cgf (X 0) μ) θ ∈ G),
        -cramerRate (X 0) μ (deriv (cgf (X 0) μ) θ)) ≤
      liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G})) atTop := by
  refine iSup₂_le fun θ hθ => iSup_le fun hxG => ?_
  rw [cramerRate_eq hθ, ← EReal.coe_neg]
  apply ereal_le_of_forall_sub_le
  intro ε hε
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [cramer_lower_exposed hindep hmeas hid hθ hG hxG hε] with n hn
  obtain ⟨hpos, hb⟩ := hn
  have hne : μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G} ≠ 0 := by
    intro h0
    rw [measureReal_def, h0, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  rw [ENNReal.log_pos_real hne (measure_ne_top _ _), ← EReal.coe_mul, EReal.coe_le_coe_iff]
  rw [measureReal_def] at hb
  linarith

/-- A bounded random variable has all exponential moments. -/
private theorem integrableExpSet_eq_univ [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    {C : ℝ} (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ C) : integrableExpSet Y μ = univ := by
  ext t
  simp only [mem_univ, iff_true]
  refine Integrable.of_bound (((hY.const_mul t).exp).aestronglyMeasurable) (exp (|t| * C)) ?_
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr
  calc t * Y ω ≤ |t * Y ω| := le_abs_self _
    _ = |t| * |Y ω| := abs_mul _ _
    _ ≤ |t| * C := mul_le_mul_of_nonneg_left hω (abs_nonneg t)

/-- If `P(Y > x) > 0`, the tilted mean exceeds `x` for some tilt: `E[(Y − x) e^{θY}] ≥ 0`. -/
private theorem exists_tilt_ge [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    {C : ℝ} (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ C) {x : ℝ} (hx : 0 < μ {ω | x < Y ω}) :
    ∃ θ, 0 ≤ ∫ ω, (Y ω - x) * exp (θ * Y ω) ∂μ := by
  -- a level `c > x` with `P(Y > c) > 0`
  have hU : {ω | x < Y ω} = ⋃ k : ℕ, {ω | x + 1 / ((k : ℝ) + 1) < Y ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < μ {ω | x + 1 / ((k : ℝ) + 1) < Y ω} := by
    by_contra h
    push Not at h
    have : μ {ω | x < Y ω} = 0 := by
      rw [hU]; exact measure_iUnion_null fun k => nonpos_iff_eq_zero.mp (h k)
    exact absurd this hx.ne'
  set c := x + 1 / ((k : ℝ) + 1) with hc
  have hcx : 0 < c - x := by rw [hc]; simp only [add_sub_cancel_left]; positivity
  set p := μ.real {ω | c < Y ω} with hp
  have hppos : 0 < p := by
    rw [hp, measureReal_def]
    exact ENNReal.toReal_pos hk.ne' (measure_ne_top _ _)
  set D := C + |x| with hD
  -- choose `θ ≥ 0` with `(c − x) p e^{θ(c − x)} ≥ D + 1`
  set θ := max 0 (Real.log ((D + 1) / ((c - x) * p)) / (c - x)) with hθ
  have hθ0 : 0 ≤ θ := le_max_left _ _
  have hD0 : 0 ≤ D := by
    obtain ⟨ω, hω⟩ := hb.exists
    rw [hD]; linarith [abs_nonneg (Y ω), abs_nonneg x]
  have hkey : D + 1 ≤ (c - x) * p * exp (θ * (c - x)) := by
    have hpos : 0 < (c - x) * p := mul_pos hcx hppos
    have h1 : Real.log ((D + 1) / ((c - x) * p)) ≤ θ * (c - x) := by
      have := le_max_right 0 (Real.log ((D + 1) / ((c - x) * p)) / (c - x))
      rw [← hθ] at this
      rwa [div_le_iff₀ hcx] at this
    have h2 := exp_le_exp.mpr h1
    rw [exp_log (by positivity)] at h2
    rw [div_le_iff₀ hpos] at h2
    linarith
  refine ⟨θ, ?_⟩
  have hint1 : Integrable (fun ω => (Y ω - x) * exp (θ * Y ω)) μ := by
    refine Integrable.of_bound
      ((hY.sub_const x).mul (hY.const_mul θ).exp).aestronglyMeasurable
      ((C + |x|) * exp (|θ| * C)) ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    refine mul_le_mul ?_ ?_ (exp_pos _).le (by positivity)
    · calc |Y ω - x| ≤ |Y ω| + |x| := abs_sub _ _
        _ ≤ C + |x| := by linarith
    · apply exp_le_exp.mpr
      calc θ * Y ω ≤ |θ * Y ω| := le_abs_self _
        _ = |θ| * |Y ω| := abs_mul _ _
        _ ≤ |θ| * C := mul_le_mul_of_nonneg_left hω (abs_nonneg θ)
  have hmeasA : MeasurableSet {ω | c < Y ω} := measurableSet_lt measurable_const hY
  -- pointwise lower bound
  have hpt : ∀ᵐ ω ∂μ, -(D * exp (θ * x)) + (c - x) * exp (θ * c) *
      ({ω | c < Y ω}.indicator 1 ω) ≤ (Y ω - x) * exp (θ * Y ω) := by
    filter_upwards [hb] with ω hω
    by_cases hω1 : c < Y ω
    · rw [indicator_of_mem (show ω ∈ {ω | c < Y ω} from hω1), Pi.one_apply, mul_one]
      have h1 : (c - x) * exp (θ * c) ≤ (Y ω - x) * exp (θ * Y ω) :=
        mul_le_mul (by linarith) (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω1.le hθ0))
          (exp_pos _).le (by linarith)
      have : 0 ≤ D * exp (θ * x) := mul_nonneg hD0 (exp_pos _).le
      linarith
    · rw [indicator_of_notMem (show ω ∉ {ω | c < Y ω} from hω1), mul_zero, add_zero]
      by_cases hω2 : x < Y ω
      · have : 0 ≤ (Y ω - x) * exp (θ * Y ω) := mul_nonneg (by linarith) (exp_pos _).le
        have : 0 ≤ D * exp (θ * x) := mul_nonneg hD0 (exp_pos _).le
        linarith
      · have hYx : Y ω ≤ x := not_lt.mp hω2
        have he : exp (θ * Y ω) ≤ exp (θ * x) := exp_le_exp.mpr (mul_le_mul_of_nonneg_left hYx hθ0)
        have hlow : -D ≤ Y ω - x := by
          rw [hD]
          have := neg_abs_le (Y ω)
          have := le_abs_self x
          linarith [abs_le.mp hω]
        have : -(D * exp (θ * x)) ≤ (Y ω - x) * exp (θ * x) := by nlinarith [exp_pos (θ * x)]
        have : (Y ω - x) * exp (θ * x) ≤ (Y ω - x) * exp (θ * Y ω) :=
          mul_le_mul_of_nonpos_left he (by linarith)
        linarith
  have hI : Integrable (fun ω => {ω | c < Y ω}.indicator (1 : Ω → ℝ) ω) μ :=
    (integrable_indicator_iff hmeasA).mpr (integrable_const (1 : ℝ)).integrableOn
  have hI2 : Integrable (fun ω => (c - x) * exp (θ * c) * {ω | c < Y ω}.indicator (1 : Ω → ℝ) ω)
      μ := hI.const_mul _
  have hint2 : Integrable (fun ω => -(D * exp (θ * x)) + (c - x) * exp (θ * c) *
      ({ω | c < Y ω}.indicator 1 ω)) μ := (integrable_const _).add hI2
  have hmono := integral_mono_ae hint2 hint1 hpt
  rw [integral_add (integrable_const _) hI2, integral_const, integral_const_mul,
    integral_indicator_one hmeasA] at hmono
  simp only [probReal_univ, smul_eq_mul] at hmono
  rw [← hp] at hmono
  have : D * exp (θ * x) ≤ (c - x) * exp (θ * c) * p := by
    have e : exp (θ * c) = exp (θ * x) * exp (θ * (c - x)) := by rw [← exp_add]; ring_nf
    rw [e]
    have hex := exp_pos (θ * x)
    nlinarith [hkey]
  linarith

/-- **Interior points of the support of a bounded variable are exposed**: if `|Y| ≤ C` a.s.,
`P(Y < x) > 0` and `P(Y > x) > 0`, then `x = Λ'(θ)` for some `θ` (interior to the effective
domain, which is all of `ℝ`).  (Intermediate value theorem for the continuous `Λ'`.) -/
@[powerlib_foundation] theorem exists_deriv_cgf_eq [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Measurable Y) {C : ℝ} (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ C) {x : ℝ}
    (hlo : 0 < μ {ω | Y ω < x}) (hhi : 0 < μ {ω | x < Y ω}) :
    ∃ θ, θ ∈ interior (integrableExpSet Y μ) ∧ deriv (cgf Y μ) θ = x := by
  have huniv := integrableExpSet_eq_univ hY.aemeasurable hb
  have hint : ∀ θ, θ ∈ interior (integrableExpSet Y μ) := fun θ => by
    rw [huniv, interior_univ]; trivial
  have hcont : Continuous (deriv (cgf Y μ)) := by
    have h := (analyticOnNhd_cgf (X := Y) (μ := μ)).deriv
    rw [huniv, interior_univ] at h
    exact continuous_iff_continuousAt.mpr fun θ => (h θ (mem_univ θ)).continuousAt
  -- `Λ'(θ) − x = E[(Y − x) e^{θY}] / M(θ)`
  have hrel : ∀ θ, deriv (cgf Y μ) θ - x =
      (∫ ω, (Y ω - x) * exp (θ * Y ω) ∂μ) / mgf Y μ θ := by
    intro θ
    have h0 : Integrable (fun ω => exp (θ * Y ω)) μ :=
      interior_subset (s := integrableExpSet Y μ) (hint θ)
    have hM : 0 < mgf Y μ θ := mgf_pos h0
    have h1 : Integrable (fun ω => Y ω * exp (θ * Y ω)) μ := by
      simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet (hint θ) 1
    have e : ∫ ω, (Y ω - x) * exp (θ * Y ω) ∂μ =
        ∫ ω, Y ω * exp (θ * Y ω) ∂μ - x * mgf Y μ θ := by
      have : (fun ω => (Y ω - x) * exp (θ * Y ω)) =
          fun ω => Y ω * exp (θ * Y ω) - x * exp (θ * Y ω) := by funext ω; ring
      rw [this, integral_sub h1 (h0.const_mul x), integral_const_mul]
      rfl
    rw [deriv_cgf (hint θ), e, sub_div, mul_div_cancel_right₀ x hM.ne']
  obtain ⟨θ₁, hθ₁⟩ := exists_tilt_ge hY hb hhi
  have hb' : ∀ᵐ ω ∂μ, |(-Y) ω| ≤ C := by
    filter_upwards [hb] with ω hω; simpa using hω
  obtain ⟨θ₀', hθ₀'⟩ := exists_tilt_ge (Y := -Y) (x := -x) hY.neg hb' (by simpa using hlo)
  have hge : x ≤ deriv (cgf Y μ) θ₁ := by
    have := hrel θ₁
    have hM : 0 < mgf Y μ θ₁ := mgf_pos (interior_subset (s := integrableExpSet Y μ) (hint θ₁))
    have : 0 ≤ deriv (cgf Y μ) θ₁ - x := by rw [this]; positivity
    linarith
  have hle : deriv (cgf Y μ) (-θ₀') ≤ x := by
    have h := hrel (-θ₀')
    have hM : 0 < mgf Y μ (-θ₀') :=
      mgf_pos (interior_subset (s := integrableExpSet Y μ) (hint (-θ₀')))
    have e : ∫ ω, (Y ω - x) * exp (-θ₀' * Y ω) ∂μ =
        -∫ ω, ((-Y) ω - -x) * exp (θ₀' * (-Y) ω) ∂μ := by
      rw [← integral_neg]
      congr 1; funext ω; simp only [Pi.neg_apply]; ring_nf
    have : deriv (cgf Y μ) (-θ₀') - x ≤ 0 := by
      rw [h, e, neg_div]
      have := div_nonneg hθ₀' hM.le
      linarith
    linarith
  obtain ⟨θ, hθ, hθx⟩ := intermediate_value_uIcc (a := -θ₀') (b := θ₁) hcont.continuousOn
    (mem_uIcc_of_le hle hge)
  exact ⟨θ, hint θ, hθx⟩

/-- **Cramér lower bound for bounded i.i.d. variables.**  If `|X₀| ≤ C` a.s., then for every open
`G`, `−inf {I(x) : x ∈ G, P(X₀ < x) > 0, P(X₀ > x) > 0} ≤ liminf (1/n) log P(S_n / n ∈ G)`:
every interior point of the convex hull of the support is exposed (`exists_deriv_cgf_eq`). -/
@[powerlib_foundation] theorem cramer_lower_bound_bounded [IsProbabilityMeasure μ]
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {C : ℝ} (hb : ∀ᵐ ω ∂μ, |X 0 ω| ≤ C)
    {G : Set ℝ} (hG : IsOpen G) :
    (⨆ x ∈ G, ⨆ (_ : 0 < μ {ω | X 0 ω < x}) (_ : 0 < μ {ω | x < X 0 ω}),
        -cramerRate (X 0) μ x) ≤
      liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G})) atTop := by
  refine le_trans ?_ (cramer_lower_bound hindep hmeas hid hG)
  refine iSup₂_le fun x hx => iSup₂_le fun hlo hhi => ?_
  obtain ⟨θ, hθ, hθx⟩ := exists_deriv_cgf_eq (hmeas 0) hb hlo hhi
  subst hθx
  exact le_iSup₂_of_le (f := fun θ (_ : θ ∈ interior (integrableExpSet (X 0) μ)) =>
    ⨆ (_ : deriv (cgf (X 0) μ) θ ∈ G), -cramerRate (X 0) μ (deriv (cgf (X 0) μ) θ)) θ hθ
    (le_iSup_of_le hx le_rfl)

/-- `∀ ε > 0, a ≤ r + ε` in `EReal` gives `a ≤ r`. -/
private theorem ereal_le_of_forall_le_add {a : EReal} {r : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ((r + ε : ℝ) : EReal)) : a ≤ (r : EReal) := by
  induction a using EReal.rec with
  | bot => exact bot_le
  | coe s =>
    rw [EReal.coe_le_coe_iff]
    exact le_of_forall_pos_le_add fun ε hε => EReal.coe_le_coe_iff.mp (h ε hε)
  | top => exact absurd (h 1 one_pos) (by rw [top_le_iff]; exact EReal.coe_ne_top _)

/-- An `EReal` below every negative real is `⊥`. -/
private theorem ereal_eq_bot_of_le {a : EReal} (h : ∀ r : ℝ, a ≤ (r : EReal)) : a = ⊥ := by
  induction a using EReal.rec with
  | bot => rfl
  | coe s =>
    have := EReal.coe_le_coe_iff.mp (h (s - 1))
    linarith
  | top => exact absurd (h 0) (by simp)

/-- **Upper endpoint of the support** (`P(X₀ > x) = 0`, no boundedness needed): with
`q = P(X₀ ∈ (x − δ, x])`, `P(S_n/n ∈ G) ≥ qⁿ` (independence) and `I(x) ≥ −log q` (tilts
`θ → +∞`), so `−I(x) ≤ liminf (1/n) log P(S_n/n ∈ G)` for `x ∈ G` open. -/
private theorem cramer_lower_upper_endpoint [IsProbabilityMeasure μ] (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {G : Set ℝ}
    (hG : IsOpen G) {x : ℝ} (hxG : x ∈ G) (hx : μ {ω | x < X 0 ω} = 0) :
    -cramerRate (X 0) μ x ≤
      liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G})) atTop := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hG x hxG
  set δ := ρ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set q := μ (X 0 ⁻¹' Ioc (x - δ) x) with hq
  have hle_x : ∀ᵐ ω ∂μ, X 0 ω ≤ x := by
    rw [ae_iff]; simpa [not_le] using hx
  -- Step 1: `log q ≤ liminf`
  have hstep1 : ENNReal.log q ≤
      liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G})) atTop := by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsub : (⋂ i ∈ Finset.range n, X i ⁻¹' Ioc (x - δ) x) ⊆
        {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G} := by
      intro ω hω
      simp only [mem_iInter, mem_preimage, mem_Ioc] at hω
      have hne : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.mpr hn⟩
      have hlo : (n : ℝ) * (x - δ) < ∑ i ∈ Finset.range n, X i ω := by
        have := Finset.sum_lt_sum_of_nonempty hne (fun i hi => (hω i hi).1)
        simpa [Finset.sum_const, Finset.card_range, mul_sub] using this
      have hhi : ∑ i ∈ Finset.range n, X i ω ≤ n * x := by
        have := Finset.sum_le_sum (fun i hi => (hω i hi).2)
        simpa [Finset.sum_const, Finset.card_range] using this
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · rw [lt_sub_iff_add_lt, lt_div_iff₀ hn']; nlinarith
      · rw [sub_lt_iff_lt_add, div_lt_iff₀ hn']; nlinarith
    have hprod : μ (⋂ i ∈ Finset.range n, X i ⁻¹' Ioc (x - δ) x) = q ^ n := by
      rw [hindep.measure_inter_preimage_eq_mul (Finset.range n) (fun i _ => measurableSet_Ioc),
        Finset.prod_congr rfl fun i _ => (hid i).measure_mem_eq measurableSet_Ioc,
        Finset.prod_const, Finset.card_range]
    have hmono : ENNReal.log (q ^ n) ≤
        ENNReal.log (μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G}) :=
      ENNReal.log_le_log (hprod ▸ measure_mono hsub)
    rw [ENNReal.log_pow] at hmono
    have hc : (0 : EReal) ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) := by
      exact_mod_cast (inv_nonneg.mpr hn'.le)
    calc ENNReal.log q = (((n : ℝ)⁻¹ : ℝ) : EReal) * ((n : EReal) * ENNReal.log q) := by
          rw [← mul_assoc, ← EReal.coe_natCast, ← EReal.coe_mul, inv_mul_cancel₀ hn'.ne',
            EReal.coe_one, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmono hc
  -- Step 2: `−I(x) ≤ log q`
  have hrate : ∀ θ : ℝ, 0 ≤ θ → -cramerRate (X 0) μ x ≤
      ((Real.log (q.toReal + exp (-(θ * δ))) : ℝ) : EReal) := by
    intro θ hθ
    have hbdd : ∀ᵐ ω ∂μ, exp (θ * X 0 ω) ≤
        exp (θ * x) * (X 0 ⁻¹' Ioc (x - δ) x).indicator 1 ω + exp (θ * (x - δ)) := by
      filter_upwards [hle_x] with ω hω
      by_cases hin : ω ∈ X 0 ⁻¹' Ioc (x - δ) x
      · rw [indicator_of_mem hin, Pi.one_apply, mul_one]
        have := exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hθ)
        linarith [exp_pos (θ * (x - δ))]
      · rw [indicator_of_notMem hin, mul_zero, zero_add]
        have hlt : X 0 ω ≤ x - δ := by
          simp only [mem_preimage, mem_Ioc, not_and, not_le] at hin
          by_contra h
          exact absurd (hin (not_le.mp h)) (not_lt.mpr hω)
        exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlt hθ)
    have hmA : MeasurableSet (X 0 ⁻¹' Ioc (x - δ) x) := hmeas 0 measurableSet_Ioc
    have hI : Integrable (fun ω => (X 0 ⁻¹' Ioc (x - δ) x).indicator (1 : Ω → ℝ) ω) μ :=
      (integrable_indicator_iff hmA).mpr (integrable_const (1 : ℝ)).integrableOn
    have hRHS : Integrable (fun ω => exp (θ * x) * (X 0 ⁻¹' Ioc (x - δ) x).indicator 1 ω +
        exp (θ * (x - δ))) μ := (hI.const_mul _).add (integrable_const _)
    have hexpi : Integrable (fun ω => exp (θ * X 0 ω)) μ :=
      Integrable.mono' hRHS (((hmeas 0).const_mul θ).exp.aestronglyMeasurable)
        (by filter_upwards [hbdd] with ω h; rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact h)
    have hM := integral_mono_ae hexpi hRHS hbdd
    rw [integral_add (hI.const_mul _) (integrable_const _), integral_const_mul,
      integral_indicator_one hmA, integral_const] at hM
    simp only [probReal_univ, smul_eq_mul, one_mul] at hM
    have hqr : μ.real (X 0 ⁻¹' Ioc (x - δ) x) = q.toReal := rfl
    rw [hqr] at hM
    have hMpos : 0 < mgf (X 0) μ θ := mgf_pos hexpi
    have hpos : 0 < q.toReal + exp (-(θ * δ)) := by positivity
    have hlog : cgf (X 0) μ θ ≤ θ * x + Real.log (q.toReal + exp (-(θ * δ))) := by
      have e : exp (θ * x) * q.toReal + exp (θ * (x - δ)) =
          exp (θ * x) * (q.toReal + exp (-(θ * δ))) := by
        rw [mul_add, ← exp_add]; ring_nf
      rw [e] at hM
      have := Real.log_le_log hMpos hM
      rw [Real.log_mul (exp_pos _).ne' hpos.ne', Real.log_exp] at this
      exact this
    have hmem : θ ∈ integrableExpSet (X 0) μ := hexpi
    have hI1 : ((θ * x - cgf (X 0) μ θ : ℝ) : EReal) ≤ cramerRate (X 0) μ x :=
      le_iSup₂_of_le (f := fun t (_ : t ∈ integrableExpSet (X 0) μ) =>
        ((t * x - cgf (X 0) μ t : ℝ) : EReal)) θ hmem le_rfl
    calc -cramerRate (X 0) μ x ≤ -((θ * x - cgf (X 0) μ θ : ℝ) : EReal) :=
          EReal.neg_le_neg_iff.mpr hI1
      _ = ((-(θ * x - cgf (X 0) μ θ) : ℝ) : EReal) := rfl
      _ ≤ _ := EReal.coe_le_coe_iff.mpr (by linarith)
  -- conclude
  refine le_trans ?_ hstep1
  by_cases hq0 : q = 0
  · have : -cramerRate (X 0) μ x = ⊥ := by
      refine ereal_eq_bot_of_le fun r => ?_
      set θ := (|r| + 1) / δ with hθ
      have hθ0 : 0 ≤ θ := by positivity
      refine (hrate θ hθ0).trans (EReal.coe_le_coe_iff.mpr ?_)
      rw [hq0, ENNReal.toReal_zero, zero_add, Real.log_exp]
      have : θ * δ = |r| + 1 := by rw [hθ]; field_simp
      rw [this]; linarith [neg_abs_le r]
    rw [this]; exact bot_le
  · have hqtop : q ≠ ⊤ := measure_ne_top _ _
    have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
    rw [ENNReal.log_pos_real hq0 hqtop]
    refine ereal_le_of_forall_le_add fun ε hε => ?_
    have hK : 0 < q.toReal * (exp ε - 1) := mul_pos hp (by linarith [add_one_lt_exp hε.ne'])
    set θ := max 0 (-Real.log (q.toReal * (exp ε - 1)) / δ) with hθ
    have hθ0 : 0 ≤ θ := le_max_left _ _
    refine (hrate θ hθ0).trans (EReal.coe_le_coe_iff.mpr ?_)
    have h1 : exp (-(θ * δ)) ≤ q.toReal * (exp ε - 1) := by
      have : -Real.log (q.toReal * (exp ε - 1)) ≤ θ * δ := by
        have := le_max_right 0 (-Real.log (q.toReal * (exp ε - 1)) / δ)
        rw [← hθ, div_le_iff₀ hδ] at this; exact this
      calc exp (-(θ * δ)) ≤ exp (Real.log (q.toReal * (exp ε - 1))) := exp_le_exp.mpr (by linarith)
        _ = _ := exp_log hK
    have h2 : q.toReal + exp (-(θ * δ)) ≤ q.toReal * exp ε := by nlinarith
    have := Real.log_le_log (by positivity) h2
    rw [Real.log_mul hp.ne' (exp_pos _).ne', Real.log_exp] at this
    exact this

/-- The rate function is invariant under the reflection `(Y, x) ↦ (−Y, −x)`. -/
private theorem cramerRate_neg (Y : Ω → ℝ) (x : ℝ) :
    cramerRate (-Y) μ (-x) = cramerRate Y μ x := by
  have hmem : ∀ t, t ∈ integrableExpSet (-Y) μ ↔ -t ∈ integrableExpSet Y μ := by
    intro t
    have : (fun ω => exp (t * (-Y) ω)) = fun ω => exp (-t * Y ω) := by
      funext ω; simp only [Pi.neg_apply]; ring_nf
    change Integrable (fun ω => exp (t * (-Y) ω)) μ ↔ Integrable (fun ω => exp (-t * Y ω)) μ
    rw [this]
  unfold cramerRate
  apply le_antisymm
  · refine iSup₂_le fun t ht => ?_
    refine le_iSup₂_of_le (f := fun t (_ : t ∈ integrableExpSet Y μ) =>
      ((t * x - cgf Y μ t : ℝ) : EReal)) (-t) ((hmem t).mp ht) (le_of_eq ?_)
    rw [cgf_neg]; congr 1; ring
  · refine iSup₂_le fun t ht => ?_
    refine le_iSup₂_of_le (f := fun t (_ : t ∈ integrableExpSet (-Y) μ) =>
      ((t * -x - cgf (-Y) μ t : ℝ) : EReal)) (-t) ((hmem (-t)).mpr (by simpa using ht))
      (le_of_eq ?_)
    rw [cgf_neg, neg_neg]; congr 1; ring

/-- **Lower endpoint of the support** (`P(X₀ < x) = 0`): reflection of
`cramer_lower_upper_endpoint`. -/
private theorem cramer_lower_lower_endpoint [IsProbabilityMeasure μ] (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {G : Set ℝ}
    (hG : IsOpen G) {x : ℝ} (hxG : x ∈ G) (hx : μ {ω | X 0 ω < x} = 0) :
    -cramerRate (X 0) μ x ≤
      liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G})) atTop := by
  have hindep' : iIndepFun (fun i => -X i) μ :=
    hindep.comp (fun _ => fun y : ℝ => -y) (fun _ => measurable_neg)
  have hmeas' : ∀ i, Measurable (-X i) := fun i => (hmeas i).neg
  have hid' : ∀ i, IdentDistrib (-X i) (-X 0) μ μ := fun i => (hid i).comp measurable_neg
  have hxG' : -x ∈ -G := by simpa using hxG
  have hx' : μ {ω | -x < (-X 0) ω} = 0 := by simpa using hx
  have h := cramer_lower_upper_endpoint (X := fun i => -X i) hindep' hmeas' hid' hG.neg hxG' hx'
  have hset : ∀ n : ℕ, {ω | (∑ i ∈ Finset.range n, (fun i => -X i) i ω) / n ∈ -G} =
      {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G} := by
    intro n; ext ω
    simp [Set.mem_neg, Finset.sum_neg_distrib, neg_div]
  simp only [hset] at h
  rwa [cramerRate_neg] at h

/-- **Cramér's theorem, lower bound, for bounded i.i.d. summands.**  If `|X₀| ≤ C` a.s., then for
every open `G ⊆ ℝ`,
`sup_{x ∈ G} (−I(x)) = −inf_{x ∈ G} I(x) ≤ liminf_{n → ∞} (1/n) log P(S_n / n ∈ G)`,
with `I = cramerRate X₀` the Legendre transform of the cumulant generating function.  Interior
points of the convex hull of the support are exposed (`cramer_lower_bound_bounded`); the two
endpoint cases (`P(X₀ > x) = 0` or `P(X₀ < x) = 0`, which include every point outside the hull,
where `I = ∞`) use `P(S_n/n ∈ G) ≥ P(X₀ ∈ (x − δ, x])ⁿ` and `I(x) ≥ −log P(X₀ ∈ (x − δ, x])`
(and the reflection `X ↦ −X`). -/
@[powerlib_foundation] theorem cramer_lower_bound_of_bounded [IsProbabilityMeasure μ]
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {C : ℝ} (hb : ∀ᵐ ω ∂μ, |X 0 ω| ≤ C)
    {G : Set ℝ} (hG : IsOpen G) :
    (⨆ x ∈ G, -cramerRate (X 0) μ x) ≤
      liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G})) atTop := by
  refine iSup₂_le fun x hx => ?_
  by_cases h1 : μ {ω | x < X 0 ω} = 0
  · exact cramer_lower_upper_endpoint hindep hmeas hid hG hx h1
  by_cases h2 : μ {ω | X 0 ω < x} = 0
  · exact cramer_lower_lower_endpoint hindep hmeas hid hG hx h2
  refine le_trans ?_ (cramer_lower_bound_bounded hindep hmeas hid hb hG)
  exact le_iSup₂_of_le (f := fun x (_ : x ∈ G) =>
    ⨆ (_ : 0 < μ {ω | X 0 ω < x}) (_ : 0 < μ {ω | x < X 0 ω}), -cramerRate (X 0) μ x) x hx
    (le_iSup₂_of_le (pos_iff_ne_zero.mpr h2) (pos_iff_ne_zero.mpr h1) le_rfl)


/-! ## Cramér lower bound: general (unbounded) i.i.d. summands, by truncation -/

/-- The truncation event `{|Y| ≤ M}` is measurable. -/
private theorem measurableSet_abs_le {Y : Ω → ℝ} (hY : Measurable Y) (M : ℝ) :
    MeasurableSet {ω | |Y ω| ≤ M} :=
  measurableSet_le (continuous_abs.measurable.comp hY) measurable_const

/-- Exponential moments of `Y − x` on the truncation `{|Y| ≤ M}` are finite. -/
private theorem integrable_exp_trunc [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (x M t : ℝ) :
    Integrable (fun ω => exp (t * (Y ω - x))) (μ.restrict {ω | |Y ω| ≤ M}) := by
  have hb : ∀ᵐ ω ∂(μ.restrict {ω | |Y ω| ≤ M}), |Y ω - x| ≤ M + |x| := by
    filter_upwards [ae_restrict_mem (measurableSet_abs_le hY M)] with ω hω
    have h : |Y ω| ≤ M := hω
    calc |Y ω - x| ≤ |Y ω| + |x| := abs_sub _ _
      _ ≤ M + |x| := by linarith
  have h := integrableExpSet_eq_univ (Y := fun ω => Y ω - x) (hY.sub_const x).aemeasurable hb
  have ht : t ∈ integrableExpSet (fun ω => Y ω - x) (μ.restrict {ω | |Y ω| ≤ M}) := by
    rw [h]; trivial
  exact ht

/-- Lower bound for the truncated exponential moment from a sub-event. -/
private theorem le_mgf_trunc [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y) (x : ℝ)
    {M t c : ℝ} {E : Set Ω} (hE : MeasurableSet E) (hsub : E ⊆ {ω | |Y ω| ≤ M})
    (hc : ∀ ω ∈ E, c ≤ t * (Y ω - x)) :
    exp c * μ.real E ≤ mgf (fun ω => Y ω - x) (μ.restrict {ω | |Y ω| ≤ M}) t := by
  have hint := integrable_exp_trunc (μ := μ) hY x M t
  have hle : μ.restrict E ≤ μ.restrict {ω | |Y ω| ≤ M} := Measure.restrict_mono hsub le_rfl
  have h1 : ∫ ω in E, exp (t * (Y ω - x)) ∂μ ≤
      mgf (fun ω => Y ω - x) (μ.restrict {ω | |Y ω| ≤ M}) t :=
    integral_mono_measure hle (ae_of_all _ fun _ => (exp_pos _).le) hint
  have h2 : ∫ ω in E, exp c ∂μ ≤ ∫ ω in E, exp (t * (Y ω - x)) ∂μ :=
    setIntegral_mono_on (integrable_const _) (hint.mono_measure hle) hE
      fun ω hω => exp_le_exp.mpr (hc ω hω)
  rw [setIntegral_const, smul_eq_mul, mul_comm] at h2
  linarith

/-- Truncated exponential moments increase with the truncation level. -/
private theorem mgf_trunc_mono [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y) (x : ℝ)
    {M M' : ℝ} (h : M ≤ M') (t : ℝ) :
    mgf (fun ω => Y ω - x) (μ.restrict {ω | |Y ω| ≤ M}) t ≤
      mgf (fun ω => Y ω - x) (μ.restrict {ω | |Y ω| ≤ M'}) t :=
  integral_mono_measure (Measure.restrict_mono (fun _ (hω : |Y _| ≤ M) => hω.trans h) le_rfl)
    (ae_of_all _ fun _ => (exp_pos _).le) (integrable_exp_trunc hY x M' t)

/-- If `P(Y > x) > 0`, some event `{Y > x + a, |Y| ≤ M}` (`a > 0`) has positive probability. -/
private theorem exists_trunc_level {Y : Ω → ℝ} {x : ℝ}
    (hx : 0 < μ {ω | x < Y ω}) :
    ∃ a : ℝ, 0 < a ∧ ∃ M : ℝ, 0 < μ {ω | x + a < Y ω ∧ |Y ω| ≤ M} := by
  have hU : {ω | x < Y ω} = ⋃ k : ℕ, {ω | x + 1 / ((k : ℝ) + 1) < Y ω ∧ |Y ω| ≤ k} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨k1, hk1⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      obtain ⟨k2, hk2⟩ := exists_nat_ge |Y ω|
      refine ⟨k1 + k2, ?_, ?_⟩
      · have : 1 / (((k1 + k2 : ℕ) : ℝ) + 1) ≤ 1 / ((k1 : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          push_cast; linarith [(k2.cast_nonneg : (0 : ℝ) ≤ k2)]
        linarith
      · exact hk2.trans (by push_cast; linarith [(k1.cast_nonneg : (0 : ℝ) ≤ k1)])
    · rintro ⟨k, hk, -⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < μ {ω | x + 1 / ((k : ℝ) + 1) < Y ω ∧ |Y ω| ≤ k} := by
    by_contra h
    push Not at h
    have : μ {ω | x < Y ω} = 0 := by
      rw [hU]; exact measure_iUnion_null fun k => nonpos_iff_eq_zero.mp (h k)
    exact absurd this hx.ne'
  exact ⟨1 / ((k : ℝ) + 1), by positivity, k, hk⟩

/-- `∀ r, ℓ ≤ r → a ≤ r` in `EReal` gives `a ≤ ℓ`. -/
private theorem ereal_le_of_forall_coe_ge {a ℓ : EReal} (h : ∀ r : ℝ, ℓ ≤ r → a ≤ r) :
    a ≤ ℓ := by
  induction ℓ using EReal.rec with
  | bot =>
    have : a = ⊥ := by
      induction a using EReal.rec with
      | bot => rfl
      | coe s =>
        have := EReal.coe_le_coe_iff.mp (h (s - 1) bot_le)
        linarith
      | top => exact absurd (h 0 bot_le) (by simp)
    rw [this]
  | coe s => exact h s le_rfl
  | top => exact le_top

/-- **Truncation limit for the Legendre transform** (Dembo–Zeitouni, proof of Thm 2.2.3).  Let
`P(Y < x) > 0` and `P(Y > x) > 0`.  If for every truncation level `M` (with `P(|Y| ≤ M) > 0`)
and every `ε > 0` some `t` has `E[e^{t(Y − x)}; |Y| ≤ M] ≤ e^{r + ε}`, then `−I(x) ≤ r`.
The minimisers stay in a fixed compact interval (both tails of `Y − x` near `x` carry mass), so
nested compact sublevel sets give one `t` working for every `M`; monotone convergence `M → ∞`
then gives `E[e^{t(Y − x)}] ≤ e^r`. -/
private theorem neg_cramerRate_le_of_trunc [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Measurable Y) {x r : ℝ} (hlo : 0 < μ {ω | Y ω < x}) (hhi : 0 < μ {ω | x < Y ω})
    (h : ∀ M : ℝ, 0 < μ {ω | |Y ω| ≤ M} → ∀ ε : ℝ, 0 < ε →
      ∃ t, mgf (fun ω => Y ω - x) (μ.restrict {ω | |Y ω| ≤ M}) t ≤ exp (r + ε)) :
    -cramerRate Y μ x ≤ (r : EReal) := by
  set F : ℝ → ℝ → ℝ := fun M t => mgf (fun ω => Y ω - x) (μ.restrict {ω | |Y ω| ≤ M}) t
    with hFdef
  obtain ⟨a1, ha1, M1, hM1⟩ := exists_trunc_level hhi
  obtain ⟨a2, ha2, M2, hM2⟩ := exists_trunc_level (x := -x) (Y := -Y) (by simpa using hlo)
  set E1 := {ω | x + a1 < Y ω ∧ |Y ω| ≤ M1} with hE1
  set E2 := {ω | -x + a2 < (-Y) ω ∧ |(-Y) ω| ≤ M2} with hE2
  have hE1m : MeasurableSet E1 :=
    (measurableSet_lt measurable_const hY).inter (measurableSet_abs_le hY M1)
  have hE2m : MeasurableSet E2 :=
    (measurableSet_lt measurable_const hY.neg).inter (measurableSet_abs_le hY.neg M2)
  set a := min a1 a2 with ha
  have ha0 : 0 < a := lt_min ha1 ha2
  set M0 := max M1 M2 with hM0
  set q := min (μ.real E1) (μ.real E2) with hq
  have hq0 : 0 < q := lt_min (ENNReal.toReal_pos hM1.ne' (measure_ne_top _ _))
    (ENNReal.toReal_pos hM2.ne' (measure_ne_top _ _))
  -- coercivity: `F M t ≥ q e^{|t| a}` for `M ≥ M0`
  have hlow : ∀ M, M0 ≤ M → ∀ t, q * exp (|t| * a) ≤ F M t := by
    intro M hM t
    rcases le_total 0 t with ht | ht
    · have hsub : E1 ⊆ {ω | |Y ω| ≤ M} := fun ω hω =>
        hω.2.trans ((le_max_left M1 M2).trans hM)
      have hc : ∀ ω ∈ E1, |t| * a ≤ t * (Y ω - x) := by
        intro ω hω
        rw [abs_of_nonneg ht]
        have : a ≤ Y ω - x := by have := hω.1; have := min_le_left a1 a2; linarith
        exact mul_le_mul_of_nonneg_left this ht
      have := le_mgf_trunc (μ := μ) hY x hE1m hsub hc
      have hq1 : q ≤ μ.real E1 := min_le_left _ _
      calc q * exp (|t| * a) ≤ μ.real E1 * exp (|t| * a) :=
            mul_le_mul_of_nonneg_right hq1 (exp_pos _).le
        _ = exp (|t| * a) * μ.real E1 := mul_comm _ _
        _ ≤ F M t := this
    · have hsub : E2 ⊆ {ω | |Y ω| ≤ M} := fun ω hω => by
        have h2 : |(-Y) ω| ≤ M2 := hω.2
        rw [Pi.neg_apply, abs_neg] at h2
        exact h2.trans ((le_max_right M1 M2).trans hM)
      have hc : ∀ ω ∈ E2, |t| * a ≤ t * (Y ω - x) := by
        intro ω hω
        rw [abs_of_nonpos ht]
        have h1 : -x + a2 < (-Y) ω := hω.1
        rw [Pi.neg_apply] at h1
        have : a ≤ x - Y ω := by have := min_le_right a1 a2; linarith
        nlinarith
      have := le_mgf_trunc (μ := μ) hY x hE2m hsub hc
      have hq2 : q ≤ μ.real E2 := min_le_right _ _
      calc q * exp (|t| * a) ≤ μ.real E2 * exp (|t| * a) :=
            mul_le_mul_of_nonneg_right hq2 (exp_pos _).le
        _ = exp (|t| * a) * μ.real E2 := mul_comm _ _
        _ ≤ F M t := this
  have hcont : ∀ M, Continuous (F M) := fun M =>
    continuous_mgf fun t => integrable_exp_trunc (μ := μ) hY x M t
  have hmono : ∀ M M', M ≤ M' → ∀ t, F M t ≤ F M' t := fun M M' hMM' t =>
    mgf_trunc_mono hY x hMM' t
  -- sublevel sets of level `≤ e^{r+1}` lie in `[−T0, T0]`
  set T0 := max 0 ((r + 1 - Real.log q) / a) with hT0
  have hin : ∀ M, M0 ≤ M → ∀ t, F M t ≤ exp (r + 1) → t ∈ Icc (-T0) T0 := by
    intro M hM t ht
    have h2 : q * exp (|t| * a) ≤ exp (r + 1) := (hlow M hM t).trans ht
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_mul hq0.ne' (exp_pos _).ne', Real.log_exp, Real.log_exp] at h3
    have h4 : |t| ≤ T0 := le_max_of_le_right ((le_div_iff₀ ha0).mpr (by linarith))
    exact ⟨by linarith [neg_abs_le t], (le_abs_self t).trans h4⟩
  -- nested compact sublevel sets
  set K : ℕ → Set ℝ := fun k =>
    Icc (-T0) T0 ∩ {t | F (M0 + k) t ≤ exp (r + 1 / ((k : ℝ) + 1))} with hK
  have hM0k : ∀ k : ℕ, M0 ≤ M0 + k := fun k => le_add_of_nonneg_right k.cast_nonneg
  have hKne : ∀ k, (K k).Nonempty := by
    intro k
    have hpos : 0 < μ {ω | |Y ω| ≤ M0 + k} := lt_of_lt_of_le hM1
      (measure_mono fun ω hω => hω.2.trans ((le_max_left M1 M2).trans (hM0k k)))
    obtain ⟨t, ht⟩ := h (M0 + k) hpos (1 / ((k : ℝ) + 1)) (by positivity)
    have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    exact ⟨t, hin (M0 + k) (hM0k k) t (ht.trans (exp_le_exp.mpr (by linarith))), ht⟩
  have hKsub : ∀ k, K (k + 1) ⊆ K k := by
    rintro k t ⟨ht1, ht2⟩
    refine ⟨ht1, ?_⟩
    simp only [mem_ofPred_eq] at ht2 ⊢
    have hkk : (M0 + k : ℝ) ≤ M0 + ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hdiv : 1 / (((k + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); push_cast; linarith
    calc F (M0 + k) t ≤ F (M0 + ((k + 1 : ℕ) : ℝ)) t := hmono _ _ hkk t
      _ ≤ exp (r + 1 / (((k + 1 : ℕ) : ℝ) + 1)) := ht2
      _ ≤ exp (r + 1 / ((k : ℝ) + 1)) := exp_le_exp.mpr (by linarith)
  have hKcl : ∀ k, IsClosed (K k) := fun k =>
    isClosed_Icc.inter (isClosed_le (hcont _) continuous_const)
  have hK0 : IsCompact (K 0) := isCompact_Icc.of_isClosed_subset (hKcl 0) inter_subset_left
  obtain ⟨t, ht⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKsub hKne hK0 hKcl
  rw [mem_iInter] at ht
  -- one tilt `t` works for every truncation level
  have hbound : ∀ j : ℕ, F (M0 + j) t ≤ exp r := by
    intro j
    have hlim : Tendsto (fun k : ℕ => exp (r + 1 / ((k : ℝ) + 1))) atTop (𝓝 (exp r)) := by
      have h0 : Tendsto (fun k : ℕ => r + 1 / ((k : ℝ) + 1)) atTop (𝓝 (r + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h0
      exact (continuous_exp.tendsto r).comp h0
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop j] with k hk
    have hjk : (M0 + j : ℝ) ≤ M0 + k := by
      have : (j : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    exact (hmono _ _ hjk t).trans (ht k).2
  -- monotone convergence: `E[e^{t(Y − x)}] ≤ e^r`
  set f : Ω → ℝ := fun ω => exp (t * (Y ω - x)) with hf
  have hfm : AEStronglyMeasurable f μ :=
    ((hY.sub_const x).const_mul t).exp.aestronglyMeasurable
  have hf0 : 0 ≤ᵐ[μ] f := ae_of_all _ fun _ => (exp_pos _).le
  have hUnion : (⋃ j : ℕ, {ω | |Y ω| ≤ M0 + j}) = univ := by
    refine eq_univ_of_forall fun ω => mem_iUnion.mpr ?_
    obtain ⟨j, hj⟩ := exists_nat_ge (|Y ω| - M0)
    exact ⟨j, show |Y ω| ≤ M0 + j by linarith⟩
  have hdir : Directed (· ⊆ ·) fun j : ℕ => {ω | |Y ω| ≤ M0 + j} := by
    refine Monotone.directed_le fun i j hij ω (hω : |Y ω| ≤ M0 + i) => ?_
    show |Y ω| ≤ M0 + j
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hlin : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal (exp r) := by
    rw [← Measure.restrict_univ (μ := μ), ← hUnion, setLIntegral_iUnion_of_directed _ hdir]
    refine iSup_le fun j => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_trunc hY x (M0 + j) t)
      (ae_of_all _ fun _ => (exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (hbound j)
  have hfi : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hfm hf0).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  have hfint : ∫ ω, f ω ∂μ ≤ exp r := by
    rw [integral_eq_lintegral_of_nonneg_ae hf0 hfm]
    exact ENNReal.toReal_le_of_le_ofReal (exp_pos r).le hlin
  -- conclude: `I(x) ≥ t x − Λ(t) ≥ −r`
  have hexp : (fun ω => exp (t * Y ω)) = fun ω => exp (t * x) * f ω := by
    funext ω; rw [hf, ← exp_add]; ring_nf
  have htD : t ∈ integrableExpSet Y μ := by
    show Integrable (fun ω => exp (t * Y ω)) μ
    rw [hexp]; exact hfi.const_mul _
  have hmgf : mgf Y μ t = exp (t * x) * ∫ ω, f ω ∂μ := by
    rw [mgf, hexp, integral_const_mul]
  have hMpos : 0 < mgf Y μ t := mgf_pos htD
  have hcgf : cgf Y μ t ≤ t * x + r := by
    rw [cgf]
    have h1 : mgf Y μ t ≤ exp (t * x + r) := by
      rw [hmgf, exp_add]; exact mul_le_mul_of_nonneg_left hfint (exp_pos _).le
    have := Real.log_le_log hMpos h1
    rwa [Real.log_exp] at this
  have hI : (((-r : ℝ)) : EReal) ≤ cramerRate Y μ x := by
    refine le_iSup₂_of_le (f := fun t (_ : t ∈ integrableExpSet Y μ) =>
      ((t * x - cgf Y μ t : ℝ) : EReal)) t htD ?_
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  rw [EReal.neg_le, ← EReal.coe_neg]
  exact hI

/-- **Truncation comparison.**  Let `ν` be the law of `X₀` conditioned on `|X₀| ≤ M`,
`p = P(|X₀| ≤ M)`, and `(Yᵢ)` the coordinates of the product space `ν^{⊗ℕ}`.  Then
`P(S_n/n ∈ G) ≥ pⁿ ν^{⊗ℕ}(S'_n/n ∈ G)` (restrict to `{|Xᵢ| ≤ M, i < n}`). -/
private theorem trunc_comparison [IsProbabilityMeasure μ] (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {G : Set ℝ}
    (hG : IsOpen G) {M : ℝ} (hp : μ {ω | |X 0 ω| ≤ M} ≠ 0) (n : ℕ) :
    μ {ω | |X 0 ω| ≤ M} ^ n * Measure.infinitePi (fun _ : ℕ => (μ.map (X 0))[|{y : ℝ | |y| ≤ M}])
        {ω : ℕ → ℝ | (∑ i ∈ Finset.range n, ω i) / n ∈ G} ≤
      μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G} := by
  set S' : Set ℝ := {y : ℝ | |y| ≤ M} with hS'def
  have hS' : MeasurableSet S' := measurableSet_le continuous_abs.measurable measurable_const
  set L := μ.map (X 0) with hLdef
  have hLS : L S' = μ {ω | |X 0 ω| ≤ M} := Measure.map_apply (hmeas 0) hS'
  set p := μ {ω | |X 0 ω| ≤ M} with hpdef
  have hptop : p ≠ ⊤ := measure_ne_top _ _
  set ν := L[|S'] with hν
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure (by rw [hLS]; exact hp)
  set s := Finset.range n with hs
  set D : Set (s → ℝ) := {z | (∑ i, z i) / n ∈ G} with hDdef
  have hD : MeasurableSet D := by
    have : Measurable fun z : s → ℝ => (∑ i, z i) / (n : ℝ) :=
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).div_const _
    exact this hG.measurableSet
  set B : Set (s → ℝ) := univ.pi fun _ => S' with hBdef
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => hS'
  -- product-space side
  have hA' : {ω : ℕ → ℝ | (∑ i ∈ s, ω i) / n ∈ G} = (s.restrict : (ℕ → ℝ) → (s → ℝ)) ⁻¹' D := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, hDdef, Finset.restrict]
    rw [Finset.sum_coe_sort s (fun i => ω i)]
  have hP : Measure.infinitePi (fun _ : ℕ => ν) ((s.restrict : (ℕ → ℝ) → (s → ℝ)) ⁻¹' D) =
      Measure.pi (fun _ : s => ν) D := by
    rw [← Measure.map_apply (Finset.measurable_restrict s) hD, Measure.infinitePi_map_restrict]
  -- original side
  have hjoint : μ.map (fun ω i => X i ω) = Measure.infinitePi (fun _ : ℕ => L) := by
    rw [hindep.map_fun_eq_infinitePi_map hmeas]
    congr 1; funext i; exact (hid i).map_eq
  have hΦ : Measurable fun ω (i : ℕ) => X i ω := measurable_pi_iff.mpr hmeas
  have hDB : MeasurableSet ((s.restrict : (ℕ → ℝ) → (s → ℝ)) ⁻¹' (D ∩ B)) :=
    (hD.inter hB).preimage (Finset.measurable_restrict (X := fun _ : ℕ => ℝ) s)
  have hμ : μ ((fun ω (i : ℕ) => X i ω) ⁻¹' ((s.restrict : (ℕ → ℝ) → (s → ℝ)) ⁻¹' (D ∩ B))) =
      Measure.pi (fun _ : s => L) (D ∩ B) := by
    rw [← Measure.map_apply hΦ hDB, hjoint,
      ← Measure.map_apply (Finset.measurable_restrict s) (hD.inter hB),
      Measure.infinitePi_map_restrict]
  have hsub : (fun ω (i : ℕ) => X i ω) ⁻¹' ((s.restrict : (ℕ → ℝ) → (s → ℝ)) ⁻¹' (D ∩ B)) ⊆
      {ω | (∑ i ∈ s, X i ω) / n ∈ G} := by
    intro ω hω
    have h1 := hω.1
    simp only [mem_ofPred_eq, hDdef, Finset.restrict] at h1
    rw [Finset.sum_coe_sort s (fun i => X i ω)] at h1
    exact h1
  -- restricting the product to the box and normalising each factor
  have hpi : Measure.pi (fun _ : s => L.restrict S') =
      p ^ n • Measure.pi (fun _ : s => ν) := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
    have hfac : ∀ i : s, L.restrict S' (t i) = p * ν (t i) := by
      intro i
      rw [hν, cond_apply hS', Measure.restrict_apply (ht i), hLS, ← mul_assoc,
        ENNReal.mul_inv_cancel hp hptop, one_mul, inter_comm]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_coe, show s.card = n from Finset.card_range n]
  have hbox : Measure.pi (fun _ : s => L) (D ∩ B) = p ^ n * Measure.pi (fun _ : s => ν) D := by
    rw [← Measure.restrict_apply hD, hBdef, Measure.restrict_pi_pi, hpi, Measure.smul_apply,
      smul_eq_mul]
  calc p ^ n * Measure.infinitePi (fun _ : ℕ => ν) {ω : ℕ → ℝ | (∑ i ∈ s, ω i) / n ∈ G}
      = μ ((fun ω (i : ℕ) => X i ω) ⁻¹' ((s.restrict : (ℕ → ℝ) → (s → ℝ)) ⁻¹' (D ∩ B))) := by
        rw [hA', hP, hμ, hbox]
    _ ≤ _ := measure_mono hsub

/-- **Truncated tilts from the `liminf`.**  If `liminf (1/n) log P(S_n/n ∈ G) ≤ r` and `x ∈ G`,
then for every truncation level `M` with `P(|X₀| ≤ M) > 0` and every `ε > 0` some tilt `t` has
`E[e^{t(X₀ − x)}; |X₀| ≤ M] ≤ e^{r + ε}`: the bounded Cramér lower bound
(`cramer_lower_bound_of_bounded`) for i.i.d. copies of `X₀` conditioned on `|X₀| ≤ M`, compared
through `trunc_comparison`, gives `I_ν(x) ≥ log P(|X₀| ≤ M) − r`. -/
private theorem trunc_exists_tilt [IsProbabilityMeasure μ] (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {G : Set ℝ}
    (hG : IsOpen G) {x : ℝ} (hxG : x ∈ G) {M : ℝ} (hp : 0 < μ {ω | |X 0 ω| ≤ M}) {r : ℝ}
    (hℓ : liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G})) atTop ≤ (r : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t, mgf (fun ω => X 0 ω - x) (μ.restrict {ω | |X 0 ω| ≤ M}) t ≤ exp (r + ε) := by
  set S' : Set ℝ := {y : ℝ | |y| ≤ M} with hS'def
  have hS' : MeasurableSet S' := measurableSet_le continuous_abs.measurable measurable_const
  set S : Set Ω := {ω | |X 0 ω| ≤ M} with hSdef
  set L := μ.map (X 0) with hLdef
  have hLS : L S' = μ S := Measure.map_apply (hmeas 0) hS'
  set p := μ S with hpdef
  have hp0 : p ≠ 0 := hp.ne'
  have hptop : p ≠ ⊤ := measure_ne_top _ _
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  set ν := L[|S'] with hν
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure (by rw [hLS]; exact hp0)
  set P : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => ν) with hPdef
  have hYm : ∀ i, Measurable (fun ω : ℕ → ℝ => ω i) := fun i => measurable_pi_apply i
  have hYind : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) P :=
    iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => id) fun _ => measurable_id
  have hYlaw : ∀ i, P.map (fun ω : ℕ → ℝ => ω i) = ν := fun i =>
    Measure.infinitePi_map_eval _ i
  have hYid : ∀ i, IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω => ω 0) P P := fun i =>
    ⟨(hYm i).aemeasurable, (hYm 0).aemeasurable, by rw [hYlaw, hYlaw]⟩
  have hYb : ∀ᵐ ω ∂P, |(fun ω : ℕ → ℝ => ω 0) ω| ≤ M :=
    ae_of_ae_map (hYm 0).aemeasurable (by rw [hYlaw 0]; exact ae_cond_mem hS')
  have hbd := cramer_lower_bound_of_bounded hYind hYm hYid hYb hG
  have hx := le_trans (le_iSup₂ (f := fun x (_ : x ∈ G) =>
    -cramerRate (fun ω : ℕ → ℝ => ω 0) P x) x hxG) hbd
  set lp := Real.log p.toReal with hlp
  -- `liminf (1/n) log ν^{⊗ℕ}(S'_n/n ∈ G) ≤ r − log p`
  have hB1 : liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
      ENNReal.log (P {ω | (∑ i ∈ Finset.range n, (fun ω : ℕ → ℝ => ω i) ω) / n ∈ G})) atTop ≤
        ((r - lp : ℝ) : EReal) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hev := eventually_lt_of_lt_liminf hc2
    have hle : ((lp + c : ℝ) : EReal) ≤ liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G})) atTop := by
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
      set a := P {ω | (∑ i ∈ Finset.range n, (fun ω : ℕ → ℝ => ω i) ω) / n ∈ G} with ha
      set b := μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G} with hb
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, ENNReal.log_zero, EReal.coe_mul_bot_of_pos (inv_pos.mpr hn')] at hn
        exact not_lt_bot hn
      have hatop : a ≠ ⊤ := measure_ne_top _ _
      have hcmp : p ^ n * a ≤ b := trunc_comparison hindep hmeas hid hG hp0 n
      have hb0 : b ≠ 0 := by
        intro h0
        rw [h0, nonpos_iff_eq_zero] at hcmp
        exact mul_ne_zero (pow_ne_zero n hp0) ha0 hcmp
      have hbtop : b ≠ ⊤ := measure_ne_top _ _
      rw [ENNReal.log_pos_real ha0 hatop, ← EReal.coe_mul, EReal.coe_lt_coe_iff] at hn
      rw [ENNReal.log_pos_real hb0 hbtop, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      have har : 0 < a.toReal := ENNReal.toReal_pos ha0 hatop
      have hcr : p.toReal ^ n * a.toReal ≤ b.toReal := by
        have := ENNReal.toReal_mono hbtop hcmp
        rwa [ENNReal.toReal_mul, ENNReal.toReal_pow] at this
      have hlog := Real.log_le_log (by positivity) hcr
      rw [Real.log_mul (by positivity) har.ne', Real.log_pow] at hlog
      have h3 : (n : ℝ)⁻¹ * (n * lp + Real.log a.toReal) ≤ (n : ℝ)⁻¹ * Real.log b.toReal :=
        mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hn'.le)
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul] at h3
      linarith
    have h2 := EReal.coe_le_coe_iff.mp (hle.trans hℓ)
    exact absurd hc1 (not_lt.mpr (EReal.coe_le_coe_iff.mpr (by linarith)))
  -- a tilt `t` for the conditioned law with `t x − Λ_ν(t) > log p − r − ε`
  have hI : ((lp - r - ε : ℝ) : EReal) < cramerRate (fun ω : ℕ → ℝ => ω 0) P x := by
    have h1 : -cramerRate (fun ω : ℕ → ℝ => ω 0) P x ≤ ((r - lp : ℝ) : EReal) := hx.trans hB1
    rw [EReal.neg_le, ← EReal.coe_neg] at h1
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith)) h1
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hI
  obtain ⟨htD, ht⟩ := lt_iSup_iff.mp ht
  rw [EReal.coe_lt_coe_iff] at ht
  refine ⟨t, ?_⟩
  have hMpos : 0 < mgf (fun ω : ℕ → ℝ => ω 0) P t := mgf_pos htD
  -- `mgf_ν(t) = p⁻¹ E[e^{tX₀}; |X₀| ≤ M]`
  have hmap : ∫ y, exp (t * y) ∂(P.map (fun ω : ℕ → ℝ => ω 0)) = ∫ ω, exp (t * ω 0) ∂P :=
    integral_map (hYm 0).aemeasurable
      ((measurable_const_mul t).exp.aestronglyMeasurable)
  rw [hYlaw 0] at hmap
  have hνint : ∫ y, exp (t * y) ∂ν = (p.toReal)⁻¹ * ∫ ω in S, exp (t * X 0 ω) ∂μ := by
    rw [hν, ProbabilityTheory.cond, integral_smul_measure,
      setIntegral_map hS' ((measurable_const_mul t).exp.aestronglyMeasurable)
        (hmeas 0).aemeasurable, hLS, ENNReal.toReal_inv, smul_eq_mul]
    rfl
  have hmgfν : mgf (fun ω : ℕ → ℝ => ω 0) P t =
      (p.toReal)⁻¹ * ∫ ω in S, exp (t * X 0 ω) ∂μ := by
    rw [← hνint, hmap]; rfl
  have hF : mgf (fun ω => X 0 ω - x) (μ.restrict S) t =
      exp (-(t * x)) * ∫ ω in S, exp (t * X 0 ω) ∂μ := by
    rw [mgf, ← integral_const_mul]
    congr 1; funext ω; rw [← exp_add]; ring_nf
  have hlt : mgf (fun ω : ℕ → ℝ => ω 0) P t < exp (t * x - lp + r + ε) := by
    rw [← Real.log_lt_iff_lt_exp hMpos]
    have : cgf (fun ω : ℕ → ℝ => ω 0) P t = Real.log (mgf (fun ω : ℕ → ℝ => ω 0) P t) := rfl
    linarith
  rw [hmgfν] at hlt
  have hJ : ∫ ω in S, exp (t * X 0 ω) ∂μ < exp (t * x) * exp (r + ε) := by
    have e : exp (t * x - lp + r + ε) = (p.toReal)⁻¹ * (exp (t * x) * exp (r + ε)) := by
      rw [show t * x - lp + r + ε = -lp + (t * x + (r + ε)) by ring, exp_add, exp_add, hlp,
        exp_neg, exp_log hpr]
    rw [e] at hlt
    exact lt_of_mul_lt_mul_left hlt (inv_nonneg.mpr hpr.le)
  rw [hF]
  calc exp (-(t * x)) * ∫ ω in S, exp (t * X 0 ω) ∂μ ≤
        exp (-(t * x)) * (exp (t * x) * exp (r + ε)) :=
        mul_le_mul_of_nonneg_left hJ.le (exp_pos _).le
    _ = exp (r + ε) := by rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]

/-- **Cramér's theorem, lower bound, general i.i.d. case** (no boundedness or moment
assumption; Dembo–Zeitouni, Thm 2.2.3).  For i.i.d. real `X₀, X₁, …` and every open `G ⊆ ℝ`,
`sup_{x ∈ G} (−I(x)) = −inf_{x ∈ G} I(x) ≤ liminf_{n → ∞} (1/n) log P(S_n / n ∈ G)`,
with `I = cramerRate X₀` the Legendre transform of the cumulant generating function over its
effective domain (`I(x) = ∞` is allowed; then the bound is trivial).
Endpoint cases `P(X₀ > x) = 0` / `P(X₀ < x) = 0` as in the bounded case.  Otherwise
truncation: for each level `M`, the bounded lower bound for `X₀` conditioned on `|X₀| ≤ M`
(on the product space of the conditioned law) and `P(S_n/n ∈ G) ≥ P(|X₀| ≤ M)ⁿ ν_M^{⊗n}(…)`
give tilts `t` with `E[e^{t(X₀ − x)}; |X₀| ≤ M] ≤ e^{ℓ + ε}` (`ℓ` the `liminf`); these tilts
stay in a compact interval, a nested-compact argument gives one `t` for all `M`, and monotone
convergence `M → ∞` yields `t x − Λ(t) ≥ −ℓ`, hence `−I(x) ≤ ℓ`. -/
@[powerlib_foundation] theorem cramer_lower_bound_general [IsProbabilityMeasure μ]
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {G : Set ℝ} (hG : IsOpen G) :
    (⨆ x ∈ G, -cramerRate (X 0) μ x) ≤
      liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (μ {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ G})) atTop := by
  refine iSup₂_le fun x hx => ?_
  by_cases h1 : μ {ω | x < X 0 ω} = 0
  · exact cramer_lower_upper_endpoint hindep hmeas hid hG hx h1
  by_cases h2 : μ {ω | X 0 ω < x} = 0
  · exact cramer_lower_lower_endpoint hindep hmeas hid hG hx h2
  refine ereal_le_of_forall_coe_ge fun r hr => ?_
  exact neg_cramerRate_le_of_trunc (hmeas 0) (pos_iff_ne_zero.mpr h2) (pos_iff_ne_zero.mpr h1)
    fun M hM ε hε => trunc_exists_tilt hindep hmeas hid hG hx hM hr hε

end Cramer

end powerlib.Stochastic.LDP
