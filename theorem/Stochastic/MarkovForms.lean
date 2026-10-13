import dependencies.Mathlib
import theorem.Attributes
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.UniformOn
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.Composition.Comp

/-! # Markov property: event form ⇔ conditional-expectation form

Source: work-sync `theory/T-markov-processes.md` §1.1 (Markov property in event form
`P(X_t ∈ A | 𝓕_s) = P(X_t ∈ A | X_s)`), §1.3 (conditional-expectation form
`E[f(X_t) | 𝓕_s] = E[f(X_t) | X_s]` for bounded measurable `f`; "the two forms are equivalent").

Foundation (probability), not an engineering result.

Main results.
* `condExp_eq_condExp_iff_aestronglyMeasurable`: for sub-σ-algebras `m₂ ≤ m₁`,
  `E[Y | m₁] = E[Y | m₂]` a.e. iff `E[Y | m₁]` is a.e. `m₂`-measurable.
* `condExp_eq_condExp_of_indicator`: if `E[1_A(Z) | m₁] = E[1_A(Z) | m₂]` for every measurable
  `A`, then `E[g(Z) | m₁] = E[g(Z) | m₂]` for every bounded measurable `g` (simple-function
  induction + conditional dominated convergence in `L¹` + closedness of the a.e.
  `m₂`-measurable functions in `L¹`).
* `MarkovEvent` and `markovEvent_iff_markovCondExp`: for an adapted process with values in a
  measurable space, the event form and the conditional-expectation form of the Markov property
  (`E[g(X_t) | 𝓕_s] = E[g(X_t) | X_s]` a.s. for `s ≤ t` and bounded measurable `g`, written out in
  the statement) are equivalent (any index order, any state space).

Counterexample: semigroup ⇏ Markov (`theory/T-markov-processes.md` §1.2, "Markov ⇔ semigroup").
* `semigroup_not_markov` (Feller's example): on `Ω = (Fin 3)²` with the uniform probability, the
  three-step process `X₀ = a`, `X₁ = b`, `X₂ = −(a + b) (mod 3)` has, for every pair of times
  `i ≠ j`, the elementary transition probabilities `P(X_j = b | X_i = a) = 1/3`, i.e. the constant
  uniform kernel `K`, and `K ∘ K = K` — the transition kernels satisfy Chapman–Kolmogorov (they are
  those of an i.i.d. uniform sequence) — yet `X` is **not** Markov in event form for any filtration
  to which it is adapted: `X₂` is a function of `(X₀, X₁)`.  Hence the semigroup
  (Chapman–Kolmogorov) relation of the two-dimensional transition laws does not imply the Markov
  property.
  Supporting facts: `feller_pair` (every pair `(X_i, X_j)` is uniform on `(Fin 3)²`),
  `feller_marginal`, `feller_transition`, `unifKernel_comp`, `feller_not_markov`.
-/

noncomputable section
namespace powerlib.Stochastic.Markov

open MeasureTheory Filter
open scoped Topology

section General

variable {Ω E : Type*} {m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  {mE : MeasurableSpace E} {P : Measure Ω} [IsFiniteMeasure P]

/-- For `m₂ ≤ m₁`, `E[Y | m₁] = E[Y | m₂]` a.e. iff `E[Y | m₁]` is a.e. `m₂`-measurable. -/
@[powerlib_foundation] theorem condExp_eq_condExp_iff_aestronglyMeasurable (h₂₁ : m₂ ≤ m₁)
    (h₁ : m₁ ≤ mΩ) {Y : Ω → ℝ} :
    P[Y | m₁] =ᵐ[P] P[Y | m₂] ↔ AEStronglyMeasurable[m₂] (P[Y | m₁]) P := by
  constructor
  · intro h
    exact stronglyMeasurable_condExp.aestronglyMeasurable.congr h.symm
  · intro hQ
    have h2 : P[P[Y | m₁] | m₂] =ᵐ[P] P[Y | m₁] :=
      condExp_of_aestronglyMeasurable' (h₂₁.trans h₁) hQ integrable_condExp
    exact h2.symm.trans (condExp_condExp_of_le h₂₁ h₁)

/-- **Indicators determine the conditional law**: if `E[1_A(Z) | m₁] = E[1_A(Z) | m₂]` for all
measurable `A`, then `E[g(Z) | m₁] = E[g(Z) | m₂]` for all bounded measurable `g`. -/
@[powerlib_foundation] theorem condExp_eq_condExp_of_indicator (h₂₁ : m₂ ≤ m₁) (h₁ : m₁ ≤ mΩ)
    {Z : Ω → E} (hZ : Measurable Z)
    (hind : ∀ A : Set E, MeasurableSet A →
      P[fun ω => A.indicator (fun _ => (1 : ℝ)) (Z ω) | m₁] =ᵐ[P]
        P[fun ω => A.indicator (fun _ => (1 : ℝ)) (Z ω) | m₂])
    {g : E → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ y, |g y| ≤ C) :
    P[fun ω => g (Z ω) | m₁] =ᵐ[P] P[fun ω => g (Z ω) | m₂] := by
  rw [condExp_eq_condExp_iff_aestronglyMeasurable h₂₁ h₁]
  have hint : ∀ s : SimpleFunc E ℝ, Integrable (fun ω => s (Z ω)) P := by
    intro s
    have := SimpleFunc.integrable_of_isFiniteMeasure (μ := P) (s.comp Z hZ)
    rwa [SimpleFunc.coe_comp] at this
  -- the property holds for simple functions
  have hsimple : ∀ s : SimpleFunc E ℝ,
      AEStronglyMeasurable[m₂] (P[fun ω => s (Z ω) | m₁]) P := by
    intro s
    induction s using SimpleFunc.induction with
    | @const c A hA =>
      have e : (fun ω => (SimpleFunc.piecewise A hA (SimpleFunc.const E c)
          (SimpleFunc.const E 0)) (Z ω)) =
          c • fun ω => A.indicator (fun _ => (1 : ℝ)) (Z ω) := by
        funext ω
        by_cases h : Z ω ∈ A <;> simp [h, Set.indicator, SimpleFunc.piecewise_apply]
      rw [e]
      have h1 := (condExp_eq_condExp_iff_aestronglyMeasurable h₂₁ h₁).mp (hind A hA)
      exact (h1.const_smul c).congr (condExp_smul c _ m₁).symm
    | @add f₁ f₂ _ hf₁ hf₂ =>
      have e : (fun ω => (f₁ + f₂) (Z ω)) = (fun ω => f₁ (Z ω)) + fun ω => f₂ (Z ω) := by
        funext ω; simp
      rw [e]
      exact (hf₁.add hf₂).congr (condExp_add (hint f₁) (hint f₂) m₁).symm
  -- bounded approximation
  have hgs : StronglyMeasurable g := hg.stronglyMeasurable
  have hC0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hgC : ∀ y, ‖g y‖ ≤ max C 0 := fun y => by
    rw [Real.norm_eq_abs]; exact (hC y).trans (le_max_left _ _)
  have hconv : ∀ ω, Tendsto (fun n => hgs.approxBounded (max C 0) n (Z ω)) atTop
      (𝓝 (g (Z ω))) := fun ω => hgs.tendsto_approxBounded_of_norm_le (hgC _)
  have hbound : ∀ n ω, ‖hgs.approxBounded (max C 0) n (Z ω)‖ ≤ max C 0 :=
    fun n ω => hgs.norm_approxBounded_le hC0 n _
  have hL1 := tendsto_condExpL1_of_dominated_convergence h₁ (μ := P)
    (fs := fun n ω => hgs.approxBounded (max C 0) n (Z ω)) (f := fun ω => g (Z ω))
    (fun _ => max C 0) (fun n => (hint _).aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hconv)
  have hclosed := isClosed_aestronglyMeasurable (F := ℝ) (p := 1) (μ := P) (h₂₁.trans h₁)
  have hmem : ∀ n, condExpL1 h₁ P (fun ω => hgs.approxBounded (max C 0) n (Z ω)) ∈
      {f : Lp ℝ 1 P | AEStronglyMeasurable[m₂] f P} := by
    intro n
    exact (hsimple _).congr (condExp_ae_eq_condExpL1 h₁ _)
  have hlim := hclosed.mem_of_tendsto hL1 (Eventually.of_forall hmem)
  exact hlim.congr (condExp_ae_eq_condExpL1 h₁ _).symm

end General

section Process

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} [mE : MeasurableSpace E] [Preorder ι]

/-- Markov property, **event form**: `P(X_t ∈ A | 𝓕_s) = P(X_t ∈ A | X_s)` a.s. for `s ≤ t`. -/
def MarkovEvent (P : Measure Ω) (𝓕 : Filtration ι mΩ) (X : ι → Ω → E) : Prop :=
  ∀ s t, s ≤ t → ∀ A : Set E, MeasurableSet A →
    P[fun ω => A.indicator (fun _ => (1 : ℝ)) (X t ω) | 𝓕 s] =ᵐ[P]
      P[fun ω => A.indicator (fun _ => (1 : ℝ)) (X t ω) | mE.comap (X s)]

/-- **Event form ⇔ conditional-expectation form** of the Markov property, for an adapted
process on a finite measure space. The right-hand side is the Markov property in
**conditional-expectation form**: `E[g(X_t) | 𝓕_s] = E[g(X_t) | X_s]` a.s. for `s ≤ t` and every
bounded measurable `g`. -/
@[powerlib_foundation] theorem markovEvent_iff_markovCondExp {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} (hadapt : ∀ s, Measurable[𝓕 s] (X s))
    (hX : ∀ t, Measurable (X t)) :
    MarkovEvent P 𝓕 X ↔
      ∀ s t, s ≤ t → ∀ g : E → ℝ, Measurable g → (∃ C, ∀ y, |g y| ≤ C) →
        P[fun ω => g (X t ω) | 𝓕 s] =ᵐ[P] P[fun ω => g (X t ω) | mE.comap (X s)] := by
  constructor
  · rintro h s t hst g hg ⟨C, hC⟩
    exact condExp_eq_condExp_of_indicator (hadapt s).comap_le (𝓕.le s) (hX t) (h s t hst) hg hC
  · intro h s t hst A hA
    refine h s t hst _ (measurable_const.indicator hA) ⟨1, fun y => ?_⟩
    by_cases hy : y ∈ A <;> simp [Set.indicator, hy]

end Process

/-! ## Semigroup does not imply Markov: Feller's example -/

section Feller

open ProbabilityTheory
open scoped ENNReal

/-- Feller's process on `Ω = (Fin 3)²`: `X₀ = a`, `X₁ = b`, `X₂ = −(a + b)` (mod 3). -/
def fellerX : Fin 3 → Fin 3 × Fin 3 → Fin 3 :=
  ![Prod.fst, Prod.snd, fun ω => -(ω.1 + ω.2)]

/-- The uniform probability on `(Fin 3)²`. -/
def fellerP : Measure (Fin 3 × Fin 3) := uniformOn Set.univ

instance : IsProbabilityMeasure fellerP := by unfold fellerP; infer_instance

/-- The constant uniform transition kernel on `Fin 3`. -/
def unifKernel : Kernel (Fin 3) (Fin 3) := Kernel.const (Fin 3) (uniformOn Set.univ)

/-- Probabilities under `fellerP` are counts divided by `9`. -/
@[powerlib_foundation] theorem fellerP_apply (p : Fin 3 × Fin 3 → Prop) [DecidablePred p] :
    fellerP {ω | p ω} = (Finset.univ.filter p).card / 9 := by
  rw [fellerP, uniformOn_univ]
  have : {ω | p ω} = ((Finset.univ.filter p : Finset _) : Set (Fin 3 × Fin 3)) := by ext; simp
  rw [this, Measure.count_apply_finset]
  rfl

/-- Every sample point has probability `1/9`. -/
@[powerlib_foundation] theorem fellerP_singleton (x : Fin 3 × Fin 3) :
    fellerP.real {x} = 1 / 9 := by
  have : ({x} : Set (Fin 3 × Fin 3)) = {ω | ω = x} := rfl
  rw [measureReal_def, this, fellerP_apply, Finset.filter_eq' Finset.univ x]
  simp

private theorem ennreal_three_div_nine : (3 : ℝ≥0∞) / 9 = 1 / 3 := by
  rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Two-dimensional laws: every pair `(X_i, X_j)`, `i ≠ j`, is uniform on `(Fin 3)²`. -/
@[powerlib_foundation] theorem feller_pair (i j : Fin 3) (hij : i ≠ j) (a b : Fin 3) :
    fellerP {ω | fellerX i ω = a ∧ fellerX j ω = b} = 1 / 9 := by
  have hc : (Finset.univ.filter fun ω => fellerX i ω = a ∧ fellerX j ω = b).card = 1 := by
    revert i j a b; decide
  rw [fellerP_apply, hc]
  simp

/-- One-dimensional laws: every `X_i` is uniform on `Fin 3`. -/
@[powerlib_foundation] theorem feller_marginal (i a : Fin 3) :
    fellerP {ω | fellerX i ω = a} = 1 / 3 := by
  have hc : (Finset.univ.filter fun ω => fellerX i ω = a).card = 3 := by revert i a; decide
  rw [fellerP_apply, hc]
  exact_mod_cast ennreal_three_div_nine

/-- `K(a, {b}) = 1/3`. -/
@[powerlib_foundation] theorem unifKernel_apply (a b : Fin 3) : unifKernel a {b} = 1 / 3 := by
  rw [unifKernel, Kernel.const_apply, uniformOn_univ, Measure.count_singleton]
  simp

/-- Chapman–Kolmogorov for the uniform kernel: `K ∘ K = K`. -/
@[powerlib_foundation] theorem unifKernel_comp : unifKernel ∘ₖ unifKernel = unifKernel := by
  ext1 a
  rw [unifKernel, Kernel.const_comp]
  simp [Kernel.const_apply]

/-- Transition probabilities between any two distinct times: `P(X_j = b | X_i = a) = K(a, {b})`. -/
@[powerlib_foundation] theorem feller_transition (i j : Fin 3) (hij : i ≠ j) (a b : Fin 3) :
    fellerP[{ω | fellerX j ω = b} | {ω | fellerX i ω = a}] = unifKernel a {b} := by
  have hm : MeasurableSet {ω : Fin 3 × Fin 3 | fellerX i ω = a} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  rw [cond_apply hm, feller_marginal, unifKernel_apply]
  have : {ω | fellerX i ω = a} ∩ {ω | fellerX j ω = b} =
      {ω : Fin 3 × Fin 3 | fellerX i ω = a ∧ fellerX j ω = b} := rfl
  rw [this, feller_pair i j hij]
  simp only [one_div, inv_inv]
  rw [← div_eq_mul_inv, ennreal_three_div_nine, one_div]

/-- Feller's process is not Markov (event form) for any filtration to which it is adapted:
`P(X₂ = 0 | 𝓕₁)` equals `1` at `(0, 0)` and `0` at `(1, 0)`, while `P(X₂ = 0 | X₁)` cannot
separate these two points (`X₁ = 0` at both). -/
@[powerlib_foundation] theorem feller_not_markov
    (𝓕 : Filtration (Fin 3) (inferInstance : MeasurableSpace (Fin 3 × Fin 3)))
    (hadapt : ∀ s, Measurable[𝓕 s] (fellerX s)) : ¬ MarkovEvent fellerP 𝓕 fellerX := by
  intro h
  set f : Fin 3 × Fin 3 → ℝ :=
    fun ω => ({0} : Set (Fin 3)).indicator (fun _ => (1 : ℝ)) (fellerX 2 ω) with hf
  have hm := h 1 2 (by decide) {0} (measurableSet_singleton 0)
  set F := fellerP[f | 𝓕 1]
  set G := fellerP[f | (inferInstance : MeasurableSpace (Fin 3)).comap (fellerX 1)]
  have hint : Integrable f fellerP := Integrable.of_finite
  -- `F` agrees with `f` at every point (singletons are `𝓕 1`-measurable, positive mass)
  have hsing : ∀ x : Fin 3 × Fin 3, MeasurableSet[𝓕 1] {x} := by
    intro x
    have h0 : Measurable[𝓕 1] (fellerX 0) := (hadapt 0).mono (𝓕.mono (by decide)) le_rfl
    have h1 : Measurable[𝓕 1] (fellerX 1) := hadapt 1
    have e : ({x} : Set (Fin 3 × Fin 3)) = fellerX 0 ⁻¹' {x.1} ∩ fellerX 1 ⁻¹' {x.2} := by
      ext ω; simp [fellerX, Prod.ext_iff]
    rw [e]
    exact (h0 (measurableSet_singleton _)).inter (h1 (measurableSet_singleton _))
  have hF : ∀ x, F x = f x := by
    intro x
    have := setIntegral_condExp (𝓕.le 1) hint (hsing x)
    rw [integral_singleton, integral_singleton, fellerP_singleton] at this
    simpa using this
  have hFG : ∀ x, F x = G x := by
    intro x
    have hx : ∫ y in {x}, F y ∂fellerP = ∫ y in {x}, G y ∂fellerP :=
      setIntegral_congr_ae (measurableSet_singleton x) (hm.mono fun y hy _ => hy)
    rw [integral_singleton, integral_singleton, fellerP_singleton] at hx
    simpa using hx
  -- `G` is `σ(X₁)`-measurable, hence constant on the fibres of `X₁`
  have hGm : Measurable[(inferInstance : MeasurableSpace (Fin 3)).comap (fellerX 1)] G :=
    stronglyMeasurable_condExp.measurable
  have hfib : G (0, 0) = G (1, 0) := by
    obtain ⟨s', -, hs'⟩ := MeasurableSpace.measurableSet_comap.mp
      (hGm (measurableSet_singleton (G (0, 0))))
    have h00 : (0, 0) ∈ fellerX 1 ⁻¹' s' := by rw [hs']; rfl
    have h10 : ((1 : Fin 3), (0 : Fin 3)) ∈ fellerX 1 ⁻¹' s' := by
      simpa [fellerX] using h00
    rw [hs'] at h10
    exact h10.symm
  have e1 : f (0, 0) = 1 := by simp [hf, fellerX]
  have e2 : f (1, 0) = 0 := by simp [hf, fellerX]
  rw [← hFG, ← hFG, hF, hF, e1, e2] at hfib
  norm_num at hfib

/-- **Semigroup ⇏ Markov** (Feller's example).  The process `fellerX` (`X₀ = a`, `X₁ = b`,
`X₂ = −(a + b) mod 3` under the uniform law of `(a, b)`) has the constant uniform transition kernel
`K` between any two times (`P(X_j = b | X_i = a) = K(a, {b}) = 1/3` for `i ≠ j`), and these
kernels satisfy Chapman–Kolmogorov (`K ∘ K = K`); nevertheless `X` is not Markov (event form) for
any filtration to which it is adapted. -/
@[powerlib_foundation] theorem semigroup_not_markov :
    unifKernel ∘ₖ unifKernel = unifKernel ∧
      (∀ i j : Fin 3, i ≠ j → ∀ a b : Fin 3,
        fellerP[{ω | fellerX j ω = b} | {ω | fellerX i ω = a}] = unifKernel a {b}) ∧
      ∀ 𝓕 : Filtration (Fin 3) (inferInstance : MeasurableSpace (Fin 3 × Fin 3)),
        (∀ s, Measurable[𝓕 s] (fellerX s)) → ¬ MarkovEvent fellerP 𝓕 fellerX :=
  ⟨unifKernel_comp, feller_transition, feller_not_markov⟩

end Feller

end powerlib.Stochastic.Markov
