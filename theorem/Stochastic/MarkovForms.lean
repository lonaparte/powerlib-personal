import dependencies.Mathlib
import theorem.Attributes
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.Probability.Process.Filtration

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

end powerlib.Stochastic.Markov
