import dependencies.Mathlib
import theorem.Attributes
import theorem.Dynamics.LipschitzFlow

/-! # LaSalle's principle along one bounded forward orbit of a globally Lipschitz flow

A forward orbit that stays in a compact set `B`, along which a continuous function `V` is
nonincreasing, accumulates only at points `p ∈ B` whose own forward orbits keep `V` constant: it
converges to every set `Z` containing those points. No positively invariant compact set and no
derivative of `V` is needed (only the orbit is assumed bounded); this is the form used for one
trajectory selected by a shooting argument, whose orbit closure is not given in advance.

Scope.
* `ẋ = f(x)` on a real Banach space `E`, `f` globally Lipschitz, through its forward flow
  `Dynamics.forwardSolution` (`theorem/Dynamics/LipschitzFlow.lean`); generic, no model family.
* The conclusion is the convergence of one orbit to a set (`𝓝ˢ Z`); the ω-limit set is Mathlib's
  `omegaLimit`.

Source: work-sync theory/T-lyapunov-function-method.md §1.4 (LaSalle invariance principle);
H. K. Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.1 and Theorem 4.4 (a bounded orbit converges
to its ω-limit set, which is invariant and on which `V` is constant).

Results.
* `tendsto_nhdsSet_of_antitone`: `x(t) ∈ B` for `t ≥ 0` (`B` compact), `V` continuous and
  nonincreasing along `x(·)`, and every `p ∈ B` with `V(φ_t p) = V(p)` for all `t ≥ 0` lies in
  `Z` ⇒ `x(t) → Z` (`Tendsto x atTop (𝓝ˢ Z)`).
-/

noncomputable section
namespace powerlib.Dynamics

open Set Filter Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {K : ℝ≥0}

/-- **LaSalle along a bounded orbit**: if the forward orbit of `x` stays in the compact set `B`,
`V` is continuous and nonincreasing along it, and every `p ∈ B` whose forward orbit keeps `V`
constant lies in `Z`, then the orbit converges to `Z`. -/
@[tmio T, powerlib_foundation] theorem tendsto_nhdsSet_of_antitone (hf : LipschitzWith K f)
    {x : E} {B : Set E} (hB : IsCompact B) (hxB : ∀ t : ℝ, 0 ≤ t → forwardSolution hf x t ∈ B)
    {V : E → ℝ} (hV : Continuous V)
    (hanti : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      V (forwardSolution hf x t) ≤ V (forwardSolution hf x s))
    {Z : Set E} (hZ : ∀ p ∈ B, (∀ t : ℝ, 0 ≤ t → V (forwardSolution hf p t) = V p) → p ∈ Z) :
    Tendsto (forwardSolution hf x) atTop (𝓝ˢ Z) := by
  have hϕx : ∀ (t : ℝ≥0) (y : E), lipschitzFlow hf t y = forwardSolution hf y t :=
    fun _ _ => rfl
  set g : ℝ≥0 → ℝ := fun t => V (lipschitzFlow hf t x) with hg
  have hganti : Antitone g := fun s t hst => by
    simp only [hg, hϕx]; exact hanti s t s.2 hst
  obtain ⟨m, hm⟩ : BddBelow (V '' B) := (hB.image hV).bddBelow
  have hgb : BddBelow (range g) := ⟨m, by
    rintro _ ⟨t, rfl⟩; exact hm ⟨_, hxB t t.2, rfl⟩⟩
  have hL := tendsto_atTop_ciInf hganti hgb
  set L := ⨅ t, g t
  set Ω := omegaLimit atTop (lipschitzFlow hf) {x}
  -- `V = L` on the ω-limit set
  have hVΩ : ∀ p ∈ Ω, V p = L := by
    intro p hp
    have hc := ((mem_omegaLimit_singleton_iff_mapClusterPt atTop (lipschitzFlow hf) x p).1
      hp).continuousAt_comp hV.continuousAt
    exact eq_of_nhds_neBot (ClusterPt.mono hc hL)
  -- the ω-limit set lies in `B`
  have hΩB : Ω ⊆ B := by
    refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := lipschitzFlow hf) (s := {x})
    univ_mem).trans ?_
    refine closure_minimal ?_ hB.isClosed
    rintro _ ⟨t, -, y, rfl, rfl⟩
    exact hxB t t.2
  -- invariance: the ω-limit set lies in `Z`
  have hinv := isInvariant_omegaLimit hf {x}
  have hΩZ : Ω ⊆ Z := by
    intro p hp
    refine hZ p (hΩB hp) fun t ht => ?_
    have h1 : lipschitzFlow hf ⟨t, ht⟩ p ∈ Ω := hinv ⟨t, ht⟩ hp
    exact (hVΩ _ h1).trans (hVΩ p hp).symm
  -- convergence
  refine (hasBasis_nhdsSet Z).tendsto_right_iff.2 fun U ⟨hU, hZU⟩ => ?_
  have hev := eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset
    (f := atTop) (ϕ := lipschitzFlow hf) (s := {x}) hB
    (Eventually.of_forall fun t => by
      rintro _ rfl; exact hxB t t.2) hU (hΩZ.trans hZU)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  filter_upwards [eventually_ge_atTop (N : ℝ)] with t ht
  have ht0 : 0 ≤ t := N.2.trans ht
  exact hN ⟨t, ht0⟩ (by exact_mod_cast ht) (mem_singleton x)

end powerlib.Dynamics
