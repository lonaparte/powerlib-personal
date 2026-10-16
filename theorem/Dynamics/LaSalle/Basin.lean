import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import theorem.Dynamics.LaSalle.Upstream
import theorem.Flow.Certificate
import theorem.Dynamics.Calculus
import theorem.Dynamics.Locality

/-! # Regions of attraction and LaSalle estimates

Region-of-attraction estimates from LaSalle's invariance principle, for `C¹` fields without the
global Lipschitz hypothesis of the upstream theorem.

Scope.
* Autonomous continuous-time ODE `ẋ = f x` on `Dynamics.State n = EuclideanSpace ℝ (Fin n)` (the
  complete closed-loop field supplied by the caller); no input, delay, switching, or
  time-variation. Solutions are `IsIntegralCurveOn` curves on `[0, ∞)` (one-sided derivative at
  `0`). `V̇ x = fderiv ℝ V x (f x)`.
* Every theorem here is a generic implication about an arbitrary field `f` (and function `V`); no
  model family is defined or fixed, so they are foundation results (Rules §3). The semantic
  predicates are the Flow / LeanForControl ones: `IsPositivelyInvariant`, `IsTrajectoryOn`,
  `LocalAsymptoticStable` from LeanForControl, `Flow.ForwardComplete` and
  `Flow.GloballyAsymptoticallyStable` (equilibrium, forward completeness and LeanForControl's
  `GlobalAsymptoticStable`) from `theorem/Flow/Defs.lean`; forward completeness of a globally
  Lipschitz field is `Flow.forwardComplete_of_lipschitzWith`.
* A region-of-attraction estimate is outside the sentence language of the library (a basin is a
  set of initial states, not a sentence about the equilibrium); model families that use it keep
  their conclusions as connection statements on the sentences it implies, or as private
  implementation evidence.

Source: work-sync `theory/T-lyapunov-function-method.md` §1.4 (LaSalle invariance principle);
interface for later work-sync formalizations (PLL potential-well basins, equal-area estimates);
LaSalle from LeanForControl (Khalil, *Nonlinear Systems*, 3rd ed., Theorem 4.4).

Results.
* Region-of-attraction estimate. "**`S` is contained in the region of attraction** of `x_eq`"
  is written out in every statement as
  `∀ x₀ ∈ S, (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
    ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
      Tendsto φ atTop (𝓝 x_eq)`:
  from every initial state in `S` a forward solution on `[0, ∞)` exists, and *every* forward
  solution from such an initial state converges to `x_eq`. The region of attraction itself, the
  largest such set, is `{x₀ | ∀ x ∈ ({x₀} : Set ℝⁿ), …}` (the same condition for the singleton
  `{x₀}`; `regionOfAttraction_iff_subset`). No stability (in the sense of Lyapunov) and no
  equilibrium property of `x_eq` is part of this condition. (Behaviour is defined only in the
  semantic layer, `theorem/Flow/Defs.lean`, so the condition is not a definition; the lemmas
  `RegionOfAttraction.mono`, `.union`, `.tendsto` are applied by full name.)
* `lasalle_invariance_principle_of_contDiff`: LaSalle's principle for a `C¹` field **without**
  the global Lipschitz hypothesis of the upstream theorem; the field is globalized by a smooth
  cutoff that agrees with it near the compact set `Ω`.
* `regionOfAttraction_of_lasalle`: `Ω` compact and positively invariant, `V̇ ≤ 0` on `Ω`, and
  every positively invariant subset of `{x ∈ Ω | V̇ x = 0}` contained in `{x_eq}` ⇒
  `Ω` lies in the region of attraction of `x_eq`.
* `regionOfAttraction_of_lasalle_sublevel`: the usual "potential-well" form. If `W` is open,
  `V̇ ≤ 0` on `W` and `Ω = {x ∈ W | V x ≤ c}` is compact, then `Ω` is automatically positively
  invariant (`isPositivelyInvariant_sublevel_of_isOpen`), so only the LaSalle condition remains.
* `lasalle_condition_of_trajectories`, `lasalle_condition_of_lieDeriv`: practical ways to
  discharge the LaSalle condition (no solution can stay in `E` except at `x_eq`; or `E` lies in
  the zero set of a `C¹` function `h` whose derivative along `f` vanishes on `E` only at `x_eq`).
* Links: `LocalAsymptoticStable` plus forward completeness gives a ball inside the region of
  attraction; `GloballyAsymptoticallyStable` puts the whole space `univ` in the region of
  attraction.
-/

noncomputable section
namespace powerlib.Dynamics.LaSalle
open Set Filter Topology Metric
open scoped Pointwise
variable {n : ℕ}
local notation "ℝⁿ" => State n

/-! ## Region-of-attraction estimates: elementary properties -/

/-- `S` is contained in the region of attraction of `x_eq` for `ẋ = f x` (left side: from every
initial state in `S` a forward solution exists, and every forward solution from it converges to
`x_eq`) iff `S` is a subset of the region of attraction of `x_eq` (right side: the set of initial
states `x₀` for which the same condition holds on the singleton `{x₀}`; the largest set
satisfying the condition). -/
@[powerlib_foundation] theorem regionOfAttraction_iff_subset {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {S : Set ℝⁿ} :
    (∀ x₀ ∈ S,
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq)) ↔
    S ⊆ {x₀ | ∀ x ∈ ({x₀} : Set ℝⁿ),
      (∃ φ : ℝ → ℝⁿ, φ 0 = x ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq)} := by
  constructor
  · intro h x hx y hy
    rw [mem_singleton_iff] at hy
    subst hy
    exact h y hx
  · intro h x hx
    exact h hx x (mem_singleton x)

/-- Monotonicity: a subset of a set in the region of attraction is in the region of attraction. -/
@[powerlib_foundation] theorem RegionOfAttraction.mono {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {S T : Set ℝⁿ}
    (h : ∀ x₀ ∈ S,
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq)) (hTS : T ⊆ S) :
    ∀ x₀ ∈ T,
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq) :=
  fun x hx => h x (hTS hx)

/-- The empty set lies in the region of attraction. -/
@[powerlib_foundation] theorem regionOfAttraction_empty (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    ∀ x₀ ∈ (∅ : Set ℝⁿ),
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq) :=
  fun _ hx => absurd hx (notMem_empty _)

/-- The region of attraction `{x₀ | the condition holds on {x₀}}` lies in the region of
attraction. -/
@[powerlib_foundation] theorem regionOfAttraction_regionOfAttraction (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    ∀ x₀ ∈ {x₀ | ∀ x ∈ ({x₀} : Set ℝⁿ),
        (∃ φ : ℝ → ℝⁿ, φ 0 = x ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
        ∀ φ : ℝ → ℝⁿ, φ 0 = x → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
          Tendsto φ atTop (𝓝 x_eq)},
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq) :=
  regionOfAttraction_iff_subset.2 subset_rfl

/-- The union of two sets in the region of attraction is in the region of attraction. -/
@[powerlib_foundation] theorem RegionOfAttraction.union {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {S T : Set ℝⁿ}
    (hS : ∀ x₀ ∈ S,
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq))
    (hT : ∀ x₀ ∈ T,
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq)) :
    ∀ x₀ ∈ S ∪ T,
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq) :=
  fun x hx => hx.elim (hS x) (hT x)

/-- Time invariance: if `S` lies in the region of attraction, a forward solution on `[t₀, ∞)`
that starts in `S` converges. -/
@[powerlib_foundation] theorem RegionOfAttraction.tendsto {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {S : Set ℝⁿ}
    (h : ∀ x₀ ∈ S,
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq))
    {t₀ : ℝ} {φ : ℝ → ℝⁿ}
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici t₀)) (hφ0 : φ t₀ ∈ S) :
    Tendsto φ atTop (𝓝 x_eq) := by
  have hψ : IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Ici 0) := by
    have hset : -t₀ +ᵥ Ici t₀ = Ici (0 : ℝ) := by
      ext x
      simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, mem_Ici]
      constructor <;> intro h <;> linarith
    have h' := _root_.IsIntegralCurveOn.comp_add_autonomous hφ t₀
    rwa [hset] at h'
  have hconv := (h _ hφ0).2 (fun s => φ (s + t₀)) (by simp) hψ
  exact Tendsto.congr (fun x => by simp)
    (hconv.comp (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id))

/-! ## Local tools: cutoff, curve transfer, continuous induction -/

/-- Positive invariance transfers to any field that agrees with `f` on an open neighbourhood
`U` of the closed set `Ω`. -/
@[powerlib_foundation] theorem IsPositivelyInvariant.of_eqOn_isOpen {f g : ℝⁿ → ℝⁿ}
    {Ω U : Set ℝⁿ} (hΩ : IsClosed Ω) (hU : IsOpen U) (hΩU : Ω ⊆ U)
    (hfg : ∀ x ∈ U, g x = f x) (hinv : IsPositivelyInvariant Ω f) :
    IsPositivelyInvariant Ω g := by
  intro t₀ t₁ ψ hψ hψ0
  refine forall_mem_Icc_of_local_step hψ.continuousOn hΩ hψ0 ?_
  intro x hx hxΩ
  obtain ⟨y, hxy, hyt, hy⟩ := exists_Icc_mem_of_isOpen hψ.continuousOn hU hx (hΩU hxΩ)
  have hseg : IsIntegralCurveOn ψ (fun _ z => f z) (Icc x y) :=
    isIntegralCurveOn_of_eq_on_curve
      (hψ.mono (Icc_subset_Icc hx.1 hyt)) (fun t ht => hfg _ (hy t ht))
  exact ⟨y, hxy, fun t ht => hinv x y ψ hseg hxΩ t (Ioo_subset_Icc_self ht)⟩

/-- **Potential-well invariance.** If `V̇ ≤ 0` on an open set `W` and
`{x ∈ W | V x ≤ c}` is closed, then this set is positively invariant. -/
@[powerlib_foundation] theorem isPositivelyInvariant_sublevel_of_isOpen {f : ℝⁿ → ℝⁿ}
    {V : ℝⁿ → ℝ} {W : Set ℝⁿ} {c : ℝ} (hW : IsOpen W) (hV : Differentiable ℝ V)
    (hLie : ∀ x ∈ W, fderiv ℝ V x (f x) ≤ 0) (hclosed : IsClosed {x ∈ W | V x ≤ c}) :
    IsPositivelyInvariant {x ∈ W | V x ≤ c} f := by
  intro t₀ t₁ ψ hψ hψ0
  refine forall_mem_Icc_of_local_step hψ.continuousOn hclosed hψ0 ?_
  rintro x hx ⟨hxW, hxV⟩
  obtain ⟨y, hxy, hyt, hy⟩ := exists_Icc_mem_of_isOpen hψ.continuousOn hW hx hxW
  have hseg : IsIntegralCurveOn ψ (fun _ z => f z) (Icc x y) :=
    hψ.mono (Icc_subset_Icc hx.1 hyt)
  have hanti : AntitoneOn (V ∘ ψ) (Icc x y) :=
    antitoneOn_V_comp_traj hV hV.continuous (convex_Icc x y) hseg
      (fun t ht => hLie _ (hy t (interior_subset ht)))
  refine ⟨y, hxy, fun t ht => ⟨hy t (Ioo_subset_Icc_self ht), ?_⟩⟩
  have := hanti ⟨le_rfl, hxy.le⟩ (Ioo_subset_Icc_self ht) ht.1.le
  exact (show V (ψ t) ≤ V (ψ x) from this).trans hxV

/-- Globalization of a `C¹` field around a compact positively invariant set. -/
@[powerlib_foundation] theorem exists_globalization {f : ℝⁿ → ℝⁿ} {Ω : Set ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hΩ_compact : IsCompact Ω) (hΩ_inv : IsPositivelyInvariant Ω f) :
    ∃ g : ℝⁿ → ℝⁿ, ContDiff ℝ 1 g ∧ (∃ K, LipschitzWith K g) ∧ (∀ x ∈ Ω, g x = f x) ∧
      IsPositivelyInvariant Ω g ∧
      (∀ N ⊆ Ω, IsPositivelyInvariant N g → IsPositivelyInvariant N f) ∧
      (∀ {φ : ℝ → ℝⁿ}, IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) → φ 0 ∈ Ω →
        IsIntegralCurveOn φ (fun _ x => g x) (Ici 0)) ∧
      (∀ {φ : ℝ → ℝⁿ}, IsIntegralCurveOn φ (fun _ x => g x) (Ici 0) → φ 0 ∈ Ω →
        IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) := by
  obtain ⟨R, hR⟩ := hΩ_compact.isBounded.subset_ball (0 : ℝⁿ)
  obtain ⟨g, hg, hglip, hgf⟩ := exists_contDiff_lipschitz_extension hf R
  have hgfU : ∀ x ∈ ball (0 : ℝⁿ) R, g x = f x := fun x hx =>
    hgf x (by rw [mem_ball, dist_zero_right] at hx; exact hx.le)
  have hgfΩ : ∀ x ∈ Ω, g x = f x := fun x hx => hgfU x (hR hx)
  have hΩ_inv_g : IsPositivelyInvariant Ω g :=
    IsPositivelyInvariant.of_eqOn_isOpen hΩ_compact.isClosed isOpen_ball hR hgfU hΩ_inv
  refine ⟨g, hg, hglip, hgfΩ, hΩ_inv_g, ?_, ?_, ?_⟩
  · intro N hNΩ hN t₀ t₁ ψ hψ hψ0 t ht
    have hstay : ∀ s ∈ Icc t₀ t₁, ψ s ∈ Ω := hΩ_inv t₀ t₁ ψ hψ (hNΩ hψ0)
    exact hN t₀ t₁ ψ
      (isIntegralCurveOn_of_eq_on_curve hψ fun s hs => (hgfΩ _ (hstay s hs)).symm) hψ0 t ht
  · intro φ hφ hφ0
    apply isIntegralCurveOn_of_eq_on_curve hφ
    intro t ht
    exact (hgfΩ _ (hΩ_inv 0 t φ (hφ.mono Icc_subset_Ici_self) hφ0 t ⟨ht, le_rfl⟩)).symm
  · intro φ hφ hφ0
    apply isIntegralCurveOn_of_eq_on_curve hφ
    intro t ht
    exact hgfΩ _ (hΩ_inv_g 0 t φ (hφ.mono Icc_subset_Ici_self) hφ0 t ⟨ht, le_rfl⟩)

/-! ## LaSalle without a global Lipschitz hypothesis -/

/-- LaSalle's invariance principle for a `C¹` field; the global Lipschitz hypothesis of the
upstream `_root_.lasalle_invariance_principle` is removed by a cutoff. -/
@[powerlib_foundation] theorem lasalle_invariance_principle_of_contDiff
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω M : Set ℝⁿ}
    (hΩ_compact : IsCompact Ω) (hΩ_inv : IsPositivelyInvariant Ω f)
    (hf_c1 : ContDiff ℝ 1 f) (hV_c1 : ContDiff ℝ 1 V)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) (hφ0 : φ 0 ∈ Ω)
    (hM : ∀ N ⊆ LieDerivZeroSet f V Ω, IsPositivelyInvariant N f → N ⊆ M) :
    Tendsto φ atTop (𝓝ˢ M) := by
  obtain ⟨g, hg, ⟨K, hglip⟩, hgfΩ, hΩ_inv_g, hback, hfwd, -⟩ :=
    exists_globalization hf_c1 hΩ_compact hΩ_inv
  have hE : LieDerivZeroSet g V Ω = LieDerivZeroSet f V Ω := by
    ext x
    simp only [lieDerivZeroSet_def, mem_sep_iff]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, by rw [← hgfΩ x hx]; exact h⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, by rw [hgfΩ x hx]; exact h⟩
  refine lasalle_invariance_principle hΩ_compact hΩ_inv_g hglip hg hV_c1
    (fun x hx => by rw [hgfΩ x hx]; exact hLie x hx) (hfwd hφ hφ0) hφ0 ?_
  intro N hN hNinv
  rw [hE] at hN
  exact hM N hN (hback N (fun x hx => (hN hx).1) hNinv)

/-! ## Regions of attraction from LaSalle -/

/-- **LaSalle region-of-attraction estimate.** `Ω` compact and positively invariant,
`V̇ ≤ 0` on `Ω`, and every positively invariant subset of `{x ∈ Ω | V̇ x = 0}` contained in
`{x_eq}` ⇒ `Ω` lies in the region of attraction of `x_eq`. -/
@[powerlib_foundation] theorem regionOfAttraction_of_lasalle
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ} {x_eq : ℝⁿ}
    (hΩ_compact : IsCompact Ω) (hΩ_inv : IsPositivelyInvariant Ω f)
    (hf_c1 : ContDiff ℝ 1 f) (hV_c1 : ContDiff ℝ 1 V)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    (hLasalle : ∀ N ⊆ LieDerivZeroSet f V Ω, IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    ∀ x₀ ∈ Ω,
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq) := by
  obtain ⟨g, -, ⟨K, hglip⟩, -, -, -, -, hgf⟩ := exists_globalization hf_c1 hΩ_compact hΩ_inv
  intro x₀ hx₀
  refine ⟨?_, fun φ hφ0 hφ => ?_⟩
  · obtain ⟨φ, hφ0, hφ⟩ := Flow.forwardComplete_of_lipschitzWith hglip 0 x₀
    exact ⟨φ, hφ0, hgf hφ (hφ0 ▸ hx₀)⟩
  · have h := lasalle_invariance_principle_of_contDiff hΩ_compact hΩ_inv hf_c1 hV_c1 hLie hφ
      (hφ0 ▸ hx₀) hLasalle
    rwa [nhdsSet_singleton] at h

/-- Same estimate with a globally Lipschitz field (the Lipschitz hypothesis is not needed:
`regionOfAttraction_of_lasalle`). -/
@[powerlib_foundation] theorem regionOfAttraction_of_lasalle_lipschitz
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ} {x_eq : ℝⁿ} {K : NNReal}
    (hΩ_compact : IsCompact Ω) (hΩ_inv : IsPositivelyInvariant Ω f)
    (_hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f) (hV_c1 : ContDiff ℝ 1 V)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    (hLasalle : ∀ N ⊆ LieDerivZeroSet f V Ω, IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    ∀ x₀ ∈ Ω,
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq) :=
  regionOfAttraction_of_lasalle hΩ_compact hΩ_inv hf_c1 hV_c1 hLie hLasalle

/-- **Potential-well estimate.** `W` open, `V̇ ≤ 0` on `W`, `Ω = {x ∈ W | V x ≤ c}` compact,
and the LaSalle condition on `Ω` ⇒ `Ω` lies in the region of attraction of `x_eq`.
Positive invariance of `Ω` is derived, not assumed. -/
@[powerlib_foundation] theorem regionOfAttraction_of_lasalle_sublevel
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {W : Set ℝⁿ} {c : ℝ} {x_eq : ℝⁿ}
    (hW : IsOpen W) (hf_c1 : ContDiff ℝ 1 f) (hV_c1 : ContDiff ℝ 1 V)
    (hLie : ∀ x ∈ W, fderiv ℝ V x (f x) ≤ 0)
    (hΩ_compact : IsCompact {x ∈ W | V x ≤ c})
    (hLasalle : ∀ N ⊆ LieDerivZeroSet f V {x ∈ W | V x ≤ c},
      IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    ∀ x₀ ∈ {x ∈ W | V x ≤ c},
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq) :=
  regionOfAttraction_of_lasalle hΩ_compact
    (isPositivelyInvariant_sublevel_of_isOpen hW (hV_c1.differentiable (by norm_num)) hLie
      hΩ_compact.isClosed)
    hf_c1 hV_c1 (fun x hx => hLie x hx.1) hLasalle

/-! ## Discharging the LaSalle condition -/

/-- If no solution segment of positive length can stay in `E` unless it starts at `x_eq`, then
every positively invariant subset of `E` is contained in `{x_eq}`. -/
@[powerlib_foundation] theorem lasalle_condition_of_trajectories {f : ℝⁿ → ℝⁿ} {E : Set ℝⁿ}
    {x_eq : ℝⁿ} (hf_c1 : ContDiff ℝ 1 f)
    (h : ∀ (T : ℝ) (φ : ℝ → ℝⁿ), 0 < T → IsTrajectoryOn φ f 0 T →
      (∀ t ∈ Icc 0 T, φ t ∈ E) → φ 0 = x_eq) :
    ∀ N ⊆ E, IsPositivelyInvariant N f → N ⊆ {x_eq} := by
  intro N hNE hN x hx
  obtain ⟨T, ψ, hT, hψ0, hψ⟩ := (hf_c1.contDiffAt (x := x)).exists_isIntegralCurveOn_Icc
  have hstay : ∀ t ∈ Icc 0 T, ψ t ∈ N := hN 0 T ψ hψ (hψ0 ▸ hx)
  rw [mem_singleton_iff, ← hψ0]
  exact h T ψ hT hψ fun t ht => hNE (hstay t ht)

/-- If `E` lies in the zero set of a `C¹` function `h`, and the derivative of `h` along `f`
vanishes at a point of `E` only at `x_eq`, then every positively invariant subset of `E` is
contained in `{x_eq}`. (Typical use: `E = {ω = 0} ∩ Ω` and `h = ω`.) -/
@[powerlib_foundation] theorem lasalle_condition_of_lieDeriv {f : ℝⁿ → ℝⁿ} {E : Set ℝⁿ}
    {x_eq : ℝⁿ} (hf_c1 : ContDiff ℝ 1 f) {h : ℝⁿ → ℝ} (hh : ContDiff ℝ 1 h)
    (hE : ∀ x ∈ E, h x = 0) (hpt : ∀ x ∈ E, fderiv ℝ h x (f x) = 0 → x = x_eq) :
    ∀ N ⊆ E, IsPositivelyInvariant N f → N ⊆ {x_eq} := by
  refine lasalle_condition_of_trajectories hf_c1 ?_
  intro T ψ hT hψ hstay
  have hmem0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hchain : HasDerivWithinAt (h ∘ ψ) (fderiv ℝ h (ψ 0) (f (ψ 0))) (Icc 0 T) 0 :=
    (hh.differentiable (by norm_num) (ψ 0)).hasFDerivAt.comp_hasDerivWithinAt 0 (hψ 0 hmem0)
  have hzero : HasDerivWithinAt (h ∘ ψ) 0 (Icc 0 T) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) _ (0 : ℝ)).congr (fun s hs => hE _ (hstay s hs))
      (hE _ (hstay 0 hmem0))
  exact hpt _ (hstay 0 hmem0) ((uniqueDiffOn_Icc hT 0 hmem0).eq_deriv _ hchain hzero)

/-! ## Links with asymptotic stability -/

/-- Local asymptotic stability plus forward completeness: some ball around `x_eq` lies in the
region of attraction. -/
@[powerlib_foundation] theorem exists_ball_regionOfAttraction_of_localAsymptoticStable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (h : LocalAsymptoticStable f x_eq) (hc : Flow.ForwardComplete f) :
    ∃ r > 0,
      ∀ x₀ ∈ ball x_eq r,
        (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
        ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
          Tendsto φ atTop (𝓝 x_eq) := by
  obtain ⟨-, r, hr, hconv⟩ := h
  refine ⟨r, hr, fun x₀ hx₀ => ⟨hc 0 x₀, fun φ hφ0 hφ => hconv 0 φ hφ ?_⟩⟩
  rw [hφ0, ← dist_eq_norm]
  exact hx₀

/-- Global asymptotic stability (with forward completeness): the whole state space lies in the
region of attraction. -/
@[powerlib_foundation] theorem regionOfAttraction_univ_of_globallyAsymptoticallyStable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (h : Flow.GloballyAsymptoticallyStable f x_eq) :
    ∀ x₀ ∈ (univ : Set ℝⁿ),
      (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
      ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
        Tendsto φ atTop (𝓝 x_eq) := by
  obtain ⟨-, hc, -, hconv⟩ := h
  exact fun x₀ _ => ⟨hc 0 x₀, fun φ _ hφ => hconv 0 φ hφ⟩

end powerlib.Dynamics.LaSalle
