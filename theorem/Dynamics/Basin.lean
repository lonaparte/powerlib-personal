import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import theorem.Upstream.LaSalle
import theorem.Flow.Certificate

/-! # Regions of attraction and LaSalle estimates

Model boundary. Autonomous continuous-time ODE `ẋ = f x` on
`Dynamics.State n = EuclideanSpace ℝ (Fin n)` (the complete closed-loop field supplied by the
caller); no input, delay, switching, or time-variation. Solutions are `IsIntegralCurveOn` curves
on `[0, ∞)` (one-sided derivative at `0`). `V̇ x = fderiv ℝ V x (f x)`.

* `RegionOfAttraction f x_eq S`: **`S` is contained in the region of attraction** of `x_eq`:
  from every initial state in `S` a forward solution on `[0, ∞)` exists, and *every* forward
  solution from such an initial state converges to `x_eq`. `regionOfAttraction f x_eq` is the
  largest such set. No stability (in the sense of Lyapunov) and no equilibrium property of
  `x_eq` is part of this predicate.
* `lasalle_invariance_principle_of_contDiff`: LaSalle's principle for a `C¹` field **without**
  the global Lipschitz hypothesis of the upstream theorem; the field is globalized by a smooth
  cutoff that agrees with it near the compact set `Ω`.
* `regionOfAttraction_of_lasalle`: `Ω` compact and positively invariant, `V̇ ≤ 0` on `Ω`, and
  every positively invariant subset of `{x ∈ Ω | V̇ x = 0}` contained in `{x_eq}` ⇒
  `RegionOfAttraction f x_eq Ω`.
* `regionOfAttraction_of_lasalle_sublevel`: the usual "potential-well" form. If `W` is open,
  `V̇ ≤ 0` on `W` and `Ω = {x ∈ W | V x ≤ c}` is compact, then `Ω` is automatically positively
  invariant (`isPositivelyInvariant_sublevel_of_isOpen`), so only the LaSalle condition remains.
* `lasalle_condition_of_trajectories`, `lasalle_condition_of_lieDeriv`: practical ways to
  discharge the LaSalle condition (no solution can stay in `E` except at `x_eq`; or `E` lies in
  the zero set of a `C¹` function `h` whose derivative along `f` vanishes on `E` only at `x_eq`).
* Links: `LocalAsymptoticStable` plus forward completeness gives a ball inside the region of
  attraction; `GloballyAsymptoticallyStable` gives `RegionOfAttraction f x_eq univ`.

Connection architecture. Every theorem here is a generic implication about an arbitrary field `f`
(and function `V`); no model family is defined or fixed, so they are foundation results
(Rules §3, port policy §4): the seven former `@[powerlib_domain]` labels are relabeled
`@[powerlib_foundation]`, with unchanged statements. The semantic predicates are the Flow /
LeanForControl ones: `IsPositivelyInvariant`, `IsTrajectoryOn`, `LocalAsymptoticStable` from
LeanForControl, `Flow.ForwardComplete` and `Flow.GloballyAsymptoticallyStable` (equilibrium,
forward completeness and LeanForControl's `GlobalAsymptoticStable`) from `theorem/Flow/Defs.lean`;
forward completeness of a globally Lipschitz field is `Flow.forwardComplete_of_lipschitzWith`.
`RegionOfAttraction` is a region-of-attraction estimate, outside the sentence language of the
library (a basin is a set of initial states, not a sentence about the equilibrium); model families
that use it keep their conclusions as connection statements on the sentences it implies, or as
private implementation evidence.

Source: interface for later work-sync formalizations (PLL potential-well basins, equal-area
estimates); LaSalle from LeanForControl (Khalil, *Nonlinear Systems*, 3rd ed., Theorem 4.4).
powerlib Phase 0, P0a.
-/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology Metric
open scoped Pointwise
variable {n : ℕ}
local notation "ℝⁿ" => State n

/-! ## Definition -/

/-- `S` is contained in the region of attraction of `x_eq` for `ẋ = f x`: from every initial
state in `S` a forward solution exists, and every forward solution from it converges to `x_eq`. -/
def RegionOfAttraction (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (S : Set ℝⁿ) : Prop :=
  ∀ x₀ ∈ S,
    (∃ φ : ℝ → ℝⁿ, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) ∧
    ∀ φ : ℝ → ℝⁿ, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
      Tendsto φ atTop (𝓝 x_eq)

/-- The region of attraction of `x_eq`: the largest set satisfying `RegionOfAttraction`. -/
def regionOfAttraction (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Set ℝⁿ :=
  {x₀ | RegionOfAttraction f x_eq {x₀}}

@[powerlib_foundation] theorem regionOfAttraction_iff_subset {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {S : Set ℝⁿ} : RegionOfAttraction f x_eq S ↔ S ⊆ regionOfAttraction f x_eq := by
  constructor
  · intro h x hx y hy
    rw [mem_singleton_iff] at hy
    subst hy
    exact h y hx
  · intro h x hx
    exact h hx x (mem_singleton x)

@[powerlib_foundation] theorem RegionOfAttraction.mono {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {S T : Set ℝⁿ} (h : RegionOfAttraction f x_eq S) (hTS : T ⊆ S) :
    RegionOfAttraction f x_eq T :=
  fun x hx => h x (hTS hx)

@[powerlib_foundation] theorem regionOfAttraction_empty (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    RegionOfAttraction f x_eq ∅ :=
  fun _ hx => absurd hx (notMem_empty _)

@[powerlib_foundation] theorem regionOfAttraction_regionOfAttraction (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    RegionOfAttraction f x_eq (regionOfAttraction f x_eq) :=
  regionOfAttraction_iff_subset.2 subset_rfl

@[powerlib_foundation] theorem RegionOfAttraction.union {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {S T : Set ℝⁿ} (hS : RegionOfAttraction f x_eq S) (hT : RegionOfAttraction f x_eq T) :
    RegionOfAttraction f x_eq (S ∪ T) := by
  rw [regionOfAttraction_iff_subset] at *
  exact union_subset hS hT

/-- Time invariance: a forward solution on `[t₀, ∞)` that starts in the set converges. -/
@[powerlib_foundation] theorem RegionOfAttraction.tendsto {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {S : Set ℝⁿ} (h : RegionOfAttraction f x_eq S) {t₀ : ℝ} {φ : ℝ → ℝⁿ}
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

/-- A `C¹` field agrees on `‖x‖ ≤ R` with a `C¹`, globally Lipschitz field. -/
@[powerlib_foundation] theorem exists_contDiff_lipschitz_extension {f : ℝⁿ → ℝⁿ}
    (hf : ContDiff ℝ 1 f) (R : ℝ) :
    ∃ g : ℝⁿ → ℝⁿ, ContDiff ℝ 1 g ∧ (∃ K, LipschitzWith K g) ∧
      ∀ x, ‖x‖ ≤ R → g x = f x := by
  let b : ContDiffBump (0 : ℝⁿ) :=
    ⟨max R 1, max R 1 + 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), by linarith⟩
  have hsmooth : ContDiff ℝ 1 (fun x => b x • f x) := b.contDiff.smul hf
  refine ⟨fun x => b x • f x, hsmooth, ?_, ?_⟩
  · exact ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport.smul_right hsmooth
      (by norm_num)
  · intro x hx
    have hb : b x = 1 := by
      apply b.one_of_mem_closedBall
      rw [mem_closedBall, dist_zero_right]
      exact hx.trans (le_max_left _ _)
    simp only [hb, one_smul]

@[powerlib_foundation] theorem isIntegralCurveOn_of_eq_on_curve {f g : ℝⁿ → ℝⁿ}
    {ψ : ℝ → ℝⁿ} {s : Set ℝ} (hψ : IsIntegralCurveOn ψ (fun _ x => g x) s)
    (h : ∀ t ∈ s, g (ψ t) = f (ψ t)) : IsIntegralCurveOn ψ (fun _ x => f x) s := by
  intro t ht
  show HasDerivWithinAt ψ (f (ψ t)) s t
  rw [← h t ht]
  exact hψ t ht

/-- Continuous induction on `[t₀, t₁]` for a closed target set. -/
@[powerlib_foundation] theorem forall_mem_Icc_of_local_step {ψ : ℝ → ℝⁿ} {Ω : Set ℝⁿ}
    {t₀ t₁ : ℝ} (hψ : ContinuousOn ψ (Icc t₀ t₁)) (hΩ : IsClosed Ω) (h0 : ψ t₀ ∈ Ω)
    (hstep : ∀ x ∈ Ico t₀ t₁, ψ x ∈ Ω → ∃ y, x < y ∧ ∀ t ∈ Ioo x y, ψ t ∈ Ω) :
    ∀ t ∈ Icc t₀ t₁, ψ t ∈ Ω := by
  have hs : IsClosed ((ψ ⁻¹' Ω) ∩ Icc t₀ t₁) := by
    rw [inter_comm]
    exact hψ.preimage_isClosed_of_isClosed isClosed_Icc hΩ
  have hsub := hs.Icc_subset_of_forall_mem_nhdsWithin (s := ψ ⁻¹' Ω) h0 (by
    rintro x ⟨hx, hxI⟩
    obtain ⟨y, hxy, hy⟩ := hstep x hxI hx
    exact mem_of_superset (Ioo_mem_nhdsGT hxy) hy)
  exact fun t ht => hsub ht

/-- A curve continuous on `[t₀, t₁]` that is in an open set at `x ∈ [t₀, t₁)` stays in it on
some `[x, y]` with `x < y ≤ t₁`. -/
@[powerlib_foundation] theorem exists_Icc_mem_of_isOpen {ψ : ℝ → ℝⁿ} {U : Set ℝⁿ}
    {t₀ t₁ x : ℝ} (hψ : ContinuousOn ψ (Icc t₀ t₁)) (hU : IsOpen U) (hx : x ∈ Ico t₀ t₁)
    (hxU : ψ x ∈ U) : ∃ y, x < y ∧ y ≤ t₁ ∧ ∀ t ∈ Icc x y, ψ t ∈ U := by
  have hIcc : Icc t₀ t₁ ∈ 𝓝[>] x :=
    mem_of_superset (Ioo_mem_nhdsGT hx.2) fun t ht => ⟨hx.1.trans ht.1.le, ht.2.le⟩
  have hpre : ψ ⁻¹' U ∈ 𝓝[>] x :=
    nhdsWithin_le_of_mem hIcc
      ((hψ x (Ico_subset_Icc_self hx)).preimage_mem_nhdsWithin (hU.mem_nhds hxU))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hpre
  have hxu : x < u := hu
  refine ⟨min ((x + u) / 2) t₁, lt_min (by linarith) hx.2, min_le_right _ _, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hlt
  · exact hxU
  · apply hsub
    exact ⟨hlt, lt_of_le_of_lt (ht.2.trans (min_le_left _ _)) (by linarith)⟩

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
    RegionOfAttraction f x_eq Ω := by
  obtain ⟨g, -, ⟨K, hglip⟩, -, -, -, -, hgf⟩ := exists_globalization hf_c1 hΩ_compact hΩ_inv
  intro x₀ hx₀
  refine ⟨?_, fun φ hφ0 hφ => ?_⟩
  · obtain ⟨φ, hφ0, hφ⟩ := Flow.forwardComplete_of_lipschitzWith hglip 0 x₀
    exact ⟨φ, hφ0, hgf hφ (hφ0 ▸ hx₀)⟩
  · have h := lasalle_invariance_principle_of_contDiff hΩ_compact hΩ_inv hf_c1 hV_c1 hLie hφ
      (hφ0 ▸ hx₀) hLasalle
    rwa [nhdsSet_singleton] at h

/-- Same estimate with a globally Lipschitz field (direct use of the upstream theorem). -/
@[powerlib_foundation] theorem regionOfAttraction_of_lasalle_lipschitz
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ} {x_eq : ℝⁿ} {K : NNReal}
    (hΩ_compact : IsCompact Ω) (hΩ_inv : IsPositivelyInvariant Ω f)
    (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f) (hV_c1 : ContDiff ℝ 1 V)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    (hLasalle : ∀ N ⊆ LieDerivZeroSet f V Ω, IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    RegionOfAttraction f x_eq Ω := by
  intro x₀ hx₀
  refine ⟨?_, fun φ hφ0 hφ => ?_⟩
  · obtain ⟨φ, hφ0, hφ⟩ := Flow.forwardComplete_of_lipschitzWith hf_lip 0 x₀
    exact ⟨φ, hφ0, hφ⟩
  · have h := lasalle_invariance_principle hΩ_compact hΩ_inv hf_lip hf_c1 hV_c1 hLie hφ
      (hφ0 ▸ hx₀) hLasalle
    rwa [nhdsSet_singleton] at h

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
    RegionOfAttraction f x_eq {x ∈ W | V x ≤ c} :=
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
    ∃ r > 0, RegionOfAttraction f x_eq (ball x_eq r) := by
  obtain ⟨-, r, hr, hconv⟩ := h
  refine ⟨r, hr, fun x₀ hx₀ => ⟨hc 0 x₀, fun φ hφ0 hφ => hconv 0 φ hφ ?_⟩⟩
  rw [hφ0, ← dist_eq_norm]
  exact hx₀

/-- Global asymptotic stability (with forward completeness): the whole state space lies in the
region of attraction. -/
@[powerlib_foundation] theorem regionOfAttraction_univ_of_globallyAsymptoticallyStable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (h : Flow.GloballyAsymptoticallyStable f x_eq) :
    RegionOfAttraction f x_eq univ := by
  obtain ⟨-, hc, -, hconv⟩ := h
  exact fun x₀ _ => ⟨hc 0 x₀, fun φ _ hφ => hconv 0 φ hφ⟩

end powerlib.Dynamics
