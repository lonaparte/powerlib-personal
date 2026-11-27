import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import theorem.Attributes

/-! # The centre manifold of a map: the invariant Lipschitz graph by the graph transform

A map in centre–stable form `F(x, y) = (A x + f(x, y), B y + g(x, y))` on `X × Y`, whose linear
part does not contract the centre direction faster than `a` (`a ‖x‖ ≤ ‖A x‖`) and contracts the
stable direction at least by `b < a` (`‖B y‖ ≤ b ‖y‖`), with nonlinearities `f`, `g` vanishing at
`0` and globally `ε`-Lipschitz, `b + 3ε < a`, has exactly one invariant graph `y = h(x)` with
`h(0) = 0` and `Lip h ≤ 1`; the reduced map on it is `r(x) = A x + f(x, h(x))`, and every orbit
approaches the graph geometrically: `‖y_k − h(x_k)‖ ≤ (b + 2ε)^k ‖y_0 − h(x_0)‖`. With `a = 1`
(an isometric or non-contracting centre part, a critical multiplier `±1`) and `b < 1` this is the
centre manifold of a map; a cut-off makes nonlinearities that are merely flat at `0` (strict
derivative `0`) globally `ε`-Lipschitz without changing them near `0`, so the theorem gives a
locally invariant, locally attracting Lipschitz centre manifold of the original map.

The graph transform `Γ` sends `h` to the graph function of the image of `graph h`: the centre
component `x ↦ A x + f(x, h x)` along a `1`-Lipschitz graph is a bi-Lipschitz bijection of `X`
(a Banach contraction solves `A x + f(x, h x) = z`), and `(Γ h)(A x + f(x, h x)) = B h(x) +
g(x, h(x))`. `Γ` keeps the graphs with `h(0) = 0`, `Lip h ≤ 1` (`b + 2ε ≤ a`), and contracts the
weighted distance `sup_x ‖h₁ x − h₂ x‖ / ‖x‖` by `κ = a(b + ε)/(a − ε)² < 1`; the invariant graph
is the pointwise limit of `Γᵏ 0`.

Scope.
* Real normed spaces `X` (complete), `Y` (complete for the existence); `X × Y` carries the max
  norm. `A : X →L[ℝ] X` surjective with `a ‖x‖ ≤ ‖A x‖`, `B : Y →L[ℝ] Y` with `‖B y‖ ≤ b ‖y‖`,
  `0 ≤ b`; `f : X × Y → X`, `g : X × Y → Y` with `f 0 = 0`, `g 0 = 0`, `LipschitzWith ε`;
  `b + 3ε < a`. No finite dimension, no smoothness of `F`: the graph is Lipschitz, and its
  uniqueness is among all `1`-Lipschitz graphs through `0` (no boundedness).
* Invariance is the static equation `h(A x + f(x, h x)) = B h(x) + g(x, h(x))` (the image of a
  graph point is a graph point, and the reduced map is onto); attraction is a one-step estimate
  iterated along orbits. No notion quantifies over time.
* The local form: for `f₀`, `g₀` with strict derivative `0` at `0`, the cut-off `f₀ ∘ π_ρ` with the
  radial retraction `π_ρ` onto the closed ball (`ballRetract`, `2`-Lipschitz in every normed
  space) agrees with `f₀` on `‖p‖ ≤ ρ`; local invariance and attraction hold for orbits of the
  original map that stay in that ball. Local centre manifolds are not unique; the one built here
  is the unique invariant graph of the cut-off map.
* Generic; nothing here describes a physical system (foundation). The reduction principle and the
  approximation theorem are `theorem/Map/CenterReduction.lean`.

Source: the graph-transform proof of the centre manifold theorem for maps: Hirsch, Pugh and
Shub, *Invariant Manifolds* (LNM 583, 1977) (the graph transform); Carr, *Applications of Centre
Manifold Theory* (1981), Ch. 2 (Theorem 1 and its version for maps); Iooss, *Bifurcation of Maps
and Applications* (1979); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §5.1
(the centre manifold of a fixed point of a map); the flow counterpart is the Lyapunov–Perron
construction (Vanderbauwhede, "Centre manifolds, normal forms and elementary bifurcations",
1989). Required by `theorem/Periodic/CriticalMultiplier.lean` (Scope: a
periodic orbit with a simple critical multiplier and a stable complement needs the centre-manifold
reduction).

Results.
* Maps: `splitMap` (`F`), `reducedMap` (`x ↦ A x + f(x, h x)`), `graphTransform` (`Γ`),
  `centreGraph` (the pointwise limit of `Γᵏ 0`).
* Along a graph: `norm_graph_sub` (`‖(x, h x) − (x', h x')‖ = ‖x − x'‖` for `Lip h ≤ 1`),
  `norm_graph`,
  `reducedMap_sub_le`, `le_norm_reducedMap_sub` (`(a − ε)‖x − x'‖ ≤ ‖r x − r x'‖`),
  `reducedMap_surjective`, `reducedMap_bijective`, `reducedMap_zero`, `norm_reducedMap_le`.
* The transform: `graphTransform_reducedMap` (`(Γ h)(r x) = B h(x) + g(x, h(x))`),
  `graphTransform_zero`, `lipschitzWith_graphTransform`, `norm_graphTransform_sub_le` (the
  weighted contraction by `κ`), `contraction_lt_one` (`0 ≤ κ < 1` from `b + 3ε < a`),
  `graphTransform_eq_self_iff` (fixed points of `Γ` are the invariant graphs),
  `graphTransform_mem` (values in a submodule invariant under `B` and `g`).
* **The theorem** `exists_unique_invariantGraph`: one and only one `1`-Lipschitz `h` with
  `h(0) = 0` and `h(A x + f(x, h x)) = B h(x) + g(x, h(x))`; `centreGraph_spec` (it is
  `centreGraph`), `centreGraph_mem` (it takes values in every closed submodule invariant under
  `B` and `g`), `splitMap_graph` (graph points go to graph points).
* Attraction: `norm_splitMap_sub_graph_le` (one step: `‖y' − h x'‖ ≤ (b + 2ε)‖y − h x‖`),
  `norm_iterate_sub_graph_le` (`(b + 2ε)^k` along every orbit).
* Cut-off: `ballRetract`, `ballRetract_of_norm_le`, `norm_ballRetract_le`,
  `lipschitzWith_ballRetract`, `exists_lipschitz_cutoff` (a map with strict derivative `0` at `0`
  agrees near `0` with an `ε`-Lipschitz map, for every `ε > 0`).
* The local theorem `exists_local_centreManifold`: for `f₀`, `g₀` with strict derivative `0` at
  `0` and every `ε > 0` with `b + 3ε < a`, a radius `ρ`, cut-offs `f`, `g` equal to `f₀`, `g₀` on
  `‖p‖ ≤ ρ`, and their invariant graph `h`; orbits of the original map that stay in that ball
  approach the graph at the rate `(b + 2ε)^k`, and the graph is invariant there.

Corrections.
None: an extension (the centre manifold of a fixed point of a map, which the critical-multiplier
analysis of `theorem/Periodic/CriticalMultiplier.lean` left out).

Family and connection conclusions.
None: static evidence on maps of normed spaces.
-/

noncomputable section

namespace powerlib.Map.CenterManifold

open Filter Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The map in centre–stable form: `(x, y) ↦ (A x + f(x, y), B y + g(x, y))`. -/
def splitMap (A : X →L[ℝ] X) (B : Y →L[ℝ] Y) (f : X × Y → X) (g : X × Y → Y) (p : X × Y) :
    X × Y :=
  (A p.1 + f p, B p.2 + g p)

/-- The centre component along the graph of `h`, `x ↦ A x + f(x, h x)`; on an invariant graph it
is the reduced (restricted) map. -/
def reducedMap (A : X →L[ℝ] X) (f : X × Y → X) (h : X → Y) (x : X) : X := A x + f (x, h x)

/-- The graph transform: the graph of `h` is carried by `splitMap` onto the graph of
`graphTransform h`, `(Γ h)(z) = B h(x) + g(x, h x)` for the preimage `x` of `z` under the reduced
map. -/
def graphTransform (A : X →L[ℝ] X) (B : Y →L[ℝ] Y) (f : X × Y → X) (g : X × Y → Y) (h : X → Y)
    (z : X) : Y :=
  B (h (Function.invFun (reducedMap A f h) z)) +
    g (Function.invFun (reducedMap A f h) z, h (Function.invFun (reducedMap A f h) z))

/-- The candidate centre manifold: the pointwise limit of the iterated graph transform from the
zero graph. -/
def centreGraph (A : X →L[ℝ] X) (B : Y →L[ℝ] Y) (f : X × Y → X) (g : X × Y → Y) (x : X) : Y :=
  limUnder atTop fun k : ℕ => (graphTransform A B f g)^[k] 0 x

/-! ## Along a `1`-Lipschitz graph -/

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
/-- Along a `1`-Lipschitz graph the max norm of `X × Y` sees only the centre coordinate. -/
@[tmio T, powerlib_foundation] theorem norm_graph_sub {h : X → Y} (hh : LipschitzWith 1 h)
    (x x' : X) : ‖(x, h x) - (x', h x')‖ = ‖x - x'‖ := by
  rw [Prod.mk_sub_mk, Prod.norm_mk]
  have := hh.norm_sub_le x x'
  simp only [NNReal.coe_one, one_mul] at this
  exact max_eq_left this

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
/-- The norm of a graph point is the norm of its centre coordinate. -/
@[tmio T, powerlib_foundation] theorem norm_graph {h : X → Y} (hh : LipschitzWith 1 h)
    (hh0 : h 0 = 0) (x : X) : ‖(x, h x)‖ = ‖x‖ := by
  have := norm_graph_sub hh x 0
  rw [hh0, Prod.mk_zero_zero] at this
  simpa using this

variable {A : X →L[ℝ] X} {B : Y →L[ℝ] Y} {f : X × Y → X} {g : X × Y → Y} {a b : ℝ} {ε : NNReal}

omit [NormedSpace ℝ Y] in
/-- The reduced map differs from `A` by an `ε`-Lipschitz term. -/
@[tmio T, powerlib_foundation] theorem reducedMap_sub_le (hf : LipschitzWith ε f) {h : X → Y}
    (hh : LipschitzWith 1 h) (x x' : X) :
    ‖reducedMap A f h x - reducedMap A f h x' - A (x - x')‖ ≤ ε * ‖x - x'‖ := by
  have e : reducedMap A f h x - reducedMap A f h x' - A (x - x') = f (x, h x) - f (x', h x') := by
    simp only [reducedMap, map_sub]; abel
  rw [e, ← norm_graph_sub hh x x']
  exact hf.norm_sub_le _ _

omit [NormedSpace ℝ Y] in
/-- The reduced map expands distances at least by `a − ε`. -/
@[tmio T, powerlib_foundation] theorem le_norm_reducedMap_sub (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖)
    (hf : LipschitzWith ε f) {h : X → Y} (hh : LipschitzWith 1 h) (x x' : X) :
    (a - ε) * ‖x - x'‖ ≤ ‖reducedMap A f h x - reducedMap A f h x'‖ := by
  have h1 := reducedMap_sub_le (A := A) hf hh x x'
  have h2 := hA (x - x')
  have h3 := norm_sub_norm_le (A (x - x')) (A (x - x') - (reducedMap A f h x - reducedMap A f h x'))
  rw [sub_sub_cancel] at h3
  have h4 : ‖A (x - x') - (reducedMap A f h x - reducedMap A f h x')‖ ≤ ε * ‖x - x'‖ := by
    rw [norm_sub_rev]; exact h1
  nlinarith

omit [NormedSpace ℝ Y] in
/-- The reduced map fixes `0`. -/
@[tmio T, powerlib_foundation] theorem reducedMap_zero (hf0 : f 0 = 0) {h : X → Y} (hh0 : h 0 = 0) :
    reducedMap A f h 0 = 0 := by
  show A 0 + f (0, h 0) = 0
  rw [map_zero, hh0, zero_add]
  exact hf0

omit [NormedSpace ℝ Y] in
/-- The reduced map is bounded linearly: `‖r x‖ ≤ (‖A‖ + ε) ‖x‖`. -/
@[tmio T, powerlib_foundation] theorem norm_reducedMap_le (hf : LipschitzWith ε f) (hf0 : f 0 = 0)
    {h : X → Y} (hh : LipschitzWith 1 h) (hh0 : h 0 = 0) (x : X) :
    ‖reducedMap A f h x‖ ≤ (‖A‖ + ε) * ‖x‖ := by
  have h1 := reducedMap_sub_le (A := A) hf hh x 0
  rw [reducedMap_zero hf0 hh0] at h1
  simp only [sub_zero] at h1
  calc ‖reducedMap A f h x‖ = ‖(reducedMap A f h x - A x) + A x‖ := by rw [sub_add_cancel]
    _ ≤ ‖reducedMap A f h x - A x‖ + ‖A x‖ := norm_add_le _ _
    _ ≤ ε * ‖x‖ + ‖A‖ * ‖x‖ := add_le_add h1 (A.le_opNorm x)
    _ = (‖A‖ + ε) * ‖x‖ := by ring

variable [CompleteSpace X]

omit [NormedSpace ℝ Y] in
/-- **The reduced map is onto.** For `ε < a` and a `1`-Lipschitz `h`, `A x + f(x, h x) = z` has a
solution: `x ↦ A⁻¹(z − f(x, h x))` is a contraction with constant `ε / a`. -/
@[tmio T, powerlib_foundation] theorem reducedMap_surjective (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hf : LipschitzWith ε f) (hεa : (ε : ℝ) < a) {h : X → Y}
    (hh : LipschitzWith 1 h) : Function.Surjective (reducedMap A f h) := by
  intro z
  have ha : 0 < a := lt_of_le_of_lt ε.coe_nonneg hεa
  set S := Function.surjInv hAs with hSdef
  have hS : ∀ u, A (S u) = u := Function.surjInv_eq hAs
  have hSl : ∀ u u', a * ‖S u - S u'‖ ≤ ‖u - u'‖ := fun u u' => by
    have := hA (S u - S u'); rwa [map_sub, hS, hS] at this
  set T : X → X := fun x => S (z - f (x, h x)) with hTdef
  let K : NNReal := ⟨ε / a, div_nonneg ε.coe_nonneg ha.le⟩
  have hK : (K : ℝ) = ε / a := rfl
  have hT : ContractingWith K T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x x' => ?_⟩
    · rw [← NNReal.coe_lt_coe, hK, NNReal.coe_one, div_lt_one ha]; exact hεa
    · rw [dist_eq_norm, dist_eq_norm, hK]
      have h1 := hSl (z - f (x, h x)) (z - f (x', h x'))
      have h2 : ‖(z - f (x, h x)) - (z - f (x', h x'))‖ ≤ ε * ‖x - x'‖ := by
        rw [sub_sub_sub_cancel_left, norm_sub_rev, ← norm_graph_sub hh x x']
        exact hf.norm_sub_le _ _
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      simp only [hTdef]
      nlinarith
  refine ⟨ContractingWith.fixedPoint T hT, ?_⟩
  have hfix : T (ContractingWith.fixedPoint T hT) = ContractingWith.fixedPoint T hT :=
    ContractingWith.fixedPoint_isFixedPt hT
  set x := ContractingWith.fixedPoint T hT
  have hAx : A x = z - f (x, h x) := by
    calc A x = A (T x) := by rw [hfix]
      _ = z - f (x, h x) := hS _
  simp only [reducedMap, hAx, sub_add_cancel]

omit [NormedSpace ℝ Y] in
/-- The reduced map along a `1`-Lipschitz graph is a bijection of `X` (`ε < a`). -/
@[tmio T, powerlib_foundation] theorem reducedMap_bijective (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hf : LipschitzWith ε f) (hεa : (ε : ℝ) < a) {h : X → Y}
    (hh : LipschitzWith 1 h) : Function.Bijective (reducedMap A f h) := by
  refine ⟨fun x x' hxx => ?_, reducedMap_surjective hAs hA hf hεa hh⟩
  have h1 := le_norm_reducedMap_sub hA hf hh x x'
  rw [hxx, sub_self, norm_zero] at h1
  have h2 : ‖x - x'‖ ≤ 0 := by
    by_contra hne
    push Not at hne
    have : 0 < (a - ε) * ‖x - x'‖ := mul_pos (by linarith) hne
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)

/-! ## The graph transform -/

/-- `(Γ h)(A x + f(x, h x)) = B h(x) + g(x, h x)`: `Γ h` is the graph of the image of `graph h`. -/
@[tmio T, powerlib_foundation] theorem graphTransform_reducedMap (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hf : LipschitzWith ε f) (hεa : (ε : ℝ) < a) {h : X → Y}
    (hh : LipschitzWith 1 h) (x : X) :
    graphTransform A B f g h (reducedMap A f h x) = B (h x) + g (x, h x) := by
  have hinj := (reducedMap_bijective hAs hA hf hεa hh).1
  have : Function.invFun (reducedMap A f h) (reducedMap A f h x) = x :=
    Function.leftInverse_invFun hinj x
  simp only [graphTransform, this]

/-- `Γ h` vanishes at `0`. -/
@[tmio T, powerlib_foundation] theorem graphTransform_zero (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hf : LipschitzWith ε f) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hεa : (ε : ℝ) < a) {h : X → Y} (hh : LipschitzWith 1 h) (hh0 : h 0 = 0) :
    graphTransform A B f g h 0 = 0 := by
  have := graphTransform_reducedMap (B := B) (g := g) hAs hA hf hεa hh 0
  rw [reducedMap_zero hf0 hh0, hh0, map_zero, zero_add] at this
  rw [this]
  exact hg0

/-- **`Γ` keeps the `1`-Lipschitz graphs** when `b + 2ε ≤ a`: the preimage map is
`1/(a − ε)`-Lipschitz and `x ↦ B h(x) + g(x, h x)` is `(b + ε)`-Lipschitz. -/
@[tmio T, powerlib_foundation] theorem lipschitzWith_graphTransform (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 2 * ε ≤ a) (hεa : (ε : ℝ) < a)
    {h : X → Y} (hh : LipschitzWith 1 h) : LipschitzWith 1 (graphTransform A B f g h) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  obtain ⟨x, rfl⟩ := reducedMap_surjective hAs hA hf hεa hh z
  obtain ⟨x', rfl⟩ := reducedMap_surjective hAs hA hf hεa hh z'
  have hlow := le_norm_reducedMap_sub hA hf hh x x'
  rw [graphTransform_reducedMap hAs hA hf hεa hh x, graphTransform_reducedMap hAs hA hf hεa hh x']
  have hval : B (h x) + g (x, h x) - (B (h x') + g (x', h x')) =
      B (h x - h x') + (g (x, h x) - g (x', h x')) := by
    rw [map_sub]; abel
  rw [hval]
  have h1 : ‖B (h x - h x')‖ ≤ b * ‖x - x'‖ := by
    refine (hB _).trans (mul_le_mul_of_nonneg_left ?_ hb)
    simpa using hh.norm_sub_le x x'
  have h2 : ‖g (x, h x) - g (x', h x')‖ ≤ ε * ‖x - x'‖ := by
    rw [← norm_graph_sub hh x x']; exact hg.norm_sub_le _ _
  have h3 := norm_add_le (B (h x - h x')) (g (x, h x) - g (x', h x'))
  have hd : 0 ≤ ‖x - x'‖ := norm_nonneg _
  nlinarith

/-- The weighted contraction constant `κ = a(b + ε)/(a − ε)²` of the graph transform. -/
@[tmio T, powerlib_foundation] theorem contraction_lt_one (hb : 0 ≤ b) (hgap : b + 3 * ε < a) :
    0 ≤ a * (b + ε) / (a - ε) ^ 2 ∧ a * (b + ε) / (a - ε) ^ 2 < 1 := by
  have hε := ε.coe_nonneg
  have ha : 0 < a := by linarith
  have hae : 0 < a - ε := by linarith
  refine ⟨div_nonneg (mul_nonneg ha.le (by linarith)) (sq_nonneg _), ?_⟩
  rw [div_lt_one (pow_pos hae 2)]
  nlinarith

/-- **The weighted contraction.** If `‖h₁ y − h₂ y‖ ≤ δ ‖y‖` for every `y`, then
`‖(Γ h₁) x − (Γ h₂) x‖ ≤ κ δ ‖x‖` with `κ = a(b + ε)/(a − ε)²`. -/
@[tmio T, powerlib_foundation] theorem norm_graphTransform_sub_le (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hf0 : f 0 = 0) (hεa : (ε : ℝ) < a)
    {h₁ h₂ : X → Y} (hh₁ : LipschitzWith 1 h₁) (hh₂ : LipschitzWith 1 h₂) (hh₂0 : h₂ 0 = 0)
    {δ : ℝ} (hδ : 0 ≤ δ) (hd : ∀ y, ‖h₁ y - h₂ y‖ ≤ δ * ‖y‖) (z : X) :
    ‖graphTransform A B f g h₁ z - graphTransform A B f g h₂ z‖ ≤
      a * (b + ε) / (a - ε) ^ 2 * δ * ‖z‖ := by
  have hε := ε.coe_nonneg
  have ha : 0 < a := lt_of_le_of_lt hε hεa
  have hae : 0 < a - ε := by linarith
  obtain ⟨x₁, hx₁⟩ := reducedMap_surjective hAs hA hf hεa hh₁ z
  obtain ⟨x₂, hx₂z⟩ := reducedMap_surjective hAs hA hf hεa hh₂ z
  have e₁ : graphTransform A B f g h₁ z = B (h₁ x₁) + g (x₁, h₁ x₁) := by
    rw [← hx₁]; exact graphTransform_reducedMap hAs hA hf hεa hh₁ x₁
  have e₂ : graphTransform A B f g h₂ z = B (h₂ x₂) + g (x₂, h₂ x₂) := by
    rw [← hx₂z]; exact graphTransform_reducedMap hAs hA hf hεa hh₂ x₂
  -- `(a − ε) ‖x₂‖ ≤ ‖z‖`
  have hx₂ : (a - ε) * ‖x₂‖ ≤ ‖z‖ := by
    have := le_norm_reducedMap_sub hA hf hh₂ x₂ 0
    rwa [hx₂z, reducedMap_zero hf0 hh₂0, sub_zero, sub_zero] at this
  -- `‖h₁ x₁ − h₂ x₂‖ ≤ ‖x₁ − x₂‖ + δ ‖x₂‖`
  have hhd : ‖h₁ x₁ - h₂ x₂‖ ≤ ‖x₁ - x₂‖ + δ * ‖x₂‖ := by
    have e : h₁ x₁ - h₂ x₂ = (h₁ x₁ - h₁ x₂) + (h₁ x₂ - h₂ x₂) := by abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hd x₂))
    simpa using hh₁.norm_sub_le x₁ x₂
  have hpair : ‖(x₁, h₁ x₁) - (x₂, h₂ x₂)‖ ≤ ‖x₁ - x₂‖ + δ * ‖x₂‖ := by
    rw [Prod.mk_sub_mk, Prod.norm_mk]
    exact max_le (le_add_of_nonneg_right (mul_nonneg hδ (norm_nonneg _))) hhd
  -- `a ‖x₁ − x₂‖ ≤ ε (‖x₁ − x₂‖ + δ ‖x₂‖)`
  have hx : a * ‖x₁ - x₂‖ ≤ ε * (‖x₁ - x₂‖ + δ * ‖x₂‖) := by
    have e : A (x₁ - x₂) = f (x₂, h₂ x₂) - f (x₁, h₁ x₁) := by
      have : reducedMap A f h₁ x₁ = reducedMap A f h₂ x₂ := hx₁.trans hx₂z.symm
      simp only [reducedMap] at this
      rw [map_sub, sub_eq_sub_iff_add_eq_add, this, add_comm]
    calc a * ‖x₁ - x₂‖ ≤ ‖A (x₁ - x₂)‖ := hA _
      _ = ‖f (x₁, h₁ x₁) - f (x₂, h₂ x₂)‖ := by rw [e, norm_sub_rev]
      _ ≤ ε * ‖(x₁, h₁ x₁) - (x₂, h₂ x₂)‖ := hf.norm_sub_le _ _
      _ ≤ ε * (‖x₁ - x₂‖ + δ * ‖x₂‖) := mul_le_mul_of_nonneg_left hpair hε
  rw [e₁, e₂]
  have hval : B (h₁ x₁) + g (x₁, h₁ x₁) - (B (h₂ x₂) + g (x₂, h₂ x₂)) =
      B (h₁ x₁ - h₂ x₂) + (g (x₁, h₁ x₁) - g (x₂, h₂ x₂)) := by
    rw [map_sub]; abel
  rw [hval]
  set N := ‖x₁ - x₂‖ + δ * ‖x₂‖ with hN
  have h1 : ‖B (h₁ x₁ - h₂ x₂)‖ ≤ b * N := (hB _).trans (mul_le_mul_of_nonneg_left hhd hb)
  have h2 : ‖g (x₁, h₁ x₁) - g (x₂, h₂ x₂)‖ ≤ ε * N :=
    (hg.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left hpair hε)
  have h3 := norm_add_le (B (h₁ x₁ - h₂ x₂)) (g (x₁, h₁ x₁) - g (x₂, h₂ x₂))
  -- `(a − ε) N ≤ a δ ‖x₂‖` and `(a − ε)² N ≤ a δ ‖z‖`
  have hs : (a - ε) * N ≤ a * δ * ‖x₂‖ := by rw [hN]; linarith
  have hs' : (a - ε) ^ 2 * N ≤ a * δ * ‖z‖ := by
    have h4 := mul_le_mul_of_nonneg_left hs hae.le
    have h5 := mul_le_mul_of_nonneg_left hx₂ (mul_nonneg ha.le hδ)
    nlinarith
  have hNle : N ≤ a * δ * ‖z‖ / (a - ε) ^ 2 := by
    rw [le_div_iff₀' (pow_pos hae 2)]; exact hs'
  have hbe : 0 ≤ b + ε := by linarith
  calc ‖B (h₁ x₁ - h₂ x₂) + (g (x₁, h₁ x₁) - g (x₂, h₂ x₂))‖ ≤ (b + ε) * N := by linarith
    _ ≤ (b + ε) * (a * δ * ‖z‖ / (a - ε) ^ 2) := mul_le_mul_of_nonneg_left hNle hbe
    _ = a * (b + ε) / (a - ε) ^ 2 * δ * ‖z‖ := by ring

/-- **Fixed points of `Γ` are the invariant graphs.** For a `1`-Lipschitz `h`, `Γ h = h` exactly
when `h(A x + f(x, h x)) = B h(x) + g(x, h x)` for every `x`. -/
@[tmio T, powerlib_foundation] theorem graphTransform_eq_self_iff (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hf : LipschitzWith ε f) (hεa : (ε : ℝ) < a) {h : X → Y}
    (hh : LipschitzWith 1 h) :
    graphTransform A B f g h = h ↔ ∀ x, h (reducedMap A f h x) = B (h x) + g (x, h x) := by
  constructor
  · intro hfix x
    rw [← graphTransform_reducedMap (B := B) (g := g) hAs hA hf hεa hh x, hfix]
  · intro hinv
    funext z
    obtain ⟨x, rfl⟩ := reducedMap_surjective hAs hA hf hεa hh z
    rw [graphTransform_reducedMap hAs hA hf hεa hh x, hinv x]

omit [CompleteSpace X] in
/-- `Γ` keeps graphs with values in a submodule `K` that `B` maps into itself and `g` maps into
`K` on `X × K`. -/
@[tmio T, powerlib_foundation] theorem graphTransform_mem {K : Submodule ℝ Y}
    (hBK : ∀ y ∈ K, B y ∈ K) (hgK : ∀ x, ∀ y ∈ K, g (x, y) ∈ K) {h : X → Y} (hhK : ∀ x, h x ∈ K)
    (z : X) : graphTransform A B f g h z ∈ K :=
  K.add_mem (hBK _ (hhK _)) (hgK _ _ (hhK _))

/-! ## Existence and uniqueness of the invariant graph -/

variable [CompleteSpace Y]

/-- The iterates `Γᵏ 0` are `1`-Lipschitz graphs through `0`, consecutive ones are `κᵏ`-close in
the weighted distance, and they converge pointwise to `centreGraph` at the rate
`κᵏ/(1 − κ)`. -/
@[tmio T, powerlib_foundation] private theorem iterate_spec (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hgap : b + 3 * ε < a) :
    (∀ k : ℕ, LipschitzWith 1 ((graphTransform A B f g)^[k] 0) ∧
      (graphTransform A B f g)^[k] 0 0 = 0) ∧
    ∀ (k : ℕ) (x : X), ‖(graphTransform A B f g)^[k] 0 x - centreGraph A B f g x‖ ≤
      ‖x‖ * (a * (b + ε) / (a - ε) ^ 2) ^ k / (1 - a * (b + ε) / (a - ε) ^ 2) := by
  have hε := ε.coe_nonneg
  have hεa : (ε : ℝ) < a := by linarith
  have hgap2 : b + 2 * ε ≤ a := by linarith
  obtain ⟨hκ0, hκ1⟩ := contraction_lt_one hb hgap
  set κ := a * (b + ε) / (a - ε) ^ 2 with hκ
  set H : ℕ → X → Y := fun k => (graphTransform A B f g)^[k] 0 with hHdef
  have hsucc : ∀ k, H (k + 1) = graphTransform A B f g (H k) := fun k => by
    simp only [hHdef]; rw [Function.iterate_succ_apply']
  have hmem : ∀ k, LipschitzWith 1 (H k) ∧ H k 0 = 0 := by
    intro k
    induction k with
    | zero => exact ⟨(LipschitzWith.const (α := X) (0 : Y)).weaken zero_le_one, rfl⟩
    | succ k ih =>
      rw [hsucc]
      exact ⟨lipschitzWith_graphTransform hAs hA hB hb hf hg hgap2 hεa ih.1,
        graphTransform_zero hAs hA hf hf0 hg0 hεa ih.1 ih.2⟩
  have hstep : ∀ k x, ‖H (k + 1) x - H k x‖ ≤ κ ^ k * ‖x‖ := by
    intro k
    induction k with
    | zero =>
      intro x
      have := (hmem 1).1.norm_sub_le x 0
      rw [(hmem 1).2] at this
      simpa [hHdef] using this
    | succ k ih =>
      intro x
      have := norm_graphTransform_sub_le (B := B) (g := g) hAs hA hB hb hf hg hf0 hεa
        (hmem (k + 1)).1 (hmem k).1 (hmem k).2 (pow_nonneg hκ0 k) ih x
      rw [← hsucc (k + 1), ← hsucc k] at this
      calc _ ≤ κ * κ ^ k * ‖x‖ := this
        _ = κ ^ (k + 1) * ‖x‖ := by ring
  have hcauchy : ∀ x, ∀ k, dist (H k x) (H (k + 1) x) ≤ ‖x‖ * κ ^ k := fun x k => by
    rw [dist_eq_norm, norm_sub_rev, mul_comm]; exact hstep k x
  have hlim : ∀ x, Tendsto (fun k => H k x) atTop (𝓝 (centreGraph A B f g x)) := fun x =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
      (cauchySeq_of_le_geometric κ ‖x‖ hκ1 (hcauchy x)))
  refine ⟨hmem, fun k x => ?_⟩
  rw [← dist_eq_norm]
  exact dist_le_of_le_geometric_of_tendsto κ ‖x‖ hκ1 (hcauchy x) (hlim x) k

/-- **The centre manifold of a map (global form).** Under `a ‖x‖ ≤ ‖A x‖` (`A` onto),
`‖B y‖ ≤ b ‖y‖`, `f`, `g` vanishing at `0` and `ε`-Lipschitz with `b + 3ε < a`, there is one and
only one `1`-Lipschitz graph `h` through `0` that the map carries into itself:
`h(A x + f(x, h x)) = B h(x) + g(x, h(x))`. -/
@[tmio T, powerlib_foundation] theorem exists_unique_invariantGraph (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hgap : b + 3 * ε < a) :
    ∃! h : X → Y, LipschitzWith 1 h ∧ h 0 = 0 ∧
      ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x) := by
  have hε := ε.coe_nonneg
  have hεa : (ε : ℝ) < a := by linarith
  obtain ⟨hκ0, hκ1⟩ := contraction_lt_one hb hgap
  set κ := a * (b + ε) / (a - ε) ^ 2 with hκ
  obtain ⟨hmem, hconv⟩ := iterate_spec hAs hA hB hb hf hg hf0 hg0 hgap
  set H : ℕ → X → Y := fun k => (graphTransform A B f g)^[k] 0 with hHdef
  set h := centreGraph A B f g with hdef
  have hsucc : ∀ k, H (k + 1) = graphTransform A B f g (H k) := fun k => by
    simp only [hHdef]; rw [Function.iterate_succ_apply']
  have hlim : ∀ x, Tendsto (fun k => H k x) atTop (𝓝 (h x)) := fun x => by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => hconv k x) ?_
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).const_mul ‖x‖).div_const (1 - κ)
    simpa using this
  have hlip : LipschitzWith 1 h := LipschitzWith.of_dist_le_mul fun x x' =>
    le_of_tendsto' ((hlim x).dist (hlim x')) fun k => (hmem k).1.dist_le_mul x x'
  have hh0 : h 0 = 0 := by
    have hc : (fun k => H k 0) = fun _ => (0 : Y) := funext fun k => (hmem k).2
    have := hlim 0
    rw [hc] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  -- `h` is a fixed point of `Γ`
  have hfix : graphTransform A B f g h = h := by
    funext z
    have hd : ∀ k, ‖graphTransform A B f g h z - H (k + 1) z‖ ≤
        κ * (κ ^ k / (1 - κ)) * ‖z‖ := fun k => by
      rw [hsucc]
      refine norm_graphTransform_sub_le hAs hA hB hb hf hg hf0 hεa hlip (hmem k).1 (hmem k).2
        (div_nonneg (pow_nonneg hκ0 k) (sub_pos.mpr hκ1).le) (fun y => ?_) z
      rw [norm_sub_rev]
      calc ‖H k y - h y‖ ≤ ‖y‖ * κ ^ k / (1 - κ) := hconv k y
        _ = κ ^ k / (1 - κ) * ‖y‖ := by ring
    have h1 : Tendsto (fun k => H (k + 1) z) atTop (𝓝 (graphTransform A B f g h z)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (g := fun k => κ * (κ ^ k / (1 - κ)) * ‖z‖) (fun k => norm_nonneg _)
        (fun k => by rw [norm_sub_rev]; exact hd k) ?_
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).div_const (1 - κ)).const_mul κ
      simpa using this.mul_const ‖z‖
    exact tendsto_nhds_unique h1 ((hlim z).comp (tendsto_add_atTop_nat 1))
  refine ⟨h, ⟨hlip, hh0, (graphTransform_eq_self_iff hAs hA hf hεa hlip).mp hfix⟩, ?_⟩
  -- uniqueness
  rintro h' ⟨hlip', hh0', hinv'⟩
  have hfix' : graphTransform A B f g h' = h' :=
    (graphTransform_eq_self_iff hAs hA hf hεa hlip').mpr hinv'
  have hk : ∀ k : ℕ, ∀ y, ‖h' y - h y‖ ≤ 2 * κ ^ k * ‖y‖ := by
    intro k
    induction k with
    | zero =>
      intro y
      have h1 := hlip'.norm_sub_le y 0
      have h2 := hlip.norm_sub_le y 0
      rw [hh0'] at h1; rw [hh0] at h2
      simp only [NNReal.coe_one, one_mul, sub_zero] at h1 h2
      calc ‖h' y - h y‖ ≤ ‖h' y‖ + ‖h y‖ := norm_sub_le _ _
        _ ≤ 2 * κ ^ 0 * ‖y‖ := by rw [pow_zero, mul_one]; linarith
    | succ k ih =>
      intro y
      have := norm_graphTransform_sub_le (B := B) (g := g) hAs hA hB hb hf hg hf0 hεa hlip' hlip
        hh0 (mul_nonneg zero_le_two (pow_nonneg hκ0 k)) ih y
      rw [hfix', hfix] at this
      calc ‖h' y - h y‖ ≤ κ * (2 * κ ^ k) * ‖y‖ := this
        _ = 2 * κ ^ (k + 1) * ‖y‖ := by ring
  funext y
  have hlim0 : Tendsto (fun k : ℕ => 2 * κ ^ k * ‖y‖) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).const_mul 2).mul_const ‖y‖
  have : ‖h' y - h y‖ ≤ 0 := ge_of_tendsto' hlim0 (fun k => hk k y)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- The invariant graph of `exists_unique_invariantGraph` is `centreGraph`, the pointwise limit of
the iterated graph transform from the zero graph. -/
@[tmio T, powerlib_foundation] theorem centreGraph_spec (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hgap : b + 3 * ε < a) :
    LipschitzWith 1 (centreGraph A B f g) ∧ centreGraph A B f g 0 = 0 ∧
      ∀ x, centreGraph A B f g (A x + f (x, centreGraph A B f g x)) =
        B (centreGraph A B f g x) + g (x, centreGraph A B f g x) := by
  have hε := ε.coe_nonneg
  have hεa : (ε : ℝ) < a := by linarith
  obtain ⟨hκ0, hκ1⟩ := contraction_lt_one hb hgap
  obtain ⟨hmem, hconv⟩ := iterate_spec hAs hA hB hb hf hg hf0 hg0 hgap
  obtain ⟨h, ⟨hlip, hh0, hinv⟩, huniq⟩ := exists_unique_invariantGraph hAs hA hB hb hf hg hf0 hg0
    hgap
  -- the iterates converge to every invariant graph, hence `h = centreGraph`
  have hfix : graphTransform A B f g h = h :=
    (graphTransform_eq_self_iff hAs hA hf hεa hlip).mpr hinv
  set κ := a * (b + ε) / (a - ε) ^ 2 with hκ
  have hk : ∀ k : ℕ, ∀ y, ‖(graphTransform A B f g)^[k] 0 y - h y‖ ≤ κ ^ k * ‖y‖ := by
    intro k
    induction k with
    | zero =>
      intro y
      have := hlip.norm_sub_le y 0
      rw [hh0] at this
      simpa using this
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply']
      have := norm_graphTransform_sub_le (B := B) (g := g) hAs hA hB hb hf hg hf0 hεa
        (hmem k).1 hlip hh0 (pow_nonneg hκ0 k) ih y
      rw [hfix] at this
      calc _ ≤ κ * κ ^ k * ‖y‖ := this
        _ = κ ^ (k + 1) * ‖y‖ := by ring
  have heq : centreGraph A B f g = h := by
    funext y
    have h1 : Tendsto (fun k => (graphTransform A B f g)^[k] 0 y) atTop (𝓝 (h y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => hk k y) ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).mul_const ‖y‖
    have h2 : Tendsto (fun k => (graphTransform A B f g)^[k] 0 y) atTop
        (𝓝 (centreGraph A B f g y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => hconv k y) ?_
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).const_mul ‖y‖).div_const (1 - κ)
      simpa using this
    exact tendsto_nhds_unique h2 h1
  rw [heq]
  exact ⟨hlip, hh0, hinv⟩

/-- **The invariant graph lies in every invariant closed submodule.** If `K ⊆ Y` is a closed
submodule with `B K ⊆ K` and `g(X × K) ⊆ K`, the centre manifold takes values in `K`: every
iterate `Γᵏ 0` does, and `K` is closed. -/
@[tmio T, powerlib_foundation] theorem centreGraph_mem {K : Submodule ℝ Y}
    (hKc : IsClosed (K : Set Y)) (hBK : ∀ y ∈ K, B y ∈ K) (hgK : ∀ x, ∀ y ∈ K, g (x, y) ∈ K)
    (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hgap : b + 3 * ε < a) (x : X) : centreGraph A B f g x ∈ K := by
  obtain ⟨hκ0, hκ1⟩ := contraction_lt_one hb hgap
  obtain ⟨-, hconv⟩ := iterate_spec hAs hA hB hb hf hg hf0 hg0 hgap
  set κ := a * (b + ε) / (a - ε) ^ 2 with hκ
  have hit : ∀ k : ℕ, ∀ z, (graphTransform A B f g)^[k] 0 z ∈ K := by
    intro k
    induction k with
    | zero => intro z; exact K.zero_mem
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply']
      exact graphTransform_mem hBK hgK ih z
  have hlim : Tendsto (fun k => (graphTransform A B f g)^[k] 0 x) atTop
      (𝓝 (centreGraph A B f g x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => hconv k x) ?_
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).const_mul ‖x‖).div_const (1 - κ)
    simpa using this
  exact hKc.mem_of_tendsto hlim (Eventually.of_forall fun k => hit k x)

omit [CompleteSpace X] [CompleteSpace Y] in
/-- Graph points go to graph points: on an invariant graph,
`F(x, h x) = (r x, h(r x))` with the reduced map `r`. -/
@[tmio T, powerlib_foundation] theorem splitMap_graph {h : X → Y}
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (x : X) :
    splitMap A B f g (x, h x) = (reducedMap A f h x, h (reducedMap A f h x)) := by
  simp only [splitMap, reducedMap, hinv]

/-! ## Attraction -/

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **One step towards the graph.** For an invariant `1`-Lipschitz graph,
`‖y' − h(x')‖ ≤ (b + 2ε) ‖y − h(x)‖` with `(x', y') = F(x, y)`. -/
@[tmio T, powerlib_foundation] theorem norm_splitMap_sub_graph_le (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) {h : X → Y} (hh : LipschitzWith 1 h)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (p : X × Y) :
    ‖(splitMap A B f g p).2 - h (splitMap A B f g p).1‖ ≤ (b + 2 * ε) * ‖p.2 - h p.1‖ := by
  obtain ⟨x, y⟩ := p
  simp only [splitMap]
  have hpp : ‖(x, y) - (x, h x)‖ = ‖y - h x‖ := by
    rw [Prod.mk_sub_mk, sub_self, Prod.norm_mk, norm_zero]
    exact max_eq_right (norm_nonneg _)
  have e : B y + g (x, y) - h (A x + f (x, y)) =
      B (y - h x) + (g (x, y) - g (x, h x)) + (h (A x + f (x, h x)) - h (A x + f (x, y))) := by
    rw [hinv, map_sub]; abel
  rw [e]
  have h1 := hB (y - h x)
  have h2 : ‖g (x, y) - g (x, h x)‖ ≤ ε * ‖y - h x‖ := by
    rw [← hpp]; exact hg.norm_sub_le _ _
  have h3 : ‖h (A x + f (x, h x)) - h (A x + f (x, y))‖ ≤ ε * ‖y - h x‖ := by
    have := hh.norm_sub_le (A x + f (x, h x)) (A x + f (x, y))
    rw [NNReal.coe_one, one_mul, add_sub_add_left_eq_sub,
      norm_sub_rev (f (x, h x)) (f (x, y))] at this
    refine this.trans ?_
    rw [← hpp]; exact hf.norm_sub_le _ _
  calc _ ≤ ‖B (y - h x) + (g (x, y) - g (x, h x))‖ + ‖h (A x + f (x, h x)) - h (A x + f (x, y))‖ :=
        norm_add_le _ _
    _ ≤ ‖B (y - h x)‖ + ‖g (x, y) - g (x, h x)‖ + ‖h (A x + f (x, h x)) - h (A x + f (x, y))‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ b * ‖y - h x‖ + ε * ‖y - h x‖ + ε * ‖y - h x‖ := by gcongr
    _ = (b + 2 * ε) * ‖y - h x‖ := by ring

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Exponential attraction.** Along every orbit of `F`, the distance to the invariant graph
decays at least like `(b + 2ε)^k`: `‖y_k − h(x_k)‖ ≤ (b + 2ε)^k ‖y_0 − h(x_0)‖`. -/
@[tmio T, powerlib_foundation] theorem norm_iterate_sub_graph_le (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖)
    (hb : 0 ≤ b) (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) {h : X → Y}
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (p : X × Y) (k : ℕ) :
    ‖((splitMap A B f g)^[k] p).2 - h ((splitMap A B f g)^[k] p).1‖ ≤
      (b + 2 * ε) ^ k * ‖p.2 - h p.1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc _ ≤ (b + 2 * ε) * ‖((splitMap A B f g)^[k] p).2 - h ((splitMap A B f g)^[k] p).1‖ :=
          norm_splitMap_sub_graph_le hB hf hg hh hinv _
      _ ≤ (b + 2 * ε) * ((b + 2 * ε) ^ k * ‖p.2 - h p.1‖) :=
          mul_le_mul_of_nonneg_left ih (by have := ε.coe_nonneg; linarith)
      _ = (b + 2 * ε) ^ (k + 1) * ‖p.2 - h p.1‖ := by ring

/-! ## The cut-off and the local theorem -/

section Cutoff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The radial retraction onto the closed ball of radius `ρ`. -/
def ballRetract (ρ : ℝ) (v : E) : E := if ‖v‖ ≤ ρ then v else (ρ / ‖v‖) • v

@[tmio T, powerlib_foundation] theorem ballRetract_of_norm_le {ρ : ℝ} {v : E} (hv : ‖v‖ ≤ ρ) :
    ballRetract ρ v = v := by simp [ballRetract, hv]

@[tmio T, powerlib_foundation] theorem norm_ballRetract_le {ρ : ℝ} (hρ : 0 ≤ ρ) (v : E) :
    ‖ballRetract ρ v‖ ≤ ρ := by
  unfold ballRetract
  split_ifs with hv
  · exact hv
  · push Not at hv
    have hv0 : 0 < ‖v‖ := hρ.trans_lt hv
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hρ hv0.le), div_mul_cancel₀ _ hv0.ne']

/-- The radial retraction is `2`-Lipschitz in every normed space. -/
@[tmio T, powerlib_foundation] theorem lipschitzWith_ballRetract {ρ : ℝ} (hρ : 0 ≤ ρ) :
    LipschitzWith 2 (ballRetract ρ : E → E) := by
  -- outside the ball: `‖ρ v/‖v‖ − w‖ ≤ (‖v‖ − ρ) + ‖v − w‖`
  have hout : ∀ v w : E, ρ < ‖v‖ → ‖(ρ / ‖v‖) • v - w‖ ≤ (‖v‖ - ρ) + ‖v - w‖ := by
    intro v w hv
    have hv0 : 0 < ‖v‖ := hρ.trans_lt hv
    have e : (ρ / ‖v‖) • v - w = (v - w) - (1 - ρ / ‖v‖) • v := by
      rw [sub_smul, one_smul]; abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by rw [sub_nonneg, div_le_one hv0]; exact hv.le),
      sub_mul, div_mul_cancel₀ _ hv0.ne', one_mul]
    linarith
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [dist_eq_norm, dist_eq_norm, show ((2 : NNReal) : ℝ) = 2 from rfl]
  have hvw := norm_sub_norm_le v w
  have hwv := norm_sub_norm_le w v
  rw [norm_sub_rev w v] at hwv
  unfold ballRetract
  split_ifs with hv hw hw
  · linarith [norm_nonneg (v - w)]
  · push Not at hw
    have h1 := hout w v hw
    rw [norm_sub_rev ((ρ / ‖w‖) • w) v, norm_sub_rev w v] at h1
    linarith
  · push Not at hv
    have := hout v w hv
    linarith
  · push Not at hv hw
    have hv0 : 0 < ‖v‖ := hρ.trans_lt hv
    have hw0 : 0 < ‖w‖ := hρ.trans_lt hw
    -- `‖ρ v/‖v‖ − ρ w/‖w‖‖ = (ρ/‖v‖) ‖v − (‖v‖/‖w‖) w‖ ≤ (ρ/‖v‖) · 2‖v − w‖`
    have e : (ρ / ‖v‖) • v - (ρ / ‖w‖) • w = (ρ / ‖v‖) • (v - (‖v‖ / ‖w‖) • w) := by
      rw [smul_sub, smul_smul]
      congr 2
      field_simp
    rw [e, norm_smul, Real.norm_of_nonneg (div_nonneg hρ hv0.le)]
    have h2 : ‖v - (‖v‖ / ‖w‖) • w‖ ≤ 2 * ‖v - w‖ := by
      have e2 : v - (‖v‖ / ‖w‖) • w = (v - w) + (1 - ‖v‖ / ‖w‖) • w := by
        rw [sub_smul, one_smul]; abel
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      have key : ‖(1 - ‖v‖ / ‖w‖) • w‖ = |‖w‖ - ‖v‖| := by
        rw [norm_smul, Real.norm_eq_abs,
          show ‖w‖ - ‖v‖ = (1 - ‖v‖ / ‖w‖) * ‖w‖ by field_simp, abs_mul, abs_of_pos hw0]
      rw [key]
      have := abs_norm_sub_norm_le w v
      rw [norm_sub_rev w v] at this
      linarith
    have h3 : ρ / ‖v‖ ≤ 1 := (div_le_one hv0).mpr hv.le
    have h4 : 0 ≤ ρ / ‖v‖ := div_nonneg hρ hv0.le
    nlinarith [norm_nonneg (v - (‖v‖ / ‖w‖) • w), norm_nonneg (v - w)]

/-- **The cut-off.** A map with `f₀ 0 = 0` and strict derivative `0` at `0` agrees on a closed
ball `‖p‖ ≤ ρ` with a globally `ε`-Lipschitz map vanishing at `0`, for every `ε > 0`:
`f₀ ∘ ballRetract ρ`, `f₀` being `ε/2`-Lipschitz near `0`. -/
@[tmio T, powerlib_foundation] theorem exists_lipschitz_cutoff {f₀ : E → F}
    (hf : HasStrictFDerivAt f₀ (0 : E →L[ℝ] F) 0) (hf0 : f₀ 0 = 0) {ε : NNReal} (hε : 0 < ε) :
    ∃ ρ > 0, ∃ f : E → F, LipschitzWith ε f ∧ f 0 = 0 ∧ ∀ p, ‖p‖ ≤ ρ → f p = f₀ p := by
  obtain ⟨s, hs, hlip⟩ := hf.exists_lipschitzOnWith_of_nnnorm_lt (ε / 2)
    (by rw [nnnorm_zero]; exact half_pos hε)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨r / 2, half_pos hr, f₀ ∘ ballRetract (r / 2), ?_, ?_, fun p hp => ?_⟩
  · have hmaps : Set.MapsTo (ballRetract (r / 2) : E → E) Set.univ s := fun p _ => hball (by
      rw [Metric.mem_ball, dist_zero_right]
      exact (norm_ballRetract_le (half_pos hr).le p).trans_lt (half_lt_self hr))
    have := hlip.comp ((lipschitzWith_ballRetract (half_pos hr).le).lipschitzOnWith
      (s := Set.univ)) hmaps
    rw [lipschitzOnWith_univ] at this
    convert this using 1
    rw [div_mul_cancel₀ _ two_ne_zero]
  · show f₀ (ballRetract (r / 2) (0 : E)) = 0
    rw [ballRetract_of_norm_le (by rw [norm_zero]; exact (half_pos hr).le), hf0]
  · show f₀ (ballRetract (r / 2) p) = f₀ p
    rw [ballRetract_of_norm_le hp]

end Cutoff

/-- **The local centre manifold of a map.** Let `F₀(x, y) = (A x + f₀(x, y), B y + g₀(x, y))`
with `f₀`, `g₀` vanishing at `0` with strict derivative `0` there (for instance `C¹` with
`Df₀(0) = Dg₀(0) = 0`). For every `ε > 0` with `b + 3ε < a` there are a radius `ρ > 0` and
`ε`-Lipschitz cut-offs `f`, `g` vanishing at `0` and equal to `f₀`, `g₀` on `‖p‖ ≤ ρ`, whose
unique invariant `1`-Lipschitz graph `h` through `0` is a local centre manifold of `F₀`: graph
points with `‖x‖ ≤ ρ` are mapped by `F₀` to graph points, and every orbit of `F₀` that stays in
the ball approaches the graph at the rate `(b + 2ε)^k`. -/
@[tmio T, powerlib_foundation] theorem exists_local_centreManifold (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) {f₀ : X × Y → X}
    {g₀ : X × Y → Y} (hf : HasStrictFDerivAt f₀ (0 : X × Y →L[ℝ] X) 0)
    (hg : HasStrictFDerivAt g₀ (0 : X × Y →L[ℝ] Y) 0) (hf0 : f₀ 0 = 0) (hg0 : g₀ 0 = 0)
    (hε : 0 < ε) (hgap : b + 3 * ε < a) :
    ∃ ρ > 0, ∃ f : X × Y → X, ∃ g : X × Y → Y,
      LipschitzWith ε f ∧ LipschitzWith ε g ∧ f 0 = 0 ∧ g 0 = 0 ∧
      (∀ p, ‖p‖ ≤ ρ → f p = f₀ p ∧ g p = g₀ p) ∧
      ∃ h : X → Y, LipschitzWith 1 h ∧ h 0 = 0 ∧
        (∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) ∧
        (∀ x, ‖x‖ ≤ ρ → splitMap A B f₀ g₀ (x, h x) =
          (A x + f₀ (x, h x), h (A x + f₀ (x, h x)))) ∧
        ∀ (p : X × Y) (k : ℕ), (∀ j < k, ‖(splitMap A B f₀ g₀)^[j] p‖ ≤ ρ) →
          ‖((splitMap A B f₀ g₀)^[k] p).2 - h ((splitMap A B f₀ g₀)^[k] p).1‖ ≤
            (b + 2 * ε) ^ k * ‖p.2 - h p.1‖ := by
  obtain ⟨ρ₁, hρ₁, f, hfl, hf0', hff⟩ := exists_lipschitz_cutoff hf hf0 hε
  obtain ⟨ρ₂, hρ₂, g, hgl, hg0', hgg⟩ := exists_lipschitz_cutoff hg hg0 hε
  set ρ := min ρ₁ ρ₂ with hρ
  have hagree : ∀ p, ‖p‖ ≤ ρ → f p = f₀ p ∧ g p = g₀ p := fun p hp =>
    ⟨hff p (hp.trans (min_le_left _ _)), hgg p (hp.trans (min_le_right _ _))⟩
  have hsplit : ∀ p, ‖p‖ ≤ ρ → splitMap A B f₀ g₀ p = splitMap A B f g p := fun p hp => by
    simp only [splitMap, (hagree p hp).1, (hagree p hp).2]
  obtain ⟨h, ⟨hlip, hh0, hinv⟩, -⟩ :=
    exists_unique_invariantGraph hAs hA hB hb hfl hgl hf0' hg0' hgap
  refine ⟨ρ, lt_min hρ₁ hρ₂, f, g, hfl, hgl, hf0', hg0', hagree, h, hlip, hh0, hinv,
    fun x hx => ?_, fun p k hk => ?_⟩
  · have hp : ‖(x, h x)‖ ≤ ρ := by rw [norm_graph hlip hh0]; exact hx
    rw [hsplit _ hp, splitMap_graph hinv, reducedMap, (hagree _ hp).1]
  · have heq : ∀ j ≤ k, (splitMap A B f₀ g₀)^[j] p = (splitMap A B f g)^[j] p := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih (Nat.le_of_succ_le hj)]
        exact hsplit _ (hk j hj)
    rw [heq k le_rfl]
    exact norm_iterate_sub_graph_le hB hb hfl hgl hlip hinv p k

end powerlib.Map.CenterManifold
