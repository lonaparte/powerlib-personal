import theorem.Periodic.JetVariation

/-! # The jet of the flow at orders four and five is the fourth and fifth variation

`theorem/Periodic/PeriodMapTaylor.lean` writes the second and third coefficients of the flow of
`ẋ = G(t, x)` about a solution in closed form, as responses of forced variational equations
(`secondVariation`, `thirdVariation`), and `theorem/Periodic/JetVariation.lean` identifies them
with the coefficients `flowJet A Q s t 2`, `3` of the jet of `theorem/Periodic/PeriodMapJet.lean`.
This file does the same at orders four and five, so that the coefficients `c₄`, `c₅` of the
degenerate flip of `theorem/Periodic/DegenerateFlipOrbit.lean`, and with them the decisive
quantity `c₅ + 3c₂c₄ − 2c₂⁴`, are computed from the variational equations up to order five.

* The compositions of `4` into at least two blocks are the seven `(1, 3)`, `(3, 1)`, `(2, 2)`,
  `(1, 1, 2)`, `(1, 2, 1)`, `(2, 1, 1)`, `(1, 1, 1, 1)`, those of `5` the fifteen of lengths
  `2, 3, 4, 5` (`compositions_four`, `compositions_five`: the `2^{k−1}` compositions of
  Mathlib's `composition_card` but the single block). Hence the source of the `k`-th equation of
  the hierarchy, `∑_c Q_{|c|}(p_{c₁}(m_{(1)}), …)`, is written out term by term, with the
  arguments split into consecutive blocks (`varSource_four`, `varSource_five`), e.g. for `k = 4`
  `Q₂(p₁m₀, p₃(m₁, m₂, m₃)) + Q₂(p₃(m₀, m₁, m₂), p₁m₃) + Q₂(p₂(m₀, m₁), p₂(m₂, m₃)) +
  Q₃(p₁m₀, p₁m₁, p₂(m₂, m₃)) + Q₃(p₁m₀, p₂(m₁, m₂), p₁m₃) + Q₃(p₂(m₀, m₁), p₁m₂, p₁m₃) +
  Q₄(p₁m₀, …, p₁m₃)`.
* With `P₁ = Φ(r, s)`, `P₂ = secondVariation`, `P₃ = thirdVariation` in place of `p₁, p₂, p₃`
  and the field coefficients `Q₂` (bilinear), `Q₃`, `Q₄` this is `fourthSource`; the fourth
  variation `P₄(t) = fourthVariation` is the four-linear map with the values
  `∫ₛᵗ Φ(t, r) fourthSource(e_{f₀}, …, e_{f₃})(r) dr` on basis vectors. Likewise `fifthSource`
  (fifteen terms, with `P₄` as well) and `P₅(t) = fifthVariation`.
* `flowJet A Q s t 4 = fourthVariation A Q₂ Q₃ Q₄ s t` and
  `flowJet A Q s t 5 = fifthVariation A Q₂ Q₃ Q₄ Q₅ s t` whenever `Q(r)₂(a, b) = Q₂(r)(a, b)`,
  `Q(r)ₖ = Qₖ(r)` (`flowJet_four`, `flowJet_five`): both sides are defined by their values on
  tuples of basis vectors as responses of the same forced equation (`varSource_flowJet_four`,
  `varSource_flowJet_five`, through `JetVariation.bilin_flowJet_two` and
  `JetVariation.flowJet_three`), so no continuity is needed. For continuous coefficients the
  variations solve `Ṗ₄(m) = A P₄(m) + fourthSource(m)`, `Ṗ₅(m) = A P₅(m) + fifthSource(m)` at every
  argument (`fourthVariation_apply`, `hasDerivAt_fourthVariation`, `fifthVariation_apply`,
  `hasDerivAt_fifthVariation`, through `PeriodMapJet.flowJet_spec` for the series `coeffSeries`
  of the coefficients), and the period map has the expansion
  `P(p + e) = p + M e + P₂(e, e) + P₃(e³) + P₄(e⁴) + P₅(e⁵) + O(‖e‖⁶)` in the variations
  (`periodMap_variations`).
* Hence `c₄ = wm ⬝ P₄(vm⁴) + wm ⬝ P₃'(vm) k₂ + wm ⬝ (P₂(vm, k₃) + P₂(k₃, vm)) + wm ⬝ P₂(k₂, k₂)`
  and `c₅ = wm ⬝ P₅(vm⁵) + wm ⬝ P₄'(vm) k₂ + wm ⬝ (P₃'(vm) k₃ + P₃'(k₂) vm) +
  wm ⬝ (P₂(vm, k₄) + P₂(k₄, vm)) + wm ⬝ (P₂(k₂, k₃) + P₂(k₃, k₂))` with the variations and the
  homological corrections `k₂, k₃, k₄`, and `c₅ + 3c₂c₄ − 2c₂⁴` of the jet equals that of the
  variations (`degenerateCoeff_jet_eq`); the flip verdict of `JetVariation.orbit_flip_of_jet`
  (`c₂² + c₃ ≷ 0`, and on `c₂² + c₃ = 0` the sign of `c₅ + 3c₂c₄ − 2c₂⁴`) holds with every
  coefficient a variation (`orbit_flip_of_variations`).

Scope.
* `ℝ^X` (`X → ℝ`, finite `X`, sup norm), continuous time, as in
  `theorem/Periodic/PeriodMapTaylor.lean` and `theorem/Periodic/PeriodMapJet.lean`; the
  identifications hold for arbitrary matrix fields `A` and coefficient fields `Q`, `Q₂`, …, `Q₅`
  (no continuity, no symmetry); the variational equations and the expansion of the period map
  need continuous coefficients; the verdict holds under the hypotheses of
  `JetVariation.orbit_flip_of_jet` on `ℝ^{Fin n}` (global Lipschitz bound), with the expansion of
  the field given by `Q₂` (bilinear), `Q₃`, `Q₄`, `Q₅` instead of a formal multilinear series.
* At a general order `k` the source is `PeriodMapJet.varSource`, the sum over the `2^{k−1} − 1`
  compositions of `k` into at least two blocks, and `PeriodMapJet.flowJet_spec` states that the
  jet solves the hierarchy; closed forms are written out for `k ≤ 5`, the orders that the flip
  and the degenerate flip read.
* Not covered: the locally Lipschitz and `C⁶` variants of the verdict in variational form (they
  are `DegenerateFlipOrbit`'s `_local` and `_of_contDiff` theorems, stated with the jet); the
  doubly degenerate case `c₂² + c₃ = 0 = c₅ + 3c₂c₄ − 2c₂⁴` (`Map.flat_jet_undecided`).
* Generic mathematics; no model family.

Source: Hartman, *Ordinary Differential Equations*, Ch. V (the higher variational equations);
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §5.4 and §9.5 (the Taylor
coefficients of a Poincaré map; the degenerate flip); Kuznetsov and Meijer, "Numerical normal forms
for codim 2 bifurcations of fixed points with at most two critical eigenvalues", SIAM J. Sci.
Comput. 26 (2005) (the fifth-order coefficient of the degenerate flip from the multilinear forms
of the map); the open item of `theorem/Periodic/JetVariation.lean` (Scope: "Not covered: the
identification at orders `≥ 4` with a closed form of the fourth and fifth variations");
`FormalMultilinearSeries.compAlongComposition_apply`, `composition_card` (Mathlib).

Results.
* `compositions_four`, `compositions_five` — the compositions with at least two blocks.
* `varSource_four`, `varSource_five` — the sources of the fourth and fifth equations of the
  hierarchy, term by term.
* `fourthSource`, `fourthVariation`, `fifthSource`, `fifthVariation` — the closed forms.
* `varSource_flowJet_four`, `flowJet_four`, `varSource_flowJet_five`, `flowJet_five` — the jet at
  orders four and five is the fourth and fifth variation.
* `multilinTwo`, `multilinTwo_apply`, `bilin_multilinTwo`, `norm_multilinTwo_le`,
  `continuous_multilinTwo`, `coeffSeries`, `coeffSeries_two`, `continuous_coeffSeries`,
  `norm_coeffSeries_le`, `sum_coeffSeries` — the coefficients `Q₂`, …, `Q₅` as a formal
  multilinear series.
* `fourthVariation_apply`, `hasDerivAt_fourthVariation`, `fifthVariation_apply`,
  `hasDerivAt_fifthVariation` — the fourth and fifth variational equations.
* `degenerateCoeff_jet_eq` — `c₄`, `c₅` and `c₅ + 3c₂c₄ − 2c₂⁴` in the variations.
* `periodMap_variations`, `orbit_flip_of_variations` — the expansion of the period map to fifth
  order and the flip verdict, both orders, in the variations.

Corrections.
None: an identification (the coefficients of `PeriodMapJet` at orders four and five and their
closed forms agree).

Family and connection conclusions.
None: static evidence on nonautonomous and periodic ODEs (the Taylor coefficients of the flow;
stability of a periodic solution at a period-doubling multiplier).
-/

noncomputable section
namespace powerlib.Periodic.JetVariationHigher

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative PeriodMapTaylor PeriodMapJet DegenerateFlipOrbit JetVariation

/-! ## The compositions of four and five into at least two blocks -/

/-- The compositions of `4` into at least two blocks: `(1, 3)`, `(3, 1)`, `(2, 2)`, `(1, 1, 2)`,
`(1, 2, 1)`, `(2, 1, 1)`, `(1, 1, 1, 1)` (the `2³ = 8` compositions but the single block). -/
@[tmio T, powerlib_foundation] theorem compositions_four :
    Finset.univ.filter (fun c : Composition 4 => 2 ≤ c.length) =
      {⟨[1, 3], by simp, by simp⟩, ⟨[3, 1], by simp, by simp⟩, ⟨[2, 2], by simp, by simp⟩,
        ⟨[1, 1, 2], by simp, by simp⟩, ⟨[1, 2, 1], by simp, by simp⟩,
        ⟨[2, 1, 1], by simp, by simp⟩, Composition.ones 4} := by
  have hu : (Finset.univ : Finset (Composition 4)) =
      {⟨[4], by simp, by simp⟩, ⟨[1, 3], by simp, by simp⟩, ⟨[3, 1], by simp, by simp⟩,
        ⟨[2, 2], by simp, by simp⟩, ⟨[1, 1, 2], by simp, by simp⟩, ⟨[1, 2, 1], by simp, by simp⟩,
        ⟨[2, 1, 1], by simp, by simp⟩, Composition.ones 4} := by
    refine (Finset.eq_univ_of_card _ ?_).symm
    rw [composition_card]
    decide
  rw [hu]
  decide

/-- The compositions of `5` into at least two blocks: `(1, 4)`, `(4, 1)`, `(2, 3)`, `(3, 2)`,
`(1, 1, 3)`, `(1, 3, 1)`, `(3, 1, 1)`, `(1, 2, 2)`, `(2, 1, 2)`, `(2, 2, 1)`, `(1, 1, 1, 2)`,
`(1, 1, 2, 1)`, `(1, 2, 1, 1)`, `(2, 1, 1, 1)`, `(1, 1, 1, 1, 1)` (the `2⁴ = 16` compositions but
the single block). -/
@[tmio T, powerlib_foundation] theorem compositions_five :
    Finset.univ.filter (fun c : Composition 5 => 2 ≤ c.length) =
      {⟨[1, 4], by simp, by simp⟩, ⟨[4, 1], by simp, by simp⟩, ⟨[2, 3], by simp, by simp⟩,
        ⟨[3, 2], by simp, by simp⟩, ⟨[1, 1, 3], by simp, by simp⟩,
        ⟨[1, 3, 1], by simp, by simp⟩, ⟨[3, 1, 1], by simp, by simp⟩,
        ⟨[1, 2, 2], by simp, by simp⟩, ⟨[2, 1, 2], by simp, by simp⟩,
        ⟨[2, 2, 1], by simp, by simp⟩, ⟨[1, 1, 1, 2], by simp, by simp⟩,
        ⟨[1, 1, 2, 1], by simp, by simp⟩, ⟨[1, 2, 1, 1], by simp, by simp⟩,
        ⟨[2, 1, 1, 1], by simp, by simp⟩, Composition.ones 5} := by
  have hu : (Finset.univ : Finset (Composition 5)) =
      {⟨[5], by simp, by simp⟩, ⟨[1, 4], by simp, by simp⟩, ⟨[4, 1], by simp, by simp⟩,
        ⟨[2, 3], by simp, by simp⟩, ⟨[3, 2], by simp, by simp⟩, ⟨[1, 1, 3], by simp, by simp⟩,
        ⟨[1, 3, 1], by simp, by simp⟩, ⟨[3, 1, 1], by simp, by simp⟩,
        ⟨[1, 2, 2], by simp, by simp⟩, ⟨[2, 1, 2], by simp, by simp⟩,
        ⟨[2, 2, 1], by simp, by simp⟩, ⟨[1, 1, 1, 2], by simp, by simp⟩,
        ⟨[1, 1, 2, 1], by simp, by simp⟩, ⟨[1, 2, 1, 1], by simp, by simp⟩,
        ⟨[2, 1, 1, 1], by simp, by simp⟩, Composition.ones 5} := by
    refine (Finset.eq_univ_of_card _ ?_).symm
    rw [composition_card]
    decide
  rw [hu]
  decide

/-! ## The sources of the fourth and fifth variational equations of the hierarchy -/

variable {X : Type*} [Fintype X] [DecidableEq X]

local notation "𝓢" => FormalMultilinearSeries ℝ (X → ℝ) (X → ℝ)

/-- Evaluates `Q ∘_c p (m)` at a concrete composition `c`: `Q_{|c|}` applied, block by block, to
`p_{c_i}` of the consecutive arguments of the block (`FormalMultilinearSeries.applyComposition`).
-/
local macro "comp_eval " q:term:max p:term:max : tactic => `(tactic| (
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  refine congrArg ($q _) (funext fun i => ?_)
  fin_cases i
  all_goals
    refine congrArg ($p _) (funext fun j => ?_)
    fin_cases j <;> rfl))

omit [Fintype X] [DecidableEq X] in
/-- The source of the fourth variational equation of the hierarchy, from the compositions
`(1, 3)`, `(3, 1)`, `(2, 2)`, `(1, 1, 2)`, `(1, 2, 1)`, `(2, 1, 1)`, `(1, 1, 1, 1)`:
`Q₂(p₁m₀, p₃(m₁, m₂, m₃)) + Q₂(p₃(m₀, m₁, m₂), p₁m₃) + Q₂(p₂(m₀, m₁), p₂(m₂, m₃)) +
Q₃(p₁m₀, p₁m₁, p₂(m₂, m₃)) + Q₃(p₁m₀, p₂(m₁, m₂), p₁m₃) + Q₃(p₂(m₀, m₁), p₁m₂, p₁m₃) +
Q₄(p₁m₀, p₁m₁, p₁m₂, p₁m₃)`. -/
@[tmio T, powerlib_foundation] theorem varSource_four (Q p : ℝ → 𝓢) (r : ℝ)
    (m : Fin 4 → X → ℝ) :
    varSource Q p 4 r m =
      Q r 2 ![p r 1 (fun _ => m 0), p r 3 ![m 1, m 2, m 3]] +
        Q r 2 ![p r 3 ![m 0, m 1, m 2], p r 1 (fun _ => m 3)] +
        Q r 2 ![p r 2 ![m 0, m 1], p r 2 ![m 2, m 3]] +
        Q r 3 ![p r 1 (fun _ => m 0), p r 1 (fun _ => m 1), p r 2 ![m 2, m 3]] +
        Q r 3 ![p r 1 (fun _ => m 0), p r 2 ![m 1, m 2], p r 1 (fun _ => m 3)] +
        Q r 3 ![p r 2 ![m 0, m 1], p r 1 (fun _ => m 2), p r 1 (fun _ => m 3)] +
        Q r 4 (fun i => p r 1 (fun _ => m i)) := by
  simp only [varSource, _root_.sum_apply]
  rw [compositions_four]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  simp only [add_assoc]
  repeat' refine congrArg₂ (· + ·) ?_ ?_
  all_goals comp_eval (Q r) (p r)

omit [Fintype X] [DecidableEq X] in
/-- The source of the fifth variational equation of the hierarchy, from the fifteen compositions
of `5` into at least two blocks (`compositions_five`): the four of length two
`Q₂(p₁m₀, p₄(m₁, …, m₄)) + Q₂(p₄(m₀, …, m₃), p₁m₄) + Q₂(p₂(m₀, m₁), p₃(m₂, m₃, m₄)) +
Q₂(p₃(m₀, m₁, m₂), p₂(m₃, m₄))`, the six of length three (one block `p₃`, or two blocks `p₂`),
the four of length four (one block `p₂`) and `Q₅(p₁m₀, …, p₁m₄)`. -/
@[tmio T, powerlib_foundation] theorem varSource_five (Q p : ℝ → 𝓢) (r : ℝ)
    (m : Fin 5 → X → ℝ) :
    varSource Q p 5 r m =
      Q r 2 ![p r 1 (fun _ => m 0), p r 4 ![m 1, m 2, m 3, m 4]] +
        Q r 2 ![p r 4 ![m 0, m 1, m 2, m 3], p r 1 (fun _ => m 4)] +
        Q r 2 ![p r 2 ![m 0, m 1], p r 3 ![m 2, m 3, m 4]] +
        Q r 2 ![p r 3 ![m 0, m 1, m 2], p r 2 ![m 3, m 4]] +
        Q r 3 ![p r 1 (fun _ => m 0), p r 1 (fun _ => m 1), p r 3 ![m 2, m 3, m 4]] +
        Q r 3 ![p r 1 (fun _ => m 0), p r 3 ![m 1, m 2, m 3], p r 1 (fun _ => m 4)] +
        Q r 3 ![p r 3 ![m 0, m 1, m 2], p r 1 (fun _ => m 3), p r 1 (fun _ => m 4)] +
        Q r 3 ![p r 1 (fun _ => m 0), p r 2 ![m 1, m 2], p r 2 ![m 3, m 4]] +
        Q r 3 ![p r 2 ![m 0, m 1], p r 1 (fun _ => m 2), p r 2 ![m 3, m 4]] +
        Q r 3 ![p r 2 ![m 0, m 1], p r 2 ![m 2, m 3], p r 1 (fun _ => m 4)] +
        Q r 4 ![p r 1 (fun _ => m 0), p r 1 (fun _ => m 1), p r 1 (fun _ => m 2),
          p r 2 ![m 3, m 4]] +
        Q r 4 ![p r 1 (fun _ => m 0), p r 1 (fun _ => m 1), p r 2 ![m 2, m 3],
          p r 1 (fun _ => m 4)] +
        Q r 4 ![p r 1 (fun _ => m 0), p r 2 ![m 1, m 2], p r 1 (fun _ => m 3),
          p r 1 (fun _ => m 4)] +
        Q r 4 ![p r 2 ![m 0, m 1], p r 1 (fun _ => m 2), p r 1 (fun _ => m 3),
          p r 1 (fun _ => m 4)] +
        Q r 5 (fun i => p r 1 (fun _ => m i)) := by
  simp only [varSource, _root_.sum_apply]
  rw [compositions_five]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  simp only [add_assoc]
  repeat' refine congrArg₂ (· + ·) ?_ ?_
  all_goals comp_eval (Q r) (p r)

/-! ## The fourth and fifth variations -/

variable {A : ℝ → Matrix X X ℝ} {Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ}
  {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ)}
  {Q₄ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 4 => X → ℝ) (X → ℝ)}
  {Q₅ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 5 => X → ℝ) (X → ℝ)}

/-- The source of the fourth variational equation: with `P₁ = Φ(r, s)`, `P₂ = secondVariation`
and `P₃ = thirdVariation` at the time `r`,
`Q₂(P₁m₀, P₃(m₁, m₂, m₃)) + Q₂(P₃(m₀, m₁, m₂), P₁m₃) + Q₂(P₂(m₀, m₁), P₂(m₂, m₃)) +
Q₃(P₁m₀, P₁m₁, P₂(m₂, m₃)) + Q₃(P₁m₀, P₂(m₁, m₂), P₁m₃) + Q₃(P₂(m₀, m₁), P₁m₂, P₁m₃) +
Q₄(P₁m₀, P₁m₁, P₁m₂, P₁m₃)`, one term for each composition of `4` into at least two blocks;
on the diagonal `m = (e, e, e, e)` it is `Q₂(y₁, y₃) + Q₂(y₃, y₁) + Q₂(y₂, y₂) +
Q₃(y₁, y₁, y₂) + Q₃(y₁, y₂, y₁) + Q₃(y₂, y₁, y₁) + Q₄(y₁, y₁, y₁, y₁)`. -/
def fourthSource (A : ℝ → Matrix X X ℝ) (Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ)
    (Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ))
    (Q₄ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 4 => X → ℝ) (X → ℝ)) (s : ℝ)
    (m : Fin 4 → X → ℝ) (r : ℝ) : X → ℝ :=
  Q₂ r (transition A r s *ᵥ m 0) (thirdVariation A Q₂ Q₃ s r ![m 1, m 2, m 3]) +
    Q₂ r (thirdVariation A Q₂ Q₃ s r ![m 0, m 1, m 2]) (transition A r s *ᵥ m 3) +
    Q₂ r (secondVariation A Q₂ s r (m 0) (m 1)) (secondVariation A Q₂ s r (m 2) (m 3)) +
    Q₃ r ![transition A r s *ᵥ m 0, transition A r s *ᵥ m 1,
      secondVariation A Q₂ s r (m 2) (m 3)] +
    Q₃ r ![transition A r s *ᵥ m 0, secondVariation A Q₂ s r (m 1) (m 2),
      transition A r s *ᵥ m 3] +
    Q₃ r ![secondVariation A Q₂ s r (m 0) (m 1), transition A r s *ᵥ m 2,
      transition A r s *ᵥ m 3] +
    Q₄ r (fun l => transition A r s *ᵥ m l)

/-- The fourth variation `P₄(t)`: the four-linear map whose value at `m` is the value at `t` of the
solution of `ẏ = A(r) y + fourthSource(m)(r)`, `y(s) = 0` (`fourthVariation_apply`), i.e.
`P₄(t)(m) = ∫ₛᵗ Φ(t, r) fourthSource(m)(r) dr`. It is defined by its values on quadruples of basis
vectors. -/
def fourthVariation (A : ℝ → Matrix X X ℝ) (Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ)
    (Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ))
    (Q₄ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 4 => X → ℝ) (X → ℝ)) (s t : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => X → ℝ) (X → ℝ) :=
  multilinOfBasis fun f => resp A (fourthSource A Q₂ Q₃ Q₄ s fun l => Pi.single (f l) 1) s t

/-- The source of the fifth variational equation: with `P₁ = Φ(r, s)`, `P₂ = secondVariation`,
`P₃ = thirdVariation` and `P₄ = fourthVariation` at the time `r`, one term for each of the
fifteen compositions of `5` into at least two blocks (`compositions_five`), in their order:
`Q₂(P₁m₀, P₄(m₁, …, m₄)) + Q₂(P₄(m₀, …, m₃), P₁m₄) + Q₂(P₂(m₀, m₁), P₃(m₂, m₃, m₄)) +
Q₂(P₃(m₀, m₁, m₂), P₂(m₃, m₄)) + Q₃(P₁m₀, P₁m₁, P₃(m₂, m₃, m₄)) + Q₃(P₁m₀, P₃(m₁, m₂, m₃), P₁m₄) +
Q₃(P₃(m₀, m₁, m₂), P₁m₃, P₁m₄) + Q₃(P₁m₀, P₂(m₁, m₂), P₂(m₃, m₄)) +
Q₃(P₂(m₀, m₁), P₁m₂, P₂(m₃, m₄)) + Q₃(P₂(m₀, m₁), P₂(m₂, m₃), P₁m₄) +
Q₄(P₁m₀, P₁m₁, P₁m₂, P₂(m₃, m₄)) + Q₄(P₁m₀, P₁m₁, P₂(m₂, m₃), P₁m₄) +
Q₄(P₁m₀, P₂(m₁, m₂), P₁m₃, P₁m₄) + Q₄(P₂(m₀, m₁), P₁m₂, P₁m₃, P₁m₄) + Q₅(P₁m₀, …, P₁m₄)`. -/
def fifthSource (A : ℝ → Matrix X X ℝ) (Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ)
    (Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ))
    (Q₄ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 4 => X → ℝ) (X → ℝ))
    (Q₅ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 5 => X → ℝ) (X → ℝ)) (s : ℝ)
    (m : Fin 5 → X → ℝ) (r : ℝ) : X → ℝ :=
  Q₂ r (transition A r s *ᵥ m 0) (fourthVariation A Q₂ Q₃ Q₄ s r ![m 1, m 2, m 3, m 4]) +
    Q₂ r (fourthVariation A Q₂ Q₃ Q₄ s r ![m 0, m 1, m 2, m 3]) (transition A r s *ᵥ m 4) +
    Q₂ r (secondVariation A Q₂ s r (m 0) (m 1)) (thirdVariation A Q₂ Q₃ s r ![m 2, m 3, m 4]) +
    Q₂ r (thirdVariation A Q₂ Q₃ s r ![m 0, m 1, m 2]) (secondVariation A Q₂ s r (m 3) (m 4)) +
    Q₃ r ![transition A r s *ᵥ m 0, transition A r s *ᵥ m 1,
      thirdVariation A Q₂ Q₃ s r ![m 2, m 3, m 4]] +
    Q₃ r ![transition A r s *ᵥ m 0, thirdVariation A Q₂ Q₃ s r ![m 1, m 2, m 3],
      transition A r s *ᵥ m 4] +
    Q₃ r ![thirdVariation A Q₂ Q₃ s r ![m 0, m 1, m 2], transition A r s *ᵥ m 3,
      transition A r s *ᵥ m 4] +
    Q₃ r ![transition A r s *ᵥ m 0, secondVariation A Q₂ s r (m 1) (m 2),
      secondVariation A Q₂ s r (m 3) (m 4)] +
    Q₃ r ![secondVariation A Q₂ s r (m 0) (m 1), transition A r s *ᵥ m 2,
      secondVariation A Q₂ s r (m 3) (m 4)] +
    Q₃ r ![secondVariation A Q₂ s r (m 0) (m 1), secondVariation A Q₂ s r (m 2) (m 3),
      transition A r s *ᵥ m 4] +
    Q₄ r ![transition A r s *ᵥ m 0, transition A r s *ᵥ m 1, transition A r s *ᵥ m 2,
      secondVariation A Q₂ s r (m 3) (m 4)] +
    Q₄ r ![transition A r s *ᵥ m 0, transition A r s *ᵥ m 1,
      secondVariation A Q₂ s r (m 2) (m 3), transition A r s *ᵥ m 4] +
    Q₄ r ![transition A r s *ᵥ m 0, secondVariation A Q₂ s r (m 1) (m 2),
      transition A r s *ᵥ m 3, transition A r s *ᵥ m 4] +
    Q₄ r ![secondVariation A Q₂ s r (m 0) (m 1), transition A r s *ᵥ m 2,
      transition A r s *ᵥ m 3, transition A r s *ᵥ m 4] +
    Q₅ r (fun l => transition A r s *ᵥ m l)

/-- The fifth variation `P₅(t)`: the five-linear map whose value at `m` is the value at `t` of the
solution of `ẏ = A(r) y + fifthSource(m)(r)`, `y(s) = 0` (`fifthVariation_apply`). It is defined
by its values on quintuples of basis vectors. -/
def fifthVariation (A : ℝ → Matrix X X ℝ) (Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ)
    (Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ))
    (Q₄ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 4 => X → ℝ) (X → ℝ))
    (Q₅ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 5 => X → ℝ) (X → ℝ)) (s t : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 5 => X → ℝ) (X → ℝ) :=
  multilinOfBasis fun f => resp A (fifthSource A Q₂ Q₃ Q₄ Q₅ s fun l => Pi.single (f l) 1) s t

/-! ## The identification -/

variable {Q : ℝ → FormalMultilinearSeries ℝ (X → ℝ) (X → ℝ)}

/-- The source of the fourth equation of the hierarchy along the jet is `fourthSource`, when the
coefficients `Q(r)₂`, `Q(r)₃`, `Q(r)₄` of the field are `Q₂` (read bilinearly), `Q₃`, `Q₄`. -/
@[tmio T, powerlib_foundation] theorem varSource_flowJet_four
    (hQ₂ : ∀ r a b, Q r 2 ![a, b] = Q₂ r a b) (hQ₃ : ∀ r, Q r 3 = Q₃ r)
    (hQ₄ : ∀ r, Q r 4 = Q₄ r) (s r : ℝ) (m : Fin 4 → X → ℝ) :
    varSource Q (flowJet A Q s) 4 r m = fourthSource A Q₂ Q₃ Q₄ s m r := by
  have hP : ∀ a b : X → ℝ, flowJet A Q s r 2 ![a, b] = secondVariation A Q₂ s r a b :=
    fun a b => by rw [← bilin_apply, bilin_flowJet_two hQ₂]
  rw [varSource_four]
  simp only [flowJet_one, hP, flowJet_three hQ₂ hQ₃, hQ₂, hQ₃, hQ₄]
  rfl

/-- **The fourth coefficient of the jet is the fourth variation.** If the coefficients of the
field are `Q(r)₂ = Q₂(r)` (read bilinearly), `Q(r)₃ = Q₃(r)`, `Q(r)₄ = Q₄(r)`, then
`flowJet A Q s t 4 = fourthVariation A Q₂ Q₃ Q₄ s t` for all `s`, `t`: both are defined by
their values on quadruples of basis vectors as responses of the same forced variational
equation (`varSource_flowJet_four`); no continuity is needed. -/
@[tmio T, powerlib_foundation] theorem flowJet_four (hQ₂ : ∀ r a b, Q r 2 ![a, b] = Q₂ r a b)
    (hQ₃ : ∀ r, Q r 3 = Q₃ r) (hQ₄ : ∀ r, Q r 4 = Q₄ r) (s t : ℝ) :
    flowJet A Q s t 4 = fourthVariation A Q₂ Q₃ Q₄ s t := by
  have h : flowJet A Q s t 4 = multilinOfBasis fun f => resp A (fun σ =>
      varSource Q (jetUpTo A Q s 2) 4 σ (fun l => Pi.single (f l) 1)) s t :=
    flowJet_succ_succ 2 t
  rw [h, fourthVariation]
  congr 1
  funext f
  congr 1
  funext σ
  have hj : varSource Q (jetUpTo A Q s 2) 4 σ = varSource Q (flowJet A Q s) 4 σ :=
    varSource_jetUpTo 2 σ
  rw [hj, varSource_flowJet_four hQ₂ hQ₃ hQ₄]

/-- The source of the fifth equation of the hierarchy along the jet is `fifthSource`. -/
@[tmio T, powerlib_foundation] theorem varSource_flowJet_five
    (hQ₂ : ∀ r a b, Q r 2 ![a, b] = Q₂ r a b) (hQ₃ : ∀ r, Q r 3 = Q₃ r)
    (hQ₄ : ∀ r, Q r 4 = Q₄ r) (hQ₅ : ∀ r, Q r 5 = Q₅ r) (s r : ℝ) (m : Fin 5 → X → ℝ) :
    varSource Q (flowJet A Q s) 5 r m = fifthSource A Q₂ Q₃ Q₄ Q₅ s m r := by
  have hP : ∀ a b : X → ℝ, flowJet A Q s r 2 ![a, b] = secondVariation A Q₂ s r a b :=
    fun a b => by rw [← bilin_apply, bilin_flowJet_two hQ₂]
  rw [varSource_five]
  simp only [flowJet_one, hP, flowJet_three hQ₂ hQ₃, flowJet_four hQ₂ hQ₃ hQ₄, hQ₂, hQ₃, hQ₄,
    hQ₅]
  rfl

/-- **The fifth coefficient of the jet is the fifth variation.** With `Q(r)₅ = Q₅(r)` as well,
`flowJet A Q s t 5 = fifthVariation A Q₂ Q₃ Q₄ Q₅ s t` for all `s`, `t`. -/
@[tmio T, powerlib_foundation] theorem flowJet_five (hQ₂ : ∀ r a b, Q r 2 ![a, b] = Q₂ r a b)
    (hQ₃ : ∀ r, Q r 3 = Q₃ r) (hQ₄ : ∀ r, Q r 4 = Q₄ r) (hQ₅ : ∀ r, Q r 5 = Q₅ r) (s t : ℝ) :
    flowJet A Q s t 5 = fifthVariation A Q₂ Q₃ Q₄ Q₅ s t := by
  have h : flowJet A Q s t 5 = multilinOfBasis fun f => resp A (fun σ =>
      varSource Q (jetUpTo A Q s 3) 5 σ (fun l => Pi.single (f l) 1)) s t :=
    flowJet_succ_succ 3 t
  rw [h, fifthVariation]
  congr 1
  funext f
  congr 1
  funext σ
  have hj : varSource Q (jetUpTo A Q s 3) 5 σ = varSource Q (flowJet A Q s) 5 σ :=
    varSource_jetUpTo 3 σ
  rw [hj, varSource_flowJet_five hQ₂ hQ₃ hQ₄ hQ₅]

/-! ## A field expansion with a bilinear quadratic coefficient as a formal multilinear series -/

section CoeffSeries

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The continuous multilinear map on `Fin 2` of a continuous bilinear map, `m ↦ B(m₀, m₁)`
(Mathlib `continuousMultilinearCurryLeftEquiv`, `continuousMultilinearCurryFin1`): the inverse
of `DegenerateFlipOrbit.bilin`. -/
def multilinTwo (B : E →L[ℝ] E →L[ℝ] F) : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) F).symm
    (((continuousMultilinearCurryFin1 ℝ E F).symm.toContinuousLinearEquiv :
      (E →L[ℝ] F) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F).comp B)

@[tmio T, powerlib_foundation] theorem multilinTwo_apply (B : E →L[ℝ] E →L[ℝ] F)
    (m : Fin 2 → E) : multilinTwo B m = B (m 0) (m 1) :=
  rfl

@[tmio T, powerlib_foundation] theorem bilin_multilinTwo (B : E →L[ℝ] E →L[ℝ] F) :
    bilin (multilinTwo B) = B := by
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  rw [bilin_apply, multilinTwo_apply]
  rfl

@[tmio T, powerlib_foundation] theorem norm_multilinTwo_le (B : E →L[ℝ] E →L[ℝ] F) :
    ‖multilinTwo B‖ ≤ ‖B‖ := by
  rw [multilinTwo, LinearIsometryEquiv.norm_map]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg B) ?_)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]
    exact ((continuousMultilinearCurryFin1 ℝ E F).symm.norm_map f).le

@[tmio T, powerlib_foundation] theorem continuous_multilinTwo {B : ℝ → E →L[ℝ] E →L[ℝ] F}
    (hB : Continuous B) : Continuous fun r => multilinTwo (B r) :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) F).symm.continuous.comp
    (continuous_const.clm_comp hB)

/-- The coefficients `Q₂` (bilinear), `Q₃`, `Q₄`, `Q₅` of an expansion of order five of a field
as a formal multilinear series: `Q₂` read on `Fin 2` (`multilinTwo`), zero at the other orders. -/
def coeffSeries (Q₂ : ℝ → E →L[ℝ] E →L[ℝ] E)
    (Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E)
    (Q₄ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) E)
    (Q₅ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 5 => E) E) (r : ℝ) :
    FormalMultilinearSeries ℝ E E
  | 2 => multilinTwo (Q₂ r)
  | 3 => Q₃ r
  | 4 => Q₄ r
  | 5 => Q₅ r
  | _ => 0

variable {Q₂ : ℝ → E →L[ℝ] E →L[ℝ] E}
  {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
  {Q₄ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) E}
  {Q₅ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 5 => E) E}

@[tmio T, powerlib_foundation] theorem coeffSeries_two (r : ℝ) (a b : E) :
    coeffSeries Q₂ Q₃ Q₄ Q₅ r 2 ![a, b] = Q₂ r a b :=
  multilinTwo_apply (Q₂ r) ![a, b]

@[tmio T, powerlib_foundation] theorem continuous_coeffSeries (hQ₂ : Continuous Q₂)
    (hQ₃ : Continuous Q₃) (hQ₄ : Continuous Q₄) (hQ₅ : Continuous Q₅) :
    ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => coeffSeries Q₂ Q₃ Q₄ Q₅ r k := by
  intro k hk1 hk2
  interval_cases k
  · exact continuous_multilinTwo hQ₂
  · exact hQ₃
  · exact hQ₄
  · exact hQ₅

@[tmio T, powerlib_foundation] theorem norm_coeffSeries_le {B : ℝ} {r : ℝ} (hB₂ : ‖Q₂ r‖ ≤ B)
    (hB₃ : ‖Q₃ r‖ ≤ B) (hB₄ : ‖Q₄ r‖ ≤ B) (hB₅ : ‖Q₅ r‖ ≤ B) :
    ∀ k, 2 ≤ k → k ≤ 5 → ‖coeffSeries Q₂ Q₃ Q₄ Q₅ r k‖ ≤ B := by
  intro k hk1 hk2
  interval_cases k
  · exact (norm_multilinTwo_le _).trans hB₂
  · exact hB₃
  · exact hB₄
  · exact hB₅

/-- On the diagonal the expansion of order five reads `Q₂(u, u) + Q₃(u³) + Q₄(u⁴) + Q₅(u⁵)`. -/
@[tmio T, powerlib_foundation] theorem sum_coeffSeries (r : ℝ) (u : E) :
    ∑ k ∈ Finset.Icc 2 5, coeffSeries Q₂ Q₃ Q₄ Q₅ r k (fun _ => u) =
      Q₂ r u u + Q₃ r (fun _ => u) + Q₄ r (fun _ => u) + Q₅ r (fun _ => u) := by
  rw [Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num),
    Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton]
  rfl

end CoeffSeries

/-! ## The fourth and fifth variations solve the forced variational equations -/

/-- The fourth variation at every argument: `P₄(t)(m)` is the value at `t` of the solution of
`ẏ = A(r) y + fourthSource(m)(r)`, `y(s) = 0`, for continuous coefficients (through
`flowJet_four` and `PeriodMapJet.flowJet_spec` for the series `coeffSeries`). -/
@[tmio T, powerlib_foundation] theorem fourthVariation_apply (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) (hQ₄ : Continuous Q₄) (s t : ℝ)
    (m : Fin 4 → X → ℝ) :
    fourthVariation A Q₂ Q₃ Q₄ s t m = resp A (fourthSource A Q₂ Q₃ Q₄ s m) s t := by
  have hc := continuous_coeffSeries hQ₂ hQ₃ hQ₄ (continuous_const (y := (0 :
    ContinuousMultilinearMap ℝ (fun _ : Fin 5 => X → ℝ) (X → ℝ))))
  rw [← flowJet_four (Q := coeffSeries Q₂ Q₃ Q₄ fun _ => 0) (Q₃ := Q₃) (Q₄ := Q₄)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl),
    (flowJet_spec hA hc 4 (by norm_num) (by norm_num)).2 (by norm_num) t m]
  congr 1
  funext σ
  exact varSource_flowJet_four (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) s σ m

/-- The fourth variational equation: `d/dr P₄(r)(m) = A(r) P₄(r)(m) + fourthSource(m)(r)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_fourthVariation (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) (hQ₄ : Continuous Q₄) (s : ℝ)
    (m : Fin 4 → X → ℝ) (r : ℝ) :
    HasDerivAt (fun r => fourthVariation A Q₂ Q₃ Q₄ s r m)
      (A r *ᵥ fourthVariation A Q₂ Q₃ Q₄ s r m + fourthSource A Q₂ Q₃ Q₄ s m r) r := by
  have hc := continuous_coeffSeries hQ₂ hQ₃ hQ₄ (continuous_const (y := (0 :
    ContinuousMultilinearMap ℝ (fun _ : Fin 5 => X → ℝ) (X → ℝ))))
  have e := fun r => flowJet_four (A := A) (Q := coeffSeries Q₂ Q₃ Q₄ fun _ => 0) (Q₃ := Q₃)
    (Q₄ := Q₄) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) s r
  have h := hasDerivAt_flowJet (s := s) hA hc (j := 4) (by norm_num) (by norm_num) m r
  rw [varSource_flowJet_four (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) s r m] at h
  simp only [e] at h
  exact h

/-- The fifth variation at every argument: `P₅(t)(m)` is the value at `t` of the solution of
`ẏ = A(r) y + fifthSource(m)(r)`, `y(s) = 0`, for continuous coefficients. -/
@[tmio T, powerlib_foundation] theorem fifthVariation_apply (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) (hQ₄ : Continuous Q₄) (hQ₅ : Continuous Q₅)
    (s t : ℝ) (m : Fin 5 → X → ℝ) :
    fifthVariation A Q₂ Q₃ Q₄ Q₅ s t m = resp A (fifthSource A Q₂ Q₃ Q₄ Q₅ s m) s t := by
  have hc := continuous_coeffSeries hQ₂ hQ₃ hQ₄ hQ₅
  rw [← flowJet_five (Q := coeffSeries Q₂ Q₃ Q₄ Q₅) (Q₃ := Q₃) (Q₄ := Q₄) (Q₅ := Q₅)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
    (flowJet_spec hA hc 5 (by norm_num) (by norm_num)).2 (by norm_num) t m]
  congr 1
  funext σ
  exact varSource_flowJet_five (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    s σ m

/-- The fifth variational equation: `d/dr P₅(r)(m) = A(r) P₅(r)(m) + fifthSource(m)(r)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_fifthVariation (hA : Continuous A)
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) (hQ₄ : Continuous Q₄) (hQ₅ : Continuous Q₅)
    (s : ℝ) (m : Fin 5 → X → ℝ) (r : ℝ) :
    HasDerivAt (fun r => fifthVariation A Q₂ Q₃ Q₄ Q₅ s r m)
      (A r *ᵥ fifthVariation A Q₂ Q₃ Q₄ Q₅ s r m + fifthSource A Q₂ Q₃ Q₄ Q₅ s m r) r := by
  have hc := continuous_coeffSeries hQ₂ hQ₃ hQ₄ hQ₅
  have e := fun r => flowJet_five (A := A) (Q := coeffSeries Q₂ Q₃ Q₄ Q₅) (Q₃ := Q₃) (Q₄ := Q₄)
    (Q₅ := Q₅) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s r
  have h := hasDerivAt_flowJet (s := s) hA hc (j := 5) (by norm_num) (by norm_num) m r
  rw [varSource_flowJet_five (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s r
    m] at h
  simp only [e] at h
  exact h

/-! ## The coefficients of the degenerate flip from the variational equations -/

open FlipReduction in
/-- **The coefficients `c₄`, `c₅` of the degenerate flip in the variations.** With `Q₂`, …, `Q₅`
corresponding to the coefficients of the jet, the coefficients
`c₄ = wm ⬝ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃` and `c₅ = wm ⬝ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄` of
`DegenerateFlipOrbit` (`P₂ = bilin (flowJet A Q s t 2)`, `Pⱼ = flowJet A Q s t j`) are, with the
variations `P₂ = secondVariation`, …, `P₅ = fifthVariation` and the homological corrections
`k₂`, `k₃`, `k₄`,
`c₄ = wm ⬝ P₄(vm⁴) + wm ⬝ P₃'(vm) k₂ + wm ⬝ (P₂(vm, k₃) + P₂(k₃, vm)) + wm ⬝ P₂(k₂, k₂)` and
`c₅ = wm ⬝ P₅(vm⁵) + wm ⬝ P₄'(vm) k₂ + wm ⬝ (P₃'(vm) k₃ + P₃'(k₂) vm) +
wm ⬝ (P₂(vm, k₄) + P₂(k₄, vm)) + wm ⬝ (P₂(k₂, k₃) + P₂(k₃, k₂))`
(`Pⱼ'(x) y = ∑ᵢ Pⱼ(x with y in slot i)`, `ContinuousMultilinearMap.linearDeriv`), and the
quantity `c₅ + 3c₂c₄ − 2c₂⁴` that decides the degenerate flip is the same for the jet and for the
variations. -/
@[tmio T, powerlib_foundation] theorem degenerateCoeff_jet_eq
    (hQ₂ : ∀ r a b, Q r 2 ![a, b] = Q₂ r a b) (hQ₃ : ∀ r, Q r 3 = Q₃ r) (hQ₄ : ∀ r, Q r 4 = Q₄ r)
    (hQ₅ : ∀ r, Q r 5 = Q₅ r) (s t : ℝ) (vm wm k₂ k₃ k₄ : X → ℝ) :
    wm ⬝ᵥ curveCoeff₄ (bilin (flowJet A Q s t 2)) (flowJet A Q s t 3) (flowJet A Q s t 4)
        vm k₂ k₃ =
      wm ⬝ᵥ fourthVariation A Q₂ Q₃ Q₄ s t (fun _ => vm) +
        wm ⬝ᵥ (thirdVariation A Q₂ Q₃ s t).linearDeriv (fun _ => vm) (fun _ => k₂) +
        wm ⬝ᵥ (secondVariation A Q₂ s t vm k₃ + secondVariation A Q₂ s t k₃ vm) +
        wm ⬝ᵥ secondVariation A Q₂ s t k₂ k₂ ∧
    wm ⬝ᵥ curveCoeff₅ (bilin (flowJet A Q s t 2)) (flowJet A Q s t 3) (flowJet A Q s t 4)
        (flowJet A Q s t 5) vm k₂ k₃ k₄ =
      wm ⬝ᵥ fifthVariation A Q₂ Q₃ Q₄ Q₅ s t (fun _ => vm) +
        wm ⬝ᵥ (fourthVariation A Q₂ Q₃ Q₄ s t).linearDeriv (fun _ => vm) (fun _ => k₂) +
        wm ⬝ᵥ ((thirdVariation A Q₂ Q₃ s t).linearDeriv (fun _ => vm) (fun _ => k₃) +
          (thirdVariation A Q₂ Q₃ s t).linearDeriv (fun _ => k₂) (fun _ => vm)) +
        wm ⬝ᵥ (secondVariation A Q₂ s t vm k₄ + secondVariation A Q₂ s t k₄ vm) +
        wm ⬝ᵥ (secondVariation A Q₂ s t k₂ k₃ + secondVariation A Q₂ s t k₃ k₂) ∧
    wm ⬝ᵥ curveCoeff₅ (bilin (flowJet A Q s t 2)) (flowJet A Q s t 3) (flowJet A Q s t 4)
          (flowJet A Q s t 5) vm k₂ k₃ k₄ +
        3 * (wm ⬝ᵥ bilin (flowJet A Q s t 2) vm vm) *
          (wm ⬝ᵥ curveCoeff₄ (bilin (flowJet A Q s t 2)) (flowJet A Q s t 3)
            (flowJet A Q s t 4) vm k₂ k₃) -
        2 * (wm ⬝ᵥ bilin (flowJet A Q s t 2) vm vm) ^ 4 =
      wm ⬝ᵥ curveCoeff₅ (secondVariation A Q₂ s t) (thirdVariation A Q₂ Q₃ s t)
          (fourthVariation A Q₂ Q₃ Q₄ s t) (fifthVariation A Q₂ Q₃ Q₄ Q₅ s t) vm k₂ k₃ k₄ +
        3 * (wm ⬝ᵥ secondVariation A Q₂ s t vm vm) *
          (wm ⬝ᵥ curveCoeff₄ (secondVariation A Q₂ s t) (thirdVariation A Q₂ Q₃ s t)
            (fourthVariation A Q₂ Q₃ Q₄ s t) vm k₂ k₃) -
        2 * (wm ⬝ᵥ secondVariation A Q₂ s t vm vm) ^ 4 := by
  rw [bilin_flowJet_two hQ₂, flowJet_three hQ₂ hQ₃, flowJet_four hQ₂ hQ₃ hQ₄,
    flowJet_five hQ₂ hQ₃ hQ₄ hQ₅]
  refine ⟨?_, ?_, rfl⟩ <;> simp only [curveCoeff₄, curveCoeff₅, dotProduct_add]

/-! ## The period map to fifth order and the flip verdict in variational form -/

/-- **The expansion of the period map to fifth order in the variations.** Under the hypotheses of
`PeriodMapJet.periodMap_jet` with `N = 5` and the expansion
`G(r, x_* + u) = G(r, x_*) + A(r) u + Q₂(r)(u, u) + Q₃(r)(u³) + Q₄(r)(u⁴) + Q₅(r)(u⁵) + O(‖u‖⁶)`
along `x_*` (continuous coefficients, `Q₂` bilinear, `‖Q_k(r)‖ ≤ B` on `[0, T]`), the period map
satisfies, with `p = x_*(0)`, `M = Φ(T, 0)` and the variations `P_j = P_j(T)`,
`‖P(p + e) − p − M e − P₂(e, e) − P₃(e³) − P₄(e⁴) − P₅(e⁵)‖ ≤ C ‖e‖⁶` for
`‖e‖ ≤ min 1 (ρ e^{−KT})`, `C = flowConst K T B c 5`. -/
@[tmio T, powerlib_foundation] theorem periodMap_variations {G : ℝ → (X → ℝ) → X → ℝ}
    {K : NNReal} (hGc : Continuous (uncurry G)) (hK : ∀ t, LipschitzWith K (G t))
    (hA : Continuous A) (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) (hQ₄ : Continuous Q₄)
    (hQ₅ : Continuous Q₅) {T B c ρ : ℝ} (hT : 0 ≤ T)
    (hAK : ∀ r ∈ Icc 0 T, ∀ v, ‖A r *ᵥ v‖ ≤ K * ‖v‖) (hB0 : 0 ≤ B)
    (hB₂ : ∀ r ∈ Icc 0 T, ‖Q₂ r‖ ≤ B) (hB₃ : ∀ r ∈ Icc 0 T, ‖Q₃ r‖ ≤ B)
    (hB₄ : ∀ r ∈ Icc 0 T, ‖Q₄ r‖ ≤ B) (hB₅ : ∀ r ∈ Icc 0 T, ‖Q₅ r‖ ≤ B) {xs : ℝ → X → ℝ}
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hper : xs T = xs 0)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) - A r *ᵥ u - Q₂ r u u -
      Q₃ r (fun _ => u) - Q₄ r (fun _ => u) - Q₅ r (fun _ => u)‖ ≤ c * ‖u‖ ^ 6)
    (e : X → ℝ) (he : ‖e‖ ≤ min 1 (ρ / Real.exp (K * T))) :
    ‖FlowDerivative.periodMap hGc hK T (xs 0 + e) - xs 0 - monodromy A T 0 *ᵥ e -
        secondVariation A Q₂ 0 T e e - thirdVariation A Q₂ Q₃ 0 T (fun _ => e) -
        fourthVariation A Q₂ Q₃ Q₄ 0 T (fun _ => e) -
        fifthVariation A Q₂ Q₃ Q₄ Q₅ 0 T (fun _ => e)‖ ≤
      flowConst K T B c 5 * ‖e‖ ^ 6 := by
  have h := periodMap_jet (Q := coeffSeries Q₂ Q₃ Q₄ Q₅) hGc hK hA (N := 5) (by norm_num)
    (continuous_coeffSeries hQ₂ hQ₃ hQ₄ hQ₅) hT hAK hB0
    (fun k hk1 hk2 r hr => norm_coeffSeries_le (hB₂ r hr) (hB₃ r hr) (hB₄ r hr) (hB₅ r hr) k hk1
      hk2) hxs hper
    (fun r hr u hu => by
      rw [sum_coeffSeries, sub_add_eq_sub_sub, sub_add_eq_sub_sub, sub_add_eq_sub_sub]
      exact hTay r hr u hu) e he
  have hs : ∑ j ∈ Finset.Icc 2 5, flowJet A (coeffSeries Q₂ Q₃ Q₄ Q₅) 0 T j (fun _ => e) =
      secondVariation A Q₂ 0 T e e + thirdVariation A Q₂ Q₃ 0 T (fun _ => e) +
        fourthVariation A Q₂ Q₃ Q₄ 0 T (fun _ => e) +
        fifthVariation A Q₂ Q₃ Q₄ Q₅ 0 T (fun _ => e) := by
    rw [Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num),
      Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton,
      ← bilin_diag, bilin_flowJet_two (Q := coeffSeries Q₂ Q₃ Q₄ Q₅) (fun _ _ _ => rfl)]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_) ?_
    · exact congrArg (fun P => P fun _ => e) (flowJet_three (Q := coeffSeries Q₂ Q₃ Q₄ Q₅)
        (Q₃ := Q₃) (fun _ _ _ => rfl) (fun _ => rfl) 0 T)
    · exact congrArg (fun P => P fun _ => e) (flowJet_four (Q := coeffSeries Q₂ Q₃ Q₄ Q₅)
        (Q₃ := Q₃) (Q₄ := Q₄) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) 0 T)
    · exact congrArg (fun P => P fun _ => e) (flowJet_five (Q := coeffSeries Q₂ Q₃ Q₄ Q₅)
        (Q₃ := Q₃) (Q₄ := Q₄) (Q₅ := Q₅) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) 0 T)
  rw [hs] at h
  simpa only [sub_add_eq_sub_sub] using h

section Orbit

variable {n : ℕ} {G : ℝ → (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

open FlipReduction in
/-- **The flip of a periodic solution decided from the variational equations up to order five.**
Let `G` be `T`-periodic, continuous, differentiable in `x` with `D_xG` jointly continuous and
`K`-Lipschitz in `x`, `x_*` a global solution with `x_*(T) = x_*(0)`, and let `G` have along `x_*`
the expansion
`G(r, x_* + u) = G(r, x_*) + D_xG u + Q₂(r)(u, u) + Q₃(r)(u³) + Q₄(r)(u⁴) + Q₅(r)(u⁵) + O(‖u‖⁶)`
(continuous coefficients, `Q₂` bilinear, remainder `c ‖u‖⁶` for `‖u‖ ≤ ρ`). Let
`M = Φ(T, 0)` have the simple multiplier `−1` (`M vm = −vm`, `wmᵀ M = −wmᵀ`, `wm ⬝ vm = 1`) with
the other multipliers inside the unit circle (`M + vm wmᵀ` Schur stable), and let
`P₂ = secondVariation`, `P₃ = thirdVariation`, `P₄ = fourthVariation`, `P₅ = fifthVariation` at
`(0, T)` (`A = jacobianAlong G x_*`): the responses at `T` of the forced variational equations
with the sources `secondSource`, `thirdSource`, `fourthSource`, `fifthSource`. With `k₂` solving
`(I − M) k₂ = P₂(vm, vm) − c₂ vm`, `c₂ = wm ⬝ P₂(vm, vm)`, `c₃ = wm ⬝ curveCoeff₃ P₂ P₃ vm k₂`:
* `c₂² + c₃ > 0`: the period map is locally asymptotically, not exponentially, stable at
  `x_*(0)`, and `x_*` is uniformly Lyapunov stable and uniformly attracting;
* `c₂² + c₃ < 0`: the period map and `x_*` are unstable, one escape radius for every initial
  time;
* `c₂² + c₃ = 0`: for `k₃`, `k₄` solving the next homological equations, `c₄`, `c₅` as in
  `degenerateCoeff_jet_eq`, the sign of `c₅ + 3c₂c₄ − 2c₂⁴` decides the same two alternatives.
This is `JetVariation.orbit_flip_of_jet` for the series `coeffSeries Q₂ Q₃ Q₄ Q₅`, whose jet is
identified with the variations by `bilin_flowJet_two`, `flowJet_three`, `flowJet_four`,
`flowJet_five`; the case `c₂² + c₃ = 0 = c₅ + 3c₂c₄ − 2c₂⁴` is left open. -/
@[tmio T, powerlib_foundation] theorem orbit_flip_of_variations
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {Q₄ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {Q₅ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) (hQ₄ : Continuous Q₄) (hQ₅ : Continuous Q₅)
    {c ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u) - Q₄ r (fun _ => u) -
        Q₅ r (fun _ => u)‖ ≤ c * ‖u‖ ^ 6)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hP₂ : P₂ = secondVariation (jacobianAlong G xs) Q₂ 0 T)
    (hP₃ : P₃ = thirdVariation (jacobianAlong G xs) Q₂ Q₃ 0 T)
    (hP₄ : P₄ = fourthVariation (jacobianAlong G xs) Q₂ Q₃ Q₄ 0 T)
    (hP₅ : P₅ = fifthVariation (jacobianAlong G xs) Q₂ Q₃ Q₄ Q₅ 0 T)
    {k₂ : Fin n → ℝ}
    (hk₂ : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm) :
    (0 < (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ →
      (Map.LocalAsymptoticStable (FlipOrbit.euclidMap (periodMap hGc hK T))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
        ¬ Map.LocallyExponentiallyStable (FlipOrbit.euclidMap (periodMap hGc hK T))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
      (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ), IsIntegralCurveOn x G (Ici τ) →
        ‖x τ - xs τ‖ < δ → ∀ t, τ ≤ t → ‖x t - xs t‖ < ε) ∧
      ∃ δ, 0 < δ ∧ ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ),
        IsIntegralCurveOn x G (Ici τ) → ‖x τ - xs τ‖ < δ → ∀ t, τ + S ≤ t → ‖x t - xs t‖ < ε) ∧
    ((wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ < 0 →
      Map.Unstable (FlipOrbit.euclidMap (periodMap hGc hK T))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∀ τ : ℝ, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici τ) ∧
        ‖x τ - xs τ‖ < δ ∧ ∃ t, τ ≤ t ∧ ε ≤ ‖x t - xs t‖) ∧
    ((wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂ = 0 →
      ∀ k₃ k₄ : Fin n → ℝ, -k₃ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₃ =
          curveCoeff₃ P₂ P₃ vm k₂ - (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂) • vm +
            (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂ →
        wm ⬝ᵥ k₃ = 0 →
        k₄ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₄ =
          curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ - (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
            ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
            (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃ →
        (0 < wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
            3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) -
            2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 →
          (Map.LocalAsymptoticStable (FlipOrbit.euclidMap (periodMap hGc hK T))
              ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
            ¬ Map.LocallyExponentiallyStable (FlipOrbit.euclidMap (periodMap hGc hK T))
              ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
          (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ),
            IsIntegralCurveOn x G (Ici τ) → ‖x τ - xs τ‖ < δ → ∀ t, τ ≤ t → ‖x t - xs t‖ < ε) ∧
          ∃ δ, 0 < δ ∧ ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ),
            IsIntegralCurveOn x G (Ici τ) → ‖x τ - xs τ‖ < δ → ∀ t, τ + S ≤ t →
              ‖x t - xs t‖ < ε) ∧
        (wm ⬝ᵥ curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
            3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) -
            2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 < 0 →
          Map.Unstable (FlipOrbit.euclidMap (periodMap hGc hK T))
              ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
          ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∀ τ : ℝ, ∃ x : ℝ → Fin n → ℝ,
            IsIntegralCurveOn x G (Ici τ) ∧ ‖x τ - xs τ‖ < δ ∧ ∃ t, τ ≤ t ∧ ε ≤ ‖x t - xs t‖)) := by
  have hQ₂' : ∀ r a b, coeffSeries Q₂ Q₃ Q₄ Q₅ r 2 ![a, b] = Q₂ r a b := fun _ _ _ => rfl
  refine orbit_flip_of_jet hGc hGd hD hK hT hGper hxs hfix
    (continuous_coeffSeries hQ₂ hQ₃ hQ₄ hQ₅) (c := c) hρ (fun r hr u hu => ?_) hv hw hwv hS
    (hP₂.trans (bilin_flowJet_two hQ₂' 0 T).symm)
    (hP₃.trans (flowJet_three hQ₂' (fun _ => rfl) 0 T).symm)
    (hP₄.trans (flowJet_four (Q₃ := Q₃) hQ₂' (fun _ => rfl) (fun _ => rfl) 0 T).symm)
    (hP₅.trans (flowJet_five (Q₃ := Q₃) (Q₄ := Q₄) hQ₂' (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) 0 T).symm) hk₂
  rw [sum_coeffSeries, sub_add_eq_sub_sub, sub_add_eq_sub_sub, sub_add_eq_sub_sub]
  exact hTay r hr u hu

end Orbit

end powerlib.Periodic.JetVariationHigher
