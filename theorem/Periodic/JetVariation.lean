import theorem.Periodic.DegenerateFlipOrbit

/-! # The jet of the flow at orders two and three is the second and third variation

`theorem/Periodic/PeriodMapTaylor.lean` expands the flow of `ẋ = G(t, x)` about a solution to
third order with a bilinear quadratic coefficient `Q₂` and a trilinear cubic one `Q₃`
(`secondVariation`, `thirdVariation`); `theorem/Periodic/PeriodMapJet.lean` expands it to every
order with multilinear coefficients `Q_k` on `Fin k` (`flowJet`). This file identifies the two at
orders two and three, so that the flip coefficient of `theorem/Periodic/FlipOrbit.lean` and the
coefficients `c₂`, `c₃` of `theorem/Periodic/DegenerateFlipOrbit.lean` are one and the same.

* The compositions of `2` into at least two blocks are `(1, 1)`, those of `3` are `(1, 2)`,
  `(2, 1)`, `(1, 1, 1)` (`compositions_two`, `compositions_three`); hence the sources of the
  hierarchy are `varSource₂(m) = Q₂(P₁m₀, P₁m₁)` and
  `varSource₃(m) = Q₂(P₁m₀, P₂(m₁, m₂)) + Q₂(P₂(m₀, m₁), P₁m₂) + Q₃(P₁m₀, P₁m₁, P₁m₂)`
  (`varSource_two`, `varSource_three`), the sources `secondSource`, `thirdSource` of
  `PeriodMapTaylor`.
* With `Q(r)₂(a, b) = Q₂(r)(a, b)` (the multilinear coefficient on `Fin 2` read as a bilinear map,
  `DegenerateFlipOrbit.bilin`) and `Q(r)₃ = Q₃(r)`:
  `bilin (flowJet A Q s t 2) = secondVariation A Q₂ s t` and
  `flowJet A Q s t 3 = thirdVariation A Q₂ Q₃ s t` for all `s`, `t` (`bilin_flowJet_two`,
  `flowJet_three`). Both sides are defined by their values on (pairs, triples of) basis vectors as
  responses of the same forced variational equations, so no continuity hypothesis is needed.
* Hence `c₂ = a` and `c₃ = b`: `wm ⬝ P₂(vm, vm)` and `wm ⬝ curveCoeff₃ P₂ P₃ vm k` of the jet are
  `wm ⬝ P₂(vm, vm)` and `wm ⬝ P₃(vm, vm, vm) + wm ⬝ (P₂(vm, k) + P₂(k, vm))` of the variations,
  and `c₂² + c₃ = a² + b` (`flipCoeff_jet_eq`): the hypothesis `c₂² + c₃ = 0` of
  `DegenerateFlipOrbit` is literally the degenerate case `a² + b = 0` of `FlipOrbit`, and the
  homological equation for `k₂` there is the equation for `k` here.
* For a field with the fifth-order expansion of `DegenerateFlipOrbit` both decisions are made from
  one set of coefficients of the period map (`orbit_flip_of_jet`): `c₂² + c₃ > 0` stable and
  `< 0` unstable (`FlipOrbitUniform`, the cubic expansion with `Q₂ = bilin Q(r)₂`, `Q₃ = Q(r)₃`
  and a quartic remainder derived from the fifth-order one), and on `c₂² + c₃ = 0` the sign of
  `c₅ + 3c₂c₄ − 2c₂⁴` (`DegenerateFlipOrbit`), all with constants uniform in the initial time.

Scope.
* `ℝ^X` (`X → ℝ`, finite `X`, sup norm), continuous time, as in
  `theorem/Periodic/PeriodMapTaylor.lean` and `theorem/Periodic/PeriodMapJet.lean`; the
  identifications hold for arbitrary matrix fields `A` and coefficient fields `Q`, `Q₂`, `Q₃`
  (no continuity, no symmetry), the combined verdict under the hypotheses of
  `DegenerateFlipOrbit.orbit_stable_of_degenerateFlip` on `ℝ^{Fin n}`.
* Not covered: the identification at orders `≥ 4` with a closed form of the fourth and fifth
  variations (there is none in the library besides `flowJet`); the doubly degenerate case
  `c₂² + c₃ = 0 = c₅ + 3c₂c₄ − 2c₂⁴` (`Map.flat_jet_undecided`).
* Generic mathematics; no model family.

Source: Hartman, *Ordinary Differential Equations*, Ch. V (the higher variational equations);
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §5.4 and §9.5 (the Taylor
coefficients of a Poincaré map; the flip and the degenerate flip); the open item of
`theorem/Periodic/PeriodMapJet.lean` (Scope: "their identification with `secondVariation`,
`thirdVariation` of `PeriodMapTaylor` (where `Q₂` is a bilinear map) is not stated");
`FormalMultilinearSeries.applyComposition_ones` (Mathlib).

Results.
* `compositions_two`, `compositions_three` — the compositions with at least two blocks.
* `compAlongComposition_ones_two`, `compAlongComposition_one_two`,
  `compAlongComposition_two_one`, `compAlongComposition_ones_three` — the composition of two
  formal multilinear series along them.
* `varSource_two`, `varSource_three` — the sources of the second and third variational equations
  of the hierarchy.
* `bilin_multilinOfBasis` — interpolation on pairs of basis vectors, read bilinearly.
* `bilin_flowJet_two`, `flowJet_three` — the jet at orders two and three is the second and third
  variation.
* `flipCoeff_jet_eq` — `c₂ = a`, `c₃ = b`, `c₂² + c₃ = a² + b`.
* `continuous_bilin`, `orbit_flip_of_jet` — the flip of a periodic solution decided from the
  fifth-order jet, nondegenerate and degenerate, with one set of coefficients.

Corrections.
None: an identification (the coefficients of `PeriodMapJet` and `PeriodMapTaylor` agree).

Family and connection conclusions.
None: static evidence on nonautonomous and periodic ODEs (the Taylor coefficients of the flow;
stability of a periodic solution at a period-doubling multiplier).
-/

noncomputable section
namespace powerlib.Periodic.JetVariation

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative PeriodMapTaylor PeriodMapJet DegenerateFlipOrbit

/-! ## The compositions of two and three into at least two blocks -/

/-- The only composition of `2` into at least two blocks is `(1, 1)`. -/
@[tmio T, powerlib_foundation] theorem compositions_two :
    Finset.univ.filter (fun c : Composition 2 => 2 ≤ c.length) = {Composition.ones 2} := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    exact Composition.eq_ones_iff_length.2 (le_antisymm c.length_le h)
  · rintro rfl
    simp

/-- The compositions of `3` into at least two blocks are `(1, 2)`, `(2, 1)` and `(1, 1, 1)`. -/
@[tmio T, powerlib_foundation] theorem compositions_three :
    Finset.univ.filter (fun c : Composition 3 => 2 ≤ c.length) =
      {⟨[1, 2], by simp, by simp⟩, ⟨[2, 1], by simp, by simp⟩, Composition.ones 3} := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    obtain ⟨bl, hpos, hsum⟩ := c
    simp only [Composition.length] at h
    rcases bl with _ | ⟨a, _ | ⟨b, _ | ⟨x, _ | ⟨y, l⟩⟩⟩⟩
    · simp at h
    · simp at h
    · have ha := hpos (List.mem_cons_self ..)
      have hb := hpos (by simp : b ∈ [a, b])
      simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
      have : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; rfl
      · right; left; rfl
    · have ha := hpos (List.mem_cons_self ..)
      have hb := hpos (by simp : b ∈ [a, b, x])
      have hx := hpos (by simp : x ∈ [a, b, x])
      simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
      obtain ⟨rfl, rfl, rfl⟩ : a = 1 ∧ b = 1 ∧ x = 1 := by omega
      right; right; rfl
    · have ha := hpos (List.mem_cons_self ..)
      have hb := hpos (by simp : b ∈ a :: b :: x :: y :: l)
      have hx := hpos (by simp : x ∈ a :: b :: x :: y :: l)
      have hy := hpos (by simp : y ∈ a :: b :: x :: y :: l)
      simp only [List.sum_cons] at hsum
      omega
  · rintro (rfl | rfl | rfl) <;> decide

section Series

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul ℝ E]

/-- `Q ∘_{(1,1)} p (m) = Q₂(p₁(m₀), p₁(m₁))`. -/
@[tmio T, powerlib_foundation] theorem compAlongComposition_ones_two
    (Q p : FormalMultilinearSeries ℝ E E) (m : Fin 2 → E) :
    Q.compAlongComposition p (Composition.ones 2) m =
      Q 2 ![p 1 (fun _ => m 0), p 1 (fun _ => m 1)] := by
  rw [FormalMultilinearSeries.compAlongComposition_apply,
    FormalMultilinearSeries.applyComposition_ones]
  show Q 2 _ = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `Q ∘_{(1,2)} p (m) = Q₂(p₁(m₀), p₂(m₁, m₂))`. -/
@[tmio T, powerlib_foundation] theorem compAlongComposition_one_two
    (Q p : FormalMultilinearSeries ℝ E E) (m : Fin 3 → E) :
    Q.compAlongComposition p ⟨[1, 2], by simp, by simp⟩ m =
      Q 2 ![p 1 (fun _ => m 0), p 2 ![m 1, m 2]] := by
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  show Q 2 _ = _
  congr 1
  funext i
  fin_cases i
  · show p 1 _ = p 1 _
    congr 1
    funext j
    fin_cases j
    rfl
  · show p 2 _ = p 2 _
    congr 1
    funext j
    fin_cases j <;> rfl

/-- `Q ∘_{(2,1)} p (m) = Q₂(p₂(m₀, m₁), p₁(m₂))`. -/
@[tmio T, powerlib_foundation] theorem compAlongComposition_two_one
    (Q p : FormalMultilinearSeries ℝ E E) (m : Fin 3 → E) :
    Q.compAlongComposition p ⟨[2, 1], by simp, by simp⟩ m =
      Q 2 ![p 2 ![m 0, m 1], p 1 (fun _ => m 2)] := by
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  show Q 2 _ = _
  congr 1
  funext i
  fin_cases i
  · show p 2 _ = p 2 _
    congr 1
    funext j
    fin_cases j <;> rfl
  · show p 1 _ = p 1 _
    congr 1
    funext j
    fin_cases j
    rfl

/-- `Q ∘_{(1,1,1)} p (m) = Q₃(p₁(m₀), p₁(m₁), p₁(m₂))`. -/
@[tmio T, powerlib_foundation] theorem compAlongComposition_ones_three
    (Q p : FormalMultilinearSeries ℝ E E) (m : Fin 3 → E) :
    Q.compAlongComposition p (Composition.ones 3) m = Q 3 (fun i => p 1 (fun _ => m i)) := by
  rw [FormalMultilinearSeries.compAlongComposition_apply,
    FormalMultilinearSeries.applyComposition_ones]
  rfl

end Series

/-! ## The sources of the second and third variational equations -/

variable {X : Type*} [Fintype X] [DecidableEq X]

local notation "𝓢" => FormalMultilinearSeries ℝ (X → ℝ) (X → ℝ)

omit [Fintype X] [DecidableEq X] in
/-- The source of the second variational equation: `Q₂(p₁(m₀), p₁(m₁))`. -/
@[tmio T, powerlib_foundation] theorem varSource_two (Q p : ℝ → 𝓢) (r : ℝ)
    (m : Fin 2 → X → ℝ) :
    varSource Q p 2 r m = Q r 2 ![p r 1 (fun _ => m 0), p r 1 (fun _ => m 1)] := by
  simp only [varSource, _root_.sum_apply]
  rw [compositions_two, Finset.sum_singleton]
  exact compAlongComposition_ones_two (Q r) (p r) m

omit [Fintype X] [DecidableEq X] in
/-- The source of the third variational equation, from the compositions `(1, 2)`, `(2, 1)`,
`(1, 1, 1)`: `Q₂(p₁(m₀), p₂(m₁, m₂)) + Q₂(p₂(m₀, m₁), p₁(m₂)) + Q₃(p₁(m₀), p₁(m₁), p₁(m₂))`. -/
@[tmio T, powerlib_foundation] theorem varSource_three (Q p : ℝ → 𝓢) (r : ℝ)
    (m : Fin 3 → X → ℝ) :
    varSource Q p 3 r m = Q r 2 ![p r 1 (fun _ => m 0), p r 2 ![m 1, m 2]] +
      Q r 2 ![p r 2 ![m 0, m 1], p r 1 (fun _ => m 2)] +
        Q r 3 (fun i => p r 1 (fun _ => m i)) := by
  simp only [varSource, _root_.sum_apply]
  rw [compositions_three, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, add_assoc]
  exact congrArg₂ (· + ·) (compAlongComposition_one_two (Q r) (p r) m)
    (congrArg₂ (· + ·) (compAlongComposition_two_one (Q r) (p r) m)
      (compAlongComposition_ones_three (Q r) (p r) m))

/-! ## Interpolation on pairs of basis vectors -/

omit [DecidableEq X] in
/-- A multilinear map on `Fin 2` defined by its values on pairs of basis vectors, read
bilinearly, is the bilinear map with the same values. -/
@[tmio T, powerlib_foundation] theorem bilin_multilinOfBasis (c : (Fin 2 → X) → X → ℝ) :
    bilin (multilinOfBasis c) = bilinOfBasis fun i j => c ![i, j] := by
  refine ContinuousLinearMap.ext fun e => ContinuousLinearMap.ext fun f => ?_
  rw [bilin_apply, multilinOfBasis_apply, bilinOfBasis_apply, ← Finset.sum_product',
    Finset.univ_product_univ]
  refine Fintype.sum_equiv (piFinTwoEquiv fun _ => X) _ _ fun g => ?_
  have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
  simp only [Fin.prod_univ_two, piFinTwoEquiv_apply]
  conv_lhs => rw [hg]
  rfl

/-! ## The identification -/

variable {A : ℝ → Matrix X X ℝ} {Q : ℝ → FormalMultilinearSeries ℝ (X → ℝ) (X → ℝ)}
  {Q₂ : ℝ → (X → ℝ) →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ}
  {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => X → ℝ) (X → ℝ)}

/-- **The second coefficient of the jet is the second variation.** If the quadratic coefficient
of the field, a multilinear map on `Fin 2`, is the bilinear map `Q₂`
(`Q(r)₂(a, b) = Q₂(r)(a, b)`), then `P₂(t) = flowJet A Q s t 2`, read bilinearly, is the second
variation `secondVariation A Q₂ s t`, for every `s`, `t`. No continuity is needed: both are
defined by the same responses on pairs of basis vectors. -/
@[tmio T, powerlib_foundation] theorem bilin_flowJet_two
    (hQ₂ : ∀ r a b, Q r 2 ![a, b] = Q₂ r a b) (s t : ℝ) :
    bilin (flowJet A Q s t 2) = secondVariation A Q₂ s t := by
  have h : flowJet A Q s t 2 = multilinOfBasis fun f => resp A (fun σ =>
      varSource Q (jetUpTo A Q s 0) 2 σ (fun l => Pi.single (f l) 1)) s t :=
    flowJet_succ_succ 0 t
  rw [h, bilin_multilinOfBasis, secondVariation]
  congr 1
  funext i j
  congr 1
  funext σ
  rw [varSource_two, ← flowJet_eq_jetUpTo (N := 0) le_rfl, flowJet_one, flowJet_one, hQ₂]
  rfl

/-- **The third coefficient of the jet is the third variation.** If the quadratic coefficient of
the field is the bilinear map `Q₂` and the cubic one is `Q₃`, then `flowJet A Q s t 3` is the
third variation `thirdVariation A Q₂ Q₃ s t`: the source of the third equation of the hierarchy
(compositions `(1, 2)`, `(2, 1)`, `(1, 1, 1)`) is `thirdSource`, through
`bilin_flowJet_two` at every time. -/
@[tmio T, powerlib_foundation] theorem flowJet_three (hQ₂ : ∀ r a b, Q r 2 ![a, b] = Q₂ r a b)
    (hQ₃ : ∀ r, Q r 3 = Q₃ r) (s t : ℝ) :
    flowJet A Q s t 3 = thirdVariation A Q₂ Q₃ s t := by
  have h : flowJet A Q s t 3 = multilinOfBasis fun f => resp A (fun σ =>
      varSource Q (jetUpTo A Q s 1) 3 σ (fun l => Pi.single (f l) 1)) s t :=
    flowJet_succ_succ 1 t
  rw [h, thirdVariation]
  congr 1
  funext f
  congr 1
  funext σ
  have h1 : jetUpTo A Q s 1 σ 1 = flowJet A Q s σ 1 := (flowJet_eq_jetUpTo (by norm_num) σ).symm
  have h2 : jetUpTo A Q s 1 σ 2 = flowJet A Q s σ 2 := (flowJet_eq_jetUpTo (by norm_num) σ).symm
  have hP : ∀ a b : X → ℝ, flowJet A Q s σ 2 ![a, b] = secondVariation A Q₂ s σ a b := fun a b => by
    rw [← bilin_apply, bilin_flowJet_two hQ₂]
  rw [varSource_three, h1, h2, flowJet_one, flowJet_one, hP, hP, hQ₂, hQ₂, hQ₃]
  simp only [flowJet_one]
  rfl

/-- **The flip coefficients of the two expansions coincide.** With `Q₂`, `Q₃` corresponding to the
coefficients `Q(r)₂`, `Q(r)₃` of the jet, the coefficients `c₂ = wm ⬝ P₂(vm, vm)` and
`c₃ = wm ⬝ curveCoeff₃ P₂ P₃ vm k` of `DegenerateFlipOrbit` (`P₂ = bilin (flowJet A Q s t 2)`,
`P₃ = flowJet A Q s t 3`) are the coefficients `a = wm ⬝ P₂(vm, vm)` and
`b = wm ⬝ P₃(vm, vm, vm) + wm ⬝ (P₂(vm, k) + P₂(k, vm))` of `FlipOrbit`
(`P₂ = secondVariation`, `P₃ = thirdVariation`), and hence `c₂² + c₃ = a² + b`. -/
@[tmio T, powerlib_foundation] theorem flipCoeff_jet_eq
    (hQ₂ : ∀ r a b, Q r 2 ![a, b] = Q₂ r a b) (hQ₃ : ∀ r, Q r 3 = Q₃ r) (s t : ℝ)
    (vm wm k : X → ℝ) :
    wm ⬝ᵥ bilin (flowJet A Q s t 2) vm vm = wm ⬝ᵥ secondVariation A Q₂ s t vm vm ∧
      wm ⬝ᵥ FlipReduction.curveCoeff₃ (bilin (flowJet A Q s t 2)) (flowJet A Q s t 3) vm k =
        wm ⬝ᵥ thirdVariation A Q₂ Q₃ s t (fun _ => vm) +
          wm ⬝ᵥ (secondVariation A Q₂ s t vm k + secondVariation A Q₂ s t k vm) ∧
      (wm ⬝ᵥ bilin (flowJet A Q s t 2) vm vm) ^ 2 +
          wm ⬝ᵥ FlipReduction.curveCoeff₃ (bilin (flowJet A Q s t 2)) (flowJet A Q s t 3) vm k =
        (wm ⬝ᵥ secondVariation A Q₂ s t vm vm) ^ 2 +
          (wm ⬝ᵥ thirdVariation A Q₂ Q₃ s t (fun _ => vm) +
            wm ⬝ᵥ (secondVariation A Q₂ s t vm k + secondVariation A Q₂ s t k vm)) := by
  rw [bilin_flowJet_two hQ₂, flowJet_three hQ₂ hQ₃, FlipReduction.curveCoeff₃, dotProduct_add]
  exact ⟨rfl, rfl, rfl⟩

/-! ## One flip verdict from the fifth-order jet -/

section Orbit

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The bilinear map of a continuous family of multilinear maps on `Fin 2` is continuous. -/
@[tmio T, powerlib_foundation] theorem continuous_bilin
    {f : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F} (hf : Continuous f) :
    Continuous fun r => bilin (f r) :=
  continuous_const.clm_comp
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) F).continuous.comp hf)

variable {n : ℕ} {G : ℝ → (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

set_option maxHeartbeats 1000000 in
/-- **The flip of a periodic solution decided from the fifth-order jet of the field, at both
orders.** Under the hypotheses of `DegenerateFlipOrbit.orbit_stable_of_degenerateFlip` (a
`T`-periodic, `K`-Lipschitz field with the fifth-order expansion along `x_*`, coefficients `Q_k`;
`M = Φ(T, 0)` with the simple multiplier `−1` and stable complement; `Pⱼ = flowJet A Q 0 T j`,
`P₂` read bilinearly; `k₂` solving `(I − M) k₂ = P₂(vm, vm) − c₂ vm`), with the one set of
coefficients `c₂ = wm ⬝ P₂(vm, vm)`, `c₃ = wm ⬝ curveCoeff₃ P₂ P₃ vm k₂` of the period map:
* `c₂² + c₃ > 0`: the period map is locally asymptotically, not exponentially, stable at `x_*(0)`
  and `x_*` is uniformly Lyapunov stable and uniformly attracting
  (`FlipOrbitUniform.orbit_uniformly_stable_of_flipCoeff_pos`, through `flipCoeff_jet_eq`:
  `c₂² + c₃` is the flip coefficient `a² + b` of `FlipOrbit`);
* `c₂² + c₃ < 0`: the period map and `x_*` are unstable, one escape radius for every initial time
  (`FlipOrbitUniform.orbit_uniformly_unstable_of_flipCoeff_neg`);
* `c₂² + c₃ = 0`: for `k₃`, `k₄` solving the next homological equations, the sign of
  `c₅ + 3c₂c₄ − 2c₂⁴` decides the same two alternatives (`DegenerateFlipOrbit`).
The cubic expansion of `FlipOrbit` (`Q₂ = bilin Q(r)₂`, `Q₃ = Q(r)₃`, quartic remainder) is
derived from the fifth-order one; the case `c₂² + c₃ = 0 = c₅ + 3c₂c₄ − 2c₂⁴` is left open. -/
@[tmio T, powerlib_foundation] theorem orbit_flip_of_jet
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q : ℝ → FormalMultilinearSeries ℝ (Fin n → ℝ) (Fin n → ℝ)}
    (hQ : ∀ k, 2 ≤ k → k ≤ 5 → Continuous fun r => Q r k) {c ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - ∑ k ∈ Finset.Icc 2 5, Q r k (fun _ => u)‖ ≤ c * ‖u‖ ^ 6)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    {P₄ : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin n → ℝ) (Fin n → ℝ)}
    {P₅ : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => Fin n → ℝ) (Fin n → ℝ)}
    (hP₂ : P₂ = bilin (flowJet (jacobianAlong G xs) Q 0 T 2))
    (hP₃ : P₃ = flowJet (jacobianAlong G xs) Q 0 T 3)
    (hP₄ : P₄ = flowJet (jacobianAlong G xs) Q 0 T 4)
    (hP₅ : P₅ = flowJet (jacobianAlong G xs) Q 0 T 5)
    {k₂ : Fin n → ℝ}
    (hk₂ : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm) :
    (0 < (wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ FlipReduction.curveCoeff₃ P₂ P₃ vm k₂ →
      (Map.LocalAsymptoticStable (FlipOrbit.euclidMap (periodMap hGc hK T))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
        ¬ Map.LocallyExponentiallyStable (FlipOrbit.euclidMap (periodMap hGc hK T))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
      (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ), IsIntegralCurveOn x G (Ici τ) →
        ‖x τ - xs τ‖ < δ → ∀ t, τ ≤ t → ‖x t - xs t‖ < ε) ∧
      ∃ δ, 0 < δ ∧ ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ),
        IsIntegralCurveOn x G (Ici τ) → ‖x τ - xs τ‖ < δ → ∀ t, τ + S ≤ t → ‖x t - xs t‖ < ε) ∧
    ((wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ FlipReduction.curveCoeff₃ P₂ P₃ vm k₂ < 0 →
      Map.Unstable (FlipOrbit.euclidMap (periodMap hGc hK T))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∀ τ : ℝ, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici τ) ∧
        ‖x τ - xs τ‖ < δ ∧ ∃ t, τ ≤ t ∧ ε ≤ ‖x t - xs t‖) ∧
    ((wm ⬝ᵥ P₂ vm vm) ^ 2 + wm ⬝ᵥ FlipReduction.curveCoeff₃ P₂ P₃ vm k₂ = 0 →
      ∀ k₃ k₄ : Fin n → ℝ, -k₃ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₃ =
          FlipReduction.curveCoeff₃ P₂ P₃ vm k₂ -
            (wm ⬝ᵥ FlipReduction.curveCoeff₃ P₂ P₃ vm k₂) • vm + (2 * (wm ⬝ᵥ P₂ vm vm)) • k₂ →
        wm ⬝ᵥ k₃ = 0 →
        k₄ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₄ =
          FlipReduction.curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃ -
            (wm ⬝ᵥ FlipReduction.curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) • vm -
            ((wm ⬝ᵥ P₂ vm vm) ^ 2 - 2 * (wm ⬝ᵥ FlipReduction.curveCoeff₃ P₂ P₃ vm k₂)) • k₂ -
            (3 * (wm ⬝ᵥ P₂ vm vm)) • k₃ →
        (0 < wm ⬝ᵥ FlipReduction.curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
            3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ FlipReduction.curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) -
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
        (wm ⬝ᵥ FlipReduction.curveCoeff₅ P₂ P₃ P₄ P₅ vm k₂ k₃ k₄ +
            3 * (wm ⬝ᵥ P₂ vm vm) * (wm ⬝ᵥ FlipReduction.curveCoeff₄ P₂ P₃ P₄ vm k₂ k₃) -
            2 * (wm ⬝ᵥ P₂ vm vm) ^ 4 < 0 →
          Map.Unstable (FlipOrbit.euclidMap (periodMap hGc hK T))
              ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
          ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∀ τ : ℝ, ∃ x : ℝ → Fin n → ℝ,
            IsIntegralCurveOn x G (Ici τ) ∧ ‖x τ - xs τ‖ < δ ∧ ∃ t, τ ≤ t ∧ ε ≤ ‖x t - xs t‖)) := by
  -- the cubic data of `FlipOrbit` from the fifth-order jet
  set Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ := fun r => bilin (Q r 2) with hQ₂d
  set Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ) :=
    fun r => Q r 3 with hQ₃d
  have hQ₂ : ∀ r a b, Q r 2 ![a, b] = Q₂ r a b := fun r a b => (bilin_apply _ a b).symm
  have hQ₃ : ∀ r, Q r 3 = Q₃ r := fun r => rfl
  have hQ₂c : Continuous Q₂ := continuous_bilin (hQ 2 le_rfl (by norm_num))
  have hQ₃c : Continuous Q₃ := hQ 3 (by norm_num) (by norm_num)
  obtain ⟨B, hB0, hB⟩ := exists_bound_coeff (Q := Q) (s := 0) (t := T) 5 hQ
  have hQk : ∀ k, 2 ≤ k → k ≤ 5 → ∀ r ∈ Icc 0 T, ∀ u : Fin n → ℝ,
      ‖Q r k (fun _ => u)‖ ≤ B * ‖u‖ ^ k := fun k hk1 hk2 r hr u => by
    refine ((Q r k).le_opNorm _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (hB k hk1 hk2 r hr) (by positivity)
  have hTay3 : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ min ρ 1 → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ (max c 0 + 2 * B) * ‖u‖ ^ 4 := by
    intro r hr u hu
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
    have hu1 : ‖u‖ ≤ 1 := hu.trans (min_le_right _ _)
    have h6 := hTay r hr u (hu.trans (min_le_left _ _))
    rw [Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num),
      Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton] at h6
    have e : G r (xs r + u) - G r (xs r) - fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u) =
        (G r (xs r + u) - G r (xs r) - fderiv ℝ (G r) (xs r) u -
          (Q r 2 (fun _ => u) + Q r 3 (fun _ => u) + Q r 4 (fun _ => u) + Q r 5 (fun _ => u))) +
          Q r 4 (fun _ => u) + Q r 5 (fun _ => u) := by
      rw [hQ₂d, bilin_diag]
      abel
    rw [e]
    have h4 := hQk 4 (by norm_num) (by norm_num) r hr u
    have h5 := hQk 5 (by norm_num) (by norm_num) r hr u
    have p5 : ‖u‖ ^ 5 ≤ ‖u‖ ^ 4 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
    have p6 : ‖u‖ ^ 6 ≤ ‖u‖ ^ 4 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
    have hc6 : c * ‖u‖ ^ 6 ≤ max c 0 * ‖u‖ ^ 4 :=
      (mul_le_mul_of_nonneg_right (le_max_left c 0) (by positivity)).trans
        (mul_le_mul_of_nonneg_left p6 (le_max_right c 0))
    have hb5 : B * ‖u‖ ^ 5 ≤ B * ‖u‖ ^ 4 := mul_le_mul_of_nonneg_left p5 hB0
    calc _ ≤ ‖G r (xs r + u) - G r (xs r) - fderiv ℝ (G r) (xs r) u -
          (Q r 2 (fun _ => u) + Q r 3 (fun _ => u) + Q r 4 (fun _ => u) + Q r 5 (fun _ => u))‖ +
          ‖Q r 4 (fun _ => u)‖ + ‖Q r 5 (fun _ => u)‖ := norm_add₃_le
      _ ≤ c * ‖u‖ ^ 6 + B * ‖u‖ ^ 4 + B * ‖u‖ ^ 5 := by gcongr
      _ ≤ (max c 0 + 2 * B) * ‖u‖ ^ 4 := by nlinarith
  subst hP₂ hP₃ hP₄ hP₅
  obtain ⟨-, -, hfc⟩ := flipCoeff_jet_eq (A := jacobianAlong G xs) hQ₂ hQ₃ 0 T vm wm k₂
  have hk : k₂ - monodromy (jacobianAlong G xs) T 0 *ᵥ k₂ =
      secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) • vm := by
    rw [← bilin_flowJet_two hQ₂]; exact hk₂
  refine ⟨fun hab => ?_, fun hab => ?_, fun hdeg k₃ k₄ hk₃ hwk₃ hk₄ => ⟨fun hκ => ?_, fun hκ => ?_⟩⟩
  · rw [hfc] at hab
    exact FlipOrbitUniform.orbit_uniformly_stable_of_flipCoeff_pos hGc hGd hD hK hT hGper hxs hfix
      hQ₂c hQ₃c (lt_min hρ one_pos) hTay3 hv hw hwv hS hk hab
  · rw [hfc] at hab
    exact FlipOrbitUniform.orbit_uniformly_unstable_of_flipCoeff_neg hGc hGd hD hK hT hGper hxs
      hfix hQ₂c hQ₃c (lt_min hρ one_pos) hTay3 hv hw hwv hS hk hab
  · exact orbit_stable_of_degenerateFlip hGc hGd hD hK hT hGper hxs hfix hQ hρ hTay hv hw hwv hS
      rfl rfl rfl rfl hk₂ hk₃ hwk₃ hk₄ hdeg hκ
  · exact orbit_unstable_of_degenerateFlip hGc hGd hD hK hT hGper hxs hfix hQ hρ hTay hv hw hwv hS
      rfl rfl rfl rfl hk₂ hk₃ hwk₃ hk₄ hdeg hκ

end Orbit

end powerlib.Periodic.JetVariation
