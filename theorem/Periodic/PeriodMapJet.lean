import theorem.Periodic.PeriodMapTaylor
import Mathlib.Analysis.Analytic.Composition

/-! # The Taylor expansion of the flow and of the period map to any order

`theorem/Periodic/PeriodMapTaylor.lean` expands the flow of `ẋ = G(t, x)` about a solution `x_*`
to third order. This module does it to every order `N`. Along `x_*` let the field have the
expansion `G(r, x_* + u) = G(r, x_*) + A(r) u + ∑_{2 ≤ k ≤ N} Q_k(r)(u, …, u) + O(‖u‖^{N+1})`
with `k`-linear coefficients `Q_k(r)` (a `FormalMultilinearSeries`). The solution from
`x_*(s) + e` is `x(r) = x_*(r) + ∑_{1 ≤ j ≤ N} P_j(r)(e, …, e) + O(‖e‖^{N+1})`, where the
`j`-linear maps `P_j(r)` solve the variational hierarchy
`Ṗ_1 = A P_1`, `P_1(s) = I`, and for `j ≥ 2`
`Ṗ_j(m) = A P_j(m) + ∑_c Q_{|c|}(P_{c_1}(m_{(1)}), …, P_{c_{|c|}}(m_{(|c|)}))`, `P_j(s) = 0`,
the sum over the compositions `c` of `j` into at least two blocks (Mathlib
`FormalMultilinearSeries.compAlongComposition`; the blocks `m_{(i)}` of the argument follow the
composition). For `j = 2, 3` these are the second and third variational equations of
`PeriodMapTaylor` (`(1,1)`; `(1,2)`, `(2,1)`, `(1,1,1)`). The coefficients are defined by
recursion on the order (`jetUpTo`, `flowJet`): the source of order `j` only reads the
coefficients of orders `< j` (`blocksFun_lt`), and each `P_j(r)` is the multilinear map with the
responses `∫ₛʳ Φ(r, σ) (source)(σ) dσ` (`PeriodMapTaylor.resp`) as values on tuples of basis
vectors, multilinear in its argument by the linearity of the response (`multilinOfBasis_resp`).

The remainder is proved by induction on the order with one Grönwall step each
(`FlowDerivative.norm_le_of_hasDerivWithinAt`): the remainder `z = u − ∑_{j ≤ n+1} y_j`,
`u = x − x_*`, `y_j = P_j(e, …, e)`, solves `ż = A z + (source)`, and the source is of order
`n + 2`: the field terms `Q_k(u^k) − Q_k(w^k)` (`w = ∑_{j ≤ n} y_j`, `u − w = O(‖e‖^{n+1})` by the
previous step, `k ≥ 2`), the remainder of the field, and the identity `comp_identity`: by Mathlib's
`FormalMultilinearSeries.comp_partialSum`, `∑_k Q_k(w^k)` is the sum over compositions with
blocks of order `≤ n`, whose part of total order `≤ n + 1` is exactly the sum of the sources of
orders `≤ n + 1`. At `s = 0`, `r = T` and a `T`-periodic `x_*` this is the expansion of the period
map, `P(p + e) = p + M e + ∑_{2 ≤ j ≤ N} P_j(T)(e, …, e) + O(‖e‖^{N+1})`, `M = Φ(T, 0)`; for
`N = 5` it is the fifth-order expansion used by the degenerate flip of a periodic solution
(`theorem/Periodic/DegenerateFlipOrbit.lean`, through `Map/DegenerateFlipCoefficients`).

Scope.
* `ℝ^X` (`X → ℝ`, finite `X`, sup norm), continuous time, solutions on segments `[s, t]`, as in
  `theorem/Periodic/FlowDerivative.lean` and `theorem/Periodic/PeriodMapTaylor.lean`; `G(r, ·)` is
  `K`-Lipschitz (for the flow and the a priori bound `‖x(r) − x_*(r)‖ ≤ e^{K(r − s)} ‖e‖`).
* The regularity enters as the expansion along `x_*` on `[s, t]` with continuous coefficients
  `A` (matrices, `‖A(r) v‖ ≤ K ‖v‖`) and `Q_k` (`2 ≤ k ≤ N`, `ContinuousMultilinearMap` on
  `Fin k`), remainder `c ‖u‖^{N+1}` for `‖u‖ ≤ ρ`; the `Q_k` need not be symmetric. For a field of
  class `C^{N+1}` in `x` it holds with `Q_k = D_x^kG/k!` and `c = B/(N + 1)!`, `B` a bound of
  `‖D_x^{N+1}G‖` on the tube (`taylor_along_of_contDiff_order`, Taylor's theorem with integral
  remainder).
* The remainder constant is explicit, `flowConst K L B c N`, defined by the recursion of the
  proof (`remConst`, with the bound `jetBound` of the coefficients `P_j`) from `K`, the length
  `L = t − s`, the bound `B ≥ ‖Q_k‖` and the field remainder `c`; the expansion holds for
  `‖e‖ ≤ 1` with `e^{K(t − s)} ‖e‖ ≤ ρ`. For a field of class `C^{N+1}`
  (`periodMap_jet_of_contDiff`) the bound `B` comes from the continuity of `D_x^kG` along `x_*`
  and the constant is stated to exist.
* The coefficients `P_j` are those of the hierarchy written with the multilinear coefficients
  `Q_k`; their identification with `secondVariation`, `thirdVariation` of `PeriodMapTaylor`
  (where `Q₂` is a bilinear map) is not stated here; it is `theorem/Periodic/JetVariation.lean`
  (`bilin_flowJet_two`, `flowJet_three`, `flipCoeff_jet_eq`); at orders four and five, with the
  closed forms `fourthVariation`, `fifthVariation`, it is
  `theorem/Periodic/JetVariationHigher.lean` (`flowJet_four`, `flowJet_five`).
* Generic mathematics; no model family.

Source: Hartman, *Ordinary Differential Equations*, Ch. V (higher differentiability with respect
to initial conditions; the higher variational equations); Kuznetsov, *Elements of Applied
Bifurcation Theory* (3rd ed.), §5.4 (the Taylor coefficients of a Poincaré map) and §9.5 (the
degenerate flip needs the fifth-order coefficients); the open item of
`theorem/Periodic/DegenerateFlipReduction.lean` (Scope: the expansion of the period map beyond
third order).

Results.
* `varSource`, `jetUpTo`, `flowJet` — the source of the `j`-th variational equation and the jet
  of the flow; `jetUpTo_succ_of_ne`, `jetUpTo_eq`, `flowJet_eq_jetUpTo`, `flowJet_zero`,
  `flowJet_one`, `flowJet_succ_succ` — its recursion.
* `blocksFun_lt`, `varSource_congr`, `varSource_jetUpTo`, `varSource_one`, `varSource_diag` —
  the source reads the lower coefficients only; on the diagonal it is
  `∑_c Q_{|c|}(y_{c_1}, …, y_{c_{|c|}})`.
* `multilinOfBasis_resp`, `continuous_varSource_apply`, `flowJet_spec`, `hasDerivAt_flowJet`,
  `flowJet_start` — the coefficients are continuous and solve the variational hierarchy.
* `exists_bound_coeff`, `norm_transition_mulVec_le`, `jetBound`, `jetBound_nonneg`,
  `norm_flowJet_le` — bounds on `[s, t]`.
* `remConst`, `remConst_nonneg`, `flowConst`, `flowConst_nonneg` — the remainder constants;
  `norm_sub_flowJet_le` — the expansion of the flow to order `N`,
  `‖x(r) − x_*(r) − ∑_{1 ≤ j ≤ N} P_j(r)(e, …, e)‖ ≤ flowConst K (t − s) B c N ‖e‖^{N+1}` on
  `[s, t]`.
* `sum_flowJet_eq`, `periodMap_jet` — the expansion of the period map,
  `‖P(p + e) − p − M e − ∑_{2 ≤ j ≤ N} P_j(T)(e, …, e)‖ ≤ flowConst K T B c N ‖e‖^{N+1}`.
* `norm_taylor_le`, `taylorSeries`, `taylor_along_of_contDiff_order`,
  `periodMap_jet_of_contDiff` — Taylor's theorem to order `N` and the expansion of the period
  map of a field of class `C^{N+1}`.

Corrections.
None: an extension (the expansion of the period map to every order; `PeriodMapTaylor` stops at
the third).

Family and connection conclusions.
None: static evidence on nonautonomous ODEs (the Taylor expansion of the flow).
-/

noncomputable section
namespace powerlib.Periodic.PeriodMapJet

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator Nat
open PeriodMapTaylor

variable {X : Type*} [Fintype X] [DecidableEq X]

local notation "𝓢" => FormalMultilinearSeries ℝ (X → ℝ) (X → ℝ)

/-! ## The variational hierarchy -/

/-- The source of the `j`-th variational equation at time `r` for a jet `p` of the flow: the sum
over the compositions `c` of `j` into at least two blocks of `Q_{|c|}(r)` applied, block by block,
to the coefficients `p(r)_{c_i}`. On the diagonal it is
`∑_c Q_{|c|}(r)(y_{c_1}, …, y_{c_{|c|}})` with `y_i = p(r)_i(e, …, e)`. -/
def varSource (Q : ℝ → 𝓢) (p : ℝ → 𝓢) (j : ℕ) (r : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => X → ℝ) (X → ℝ) :=
  ∑ c ∈ Finset.univ.filter (fun c : Composition j => 2 ≤ c.length),
    (Q r).compAlongComposition (p r) c

/-- The coefficients of the flow up to order `N + 1`: the index `1` is the transition matrix
`Φ(r, s)`, the index `N + 2` the response of the `(N + 2)`-th variational equation, whose source
only reads the indices up to `N + 1` (defined by its values on tuples of basis vectors). -/
def jetUpTo (A : ℝ → Matrix X X ℝ) (Q : ℝ → 𝓢) (s : ℝ) : ℕ → ℝ → 𝓢
  | 0 => fun r => Function.update 0 1
      ((continuousMultilinearCurryFin1 ℝ (X → ℝ) (X → ℝ)).symm
        (Matrix.toLin' (transition A r s)).toContinuousLinearMap)
  | N + 1 => fun r => Function.update (jetUpTo A Q s N r) (N + 2)
      (multilinOfBasis fun f => resp A (fun σ => varSource Q (jetUpTo A Q s N) (N + 2) σ
        (fun l => Pi.single (f l) 1)) s r)

/-- **The jet of the flow.** `flowJet A Q s r j` is the `j`-linear map `P_j(r)` with
`x(r) = x_*(r) + ∑_j P_j(r)(e, …, e) + …` for `x(s) = x_*(s) + e`: `P_1(r) = Φ(r, s)` and
`P_j(r)(m) = ∫ₛʳ Φ(r, σ) varSource(m)(σ) dσ` for `j ≥ 2` (`flowJet_apply`). -/
def flowJet (A : ℝ → Matrix X X ℝ) (Q : ℝ → 𝓢) (s r : ℝ) : 𝓢 :=
  fun j => jetUpTo A Q s j r j

variable {A : ℝ → Matrix X X ℝ} {Q : ℝ → FormalMultilinearSeries ℝ (X → ℝ) (X → ℝ)} {s : ℝ}

@[tmio T, powerlib_foundation] theorem jetUpTo_succ_of_ne {N j : ℕ} (h : j ≠ N + 2) (r : ℝ) :
    jetUpTo A Q s (N + 1) r j = jetUpTo A Q s N r j := by
  simp only [jetUpTo]
  exact Function.update_of_ne h _ _

@[tmio T, powerlib_foundation] theorem jetUpTo_eq {N j : ℕ} (hj : j ≤ N + 1) :
    ∀ M, N ≤ M → ∀ r, jetUpTo A Q s M r j = jetUpTo A Q s N r j := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => exact fun _ => rfl
  | succ M hNM ih =>
    intro r
    rw [jetUpTo_succ_of_ne (by omega), ih]

@[tmio T, powerlib_foundation] theorem flowJet_eq_jetUpTo {N j : ℕ} (hj : j ≤ N + 1) (r : ℝ) :
    flowJet A Q s r j = jetUpTo A Q s N r j := by
  rcases Nat.lt_or_ge j (N + 1) with h | h
  · exact (jetUpTo_eq (Nat.le_succ j) N (by omega) r).symm
  · obtain rfl : j = N + 1 := le_antisymm hj h
    exact jetUpTo_succ_of_ne (by omega) r

@[tmio T, powerlib_foundation] theorem flowJet_zero (r : ℝ) : flowJet A Q s r 0 = 0 := by
  rw [flowJet_eq_jetUpTo (N := 0) (by omega)]
  simp only [jetUpTo]
  exact Function.update_of_ne (by omega) _ _

@[tmio T, powerlib_foundation] theorem flowJet_one (r : ℝ) (m : Fin 1 → X → ℝ) :
    flowJet A Q s r 1 m = transition A r s *ᵥ m 0 := by
  rw [flowJet_eq_jetUpTo (N := 0) le_rfl]
  simp only [jetUpTo, Function.update_self, continuousMultilinearCurryFin1_symm_apply]
  rfl

@[tmio T, powerlib_foundation] theorem flowJet_succ_succ (N : ℕ) (r : ℝ) :
    flowJet A Q s r (N + 2) = multilinOfBasis fun f => resp A (fun σ =>
      varSource Q (jetUpTo A Q s N) (N + 2) σ (fun l => Pi.single (f l) 1)) s r := by
  rw [flowJet_eq_jetUpTo (N := N + 1) le_rfl]
  simp only [jetUpTo]
  exact Function.update_self _ _ _


/-! ## Compositions with at least two blocks -/

/-- A composition of `j` into at least two blocks has every block smaller than `j` (Mathlib
`Composition.ne_single_iff`: it is not the single block). -/
@[tmio T, powerlib_foundation] theorem blocksFun_lt {j : ℕ} {c : Composition j}
    (hc : 2 ≤ c.length) (i : Fin c.length) : c.blocksFun i < j := by
  have hj : 0 < j := lt_of_lt_of_le (by omega) (hc.trans c.length_le)
  refine (Composition.ne_single_iff hj).1 (fun h => ?_) i
  have := (Composition.eq_single_iff_length hj).1 h
  omega

omit [Fintype X] [DecidableEq X] in
/-- The source only reads the coefficients of orders `1, …, j − 1` of the jet. -/
@[tmio T, powerlib_foundation] theorem varSource_congr {p p' : ℝ → 𝓢} {j : ℕ} {r : ℝ}
    (h : ∀ i, 1 ≤ i → i < j → p r i = p' r i) : varSource Q p j r = varSource Q p' j r := by
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc2 := (Finset.mem_filter.1 hc).2
  refine ContinuousMultilinearMap.ext fun v => ?_
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  congr 1
  funext i
  simp only [FormalMultilinearSeries.applyComposition]
  rw [h _ (c.one_le_blocksFun i) (blocksFun_lt hc2 i)]

@[tmio T, powerlib_foundation] theorem varSource_jetUpTo (N : ℕ) (r : ℝ) :
    varSource Q (jetUpTo A Q s N) (N + 2) r = varSource Q (flowJet A Q s) (N + 2) r :=
  varSource_congr fun i _ hi => (flowJet_eq_jetUpTo (by omega) r).symm

omit [Fintype X] [DecidableEq X] in
/-- A composition of `1` has a single block: the first variational equation has no source. -/
@[tmio T, powerlib_foundation] theorem varSource_one (p : ℝ → 𝓢) (r : ℝ) :
    varSource Q p 1 r = 0 := by
  refine Finset.sum_eq_zero fun c hc => ?_
  have := (Finset.mem_filter.1 hc).2
  have := c.length_le
  omega

omit [Fintype X] [DecidableEq X] in
/-- The source on the diagonal: `∑_c Q_{|c|}(r)(y_{c_1}, …)` with `y_i = p(r)_i(e, …, e)`. -/
@[tmio T, powerlib_foundation] theorem varSource_diag (p : ℝ → 𝓢) (j : ℕ) (r : ℝ)
    (e : X → ℝ) : varSource Q p j r (fun _ => e) =
      ∑ c ∈ Finset.univ.filter (fun c : Composition j => 2 ≤ c.length),
        Q r c.length (fun i => p r (c.blocksFun i) (fun _ => e)) := by
  simp only [varSource, _root_.sum_apply, FormalMultilinearSeries.compAlongComposition_apply]
  rfl

/-! ## The coefficients solve the variational equations -/

/-- A multilinear map defined by its values on tuples of basis vectors as responses of
`ẏ = A y + S(σ)(m)`, with `S` multilinear and continuous in time, is the response at every
tuple. -/
@[tmio T, powerlib_foundation] theorem multilinOfBasis_resp (hA : Continuous A) {j : ℕ}
    {S : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin j => X → ℝ) (X → ℝ)}
    (hS : ∀ m, Continuous fun σ => S σ m) (r : ℝ) (m : Fin j → X → ℝ) :
    multilinOfBasis (fun f => resp A (fun σ => S σ (fun l => Pi.single (f l) 1)) s r) m =
      resp A (fun σ => S σ m) s r := by
  let M : MultilinearMap ℝ (fun _ : Fin j => X → ℝ) (X → ℝ) :=
    { toFun := fun m => resp A (fun σ => S σ m) s r
      map_update_add' := fun {inst} m i x y => by
        obtain rfl : inst = instDecidableEqFin j := Subsingleton.elim _ _
        have h : (fun σ => S σ (update m i (x + y))) =
            fun σ => S σ (update m i x) + S σ (update m i y) :=
          funext fun σ => (S σ).map_update_add m i x y
        simp only [h, resp_add hA (hS _) (hS _)]
      map_update_smul' := fun {inst} m i c x => by
        obtain rfl : inst = instDecidableEqFin j := Subsingleton.elim _ _
        have h : (fun σ => S σ (update m i (c • x))) = fun σ => c • S σ (update m i x) :=
          funext fun σ => (S σ).map_update_smul m i c x
        simp only [h, resp_smul hA (hS _)] }
  exact multilinOfBasis_eq M m

omit [DecidableEq X] in
/-- The source is continuous in time when the field coefficients and the lower coefficients of
the jet are. -/
@[tmio T, powerlib_foundation] theorem continuous_varSource_apply {p : ℝ → 𝓢} {j : ℕ}
    (hQ : ∀ k, 2 ≤ k → k ≤ j → Continuous fun r => Q r k)
    (hp : ∀ i, 1 ≤ i → i < j → ∀ m, Continuous fun r => p r i m) (m : Fin j → X → ℝ) :
    Continuous fun r => varSource Q p j r m := by
  simp only [varSource, _root_.sum_apply, FormalMultilinearSeries.compAlongComposition_apply]
  refine continuous_finsetSum _ fun c hc => ?_
  have hc2 := (Finset.mem_filter.1 hc).2
  exact continuous_eval.comp ((hQ c.length hc2 c.length_le).prodMk
    (continuous_pi fun i => hp _ (c.one_le_blocksFun i) (blocksFun_lt hc2 i) _))

/-- **The coefficients of the jet.** For `1 ≤ j ≤ N` (`N` the order of the continuous field
coefficients) `r ↦ P_j(r)(m)` is continuous, and for `j ≥ 2` it is the response of the `j`-th
variational equation `ẏ = A y + varSource(m)`, `y(s) = 0`. -/
@[tmio T, powerlib_foundation] theorem flowJet_spec (hA : Continuous A) {N : ℕ}
    (hQ : ∀ k, 2 ≤ k → k ≤ N → Continuous fun r => Q r k) :
    ∀ j, 1 ≤ j → j ≤ N → (∀ m, Continuous fun r => flowJet A Q s r j m) ∧
      (2 ≤ j → ∀ r m, flowJet A Q s r j m =
        resp A (fun σ => varSource Q (flowJet A Q s) j σ m) s r) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hjN
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 1 := by omega
      refine ⟨fun m => ?_, fun h => absurd h (by omega)⟩
      simp only [flowJet_one]
      exact continuous_transition_mulVec hA s (m 0)
    · obtain ⟨N', rfl⟩ : ∃ N', j = N' + 2 := ⟨j - 2, by omega⟩
      have hS : ∀ m, Continuous fun σ => varSource Q (flowJet A Q s) (N' + 2) σ m :=
        continuous_varSource_apply (fun k hk1 hk2 => hQ k hk1 (by omega))
          (fun i hi1 hi2 => (ih i hi2 hi1 (by omega)).1)
      have hval : ∀ r m, flowJet A Q s r (N' + 2) m =
          resp A (fun σ => varSource Q (flowJet A Q s) (N' + 2) σ m) s r := by
        intro r m
        rw [flowJet_succ_succ]
        simp only [varSource_jetUpTo]
        exact multilinOfBasis_resp hA hS r m
      refine ⟨fun m => ?_, fun _ => hval⟩
      have : (fun r => flowJet A Q s r (N' + 2) m) =
          resp A (fun σ => varSource Q (flowJet A Q s) (N' + 2) σ m) s :=
        funext fun r => hval r m
      rw [this]
      exact continuous_iff_continuousAt.2 fun r =>
        (hasDerivAt_resp hA (hS m) s r).continuousAt

/-- **The variational equations.** For `1 ≤ j ≤ N`,
`d/dr P_j(r)(m) = A(r) P_j(r)(m) + varSource(m)(r)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_flowJet (hA : Continuous A) {N : ℕ}
    (hQ : ∀ k, 2 ≤ k → k ≤ N → Continuous fun r => Q r k) {j : ℕ} (hj1 : 1 ≤ j)
    (hjN : j ≤ N) (m : Fin j → X → ℝ) (r : ℝ) :
    HasDerivAt (fun r => flowJet A Q s r j m)
      (A r *ᵥ flowJet A Q s r j m + varSource Q (flowJet A Q s) j r m) r := by
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · obtain rfl : j = 1 := by omega
    rw [varSource_one, _root_.zero_apply, add_zero]
    simp only [flowJet_one]
    exact FlowDerivative.hasDerivAt_transition_mulVec hA s (m 0) r
  · have hspec := flowJet_spec (s := s) hA hQ j hj1 hjN
    have hS : Continuous fun σ => varSource Q (flowJet A Q s) j σ m :=
      continuous_varSource_apply (fun k hk1 hk2 => hQ k hk1 (by omega))
        (fun i hi1 hi2 => (flowJet_spec (s := s) hA hQ i hi1 (by omega)).1) m
    have : (fun r => flowJet A Q s r j m) =
        resp A (fun σ => varSource Q (flowJet A Q s) j σ m) s :=
      funext fun r => hspec.2 hj2 r m
    rw [this, hspec.2 hj2 r m]
    exact hasDerivAt_resp hA hS s r

/-- The coefficients of order `j ≥ 2` vanish at the initial time. -/
@[tmio T, powerlib_foundation] theorem flowJet_start (hA : Continuous A) {N : ℕ}
    (hQ : ∀ k, 2 ≤ k → k ≤ N → Continuous fun r => Q r k) {j : ℕ} (hj2 : 2 ≤ j)
    (hjN : j ≤ N) (m : Fin j → X → ℝ) : flowJet A Q s s j m = 0 := by
  rw [(flowJet_spec (s := s) hA hQ j (by omega) hjN).2 hj2 s m, resp_start]


/-! ## Bounds of the coefficients -/

omit [DecidableEq X] in
/-- Finitely many continuous coefficients are bounded on a compact interval. -/
@[tmio T, powerlib_foundation] theorem exists_bound_coeff {s t : ℝ} :
    ∀ N : ℕ, (∀ k, 2 ≤ k → k ≤ N → Continuous fun r => Q r k) →
      ∃ B, 0 ≤ B ∧ ∀ k, 2 ≤ k → k ≤ N → ∀ r ∈ Icc s t, ‖Q r k‖ ≤ B := by
  intro N
  induction N with
  | zero => exact fun _ => ⟨0, le_rfl, fun k hk1 hk2 => absurd hk2 (by omega)⟩
  | succ N ih =>
    intro hQ
    obtain ⟨B, hB0, hB⟩ := ih fun k hk1 hk2 => hQ k hk1 (by omega)
    by_cases hN : 2 ≤ N + 1
    · obtain ⟨B', hB'⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (hQ (N + 1) hN le_rfl).continuousOn (s := Icc s t)
      refine ⟨max B B', le_max_of_le_left hB0, fun k hk1 hk2 r hr => ?_⟩
      rcases Nat.lt_or_ge k (N + 1) with hk | hk
      · exact (hB k hk1 (by omega) r hr).trans (le_max_left _ _)
      · obtain rfl : k = N + 1 := by omega
        exact (hB' r hr).trans (le_max_right _ _)
    · exact ⟨B, hB0, fun k hk1 hk2 => hB k hk1 (by omega)⟩

/-- `‖Φ(r, s) v‖ ≤ e^{K(t − s)} ‖v‖` on `[s, t]` when `‖A(r) v‖ ≤ K ‖v‖` there (Grönwall). -/
@[tmio T, powerlib_foundation] theorem norm_transition_mulVec_le (hA : Continuous A)
    {K : NNReal} {t : ℝ} (hAK : ∀ r ∈ Icc s t, ∀ v, ‖A r *ᵥ v‖ ≤ K * ‖v‖) (v : X → ℝ) :
    ∀ r ∈ Icc s t, ‖transition A r s *ᵥ v‖ ≤ Real.exp (K * (t - s)) * ‖v‖ := by
  intro r hr
  have h := FlowDerivative.norm_le_of_hasDerivWithinAt (w := fun r => transition A r s *ᵥ v)
    (δ := ‖v‖) K.2 le_rfl
    (fun q _ => (FlowDerivative.hasDerivAt_transition_mulVec hA s v q).hasDerivWithinAt)
    (fun q hq => by simpa using hAK q (Ico_subset_Icc_self hq) (transition A q s *ᵥ v))
    (by simp [LinearSystems.stateTransitionMatrix_self]) r hr
  rw [zero_mul, add_zero] at h
  exact h.trans_eq (mul_comm _ _)

/-- The bound of the coefficients of orders `0, …, M` of the jet on a segment of length `L`, for
`E = e^{KL}` and the bound `B ≥ ‖Q_k‖` of the field coefficients: `jetBound 0 = 0`,
`jetBound 1 = E` (the transition matrix) and
`jetBound (M + 1) = max (jetBound M) (#Comp(M + 1) · B · D₁^{M+1} · L · E)`,
`D₁ = max (jetBound M) 1`, for `M ≥ 1` (the variation of constants over the compositions of
`M + 1`). -/
def jetBound (E L B : ℝ) : ℕ → ℝ
  | 0 => 0
  | M + 1 => max (jetBound E L B M) (if M = 0 then E else
      (Fintype.card (Composition (M + 1)) : ℝ) * (B * max (jetBound E L B M) 1 ^ (M + 1)) * L * E)

@[tmio T, powerlib_foundation] theorem jetBound_nonneg (E L B : ℝ) :
    ∀ M, 0 ≤ jetBound E L B M
  | 0 => le_rfl
  | M + 1 => (jetBound_nonneg E L B M).trans (le_max_left _ _)

/-- **The coefficients of the jet are bounded on `[s, t]`**: `‖P_j(r)‖ ≤ jetBound E (t − s) B N`
for `j ≤ N`, `E = e^{K(t − s)}`, when `‖A(r) v‖ ≤ K ‖v‖` and `‖Q_k(r)‖ ≤ B` (`2 ≤ k ≤ N`). -/
@[tmio T, powerlib_foundation] theorem norm_flowJet_le (hA : Continuous A) {N : ℕ}
    (hQ : ∀ k, 2 ≤ k → k ≤ N → Continuous fun r => Q r k) {K : NNReal} {t B : ℝ} (hst : s ≤ t)
    (hAK : ∀ r ∈ Icc s t, ∀ v, ‖A r *ᵥ v‖ ≤ K * ‖v‖) (hB0 : 0 ≤ B)
    (hB : ∀ k, 2 ≤ k → k ≤ N → ∀ r ∈ Icc s t, ‖Q r k‖ ≤ B) :
    ∀ j ≤ N, ∀ r ∈ Icc s t,
      ‖flowJet A Q s r j‖ ≤ jetBound (Real.exp (K * (t - s))) (t - s) B N := by
  set E := Real.exp (K * (t - s)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  suffices h : ∀ M, M ≤ N → ∀ j ≤ M, ∀ r ∈ Icc s t,
      ‖flowJet A Q s r j‖ ≤ jetBound E (t - s) B M from h N le_rfl
  intro M
  induction M with
  | zero =>
    intro _ j hj r _
    obtain rfl : j = 0 := by omega
    rw [flowJet_zero, norm_zero]
    exact le_rfl
  | succ M ih =>
    intro hMN
    have hD := ih (by omega)
    set D := jetBound E (t - s) B M with hDdef
    have hD0 : 0 ≤ D := jetBound_nonneg _ _ _ M
    -- the new coefficient `j = M + 1`
    have hnew : ∀ r ∈ Icc s t, ‖flowJet A Q s r (M + 1)‖ ≤ (if M = 0 then E else
        (Fintype.card (Composition (M + 1)) : ℝ) * (B * max D 1 ^ (M + 1)) * (t - s) * E) := by
      rcases Nat.eq_zero_or_pos M with h0 | h0
      · subst h0
        intro r hr
        rw [ite_eq_left rfl]
        refine ContinuousMultilinearMap.opNorm_le_bound hE0 fun m => ?_
        rw [flowJet_one, Fin.prod_univ_one]
        exact norm_transition_mulVec_le hA hAK (m 0) r hr
      · intro r hr
        rw [ite_eq_right (by omega)]
        have h2 : 2 ≤ M + 1 := by omega
        set D₁ := max D 1 with hD₁
        set εS := (Fintype.card (Composition (M + 1)) : ℝ) * (B * D₁ ^ (M + 1)) with hεS
        have hεS0 : 0 ≤ εS := by positivity
        have hSb : ∀ σ ∈ Icc s t, ‖varSource Q (flowJet A Q s) (M + 1) σ‖ ≤ εS := by
          intro σ hσ
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_card_nsmul _ _ (B * D₁ ^ (M + 1)) fun c hc => ?_).trans ?_
          · have hc2 := (Finset.mem_filter.1 hc).2
            refine ((Q σ).compAlongComposition_norm (flowJet A Q s σ) c).trans ?_
            have hprod : ∏ i, ‖flowJet A Q s σ (c.blocksFun i)‖ ≤ D₁ ^ (M + 1) := by
              calc ∏ i, ‖flowJet A Q s σ (c.blocksFun i)‖ ≤ ∏ _i : Fin c.length, D₁ :=
                    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
                      (hD _ (by have := blocksFun_lt hc2 i; omega) σ hσ).trans
                        (le_max_left _ _)
                _ = D₁ ^ c.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                _ ≤ D₁ ^ (M + 1) := pow_le_pow_right₀ (le_max_right _ _) c.length_le
            exact mul_le_mul (hB _ hc2 (c.length_le.trans hMN) σ hσ) hprod (by positivity) hB0
          · rw [nsmul_eq_mul, hεS]
            gcongr
            exact_mod_cast (Finset.card_filter_le _ _).trans_eq Finset.card_univ
        refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
        have hspec := flowJet_spec (s := s) hA hQ (M + 1) (by omega) hMN
        have hS : Continuous fun σ => varSource Q (flowJet A Q s) (M + 1) σ m :=
          continuous_varSource_apply (fun k hk1 hk2 => hQ k hk1 (by omega))
            (fun i hi1 hi2 => (flowJet_spec (s := s) hA hQ i hi1 (by omega)).1) m
        rw [hspec.2 h2 r m]
        have h := norm_resp_le hA hS K.2 (by positivity : 0 ≤ εS * ∏ i, ‖m i‖) hAK
          (fun σ hσ => ((varSource Q (flowJet A Q s) (M + 1) σ).le_opNorm m).trans
            (mul_le_mul_of_nonneg_right (hSb σ hσ) (by positivity))) r hr
        calc ‖resp A (fun σ => varSource Q (flowJet A Q s) (M + 1) σ m) s r‖
            ≤ (εS * ∏ i, ‖m i‖) * (t - s) * E := h
          _ = εS * (t - s) * E * ∏ i, ‖m i‖ := by ring
    intro j hj r hr
    show _ ≤ max D _
    rcases Nat.lt_or_ge j (M + 1) with hj' | hj'
    · exact (hD j (by omega) r hr).trans (le_max_left _ _)
    · obtain rfl : j = M + 1 := by omega
      exact (hnew r hr).trans (le_max_right _ _)

/-! ## The Taylor expansion of the flow to order `N` -/

/-- **The composition identity of the expansion.** With the truncation `q` of the field
coefficients to the orders `2, …, N` and `w = ∑_{1 ≤ j ≤ n} P_j(r)(e, …, e)`, `n < N`, the
part of `∑_{2 ≤ k ≤ N} Q_k(w, …, w)` of total order at most `n + 1` is the sum of the sources of
orders `1, …, n + 1`; the rest is the sum over the compositions of total order above `n + 1`
(Mathlib `FormalMultilinearSeries.comp_partialSum`). -/
@[tmio T, powerlib_foundation] private theorem comp_identity {N n : ℕ} (hnN : n + 1 ≤ N)
    (r : ℝ) (e : X → ℝ) :
    ∑ k ∈ Finset.Icc 2 N, Q r k (fun _ => ∑ j ∈ Finset.Icc 1 n, flowJet A Q s r j (fun _ => e)) -
      ∑ j ∈ Finset.Icc 1 (n + 1), varSource Q (flowJet A Q s) j r (fun _ => e) =
    ∑ a ∈ (FormalMultilinearSeries.compPartialSumTarget 0 (N + 1) (n + 1)).filter
        (fun a => ¬ a.1 ≤ n + 1),
      (FormalMultilinearSeries.compAlongComposition
        (fun k => if 2 ≤ k ∧ k ≤ N then Q r k else 0) (flowJet A Q s r) a.2) (fun _ => e) := by
  set q : 𝓢 := fun k => if 2 ≤ k ∧ k ≤ N then Q r k else 0 with hq
  set p : 𝓢 := flowJet A Q s r with hp
  set T := FormalMultilinearSeries.compPartialSumTarget 0 (N + 1) (n + 1) with hT
  set f : (Σ k, Composition k) → X → ℝ := fun a => (q.compAlongComposition p a.2) (fun _ => e)
    with hf
  have hqin : ∀ k, 2 ≤ k → k ≤ N → q k = Q r k := fun k h1 h2 => by
    rw [hq]; exact ite_eq_left ⟨h1, h2⟩
  have hqout : ∀ k, ¬ (2 ≤ k ∧ k ≤ N) → q k = 0 := fun k h => by rw [hq]; exact ite_eq_right h
  -- the field part as a partial sum
  have h1 : ∑ k ∈ Finset.Icc 2 N, Q r k (fun _ => ∑ j ∈ Finset.Icc 1 n, p j (fun _ => e)) =
      q.partialSum (N + 1) (∑ j ∈ Finset.Ico 1 (n + 1), p j (fun _ => e)) := by
    rw [Finset.Ico_add_one_right_eq_Icc, FormalMultilinearSeries.partialSum]
    refine (Finset.sum_congr rfl fun k hk => ?_).trans (Finset.sum_subset
      (fun k hk => by simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega)
      fun k _ hk => ?_)
    · simp only [Finset.mem_Icc] at hk
      rw [hqin k hk.1 hk.2]
    · rw [hqout k (by simpa [Finset.mem_Icc] using hk), _root_.zero_apply]
  -- the sources as a sum over compositions
  have h2 : ∑ j ∈ Finset.Icc 1 (n + 1), varSource Q (flowJet A Q s) j r (fun _ => e) =
      ∑ a ∈ (Finset.Icc 1 (n + 1)).sigma
        (fun j => Finset.univ.filter (fun c : Composition j => 2 ≤ c.length)), f a := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [varSource, _root_.sum_apply]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc2 := (Finset.mem_filter.1 hc).2
    simp only [Finset.mem_Icc] at hj
    simp only [hf, FormalMultilinearSeries.compAlongComposition,
      hqin c.length hc2 (c.length_le.trans (by omega))]
    rfl
  -- the target splits by the total order
  have h3 : ∑ a ∈ T.filter (fun a => a.1 ≤ n + 1), f a =
      ∑ a ∈ (Finset.Icc 1 (n + 1)).sigma
        (fun j => Finset.univ.filter (fun c : Composition j => 2 ≤ c.length)), f a := by
    symm
    refine Finset.sum_subset (fun a ha => ?_) fun a ha hna => ?_
    · rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter] at ha
      rw [Finset.mem_filter, hT, FormalMultilinearSeries.mem_compPartialSumTarget_iff]
      refine ⟨⟨Nat.zero_le _, by have := a.2.length_le; omega, fun i => ?_⟩, ha.1.2⟩
      have := blocksFun_lt ha.2.2 i
      omega
    · rw [Finset.mem_filter] at ha
      have hlen : a.2.length < 2 := by
        by_contra hcon
        apply hna
        rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter]
        refine ⟨⟨?_, ha.2⟩, Finset.mem_univ _, by omega⟩
        have := a.2.length_le
        omega
      simp only [hf, FormalMultilinearSeries.compAlongComposition_apply,
        hqout a.2.length (by omega), _root_.zero_apply]
  rw [h1, FormalMultilinearSeries.comp_partialSum, h2, ← h3,
    ← Finset.sum_filter_add_sum_filter_not T (fun a => a.1 ≤ n + 1)]
  abel

/-- The constants of the remainders of the flow, for `E = e^{KL}`, the segment length `L`, the
bounds `B ≥ ‖Q_k‖`, `D ≥ ‖P_j‖` (`j ≤ N`) and the remainder constant `c` of the field:
`remConst … 0 = E` (the a priori bound) and
`remConst … (n + 1) = (c⁺ E^{N+1} + (N + 1) B N F^N C + #T B D₁^N) L E` with
`C = remConst … n`, `F = max (E + C) 1`, `D₁ = max D 1` and `T` the compositions of
`compPartialSumTarget 0 (N + 1) (n + 1)`. -/
def remConst (E L B c D : ℝ) (N : ℕ) : ℕ → ℝ
  | 0 => E
  | n + 1 => (max c 0 * E ^ (N + 1) +
      (N + 1 : ℝ) * (B * N * max (E + remConst E L B c D N n) 1 ^ N * remConst E L B c D N n) +
      ((FormalMultilinearSeries.compPartialSumTarget 0 (N + 1) (n + 1)).card : ℝ) *
        (B * max D 1 ^ N)) * L * E

@[tmio T, powerlib_foundation] theorem remConst_nonneg {E L B c D : ℝ} (N : ℕ) (hE : 0 ≤ E)
    (hL : 0 ≤ L) (hB : 0 ≤ B) : ∀ n, 0 ≤ remConst E L B c D N n
  | 0 => hE
  | n + 1 => by
    have := remConst_nonneg (c := c) (D := D) N hE hL hB n
    simp only [remConst]
    positivity

/-- The remainder constant of the expansion of order `N` of the flow over a segment of length
`L`: `remConst` at the order `N`, with `E = e^{KL}` and `D = jetBound E L B N`. -/
def flowConst (K L B c : ℝ) (N : ℕ) : ℝ :=
  remConst (Real.exp (K * L)) L B c (jetBound (Real.exp (K * L)) L B N) N N

@[tmio T, powerlib_foundation] theorem flowConst_nonneg {K L B c : ℝ} (N : ℕ) (hL : 0 ≤ L)
    (hB : 0 ≤ B) : 0 ≤ flowConst K L B c N :=
  remConst_nonneg N (Real.exp_pos _).le hL hB N

/-- **The Taylor expansion of the flow to order `N`.** Let `x_*` and `x` solve `ẋ = G(t, x)` on
`[s, t]`, `G(r, ·)` `K`-Lipschitz, and let `G` have along `x_*` the expansion of order `N`,
`G(r, x_* + u) = G(r, x_*) + A(r) u + ∑_{2 ≤ k ≤ N} Q_k(r)(u, …, u) + R`, `‖R‖ ≤ c ‖u‖^{N+1}`
for `‖u‖ ≤ ρ`, with continuous coefficients, `‖A(r) v‖ ≤ K ‖v‖` and `‖Q_k(r)‖ ≤ B` on `[s, t]`
(for a field of class `C^{N+1}`: `Q_k = D_x^kG/k!`, `taylor_along_of_contDiff_order`). Then
`‖x(r) − x_*(r) − ∑_{1 ≤ j ≤ N} P_j(r)(e, …, e)‖ ≤ C ‖e‖^{N+1}` on `[s, t]`, `e = x(s) − x_*(s)`,
for `‖e‖ ≤ 1` and `e^{K(t − s)} ‖e‖ ≤ ρ`, with the jet `P_j = flowJet A Q s` of the variational
hierarchy and `C = flowConst K (t − s) B c N`. The proof is an induction on the order: the
remainder of order `n + 1` solves `ż = A z + (source)` with the source of order `n + 2` by the
composition identity (`comp_identity`) and the remainder of order `n`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_flowJet_le {G : ℝ → (X → ℝ) → X → ℝ}
    {K : NNReal} (hK : ∀ t, LipschitzWith K (G t)) (hA : Continuous A) {N : ℕ}
    (hQ : ∀ k, 2 ≤ k → k ≤ N → Continuous fun r => Q r k) {t B c ρ : ℝ} (hst : s ≤ t)
    (hAK : ∀ r ∈ Icc s t, ∀ v, ‖A r *ᵥ v‖ ≤ K * ‖v‖) (hB0 : 0 ≤ B)
    (hB : ∀ k, 2 ≤ k → k ≤ N → ∀ r ∈ Icc s t, ‖Q r k‖ ≤ B) {xs : ℝ → X → ℝ}
    (hxs : IsIntegralCurveOn xs G (Icc s t))
    (hTay : ∀ r ∈ Icc s t, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) - A r *ᵥ u -
      ∑ k ∈ Finset.Icc 2 N, Q r k (fun _ => u)‖ ≤ c * ‖u‖ ^ (N + 1))
    {x : ℝ → X → ℝ} (hx : IsIntegralCurveOn x G (Icc s t)) (he1 : ‖x s - xs s‖ ≤ 1)
    (heρ : Real.exp (K * (t - s)) * ‖x s - xs s‖ ≤ ρ) :
    ∀ r ∈ Icc s t,
      ‖x r - xs r - ∑ j ∈ Finset.Icc 1 N, flowJet A Q s r j (fun _ => x s - xs s)‖ ≤
        flowConst K (t - s) B c N * ‖x s - xs s‖ ^ (N + 1) := by
  set E := Real.exp (K * (t - s)) with hE
  set D := jetBound E (t - s) B N with hDdef
  have hD := norm_flowJet_le hA hQ hst hAK hB0 hB
  have hD0 : 0 ≤ D := jetBound_nonneg _ _ _ N
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg K.2 hts)
  have hexp : ∀ r ∈ Icc s t, Real.exp (K * (r - s)) ≤ E := fun r hr =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hr.2]) K.2)
  suffices H : ∀ n, n ≤ N → ∀ r ∈ Icc s t,
      ‖x r - xs r - ∑ j ∈ Finset.Icc 1 n, flowJet A Q s r j (fun _ => x s - xs s)‖ ≤
        remConst E (t - s) B c D N n * ‖x s - xs s‖ ^ (n + 1) from H N le_rfl
  intro n
  induction n with
  | zero =>
    intro _ r hr
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, sub_zero, zero_add, pow_one]
    have h := dist_le_of_isIntegralCurveOn_Icc hK hx hxs r hr
    rw [dist_eq_norm, dist_eq_norm] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (hexp r hr) (norm_nonneg _)).trans_eq (mul_comm _ _))
  | succ n ih =>
    intro hnN r₀ hr₀
    have hC := ih (by omega)
    set C := remConst E (t - s) B c D N n with hCdef
    have hC0 : 0 ≤ C := remConst_nonneg N (by positivity) hts hB0 n
    set F := max (E + C) 1 with hF
    have hF1 : 1 ≤ F := le_max_right _ _
    set D₁ := max D 1 with hD₁
    set T := FormalMultilinearSeries.compPartialSumTarget 0 (N + 1) (n + 1) with hT
    set ε := max c 0 * E ^ (N + 1) + (N + 1 : ℝ) * (B * N * F ^ N * C) +
      (T.card : ℝ) * (B * D₁ ^ N) with hε
    have hε0 : 0 ≤ ε := by positivity
    set e := x s - xs s with he
    set η := ‖e‖ with hη
    have hη0 : 0 ≤ η := norm_nonneg _
    have hηpow : ∀ a b : ℕ, a ≤ b → η ^ b ≤ η ^ a := fun a b hab =>
      pow_le_pow_of_le_one hη0 he1 hab
    -- the curves of the expansion
    set u : ℝ → X → ℝ := fun r => x r - xs r with hu
    set y : ℕ → ℝ → X → ℝ := fun j r => flowJet A Q s r j (fun _ => e) with hy
    have hub : ∀ r ∈ Icc s t, ‖u r‖ ≤ E * η := by
      intro r hr
      have h := dist_le_of_isIntegralCurveOn_Icc hK hx hxs r hr
      rw [dist_eq_norm, dist_eq_norm] at h
      exact h.trans ((mul_le_mul_of_nonneg_left (hexp r hr) hη0).trans_eq (mul_comm _ _))
    have hzb : ∀ r ∈ Icc s t, ‖u r - ∑ j ∈ Finset.Icc 1 n, y j r‖ ≤ C * η ^ (n + 1) := hC
    have hwb : ∀ r ∈ Icc s t, ‖∑ j ∈ Finset.Icc 1 n, y j r‖ ≤ F * η := by
      intro r hr
      have h1 : ‖∑ j ∈ Finset.Icc 1 n, y j r‖ ≤ ‖u r‖ + ‖u r - ∑ j ∈ Finset.Icc 1 n, y j r‖ := by
        have := norm_sub_le (u r) (u r - ∑ j ∈ Finset.Icc 1 n, y j r)
        rwa [sub_sub_cancel] at this
      have h2 : C * η ^ (n + 1) ≤ C * η := mul_le_mul_of_nonneg_left
        (by simpa using hηpow 1 (n + 1) (by omega)) hC0
      have h3 : (E + C) * η ≤ F * η := mul_le_mul_of_nonneg_right (le_max_left _ _) hη0
      linarith [hub r hr, hzb r hr]
    -- the derivative of the remainder of order `n + 1`
    have hd : ∀ r ∈ Icc s t, HasDerivWithinAt (fun r => u r - ∑ j ∈ Finset.Icc 1 (n + 1), y j r)
        (A r *ᵥ (u r - ∑ j ∈ Finset.Icc 1 (n + 1), y j r) +
          ((G r (xs r + u r) - G r (xs r) - A r *ᵥ u r) -
            ∑ j ∈ Finset.Icc 1 (n + 1), varSource Q (flowJet A Q s) j r (fun _ => e)))
        (Icc s t) r := by
      intro r hr
      have hsum : HasDerivAt (fun r => ∑ j ∈ Finset.Icc 1 (n + 1), y j r)
          (∑ j ∈ Finset.Icc 1 (n + 1), (A r *ᵥ y j r +
            varSource Q (flowJet A Q s) j r (fun _ => e))) r :=
        HasDerivAt.fun_sum fun j hj => by
          simp only [Finset.mem_Icc] at hj
          exact hasDerivAt_flowJet hA hQ hj.1 (by omega) _ r
      convert ((hx r hr).sub (hxs r hr)).sub hsum.hasDerivWithinAt using 1
      have hxu : x r = xs r + u r := by simp [hu]
      rw [hxu, Matrix.mulVec_sub, Matrix.mulVec_sum, Finset.sum_add_distrib]
      abel
    -- the source of order `n + 2`
    have hbd : ∀ r ∈ Ico s t, ‖A r *ᵥ (u r - ∑ j ∈ Finset.Icc 1 (n + 1), y j r) +
        ((G r (xs r + u r) - G r (xs r) - A r *ᵥ u r) -
          ∑ j ∈ Finset.Icc 1 (n + 1), varSource Q (flowJet A Q s) j r (fun _ => e))‖ ≤
        K * ‖u r - ∑ j ∈ Finset.Icc 1 (n + 1), y j r‖ + ε * η ^ (n + 2) := by
      intro r hr
      have hr' := Ico_subset_Icc_self hr
      set w := ∑ j ∈ Finset.Icc 1 n, y j r with hw
      -- the three parts of the source
      have hsplit : (G r (xs r + u r) - G r (xs r) - A r *ᵥ u r) -
          ∑ j ∈ Finset.Icc 1 (n + 1), varSource Q (flowJet A Q s) j r (fun _ => e) =
          (G r (xs r + u r) - G r (xs r) - A r *ᵥ u r -
            ∑ k ∈ Finset.Icc 2 N, Q r k (fun _ => u r)) +
          ∑ k ∈ Finset.Icc 2 N, (Q r k (fun _ => u r) - Q r k (fun _ => w)) +
          (∑ k ∈ Finset.Icc 2 N, Q r k (fun _ => w) -
            ∑ j ∈ Finset.Icc 1 (n + 1), varSource Q (flowJet A Q s) j r (fun _ => e)) := by
        rw [Finset.sum_sub_distrib]
        abel
      have hR : ‖G r (xs r + u r) - G r (xs r) - A r *ᵥ u r -
          ∑ k ∈ Finset.Icc 2 N, Q r k (fun _ => u r)‖ ≤ max c 0 * E ^ (N + 1) * η ^ (n + 2) := by
        refine (hTay r hr' (u r) ((hub r hr').trans heρ)).trans ?_
        calc c * ‖u r‖ ^ (N + 1) ≤ max c 0 * (E * η) ^ (N + 1) := by
              gcongr
              · exact le_max_left _ _
              · exact hub r hr'
          _ = max c 0 * E ^ (N + 1) * η ^ (N + 1) := by ring
          _ ≤ max c 0 * E ^ (N + 1) * η ^ (n + 2) :=
              mul_le_mul_of_nonneg_left (hηpow _ _ (by omega)) (by positivity)
      have hT1 : ‖∑ k ∈ Finset.Icc 2 N, (Q r k (fun _ => u r) - Q r k (fun _ => w))‖ ≤
          (N + 1 : ℝ) * (B * N * F ^ N * C) * η ^ (n + 2) := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ (B * N * F ^ N * C * η ^ (n + 2))
          fun k hk => ?_).trans ?_
        · simp only [Finset.mem_Icc] at hk
          have h := (Q r k).norm_image_sub_le (fun _ => u r) (fun _ => w)
          have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
          rw [Fintype.card_fin, pi_norm_const, pi_norm_const,
            show ((fun _ : Fin k => u r) - fun _ => w) = fun _ => u r - w from rfl,
            pi_norm_const] at h
          refine h.trans ?_
          have hmax : max ‖u r‖ ‖w‖ ≤ F * η :=
            max_le ((hub r hr').trans (mul_le_mul_of_nonneg_right
              ((le_add_of_nonneg_right hC0).trans (le_max_left _ _)) hη0)) (hwb r hr')
          have hpow : max ‖u r‖ ‖w‖ ^ (k - 1) ≤ F ^ N * η := by
            calc max ‖u r‖ ‖w‖ ^ (k - 1) ≤ (F * η) ^ (k - 1) := by gcongr
              _ = F ^ (k - 1) * η ^ (k - 1) := mul_pow _ _ _
              _ ≤ F ^ N * η ^ 1 :=
                  mul_le_mul (pow_le_pow_right₀ hF1 (by omega)) (hηpow 1 (k - 1) (by omega))
                    (by positivity) (by positivity)
              _ = F ^ N * η := by rw [pow_one]
          have hz := hzb r hr'
          have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk.2
          calc ‖Q r k‖ * k * max ‖u r‖ ‖w‖ ^ (k - 1) * ‖u r - w‖
              ≤ B * N * (F ^ N * η) * (C * η ^ (n + 1)) := by
                gcongr
                exact hB k hk.1 hk.2 r hr'
            _ = B * N * F ^ N * C * η ^ (n + 2) := by ring
        · rw [nsmul_eq_mul, ← mul_assoc]
          gcongr
          rw [Nat.card_Icc]
          exact_mod_cast (by omega : N + 1 - 2 ≤ N + 1)
      have hT2 : ‖∑ k ∈ Finset.Icc 2 N, Q r k (fun _ => w) -
          ∑ j ∈ Finset.Icc 1 (n + 1), varSource Q (flowJet A Q s) j r (fun _ => e)‖ ≤
          (T.card : ℝ) * (B * D₁ ^ N) * η ^ (n + 2) := by
        rw [hw, comp_identity hnN r e]
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ (B * D₁ ^ N * η ^ (n + 2)) fun a ha => ?_).trans ?_
        · rw [Finset.mem_filter, FormalMultilinearSeries.mem_compPartialSumTarget_iff] at ha
          refine ((ContinuousMultilinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (FormalMultilinearSeries.compAlongComposition_norm _ _ _)
              (by positivity))).trans ?_
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          have hq : ‖(fun k => if 2 ≤ k ∧ k ≤ N then Q r k else 0 : 𝓢) a.2.length‖ ≤ B := by
            by_cases h : 2 ≤ a.2.length ∧ a.2.length ≤ N
            · beta_reduce; rw [ite_eq_left h]; exact hB _ h.1 h.2 r hr'
            · beta_reduce; rw [ite_eq_right h, norm_zero]; exact hB0
          have hprod : ∏ i, ‖flowJet A Q s r (a.2.blocksFun i)‖ ≤ D₁ ^ N := by
            calc ∏ i, ‖flowJet A Q s r (a.2.blocksFun i)‖ ≤ ∏ _i : Fin a.2.length, D₁ :=
                  Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
                    (hD _ (by have := ha.1.2.2 i; omega) r hr').trans (le_max_left _ _)
              _ = D₁ ^ a.2.length := by
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              _ ≤ D₁ ^ N := pow_le_pow_right₀ (le_max_right _ _) (by have := ha.1.2.1; omega)
          have hηa : η ^ a.1 ≤ η ^ (n + 2) := hηpow _ _ (by omega)
          exact mul_le_mul (mul_le_mul hq hprod (by positivity) hB0) hηa (by positivity)
            (by positivity)
        · rw [nsmul_eq_mul, ← mul_assoc]
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          exact Nat.cast_le.2 (Finset.card_filter_le _ _)
      rw [hsplit]
      calc _ ≤ ‖A r *ᵥ (u r - ∑ j ∈ Finset.Icc 1 (n + 1), y j r)‖ +
            (‖G r (xs r + u r) - G r (xs r) - A r *ᵥ u r -
              ∑ k ∈ Finset.Icc 2 N, Q r k (fun _ => u r)‖ +
            ‖∑ k ∈ Finset.Icc 2 N, (Q r k (fun _ => u r) - Q r k (fun _ => w))‖ +
            ‖∑ k ∈ Finset.Icc 2 N, Q r k (fun _ => w) -
              ∑ j ∈ Finset.Icc 1 (n + 1), varSource Q (flowJet A Q s) j r (fun _ => e)‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) le_rfl)))
        _ ≤ K * ‖u r - ∑ j ∈ Finset.Icc 1 (n + 1), y j r‖ +
            (max c 0 * E ^ (N + 1) * η ^ (n + 2) +
              (N + 1 : ℝ) * (B * N * F ^ N * C) * η ^ (n + 2) +
              (T.card : ℝ) * (B * D₁ ^ N) * η ^ (n + 2)) := by
            gcongr
            exact hAK r hr' _
        _ = K * ‖u r - ∑ j ∈ Finset.Icc 1 (n + 1), y j r‖ + ε * η ^ (n + 2) := by
            rw [hε]; ring
    -- the remainder vanishes at the initial time
    have h0 : ‖u s - ∑ j ∈ Finset.Icc 1 (n + 1), y j s‖ ≤ 0 := by
      have hs1 : ∑ j ∈ Finset.Icc 1 (n + 1), y j s = e := by
        rw [Finset.sum_eq_single 1 (fun j hj hj1 => ?_) (fun h => absurd
          (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) h)]
        · simp only [hy, flowJet_one, LinearSystems.stateTransitionMatrix_self, Matrix.one_mulVec]
        · simp only [Finset.mem_Icc] at hj
          exact flowJet_start hA hQ (by omega) (by omega) _
      rw [hs1, show u s = e from rfl, sub_self, norm_zero]
    have h := FlowDerivative.norm_le_of_hasDerivWithinAt K.2 (by positivity) hd hbd h0 r₀ hr₀
    calc ‖x r₀ - xs r₀ - ∑ j ∈ Finset.Icc 1 (n + 1), flowJet A Q s r₀ j (fun _ => e)‖
        ≤ (0 + ε * η ^ (n + 2) * (t - s)) * Real.exp (K * (t - s)) := h
      _ = remConst E (t - s) B c D N (n + 1) * η ^ (n + 1 + 1) := by
          simp only [remConst]
          rw [← hCdef, hε, hF, hD₁, hT, hE]
          ring


/-- The first coefficient of the jet at the period is the monodromy:
`∑_{1 ≤ j ≤ N} P_j(e, …, e) = M e + ∑_{2 ≤ j ≤ N} P_j(e, …, e)`, `M = Φ(T, 0)`. -/
@[tmio T, powerlib_foundation] theorem sum_flowJet_eq {N : ℕ} (hN : 1 ≤ N) (T : ℝ)
    (e : X → ℝ) :
    ∑ j ∈ Finset.Icc 1 N, flowJet A Q 0 T j (fun _ => e) =
      monodromy A T 0 *ᵥ e + ∑ j ∈ Finset.Icc 2 N, flowJet A Q 0 T j (fun _ => e) := by
  rw [← Finset.add_sum_Ioc_eq_sum_Icc hN, flowJet_one, monodromy, zero_add]
  rfl

/-- **The Taylor expansion of the period map to order `N`.** Let `G` be continuous and
`K`-Lipschitz in the state, `x_*` a global solution with `x_*(T) = x_*(0)`, and let `G` have
along `x_*` on `[0, T]` the expansion of order `N ≥ 1` of `norm_sub_flowJet_le` (`‖Q_k‖ ≤ B`,
remainder `c ‖u‖^{N+1}` for `‖u‖ ≤ ρ`). Then the period map `P(ξ) = x(T; 0, ξ)`
(`FlowDerivative.periodMap`) satisfies, with `p = x_*(0)`, `M = Φ(T, 0) = monodromy A T 0` and
the coefficients `P_j = P_j(T)` of the variational hierarchy,
`‖P(p + e) − p − M e − ∑_{2 ≤ j ≤ N} P_j(e, …, e)‖ ≤ C ‖e‖^{N+1}` for
`‖e‖ ≤ min 1 (ρ e^{−KT})`, `C = flowConst K T B c N`. -/
@[tmio T, powerlib_foundation] theorem periodMap_jet {G : ℝ → (X → ℝ) → X → ℝ} {K : NNReal}
    (hGc : Continuous (uncurry G)) (hK : ∀ t, LipschitzWith K (G t)) (hA : Continuous A)
    {N : ℕ} (hN : 1 ≤ N) (hQ : ∀ k, 2 ≤ k → k ≤ N → Continuous fun r => Q r k) {T B c ρ : ℝ}
    (hT : 0 ≤ T) (hAK : ∀ r ∈ Icc 0 T, ∀ v, ‖A r *ᵥ v‖ ≤ K * ‖v‖) (hB0 : 0 ≤ B)
    (hB : ∀ k, 2 ≤ k → k ≤ N → ∀ r ∈ Icc 0 T, ‖Q r k‖ ≤ B) {xs : ℝ → X → ℝ}
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hper : xs T = xs 0)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) - A r *ᵥ u -
      ∑ k ∈ Finset.Icc 2 N, Q r k (fun _ => u)‖ ≤ c * ‖u‖ ^ (N + 1))
    (e : X → ℝ) (he : ‖e‖ ≤ min 1 (ρ / Real.exp (K * T))) :
    ‖FlowDerivative.periodMap hGc hK T (xs 0 + e) - xs 0 - monodromy A T 0 *ᵥ e -
        ∑ j ∈ Finset.Icc 2 N, flowJet A Q 0 T j (fun _ => e)‖ ≤
      flowConst K T B c N * ‖e‖ ^ (N + 1) := by
  have hxsI : IsIntegralCurveOn xs G (Icc 0 T) := fun r _ => (hxs r).hasDerivWithinAt
  set x := FlowDerivative.flow hGc hK 0 (xs 0 + e) with hxdef
  have hx0 : x 0 - xs 0 = e := by
    rw [hxdef, FlowDerivative.flow_start]; abel
  have hxI : IsIntegralCurveOn x G (Icc 0 T) :=
    (FlowDerivative.flow_solution hGc hK 0 _).mono Icc_subset_Ici_self
  have hE : 0 < Real.exp (K * T) := Real.exp_pos _
  have he1 : ‖x 0 - xs 0‖ ≤ 1 := by rw [hx0]; exact he.trans (min_le_left _ _)
  have heρ : Real.exp (K * (T - 0)) * ‖x 0 - xs 0‖ ≤ ρ := by
    rw [hx0, sub_zero]
    have := he.trans (min_le_right _ _)
    rw [le_div_iff₀ hE] at this
    linarith
  have h := norm_sub_flowJet_le hK hA hQ hT hAK hB0 hB hxsI hTay hxI he1 heρ T ⟨hT, le_rfl⟩
  rw [hx0, hper, sum_flowJet_eq hN, ← sub_sub, sub_zero] at h
  exact h

/-! ## Fields of class `C^{N+1}` -/

section ContDiff

/-- **Taylor's theorem to order `N` with a remainder of order `N + 1`.** For `f` of class
`C^{N+1}` on the closed ball of radius `ρ` about `x` with `‖D^{N+1}f‖ ≤ B` there,
`‖f(x + u) − ∑_{k ≤ N} D^kf(x)(u, …, u)/k!‖ ≤ B/(N + 1)! ‖u‖^{N+1}` for `‖u‖ ≤ ρ` (Mathlib
`map_add_eq_sum_add_integral_iteratedFDeriv`, the integral remainder
`(1/N!) ∫₀¹ (1 − τ)^N D^{N+1}f(x + τ u)(u, …, u) dτ`). -/
@[tmio T, powerlib_foundation] theorem norm_taylor_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {N : ℕ}
    {f : E → F} {x : E} {ρ B : ℝ} (hf : ∀ y ∈ Metric.closedBall x ρ, ContDiffAt ℝ (N + 1) f y)
    (hB : ∀ y ∈ Metric.closedBall x ρ, ‖iteratedFDeriv ℝ (N + 1) f y‖ ≤ B) {u : E}
    (hu : ‖u‖ ≤ ρ) :
    ‖f (x + u) - ∑ k ∈ Finset.range (N + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => u)‖ ≤
      B / (N + 1)! * ‖u‖ ^ (N + 1) := by
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • u ∈ Metric.closedBall x ρ := fun τ hτ => by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hτ.1]
    nlinarith [norm_nonneg u, hτ.2]
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (n := N) (x := x) (y := u) (f := f)
    (fun τ hτ => hf _ (hmem τ hτ))
  rw [hT, add_sub_cancel_left]
  have hbound : ∀ τ ∈ Ioc (0 : ℝ) 1,
      ‖(1 - τ) ^ N • iteratedFDeriv ℝ (N + 1) f (x + τ • u) (fun _ => u)‖ ≤
        (1 - τ) ^ N * (B * ‖u‖ ^ (N + 1)) := by
    intro τ hτ
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (by linarith [hτ.2]) N)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith [hτ.2]) N)
    refine ((iteratedFDeriv ℝ (N + 1) f (x + τ • u)).le_opNorm _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    exact hB _ (hmem τ ⟨hτ.1.le, hτ.2⟩)
  have hint := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    zero_le_one (MeasureTheory.ae_of_all _ hbound)
    ((by fun_prop : Continuous fun τ : ℝ => (1 - τ) ^ N * (B * ‖u‖ ^ (N + 1))).intervalIntegrable
      0 1)
  have hval : ∫ τ in (0 : ℝ)..1, (1 - τ) ^ N * (B * ‖u‖ ^ (N + 1)) =
      B * ‖u‖ ^ (N + 1) / (N + 1) := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_comp_sub_left (fun τ => τ ^ N)]
    norm_num [integral_pow]
    ring
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc (N ! : ℝ)⁻¹ * ‖∫ τ in (0 : ℝ)..1,
        (1 - τ) ^ N • iteratedFDeriv ℝ (N + 1) f (x + τ • u) (fun _ => u)‖
      ≤ (N ! : ℝ)⁻¹ * (B * ‖u‖ ^ (N + 1) / (N + 1)) := by rw [← hval]; gcongr
    _ = B / (N + 1)! * ‖u‖ ^ (N + 1) := by
        rw [Nat.factorial_succ]; push_cast; field_simp

/-- The Taylor coefficients of a field along a curve, `Q_k(r) = D_x^kG(r, x_*(r))/k!`. -/
def taylorSeries (G : ℝ → (X → ℝ) → X → ℝ) (xs : ℝ → X → ℝ) (r : ℝ) : 𝓢 :=
  fun k => (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k (G r) (xs r)

omit [DecidableEq X] in
/-- **The Taylor expansion along a curve for a field of class `C^{N+1}`.** If `G(r, ·)` is
`C^{N+1}` on the tube of radius `ρ` about `x_*` with `‖D_x^{N+1}G‖ ≤ B` there (`N ≥ 1`), then
along `x_*`,
`‖G(r, x_* + u) − G(r, x_*) − D_xG u − ∑_{2 ≤ k ≤ N} Q_k(u, …, u)‖ ≤ B/(N + 1)! ‖u‖^{N+1}` for
`‖u‖ ≤ ρ`, with `Q = taylorSeries G x_*`. -/
@[tmio T, powerlib_foundation] theorem taylor_along_of_contDiff_order
    {G : ℝ → (X → ℝ) → X → ℝ} {xs : ℝ → X → ℝ} {I : Set ℝ} {N : ℕ} (hN : 1 ≤ N) {ρ B : ℝ}
    (hG : ∀ r ∈ I, ∀ y ∈ Metric.closedBall (xs r) ρ, ContDiffAt ℝ (N + 1) (G r) y)
    (hB : ∀ r ∈ I, ∀ y ∈ Metric.closedBall (xs r) ρ, ‖iteratedFDeriv ℝ (N + 1) (G r) y‖ ≤ B) :
    ∀ r ∈ I, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) - fderiv ℝ (G r) (xs r) u -
      ∑ k ∈ Finset.Icc 2 N, taylorSeries G xs r k (fun _ => u)‖ ≤
        B / (N + 1)! * ‖u‖ ^ (N + 1) := by
  intro r hr u hu
  have h := norm_taylor_le (hG r hr) (hB r hr) hu
  set g : ℕ → X → ℝ := fun k => (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k (G r) (xs r) (fun _ => u)
    with hg
  have hsum : ∑ k ∈ Finset.range (N + 1), g k =
      G r (xs r) + fderiv ℝ (G r) (xs r) u +
        ∑ k ∈ Finset.Icc 2 N, taylorSeries G xs r k (fun _ => u) := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : 2 ≤ N + 1),
      Finset.Ico_add_one_right_eq_Icc, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : g 0 = G r (xs r) := by
      simp only [hg, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
        iteratedFDeriv_zero_apply]
    have h1 : g 1 = fderiv ℝ (G r) (xs r) u := by
      simp only [hg, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
        iteratedFDeriv_one_apply]
    rw [h0, h1]
    rfl
  rw [hsum] at h
  convert h using 2
  abel

/-- **The period map of a field of class `C^{N+1}` to order `N`.** `periodMap_jet` for a field
with `G(t, ·)` of class `C^{N+1}` (`N ≥ 1`), `D_xG` jointly continuous, `D_x^kG` continuous along
`x_*` for `2 ≤ k ≤ N` and `‖D_x^{N+1}G‖ ≤ B` on the tube of radius `ρ` about `x_*` over `[0, T]`:
the coefficients are those of the variational hierarchy of `A = D_xG(·, x_*)`
(`jacobianAlong G x_*`) and `Q_k = D_x^kG/k!` along `x_*` (`taylorSeries G x_*`). -/
@[tmio T, powerlib_foundation] theorem periodMap_jet_of_contDiff {G : ℝ → (X → ℝ) → X → ℝ}
    {K : NNReal} (hGc : Continuous (uncurry G)) (hK : ∀ t, LipschitzWith K (G t)) {N : ℕ}
    (hN : 1 ≤ N) (hG : ∀ t, ContDiff ℝ (N + 1) (G t))
    (hD : Continuous fun p : ℝ × (X → ℝ) => fderiv ℝ (G p.1) p.2) {xs : ℝ → X → ℝ}
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) {T : ℝ} (hT : 0 ≤ T) (hper : xs T = xs 0)
    (hDk : ∀ k, 2 ≤ k → k ≤ N → Continuous fun r => iteratedFDeriv ℝ k (G r) (xs r)) {ρ B : ℝ}
    (hB : ∀ r ∈ Icc 0 T, ∀ y ∈ Metric.closedBall (xs r) ρ,
      ‖iteratedFDeriv ℝ (N + 1) (G r) y‖ ≤ B) :
    ∃ C, 0 ≤ C ∧ ∀ e : X → ℝ, ‖e‖ ≤ min 1 (ρ / Real.exp (K * T)) →
      ‖FlowDerivative.periodMap hGc hK T (xs 0 + e) - xs 0 -
        monodromy (FlowDerivative.jacobianAlong G xs) T 0 *ᵥ e -
        ∑ j ∈ Finset.Icc 2 N,
          flowJet (FlowDerivative.jacobianAlong G xs) (taylorSeries G xs) 0 T j (fun _ => e)‖ ≤
        C * ‖e‖ ^ (N + 1) := by
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  have hAK : ∀ r ∈ Icc 0 T, ∀ v, ‖FlowDerivative.jacobianAlong G xs r *ᵥ v‖ ≤ K * ‖v‖ :=
    fun r _ v => by
      rw [FlowDerivative.jacobianAlong_mulVec]
      exact ((fderiv ℝ (G r) (xs r)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hK r)) (norm_nonneg v))
  have hTay := taylor_along_of_contDiff_order (I := Icc 0 T) hN
    (fun r _ y _ => (hG r).contDiffAt) hB
  have hQc : ∀ k, 2 ≤ k → k ≤ N → Continuous fun r => taylorSeries G xs r k :=
    fun k hk1 hk2 => (hDk k hk1 hk2).const_smul ((k ! : ℝ)⁻¹)
  obtain ⟨B', hB'0, hB'⟩ := exists_bound_coeff (Q := taylorSeries G xs) (s := 0) (t := T) N hQc
  refine ⟨flowConst K T B' (B / (N + 1)!) N, flowConst_nonneg N hT hB'0, fun e he =>
    periodMap_jet hGc hK (FlowDerivative.continuous_jacobianAlong hD hxc) hN hQc hT hAK hB'0 hB'
      hxs hper (fun r hr u hu => ?_) e he⟩
  rw [FlowDerivative.jacobianAlong_mulVec]
  exact hTay r hr u hu

end ContDiff

end powerlib.Periodic.PeriodMapJet
