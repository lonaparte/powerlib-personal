import theorem.DAE.Pryce

/-! # Pantelides' index-reduction algorithm: termination under structural nonsingularity

Foundation layer (category B of the work-sync formalization).

Object: the structural description of a square DAE from `theorem.DAE.Pryce` — a `Signature ι`
with `occurs i j` (variable `x_j` appears in equation `F_i`) and `order i j` (highest derivative
order of `x_j` in `F_i`); equations and variables are both indexed by the finite type `ι`.

Algorithm (Pantelides 1988, written in offset form). A state (`PantelidesState`) records
`c i` (how often `F_i` has been differentiated), `d j` (the highest derivative `x_j^(d j)` present
in the extended system) and a partial assignment `assign : ι → Option ι` of equations to
variables. The current version `F_i^(c i)` contains `x_j^(order i j + c i)`; the
*highest-derivative graph* (`Tight`) joins `F_i` to `x_j` when `occurs i j` and
`order i j + c i = d j`, i.e. when `F_i^(c i)` contains the current highest derivative of `x_j`
(Pantelides' `AUGMENTPATH` ignores the variables that already have a derivative).
* Initial state (`initial`): `c = 0`, `d j = max_i order i j`, nothing assigned.
* Search from an unassigned equation `i` (`reachWithin`, `Reach`): the coloured equations are `i`
  and, recursively, every equation assigned to a variable adjacent (in the highest-derivative
  graph) to a coloured equation — Pantelides' colouring of the alternating search.
* Step (`Step`), for any unassigned equation `i`:
  - `augment` (path found: some variable adjacent to a coloured equation is unassigned): the
    assignment becomes a matching of the same highest-derivative graph that covers the previously
    assigned equations and `i`. The augmenting-path update of the algorithm is one such matching
    (`exists_step` constructs it by switching along the alternating path, `exists_switch`); the
    step allows any of them.
  - `differentiate` (no path: `SearchFails`): every coloured equation is differentiated
    (`c ← c + 1`) and every coloured variable — the highest-derivative neighbours of coloured
    equations — receives its next derivative (`d ← d + 1`); assignments are carried to the
    derivatives (`ASSIGN(A(j)) := B(ASSIGN(j))`). By `differentiate_d_eq_max`, this is the same as
    the note's formulation "add `dF_k/dt` for every equation on the path and `dz_j/dt` for every
    variable in it": the new highest derivative of `x_j` is the maximum of the old one and the
    orders occurring in the differentiated coloured equations.
  The equation `i` processed at each step is arbitrary, so the results cover Pantelides'
  sequential order (process `F_1, F_2, …` and keep working on `F_i` until it is assigned).
* Terminal state (`PantelidesState.IsFinal`): every equation is assigned.

Results.
* Invariant (`Valid`, `Step.valid`): the offsets are dual feasible
  (`order i j + c i ≤ d j` wherever `occurs i j`, Pryce's `IsDualFeasible`) and `assign` is a
  matching of the highest-derivative graph.
* Measure (`potential σ`, for a transversal `σ`): number of unassigned equations plus
  `Σ d - (Σ c + value σ)`, which is a natural number by weak duality (`value_add_le`). An
  augmentation assigns one more equation; a failed search colours one more equation than
  variables (`card_coloured_lt`: every coloured variable is assigned to a coloured equation other
  than `i`), so a differentiation lowers `Σ d - Σ c` (`Step.potential_lt`).
* Progress (`exists_step`): every valid state with an unassigned equation has a step.
* **Termination** (`pantelides_terminates`): if the occurrence pattern has a transversal
  (structural nonsingularity), every run from the initial state has at most
  `|ι| + Σ_j d⁰_j` steps, and some run reaches a terminal state; its assignment is a transversal
  `σ` on which the final offsets are dual feasible and tight — Pryce's conditions — so `σ` is a
  highest-value transversal and `Σ d - Σ c = value σ`.
* Necessity (`exists_infinite_run`, `pantelides_terminates_iff`): if no transversal exists, there
  is an infinite run; hence "every run terminates" is equivalent to structural nonsingularity
  (`StructurallyNonsingular`, a nonsingular real matrix with the occurrence pattern).
* Relation to Pryce — **equality, for every run** (§1.5 of the note). `pryce_le_pantelides`: at
  a reachable state with assignment `σ`, Pryce's least offsets for `σ` are componentwise at most
  Pantelides' counts `(c, d)`. Conversely (`differentiate_le`, `le_of_reaches`), along every run
  the counts stay below every pair of offsets that is dual feasible and tight on some transversal
  (every optimal dual solution of the assignment problem): a failed search can only colour
  equations and variables whose optimal offsets are strictly above the current counts. Hence
  `pryce_eq_pantelides`: Pryce's offsets on the final assignment *equal* `(c, d)`;
  `pryce_eq_pantelides_of_highestValue`: the same holds for Pryce's offsets on any
  highest-value transversal. Uniqueness question: the step relation is nondeterministic (choice
  of the processed equation, choice of the augmenting matching) and different runs may end with
  different assignments, but `pantelides_offsets_unique` shows that all terminating runs end with
  the same counts `(c, d)` — the componentwise least optimal dual offsets (Pryce's canonical
  offsets). So the correct form of the note's claim is "all runs give Pryce's offsets", not
  merely "some run does" (`pantelides_eq_of_least` computes the counts from least offsets).
* Examples: termination on the pendulum and on the index-formula counterexample of
  `theorem.DAE.Pryce` (`pendulum_pantelides_terminates`, `example_pantelides_terminates`); every
  terminating run on the pendulum ends with `c = (1,1,0,0,2)`, `d = (2,2,1,1,0)`
  (`pendulum_offsets_least`, `pendulum_pantelides_counts`); on the counterexample no run ever
  differentiates (`example_pantelides_counts`); an infinite run on a structurally singular
  pattern (`singular_pantelides_nonterminating`).

Model boundary: structural (occurrence/order pattern) analysis only. No claim is made that the
number of differentiations equals the differentiation index (the note's "key lemma"
`ν_S = max differentiations + 1`, and its structural-regularity premise), that the output system
has index 1, about Hopcroft–Karp complexity, or about dummy derivatives (§1.4). The augmentation
step is the abstract "some augmenting matching" rather than one specific path search.

Architecture: generic mathematical support (no `Family`); the algorithm state is static
combinatorial data (no time, no solution notion), all results `@[powerlib_foundation]`.

Source: work-sync theory/T-pantelides-index-reduction.md §1.3 (Pantelides algorithm,
bipartite matching, augmenting paths, differentiation of the equations on the path), §1.5
(offsets, HVT, relation of Pantelides' counts to Pryce's offsets); Pantelides, SIAM J. Sci.
Stat. Comput. 9 (1988) 213–231; Pryce, BIT 41 (2001) 364–394, §5.
-/

noncomputable section
namespace powerlib.DAE
open Finset

/-- State of Pantelides' algorithm in offset form: equation `i` has been differentiated `c i`
times, the highest derivative of variable `j` present in the extended system is `x_j^(d j)`,
and `assign i = some j` records that (the `c i`-th derivative of) equation `i` is assigned to
`x_j^(d j)`. -/
structure PantelidesState (ι : Type*) where
  c : ι → ℕ
  d : ι → ℕ
  assign : ι → Option ι

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace PantelidesState

/-- Terminal state: every equation is assigned. -/
def IsFinal (st : PantelidesState ι) : Prop := ∀ i, (st.assign i).isSome

/-- Number of unassigned equations. -/
def unassigned (st : PantelidesState ι) : ℕ := (univ.filter fun i => st.assign i = none).card

end PantelidesState

namespace Signature

variable (S : Signature ι)

/-- Edge of the highest-derivative graph: `x_j^(d j)` occurs in the `c i`-th derivative of
equation `i`. -/
def Tight (c d : ι → ℕ) (i j : ι) : Prop := S.occurs i j = true ∧ S.order i j + c i = d j

/-- Invariant of the algorithm: dual feasibility of the offsets (no derivative above `d j`
occurs), and `assign` is a matching of the highest-derivative graph. -/
def Valid (st : PantelidesState ι) : Prop :=
  S.IsDualFeasible st.c st.d ∧ (∀ i j, st.assign i = some j → S.Tight st.c st.d i j) ∧
    ∀ i i' j, st.assign i = some j → st.assign i' = some j → i = i'

/-- Equations coloured within `k` rounds of the alternating search from equation `i`
(Pantelides' `AUGMENTPATH`): from a coloured equation, along a highest-derivative edge to a
variable, then back along the assignment to the equation assigned to it. -/
def reachWithin (st : PantelidesState ι) (i : ι) : ℕ → ι → Prop
  | 0, x => x = i
  | k + 1, x => reachWithin st i k x ∨
      ∃ l j, reachWithin st i k l ∧ S.Tight st.c st.d l j ∧ st.assign x = some j

/-- Equations coloured by the alternating search from `i`. -/
def Reach (st : PantelidesState ι) (i x : ι) : Prop := ∃ k, S.reachWithin st i k x

/-- The search from `i` finds no augmenting path: every variable adjacent (in the
highest-derivative graph) to a coloured equation is already assigned. -/
def SearchFails (st : PantelidesState ι) (i : ι) : Prop :=
  ∀ l j, S.Reach st i l → S.Tight st.c st.d l j → ∃ x, st.assign x = some j

open Classical in
/-- Failure branch of Pantelides' algorithm: differentiate every coloured equation once and
introduce the next derivative of every coloured variable; assignments are carried to the
derivatives. -/
def differentiate (st : PantelidesState ι) (i : ι) : PantelidesState ι where
  c l := st.c l + if S.Reach st i l then 1 else 0
  d j := st.d j + if ∃ l, S.Reach st i l ∧ S.Tight st.c st.d l j then 1 else 0
  assign := st.assign

/-- One step of Pantelides' algorithm for an unassigned equation `i`: if the alternating search
succeeds, the matching is augmented (abstractly: replaced by any matching of the same
highest-derivative graph covering the previously assigned equations and `i`); if it fails, the
coloured equations and variables are differentiated. -/
inductive Step : PantelidesState ι → PantelidesState ι → Prop
  | augment (st : PantelidesState ι) (i : ι) (a : ι → Option ι) :
      st.assign i = none → ¬ S.SearchFails st i →
      (∀ l j, a l = some j → S.Tight st.c st.d l j) →
      (∀ l l' j, a l = some j → a l' = some j → l = l') →
      (∀ l, (a l).isSome ↔ ((st.assign l).isSome ∨ l = i)) →
      Step st ⟨st.c, st.d, a⟩
  | differentiate (st : PantelidesState ι) (i : ι) :
      st.assign i = none → S.SearchFails st i → Step st (S.differentiate st i)

/-- Initial state: no equation differentiated, `d j` the highest derivative order of `x_j` in
the original system, nothing assigned. -/
def initial : PantelidesState ι where
  c _ := 0
  d j := (univ.filter fun i => S.occurs i j = true).sup fun i => S.order i j
  assign _ := none

/-- Termination measure relative to a transversal `σ`. -/
def potential (σ : Equiv.Perm ι) (st : PantelidesState ι) : ℕ :=
  st.unassigned + (∑ j, st.d j - (∑ i, st.c i + S.value σ))

/-! ## Invariant -/

omit [DecidableEq ι] in
@[powerlib_foundation] theorem initial_valid : S.Valid S.initial := by
  refine ⟨fun i j hij => ?_, fun _ _ h => by simp [initial] at h, fun _ _ _ h => by
    simp [initial] at h⟩
  simp only [initial, add_zero]
  exact Finset.le_sup (f := fun i => S.order i j) (by simpa using hij)

omit [Fintype ι] [DecidableEq ι] in
@[powerlib_foundation] theorem reachWithin_mono {st : PantelidesState ι} {i : ι} {k k' : ℕ}
    (h : k ≤ k') {x : ι} (hx : S.reachWithin st i k x) : S.reachWithin st i k' x := by
  induction h with
  | refl => exact hx
  | step _ ih => exact Or.inl ih

omit [Fintype ι] [DecidableEq ι] in
@[powerlib_foundation] theorem reachWithin_dom {st : PantelidesState ι} {i : ι} :
    ∀ k x, S.reachWithin st i k x → x = i ∨ (st.assign x).isSome := by
  intro k
  induction k with
  | zero => intro x hx; exact Or.inl hx
  | succ k ih =>
    rintro x (hx | ⟨l, j, -, -, hj⟩)
    · exact ih x hx
    · exact Or.inr (by simp [hj])

omit [Fintype ι] [DecidableEq ι] in
@[powerlib_foundation] theorem reach_of_assign {st : PantelidesState ι} {i l j x : ι}
    (hl : S.Reach st i l) (ht : S.Tight st.c st.d l j) (hx : st.assign x = some j) :
    S.Reach st i x := by
  obtain ⟨k, hk⟩ := hl
  exact ⟨k + 1, Or.inr ⟨l, j, hk, ht, hx⟩⟩

omit [Fintype ι] [DecidableEq ι] in
@[powerlib_foundation] theorem reach_self (st : PantelidesState ι) (i : ι) : S.Reach st i i :=
  ⟨0, rfl⟩

omit [DecidableEq ι] in
/-- The failure branch preserves the invariant: the coloured variables are exactly the
highest-derivative neighbours of the coloured equations, so tight edges out of coloured
equations stay tight, other edges stay below the new highest derivatives, and every assigned
edge is either inside the coloured part or outside it. -/
@[powerlib_foundation] theorem differentiate_valid {st : PantelidesState ι} {i : ι}
    (hv : S.Valid st) : S.Valid (S.differentiate st i) := by
  classical
  obtain ⟨hf, ht, hinj⟩ := hv
  refine ⟨fun l j hlj => ?_, fun l j hlj => ?_, hinj⟩
  · simp only [differentiate]
    have h1 := hf l j hlj
    by_cases hl : S.Reach st i l
    · by_cases htj : S.Tight st.c st.d l j
      · have hJ : ∃ l, S.Reach st i l ∧ S.Tight st.c st.d l j := ⟨l, hl, htj⟩
        have := htj.2
        simp only [hl, hJ, ite_true]
        omega
      · have hlt : S.order l j + st.c l < st.d j := lt_of_le_of_ne h1 (fun h => htj ⟨hlj, h⟩)
        simp only [hl, ite_true]
        split_ifs <;> omega
    · simp only [hl, ite_false]
      split_ifs <;> omega
  · obtain ⟨hocc, heq⟩ := ht l j hlj
    refine ⟨hocc, ?_⟩
    simp only [differentiate]
    by_cases hl : S.Reach st i l
    · have hJ : ∃ l, S.Reach st i l ∧ S.Tight st.c st.d l j := ⟨l, hl, ⟨hocc, heq⟩⟩
      simp only [hl, hJ, ite_true]
      omega
    · have hJ : ¬ ∃ l', S.Reach st i l' ∧ S.Tight st.c st.d l' j := by
        rintro ⟨l', hl', ht'⟩
        exact hl (S.reach_of_assign hl' ht' hlj)
      simp only [hl, hJ, ite_false]
      omega

omit [DecidableEq ι] in
@[powerlib_foundation] theorem Step.valid {st st' : PantelidesState ι} (hv : S.Valid st)
    (h : S.Step st st') : S.Valid st' := by
  cases h with
  | augment i a _ _ ht hinj _ => exact ⟨hv.1, ht, hinj⟩
  | differentiate i _ _ => exact S.differentiate_valid hv

/-! ## The termination measure -/

omit [DecidableEq ι] in
open Classical in
@[powerlib_foundation] theorem sum_differentiate_c (st : PantelidesState ι) (i : ι) :
    ∑ l, (S.differentiate st i).c l = ∑ l, st.c l + (univ.filter (S.Reach st i)).card := by
  simp only [differentiate, sum_add_distrib, sum_boole, Nat.cast_id]

omit [DecidableEq ι] in
open Classical in
@[powerlib_foundation] theorem sum_differentiate_d (st : PantelidesState ι) (i : ι) :
    ∑ j, (S.differentiate st i).d j = ∑ j, st.d j +
      (univ.filter fun j => ∃ l, S.Reach st i l ∧ S.Tight st.c st.d l j).card := by
  simp only [differentiate, sum_add_distrib, sum_boole, Nat.cast_id]

open Classical in
/-- A failed search colours one more equation than variables (Hall violator): every coloured
variable is assigned to a coloured equation other than the root `i`. -/
@[powerlib_foundation] theorem card_coloured_lt {st : PantelidesState ι} {i : ι}
    (hi : st.assign i = none) (hfail : S.SearchFails st i) :
    (univ.filter fun j => ∃ l, S.Reach st i l ∧ S.Tight st.c st.d l j).card <
      (univ.filter (S.Reach st i)).card := by
  have hsurj : Set.SurjOn (fun x => (st.assign x).getD i)
      ↑((univ.filter (S.Reach st i)).erase i)
      ↑(univ.filter fun j => ∃ l, S.Reach st i l ∧ S.Tight st.c st.d l j) := by
    intro j hj
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj
    obtain ⟨l, hl, htj⟩ := hj
    obtain ⟨x, hx⟩ := hfail l j hl htj
    refine ⟨x, ?_, by simp [hx]⟩
    simp only [coe_erase, coe_filter, mem_univ, true_and, Set.mem_sdiff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    refine ⟨S.reach_of_assign hl htj hx, fun hxi => ?_⟩
    rw [hxi, hi] at hx
    cases hx
  have h1 := card_le_card_of_surjOn _ hsurj
  have h2 : i ∈ univ.filter (S.Reach st i) := by simp [S.reach_self st i]
  rw [card_erase_of_mem h2] at h1
  have h3 : 0 < (univ.filter (S.Reach st i)).card := card_pos.mpr ⟨i, h2⟩
  omega

/-- Each step strictly decreases the measure: an augmentation assigns one more equation, a
differentiation lowers `Σ d - Σ c` (bounded below by the value of any transversal, weak
duality) by at least one. -/
@[powerlib_foundation] theorem Step.potential_lt {σ : Equiv.Perm ι} (hσ : S.IsTransversal σ)
    {st st' : PantelidesState ι} (hv : S.Valid st) (h : S.Step st st') :
    S.potential σ st' < S.potential σ st := by
  classical
  have hv' := h.valid S hv
  have hw := S.value_add_le hσ hv.1
  have hw' := S.value_add_le hσ hv'.1
  cases h with
  | augment i a hi _ _ _ hdom =>
    simp only [potential, PantelidesState.unassigned]
    have hsub : (univ.filter fun l => a l = none) ⊂ univ.filter fun l => st.assign l = none := by
      refine ssubset_iff_of_subset (fun l hl => ?_) |>.mpr ⟨i, by simp [hi], ?_⟩
      · simp only [mem_filter, mem_univ, true_and] at hl ⊢
        have := (hdom l).not
        simp only [hl, Option.isSome_none, Bool.false_eq_true, not_false_eq_true, not_or,
          true_iff] at this
        simpa using this.1
      · have := (hdom i).mpr (Or.inr rfl)
        simp only [mem_filter, mem_univ, true_and]
        intro hai
        simp [hai] at this
    have := card_lt_card hsub
    omega
  | differentiate i hi hfail =>
    have hc := S.sum_differentiate_c st i
    have hd := S.sum_differentiate_d st i
    have hlt := S.card_coloured_lt hi hfail
    simp only [potential, PantelidesState.unassigned] at hw' ⊢
    have hu : (S.differentiate st i).assign = st.assign := rfl
    rw [hu]
    omega

/-! ## Progress: alternating paths -/

omit [Fintype ι] in
/-- Switching along an alternating path: for every equation `l` coloured within `k` rounds of
the search from the unassigned equation `i`, there is a matching of the highest-derivative
graph assigning exactly the previously assigned equations and `i`, except `l`, with the same
assigned variables, and agreeing with `assign` outside the equations coloured within `k`
rounds. -/
@[powerlib_foundation] theorem exists_switch {st : PantelidesState ι} {i : ι} (hv : S.Valid st)
    (hi : st.assign i = none) :
    ∀ k l, S.reachWithin st i k l → ∃ a : ι → Option ι,
      (∀ x j, a x = some j → S.Tight st.c st.d x j) ∧
      (∀ x x' j, a x = some j → a x' = some j → x = x') ∧
      (∀ x, (a x).isSome ↔ (((st.assign x).isSome ∨ x = i) ∧ x ≠ l)) ∧
      (∀ j, (∃ x, a x = some j) ↔ ∃ x, st.assign x = some j) ∧
      (∀ x, ¬ S.reachWithin st i k x → a x = st.assign x) := by
  intro k
  induction k with
  | zero =>
    intro l hl
    have hl' : l = i := hl
    subst hl'
    refine ⟨st.assign, hv.2.1, hv.2.2, fun x => ?_, fun j => Iff.rfl, fun x _ => rfl⟩
    by_cases hx : x = l
    · subst hx; simp [hi]
    · simp [hx]
  | succ k ih =>
    intro l hl
    by_cases hlk : S.reachWithin st i k l
    · obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ := ih l hlk
      exact ⟨a, ha1, ha2, ha3, ha4, fun x hx => ha5 x fun h => hx (Or.inl h)⟩
    · obtain ⟨l₀, j, hl₀, htj, hlj⟩ := hl.resolve_left hlk
      obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ := ih l₀ hl₀
      have hne : l ≠ l₀ := fun h => hlk (h ▸ hl₀)
      have hal : a l = some j := by rw [ha5 l hlk, hlj]
      have hal₀ : a l₀ = none := by
        have := (ha3 l₀).not
        simpa using this
      set a' : ι → Option ι := fun x => if x = l then none else if x = l₀ then some j else a x
        with ha'
      have hal' : a' l = none := by simp [ha']
      have hal₀' : a' l₀ = some j := by simp [ha', Ne.symm hne]
      have hax : ∀ x, x ≠ l → x ≠ l₀ → a' x = a x := fun x h1 h2 => by simp [ha', h1, h2]
      refine ⟨a', ?_, ?_, ?_, ?_, ?_⟩
      · intro x j' hx
        by_cases h1 : x = l
        · rw [h1, hal'] at hx; cases hx
        by_cases h2 : x = l₀
        · rw [h2, hal₀', Option.some.injEq] at hx
          rw [h2, ← hx]; exact htj
        rw [hax x h1 h2] at hx
        exact ha1 x j' hx
      · intro x x' j' hx hx'
        by_cases h1 : x = l
        · rw [h1, hal'] at hx; cases hx
        by_cases h1' : x' = l
        · rw [h1', hal'] at hx'; cases hx'
        by_cases h2 : x = l₀ <;> by_cases h2' : x' = l₀
        · rw [h2, h2']
        · rw [h2, hal₀', Option.some.injEq] at hx
          rw [hax x' h1' h2', ← hx] at hx'
          exact absurd (ha2 _ _ _ hx' hal) h1'
        · rw [h2', hal₀', Option.some.injEq] at hx'
          rw [hax x h1 h2, ← hx'] at hx
          exact absurd (ha2 _ _ _ hx hal) h1
        · rw [hax x h1 h2] at hx
          rw [hax x' h1' h2'] at hx'
          exact ha2 _ _ _ hx hx'
      · intro x
        by_cases h1 : x = l
        · rw [h1, hal']; simp
        by_cases h2 : x = l₀
        · rw [h2, hal₀']
          have hdom := S.reachWithin_dom k l₀ hl₀
          simp only [Option.isSome_some, true_iff]
          exact ⟨hdom.symm, h2 ▸ h1⟩
        · rw [hax x h1 h2, ha3 x]
          simp [h1, h2]
      · intro j'
        rw [← ha4 j']
        constructor
        · rintro ⟨x, hx⟩
          by_cases h1 : x = l
          · rw [h1, hal'] at hx; cases hx
          by_cases h2 : x = l₀
          · rw [h2, hal₀', Option.some.injEq] at hx
            exact ⟨l, hx ▸ hal⟩
          · rw [hax x h1 h2] at hx
            exact ⟨x, hx⟩
        · rintro ⟨x, hx⟩
          by_cases h1 : x = l
          · rw [h1, hal] at hx
            exact ⟨l₀, hx ▸ hal₀'⟩
          by_cases h2 : x = l₀
          · rw [h2, hal₀] at hx; cases hx
          · exact ⟨x, by rw [hax x h1 h2, hx]⟩
      · intro x hx
        have h1 : x ≠ l := fun h => hx (h ▸ hl)
        have h2 : x ≠ l₀ := fun h => hx (h ▸ Or.inl hl₀)
        rw [hax x h1 h2]
        exact ha5 x fun h => hx (Or.inl h)

/-- Progress: from a valid state, every unassigned equation admits a step (an augmentation
if the alternating search succeeds, a differentiation if it fails). -/
@[powerlib_foundation] theorem exists_step {st : PantelidesState ι} {i : ι} (hv : S.Valid st)
    (hi : st.assign i = none) : ∃ st', S.Step st st' := by
  classical
  by_cases hfail : S.SearchFails st i
  · exact ⟨_, Step.differentiate st i hi hfail⟩
  · have hfail' := hfail
    simp only [SearchFails, not_forall, not_exists] at hfail'
    obtain ⟨l, j, ⟨k, hl⟩, htj, hfree⟩ := hfail'
    obtain ⟨a, ha1, ha2, ha3, ha4, -⟩ := S.exists_switch hv hi k l hl
    have hja : ∀ x, a x ≠ some j := fun x hx => by
      obtain ⟨x', hx'⟩ := (ha4 j).mp ⟨x, hx⟩
      exact hfree x' hx'
    refine ⟨_, Step.augment st i (Function.update a l (some j)) hi hfail ?_ ?_ ?_⟩
    · intro x j' hx
      by_cases h : x = l
      · subst h; simp only [Function.update_self, Option.some.injEq] at hx; subst hx; exact htj
      · rw [Function.update_of_ne h] at hx; exact ha1 x j' hx
    · intro x x' j' hx hx'
      by_cases h : x = l <;> by_cases h' : x' = l
      · rw [h, h']
      · rw [h, Function.update_self, Option.some.injEq] at hx
        rw [Function.update_of_ne h'] at hx'
        subst hx; exact absurd hx' (hja x')
      · rw [h', Function.update_self, Option.some.injEq] at hx'
        rw [Function.update_of_ne h] at hx
        subst hx'; exact absurd hx (hja x)
      · rw [Function.update_of_ne h] at hx
        rw [Function.update_of_ne h'] at hx'
        exact ha2 _ _ _ hx hx'
    · intro x
      by_cases h : x = l
      · subst h
        simp only [Function.update_self, Option.isSome_some, true_iff]
        exact (S.reachWithin_dom k x hl).symm
      · rw [Function.update_of_ne h, ha3 x]
        simp [h]

omit [DecidableEq ι] in
open Classical in
/-- The note's formulation of the failure branch ("add `dF_k/dt` for each equation on the path
and `dz_j/dt` for each variable in it") gives the same new highest derivatives: `d j` becomes the
larger of the old value and the orders `order l j + c l + 1` in the differentiated coloured
equations. -/
@[powerlib_foundation] theorem differentiate_d_eq_max {st : PantelidesState ι} {i : ι}
    (hv : S.Valid st) (j : ι) :
    (S.differentiate st i).d j = max (st.d j)
      ((univ.filter fun l => S.Reach st i l ∧ S.occurs l j = true).sup
        fun l => S.order l j + st.c l + 1) := by
  have hle : ∀ l ∈ univ.filter (fun l => S.Reach st i l ∧ S.occurs l j = true),
      S.order l j + st.c l + 1 ≤ st.d j + 1 := fun l hl => by
    have := hv.1 l j (by simp at hl; exact hl.2)
    omega
  simp only [differentiate]
  by_cases hJ : ∃ l, S.Reach st i l ∧ S.Tight st.c st.d l j
  · obtain ⟨l, hl, htj⟩ := hJ
    have hsup : (univ.filter fun l => S.Reach st i l ∧ S.occurs l j = true).sup
        (fun l => S.order l j + st.c l + 1) = st.d j + 1 := by
      refine le_antisymm (Finset.sup_le hle) ?_
      have := Finset.le_sup (f := fun l => S.order l j + st.c l + 1)
        (s := univ.filter fun l => S.Reach st i l ∧ S.occurs l j = true)
        (by simp [hl, htj.1] : l ∈ _)
      have h2 := htj.2
      omega
    have hJ : ∃ l, S.Reach st i l ∧ S.Tight st.c st.d l j := ⟨l, hl, htj⟩
    simp only [hJ, ite_true, hsup]
    omega
  · simp only [hJ, ite_false, add_zero]
    refine (max_eq_left (Finset.sup_le fun l hl => ?_)).symm
    simp only [mem_filter, mem_univ, true_and] at hl
    have h1 := hv.1 l j hl.2
    have h2 : S.order l j + st.c l ≠ st.d j := fun h => hJ ⟨l, hl.1, hl.2, h⟩
    omega

/-! ## Termination -/

/-- Every run of the algorithm from a valid state has at most `potential σ` steps, for any
transversal `σ`. -/
@[powerlib_foundation] theorem run_length_le {σ : Equiv.Perm ι} (hσ : S.IsTransversal σ)
    (run : ℕ → PantelidesState ι) (n : ℕ) (hv : S.Valid (run 0))
    (hrun : ∀ k < n, S.Step (run k) (run (k + 1))) : n ≤ S.potential σ (run 0) := by
  have key : ∀ k ≤ n, S.Valid (run k) ∧ S.potential σ (run k) + k ≤ S.potential σ (run 0) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hv, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨hvk, hpk⟩ := ih (by omega)
      have hs := hrun k (by omega)
      exact ⟨hs.valid S hvk, by have := hs.potential_lt S hσ hvk; omega⟩
  have := (key n le_rfl).2
  omega

/-- No infinite run from a valid state when a transversal exists. -/
@[powerlib_foundation] theorem not_infinite_run {σ : Equiv.Perm ι} (hσ : S.IsTransversal σ)
    (run : ℕ → PantelidesState ι) (hv : S.Valid (run 0)) :
    ¬ ∀ k, S.Step (run k) (run (k + 1)) := fun h => by
  have := S.run_length_le hσ run (S.potential σ (run 0) + 1) hv fun k _ => h k
  omega

omit [DecidableEq ι] in
/-- A terminal valid state is a perfect matching of the highest-derivative graph: it defines a
transversal `σ` on which the final offsets are dual feasible and tight (Pryce's conditions). -/
@[powerlib_foundation] theorem exists_perm_of_isFinal {st : PantelidesState ι} (hv : S.Valid st)
    (hfin : st.IsFinal) : ∃ σ : Equiv.Perm ι, (∀ i, st.assign i = some (σ i)) ∧
      S.IsTransversal σ ∧ S.IsDualFeasible st.c st.d ∧ S.IsTight σ st.c st.d := by
  set f : ι → ι := fun i => (st.assign i).get (hfin i)
  have hf : ∀ i, st.assign i = some (f i) := fun i => by simp [f]
  have hinj : Function.Injective f := fun i i' h =>
    hv.2.2 i i' (f i) (hf i) (by rw [h]; exact hf i')
  set σ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, hf, fun i => (hv.2.1 i (f i) (hf i)).1, hv.1, fun i => (hv.2.1 i (f i) (hf i)).2⟩

/-- From a valid state, when a transversal exists, some run reaches a terminal valid state. -/
@[powerlib_foundation] theorem exists_final_of_valid {σ : Equiv.Perm ι}
    (hσ : S.IsTransversal σ) : ∀ (m : ℕ) (st : PantelidesState ι), S.Valid st →
      S.potential σ st ≤ m → ∃ st', Relation.ReflTransGen S.Step st st' ∧ st'.IsFinal ∧
        S.Valid st' := by
  intro m
  induction m with
  | zero =>
    intro st hv hp
    refine ⟨st, Relation.ReflTransGen.refl, fun i => ?_, hv⟩
    by_contra hi
    obtain ⟨st', hs⟩ := S.exists_step hv (Option.not_isSome_iff_eq_none.mp hi)
    have := hs.potential_lt S hσ hv
    omega
  | succ m ih =>
    intro st hv hp
    by_cases hfin : st.IsFinal
    · exact ⟨st, Relation.ReflTransGen.refl, hfin, hv⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hfin
      obtain ⟨st', hs⟩ := S.exists_step hv (Option.not_isSome_iff_eq_none.mp hi)
      have hlt := hs.potential_lt S hσ hv
      obtain ⟨st'', hr, hf, hv''⟩ := ih st' (hs.valid S hv) (by omega)
      exact ⟨st'', Relation.ReflTransGen.head hs hr, hf, hv''⟩

omit [DecidableEq ι] in
/-- The measure of the initial state is at most `|ι| + Σ_j d⁰_j`. -/
@[powerlib_foundation] theorem potential_initial_le (σ : Equiv.Perm ι) :
    S.potential σ S.initial ≤ Fintype.card ι + ∑ j, S.initial.d j := by
  have h : S.initial.unassigned ≤ Fintype.card ι := card_le_univ _
  unfold potential
  omega

/-- **Termination of Pantelides' algorithm.** If the DAE is structurally nonsingular (its
occurrence pattern has a transversal), then every run from the initial state stops after at most
`|ι| + Σ_j d⁰_j` steps (`d⁰_j` = highest derivative order of `x_j` in the original system), and
some run reaches a terminal state: every equation is assigned to the highest derivative of a
distinct variable, and the final offsets `(c, d)` are dual feasible and tight on that
assignment (so it is a highest-value transversal, with `Σ d - Σ c` equal to its value). -/
@[powerlib_foundation] theorem pantelides_terminates (h : ∃ σ : Equiv.Perm ι, S.IsTransversal σ) :
    (∀ (run : ℕ → PantelidesState ι) (n : ℕ), run 0 = S.initial →
        (∀ k < n, S.Step (run k) (run (k + 1))) → n ≤ Fintype.card ι + ∑ j, S.initial.d j) ∧
      ∃ st, Relation.ReflTransGen S.Step S.initial st ∧ st.IsFinal ∧
        ∃ σ : Equiv.Perm ι, (∀ i, st.assign i = some (σ i)) ∧ S.IsTransversal σ ∧
          S.IsDualFeasible st.c st.d ∧ S.IsTight σ st.c st.d ∧
          (∀ τ, S.IsTransversal τ → S.value τ ≤ S.value σ) ∧
          S.value σ + ∑ i, st.c i = ∑ j, st.d j := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun run n h0 hrun => ?_, ?_⟩
  · have := S.run_length_le hσ run n (h0 ▸ S.initial_valid) hrun
    rw [h0] at this
    exact this.trans (S.potential_initial_le σ)
  · obtain ⟨st, hr, hfin, hv⟩ := S.exists_final_of_valid hσ _ S.initial S.initial_valid le_rfl
    obtain ⟨τ, hτ, htr, hdf, ht⟩ := S.exists_perm_of_isFinal hv hfin
    exact ⟨st, hr, hfin, τ, hτ, htr, hdf, ht, fun τ' hτ' => S.value_le_of_tight hτ' hdf ht,
      S.value_add_eq ht⟩

omit [DecidableEq ι] in
/-- Every state reachable from the initial state satisfies the invariant. -/
@[powerlib_foundation] theorem valid_of_reaches {st : PantelidesState ι}
    (hr : Relation.ReflTransGen S.Step S.initial st) : S.Valid st := by
  induction hr with
  | refl => exact S.initial_valid
  | tail _ hs ih => exact hs.valid S ih

omit [DecidableEq ι] in
/-- Conversely, a run that reaches a terminal state exhibits a transversal. -/
@[powerlib_foundation] theorem exists_transversal_of_reaches_final {st : PantelidesState ι}
    (hr : Relation.ReflTransGen S.Step S.initial st) (hfin : st.IsFinal) :
    ∃ σ : Equiv.Perm ι, S.IsTransversal σ := by
  have hv : S.Valid st := S.valid_of_reaches hr
  obtain ⟨σ, -, hσ, -⟩ := S.exists_perm_of_isFinal hv hfin
  exact ⟨σ, hσ⟩

/-- Structurally singular DAE: the algorithm never stops — there is an infinite run from the
initial state (no state is terminal, and every valid non-terminal state has a step). -/
@[powerlib_foundation] theorem exists_infinite_run (h : ¬ ∃ σ : Equiv.Perm ι, S.IsTransversal σ) :
    ∃ run : ℕ → PantelidesState ι, run 0 = S.initial ∧ ∀ k, S.Step (run k) (run (k + 1)) := by
  have hnext : ∀ st : {st : PantelidesState ι // S.Valid st}, ∃ st', S.Step st.1 st' := by
    rintro ⟨st, hv⟩
    by_cases hfin : st.IsFinal
    · obtain ⟨σ, -, hσ, -⟩ := S.exists_perm_of_isFinal hv hfin
      exact absurd ⟨σ, hσ⟩ h
    · obtain ⟨i, hi⟩ := not_forall.mp hfin
      exact S.exists_step hv (Option.not_isSome_iff_eq_none.mp hi)
  let next : {st : PantelidesState ι // S.Valid st} → {st : PantelidesState ι // S.Valid st} :=
    fun st => ⟨Classical.choose (hnext st), (Classical.choose_spec (hnext st)).valid S st.2⟩
  refine ⟨fun k => (next^[k] ⟨S.initial, S.initial_valid⟩).1, rfl, fun k => ?_⟩
  simp only [Function.iterate_succ_apply']
  exact Classical.choose_spec (hnext _)

/-- Pantelides' algorithm terminates on every run iff the DAE is structurally nonsingular
(some real matrix with its occurrence pattern is nonsingular). -/
@[powerlib_foundation] theorem pantelides_terminates_iff :
    (¬ ∃ run : ℕ → PantelidesState ι, run 0 = S.initial ∧ ∀ k, S.Step (run k) (run (k + 1))) ↔
      S.StructurallyNonsingular := by
  rw [S.structurallyNonsingular_iff]
  constructor
  · intro h
    by_contra hs
    exact h (S.exists_infinite_run hs)
  · rintro ⟨σ, hσ⟩ ⟨run, h0, hrun⟩
    exact S.not_infinite_run hσ run (h0 ▸ S.initial_valid) hrun

omit [DecidableEq ι] in
/-- Pantelides' counts dominate Pryce's offsets: at a reachable state assigning each equation `i`
to `σ i`, Pryce's fixed-point iteration on `σ` (`theorem.DAE.Pryce`) stops at offsets
componentwise below the differentiation counts `c` and highest derivative orders `d` produced by
Pantelides' algorithm. -/
@[powerlib_foundation] theorem pryce_le_pantelides {st : PantelidesState ι}
    (hr : Relation.ReflTransGen S.Step S.initial st) {σ : Equiv.Perm ι}
    (hσ : ∀ i, st.assign i = some (σ i)) :
    ∃ N, S.pryceStep σ (S.pryceIter σ N) = S.pryceIter σ N ∧
      S.IsDualFeasible (S.pryceIter σ N).1 (S.pryceIter σ N).2 ∧
      S.IsTight σ (S.pryceIter σ N).1 (S.pryceIter σ N).2 ∧ S.pryceIter σ N ≤ (st.c, st.d) := by
  have hv := S.valid_of_reaches hr
  have htr : S.IsTransversal σ := fun i => (hv.2.1 i (σ i) (hσ i)).1
  have ht : S.IsTight σ st.c st.d := fun i => (hv.2.1 i (σ i) (hσ i)).2
  obtain ⟨N, -, hfix, hdf, htt, hmin⟩ := S.pryce_iteration_terminates htr hv.1 ht
  exact ⟨N, hfix, hdf, htt, hmin st.c st.d hv.1 ht⟩

/-! ## Equality with Pryce's offsets (all runs) -/

omit [DecidableEq ι] in
/-- Complementary slackness for the assignment LP: dual-feasible offsets whose dual objective
`Σ d - Σ c` equals the value of a transversal `τ` are tight on `τ`. -/
@[powerlib_foundation] theorem isTight_of_value_add_eq {τ : Equiv.Perm ι} {c d : ι → ℕ}
    (hτ : S.IsTransversal τ) (hf : S.IsDualFeasible c d) (h : S.value τ + ∑ i, c i = ∑ j, d j) :
    S.IsTight τ c d := by
  intro i
  have hle : ∀ i ∈ (univ : Finset ι), S.order i (τ i) + c i ≤ d (τ i) :=
    fun i _ => hf i (τ i) (hτ i)
  have hsum : ∑ i, (S.order i (τ i) + c i) = ∑ i, d (τ i) := by
    rw [sum_add_distrib, Equiv.sum_comp τ d]; exact h
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum i (mem_univ i)

/-- Key step of the equality: a failed search keeps Pantelides' counts below every optimal dual
solution. Let `(c, d)` be dual feasible and tight on a transversal `τ`, with
`(st.c, st.d) ≤ (c, d)`. Then every coloured equation has `st.c l < c l` (and hence every
coloured variable `st.d j < d j`), so the differentiated state is still below `(c, d)`.
Proof: let `R₀` (`J₀`) be the coloured equations (variables) where the bound is attained. `τ`
maps `R₀` injectively into `J₀` (an attained tight `τ`-edge is a current highest-derivative edge),
and the assignment maps `R₀ \ {i}` onto `J₀` (an attained variable is assigned to an attained
equation). Counting gives `i ∉ R₀` and `assign(R₀) = J₀`; then `R₀` is empty, because the
complement of `R₀` among the coloured equations contains the root and is closed under the
alternating search (a strict bound at `l` is strict at every highest-derivative neighbour of
`l`, which is not in `J₀`, so its assigned equation is not in `R₀`). -/
@[powerlib_foundation] theorem differentiate_le {st : PantelidesState ι} {i : ι}
    (hv : S.Valid st) (hi : st.assign i = none) (hfail : S.SearchFails st i)
    {τ : Equiv.Perm ι} (hτ : S.IsTransversal τ) {c d : ι → ℕ} (hf : S.IsDualFeasible c d)
    (ht : S.IsTight τ c d) (hle : (st.c, st.d) ≤ (c, d)) :
    ((S.differentiate st i).c, (S.differentiate st i).d) ≤ (c, d) := by
  classical
  obtain ⟨hfst, htight, -⟩ := hv
  have hcle : ∀ l, st.c l ≤ c l := hle.1
  have hdle : ∀ j, st.d j ≤ d j := hle.2
  set R0 := univ.filter fun l => S.Reach st i l ∧ c l = st.c l with hR0
  set J0 := univ.filter fun j => (∃ l, S.Reach st i l ∧ S.Tight st.c st.d l j) ∧ d j = st.d j
    with hJ0
  set g : ι → ι := fun x => (st.assign x).getD i with hg
  have hτR : ∀ l ∈ R0, τ l ∈ J0 := by
    intro l hl
    simp only [R0, mem_filter, mem_univ, true_and] at hl
    obtain ⟨hlr, hlc⟩ := hl
    have h1 := ht l
    have h2 := hfst l (τ l) (hτ l)
    have h3 := hdle (τ l)
    have heq : S.order l (τ l) + st.c l = st.d (τ l) := by omega
    simp only [J0, mem_filter, mem_univ, true_and]
    exact ⟨⟨l, hlr, hτ l, heq⟩, by omega⟩
  have hJR : ∀ j ∈ J0, ∃ x ∈ R0.erase i, g x = j := by
    intro j hj
    simp only [J0, mem_filter, mem_univ, true_and] at hj
    obtain ⟨⟨l, hl, htj⟩, hdj⟩ := hj
    obtain ⟨x, hx⟩ := hfail l j hl htj
    have hxr := S.reach_of_assign hl htj hx
    obtain ⟨hocc, heq⟩ := htight x j hx
    have h1 := hf x j hocc
    have h2 := hcle x
    refine ⟨x, ?_, by simp [g, hx]⟩
    simp only [R0, mem_erase, mem_filter, mem_univ, true_and]
    refine ⟨fun hxi => (by rw [hxi, hi] at hx; cases hx), hxr, by omega⟩
  have hc1 : R0.card ≤ J0.card :=
    card_le_card_of_injOn τ (fun l hl => hτR l hl) τ.injective.injOn
  have hsub : J0 ⊆ (R0.erase i).image g := fun j hj => by
    obtain ⟨x, hx, hgx⟩ := hJR j hj
    exact mem_image.mpr ⟨x, hx, hgx⟩
  have hc2 := card_le_card hsub
  have hc3 : ((R0.erase i).image g).card ≤ (R0.erase i).card := card_image_le
  have hiR : i ∉ R0 := fun hiR => by
    have := card_erase_of_mem hiR
    have := card_pos.mpr ⟨i, hiR⟩
    omega
  have hc4 : (R0.erase i).card ≤ R0.card := card_erase_le
  have hJeq : J0 = (R0.erase i).image g := eq_of_subset_of_card_le hsub (by omega)
  have hRJ : ∀ x ∈ R0, g x ∈ J0 := fun x hx => by
    rw [hJeq]
    exact mem_image_of_mem g (mem_erase.mpr ⟨fun h => hiR (h ▸ hx), hx⟩)
  have hlt : ∀ k l, S.reachWithin st i k l → st.c l < c l := by
    intro k
    induction k with
    | zero =>
      intro l hl
      have hl' : l = i := hl
      subst hl'
      by_contra hcx
      exact hiR (by
        simp only [R0, mem_filter, mem_univ, true_and]
        exact ⟨S.reach_self st l, by have := hcle l; omega⟩)
    | succ k ih =>
      rintro x (hx | ⟨l, j, hl, htj, hxj⟩)
      · exact ih x hx
      · have hcl := ih l hl
        by_contra hcx
        have hxR0 : x ∈ R0 := by
          simp only [R0, mem_filter, mem_univ, true_and]
          exact ⟨S.reach_of_assign ⟨k, hl⟩ htj hxj, by have := hcle x; omega⟩
        have hgx := hRJ x hxR0
        simp only [g, hxj, Option.getD_some, J0, mem_filter, mem_univ, true_and] at hgx
        have h1 := hf l j htj.1
        have h2 := htj.2
        omega
  refine ⟨fun l => ?_, fun j => ?_⟩
  · simp only [differentiate]
    split_ifs with h
    · obtain ⟨k, hk⟩ := h
      have := hlt k l hk
      omega
    · simpa using hcle l
  · simp only [differentiate]
    split_ifs with h
    · obtain ⟨l, ⟨k, hk⟩, htj⟩ := h
      have h0 := hlt k l hk
      have h1 := hf l j htj.1
      have h2 := htj.2
      omega
    · simpa using hdle j


/-- Every step keeps the counts below a dual-feasible `(c, d)` tight on a transversal (an
augmentation does not change the counts; a differentiation is `differentiate_le`). -/
@[powerlib_foundation] theorem Step.le_of_le {st st' : PantelidesState ι} (hv : S.Valid st)
    (h : S.Step st st') {τ : Equiv.Perm ι} (hτ : S.IsTransversal τ) {c d : ι → ℕ}
    (hf : S.IsDualFeasible c d) (ht : S.IsTight τ c d) (hle : (st.c, st.d) ≤ (c, d)) :
    (st'.c, st'.d) ≤ (c, d) := by
  cases h with
  | augment i a _ _ _ _ _ => exact hle
  | differentiate i hi hfail => exact S.differentiate_le hv hi hfail hτ hf ht hle

omit [DecidableEq ι] in
/-- The initial counts are below every dual-feasible pair of offsets. -/
@[powerlib_foundation] theorem initial_le {c d : ι → ℕ} (hf : S.IsDualFeasible c d) :
    (S.initial.c, S.initial.d) ≤ (c, d) := by
  refine ⟨fun l => Nat.zero_le _, fun j => Finset.sup_le fun l hl => ?_⟩
  have := hf l j (by simpa using hl)
  change S.order l j ≤ d j
  omega

/-- **Pantelides' counts are below every optimal dual solution**: at every state reachable from
the initial state (along any run), `(c, d)` is componentwise at most every pair of offsets that
is dual feasible and tight on some transversal (equivalently, by complementary slackness, every
optimal solution of the dual of the assignment problem). -/
@[powerlib_foundation] theorem le_of_reaches {st : PantelidesState ι}
    (hr : Relation.ReflTransGen S.Step S.initial st) {τ : Equiv.Perm ι} (hτ : S.IsTransversal τ)
    {c d : ι → ℕ} (hf : S.IsDualFeasible c d) (ht : S.IsTight τ c d) :
    (st.c, st.d) ≤ (c, d) := by
  induction hr with
  | refl => exact S.initial_le hf
  | tail hr' hs ih => exact hs.le_of_le S (S.valid_of_reaches hr') hτ hf ht ih

/-- **Pryce's offsets equal Pantelides' counts** (T-pantelides-index-reduction §1.5), for every
run: at a reachable state assigning each equation `i` to `σ i` (in particular at the terminal
state of any run), Pryce's fixed-point iteration on `σ` stops exactly at the differentiation
counts `c` and highest derivative orders `d` produced by Pantelides' algorithm. The `≤` half is
`pryce_le_pantelides`; the `≥` half is `le_of_reaches` applied to Pryce's offsets. -/
@[powerlib_foundation] theorem pryce_eq_pantelides {st : PantelidesState ι}
    (hr : Relation.ReflTransGen S.Step S.initial st) {σ : Equiv.Perm ι}
    (hσ : ∀ i, st.assign i = some (σ i)) :
    ∃ N, S.pryceStep σ (S.pryceIter σ N) = S.pryceIter σ N ∧
      S.IsDualFeasible (S.pryceIter σ N).1 (S.pryceIter σ N).2 ∧
      S.IsTight σ (S.pryceIter σ N).1 (S.pryceIter σ N).2 ∧ S.pryceIter σ N = (st.c, st.d) := by
  have hv := S.valid_of_reaches hr
  have htr : S.IsTransversal σ := fun i => (hv.2.1 i (σ i) (hσ i)).1
  obtain ⟨N, hfix, hdf, htt, hle⟩ := S.pryce_le_pantelides hr hσ
  exact ⟨N, hfix, hdf, htt, le_antisymm hle (S.le_of_reaches hr htr hdf htt)⟩

/-- Pryce's offsets computed on **any** highest-value transversal `τ` (not necessarily the
assignment found by the run) equal the counts at the terminal state of any run. -/
@[powerlib_foundation] theorem pryce_eq_pantelides_of_highestValue {st : PantelidesState ι}
    (hr : Relation.ReflTransGen S.Step S.initial st) (hfin : st.IsFinal) {τ : Equiv.Perm ι}
    (hτ : S.IsTransversal τ) (hmax : ∀ τ', S.IsTransversal τ' → S.value τ' ≤ S.value τ) :
    ∃ N, S.pryceStep τ (S.pryceIter τ N) = S.pryceIter τ N ∧
      S.IsDualFeasible (S.pryceIter τ N).1 (S.pryceIter τ N).2 ∧
      S.IsTight τ (S.pryceIter τ N).1 (S.pryceIter τ N).2 ∧ S.pryceIter τ N = (st.c, st.d) := by
  have hv := S.valid_of_reaches hr
  obtain ⟨σ, -, hσ, hdf, ht⟩ := S.exists_perm_of_isFinal hv hfin
  have h1 := S.value_add_eq ht
  have h2 := S.value_add_le hτ hdf
  have h3 := hmax σ hσ
  have htτ : S.IsTight τ st.c st.d := S.isTight_of_value_add_eq hτ hdf (by omega)
  obtain ⟨N, -, hfix, hdf', htt', hmin⟩ := S.pryce_iteration_terminates hτ hdf htτ
  exact ⟨N, hfix, hdf', htt', le_antisymm (hmin _ _ hdf htτ) (S.le_of_reaches hr hτ hdf' htt')⟩

/-- **The counts do not depend on the run.** The step relation is nondeterministic (the
processed equation and the augmenting matching are arbitrary), and different runs may end with
different assignments, but any two terminal states reachable from the initial state have the
same differentiation counts `c` and the same highest derivative orders `d`. -/
@[powerlib_foundation] theorem pantelides_offsets_unique {st st' : PantelidesState ι}
    (hr : Relation.ReflTransGen S.Step S.initial st) (hfin : st.IsFinal)
    (hr' : Relation.ReflTransGen S.Step S.initial st') (hfin' : st'.IsFinal) :
    st.c = st'.c ∧ st.d = st'.d := by
  obtain ⟨σ, -, hσ, hdf, ht⟩ := S.exists_perm_of_isFinal (S.valid_of_reaches hr) hfin
  obtain ⟨σ', -, hσ', hdf', ht'⟩ := S.exists_perm_of_isFinal (S.valid_of_reaches hr') hfin'
  have h1 := S.le_of_reaches hr hσ' hdf' ht'
  have h2 := S.le_of_reaches hr' hσ hdf ht
  have h := le_antisymm h1 h2
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Computing Pantelides' counts from least offsets: if `(c, d)` is dual feasible, tight on a
transversal `τ`, and componentwise least among such offsets, then every run that terminates
ends with counts exactly `(c, d)`. -/
@[powerlib_foundation] theorem pantelides_eq_of_least {st : PantelidesState ι}
    (hr : Relation.ReflTransGen S.Step S.initial st) (hfin : st.IsFinal) {τ : Equiv.Perm ι}
    (hτ : S.IsTransversal τ) {c d : ι → ℕ} (hf : S.IsDualFeasible c d) (ht : S.IsTight τ c d)
    (hleast : ∀ c' d', S.IsDualFeasible c' d' → S.IsTight τ c' d' → c ≤ c' ∧ d ≤ d') :
    st.c = c ∧ st.d = d := by
  obtain ⟨N, -, -, htN, hN⟩ := S.pryce_eq_pantelides_of_highestValue hr hfin hτ
    (fun τ' hτ' => S.value_le_of_tight hτ' hf ht)
  have hle := S.le_of_reaches hr hτ hf ht
  have hge := hleast (S.pryceIter τ N).1 (S.pryceIter τ N).2
    (by have := S.valid_of_reaches hr; rw [hN]; exact this.1) htN
  rw [hN] at hge
  exact ⟨le_antisymm hle.1 hge.1, le_antisymm hle.2 hge.2⟩

end Signature

/-! ## Examples -/

/-- Pantelides' algorithm terminates on the pendulum (index-3 example of `theorem.DAE.Pryce`). -/
@[powerlib_foundation] theorem pendulum_pantelides_terminates :
    ¬ ∃ run : ℕ → PantelidesState (Fin 5), run 0 = pendulumSig.initial ∧
      ∀ k, pendulumSig.Step (run k) (run (k + 1)) :=
  pendulumSig.pantelides_terminates_iff.mpr
    (pendulumSig.structurallyNonsingular_iff.mpr ⟨pendulumσ, pendulum_offsets.1⟩)

/-- Pantelides' algorithm terminates on the index-formula counterexample of `theorem.DAE.Pryce`. -/
@[powerlib_foundation] theorem example_pantelides_terminates :
    ¬ ∃ run : ℕ → PantelidesState (Fin 3), run 0 = exampleSig.initial ∧
      ∀ k, exampleSig.Step (run k) (run (k + 1)) :=
  exampleSig.pantelides_terminates_iff.mpr
    (exampleSig.structurallyNonsingular_iff.mpr ⟨exampleσ, example_offsets.1⟩)

/-- On the pendulum, `c = (1,1,0,0,2)`, `d = (2,2,1,1,0)` are the least offsets that are dual
feasible and tight on `pendulumσ`. -/
@[powerlib_foundation] theorem pendulum_offsets_least (c d : Fin 5 → ℕ)
    (hf : pendulumSig.IsDualFeasible c d) (ht : pendulumSig.IsTight pendulumσ c d) :
    pendulumC ≤ c ∧ pendulumD ≤ d := by
  have f01 := hf 0 2 rfl
  have f12 := hf 1 1 rfl
  have f24 := hf 2 4 rfl
  have f40 := hf 4 0 rfl
  have f41 := hf 4 1 rfl
  have f31 := hf 3 3 rfl
  have t0 := ht 0
  have t1 := ht 1
  have t2 := ht 2
  have t3 := ht 3
  have t4 := ht 4
  simp [pendulumSig, pendulumσ] at f01 f12 f24 f40 f41 f31 t0 t1 t2 t3 t4
  refine ⟨fun i => ?_, fun j => ?_⟩
  · fin_cases i <;> simp [pendulumC] <;> omega
  · fin_cases j <;> simp [pendulumD] <;> omega

/-- Every terminating run of Pantelides' algorithm on the pendulum differentiates the position
equations `ṗ₁ = v₁`, `ṗ₂ = v₂` once and the constraint `p₁² + p₂² = L²` twice
(`c = (1,1,0,0,2)`), and ends with highest derivatives `d = (2,2,1,1,0)` — Pryce's offsets
(`pendulum_offsets`). -/
@[powerlib_foundation] theorem pendulum_pantelides_counts {st : PantelidesState (Fin 5)}
    (hr : Relation.ReflTransGen pendulumSig.Step pendulumSig.initial st) (hfin : st.IsFinal) :
    st.c = pendulumC ∧ st.d = pendulumD :=
  pendulumSig.pantelides_eq_of_least hr hfin pendulum_offsets.1 pendulum_offsets.2.1
    pendulum_offsets.2.2.1 pendulum_offsets_least

/-- On the index-formula counterexample, every reachable state has the counts `c = 0`,
`d = (1,1,0)` (Pryce's offsets): Pantelides' algorithm never differentiates. -/
@[powerlib_foundation] theorem example_pantelides_counts {st : PantelidesState (Fin 3)}
    (hr : Relation.ReflTransGen exampleSig.Step exampleSig.initial st) :
    st.c = exampleC ∧ st.d = exampleD := by
  have hle := exampleSig.le_of_reaches hr example_offsets.1 example_offsets.2.1
    example_offsets.2.2
  have hge := example_offsets_least st.c st.d (exampleSig.valid_of_reaches hr).1
  exact ⟨le_antisymm hle.1 hge.1, le_antisymm hle.2 hge.2⟩

/-- A structurally singular pattern: two equations in `x₁` only (`x₂` occurs nowhere). -/
def singularSig : Signature (Fin 2) where
  occurs := fun _ j => decide (j = 0)
  order := fun _ _ => 0

/-- On the structurally singular pattern the algorithm runs forever. -/
@[powerlib_foundation] theorem singular_pantelides_nonterminating :
    ∃ run : ℕ → PantelidesState (Fin 2), run 0 = singularSig.initial ∧
      ∀ k, singularSig.Step (run k) (run (k + 1)) := by
  refine singularSig.exists_infinite_run ?_
  rintro ⟨σ, hσ⟩
  have h0 := hσ 0
  have h1 := hσ 1
  simp only [singularSig, decide_eq_true_eq] at h0 h1
  exact absurd (σ.injective (h0.trans h1.symm)) (by decide)

end powerlib.DAE
