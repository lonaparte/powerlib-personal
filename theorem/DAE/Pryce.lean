import theorem.Linear.Transfer
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # Structural index analysis: Pryce signature method, transversals, Hall's theorem

Foundation layer (category B).

A *signature* of a square DAE with equations and variables both indexed by `ι` records
`occurs i j` (variable `j` appears in equation `i`) and `order i j : ℕ` (highest derivative
order of `j` in `i`; meaningful where `occurs i j`). Offsets `c d : ι → ℕ` are *dual feasible*
if `order i j + c i ≤ d j` wherever `occurs i j`, and *tight* on a transversal `σ` if
`order i (σ i) + c i = d (σ i)`.

Results.
* Weak duality: for every transversal `σ` and dual-feasible `(c, d)`,
  `value σ + Σ c ≤ Σ d` (`value σ = Σᵢ order i (σ i)`); tightness gives equality
  `Σ d - Σ c = value σ` (the "HVT-tight" identity), and then `σ` is a highest-value
  transversal.
* Structural nonsingularity: some real matrix with the sparsity pattern of `occurs` is
  nonsingular iff a perfect matching (transversal) exists; and (Hall, wrapper of
  `Finset.all_card_le_biUnion_card_iff_exists_injective`) a transversal exists iff every set
  of `k` equations involves at least `k` variables.
* Pryce fixed-point iteration (`pryceStep`: `d_j ← max_{i ∋ j} (c_i + order i j)`,
  `c_i ← d_{σ i} - order i (σ i)` truncated at `0`, started at `0`): if some dual-feasible
  offsets tight on `σ` exist, the iteration reaches a fixed point after at most
  `Σ c* + Σ d*` steps; the fixed point is dual feasible, tight on `σ`, and componentwise
  below every such solution (the least offsets).
* Correction (index formula, T-pantelides-index-reduction §1.5): the note's rule
  `ν_S = max c + 1{∃ i: max_j Σ_ij = 0}` is wrong; Pryce's indicator is "some variable
  offset `d_j = 0`". Counterexample `ẋ₁ = y, ẋ₂ = x₁ - y, ẋ₁ + 2ẋ₂ = 0`: offsets
  `c = 0, d = (1, 1, 0)`; the note's formula gives `0`, the corrected one gives `1`, and the
  DAE indeed has differentiation index `1`: every solution satisfies the hidden constraint
  `y = 2 x₁` (so an initial point is inconsistent — index ≠ 0) and one differentiation gives
  the explicit ODE `ẏ = 2 y`. A solution of the example is a triple `x₁ x₂ y : ℝ → ℝ` with
  `∀ t, HasDerivAt x₁ (y t) t ∧ HasDerivAt x₂ (x₁ t - y t) t ∧ deriv x₁ t + 2 * deriv x₂ t = 0`,
  written out in each statement. For the pendulum both formulas give `3`.
* Correction (§1.9 Case A): adding `ω₁ = ω₂` to two independent swing equations makes the
  system overdetermined (three equations, two unknowns), not "index raised": solutions exist
  only under a compatibility condition on the data, and e.g. distinct constant
  accelerations admit no solution at all.

Model boundary: structural (sparsity/order pattern) analysis and two concrete DAEs; no claim
about numerical rank (structural regularity is an assumption of the method, not proved), and
no formalization of the Pantelides algorithm itself, Weierstrass/Kronecker forms or of
`ν_d = ν_S` in general.

Source: work-sync theory/T-pantelides-index-reduction.md §1.3 (bipartite matching),
§1.5 (signature matrix, offsets, fixed-point iteration, index formula, HVT-tight identity,
pendulum example), §1.9 Case A.
-/

noncomputable section
namespace powerlib.DAE
open Finset

variable {ι : Type*} [Fintype ι]

/-- Signature of a square DAE: occurrence pattern and highest derivative orders. -/
structure Signature (ι : Type*) where
  occurs : ι → ι → Bool
  order : ι → ι → ℕ

namespace Signature

variable (S : Signature ι)

def IsTransversal (σ : Equiv.Perm ι) : Prop := ∀ i, S.occurs i (σ i) = true

def value (σ : Equiv.Perm ι) : ℕ := ∑ i, S.order i (σ i)

def IsDualFeasible (c d : ι → ℕ) : Prop :=
  ∀ i j, S.occurs i j = true → S.order i j + c i ≤ d j

def IsTight (σ : Equiv.Perm ι) (c d : ι → ℕ) : Prop := ∀ i, S.order i (σ i) + c i = d (σ i)

/-! ## Weak duality and the HVT-tight identity -/

@[powerlib_foundation] theorem value_add_le {σ : Equiv.Perm ι} {c d : ι → ℕ}
    (hσ : S.IsTransversal σ) (h : S.IsDualFeasible c d) :
    S.value σ + ∑ i, c i ≤ ∑ j, d j := by
  rw [value, ← sum_add_distrib, ← Equiv.sum_comp σ d]
  exact sum_le_sum fun i _ => h i (σ i) (hσ i)

@[powerlib_foundation] theorem value_add_eq {σ : Equiv.Perm ι} {c d : ι → ℕ}
    (ht : S.IsTight σ c d) : S.value σ + ∑ i, c i = ∑ j, d j := by
  rw [value, ← sum_add_distrib, ← Equiv.sum_comp σ d]
  exact sum_congr rfl fun i _ => ht i

/-- Tight dual-feasible offsets certify that `σ` is a highest-value transversal. -/
@[powerlib_foundation] theorem value_le_of_tight {σ τ : Equiv.Perm ι} {c d : ι → ℕ}
    (hτ : S.IsTransversal τ) (h : S.IsDualFeasible c d) (ht : S.IsTight σ c d) :
    S.value τ ≤ S.value σ := by
  have h1 := S.value_add_le hτ h
  have h2 := S.value_add_eq ht
  omega

/-! ## Structural nonsingularity, perfect matchings and Hall's condition -/

/-- Some real matrix with the occurrence pattern is nonsingular. -/
def StructurallyNonsingular [DecidableEq ι] : Prop :=
  ∃ M : Matrix ι ι ℝ, (∀ i j, S.occurs i j = false → M i j = 0) ∧ M.det ≠ 0

@[powerlib_foundation] theorem structurallyNonsingular_iff [DecidableEq ι] :
    S.StructurallyNonsingular ↔ ∃ σ : Equiv.Perm ι, S.IsTransversal σ := by
  constructor
  · rintro ⟨M, hM, hdet⟩
    rw [Matrix.det_apply] at hdet
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
    have hprod : ∏ i, M (σ i) i ≠ 0 := by
      intro h; apply hσ; rw [h, smul_zero]
    refine ⟨σ⁻¹, fun i => ?_⟩
    by_contra hocc
    apply hprod
    apply Finset.prod_eq_zero (Finset.mem_univ (σ⁻¹ i))
    apply hM
    simpa using hocc
  · rintro ⟨σ, hσ⟩
    refine ⟨σ.permMatrix ℝ, fun i j hij => ?_, ?_⟩
    · rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      have hne : σ i ≠ j := by
        intro h
        have := hσ i
        rw [h, hij] at this
        exact Bool.false_ne_true this
      simp [hne]
    · rw [Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- Hall's marriage condition for the occurrence pattern. -/
@[powerlib_foundation] theorem exists_transversal_iff_hall [DecidableEq ι] :
    (∃ σ : Equiv.Perm ι, S.IsTransversal σ) ↔
      ∀ A : Finset ι, A.card ≤ (A.biUnion fun i => univ.filter fun j => S.occurs i j = true).card := by
  rw [Finset.all_card_le_biUnion_card_iff_exists_injective]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, σ.injective, fun i => by simpa using hσ i⟩
  · rintro ⟨f, hf, hmem⟩
    refine ⟨Equiv.ofBijective f hf.bijective_of_finite, fun i => ?_⟩
    simpa using hmem i

/-! ## Pryce's fixed-point iteration -/

/-- One sweep: `d_j ← max_{i : j ∈ i} (c_i + order i j)`, then `c_i ← d_{σ i} - order i (σ i)`
(truncated subtraction, i.e. `max 0`). -/
def pryceStep (σ : Equiv.Perm ι) (p : (ι → ℕ) × (ι → ℕ)) : (ι → ℕ) × (ι → ℕ) :=
  let d : ι → ℕ := fun j => (univ.filter fun i => S.occurs i j = true).sup fun i => p.1 i + S.order i j
  (fun i => d (σ i) - S.order i (σ i), d)

def pryceIter (σ : Equiv.Perm ι) (k : ℕ) : (ι → ℕ) × (ι → ℕ) := (S.pryceStep σ)^[k] (0, 0)

@[powerlib_foundation] theorem pryceStep_mono (σ : Equiv.Perm ι) {p q : (ι → ℕ) × (ι → ℕ)}
    (h : p ≤ q) : S.pryceStep σ p ≤ S.pryceStep σ q := by
  have hd : ∀ j, (univ.filter fun i => S.occurs i j = true).sup (fun i => p.1 i + S.order i j) ≤
      (univ.filter fun i => S.occurs i j = true).sup (fun i => q.1 i + S.order i j) := fun j =>
    Finset.sup_mono_fun fun i _ => Nat.add_le_add_right (h.1 i) _
  exact ⟨fun i => Nat.sub_le_sub_right (hd (σ i)) _, hd⟩

/-- Every dual-feasible tight solution is an upper bound preserved by the step. -/
@[powerlib_foundation] theorem pryceStep_le {σ : Equiv.Perm ι} {c d : ι → ℕ}
    (hf : S.IsDualFeasible c d) (ht : S.IsTight σ c d) {p : (ι → ℕ) × (ι → ℕ)}
    (hp : p ≤ (c, d)) : S.pryceStep σ p ≤ (c, d) := by
  have hd : ∀ j, (univ.filter fun i => S.occurs i j = true).sup (fun i => p.1 i + S.order i j) ≤
      d j := fun j => Finset.sup_le fun i hi => by
    have := hf i j (by simpa using hi)
    have := hp.1 i
    simp only at *
    omega
  refine ⟨fun i => ?_, hd⟩
  have h1 := hd (σ i)
  have h2 := ht i
  simp only [pryceStep]
  omega

@[powerlib_foundation] theorem pryceIter_le {σ : Equiv.Perm ι} {c d : ι → ℕ}
    (hf : S.IsDualFeasible c d) (ht : S.IsTight σ c d) (k : ℕ) : S.pryceIter σ k ≤ (c, d) := by
  induction k with
  | zero => exact ⟨fun i => Nat.zero_le _, fun j => Nat.zero_le _⟩
  | succ k ih =>
    rw [pryceIter, Function.iterate_succ_apply']
    exact S.pryceStep_le hf ht ih

@[powerlib_foundation] theorem pryceIter_mono_succ (σ : Equiv.Perm ι) (k : ℕ) :
    S.pryceIter σ k ≤ S.pryceIter σ (k + 1) := by
  induction k with
  | zero => exact ⟨fun i => Nat.zero_le _, fun j => Nat.zero_le _⟩
  | succ k ih =>
    rw [pryceIter, Function.iterate_succ_apply', pryceIter, Function.iterate_succ_apply' _ (k + 1)]
    exact S.pryceStep_mono σ ih

private def potential (p : (ι → ℕ) × (ι → ℕ)) : ℕ := ∑ i, p.1 i + ∑ j, p.2 j

@[powerlib_foundation] private lemma potential_lt {p q : (ι → ℕ) × (ι → ℕ)} (h : p ≤ q)
    (hne : p ≠ q) : potential p < potential q := by
  have h1 : ∑ i, p.1 i ≤ ∑ i, q.1 i := sum_le_sum fun i _ => h.1 i
  have h2 : ∑ j, p.2 j ≤ ∑ j, q.2 j := sum_le_sum fun j _ => h.2 j
  by_contra hle
  have e1 : ∑ i, p.1 i = ∑ i, q.1 i := by unfold potential at hle; omega
  have e2 : ∑ j, p.2 j = ∑ j, q.2 j := by unfold potential at hle; omega
  apply hne
  have f1 : p.1 = q.1 := funext fun i =>
    (Finset.sum_eq_sum_iff_of_le (fun i _ => h.1 i)).mp e1 i (mem_univ i)
  have f2 : p.2 = q.2 := funext fun j =>
    (Finset.sum_eq_sum_iff_of_le (fun j _ => h.2 j)).mp e2 j (mem_univ j)
  exact Prod.ext f1 f2

/-- Pryce's iteration terminates (within `Σ c* + Σ d*` sweeps) at the least dual-feasible
offsets that are tight on `σ`, provided some such offsets exist. -/
@[powerlib_foundation] theorem pryce_iteration_terminates {σ : Equiv.Perm ι}
    (hσ : S.IsTransversal σ) {c d : ι → ℕ} (hf : S.IsDualFeasible c d) (ht : S.IsTight σ c d) :
    ∃ N ≤ potential (c, d), S.pryceStep σ (S.pryceIter σ N) = S.pryceIter σ N ∧
      S.IsDualFeasible (S.pryceIter σ N).1 (S.pryceIter σ N).2 ∧
      S.IsTight σ (S.pryceIter σ N).1 (S.pryceIter σ N).2 ∧
      ∀ c' d', S.IsDualFeasible c' d' → S.IsTight σ c' d' → S.pryceIter σ N ≤ (c', d') := by
  -- termination by a bounded strictly increasing potential
  have hex : ∃ N ≤ potential (c, d), S.pryceIter σ (N + 1) = S.pryceIter σ N := by
    by_contra hno
    push Not at hno
    have hgrow : ∀ k ≤ potential (c, d) + 1, k ≤ potential (S.pryceIter σ k) := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have hlt := potential_lt (S.pryceIter_mono_succ σ k) (hno k (by omega)).symm
        have := ih (by omega)
        omega
    have hb := hgrow _ le_rfl
    have hle := S.pryceIter_le hf ht (potential (c, d) + 1)
    have : potential (S.pryceIter σ (potential (c, d) + 1)) ≤ potential (c, d) := by
      unfold potential
      exact Nat.add_le_add (sum_le_sum fun i _ => hle.1 i) (sum_le_sum fun j _ => hle.2 j)
    omega
  obtain ⟨N, hN, hfix⟩ := hex
  have hfix' : S.pryceStep σ (S.pryceIter σ N) = S.pryceIter σ N := by
    calc S.pryceStep σ (S.pryceIter σ N) = S.pryceIter σ (N + 1) := by
          simp only [pryceIter, Function.iterate_succ_apply']
      _ = S.pryceIter σ N := hfix
  have hmin : ∀ c' d', S.IsDualFeasible c' d' → S.IsTight σ c' d' →
      S.pryceIter σ N ≤ (c', d') := fun c' d' hf' ht' => S.pryceIter_le hf' ht' N
  refine ⟨N, hN, ?_⟩
  generalize S.pryceIter σ N = p at hfix' hmin ⊢
  have hd : ∀ j, p.2 j =
      (univ.filter fun i => S.occurs i j = true).sup fun i => p.1 i + S.order i j := by
    intro j
    exact (congrArg (fun q => q.2 j) hfix').symm
  have hc : ∀ i, p.1 i = p.2 (σ i) - S.order i (σ i) := by
    intro i
    have := congrArg (fun q => q.1 i) hfix'
    simp only [pryceStep] at this
    rw [← this, hd (σ i)]
  have hfeas : S.IsDualFeasible p.1 p.2 := by
    intro i j hij
    rw [hd j]
    exact Finset.le_sup (f := fun i => p.1 i + S.order i j) (by simpa using hij) |>.trans' (by
      simp [add_comm])
  refine ⟨hfix', hfeas, fun i => ?_, hmin⟩
  have h1 := hfeas i (σ i) (hσ i)
  have h2 := hc i
  omega

/-! ## Index formulas -/

/-- The note's formula: `max c + 1` if some equation has all its variables at order `0`. -/
def noteIndex (c : ι → ℕ) [Nonempty ι] : ℕ :=
  univ.sup' univ_nonempty c +
    if ∃ i, ∀ j, S.occurs i j = true → S.order i j = 0 then 1 else 0

/-- Pryce's formula: `max c + 1` if some variable offset vanishes. -/
def pryceIndex (_S : Signature ι) (c d : ι → ℕ) [Nonempty ι] : ℕ :=
  univ.sup' univ_nonempty c + if ∃ j, d j = 0 then 1 else 0

end Signature

/-! ## Counterexample `ẋ₁ = y, ẋ₂ = x₁ - y, ẋ₁ + 2ẋ₂ = 0` (variables `x₁, x₂, y`) -/

/-- Signature of the counterexample; rows = equations, columns = `(x₁, x₂, y)`. -/
def exampleSig : Signature (Fin 3) where
  occurs := fun i j => (![![true, false, true], ![true, true, true], ![true, true, false]] i) j
  order := fun i j => (![![1, 0, 0], ![0, 1, 0], ![1, 1, 0]] i) j

def exampleC : Fin 3 → ℕ := ![0, 0, 0]
def exampleD : Fin 3 → ℕ := ![1, 1, 0]
/-- Transversal `F₁ ↦ y, F₂ ↦ x₂, F₃ ↦ x₁`. -/
def exampleσ : Equiv.Perm (Fin 3) := Equiv.swap 0 2

@[powerlib_foundation] theorem example_offsets :
    exampleSig.IsTransversal exampleσ ∧ exampleSig.IsDualFeasible exampleC exampleD ∧
      exampleSig.IsTight exampleσ exampleC exampleD := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Signature.IsTransversal, Signature.IsDualFeasible, Signature.IsTight] <;> decide

/-- `(0, (1,1,0))` are the least nonnegative dual-feasible offsets. -/
@[powerlib_foundation] theorem example_offsets_least (c d : Fin 3 → ℕ)
    (h : exampleSig.IsDualFeasible c d) : exampleC ≤ c ∧ exampleD ≤ d := by
  have h00 := h 0 0 rfl
  have h11 := h 1 1 rfl
  have h02 := h 0 2 rfl
  simp [exampleSig] at h00 h11 h02
  refine ⟨fun i => by fin_cases i <;> simp [exampleC], fun j => ?_⟩
  fin_cases j <;> simp [exampleD] <;> omega

@[powerlib_foundation] theorem example_noteIndex :
    exampleSig.noteIndex exampleC = 0 := by
  unfold Signature.noteIndex
  decide

@[powerlib_foundation] theorem example_pryceIndex :
    exampleSig.pryceIndex exampleC exampleD = 1 := by
  unfold Signature.pryceIndex
  decide

/-- Hidden constraint: every solution of `ẋ₁ = y, ẋ₂ = x₁ - y, ẋ₁ + 2ẋ₂ = 0` (hypothesis `h`)
satisfies `y = 2 x₁`. -/
@[powerlib_foundation] theorem example_hidden_constraint {x₁ x₂ y : ℝ → ℝ}
    (h : ∀ t, HasDerivAt x₁ (y t) t ∧ HasDerivAt x₂ (x₁ t - y t) t ∧
      deriv x₁ t + 2 * deriv x₂ t = 0) (t : ℝ) : y t = 2 * x₁ t := by
  obtain ⟨h1, h2, h3⟩ := h t
  rw [h1.deriv, h2.deriv] at h3
  linarith

/-- Index ≠ 0: the initial point `(x₁, x₂, y) = (0, 0, 1)` is inconsistent: no solution of
`ẋ₁ = y, ẋ₂ = x₁ - y, ẋ₁ + 2ẋ₂ = 0` starts there. -/
@[powerlib_foundation] theorem example_inconsistent_initial {x₁ x₂ y : ℝ → ℝ}
    (h : ∀ t, HasDerivAt x₁ (y t) t ∧ HasDerivAt x₂ (x₁ t - y t) t ∧
      deriv x₁ t + 2 * deriv x₂ t = 0) : ¬ (x₁ 0 = 0 ∧ y 0 = 1) := by
  rintro ⟨h1, h2⟩
  have := example_hidden_constraint h 0
  rw [h1, h2] at this
  norm_num at this

/-- Index ≤ 1: along every solution of `ẋ₁ = y, ẋ₂ = x₁ - y, ẋ₁ + 2ẋ₂ = 0`, one
differentiation of the hidden constraint gives `ẏ = 2 y`, so `(x₁, x₂, y)` solves an explicit
ODE. -/
@[powerlib_foundation] theorem example_one_differentiation {x₁ x₂ y : ℝ → ℝ}
    (h : ∀ t, HasDerivAt x₁ (y t) t ∧ HasDerivAt x₂ (x₁ t - y t) t ∧
      deriv x₁ t + 2 * deriv x₂ t = 0) (t : ℝ) : HasDerivAt y (2 * y t) t := by
  have hd := ((h t).1).const_mul 2
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => example_hidden_constraint h s)

/-! ## Pendulum: both formulas give index 3 -/

/-- Pendulum `ṗ₁ = v₁, ṗ₂ = v₂, v̇₁ = -λ p₁, v̇₂ = -λ p₂ - g, p₁² + p₂² = L²`;
columns `(p₁, p₂, v₁, v₂, λ)`. -/
def pendulumSig : Signature (Fin 5) where
  occurs := fun i j => (![![true, false, true, false, false], ![false, true, false, true, false],
    ![true, false, true, false, true], ![false, true, false, true, true],
    ![true, true, false, false, false]] i) j
  order := fun i j => (![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]] i) j

def pendulumC : Fin 5 → ℕ := ![1, 1, 0, 0, 2]
def pendulumD : Fin 5 → ℕ := ![2, 2, 1, 1, 0]
/-- `F₁ ↦ p₁, F₂ ↦ v₂, F₃ ↦ v₁, F₄ ↦ λ, F₅ ↦ p₂`. -/
def pendulumσ : Equiv.Perm (Fin 5) :=
  ⟨![0, 3, 2, 4, 1], ![0, 4, 2, 1, 3], by decide, by decide⟩

@[powerlib_foundation] theorem pendulum_offsets :
    pendulumSig.IsTransversal pendulumσ ∧ pendulumSig.IsDualFeasible pendulumC pendulumD ∧
      pendulumSig.IsTight pendulumσ pendulumC pendulumD ∧
      pendulumSig.noteIndex pendulumC = 3 ∧ pendulumSig.pryceIndex pendulumC pendulumD = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Signature.IsTransversal, Signature.IsDualFeasible, Signature.IsTight,
      Signature.noteIndex, Signature.pryceIndex] <;> decide

/-! ## §1.9 Case A: synchronous constraint makes the system overdetermined -/

/-- Two swing equations `ω̇ₖ = Fₖ(t, ωₖ)` plus `ω₁ = ω₂` admit a solution only if the data
satisfy the compatibility condition `F₁(t, ω) = F₂(t, ω)` along it. -/
@[powerlib_foundation] theorem synchronous_constraint_compatibility {F₁ F₂ : ℝ → ℝ → ℝ}
    {ω₁ ω₂ : ℝ → ℝ} (h : ∀ t, HasDerivAt ω₁ (F₁ t (ω₁ t)) t ∧ HasDerivAt ω₂ (F₂ t (ω₂ t)) t ∧
      ω₁ t = ω₂ t) (t : ℝ) : F₁ t (ω₁ t) = F₂ t (ω₁ t) := by
  have he : ω₁ = ω₂ := funext fun s => (h s).2.2
  have h1 := (h t).1
  have h2 := (h t).2.1
  rw [← he] at h2
  exact h1.unique h2

/-- Distinct constant accelerations: the overdetermined system has no solution. -/
@[powerlib_foundation] theorem synchronous_constraint_no_solution {a₁ a₂ : ℝ} (ha : a₁ ≠ a₂) :
    ¬ ∃ ω₁ ω₂ : ℝ → ℝ, ∀ t, HasDerivAt ω₁ a₁ t ∧ HasDerivAt ω₂ a₂ t ∧ ω₁ t = ω₂ t := by
  rintro ⟨ω₁, ω₂, h⟩
  exact ha (synchronous_constraint_compatibility (F₁ := fun _ _ => a₁) (F₂ := fun _ _ => a₂) h 0)

end powerlib.DAE
