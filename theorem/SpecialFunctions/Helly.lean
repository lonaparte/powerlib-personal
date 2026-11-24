import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.Convex.Radon

/-! # Helly's theorem, drop-one form (foundation)

In a real vector space of finite dimension `d`, a family of `d + 2` convex sets has a common point
as soon as every subfamily obtained by dropping one set has a common point.

This is the form in which Helly's theorem settles an optimization problem with `d + 1`
constraints in dimension `d`: add the superlevel set `{x | f x ≥ t}` of a quasi-concave objective
to the `d + 1` convex constraint sets; dropping the superlevel set leaves the feasible set, and
dropping a constraint leaves a relaxation. If the feasible set is nonempty and every relaxation
dropping one constraint reaches the level `t`, the full problem reaches `t`: the optimum is the
smallest of the optima of the relaxations.

Scope.
* Generic convex geometry in a finite-dimensional real vector space; no model family and no
  engineering object.

Source: Helly's theorem (E. Helly, 1923), in the form of `Convex.helly_theorem'` of Mathlib
(`Mathlib/Analysis/Convex/Radon.lean`), specialized to `d + 2` sets: every subfamily of at most
`d + 1` sets misses some index, so it contains the subfamily dropping that index.

Results.
* `nonempty_iInter_of_drop_one`: if `finrank ℝ E = d`, the `d + 2` sets `F i` are convex and, for
  every `j`, the sets `F i` with `i ≠ j` have a common point, then all `F i` have a common point.
-/

namespace powerlib.SpecialFunctions

open Finset in
/-- **Helly's theorem, drop-one form**: `d + 2` convex sets in dimension `d` meet as soon as
every `d + 1` of them obtained by dropping one meet. -/
@[tmio T, powerlib_foundation] theorem nonempty_iInter_of_drop_one {E : Type*} [AddCommGroup E]
    [Module ℝ E] [FiniteDimensional ℝ E] {d : ℕ} (hd : Module.finrank ℝ E = d)
    (F : Fin (d + 2) → Set E) (hF : ∀ i, Convex ℝ (F i))
    (h : ∀ j, ∃ x, ∀ i, i ≠ j → x ∈ F i) : ∃ x, ∀ i, x ∈ F i := by
  classical
  have key := Convex.helly_theorem' (𝕜 := ℝ) (s := Finset.univ) (F := F) (fun i _ => hF i) (by
    intro I _ hI
    have hlt : #I < #(Finset.univ : Finset (Fin (d + 2))) := by
      rw [Finset.card_univ, Fintype.card_fin]; omega
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    obtain ⟨x, hx⟩ := h j
    exact ⟨x, Set.mem_iInter₂.mpr fun i hi => hx i fun hij => hj (hij ▸ hi)⟩)
  obtain ⟨x, hx⟩ := key
  exact ⟨x, fun i => Set.mem_iInter₂.mp hx i (Finset.mem_univ i)⟩

end powerlib.SpecialFunctions
