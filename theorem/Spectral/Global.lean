import theorem.Spectral.Local

/-! # Families whose translations also cover global sentences (foundation)

The local table of `theorem/Spectral/Local.lean` sends the global sentences, decay rates, sampled
contraction and conservation to the whole, inconsistent, requirement language. Families with a
global certificate — a quadratic decay energy, a Hurwitz state matrix, a sum-of-squares witness —
translate them into requirements of their own: global asymptotic and global exponential stability
and sampled contraction into a set `Rg` that gives global exponential stability, decay at the rate
`a` into a set `Rd a`, conservation (a conserved energy) into a set `Rc`. Their soundness proofs
repeated one case analysis over every sentence. This module states their table once, as an
instance of the table `Spectral.table` of `theorem/Spectral/Local.lean`.

Scope.
* A generic template, not a model: an arbitrary family `F : Family X Q n p` (continuous or
  discrete behaviour, with or without ports), an arbitrary requirement language `Q` and requirement
  sets. Obligations are stated on denotations, as in `theorem/Spectral/Local.lean`, so each family
  discharges them with its own members or private stability lemmas; no new behavioural notion is
  defined.

Source: generic `Family` laws shared by the families with global certificates (audit of the
library; the implications between the sentences of `theorem/Flow/Basic.lean` and
`theorem/Map/Basic.lean`).

Results.
* The table: `globalTable Rs Rg Ru Rc Rp Rd` (`Spectral.table` with Lyapunov stability sharing
  the local sentences' `Rs` and the envelope sentences sent to no requirement: the local sentences
  to `Rs`, the global sentences and sampled contraction to `Rg`, decay at the rate `a` to `Rd a`,
  instability to `Ru`, conservation to `Rc`, passivity to `Rp`). It is not the local table when
  `Rg`, `Rd` and `Rc` are the whole language: the local table sends the envelope sentences to the
  whole language, the global table to no requirement. `chain_le_semantics_of_globalTable` proves
  every translation sound from six obligations: `Rs` gives local exponential stability, `Rg`
  global exponential stability, `Rd a` decay at the rate `a`, `Ru` instability, `Rc` conservation,
  `Rp` passivity, and every member satisfies the envelope sentences; a set that is the whole,
  inconsistent, language discharges its obligation by `realize_univ_subset_of_eq_empty`. The
  denotation inclusions of the global sentences (`den_globallyExponentiallyStable_subset_gas` and
  its relatives) are in `theorem/Spectral/Local.lean`.

Family and connection conclusions.
* The soundness of the global table is a generic foundation connection. Model modules
  instantiate it for their own engineering conclusions.
-/

noncomputable section

namespace powerlib.Spectral

open TMIO Set

variable {X Q : Type*} {n p : ℕ}

/-! ## The global table and soundness -/

/-- The global table: the local sentences to `Rs`, global asymptotic and global exponential
stability and sampled contraction to `Rg`, decay at the rate `a` to `Rd a`, instability to `Ru`,
conservation to `Rc`, passivity to `Rp`, the envelope sentences to no requirement. -/
abbrev globalTable (Rs Rg Ru Rc Rp : Set Q) (Rd : ℝ → Set Q) : Sentence → Set Q :=
  table Rs Rs Rg Ru Rc Rp Rd ∅

section Table

variable {F : Family X Q n p} {Rs Rg Ru Rc Rp : Set Q} {Rd : ℝ → Set Q}

/-- Soundness of every translation of a family with the global table: the requirement sets give
local exponential stability (`Rs`), global exponential stability (`Rg`), decay at the rate `a`
(`Rd a`), instability (`Ru`), conservation (`Rc`) and passivity (`Rp`), and every member satisfies
the envelope sentences (a family read without an envelope, `Family.IsPort.den_envelope`). -/
@[tmio TM, powerlib_foundation] theorem chain_le_semantics_of_globalTable
    (ht : ∀ s, F.translate s = globalTable Rs Rg Ru Rc Rp Rd s)
    (hS : realize F.meets Rs ⊆ F.den (.flow .locallyExponentiallyStable))
    (hG : realize F.meets Rg ⊆ F.den (.flow .globallyExponentiallyStable))
    (hD : ∀ a, realize F.meets (Rd a) ⊆ F.den (.flow (.decay a)))
    (hU : realize F.meets Ru ⊆ F.den (.flow .unstable))
    (hC : realize F.meets Rc ⊆ F.den (.flow .conservative))
    (hP : realize F.meets Rp ⊆ F.den .passive) (hE : ∀ E, F.den (.envelope E) = univ) :
    connection% (∀ P, F.chain P ≤ F.semantics P) := show ∀ P, F.chain P ≤ F.semantics P from
  chain_le_semantics_of_table ht
    (fun _ hx => den_locallyExponentiallyStable_subset_lyapunovStable (hS hx)) hS hG hD hU hC hP
    (fun E x _ => (hE E).symm ▸ mem_univ x)

end Table

end powerlib.Spectral
