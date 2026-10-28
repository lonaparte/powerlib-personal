import theorem.Spectral.Local

/-! # Families whose translations also cover global sentences (foundation)

The local table of `theorem/Spectral/Local.lean` sends the global sentences, decay rates, sampled
contraction and conservation to the whole, inconsistent, requirement language. Families with a
global certificate — a quadratic decay energy, a Hurwitz state matrix, a sum-of-squares witness —
translate them into requirements of their own: global asymptotic and global exponential stability
and sampled contraction into a set `Rg` that gives global exponential stability, decay at the rate
`a` into a set `Rd a`, conservation (a conserved energy) into a set `Rc`. Their soundness proofs
repeated one case analysis over every sentence. This module states it once.

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
* Denotations: `den_globallyExponentiallyStable_subset_gas`,
  `den_globallyExponentiallyStable_subset_les`,
  `den_globallyExponentiallyStable_subset_contractive` (for every family, continuous or
  discrete: `theorem/Flow/Basic.lean` and `theorem/Map/Basic.lean`).
* Requirement spaces: `mem_realize_singleton` (the space of one requirement);
  `realize_univ_subset_of_eq_empty` (the whole, inconsistent, language realizes into every set).
* The table: `globalTable Rs Rg Ru Rc Rp Rd` (the local sentences to `Rs`, the global sentences
  and sampled contraction to `Rg`, decay at the rate `a` to `Rd a`, instability to `Ru`,
  conservation to `Rc`, passivity to `Rp`). With `Rg`, `Rd` and `Rc` the whole language it is the
  local table with `Rl = Rs`. `chain_le_semantics_of_globalTable` proves every translation sound
  from six obligations: `Rs` gives local exponential stability, `Rg` global exponential
  stability, `Rd a` decay at the rate `a`, `Ru` instability, `Rc` conservation, `Rp` passivity; a
  set that is the whole, inconsistent, language discharges its obligation by
  `realize_univ_subset_of_eq_empty`.

Family and connection conclusions.
* None: the module states the laws once for arbitrary families; model modules instantiate them and
  publish their conclusions as connection statements.
-/

noncomputable section

namespace powerlib.Spectral

open TMIO Set

variable {X Q : Type*} {n p : ℕ}

/-! ## Denotations of the global sentences -/

section Denotation

variable {F : Family X Q n p}

/-- Global exponential stability gives global asymptotic stability, for every family. -/
@[tmio TM, powerlib_foundation] theorem den_globallyExponentiallyStable_subset_gas :
    F.den (.flow .globallyExponentiallyStable) ⊆
      F.den (.flow .globallyAsymptoticallyStable) := by
  intro x hx
  rw [Family.mem_den] at hx ⊢
  cases h : F.system x with
  | continuous s =>
    rw [h, Sentence.holds_flow] at hx
    rw [Sentence.holds_flow]
    exact Flow.GloballyExponentiallyStable.globallyAsymptoticallyStable hx
  | discrete s =>
    rw [h, Sentence.holds_flow_discrete] at hx
    rw [Sentence.holds_flow_discrete]
    exact Map.GloballyExponentiallyStable.globallyAsymptoticallyStable hx
  | disturbed s _ _ _ =>
    rw [h, Sentence.holds_flow_disturbed] at hx
    rw [Sentence.holds_flow_disturbed]
    exact fun ω => Flow.GloballyExponentiallyStable.globallyAsymptoticallyStable (hx ω)

/-- Global exponential stability gives local exponential stability, for every family. -/
@[powerlib_foundation] theorem den_globallyExponentiallyStable_subset_les :
    F.den (.flow .globallyExponentiallyStable) ⊆
      F.den (.flow .locallyExponentiallyStable) := by
  intro x hx
  rw [Family.mem_den] at hx ⊢
  cases h : F.system x with
  | continuous s =>
    rw [h, Sentence.holds_flow] at hx
    rw [Sentence.holds_flow]
    exact Flow.GloballyExponentiallyStable.locallyExponentiallyStable hx
  | discrete s =>
    rw [h, Sentence.holds_flow_discrete] at hx
    rw [Sentence.holds_flow_discrete]
    exact Map.GloballyExponentiallyStable.locallyExponentiallyStable hx
  | disturbed s _ _ _ =>
    rw [h, Sentence.holds_flow_disturbed] at hx
    rw [Sentence.holds_flow_disturbed]
    exact fun ω => Flow.GloballyExponentiallyStable.locallyExponentiallyStable (hx ω)

/-- Global exponential stability gives sampled contraction, for every family. -/
@[powerlib_foundation] theorem den_globallyExponentiallyStable_subset_contractive :
    F.den (.flow .globallyExponentiallyStable) ⊆ F.den (.flow .contractive) := by
  intro x hx
  rw [Family.mem_den] at hx ⊢
  cases h : F.system x with
  | continuous s =>
    rw [h, Sentence.holds_flow] at hx
    rw [Sentence.holds_flow]
    exact Flow.GloballyExponentiallyStable.sampledContraction hx
  | discrete s =>
    rw [h, Sentence.holds_flow_discrete] at hx
    rw [Sentence.holds_flow_discrete]
    exact Map.GloballyExponentiallyStable.sampledContraction hx
  | disturbed s _ _ _ =>
    rw [h, Sentence.holds_flow_disturbed] at hx
    rw [Sentence.holds_flow_disturbed]
    exact fun ω => Flow.GloballyExponentiallyStable.sampledContraction (hx ω)

end Denotation

/-- The space of one requirement. -/
@[powerlib_foundation] theorem mem_realize_singleton {meets : X → Q → Prop} {q : Q} {x : X} :
    x ∈ realize meets {q} ↔ meets x q := by
  simp [mem_realize]

/-- The whole language, when no system meets it, realizes into every set. -/
@[powerlib_foundation] theorem realize_univ_subset_of_eq_empty {meets : X → Q → Prop}
    (h : realize meets univ = ∅) (S : Set X) : realize meets univ ⊆ S := by
  rw [h]
  exact empty_subset S

/-! ## The global table and soundness -/

/-- The global table: the local sentences to `Rs`, global asymptotic and global exponential
stability and sampled contraction to `Rg`, decay at the rate `a` to `Rd a`, instability to `Ru`,
conservation to `Rc`, passivity to `Rp`, the envelope sentences to no requirement. -/
def globalTable (Rs Rg Ru Rc Rp : Set Q) (Rd : ℝ → Set Q) : Sentence → Set Q
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => Rs
  | .flow .globallyAsymptoticallyStable | .flow .globallyExponentiallyStable
  | .flow .contractive => Rg
  | .flow (.decay a) => Rd a
  | .flow .unstable => Ru
  | .flow .conservative => Rc
  | .passive => Rp
  | .envelope _ => ∅

section Table

variable {F : Family X Q n p} {Rs Rg Ru Rc Rp : Set Q} {Rd : ℝ → Set Q}

/-- Soundness of every translation of a family with the global table: the requirement sets give
local exponential stability (`Rs`), global exponential stability (`Rg`), decay at the rate `a`
(`Rd a`), instability (`Ru`), conservation (`Rc`) and passivity (`Rp`), and every member satisfies
the envelope sentences (a family read without an envelope, `Family.IsAutonomous.den_envelope`). -/
@[powerlib_foundation] theorem chain_le_semantics_of_globalTable
    (ht : ∀ s, F.translate s = globalTable Rs Rg Ru Rc Rp Rd s)
    (hS : realize F.meets Rs ⊆ F.den (.flow .locallyExponentiallyStable))
    (hG : realize F.meets Rg ⊆ F.den (.flow .globallyExponentiallyStable))
    (hD : ∀ a, realize F.meets (Rd a) ⊆ F.den (.flow (.decay a)))
    (hU : realize F.meets Ru ⊆ F.den (.flow .unstable))
    (hC : realize F.meets Rc ⊆ F.den (.flow .conservative))
    (hP : realize F.meets Rp ⊆ F.den .passive) (hE : ∀ E, F.den (.envelope E) = univ) :
    ∀ P, F.chain P ≤ F.semantics P := by
  refine Family.chain_le_semantics_iff.mpr fun s x hx => ?_
  change x ∈ realize F.meets (F.translate s) at hx
  rw [ht s] at hx
  rcases s with P | _ | E
  · cases P
    case lyapunovStable => exact den_locallyExponentiallyStable_subset_lyapunovStable (hS hx)
    case locallyAsymptoticallyStable => exact den_locallyExponentiallyStable_subset_las (hS hx)
    case locallyExponentiallyStable => exact hS hx
    case globallyAsymptoticallyStable => exact den_globallyExponentiallyStable_subset_gas (hG hx)
    case globallyExponentiallyStable => exact hG hx
    case contractive => exact den_globallyExponentiallyStable_subset_contractive (hG hx)
    case decay a => exact hD a hx
    case unstable => exact hU hx
    case conservative => exact hC hx
  · exact hP hx
  · rw [hE E]
    exact mem_univ x

end Table

end powerlib.Spectral
