import theorem.TMIO.ClaimElab

/-! Common constraints restrict the comparison domain. They do not add a conclusion or
turn an arbitrary intersection into an endpoint. Keep all carrier universes independent. -/

namespace ConstrainedConnectionCases
open powerlib.TMIO OrderDual
universe u v w z

def ExactUnder {Y : Type v} (s t d : Set Y) : Prop := s ∩ d = t ∩ d
def SoundUnder {Y : Type v} (s t d : Set Y) : Prop := s ∩ d ⊆ t
def CompleteUnder {Y : Type v} (s t d : Set Y) : Prop := t ∩ d ⊆ s

variable {X : Type u} {Y : Type v} {R : Type w}
  (rel : SetRel X Y) (holds : X → Nat → Prop) (meets : Y → R → Prop)
  (impl : Y → Nat → Prop) (s : Nat) (Δ : Set R)

@[powerlib_foundation] theorem exact_iff :
    connection% (ExactUnder (certify rel (realize holds {s})) (realize impl {s}) (realize meets Δ) ↔
      SoundUnder (certify rel (realize holds {s})) (realize impl {s}) (realize meets Δ) ∧
      CompleteUnder (certify rel (realize holds {s})) (realize impl {s}) (realize meets Δ)) := by
  unfold Statement ExactUnder SoundUnder CompleteUnder
  constructor
  · intro h
    exact ⟨fun _ hy => (h ▸ hy).1, fun _ hy => (h.symm ▸ hy).1⟩
  · rintro ⟨hs, hc⟩
    exact Set.Subset.antisymm (fun _ hy => ⟨hs hy, hy.2⟩) (fun _ hy => ⟨hc hy, hy.2⟩)

@[powerlib_foundation] theorem exact_mono {Δ' : Set R}
    (h : certify rel (realize holds {s}) ∩ realize meets Δ =
      realize impl {s} ∩ realize meets Δ) (hΔ : Δ ⊆ Δ') :
    connection% (certify rel (realize holds {s}) ∩ realize meets Δ' =
      realize impl {s} ∩ realize meets Δ') := by
  unfold Statement
  have hsub := realize_antitone meets hΔ
  apply Set.Subset.antisymm
  · intro y hy
    exact ⟨(h ▸ (show y ∈ certify rel (realize holds {s}) ∩ realize meets Δ from
      ⟨hy.1, hsub hy.2⟩)).1, hy.2⟩
  · intro y hy
    exact ⟨(h.symm ▸ (show y ∈ realize impl {s} ∩ realize meets Δ from
      ⟨hy.1, hsub hy.2⟩)).1, hy.2⟩

-- Existing iff consumers still work, including rewriting through the checked proof view.
example : (certify rel (realize holds {s}) ∩ realize meets Δ =
    realize impl {s} ∩ realize meets Δ) ↔
    (certify rel (realize holds {s}) ∩ realize meets Δ ⊆ realize impl {s} ∧
      realize impl {s} ∩ realize meets Δ ⊆ certify rel (realize holds {s})) := by
  exact exact_iff rel holds meets impl s Δ

example : ExactUnder (certify rel (realize holds {s})) (realize impl {s}) (realize meets Δ) ↔
    SoundUnder (certify rel (realize holds {s})) (realize impl {s}) (realize meets Δ) ∧
    CompleteUnder (certify rel (realize holds {s})) (realize impl {s}) (realize meets Δ) := by
  rw [connection_proof% exact_iff]

@[powerlib_foundation] theorem seeds_eq {T : Type u} {M : Type v}
    {I : Type w} {O : Type z} [CompleteLattice T] [CompleteLattice M]
    [CompleteLattice I] [CompleteLattice O] (S : Seed T M I O) :
    connection% (S = S) := rfl

@[powerlib_foundation] theorem kern_identity (S : Set X) : connection% (kern id S = S) := by
  change Set.kernImage id S = S
  ext x
  exact ⟨fun h => h rfl, fun h y heq => (congrArg (fun z => z ∈ S) heq).mpr h⟩

-- The old type is definitionally equal; tactic matching uses the endpoint formulation explicitly.
example (S : Set X) : Set.kernImage id S = S := kern_identity S
example (S : Set X) : Set.kernImage id S = S := by
  change kern id S = S
  rw [kern_identity]

open Lean Meta Elab Command Term in
run_cmd liftTermElabM do
  let controls : Array Term := #[
    ← `(∀ d e : Set Nat, (sInfHom.id (Set Nat)) ∅ ∩ d = ∅ ∩ e),
    ← `(∀ d : Set Nat, ((sInfHom.id (Set Nat)) ∅ ∩ d = ∅ ∩ d) ∧ True),
    ← `(∀ d : Set Nat, ((sInfHom.id (Set Nat)) ∅ ∩ d = ∅ ∩ d) ↔
      ((sInfHom.id (Set Nat)) ∅ ∩ d ⊆ ∅ ∧ d ⊆ ∅)),
    ← `(∀ d : Set Nat, (sInfHom.id (Set Nat)) ∅ ∩ d ⊆ d),
    ← `((0, 1) = ((0, 1) : Nat × Nat))]
  for stx in controls do
    let prop ← elabTermEnsuringType stx (mkSort .zero)
    synthesizeSyntheticMVarsNoPostponing
    let prop ← instantiateMVars prop
    let saved ← saveState
    let accepted ← try
      discard <| ClaimElab.encode prop
      pure true
    catch _ => pure false
    saved.restore
    if accepted then throwError "Constrained connection syntax admitted unrelated structure: {stx}"
  for name in #[``exact_iff, ``exact_mono, ``seeds_eq, ``kern_identity] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
  logInfo "POWERLIB_CONSTRAINED_CONNECTIONS_OK: independent universes; 5 negative controls; trusted proofs"

end ConstrainedConnectionCases
