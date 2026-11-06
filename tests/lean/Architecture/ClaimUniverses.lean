import theorem.TMIO.ClaimElab

/-! # Universe-polymorphic connection certificates

These checks import only the connection grammar and its order/set constructors. The forward and
backward sides of an adjunction may have different carrier universes. Failed endpoint choices
must leave the other endpoint available, and `Type*` parameters must remain polymorphic.
The negative cases retain the closed grammar's restrictions on unrelated propositions, including
those hidden behind a type binder.
-/

namespace ClaimUniverseCases

open powerlib.TMIO OrderDual

universe u v

variable {A : Type u} {B : Type v} [CompleteLattice A] [CompleteLattice B]

@[powerlib_foundation] theorem endpoint (back : sInfHom B A) (b : B) :
    connection% (back b = back b) := rfl

@[powerlib_foundation] theorem quantified (back : sInfHom B A) :
    connection% (∀ b, back b = back b) := fun _ => rfl

@[powerlib_foundation] theorem reverse_iff (back : sInfHom B A) (b : B) (a : A) :
    connection% (back b = back b ↔ generate back a = generate back a) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

@[powerlib_foundation] theorem reverse_and (back : sInfHom B A) (b : B) (a : A) :
    connection% (back b = back b ∧ generate back a = generate back a) := ⟨rfl, rfl⟩

@[powerlib_foundation] theorem reverse_maps (back : sInfHom B A) (a : A) :
    connection% (generate back a = generate back a ∧ back = back) := ⟨rfl, rfl⟩

variable {X : Type u} {Q : Type v}

-- The first equality fixes the pair (0, u). The left endpoint of the second equality uses
-- (u, v), so its rejected candidates must not prevent choosing the right endpoint (u, 0).
@[powerlib_foundation] theorem right_endpoint_fallback
    (semantics : sInfHom (Set X)ᵒᵈ (Set Nat))
    (requirements : sInfHom (Set X)ᵒᵈ (Set Q)) (s : Nat) (q : Set Q)
    (h : semantics = semantics ↔ ofDual (generate requirements q) =
      ofDual (generate semantics {s})) :
    connection% (semantics = semantics ↔ ofDual (generate requirements q) =
      ofDual (generate semantics {s})) := h

-- The first clause has an available endpoint in (u, v), but only its other endpoint
-- shares (u, 0) with the later clause. The whole certificate must retry that earlier choice.
@[powerlib_foundation] theorem earlier_endpoint_fallback
    (semantics : sInfHom (Set X)ᵒᵈ (Set Nat))
    (requirements : sInfHom (Set X)ᵒᵈ (Set Q)) (Φ : Set Nat) (Γ : Set Q)
    (h : ofDual (generate requirements Γ) = ofDual (generate semantics Φ) ↔
      generate semantics Φ = generate semantics Φ) :
    connection% (ofDual (generate requirements Γ) = ofDual (generate semantics Φ) ↔
      generate semantics Φ = generate semantics Φ) := h

@[powerlib_foundation] theorem reverse_membership
    (back : sInfHom (Set X)ᵒᵈ (Set Nat)) (Φ : Set Nat) (x : X) :
    connection% (back = back ∧
      (x ∈ ofDual (generate back Φ) ↔ x ∈ ofDual (generate back Φ))) := ⟨rfl, Iff.rfl⟩

@[powerlib_foundation] theorem certification_inference
    (back : sInfHom (Set X)ᵒᵈ (Set Nat)) (D : Set X) (Φ : Set Nat) :
    connection% (D ⊆ ofDual (generate back Φ) ↔ Φ ⊆ back (toDual D)) :=
  (gc_generate back) Φ (toDual D)

@[powerlib_foundation] theorem exact_under_shape (sat : X → Q → Prop)
    (holds : X → Nat → Prop) (translate : Nat → Set Q) (s : Nat) (Δ : Set Q)
    (h : realize sat (translate s ∪ Δ) = realize holds {s} ∩ realize sat Δ) :
    connection% (realize sat (translate s ∪ Δ) = realize holds {s} ∩ realize sat Δ) := h

@[powerlib_foundation] theorem preimage_other_universe {Y : Type v} (g : X → Y)
    (holdsX : X → Nat → Prop) (holdsY : Y → Nat → Prop) (s : Nat)
    (h : g ⁻¹' realize holdsY {s} = realize holdsX {s}) :
    connection% (g ⁻¹' realize holdsY {s} = realize holdsX {s}) := h

@[powerlib_foundation] theorem not_realize (sat : X → Q → Prop) (x : X) (q : Q)
    (h : ¬ sat x q) : connection% (x ∉ realize sat {q}) := by
  intro hx
  exact h ((mem_realize sat {q} x).mp hx q (by simp))

@[powerlib_foundation] theorem kern_image {Y : Type v} (f : X → Y)
    (holds : X → Nat → Prop) (s : Nat) :
    connection% (kern f (realize holds {s}) = Set.kernImage f (realize holds {s})) := rfl

@[powerlib_foundation] theorem pointwise_generate (back : sInfHom B A) :
    connection% (∀ a, generate back a = generate back a) := fun _ => rfl

@[powerlib_foundation] theorem existential_type (back : sInfHom B A) (b : B) :
    connection% (∃ _X : Type 1, back b = back b) := ⟨PUnit, rfl⟩

-- The automatically introduced universe parameters are independent, just like explicit u/v.
@[powerlib_foundation] theorem star_carriers {A B : Type*}
    [CompleteLattice A] [CompleteLattice B] (back : sInfHom B A) (b : B) (a : A) :
    connection% (back b = back b ↔ generate back a = generate back a) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

-- Applying the declaration at unrelated named universes detects accidental specialization.
example (back : sInfHom B A) (b : B) (a : A) :
    back b = back b ↔ generate back a = generate back a := star_carriers back b a

open Lean Meta Elab Command Term in
run_cmd liftTermElabM do
  let controls : Array Term := #[
    ← `(((sInfHom.id (Set Nat)) ∅ = ∅) ∧ True),
    ← `(((sInfHom.id (Set Nat)) ∅ = ∅) ∧ (0 : Nat) ≤ 1),
    ← `(∃ X : Type, Nonempty X)]
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
    if accepted then throwError "Universe inference admitted an unrelated connection clause"
  logInfo "POWERLIB_CLAIM_UNIVERSES_OK: polymorphic, reversed and fallback atoms; 3 negative controls"

end ClaimUniverseCases
