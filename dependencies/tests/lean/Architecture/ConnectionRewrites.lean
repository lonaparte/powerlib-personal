import theorem.TMIO.Compare
import theorem.TMIO.Instances.Finite
import theorem.Data.Analysis

/-! # Certified rewrites preserve the original mathematical interfaces

These checks exercise the actual production definitions, including arbitrary endpoint universes,
rewriting certified iff proofs, and the original forms of statements rewritten using generated
maps. Negative cases keep extensional equality from accepting unrelated functions or clauses.
-/

namespace ConnectionRewriteCases

open powerlib.TMIO OrderDual
universe u v w z

variable {A : Type u} {B : Type v} [CompleteLattice A] [CompleteLattice B]

example (back : sInfHom B A) : GaloisConnection (generate back) back := gc_generate back
example (back : sInfHom B A) (a : A) : IsLeast {b | a ≤ back b} (generate back a) :=
  generate_isLeast back a
example (back : sInfHom B A) (l : LowerAdjoint back) : l = generate back :=
  lowerAdjoint_eq_generate back l

example {I : Type w} {O : Type z} [CompleteLattice I] [CompleteLattice O]
    (S : Seed A B I O) :
    GaloisConnection (S.l₃ ∘ S.l₂ ∘ S.l₁) (S.u₁ ∘ S.u₂ ∘ S.u₃) := by
  change GaloisConnection (S.l₃ ∘ S.l₂ ∘ S.l₁) S.uTO
  rw [← S.generate_uTO]
  exact S.gc_whole

example {A' B' : Type*} [CompleteLattice A'] [CompleteLattice B']
    (back : sInfHom B A) (eA : A ≃o A') (eB : B ≃o B')
    (a : {a : A // back (generate back a) = a}) :
    fixedPointsIso (transport back eA eB) (closedTransport back eA eB a) =
      interiorTransport back eA eB (fixedPointsIso back a) :=
  Subtype.ext (fixedPointsIso_transport back eA eB a)

example {X : Type u} {Y : Type v} (t : X → Set Y) (x : X) :
    (table t).image {x} = t x := by
  have h := image_table_singleton t x
  change generate (cover (table t)) {x} = t x at h
  simpa only [generate_cover] using h

example {X : Type u} {Y : Type v} (R : SetRel X Y) (s : Set X) (y : Y)
    (h : y ∈ certify R s) : ∀ x, (x, y) ∈ R → x ∈ s := by
  rw [connection_proof% mem_certify] at h
  exact h

-- The generated-map formulation rules out every unbundled upper adjoint as before.
example : ¬ ∃ f : Set Bool → (Set (Bool × Bool))ᵒᵈ,
    GaloisConnection (fun P : (Set (Bool × Bool))ᵒᵈ => Prod.fst '' ofDual P) f := by
  rintro ⟨f, gc⟩
  let back : sInfHom (Set Bool) (Set (Bool × Bool))ᵒᵈ :=
    { toFun := f, map_sInf' := fun s => by rw [sInf_image]; exact gc.u_sInf }
  exact Finite.image_not_lowerAdjoint_inclusion ⟨back, (generate_unique back gc).symm⟩

example : ¬ ∃ f : (Set Bool)ᵒᵈ → (Set (Bool × Bool))ᵒᵈ,
    GaloisConnection (fun P : (Set (Bool × Bool))ᵒᵈ => toDual (Prod.fst '' ofDual P)) f := by
  rintro ⟨f, gc⟩
  let back : sInfHom (Set Bool)ᵒᵈ (Set (Bool × Bool))ᵒᵈ :=
    { toFun := f, map_sInf' := fun s => by rw [sInf_image]; exact gc.u_sInf }
  exact Finite.image_not_lowerAdjoint_reverse ⟨back, (generate_unique back gc).symm⟩

open powerlib.Data.Analysis in
example {K : Type u} [Field K] (d₁ d₂ : Record K) :
    stats (d₁ ++ d₂) = stats d₁ + stats d₂ := stats_append d₁ d₂

open powerlib.Data.Analysis in
example {K : Type u} [Field K] {R : K} (d : Record K)
    (hd : ∀ s ∈ d, s.voltage = R * s.current) (h : (stats d).2 ≠ 0) : estimate d = R :=
  estimate_eq_of_exact d hd h

open powerlib.Data.Analysis in
example {K : Type u} [Field K] :
    Set.image fit ∘ Set.image (fun s : (K × K) × (K × K) => s.1 + s.2) ∘
      Set.image (Prod.map stats stats) =
    Set.image estimate ∘ Set.image (fun p : Record K × Record K => p.1 ++ p.2) := by
  have h := generate_distributedEdge (K := K)
  change ⇑(generate distributedEdge) = ⇑(generate centralEdge) at h
  simpa only [distributedEdge, centralEdge, generate_comp, fitEdge, estimateEdge,
    generate_preimage, Function.comp_assoc] using h

open Lean Meta Elab Command Term in
run_cmd liftTermElabM do
  let rejected : Array Term := #[
    ← `((fun n : Nat => n + 1) = (fun n : Nat => n + 1)),
    ← `((fun _ : Nat => True) = (fun _ : Nat => True)),
    ← `((sInfHom.id (Set Nat)) ∅ = ∅ ∧ True)]
  for stx in rejected do
    let prop ← elabTermEnsuringType stx (mkSort .zero)
    synthesizeSyntheticMVarsNoPostponing
    let prop ← instantiateMVars prop
    let saved ← saveState
    let accepted ← try
      discard <| ClaimElab.encode prop
      pure true
    catch _ => pure false
    saved.restore
    if accepted then throwError "Extensional connection syntax admitted unrelated mathematics"
  logInfo "POWERLIB_CONNECTION_REWRITES_OK: original interfaces; certified iff reuse; 3 negative controls"

end ConnectionRewriteCases
