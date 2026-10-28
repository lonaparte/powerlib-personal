import theorem.Circuits.RL
import theorem.Architecture
import dependencies.tests.lean.Architecture.ConnectionFamilyFixture
import dependencies.tests.lean.Architecture.GenericModelValueFixture

open powerlib powerlib.TMIO

namespace ConnectionAdmission

-- A real public connection is admitted without assigning a presentation classification.
theorem passive (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    connection% (m ∈ Circuits.RL.family.den .passive) := by
  unfold Statement
  exact Circuits.RL.family_isLinear.mem_den_passive (Circuits.RL.kyp m h)

-- Explicit metadata is preserved; admission still checks the actual statement.
@[powerlib_foundation] theorem foundation_connection (m : Circuits.RL.Impedance)
    (h : 0 ≤ m.resistance) : connection% (m ∈ Circuits.RL.family.den .passive) := passive m h

@[powerlib_domain] theorem domain_connection (m : Circuits.RL.Impedance)
    (h : 0 ≤ m.resistance) : connection% (m ∈ Circuits.RL.family.den .passive) := passive m h

-- Private fixtures are implementation evidence, never public results.
@[powerlib_foundation] private theorem raw (m : Circuits.RL.Impedance)
    (h : 0 ≤ m.resistance) : m.plant.system.Passive :=
  ⟨_, (Circuits.RL.kyp m h).passiveWith⟩

def fakeEndpoint (m : Circuits.RL.Impedance) : Prop := m.plant.system.Passive

private theorem aliased (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    fakeEndpoint m := raw m h

abbrev ModelAlias := Circuits.RL.Impedance

private theorem aliasedModel (m : ModelAlias) (h : 0 ≤ m.resistance) :
    fakeEndpoint m := raw m h

private def proofDefinition (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    fakeEndpoint m := raw m h

private theorem hiddenRelation (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    connection% (m ∈ Circuits.RL.family.den .passive ↔ fakeEndpoint m) := by
  unfold Statement
  exact ⟨fun _ => raw m h, fun _ => passive m h⟩

private theorem rawHypothesis (m : Circuits.RL.Impedance) (h : m.plant.system.Passive) :
    connection% (m ∈ Circuits.RL.family.den .passive) := by
  unfold Statement
  exact Circuits.RL.family.mem_den.mpr h

-- A real connection does not make a raw behavioural input an admitted interface.
private theorem hiddenInput (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    connection% (m ∈ (sInfHom.id (Set Circuits.RL.Impedance))
      {m : Circuits.RL.Impedance | fakeEndpoint m}) := by
  unfold Statement
  exact raw m h

private theorem freshRaw (m : ConnectionFamilyFixture.Model) :
    (Port.System.autonomous m.field).Passive := Port.System.autonomous_passive m.field

def AllPassive : Prop := ∀ m : Circuits.RL.Impedance, 0 ≤ m.resistance → m.plant.system.Passive

private theorem packed : AllPassive := fun m h => raw m h

-- The grammar extension. A claim about arbitrary families of `Type`: type parameters of the
-- theorem, or binders over `Type` inside the claim (`allType`).
@[powerlib_foundation] theorem genericPassive {X Q : Type} (F : Family X Q 1 0) (x : X)
    (h : x ∈ F.den .passive) :
    connection% (x ∈ F.den .passive) := by
  unfold Statement
  exact h

-- A generic semantic bridge may name the library's behavioural interface. Its classification
-- does not grant that permission: the model type is arbitrary and the conclusion uses F.
@[powerlib_foundation] theorem genericFlowInterface {X Q : Type} (F : Family X Q 1 0)
    (f : X → Dynamics.State 1 → Dynamics.State 1) (pt : X → Dynamics.State 1)
    (hden : ∀ x (P : Flow.Property), x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x))
    (x : X) (P : Flow.Property) :
    connection% (x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x)) := by
  unfold Statement
  exact hden x P

@[powerlib_foundation] theorem genericReachInterface {X Q : Type} (F : Family X Q 1 0)
    (sys : X → Port.System 1 0) (S A : X → Set (Dynamics.State 1)) (T ε : ℝ≥0∞)
    (hden : ∀ x, x ∈ F.den (.envelope (.safe T ε)) ↔ (sys x).reach (S x) T ⊆ A x)
    (x : X) :
    connection% (x ∈ F.den (.envelope (.safe T ε)) ↔ (sys x).reach (S x) T ⊆ A x) := by
  unfold Statement
  exact hden x

-- An arbitrary Family cannot launder a concrete model or an unconnected signal input.
@[powerlib_foundation] private theorem genericModelInput {X Q : Type} (F : Family X Q 1 0)
    (x : X) (m : Circuits.RL.Impedance) (_h : m.plant.system.Passive)
    (hx : x ∈ F.den .passive) : connection% (x ∈ F.den .passive) := hx

private theorem phantomFamilyInput {X Q : Type} (_F : Family X Q 1 0)
    (m : Circuits.RL.Impedance) (h : m.plant.system.Passive) :
    connection% (m ∈ Circuits.RL.family.den .passive) := by
  unfold Statement
  exact Circuits.RL.family.mem_den.mpr h

private theorem genericSignalInput {X Q : Type} (F : Family X Q 1 0) (x : X)
    (_signal : ℝ → Dynamics.State 1) (hx : x ∈ F.den .passive) :
    connection% (x ∈ F.den .passive) := hx

private theorem hiddenGenericModelInterface {X Q : Type} (F : Family X Q 1 0) (x : X)
    (r : ℝ)
    (h : x ∈ F.den .passive ↔ (GenericModelValueFixture.systemAlias r).Passive) :
    connection% (x ∈ F.den .passive ↔ (GenericModelValueFixture.systemAlias r).Passive) := h

-- The module linter must discover this model before it becomes an imported declaration.
structure CurrentModel where
  field : Dynamics.State 1 → Dynamics.State 1

noncomputable def currentFamily : Family CurrentModel Unit 1 0 :=
  ⟨fun m => Port.System.autonomous m.field, fun _ _ => True, fun _ => Set.univ⟩

private theorem genericCurrentModelInput {X Q : Type} (F : Family X Q 1 0) (x : X)
    (m : CurrentModel) (_h : (Port.System.autonomous m.field).Passive)
    (hx : x ∈ F.den .passive) : connection% (x ∈ F.den .passive) := hx

theorem allTypeClaim : connection% (∀ (X Q : Type) (F : Family X Q 1 0) (x : X),
    x ∈ F.den .passive → x ∈ F.den .passive) := by
  unfold Statement
  exact fun _ _ _ _ h => h

-- A claim characterized by a numeric side condition (`iffCondition`), and an existential whose
-- witness is guarded by one (`existsGuard`).
theorem conditionIff :
    connection% (Circuits.RL.family.chain = Circuits.RL.family.semantics ↔ (0 : ℕ) ≤ 1) := by
  unfold Statement
  exact iff_of_true Circuits.RL.chain_eq_semantics (by norm_num)

theorem guardedExists (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    connection% (∃ r : ℝ, 0 < r ∧ m ∈ Circuits.RL.family.den .passive) := by
  unfold Statement
  exact ⟨1, one_pos, passive m h⟩

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftTermElabM do
    let ctx ← Architecture.context
    let models ← Architecture.modelTypes
    for name in #[``raw, ``aliased, ``aliasedModel, ``proofDefinition, ``hiddenRelation,
        ``rawHypothesis, ``hiddenInput, ``freshRaw, ``packed, ``genericModelInput,
        ``phantomFamilyInput, ``genericSignalInput, ``hiddenGenericModelInterface,
        ``genericCurrentModelInput] do
      if (← Architecture.publicTypeRejection ctx models (← getConstInfo name).type).isNone then
        throwError "Public admission accepted its rejection fixture: {name}"
    for name in #[``passive, ``foundation_connection, ``domain_connection, ``genericPassive,
        ``genericFlowInterface, ``genericReachInterface, ``allTypeClaim, ``conditionIff,
        ``guardedExists] do
      if let some reason ← Architecture.declarationRejection ctx models name then
        throwError "Public admission rejected its positive fixture: {name}: {reason}"
  let classified := Registry.theoremNames env
  let foundations := Registry.theoremNames env (some .foundation)
  let domains := Registry.theoremNames env (some .domain)
  for name in #[``passive, ``allTypeClaim, ``conditionIff, ``guardedExists] do
    unless (Registry.kindOf? env name).isNone && !classified.contains name &&
        !foundations.contains name && !domains.contains name do
      throwError "An unannotated connection acquired a presentation classification: {name}"
  for name in #[``foundation_connection, ``genericPassive, ``genericFlowInterface,
      ``genericReachInterface] do
    unless Registry.kindOf? env name == some .foundation && classified.contains name &&
        foundations.contains name && !domains.contains name do
      throwError "A connection overrode its explicit foundation classification: {name}"
  unless Registry.kindOf? env ``domain_connection == some .domain &&
      classified.contains ``domain_connection && domains.contains ``domain_connection &&
      !foundations.contains ``domain_connection do
    throwError "An explicitly classified domain connection was lost"
  logInfo m!"POWERLIB_TYPED_ADMISSION_OK: unclassified, foundation and domain connections; \
    14 rejection controls"

-- The grammar extension admits side conditions only as the characterizing side of an iff and as
-- the guard of an existential, and comparisons of numbers only. Binder universes are inferred;
-- behaviour in an operand or a binder is still rejected by the bypass audit.
open Lean Elab Command Term in
run_cmd liftTermElabM do
  let ctx ← Architecture.context
  let elabProp (stx : Term) : TermElabM Expr := do
    let e ← elabTerm stx (some (mkSort .zero))
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let controls : Array (String × Term) := #[
    ("claim ↔ a static fact that is no comparison of numbers",
      ← `(Circuits.RL.family.chain = Circuits.RL.family.semantics ↔
          LinearSystems.IsHurwitz !![(-1 : ℝ)])),
    ("a numeric conjunct", ← `(Circuits.RL.family.chain = Circuits.RL.family.semantics ∧
          (1 : ℕ) ≤ 2)),
    ("condition ↔ condition", ← `(((2 : ℕ) ≤ 1) ↔ ((2 : ℕ) ≤ 1))),
    ("a comparison in Prop", ← `(Circuits.RL.family.chain = Circuits.RL.family.semantics ↔
          ((True : Prop) ≤ ((1 : ℕ) ≤ 2)))),
    ("behaviour inside a numeric operand", ← `(∀ m : Circuits.RL.Impedance,
          Circuits.RL.family.chain = Circuits.RL.family.semantics ↔
            (@ite ℕ m.plant.system.Passive (Classical.propDecidable _) 0 1) ≤ 0)),
    ("a binder over Type without a claim", ← `(∀ X : Type, Nonempty (X → X))),
    ("an existential over types without a claim", ← `(∃ X : Type, Nonempty X)),
    ("a binder over Type with a signal binder",
      ← `(∀ (X : Type) (σ : ℝ → EuclideanSpace ℝ (Fin 1)),
          Circuits.RL.family.chain = Circuits.RL.family.semantics)),
    ("a condition mixed with a static fact",
      ← `(Circuits.RL.family.chain = Circuits.RL.family.semantics ↔
          ((1 : ℕ) ≤ 2 ∧ LinearSystems.IsHurwitz !![(-1 : ℝ)]))),
    ("condition ↔ claim", ← `(((2 : ℕ) ≤ 1) ↔
          Circuits.RL.family.chain = Circuits.RL.family.semantics)),
    ("an existential guarded by a static fact", ← `(∃ k : ℕ,
          LinearSystems.IsHurwitz !![(-1 : ℝ)] ∧
            Circuits.RL.family.chain = Circuits.RL.family.semantics)),
    ("an existential with the condition after the claim", ← `(∃ k : ℕ,
          Circuits.RL.family.chain = Circuits.RL.family.semantics ∧ k ≤ 2)),
    ("an existential with a condition and no claim",
      ← `(∃ k : ℕ, k ≤ 2 ∧ LinearSystems.IsHurwitz !![(-1 : ℝ)]))]
  for (label, stx) in controls do
    if (← Architecture.rejection ctx (← elabProp stx)).isNone then
      throwError "Public admission accepted its grammar-extension control: {label}"
  logInfo m!"POWERLIB_CLAIM_EXTENSION_OK: 4 positive claims (type parameters, binders over \
    Type, a numeric iff, a guarded existential); {controls.size} rejection controls"

end ConnectionAdmission
