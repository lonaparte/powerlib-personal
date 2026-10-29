# PowerLib Rules

These rules define what PowerLib admits, how results are checked, and what its
automation claims mean. They apply to the library, bridges, synthesizers,
discovery tools, examples, tests, and public documentation.

## 0. Meta-rules

Six meta-rules fix the form of the library. Every later section applies one of
them or filters what they admit, and says which.

| | Meta-rule | Enforced by |
| --- | --- | --- |
| M1 | **One semantics.** Behaviour is a continuous-time or discrete-time system with ports, or a random continuous-time system with an operating envelope, interpreted once by `Sentence.holds`. | single-semantics audit; `BARE_BEHAVIOUR` |
| M2 | **One connection shape.** A TMIO seed supplies one arbitrary-infimum-preserving backward map per adjacent edge; adjoints, closures, composites, denotations, exactness and soundness are generated. A family supplies only its system map, requirement satisfaction and translation. | the types `TMIO.Seed`, `Family`, `Implementation`, `Stack` |
| M3 | **One public conclusion.** A public model conclusion is `connection% P`, a statement of the closed grammar `TMIO.ConnectionClaim`. | kernel-checked certificate; whole-package admission; bypass audit |
| M4 | **Scaffold first.** A connection between contents (two model families, a model and its implementation, a model and its records, two representations) is first built as an Agda scaffold, then proved in Lean in the generality the scaffold fixes; the Lean module cites the scaffold. | `SCAFFOLDS` |
| M5 | **Generic once.** A law about arbitrary families or fields is proved once, in a generic module that imports no engineering module; instances supply only their obligations and do not restate it. Upstream results are reused, not reproved. | `DEPENDENCIES`, `DUPLICATES`, `RESTATEMENTS` |
| M6 | **One trust root.** The Lean kernel with the axioms `propext`, `Classical.choice` and `Quot.sound`. Agda, synthesizers, solvers, scripts and the elaborator are untrusted. | axiom audit; admission |

The checks are the library structure test (`dependencies/tests/lean/Library/Structure.lean`) and
the admission tests (`dependencies/tests/lean/Architecture/`). The meta-rules fix the form of the
library, not its content: which models and conclusions it contains is chosen from the sources each
module header cites.

## 1. Agda scaffolding and the Lean 4 theorem layer

*Applies M4, and M6 for what Agda cannot establish.*

Agda is the scaffolding between the different contents of the library: models,
representations and layers. Every connection between them is first constructed
in Agda, which fixes the statement of the connection, its generality, and the
structure it must preserve. Lean 4 is the only theorem layer. It proves every
connection independently, and every formal result exposed by PowerLib, foundation
or domain, is a named theorem checked by the Lean kernel. The library builds and
checks without Agda. An Agda proof is not a PowerLib theorem and cannot replace one.

A connection is built in three steps:

1. The Agda scaffold states the two contents, the equivalence or relation between
   them, and the structure it preserves. For an equivalence of representations,
   univalence transports every construction along it, so the scaffold fixes the
   general statement, and the operations the equivalence must preserve are what
   Lean has to prove. For a relation that holds only for some sentences, under
   constraints or in one direction, the scaffold records the shape of the
   connection (relation, sentences, constraints, direction, composition); its
   analytic content is proved in Lean alone.
2. Lean proves the connection, in the generality the scaffold fixes, by its own
   means.
3. The scaffold stays in `theorem/` as the design record of the connection, and the
   header of the Lean module cites it. Only data passes between Agda and Lean (§11).

The scaffold table of [Architecture.md](Architecture.md) is the registry: one row per
scaffold, naming the Lean modules that prove its connection. The `SCAFFOLDS` check
recognizes a connection from a public statement that uses two model families, an
implementation or stack, or an observation seed, or that changes the representation inside
one family (an iff or an equality with that family's denotation of one sentence on both
sides, at different models); the module must cite a scaffold whose row names it. Every
scaffold is cited by a Lean module and has a row. A scaffold's comments cite only public
Lean declarations and library modules, and the check resolves every such name: a step
proved by a private lemma is cited through the public theorem whose proof contains it.

A scaffold is named after the contents it connects: a reading of one family through
another after the two families (`DroopSwing.agda`: the droop loop read as a swing
machine), a change of representation after the representations or the change
(`Conversion.agda`, `Rebase.agda`, `CurrentDirection.agda`), a realization after its
implementation (`ExactSampling.agda`, `DigitalCurrentLoop.agda`), records after the
model and the observation (`RLMeasurement.agda`). One scaffold records one connection. A
construction shared by several connections is a scaffold of its own, named after the
construction (`FamilyReading.agda`, `Realization.agda`, `Records.agda`), and content
shared by several readings of one hub is named after the hub (`Swing.agda`).

Markdown derivations, Python computations, Mathematica or SymPy results,
numerical experiments, and Agda-only proofs are not admitted theorems.

## 2. Formalization directory

*Filter (M6): what counts as library source.*

The active visible source directories are `theorem/`, `example/`, and
`dependencies/`. `theorem/` contains formalization source and checked generated
formalization source, with no Markdown files. `example/` contains formal public
consumers. Necessary kernel, discovery, and automatic-reuse consumers belong in
`dependencies/tests/`; pinned integration profiles belong in
`dependencies/integrations/`. Procedural or redundant tests and research notes
stay in the local workspace outside the repositories. A result not yet expressed
as a Lean theorem is a research note, regardless of its mathematical plausibility.
Directory structure must enforce this distinction.

## 2a. Knowledge units and external observations

The core admits exactly five kinds of knowledge unit: **T**, **M**, **T–M**,
**M–I** and **I–O**. T contains general mathematical theory; M contains model
definitions and their internal structural facts. T–M relates sentences to models
and their requirements. M–I relates designs to realizations under stated
constraints. I–O specifies the interface between a realization and external
observations. I and O are endpoints of relations, not independent knowledge units.

The types of implementations and observations, and the definitions needed to
state their relations, belong to those relations. A mathematical model of an
implementation may itself be M in another connection: the role is relative to
the connection, not a permanent classification of its carrier type. General
composition laws belong to T; derived paths use the three admitted relation kinds
without introducing T–O or M–M as additional unit kinds.

Concrete measurement records and results are not core knowledge. Keep record
types, compatibility or production interfaces, and theorems quantified over
arbitrary external observations. Do not store a fixed observation or publish a
conclusion specific to its measured values. Mathematical constants, normalized
models, and exact witnesses or certificates needed to prove general results are
not measurement records and are reviewed according to their mathematical role.

The generic/engineering module partition and foundation/domain metadata are
independent of these five kinds. Supporting definitions, private proofs and
metaprogramming infrastructure support admitted units rather than forming a
sixth knowledge kind.

Each public typed connection theorem in `theorem/` carries exactly one source
attribute: `@[tmio T]`, `@[tmio M]`, `@[tmio TM]`, `@[tmio MI]` or `@[tmio IO]`.
These attributes are the sole source of classification; queries reconstruct an
index from them, and no separate classification table is maintained.
Combine existing attributes in the same block, for example
`@[tmio TM, powerlib_domain]`; consecutive `@[...]` blocks are not valid Lean syntax.
`theorem/TMIO/KnowledgeKind.lean` checks that an attribute targets a theorem,
uses one of the five kinds, and is not assigned twice. The assigned kind records
review of the complete statement and its hypotheses; the attribute checker does
not prove that semantic judgment or replace mathematical admission.

The current reviewed coverage is 2,925 theorems: T 1,701, M 335, T–M 760, M–I 102
and I–O 27, including 111 private helpers. This includes all 1,043 public
`connection%` theorems (T 102, M 52, T–M 760, M–I 102, I–O 27) and 1,882 individually
reviewed ordinary theorems. Module-level role suggestions do not assign a kind to
every declaration in a module. The remaining 4,959 theorems are unclassified;
definitions are outside this theorem-attribute inventory.
The required missing-label check is limited to public typed connection theorems;
every explicit attribute, including one on an ordinary or private theorem, is checked.
`Layers.md` gives the Lean environment queries and the source-only queries.

## 3. Foundation results and domain results

*Applies M3 and M5.*

Foundation results include algebraic identities, conversion involutions,
representation equivalences, transport laws, and auxiliary lemmas. They may
be proved manually and are checked by the Lean kernel; an Agda scaffold may have
established the same fact first (§1). Not every lemma requires synthesis.

Domain results express engineering conclusions about power systems or power
electronics, such as small-signal stability, impedance stability, or closed-loop
exponential stability. They require final Lean theorems about the formalized
system. Foundation evidence must not be presented as a domain conclusion.

`@[powerlib_foundation]` and `@[powerlib_domain]` are optional discovery and
presentation metadata. They do not grant admission or exempt a declaration from
checking. Only an explicit annotation assigns one of these classifications: a typed
`TMIO.Statement` neither implies domain nor overrides foundation. Unannotated
connection statements remain unclassified in this registry; connection discovery
and admission still inspect their types independently. Simp, ext and Aesop
registration remain independent decisions.

Generic static lemmas, semantic implications and certificate arithmetic are
foundation results. Generic connection laws — laws about arbitrary families stated
as connections, such as the explicit Euler template or the hub transfer laws — may
remain foundation results. These connection statements retain their generic
family parameters and are stated once; an instance applies
them to its family's static evidence (autonomy, smoothness of its field) and
publishes only what carries its own content. A model family's public engineering
conclusion must be a domain theorem on a connection: an evaluation of its
generated space, a comparison of connections, or a boundary witness. Relabeling
such a conclusion as foundation does not complete its public domain interface.

## 3a. Generated connections and public conclusions

*Applies M2 and M3.*

The TMIO chain has four ordered endpoints; the core's knowledge units are those
of §2a. A seed supplies one
arbitrary-infimum-preserving semantic map per adjacent edge; the forward
adjoints, complete implementation spaces, closures and composites are generated.
Do not supply a second independent forward map or implementation space.

A family supplies its system map, requirement satisfaction and translation.
Its semantics connection generates sentence denotations. Exactness compares the
translation chain with that semantics connection; soundness orders them. These
comparisons and their propagation belong to the generic framework.

There are two admission rules:

1. A connection stores an arbitrary-infimum-preserving backward map. Its forward
   adjoint is generated; an independently proposed adjoint must prove the Galois
   law and therefore equals the generated map.
2. A published connection result carries a `TMIO.ConnectionClaim` certificate in
   its proposition type (`TMIO.Statement`). The closed grammar admits endpoint
   evaluations, connection comparisons and boundaries. It has no constructor
   injecting an arbitrary `Prop`. Use `connection% (ordinary proposition)` to
   construct the certificate; Lean's kernel checks both it and the theorem proof.
   Premises are unrestricted. Side conditions are comparisons of numbers (`≤`,
   `<`, `=` in ℕ, ℤ, ℚ, ℝ, combined by `¬ ∧ ∨`) and enter a conclusion only as the
   characterizing side of an iff (`C ↔ n ≤ 1`) or as the guard of an existential
   witness (`∃ h₀, 0 < h₀ ∧ C`). A claim may bind types (`∀ X : Type, …`, or type
   parameters of the theorem). Certificate universes are inferred from the actual
   endpoints; one claim can combine both directions of the same pair of endpoint
   universes. Extensional equality of functions, bundled lower adjoints and closure
   operators requires a connection certificate at every argument. Quantifiers can use
   either endpoint universe. Generic declarations retain their `Type*` parameters. The external
   theorem telescope is checked separately, rather than re-encoded as part of the
   conclusion's certificate.
   Equality of two `Seed`s compares their three supplied upper maps, retaining four independent
   carrier universes. Equality under a common constraint, `s ∩ d = t ∩ d`, requires an endpoint
   certificate for `s` or `t`; its equivalent pair of inclusions
   `s ∩ d ⊆ t ∧ t ∩ d ⊆ s` may characterize that same equality. The context `d` restricts the
   comparison domain. It does not make arbitrary intersections endpoints, admit differing
   contexts, or permit unrelated conjuncts. The behavioural bypass check still inspects it.

`TMIO.Endpoint` certificates are built from typed `sInfHom` applications,
`generate`, generated closure, and structural powerset operations. Endpoint
metadata cannot substitute for these certificates. A connection only in a
hypothesis or an unrelated conjunct cannot satisfy the closed grammar. Behaviour
of a concrete model is reached through these endpoints, never through a direct or
aliased behavioural conclusion or operand.

The bypass check inspects endpoint inputs, structural maps, and hypothesis types.
An identity connection applied to a raw behavioural set cannot hide that set
behind the otherwise valid connection.

Generic semantic interface laws may relate an arbitrary `Family` to the library's
semantic predicates, such as `holds` and `reach`. Their conclusions must still
carry the complete connection certificate, actually depend on that arbitrary
family, and have no concrete model dependency, including through value aliases.
They retain the semantic-layer checks against raw signals, discrete evolution and
ambient behavioural predicates. A foundation label or an unused family parameter
does not grant this interface allowance.

Whole-package admission discovers model-domain types from actual `Family`
definitions. Every public model-specific behavioural proof must use Statement,
even without foundation/domain metadata, when labeled foundation, or when written
as a proof-valued definition.
Generic semantic support and private helpers remain implementation evidence;
ordinary non-connection theorems are outside the current required `tmio` coverage.
Negative behavioural fixtures are private evidence explicitly submitted to
rejection tests.

The public entry points `lake build` and `lake build powerlib` first check source
classification with `python3 tools/tmio_classification.py check`, then build every
module selected by the package's actual Lake library globs and audit that complete
inventory. The environment check requires a `tmio` attribute on each imported
public typed connection theorem in a `theorem.*` module. A file cannot opt out by
omitting an Architecture import or by being absent from `powerlib.lean`.
Examples, tests and the independent integration
profile use the same admission checker. Raw `lean` or a staging-library target
is compilation, not PowerLib admission. Changing the trusted build configuration
can bypass policy; the kernel alone cannot forbid arbitrary valid Lean theorems.

An inconsistent requirement context may give a sound empty translation space.
Report it as unavailable translation coverage, not as evidence that the sentence
has a usable translation. Adjoint generation, translation exactness and
algorithmic synthesis completeness are separate claims and require separate
evidence. Preserve UNPROVED until a kernel-checked proof or refutation exists.

## 4. Explicit model boundaries

*Filter on M3 conclusions: the boundary of every domain theorem.*

Every domain theorem must precisely identify the system it concerns. State
its state variables and their order, coordinate frame, parameter ranges, inputs,
controller and feedback signs, whether delay, PWM, or PLL dynamics are included,
whether time is continuous or discrete, and whether it concerns an equilibrium
or linearization around a trajectory.

A theorem about an ideal three-state LCL plant must not have a name or public
description that implies stability of a complete grid-connected converter.
Excluded components and idealizations are part of the model boundary.

## 5. Formalize the system before its calculation

*Applies M1: behaviour belongs to the formalized system.*

Represent the engineering model itself formally. Construct state-space models,
impedance descriptions, closed-loop matrices, or other derived objects from
that model, then prove their relationships to the intended system.

Importing a previously calculated characteristic polynomial, LMI, or stability
condition and proving only that final algebraic condition is insufficient.
The formal chain must connect the original model to the derived objects and
the final engineering property.

## 6. Semantic completion

*Applies M1 and M3.*

Determinant positivity, a Routh-Hurwitz condition, a determinant identity, or
`A^T * P + P * A = -I` is intermediate evidence. Certificate arithmetic is not
the completion criterion.

The completed result must conclude a meaningful system property, for example:

```lean
@[tmio TM] theorem stable :
    connection% (submittedModel ∈ family.den (.flow .lyapunovStable))
@[tmio TM] theorem exponentially_stable :
    connection% (submittedModel ∈ family.den (.flow .globallyExponentiallyStable))
```

The relevant stability predicate must describe the formalized system, with
its interpretation and assumptions established through the family's system map.
PowerLib must not present a
successful certificate check as proof of an engineering theorem unless the
semantic theorem has also been derived and kernel-checked.

## 7. Synthesis is the default ATP target

*Filter: the maturity of ATP claims (§14).*

ATP-facing domain results default to S-level: the system receives a problem
description or model without the missing witness and automatically finds the
witness or certificate, then Lean derives the semantic theorem.

An input that already supplies a Lyapunov matrix, controller gain, SOS
decomposition, or other sought answer supports certificate verification. It
does not demonstrate synthesis of that answer.

For example, submitting only `R = 2` and `L = 1`, automatically obtaining
`p = 1/4`, and having Lean derive the resulting theorem is synthesis. Having a person supply those witness values is verification.

## 8. The synthesizer is untrusted

*Applies M6.*

Python, an LLM, an SMT or SDP solver, a CAS, a search procedure, or a neural
network may propose witnesses. None belongs to the trusted computing base.
An arbitrarily wrong proposal must lead at most to rejection; it must never
compromise the soundness of admitted results.

## 9. Independent reconstruction of the submitted model

*Applies M6.*

The checker must independently reconstruct the target model from the original
submission. It must not trust a certificate's claimed model, success flag,
theorem name, or proof path.

Certificates must be tied to the exact submitted model. A witness or proof for
a different model must not be admitted as the submitted model's certificate.
The model-indexed certificate types, such as `Linear.Certificate` of the state
matrix that a family's plant map reconstructs from the submission, and the
independent admission target are the pattern for every family. A witness that genuinely satisfies the
obligations for several models can be checked anew for each model; an earlier
acceptance for one model cannot replace checking another.

## 10. Kernel trust and proof escapes

*Applies M6.*

Final proof trust comes only from the proof kernel. No admitted theorem may
transitively depend on `sorry`, `admit`, `sorryAx`, a custom unapproved axiom,
or a mechanism that escapes kernel checking. The Lean axiom allowlist is:

```text
propext
Classical.choice
Quot.sound
```

Admission must automatically audit transitive dependencies. A textual scan or
manual inspection is insufficient. Use the existing `Lean.CollectAxioms`
admission audit and `#print axioms` for inspection. Intentional negative test
inputs must remain rejected and must never become public theorem dependencies.

Use Lean attributes such as `@[simp]` and `@[ext]` for their intended automation
roles, so reusable library facts have a standard interface. Attributes do not
replace kernel checking, and not every theorem should be a simplification rule.

## 11. A narrow Agda-to-Lean bridge

*Applies M4 and M6: the only data path from a scaffold to Lean.*

The bridge exports a limited, versioned, structurally specified, machine-checkable
data representation of an Agda-checked executable operation. Lean independently
checks the exported endpoint contract and its concrete instantiation.

There is no assumed general translation of Agda proofs to Lean. An Agda proof
does not authorize unconditional acceptance by Lean. A restricted versioned wire
interface is the institutional pattern.

The exported modules in `theorem/generated/` keep their provenance comments (the
Agda source and its SHA-256) as the first lines and carry a library module docstring
after their imports, like every other module. Regenerating one must keep both: the
generator emits the data, the docstring is maintained with the module.

## 12. Exact acceptance

*Applies M6.*

Prefer exact checking of integers, rational numbers, and symbolic expressions.
Floating-point values, numerical eigenvalue calculations, and ordinary SDP
outputs cannot directly establish strict proofs.

When numerical methods are used for discovery or synthesis, produce additional
kernel-checkable evidence such as rigorous error bounds, interval certificates,
or rational reconstruction. Numerical search remains outside the trusted base.

## 13. Public admission and provenance

*Filter (M3, M6): admission and provenance.*

One successful Lean compilation does not automatically admit a result to the
library. An admitted theorem requires a stable name and namespace, explicit
provenance, reproducible construction with pinned dependencies, and access
through the unified public interface. For example:

```lean
import powerlib
#check powerlib.Circuits.LCL.exact_hurwitz
```

A theorem generated temporarily in `results/.../Certificate.lean` is a proof
artifact, not automatically a library theorem. A library theorem may state a
general certificate-to-property implication; generated artifacts instantiate
that implication for a submitted model.

Track original input/model identity, theorem names, dependency and kernel
versions, Agda source hashes, wire interface/version and normalized data,
generated Lean source hashes, certificate proof hashes, and verification logs.
Hashes establish artifact identity, not mathematical correctness.

## 14. Result maturity and discovery claims

*Filter: how results and claims are labelled.*

| Status | Meaning and required evidence |
| --- | --- |
| Note | Nonformal derivation, computation, or experiment; no admitted domain claim. |
| Foundation | Kernel-checked Lean infrastructure such as conversion, equivalence, or algebraic lemmas. An Agda scaffold is a design record, not a foundation result. |
| Lean theorem | A formally modeled domain conclusion expressed as a public, kernel-checked Lean theorem. |
| S-level | Witness-free input leads to automatic witness synthesis, kernel-checked certificate admission, and a final semantic Lean theorem. |
| ATD-discovered | The system also generates the conjecture itself and proves or refutes it; the conjectures were not manually fixed in advance. |

These statuses describe evidence, not interchangeable labels. Report achieved
maturity and outstanding gaps explicitly. Do not label an uncompiled source
file as a verified theorem, a supplied-witness check as synthesis, or a fixed
list of three candidate conditions as complete theorem discovery.

Proof search failure is `UNPROVED`, not `REFUTED`. Refutation requires its own
kernel-checked counterexample or negation theorem. ATP returns `ACCEPTED` only
after model-bound admission, the semantic theorem, and the axiom audit pass.

The current manually enumerated ATD examples are fixed-candidate verification
prototypes. Complete ATD remains an objective until conjecture generation,
formal proof/refutation, traceability, and library admission are all implemented.

## 15. Reuse Mathlib and LeanForControl

*Applies M5 across libraries.*

PowerLib follows the reuse principle of LeanForControl. Check Mathlib and
LeanForControl for existing formalized results before developing new proofs.
Directly import and apply their existing theorems whenever their assumptions
and conclusions match the required result. Do not duplicate those proofs in
PowerLib. Keep new formalization focused on missing results, formal models,
and the connections needed to apply existing theorems to those models.

Project-specific wrappers may provide stable public names, model-specific
contracts, and discovery attributes while invoking the upstream theorem.
Any additional assumptions or model conversions required for that application
must themselves be stated and checked.

Reused results remain subject to the same kernel checks, transitive axiom
allowlist, and provenance requirements as local proofs. Pin imported
dependencies to compatible versions and verify them in the reproducible build.

Automation must search the types of actual imported Lean declarations, including
upstream theorems without PowerLib attributes. Use the standard library-search
index to find relevant applications from a goal, and preserve the original
declaration name, defining module, universe parameters, assumptions, and axiom
dependencies. PowerLib foundation/domain labels classify its own named theorems;
they are not prerequisites for reusing an upstream theorem. A documentation or
blueprint annotation does not establish a proof or a searchable semantic contract.

Reject candidates whose transitive dependencies violate the axiom allowlist,
and audit the completed proof independently. Automatic application must discharge
the theorem's actual hypotheses; matching prose or model names is insufficient.
Do not describe a library as connected until a compatible pinned dependency is
imported and direct reuse has passed kernel checks. A version mismatch requires
a separately verified compatibility change before that dependency can be used.

## 16. Formal theorem dependencies

*Applies M5 and M6 to dependencies.*

`dependencies/` is the formal interface to the upstream results PowerLib uses.
Its Lean import interfaces directly import Mathlib or LeanForControl modules.
First-party adapters, wrappers, and new or modified theorem proofs belong in
`theorem/`; importing upstream theorems does not copy their proofs. Preserve
the actual upstream theorem, defining module, assumptions, version, and
transitive axioms. Do not copy upstream proofs
into PowerLib or replace their import with a local reimplementation. Lake resolves
dependency package sources from the pinned manifest. Full upstream checkouts
live beside the repository as `../mathlib/` and `../LeanForControl/`. Keep them
outside the repository; they must not be committed or promoted. The project
commits its portable Lake configuration and fixed dependency versions.

A demonstrated upstream version mismatch may require a minimal exact
compatibility diff in `dependencies/`. Keep the actual upstream revision pinned,
preserve theorem statements and direct imported theorem reuse, and audit the
effective source diff before compiling it. Record the original pin, compatibility
diff identity, and checked effective source identity in provenance. Do not vendor
full upstream proofs. Kernel, semantic, automatic-reuse, rejection, and transitive
axiom checks still apply to every reused result.

Necessary formal verification consumers belong in `dependencies/tests/`.
They check the public interface, kernel and transitive axiom audit, registered
theorem discovery, automatic reuse, or required semantic acceptance boundaries.
Pinned formal integration profiles and their build configurations belong in
`dependencies/integrations/`. Keep those profiles independently scoped; the main
library must not recursively build their sources or negative fixtures. Procedural
and redundant test support stays in the local workspace outside the repositories.

Bootstrap programs, Python synthesizers, bridge exporters, admission runners,
procedural regression harnesses, normalized wire artifacts, temporary generated certificate
artifacts, logs, and local development support do not belong in `dependencies/`
or elsewhere in the active published library. Model-specific foundations and
domain results belong in `theorem/`; formal public examples belong in `example/`.
A dependency interface must not imply that an incompatible upstream library is
available through the main public import.

The active published library contains formal sources, necessary formal
verification consumers, and pinned build configuration. Local bootstrap and
orchestration programs, bridge exporters, untrusted synthesizers, artifact
admission runners, their procedural regression harnesses, and their input/output
artifacts stay in the local workspace outside the repositories. A local program's
output is not an admitted library result. Keep independent kernel checks and
retained provenance when reorganizing support. Historical archive content is
preserved in the local workspace outside the repositories and remains excluded
from public build, discovery, admission, and promotion.
