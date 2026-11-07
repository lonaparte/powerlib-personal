# PowerLib Architecture

The architecture is described here; [Rules.md](Rules.md) specifies admission and
contribution requirements, and [Changelog.md](Changelog.md) records completed changes.

## Physical organization

Engineering sources are grouped by equipment class: grid-tied converters, electric drives,
power systems, passive components, grid structure, and numerical simulation. Further classes (MMC, DC systems,
resonant converters) get a directory of their own when their first module is added. Mathematical
sources are grouped by topic. Directory names do not assign `tmio`, foundation/domain, or
connection status to declarations.

```text
powerlib.lean                 public Lean import
theorem/
  TMIO/                      generated connections, claim grammar and classification
  Family/                    model families and semantic readings between families
  Stack/                     realization and production interfaces
  Flow/, Map/, Port/         the shared behavioural semantics
  Linear/                    linear systems, certificates and coordinate laws
  LTI/                       time evolution and sampling of linear systems
  Spectral/                  spectral criteria and family interpretation templates
  PH/                        general port-Hamiltonian theory
  Estimation/                estimation theory and symbolic resistance fitting
  Transform/                 coordinate and unit transformations
  GridTiedConverter/         grid-tied converters
    GFL/, GFM/, PLL/         grid-following, grid-forming (Limiting/: current limiting), PLL
    CurrentControl/          converter current loops
  Drives/                    electric machines and drives
  PowerSystem/               power systems
    Synchronous/             synchronous machines, swing equation, equal area
    Network/                 multi-machine networks, power flow, synchronization
    Frequency/               frequency response and control
  Passive/                   passive components: RL branch and GC shunt (also in dq), LCL filter,
                             RLC and LC PH instances (PH/), lines and cables (Line/)
  Grid/                      grid structure: source–load interconnection, RL networks, grid
                             impedance seen from a converter, power flow, shared network nodes
  Numerics/                  numerical methods; EMT/ electromagnetic-transient simulation
  ...                        other mathematical topics
  generated/                 checked data generated from Agda
  Architecture.lean          public-interface admission checker
  Attributes.lean            foundation/domain metadata and provenance
  LibrarySearch.lean         theorem discovery and reuse checks
tests/lean/                  architecture and library verification
example/                     formal library consumers
dependencies/                upstream import interfaces and compatibility patch
  integrations/              pinned standalone integration profiles
tools/                       source inspection tooling and its Python tests
```

Agda scaffolds live beside the Lean sources for their topic. Shared scaffolds
remain with the general construction: family readings in `Family/`, realizations
and record interfaces in `Stack/`, numerical bridges in `Numerics/`. The Agda
module name follows its physical path. Lean import paths likewise follow files;
public declaration namespaces need not change when a file moves.

`Linear/` supplies general linear-system mathematics; `LTI/` specializes the
evolution and sampling interfaces; `Spectral/` organizes spectral criteria into
family semantics. A reading between arbitrary families lives in `Family/` even
when a spectral family is one of its applications. General PH constructions live
in `PH/`; RL, RLC, DC-link and LC-filter instances live in `Passive/PH/`. A passive component's
own properties (impedance, state equation, stored energy, dq form) live once in `Passive/`; the
way components are connected (interconnections, networks, the grid seen from a converter) lives
in `Grid/`. The two first-order elements have one definition each, with their decay rate,
immittance, stored energy and power balance: the series branch `Passive.RL` (`Passive/Branch.lean`)
and its dual, the shunt `Passive.GC` (`Passive/Shunt.lean`). Their dq immittance matrices, the dq
capacitor law and the dq power balance are in `Passive/Dq.lean`. Every model containing such an
element carries it as a field and uses those laws instead of restating them: the impedance model,
the dq branch, current-loop plants, converter filters and lines, a machine link, RL-network
branches and nodes, DC links with their loss conductance, filter capacitors and loads, the
series RLC loop, and the unit length of a transmission line (series `Passive.RL`, shunt
`Passive.GC`). `Grid/` only connects them (for example `Grid/GridImpedance.lean`: a line branch
in parallel with a shunt).

## Knowledge nodes and relations

The core admits exactly five kinds of knowledge unit: T, M, T–M, M–I and I–O.
T contains general theory and its internal theorems; M contains mathematical
models and their internal structural facts. The other three kinds relate
sentences to models, models to implementations, and implementations to external
observations, respectively. There are no standalone I or O knowledge units.

`TMIO.Seed` still fixes the mathematics of four ordered endpoints, with one
infimum-preserving backward map per adjacent edge and uniquely generated forward
adjoints. Endpoint roles must not be confused with independent library contents.
Implementation and record types are interface definitions owned by relations;
concrete measurement records and numerical measurement results are external.

## Endpoint roles

| Layer | Objects | Changes when |
| --- | --- | --- |
| T, theory | General mathematical theory, properties and their laws. The model-facing language is `Sentence`: flow properties, passivity and envelope properties. | The mathematics changes. |
| M, model | The theory organized for a concrete situation. A model is an idealized description of one situation (topology, control law, parameters); its behaviour is given exactly by the semantic layer. A requirement language describes classes of models and organizes the theory over them. | The modelling changes for the same theory. |
| I, implementation | A model under realistic constraints: experimental platforms and test rigs, sampling and computation delay, sensor and actuator dynamics, quantization, limits the design did not intend, parameter tolerances, disturbances, numerical integration. An implementation has its own behaviour, read by the same semantic layer, which in general differs from the behaviour of the model it realizes. | The conditions of realization change for the same model: platform, digitization, simulation method. |
| O, observation | Records produced by implementations: sampled waveforms, frequency sweeps, identification results, with their measurement errors. A record has no behaviour of its own. | The run or the sensor changes for the same implementation. |

Boundary cases follow from design intent. A designed current limit, an averaged model and
nominal parameters belong to M. A hardware limit, the switched circuit, an EMT discretization and
a tolerance set belong to I.

Theory-driven work runs forward along the chain: from sentences to the models that satisfy them,
to the implementations whose models all satisfy them, to the records those implementations
certify. Data-driven work is the complete backward traversal: from records to the
implementations that may produce them, to the models they realize, to the sentences all those
models satisfy. The whole-chain Galois connection ties the two directions together: a set of
records supports a set of sentences exactly when every record is certified for them.

## The Lean interface

Two structures carry the layers. An `Implementation X Q Y R n p m q`
(`theorem/Stack/Implementation.lean`) is the T–M–I part:

* `model : Family X Q n p`: models `X` with their requirement language `Q` and translation;
* `impl : Family Y R m q`: implementations `Y` with their own system map, and the requirement
  language `R` of their realistic constraints;
* `realizes : SetRel X Y`: the implementation realizes the model (for a design map,
  `Implementation.ofDesign`).

A `Stack X Q Y R V n p m q` (`theorem/Stack/Basic.lean`) extends an `Implementation` by
`produces : SetRel Y V`, the implementation may produce the record.

| Operation | Meaning | Lean |
| --- | --- | --- |
| Composite through the realized models | Sentences every model realized by the given implementations satisfies | `Implementation.uTI` |
| Realization soundness | Within constraints `Δ`, an implementation whose realized models all satisfy `s` satisfies `s` | `RealizationSoundUnder Δ s` |
| Realization completeness | Within `Δ`, an implementation satisfying `s` realizes only models of `s` | `RealizationCompleteUnder Δ s` |
| Realization exactness | Both: within `Δ`, an implementation satisfies `s` exactly when its realized models do | `RealizationExactUnder Δ s` |
| Data-driven inference | Sentences satisfied by every model realized by a possible producer of the records | `Stack.infer` (`seed.uTO`) |
| Theory-driven certification | Records all of whose possible producers realize only models of the sentences | `Stack.certified` (generated `uTO`) |
| Inference through the requirement language | The same, checking the translation instead of the semantics | `Stack.inferOrganized`, `Stack.certifiedOrganized` |
| Implementation truth | Sentences satisfied by every possible producer itself | `Stack.truth` |
| Prediction | Records some implementation satisfying `s` may produce | `Stack.predicted` |

The seed `Stack.seed` has the semantic maps `model.semantics`, `possibly realizes` and
`possibly produces`; the organized seed `Stack.organized` replaces the first map by the
translation chain `model.chain`, the theory as the requirement language organizes it.

Realization soundness compares two connections from sentences to implementations, the
composite through the realized models (`uTI`) and the implementations' own semantics, just as
the soundness of a translation compares the translation chain with the semantics one layer up.
It reduces to static obligations on requirements
(`Implementation.realizationSoundUnder_of_requirements`): an exact model translation, a sound
implementation translation, and an implication between the two requirement languages. A
realization by a design map whose implementation denotation is the model denotation pulled back
is exact (`Implementation.realizationExactUnder_of_den_eq_preimage`).
Data-driven inference reaches conclusions about the realized models. They become conclusions
about the producing implementations through realization soundness, for records certified for the
constraints (`Stack.infer_true`, `Stack.infer_subset_truth`), and completeness gives the converse
(`Stack.mem_infer_of_truth`). A record outside the predicted records refutes the sentence for its
producers (`Stack.refutes`) and, through realization soundness, for some realized model
(`Stack.refutes_realized`). Sound translations let inference use the requirement language
(`Stack.mem_infer_of_organized`, `Stack.certifiedOrganized_subset`).

## Placing knowledge units

* **T**: general mathematics, semantic laws, numerical and estimation theory, and
  generic connection composition or transport laws. Framework infrastructure supports
  these units; it is not an extra knowledge category.
* **M**: models, parameter and requirement languages, algebraic structure and changes
  of model representation. A platform's mathematical description can be M as well.
* **T–M**: interpretation of sentences in model families, parameter criteria,
  translation soundness/exactness and preservation of this interpretation under a
  model reading. A model mapping itself is M; a theorem about its interpretation is T–M.
* **M–I**: realization relations and their conditional soundness, completeness,
  exactness and boundaries. Endpoint models and requirements support the relation;
  their carrier types do not acquire a permanent I classification.
* **I–O**: production or compatibility interfaces for arbitrary external observations,
  and their inference, certification and prediction laws. Records are parameters,
  not stored measurements. Whole-chain results compose T–M, M–I and I–O; they do
  not create independent O or T–O knowledge units.

The legacy `Family.seed` encoding places requirement sets and model instances in
its middle positions; both are on the M side of the interpretation. It does not
establish a physical realization merely by occupying the third Seed position.
In `Passive/RLMeasurement`, `reading` is a model-side compatibility criterion
for a symbolic resistance estimate. Its constraint calculations belong to M and
its sentence criteria to T–M. A genuine I–O reading would additionally require an
implementation and a justified production interface; that connection is not claimed.

The generic/engineering dependency partition does not determine theorem metadata.
Generic modules can contain engineering instances; engineering directories can contain
general T lemmas. Foundation permits T, M and TM; domain permits M, TM, MI and IO.
M and TM may belong to either class according to whether the selected object is a
mathematical model or an engineering model. Classify the complete
statement and its hypotheses, not just the directory or the type of one endpoint.
In particular, general coordinate-change laws are foundation, while properties of
the chosen abc/αβ/dq Clarke and Park transforms are domain. Quantifying over arbitrary
vectors does not make a theorem about one selected electrical transform generic.
Their model formulas belong to M; an M–I claim needs an actual realization relation.

The semantic layer reads three kinds of systems (`Behaviour`): continuous-time systems with ports
(`theorem/Flow/Defs.lean`, `theorem/Port/Defs.lean`), discrete-time systems with ports
(`theorem/Map/Defs.lean`), and random continuous-time systems with an operating envelope
(`theorem/Port/Defs.lean`, `disturbed`). A digital controller, a sampled-data loop read at its sampling instants
(`LTI/Sampling`), and the period map of a switched converter (`Averaging/SwitchedStability`)
can describe discrete-time engineering implementations. A generic numerical integration or
sampling scheme is a mathematical model; its interpretation does not alone establish MI.
State-dependent hybrid switching is outside this semantic interface. The random kind
uses a continuous-time system for each disturbance sample; it is not an Itô SDE interpreter.
Discrete stability is read through map iterates; decay rates also depend on the sampling period.

## Source attributes and queries

A theorem carries its knowledge kind as one of `@[tmio T]`, `@[tmio M]`,
`@[tmio TM]`, `@[tmio MI]` or `@[tmio IO]` beside its declaration. The attribute
is the only source of its classification. There is no separately maintained
catalog; an index is reconstructed when queried. Classification considers the
complete statement, including its hypotheses and the relative roles of its
endpoints.

For example, `@[tmio TM, powerlib_domain] theorem ...` records both classifications.
The declaration and compatibility rules are in [Rules.md](Rules.md#2a-knowledge-units-and-external-observations).

`theorem/TMIO/KnowledgeKind.lean` defines the attribute and checks its theorem
target, allowed kind and unique assignment. These checks do not decide whether
the chosen kind correctly describes the mathematics. `theorem/Attributes.lean` additionally
rejects foundation + MI/IO and domain + T at module boundaries and in environment audits,
including private theorems and delayed attributes. M/TM are valid with either metadata label.
Neither metadata label requires or follows from a kernel-checked `connection%` statement.

The queries below compute current coverage and category counts from the attributes,
including reviewed private helpers and ordinary theorems. No separate count or
theorem inventory is maintained. A module's role does not assign a class to its declarations.

`theorem/TMIO/KnowledgeIndex.lean` queries the attributes in the currently imported
`theorem.*` modules:

```lean
import powerlib
import theorem.TMIO.KnowledgeIndex

#tmio_theorems    -- All explicitly classified authored theorems, including private ones.
#tmio_theorems T  -- List classified theory theorems; arguments are T, M, TM, MI and IO.
#tmio_edges       -- Counts restricted to public typed connections.
#tmio_edges TM    -- List T–M connections only.
#tmio_check       -- Check connection coverage and report all classified theorems.
```

These commands cover only imported modules. A missing attribute on a public typed
connection is an error; unclassified ordinary theorems are not automatically assigned
a kind. Private theorems appear under their source names with a visibility marker.
Unimported modules are outside the query. The default Lake target first performs
a source check, then checks the environment containing its complete module
inventory, including modules absent from `powerlib.lean`.

Source queries need only Python and do not start Lean or build dependencies:

```sh
python3 tools/tmio_classification.py check
python3 tools/tmio_classification.py list T
python3 tools/tmio_classification.py list TM
python3 tools/tmio_classification.py show powerlib.LTI.sampled_exact_iff
```

The source tool lists and shows every explicitly classified theorem, including
ordinary and private ones. `check` reports both connection coverage and the total
classified population, rejecting invalid or repeated labels on either population.
No handwritten theorem-to-kind list is maintained. The source tool is a
preflight and lookup tool; the Lean environment check additionally reads elaborated
declaration types, including aliases. Neither check proves semantic classification
or constructs a verified graph of relation endpoints.

## Generated connections and family readings

`TMIO.Seed` supplies three adjacent infimum-preserving backward maps. `generate`
constructs their lower adjoints; uniqueness, leastness, supremum preservation
and composition are proved from the same construction. Deterministic and
relational interfaces use these maps rather than introducing separate semantics.

A `Family` supplies its system map, requirement satisfaction and sentence
translation. `Family.semantics` is generated from `Sentence.holds`; `Family.den`
is its singleton denotation. The translation's chain is compared with this
semantics to express soundness and exactness.

`Spectral.linearFamily`, `Spectral.localFamily` and the named-requirement
`localTable` template share the spectral interpretation laws.
[Family/Reading.lean](theorem/Family/Reading.lean) transfers soundness, exactness
and requirement obligations along a model reading and a correspondence of
requirements on a context. This is how different electrical families reuse a
swing, PLL or current-loop family without reproving the common interpretation.

[TMIO/Representation.lean](theorem/TMIO/Representation.lean) transports semantic
and generated maps, closure and interior operators, and their fixed points
under representation changes.

## Realization and observation interfaces

The model and implementation are both read by `Sentence.holds`; a realization
relates them and states the constraints under which their denotations agree or
imply one another. The interpretation of each endpoint alone does not establish
a realization. Generic sampling and discretization laws supply reusable mathematics;
an electrical realization additionally fixes the engineering endpoints and constraints.

Representative interfaces are:

| Topic | Interface and boundary | Source |
| --- | --- | --- |
| VSM test platform | A design, a delay-constrained implementation and a symbolic record-production relation; model inference implies producer truth only under realization soundness. | [VSMLPFRig.lean](theorem/GridTiedConverter/GFM/VSMLPFRig.lean) |
| Current control | Parameter mismatch, digital delay and hardware voltage limits have separate realization relations and explicit constraints. | [Mismatch.lean](theorem/GridTiedConverter/CurrentControl/Mismatch.lean), [DigitalPI.lean](theorem/GridTiedConverter/CurrentControl/DigitalPI.lean), [VoltageLimit.lean](theorem/GridTiedConverter/CurrentControl/VoltageLimit.lean) |
| Sampling and numerical methods | Exact sampling, Euler and implicit methods connect continuous and discrete interpretations; their generic laws and electrical instances remain distinct. | [ExactSampling.lean](theorem/LTI/ExactSampling.lean), [EulerRealization.lean](theorem/Numerics/EulerRealization.lean), [ImplicitRealization.lean](theorem/Numerics/ImplicitRealization.lean), [EMT/Plant.lean](theorem/Numerics/EMT/Plant.lean) |
| Disturbance envelopes | Finite-horizon safety uses solvability, margin and perturbation bounds; a finite-horizon guarantee does not imply an infinite-horizon guarantee. | [Disturbed.lean](theorem/Envelope/Disturbed.lean) |

The observation interface is relational: it reasons about every possible producer
of an arbitrary external record. It does not assign probabilities to observations.
Record likelihoods would require a probability law beyond this interface.

## Agda and Lean

Agda scaffolds fix the connection's endpoints, generality and preserved
structure. Lean independently proves the mathematical claims and is the sole
theorem trust root. Only checked data crosses the narrow generation boundary
into `theorem/generated/`; an Agda proof is not imported as a Lean proof.

Each scaffold declares its implementing Lean modules in a `-- Lean modules:`
header. Those modules cite the scaffold in their docstrings. The structure check
reads these source-local declarations, verifies both directions, and resolves
Lean references in scaffold comments to public declarations or library modules.
It does not read Markdown or maintain a second documentation registry.
The required format and ownership rules are in [Rules.md](Rules.md#1-agda-scaffolding-and-the-lean-4-theorem-layer).

## Public admission

`TMIO.Endpoint` and `TMIO.ConnectionClaim` are closed, proposition-indexed
grammars. They certify generated endpoint evaluations, comparisons and boundary
claims without an arbitrary-proposition constructor. `TMIO.Statement` retains
the syntax certificate in the proposition type. `connection% (P)` constructs
that certificate, and Lean's kernel checks both it and the proof of `P`.
`connection_proof%` exposes the definitionally equal proposition for tactic reuse.

Primitive maps and seeds live in `ConnectionBase`; `ClaimSyntax` provides the
elaborator below the public connection laws, and `ClaimElab` is the public
notation import. This ordering avoids a bootstrap cycle. The grammar supports
polymorphic endpoints, extensional comparisons and constrained claims through
explicit constructors; the allowed shapes are specified in Rules §3a.

Admission discovers model types from actual `Family` definitions and typed
claims from elaborated declarations, independently of metadata. A separate
bypass check examines operands, hypotheses and first-party dependencies for
behaviour stated outside the shared semantics. Wrapping a raw behavioural set
in an identity connection cannot bypass that check. Generic interface theorems
about arbitrary families receive only the limited allowance specified in Rules §3a.

Rational certificate synthesis treats candidate search as untrusted. A fast
candidate is checked against the exact Lyapunov equation; the complete rational
fallback inverts the finite Lyapunov operator. The kernel checks the resulting
equation and positivity. The polynomial sum-of-squares search is sound but
incomplete. Completeness claims concern the certificate language, not runtime.

## Verification entry points

`lake build` (equivalently `lake build powerlib`) runs the source preflight,
builds the actual inventory selected by all package library globs, and audits
an environment importing that whole inventory. A new module is therefore checked
even if it is absent from `powerlib.lean` or omits the architecture import.
Internal library compilation alone does not run this admission gate. Scaffold
source contents participate in the admission cache trace, and admission rechecks
their ownership headers even when compiled Lean modules are reused.

The tests in `tests/lean/Architecture/` exercise claim grammar, semantic bypass,
axioms, metadata, discovery and reuse. `tests/lean/Library/Structure.lean` checks
module dependency roles, headers, duplicate and restated results, and scaffold
ownership. `TMIOIndex.lean` checks classification queries. The dependency-role
partition constrains imports and is separate from declaration-level metadata.

The standalone profile in `dependencies/integrations/leanforcontrol/` checks
upstream reuse and axiom rejection. Agda scaffolds are checked separately with
Agda and Cubical, for example `agda theorem/Stack/Records.agda` from the root.
The Lean build reads scaffold text for structural checks but does not execute Agda.
