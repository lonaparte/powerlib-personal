# Knowledge nodes and TMIO relations

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
In `Circuits/RLMeasurement`, `reading` is a model-side compatibility criterion
for a symbolic resistance estimate. Its constraint calculations belong to M and
its sentence criteria to T–M. A genuine I–O reading would additionally require an
implementation and a justified production interface; that connection is not claimed.

The generic/engineering dependency partition and foundation/domain presentation
metadata remain independent. Generic modules can contain T–M or M–I relations;
engineering directories can contain general T lemmas. Classify the complete
statement and its hypotheses, not just the directory or the type of one endpoint.

The semantic layer reads three kinds of systems (`Behaviour`): continuous-time systems with ports
(`theorem/Flow/Defs.lean`, `theorem/Port/Defs.lean`), discrete-time systems with ports
(`theorem/Map/Defs.lean`), and random continuous-time systems with an operating envelope
(`theorem/Port/Defs.lean`, `disturbed`). A digital controller, a sampled-data loop read at its sampling instants
(`LTI/Sampling`), the period map of a switched converter (`Averaging/SwitchedStability`) and a
numerical integration scheme (`Numerics/EMT`) are discrete-time implementation families of
continuous-time models. Hybrid behaviour (state-dependent switching) is not yet read; see
[ImplementationLayer.md](ImplementationLayer.md).

## Source attributes and queries

Every reviewed public connection theorem carries one of `@[tmio T]`, `@[tmio M]`,
`@[tmio TM]`, `@[tmio MI]` or `@[tmio IO]` beside its declaration. The attribute
is the only source of its classification. There is no separately maintained
catalog; an index is reconstructed when queried. Classification considers the
complete statement, including its hypotheses and the relative roles of its
endpoints.

Keep all attributes on a declaration in one block. For example,
`@[tmio TM, powerlib_domain] theorem ...` retains both classifications; do not
place a new `@[tmio TM]` block before another `@[...]` block.

`theorem/TMIO/KnowledgeKind.lean` defines the attribute and checks its theorem
target, allowed kind and unique assignment. These checks do not decide whether
the chosen kind correctly describes the mathematics. Foundation/domain metadata
and the kernel-checked `connection%` admission contract remain independent.

The current source coverage is 2,925 theorems in 405 modules: T 1,701, M 335,
T–M 760, M–I 102 and I–O 27, including 111 private helpers. All 1,043 public
`connection%` theorems remain covered (T 102, M 52, T–M 760, M–I 102, I–O 27).
The 1,882 classified ordinary theorems have been individually reviewed, including
general analysis, stability, matrix and estimation theory, abstract relation laws,
and model representation identities. A module's suggested role does not classify
all its declarations. The remaining 4,959 theorems are unclassified; statements
with unsettled layer boundaries remain unmarked pending further review.

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

## Models and realization interfaces

### Pilot: a grid-forming VSM on a test platform

`theorem/GFM/VSMLPFRig.lean` supplies model definitions, their T–M interpretation,
an M–I realization and an I–O interface for the VSM with a first-order power filter
on an infinite bus.

* M: `GFM.VSMLPF.family` (three states), unchanged.
* M–I endpoint: `VSMLPF.Rig`, a design model with an execution delay `τ` (the first-order equivalent of the
  computation delay and PWM update), four states. Its requirement language adds the platform
  Routh condition `H > 0` and the constraint `fastLag`, a delay fast against the design margin.
  Within a physical design and a positive delay its translation of local exponential stability
  is exact.
* I–O interface: `VSMLPF.Record`, an identification result (parameter intervals and a delay bound), produced
  by every platform running at its balanced operating point with parameters in the intervals.
* M–I: local exponential stability is realized soundly within `fastLag`, by the static reduction
  above, and completely for every delay (a delay never stabilizes). Without `fastLag` it is not
  realized soundly: `slowRig` has a stable design (`K = 1 < 2`) and is unstable at `τ = 1`.
  Instability of a destabilizing design is realized for every delay.
* Composite inference through T–M, M–I and I–O: an external record passing the worst-corner fast-filter check supports local exponential stability
  of every realized model, inferred through the model family's requirement language and its
  soundness. Only with the worst-corner delay check as well does the sentence hold for every
  producing platform. `infer_not_truth_of_unstable_producer` states the gap for any model-checked
  record and any compatible unstable producer, without storing a concrete record. A slow-filter record
  supports instability of models and platforms and lies outside the records predicted by platform
  stability.

### Current loops: tolerance, digital realization, voltage limit

The single-axis PI current loop `CurrentControl.PIParams.family` (M) has three implementations.

* Parameter tolerance (`CurrentControl/Mismatch.lean`): the dq loop whose decoupling uses an
  inductance estimate. The attractive sentences are realized exactly without constraints; the
  estimate never changes the stability region.
* Digital realization (`CurrentControl/DigitalPI.lean`): computation delay and zero-order hold,
  together `τ = 1.5 Tₛ` (`Delay/SampleHold`, `Delay/Pade`), realized by a Padé(1,1) state. The
  attractive sentences are realized soundly when `3 Kp Tₛ ≤ L` and `3 Ki Tₛ ≤ R + Kp`, completely
  for every `Tₛ > 0`, and not soundly without that constraint. For the IMC tuning the platform is
  stable exactly when `3 ω_b Tₛ < 4`. The pure delay `e^{−sτ}` gives `ω_b Tₛ < π/3`
  (`CurrentControl/LoopDelay.lean`): the Padé(1,1) implementation model overestimates the stable
  range by `4/π`, so an implementation family is itself a model of the platform and carries its
  own approximation.
* Voltage limit (`CurrentControl/VoltageLimit.lean`): the applied voltage saturates at the
  linear modulation limit `V_dc/√3` (`Drives/Modulation`), a hardware constraint. With headroom at
  the operating point the local sentences are realized exactly (the limit is inactive nearby,
  `Dynamics/Locality`); under overload the operating point is not an equilibrium and the platform
  is unstable whatever its design; global exponential stability holds for no platform, so it is
  not realized soundly even with headroom.

### Disturbed implementations of deterministic designs

A deterministic design is a model read with its operating envelope (initial set, safe set) and no
disturbance; an implementation adds a random perturbation of intensity `σ` to its field and is
judged on its own safe set, which keeps a margin around the design's
(`theorem/Envelope/Disturbed.lean`, scaffold `theorem/DisturbedRealization.agda`). The
disturbance is a realistic constraint of the implementation, so the connection is M–I, and the
sentence is safety over a horizon at a probability level.

* M–I: over a finite horizon the realization is sound within a Lipschitz, solvable design, the
  margin, an intensity whose Grönwall bound at the horizon is at most the margin, and a
  perturbation bounded with probability `1 − ε` (`noisy_realizationSoundUnder_safe`). Over the
  infinite horizon it is not sound under any intensity bound: the drift design `ẋ = 0` is safe
  over every horizon, while its implementation `ẋ = σ ω₀`, `ω₀` standard Gaussian, leaves its
  safe set, the unit ball, with probability one for every `σ ≠ 0` (`noisyDrift_not_mem_den_top`,
  `not_driftImpl_realizationSoundUnder_top`). Over each finite horizon a threshold `σ₀(T)` exists
  (`noisyDrift_mem_den_finite`; the proof gives one of order `1/T`), and no threshold serves every
  horizon: small disturbance and long horizon do not commute.
* T–M, for every family: the infinite horizon is the meet of the finite horizons, and horizon and
  level enter through Galois connections whose generated adjoints are the longest certified
  horizon and the worst exceedance probability (`theorem/Envelope/Basic.lean`, scaffold
  `theorem/Envelope.agda`). Safe sets are closed under countable meets almost surely only; at a
  positive level no certified safe set need be least (`not_isLeast_safe`).
* I–O: the observation interface is relational (`possibly produces`): it infers what holds for every possible
  producer and cannot attach a probability to a record. Inferring a level `ε` from records needs a
  law of the records given the implementation, which is not represented.
