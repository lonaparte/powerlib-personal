# The four TMIO layers in this library

`TMIO.Seed` fixes the mathematics of a four-layer chain: four complete lattices, one
infimum-preserving semantic map per adjacent edge pointing back to the earlier layer, and
forward maps generated as unique lower adjoints ([Architecture.md](Architecture.md)). This
document fixes what the four layers mean in powerlib, how a result is placed in one of them, and
how the Lean interface carries each layer. The interface is `theorem/Stack/Basic.lean`.

## Definitions

| Layer | Objects | Changes when |
| --- | --- | --- |
| T, theory | Sentences of the semantic layer (`Sentence`: the flow properties and passivity). Generic mathematics supplies their proofs. | The mathematics changes. |
| M, model | The theory organized for a concrete situation. A model is an idealized description of one situation (topology, control law, parameters); its behaviour is given exactly by the semantic layer. A requirement language describes classes of models and organizes the theory over them. | The modelling changes for the same theory. |
| I, implementation | A model under realistic constraints: experimental platforms and test rigs, sampling and computation delay, sensor and actuator dynamics, quantization, limits the design did not intend, parameter tolerances, numerical integration. An implementation has its own behaviour, read by the same semantic layer, which in general differs from the behaviour of the model it realizes. | The conditions of realization change for the same model: platform, digitization, simulation method. |
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

A `Stack X Q Y R V n p m q` consists of

* `model : Family X Q n p`: models `X` with their requirement language `Q` and translation;
* `impl : Family Y R m q`: implementations `Y` with their own system map, and the requirement
  language `R` of their realistic constraints;
* `realizes : SetRel X Y`: the implementation realizes the model (for a design map,
  `Stack.ofDesign`);
* `produces : SetRel Y V`: the implementation may produce the record.

Its seed `Stack.seed` has the semantic maps `model.semantics`, `possibly realizes` and
`possibly produces`. The organized seed `Stack.organized` replaces the first map by the
translation chain `model.chain`, the theory as the requirement language organizes it. The derived
operations are

| Operation | Meaning | Lean |
| --- | --- | --- |
| Data-driven inference | Sentences satisfied by every model realized by a possible producer of the records | `Stack.infer` (`seed.uTO`) |
| Theory-driven certification | Records all of whose possible producers realize only models of the sentences | `Stack.certified` (generated `uTO`) |
| Inference through the requirement language | The same, checking the translation instead of the semantics | `Stack.inferOrganized`, `Stack.certifiedOrganized` |
| Implementation truth | Sentences satisfied by every possible producer itself | `Stack.truth` |
| Realization soundness | Within constraints `Δ`, an implementation whose realized models all satisfy `s` satisfies `s` | `Stack.RealizationSoundUnder Δ s` |
| Realization exactness | Within `Δ`, an implementation satisfies `s` exactly when its realized models do | `Stack.RealizationExactUnder Δ s` |

Realization soundness compares two connections from sentences to implementations, the
composite through the realized models (`seed.uTI`) and the implementations' own semantics, just
as the soundness of a translation compares the translation chain with the semantics one layer
up. Data-driven inference reaches conclusions about the realized models. They become
conclusions about the producing implementations through realization soundness
(`Stack.infer_true`, `Stack.infer_subset_truth`). Refutation runs the same edge backwards
(`Stack.refutes_realized`). Sound translations let inference use the requirement language
(`Stack.mem_infer_of_organized`, `Stack.certifiedOrganized_subset`).

## Placing results

* A model family with its translation is one T–M connection. Its translation, denotation and
  requirement-space conclusions are T–M and M results. The codex encoding `Family.seed` puts the
  model instances in the third position and the requirement sets in the second; in the reading
  above both belong to M.
* An implementation is a second family. Its own conclusions have the same three shapes and are
  I results; its realistic constraints are requirements of its language.
* A theorem relating implementations to the models they realize is an M–I result, stated with
  `RealizationSoundUnder` or `RealizationExactUnder`.
* A theorem about records along a stack is a T–O result, stated with `infer`, `certified` or
  `truth`.

Generic modules supply the tools of each layer without belonging to it: the delay, sampling,
averaging, modulation and EMT discretization modules for implementations, and the estimation
modules for records.

`dependencies/tests/lean/Library/TMIOIndex.lean` files every connection statement under one
category by the constants of its proposition. It recognizes implementation families by the
implementation type of a `Stack` declared in the library, not by names or tags:

```
import dependencies.tests.lean.Library.TMIOIndex

#tmio_edges                  -- statements per category and layer
#tmio_edges realization      -- one category, grouped by module
```

The categories are `translation`, `denotation` (T–M), `requirementSpace` (M), `implementation`
(I), `realization` (M–I), `data` (T–O) and `observation` (the codex observation relations on
models).
