# The four TMIO layers in this library

`TMIO.Seed` fixes the mathematics of a four-layer chain: four complete lattices, one
infimum-preserving semantic map per adjacent edge pointing back to the earlier layer, and
forward maps generated as unique lower adjoints ([Architecture.md](Architecture.md)). This
document fixes what the four layers mean in powerlib, how a result is placed in one of them, and
how the Lean interface carries each layer. The interface is `theorem/Stack/Implementation.lean`
and `theorem/Stack/Basic.lean`.

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

## Placing results

* A model family with its translation is one T–M connection. Its translation, denotation and
  requirement-space conclusions are T–M and M results. The codex encoding `Family.seed` puts the
  model instances in the third position and the requirement sets in the second; in the reading
  above both belong to M.
* An implementation is a second family. Its own conclusions have the same three shapes and are
  I results; its realistic constraints are requirements of its language.
* A theorem relating implementations to the models they realize is an M–I result, stated with
  `RealizationSoundUnder`, `RealizationCompleteUnder` or `RealizationExactUnder`.
* A theorem about records along a stack is an O result, stated with `infer`, `certified`,
  `truth` (T–O) or `predicted` (O–I).

Generic modules supply the tools of each layer without belonging to it: the delay, sampling and
modulation modules for implementations, and the estimation modules for records. The model
families of the library are idealized: their model boundaries list delay, PWM, sampling and
saturation among the exclusions, which are the realistic constraints of the implementation
layer.

The semantic layer reads continuous-time autonomous flows and port systems. A discrete-time
recursion (an EMT discretization, `Numerics/EMT`; a discrete LTI system, `LTI/Discrete`) or a
periodically switched system (`Averaging/StateSpaceAveraging`) is therefore not a family, and its
results remain static or generic statements outside the layers until the semantic layer reads
discrete time or switching.

`dependencies/tests/lean/Library/TMIOIndex.lean` files every connection statement under one
category by the constants of its proposition. It recognizes implementation families by the
implementation type of an `Implementation` or `Stack` declared in the library, not by names or
tags:

```
import dependencies.tests.lean.Library.TMIOIndex

#tmio_edges                  -- statements per category and layer
#tmio_edges realization      -- one category, grouped by module
```

The categories are `translation`, `denotation` (T–M), `requirementSpace` (M), `implementation`
(I), `realization` (M–I), `data` (records: T–O and O–I) and `observation` (the codex observation
relations on models).

## Implementation families

### Pilot: a grid-forming VSM on a test platform

`theorem/GFM/VSMLPFRig.lean` builds the four layers for the VSM with a first-order power filter
on an infinite bus.

* M: `GFM.VSMLPF.family` (three states), unchanged.
* I: `VSMLPF.Rig`, a design model with an execution delay `τ` (the first-order equivalent of the
  computation delay and PWM update), four states. Its requirement language adds the platform
  Routh condition `H > 0` and the constraint `fastLag`, a delay fast against the design margin.
  Within a physical design and a positive delay its translation of local exponential stability
  is exact.
* O: `VSMLPF.Record`, an identification result (parameter intervals and a delay bound), produced
  by every platform running at its balanced operating point with parameters in the intervals.
* M–I: local exponential stability is realized soundly within `fastLag`, by the static reduction
  above, and completely for every delay (a delay never stabilizes). Without `fastLag` it is not
  realized soundly: `slowRig` has a stable design (`K = 1 < 2`) and is unstable at `τ = 1`.
  Instability of a destabilizing design is realized for every delay.
* T–O: a record passing the worst-corner fast-filter check supports local exponential stability
  of every realized model, inferred through the model family's requirement language and its
  soundness. Only with the worst-corner delay check as well does the sentence hold for every
  producing platform. `lagFreeRecord_infer_not_truth` shows the gap: a record produced by
  `slowRig` supports stability of the models while its producer is unstable. A slow-filter record
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
