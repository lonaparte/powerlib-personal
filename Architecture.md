# Generated connections and verified completion

PowerLib supplies objects at the T, M, I and O layers. The public engineering
interface evaluates or compares generated connections. [Rules.md](Rules.md)
applies that interface to library results, examples, admission tests, automatic
reuse and the standalone LeanForControl integration.

## Architecture

A `TMIO.Seed` contains only three adjacent semantic `sInfHom` maps. `generate`
constructs each lower adjoint, with uniqueness, leastness, supremum preservation
and composition proved using Mathlib. Satisfaction generates the complete set
of implementations; deterministic and relational observation maps generate
certification and prediction. The finite four-layer and distributed analysis
instances exercise the same framework.

A `Family` contains only its system map, requirement satisfaction and sentence
translation. `Family.semantics` is the satisfaction connection generated from
`Sentence.holds`; `Family.den` is its generated singleton value.
`chain_eq_semantics_iff` and `chain_le_semantics_iff` reduce exactness and soundness
to the generic connection comparisons in `TMIO.Compare`. Certification,
refutation, representation changes and requirement extensions use this interface.

The system map returns a `Behaviour`: a continuous-time system with ports (`Flow.Defs`,
`Port.Defs`) or a discrete-time system with ports (`Map.Defs`), each interpreted once by
`Sentence.holds`. Discrete notions are stated through iterates of the state map and
one-step inequalities, so the semantic layer keeps one time axis. The single-semantics
audit recognizes discrete behaviour — a sequence indexed by steps into a state space, an
iterate of a state map, the step of a discrete system — inside the semantic layer and
rejects it outside, as it does for signals of time.

Family laws that recur across models are proved once in generic templates and instantiated by
the model families: `Spectral.linearFamily` and `Spectral.localFamily` for the two-requirement
languages, and the named-requirement template `theorem/Spectral/Local.lean` (`localTable`,
`chain_le_semantics_of_localTable`, `exactUnder_les_of_jacobian`, the witness lemmas
`not_exact_of_witness`, `not_exact_of_les_witness`, `mem_den_unstable_of_ne_zero`) for families
that keep their own requirement languages. A model family then supplies only its obligations:
which requirements give local exponential stability or instability, and the converse algebra of
its Jacobian.

Families that are other families in disguise are read through a hub instead of re-proving its
laws: the droop loop with a power filter, the saturated converter and the classical machine through
the swing family, the port-Hamiltonian PLL through the PI-PLL, the drive IMC loop through the
converter PI loop. A spoke supplies a map of models, a reading (usually an affine change of state
coordinates, `Spectral.mem_den_flow_iff_of_transport`) and the correspondence of its requirement
language with the hub's on a context; `theorem/Spectral/Hub.lean` then carries exactness within the
context, soundness and requirement obligations from the hub (`exactUnder_of_hub`, `exact_of_hub`,
`sound_of_hub`, `realize_subset_den_of_hub`).

Representation transport preserves the semantic and generated maps and
transports closed and interior fixed points. `closedTransport`,
`interiorTransport` and `fixedPointsIso_transport` prove that the fixed-point
correspondence commutes with representation changes.

## Scaffolds

Every connection between contents of the library is first built as an Agda scaffold
([Rules.md](Rules.md) §1) and then proved in Lean. The scaffolds are kept in `theorem/` as
design records; the Lean build does not read them. Data generated from a scaffold passes the
narrow bridge of Rules §11 and is checked by Lean (`theorem/generated/`).

| Scaffold | Connection | Lean |
| --- | --- | --- |
| `theorem/Conversion.agda` | RL branch: impedance parameters ↔ state-space parameters | `Circuits/RL` (generated `Conversion`) |
| `theorem/LCLConversion.agda` | LCL filter: circuit parameters ↔ state-space parameters | `Circuits/LCL` (generated `LCLConversion`) |
| `theorem/ImpedanceInterconnection.agda` | source and load → closed loop; covariance under state coordinates | `Circuits/Interconnection` (generated `ImpedanceInterconnection`) |
| `theorem/TMIO/Representation.agda` | representation changes transport satisfaction structures and generated spaces | `TMIO/Representation` (`generate_transport`, `Seed.transport_whole`) |
| `theorem/Rebase.agda` | changes of bases of an interconnection: state coordinates, per-unit bases, current direction, time base | `Transform/Rebase`; per-unit instance `Transform/PerUnitLTI` |
| `theorem/FamilyReading.agda` | the generic pattern: a spoke family read through a hub family (readings by conjugacy or equality, contexts, transfer of exactness and soundness, composition) | `Spectral/Hub` |
| `theorem/FlowSemantics.agda` | the semantic layer the readings use: fields at a point, affine changes of coordinates, the local sentence kinds and table | `Dynamics/Transport` (`holds_transport_iff`), `Spectral/Local` (`localTable`) |
| `theorem/Swing.agda` | the swing hub: models, requirements, translation and the laws its spokes read | `Synchronous/Swing` |
| `theorem/DroopSwing.agda` | the droop loop with a power filter read as a swing machine (`P_f = P₀ − D ω`, within `D, ω_c > 0`) | `GFM/VSMLPF` (`DroopLPF.mem_den_iff_swing`) |
| `theorem/SaturationSwing.agda` | the current-saturated converter read as a swing machine (same field, within positive inertia) | `Limiting/Saturation` (`mem_den_flow_iff_swing`) |
| `theorem/ClassicalMachineSwing.agda` | the classical machine read as a swing machine (momentum `p = M ω`, flow sentences) | `Synchronous/PH` (`ClassicalSM.mem_den_flow_iff_swing`) |
| `theorem/MatchingSwing.agda` | the swing family of matching control read as a swing machine on a speed-independent sinusoidal law with `ω* = 0` (same field; local exponential stability from the hub) | `GFM/Matching/Matching` (`swing_mem_den_iff_hub_of_sinusoid`, `swing_mem_den_locallyExponentiallyStable_iff_of_sinusoid`) |
| `theorem/VSMSwing.agda` | the VSM family (any power map, any frame) read as a swing machine where the power curve is sinusoidal and `ω* = 0`: same system, image `⟨M, D, P_ref + D ω_s, k₁, k₂, k₃⟩`; the infinite bus is a special case; no correspondence of requirements, so the VSM family keeps its own laws | `GFM/DroopVSM` (`vsm_mem_den_iff_swing_of_sinusoid`, `vsm_mem_den_iff_swing`) |
| `theorem/DroopVSM.agda` | the droop + LPF family read as the VSM family by an affine change of coordinates (`M = τ_p K_R`, `D = K_R`), for every model and every sentence: its semantics is the VSM semantics pulled back along `toVSM`, and soundness transfers; composed with `VSMSwing`, the infinite-bus stability of droop + LPF | `GFM/DroopVSM` (`semantics_eq_comap`, `den_eq_preimage`, `droopFamily_chain_le_semantics`, `infiniteBus_locallyExponentiallyStable`) |
| `theorem/SwingPortHamiltonian.agda` | the linearized swing family read as a linear port-Hamiltonian system when `M > 0`, `D ≥ 0`, `K > 0` (state matrix `diag(1, M) J diag(1, 1/M)`): flow sentences read; passivity and Lyapunov stability of the image | `Synchronous/SwingPH` (`linearPH_mem_den_flow_iff`, `linearPH_passive`, `linearPH_lyapunovStable`) |
| `theorem/PortHamiltonianPLL.agda` | the port-Hamiltonian SRF-PLL read as a PI-PLL (flow sentences, within nonnegative energy) | `PLL/PH` (`PLLPH.mem_den_flow_iff_srf`) |
| `theorem/IMCCurrentLoop.agda` | the drive IMC current loop read as the converter PI loop with IMC tuning (same plant, `L ≠ 0`) | `Drives/CascadeControl` (`mem_den_iff_imc`) |
| `theorem/BasinGuardFourState.agda` | the basin-guard carrier read as the four-state DC-link model with `I_q* = 0` (integrator sign flip and shift; local exponential stability by the four-state Routh conditions) | `GFL/DCLink/BasinGuard` (`mem_den_iff_fourState`, `mem_den_locallyExponentiallyStable_iff`; the translation of local exponential stability is exact within `{iqZero, vdcNonzero}`: `exactUnder_locallyExponentiallyStable`) |
| `theorem/FeedforwardCurrentLoop.agda` | the PI current loop with low-pass PCC-voltage feedforward read through the PI loop: its spectrum adds `−1/τ`, so the attractive denotation is the PI one pulled back along `LPFLoop.pi`, cut by `τ > 0` | `CurrentControl/Feedforward` (`lpfDen_eq`) |
| `theorem/CascadeCurrentLoop.agda` | the linearized current-loop/DC-link cascade against the converter PI loop: the attractive denotation is the PI one pulled back along `pi`, cut by a positive DC-node coefficient `I_dc0/(C V0)` (the DC node adds its own pole) | `GFL/DCLink/Cascade` (`linearizedDen_eq`, `linearizedExact`, `linearized_mem_den_iff`) |
| `theorem/GovernorReduction.agda` | the swing–governor family against its first-order reduction (`T_g → 0`): the attractive sentences and sampled contraction transfer when `0 < M + D T_g` (every `T_g` when `D ≥ 0`) and not on the whole family (an unstable model with a globally exponentially stable reduction); decay rates off the governor pole transfer below a threshold | `Frequency/SwingGovernor` (`mem_den_iff_reduce`, `mem_den_iff_reduce_of_nonneg`, `exists_unstable_reduce_globallyExponentiallyStable`, `exists_threshold_mem_den_decay_iff_reduce`) |
| `theorem/CurrentDirection.agda` | OUT-positive and IN-positive writings of a model related by the reversal of currents and powers (conventions §D) | `GFL/PowerLoop/QuasiStatic`, `GFL/RatePLL`, `GFL/ModelLayers`, `GFL/LCLine/FullModel`, `GFL/LCLine/FullModelDC` (IN-written families; the literature OUT forms and `field_eq_transport_literatureField`-type identities) |
| `theorem/DqAlphaBeta.agda` | the RL branch in the dq frame at speed `ω` and in the αβ frame (`ω = 0`): the attractive denotation is its own pull-back along `DqBranch.alphaBeta` (Hurwitz iff `R/L > 0` at every frame speed; not a conjugacy, Park's transformation being time-varying) | `CurrentControl/DqRL` (`den_eq_alphaBeta`) |
| `theorem/PLLAmplitude.agda` | amplitude invariance inside the PI-PLL family: for `V ≠ 0` the SRF-PLL of amplitude `V` and gains `(K_p, K_i)` is conjugate (`ξ = η / V`) to the unit-amplitude one with gains `(V K_p, V K_i)` on every flow sentence | `PLL/Model` (`srf_mem_den_iff_unitAmplitude`) |
| `theorem/Realization.agda` | the generic model–implementation pattern: realization soundness, completeness and exactness within constraints; realization by a design map and readings through the design model | `Stack/Implementation` (`ofDesign`, `realizationExactUnder_of_den_eq_preimage`, `not_realizationSoundUnder_of_design`) |
| `theorem/ExactSampling.agda` | continuous linear model ↔ its exact sampling at any period: every sentence is read through the design, so the realization is exact for every sentence without constraints, and the sampled family inherits the soundness and exactness of the model's translations | `LTI/ExactSampling` (`sampled_reading`, `exactSampling_realizationExact`, `sampled_chain_le_semantics`, `sampled_exact_iff`), sentence by sentence `LTI/SampledFlow` (`holds_iff_holdsMap_exp`), discrete linear reading `Map/LinearReading` (`holdsMap_op_iff_schurStable`) |
| `theorem/SwitchedAveraging.agda` | averaged linear model ↔ switched implementation read stroboscopically: sound under fast switching; exact for every sentence when the topologies commute, hence always in dimension one; not sound without a constraint in every dimension `n ≥ 2` | `Averaging/SwitchedFamily` (`switching_sound_fast`, `switching_realizationExactUnder_commuting`, `switching_realizationExactUnder_of_le_one`, `not_switching_realizationSoundUnder`, and the boundary `switching_realizationSoundUnder_iff`: sound without constraint ↔ `n ≤ 1`) |
| `theorem/EulerDiscretization.agda` | model ↔ explicit Euler implementation: local exponential stability realized for every small step, and never for every step; only smoothness at the selected point is needed | connection statements over arbitrary autonomous families in `Numerics/EulerRealization` (`euler_sound_small_step(_local)`, `euler_certified_small_step(_local)`, `not_euler_realizationSoundUnder_of_large_step(_local)`); per family (the `Euler` modules of `Synchronous`, `GFM`, `GFM/Matching`, `GFL`, `GFL/PowerLoop`, `GFL/LCLine`, `GFL/DCLink`, `CurrentControl`, `Network/Swing`, `Drives`, `PLL`, `Limiting`): the Euler implementation, the public smoothness lemma and `not_euler_realizationSoundUnder` with the family's witness |
| `theorem/EulerPorts.agda` | model with ports ↔ explicit Euler implementation: flow sentences read through the zero-input dynamics (the autonomous laws carry over); passivity is not realized at any step when the output does not depend on the input; for linear plants the realization is complete at every step and exact below a threshold | connection statements over arbitrary families with ports in `Numerics/EulerPorts` (`eulerPorts_realizationSoundUnder_flow_iff`, `eulerPorts_sound_small_step_local`, `not_eulerPorts_realizationSoundUnder_passive`, `eulerPorts_realizationCompleteUnder_linear`, `eulerPorts_exact_small_step_linear`; contrast `discreteGradient_passiveWith`); per family the passivity and large-step witnesses (`Circuits/PortEuler`, `GFL/DCLink/PortEuler`, `Synchronous/PortEuler`, `PLL/PortEuler`) |
| `theorem/VSMPlatform.agda` | VSM + LPF models (M) realized by test platforms with an execution delay (I) that produce identification records (O): realization sound and exact within `fastLag`, complete for every delay, not sound without `fastLag`; instability realized for every delay; inference, certification, truth and the inference–truth gap of a record without the delay check | `GFM/VSMLPFRig` (`realizationExactUnder_locallyExponentiallyStable`, `not_realizationSoundUnder_locallyExponentiallyStable`, `realizationSoundUnder_unstable`, `locallyExponentiallyStable_mem_infer`, `mem_certified_locallyExponentiallyStable`, `lagFreeRecord_infer_not_truth`) |
| `theorem/DigitalCurrentLoop.agda` | PI current loop ↔ its digital platform (computation delay and zero-order hold, `τ = 3Tₛ/2`, as a Padé(1,1) state): attractive sentences realized soundly under the step constraints, completely for every period, exactly under the constraints; not soundly without them; instability realized for unstable designs | `CurrentControl/DigitalPI` (`realizationSoundUnder`, `realizationCompleteUnder`, `realizationExactUnder`, `not_realizationSoundUnder`, `realizationSoundUnder_unstable`) |
| `theorem/DecouplingMismatch.agda` | PI current loop ↔ the dq loop decoupled with an inductance estimate: the attractive denotation is the design's pulled back along `base` for every frame speed and mismatch, so the attractive sentences are realized exactly without constraints | `CurrentControl/Mismatch` (`den_eq_base`, `realizationExactUnder`) |
| `theorem/VoltageLimit.agda` | PI current loop ↔ the loop with the applied voltage saturated at `V_dc/√3`: local sentences exact with integral action and headroom; without integral action Lyapunov stability not realized soundly; under overload every platform is unstable; global exponential stability not realized soundly | `CurrentControl/VoltageLimit` (`realizationExactUnder_local`, `realizationSoundUnder_attractive`, `not_realizationSoundUnder_lyapunovStable`, `realizationSoundUnder_unstable_of_overload`, `not_realizationSoundUnder_globallyExponentiallyStable`) |
| `theorem/RLMeasurement.agda` | the RL family and its DC resistance readings of accuracy `ε` (models → records): certification by the resistance window, prediction, an observation closure that cannot separate equal resistances (inductance and decay rate not identifiable), records certified through their estimate, independence of the model representation | `Circuits/RLMeasurement` (`certify_reading`, `predict_reading`, `certified_readings`, `closure_resistance`, `certified_records`, `stateSpace_whole`) |

The rebasing scaffold shows the division of labour. Univalence turns the equivalences of the
six spaces of an interconnection into a path, so the closed loop commutes with every change of
bases at once (`closedLoop-natural`), and the scaffold names what is left to prove: the
equivalences must preserve the additive operations (`Preserves`, `closedLoop-rebased`). Lean
proves the same statement in the same generality through typed constructions and one
naturality theorem (`Construction.eval_rebase`), where linearity supplies the preservation and
only the invertibility of the bases the constructions pass through remains as a hypothesis.
Coordinates, per-unit bases and the current direction are then instances, not separate proofs.

## Public admission

Rules §3a states what a public conclusion may be. Its implementation uses two closed,
proposition-indexed inductive grammars:
`TMIO.Endpoint` certifies values of real infimum-preserving maps or their uniquely
generated adjoints; `TMIO.ConnectionClaim` certifies endpoint evaluation,
comparison and boundary conclusions. Neither has an arbitrary-Prop constructor.
`TMIO.Statement` carries this syntax certificate in the public proposition type.
`connection% (P)` elaborates ordinary notation into the certificate. Both the
certificate and the proof of P are checked by the kernel; the elaborator is
untrusted. Statements unfold definitionally to P, preserving mathematical use.
Admission keeps the stored certificate, so every restriction on the shape of a
claim is a constructor of the kernel grammar, not an elaborator check.

The constructors `allType`, `iffCondition` and `existsGuard` carry the binders and
side conditions of Rules §3a. Endpoints and binders have fixed universes: one claim
mixes endpoints generated from sentences and from model sets, so a
universe-polymorphic claim would need a certificate with a universe per node. Side
conditions are `TMIO.Condition` values. A tautological claim can still carry its
condition, as `memberIff` can carry any right side; neither adds a kind of
conclusion, and the bypass audit still reads every operand.

Admission infers model types from actual Family definitions, not a handwritten
list, and discovers typed claims whatever their annotations. The semantic bypass
checker independently checks that
claim operands and hypothesis types do not directly state behaviour. At a
certified endpoint it checks the input and structural maps while keeping the
semantic map abstract. A raw behavioural set passed to an identity connection
therefore fails admission even though that connection is mathematically valid.

The default Lake target `powerlib` builds every module selected by all package
library globs and generates an admission module importing that actual inventory.
Consequently a new source cannot evade admission by omitting the linter import
or the central library import. `lake build` and `lake build powerlib` include this
gate. Lake reuses a successful audit only while the complete module inventory and
all its built module dependencies are unchanged, including the admission checker.
Failed audits never produce a success receipt. Direct Lean invocation or internal
staging-library builds are not admission;
changing the gate itself remains a build-policy change, not a mathematical claim.

This is a structural public-interface contract. The gate infers concrete model
domains from declared Family types, including transparent aliases. It does not
decide whether an arbitrary generic mathematical proposition ought to be an
engineering claim. Generic support remains available for implementation proofs.

PortHamiltonian has a Family interface for passivity and Lyapunov stability.
`Similar.sentence_iff` includes port passivity, using pullback of storage through
the inverse state coordinates. `Family.IsLinear.den_similar` preserves every
sentence denotation, with no minimality premise.

## Completed mathematical boundaries

| Question | Kernel-checked result |
| --- | --- |
| Is LCL right-half-plane-pole translation exact for instability? | **Refuted** by `Circuits.LCL.not_exact_unstable`: opposite unit resistances, unit inductances and capacitance 2 give frequency polynomial `2 s³`, but a zero-eigenvalue Jordan chain gives unbounded linear growth. |
| Is LCL passive translation exact for Lyapunov stability? | **Refuted** by `not_exact_lyapunovStable`. |
| Is LCL lossless translation exact for conservation without passivity? | **Refuted** by `not_exact_conservative`; `exactUnder_conservative` retains the passive context. |
| Are polynomial global asymptotic translations exact? | **Refuted** by the cubic damping boundary `not_exact_asymptotic`. |
| Can the cascade be globally certified? | `cascade_asymptotic` proves global asymptotic semantics for `x′ = -2x + y²`, `y′ = -y`; `cascade_not_exponential` proves failure of a uniform global exponential bound. `cascade_certificate_boundary` therefore proves absence of every certificate in this language, independently of search failure. |
| Is the polynomial global exponential translation exact? | **Refuted** by `not_exact_exponential`: `x′ = -x - y³`, `y′ = -y + x³` has a quartic energy with exponential decay, but no quadratic certificate in the language (`quartic_certificate_boundary`). |
| Is the polynomial sampled-contraction translation exact? | **Refuted** by `not_exact_contractive`, using the same quartic model. |
| Is rational synthesis complete? | **Proved** by `Linear.Synthesis.accepts_iff_isHurwitz` for every finite dimension; `Linear.Rational.accepted_eq_den` exposes it as an equality of generated requirement space and denotation. |

The instability lemma `Linear.unstable_of_zero_jordan_chain` is generic.
The polynomial boundaries concern autonomous rational two-state fields on all
of ℝ², in continuous time, with no switching, delay or inputs.

## Rates and synthesis

LCL, source-load interconnection and rational-matrix requirements include a
specified real rate. The static requirement is `RateMargin A a`, meaning
`IsHurwitz (A + a • 1)`. A shared quadratic-energy comparison proves its
soundness at every real rate, including zero and negative rates. The interconnection
rate uses the complete closed-loop state matrix; component stability is not
required for this state-space evidence. Admission includes a nonempty positive-rate
LCL example. Strict margin is sufficient; equality at the spectral boundary is
not claimed exact.

Rational synthesis checks an untrusted fast candidate when it solves the exact
Lyapunov equation. Otherwise it computes a candidate by inverting the full finite
rational Lyapunov operator. Upstream uniqueness makes that operator injective for
a Hurwitz input and identifies every rational solution with the positive real
solution. `Linear.Positive.check_iff` proves the executable Schur check equivalent
to real positive definiteness. Both `accepts` and `lyapunov_certificate%` use this
candidate selection and check. The elaborator writes rational literals; the
kernel verifies the equation and positivity without trusting elaborator execution.

The cofactor fallback proves completeness and is expensive for large matrices.
The fast candidate avoids it in the common case; completeness is not a running-time
claim. The polynomial sum-of-squares search remains sound and incomplete, with
proved separating models rather than an unsupported completeness claim.

## Validation

`lake build` checks the library, examples and the admission, discovery, reuse, architecture
and library-structure tests. The library structure test enforces the meta-rules of Rules §0
that are visible in the built environment: every module in exactly one layer (`LAYERS`), no
generic module importing an engineering one (`DEPENDENCIES`), model behaviour only inside
connection statements (`BARE_BEHAVIOUR`), module headers (`HEADERS`), no duplicate statements
(`DUPLICATES`), no theorem restating another it could use (`RESTATEMENTS`, no exemptions), and
every connection between contents citing its scaffold, every scaffold cited and listed above
(`SCAFFOLDS`). The independent LeanForControl profile checks direct imported theorem
reuse and rejection of an actual upstream custom-axiom consequence. The Agda
scaffolds are checked with Agda 2.8.0 and cubical 0.9 (`agda theorem/<Module>.agda`
from the repository root); the Lean build does not depend on them. Dependency
oleans were reused without building Mathlib from source.

The completed main admission checks 56 built modules, 705 proof declarations and
85 typed connection statements, including private rejection fixtures. The
independent profile checks 31 modules, 347 proof declarations and 6 typed
statements. The admitted Lean axiom set remains `propext`, `Classical.choice`
and `Quot.sound`.

`ConnectionAdmission.lean` supplies two positive claims, one unannotated and one
misleadingly annotated foundation, and nine rejection controls. Real temporary
source files also exercise the public `lake build` entry point; none is added to
the central library import or imports Architecture. Every expected rejection
was checked against the offending declaration, rather than merely a nonzero
build exit code.

| Actual build probe | Result |
| --- | --- |
| Unannotated raw model behaviour, without the linter import | Rejected |
| Raw behaviour marked foundation | Rejected |
| Behavioural alias or model type alias | Both rejected |
| Raw proof-valued `def` | Rejected |
| Raw behavioural hypothesis of a typed claim | Rejected |
| A new model behind a Family type alias | Rejected |
| Entire model telescope hidden in a proposition alias | Rejected |
| Behavioural set hidden as an identity connection's input | Rejected |
| Behavioural alias marked with the removed endpoint tag inside TMIO | Rejected at compilation |
| Unannotated genuine connection claim without the linter import | Accepted and discovered |
