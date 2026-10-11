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

Representation transport preserves the semantic and generated maps, and now
also transports closed and interior fixed points. `closedTransport`,
`interiorTransport` and `fixedPointsIso_transport` prove that the fixed-point
correspondence commutes with representation changes.

The independent review of `8919b16` found this core architecture implemented,
but found gaps at the public interface: the old placement audit counted any
occurrence of a TMIO or Family constant, the bypass audit stopped at first-party
aliases, PortHamiltonian had only raw semantic conclusions, some reuse consumers
had raw flow conclusions, and the coordinate theorem omitted passivity.
Those gaps are addressed by the interfaces and checks below.

## Public admission

`powerlib_connection` marks generated endpoint definitions within TMIO and
Family. It does not mark `Family.Holds`. `Architecture.conclusionOnConnection`
examines the conclusion after removing the parameter and hypothesis telescope,
checks every conjunction or disjunction branch, and follows aliases.
`Architecture.rejection` also follows behavioural predicates transitively until
an admitted endpoint. A Family parameter, a connection hypothesis or an unrelated
connection conjunct cannot make a raw engineering conclusion admissible.

A module linter checks classified domain consumers. The full build additionally
checks every imported first-party domain theorem, including all library modules,
without a theorem-name exemption list. Seven adversarial placement controls and
sixteen single-semantics definition controls exercise rejection. The existing
provenance and transitive axiom checks remain independent requirements.

PortHamiltonian now has a Family interface for passivity and Lyapunov stability.
`Similar.sentence_iff` includes port passivity, using pullback of storage through
the inverse state coordinates. `Family.IsLinear.den_similar` preserves every
sentence denotation, with no minimality premise.

## Completed mathematical boundaries

| Question | Kernel-checked result |
| --- | --- |
| Is LCL right-half-plane-pole translation exact for instability? | **Refuted** by `Circuits.LCL.not_exact_unstable`: opposite unit resistances, unit inductances and capacitance 2 give frequency polynomial `2 s³`, but a zero-eigenvalue Jordan chain gives unbounded linear growth. |
| Is LCL passive translation exact for Lyapunov stability? | **Refuted**, as already proved by `not_exact_lyapunovStable` in the reviewed branch. |
| Is LCL lossless translation exact for conservation without passivity? | **Refuted**, as already proved by `not_exact_conservative`; `exactUnder_conservative` retains the passive context. |
| Are polynomial global asymptotic translations exact? | **Refuted** by the existing cubic damping boundary `not_exact_asymptotic`. |
| Can the cascade be globally certified? | `cascade_asymptotic` proves global asymptotic semantics for `x′ = -2x + y²`, `y′ = -y`; `cascade_not_exponential` proves failure of a uniform global exponential bound. `cascade_certificate_boundary` therefore proves absence of every certificate in this language, independently of search failure. |
| Is the polynomial global exponential translation exact? | **Refuted** by `not_exact_exponential`: `x′ = -x - y³`, `y′ = -y + x³` has a quartic energy with exponential decay, but no quadratic certificate in the language (`quartic_certificate_boundary`). |
| Is the polynomial sampled-contraction translation exact? | **Refuted** by `not_exact_contractive`, using the same quartic model. |
| Is rational synthesis complete? | **Proved** by `Linear.Synthesis.accepts_iff_isHurwitz` for every finite dimension; `Linear.Rational.accepted_eq_den` exposes it as an equality of generated requirement space and denotation. |

The new instability lemma `Linear.unstable_of_zero_jordan_chain` is generic.
The polynomial boundaries concern autonomous rational two-state fields on all
of ℝ², in continuous time, with no switching, delay or inputs.

## Rates and synthesis

LCL, source-load interconnection and rational-matrix requirements now include a
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

`lake build` checks the library, examples and admission/discovery/reuse/architecture
tests. The independent LeanForControl profile checks direct imported theorem
reuse and rejection of an actual upstream custom-axiom consequence. All four
Agda modules are checked with Agda 2.8.0 and cubical 0.9. The completed main build checks 37 library domain declarations and 987 library
declarations in the single-semantics audit, in addition to the consumer module
linters. The admitted Lean axiom
set is restricted to `propext`, `Classical.choice` and `Quot.sound`.
