# PowerLib Rules

These rules define what PowerLib admits, how results are checked, and what its
automation claims mean. They apply to the library, bridges, synthesizers,
discovery tools, examples, tests, and public documentation.

## 1. Agda foundation and Lean 4 theorem layer

Agda is the foundation. It supports underlying structures, representations,
representation conversions, equivalences, and transport between models.
Lean 4 is the public theorem layer. Every formal domain result exposed by
PowerLib must ultimately be a named theorem checked by the Lean kernel.
Agda can support Lean; an Agda proof cannot replace the final Lean theorem.

Markdown derivations, Python computations, Mathematica or SymPy results,
numerical experiments, and Agda-only proofs are not admitted domain theorems.

## 2. Formalization directory

The active visible source directories are `theorem/`, `example/`, and
`dependencies/`. `theorem/` contains formalization source and checked generated
formalization source, with no Markdown files. `example/` contains formal public
consumers. Necessary kernel, discovery, and automatic-reuse consumers belong in
`dependencies/tests/`; pinned integration profiles belong in
`dependencies/integrations/`. Procedural or redundant tests and research notes
stay in the local workspace outside the repositories. A result not yet expressed
as a Lean theorem is a research note, regardless of its mathematical plausibility.
Directory structure must enforce this distinction.

## 3. Foundation results and domain results

Foundation results include algebraic identities, conversion involutions,
representation equivalences, transport laws, and auxiliary lemmas. They may
be proved manually and checked by the Lean or Agda kernel. Not every lemma
requires synthesis.

Domain results express engineering conclusions about power systems or power
electronics, such as small-signal stability, impedance stability, or closed-loop
exponential stability. They require final Lean theorems about the formalized
system. Foundation evidence must not be presented as a domain conclusion.

Every first-party, source-authored named Lean theorem must carry exactly one of
`@[powerlib_foundation]` and `@[powerlib_domain]`. This includes private helpers,
dependency adapters, generated endpoint contracts, and named formal consumers.
The two classifications are mutually exclusive. Independently reviewed `simp`,
`ext`, and Aesop attributes may coexist with either classification; classification
alone does not register an automatic proof rule. Definitions, structures,
anonymous examples, compiler-generated auxiliaries, and directly imported
upstream theorems do not require these classification attributes.

Admission must detect missing classifications from elaborated declaration
provenance and collect registered theorems automatically, without a handwritten
theorem list. Classification does not replace kernel or transitive axiom checks.

## 4. Explicit model boundaries

Every domain theorem must precisely identify the system it concerns. State
its state variables and their order, coordinate frame, parameter ranges, inputs,
controller and feedback signs, whether delay, PWM, or PLL dynamics are included,
whether time is continuous or discrete, and whether it concerns an equilibrium
or linearization around a trajectory.

A theorem about an ideal three-state LCL plant must not have a name or public
description that implies stability of a complete grid-connected converter.
Excluded components and idealizations are part of the model boundary.

## 5. Formalize the system before its calculation

Represent the engineering model itself formally. Construct state-space models,
impedance descriptions, closed-loop matrices, or other derived objects from
that model, then prove their relationships to the intended system.

Importing a previously calculated characteristic polynomial, LMI, or stability
condition and proving only that final algebraic condition is insufficient.
The formal chain must connect the original model to the derived objects and
the final engineering property.

## 6. Semantic completion

Determinant positivity, a Routh-Hurwitz condition, a determinant identity, or
`A^T * P + P * A = -I` is intermediate evidence. Certificate arithmetic is not
the completion criterion.

The completed result must conclude a meaningful system property, for example:

```lean
theorem stable : ClosedLoop.Stable
theorem exponentially_stable : ExponentiallyStable system
```

The relevant stability predicate must describe the formalized system, with
its interpretation and assumptions established. PowerLib must not present a
successful certificate check as proof of an engineering theorem unless the
semantic theorem has also been derived and kernel-checked.

## 7. Synthesis is the default ATP target

ATP-facing domain results default to S-level: the system receives a problem
description or model without the missing witness and automatically finds the
witness or certificate, then Lean derives the semantic theorem.

An input that already supplies a Lyapunov matrix, controller gain, SOS
decomposition, or other sought answer supports certificate verification. It
does not demonstrate synthesis of that answer.

For example, submitting only `R = 2` and `L = 1`, automatically obtaining
`p = 1/4` and `rate = 4`, and having Lean derive the resulting theorem is
synthesis. Having a person supply those witness values is verification.

## 8. The synthesizer is untrusted

Python, an LLM, an SMT or SDP solver, a CAS, a search procedure, or a neural
network may propose witnesses. None belongs to the trusted computing base.
An arbitrarily wrong proposal must lead at most to rejection; it must never
compromise the soundness of admitted results.

## 9. Independent reconstruction of the submitted model

The checker must independently reconstruct the target model from the original
submission. It must not trust a certificate's claimed model, success flag,
theorem name, or proof path.

Certificates must be tied to the exact submitted model. A witness or proof for
a different model must not be admitted as the submitted model's certificate.
The existing RL model-indexed `Accepted` type and independent admission target
are the pattern for every family. A witness that genuinely satisfies the
obligations for several models can be checked anew for each model; an earlier
acceptance for one model cannot replace checking another.

## 10. Kernel trust and proof escapes

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

The bridge exports a limited, versioned, structurally specified, machine-checkable
data representation of an Agda-checked executable operation. Lean independently
checks the exported endpoint contract and its concrete instantiation.

There is no assumed general translation of Agda proofs to Lean. An Agda proof
does not authorize unconditional acceptance by Lean. A restricted versioned wire
interface is the institutional pattern.

## 12. Exact acceptance

Prefer exact checking of integers, rational numbers, and symbolic expressions.
Floating-point values, numerical eigenvalue calculations, and ordinary SDP
outputs cannot directly establish strict proofs.

When numerical methods are used for discovery or synthesis, produce additional
kernel-checkable evidence such as rigorous error bounds, interval certificates,
or rational reconstruction. Numerical search remains outside the trusted base.

## 13. Public admission and provenance

One successful Lean compilation does not automatically admit a result to the
library. An admitted theorem requires a stable name and namespace, explicit
provenance, reproducible construction with pinned dependencies, and access
through the unified public interface. For example:

```lean
import powerlib
#check powerlib.lcl_stable_iff
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

| Status | Meaning and required evidence |
| --- | --- |
| Note | Nonformal derivation, computation, or experiment; no admitted domain claim. |
| Foundation | Kernel-checked Lean/Agda infrastructure such as conversion, equivalence, or algebraic lemmas. |
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
