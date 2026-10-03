# Powerlib Personal

This private repository is the development workspace for Powerlib, an axiomatic
library for power electronics and power systems. Its goal is to automate the
discovery and proof of mathematical results about explicitly defined models.

## Two Directions

### ATD: Automated Theorem Discovery

ATD starts from models, definitions, assumptions, and existing theorems to propose
new conjectures, useful conditions, and reusable lemmas. Candidate statements
must be proved and checked before they become accepted library results.

### ATP: Automated Theorem Proving, Including Synthesis

ATP starts from a specified proposition and its assumptions, then automatically
constructs a proof. It may apply existing theorems, simplify expressions, search
for intermediate lemmas, or use specialized procedures.

**ATP includes synthesis of certificates and other required witnesses.** When a
problem requires an object, the workflow must generate that object and prove
that it satisfies the specification. An existence theorem alone does not fulfill
a request for a concrete certificate.

For small-signal stability, the intended workflow takes a model and operating
point, synthesizes a Lyapunov matrix and any required neighborhood and decay
bounds, and produces Lean-checked proofs about the original input model. The
caller should not have to supply the stability certificate or its validity proof.

Failure to find a proof or certificate is inconclusive; it is not a proof that
the proposition is false or that the system is unstable.

## Development Cycle

```text
Models and existing knowledge
    -> ATD proposes conjectures
    -> ATP proves them, using synthesis when needed
    -> Formal proof checking
    -> Review and library integration
    -> Expanded knowledge for future discovery and proving
```

ATP also accepts user-specified propositions directly. Develop is the engineering
workflow for building and maintaining the definitions, theorems, synthesis
algorithms, and checking interfaces that support both directions.

Lean checks formal mathematical proofs. Agda/Cubical supports equivalences and
transport where explicitly established. Begin with a minimal end-to-end example;
introduce shared abstractions as concrete examples require them. These directions
describe the development goals, rather than a claim that every capability is
already implemented.

## Repository Workflow

Daily development and library integration happen in `powerlib-personal`.
Completed changes are validated as appropriate and committed automatically;
pushing follows the owner's instructions. After personal review, the owner
transfers selected results to `powerlib`. Changes to that repository require
explicit authorization.

All repository content and commit messages are written in English. Day-to-day
conversation may be in Chinese. Earlier development materials are kept in
`archive/`.
