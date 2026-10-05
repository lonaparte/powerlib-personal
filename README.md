# powerlib

powerlib is a theorem library for power systems and power electronics, built on Lean 4 and Agda.

Agda is the foundation for structures, representation conversions, equivalences,
and transport. Lean 4 is the public theorem layer: every admitted domain result
must end in a kernel-checked Lean theorem. The project's requirements for models,
semantic theorems, synthesis, admission, provenance, and result maturity are
defined in [Rules.md](Rules.md).

## Version compatibility

This package pins Lean 4.30.0-rc2 and Mathlib v4.30.0-rc2.
The isolated LeanForControl profile pins Lean and Mathlib v4.30.0-rc2.

When toolchain or dependency versions do not match, first adapt incompatible
dependencies to the project's current pinned Lean and Mathlib versions and retry
the pinned build. Check compatible older upstream revisions, or make minimal local
compatibility changes to the dependency code, before considering a project
toolchain upgrade. The absence of a matching historical pin does not establish
incompatibility. Preserve upstream provenance and theorem contracts, keep all pins
explicit, and require the complete build and proof checks to pass together.

## Directions

- **ATP (Automated Theorem Proving):** automatically prove given propositions, especially **synthesis of certificates**.
- **ATD (Automated Theorem Discovery):** discover new conjectures from models and existing knowledge, prove them, and add the results to the library.

We are exploring a combination in which Agda serves as the foundation for
conversions between modeling approaches, while Lean 4 supports everyday
reasoning. We draw inspiration from
[mathlib](https://github.com/leanprover-community/mathlib4) and
[LeanForControl](https://github.com/AnandGokhale/LeanForControl).

We recognize that power systems and power electronics have fewer general
theorems than mathematics and control theory. Much of the knowledge concerns
specific operating conditions, hardware, control methods, and their combinations.
We see this as a good experimental setting for making ATP work at the synthesis
level and exploring the potential of ATD.

Development takes place first in the private repository with the maintainer and Codex, and is periodically synchronized to the public repository.
