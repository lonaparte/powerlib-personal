# powerlib

powerlib is a theorem library for power systems and power electronics, built on Lean 4 and Agda.

Agda is the foundation for structures, representation conversions, equivalences,
and transport. Lean 4 is the public theorem layer: every admitted domain result
must end in a kernel-checked Lean theorem. The project's requirements for models,
semantic theorems, synthesis, admission, provenance, and result maturity are
defined in [Rules.md](Rules.md).

## Version compatibility

The project pins Lean 4.34.1 and Mathlib v4.34.1.

When toolchain or dependency versions do not match, first adapt incompatible
dependencies to the project's current pinned Lean and Mathlib versions and retry
the pinned build. Check compatible older upstream revisions, or make minimal local
compatibility changes to the dependency code, before considering a project
toolchain upgrade. The absence of a matching historical pin does not establish
incompatibility. Preserve upstream provenance and theorem contracts, keep all pins
explicit, and require the complete build and proof checks to pass together.

## Dependency locations

Keep complete upstream checkouts outside the repository. For a repository at
`<workspace>/<repository>`, use these external locations with the commits pinned
in the applicable `lake-manifest.json`:

- Mathlib: `<workspace>/support/upstream/mathlib`.
- LeanForControl: `<workspace>/support/upstream/LeanForControl`.

The main package's ignored `.lake/packages` directory and the isolated profile's
ignored `dependencies/integrations/leanforcontrol/.lake/packages` directory must
link to `<workspace>/support/upstream`. Lake resolves imported
modules through those links. LeanForControl is used by the isolated profile;
install it for the main package when its manifest also requires it. Complete
upstream sources and compiled caches are not repository files. Only necessary
interfaces, formal consumers, exact compatibility changes, and version pins belong
in the published project. CI stores upstream checkouts in its runner temporary
directory.

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
