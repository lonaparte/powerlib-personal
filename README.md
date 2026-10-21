# powerlib

powerlib is a theorem library for power systems and power electronics. Its theorems are proved in Lean 4; Agda is the scaffolding between its different contents.

Development takes place first in the private repository with the maintainer and coding agents, and is periodically synchronized to the public repository. The whole library is developed in one role: no part of it is reserved to one agent.

## Directions

- **ATP (Automated Theorem Proving):** automatically prove given propositions, especially **synthesis of certificates**.
- **ATD (Automated Theorem Discovery):** discover new conjectures from models and existing knowledge, prove them, and add the results to the library.

Agda is the scaffolding between the different contents of the library: models,
representations and layers. Every connection between them is first constructed
in Agda, which fixes its statement, its generality and the structure it must
preserve; Lean 4 then proves the connection independently. We draw inspiration from
[mathlib](https://github.com/leanprover-community/mathlib4) and
[LeanForControl](https://github.com/AnandGokhale/LeanForControl).

We recognize that power systems and power electronics have fewer general
theorems than mathematics and control theory. Much of the knowledge concerns
specific operating conditions, hardware, control methods, and their combinations.
We see this as a good experimental setting for making ATP work at the synthesis
level and exploring the potential of ATD.

## Structure

Lean 4 is the only theorem layer: it proves every admitted result, and the library
builds and checks without Agda. The Agda scaffolds stay in `theorem/` as the design
records of the connections they built; only data passes between Agda and Lean, and
Lean checks it independently. The project pins Lean 4.34.1,
Mathlib v4.34.1, and Agda 2.8.0. Adapt dependencies to these pins with minimal,
provenance-preserving changes, and accept them only after the complete build and
proof checks pass. See [Rules.md](Rules.md) for the six meta-rules and the formal
requirements, and [Architecture.md](Architecture.md) for generated connections,
admission and proved completion boundaries. [Layers.md](Layers.md) defines the theory, model,
implementation and observation layers and how results are placed in them.

Public model results use `connection% (ordinary proposition)`. The resulting
`TMIO.Statement` carries a kernel-checked certificate that the conclusion evaluates
or compares generated connections. Classification annotations are optional search
metadata. `lake build` and `lake build powerlib` check the actual module inventory,
including new modules that omit the architecture linter import. Internal library
targets provide compilation only; they do not run whole-package admission.

## Dependencies

Lake resolves pinned Mathlib and LeanForControl checkouts as siblings of the
repository:

```text
<parent>/
  powerlib/
  mathlib/
  LeanForControl/
```

The private repository uses the same layout. Its import interfaces are
`dependencies/Mathlib.lean` and `dependencies/LeanForControl.lean`; first-party
proofs belong in `theorem/`. Upstream sources and caches remain outside the
repository.

After installing Elan, run from the repository root:

```sh
compatibility_patch="$PWD/dependencies/LeanForControl-4.34.1.patch"
git -C ../LeanForControl apply --check "$compatibility_patch"
git -C ../LeanForControl apply "$compatibility_patch"
lake exe cache get
lake build
(cd dependencies/integrations/leanforcontrol && lake exe cache get && lake build)
```

Apply the compatibility diff only to the pinned clean LeanForControl checkout;
the checks verify its source identity and exact diff.
