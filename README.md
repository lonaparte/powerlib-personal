# powerlib

powerlib is a theorem library for power systems and power electronics, built on Lean 4 and Agda.

Development takes place first in the private repository with the maintainer and coding agents, and is periodically synchronized to the public repository.

## Directions

- **ATP (Automated Theorem Proving):** prove given propositions, with certificate synthesis as the default target.
- **ATD (Automated Theorem Discovery):** generate conjectures, prove or refute them, and admit the verified results.

PowerLib follows the direct-reuse principles of [Mathlib](https://github.com/leanprover-community/mathlib4) and [LeanForControl](https://github.com/AnandGokhale/LeanForControl).

## Structure

Agda provides foundational scaffolds for structures and connections. Lean 4 is the public theorem layer, and every admitted result ends in a kernel-checked Lean theorem. Formal sources live in `theorem/`, public consumers in `example/`, and dependency interfaces, integration profiles, and necessary verification consumers in `dependencies/`. The formalization, classification, provenance, and admission requirements are defined in [Rules.md](Rules.md).

The project pins Lean 4.34.1, Mathlib v4.34.1, Agda 2.8.0, and Cubical 0.9.

## Dependencies

Lake resolves pinned Mathlib and LeanForControl checkouts as repository siblings:

```text
<parent>/
  powerlib/
  mathlib/
  LeanForControl/
```

The import interfaces are in `dependencies/`; first-party proofs remain in `theorem/`. Upstream sources and caches remain outside this repository. From the repository root, prepare the pinned clean LeanForControl checkout, download Mathlib's precompiled cache, and build serially:

```sh
patch="$PWD/dependencies/LeanForControl-4.34.1.patch"
git -C ../LeanForControl apply --check "$patch"
git -C ../LeanForControl apply "$patch"
lake exe cache get
lake build
(cd dependencies/integrations/leanforcontrol && lake build)
```
