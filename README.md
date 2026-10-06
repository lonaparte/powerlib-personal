# powerlib

powerlib is a theorem library for power systems and power electronics, built on Lean 4 and Agda.

Development takes place first in the private repository with the maintainer and Codex, and is periodically synchronized to the public repository.

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

## Structure

Agda supplies foundational structures and conversions; Lean 4 exposes every
admitted domain result as a kernel-checked theorem. The project pins Lean 4.34.1,
Mathlib v4.34.1, and Agda 2.8.0. Adapt dependencies to these pins with minimal,
provenance-preserving changes, and accept them only after the complete build and
proof checks pass. See [Rules.md](Rules.md) for the formal requirements.

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
