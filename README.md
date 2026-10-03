# Powerlib

Powerlib is a theorem library for power systems and power electronics, built on Lean 4 and Agda.

Agda provides the foundation for transporting theorems between equivalent modeling systems. Lean 4 handles the main reasoning and proof work.

## Directions

- **ATD (Automated Theorem Discovery):** discover new conjectures from models and existing knowledge, prove them, and add the results to the library.
- **ATP (Automated Theorem Proving):** automatically prove given propositions, including **synthesis of certificates**.

## Quick Start

With Lean/Elan installed, run from the repository root to check an existing theorem file:

```sh
cd archive/01/lean
lean PHGeneral.lean
```

Elan selects the pinned Lean version. See [archive/](archive/) for the current theorem collections and their usage instructions.
