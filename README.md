# powerlib

powerlib is a theorem library for power systems and power electronics, built on Lean 4 and Agda.

## Directions

- **ATP (Automated Theorem Proving):** automatically prove given propositions, especially **synthesis of certificates**.
- **ATE (Automated Theory Exploration):** explore models and existing knowledge, prove useful conjectures, and add the resulting theorems to the library.

We are exploring a combination in which Agda serves as the foundation for
conversions between modeling approaches, while Lean 4 supports everyday
reasoning. We draw inspiration from
[mathlib](https://github.com/leanprover-community/mathlib4) and
[LeanForControl](https://github.com/AnandGokhale/LeanForControl).

We recognize that power systems and power electronics have fewer general
theorems than mathematics and control theory. Much of the knowledge concerns
specific operating conditions, hardware, control methods, and their combinations.
We see this as a good experimental setting for making ATP work at the synthesis
level and exploring the potential of ATE.

## Quick Start

Run ATP and ATE on the RL example:

```sh
python3 dependencies/powerlib.py atp dependencies/examples/rl.json
python3 dependencies/powerlib.py ate
```

For `R = 2`, `L = 1`, ATP synthesizes `V(i) = i²/4` and returns `ACCEPTED`
after Lean verifies the certificate. ATE checks three candidate stability conditions.

Use a theorem in Lean:

```lean
import powerlib

example (m : powerlib.Impedance) :
    (powerlib.toStateSpace m).Stable ↔ m.Stable :=
  powerlib.stability_agrees m
```
