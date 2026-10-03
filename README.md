# powerlib

powerlib is a theorem library for power systems and power electronics, built on Lean 4 and Agda.

## Directions

- **ATP (Automated Theorem Proving):** automatically prove given propositions, including **synthesis of certificates**.
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
level, including synthesizing certificates, and exploring the potential of ATD.

## Quick Start

From the repository root, with Lean/Elan, Git, and Python 3.12+ on Linux x86_64:

```sh
python3 scripts/setup.py
python3 scripts/powerlib.py atp examples/rl.json
python3 scripts/powerlib.py atd
lake env lean examples/Use.lean
```

Setup installs pinned dependencies locally and checks Agda and Lean. ATP returns
`ACCEPTED` only after Lean verifies the synthesized certificate for the submitted
model. ATD searches three resistance sign conditions and checks proofs or
counterexamples. Proof files, logs, and reports are saved under `results/`.

The first example is a canonical single-port RL circuit with `L > 0`:
`i' = -(R/L)i + (1/L)v`, equivalent to `Z(s) = R + Ls`. For `R = 2`, `L = 1`,
ATP produces `V(i) = (1/4)i^2` and the squared-current decay rate `4`.
Edit [examples/rl.json](examples/rl.json) using integers or rational strings such
as `"3/2"`; strict stability requires `R > 0`.
Here voltage is the input, so the impedance criterion checks that zeros of `Z(s)`
(poles of `1/Z(s)`) lie in the open left half-plane.

To use the library in Lean, start with `import powerlib`:

```lean
import powerlib

example (m : powerlib.Impedance) :
    (powerlib.toStateSpace m).Stable ↔ m.Stable :=
  powerlib.stability_agrees m
```

Agda checks the abstract model equivalence and theorem transport. Its executable
conversion is exported through a small data interface; Lean independently proves
the concrete real-number equivalence, port relation, and stability results.
This first system covers the canonical RL family.

Recheck the bridge with `python3 scripts/bridge.py`; run the acceptance tests with
`python3 -m unittest discover -s tests -v`.
