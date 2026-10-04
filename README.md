# powerlib

powerlib is a theorem library for power systems and power electronics, built on Lean 4 and Agda.

Agda is the foundation for structures, representation conversions, equivalences,
and transport. Lean 4 is the public theorem layer: every admitted domain result
must end in a kernel-checked Lean theorem. The project's requirements for models,
semantic theorems, synthesis, admission, provenance, and result maturity are
defined in [Rules.md](Rules.md).

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

## Quick Start

Run ATP and the fixed-candidate ATD prototype on the RL example:

```sh
python3 dependencies/powerlib.py atp dependencies/examples/rl.json
python3 dependencies/powerlib.py atd
```

For `R = 2`, `L = 1`, ATP synthesizes `V(i) = i²/4` and returns `ACCEPTED`
after Lean verifies the certificate and derives its model-bound theorems.
The `atd` prototype checks three manually enumerated stability conditions; it
does not yet generate conjectures or constitute complete theorem discovery.

Use a theorem in Lean:

```lean
import powerlib

example (m : powerlib.Impedance) :
    (powerlib.toStateSpace m).Stable ↔ m.Stable :=
  powerlib.stability_agrees m
```

## Canonical LCL plant

The LCL family has stationary scalar phase states `(i1, vc, i2)` and external
terminal voltages `(u, vg)`. Its continuous-time equations are
`L1*i1' = u - R1*i1 - vc`, `C*vc' = i1 - i2`, and
`L2*i2' = vc - R2*i2 - vg`. Inductances and capacitance are strictly positive.
The model includes no controller, PLL, PWM, delay, or additional grid dynamics.
It is linear; perturbations about a constant-input equilibrium use the same
state matrix with terminal input perturbations held at zero.

Here `Stable` means all poles of the formal internal state matrix lie strictly
in the open left half-plane. For nonnegative resistances, the public theorem
states that this holds exactly when the two resistances are not both zero:

```lean
import powerlib

#check powerlib.lcl_stable_iff
#check powerlib.LCL.Accepted.stable
```

The Agda conversion reuses the RL branch conversion twice and converts the
capacitor gain. Lean checks its exported endpoint, the physical equations,
the state matrix, its characteristic polynomial, and the stability theorem.
ATP solves the symmetric Lyapunov equations in exact rational arithmetic to
find `P` from model parameters alone. Lean independently reconstructs the
submitted model, checks the indexed certificate and its transitive axioms,
and derives stability, positive energy, and strict energy dissipation.

```sh
python3 dependencies/powerlib.py atp dependencies/examples/lcl.json --family lcl
python3 dependencies/powerlib.py atd --family lcl
```

The LCL `atd` command is also a fixed-candidate verification prototype.
Generated model-specific proofs remain proof artifacts; the public general
theorems are available through `import powerlib`. CI retains proof artifacts,
model and dependency provenance, and kernel logs for review and reproduction.
