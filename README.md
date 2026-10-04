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

## Model boundaries and completed results

The RL family is `L*i' = v - R*i`, with state order `[i]`, physical scalar
branch current in stationary coordinates (no dq transformation). Time is
continuous, `L > 0`, and `R` is real; strict stability requires `R > 0`.
Voltage is positive in the stated current direction and resistance opposes
current. There is no controller or feedback interconnection, PWM, PLL, delay,
switching, sampling, or additional state. The voltage input is held constant.
Perturbations are around an equilibrium `R*e = v`, not a time-varying trajectory.

`theorems/RLStability.lean` proves forward existence and uniqueness, the exact
perturbation equation, and epsilon-delta stability plus attraction if and only
if `R > 0`. An accepted certificate entails global asymptotic and exponential
stability for every forward solution, and the actual trajectory derivative
of `V = p*(i-e)^2` is `-(i-e)^2`. Linearity makes this an exact small-signal
result. `synthesize` also constructs certificates for symbolic real parameters.
The ATP command accepts exact rational model parameters without a supplied
witness and concludes `Admission.small_signal`; its achieved maturity is S-level.

The LCL family has stationary scalar state order `[i1, vc, i2]` and external
inputs `[u, vg]`. Its continuous-time equations fix all port signs:
`L1*i1' = u - R1*i1 - vc`, `C*vc' = i1 - i2`,
`L2*i2' = vc - R2*i2 - vg`. Both inductances and capacitance are positive;
resistances are real, with nonnegativity required by passive-family theorems.
There is no controller or feedback interconnection, PLL, PWM, delay, sampling,
switching, or additional grid dynamics. Perturbations are about constant-input
equilibria, with both input perturbations fixed at zero.

LCL's public `Stable` predicate concerns the formal internal state-matrix
poles. For passive resistances it holds exactly when they are not both zero.
ATP synthesizes a rational Lyapunov matrix and Lean derives this spectral
stability theorem, positive energy and strict dissipation. LCL does not yet
export RL's arbitrary-trajectory epsilon-delta and convergence theorems.

```sh
python3 dependencies/powerlib.py atp dependencies/examples/lcl.json --family lcl
python3 dependencies/powerlib.py atd --family lcl
```

Both `atd` commands are fixed-candidate verification prototypes, not
ATD-discovered results. Refutations have their own checked Lean negation
theorems; search failure alone remains `UNPROVED`.

## Public automation and admission

`import powerlib` exposes both families and their named general theorems.
`powerlib_foundation` and `powerlib_domain` classify the public results;
`powerlib.Registry.theoremNames` discovers them. Standard `simp`, `ext` and
`aesop` interfaces remain available. `powerlib_auto` additionally searches all
imported `powerlib` theorems without requiring the caller to name them:

```lean
import powerlib

example (m : powerlib.Impedance) (c : powerlib.Accepted m) :
    powerlib.AsymptoticallyStable m 0 0 := by
  powerlib_auto

example (m : powerlib.LCL.Circuit) (c : powerlib.LCL.Accepted m) :
    (powerlib.LCL.toStateSpace m).Stable := by
  powerlib_auto
```

New formal modules must be imported before registration in
`theorems/Automation.lean`. Search is bounded and can fail; it never admits an
unproved goal. Exhaustive independent consumers check every imported theorem's
exact type, including its universe parameters, and audit the resulting proofs.

Admission audits all safe `powerlib` declarations and all registered theorems,
including current-file registrations outside that namespace. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. Compiler-only unsafe executable
implementations are excluded; every theorem and its proof dependencies are
checked. Intentional negative fixtures must be rejected.

Each accepted ATP artifact retains the original submitted JSON, normalized
model, theorem names, proof and kernel-log hashes, dependency revisions and
lockfile hash, public Lean source hashes, and both Agda conversion reports.
Those reports bind Agda/Cubical versions, source hashes, versioned normalized
wire data, generated Lean hashes, endpoint proofs and verification logs.
Dependencies and conversion evidence are checked for mismatches. Generated
certificates instantiate public theorems; they are not automatically new
library theorems. Hashes identify evidence; Lean/Agda establish correctness.

After installing the pinned Lean toolchain, run the complete verification:

```sh
python3 dependencies/setup.py
python3 dependencies/lcl_bridge.py
python3 dependencies/check_automatic.py
POWERLIB_LCL_KERNEL_TESTS=1 python3 -m unittest discover -s dependencies/tests -v
```

CI also runs both ATP and both fixed-candidate commands and retains the proof
artifacts. The formalization directory is checked to contain no Markdown.
Archived experiments are outside the public imported library.
