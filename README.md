# powerlib

powerlib is a theorem library for power systems and power electronics, built on Lean 4 and Agda.

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

Run ATP and ATD on the RL example:

```sh
python3 dependencies/powerlib.py atp dependencies/examples/rl.json
python3 dependencies/powerlib.py atd
```

For `R = 2`, `L = 1`, ATP synthesizes `V(i) = i²/4` and returns `ACCEPTED`
after Lean verifies the certificate and its trajectory-level consequences.
ATD checks three candidate asymptotic-stability conditions.

Use a theorem in Lean:

```lean
import powerlib

example (m : powerlib.Impedance) :
    (powerlib.toStateSpace m).Stable ↔ m.Stable :=
  powerlib.stability_agrees m
```

## RL stability contract

The model is `L*i' + R*i = v`, with `L > 0`, physical current as the only
state, and constant voltage input. For every equilibrium `R*e = v`, Lean proves:

- Forward solutions exist for every initial current and are unique on `[0, ∞)`.
- The perturbation `i - e` obeys the exact autonomous RL equation.
- Epsilon-delta stability plus local attraction holds if and only if `R > 0`.
- An accepted certificate implies global asymptotic and global exponential
  stability, for **every** forward solution, not just a selected explicit one.
- Along every such trajectory, `V = p*(i-e)^2` has derivative `-(i-e)^2`, and
  `(i(t)-e)^2 = (i(0)-e)^2 * exp(-rate*t)` for `t >= 0`.

Because this model is linear, these conclusions cover small-signal stability
without a linearization approximation. Time-varying input disturbances and
nonlinear or hidden-state models are outside this contract.

`theorems/RLStability.lean` defines the trajectory-level predicates explicitly;
they are not aliases for a coefficient sign. `synthesize` also constructs a
symbolic certificate for arbitrary real parameters satisfying `R > 0`.
The executable ATP frontend accepts exact rational parameters and synthesizes
the witness before Lean checks it. The ATD example is a finite search over
three predefined sign conditions, using existing library theorems; it is not
open-ended conjecture generation.

## Automatic theorem reuse and verification

`import powerlib` imports the complete active Lean API. All public theorems in
the `powerlib` namespace are automatically registered in the `PowerLib` Aesop
rule set. Use `powerlib_auto` to search it without supplying theorem names:

```lean
import powerlib

example (m : powerlib.Impedance) (c : powerlib.Accepted m) :
    powerlib.AsymptoticallyStable m 0 0 := by
  powerlib_auto
```

Proof search is not guaranteed for every possible goal: failure rejects the
goal. New theorem modules belong before the registration step in
`theorems/Automation.lean`. `dependencies/tests/Automatic.lean` exercises the
public API independently, including conversions, certificate consumers and
trajectory results, and automatically re-proves every exported theorem's type
using `powerlib_auto` without passing the theorem name to the tactic.

After installing Lean from `lean-toolchain`, run:

```sh
python3 dependencies/setup.py
python3 dependencies/check_automatic.py
python3 -m unittest discover -s dependencies/tests -v
```

The kernel audit traverses every safe declaration in the `powerlib` namespace
(including every theorem; compiler-only unsafe implementations are excluded),
not a manually maintained theorem list. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. `sorryAx` and additional axioms are rejected; tests
deliberately inject them and require rejection. ATP and ATD outputs are audited
as well. Archived experiments are not part of the active imported library.
