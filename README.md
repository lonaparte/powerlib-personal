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

## Arbitrary-dimensional LTI stability

Submit a nonempty square rational matrix, with coordinates ordered as
`x[0], ..., x[n-1]`, for the continuous-time autonomous system `x' = A x`:

```json
{"A": [[-1, 10], [0, -1]]}
```

```sh
python3 dependencies/powerlib.py atp dependencies/examples/lti.json --family lti
```

Use integers or exact rational strings such as `"3/2"`; floats and supplied
witnesses are excluded from this ATP input. The exact solver finds `P` from
`AᵀP + PA = -I` and rational bounds `0 < lower`, `0 < upper`,
`lower‖x‖₂² ≤ xᵀPx ≤ upper‖x‖₂²`. Rational LDL decompositions produce
sum-of-squares evidence. Lean independently checks the original submitted
matrix, the certificate, the trajectory theorem, and all transitive axioms.

The public theorem `powerlib.LTI.Accepted.exponentially_stable` is quantified
over every finite dimension, using Mathlib's Euclidean norm. `Accepted.norm_bound`
proves `‖x(t)‖₂ ≤ sqrt(upper/lower) exp(-t/(2 upper)) ‖x(0)‖₂` for `t ≥ 0`;
`Accepted.decay_bound` provides the equivalent squared-norm estimate.
`trajectory_exists` constructs a global solution; `Accepted.response_unique`
identifies every global solution with it for `t ≥ 0`, and `Accepted.sqNorm_tendsto_zero`
proves convergence. These named theorems are available through `import powerlib`
and the theorem registry. Agda checks the matrix/row representation equivalence
and executable field operation; Lean independently checks its exported endpoint.

`ACCEPTED` means S-level for this witness-free ATP path. A supplied certificate
checked by `lti.admit` is verification, not synthesis. Synthesis failure is
`UNPROVED`, not a formal instability result. The Python search/termination and
the converse Lyapunov theorem are not themselves claimed as Lean theorems.

The matrix is the submitted model. Any controller states must already be
included. This result does not establish a missing circuit-to-matrix derivation,
nonlinear linearization, parameter uncertainty, switching, delays, PWM, PLL,
or DAE reduction. Large dimensions and rational bit sizes can be expensive.
