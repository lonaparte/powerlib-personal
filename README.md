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

## Passivity and stability

`import powerlib` exposes the general continuous-time state-space model
`x' = A x + B u`, `y = C x + D u` in `powerlib.StateSpacePassivity`.
State and port dimensions are arbitrary finite types. A model-indexed
`Certificate` contains a symmetric positive definite matrix `P` and the full
quadratic KYP inequality
`(P*x)ᵀ*(A*x+B*u) <= uᵀ*(C*x+D*u)` for every state and input.
It permits off-diagonal storage, feedthrough, and noncollocated ports.
`MatrixCertificate` checks the equivalent full block KYP dissipation matrix
and converts it to this trajectory certificate.
`CollocatedCertificate` provides a sufficient construction from matrix
positivity, dissipation, and the checked port relation `P*B = Cᵀ`.

The common theorem proves the derivative of `H(x) = xᵀ*P*x/2` along the
model's actual ODE trajectories, and derives integral input-output passivity
and epsilon-delta Lyapunov stability of the zero-input origin.
`StateSpaceTrajectories` proves global zero-input solution existence and
uniqueness for every model, independently of a storage certificate, using
Mathlib's operator exponential and ODE uniqueness theorem. Translation by
an existing constant-input equilibrium also proves its stability and global
solution existence. These results concern finite-dimensional real linear
models with constant coefficients.

The underlying semantic port-system interface in `powerlib.Passivity` also
supports general normed real state spaces. A differential storage contract
connects its field to the derivative along actual forward trajectories. The public
`QuadraticStorage.passiveWithStorage` theorem establishes nonnegative storage
and the input-output energy inequality. `PassiveWithStorage.lyapunovStable_of_bounds`
derives epsilon-delta stability from that integral passivity and coercivity;
`QuadraticStorage.lyapunovStable` supplies those bounds automatically for
continuous, positive quadratic storage. The origin
must be an equilibrium; solution existence remains an explicit model obligation.

The cases instantiate the common state-space theorem through checked matrix,
energy, trajectory, and equilibrium correspondences. They do not repeat its
storage calculus or stability proof.

`powerlib.RLPort` derives the one-state terminal model from the checked Agda
RL conversion: `A = -R/L`, `B = 1/L`, `C = 1`, `D = 0`, with physical
magnetic storage `L*i^2/2`. Positive inductance and nonnegative resistance,
including a lossless inductor, construct its certificate from model parameters.

`powerlib.PortHamiltonian` instantiates the common theorem in arbitrary nonempty
finite dimension for the original linear model
`x' = (J - diag d) diag w x + B u`, with `J` skew, `w > 0`, `d >= 0`,
and output `y = B^T diag w x`. Its `storage` is constructed from the model
parameters. The public `passiveWithStorage` and `lyapunovStable` theorems
establish passivity and zero-input stability. Its trajectory results also
reuse the general state-space theorems.

The LCL instance uses the checked Agda-to-Lean circuit conversion. Its state
order is converter current, capacitor voltage, grid current; terminal inputs
are converter and grid voltages, with outputs converter current and negative
grid current. The storage is `(L1*i1^2 + C*vc^2 + L2*i2^2)/2`.
`powerlib.LCL.physical_integral_passivity` handles varying terminal inputs
with integrable supplied power. `powerlib.LCL.passive_lyapunovStable_via_ports`
uses this storage contract to prove stability about every existing
constant-input equilibrium. Forward existence and uniqueness are proved for
the original circuit, including the lossless case.

To automatically construct and admit a physical storage certificate from only
the component parameters:

```bash
python3 dependencies/powerlib.py atp dependencies/examples/lcl-lossless.json --family lcl --goal passive-stability
```

This target requires nonnegative resistances and positive inductances and
capacitance. It includes zero resistance and concludes Lyapunov stability.
The separate default `exponential-stability` target synthesizes a strict
Lyapunov certificate; passive LCL plants additionally need nonzero damping
for that stronger conclusion. The model is an ideal continuous-time plant
in stationary scalar coordinates, without a controller, PLL, PWM, or delay.

Admission independently reconstructs the submitted circuit, checks the proposed
storage matrix in Lean, audits transitive axioms, and retains the original input,
proof, dependency pins, bridge evidence, and source hashes. Supplying an existing
certificate through `dependencies/passivity.py verify` is reported as certificate
verification. ATP reports S-level only after automatic construction and all kernel
checks complete.

The general certificate-to-property implications and checked model instances
are public Lean theorems. Arbitrary `A,B,C,D` certificate synthesis is not an
S-level command; the witness-free LCL command above is the currently admitted
S-level passivity path.

The public import contains the mathematical model and theorem modules directly.
Reusable facts carry native `simp`, `ext`, or Aesop attributes where appropriate;
ordinary `simp`, `aesop`, and `exact?` can combine them with Mathlib declarations.
There is no private proof-search tactic or bulk theorem rule set. The independent
verification consumers in `dependencies/tests/NativeTheoremUse.lean` and
`dependencies/tests/StateSpacePassivityCases.lean` exercise these interfaces and
audit their completed proof terms. They include a two-state example with
off-diagonal `P`, nonzero `D`, and `P*B != Cᵀ`, plus kernel-checked rejection
of an indefinite storage matrix and reversed port sign. Declaration inspection
is verification support in `dependencies/TheoremInspection.lean`, outside the
public mathematical import.

```lean
import powerlib

example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty ι]
    (m : powerlib.StateSpacePassivity.Model ι κ)
    (c : powerlib.StateSpacePassivity.Certificate m) :
    powerlib.Passivity.LyapunovStable (powerlib.StateSpacePassivity.system m) := by
  aesop
```

The analytic steps directly reuse pinned Mathlib `v4.19.0` declarations
`antitoneOn_of_hasDerivWithinAt_nonpos` and
`intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le`; the upstream reuse
check verifies the actual proof references and axiom dependencies. LeanForControl's
`lyapunov_stable` was inspected at commit
`7507ed04d94068fe3e7d4624b3383433a861bea7`, but that version requires Lean/Mathlib
`v4.30.0-rc2` and is not an imported dependency of this `v4.19.0` build.
