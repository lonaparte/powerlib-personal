# Building the implementation layer

Status: the discrete-time kind of the semantic layer (§3.1–3.2), the generic bridges (§3.5) and
the continuous-time implementation families are in the library. The limit sentences (§3.3), the
approximation relation (§3.4) and the hybrid kind are proposals awaiting decisions (§5).

[Layers.md](Layers.md) defines the implementation layer: a model under realistic constraints
(digitization, switching, physical limits, tolerances, numerical integration), with its own
behaviour, related to the model it realizes. The interface (`theorem/Stack/Implementation.lean`)
is complete for implementations whose behaviour the semantic layer can read. This document
records what the semantic layer cannot yet read, what each kind of implementation needs, and a
staged plan.

## 1. The obstacle

Before the discrete kind (§3.1), the semantic layer (`theorem/Flow/Defs.lean`,
`theorem/Port/Defs.lean`) read only complete autonomous vector fields in continuous time; its
header excludes delay, sampling, PWM and switching. A family's system map returned a
`Port.System`, so a discrete-time controller, a numerical scheme or a switched converter could
not be an implementation family. The library model
families confirm the gap from the other side: their model boundaries list delay, PWM, sampling
and saturation among the exclusions.

Continuous surrogates are possible but are themselves models of the implementation with their
own error. For the IMC-tuned PI current loop with a one-sample computation delay, zero-order
hold and a forward-Euler integrator, the exact sampled-data stability boundary tends to
`ω_b Tₛ = 1` as `R → 0` (proved for the limiting loop, `LTI.schurStable_integratorDelay_iff`) and
is about `1 + R Tₛ/(2L)` for small `R Tₛ/L` (numerical scan of the lifted 3×3 map; non-monotone
for large `R Tₛ/L`, about `0.65` at `R Tₛ/L = 10`). The pure-delay surrogate gives `π/3 ≈ 1.047`,
and the Padé(1,1) surrogate of `CurrentControl/DigitalPI.lean` gives `4/3`, a third too
optimistic: for `ω_b Tₛ` between the exact boundary and `4/3` the surrogate platform is stable
and the sampled loop is not.

Upstream offers little: Mathlib and LeanForControl have no stability notions for maps, no
switched, hybrid, Filippov or Carathéodory systems, no sampled-data or discretization theorems,
no saturation, quantization or sector theory, and no Floquet theory. LeanForControl's
time-varying stability theorems rest on its unproved axioms and cannot be used.

## 2. What each implementation needs

| Phenomenon | Mathematical object | Sentences | Realization | Library tools | Semantic need |
| --- | --- | --- | --- | --- | --- |
| Sensor and actuator dynamics, filters, delay surrogates | augmented ODE | existing | design map | `Delay/*`, `GFM/VSMLPFRig`, `CurrentControl/DigitalPI` | none |
| Parameter tolerance, aging | same ODE, parameter set | existing | relation (tolerance set) | `CurrentControl/Mismatch`, `SingularPerturbation/FrozenFast` | none |
| Continuous hardware limits (voltage, modulation, current, rate limiter) | Lipschitz nonlinear ODE | local sentences carry over with headroom; global ones fail | design map | `CurrentControl/VoltageLimit`, `Dynamics/Locality`, `Drives/Modulation`, `Limiting/*` | new sentences (§3.3) |
| Digital control: sampling, ZOH, computation delay, controller discretization (Euler, Tustin, ZOH equivalent), deadbeat, MPC | sampled-data system; lifted map at the sampling instants | stability of the lifted map, with an intersample bound | design map | `LTI/Discrete`, `Dynamics/VariationOfConstants`, `Numerics/LinearSchemes`, `Drives/PredictiveControl`, `LTI/Sampling` | discrete-time kind |
| Quantization (ADC, DPWM), finite word length | discontinuous map | practical stability (ultimate bound) | design map | none | discrete-time kind, new sentences |
| Numerical simulation (EMT, integrators) | one-step map | stability of the map; global error | design map; approximation relation (§3.4) | `Numerics/*`, `Numerics/EMT/*` | discrete-time kind |
| PWM switching with ideal switches, CCM | periodic piecewise-in-time ODE; period map | uniform stability of the periodic system, or stability of the period map | design map to the averaged model; approximation | `Averaging/*`, `Periodic/*`, `Averaging/SwitchedStability` | periodic kind, or the period map read by the discrete-time kind |
| State-dependent switching: DCM, diodes, hysteresis control, current-limit mode changes, protection | hybrid system (flows and jumps) | hybrid stability | design map | written-out trajectories in `Frequency/UFLSLatched`, `Synchronous/FaultSequence` | hybrid kind (second time axis) |
| Dead time | discontinuous in the current sign (Filippov) | as above | design map | none | hybrid or Filippov kind |
| Device switching transients | stiff fast dynamics | usually excluded by the ideal-switch boundary | singular perturbation | `SingularPerturbation/*` | none (boundary) |
| Process noise | SDE | mean-square or almost-sure stability | design map | `Stochastic/*`, `Numerics/EulerMaruyama` | stochastic kind |

## 3. Design

### 3.1 System kinds

A family's system map returns one of a closed set of system kinds, each interpreted once in the
semantic layer by the same sentence language:

```lean
-- theorem/Port/Defs.lean
inductive Behaviour (n p : ℕ)
  | continuous (s : Port.System n p)   -- Flow semantics
  | discrete (s : Map.System n p)      -- Map semantics: step x u, output, period T
def Sentence.holds : Sentence → Behaviour n p → Prop
  | .flow P, .continuous s => P.holds s.zeroInput 0
  | .passive, .continuous s => s.Passive
  | .flow P, .discrete s => P.holdsMap s.period s.zeroInput 0
  | .passive, .discrete s => s.Passive
```

`Family.system : X → Behaviour n p`, with a coercion from `Port.System`; `Family.IsAutonomous`
reads continuous autonomous families and `Family.IsAutonomousMap` discrete ones. Everything built
on families — TMIO connections, `Family.den`, translation exactness, admission's inference of
model types from `Family` definitions, `Implementation` and `Stack` — works unchanged, and a
continuous model family can be realized by a discrete implementation family directly.

The migration changed `Port/Defs`, `Port/Basic`, `Family/Basic`, `Architecture` and the
architecture tests, added the semantic module `Map/Defs`, and needed an explicit
`.continuous` where the coercion does not fire (a few family definitions and proofs); `TMIO/*`
did not change. Later kinds (periodic, hybrid, stochastic) extend `Behaviour` and
`Sentence.holds` the same way.

### 3.2 Discrete time without a second time axis

Discrete-time notions are stated through iterates `F^[k] x` and one-step inequalities, never by
quantifying sequences `ℕ → ℝⁿ`: Lyapunov, asymptotic and geometric local stability, the global
notions, decay, k-step contraction, conservation (`V ∘ F = V`), and passivity as the one-step
dissipation inequality `V (F x u) − V x ≤ u ⬝ y`. The architecture's time-axis inference then
still reports the single axis `ℝ` (prototype: Flow + Port + Map definitions give `{ℝ}`; a
sequence-quantifying definition gives `{ℝ, ℕ}`, as intended).

What the extension carries:

* Recognition of discrete behaviour. Besides signals of time, the audit recognizes a sequence
  indexed by steps into a state space (a discrete signal) and discrete evolution (an iterate of a
  self-map of a state space, or the step of a discrete system): such notions are behavioural
  inside the semantic layer and rejected outside it, so no discrete notion is defined outside the
  semantic layer.
* `decay a` must mean the same rate in both kinds; the discrete system therefore carries its
  sampling period `T`, and `decay a` reads as `e^{−a T k}`. The other sentences are scale-free.
* The first theorem of the discrete layer is proved: a map differentiable at a fixed point with
  a Schur-stable Jacobian is locally geometrically stable (only differentiability at the point is
  needed). Instability from one eigenvalue outside the unit circle is proved when all eigenvalues
  are outside; the general case needs a spectral splitting with adapted norms (several hundred
  lines, not done).

Sampled-data and switched implementations need no second time axis either. A continuous plant
under zero-order hold with a discrete controller (and a computation delay, added as a controller
state) is exactly its lifted map at the sampling instants: uniform exponential decay of the
continuous-time trajectories, between samples included, holds if and only if the lifted matrix
has spectral radius below one (`LTI.sampledLoop_exponentialDecay_iff`). A switched converter is
read through its period map, with the ripple bounded within a period
(`Averaging.switched_decay_of_isHurwitz`). The single-axis rule constrains definitions only:
these bridge theorems quantify sampled sequences and continuous trajectories together and pass
the semantic and admission checks.

### 3.3 Sentences for physical limits

Saturation, quantization and limits destroy global and often asymptotic properties: no
voltage-limited PI loop is globally exponentially stable (`CurrentControl/VoltageLimit`), and a
quantized loop converges only to a neighbourhood. The sentence language needs parameterized
sentences in the style of `decay a`:

* `ultimatelyBounded r`: every solution eventually enters and stays in the ball of radius `r`
  (practical stability; quantization, limit cycles);
* `confined r₀ r₁`: solutions starting in the ball `r₀` stay in the ball `r₁` (safety: currents
  within ratings);
* `attracts r`: the region of attraction contains the ball `r` (saturation, current limiting).

Limits on individual coordinates (a current magnitude, a DC-link voltage) need a weighted or
coordinate form; the first version can use balls in scaled coordinates.

### 3.4 Approximation as a realization

Simulation and averaging relate an implementation to its model by trajectory closeness rather
than by shared sentences: `‖x_h(kh) − x(kh)‖ ≤ C h^p` on a horizon, `‖x_T(t) − x̄(t)‖ ≤ C T`. A
generic approximation relation (an error bound as a function of the implementation parameter on
a horizon) complements realization soundness; the library has the bounds for forward Euler,
state-space averaging and KBM averaging.

### 3.5 Bridges

Bridges relate a continuous model to its discrete or switched implementation and are generic
mathematics, independent of the semantic decision:

| Bridge | Status |
| --- | --- |
| Trapezoidal (Tustin) discretization Schur iff Hurwitz; backward Euler sound; forward Euler step condition | in `Numerics/LinearSchemes`, `Numerics/StabilityFunctions` |
| Averaged model versus switched system on a finite horizon, `O(T)` | in `Averaging/StateSpaceAveraging`, `Averaging/KBM` |
| Spectral radius of the monodromy below one gives exponential decay | in `Periodic/Floquet` (sufficient direction) |
| Hurwitz iff the sampled exponential `e^{TA}` is Schur; exact ZOH discretization; sampled-data closed loop: uniform exponential decay, between samples included, iff the lifted matrix is Schur; computation delay by augmentation | `LTI/Sampling` |
| Averaged model Hurwitz implies uniform exponential decay of the switched system, ripple included, for `T ≤ T₀`; conversely a `T`-uniform decay forces the average Hurwitz; averaging error `O(T)` on the whole half line | `Averaging/SwitchedStability` |
| Slow switching breaks the transfer: two Hurwitz topologies with a Hurwitz average switch into an unstable system (a period-doubling flip, multiplier `−4 e^{−1/2}` at `T = 5`) | `Averaging/SwitchedStability` |
| Discrete linearization (Schur Jacobian); instability when every eigenvalue lies outside the closed unit disk | `Map/Linearization` |
| Exact sampling as a realization: every sentence read through the design model, exact without constraint | `LTI/ExactSampling` (scaffold `theorem/ExactSampling.agda`) |
| Switched averaging as a realization: sound under fast switching, exact for commuting topologies, sound without constraint iff `n ≤ 1` | `Averaging/SwitchedFamily` (scaffold `theorem/SwitchedAveraging.agda`) |
| Explicit Euler as a realization: local exponential stability realized below a step threshold, never for every step; with ports, flow sentences read through the zero input and passivity never realized when the output does not depend on the input | `Numerics/EulerRealization`, `Numerics/EulerPorts` (scaffolds `theorem/EulerDiscretization.agda`, `theorem/EulerPorts.agda`) |
| Instability for every small `T` when the average has an eigenvalue with positive real part | to do |
| Quantized loops: ultimate bound from a Lyapunov decrease outside a ball | to do |
| Saturated loops: region of attraction from a Lyapunov sublevel set | to do |

Consequences for implementation requirements. Fast switching is an exact requirement only in its
`T`-uniform form; its threshold scales with the averaged dynamics (in the counterexample the flip
appears near a third of the averaged oscillation period), so it should be stated relative to the
averaged model, not as an absolute period. The `T₀` extracted from the proof is explicit but
conservative. With a constant input the switched statements are incremental: trajectories
approach the periodic steady state, and the Hurwitz hypothesis applies to the deviation
dynamics.

## 4. Plan

0. Without semantic change: continuous-time implementation families (done: VSM platform, PI
   loop with tolerance, Padé-delayed digital loop, voltage limit) and the generic bridges of §3.5
   (done: sampling, switching and explicit Euler, as realizations).
1. Discrete-time kind: `Behaviour`, `Map/Defs` with its recognition rule, the discrete
   linearization theorem (`Map/Linearization`) — done. First families: the exact digital PI loop (ZOH, computation delay,
   Euler or Tustin integrator; its lifted matrix is `LTI.delayedLoopMatrix`) realizing the PI
   design, replacing the Padé surrogate; the EMT
   trapezoidal and backward-Euler discretizations realizing the RL and LCL plants (their stability
   results are private evidence today); the forward-Euler controller discretization of the drive
   current loop.
2. Switching: the period map of a switched converter read by the discrete kind, with the
   averaging bridge; then a periodic kind if intersample behaviour is to be stated directly.
   Families: buck and boost converters in CCM realizing their averaged models; PWM-sampled loops.
3. Limit and quantization sentences (§3.3): quantized digital loops, anti-windup, current
   ratings, saturation regions of attraction.
4. Hybrid kind (second time axis, a change of the single-axis rule): DCM, diodes, hysteresis
   control, limiting mode changes, protection; dead time; then noise.

## 5. Decisions

* Extending the shared semantic layer with system kinds (§3.1–3.2), including the recognition
  rule for discrete behaviour: decided and done for the discrete kind.
* Adding parameterized limit sentences to the sentence language (§3.3).
* Later: hybrid time, which changes the single-time-axis rule.
