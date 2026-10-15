# Building the implementation layer

Status: design proposal. The semantic-layer changes below touch the shared codex layer and
await the maintainer's decision; the generic bridges and the continuous-time implementation
families are already in the library.

[Layers.md](Layers.md) defines the implementation layer: a model under realistic constraints
(digitization, switching, physical limits, tolerances, numerical integration), with its own
behaviour, related to the model it realizes. The interface (`theorem/Stack/Implementation.lean`)
is complete for implementations whose behaviour the semantic layer can read. This document
records what the semantic layer cannot yet read, what each kind of implementation needs, and a
staged plan.

## 1. The obstacle

The semantic layer (`theorem/Flow/Defs.lean`, `theorem/Port/Defs.lean`) reads complete
autonomous vector fields in continuous time; its header excludes delay, sampling, PWM and
switching. A family's system map returns a `Port.System`, so a discrete-time controller, a
numerical scheme or a switched converter cannot be an implementation family. The library model
families confirm the gap from the other side: their model boundaries list delay, PWM, sampling
and saturation among the exclusions.

Continuous surrogates are possible but are themselves models of the implementation with their
own error. For the IMC-tuned PI current loop with a one-sample computation delay, zero-order
hold and a forward-Euler integrator, the exact sampled-data stability boundary is
`ω_b Tₛ ≈ 1.00–1.05` for `R Tₛ/L ≤ 0.1` (numerical scan of the lifted 3×3 map over twelve values
of `R Tₛ/L`; non-monotone, `≈ 0.65` at `R Tₛ/L = 10`). The pure-delay surrogate gives `π/3 ≈ 1.047`
and the Padé(1,1) surrogate of `CurrentControl/DigitalPI.lean` gives `4/3`, a third too
optimistic.

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
inductive Behaviour (n p : ℕ)
  | continuous (s : Port.System n p)   -- existing
  | discrete (s : Map.System n p)      -- x⁺ = F(x, u), sampling period T
  -- later: periodic, hybrid, stochastic
def Sentence.holds : Sentence → Behaviour n p → Prop   -- by cases, fixed once
```

`Family.system : X → Behaviour n p`, with a coercion from `Port.System`. Everything built on
families — TMIO connections, `Family.den`, translation exactness, admission's inference of model
types from `Family` definitions, `Implementation` and `Stack` — works unchanged, and a
continuous model family can be realized by a discrete implementation family directly.

The prototype (scratch `poc-sem`, compiled, not in the repository) measured the fallout: of about
60 family definitions, the lambda-style ones pass through the coercion, families built through
`Spectral`, `extend` or `comap` are untouched, and two point-free definitions need a lambda
(`GFM/Matching/ClosedLoop.lean`, `Synchronous/SMIB11PH.lean`); roughly 15–30 rewrites of
`Sentence.holds` in proofs change mechanically. The codex files that change are `Port/Defs`,
`Port/Basic`, `Family/Basic`, `Linear/Family`, `Linear/Coordinates`, `Architecture` and the
architecture tests; a new semantic module `Map/Defs` is added. `TMIO/*` does not change.

### 3.2 Discrete time without a second time axis

Discrete-time notions are stated through iterates `F^[k] x` and one-step inequalities, never by
quantifying sequences `ℕ → ℝⁿ`: Lyapunov, asymptotic and geometric local stability, the global
notions, decay, k-step contraction, conservation (`V ∘ F = V`), and passivity as the one-step
dissipation inequality `V (F x u) − V x ≤ u ⬝ y`. The architecture's time-axis inference then
still reports the single axis `ℝ` (prototype: Flow + Port + Map definitions give `{ℝ}`; a
sequence-quantifying definition gives `{ℝ, ℕ}`, as intended).

Findings of the prototype that the extension must carry:

* The behaviour recognizer of the architecture does not recognize iterate-based notions (zero
  behavioural notions found in the map definitions). Without a rule for them, discrete behaviour
  would be invisible to admission, a bypass. The semantic layer needs an explicit recognition
  rule for predicates of state maps, added together with the definitions.
* `decay a` must mean the same rate in both kinds; the discrete system therefore carries its
  sampling period `T`, and `decay a` reads as `e^{−a T k}`. The other sentences are scale-free.
* The first theorem of the discrete layer is proved: a map differentiable at a fixed point with
  a Schur-stable Jacobian is locally geometrically stable (only differentiability at the point is
  needed). Instability from one eigenvalue outside the unit circle is proved when all eigenvalues
  are outside; the general case needs a spectral splitting with adapted norms (several hundred
  lines, not done).

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
| Hurwitz iff the sampled exponential `e^{TA}` is Schur; exact ZOH discretization; sampled-data closed loop with intersample bound | in progress (`LTI/Sampling`) |
| Averaged model Hurwitz implies the switched system is exponentially stable for fast switching | in progress (`Averaging/SwitchedStability`) |
| Discrete linearization (Schur Jacobian) | prototype, proved |
| Quantized loops: ultimate bound from a Lyapunov decrease outside a ball | to do |
| Saturated loops: region of attraction from a Lyapunov sublevel set | to do |

## 4. Plan

0. Without semantic change (in progress): continuous-time implementation families (done: VSM
   platform, PI loop with tolerance, Padé-delayed digital loop, voltage limit) and the generic
   bridges of §3.5.
1. Discrete-time kind: `Behaviour`, `Map/Defs` with its recognition rule, the discrete
   linearization theorem. First families: the exact digital PI loop (ZOH, computation delay,
   Euler or Tustin integrator) realizing the PI design, replacing the Padé surrogate; the EMT
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
  rule for discrete behaviour.
* Adding parameterized limit sentences to the sentence language (§3.3).
* Later: hybrid time, which changes the single-time-axis rule.
