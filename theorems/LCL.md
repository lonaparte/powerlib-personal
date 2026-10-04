# Small-signal stability of a canonical LCL filter

## Scope and coordinates

This derivation concerns a continuous-time, single-phase LCL filter with two
series inductors, their series resistances, and an ideal shunt capacitor. The
two terminal voltages are external inputs. There is no controller, PLL, PWM,
sampling delay, capacitor ESR, or additional grid state. The result does not
establish stability of a controlled grid-connected converter.

Assume `L1 > 0`, `L2 > 0`, and `C > 0`. Allow signed `R1` and `R2` in the general
criterion; the passive specialization assumes both are nonnegative. Current
`i1` flows from the converter terminal to the capacitor node, and `i2` flows
from that node to the grid terminal. Capacitor voltage is `vc`.

Kirchhoff's laws give

```text
L1 * di1/dt = u - R1*i1 - vc
C  * dvc/dt = i1 - i2
L2 * di2/dt = vc - R2*i2 - vg
```

The circuit is already linear. Subtracting any nominal solution with the same
parameters gives these same equations for the perturbations. A constant
equilibrium is a special case. In the state order `x = (delta_i1, delta_vc,
delta_i2)`, the perturbation model is

```text
dx/dt = A*x + Bu*delta_u + Bg*delta_vg

A = [ -R1/L1   -1/L1       0    ]
    [   1/C       0       -1/C   ]
    [    0       1/L2    -R2/L2  ]

Bu = (1/L1, 0, 0)^T
Bg = (0, 0, -1/L2)^T
```

Internal small-signal stability means that all eigenvalues of `A` have strictly
negative real part. Set both input perturbations to zero when testing it.
This is exponential stability of the homogeneous three-state system.

## Characteristic polynomial and exact criterion

Expanding `det(s*I - A)` gives `D(s)/(L1*L2*C)`, where

```text
D(s) = a3*s^3 + a2*s^2 + a1*s + a0

a3 = L1*L2*C
a2 = C*(R1*L2 + R2*L1)
a1 = L1 + L2 + C*R1*R2
a0 = R1 + R2
```

For example, expand along the first row:

```text
det(s*I-A)
  = (s+R1/L1)*(s*(s+R2/L2)+1/(C*L2))
    + (s+R2/L2)/(L1*C).
```

Since `a3 > 0`, the cubic Routh-Hurwitz criterion is necessary and sufficient:

```text
a2 > 0,  a1 > 0,  a0 > 0,  a2*a1 - a3*a0 > 0.
```

The Routh table first column is `a3`, `a2`,
`(a2*a1-a3*a0)/a2`, `a0`. Strict positivity of this column yields the criterion.
The condition on `a1` follows from the other three but is retained for clarity.
Equality is a boundary case and must not be accepted as strict stability.

An especially useful identity is

```text
a2*a1 - a3*a0
  = C*(R1*L2^2 + R2*L1^2
       + C*R1*R2*(R1*L2 + R2*L1)).
```

For passive resistances `R1 >= 0` and `R2 >= 0`, the exact result simplifies to

```text
A is Hurwitz  <=>  R1 + R2 > 0.
```

Indeed, a positive sum gives `a0 > 0`, `a2 > 0`, and `a1 > 0`. At least one of
`R1*L2^2` and `R2*L1^2` is strictly positive, while the remaining term in the
gap is nonnegative. Conversely, strict stability requires `a0 > 0`. Therefore
one lossy inductor is enough in this specific three-state model.

## Lossless boundary and physical energy

When `R1 = R2 = 0`,

```text
D(s) = s*(L1*L2*C*s^2 + L1 + L2)
eigenvalues = 0, +j*omega0, -j*omega0
omega0^2 = (L1 + L2)/(L1*L2*C).
```

The zero mode and undamped oscillatory modes rule out asymptotic stability.
Positive energy is conserved, so this lossless system is nevertheless stable
in the Lyapunov sense. Do not conflate that property with strict Hurwitz stability.

For arbitrary input perturbations, the physical energy and its derivative are

```text
E(x) = (L1*x1^2 + C*x2^2 + L2*x3^2)/2
dE/dt = -R1*x1^2 - R2*x3^2 + delta_u*x1 - delta_vg*x3.
```

Even with positive resistances, this derivative is zero at states with both
currents zero. Thus the diagonal physical-energy matrix does not satisfy a
strict `A^T*P + P*A < 0` inequality. An automated strict certificate generally
needs cross terms; semidefinite energy dissipation alone is not that certificate.

## Synthesis certificate interface

For exact rational parameters satisfying the criterion, solve the six linear
equations for a symmetric matrix `P` in

```text
A^T*P + P*A = -I.
```

The unique solution has rational entries. Check positive definiteness through
Sylvester's criterion: `P11 > 0`, `P11*P22-P12^2 > 0`, and `det(P) > 0`.
The witness then gives

```text
V(x) = x^T*P*x > 0 for x != 0
dV/dt = -x^T*x < 0 for x != 0.
```

More explicitly, for a real solution of `dx/dt=A*x`, positive definiteness gives
positive constants `m` and `M` with `m*||x||^2 <= V(x) <= M*||x||^2`. Hence
`dV/dt <= -V/M`, so `V(t) <= V(0)*exp(-t/M)` for `t >= 0`. This proves global
exponential stability for this linear perturbation model.

Synthesis and checking have different responsibilities:

1. Reconstruct `A` from the submitted circuit, with the fixed state order above.
2. Let an untrusted synthesizer propose the six exact entries of `P`.
3. Independently check the submitted parameters, the three positive minors,
   and all nine entries of the Lyapunov identity.
4. Generate a kernel proof of these arithmetic obligations tied to that model.
5. Apply a separately proved real-valued Lyapunov theorem to obtain the final
   stability theorem. Do not label arithmetic verification as completion of
   this final step.

The intended extension to controller synthesis is to search a controller `K`
and a witness `P`, then check the exact closed-loop matrix. That extension must
state its controller, feedback signs, inputs, and delay model explicitly.

## References and proof status

The circuit equations and all coefficient and gap expansions above are derived
here. The cubic criterion follows the
[MIT ES.1803 stability notes](https://ocw.mit.edu/courses/es-1803-differential-equations-spring-2024/mites_1803_s24_day16-notes.pdf).
For another university example of deriving LCL state equations from Kirchhoff's
laws, see [Harvey Mudd's circuit notes](https://pages.hmc.edu/ruye/e84/lectures/ch3/node15.html);
that example uses a resistive load, so its boundary conditions differ from ours.

This is a mathematical derivation. The existing Lean/Agda RL proofs do not prove
the LCL stability theorem. Exact rational certificate checks are a foundation
for formalization, not a claim that the real-valued LCL Lyapunov theorem has
already been checked by Lean.
