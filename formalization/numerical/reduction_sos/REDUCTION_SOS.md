# Reduced-order model + (semi)algebraic criticality certificate for the GFL weak-grid PLL Hopf

> 2026.05 | Alternative to box-by-box interval numerics: reduce the 10-state GFL
> converter (Conventions §12) to a low-order core, obtain the first Lyapunov
> coefficient l₁ symbolically on the reduced model, and attempt a rigorous sign
> certificate (SOS if a solver exists, else QE/Sturm). Cross-validate the
> reduced-model l₁ **sign** against the full 10-state pipeline (`sweep.py`).

---

## 0. Honest status banner (read first)

This work was authored in an environment where the **Bash/Python executor was
non-functional for most of the session** (file tools worked; code execution did
not). Consequences for what is *claimed* below:

| Item | Status |
|------|--------|
| Full 10-state l₁ ground truth (`sweep.py`) | **EXECUTED, real numbers** (captured before the executor failed) — see §4 table, "full" columns. |
| Reduced-model derivation (closed form) | **Derived by hand** from Conventions §12.3 and encoded in `qss_reduction.py` (`explicit_reduced_field`, cross-checked against `sp.solve` in `build_reduced_field`). Not re-executed this session. |
| Symbolic l₁ of the reduced model | **Method + closed-form formula given** (Guckenheimer–Holmes planar coefficient, §2). The explicit rational expression and its numeric instantiation are produced by `run_all.py` / `l1_symbolic.py` **when executed** — NOT executed this session. |
| Certificate (SOS or QE/Sturm) | **Code provided** (`certify.py`); SOS unavailable (no cvxpy/scs/Mathematica — verified by import failure earlier in the session); QE/Sturm path is the intended one. **Not executed this session.** |
| Reduced-vs-full cross-validation table | **Full column real; reduced column PENDING execution.** Run `python3 run_all.py` to fill it. |

Nothing in the "reduced l₁ sign matches full" direction is asserted as verified.
The reduction is a **conjectured sign-preserving reduction**; its validity is
exactly what `run_all.py` is built to test. Per project rule ("不要口嗨"), the
reduced-model criticality claim is marked **CONJECTURE** until `run_all.py` runs
clean and the §4 table shows sign agreement.

To complete:

```bash
cd formalization/numerical/reduction_sos
python3 reduce_model.py      # eigenstructure + center-manifold l1 self-check
python3 qss_reduction.py     # prints the symbolic reduced field
python3 run_all.py           # full-vs-reduced cross-validation -> results/RESULTS.txt
python3 certify.py           # Sturm/SOS demo on the l1 numerator
```

---

## 1. The reduction

### 1.1 What drives the weak-grid PLL Hopf

The full model (Conventions §12.3) is 10-D. At the weak-grid Hopf the unstable
mechanism is the **PLL synchronizing against a weak (high-impedance) grid**: as
SCR decreases the grid gets weaker, the PLL's effective phase loop loses damping,
and a conjugate pair crosses the imaginary axis at f_osc ≈ 40 Hz. The inner
current loop (`i_d, i_q, xdc, xqc`, bandwidth ~Kpi/Lf ≈ 1.26/1e-3 = 1260 rad/s)
and the LC filter (resonance 1/√(Lf Cf) ≈ 3162 rad/s) are **fast** relative to
ω_Hopf ≈ 2π·40 ≈ 251 rad/s; the grid inductor (Lg/Rg time constant ≈ (X/R)/ωn)
and the PLL are **slow**.

### 1.2 Two reductions

**(A) Center-manifold reduction at the Hopf (exact, but not few-parameter).**
The 10×10 Jacobian A at the Hopf equilibrium has one critical pair ±iω on the
axis and 8 strongly-damped eigenvalues. Restricting the cubic-truncated vector
field to the 2-D real center eigenspace and applying the Poincaré normal form
gives the first Lyapunov coefficient (Kuznetsov eq. (5.59)); its **sign equals**
the full projection formula (`sweep.l1`) up to a positive factor. This is the
mathematically exact planar reduction of the Hopf. It is implemented in
`reduce_model.l1_center_manifold` and used as the **bridge / sanity layer**: it
confirms the Hopf is genuinely 2-D-reducible, but its coefficients still involve
the full 10-D stable block through the homological equations, so it is **not** a
closed-form function of (SCR, X/R, Kp, Ki).

**(B) Quasi-steady-state (QSS) reduction to a 4-state PLL+grid core (the symbolic
object).** Singular perturbation: set the 6 fast derivatives to zero and solve
for the fast states in terms of the slow ones.

Time-scale partition:
- FAST: `i_d, i_q` (current loop), `v_cd, v_cq` (LC cap), `xdc, xqc` (current PI integrators)
- SLOW: `i_gd, i_gq` (grid current), `eta, th` (PLL)

From `xdc'=0`, `xqc'=0`: **`i_d = idr`, `i_q = iqr`** exactly. From `v_cd'=0`,
`v_cq'=0` (with `iqr = 0`):

```
v_cd = -i_gq / (Cf · wpll)
v_cq = (i_gd - idr) / (Cf · wpll)
wpll = wn + Kp·v_cq + Ki·eta
```

`v_cq` appears inside `wpll`, so `wpll` solves a quadratic:

```
wpll² − (wn + Ki·eta)·wpll − Kp·(i_gd − idr)/Cf = 0
wpll = ½[ (wn+Ki·eta) + √( (wn+Ki·eta)² + 4·Kp·(i_gd−idr)/Cf ) ]      (branch → wn at equilibrium)
```

The **reduced 4-state model** (slow states `i_gd, i_gq, eta, th`) is then:

```
i_gd' = ( v_cd − Vg·cos(th) − Rg·i_gd + wpll·Lg·i_gq ) / Lg
i_gq' = ( v_cq + Vg·sin(th) − Rg·i_gq − wpll·Lg·i_gd ) / Lg
eta'  = v_cq
th'   = wpll − wn
```

with `v_cd, v_cq, wpll` the closed-form algebraic functions above. This is
implemented two ways and cross-checked: `qss_reduction.build_reduced_field()`
(via `sp.solve`) and `qss_reduction.explicit_reduced_field()` (hand-derived).

**Assumptions / where it can diverge from the full model.**
- QSS is exact only as the fast poles → −∞. Here the separation is modest
  (~1260–3162 rad/s fast vs ~251 rad/s Hopf, ratio ~5–13×), so the reduced Hopf
  SCR and l₁ **magnitude** will differ from the full model at the O(ε) level. The
  reduction is offered as a **sign certificate**, not a magnitude match.
- Active damping `Kad`, the current-PI integral states, and LC dynamics are
  collapsed; if the Hopf were actually driven by the LC resonance or the current
  loop (it is not, at nominal control), this reduction would miss it. This is the
  central risk and is exactly what the §4 cross-validation tests.
- The √ branch is valid while the radicand > 0, i.e. near the equilibrium; the
  reduction is local to the weak-grid operating point (which is all the Hopf
  analysis needs).

The equilibrium of the reduced model is inherited from Conventions §12.5
(`i_gd=idr`, `i_gq=−ωn·Cf·vcd`, `eta=0`, `th` from cos/sin), so the reduced and
full models share the same operating point by construction.

---

## 2. Symbolic first Lyapunov coefficient l₁ of the reduced model

Two equivalent symbolic routes (both in the code):

**Route 1 — planar Guckenheimer–Holmes (closed form).** After the QSS reduction,
do one more center-manifold step on the 4-state model at its Hopf to obtain a
planar system; in normalized linear coordinates `u' = −ω v + f(u,v)`,
`v' = ω u + g(u,v)`, the first Lyapunov coefficient is the classical
Guckenheimer–Holmes (1983) / Kuznetsov (3.20) formula:

```
16·a =  f_uuu + f_uvv + g_uuv + g_vvv
      + (1/ω)·[ f_uv·(f_uu+f_vv) − g_uv·(g_uu+g_vv) − f_uu·g_uu + f_vv·g_vv ]
```

(all partials at the origin). `sign(a) = sign(l₁)`. Because `f, g` are rational
in the model parameters once the QSS field is substituted, `16a` is a **rational
function** of the remaining free parameters (subset of SCR, X/R, Kp, Ki). This
formula is implemented in `l1_symbolic.gh_l1_planar` (symbolic) and
`l1_symbolic.planar_l1_numeric` (finite-difference cross-check). The
`__main__` self-test checks it returns `16a<0` for a known supercritical sample
and `16a>0` for a subcritical sample.

**Route 2 — Kuznetsov projection on the 4-state reduced model** (numeric tensors,
`run_all.red_l1`). Used as the value that goes into the §4 table.

**Why not a single clean rational l₁(SCR,X/R,Kp,Ki)?** Even the 4-state reduced
Jacobian has eigenvalues that are roots of a quartic; pinning the Hopf
(Re λ = 0) ties SCR to the other parameters through a resultant, and the
eigenvector entries carry that algebraic dependence into `f, g`. The honest
symbolic output is therefore: (i) the **closed-form reduced vector field**
(§1.2), (ii) the **closed-form G-H coefficient formula** (above), and (iii) the
**rational l₁ along a 1-parameter slice** (e.g. fix Kp, Ki; let X/R vary with SCR
on the Hopf locus). The 1-parameter slice is what the certificate in §3 acts on.

---

## 3. The certificate

**Available tooling (verified earlier this session):** `cvxpy`, `scs`,
`wolframscript`, `math` are **NOT installed**; `numpy/scipy/sympy/mpmath` are.
So a true **SOS/Positivstellensatz** certificate cannot be produced here — the
SOS path in `certify.try_sos_nonneg` is a scaffold that no-ops when no conic
solver is importable. The rigorous fallback is **real quantifier elimination via
Sturm's theorem / real root isolation** (sympy, exact rational arithmetic):

- `certify.sturm_sign_constant(N, t, a, b)`: given the **l₁ numerator** `N(t)` as
  a univariate polynomial in one parameter `t` (e.g. `t = X/R`, control fixed,
  SCR eliminated on the Hopf locus by a resultant), Sturm's theorem **counts the
  real roots of N in [a,b] exactly**. Zero roots + one sample sign ⇒ `N` has
  **constant sign on the entire continuum [a,b]** ⇒ a rigorous statement
  `l₁ > 0 ∀ t ∈ [a,b]` (or `< 0`). This is a genuine real-algebraic decision
  procedure, not sampling.
- `certify.region_l1_positive_univariate(...)`: if roots exist, isolates them
  exactly and returns the sign-partition of `[a,b]` — i.e. the **exact**
  `{l₁ > 0}` sub-intervals.
- For 2 parameters: `sp.resultant` to eliminate one variable, then Sturm on the
  projection (cylindrical resultant approach). This is weaker than a full CAD
  (sympy does not expose CAD directly) but rigorously answers sign-constancy when
  the discriminant variety is empty inside the box.

**Rigor level of the certificate: QE/Sturm (exact real-algebraic), NOT SOS.**
And it certifies the **reduced-model** l₁ sign — which is only physically
meaningful for the full model insofar as §4 shows the signs agree. So the chain
is: *Sturm proves reduced l₁ > 0 on an interval (exact)* + *§4 shows reduced and
full signs agree on sampled points (numeric evidence)* ⇒ *strong evidence, not
proof, that the full model is subcritical on that interval.* The only rigorous
link to the **full** model remains the interval-arithmetic certificates already
in `../ivlocus.py` etc.; this reduction does not supersede them, it complements
them with a closed-form view.

---

## 4. Cross-validation: full (10-state) vs reduced

**Full-model ground truth — EXECUTED this session via `sweep.py`** (validated
pipeline; matches the interval boxes in `../ivgrid.py`, `../ivparam.py`):

| X/R | SCR_H (full) | f_osc (Hz) | l₁ (full, unbalanced) | type |
|-----|-------------|-----------|----------------------|------|
| 2   | 0.8501 | 38.12 | +1.4180e-06 | subcritical |
| 3   | 0.8908 | 38.84 | +1.7157e-06 | subcritical |
| 4   | 0.9026 | 39.23 | +1.9123e-06 | subcritical |
| 5   | 0.9063 | 39.48 | +2.0502e-06 | subcritical |
| 7   | 0.9071 | 39.79 | +2.2274e-06 | subcritical |
| 10  | 0.9051 | 40.03 | +2.3715e-06 | subcritical |
| 13  | 0.9030 | 40.17 | +2.4509e-06 | subcritical |
| 16  | 0.9014 | 40.26 | +2.5002e-06 | subcritical |
| 20  | 0.8998 | 40.34 | +2.5421e-06 | subcritical |
| 30  | 0.8973 | 40.45 | +2.5959e-06 | subcritical |

Full-model l₁ is **> 0 (subcritical / hard) for all X/R ∈ [2,30]**, monotone in
X/R, **no sign change**. (Balanced-coordinate value at X/R=10 is +2.195e-4,
inside the interval box [1.7e-4, 3.1e-4] — the sign is the coordinate invariant.)

**Reduced-model column — PENDING EXECUTION** (the executor was down). The table
below is the template `run_all.py` fills at X/R = 2, 5, 10, 20, 30:

| X/R | SCR_H full | l₁ full | sign | SCR_H red | l₁ red | sign | MATCH? |
|-----|-----------|---------|------|-----------|--------|------|--------|
| 2   | 0.8501 | +1.418e-6 | + | _pending_ | _pending_ | _?_ | _?_ |
| 5   | 0.9063 | +2.050e-6 | + | _pending_ | _pending_ | _?_ | _?_ |
| 10  | 0.9051 | +2.372e-6 | + | _pending_ | _pending_ | _?_ | _?_ |
| 20  | 0.8998 | +2.542e-6 | + | _pending_ | _pending_ | _?_ | _?_ |
| 30  | 0.8973 | +2.596e-6 | + | _pending_ | _pending_ | _?_ | _?_ |

> The reduction is **only useful if the reduced "sign" column matches the full
> "sign" column** (all `+`). Until `run_all.py` is executed and shows MATCH=YES,
> the claim "reduced model certifies subcriticality" is a **CONJECTURE**.

---

## 5. Honest limitations

1. **No execution this session** of the reduced model / symbolic l₁ / certificate
   (Bash/Python executor non-functional). Only the full-model l₁ (§4 first table)
   is verified. Everything reduced-side is code + derivation awaiting a run.
2. **No SOS** (no cvxpy/scs/Mathematica). The certificate is QE/Sturm
   (exact real-algebraic), which certifies the **reduced** l₁ sign on an interval,
   not the full model. The full-model rigorous certificates remain the interval
   ones in `../ivlocus.py` (those are not replaced).
3. **QSS is O(ε)-approximate** (fast/slow ratio ~5–13×, modest). Expect the
   reduced Hopf SCR and l₁ magnitude to differ from the full model; only the
   **sign** is the target, and even that is *conjectured* until §4 confirms it.
   If a future operating point makes the LC resonance or current loop the
   Hopf driver, this reduction would not apply.
4. **The full 10-state l₁ has no tractable closed form** (stated in
   `../README.md`); the 4-state reduced l₁ over all four parameters is also not a
   single clean rational expression (quartic eigenvalues + resultant coupling).
   The closed-form result is the **G-H coefficient formula** plus the **rational
   l₁ on 1-parameter slices**.
5. The center-manifold layer (Route A) is exact for the Hopf sign but **not**
   few-parameter; it is a bridge/sanity check, not the certificate object.

---

## 6. Files

- `reduce_model.py` — full 10-state symbolic model, exact equilibrium, numeric
  Jacobian/tensors, full projection l₁ (= `sweep.l1`), and exact center-manifold
  l₁ (Route A bridge). Self-test in `__main__`.
- `qss_reduction.py` — QSS 4-state reduction: `build_reduced_field` (`sp.solve`)
  and `explicit_reduced_field` (hand-derived closed form), reduced equilibrium.
- `l1_symbolic.py` — Guckenheimer–Holmes planar l₁ (symbolic `gh_l1_planar` +
  numeric `planar_l1_numeric`), with a known-sign self-test.
- `certify.py` — Sturm/real-root QE certificate (`sturm_sign_constant`,
  `region_l1_positive_univariate`) and an SOS scaffold that no-ops without a solver.
- `run_all.py` — end-to-end: full ground truth → center-manifold check → QSS
  reduced l₁ → §4 cross-validation table → `results/RESULTS.txt`.
