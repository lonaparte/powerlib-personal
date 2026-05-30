# Rigorous Bautin enclosure for the GFL weak-grid Hopf (Ki_pll = 150)

> 2026.05 | Interval-sound proof that the first Lyapunov coefficient l₁ changes
> **sign** along the weak-grid Hopf locus between two certified Hopf points, hence a
> Bautin (generalized-Hopf, l₁=0) point is rigorously bracketed in Kp_pll.

## What this proves

Model: the repo's 10-state GFL converter (Conventions.md §12), identical equations,
equilibrium, Jacobian and exact symbolic 2nd/3rd-derivative tensors as
`sweep.py` / `ivparam.py` / `ivgrid.py`. Operating point: **Ki_pll = 150 fixed,
grid angle X/R = 10 fixed**; the Hopf bifurcation parameter is SCR (grid strength);
the Bautin sweep parameter is the PLL proportional gain **Kp_pll**.

`bautin.py` (FLOAT) found that l₁ at the weak-grid Hopf changes sign near
**Kp\* ≈ 0.4036** (l₁>0 / subcritical / hard for Kp<Kp\*, l₁<0 / supercritical /
soft for Kp>Kp\*). This directory turns that float evidence into a **rigorous
interval bracket**.

### Main result (interval-sound)

At each endpoint Kp we (a) certify a Hopf — the interval critical-eigenvalue
real-part enclosure provably contains 0 — and (b) interval-evaluate l₁ over the
straddling box. The two l₁ enclosures have **definite opposite signs**:

| Kp endpoint | Hopf SCR_H (float) | Re λ enclosure (straddles 0 ⇒ Hopf in box) | l₁ enclosure | sign |
|---|---|---|---|---|
| **0.40000** | 0.807242 | [−7.939e−4, +7.939e−4] ✓ | **[+2.4406e−6, +2.3925e−5]** | **l₁ > 0** |
| **0.40800** | 0.803617 | [−8.132e−4, +8.132e−4] ✓ | **[−6.9205e−5, −2.8955e−6]** | **l₁ < 0** |

Opposite definite signs ⇒ by the intermediate value theorem (l₁ continuous along
the Hopf locus) there is a **Kp\* ∈ [0.40000, 0.40800] with l₁(Kp\*) = 0**: a
rigorously bracketed Bautin / generalized-Hopf point.

- **Rigorous bracket: Kp\* ∈ [0.40000, 0.40800], width 0.00800.**
- Consistent with (and contains) the float Kp\* ≈ 0.4036 from `bautin.py`.

A wider, more comfortable bracket is also certified:

| bracket | l₁(Kp_lo) | l₁(Kp_hi) | width | status |
|---|---|---|---|---|
| [0.39000, 0.42000] | [+3.6560e−5, +5.7465e−5] | [−1.7465e−4, −1.0968e−4] | 0.03000 | ✓ opposite signs |
| [0.39500, 0.41000] | [+1.9990e−5, +4.1211e−5] | [−8.5991e−5, −1.9801e−5] | 0.01500 | ✓ opposite signs |
| **[0.40000, 0.40800]** | **[+2.4406e−6, +2.3925e−5]** | **[−6.9205e−5, −2.8955e−6]** | **0.00800** | **✓ tightest certified** |
| [0.40200, 0.40600] | [−4.88e−6, +1.67e−5] | [−2.01e−5, +1.65e−6] | 0.00400 | ✗ both straddle 0 (inconclusive) |

## Method (interval-sound throughout)

Route (i) of the task — the "box straddles the Hopf surface" technique already used
in `ivparam.py` / `ivgrid.py` / `ivlocus.py`:

1. **Locate** the float Hopf SCR_H(Kp) at the endpoint (bisection on max Re eig).
2. **Straddle box**: take SCR ∈ [SCR_H − pad, SCR_H + pad] (pad = 1e−6). Build the
   interval Jacobian over this box (closed-form equilibrium; all entries in mpmath
   interval arithmetic with directed rounding).
3. **Certify the Hopf**: verify the critical right eigenpair (i·ω, q) and the left
   eigenpair p exist-and-are-unique over the whole box via **Krawczyk / Rump** on
   the bordered eigen-system. The verified Re λ enclosure **contains 0**, so the box
   provably contains a true Re λ=0 Hopf. (If Krawczyk fails to contract, the code
   RAISES — never returns an unverified result.)
4. **Interval l₁** (Kuznetsov projection formula) evaluated entirely in interval
   arithmetic; the two linear solves are enclosed by a verified Neumann bound
   (‖I − R·M‖∞ < 1 checked; raises otherwise). Because the box contains a Hopf, the
   interval l₁ **encloses l₁ at that Hopf**.
5. **Opposite-sign test** reads l₁.b<0 vs l₁.a>0 from the ENCLOSURES, never from
   float midpoints.

Why l₁ must be evaluated **at** a Hopf: l₁ is only defined when Re λ=0 (the
projection formula is derived at, and divides by, a purely imaginary critical pair).
The straddle guarantees a genuine Hopf inside the box, so the certificate is about
l₁ at an actual Hopf, not at an arbitrary off-Hopf point.

## Sign is invariant, magnitude is a convention

Per Conventions.md §12.6 and `numerical/README.md`: the **magnitude** of l₁ is
normalization/coordinate dependent (balanced vs unbalanced coords differ ~100×); the
**sign** of l₁ is the coordinate-invariant physical quantity (sub/supercritical).
We work in **balanced coordinates** (matrix_balance), purely to lower the condition
number; the Bautin conclusion rests only on the sign. The numbers above are in
balanced coords (so ~1e−5..1e−4, like `ivparam.py`'s box), NOT the unbalanced
~1e−6 of `bautin.py`/`ivcert.py` — do not compare magnitudes across coordinate
conventions.

## Honest limitations / conditioning

- **Tightest rigorous bracket is width 0.008** ([0.40, 0.408]). Narrowing further to
  [0.402, 0.406] FAILS: both l₁ enclosures straddle 0. This is the genuine
  conditioning limit — as Kp→Kp\*, the true |l₁|→0, while the interval l₁ has a
  finite width (~2e−5 here, set by the SCR-box pad propagating through the
  bordered-eigenpair Krawczyk step and the Neumann solve). Once |l₁| < (interval
  width)/2 the sign is no longer resolvable. This is the same Krawczyk/condition-
  number wall noted for the existing `iv*` scripts, and is honest: we report the
  tightest bracket the arithmetic supports, not a tighter unsupported one. The width
  could be reduced by Route (ii) (a bordered Re λ=0 Hopf system enclosing SCR_H
  jointly, removing the SCR-pad over-approximation) and/or affine arithmetic; that is
  future work, not done here.
- **The Bautin point Kp\* itself is bracketed, not pinned**: this certifies a sign
  change (l₁=0 somewhere in [0.40,0.408]), i.e. existence of a Bautin point in the
  interval. It does not interval-enclose Kp\* to high precision (that needs Route
  (ii) + interval root-finding on l₁(Kp)=0).
- **Second Lyapunov coefficient l₂ (nondegeneracy): NOT computed.** A genuine
  (codim-2 nondegenerate) Bautin requires l₂(Kp\*) ≠ 0. Computing l₂ rigorously needs
  the 5th-order normal-form coefficient (Kuznetsov's l₂ formula: 4th/5th
  multilinear forms B…E, three additional resolvent solves on the full 10-state
  system). The exact symbolic 4th/5th derivative tensors and the extra verified
  solves are not implemented here. Float evidence: l₁ crosses 0 transversally in Kp
  (the float l₁(Kp) has clearly nonzero slope through Kp\* — see `bautin.py`'s clean
  sign change and the monotone endpoint values above), which is *consistent with*
  (but does not prove) nondegeneracy. **We do not claim l₂≠0.** Honest status:
  open / not done rigorously.
- This is **interval-arithmetic** rigor (verified mpmath enclosures over the whole
  parameter box), **not** a KeYmaera X `.kyx` / Lean proof. Same rigor level and
  caveat as the existing `ivcert/ivparam/ivgrid/ivlocus`.

## Files

- `bautin_cert.py` — the certificate. Standalone (mirrors `ivparam.py`'s structure;
  same model/tensors). Run: `cd formalization/numerical && python3 bautin_cert/bautin_cert.py`.
  Prints the bracket + both endpoint enclosures; writes `results.json`.
- `crossval.py` — cross-validation: (1) the independent float l₁ pipeline in
  `sweep.py` (numpy einsum tensors, separate code path) lands inside the rigorous
  enclosures; (2) the float Bautin Kp\* from `bautin.py` lies inside the bracket.
  Run after `bautin_cert.py`.
- `results.json` — machine-readable enclosures for all brackets tried.
- `RESULTS.md` — this file.

## Reproduce

```
cd formalization/numerical
python3 bautin.py                 # float evidence: Kp*(Ki=150) ≈ 0.4036
python3 bautin_cert/bautin_cert.py   # rigorous bracket [0.40,0.408], opposite-sign l1 enclosures
python3 bautin_cert/crossval.py      # cross-checks against the independent sweep.py pipeline
```
