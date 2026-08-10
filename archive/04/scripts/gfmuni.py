"""One universal curve instead of a two-term expansion.

gfmfold2 measured delta = (eps_c - eps_qs)/eps_qs against
nu = w_p/sqrt(2 a b eps_qs) and found delta/nu - 1 = C2 nu with C2 close to
the derived universal 3/8 -- but only up to nu ~ 0.1.  At nu = 0.3 the
series is not converged (cell A: (delta/nu-1)/nu falls from 0.361 to 0.259),
and w_p = 0.3 w0 is exactly the case that has been carrying the 1.5%.

Truncating is unnecessary.  The whole tangential structure -- every order of
cos, and the implicit dependence of the curvature c = eps w^2/2 on the
UNKNOWN eps_c -- is contained in the fold normal form driven by the actual
cosine,

    xidot = a (eps cos(w t) - eps_qs) + b xi^2 ,

and that two-parameter problem collapses to ONE parameter.  With
s = w t (deepest dip at s = 0) and xi = (w/b) v,

    dv/ds = beta (u cos s - 1) + v^2 ,   beta = a b eps_qs / w_p^2 ,
                                         u    = eps / eps_qs

so the escape threshold is a universal function of a single argument:

    eps_c / eps_qs = F(beta) ,   beta = 1/(2 nu^2)                       (U)

computed once, for all cells and all frequencies, by shooting.  Its large-
beta expansion must reproduce the derived series 1 + nu + (3/8) nu^2, which
is a check on both.

Three things get separated here that were previously entangled:
  (a) F(beta) itself -- how much of the finite-frequency excess is the
      universal tangential passage;
  (b) the initial condition -- the measurement starts the state at the
      UNFORCED equilibrium while (U) starts it on the quasi-static branch of
      the raised-voltage half cycle.  Both are run; if they differ the
      protocol matters and that must be said, not averaged over;
  (c) what is left after (a) -- necessarily fold-specific (cubic and
      quartic terms of the reduced map, parameter curvature, and the lag of
      the non-critical states), i.e. the O(nu) corrections to lambda* that
      the solvability formula turns into Gaussian moments.
"""
import math, time, re
import numpy as np
from scipy.integrate import solve_ivp

LOG = open('sweep20/gfmuni.log', 'w')


def out(m):
    LOG.write(m + '\n'); LOG.flush()


T0 = time.time()


def esc_uni(beta, u, ic='branch'):
    """does v blow up over one drive period, starting at s = -pi?"""
    if u*1.0 <= 1.0 and beta > 0:
        pass
    s0 = -math.pi
    if ic == 'branch':
        v0 = -math.sqrt(max(beta*(1.0 - u*math.cos(s0)), 0.0))
    else:                      # unforced equilibrium: dip = 0
        v0 = -math.sqrt(beta)

    def f(s, y):
        return [beta*(u*math.cos(s) - 1.0) + y[0]*y[0]]

    def ev(s, y):
        return y[0] - 10.0*math.sqrt(beta)
    ev.terminal = True; ev.direction = 1
    r = solve_ivp(f, (s0, math.pi), [v0], method='DOP853', rtol=1e-10,
                  atol=1e-12, events=(ev,))
    return len(r.t_events[0]) > 0 or r.status < 0


def F(beta, ic='branch', nit=44):
    nu = 1.0/math.sqrt(2.0*beta)
    lo, hi = 1.0 + 0.80*nu, 1.0 + 1.60*nu + 2.0*nu*nu
    n = 0
    while esc_uni(beta, lo, ic) and n < 30:
        hi = lo; lo = 1.0 + 0.5*(lo - 1.0); n += 1
    n = 0
    while not esc_uni(beta, hi, ic) and n < 30:
        lo = hi; hi = 1.0 + 1.7*(hi - 1.0); n += 1
    if not esc_uni(beta, hi, ic) or esc_uni(beta, lo, ic):
        return float('nan')
    for _ in range(nit):
        m = 0.5*(lo + hi)
        if esc_uni(beta, m, ic):
            hi = m
        else:
            lo = m
    return 0.5*(lo + hi)


out("=== (U) the universal curve, and its own asymptotics")
out("   nu     |  beta     |  F-1 (branch IC) | (F-1)/nu | ((F-1)/nu-1)/nu "
    "| F-1 (equil IC)")
NUS = [0.01, 0.02, 0.03, 0.05, 0.075, 0.10, 0.15, 0.20, 0.25, 0.30,
       0.40, 0.50]
FB = {}
for nu in NUS:
    beta = 1.0/(2.0*nu*nu)
    f1 = F(beta) - 1.0
    f2 = F(beta, ic='equil') - 1.0
    FB[nu] = (f1, f2)
    out(f"  {nu:.3f}  | {beta:9.3f} | {f1:16.8f} | {f1/nu:8.5f} | "
        f"{(f1/nu-1)/nu:15.5f} | {f2:14.8f}")
out(f"    the derived series is 1 + nu + (3/8) nu^2, so the fourth column")
out(f"    must approach 0.375 as nu -> 0   [{time.time()-T0:.0f}s]")

MEAS = {}
cur = None
for ln in open('sweep20/gfmfold2.log').read().split('\n'):
    m = re.match(r'\s+([ABCD])\s+\|\s+([\d.]+)\s+\|\s+([\d.]+)\s+\|\s+'
                 r'([\d.e+-]+)\s+\|\s+([\d.]+)\s+\|', ln)
    if m:
        MEAS.setdefault(m.group(1), []).append(
            (float(m.group(2)), float(m.group(3)), float(m.group(5))))
out("")
out("=== (U) against the four cells")
out("  cell r     nu      | delta_meas | nu (1st) | 1+3/8 (2nd) | F(beta)-1 |"
    "  err 1st |  err 2nd |  err F")
sm = {k: [[], [], []] for k in 'ABCD'}
for c in 'ABCD':
    for r, nu, dl in MEAS.get(c, []):
        beta = 1.0/(2.0*nu*nu)
        fu = FB[nu][0] if nu in FB else F(beta) - 1.0
        p1, p2 = nu, nu + 0.375*nu*nu
        e1 = (p1 - dl)/(1.0 + dl)*100
        e2 = (p2 - dl)/(1.0 + dl)*100
        eF = (fu - dl)/(1.0 + dl)*100
        for i, e in enumerate((e1, e2, eF)):
            sm[c][i].append(abs(e))
        out(f"   {c}  {r:.3f} {nu:.5f} | {dl:.6f}   | {p1:.6f} | {p2:.6f}  "
            f"| {fu:.6f}  | {e1:+7.3f}% | {e2:+7.3f}% | {eF:+7.3f}%")
out("")
out("  (errors are on eps_c, i.e. (pred-meas)/(1+delta), so they are")
out("   directly comparable with the recorded 0.08 / 0.32 / 1.50%)")
out("  cell | max|err| 1st | max|err| 2nd | max|err| F")
for c in 'ABCD':
    if not sm[c][0]:
        continue
    out(f"    {c}  | {max(sm[c][0]):11.3f}% | {max(sm[c][1]):11.3f}% | "
        f"{max(sm[c][2]):10.3f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
