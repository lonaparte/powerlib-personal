"""A3 magnitude, done where the cubic normal form is entitled to be right.

The sign question is settled: analytic Re c1 < 0 for all five VSM cells, the
measured slope of D(rho) = alpha - Re c1 rho^2 agrees in sign for all five,
and the earlier "M4 negative slope, therefore subcritical" was a
conditioning artefact.

The MAGNITUDE checks then failed, and the failures are informative rather
than mysterious:

    M1 limit cycle   +31.7%   rho_LC = 1.97 rad
    M5 limit cycle   -24.5%   rho_LC = 17.3, ripple 0.56
    M2 short-window  slope -2.86e-3 against analytic +4.60e-3 -- sign flip
    M3 short-window  +155%,  D varied by 291% of alpha across the sweep

Every one of these is the same mistake: Re c1 is the cubic coefficient of an
expansion about a HOPF POINT, and these cells are nowhere near one.  M5 has
alpha = -1.383 against w0 = 21.96, so it is far past its bifurcation and its
attractor is a large relaxation-type orbit with 56% ripple in |<p,x-x_eq>| --
calling its radius sqrt(alpha/Re c1) is meaningless.  M3's sweep pushed
Re c1 rho^2 up to 1.2x alpha, i.e. the cubic term became the whole equation.
Reporting those numbers as a test of Re c1 would be testing an expansion
outside its own radius of convergence.

Done correctly here.  For each cell, locate the Hopf in the damping D (D is
the natural continuation parameter: lowering it destabilises), evaluate
Re c1 AT that Hopf point, then step a controlled distance onto the unstable
side, D = D_H (1 - eta).  Supercritical plus an unstable equilibrium gives a
STABLE limit cycle whose radius is fixed with no fit:

    rho_LC = sqrt(alpha / Re c1),  alpha = -Re lam < 0, Re c1 < 0.

Three values of eta per cell test both the constant AND the scaling, since
rho_LC must go as sqrt(alpha): halving eta must shrink the radius by
sqrt(2).  That scaling is the part that cannot be faked by a coincidence of
one number.
Budget ~25 min.
"""
import math, time
import numpy as np
import gfmlib as G
from scipy.integrate import solve_ivp
LOG = open('sweep20/wrapA3c.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

for nm in ('M1', 'M2', 'M3', 'M4', 'M5'):
    base = G.mset(nm)
    prH = None
    for lo, hi in ((1e-4, base['D']), (base['D'], 20*base['D']),
                   (1e-5, 50*base['D'])):
        prH = G.hopf_in(dict(base), 'D', lo, hi)
        if prH is not None:
            break
    if prH is None:
        out(f"=== {nm}: no Hopf found in D over [1e-5, 50 D0]")
        continue
    DH = prH['D']
    co = G.hopf_c1(prH)
    c1r = co['c1'].real
    lamH = G.crit_mode(G.jac(G.equil(prH), prH))
    out(f"=== {nm}: Hopf at D = {DH:.6e} (D0 = {base['D']:.4g}), "
        f"w0 = {lamH.imag:.5f}, Re lam = {lamH.real:+.2e}")
    out(f"    Re c1 at the Hopf point = {c1r:+.6e}  "
        f"({'supercritical' if c1r < 0 else 'subcritical'})")
    if c1r >= 0:
        out("    subcritical: no stable limit cycle to measure, skipping")
        continue
    out("   eta   |     D      |  alpha    | rho_LC pred | rho_LC meas | "
        "err     | ripple | sqrt scaling")
    prev = None
    for eta in (0.02, 0.04, 0.08):
        pr = dict(prH, D=DH*(1.0 - eta))
        st = G.equil(pr)
        if st is None:
            out(f"   {eta:5.3f} | no equilibrium"); continue
        lam = G.crit_mode(G.jac(st, pr))
        alpha = -lam.real
        if alpha >= 0:
            out(f"   {eta:5.3f} | still stable (alpha={alpha:+.2e})")
            continue
        rp = math.sqrt(alpha/c1r)
        Tn = 2*math.pi/lam.imag
        pvec = co['p']; qvec = co['q']
        x = st + 2*np.real(0.5*rp*qvec)
        s = solve_ivp(lambda t, y: G.rhs(y, pr), (0, 900*Tn), x,
                      method='DOP853', rtol=1e-12, atol=1e-15,
                      dense_output=True)
        ts = np.linspace(820*Tn, 900*Tn, 12000)
        zz = np.array([abs(np.vdot(pvec, s.sol(t) - st)) for t in ts])
        rm = float(np.mean(zz))
        rip = float((zz.max()-zz.min())/rm)
        sc = "" if prev is None else \
            f" meas {rm/prev[0]:.4f} vs sqrt {math.sqrt(alpha/prev[1]):.4f}"
        out(f"   {eta:5.3f} | {pr['D']:.4e} | {alpha:+.6f} | {rp:.6e} | "
            f"{rm:.6e} | {(rp-rm)/rm*100:+7.2f}% | {rip:.1e} |{sc}  "
            f"[{time.time()-T0:.0f}s]")
        prev = (rm, alpha)
out(f"DONE wall={time.time()-T0:.0f}s")
