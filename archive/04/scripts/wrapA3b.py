"""A3 sharpened: measure Re c1 on the GFM cells where the fit is conditioned.

The first pass settled the sign question: all five VSM cells have analytic
Re c1 < 0 (supercritical), and the measured slope of D(rho) = alpha
- Re c1 rho^2 came out positive in all five, so the earlier "M4 has a
negative slope, therefore subcritical" was wrong -- and wrong for a reason
worth recording rather than waving away.

M4 has alpha = 1.963 with w0 = 12.776, so free oscillation loses a factor
e^{-0.96} per period.  Over the three-period fit window the amplitude falls
by 20x, the measured D varied by only 0.17% (1.96500..1.99926), and the
"rho at the window centre" label on that D is meaningless.  The regression
was fitting noise, which is how it produced a magnitude 2.4x too large here
and a sign flip in the earlier session.  Conditioning, not criticality.

Two better readouts, chosen per cell instead of one protocol for all:

 (a) unstable cells (M1, M5 have Re lam > 0 at Pref = 0.5).  Supercritical
     plus an unstable equilibrium means a STABLE limit cycle, whose radius
     is fixed with no fit at all:
         rho_LC = sqrt(alpha / Re c1),  both negative, ratio positive.
     Measured by integrating to the attractor and reading |<p, x - x_eq>|.
     This is the strongest available test of the MAGNITUDE of Re c1: one
     number against one number.

 (b) stable cells (M2, M3, M4).  Same decay law, but measured on windows
     short compared with 1/alpha so that rho barely moves within a window:
     window length 0.3/alpha capped at a third of a period, launch radii
     spanning 8 values, D evaluated by a two-point log slope at the window
     centre.  The span of rho across the SWEEP then does the work that the
     span within a window was wrongly being asked to do.
Budget ~25 min.
"""
import math, time
import numpy as np
import gfmlib as G
from scipy.integrate import solve_ivp
LOG = open('sweep20/wrapA3b.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

out("=== (a) unstable cells: limit-cycle radius vs sqrt(alpha / Re c1)")
out(" cell | alpha    | Re c1      | rho_LC predicted | rho_LC measured | err")
for nm in ('M1', 'M5'):
    pr = G.mset(nm)
    st = G.equil(pr)
    lam = G.crit_mode(G.jac(st, pr))
    co = G.hopf_c1(pr)
    pvec = co['p']; qvec = co['q']
    alpha = -lam.real; w0 = lam.imag; Tn = 2*math.pi/w0
    c1r = co['c1'].real
    if alpha >= 0 or c1r >= 0:
        out(f" {nm}: not an unstable+supercritical cell "
            f"(alpha={alpha:.4f}, Re c1={c1r:.3e})")
        continue
    rp = math.sqrt(alpha/c1r)
    x = st + 2*np.real(0.3*rp*qvec)
    s = solve_ivp(lambda t, y: G.rhs(y, pr), (0, 400*Tn), x,
                  method='DOP853', rtol=1e-12, atol=1e-15,
                  dense_output=True)
    ts = np.linspace(360*Tn, 400*Tn, 8000)
    zz = np.array([abs(np.vdot(pvec, s.sol(t) - st)) for t in ts])
    rm = float(np.mean(zz))
    ripple = float((zz.max()-zz.min())/rm)
    out(f" {nm}  | {alpha:+.6f} | {c1r:+.4e} | {rp:.6e}     | {rm:.6e}    "
        f"| {(rp-rm)/rm*100:+7.2f}%   (ripple {ripple:.1e}, "
        f"|z|/1 rad-scale)  [{time.time()-T0:.0f}s]")
    out(f"        launch 0.3 rho_LC, settled over 360-400 natural periods")

out("")
out("=== (b) stable cells: short-window D(rho), 8 launch radii")
for nm in ('M2', 'M3', 'M4'):
    pr = G.mset(nm)
    st = G.equil(pr)
    lam = G.crit_mode(G.jac(st, pr))
    co = G.hopf_c1(pr)
    pvec = co['p']; qvec = co['q']
    alpha = -lam.real; w0 = lam.imag; Tn = 2*math.pi/w0
    c1r = co['c1'].real
    xs = G.equil(pr, branch='saddle')
    rmax = 0.30*abs(np.vdot(pvec, xs - st))
    win = min(0.30/alpha, Tn/3.0)
    t0 = min(0.15/alpha, Tn/6.0)
    rows = []
    for k in range(8):
        r0 = rmax*(0.12 + 0.88*k/7.0)
        x = st + 2*np.real(r0*qvec)
        s = solve_ivp(lambda t, y: G.rhs(y, pr), (0, t0+2*win), x,
                      method='DOP853', rtol=1e-13, atol=1e-16,
                      dense_output=True)
        ta, tb = t0, t0+win
        za = abs(np.vdot(pvec, s.sol(ta) - st))
        zb = abs(np.vdot(pvec, s.sol(tb) - st))
        # average over a whole number of half-cycles is not available for
        # a fast cell, so use the envelope from three closely spaced probes
        D = -(math.log(zb) - math.log(za))/win
        rc = math.sqrt(za*zb)
        rows.append((rc, D))
    rr = np.array([r for r, _ in rows]); dd = np.array([d for _, d in rows])
    M = np.vstack([np.ones_like(rr), rr**2]).T
    a_fit, s_fit = np.linalg.lstsq(M, dd, rcond=None)[0]
    pred = a_fit - c1r*rr**2
    rms = float(np.sqrt(np.mean((dd - pred)**2)))
    out(f" {nm}: alpha(eig)={alpha:.6f} alpha(fit)={a_fit:.6f} "
        f"| -Re c1 = {-c1r:+.5e} vs slope {s_fit:+.5e} "
        f"({(s_fit+c1r)/(-c1r)*100:+7.2f}%)")
    out(f"      window {win:.4f}s ({win/Tn:.3f} periods), rho span "
        f"{rr.min():.4e}..{rr.max():.4e} ({rr.max()/rr.min():.1f}x), "
        f"D span {dd.min():.5f}..{dd.max():.5f} "
        f"({(dd.max()-dd.min())/alpha*100:.2f}% of alpha)")
    out(f"      rms of D about alpha - Re c1 rho^2 with the ANALYTIC c1: "
        f"{rms:.3e}  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
