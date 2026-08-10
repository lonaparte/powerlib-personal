"""Second pass on the GFM, with three faults from gfmobs fixed.

1. The sign label was inverted.  rate = alpha_eff - Re c1 a^2, so a
   NEGATIVE a^2 coefficient means Re c1 > 0 = SUBcritical (a local guard
   exists) and a POSITIVE one means SUPERcritical (damping grows with
   amplitude, no local guard).  gfmobs printed the opposite; M2's
   measured +1.72e-1 therefore says supercritical, which is the correct
   physics for a GFM, not subcritical.
2. M5 at its default operating point has Re lam = +1.38 -- it is already
   past its Hopf point and sits on a bounded limit cycle, so it is not a
   valid ringdown cell.  A margin is imposed here by lowering Pref.
3. The largest excursion was being dropped: the release point at t = 0 is
   not found by the interior extremum test, so the first recorded swing
   was 0.43 of the margin instead of 0.97.  t = 0 is now included, and
   the separatrix fit uses the pendulum's own law -- the half period
   diverges LOGARITHMICALLY at the separatrix,
       T_half(A) = p + (1/lam_s) ln( 1/(A_sep - A) ),
   fitted for A_sep -- instead of the quadratic extrapolation, which
   reaches zero too early (gfmobs got 0.77 of the margin, -23%).
"""
import math, numpy as np, time
from scipy.integrate import solve_ivp
from scipy.optimize import least_squares
import gfmlib as G
LOG = open('sweep20/gfmobs2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
CELLS = [('M2', {}), ('M5', dict(Pref=0.25)), ('M4', {})]
for name, over in CELLS:
    pr = G.mset(name, **over)
    st = G.equil(pr, 'stable'); sd = G.equil(pr, 'saddle')
    if st is None or sd is None:
        out(f"{name}: no equilibrium pair"); continue
    d0, dsad = st[0], sd[0]; marg = dsad - d0
    A = G.jac(st, pr); ev = np.linalg.eigvals(A)
    cx = [e for e in ev if e.imag > 1e-9]
    lam = max(cx, key=lambda z: z.real) if cx else None
    Asd = G.jac(sd, pr)
    lams = max(np.linalg.eigvals(Asd), key=lambda z: z.real).real
    out(f"=== {name}{over}: margin={marg:.5f} rad, lam={lam:.5f}, "
        f"saddle unstable eigenvalue={lams:.5f}")
    if lam.real > 0:
        out("   operating point is past its Hopf point; skipped"); continue
    def ring(A0, T):
        x0 = np.array([d0 + A0, 0.0, st[2], st[3]])
        s = solve_ivp(lambda t, x: G.rhs(x, pr), (0, T), x0,
                      method='DOP853', rtol=1e-11, atol=1e-14,
                      dense_output=True)
        tt = np.linspace(0, min(T, s.t[-1]), 300000)
        return tt, s.sol(tt)
    tt, Y = ring(0.02*marg, 60.0)
    dv = Y[0] - d0
    d1 = np.diff(dv)
    idx = np.where(d1[:-1]*d1[1:] < 0)[0] + 1
    pk = [(tt[i], abs(dv[i])) for i in idx if abs(dv[i]) > 1e-12]
    amp, rate = [], []
    for i in range(0, len(pk)-2, 2):
        t1, a1 = pk[i]; t2, a2 = pk[i+2]
        if a1 > 0 and a2 > 0 and t2 > t1:
            amp.append(0.5*(a1+a2)); rate.append(-math.log(a2/a1)/(t2-t1))
    amp = np.array(amp); rate = np.array(rate)
    m = (amp > 0.1*amp.max()) & (amp < 0.98*amp.max())
    cf, *_ = np.linalg.lstsq(np.vstack([amp[m]**2, np.ones(m.sum())]).T,
                             rate[m], rcond=None)
    tag = ("SUBcritical (local guard exists)" if cf[0] < 0
           else "SUPERcritical (no local guard)")
    out(f"  (A) rate = {cf[1]:.6f} {cf[0]:+.4e} a^2  ->  {tag}")
    out(f"      intercept vs -Re lam: {cf[1]:.6f} vs {-lam.real:.6f} "
        f"({(cf[1]+lam.real)/(-lam.real)*100:+.3f}%)")
    tt, Y = ring(0.97*marg, 120.0)
    dv = Y[0] - d0
    d1 = np.diff(dv)
    idx = np.where(d1[:-1]*d1[1:] < 0)[0] + 1
    ex = [(0.0, dv[0])] + [(tt[i], dv[i]) for i in idx]
    rows = []
    for i in range(len(ex)-1):
        t1, v1 = ex[i]; t2, v2 = ex[i+1]
        if t2 > t1:
            rows.append((max(abs(v1), abs(v2)), t2-t1))
    rows = [r for r in rows if r[0] > 0.05*marg][:10]
    out(f"  (B) ringdown from 0.97 x margin: swing / margin  ->  half period")
    for a, T in rows:
        out(f"      {a/marg:.4f}   {T:.5f} s")
    if len(rows) >= 4:
        aa = np.array([r[0] for r in rows]); TT = np.array([r[1] for r in rows])
        def res(p):
            Asep, p0, sl = p
            d = np.maximum(Asep - aa, 1e-9)
            return p0 + sl*np.log(1.0/d) - TT
        sol = least_squares(res, [1.05*aa.max(), TT.min(), 1.0/max(lams, 0.1)],
                            bounds=([aa.max()*1.0001, -10, 1e-4],
                                    [5*marg, 10, 100]))
        Asep = sol.x[0]
        out(f"      log-law fit -> separatrix at swing {Asep:.5f} = "
            f"{Asep/marg:.4f} x the angle margin "
            f"({(Asep-marg)/marg*100:+.2f}%); fitted 1/lam_s = {sol.x[2]:.4f} "
            f"vs 1/lam_s(saddle) = {1/lams:.4f}  [{time.time()-T0:.0f}s]")
out("DONE")
