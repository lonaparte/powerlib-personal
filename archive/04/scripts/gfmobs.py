"""The identification-free readout beyond the subcritical case.

The decay-line proof used the subcritical guard: rho_g = sqrt(alpha_eff /
Re c1), so it says nothing about a supercritical machine like the GFM,
whose boundary is not a nearby limit cycle at all but the stable manifold
of the saddle periodic orbit, at angular distance delta_sad - delta_0.

What the proof actually used is weaker: (1) the dynamics near the
boundary reduces to one amplitude-like coordinate, (2) any observable's
envelope is that coordinate times an unknown constant, (3) therefore any
SCALE-INVARIANT functional of the observable equals the same functional
of the internal coordinate.  Step (3) does not care what the boundary is.
Only the choice of which scale-invariant rate vanishes there changes:

  subcritical guard cycle -> the radial decay rate -da/a / a  -> 0
  saddle separatrix       -> the oscillation FREQUENCY 2 pi/T -> 0
                             (the pendulum's period diverges at the
                             separatrix)

Two things are measured here on the GFM, both from ringdowns of a single
observable and with no model used in the reading:

(A) the sign test.  Fit -da/a = A - B a^2 at small amplitude.  For a
    supercritical machine B must come out NEGATIVE (damping grows with
    amplitude, no local guard), which is the observable form of
    sign(Re l1) -- the tree's A3/A5/B3 node, read off one ringdown.
(B) the separatrix test.  Ring down from just inside the basin and record
    (peak angle swing, half period).  The oscillation frequency must fall
    towards zero as the swing approaches the angle margin
    delta_sad - delta_0, which is known independently from the two
    equilibria.  Extrapolating frequency -> 0 gives the boundary without
    any model.
Sets: M2 and M5, the two whose desynchronisation signature was verified
digit-for-digit earlier.
"""
import math, numpy as np, time
from scipy.integrate import solve_ivp
import gfmlib as G
LOG = open('sweep20/gfmobs.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
for name in ('M2', 'M5'):
    pr = G.mset(name)
    st = G.equil(pr, 'stable'); sd = G.equil(pr, 'saddle')
    d0, dsad = st[0], sd[0]
    marg = dsad - d0
    A = G.jac(st, pr)
    ev = np.linalg.eigvals(A)
    cx = [e for e in ev if e.imag > 1e-9]
    lam = max(cx, key=lambda z: z.real) if cx else None
    out(f"=== {name}: delta_0={d0:.5f}, delta_sad={dsad:.5f}, "
        f"angle margin={marg:.5f} rad; lam={lam:.5f}")
    def ring(A0, T, npts=200000):
        x0 = np.array([d0 + A0, 0.0, st[2], st[3]])
        s = solve_ivp(lambda t, x: G.rhs(x, pr), (0, T), x0,
                      method='DOP853', rtol=1e-11, atol=1e-14,
                      dense_output=True)
        tt = np.linspace(0, min(T, s.t[-1]), npts)
        Y = s.sol(tt)
        return tt, Y
    # ---- (A) small-amplitude: sign of the a^2 coefficient ----
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
    Xf = np.vstack([amp[m]**2, np.ones(m.sum())]).T
    cf, *_ = np.linalg.lstsq(Xf, rate[m], rcond=None)
    out(f"  (A) small-amplitude fit on the angle signal, {m.sum()} points:"
        f"  rate = {cf[1]:.6f} {cf[0]:+.4e} a^2")
    tag = ("NEGATIVE (supercritical: damping grows with amplitude, "
           "no local guard)" if cf[0] < 0 else
           "POSITIVE (subcritical: a local guard exists)")
    out(f"      a^2 coefficient sign = {tag}")
    out(f"      intercept {cf[1]:.6f} vs -Re lam {-lam.real:.6f} "
        f"({(cf[1]+lam.real)/(-lam.real)*100:+.2f}%)")
    # ---- (B) large amplitude: frequency towards the separatrix ----
    tt, Y = ring(0.97*marg, 80.0)
    dv = Y[0] - d0
    d1 = np.diff(dv)
    idx = np.where(d1[:-1]*d1[1:] < 0)[0] + 1
    ex = [(tt[i], dv[i]) for i in idx]
    rows = []
    for i in range(len(ex)-1):
        t1, v1 = ex[i]; t2, v2 = ex[i+1]
        if t2 <= t1: continue
        rows.append((0.5*(abs(v1)+abs(v2)), math.pi/(t2-t1)))
    rows = [r for r in rows if r[0] > 0.05*marg]
    out(f"  (B) ringdown from 0.97 x margin, {len(rows)} half-periods:")
    for a, w in rows[:8]:
        out(f"      swing {a/marg:.4f} x margin   frequency {w:.5f} rad/s")
    if len(rows) >= 4:
        aa = np.array([r[0] for r in rows[:6]])
        ww = np.array([r[1] for r in rows[:6]])
        Xf2 = np.vstack([aa**2, np.ones(len(aa))]).T
        c2, *_ = np.linalg.lstsq(Xf2, ww**2, rcond=None)
        acr = math.sqrt(-c2[1]/c2[0]) if c2[0] < 0 else float('nan')
        out(f"      w^2 vs a^2 fit -> zero at swing {acr:.5f} = "
            f"{acr/marg:.4f} x the angle margin  [{time.time()-T0:.0f}s]")
out("DONE")
