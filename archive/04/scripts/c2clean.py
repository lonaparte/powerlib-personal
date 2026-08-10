"""Is C2_meas protocol-contaminated?  It has to be checked, not assumed.

C2 was extracted from delta(nu) measured with the UNFORCED-equilibrium start,
because that was the recorded protocol.  §20.3 then found that protocol is
contaminated -- and quantified it at w_p = 0.10 w0 as +0.18% (B), -0.13% (C),
-1.07% (D) on delta.  I checked that those frequencies were "<= 0.10 w0 so
protocol-safe" and moved on.  That check was against the wrong yardstick.

C2 is the coefficient of the SECOND-order term: delta/nu - 1 = C2 nu, and at
the small nu used for the fit that quantity is ~0.008-0.012.  A 1% error on
delta is therefore not 1% of the answer, it is up to ~50% of it.  For cell D
the contamination at 0.10 is -1.07%; if it scales like nu^2 it is still ~0.6%
at r = 0.075, against a signal of ~1.2%.

So the agreement C2_pred vs C2_meas (+0.0001/-0.0006/+0.0021/+0.0032) may be
partly fortuitous for B, C, D.  Cell A is safe -- gfmfold2b measured both
protocols at every frequency and they were identical to 6 digits.

Re-measure delta(nu) for B, C, D at the four smallest nu with the CLEAN
protocol (state starts on the quasi-static branch of V0 + eps), re-extract
C2, and compare.  Budget ~25 min.
"""
import math, time
import numpy as np
import gfmlib as G
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

LOG = open('sweep20/c2clean.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()


def Pmax(pr):
    h = 1e-6
    def dP(d):
        return (G.P_of(d+h, pr) - G.P_of(d-h, pr))/(2*h)
    dl = np.linspace(0.05, math.pi-0.05, 4000)
    Pv = np.array([G.P_of(d, pr) for d in dl])
    i = int(np.argmax(Pv))
    return brentq(dP, dl[max(i-2, 0)], dl[min(i+2, len(dl)-1)],
                  xtol=1e-14, rtol=1e-15)


def eps_qs_of(pr):
    def gap(u):
        q = dict(pr, V=pr['V']-u)
        return G.P_of(Pmax(q), q) - pr['Pref']
    hi = 0.98*pr['V']; n = 0
    while gap(hi) > 0 and n < 40:
        hi = 0.5*(hi + pr['V']); n += 1
    return brentq(gap, 0.0, hi, xtol=1e-14, rtol=1e-15)


def escaped(pr, eps, wp, dsad, st, ic):
    x0 = st if ic == 'unforced' else G.equil(dict(pr, V=pr['V']+eps))
    if x0 is None:
        return True
    def fun(t, x):
        return G.rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
    def ev(t, x):
        return x[0] - dsad
    ev.terminal = True; ev.direction = 1
    s = solve_ivp(fun, (0.0, 2.2*2*math.pi/wp), x0, method='DOP853',
                  rtol=1e-11, atol=1e-13, events=(ev,))
    return len(s.t_events[0]) > 0


def thr(pr, wp, dsad, st, eqs, ic, nit=36):
    lo, hi = eqs*(1.0 + 1e-7), eqs*1.6
    n = 0
    while not escaped(pr, hi, wp, dsad, st, ic) and n < 8:
        lo = hi; hi *= 1.3; n += 1
    if not escaped(pr, hi, wp, dsad, st, ic):
        return float('nan')
    for _ in range(nit):
        m = 0.5*(lo+hi)
        if escaped(pr, m, wp, dsad, st, ic): hi = m
        else: lo = m
    return 0.5*(lo+hi)


CELLS = [('B  M3 Xg=0.5 90%', 'M3', 0.5, 0.90, 0.3741),
         ('C  M2 Xg=0.3 75%', 'M2', 0.3, 0.75, 0.3350),
         ('D  M3 Xg=0.3 90%', 'M3', 0.3, 0.90, 0.3972)]
RATS = [0.02, 0.03, 0.05, 0.075]
out("  cell |  r    |    nu    | delta unforced | delta branch  | dU/nu-1 |"
    " dB/nu-1 | protocol shift")
for tag, nm, Xg, frac in [(c[0], c[1], c[2], c[3]) for c in CELLS]:
    pr0 = G.mset(nm, Xg=Xg)
    pr = G.mset(nm, Xg=Xg, Pref=frac*G.P_of(Pmax(pr0), pr0))
    st = G.equil(pr)
    w0 = G.crit_mode(G.jac(st, pr)).imag
    eqs = eps_qs_of(pr)
    prf = dict(pr, V=pr['V']-eqs)
    df = Pmax(prf)
    E = G.E_of(df, prf)
    Qf = (E*E - E*prf['V']*math.cos(df))/prf['Xg']
    stf = np.array([df, 0.0, prf['Pref'], Qf])
    from scipy.linalg import eig
    evv, VL, VR = eig(G.jac(stf, prf), left=True, right=True)
    k = int(np.argmin(np.abs(evv)))
    vv = np.real(VR[:, k]); wv = np.real(VL[:, k]); wv = wv/np.dot(wv, vv)
    HS = 1e-6
    fV = (G.rhs(stf, dict(prf, V=prf['V']+HS))
          - G.rhs(stf, dict(prf, V=prf['V']-HS)))/(2*HS)
    ab = abs(float(np.dot(wv, -fV))
             * 0.5*float(np.dot(wv, G.Bform(stf, prf, vv, vv))))
    dsad = G.equil(pr, branch='saddle')[0]
    nus = []; cu = []; cb = []
    for r in RATS:
        wp = r*w0
        nu = wp/math.sqrt(2.0*ab*eqs)
        eu = thr(pr, wp, dsad, st, eqs, 'unforced')
        eb = thr(pr, wp, dsad, st, eqs, 'branch')
        du = eu/eqs - 1.0; db = eb/eqs - 1.0
        nus.append(nu); cu.append((du/nu - 1.0)/nu); cb.append((db/nu - 1.0)/nu)
        out(f"   {tag[0]}   | {r:.3f} | {nu:.5f} | {du:.7f}      | "
            f"{db:.7f}     | {du/nu-1:+.5f} | {db/nu-1:+.5f} | "
            f"{(db-du)/du*100:+.3f}%   [{time.time()-T0:.0f}s]")
    nus = np.array(nus)
    fu_ = np.polyfit(nus, np.array(cu), 1)[1]
    fb_ = np.polyfit(nus, np.array(cb), 1)[1]
    out(f"   {tag}: C2 from unforced protocol {fu_:+.4f}, from clean "
        f"protocol {fb_:+.4f}, shift {fb_-fu_:+.4f}")
out(f"DONE wall={time.time()-T0:.0f}s")
