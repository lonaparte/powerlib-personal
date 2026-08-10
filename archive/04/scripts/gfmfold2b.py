"""Is the erratic delta(nu) at larger w_p physics, or the start transient?

gfmfold2's delta/nu is monotone and smooth for cell A at every frequency,
but for B and C it breaks above w_p ~ 0.15 w0 (B: 1.0163, 0.9793, 0.9535,
1.0725; C: 1.0242, 1.0215, 1.0901, 1.0644).  Non-monotone is a warning
sign, not a data point.

The obvious suspect is the PROTOCOL, not the mechanism: the run starts the
state at the UNFORCED equilibrium at t = 0, where the drive already sits at
its maximum V0 + eps.  That is an O(eps) initial offset from the branch, and
it rings at w0 with the cell's own damping before the first dip arrives at
t = T/2.  Cells A and C are M2 (M = 0.1, D = 0.2); B and D are M3
(M = 0.005, D = 0.02) -- an order of magnitude lighter.  A lightly damped
cell would still be ringing when the dip arrives, and the threshold would
then depend on the ringing phase, which is exactly what "non-monotone in
w_p" looks like.

So re-measure with the transient removed: start on the QUASI-STATIC branch,
i.e. at the stable equilibrium of V = V0 + eps.  If the erratic points
straighten out, the recorded eps_c at larger w_p (and the 1.50% residual
built on them) were partly protocol; if they do not, the resonant band is
genuinely intruding and belongs to the Melnikov branch, not to slow passage.
Either answer is worth having; guessing between them is not.
"""
import math, time
import numpy as np
import gfmlib as G
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

LOG = open('sweep20/gfmfold2b.log', 'w')
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
    df = brentq(dP, dl[max(i-2, 0)], dl[min(i+2, len(dl)-1)],
                xtol=1e-14, rtol=1e-15)
    return df, G.P_of(df, pr)


def eps_qs_of(pr):
    def gap(u):
        return Pmax(dict(pr, V=pr['V']-u))[1] - pr['Pref']
    hi = 0.98*pr['V']; n = 0
    while gap(hi) > 0 and n < 40:
        hi = 0.5*(hi + pr['V']); n += 1
    return brentq(gap, 0.0, hi, xtol=1e-14, rtol=1e-15)


def escaped(pr, eps, wp, dsad, st, ic, nper=2.2):
    x0 = st if ic == 'unforced' else G.equil(dict(pr, V=pr['V']+eps))
    if x0 is None:
        return True
    def fun(t, x):
        return G.rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
    def ev(t, x):
        return x[0] - dsad
    ev.terminal = True; ev.direction = 1
    s = solve_ivp(fun, (0.0, nper*2*math.pi/wp), x0, method='DOP853',
                  rtol=1e-11, atol=1e-13, events=(ev,))
    return len(s.t_events[0]) > 0


def thr(pr, wp, dsad, st, eqs, ic, nit=34):
    lo, hi = eqs*(1.0 + 1e-6), eqs*1.60
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


CELLS = [('A  M2 Xg=0.5 90%', 'M2', 0.5, 0.90),
         ('B  M3 Xg=0.5 90%', 'M3', 0.5, 0.90),
         ('C  M2 Xg=0.3 75%', 'M2', 0.3, 0.75),
         ('D  M3 Xg=0.3 90%', 'M3', 0.3, 0.90)]
RATS = [0.02, 0.05, 0.10, 0.15, 0.20, 0.30]
out("  cell |  w_p/w0 |    nu    | delta (unforced IC) | delta (branch IC) | "
    "d/nu unf | d/nu br | interval?")
for tag, nm, Xg, frac in CELLS:
    _, Pm0 = Pmax(G.mset(nm, Xg=Xg))
    pr = G.mset(nm, Xg=Xg, Pref=frac*Pm0)
    st = G.equil(pr)
    w0 = G.crit_mode(G.jac(st, pr)).imag
    eqs = eps_qs_of(pr)
    stf_pr = dict(pr, V=pr['V']-eqs)
    df, _ = Pmax(stf_pr)
    E = G.E_of(df, stf_pr)
    Qf = (E*E - E*stf_pr['V']*math.cos(df))/stf_pr['Xg']
    A = G.jac(np.array([df, 0.0, stf_pr['Pref'], Qf]), stf_pr)
    from scipy.linalg import eig
    evv, VL, VR = eig(A, left=True, right=True)
    k = int(np.argmin(np.abs(evv)))
    vv = np.real(VR[:, k]); wv = np.real(VL[:, k]); wv = wv/np.dot(wv, vv)
    HS = 1e-6
    fV = (G.rhs(np.array([df, 0.0, stf_pr['Pref'], Qf]),
                dict(stf_pr, V=stf_pr['V']+HS))
          - G.rhs(np.array([df, 0.0, stf_pr['Pref'], Qf]),
                  dict(stf_pr, V=stf_pr['V']-HS)))/(2*HS)
    a = float(np.dot(wv, -fV))
    b = 0.5*float(np.dot(wv, G.Bform(np.array([df, 0.0, stf_pr['Pref'], Qf]),
                                     stf_pr, vv, vv)))
    ab = abs(a*b)
    dsad = G.equil(pr, branch='saddle')[0]
    for r in RATS:
        wp = r*w0
        nu = wp/math.sqrt(2.0*ab*eqs)
        e1 = thr(pr, wp, dsad, st, eqs, 'unforced')
        e2 = thr(pr, wp, dsad, st, eqs, 'branch')
        d1 = e1/eqs - 1.0; d2 = e2/eqs - 1.0
        flips = 0; prev = None
        for f in (0.97, 0.99, 1.0, 1.005, 1.01, 1.03, 1.06, 1.10):
            g = escaped(pr, e2*f, wp, dsad, st, 'branch')
            if prev is not None and g != prev:
                flips += 1
            prev = g
        out(f"   {tag[0]}   |  {r:.3f}  | {nu:.5f} | {d1:.6f}            | "
            f"{d2:.6f}          | {d1/nu:.5f} | {d2/nu:.5f} | "
            f"{'ok' if flips == 1 else f'FLIPS={flips}'}   "
            f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
