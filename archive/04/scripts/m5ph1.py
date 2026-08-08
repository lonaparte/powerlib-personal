"""M5@0.10 res eps=0.01: fine kick scan at ph1 (meas 4.914, BVP pred
+1.1%) and ph0 control (-0.1%). For each fac x meas: fate (c/E),
escape time, and swing count (delta local maxima before escape).
Banded fate sequence -> ph1 is band-edge like ph2/ph3 (envelope
delivery); monotone -> real BVP error. Budget ~3 min.
"""
import math, numpy as np, time, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event)
from scipy.integrate import solve_ivp
LOG = open('sweep20/m5ph1.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def build(name, Xg):
    pr = mset(name, Xg=Xg)
    dfold, Pm = fold(pr)
    q = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
    P_H = q['Pref']
    def g(P):
        r = maxre_cx(dict(pr, Pref=P))
        return 1.0 if r is None else r
    Phi_ = min(0.95*Pm, 2.5*P_H)
    tt = 0.10
    if g(Phi_) > -tt:
        tt = max(0.3*abs(g(Phi_)), 0.02)
    lo2, hi2 = P_H, Phi_
    for _ in range(45):
        m = 0.5*(lo2+hi2)
        if g(m) > -tt: lo2 = m
        else: hi2 = m
    return dict(pr, Pref=0.5*(lo2+hi2))

prm = build('M5', 0.10)
st = equil(prm)
w0 = crit_mode(jac(st, prm)).imag
ev, dsad = escape_event(prm)
eps, wp = 0.010, w0
V0 = prm['V']
Tset = 60.0
Tdp = 2*math.pi/wp
def f(t, xx):
    qq = dict(prm, V=V0*(1 + eps*math.cos(wp*t)))
    return rhs(xx, qq)
s = solve_ivp(f, (0, Tset+Tdp), st.copy(), method='DOP853',
              rtol=1e-10, atol=1e-13, dense_output=True)
MEAS = {0: 6.945, 1: 4.914}
for j in (1, 0):
    tk = Tset + j*Tdp/4
    xb = s.sol(tk)
    meas = MEAS[j]
    out(f"ph{j}: xb=({xb[0]:.4f},{xb[1]:.4f},{xb[2]:.4f},{xb[3]:.4f}) "
        f"meas={meas}")
    for fac in (0.95, 0.96, 0.97, 0.98, 0.99, 1.00, 1.01, 1.02, 1.03,
                1.04, 1.06, 1.08):
        xk = xb.copy(); xk[1] += fac*meas
        sk = solve_ivp(f, (tk, tk+80.0), xk, method='DOP853',
                       rtol=1e-9, atol=1e-12, events=ev,
                       dense_output=True)
        esc = len(sk.t_events[0]) > 0
        te = sk.t_events[0][0]-tk if esc else None
        # swing count: local maxima of delta before escape/end
        tt2 = np.linspace(tk, sk.t_events[0][0] if esc else tk+80.0,
                          4000)
        dl = sk.sol(tt2)[0]
        nmax = int(np.sum((dl[1:-1] > dl[:-2]) & (dl[1:-1] > dl[2:])
                          & (dl[1:-1] > 0.2)))
        out(f"  ph{j} fac={fac:.2f}: {'E' if esc else 'c'}"
            + (f" t={te:.2f}s swings={nmax}" if esc else
               f" swings(80s)={nmax}")
            + f" [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
