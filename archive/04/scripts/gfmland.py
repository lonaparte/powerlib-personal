"""Quantitative confirmation that the GFM sudden-on desync threshold is
a connection to the SADDLE periodic orbit (the basin boundary swept
past the unforced equilibrium).
Per set:
 (1) escape threshold by fine bisection (18 steps) + window check
     (T=60 vs 200 s) -- this IS the connection criterion, exactly;
 (2) landing eps: scan eps for the minimum scaled closest approach of
     the st-trajectory to the saddle orbit (metric normalised by the
     equilibrium-to-saddle separation);
 (3) agreement of (1) and (2) = quantitative confirmation.
Sets M2@0.03, M5@0.15. Budget ~12 min.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event)
from scipy.integrate import solve_ivp
LOG = open('sweep20/gfmland.log', 'w')
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

for name, Xg in (('M2', 0.03), ('M5', 0.15)):
    pr = build(name, Xg)
    st = equil(pr); ss = equil(pr, branch='saddle')
    w0 = crit_mode(jac(st, pr)).imag
    ev, dsad = escape_event(pr)
    V0 = pr['V']; wp = w0; Td = 2*math.pi/wp
    scale = np.maximum(np.abs(ss - st), 1e-3)
    out(f"{name}@{Xg}: st_d={st[0]:.4f} sad_d={ss[0]:.4f} w0={w0:.3f}")
    def esc(eps, T=60.0):
        def f(t, x):
            return rhs(x, dict(pr, V=V0*(1 + eps*math.cos(wp*t))))
        def e_d(t, x): return x[0] - dsad
        e_d.terminal = True; e_d.direction = 1
        s = solve_ivp(f, (0, T), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13, events=e_d)
        return len(s.t_events[0]) > 0 or s.status < 0
    lo, hi = 0.02, 0.10
    while not esc(hi) and hi < 0.5:
        hi *= 1.3
    while esc(lo) and lo > 1e-3:
        lo *= 0.7
    for _ in range(18):
        m = 0.5*(lo+hi)
        if esc(m): hi = m
        else: lo = m
    e_esc = 0.5*(lo+hi)
    if not esc(lo, 200.0):
        e200 = e_esc
    else:
        a2, b2 = 0.7*lo, lo
        for _ in range(12):
            m = 0.5*(a2+b2)
            if esc(m, 200.0): b2 = m
            else: a2 = m
        e200 = 0.5*(a2+b2)
    out(f"  escape threshold T=60s {e_esc*100:.4f}%  T=200s "
        f"{e200*100:.4f}%  (window shift {(e200-e_esc)/e_esc*100:+.2f}%) "
        f"[{time.time()-T0:.0f}s]")
    def strobe(x0, eps):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=V0*(1 + eps*math.cos(wp*t)))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq), (jac(x, qq) @ Phi).ravel()])
        s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                      method='DOP853', rtol=1e-11, atol=1e-13,
                      dense_output=True)
        return s, s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def orbit(x0, eps, itmax=40):
        x = x0.copy()
        for it in range(itmax):
            s, xT, M = strobe(x, eps)
            Fx = xT - x
            if np.max(np.abs(Fx)) < 1e-11:
                return s, x, True
            try:
                dx = np.linalg.solve(M - np.eye(4), -Fx)
            except np.linalg.LinAlgError:
                return None, x, False
            n = np.max(np.abs(dx))
            if n > 0.1: dx *= 0.1/n
            x = x + dx
        return None, x, False
    xS = ss.copy()
    NS = 400
    def dmin_at(eps, xS0):
        sS, xS1, ok = orbit(xS0, eps)
        if not ok:
            return None, xS0
        ttS = np.linspace(0, Td, NS)
        US = np.array([sS.sol(t)[:4] for t in ttS])
        def f4(t, x):
            return rhs(x, dict(pr, V=V0*(1 + eps*math.cos(wp*t))))
        def e_d(t, x): return x[0] - dsad
        e_d.terminal = True; e_d.direction = 1
        s4 = solve_ivp(f4, (0, 60.0), st.copy(), method='DOP853',
                       rtol=1e-10, atol=1e-13, events=e_d,
                       dense_output=True)
        dm = np.inf
        for t in np.linspace(0, s4.t[-1], 8000):
            j = int(round((t % Td)/Td*(NS-1))) % NS
            d = np.linalg.norm((s4.sol(t) - US[j])/scale)
            if d < dm: dm = d
        return dm, xS1
    for e_sub in np.linspace(0.002, 0.9*e_esc, 8):
        _, xS = dmin_at(e_sub, xS)
    best = None
    for fac in (0.96, 0.98, 0.99, 0.995, 1.0, 1.005, 1.01, 1.02):
        eps = fac*e_esc
        dm, xS = dmin_at(eps, xS)
        if dm is None:
            out(f"    fac={fac}: saddle orbit Newton failed"); continue
        out(f"    eps={eps*100:.4f}% ({fac:.3f}x): scaled closest "
            f"approach={dm:.4f} [{time.time()-T0:.0f}s]")
        if best is None or dm < best[1]:
            best = (eps, dm)
    if best:
        out(f"  LANDING at {best[0]*100:.4f}% (min approach {best[1]:.4f}"
            f") vs escape {e_esc*100:.4f}% -> agreement "
            f"{(best[0]-e_esc)/e_esc*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
