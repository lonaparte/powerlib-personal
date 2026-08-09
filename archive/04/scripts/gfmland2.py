"""GFM sudden-on threshold: signed landing indicator.
Boundary object = saddle fixed point x_S of the stroboscopic map
(continuation of the saddle equilibrium).  Let p_u be the left
eigenvector of the monodromy for the unstable multiplier.  Along the
trajectory from the unforced equilibrium, take the stroboscopic point
of closest approach to x_S (delta-omega metric) and evaluate the
signed unstable component
        s(eps) = <p_u, x_closest - x_S> / ||x_closest - x_S||.
Below threshold the trajectory falls back (one sign), above it departs
through the boundary (other sign); the zero crossing locates the
connection.  Compare with the escape bisection (which IS the exact
criterion).  Sets M2@0.03 (escape 5.2639%), M5@0.15 (4.8753%).
Budget ~10 min.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event)
from scipy.integrate import solve_ivp
from scipy.linalg import eig as _eig
LOG = open('sweep20/gfmland2.log', 'w')
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

for name, Xg, e_esc in (('M2', 0.03, 0.052639), ('M5', 0.15, 0.048753)):
    pr = build(name, Xg)
    st = equil(pr); ss = equil(pr, branch='saddle')
    w0 = crit_mode(jac(st, pr)).imag
    ev, dsad = escape_event(pr)
    V0 = pr['V']; wp = w0; Td = 2*math.pi/wp
    out(f"{name}@{Xg}: st_d={st[0]:.4f} sad_d={ss[0]:.4f} "
        f"escape_ref={e_esc*100:.4f}%")
    def strobe(x0, eps):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=V0*(1 + eps*math.cos(wp*t)))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq), (jac(x, qq) @ Phi).ravel()])
        s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                      method='DOP853', rtol=1e-11, atol=1e-13)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def saddle_fp(x0, eps, itmax=40):
        x = x0.copy()
        for it in range(itmax):
            xT, M = strobe(x, eps)
            Fx = xT - x
            if np.max(np.abs(Fx)) < 1e-12:
                return x, M, True
            try:
                dx = np.linalg.solve(M - np.eye(4), -Fx)
            except np.linalg.LinAlgError:
                return x, None, False
            n = np.max(np.abs(dx))
            if n > 0.08: dx *= 0.08/n
            x = x + dx
        return x, M, np.max(np.abs(Fx)) < 1e-9
    def indicator(eps, xS0):
        xS, M, ok = saddle_fp(xS0, eps)
        if not ok:
            return None, xS0, None
        evals, VL, VR = _eig(M, left=True, right=True)
        k = int(np.argmax(np.abs(evals)))
        pu = VL[:, k].real
        pu = pu/np.linalg.norm(pu)
        def f4(t, x):
            return rhs(x, dict(pr, V=V0*(1 + eps*math.cos(wp*t))))
        def e_d(t, x): return x[0] - dsad
        e_d.terminal = True; e_d.direction = 1
        NP = 900
        tev = np.arange(NP)*Td
        s4 = solve_ivp(f4, (0, (NP-1)*Td), st.copy(), method='DOP853',
                       rtol=1e-11, atol=1e-13, events=e_d, t_eval=tev)
        X = s4.y.T
        w = np.array([1.0, 1.0/max(w0, 1.0), 0.0, 0.0])   # delta-omega
        d = np.array([np.linalg.norm(w*(x - xS)) for x in X])
        j = int(np.argmin(d))
        v = X[j] - xS
        sgn = float(np.dot(pu, v)/max(np.linalg.norm(v), 1e-30))
        return (sgn, d[j], j, len(s4.t_events[0]) > 0), xS, pu
    xS = ss.copy()
    for e_sub in np.linspace(0.002, 0.90*e_esc, 10):
        _, xS, _ = indicator(e_sub, xS)
    rows = []
    for fac in (0.90, 0.95, 0.98, 0.995, 1.0, 1.005, 1.02, 1.05):
        eps = fac*e_esc
        r, xS, pu = indicator(eps, xS)
        if r is None:
            out(f"    fac={fac}: saddle Newton failed"); continue
        sgn, dcl, j, esc = r
        rows.append((eps, sgn))
        out(f"    eps={eps*100:.4f}% ({fac:.3f}x): closest approach "
            f"d={dcl:.4e} at n={j}, signed unstable component="
            f"{sgn:+.4f}, escaped={esc} [{time.time()-T0:.0f}s]")
    # zero crossing of the signed indicator
    zc = None
    for (e1, s1), (e2, s2) in zip(rows[:-1], rows[1:]):
        if s1*s2 < 0:
            zc = e1 + (e2-e1)*(-s1)/(s2-s1)
            break
    if zc:
        out(f"  signed-indicator zero crossing at {zc*100:.4f}% vs "
            f"escape {e_esc*100:.4f}% -> err {(zc-e_esc)/e_esc*100:+.2f}%")
    else:
        out(f"  no sign change over the scanned range "
            f"(indicator range {min(r[1] for r in rows):+.3f} .. "
            f"{max(r[1] for r in rows):+.3f})")
out(f"DONE wall={time.time()-T0:.0f}s")
