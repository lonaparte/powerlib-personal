"""GFM sudden-on desync: which object carries the threshold?
Three competing explanations, all tested at the measured edge:
 (H1) forced attracting orbit loses Floquet stability  -> check |mu|max
 (H2) forced attracting orbit's angle excursion reaches delta_sad
      (already refuted: predicts 27% vs measured 5.26%)
 (H3) the basin boundary of the forced attractor sweeps past the
      unforced equilibrium; boundary = stable manifold of the SADDLE
      periodic orbit (continued from the saddle equilibrium).
      Criterion (same structure as GFL's B3a, different object):
      trajectory from st lands asymptotically on the saddle orbit.
Measure: min stroboscopic distance from the st-trajectory to the
saddle orbit, as a function of eps; the landing (distance -> 0)
locates the threshold.  Sets M2@0.03 (meas 5.26%), M5@0.15 (4.88%),
M1@0.10 (no desync to 45% -> saddle orbit must stay far).
Budget ~12 min.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event)
from scipy.integrate import solve_ivp
LOG = open('sweep20/gfmconn.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

CASES = [('M2', 0.03, 0.0526), ('M5', 0.15, 0.0488), ('M1', 0.10, None)]

def build(name, Xg):
    pr = mset(name, Xg=Xg)
    dfold, Pm = fold(pr)
    q = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
    if q is None: return None
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

for name, Xg, meas in CASES:
    pr = build(name, Xg)
    if pr is None:
        out(f"{name}@{Xg}: no window"); continue
    st = equil(pr)
    ss = equil(pr, branch='saddle')
    w0 = crit_mode(jac(st, pr)).imag
    ev, dsad = escape_event(pr)
    V0 = pr['V']; wp = w0; Td = 2*math.pi/wp
    out(f"{name}@{Xg}: st_d={st[0]:.4f} saddle_d={ss[0]:.4f} "
        f"w0={w0:.3f} meas={meas}")
    def strobe(x0, eps):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=V0*(1 + eps*math.cos(wp*t)))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq), (jac(x, qq) @ Phi).ravel()])
        s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                      method='DOP853', rtol=1e-10, atol=1e-12,
                      dense_output=True)
        return s, s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def orbit(x0, eps, itmax=40):
        x = x0.copy()
        for it in range(itmax):
            s, xT, M = strobe(x, eps)
            Fx = xT - x
            if np.max(np.abs(Fx)) < 1e-10:
                return s, x, M, True
            try:
                dx = np.linalg.solve(M - np.eye(4), -Fx)
            except np.linalg.LinAlgError:
                return None, x, None, False
            n = np.max(np.abs(dx))
            if n > 0.15: dx *= 0.15/n
            x = x + dx
        return None, x, None, False
    # continue both orbits in eps; report multipliers and landing
    xA, xS = st.copy(), ss.copy()
    epsg = ([0.2*meas, 0.5*meas, 0.8*meas, 0.95*meas, 1.0*meas,
             1.05*meas, 1.2*meas] if meas else [0.05, 0.15, 0.30, 0.45])
    prev = 0.0
    for eps in epsg:
        # step both orbits gradually to eps
        for e_sub in np.linspace(prev, eps, 6)[1:]:
            sA, xA, MA, okA = orbit(xA, e_sub)
            sS, xS, MS, okS = orbit(xS, e_sub)
        prev = eps
        if not okA or not okS:
            out(f"  eps={eps*100:.2f}%: orbit Newton failed "
                f"(A={okA}, S={okS})")
            continue
        muA = np.max(np.abs(np.linalg.eigvals(MA)))
        muS = np.sort(np.abs(np.linalg.eigvals(MS)))[::-1]
        # saddle orbit sampled over one period
        ttS = np.linspace(0, Td, 200)
        US = np.array([sS.sol(t)[:4] for t in ttS])
        dA = max(sA.sol(t)[0] for t in np.linspace(0, Td, 200))
        # trajectory from the unforced equilibrium: min distance to
        # the saddle orbit at matching phase (stroboscopic + dense)
        def f4(t, x):
            return rhs(x, dict(pr, V=V0*(1 + eps*math.cos(wp*t))))
        s4 = solve_ivp(f4, (0, 60.0), st.copy(), method='DOP853',
                       rtol=1e-9, atol=1e-12, dense_output=True)
        dmin = np.inf
        for t in np.linspace(0, min(s4.t[-1], 60.0), 4000):
            ph = (t % Td)
            j = int(round(ph/Td*199)) % 200
            d = np.linalg.norm(s4.sol(t) - US[j])
            if d < dmin: dmin = d
        out(f"  eps={eps*100:.2f}%: |mu|max(attractor)={muA:.4f} "
            f"saddle mult=({muS[0]:.3g},{muS[1]:.3g})  "
            f"max_delta(attr)={dA:.4f}  min dist(traj, saddle orbit)"
            f"={dmin:.3e} [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
