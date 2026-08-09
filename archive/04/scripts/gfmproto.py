"""What does the GFM 'desync threshold' number mean?  Two protocols:
 A (switch-on / event): start at the UNFORCED equilibrium with
   V(t)=V0(1+eps cos(wp t + phi)).  At phi=0 this carries a step of
   eps*V0 at t=0, so the number mixes step transient with resonant
   build-up -> scan phi = 0, pi/2, pi, 3pi/2 to expose the dependence.
 B (pre-existing ambient oscillation): start ON the forced periodic
   orbit (Newton), perturb by 1e-6, and ask whether the state stays.
   This is the threshold relevant to an oscillation that has been
   present all along.
Set M2@0.03 (protocol-A phi=0 threshold 5.2639%), M5@0.15 (4.8753%).
Budget ~12 min.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event)
from scipy.integrate import solve_ivp
LOG = open('sweep20/gfmproto.log', 'w')
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
    st = equil(pr)
    w0 = crit_mode(jac(st, pr)).imag
    ev, dsad = escape_event(pr)
    V0 = pr['V']; wp = w0; Td = 2*math.pi/wp
    out(f"{name}@{Xg}: d0={st[0]:.4f} dsad={dsad:.4f} w0={w0:.3f}")
    # ---- protocol A, switch-on phase scan ----
    def escA(eps, phi, T=60.0):
        def f(t, x):
            return rhs(x, dict(pr, V=V0*(1 + eps*math.cos(wp*t + phi))))
        def e_d(t, x): return x[0] - dsad
        e_d.terminal = True; e_d.direction = 1
        s = solve_ivp(f, (0, T), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13, events=e_d)
        return len(s.t_events[0]) > 0 or s.status < 0
    for phi, tag in ((0.0, 'phi=0 (step +eps)'),
                     (math.pi/2, 'phi=pi/2 (no step)'),
                     (math.pi, 'phi=pi (step -eps)'),
                     (3*math.pi/2, 'phi=3pi/2 (no step)')):
        lo, hi = 0.01, 0.10
        n = 0
        while not escA(hi, phi) and hi < 0.6 and n < 12:
            lo = hi; hi *= 1.3; n += 1
        if not escA(hi, phi):
            out(f"  A {tag}: no desync up to {hi*100:.1f}% "
                f"[{time.time()-T0:.0f}s]")
            continue
        while escA(lo, phi) and lo > 1e-3:
            lo *= 0.7
        for _ in range(14):
            m = 0.5*(lo+hi)
            if escA(m, phi): hi = m
            else: lo = m
        out(f"  A {tag}: threshold {0.5*(lo+hi)*100:.4f}% "
            f"[{time.time()-T0:.0f}s]")
    # ---- protocol B: start on the forced orbit ----
    def strobe(x0, eps):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=V0*(1 + eps*math.cos(wp*t)))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq), (jac(x, qq) @ Phi).ravel()])
        s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                      method='DOP853', rtol=1e-10, atol=1e-12)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def orbit(x0, eps, itmax=40):
        x = x0.copy()
        for it in range(itmax):
            xT, M = strobe(x, eps)
            Fx = xT - x
            if np.max(np.abs(Fx)) < 1e-11:
                return x, M, True
            try:
                dx = np.linalg.solve(M - np.eye(4), -Fx)
            except np.linalg.LinAlgError:
                return x, None, False
            n = np.max(np.abs(dx))
            if n > 0.1: dx *= 0.1/n
            x = x + dx
        return x, M, False
    xg = st.copy(); eps = 0.0; step = 0.004
    last = None
    while eps < 0.60:
        e_try = eps + step
        xn, M, ok = orbit(xg, e_try)
        if not ok:
            step *= 0.5
            if step < 2e-4:
                out(f"  B: orbit continuation stall at {eps*100:.2f}% "
                    f"[{time.time()-T0:.0f}s]")
                break
            continue
        mu = float(np.max(np.abs(np.linalg.eigvals(M))))
        # does a perturbed start on the orbit stay bounded?
        def f(t, x):
            return rhs(x, dict(pr, V=V0*(1 + e_try*math.cos(wp*t))))
        def e_d(t, x): return x[0] - dsad
        e_d.terminal = True; e_d.direction = 1
        s = solve_ivp(f, (0, 60.0), xn + 1e-6, method='DOP853',
                      rtol=1e-10, atol=1e-13, events=e_d)
        esc = len(s.t_events[0]) > 0 or s.status < 0
        eps, xg = e_try, xn
        last = (eps, mu, esc)
        if esc:
            out(f"  B: ambient-start escape first at {eps*100:.2f}% "
                f"(|mu|max={mu:.4f}) [{time.time()-T0:.0f}s]")
            break
        step = min(step*1.25, 0.02)
    if last and not last[2]:
        out(f"  B: no ambient-start escape up to {last[0]*100:.2f}% "
            f"(|mu|max={last[1]:.4f}) [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
