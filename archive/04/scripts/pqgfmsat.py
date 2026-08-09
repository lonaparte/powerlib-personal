"""GFM direct resonant forcing saturation test, P and Q channels
(analog of the 40%-V test). Sets M3@0.05, M5@0.15.
Forcing u(t) = u0 + a cos(w0 t), amplitude ladder; record max|omega|
over the post-settle window, saturation ratio vs linear extrapolation,
and events (delta over saddle / omega blow). If desync occurs, coarse
bisect the onset. Budget ~12 min.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event)
from scipy.integrate import solve_ivp
from scipy.linalg import eig as _eig
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/pqgfmsat.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

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
    prm = dict(pr, Pref=0.5*(lo2+hi2))
    return prm, P_H

for name, Xg in (('M3', 0.05), ('M5', 0.15)):
    r = build(name, Xg)
    if r is None:
        out(f"{name}@{Xg}: no window"); continue
    pr, P_H = r
    st = equil(pr)
    lam = crit_mode(jac(st, pr))
    w0 = lam.imag; alpha = -lam.real
    ev, dsad = escape_event(pr)
    dP = pr['Pref'] - P_H
    ev2, VL, VR = _eig(jac(st, pr), left=True, right=True)
    k = int(np.argmin(np.abs(ev2 - lam)))
    pv = VL[:, k]/np.vdot(VR[:, k], VL[:, k])
    out(f"{name}@{Xg}: P0={pr['Pref']:.4f} P_H={P_H:.4f} dP={dP:.4f} "
        f"w0={w0:.3f} alpha={alpha:.4f} dsad={dsad:.3f}")
    for key, amps, unit in (
            ('Pref', [0.1, 0.3, 1.0, 3.0, 10.0], 'xdP'),
            ('Qref', [0.05, 0.15, 0.5, 1.0, 2.0], 'pu')):
        u0 = pr[key]
        h = 1e-6
        fu = (rhs(st, dict(pr, **{key: u0+h}))
              - rhs(st, dict(pr, **{key: u0-h})))/(2*h)
        # linear resonant response slope of omega per unit amplitude
        Rlin = np.linalg.solve(1j*w0*np.eye(4) - jac(st, pr), fu)
        slope = abs(Rlin[1])
        base = None
        for am in amps:
            a = am*dP if unit == 'xdP' else am
            Tset, Tm = 40.0, 30.0
            def f(t, x):
                return rhs(x, dict(pr, **{key: u0 + a*math.cos(w0*t)}))
            def blow(t, x): return abs(x[1]) - 80.0
            blow.terminal = True; blow.direction = 1
            ev.terminal = True
            s = solve_ivp(f, (0, Tset+Tm), st.copy(), method='DOP853',
                          rtol=1e-9, atol=1e-12, events=(ev, blow),
                          dense_output=True)
            esc = any(len(t) > 0 for t in s.t_events) or s.status < 0
            if esc:
                te = min((t[0] for t in s.t_events if len(t)),
                         default=s.t[-1])
                out(f"  {key} a={a:.4f} ({am}{unit}): DESYNC/escape "
                    f"at t={te:.2f}s [{time.time()-T0:.0f}s]")
                continue
            tt2 = np.linspace(Tset, Tset+Tm, 4000)
            om = s.sol(tt2)[1]
            mo = float(np.max(np.abs(om)))
            lin = slope*a
            if base is None:
                base = mo/a
            out(f"  {key} a={a:.4f} ({am}{unit}): max|om|={mo:.4f} "
                f"lin_pred={lin:.4f} sat_ratio={mo/lin:.3f} "
                f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
