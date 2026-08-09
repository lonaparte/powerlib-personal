"""GFM direct-forcing desync: mechanism = forced periodic orbit's angle
excursion reaches the saddle angle.  Criterion:
      max_t delta_orbit(t; eps) = delta_sad
computed on the EXACT forced periodic orbit (Newton on the stroboscopic
map, continued in eps), compared with the measured desync threshold.
Also compares the leading-order amplitude-equation prediction
      2|q_delta| a(eps) = delta_sad - delta_0,
      a: a^2[(alpha-Re l1 a^2)^2+(det+Im l1 a^2)^2] = eps^2|<p,f_u>/2|^2
to show where the local normal form stops being adequate (large swing).
Cells: V channel on M2@0.03, M5@0.15 (measured 5.26%, 4.88% at
resonance); M1@0.10 as the negative control (no desync to 45%).
Budget ~12 min.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event, hopf_c1, Enom)
from scipy.integrate import solve_ivp
from scipy.linalg import eig as _eig
LOG = open('sweep20/gfmdirect.log', 'w')
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
    A = jac(st, pr)
    lam = crit_mode(A)
    w0 = lam.imag; alpha = -lam.real
    ev, dsad = escape_event(pr)
    V0 = pr['V']
    margin = dsad - st[0]
    wp = w0
    Td = 2*math.pi/wp
    ev2, VL, VR = _eig(A, left=True, right=True)
    k = int(np.argmin(np.abs(ev2 - lam)))
    qv = VR[:, k]; pv = VL[:, k]
    pv = pv/np.vdot(qv, pv)
    h = 1e-6
    fV = (rhs(st, dict(pr, V=V0+h)) - rhs(st, dict(pr, V=V0-h)))/(2*h)
    F1 = abs(np.vdot(pv, fV))/2.0
    try:
        cc = hopf_c1(pr)
        l1 = cc['c1']
    except Exception:
        l1 = None
    out(f"{name}@{Xg}: d0={st[0]:.4f} dsad={dsad:.4f} margin={margin:.4f} "
        f"w0={w0:.3f} alpha={alpha:.4f} |q_d|={abs(qv[0]):.4f} "
        f"F1={F1:.4f} l1={l1}")
    # ---- exact forced periodic orbit, continued in eps ----
    def strobe(x0, eps, want_traj=False):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=V0*(1 + eps*math.cos(wp*t)))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq), (jac(x, qq) @ Phi).ravel()])
        s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                      method='DOP853', rtol=1e-10, atol=1e-12,
                      dense_output=want_traj)
        return s, s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def orbit(eps, xg):
        x = xg.copy()
        for it in range(40):
            s, xT, M = strobe(x, eps, want_traj=True)
            Fx = xT - x
            if np.max(np.abs(Fx)) < 1e-10:
                tt2 = np.linspace(0, Td, 1200)
                dd = np.array([s.sol(t)[0] for t in tt2])
                return x, float(dd.max()), True
            try:
                dx = np.linalg.solve(M - np.eye(4), -Fx)
            except np.linalg.LinAlgError:
                return x, None, False
            n = np.max(np.abs(dx))
            if n > 0.2: dx *= 0.2/n
            x = x + dx
        return x, None, False
    xg = st.copy()
    eps = 0.0
    step = 0.002
    last_ok = (0.0, st[0])
    pred = None
    while eps < 0.50:
        e_try = eps + step
        xn, dmax, ok = orbit(e_try, xg)
        if not ok:
            step *= 0.5
            if step < 1e-5:
                out(f"  orbit continuation stall at eps={eps:.4f} "
                    f"(dmax={last_ok[1]:.4f}, margin end {dsad:.4f})")
                break
            continue
        if dmax >= dsad:
            lo3, hi3 = eps, e_try
            for _ in range(14):
                em = 0.5*(lo3+hi3)
                xm, dm, okm = orbit(em, xg)
                if not okm:
                    hi3 = em; continue
                if dm >= dsad: hi3 = em
                else: lo3 = em; xg = xm
            pred = 0.5*(lo3+hi3)
            break
        eps, xg = e_try, xn
        last_ok = (eps, dmax)
        step = min(step*1.3, 0.01)
    if pred is not None:
        msg = (f"  ORBIT-TOUCHES-SADDLE at V swing {pred*100:.2f}%")
        if meas:
            msg += f"  meas={meas*100:.2f}%  err={(pred-meas)/meas*100:+.2f}%"
        out(msg + f" [{time.time()-T0:.0f}s]")
    else:
        out(f"  no saddle touch up to eps={eps:.3f} "
            f"(max delta on orbit {last_ok[1]:.4f} vs dsad {dsad:.4f}) "
            f"[{time.time()-T0:.0f}s]")
    # ---- leading-order amplitude-equation estimate ----
    if l1 is not None and abs(qv[0]) > 0:
        areq = margin/(2*abs(qv[0]))
        rhs_e = (areq**2)*((alpha - l1.real*areq**2)**2
                           + (l1.imag*areq**2)**2)
        eps_lo = math.sqrt(max(rhs_e, 0.0))/max(F1, 1e-12)/V0
        out(f"  leading-order estimate (2|q_d|a = margin): "
            f"a_req={areq:.4f}  eps={eps_lo*100:.2f}%"
            + (f"  err={(eps_lo-meas)/meas*100:+.1f}%" if meas else ""))
out(f"DONE wall={time.time()-T0:.0f}s")
