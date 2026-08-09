"""GFM direct V-forcing: is the '40% immunity' a device property or an
M1@0.10 artefact?  Original claim tested ONE set (quickgaps.py:103).
Per set and per drive frequency (w0 and 0.9 w0), bisect the source-
voltage oscillation fraction for THREE separate events, kept apart
(third detector lesson: solver failure != instability):
  (a) DESYNC : delta crosses the saddle angle
  (b) E<=0   : internal EMF touches zero  -> MODEL VALIDITY boundary
  (c) SOLVER : integrator death with neither of the above
Report which boundary comes first, and the E excursion at it.
Sets span mq: M2(.05) M1(.1) M4(.1) M5(.1) M3(.2).
Budget ~15 min, progress lines.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event, Enom)
from scipy.integrate import solve_ivp
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/vgfmwide.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

SETS = [('M2', 0.03), ('M1', 0.10), ('M4', 0.10), ('M5', 0.15),
        ('M3', 0.05)]

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

for name, Xg in SETS:
    pr = build(name, Xg)
    if pr is None:
        out(f"{name}@{Xg}: no Hopf window"); continue
    st = equil(pr)
    lam = crit_mode(jac(st, pr))
    w0 = lam.imag
    ev, dsad = escape_event(pr)
    mq = pr['mq']; V0 = pr['V']
    E0 = Enom - mq*(st[3] - pr['Qref'])
    out(f"{name}@{Xg}: mq={mq} P0={pr['Pref']:.4f} w0={w0:.3f} "
        f"E0={E0:.4f} d0={st[0]:.4f} dsad={dsad:.4f}")
    for rr, tagf in ((1.0, 'res'), (0.9, 'r=0.9')):
        wp = rr*w0
        def probe(frac, T=60.0):
            """return (event, minE, maxdelta)"""
            def f(t, x):
                return rhs(x, dict(pr, V=V0*(1 + frac*math.cos(wp*t))))
            def e_d(t, x): return x[0] - dsad
            def e_E(t, x):
                return (Enom - mq*(x[3] - pr['Qref'])) - 1e-3
            e_d.terminal = True; e_d.direction = 1
            e_E.terminal = True; e_E.direction = -1
            s = solve_ivp(f, (0, T), st.copy(), method='DOP853',
                          rtol=1e-9, atol=1e-12, events=(e_d, e_E),
                          dense_output=True)
            got_d = len(s.t_events[0]) > 0
            got_E = len(s.t_events[1]) > 0
            if got_d and got_E:
                first = 'DESYNC' if s.t_events[0][0] < s.t_events[1][0] \
                    else 'E<=0'
            elif got_d:
                first = 'DESYNC'
            elif got_E:
                first = 'E<=0'
            elif s.status < 0:
                first = 'SOLVER'
            else:
                first = None
            tt2 = np.linspace(0.5*s.t[-1], s.t[-1], 2000)
            X = s.sol(tt2)
            Emin = float(np.min(Enom - mq*(X[3] - pr['Qref'])))
            dmax = float(np.max(np.abs(X[0] - st[0])))
            return first, Emin, dmax
        # bracket
        flo, fhi = 0.02, 0.04
        n = 0
        while probe(fhi)[0] is None and fhi < 0.45 and n < 12:
            flo = fhi; fhi *= 1.5; n += 1
        r_hi = probe(min(fhi, 0.45))
        if r_hi[0] is None:
            out(f"  {tagf}: no event up to 45% V "
                f"(minE={r_hi[1]:.3f}, max|dd|={r_hi[2]:.3f}) "
                f"— immunity holds [{time.time()-T0:.0f}s]")
            continue
        fhi = min(fhi, 0.45)
        for _ in range(11):
            fm = 0.5*(flo+fhi)
            if probe(fm)[0] is not None: fhi = fm
            else: flo = fm
        fc = 0.5*(flo+fhi)
        kind, Emin, dmax = probe(fhi)
        _, Emin_lo, dmax_lo = probe(flo)
        out(f"  {tagf}: first boundary at V swing {fc*100:.2f}% "
            f"type={kind}  at edge: minE={Emin:.4f} "
            f"max|dd|={dmax:.4f} rad; just below: minE={Emin_lo:.4f} "
            f"max|dd|={dmax_lo:.4f} [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
