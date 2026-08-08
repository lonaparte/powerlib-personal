"""Derive the GFM velocity-kick escape threshold from the energy BVP
(1/2 M dw^2 = DeltaU + W) with dynamic Pf/Qf profiles along the escape
path (semi-implicit exponential filter integration in delta), replacing
the measured anchors for all six windowed sets. Budget ~3 min.
"""
import math, numpy as np, time, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, P_of, E_of, escape_event, Enom)
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/gfmbvp.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

MEAS = {('M1', 0.10): 32.8125, ('M2', 0.05): 9.8281, ('M3', 0.05): 28.9688,
        ('M1', 0.05): 12.7969, ('M5', 0.10): 4.9922, ('M2', 0.03): 6.3203}

def build(name, Xg):
    pr = mset(name, Xg=Xg)
    dfold, Pm = fold(pr)
    q = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
    if q is None:
        return None
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

for (name, Xg), dwm in MEAS.items():
    pr = build(name, Xg)
    if pr is None:
        out(f"{name}@{Xg}: no window"); continue
    st = equil(pr)
    from gfmlib import escape_event as _ee
    ev, dsad = _ee(pr)
    M, D, wc, mq, V, Xgv = (pr['M'], pr['D'], pr['wc'], pr['mq'],
                            pr['V'], pr['Xg'])
    d0 = st[0]
    N = 4000
    dg = np.linspace(d0, dsad, N)
    dd = dg[1] - dg[0]
    def Qe_of(d, E):
        return (E*E - E*V*math.cos(d))/Xgv
    def Pe_of(d, E):
        return E*V*math.sin(d)/Xgv
    # profiles: v(delta), Pf(delta), Qf(delta); iterate to fixed point
    def profiles(dw, nit=25):
        v = np.full(N, max(dw, 1e-3))
        for it in range(nit):
            Pf = np.empty(N); Qf = np.empty(N)
            Pf[0] = pr['Pref']; Qf[0] = st[3]
            for n in range(1, N):
                vn = max(v[n-1], 0.05*dw)
                E = Enom - mq*(Qf[n-1] - pr['Qref'])
                Pe = Pe_of(dg[n], E)
                Qe = Qe_of(dg[n], E)
                ex = math.exp(-wc*dd/vn)
                Pf[n] = Pe + (Pf[n-1] - Pe)*ex
                Qf[n] = Qe + (Qf[n-1] - Qe)*ex
            # energy: d(1/2 M v^2)/dd = Pref - Pf - D v
            E2 = np.empty(N)
            E2[0] = 0.5*M*dw*dw
            for n in range(1, N):
                E2[n] = E2[n-1] + (pr['Pref'] - Pf[n] -
                                   D*max(v[n-1], 0.05*dw))*dd
            vn2 = np.sqrt(np.maximum(2*np.maximum(E2, 0)/M, (0.05*dw)**2))
            v = 0.5*v + 0.5*vn2
        return E2[-1]
    lo3, hi3 = 0.3*dwm, 2.5*dwm
    for _ in range(40):
        mid = 0.5*(lo3+hi3)
        if profiles(mid) > 0: hi3 = mid
        else: lo3 = mid
    dwp = 0.5*(lo3+hi3)
    out(f"{name}@Xg={Xg}: dw_pred={dwp:.4f} dw_meas={dwm:.4f} "
        f"err={(dwp-dwm)/dwm*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
