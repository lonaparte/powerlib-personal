"""E-GFM: forced-path BVP predictor applied to ALL measured erosion
configurations (replaces the first-order energy-superposition formula).
Sets/measured values from emtheory.log and e5-gfm.log. Target <=1-2%.
Budget ~20 min (6 sets x up to 4 configs x 4 phases).
"""
import math, numpy as np, time, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event, Enom)
from scipy.integrate import solve_ivp
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/egfmall.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

MEAS = {
 ('M1', 0.10, 0.005, 'res'): [34.562, 35.312, 30.781, 30.219],
 ('M1', 0.10, 0.010, 'res'): [34.312, 36.438, 30.844, 29.219],
 ('M1', 0.10, 0.020, 'res'): [34.438, 37.562, 30.406, 28.031],
 ('M1', 0.10, 0.010, 'off'): [32.562, 32.812, 33.062, 32.938],
 ('M2', 0.05, 0.010, 'res'): [12.172, 10.109, 7.164, 8.922],
 ('M2', 0.05, 0.010, 'off'): [9.984, 9.547, 9.672, 10.109],
 ('M3', 0.05, 0.010, 'res'): [37.188, 31.531, 18.844, 23.906],
 ('M1', 0.05, 0.010, 'res'): [14.703, 16.406, 8.828, 8.984],
 ('M5', 0.10, 0.010, 'res'): [6.945, 4.914, 2.348, 3.668],
 ('M2', 0.03, 0.010, 'res'): [3.770, 5.336, 8.359, 6.383],
}

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

cache = {}
worst = 0.0
nover1 = 0
ntot = 0
for (name, Xg, eps, tagf), meas in MEAS.items():
    key = (name, Xg)
    if key not in cache:
        prm = build(name, Xg)
        st = equil(prm)
        lam = crit_mode(jac(st, prm))
        ev, dsad = escape_event(prm)
        cache[key] = (prm, st, lam.imag, dsad)
    prm, st, w0, dsad = cache[key]
    M, D, wc, mq, V0, Xgv = (prm['M'], prm['D'], prm['wc'], prm['mq'],
                             prm['V'], prm['Xg'])
    wp = w0 if tagf == 'res' else 0.7*w0
    def Pe_of(d, E, V): return E*V*math.sin(d)/Xgv
    def Qe_of(d, E, V): return (E*E - E*V*math.cos(d))/Xgv
    def bvp_dw(x0, tk):
        d0, om0, Pf0, Qf0 = x0
        N = 2500
        dg = np.linspace(d0, dsad, N)
        dd = dg[1] - dg[0]
        def endE(dw):
            v = np.full(N, max(om0 + dw, 1e-3))
            for it in range(20):
                Pf = np.empty(N); Qf = np.empty(N); tt2 = np.empty(N)
                Pf[0] = Pf0; Qf[0] = Qf0; tt2[0] = tk
                for n in range(1, N):
                    vn = max(v[n-1], 0.05*(om0+dw))
                    tt2[n] = tt2[n-1] + dd/vn
                    Vt = V0*(1 + eps*math.cos(wp*tt2[n]))
                    E = Enom - mq*(Qf[n-1] - prm['Qref'])
                    ex = math.exp(-wc*dd/vn)
                    Pe = Pe_of(dg[n], E, Vt)
                    Qe = Qe_of(dg[n], E, Vt)
                    Pf[n] = Pe + (Pf[n-1] - Pe)*ex
                    Qf[n] = Qe + (Qf[n-1] - Qe)*ex
                E2 = np.empty(N)
                E2[0] = 0.5*M*(om0+dw)**2
                for n in range(1, N):
                    E2[n] = E2[n-1] + (prm['Pref'] - Pf[n]
                                       - D*max(v[n-1], 0.05*(om0+dw)))*dd
                v = 0.5*v + 0.5*np.sqrt(np.maximum(
                    2*np.maximum(E2, 0)/M, (0.05*(om0+dw))**2))
            return E2[-1]
        lo3, hi3 = 0.3, 60.0
        for _ in range(34):
            mid = 0.5*(lo3+hi3)
            if endE(mid) > 0: hi3 = mid
            else: lo3 = mid
        return 0.5*(lo3+hi3)
    Tset = 60.0
    Tdp = 2*math.pi/wp
    def f(t, xx):
        qq = dict(prm, V=V0*(1 + eps*math.cos(wp*t)))
        return rhs(xx, qq)
    s = solve_ivp(f, (0, Tset+Tdp), st.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, dense_output=True)
    errs = []
    for j in range(4):
        tk = Tset + j*Tdp/4
        xb = s.sol(tk)
        pred = bvp_dw(xb, tk)
        e = (pred - meas[j])/meas[j]*100
        errs.append(e)
        ntot += 1
        if abs(e) > 1.0:
            nover1 += 1
        worst = max(worst, abs(e))
    out(f"{name}@{Xg} eps={eps} {tagf}: errs = "
        + " ".join(f"{e:+.1f}%" for e in errs)
        + f" [{time.time()-T0:.0f}s]")
out(f"SUMMARY: {ntot} points, worst {worst:.1f}%, >1%: {nover1}")
out(f"DONE wall={time.time()-T0:.0f}s")
