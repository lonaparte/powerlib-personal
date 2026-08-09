"""P-channel erosion (GFM M1@0.10): kick threshold dwc on a
Pref-oscillation background vs quiet background.
Background Pref(t) = P0 + aP cos(wp t), aP in {0.05, 0.15} pu,
wp in {w0 (res), 0.7 w0 (off)}; 4 kick phases.
Prediction: forced-path BVP with Pref(t) time-tracked in the energy
integral (egfmall machinery, V fixed). Budget ~15 min.
"""
import math, numpy as np, time, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, escape_event, Enom)
from scipy.integrate import solve_ivp
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/pqerosion.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

pr0 = mset('M1', Xg=0.10)
dfold, Pm = fold(pr0)
qh = hopf_in(pr0, 'Pref', 0.02*Pm, 0.95*Pm)
P_H = qh['Pref']
def g(P):
    r = maxre_cx(dict(pr0, Pref=P))
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
P0 = 0.5*(lo2+hi2)
pr = dict(pr0, Pref=P0)
st = equil(pr)
w0 = crit_mode(jac(st, pr)).imag
ev, dsad = escape_event(pr)
M, D, wc, mq, V0, Xg = (pr['M'], pr['D'], pr['wc'], pr['mq'],
                        pr['V'], pr['Xg'])
out(f"M1@0.10: P0={P0:.4f} P_H={P_H:.4f} w0={w0:.3f} dsad={dsad:.3f}")

def esc_from(x, tk, aP, wp, Tf=80.0):
    def f(t, xx):
        return rhs(xx, dict(pr, Pref=P0 + aP*math.cos(wp*t)))
    ev.terminal = True
    s = solve_ivp(f, (tk, tk+Tf), x, method='DOP853', rtol=1e-9,
                  atol=1e-12, events=ev)
    return len(s.t_events[0]) > 0

def dwc_measure(xb, tk, aP, wp):
    lo3, hi3 = 0.0, 2.0
    while not esc_from(np.concatenate([xb[:1], [xb[1]+hi3], xb[2:]]),
                       tk, aP, wp) and hi3 < 80:
        hi3 *= 2
    for _ in range(11):
        dm = 0.5*(lo3+hi3)
        xk = xb.copy(); xk[1] += dm
        if esc_from(xk, tk, aP, wp): hi3 = dm
        else: lo3 = dm
    return 0.5*(lo3+hi3)

def Pe_of(d, E, V): return E*V*math.sin(d)/Xg
def Qe_of(d, E, V): return (E*E - E*V*math.cos(d))/Xg

def bvp_dw(x0, tk, aP, wp):
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
                Prt = P0 + aP*math.cos(wp*tt2[n])
                E = Enom - mq*(Qf[n-1] - pr['Qref'])
                ex = math.exp(-wc*dd/vn)
                Pe = Pe_of(dg[n], E, V0)
                Qe = Qe_of(dg[n], E, V0)
                Pf[n] = Pe + (Pf[n-1] - Pe)*ex
                Qf[n] = Qe + (Qf[n-1] - Qe)*ex
            E2 = np.empty(N)
            E2[0] = 0.5*M*(om0+dw)**2
            for n in range(1, N):
                Prt = P0 + aP*math.cos(wp*tt2[n])
                E2[n] = E2[n-1] + (Prt - Pf[n]
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

dw0 = dwc_measure(st.copy(), 0.0, 0.0, w0)
out(f"quiet anchor dw0={dw0:.4f}")
for wp, tagf in ((w0, 'res'), (0.7*w0, 'off')):
    for aP in (0.05, 0.15):
        Tset = 60.0
        Tdp = 2*math.pi/wp
        def f(t, xx):
            return rhs(xx, dict(pr, Pref=P0 + aP*math.cos(wp*t)))
        s = solve_ivp(f, (0, Tset+Tdp), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13, dense_output=True)
        errs = []
        eros = []
        for j in range(4):
            tk = Tset + j*Tdp/4
            xb = s.sol(tk)
            meas = dwc_measure(xb.copy(), tk, aP, wp)
            pred = bvp_dw(xb, tk, aP, wp)
            errs.append((pred-meas)/meas*100)
            eros.append((dw0-meas)/dw0*100)
        out(f"  {tagf} aP={aP}: erosion%={['%.1f' % e for e in eros]} "
            f"BVP errs={['%+.1f' % e for e in errs]}% "
            f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
