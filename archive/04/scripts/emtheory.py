"""GFM erosion law — mechanistic prediction and check.
Claim: the kick threshold from an oscillating background state is the
energy criterion evaluated at the pre-kick state (velocity superposition
+ potential offset), anchored by the unforced threshold:
  E_esc = (1/2) M dw0^2      (absorbs the filter-work term W)
  dwc_pred(state) = sqrt( max(0, 2(E_esc - U(delta_s))/M) ) - omega_s
with U(d) = int (P_of(x) - Pref) dx  (enslaved-E potential, U(d0)=0).
Zero fitting. Check per phase vs measured (M1 existing; M2@Xg=0.05 fresh).
"""
import math, numpy as np, time, os, sys
from scipy.integrate import solve_ivp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, P_of, escape_event)
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/emtheory.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

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
    prm = dict(pr, Pref=0.5*(lo2+hi2))
    st = equil(prm)
    lam = crit_mode(jac(st, prm))
    return dict(pr=prm, st=st, alpha=-lam.real, w0=lam.imag)

def run_case(tag, name, Xg, ebgs, meas=None):
    b = build(name, Xg)
    if b is None:
        out(f"{tag}: no window — skip")
        return
    pr, st, w0 = b['pr'], b['st'], b['w0']
    M = pr['M']
    ev, dsad = escape_event(pr)
    out(f"{tag}: P0={pr['Pref']:.4f} alpha={b['alpha']:.4f} w0={w0:.4f} "
        f"d0={st[0]:.4f} dsad={dsad:.4f}")
    # potential U(d) with U(d0)=0
    dg = np.linspace(st[0]-0.6, dsad+0.1, 3000)
    Pv = np.array([P_of(x, pr) - pr['Pref'] for x in dg])
    Ug = np.concatenate([[0], np.cumsum(0.5*(Pv[1:]+Pv[:-1])*np.diff(dg))])
    Ug -= np.interp(st[0], dg, Ug)
    def U(d): return float(np.interp(d, dg, Ug))
    # unforced threshold (measured) -> E_esc anchor
    def esc_from(x, tk, eps, wp, Tf=80.0):
        def f(t, xx):
            qq = dict(pr, V=pr['V']*(1 + eps*math.cos(wp*t)))
            return rhs(xx, qq)
        s = solve_ivp(f, (tk, tk+Tf), x, method='DOP853', rtol=1e-9,
                      atol=1e-12, events=ev)
        return len(s.t_events[0]) > 0
    def dwc_measure(xb, tk, eps, wp):
        lo2, hi2 = 0.0, 2.0
        while not esc_from(np.concatenate([xb[:1], [xb[1]+hi2], xb[2:]]),
                           tk, eps, wp) and hi2 < 80:
            hi2 *= 2
        for _ in range(9):
            dm = 0.5*(lo2+hi2)
            xk = xb.copy(); xk[1] += dm
            if esc_from(xk, tk, eps, wp): hi2 = dm
            else: lo2 = dm
        return 0.5*(lo2+hi2)
    dw0 = dwc_measure(st.copy(), 0.0, 0.0, w0)
    Eesc = 0.5*M*dw0*dw0
    out(f"  dw0(measured)={dw0:.4f}  E_esc={Eesc:.4f}")
    def pred_from_state(x):
        avail = 2*(Eesc - U(x[0]))/M
        return (math.sqrt(avail) if avail > 0 else 0.0) - x[1]
    for eps, wp, tagf in ebgs:
        Tset = 60.0
        Tdp = 2*math.pi/wp
        def f(t, xx):
            qq = dict(pr, V=pr['V']*(1 + eps*math.cos(wp*t)))
            return rhs(xx, qq)
        s = solve_ivp(f, (0, Tset+Tdp), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13, dense_output=True)
        rows = []
        for j in range(4):
            tk = Tset + j*Tdp/4
            xb = s.sol(tk)
            pred = pred_from_state(xb)
            msd = dwc_measure(xb.copy(), tk, eps, wp) if meas is None \
                else meas[(eps, tagf)][j]
            err = (pred - msd)/msd*100
            rows.append((pred, msd, err))
        out(f"  RESULT {tagf} eps={eps:.3f}: "
            + "  ".join(f"[ph{j}: pred={r[0]:.3f} meas={r[1]:.3f} "
                        f"err={r[2]:+.1f}%]" for j, r in enumerate(rows)))

MEAS_M1 = {(0.005, 'res'): [34.562, 35.312, 30.781, 30.219],
           (0.010, 'res'): [34.312, 36.438, 30.844, 29.219],
           (0.020, 'res'): [34.438, 37.562, 30.406, 28.031],
           (0.010, 'off'): [32.562, 32.812, 33.062, 32.938]}
b1 = build('M1', 0.10)
w01 = b1['w0']
run_case('M1@Xg=0.10', 'M1', 0.10,
         [(0.005, w01, 'res'), (0.010, w01, 'res'), (0.020, w01, 'res'),
          (0.010, 0.7*w01, 'off')],
         meas=MEAS_M1)
b2 = build('M2', 0.05)
if b2 is not None:
    run_case('M2@Xg=0.05', 'M2', 0.05,
             [(0.010, b2['w0'], 'res'), (0.010, 0.7*b2['w0'], 'off')],
             meas=None)
else:
    out("M2@Xg=0.05: no window — skip")
out(f"DONE wall={time.time()-T0:.0f}s")
