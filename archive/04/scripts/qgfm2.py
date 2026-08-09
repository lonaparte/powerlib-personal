"""GFM Qref-tongue near-cancellation cells (M2@0.03 -6%, M5@0.15 -82%).
Attempt: O(eps^2) diagonal correction (dgfm2 machinery, u=Qref,
a=eps/2) with fixed-point iteration; report whether the diagonal
terms close the gap or the expansion leaves its validity domain
(a ~ O(1)). Also report the two pi-components' phase alignment
(self-shielding of the droop loop). Budget ~3 min.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, Bform, Cform)
from scipy.linalg import eig as _eig
LOG = open('sweep20/qgfm2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

CASES = [dict(tag='M3 Xg=0.05', name='M3', Xg=0.05, meas=1.7905e-1),
         dict(tag='M2 Xg=0.03', name='M2', Xg=0.03, meas=2.2886e0),
         dict(tag='M5 Xg=0.15', name='M5', Xg=0.15, meas=1.0066e1)]

def build(case):
    pr = mset(case['name'], Xg=case['Xg'])
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
    st = equil(prm)
    A = jac(st, prm)
    lam = crit_mode(A)
    ev, VL, VR = _eig(A, left=True, right=True)
    k = int(np.argmin(np.abs(ev - lam)))
    qv = VR[:, k]; pv = VL[:, k]
    pv = pv/np.vdot(qv, pv)
    return prm, st, A, lam, qv, pv

for case in CASES:
    r = build(case)
    if r is None:
        out(f"{case['tag']}: no window"); continue
    pr, st, A, lam, qv, pv = r
    alpha = -lam.real; w0 = lam.imag
    wp = 2*w0
    u0 = pr['Qref']
    h = 1e-6
    key = 'Qref'
    fU = (rhs(st, dict(pr, **{key: u0+h}))
          - rhs(st, dict(pr, **{key: u0-h})))/(2*h)
    fUU = (rhs(st, dict(pr, **{key: u0+h})) - 2*rhs(st, pr)
           + rhs(st, dict(pr, **{key: u0-h})))/h**2
    M1 = (jac(st, dict(pr, **{key: u0+h}))
          - jac(st, dict(pr, **{key: u0-h})))/(2*h)
    M2m = (jac(st, dict(pr, **{key: u0+h})) - 2*jac(st, pr)
           + jac(st, dict(pr, **{key: u0-h})))/h**2
    hF = np.linalg.solve(1j*wp*np.eye(4) - A, fU)
    t1 = np.vdot(pv, M1 @ np.conj(qv))
    t2 = np.vdot(pv, Bform(st, pr, hF, np.conj(qv)))
    pi0 = t1 + t2
    cosang = (t1*np.conj(t2)).real/(abs(t1)*abs(t2))
    out(f"{case['tag']}: t1={t1:.4f} t2={t2:.4f} |pi|={abs(pi0):.4f} "
        f"cos(t1,t2)={cosang:+.3f}")
    def N1(u, v):
        return (Bform(st, dict(pr, **{key: u0+h}), u, v)
                - Bform(st, dict(pr, **{key: u0-h}), u, v))/(2*h)
    hb = np.conj(hF)
    Reh = np.real(hF)
    qb = np.conj(qv); pb = np.conj(pv)
    Mdefl = (np.conj(lam)*np.eye(4) - A) + np.outer(qb, np.conj(pb))
    Rplus = np.linalg.inv((lam + 1j*wp)*np.eye(4) - A)
    def Rtilde(v):
        vperp = v - qb*np.vdot(pb, v)
        y = np.linalg.solve(Mdefl, vperp)
        return y - qb*np.vdot(pb, y)
    def alpha_eff(eps):
        a = eps/2.0
        src = (Bform(st, pr, hF, hb).real + fUU + 2*(M1 @ Reh))
        xDC = -a*a*np.linalg.solve(A, src)
        dl_DC = (np.vdot(pv, Bform(st, pr, xDC, qv))
                 + a*a*np.vdot(pv, Cform(st, pr, hF, hb, qv))
                 + 2*a*a*np.vdot(pv, N1(Reh, qv))
                 + a*a*np.vdot(pv, M2m @ qv))
        Pip = lambda v: a*(Bform(st, pr, hF, v) + M1 @ v)
        Pim = lambda v: a*(Bform(st, pr, hb, v) + M1 @ v)
        dl_lad = (np.vdot(pv, Pim(Rplus @ Pip(qv)))
                  + np.vdot(pv, Pip(Rtilde(Pim(qv)))))
        return alpha - (dl_DC + dl_lad).real, dl_DC, dl_lad
    eps0 = 2*alpha/abs(pi0)
    eps = eps0
    okiter = True
    for it in range(12):
        ae, dDC, dlad = alpha_eff(eps)
        if ae <= 0 or not np.isfinite(ae):
            okiter = False; break
        eps_new = 2*ae/abs(pi0)
        if abs(eps_new - eps) < 1e-10:
            eps = eps_new; break
        eps = 0.5*eps + 0.5*eps_new
    meas = case['meas']
    if okiter:
        out(f"  eps0={eps0:.4e} ({(eps0-meas)/meas*100:+.1f}%)  "
            f"eps2={eps:.4e} ({(eps-meas)/meas*100:+.1f}%)  "
            f"a=eps/2={eps/2:.2f}  dDC={dDC:.4f} dlad={dlad:.4f}")
    else:
        out(f"  eps0={eps0:.4e} ({(eps0-meas)/meas*100:+.1f}%)  "
            f"O(eps^2) iteration left validity domain "
            f"(alpha_eff<=0 at a~{eps/2:.2f})")
out(f"DONE wall={time.time()-T0:.0f}s")
