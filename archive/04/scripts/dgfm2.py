"""D-GFM O(eps^2) correction of the 2:1 parametric tongue for the
two large-eps_t sets (M2@Xg=0.03 -1.56%, M5@Xg=0.15 -1.28%);
M3@Xg=0.05 as regression control.
Second-order two-level reduction, all O(eps^2) diagonal terms with
a = eps*V0/2, h = h_F = (i wp I - A)^{-1} f_V:
  DC orbit shift : x_DC = -a^2 A^{-1}[B(h,hb) + f_VV + 2 M1 Re h]
  DC Jacobian    : dlam_DC = <p, B(x_DC,q) + a^2 C(h,hb,q)
                              + 2 a^2 N1(Re h, q) + a^2 M2 q>
  ladder (k=+-1) : Pi+ = a[B(h,.)+M1], Pi- = a[B(hb,.)+M1]
    dlam_lad = <p, Pi- R(lam+i wp) Pi+ q> + <p, Pi+ Rt(lam-i wp) Pi- q>
    with lam - i wp = lamb exactly -> Rt = resolvent deflated at qb
    (the resonant qb channel is the PD coupling handled by pi_eff).
Threshold: eps solves eps = 2*alpha_eff(eps)/|pi_eff|/V0 (fixed point).
Measurements reused from sweep20/d5-gfm.log. Budget ~2 min.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, Bform, Cform)
from scipy.linalg import eig as _eig
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/dgfm2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

CASES = [
    dict(tag='M3 Xg=0.05', name='M3', Xg=0.05, meas=1.0019e-2),
    dict(tag='M2 Xg=0.03', name='M2', Xg=0.03, meas=4.1171e-2),
    dict(tag='M5 Xg=0.15', name='M5', Xg=0.15, meas=3.5836e-2),
]

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
    V0 = pr['V']
    wp = 2*w0
    h = 1e-6
    fV = (rhs(st, dict(pr, V=V0+h)) - rhs(st, dict(pr, V=V0-h)))/(2*h)
    fVV = (rhs(st, dict(pr, V=V0+h)) - 2*rhs(st, pr)
           + rhs(st, dict(pr, V=V0-h)))/h**2
    M1 = (jac(st, dict(pr, V=V0+h)) - jac(st, dict(pr, V=V0-h)))/(2*h)
    M2 = (jac(st, dict(pr, V=V0+h)) - 2*jac(st, pr)
          + jac(st, dict(pr, V=V0-h)))/h**2
    hF = np.linalg.solve(1j*wp*np.eye(4) - A, fV)
    pi_eff = (np.vdot(pv, M1 @ np.conj(qv))
              + np.vdot(pv, Bform(st, pr, hF, np.conj(qv))))
    def N1(u, v):
        return (Bform(st, dict(pr, V=V0+h), u, v)
                - Bform(st, dict(pr, V=V0-h), u, v))/(2*h)
    hb = np.conj(hF)
    Reh = np.real(hF)
    # deflated resolvent at lam - i wp = conj(lam): remove qb channel
    qb = np.conj(qv); pb = np.conj(pv)
    Mdefl = (np.conj(lam)*np.eye(4) - A) + np.outer(qb, np.conj(pb))
    Rplus = np.linalg.inv((lam + 1j*wp)*np.eye(4) - A)
    def Rtilde(v):
        vperp = v - qb*np.vdot(pb, v)
        y = np.linalg.solve(Mdefl, vperp)
        return y - qb*np.vdot(pb, y)
    def alpha_eff(eps):
        a = eps*V0/2
        src = (Bform(st, pr, hF, hb).real + fVV + 2*(M1 @ Reh))
        xDC = -a*a*np.linalg.solve(A, src)
        dl_DC = (np.vdot(pv, Bform(st, pr, xDC, qv))
                 + a*a*np.vdot(pv, Cform(st, pr, hF, hb, qv))
                 + 2*a*a*np.vdot(pv, N1(Reh, qv))
                 + a*a*np.vdot(pv, M2 @ qv))
        Pip = lambda v: a*(Bform(st, pr, hF, v) + M1 @ v)
        Pim = lambda v: a*(Bform(st, pr, hb, v) + M1 @ v)
        dl_lad = (np.vdot(pv, Pim(Rplus @ Pip(qv)))
                  + np.vdot(pv, Pip(Rtilde(Pim(qv)))))
        return alpha - (dl_DC + dl_lad).real, dl_DC, dl_lad
    eps0 = 2*alpha/abs(pi_eff)/V0
    eps = eps0
    for it in range(8):
        ae, dDC, dlad = alpha_eff(eps)
        eps_new = 2*ae/abs(pi_eff)/V0
        if abs(eps_new - eps) < 1e-12:
            eps = eps_new; break
        eps = eps_new
    meas = case['meas']
    out(f"{case['tag']}: alpha={alpha:.4f} w0={w0:.3f} "
        f"eps0={eps0:.4e} ({(eps0-meas)/meas*100:+.2f}%)")
    out(f"  dlam_DC={dDC:.5f} dlam_lad={dlad:.5f} "
        f"alpha_eff={alpha - (dDC+dlad).real:.5f}")
    out(f"  RESULT eps2={eps:.4e} meas={meas:.4e} "
        f"err={(eps-meas)/meas*100:+.2f}%  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
