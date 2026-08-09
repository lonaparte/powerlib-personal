"""GFM Qref tongue: mechanism-updated recomputation for the
near-cancellation cells (M2 -6%, M5 -80% at leading order).
Updated predictor: analytic forced orbit to O(eps^2)
  x_p(t) = st + (eps/2)(h e^{iwt}+cc) + x2DC + (x2p e^{2iwt}+cc)
  x2DC = -A^-1 (eps^2/4)[B(h,hb)+f_uu+2 M1 Re h]
  x2p  = (2iw I-A)^-1 (eps^2/8)[B(h,h)+f_uu+2 M1 h]
then EXACT Jacobian along it, monodromy of wdot=J(t)w, tongue edge =
max|multiplier| crossing 1 (bisect in eps). Includes pi0, all ladder
and pi3-type terms of the linearization to all orders; only the orbit
is truncated (stated order).
Diagnostics at measured edge: multiplier exit angle (PD = through -1)
and min_t E(t); if exit is not PD and min E ~ 0, the measured edge is
the internal-voltage collapse boundary -> predict via min_t E(eps)=0.
Sets: M3 (regression), M2, M5. Budget ~6 min.
"""
import sys, time, os, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, Bform, Enom)
from scipy.integrate import solve_ivp
from scipy.linalg import eig as _eig
LOG = open('sweep20/qgfm3.log', 'w')
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
    return prm, st

for case in CASES:
    r = build(case)
    if r is None:
        out(f"{case['tag']}: no window"); continue
    pr, st = r
    A = jac(st, pr)
    lam = crit_mode(A)
    w0 = lam.imag
    wp = 2*w0
    Td = 2*math.pi/wp
    u0 = pr['Qref']; key = 'Qref'
    hq = 1e-6
    fU = (rhs(st, dict(pr, **{key: u0+hq}))
          - rhs(st, dict(pr, **{key: u0-hq})))/(2*hq)
    fUU = (rhs(st, dict(pr, **{key: u0+hq})) - 2*rhs(st, pr)
           + rhs(st, dict(pr, **{key: u0-hq})))/hq**2
    M1 = (jac(st, dict(pr, **{key: u0+hq}))
          - jac(st, dict(pr, **{key: u0-hq})))/(2*hq)
    h = np.linalg.solve(1j*wp*np.eye(4) - A, fU)
    # per-eps^2 coefficients of the second-order orbit
    x2DC_e2 = -np.linalg.solve(
        A, (Bform(st, pr, h, np.conj(h)).real + fUU
            + 2*(M1 @ np.real(h))))/4.0
    x2p_e2 = np.linalg.solve(
        2j*wp*np.eye(4) - A,
        (Bform(st, pr, h, h) + fUU + 2*(M1 @ h)))/8.0
    mq = pr['mq']
    def orbit(t, eps):
        e1 = np.exp(1j*wp*t)
        return (st + eps*np.real(h*e1)
                + eps*eps*x2DC_e2
                + eps*eps*2*np.real(x2p_e2*e1*e1))
    def monodromy(eps):
        def f(t, y):
            Phi = y.reshape(4, 4)
            qq = dict(pr, **{key: u0 + eps*math.cos(wp*t)})
            J = jac(orbit(t, eps), qq)
            return (J @ Phi).ravel()
        s = solve_ivp(f, (0, Td), np.eye(4).ravel(), method='DOP853',
                      rtol=1e-11, atol=1e-13)
        return s.y[:, -1].reshape(4, 4)
    def maxmul(eps):
        return np.linalg.eigvals(monodromy(eps))
    def stab(eps):
        return float(np.max(np.abs(maxmul(eps)))) < 1.0
    meas = case['meas']
    # bisect tongue edge with the updated predictor
    elo, ehi = 0.5*meas, 1.3*meas
    n = 0
    while not stab(elo) and n < 8:
        elo *= 0.7; n += 1
    n = 0
    while stab(ehi) and n < 8:
        ehi *= 1.3; n += 1
    if not stab(elo) or stab(ehi):
        out(f"{case['tag']}: bracket failed "
            f"(stab({elo:.3g})={stab(elo)}, stab({ehi:.3g})={stab(ehi)})")
    else:
        for _ in range(13):
            em = 0.5*(elo+ehi)
            if stab(em): elo = em
            else: ehi = em
        pred = 0.5*(elo+ehi)
        # exit-type diagnostic at the predicted edge
        mus = maxmul(ehi)
        k = int(np.argmax(np.abs(mus)))
        ang = math.degrees(math.atan2(mus[k].imag, mus[k].real))
        # min E on the analytic orbit at the edge
        tt2 = np.linspace(0, Td, 400)
        Emin = min(Enom - mq*(orbit(t, pred)[3]
                              - (u0 + pred*math.cos(wp*t)))
                   for t in tt2)
        out(f"{case['tag']}: pred(updated)={pred:.4e} meas={meas:.4e} "
            f"err={(pred-meas)/meas*100:+.2f}%  exit_mult_angle={ang:.1f}deg "
            f"minE@edge={Emin:.3f} [{time.time()-T0:.0f}s]")
    # E-collapse ceiling: min_t E(t;eps)=0 on the analytic orbit
    def minE(eps):
        tt2 = np.linspace(0, Td, 400)
        return min(Enom - mq*(orbit(t, eps)[3]
                              - (u0 + eps*math.cos(wp*t)))
                   for t in tt2)
    elo2, ehi2 = 0.1, 1.0
    while minE(ehi2) > 0 and ehi2 < 400:
        ehi2 *= 1.5
    if minE(ehi2) <= 0:
        for _ in range(40):
            em = 0.5*(elo2+ehi2)
            if minE(em) > 0: elo2 = em
            else: ehi2 = em
        eceil = 0.5*(elo2+ehi2)
        out(f"  E-collapse ceiling eps*={eceil:.4e}  "
            f"meas/ceiling={meas/eceil:.3f}")
out(f"DONE wall={time.time()-T0:.0f}s")
