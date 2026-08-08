"""Mechanistic 2:1 parametric-tongue formula and multi-parameter check.
Formula (derived, zero fitting):
  mode eq. in the co-rotating frame under V pumping at 2*w0:
    w' = -alpha*w + (eps/2)*pi_eff*conj(w),
    pi_eff = <p, (dA/dV) qbar> + <p, B(h_F, qbar)>,
    h_F = (2i*w0*I - A)^{-1} f_V   (response at the pump frequency)
  threshold:  eps_th = 2*alpha/|pi_eff|      (PD, multiplier through -1)
Verification: Floquet measurement of the tongue edge per set.
Usage: python dtheory.py {gfl|gfm}
"""
import sys
WHICH = sys.argv[1]
import time, os
os.makedirs('sweep20', exist_ok=True)
LOG = open(f'sweep20/dtheory-{WHICH}.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

if WHICH == 'gfl':
    exec(open('selfhead.py').read())
    _Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
            for j in range(4)] for i in range(4)]
    def jac_a(x, prm):
        a = _avl(x, prm)
        return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                         for i in range(4)])
    CASES = [
        dict(tag='G1 m=0.05', over={}, marg=0.05),
        dict(tag='G1 m=0.10', over={}, marg=0.10),
        dict(tag='G1 m=0.20', over={}, marg=0.20),
        dict(tag='Xg=0.70',   over=dict(Xg=0.70), marg=0.10),
        dict(tag='C=0.02',    over=dict(C=0.02), marg=0.10),
        dict(tag='mix12',     over=dict(kp=40., ki=800., kpv=1.5, kiv=60.,
                                        C=0.015, Xg=0.45), marg=0.10),
        dict(tag='mix16',     over=dict(kp=45., ki=900., Xg=0.55), marg=0.10),
    ]
    def build(case):
        prb = gset('G1', **case['over'])
        Psn = 3*prb['V']**2/(4*prb['Xg'])
        def reA(P):
            q = dict(prb, P=P)
            x = equil(q)
            if x is None: return None
            cm = crit_mode(jac(x, q))
            return None if cm is None else cm.real
        grid = np.linspace(0.05, 0.985, 60)*Psn
        va = [reA(P) for P in grid]
        br = None
        for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
            if fa is not None and fb is not None and fa < 0 <= fb:
                br = (a, b); break
        if br is None: return None
        lo, hi = br
        for _ in range(45):
            m = 0.5*(lo+hi)
            v = reA(m)
            if v is None or v >= 0: hi = m
            else: lo = m
        PH = 0.5*(lo+hi)
        P = margin_point(prb, PH, case['marg'])
        pr = dict(prb, P=P)
        co = nf_coeffs(pr)
        return pr, co
    def tensors(pr, st):
        a = _avl(st, pr)
        def B2c(u, v):
            return np.array([sum(_Hl[i][j][k](*a)*u[j]*v[k]
                                 for j in range(4) for k in range(4))
                             for i in range(4)])
        return B2c
    def dAdV(st, pr, h=1e-6):
        return (jac_a(st, dict(pr, V=pr['V']+h))
                - jac_a(st, dict(pr, V=pr['V']-h)))/(2*h)
    def fV(st, pr, h=1e-6):
        return (rhs(st, dict(pr, V=pr['V']+h))
                - rhs(st, dict(pr, V=pr['V']-h)))/(2*h)
    def strobe_var(x0, pr, eps, wp, Td):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=pr['V'] + eps*math.cos(wp*t))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq), (jac_a(x, qq) @ Phi).ravel()])
        y0 = np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11, atol=1e-13)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
else:
    import math, numpy as np
    from scipy.integrate import solve_ivp
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                        mset, fold, Bform)
    from scipy.linalg import eig as _eig
    CASES = [
        dict(tag='M1 Xg=0.10', name='M1', Xg=0.10),
        dict(tag='M1 Xg=0.05', name='M1', Xg=0.05),
        dict(tag='M2 Xg=0.05', name='M2', Xg=0.05),
        dict(tag='M5 Xg=0.10', name='M5', Xg=0.10),
        dict(tag='M5 Xg=0.05', name='M5', Xg=0.05),
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
        co = dict(st=st, alpha=-lam.real, w0=lam.imag, q=qv, p=pv)
        return prm, co
    def tensors(pr, st):
        return lambda u, v: Bform(st, pr, u, v)
    def dAdV(st, pr, h=1e-6):
        return (jac(st, dict(pr, V=pr['V']+h))
                - jac(st, dict(pr, V=pr['V']-h)))/(2*h)
    def fV(st, pr, h=1e-6):
        return (rhs(st, dict(pr, V=pr['V']+h))
                - rhs(st, dict(pr, V=pr['V']-h)))/(2*h)
    def strobe_var(x0, pr, eps, wp, Td):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=pr['V']*(1 + eps*math.cos(wp*t)))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq), (jac(x, qq) @ Phi).ravel()])
        y0 = np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-10, atol=1e-12)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)

def newton_fp(xg, pr, eps, wp, Td, itmax=25):
    import numpy as np
    x = xg.copy(); M = None
    for it in range(itmax):
        xT, M = strobe_var(x, pr, eps, wp, Td)
        Fx = xT - x
        if np.max(np.abs(Fx)) < 1e-10:
            return x, M, True
        try:
            dx = np.linalg.solve(M - np.eye(4), -Fx)
        except np.linalg.LinAlgError:
            return x, M, False
        n = np.max(np.abs(dx))
        if n > 0.3:
            dx *= 0.3/n
        x = x + dx
    return x, M, np.max(np.abs(Fx)) < 1e-8

import numpy as np, math
for case in CASES:
    r = build(case)
    if r is None:
        out(f"{case['tag']}: no Hopf window — skip")
        continue
    pr, co = r
    st = co['st']; alpha = co['alpha']; w0 = co['w0']
    qv = co['q']; pv = co['p']
    B2 = tensors(pr, st)
    M1 = dAdV(st, pr)
    bv = fV(st, pr)
    hF = np.linalg.solve(2j*w0*np.eye(4) - jac(st, pr) if WHICH == 'gfm'
                         else 2j*w0*np.eye(4) - jac_a(st, pr), bv)
    t1 = np.vdot(pv, M1 @ np.conj(qv))
    t2 = np.vdot(pv, B2(hF, np.conj(qv)))
    pi_eff = t1 + t2
    scale = pr['V'] if WHICH == 'gfm' else 1.0   # gfm pump is V*(1+eps cos)
    eps_pred = 2*alpha/abs(pi_eff)/scale
    wp = 2*w0
    Td = 2*math.pi/wp
    def stab(e):
        xn, Mn, okn = newton_fp(st.copy(), pr, e, wp, Td)
        if not okn:
            return False
        return float(np.max(np.abs(np.linalg.eigvals(Mn)))) < 1.0
    elo, ehi = 0.6*eps_pred, 1.6*eps_pred
    n = 0
    while not stab(elo) and n < 6:
        elo /= 1.7; n += 1
    n = 0
    while stab(ehi) and n < 6:
        ehi *= 1.7; n += 1
    if not stab(elo) or stab(ehi):
        out(f"{case['tag']}: bracket failed around pred={eps_pred:.3e}")
        continue
    for _ in range(12):
        em = 0.5*(elo+ehi)
        if stab(em): elo = em
        else: ehi = em
    eps_meas = 0.5*(elo+ehi)
    err = (eps_pred - eps_meas)/eps_meas*100
    out(f"{case['tag']}: alpha={alpha:.4f} w0={w0:.3f} "
        f"|t1|={abs(t1):.1f} |t2|={abs(t2):.1f} |pi|={abs(pi_eff):.1f} "
        f"pred={eps_pred:.4e} meas={eps_meas:.4e} err={err:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
