"""Slot F, round 2: co-moving-frame slow reduction (exact structure).
Using f(st(V),V)=0  =>  f_V = -A st_V  =>  <p,f_V> = -lam <p,st_V>,
the fixed-origin forcing cancels and the correct 1D reduced model is
    zdot = lam(mu(t)) z - <p, st_mu> mudot - <p, q_mu> mudot z
           + c1(mu) |z|^2 z
with ALL coefficients evaluated along the swept path mu(t) (V for GFL,
Pref for GFM) and eigenvectors phase-aligned along the path.
GFL: predict a_c(ws) vs measured; GFM: predict max|om| vs measured.
Usage: python rates2.py {gfl|gfm}
"""
import sys
WHICH = sys.argv[1]
import time, os
os.makedirs('sweep20', exist_ok=True)
LOG = open(f'sweep20/rates2-{WHICH}.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

import math, numpy as np
from scipy.integrate import solve_ivp

def align(qs, ps):
    for i in range(1, len(qs)):
        c = np.vdot(qs[i-1], qs[i])
        ph = c/abs(c)
        qs[i] = qs[i]/ph
        ps[i] = ps[i]/ph
    return qs, ps

if WHICH == 'gfl':
    exec(open('selfhead.py').read())
    pr0 = gset('G1', Xg=0.5)
    lo, hi = 0.9, 1.4775
    def g0(P):
        x = equil(dict(pr0, P=P))
        return crit_mode(jac(x, dict(pr0, P=P))).real
    for _ in range(45):
        m = 0.5*(lo+hi)
        if g0(m) < 0: lo = m
        else: hi = m
    P = margin_point(pr0, 0.5*(lo+hi), 0.10)
    pr = dict(pr0, P=P)
    amax = 4.5e-3
    Vg = 1.0 + np.linspace(-1.3*amax, 1.3*amax, 49)
    sts, lams, c1s, qs, ps = [], [], [], [], []
    for V in Vg:
        co = nf_coeffs(dict(pr, V=V))
        sts.append(co['st']); lams.append(co['lam'])
        c1s.append(co['c1']); qs.append(co['q']); ps.append(co['p'])
    qs, ps = align(qs, ps)
    sts = np.array(sts); lams = np.array(lams); c1s = np.array(c1s)
    qs = np.array(qs); ps = np.array(ps)
    dV = Vg[1] - Vg[0]
    st_V = np.gradient(sts, dV, axis=0)
    q_V = np.gradient(qs, dV, axis=0)
    pstV = np.array([np.vdot(ps[i], st_V[i]) for i in range(len(Vg))])
    pqV = np.array([np.vdot(ps[i], q_V[i]) for i in range(len(Vg))])
    zg = math.sqrt((-lams.real[len(Vg)//2])/c1s.real[len(Vg)//2])
    out(f"P={P:.5f} zg={zg:.4e} lamRe range "
        f"[{lams.real.min():.2f},{lams.real.max():.2f}] "
        f"|pstV| mid={abs(pstV[len(Vg)//2]):.3f} "
        f"|pqV| mid={abs(pqV[len(Vg)//2]):.2f}")
    def itp(arr, V):
        return complex(np.interp(V, Vg, arr.real),
                       np.interp(V, Vg, arr.imag))
    MEAS = {0.2: 4.227e-4, 1.0: 1.274e-3, 5.0: 3.163e-3}
    for ws in (0.2, 1.0, 5.0):
        Tt = 3*2*math.pi/ws
        def escape1d(a):
            def f(t, y):
                z = y[0] + 1j*y[1]
                V = 1.0 - a*math.sin(ws*t)
                Vd = -a*ws*math.cos(ws*t)
                dz = (itp(lams, V)*z - itp(pstV, V)*Vd
                      - itp(pqV, V)*Vd*z + itp(c1s, V)*abs(z)**2*z)
                return [dz.real, dz.imag]
            def blow(t, y):
                return math.hypot(y[0], y[1]) - 5*zg
            blow.terminal = True; blow.direction = 1
            s = solve_ivp(f, (0, Tt), [0.0, 0.0], method='DOP853',
                          rtol=1e-10, atol=1e-14, events=blow)
            return len(s.t_events[0]) > 0
        alo, ahi = 1e-5, 0.02
        if not escape1d(ahi):
            out(f"  ws={ws}: no escape at a=0.02"); continue
        for _ in range(14):
            am = 0.5*(alo+ahi)
            if escape1d(am): ahi = am
            else: alo = am
        ap = 0.5*(alo+ahi)
        ms = MEAS[ws]
        out(f"  RESULT ws={ws}: a_pred={ap:.4e} a_meas={ms:.4e} "
            f"err={(ap-ms)/ms*100:+.1f}%")
    out(f"DONE wall={time.time()-T0:.0f}s")

else:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                        mset, fold, hopf_c1)
    pr = mset('M1', Xg=0.10)
    dfold, Pm = fold(pr)
    qh = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
    P_H = qh['Pref']
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
    P0 = 0.5*(lo2+hi2)
    dP = P0 - P_H
    Pmin = 0.06*P_H
    Pg = np.linspace(Pmin, P0 + 0.25*dP, 49)
    sts, lams, c1s, qs, ps = [], [], [], [], []
    for Pq in Pg:
        co = hopf_c1(dict(pr, Pref=Pq))
        sts.append(co['st']); lams.append(co['lam'])
        c1s.append(co['c1']); qs.append(co['q']); ps.append(co['p'])
    qs, ps = align(qs, ps)
    sts = np.array(sts); lams = np.array(lams); c1s = np.array(c1s)
    qs = np.array(qs); ps = np.array(ps)
    dPg = Pg[1] - Pg[0]
    st_P = np.gradient(sts, dPg, axis=0)
    q_P = np.gradient(qs, dPg, axis=0)
    pstP = np.array([np.vdot(ps[i], st_P[i]) for i in range(len(Pg))])
    pqP = np.array([np.vdot(ps[i], q_P[i]) for i in range(len(Pg))])
    out(f"M1: P_H={P_H:.4f} P0={P0:.4f} dP={dP:.4f} "
        f"c1Re range [{c1s.real.min():.4f},{c1s.real.max():.4f}]")
    def itpC(arr, Pq):
        Pq = min(max(Pq, Pg[0]), Pg[-1])
        return complex(np.interp(Pq, Pg, arr.real),
                       np.interp(Pq, Pg, arr.imag))
    def itpV(arr, Pq):
        Pq = min(max(Pq, Pg[0]), Pg[-1])
        return np.array([complex(np.interp(Pq, Pg, arr[:, i].real),
                                 np.interp(Pq, Pg, arr[:, i].imag))
                         for i in range(4)])
    MEAS = {(0.1, 0.5): 0.0060, (0.1, 1.5): 0.0179, (0.1, 3.0): 0.0416,
            (0.5, 0.5): 0.0299, (0.5, 1.5): 0.0897, (0.5, 3.0): 0.1847}
    for ws in (0.1, 0.5):
        for fdip in (0.5, 1.5, 3.0):
            a = fdip*dP
            Tt = 2*2*math.pi/ws
            def f(t, y):
                z = y[0] + 1j*y[1]
                Pq = P0 - a*math.sin(ws*t)
                Pd = -a*ws*math.cos(ws*t)
                dz = (itpC(lams, Pq)*z - itpC(pstP, Pq)*Pd
                      - itpC(pqP, Pq)*Pd*z + itpC(c1s, Pq)*abs(z)**2*z)
                return [dz.real, dz.imag]
            s = solve_ivp(f, (0, Tt), [0.0, 0.0], method='DOP853',
                          rtol=1e-9, atol=1e-13, dense_output=True)
            tt2 = np.linspace(0, Tt, 4000)
            ys = s.sol(tt2)
            zs = ys[0] + 1j*ys[1]
            oms = np.empty(len(tt2))
            for i2 in range(len(tt2)):
                Pq = P0 - a*math.sin(ws*tt2[i2])
                qv = itpV(qs, Pq)
                oms[i2] = 2*(zs[i2]*qv[1]).real
            pred = float(np.max(np.abs(oms)))
            ms = MEAS[(ws, fdip)]
            out(f"  RESULT ws={ws} dip={fdip}: pred={pred:.4f} "
                f"meas={ms:.4f} err={(pred-ms)/ms*100:+.1f}%")
    out(f"DONE wall={time.time()-T0:.0f}s")
