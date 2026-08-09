"""F-GFM M1 residuals (ws=0.1, dip=0.5: -1.5%; dip=1.5: -1.0%).
(1) Full-precision 4D remeasurement (old MEAS were 4-decimal
    transcriptions: 0.0060 -> +-0.8% quantization).
(2) GFM shifted-origin T5 model: wdot = A(P)w + 1/2 B + 1/6 C
    + D4/24 + D5/120 - st_P*Pd;  omega(t) = w[1].  pred = max|w[1]|
    over the same 2-period window. dip=3.0 as regression.
Budget ~20 min.
"""
import math, numpy as np, time, os, sys, itertools
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, _x, _p, f_, _args, _av, _H, _T)
from scipy.integrate import solve_ivp
from scipy.interpolate import CubicSpline
LOG = open('sweep20/fgfm2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

_Q4l = [dict() for _ in range(4)]
_Q5l = [dict() for _ in range(4)]
for i in range(4):
    for combo in itertools.combinations_with_replacement(range(4), 4):
        e = f_[i]
        for j in combo:
            e = sp.diff(e, _x[j])
        _Q4l[i][combo] = sp.lambdify(_args, e, 'numpy')
    for combo in itertools.combinations_with_replacement(range(4), 5):
        e = f_[i]
        for j in combo:
            e = sp.diff(e, _x[j])
        _Q5l[i][combo] = sp.lambdify(_args, e, 'numpy')
out(f"lambdas built [{time.time()-T0:.0f}s]")

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
st0 = equil(dict(pr, Pref=P0))
out(f"M1: P_H={P_H:.4f} P0={P0:.4f} dP={dP:.4f}")
Pmin = 0.06*P_H
Pg = np.linspace(Pmin, P0 + 0.25*dP, 181)
n = len(Pg)
sts = np.zeros((n, 4)); Ag = np.zeros((n, 4, 4))
Hg = np.zeros((n, 4, 4, 4)); Cg = np.zeros((n, 4, 4, 4, 4))
D4g = np.zeros((n, 4, 4, 4, 4, 4))
D5g = np.zeros((n, 4, 4, 4, 4, 4, 4))
for iP, Pq in enumerate(Pg):
    prq = dict(pr, Pref=Pq)
    stq = equil(prq)
    sts[iP] = stq
    Ag[iP] = jac(stq, prq)
    av = _av(stq, prq)
    for i in range(4):
        for j in range(4):
            for k in range(4):
                Hg[iP, i, j, k] = float(_H[i][j][k](*av))
                for l in range(4):
                    Cg[iP, i, j, k, l] = float(_T[i][j][k][l](*av))
    for i in range(4):
        for combo, fn in _Q4l[i].items():
            val = float(fn(*av))
            if val == 0.0:
                continue
            for perm in set(itertools.permutations(combo)):
                D4g[(iP, i) + perm] = val
        for combo, fn in _Q5l[i].items():
            val = float(fn(*av))
            if val == 0.0:
                continue
            for perm in set(itertools.permutations(combo)):
                D5g[(iP, i) + perm] = val
st_P = np.gradient(sts, Pg[1]-Pg[0], axis=0)
spA = CubicSpline(Pg, Ag); spH = CubicSpline(Pg, Hg)
spC = CubicSpline(Pg, Cg); spD4 = CubicSpline(Pg, D4g)
spD5 = CubicSpline(Pg, D5g)
spst = CubicSpline(Pg, sts); spstP = CubicSpline(Pg, st_P)
out(f"tensor grid done [{time.time()-T0:.0f}s]")
Plo_, Phi2_ = Pg[0], Pg[-1]
for ws in (0.1,):
    for fdip in (0.5, 1.5, 3.0):
        a = fdip*dP
        Tt = 2*2*math.pi/ws
        tt2 = np.linspace(0, Tt, 4000)
        # (1) 4D full-precision measurement
        def f4(t, x):
            return rhs(x, dict(pr, Pref=P0 - a*math.sin(ws*t)))
        s4 = solve_ivp(f4, (0, Tt), st0 + np.array([1e-5, 0, 0, 0]),
                       method='DOP853', rtol=1e-10, atol=1e-13,
                       dense_output=True)
        meas = float(np.max(np.abs(s4.sol(tt2)[1])))
        # (2) T5 shifted-origin prediction
        def fT(t, w):
            Pq = P0 - a*math.sin(ws*t)
            Pq = min(max(Pq, Plo_), Phi2_)
            Pd = -a*ws*math.cos(ws*t)
            dw = (spA(Pq) @ w
                  + 0.5*np.einsum('ijk,j,k->i', spH(Pq), w, w)
                  + np.einsum('ijkl,j,k,l->i', spC(Pq), w, w, w)/6.0
                  + np.einsum('ijklm,j,k,l,m->i', spD4(Pq),
                              w, w, w, w)/24.0
                  + np.einsum('ijklmn,j,k,l,m,n->i', spD5(Pq),
                              w, w, w, w, w)/120.0
                  - spstP(Pq)*Pd)
            return dw
        sT = solve_ivp(fT, (0, Tt), np.zeros(4), method='DOP853',
                       rtol=1e-10, atol=1e-13, dense_output=True)
        pred = float(np.max(np.abs(sT.sol(tt2)[1])))
        oldm = {0.5: 0.0060, 1.5: 0.0179, 3.0: 0.0416}[fdip]
        out(f"  ws={ws} dip={fdip}: meas(full)={meas:.6f} "
            f"(old rounded {oldm}) T5pred={pred:.6f} "
            f"err={(pred-meas)/meas*100:+.2f}% [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
