"""GFM P_H made explicit: Hopf condition = Routh Delta3(delta) =
a1 a2 a3 - a3^2 - a1^2 a4 = 0 (charpoly coefficients of the 4-state
Jacobian along the enslaved-E equilibrium family) — an explicit
algebraic criterion; verify equality with the eigenvalue-bisected P_H,
and quantify the 3-state compact formula K_qs(d_H) = D(D/M + wc)
across the six windows. Budget ~3 min.
"""
import math, numpy as np, time, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, P_of, E_of)
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/phrouth.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

SETS = [('M1', 0.10), ('M2', 0.05), ('M3', 0.05), ('M1', 0.05),
        ('M5', 0.10), ('M2', 0.03)]
for name, Xg in SETS:
    pr = mset(name, Xg=Xg)
    dfold, Pm = fold(pr)
    q = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
    if q is None:
        out(f"{name}@{Xg}: no window"); continue
    P_H_eig = q['Pref']
    M, D, wc = pr['M'], pr['D'], pr['wc']
    def st_of(d):
        prd = dict(pr, Pref=P_of(d, pr))
        E = E_of(d, prd)
        Qf = (E*E - E*pr['V']*math.cos(d))/pr['Xg']
        return np.array([d, 0.0, prd['Pref'], Qf]), prd
    def Delta3(d):
        st, prd = st_of(d)
        A = jac(st, prd)
        cp = np.poly(A)            # [1, a1, a2, a3, a4]
        a1, a2, a3, a4 = cp[1], cp[2], cp[3], cp[4]
        return a1*a2*a3 - a3*a3 - a1*a1*a4
    # bisect Delta3 = 0 in delta
    dl = np.linspace(1e-3, dfold*0.999, 400)
    vals = [Delta3(d) for d in dl]
    dH = None
    for a, b, fa, fb in zip(dl[:-1], dl[1:], vals[:-1], vals[1:]):
        if fa*fb < 0:
            lo, hi = a, b
            for _ in range(60):
                mid = 0.5*(lo+hi)
                if Delta3(mid)*fa > 0: lo = mid
                else: hi = mid
            dH = 0.5*(lo+hi)
            break
    if dH is None:
        out(f"{name}@{Xg}: Delta3 has no zero below fold?!"); continue
    P_H_routh = P_of(dH, pr)
    # 3-state compact formula: K_qs(d) = dP_of/dd = D(D/M + wc)
    KH = D*(D/M + wc)
    h = 1e-6
    def Kqs(d): return (P_of(d+h, pr) - P_of(d-h, pr))/(2*h)
    lo, hi = 1e-3, dfold*0.999
    # K_qs decreases toward fold; find K_qs = KH
    if Kqs(lo) < KH:
        out(f"{name}@{Xg}: K_qs(0)<K_H — 3-state formula out of range "
            f"(KH={KH:.2f} vs Kmax={Kqs(lo):.2f})")
        P_H3 = None
    else:
        for _ in range(60):
            mid = 0.5*(lo+hi)
            if Kqs(mid) > KH: lo = mid
            else: hi = mid
        P_H3 = P_of(0.5*(lo+hi), pr)
    r_err = (P_H_routh - P_H_eig)/P_H_eig*100
    line = (f"{name}@Xg={Xg}: P_H(eig)={P_H_eig:.5f} "
            f"P_H(Routh)={P_H_routh:.5f} ({r_err:+.2e}%)")
    if P_H3 is not None:
        line += (f"  P_H(3-state)={P_H3:.5f} "
                 f"err={(P_H3-P_H_eig)/P_H_eig*100:+.2f}%")
    out(line)
out(f"DONE wall={time.time()-T0:.0f}s")
