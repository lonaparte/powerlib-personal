"""Closed-form Hopf criterion for the GFM 4-state VSM.
Jacobian structure (states d, om, Pf, Qf):
    [[0, 1, 0, 0], [0, -D/M, -1/M, 0],
     [wc*K, 0, -wc, wc*a], [wc*L, 0, 0, -wc*b]]
with K=dPe/dd, a=dPe/dQf, L=dQe/dd, b=1-dQe/dQf.  Solve the Routh
Hopf condition Delta3 = a1 a2 a3 - a3^2 - a1^2 a4 = 0 for K
symbolically -> explicit K_H(a,L,b;M,D,wc).  Verify per set against
the eigenvalue-bisected P_H (expect ~machine) and print the a,L->0
limit (3-state formula). Budget ~2 min.
"""
import sympy as sy
import math, numpy as np, time, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                    mset, fold, P_of, E_of)
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/phsym.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

K, a, L, b, M, D, wc = sy.symbols('K a L b M D w_c', positive=False)
A = sy.Matrix([[0, 1, 0, 0], [0, -D/M, -sy.Rational(1)/M, 0],
               [wc*K, 0, -wc, wc*a], [wc*L, 0, 0, -wc*b]])
lam = sy.symbols('lam')
cp = A.charpoly(lam).all_coeffs()      # [1, a1, a2, a3, a4]
a1, a2, a3, a4 = cp[1], cp[2], cp[3], cp[4]
D3 = sy.expand(a1*a2*a3 - a3**2 - a1**2*a4)
sols = sy.solve(sy.Eq(D3, 0), K)
out(f"Delta3 degree in K: {sy.degree(sy.Poly(D3, K))}; "
    f"{len(sols)} root(s)")
for i, s0 in enumerate(sols):
    out(f"K_H root {i}: {sy.simplify(s0)}")
KH = sols[1] if len(sols) > 1 else sols[0]
lim0 = sy.simplify(KH.subs({a: 0, L: 0}))
out(f"a,L->0 limit: {lim0}   (3-state: D*(D/M+w_c))")
KHf = sy.lambdify((a, L, b, M, D, wc), KH, 'numpy')

SETS = [('M1', 0.10), ('M2', 0.05), ('M3', 0.05), ('M1', 0.05),
        ('M5', 0.10), ('M2', 0.03)]
for name, Xg in SETS:
    pr = mset(name, Xg=Xg)
    dfold, Pm = fold(pr)
    q = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
    if q is None:
        out(f"{name}@{Xg}: no window"); continue
    PH_eig = q['Pref']
    def st_of(d):
        prd = dict(pr, Pref=P_of(d, pr))
        E = E_of(d, prd)
        Qf = (E*E - E*pr['V']*math.cos(d))/pr['Xg']
        return np.array([d, 0.0, prd['Pref'], Qf]), prd
    def coefs(d):
        stx, prd = st_of(d)
        J = jac(stx, prd)
        wcv = pr['wc']
        Kv = J[2, 0]/wcv
        av = J[2, 3]/wcv
        Lv = J[3, 0]/wcv
        bv = -J[3, 3]/wcv
        return Kv, av, Lv, bv
    def crit(d):
        Kv, av, Lv, bv = coefs(d)
        return Kv - float(KHf(av, Lv, bv, pr['M'], pr['D'], pr['wc']))
    dl = np.linspace(1e-3, dfold*0.999, 300)
    vals = [crit(d) for d in dl]
    dH = None
    for x1, x2, f1, f2 in zip(dl[:-1], dl[1:], vals[:-1], vals[1:]):
        if f1*f2 < 0:
            lo, hi = x1, x2
            for _ in range(60):
                mid = 0.5*(lo+hi)
                if crit(mid)*f1 > 0: lo = mid
                else: hi = mid
            dH = 0.5*(lo+hi)
            break
    if dH is None:
        out(f"{name}@{Xg}: closed-form criterion no root?!"); continue
    PH_c = P_of(dH, pr)
    out(f"{name}@Xg={Xg}: P_H(closed-form)={PH_c:.6f} "
        f"P_H(eig)={PH_eig:.6f} rel={(PH_c-PH_eig)/PH_eig:+.2e}")
out(f"DONE wall={time.time()-T0:.0f}s")
