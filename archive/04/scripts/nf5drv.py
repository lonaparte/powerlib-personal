"""Two-carrier fifth-order normal form with the DRIVE CHANNEL as an argument.

mech7 hardcoded the fifth expansion variable to V_, so every multiplicative
(parametric) term it built was d^2 f/dy dV -- regardless of which parameter
actually carried the drive.  mech8 then ran that machinery on P and Q.

For P that is provably wrong and provably harmless-looking: P enters the
field only through P/C in the DC-link balance, so d^2 f / dy dP == 0 and
P's parametric share must be EXACTLY zero.  mech8 printed -0.02%, which is
the V tensors leaking into the P run.

For Q it is wrong in a way that matters: Q enters both the network algebra
(vgd = V cos th - Xg Q) and the DC balance (1.5 (vgd idr + vgq Q)/Vdc), so
d^2 f/dy dQ is genuinely nonzero and is NOT proportional to d^2 f/dy dV.
The Q channel therefore ran with the wrong multiplicative operator, which
is the first thing to check against its +0.56% additive-only residual.

Requires selfhead.py to have been exec'd (provides f_, _x, the parameter
symbols, equil, jac).
"""
import itertools
from math import factorial
import numpy as np

TR = 5


def pmul(a, b):
    r = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = (ka[0]+kb[0], ka[1]+kb[1], ka[2]+kb[2], ka[3]+kb[3])
            if k[0]+k[1]+k[2]+k[3] > TR:
                continue
            r[k] = r.get(k, 0) + va*vb
    return r


def deg(k):
    return k[0]+k[1]+k[2]+k[3]


def mult_count(combo):
    n = len(combo); r = factorial(n)
    for j in set(combo):
        r //= factorial(combo.count(j))
    return r


def make_tensors5(sp, f_, _x, syms, pr, st, drv):
    """d^k f_i / d(th,xp,Vdc,xi,u)^k at (st, u0), k = 2..5, with u = drv.

    drv is the sympy symbol of the parameter that carries the drive.
    Index 4 in a combo means 'differentiate once more w.r.t. u'.
    """
    vars5 = list(_x) + [drv]
    subs = dict(syms)
    subs.update({_x[0]: st[0], _x[1]: st[1], _x[2]: st[2], _x[3]: st[3]})
    Dk = {}
    for k in range(2, 6):
        Dk[k] = [dict() for _ in range(4)]
        for i in range(4):
            for combo in itertools.combinations_with_replacement(range(5), k):
                e = f_[i]
                for j in combo:
                    e = sp.diff(e, vars5[j])
                    if e == 0:
                        break
                if e == 0:
                    continue
                val = complex(e.subs(subs).evalf())
                if abs(val) > 1e-13:
                    Dk[k][i][combo] = val
    return Dk


def solve_nf5(A, lam, q, p, fu, wp, Dk, param=True):
    """Homological solve on the four carrier variables, returning the
    resonant coefficients.  Dk carries index 4 = the drive coordinate u;
    param=False strips every derivative that touches u."""
    if not param:
        Dk = {k: [{c: v for c, v in Dk[k][i].items() if 4 not in c}
                  for i in range(4)] for k in Dk}
    I = np.eye(4)
    H = np.linalg.solve(1j*wp*I - A, fu.astype(complex))
    Y = [dict() for _ in range(5)]
    for i in range(4):
        Y[i][(1, 0, 0, 0)] = q[i]; Y[i][(0, 1, 0, 0)] = np.conj(q[i])
        Y[i][(0, 0, 1, 0)] = H[i]; Y[i][(0, 0, 0, 1)] = np.conj(H[i])
    Y[4][(0, 0, 1, 0)] = 1.0 + 0j; Y[4][(0, 0, 0, 1)] = 1.0 + 0j
    g = {}; lamb = np.conj(lam); qb = np.conj(q)
    for n in range(2, TR+1):
        N = {}
        for k in range(2, n+1):
            for combo in itertools.combinations_with_replacement(range(5), k):
                nz = [i for i in range(4) if combo in Dk[k][i]]
                if not nz:
                    continue
                cf = mult_count(combo)/factorial(k)
                prod = Y[combo[0]]
                for c in combo[1:]:
                    prod = pmul(prod, Y[c])
                for idx, v in prod.items():
                    if deg(idx) != n:
                        continue
                    if idx not in N:
                        N[idx] = np.zeros(4, complex)
                    for i in nz:
                        N[idx][i] += cf*Dk[k][i][combo]*v
        gb = {(b, a, d, c): np.conj(v) for (a, b, c, d), v in g.items()}
        Tt = {}
        for i in range(4):
            dz = {}; dzb = {}
            for idx, v in Y[i].items():
                if idx[0] >= 1:
                    k2 = (idx[0]-1, idx[1], idx[2], idx[3])
                    dz[k2] = dz.get(k2, 0) + idx[0]*v
                if idx[1] >= 1:
                    k2 = (idx[0], idx[1]-1, idx[2], idx[3])
                    dzb[k2] = dzb.get(k2, 0) + idx[1]*v
            for src in ((pmul(dz, g) if g else {}),
                        (pmul(dzb, gb) if gb else {})):
                for idx, v in src.items():
                    if deg(idx) != n:
                        continue
                    if idx not in Tt:
                        Tt[idx] = np.zeros(4, complex)
                    Tt[idx][i] += v
        newg = {}
        for idx in sorted(set(list(N.keys()) + list(Tt.keys()))):
            j, k2, l, m = idx
            D = j*lam + k2*lamb + (l-m)*1j*wp
            rv = (N.get(idx, np.zeros(4, complex))
                  - Tt.get(idx, np.zeros(4, complex)))
            if np.max(np.abs(rv)) < 1e-14:
                continue
            if abs(D - lam) < 1e-7*max(1.0, abs(lam)):
                cg = np.vdot(p, rv); newg[idx] = cg
                M = np.zeros((5, 5), complex)
                M[:4, :4] = D*I - A; M[:4, 4] = q; M[4, :4] = np.conj(p)
                h = np.linalg.solve(M, np.concatenate([rv - cg*q, [0.0]]))[:4]
            elif abs(D - lamb) < 1e-7*max(1.0, abs(lam)):
                cg = np.dot(p, rv)
                M = np.zeros((5, 5), complex)
                M[:4, :4] = D*I - A; M[:4, 4] = qb; M[4, :4] = p
                h = np.linalg.solve(M, np.concatenate([rv - cg*qb, [0.0]]))[:4]
            else:
                h = np.linalg.solve(D*I - A, rv)
            for i in range(4):
                if abs(h[i]) > 0:
                    Y[i][idx] = Y[i].get(idx, 0) + h[i]
        g.update(newg)
    hh = {idx: np.array([Y[i].get(idx, 0) for i in range(4)])
          for idx in ((0, 0, 2, 0), (0, 0, 1, 1), (0, 0, 0, 2))}
    return dict(lam=lam, q=q, p=p, A=A, H=H, Y=Y, g=g, h=hh,
                c1=g.get((2, 1, 0, 0), 0), c_x=g.get((1, 0, 1, 1), 0),
                c2=g.get((3, 2, 0, 0), 0), c_xx=g.get((2, 1, 1, 1), 0),
                c_a4=g.get((1, 0, 2, 2), 0))


def guard_root(aeff, c1e, c2e):
    """Positive root of c2 r^4 + c1e r^2 - aeff = 0 that is the guard.
    aeff <= 0 means the guard has already been eroded away: no barrier."""
    import math
    if aeff <= 0.0 or c1e <= 0.0:
        return float('nan')
    if abs(c2e)*aeff < 1e-12*c1e**2:
        return math.sqrt(aeff/c1e)
    disc = c1e**2 + 4*c2e*aeff
    if disc < 0.0:
        return float('nan')
    r2 = (-c1e + math.sqrt(disc))/(2*c2e)
    return math.sqrt(r2) if r2 > 0 else float('nan')
