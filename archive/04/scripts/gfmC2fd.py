"""C2, parts 2 and 3: the lag terms, then the four GFM cells.

Part 1 (gfmC2.py) validated the STATIC half of the O(nu) list on a scalar
system: the first-order Gaussian moments for (0,2), (2,1), (4,0) and the
second-order quadrature for (1,1), (3,0) all reproduced a directly measured
C2 to four decimals.  What that cannot test is the part that only exists
because the GFM is a 4-state system: the non-critical states do not sit
exactly on their quasi-static values, they LAG, and the lag feeds back into
the critical direction.

Part 2 puts in the smallest system that has a lag and still has every
coefficient in closed form:

    xdot = a D + b x^2 + c12 x y ,     ydot = -lf y + d D + e x^2

Here y* = (dD + e x^2)/lf exactly, so the Lyapunov-Schmidt reduced map is
    R(xi,D) = a D + b xi^2 + (c12 d/lf) xi D + (c12 e/lf) xi^3
i.e. kappa = c12 d/lf and b3 = c12 e/lf, with a2 = be2 = b4 = 0, and the two
lag coefficients follow from  y = y* + Ap (dy*/dD Ddot + dy*/dxi xidot):

    mu_D  = <w, B(v, Ap y_D)>      = -c12 d / lf^2
    mu_xi = <w, B(v, Ap y*_xixi)>  = -2 c12 e / lf^2

Both are O(1/lf^2): a faster stable mode lags less, quadratically.  So the
test has a knob (lf) that changes the lag by a factor of 9 while leaving the
static coefficients fixed -- if the formula tracks that, the lag terms are
right for the reason claimed and not by coincidence.

Part 3 then points the assembled machine at the four GFM cells and compares
with the measured C2 = 0.361 / 0.375 / 0.333 / 0.394 (universal 3/8 = 0.375).
The static coefficients come from a polynomial fit of the exact LS-reduced
map (Newton-solved, no Taylor truncation anywhere in its construction), the
lag ones from two bordered solves.  Zero fitted constants.
"""
import math, time
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import gfmlib as G
from scipy.linalg import eig

LOG = open('sweep20/gfmC2fd.log', 'w')


def out(m):
    LOG.write(m + '\n'); LOG.flush()


T0 = time.time()

def stable_root(Rf, Dv, scale):
    """first sign change of R going from xi = 0 downward: the stable branch.
    Scanning, not bracketing: with a xi^3 term R(-L) turns negative again far
    out, so an expanding bracket walks past the root and then fails."""
    xs = -np.linspace(1e-13, 3.0*scale, 800)
    vv = np.asarray(Rf(xs), float)
    s0 = np.sign(vv[0])
    idx = np.where(np.sign(vv) != s0)[0]
    if len(idx) == 0:
        return float('nan')
    i = idx[0]
    return brentq(Rf, xs[i], xs[i-1], xtol=1e-16, rtol=8.9e-16)

SQPI = math.sqrt(math.pi)
TG = np.linspace(-7.0, 7.0, 40001)
WG = np.exp(-TG*TG)


def lam2(kap, b3):
    def Phi(t):
        return kap*t*(1.0 - t*t) + b3*t**3

    def PhiX(t):
        return kap*(1.0 - t*t) + 3.0*b3*t*t
    ph = Phi(TG)
    u = np.zeros_like(TG)
    for i in range(len(TG)):
        if TG[i] <= 0.0:
            s = TG[:i+1]
            u[i] = np.trapezoid(np.exp(TG[i]**2 - s*s)*ph[:i+1], s)
        else:
            s = TG[i:]
            u[i] = -np.trapezoid(np.exp(TG[i]**2 - s*s)*ph[i:], s)
    return -float(np.trapezoid(WG*(u*u + PhiX(TG)*u), TG))/SQPI


def c2_terms(a, b, eqs, cf, muD=0.0, muX=0.0, nu=0.03):
    c = eqs*(nu*math.sqrt(2.0*a*b*eqs))**2/2.0
    T = (a*b*c)**-0.25

    def hat(m, n):
        return cf.get((m, n), 0.0)*b**(1-m)*a**(-n)*b**(-n)*T**(2-m-2*n)
    t = dict(a2=-0.75*hat(0, 2)/nu, be2=0.25*hat(2, 1)/nu,
             b4=-0.75*hat(4, 0)/nu, muD=muD/(a*b*T*T)/nu,
             muX=-0.5*muX/(b*b*T*T)/nu,
             snd=lam2(hat(1, 1), hat(3, 0))/nu)
    return 0.375 + sum(t.values()), t


# ===================================================================== part 3
out("")
out("=== part 3. the four GFM cells")


def Pmax(pr):
    h = 1e-6

    def dP(dd):
        return (G.P_of(dd+h, pr) - G.P_of(dd-h, pr))/(2*h)
    dl = np.linspace(0.05, math.pi-0.05, 4000)
    Pv = np.array([G.P_of(dd, pr) for dd in dl])
    i = int(np.argmax(Pv))
    df = brentq(dP, dl[max(i-2, 0)], dl[min(i+2, len(dl)-1)],
                xtol=1e-14, rtol=1e-15)
    return df, G.P_of(df, pr)


def eps_qs_of(pr):
    def gap(uu):
        return Pmax(dict(pr, V=pr['V']-uu))[1] - pr['Pref']
    hi = 0.98*pr['V']; n = 0
    while gap(hi) > 0 and n < 40:
        hi = 0.5*(hi + pr['V']); n += 1
    return brentq(gap, 0.0, hi, xtol=1e-14, rtol=1e-15)


CELLS = [('A  M2 Xg=0.5 90%', 'M2', 0.5, 0.90, 0.3612),
         ('B  M3 Xg=0.5 90%', 'M3', 0.5, 0.90, 0.3747),
         ('C  M2 Xg=0.3 75%', 'M2', 0.3, 0.75, 0.3329),
         ('D  M3 Xg=0.3 90%', 'M3', 0.3, 0.90, 0.3940)]
out("  cell             |    a2/a    |    kap     |     b3     |    be2     "
    "|     b4     |   mu_D     |   mu_xi")
res = []
for tag, nm, Xg, frac, c2m in CELLS:
    _, Pm0 = Pmax(G.mset(nm, Xg=Xg))
    pr = G.mset(nm, Xg=Xg, Pref=frac*Pm0)
    eqs = eps_qs_of(pr)
    prf = dict(pr, V=pr['V']-eqs)
    df, _ = Pmax(prf)
    E = G.E_of(df, prf)
    Qf = (E*E - E*prf['V']*math.cos(df))/prf['Xg']
    stf = np.array([df, 0.0, prf['Pref'], Qf])
    A = G.jac(stf, prf)
    ev_, VL, VR = eig(A, left=True, right=True)
    k = int(np.argmin(np.abs(ev_)))
    v = np.real(VR[:, k]); w = np.real(VL[:, k]); w = w/np.dot(w, v)
    Qm = np.eye(4) - np.outer(v, w)
    Ab = np.vstack([np.hstack([A, v.reshape(4, 1)]),
                    np.hstack([w.reshape(1, 4), np.zeros((1, 1))])])

    def Ap(z):
        return np.linalg.solve(Ab, np.concatenate([z, [0.0]]))[:4]

    BAD = [0.0]

    def solve_y1(xi, D, y0):
        y = y0.copy()
        res = 1.0
        for _ in range(200):
            x = stf + xi*v + y
            pq = dict(prf, V=prf['V'] - D)
            F = Qm @ G.rhs(x, pq) + v*np.dot(w, y)
            res = float(np.max(np.abs(F)))
            if res < 1e-15:
                break
            J = Qm @ G.jac(x, pq) + np.outer(v, w)
            y = y - np.linalg.solve(J, F)
        return y, res

    BAD = [0.0]

    def solve_y(xi, D, K=12):
        """continuation from (0,0): a cold Newton diverges on the stiff cells"""
        y = np.zeros(4)
        for k in range(1, K+1):
            y, r = solve_y1(k*xi/K, k*D/K, y)
        BAD[0] = max(BAD[0], r)
        return y

    def R(xi, D):
        return float(np.dot(w, G.rhs(stf + xi*v + solve_y(xi, D),
                                     dict(prf, V=prf['V'] - D))))
    HS = 1e-6
    fV = (G.rhs(stf, dict(prf, V=prf['V']+HS))
          - G.rhs(stf, dict(prf, V=prf['V']-HS)))/(2*HS)
    a0 = float(np.dot(w, -fV))
    b0 = 0.5*float(np.dot(w, G.Bform(stf, prf, v, v)))
    ab = a0*b0
    nu0 = 0.05
    c0 = eqs*(nu0*math.sqrt(2*ab*eqs))**2/2.0
    Tt = (ab*c0)**-0.25
    XS = 1.0/abs(b0*Tt); DS = 1.0/abs(ab*Tt*Tt)

    def coeffs(fac):
        """direct stencils, not a 27-term 2-D fit: far better conditioned"""
        h = fac*XS; k = fac*DS
        R0 = R(0.0, 0.0)
        c = {}
        c[(0, 1)] = (R(0, k) - R(0, -k))/(2*k)
        c[(0, 2)] = 0.5*(R(0, k) - 2*R0 + R(0, -k))/k**2
        c[(2, 0)] = 0.5*(R(h, 0) - 2*R0 + R(-h, 0))/h**2
        c[(3, 0)] = (R(2*h, 0) - 2*R(h, 0) + 2*R(-h, 0)
                     - R(-2*h, 0))/(12.0*h**3)
        c[(4, 0)] = (R(2*h, 0) - 4*R(h, 0) + 6*R0 - 4*R(-h, 0)
                     + R(-2*h, 0))/(24.0*h**4)
        c[(1, 1)] = (R(h, k) - R(h, -k) - R(-h, k) + R(-h, -k))/(4*h*k)
        d2p = (R(h, k) - 2*R(0, k) + R(-h, k))/h**2
        d2m = (R(h, -k) - 2*R(0, -k) + R(-h, -k))/h**2
        c[(2, 1)] = 0.5*(d2p - d2m)/(2*k)
        return c
    cf = coeffs(0.30); cfh = coeffs(0.15)
    out(f"      max Newton residual: {BAD[0]:.2e}   "
        f"(a fit is only meaningful if this is ~1e-14)")
    out("      step 0.30 vs 0.15 inner scale:")
    for key in ((0, 1), (2, 0), (0, 2), (1, 1), (3, 0), (2, 1), (4, 0)):
        out(f"        c{key} = {cf[key]:+.6e} vs {cfh[key]:+.6e}  "
            f"({(cfh[key]/cf[key]-1)*100:+.3f}%)")
    cf = {kk: (4*cfh[kk] - cf[kk])/3.0 for kk in cf}   # Richardson
    yD = -Ap(Qm @ (-fV))
    hxi = 0.01*XS
    yxx = (solve_y(hxi, 0.0) - 2*solve_y(0.0, 0.0)
           + solve_y(-hxi, 0.0))/hxi**2
    muD = float(np.dot(w, G.Bform(stf, prf, v, Ap(yD))))
    muX = float(np.dot(w, G.Bform(stf, prf, v, Ap(yxx))))
    out(f"  {tag} | {cf[(0,2)]/cf[(0,1)]:+.4e} | {cf[(1,1)]:+.4e} | "
        f"{cf[(3,0)]:+.4e} | {cf[(2,1)]:+.4e} | {cf[(4,0)]:+.4e} | "
        f"{muD:+.4e} | {muX:+.4e}")
    res.append((tag, cf, muD, muX, eqs, c2m,
                cf[(0, 1)], cf[(2, 0)], a0, b0))
out("")
out("  (a,b from the fit vs from the direct formulas -- must agree)")
for tag, cf, muD, muX, eqs, c2m, af, bf, a0, b0 in res:
    out(f"  {tag} | a {af:+.6e} vs {a0:+.6e} ({(af/a0-1)*100:+.3f}%) | "
        f"b {bf:+.6e} vs {b0:+.6e} ({(bf/b0-1)*100:+.3f}%)")
out("")
out("  cell             |  3/8   |   a2    |  be2    |   b4    |  mu_D   |"
    "  mu_xi  |  2nd    | C2_pred | C2_meas |  diff")
for tag, cf, muD, muX, eqs, c2m, af, bf, a0, b0 in res:
    pr_, t = c2_terms(a0, b0, eqs, cf, muD, muX)
    out(f"  {tag} | 0.3750 | {t['a2']:+7.4f} | {t['be2']:+7.4f} | "
        f"{t['b4']:+7.4f} | {t['muD']:+7.4f} | {t['muX']:+7.4f} | "
        f"{t['snd']:+7.4f} | {pr_:7.4f} | {c2m:7.4f} | {pr_-c2m:+7.4f}")
out(f"DONE wall={time.time()-T0:.0f}s")
