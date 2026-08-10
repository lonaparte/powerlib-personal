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

LOG = open('sweep20/gfmC2b.log', 'w')


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


# ===================================================================== part 2
out("=== part 2. lag terms: 2-state control with everything in closed form")
out("    xdot = a D + b x^2 + c12 x y ,  ydot = -lf y + d D + e x^2")
EQS = 0.2


def two_esc(pars, u, nu):
    a, b, c12, lf, d, e = pars
    w = nu*math.sqrt(2.0*a*b*EQS)

    def D(s):
        return u*EQS*math.cos(s) - EQS

    def R(x, Dv):
        return a*Dv + b*x*x + (c12*d/lf)*x*Dv + (c12*e/lf)*x**3
    D0 = D(-math.pi)
    x0 = stable_root(lambda x: R(x, D0), D0, math.sqrt(abs(a*D0/b)))
    y0 = (d*D0 + e*x0*x0)/lf

    def f(s, z):
        Dv = D(s)
        return [(a*Dv + b*z[0]**2 + c12*z[0]*z[1])/w,
                (-lf*z[1] + d*Dv + e*z[0]**2)/w]

    def ev(s, z):
        return z[0] - 5.0
    ev.terminal = True; ev.direction = 1
    r = solve_ivp(f, (-math.pi, math.pi), [x0, y0], method='DOP853',
                  rtol=1e-12, atol=1e-15, events=(ev,))
    return len(r.t_events[0]) > 0 or r.status < 0


def two_C2(pars, nu):
    lo, hi = 1.0 + 0.5*nu, 1.0 + 2.0*nu + 6.0*nu*nu
    n = 0
    while two_esc(pars, lo, nu) and n < 30:
        hi = lo; lo = 1.0 + 0.5*(lo - 1.0); n += 1
    n = 0
    while not two_esc(pars, hi, nu) and n < 30:
        lo = hi; hi = 1.0 + 1.6*(hi - 1.0); n += 1
    for _ in range(46):
        m = 0.5*(lo+hi)
        if two_esc(pars, m, nu): hi = m
        else: lo = m
    d = 0.5*(lo+hi) - 1.0
    return (d/nu - 1.0)/nu


out("  a  b  c12  lf   d    e   | C2_meas(.02/.03/.05)->0 | C2_pred | "
    "(muD,muX,2nd) | diff")
CASES = [(1.0, 1.0, 1.0, 3.0, 1.0, 0.0),
         (1.0, 1.0, 1.0, 1.0, 1.0, 0.0),
         (1.0, 1.0, 1.0, 3.0, 0.0, 1.0),
         (1.0, 1.0, 1.0, 1.0, 0.0, 1.0),
         (1.0, 1.0, -1.5, 2.0, 1.0, 1.0),
         (1.0, 1.0, 1.0, 0.7, 1.0, 1.0)]
for pars in CASES:
    a, b, c12, lf, d, e = pars
    cf = {(0, 1): a, (2, 0): b, (1, 1): c12*d/lf, (3, 0): c12*e/lf}
    muD = -c12*d/lf**2
    muX = -2.0*c12*e/lf**2
    ms = [two_C2(pars, nu) for nu in (0.02, 0.03, 0.05)]
    m0 = float(np.polyfit([0.02, 0.03, 0.05], ms, 1)[1])
    pr, t = c2_terms(a, b, EQS, cf, muD, muX)
    out(f"  {a:.1f} {b:.1f} {c12:+.1f} {lf:.1f} {d:.1f} {e:.1f} | "
        f"{ms[0]:6.4f}/{ms[1]:6.4f}/{ms[2]:6.4f} -> {m0:7.4f} | {pr:7.4f} | "
        f"({t['muD']:+.3f},{t['muX']:+.3f},{t['snd']:+.3f}) | {m0-pr:+7.4f}"
        f"   [{time.time()-T0:.0f}s]")

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

    def solve_y(xi, D, y0=None):
        y = np.zeros(4) if y0 is None else y0.copy()
        for _ in range(80):
            x = stf + xi*v + y
            pq = dict(prf, V=prf['V'] - D)
            F = Qm @ G.rhs(x, pq) + v*np.dot(w, y)
            if np.max(np.abs(F)) < 1e-15:
                break
            J = Qm @ G.jac(x, pq) + np.outer(v, w)
            y = y - np.linalg.solve(J, F)
        return y

    def R(xi, D):
        return float(np.dot(w, G.rhs(stf + xi*v + solve_y(xi, D),
                                     dict(prf, V=prf['V'] - D))))
    # fit box: the inner scales at a representative nu
    nu0 = 0.05
    HS = 1e-6
    fV = (G.rhs(stf, dict(prf, V=prf['V']+HS))
          - G.rhs(stf, dict(prf, V=prf['V']-HS)))/(2*HS)
    a0 = float(np.dot(w, -fV))
    b0 = 0.5*float(np.dot(w, G.Bform(stf, prf, v, v)))
    ab = a0*b0
    c0 = eqs*(nu0*math.sqrt(2*ab*eqs))**2/2.0
    Tt = (ab*c0)**-0.25
    def fit(box):
        hx = box/abs(b0*Tt); hd = box/abs(ab*Tt*Tt)
        NX = 15
        xs = np.linspace(-hx, hx, NX); ds = np.linspace(-hd, hd, NX)
        XX, DD = np.meshgrid(xs, ds, indexing='ij')
        RR = np.array([[R(XX[i, j], DD[i, j]) for j in range(NX)]
                       for i in range(NX)])
        terms = [(m, n) for m in range(7) for n in range(5) if 0 < m+n <= 6]
        M = np.array([[(XX[i, j]/hx)**m*(DD[i, j]/hd)**n for (m, n) in terms]
                      for i in range(NX) for j in range(NX)])
        sol = np.linalg.lstsq(M, RR.ravel(), rcond=None)[0]
        return {(m, n): sol[i]/hx**m/hd**n for i, (m, n) in enumerate(terms)}
    cf = fit(1.0); cfh = fit(0.5)
    out("      box 1.0 vs 0.5 inner scale (must agree if the fit is a "
        "Taylor coefficient and not a fit artefact):")
    for key in ((0, 1), (2, 0), (0, 2), (1, 1), (3, 0), (2, 1), (4, 0)):
        out(f"        c{key} = {cf[key]:+.6e} vs {cfh[key]:+.6e}  "
            f"({(cfh[key]/cf[key]-1)*100:+.3f}%)")
    yD = -Ap(Qm @ (-fV))
    hxi = 0.02*hx
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
