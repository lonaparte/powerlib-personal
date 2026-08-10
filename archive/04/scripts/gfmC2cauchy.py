"""C2 without finite differences: Taylor coefficients by Cauchy contour.

§20.2 stopped with "the machine is right, the application is blocked on
conditioning".  The blocker was specific: the fold-specific part of C2 is a
99% cancellation of O(1) terms, so it needs each Taylor coefficient of the
Lyapunov-Schmidt map to ~0.3%, and third/fourth xi-derivatives by finite
differences do not deliver that (the two step sizes disagreed by 13-15%, and
for two cells the cold Newton solve diverged outright).

Finite differences were the wrong tool, not the wrong idea.  R(xi, D) is
ANALYTIC in both arguments -- it is built from the analytic vector field by
an implicit-function solve -- so its Taylor coefficients are Cauchy
integrals,

    c_mn = (1/(2 pi i)^2) OO R(xi,D) xi^{-m-1} D^{-n-1} dxi dD

evaluated on a torus |xi| = r_x, |D| = r_d by the trapezoid rule, which for
a periodic analytic integrand converges GEOMETRICALLY.  The relative error is
~1e-16 independent of m and n: no cancellation, no step-size tradeoff.  The
only requirement is that the Newton solve for y*(xi,D) converge everywhere on
the torus, which continuation in the radius handles, and that the radius stay
inside the domain of analyticity, which is checked by comparing two radii.

Everything else is unchanged from the machine that was validated on 11
controlled cells.  The lag coefficients come from the same contour applied
to y* itself (mu_D from d y*/dD, mu_xi from d^2 y*/d xi^2), so they are
exact too.
"""
import math, time
import numpy as np
import gfmlib as G
from scipy.linalg import eig

LOG = open('sweep20/gfmC2cauchy.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
SQPI = math.sqrt(math.pi)
TG = np.linspace(-7.0, 7.0, 40001)
WG = np.exp(-TG*TG)


def crhs(st, pr):
    return np.array(G.f_num(*G._av(st, pr)), complex).ravel()


def cjac(st, pr):
    return np.array(G.J_num(*G._av(st, pr)), complex)


def lam2(kap, b3):
    def Phi(t):
        return kap*t*(1.0 - t*t) + b3*t**3
    def PhiX(t):
        return kap*(1.0 - t*t) + 3.0*b3*t*t
    ph = Phi(TG); u = np.zeros_like(TG)
    for i in range(len(TG)):
        if TG[i] <= 0.0:
            s = TG[:i+1]; u[i] = np.trapezoid(np.exp(TG[i]**2 - s*s)*ph[:i+1], s)
        else:
            s = TG[i:]; u[i] = -np.trapezoid(np.exp(TG[i]**2 - s*s)*ph[i:], s)
    return -float(np.trapezoid(WG*(u*u + PhiX(TG)*u), TG))/SQPI


def c2_terms(a, b, eqs, cf, muD, muX, nu=0.03):
    c = eqs*(nu*math.sqrt(2.0*a*b*eqs))**2/2.0
    T = (a*b*c)**-0.25
    def hat(m, n):
        return cf.get((m, n), 0.0)*b**(1-m)*a**(-n)*b**(-n)*T**(2-m-2*n)
    t = dict(a2=-0.75*hat(0, 2)/nu, be2=0.25*hat(2, 1)/nu,
             b4=-0.75*hat(4, 0)/nu, muD=muD/(a*b*T*T)/nu,
             muX=-0.5*muX/(b*b*T*T)/nu, snd=lam2(hat(1, 1), hat(3, 0))/nu)
    return 0.375 + sum(t.values()), t


def Pmax(pr):
    from scipy.optimize import brentq
    h = 1e-6
    def dP(dd):
        return (G.P_of(dd+h, pr) - G.P_of(dd-h, pr))/(2*h)
    dl = np.linspace(0.05, math.pi-0.05, 4000)
    Pv = np.array([G.P_of(dd, pr) for dd in dl])
    i = int(np.argmax(Pv))
    return brentq(dP, dl[max(i-2, 0)], dl[min(i+2, len(dl)-1)],
                  xtol=1e-14, rtol=1e-15), None


def eps_qs_of(pr):
    from scipy.optimize import brentq
    def gap(uu):
        d, _ = Pmax(dict(pr, V=pr['V']-uu))
        return G.P_of(d, dict(pr, V=pr['V']-uu)) - pr['Pref']
    hi = 0.98*pr['V']; n = 0
    while gap(hi) > 0 and n < 40:
        hi = 0.5*(hi + pr['V']); n += 1
    return brentq(gap, 0.0, hi, xtol=1e-14, rtol=1e-15)


CELLS = [('A  M2 Xg=0.5 90%', 'M2', 0.5, 0.90, 0.3612),
         ('B  M3 Xg=0.5 90%', 'M3', 0.5, 0.90, 0.3747),
         ('C  M2 Xg=0.3 75%', 'M2', 0.3, 0.75, 0.3329),
         ('D  M3 Xg=0.3 90%', 'M3', 0.3, 0.90, 0.3940)]
NF = 48
out("=== Taylor coefficients of the LS map by Cauchy contour (N=%d per "
    "circle)" % NF)
res = []
for tag, nm, Xg, frac, c2m in CELLS:
    d0, _ = Pmax(G.mset(nm, Xg=Xg))
    Pm0 = G.P_of(d0, G.mset(nm, Xg=Xg))
    pr = G.mset(nm, Xg=Xg, Pref=frac*Pm0)
    eqs = eps_qs_of(pr)
    prf = dict(pr, V=pr['V']-eqs)
    df, _ = Pmax(prf)
    E = G.E_of(df, prf)
    Qf = (E*E - E*prf['V']*math.cos(df))/prf['Xg']
    stf = np.array([df, 0.0, prf['Pref'], Qf])
    A = np.real(cjac(stf, prf))
    ev_, VL, VR = eig(A, left=True, right=True)
    k = int(np.argmin(np.abs(ev_)))
    v = np.real(VR[:, k]); w = np.real(VL[:, k]); w = w/np.dot(w, v)
    Qm = np.eye(4) - np.outer(v, w)
    Ab = np.vstack([np.hstack([A, v.reshape(4, 1)]),
                    np.hstack([w.reshape(1, 4), np.zeros((1, 1))])])
    def Ap(z):
        return np.linalg.solve(Ab, np.concatenate([z, [0.0]]))[:4]
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

    def solve_y(xi, D, y0, K=1):
        y = np.array(y0, complex)
        for kk in range(1, K+1):
            for _ in range(60):
                x = stf + (kk*xi/K)*v + y
                pq = dict(prf, V=prf['V'] - kk*D/K)
                F = Qm @ crhs(x, pq) + v*np.dot(w, y)
                if np.max(np.abs(F)) < 1e-15:
                    break
                J = Qm @ cjac(x, pq) + np.outer(v, w)
                y = y - np.linalg.solve(J, F)
        return y, float(np.max(np.abs(F)))

    def contour(rx, rd):
        th = 2*np.pi*np.arange(NF)/NF
        Rv = np.zeros((NF, NF), complex)
        Yv = np.zeros((NF, NF, 4), complex)
        bad = 0.0
        for i, t1 in enumerate(th):
            y = np.zeros(4, complex)
            for j, t2 in enumerate(th):
                xi = rx*np.exp(1j*t1); D = rd*np.exp(1j*t2)
                y, r = solve_y(xi, D, y, K=(6 if j == 0 else 1))
                bad = max(bad, r)
                Yv[i, j] = y
                Rv[i, j] = np.dot(w, crhs(stf + xi*v + y,
                                          dict(prf, V=prf['V'] - D)))
        FR = np.fft.fft2(Rv)/(NF*NF)
        FY = np.fft.fft2(Yv, axes=(0, 1))/(NF*NF)
        cf = {(m, n): (FR[m, n]/(rx**m*rd**n)).real
              for m in range(5) for n in range(3)}
        yy = {(m, n): (FY[m, n]/(rx**m*rd**n)).real
              for m in range(3) for n in range(2)}
        return cf, yy, bad
    cfA, yyA, badA = contour(0.25*XS, 0.25*DS)
    cfB, yyB, badB = contour(0.50*XS, 0.50*DS)
    muD = float(np.dot(w, G.Bform(stf, prf, v, Ap(yyA[(0, 1)]))))
    muX = float(np.dot(w, G.Bform(stf, prf, v, Ap(2.0*yyA[(2, 0)]))))
    out(f"  {tag}: eps_qs={eqs:.6e}  Newton res {badA:.1e}/{badB:.1e}")
    out("     coeff |   r = 0.25 scale  |   r = 0.50 scale  |  rel diff")
    for key in ((0, 1), (2, 0), (0, 2), (1, 1), (3, 0), (2, 1), (4, 0)):
        out(f"     c{key} | {cfA[key]:+.9e} | {cfB[key]:+.9e} | "
            f"{(cfB[key]/cfA[key]-1)*100:+.4f}%")
    out(f"     a from contour {cfA[(0,1)]:+.8e} vs direct {a0:+.8e} "
        f"({(cfA[(0,1)]/a0-1)*100:+.5f}%);  b {cfA[(2,0)]:+.8e} vs "
        f"{b0:+.8e} ({(cfA[(2,0)]/b0-1)*100:+.5f}%)")
    res.append((tag, cfA, muD, muX, eqs, c2m, a0, b0))
    out(f"     [{time.time()-T0:.0f}s]")

out("")
out("  cell             |  3/8   |   a2    |  be2    |   b4    |  mu_D   |"
    "  mu_xi  |  2nd    | C2_pred | C2_meas |  diff")
for tag, cf, muD, muX, eqs, c2m, a0, b0 in res:
    pr_, t = c2_terms(a0, b0, eqs, cf, muD, muX)
    out(f"  {tag} | 0.3750 | {t['a2']:+7.4f} | {t['be2']:+7.4f} | "
        f"{t['b4']:+7.4f} | {t['muD']:+7.4f} | {t['muX']:+7.4f} | "
        f"{t['snd']:+7.4f} | {pr_:7.4f} | {c2m:7.4f} | {pr_-c2m:+7.4f}")
out(f"DONE wall={time.time()-T0:.0f}s")
