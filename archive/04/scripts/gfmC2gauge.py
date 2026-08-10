"""Finish C2: every O(nu) term, validated on a case where the answer is known.

19.2 stopped at "the terms are enumerated, the closed forms are written, but
evaluating them is not done".  That is a named absence again.  It is also the
place where I already got burned once: a PARTIAL sum of the same list was off
by two orders of magnitude, because the split is gauge dependent.  So the
only acceptable way to finish is (i) assemble the WHOLE list and (ii) test
the assembled machine on a system whose C2 can be measured directly and
whose coefficients are known exactly -- before pointing it at the GFM.

Scaling fixes the list.  A monomial c_mn xi^m D^n in the reduced equation
becomes, after xi = X/(bT), t = T tau, T = (abc)^{-1/4}, D = D_s(lam - tau^2),
D_s = 1/(a b T^2),

    chat_mn = c_mn b^{1-m} a^{-n} b^{-n} T^{2-m-2n} ,   T^{-2} = nu a b eps

so its order in nu is (m + 2n - 2)/2.  Exactly at O(nu):

  first order in perturbation theory   (m,n) = (0,2), (2,1), (4,0)
  second order (coefficients ~ nu^1/2) (m,n) = (1,1), (3,0)
  plus two terms that are not monomials in (xi, D) at all -- the LAG of the
  non-critical states, which is what makes this a reduction of a 4-state
  system rather than a scalar model:
      mu_D xi Ddot      from  y = y* + Ap dy*/dD Ddot
      mu_xi xi^2 xidot  from  y = y* + Ap dy*/dxi xidot

First-order contributions come straight from the solvability formula (*)
as Gaussian moments:

    (0,2) -> -3/4 chat      (2,1) -> +1/4 chat      (4,0) -> -3/4 chat
    xi Ddot -> +muhat_D     xi^2 xidot -> -1/2 muhat_xi

Second order needs one more line of perturbation theory.  With
X = tau + u + w, lambda = 1 + lambda_1 + lambda_2 and Phi odd (so
lambda_1 = 0):

    u' = 2 tau u + Phi(tau,tau)
    w' = 2 tau w + lambda_2 + u^2 + Phi_X(tau,tau) u
    ==> lambda_2 = -(1/sqrt(pi)) INT e^{-tau^2} [u^2 + Phi_X u] dtau ,
        u(tau) = INT_{-inf}^{tau} e^{tau^2 - s^2} Phi(s,s) ds

(written as e^{tau^2-s^2} inside the integral, not e^{tau^2} times a tiny
number, or it cancels to noise).

PART 1 is the control: a purely SCALAR system with the seven coefficients set
by hand, where mu_D = mu_xi = 0 and C2 can be measured by bisection to five
digits.  If the assembled formula does not reproduce that, the static half of
the list is wrong and nothing else matters.
PART 2 adds a fast stable mode with known coupling, so mu_D and mu_xi are
known in closed form and can be checked the same way.
PART 3 only then points the machine at the four GFM cells, where the target
is C2_meas = 0.361 / 0.375 / 0.333 / 0.394 against the universal 3/8.
"""
import math, time
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

LOG = open('sweep20/gfmC2gauge.log', 'w')


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
TG = np.linspace(-7.0, 7.0, 60001)
WG = np.exp(-TG*TG)


def lam2(kap, b3):
    """second-order shift from the two O(nu^1/2) perturbations"""
    def Phi(t):
        return kap*t*(1.0 - t*t) + b3*t**3

    def PhiX(t):
        return kap*(1.0 - t*t) + 3.0*b3*t*t
    ph = Phi(TG)
    u = np.zeros_like(TG)
    # tau <= 0 : integrate from -inf ; tau > 0 : minus integral to +inf
    neg = TG <= 0.0
    for i in np.where(neg)[0]:
        s = TG[:i+1]
        u[i] = np.trapezoid(np.exp(TG[i]**2 - s*s)*ph[:i+1], s)
    for i in np.where(~neg)[0]:
        s = TG[i:]
        u[i] = -np.trapezoid(np.exp(TG[i]**2 - s*s)*ph[i:], s)
    return -float(np.trapezoid(WG*(u*u + PhiX(TG)*u), TG))/SQPI


def c2_predict(a, b, eqs, cf, muD=0.0, muX=0.0, nu=0.05):
    """cf: dict (m,n) -> c_mn of the reduced map.  Returns C2 - 3/8."""
    c = eqs*(nu*math.sqrt(2.0*a*b*eqs))**2/2.0      # c = eps w^2/2
    T = (a*b*c)**-0.25

    def hat(m, n):
        return cf.get((m, n), 0.0)*b**(1-m)*a**(-n)*b**(-n)*T**(2-m-2*n)
    first = (-0.75*hat(0, 2) + 0.25*hat(2, 1) - 0.75*hat(4, 0)
             + muD/(a*b*T*T) - 0.5*muX/(b*b*T*T))
    second = lam2(hat(1, 1), hat(3, 0))
    return (first + second)/nu, first/nu, second/nu


# ===================================================================== part 1
out("=== part 1b. gauge invariance + all terms at once")
out("    xi -> xi + sigma D maps the pure fold onto a2 = b sigma^2,")
out("    kap = 2 b sigma.  C2 must come back 0.3750 unchanged: a2 enters at")
out("    FIRST order and kap only at SECOND, so this is the sharpest test")
out("    that the two halves of the machine are consistent.")
out("    xidot = a D + b xi^2 + a2 D^2 + kap xi D + b3 xi^3 + be2 xi^2 D"
    " + b4 xi^4")
out("    D(t) = eps cos(w t) - eps_qs,  a = b = 1, eps_qs = 0.2")
out("    (eps_qs small so the polynomial keeps its fold structure over the")
out("     whole cycle: |D| <= 2 eps_qs, so the extra terms never dominate aD)")
EQS = 0.2


def toy_R(xi, D, cf):
    r = 0.0
    for (m, n), c in cf.items():
        r += c*xi**m*D**n
    return r


def toy_esc(cf, u, nu):
    """u = eps/eps_qs is the RATIO; the absolute amplitude is u*EQS"""
    w = nu*math.sqrt(2.0*EQS)

    def D(s):
        return u*EQS*math.cos(s) - EQS

    x0 = stable_root(lambda x: toy_R(x, D(-math.pi), cf), D(-math.pi),
                     math.sqrt(abs(D(-math.pi))))
    if not np.isfinite(x0):
        raise RuntimeError('no quasi-static branch at the deepest raise: the '
                           'polynomial has left its domain of validity')

    def f(s, y):
        return [toy_R(y[0], D(s), cf)/w]

    def ev(s, y):
        return y[0] - 5.0
    ev.terminal = True; ev.direction = 1
    r = solve_ivp(f, (-math.pi, math.pi), [x0], method='DOP853', rtol=1e-12,
                  atol=1e-15, events=(ev,))
    return len(r.t_events[0]) > 0 or r.status < 0


def toy_C2(cf, nu):
    lo, hi = 1.0 + 0.5*nu, 1.0 + 2.0*nu + 6.0*nu*nu
    n = 0
    while toy_esc(cf, lo, nu) and n < 30:
        hi = lo; lo = 1.0 + 0.5*(lo - 1.0); n += 1
    n = 0
    while not toy_esc(cf, hi, nu) and n < 30:
        lo = hi; hi = 1.0 + 1.6*(hi - 1.0); n += 1
    for _ in range(46):
        m = 0.5*(lo+hi)
        if toy_esc(cf, m, nu): hi = m
        else: lo = m
    d = 0.5*(lo+hi) - 1.0
    return (d/nu - 1.0)/nu


BASE = {(0, 1): 1.0, (2, 0): 1.0}
TOYS = [('gauge: shift sigma=0.4  ', {(0, 2): 0.16, (1, 1): 0.8}),
        ('gauge: shift sigma=-0.7 ', {(0, 2): 0.49, (1, 1): -1.4}),
        ('all five, moderate      ', {(0, 2): 0.5, (2, 1): 0.6, (4, 0): 0.5,
                                      (1, 1): -0.6, (3, 0): 0.3})]
out("  extra terms              | C2_meas(nu=.02/.03/.05) | C2_pred | "
    "(1st,2nd) | diff")
for tag, extra in TOYS:
    cf = dict(BASE)
    for k, v in extra.items():
        cf[k] = cf.get(k, 0.0) + v if k != (2, 0) else v
    ms = [toy_C2(cf, nu) for nu in (0.02, 0.03, 0.05)]
    # extrapolate linearly in nu to nu -> 0
    A = np.polyfit([0.02, 0.03, 0.05], ms, 1)
    m0 = A[1]
    pr, p1, p2 = c2_predict(1.0, cf[(2, 0)], EQS, cf, nu=0.03)
    pr += 0.375
    out(f"  {tag} | {ms[0]:7.4f}/{ms[1]:7.4f}/{ms[2]:7.4f} -> {m0:7.4f} | "
        f"{pr:7.4f} | ({p1:+.3f},{p2:+.3f}) | {m0-pr:+7.4f}   "
        f"[{time.time()-T0:.0f}s]")
out(f"    [{time.time()-T0:.0f}s]")
