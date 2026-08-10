"""The GFM slow-passage residual, second order -- as a formula, not a number.

The record says: leading order eps_c = eps_qs + w_p sqrt(eps_qs/(2ab)) with
lambda* = 1 exactly, residual 0.08 / 0.32 / 1.50% at w_p/w0 = 0.05/0.10/0.30,
and "the next order of the tangential expansion (X' = lambda - tau^2 +
gamma tau^4 + X^2, lambda*(gamma) computable)" left underived.

That framing was too narrow.  gamma tau^4 is ONE of several corrections that
all enter at the SAME order, and there is a single mechanism that produces
all of their contributions in closed form.

The unperturbed inner problem X' = lambda - tau^2 + X^2 has the exact
separatrix X = tau at lambda = 1.  Linearise about it: u' = 2 tau u + ...,
whose homogeneous solution is e^{tau^2} and whose ADJOINT is e^{-tau^2}.
So for ANY perturbation Phi(tau, X) added to the inner equation, the
Fredholm alternative gives the shift of the escape threshold in one line:

    lambda*  =  1 - (1/sqrt(pi)) INT e^{-tau^2} Phi(tau, tau) dtau         (*)

Every correction is now a Gaussian moment, and PARITY does most of the work:
any Phi odd in tau on the separatrix contributes exactly zero.

    Phi = gamma tau^4          (tangential quartic)    -> -3/4 gamma
    Phi = ahat2 (1 - tau^2)^2  (parameter curvature)   -> -3/4 ahat2
    Phi = -2 muhat tau X       (non-adiabatic lag)     -> +muhat
    Phi = b3hat X^3            (fold cubic)            ->  0   (odd)
    Phi = kaphat X (1-tau^2)   (mixed xi*D)            ->  0   (odd)

The two vanishing ones are the terms one would have had to compute by hand;
parity kills them.  What survives is computable from the fold's own data.

Restoring units (nu = w_p / sqrt(2 a b eps_qs) is the ONLY small parameter):

    gamma = nu/6 ,   ahat2 = (a2/a) eps nu ,   muhat = mu eps nu

with, at the fold (V = V0 - eps_qs, right/left null vectors v, w, <w,v> = 1),

    a  = <w, -f_V>                                   (already on record)
    b  = (1/2) <w, B(v,v)>                           (already on record)
    a2 = (1/2) d^2 R / dD^2   from the Lyapunov-Schmidt reduced map R(xi,D)
                              (so it includes the y-feedback terms, not just
                               the bare <w, f_VV>/2)
    mu = <w, B(v, Ap yD)> ,   yD = -Ap Q f_u ,  Q = I - v w^T
                              (Ap = pseudo-inverse on range(A); yD is how the
                               NON-critical states follow the parameter, and
                               Ap yD is how far they LAG behind it)

and one more effect that is not a Phi at all: c = eps w^2/2 is built from the
ACTUAL drive amplitude eps_c, not from eps_qs, so the criterion is implicit.
Solving it to second order,

    delta = (eps_c - eps_qs)/eps_qs = nu + C2 nu^2 + O(nu^3)
    C2 = 3/8 - (3/4)(a2/a) eps_qs + mu eps_qs                            (**)

3/8 = 1/2 (self-consistency) - 1/8 (quartic).  Nothing is fitted; a2 and mu
are computed from the model at the fold.

Two things get tested here.
  Part 1 verifies (*) itself by shooting a perturbed inner equation -- and in
    particular verifies the two PREDICTED ZEROS, which is the sharpest test
    available, since a wrong adjoint would not produce exact zeros.
  Part 3 measures delta(nu) on the full 4-state model at eight drive
    frequencies per cell, precise enough to extract C2, and compares it with
    (**).  A C2 that matches across four cells whose a2/a and mu differ is
    the claim; a C2 that does not is a report, not a patch.

Also fixed here: the fold used a grid argmax (n = 2e5), leaving the zero
eigenvalue at 6e-5 instead of ~1e-10.  a and b were read off a point that
was not quite the fold.  Now the fold is a root of dP/ddelta.
"""
import math, time, sys
import numpy as np
import gfmlib as G
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from scipy.linalg import eig

LOG = open('sweep20/gfmfold2.log', 'w')


def out(m):
    LOG.write(m + '\n'); LOG.flush()


T0 = time.time()
TRAP = np.trapezoid if hasattr(np, 'trapezoid') else np.trapz

# ===================================================================== part 1
out("=== part 1. the solvability formula (*) tested by shooting")
out("    X' = lambda - tau^2 + X^2 + Phi(tau, X),  Phi localised so that the")
out("    unperturbed start at tau = -T0 stays valid")
out("    prediction:  dlambda*/deps = -(1/sqrt(pi)) INT e^{-t^2} Phi(t,t) dt")


def lamstar(Phi=None, T0s=9.0):
    def blows(lam):
        x0 = -math.sqrt(T0s*T0s - lam)

        def f(t, y):
            r = lam - t*t + y[0]*y[0]
            if Phi is not None:
                r = r + Phi(t, y[0])
            return [r]

        def ev(t, y):
            return y[0] - 1e4
        ev.terminal = True; ev.direction = 1
        s = solve_ivp(f, (-T0s, T0s), [x0], method='DOP853', rtol=1e-12,
                      atol=1e-14, events=(ev,))
        return len(s.t_events[0]) > 0 or s.status < 0
    lo, hi = -2.0, 6.0
    for _ in range(70):
        m = 0.5*(lo+hi)
        if blows(m): hi = m
        else: lo = m
    return 0.5*(lo+hi)


def cut(g, tc=4.0):
    return lambda t, x: (g(t, x) if abs(t) < tc else 0.0)


def moment(g, tc=4.0):
    tt = np.linspace(-tc, tc, 400001)
    return -float(TRAP(np.exp(-tt*tt)*np.array([g(t, t) for t in tt]),
                       tt))/math.sqrt(math.pi)


TESTS = [('gamma tau^4        (tangential quartic)', lambda t, x: t**4),
         ('ahat2 (1-tau^2)^2  (parameter curvature)',
          lambda t, x: (1.0 - t*t)**2),
         ('-2 muhat tau X     (non-adiabatic lag)  ', lambda t, x: -2*t*x),
         ('b3hat X^3          (fold cubic)         ', lambda t, x: x**3),
         ('kaphat X (1-tau^2) (mixed xi D)         ', lambda t, x: x*(1-t*t)),
         ('localised probe  e^{-tau^2/2}           ',
          lambda t, x: math.exp(-0.5*t*t)),
         ('localised probe  X e^{-tau^2/2}         ',
          lambda t, x: x*math.exp(-0.5*t*t))]
L0 = lamstar()
out(f"    unperturbed lambda* = {L0:.10f}")
out("    perturbation                             | measured d/deps |"
    " formula (*) | ")
for tag, g in TESTS:
    gg = cut(g)
    hs = [2e-3, -2e-3]
    vals = [lamstar(lambda t, x, e=h, gc=gg: e*gc(t, x)) for h in hs]
    slope = (vals[0]-vals[1])/(hs[0]-hs[1])
    pred = moment(g)
    ok = 'ok' if abs(slope-pred) < 3e-3*max(1.0, abs(pred)) else '<-- MISMATCH'
    out(f"    {tag} | {slope:+15.6f} | {pred:+11.6f} | {ok}")
out(f"    [{time.time()-T0:.0f}s]")

# ===================================================================== part 2
out("")
out("=== part 2. the fold's own second-order data, per cell")


def Pmax(pr):
    """fold of P(delta) as a ROOT of dP/ddelta, not a grid argmax"""
    h = 1e-6

    def dP(d):
        return (G.P_of(d+h, pr) - G.P_of(d-h, pr))/(2*h)
    dl = np.linspace(0.05, math.pi-0.05, 4000)
    Pv = np.array([G.P_of(d, pr) for d in dl])
    i = int(np.argmax(Pv))
    lo, hi = dl[max(i-2, 0)], dl[min(i+2, len(dl)-1)]
    df = brentq(dP, lo, hi, xtol=1e-14, rtol=1e-15)
    return df, G.P_of(df, pr)


def eps_qs_of(pr):
    """exact static fold offset: P_max(V0 - u) = Pref"""
    def gap(u):
        return Pmax(dict(pr, V=pr['V']-u))[1] - pr['Pref']
    lo, hi = 0.0, 0.98*pr['V']
    n = 0
    while gap(hi) > 0 and n < 40:
        hi = 0.5*(hi + pr['V']); n += 1
    return brentq(gap, lo, hi, xtol=1e-14, rtol=1e-15)


def fold_state(pr, eqs):
    prf = dict(pr, V=pr['V']-eqs)
    df, Pm = Pmax(prf)
    E = G.E_of(df, prf)
    Qf = (E*E - E*prf['V']*math.cos(df))/prf['Xg']
    return np.array([df, 0.0, prf['Pref'], Qf]), prf


def null_pair(A):
    ev, VL, VR = eig(A, left=True, right=True)
    k = int(np.argmin(np.abs(ev)))
    v = np.real(VR[:, k]); w = np.real(VL[:, k])
    w = w/np.dot(w, v)
    return v, w, abs(ev[k])


def reduce_LS(stf, prf, v, w, A):
    """Lyapunov-Schmidt: y*(xi,D) solves Q f = 0 with <w,y> = 0; R = <w,f>."""
    Qm = np.eye(4) - np.outer(v, w)

    def solve_y(xi, D, y0=None):
        y = np.zeros(4) if y0 is None else y0.copy()
        for _ in range(60):
            x = stf + xi*v + y
            pq = dict(prf, V=prf['V'] - D)
            F = Qm @ G.rhs(x, pq) + v*np.dot(w, y)
            if np.max(np.abs(F)) < 1e-14:
                break
            J = Qm @ G.jac(x, pq) + np.outer(v, w)
            y = y - np.linalg.solve(J, F)
        return y

    def R(xi, D):
        return float(np.dot(w, G.rhs(stf + xi*v + solve_y(xi, D),
                                     dict(prf, V=prf['V'] - D))))
    return R


CELLS = [('A  M2 Xg=0.5 90%', 'M2', 0.5, 0.90),
         ('B  M3 Xg=0.5 90%', 'M3', 0.5, 0.90),
         ('C  M2 Xg=0.3 75%', 'M2', 0.3, 0.75),
         ('D  M3 Xg=0.3 90%', 'M3', 0.3, 0.90)]
DAT = {}
out("  cell             |   eps_qs   | |zero ev| |     a      |     b      "
    "|    a2/a    |     mu     |   C2_pred")
for tag, nm, Xg, frac in CELLS:
    _, Pm0 = Pmax(G.mset(nm, Xg=Xg))
    pr = G.mset(nm, Xg=Xg, Pref=frac*Pm0)
    st = G.equil(pr)
    w0 = G.crit_mode(G.jac(st, pr)).imag
    eqs = eps_qs_of(pr)
    stf, prf = fold_state(pr, eqs)
    A = G.jac(stf, prf)
    v, w, zev = null_pair(A)
    R = reduce_LS(stf, prf, v, w, A)
    hD = 2e-4*max(eqs, 1e-3)
    hx = 2e-3
    a = (R(0.0, hD) - R(0.0, -hD))/(2*hD)
    a4 = (R(0.0, 2*hD) - R(0.0, -2*hD))/(4*hD)
    a = (4*a - a4)/3.0
    a2 = 0.5*(R(0.0, hD) - 2*R(0.0, 0.0) + R(0.0, -hD))/hD**2
    a2b = 0.5*(R(0.0, 2*hD) - 2*R(0.0, 0.0) + R(0.0, -2*hD))/(4*hD**2)
    a2 = (4*a2 - a2b)/3.0
    b = 0.5*(R(hx, 0.0) - 2*R(0.0, 0.0) + R(-hx, 0.0))/hx**2
    bb = 0.5*(R(2*hx, 0.0) - 2*R(0.0, 0.0) + R(-2*hx, 0.0))/(4*hx**2)
    b = (4*b - bb)/3.0
    # mu: how far the non-critical states LAG the parameter
    HS = 1e-6
    fV = (G.rhs(stf, dict(prf, V=prf['V']+HS))
          - G.rhs(stf, dict(prf, V=prf['V']-HS)))/(2*HS)
    fu = -fV
    Qm = np.eye(4) - np.outer(v, w)
    Ab = np.vstack([np.hstack([A, v.reshape(4, 1)]),
                    np.hstack([w.reshape(1, 4), np.zeros((1, 1))])])

    def Ap(z):
        s = np.linalg.solve(Ab, np.concatenate([z, [0.0]]))
        return s[:4]
    yD = -Ap(Qm @ fu)
    mu = float(np.dot(w, G.Bform(stf, prf, v, Ap(yD))))
    C2 = 0.375 - 0.75*(a2/a)*eqs + mu*eqs
    DAT[tag] = dict(pr=pr, st=st, w0=w0, eqs=eqs, a=a, b=b, a2=a2, mu=mu,
                    C2=C2, ab=abs(a*b))
    out(f"  {tag} | {eqs:.6e} | {zev:.2e} | {a:+.4e} | {b:+.4e} | "
        f"{a2/a:+.4e} | {mu:+.4e} | {C2:+9.4f}")
out(f"    [{time.time()-T0:.0f}s]")

# ===================================================================== part 3
out("")
out("=== part 3. delta(nu) measured on the full 4-state model")
out("    V(t) = V0 + eps cos(w_p t); state starts at the UNFORCED")
out("    equilibrium (the protocol the recorded eps_c used)")
RATS = [0.02, 0.03, 0.05, 0.075, 0.10, 0.15, 0.20, 0.30]
NPER = 2.2


def escaped(pr, x0, eps, wp, dsad, nper=NPER):
    Tend = nper*2*math.pi/wp

    def fun(t, x):
        return G.rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))

    def ev(t, x):
        return x[0] - dsad
    ev.terminal = True; ev.direction = 1
    s = solve_ivp(fun, (0.0, Tend), x0, method='DOP853', rtol=1e-11,
                  atol=1e-13, events=(ev,))
    return len(s.t_events[0]) > 0


def thr(pr, x0, wp, dsad, eqs, nit=34):
    lo, hi = eqs*(1.0 + 1e-6), eqs*1.60
    if escaped(pr, x0, lo, wp, dsad):
        return float('nan')
    n = 0
    while not escaped(pr, x0, hi, wp, dsad) and n < 8:
        lo = hi; hi *= 1.3; n += 1
    if not escaped(pr, x0, hi, wp, dsad):
        return float('nan')
    for _ in range(nit):
        m = 0.5*(lo+hi)
        if escaped(pr, x0, m, wp, dsad):
            hi = m
        else:
            lo = m
    return 0.5*(lo+hi)


out("  cell |  w_p/w0 |    nu    |   eps_c      |  delta    | delta/nu | "
    "1+C2nu(pred)")
RES = {}
for tag, nm, Xg, frac in CELLS:
    d = DAT[tag]
    pr = d['pr']; st = d['st']; eqs = d['eqs']; w0 = d['w0']
    xs = G.equil(pr, branch='saddle'); dsad = xs[0]
    rows = []
    for r in RATS:
        wp = r*w0
        nu = wp/math.sqrt(2.0*d['ab']*eqs)
        ec = thr(pr, st, wp, dsad, eqs)
        dl = ec/eqs - 1.0
        rows.append((r, nu, ec, dl))
        out(f"   {tag[0]}   |  {r:.3f}  | {nu:.5f} | {ec:.7e} | {dl:.6f} | "
            f"{dl/nu:.5f} | {1.0 + d['C2']*nu:.5f}   [{time.time()-T0:.0f}s]")
    RES[tag] = rows
out("")
out("=== C2 extracted from the measurement vs C2 predicted from the fold")
out("  fit delta/nu = 1 + C2 nu + C3 nu^2 over the four smallest nu")
out("  cell             | C2_meas  | C2_pred  | diff     | "
    "leading-order err at largest nu | with C2")
for tag, nm, Xg, frac in CELLS:
    rows = [rw for rw in RES[tag] if rw[3] == rw[3]]
    if len(rows) < 4:
        out(f"  {tag} | insufficient points"); continue
    nu = np.array([rw[1] for rw in rows]); dl = np.array([rw[3] for rw in rows])
    y = dl/nu - 1.0
    k = 4
    M = np.vstack([nu[:k], nu[:k]**2]).T
    cf = np.linalg.lstsq(M, y[:k], rcond=None)[0]
    d = DAT[tag]
    e1 = (nu[-1]/dl[-1] - 1.0)*100
    e2 = (nu[-1]*(1.0 + d['C2']*nu[-1])/dl[-1] - 1.0)*100
    out(f"  {tag} | {cf[0]:+8.4f} | {d['C2']:+8.4f} | "
        f"{cf[0]-d['C2']:+8.4f} | {e1:+30.2f}% | {e2:+7.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
