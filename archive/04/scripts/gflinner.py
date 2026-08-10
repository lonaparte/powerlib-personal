"""How much does an inner current loop actually move the GFL numbers?

The question "what needs correcting when the inner loop goes in" should be
answered with numbers, not adjectives.  The dominant effect of a current loop
is that the current no longer equals its reference instantly -- it tracks with
a finite bandwidth.  That single effect can be put in with ONE extra state,
without committing to a particular PI/decoupling/feedforward structure:

    4-state:  i_d = i_d* = kpv(1-Vdc) + kiv xi        (algebraic, instantaneous)
    5-state:  di_d/dt = w_c (i_d* - i_d)              (first-order tracking)

w_c -> infinity must return the 4-state model exactly, which is the
consistency check; the RATE at which it returns is the size of the correction.
This is not a full current-loop model (no L filter, no decoupling, no
feedforward, q-axis still a constant reference) and is not presented as one --
it isolates the tracking lag, which is the term that survives in the singular
perturbation and therefore sets the leading correction.

Why this matters more than the 1/w_c ratio suggests: alpha is the SMALL real
part of an eigenvalue whose imaginary part is ~300x larger (alpha/w0 = 0.0031,
Q = w0/2alpha = 162).  A perturbation that changes the Jacobian by O(1/w_c)
can change alpha by O(Q/w_c), i.e. amplified by the quality factor.  If that
is what happens, the inner loop is NOT a small correction to the stability
margin even at high bandwidth, and every threshold that carries alpha moves
with it.  If it is not what happens, that also needs to be shown rather than
assumed.  Reported: P_Hopf, alpha, w0, Re c1, rho_g against w_c/w0.
"""
import math, time
import numpy as np
import sympy as sp
from scipy.linalg import eig
from scipy.optimize import brentq, fsolve

LOG = open('sweep20/gflinner.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

th, xp, Vdc, xi, idl = sp.symbols('th xp Vdc xi idl', real=True)
P_, Q_, V_, Xg_, kp_, ki_, kpv_, kiv_, C_, wc_ = sp.symbols(
    'P Q V Xg kp ki kpv kiv C wc', real=True)
X5 = (th, xp, Vdc, xi, idl)
idref = kpv_*(1 - Vdc) + kiv_*xi
vgd = V_*sp.cos(th) - Xg_*Q_
vgq = -V_*sp.sin(th) + Xg_*idl
f5 = sp.Matrix([kp_*vgq + ki_*xp, vgq,
                (P_ + sp.Rational(3, 2)*(vgd*idl + vgq*Q_)/Vdc)/C_,
                1 - Vdc,
                wc_*(idref - idl)])
PAR = (P_, Q_, V_, Xg_, kp_, ki_, kpv_, kiv_, C_, wc_)
AR = X5 + PAR
f5n = sp.lambdify(AR, f5, 'numpy')
J5n = sp.lambdify(AR, f5.jacobian(sp.Matrix(X5)), 'numpy')
H5 = sp.lambdify(AR, sp.Array([[[sp.diff(f5[i], X5[j], X5[k])
                                 for k in range(5)] for j in range(5)]
                                for i in range(5)]), 'numpy')
T5 = sp.lambdify(AR, sp.Array([[[[sp.diff(f5[i], X5[j], X5[k], X5[l])
                                  for l in range(5)] for k in range(5)]
                                 for j in range(5)] for i in range(5)]),
                 'numpy')
BASE = dict(Q=0.0, V=1.0, Xg=0.5, kp=50.0, ki=1000.0, kpv=1.0, kiv=50.0,
            C=0.01)


def av(x, pr):
    return tuple(x) + (pr['P'], pr['Q'], pr['V'], pr['Xg'], pr['kp'],
                       pr['ki'], pr['kpv'], pr['kiv'], pr['C'], pr['wc'])


def rhs5(x, pr):
    return np.array(f5n(*av(x, pr)), float).ravel()


def jac5(x, pr):
    return np.array(J5n(*av(x, pr)), float)


def eq5(pr):
    """same multi-start protocol as the 4-state equil(), extended by the
    slaved current state i_d = i_d* (which is exact at equilibrium)"""
    def res(x):
        return rhs5(x, pr)
    for t0 in (-0.3, -0.6, -0.9):
        i0 = -pr['P']/(1.5*(pr['V']*math.cos(t0) - pr['Xg']*pr['Q']))
        x0 = np.array([t0, 0.0, 1.0, i0/pr['kiv'], i0])
        z, info, ier, _ = fsolve(res, x0, full_output=True)
        if ier == 1 and np.max(np.abs(res(z))) < 1e-9:
            return z
    return None


def _eqok(pr):
    return eq5(pr) is not None


def crit(pr):
    x = eq5(pr)
    if x is None:
        raise RuntimeError('no equilibrium')
    A = jac5(x, pr)
    ev, VL, VR = eig(A, left=True, right=True)
    k = max((i for i in range(5) if ev[i].imag > 1e-9),
            key=lambda i: ev[i].real)
    lam = ev[k]; q = VR[:, k]
    # c1 is NOT normalisation invariant (q -> s q sends c1 -> |s|^2 c1), and a
    # 5-D unit vector has a different theta-component than a 4-D one, so
    # comparing c1 across dimensions requires fixing a PHYSICAL normalisation.
    # Use the theta component (state 0), which exists in both models.
    q = q/q[0]
    p = VL[:, k]; p = p/np.vdot(q, p)
    return x, A, lam, q, p


def c1_of(pr):
    x, A, lam, q, p = crit(pr)
    a = av(x, pr)
    Hm = np.array(H5(*a), float); Tm = np.array(T5(*a), float)
    B2 = lambda u, v: np.einsum('ijk,j,k->i', Hm, u, v)
    C3 = lambda u, v, w: np.einsum('ijkl,j,k,l->i', Tm, u, v, w)
    w0 = lam.imag
    h11 = np.linalg.solve(A, B2(q, q.conj()))
    h20 = np.linalg.solve(2j*w0*np.eye(5) - A, B2(q, q))
    g21 = np.vdot(p, C3(q, q, q.conj())) - 2*np.vdot(p, B2(q, h11)) \
        + np.vdot(p, B2(q.conj(), h20))
    return lam, (g21/2), q, p


def hopfP(pr):
    """same bracket protocol as the 4-state campaign: scan P over
    [0.05, 0.985] x 3V^2/(4Xg) and take the first sign change of Re lam"""
    Ps = 3*pr['V']**2/(4*pr['Xg'])
    def g(P):
        try:
            return crit(dict(pr, P=P))[2].real
        except Exception:
            return None
    grid = np.linspace(0.05, 0.999, 240)*Ps
    va = [g(P) for P in grid]
    br = None
    for a_, b_, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
        if fa is not None and fb is not None and fa < 0 <= fb:
            br = (a_, b_); break
    if br is None:
        raise RuntimeError('no sign change of Re lam on the grid')
    lo, hi = br
    for _ in range(50):
        m = 0.5*(lo+hi)
        v = g(m)
        if v is None or v < 0: lo = m
        else: hi = m
    return 0.5*(lo+hi)


def marginP(pr, PH, target=0.10):
    lo, hi = 0.5*PH, PH
    def g(P):
        return crit(dict(pr, P=P))[2].real
    for _ in range(45):
        m = 0.5*(lo+hi)
        if g(m) < -target: lo = m
        else: hi = m
    return 0.5*(lo+hi)


out("=== 5-state GFL: inner current loop as a first-order tracking lag")
out("    evaluated at the SAME operating point the 4-state campaign uses")
out("    (P0 = 1.4550001, i.e. margin 0.10 of the 4-state Hopf), so no")
out("    root-finding is involved and the comparison is like-for-like.")
P0 = 1.4550001208424934
# theta-normalised gauge (q/q_theta), so c1 is comparable across dimensions
REF = (1.455154042427857, 0.10000011850620183, 32.39883510867426,
       1894.2878411325446)
out(f"    4-state reference at P0: alpha={REF[1]:.7f}  w0={REF[2]:.5f}  "
    f"Re c1={REF[3]:.6e}  rho_g={math.sqrt(REF[1]/REF[3]):.6e}")
out("")
out("   w_c/w0 |   alpha     | d alpha  |    w0     |  d w0   |   Re c1    "
    "| d Re c1 |   rho_g    | d rho_g")
w0r = REF[2]
rows = []
for fac in (3000.0, 1000.0, 300.0, 100.0, 30.0, 10.0, 5.0, 3.0):
    pr = dict(BASE, P=P0, wc=fac*w0r)
    try:
        lam, c1, q, p = c1_of(pr)
    except Exception as e:
        out(f"   {fac:8.1f} | failed: {e}"); continue
    al = -lam.real; w0 = lam.imag; c1r = c1.real
    rg = math.sqrt(al/c1r) if c1r > 0 and al > 0 else float("nan")
    rg0 = math.sqrt(REF[1]/REF[3])
    rows.append((fac, al, w0, c1r, rg))
    evall = np.linalg.eigvals(jac5(eq5(pr), pr))
    slow = sorted([e for e in evall if abs(e.imag) > 1e-9 and e.imag > 0],
                  key=lambda z: -z.real)[:2]
    out(f"   {fac:8.1f} | {al:.7f} | {(al/REF[1]-1)*100:+8.3f}% | "
        f"{w0:9.5f} | {(w0/REF[2]-1)*100:+7.4f}% | {c1r:.5e} | "
        f"{(c1r/REF[3]-1)*100:+7.3f}% | {rg:.5e} | "
        f"{(rg/rg0-1)*100:+7.3f}%  | modes " +
        ", ".join(f"{e:.3f}" for e in slow))
out("")
out("  the point of the table: alpha is the SMALL real part of an eigenvalue")
out(f"  whose imaginary part is {REF[2]/REF[1]:.0f}x larger, so a lag that")
out("  perturbs the Jacobian by O(w0/w_c) can perturb alpha by O(Q w0/w_c).")
out(f"  Q = w0/(2 alpha) = {REF[2]/(2*REF[1]):.1f}")
out("   w_c/w0 | d alpha/alpha | naive 1/(w_c/w0) | amplification factor")
for fac, al, w0, c1r, rg in rows:
    d = (al/REF[1]-1)*100
    out(f"   {fac:8.1f} | {d:+13.4f}% | {100/fac:16.4f}% | "
        f"{d/(100/fac):+8.1f}x")
out("")
out("=== and the Hopf boundary itself (grid scan, same protocol as 4-state)")
out("   w_c/w0 |   P_Hopf    | shift vs 4-state 1.4551540")
for fac in (3000.0, 300.0, 100.0, 30.0, 10.0):
    pr = dict(BASE, P=P0, wc=fac*w0r)
    try:
        PH = hopfP(pr)
        xh = eq5(dict(pr, P=PH)); evh = np.linalg.eigvals(jac5(xh, dict(pr, P=PH)))
        cr = max((e for e in evh if e.imag > 1e-9), key=lambda z: z.real)
        out(f"   {fac:8.1f} | {PH:.7f} | {(PH/REF[0]-1)*100:+9.4f}%  | "
            f"crossing mode w = {cr.imag:.4f} (4-state crosses at 32.40)")
    except Exception as e:
        out(f"   {fac:8.1f} | not bracketed ({e})")
out(f"DONE wall={time.time()-T0:.0f}s")
