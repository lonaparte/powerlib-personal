"""A closed form for the GFM side, where there is no local guard.

The GFL closed form is built on a subcritical Hopf: the guard is the
unstable limit cycle at rho_g, the drive erodes it, escape is local.  A
first pass over the five VSM cells settles the premise -- Re c1 is negative
in all five (M1 -3.1e-3, M2 -4.6e-3, M3 -1.3e-3, M4 -1.2e-2, M5 -4.6e-3),
so every one of them is supercritical and there is no unstable limit cycle
anywhere for the drive to erode.  The construction has nothing to act on
and must be replaced, not adapted.

What replaces it is the basin boundary of the stable equilibrium: the
stable manifold of the saddle on the upper branch of P(delta).  The
mechanism is B3 -- the forced orbit grows until it reaches a boundary that
itself barely moves.  Three predictions, increasing in content, none fitted:

 (1) quasi-static limit, w_p -> 0.  The drive is then a slow parameter
     sweep and escape is the disappearance of the equilibrium:
         eps_qs = V0 - V*,   P_max(V*) = Pref .
     No dynamics at all.

 (2) resonant excursion against the tangent plane.  With x_s the saddle,
     A_s its Jacobian, n the left eigenvector of A_s for the unstable real
     eigenvalue, the boundary is { <n, x - x_s> = 0 } to first order.  The
     linear forced orbit is x_0 + eps Re[H e^{i w_p t}],
     H = (i w_p I - A_0)^{-1} f_u, with largest signed excursion along n
     equal to eps |<n,H>|.  Hence
         eps_lin = <n, x_s - x_0> / |<n,H>| .

 (3) second-order rectification.  A symmetric drive is not mean-preserving:
     the quadratic response has a DC part that displaces both the operating
     point and the saddle,
         y_DC = -A^{-1}[2|a|^2 B(H,Hbar) + 4|a|^2 M1 Re H + 2|a|^2 f_uu],
     M1 = d^2f/dy du, a = eps/2.  Replacing the numerator of (2) by
     <n, (x_s + y_DC^s) - (x_0 + y_DC^0)> makes eps the root of a quadratic.
     This is the GFM analogue of erosion: not a shrinking guard, a closing
     gap.

Geometry is separated from dynamics by also measuring the true basin
distance along the forced excursion locus: bisect eps such that some point
of { x_0 + eps Re[H e^{i w_p t}] } already lies outside the basin under the
UNFORCED flow.  The gap from there to the fully forced threshold is what
the drive adds beyond geometry; the gap to (2) is the curvature of the
stable manifold.

Cells are chosen so that both branches are in play at a comparable drive
level (weak enough grid, loaded to 0.75-0.9 of the fold), otherwise the
test is uninformative:
    A: M2 Xg=0.5 Pref=0.90 P_max    B: M3 Xg=0.5 Pref=0.90 P_max
    C: M2 Xg=0.3 Pref=0.75 P_max    D: M3 Xg=0.3 Pref=0.90 P_max
Budget ~45 min.
"""
import math, time
import numpy as np
import gfmlib as G
from scipy.integrate import solve_ivp
from scipy.linalg import eig
LOG = open('sweep20/gfmclose.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
HS = 1e-6
KEY = 'V'


def fu_of(st, pr, key):
    return (G.rhs(st, dict(pr, **{key: pr[key]+HS}))
            - G.rhs(st, dict(pr, **{key: pr[key]-HS})))/(2*HS)


def M1_of(st, pr, key):
    return (G.jac(st, dict(pr, **{key: pr[key]+HS}))
            - G.jac(st, dict(pr, **{key: pr[key]-HS})))/(2*HS)


def fuu_of(st, pr, key):
    return (G.rhs(st, dict(pr, **{key: pr[key]+HS}))
            - 2*G.rhs(st, pr)
            + G.rhs(st, dict(pr, **{key: pr[key]-HS})))/HS**2


def dc_shift(st, pr, key, H):
    A = G.jac(st, pr)
    B = lambda u, v: G.Bform(st, pr, u, v)
    src = (2*np.real(B(H, np.conj(H))) + 4*(M1_of(st, pr, key) @ np.real(H))
           + 2*fuu_of(st, pr, key))
    return -np.linalg.solve(A, src)


def escaped(pr, x0, T, drive=None):
    dlim = math.pi + 0.20

    def f(t, x):
        return G.rhs(x, pr if drive is None else dict(pr, **drive(t)))

    def ev(t, x):
        return x[0] - dlim
    ev.terminal = True; ev.direction = 1
    s = solve_ivp(f, (0, T), x0, method='DOP853', rtol=1e-9, atol=1e-12,
                  events=(ev,))
    return len(s.t_events[0]) > 0 or s.status < 0


def bisect(pred, lo, hi, nit=16):
    n = 0
    while not pred(hi) and n < 12:
        lo = hi; hi *= 1.35; n += 1
    n = 0
    while pred(lo) and n < 12:
        hi = lo; lo *= 0.7; n += 1
    if pred(lo) or not pred(hi):
        return float('nan')
    for _ in range(nit):
        m = 0.5*(lo+hi)
        if pred(m): hi = m
        else: lo = m
    return 0.5*(lo+hi)


def quasi_static(pr, key='V'):
    def gapf(u):
        q = dict(pr, **{key: pr[key]-u})
        try:
            _, Pm = G.fold(q)
        except Exception:
            return 1.0
        return pr['Pref'] - Pm
    lo, hi = 0.0, 0.999*pr[key]
    if gapf(hi) < 0:
        return float('nan')
    for _ in range(70):
        m = 0.5*(lo+hi)
        if gapf(m) > 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)


CELLS = [('A  M2 Xg=0.5 90%', 'M2', 0.5, 0.90),
         ('B  M3 Xg=0.5 90%', 'M3', 0.5, 0.90),
         ('C  M2 Xg=0.3 75%', 'M2', 0.3, 0.75),
         ('D  M3 Xg=0.3 90%', 'M3', 0.3, 0.90)]
RATS = [0.1, 0.5, 0.9, 1.5, 3.0]
for tag, nm, Xg, frac in CELLS:
    _, Pm = G.fold(G.mset(nm, Xg=Xg))
    pr = G.mset(nm, Xg=Xg, Pref=frac*Pm)
    st = G.equil(pr); A = G.jac(st, pr)
    lam = G.crit_mode(A); w0 = lam.imag
    c1r = G.hopf_c1(pr)['c1'].real
    xs = G.equil(pr, branch='saddle')
    As = G.jac(xs, pr)
    ev, VL, _ = eig(As, left=True, right=True)
    k = int(np.argmax(ev.real))
    nvec = VL[:, k].real.copy(); nvec /= np.linalg.norm(nvec)
    d_geom = float(np.dot(nvec, xs - st))
    if d_geom < 0:
        nvec = -nvec; d_geom = -d_geom
    fu = fu_of(st, pr, KEY)
    e_qs = quasi_static(pr, KEY)
    Tn = 2*math.pi/w0
    out(f"=== {tag}: Pref={pr['Pref']:.4f} (P_max={Pm:.4f}) alpha="
        f"{-lam.real:.5f} w0={w0:.4f} Re c1={c1r:+.4e} (supercritical="
        f"{c1r < 0})")
    out(f"    delta0={st[0]:.5f} delta_s={xs[0]:.5f} lam_u(saddle)="
        f"{ev[k].real:.4f} (imag {ev[k].imag:.1e})")
    out(f"    <n, x_s - x_0> = {d_geom:.6e}   eps_qs = {e_qs:.6e}  "
        f"[{time.time()-T0:.0f}s]")
    out("  w_p/w0 | measured    | eps_lin (2)      | +DC (3)          | "
        "eps_sep (geometry)")
    for rat in RATS:
        wp = rat*w0; Td = 2*math.pi/wp
        I = np.eye(4)
        H = np.linalg.solve(1j*wp*I - A, fu.astype(complex))
        exc = abs(np.dot(nvec, H))
        e_lin = d_geom/exc
        d0 = dc_shift(st, pr, KEY, H)
        Hs = np.linalg.solve(1j*wp*I - As, fu_of(xs, pr, KEY).astype(complex))
        ds = dc_shift(xs, pr, KEY, Hs)
        kdc = float(np.dot(nvec, ds - d0))

        def gap(eps):
            return eps*exc - (d_geom + kdc*0.25*eps*eps)
        lo, hi = 1e-10, 60*e_lin
        e_dc = float('nan')
        if gap(hi) > 0:
            for _ in range(200):
                m = 0.5*(lo+hi)
                if gap(m) > 0: hi = m
                else: lo = m
            e_dc = 0.5*(lo+hi)

        def outside(eps):
            for t in np.linspace(0, Td, 17)[:-1]:
                x = st + eps*np.real(H*np.exp(1j*wp*t))
                if escaped(pr, x, 40*Tn):
                    return True
            return False
        e_sep = bisect(outside, 0.6*e_lin, 1.4*e_lin, nit=13)

        NP = 60 if rat >= 0.5 else 20

        def forced(eps):
            return escaped(pr, st.copy(), NP*Td,
                           lambda t: {KEY: pr[KEY] + eps*math.cos(wp*t)})
        seed = e_sep if e_sep == e_sep else e_lin
        e_m = bisect(forced, 0.6*seed, 1.4*seed, nit=17)

        def pc(x):
            if not (x == x) or not (e_m == e_m):
                return "   n/a "
            return f"{(x-e_m)/e_m*100:+7.2f}%"
        out(f"   {rat:5.2f} | {e_m:.5e} | {e_lin:.5e} {pc(e_lin)} | "
            f"{e_dc:.5e} {pc(e_dc)} | {e_sep:.5e} {pc(e_sep)}  "
            f"[{time.time()-T0:.0f}s]")
    out(f"    (eps_qs = {e_qs:.5e} is the w_p -> 0 limit; compare the "
        f"rat=0.1 row)")
out(f"DONE wall={time.time()-T0:.0f}s")
