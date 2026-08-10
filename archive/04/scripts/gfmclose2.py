"""GFM closed form, second pass: the drive moves the boundary, not just the state.

The first pass established the premise and then failed usefully.  Premise:
all five VSM cells have analytic Re c1 < 0, so every one is supercritical,
there is no unstable limit cycle anywhere, and the guard-erosion machinery
has nothing to act on.  The object is the basin boundary -- the stable
manifold of the saddle on the upper branch of P(delta).

The failure is in cell A (M2, Xg=0.5, 90% loaded), and it is systematic:

    w_p/w0   measured    eps_lin = d/|<n,H>|      eps_sep (true basin)
     0.10    1.096e-1    4.296e-1  +292%          4.296e-1  +292%
     0.50    1.478e-1    3.435e-1  +132%          3.430e-1  +132%
     0.90    1.843e-1    2.301e-1   +25%          2.272e-1   +23%
     1.50    5.013e-1    4.189e-1   -16%          3.913e-1   -22%
     3.00    2.064e+0    1.406e+0   -32%          1.158e+0   -44%

eps_sep tracks eps_lin to a few percent everywhere, so the tangent plane IS
the basin boundary to the accuracy needed -- the geometry is right and the
criterion is wrong.  What it gets wrong is visible in the low-frequency
rows: at w_p = 0.1 w0 the measurement (1.096e-1) sits on the quasi-static
fold value eps_qs = 9.94e-2, not on the excursion value.  A slow drive does
not push the state out to a fixed boundary; it drags the boundary in to
meet the state, because the saddle is a function of the instantaneous drive
too.  The criterion used only half of the relative motion.

Both halves have the same form.  The state responds with
H   = (i w_p I - A_0)^{-1} f_u(x_0), the saddle with
H_s = (i w_p I - A_s)^{-1} f_u(x_s), and only their DIFFERENCE closes the
gap.  So define the relative approach transfer function

    s(w) = <n, H(w) - H_s(w)> ,   s_0 = s(0) = <n, -A_0^{-1}f_u + A_s^{-1}f_u> ,

which has the two limits built in: at w -> 0 the boundary follows the drive
fully, at w -> infinity it cannot follow at all and s -> <n,H>.

That still leaves one thing linearisation cannot supply.  Near a fold the
gap closes like a square root, G(u) ~ C sqrt(u_f - u), so extrapolating
linearly from u = 0 lands at about 2 u_f -- a factor-two error at w_p -> 0
no matter how exact the transfer functions are.  The cure is to take the
static fold from the exact static problem rather than from a tangent, and
let the transfer function supply only the frequency dependence:

    eps_uni(w_p) = eps_qs * s_0 / |s(w_p)| .

eps_qs is the exact static fold offset (P_max(V0 - eps_qs) = Pref), so the
w_p -> 0 limit is exact by construction; s_0/|s| is a pure ratio, so the
normalisation of n cancels and nothing is fitted.  Reported alongside
eps_lin (state only) and eps_rel = d/|s| (both, but linear throughout) so
that the two separate defects -- ignoring boundary motion, and linearising
a square root -- can be told apart.
Budget ~40 min.
"""
import math, time
import numpy as np
import gfmlib as G
from scipy.integrate import solve_ivp
from scipy.linalg import eig
LOG = open('sweep20/gfmclose2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
HS = 1e-6
KEY = 'V'


def fu_of(st, pr, key):
    return (G.rhs(st, dict(pr, **{key: pr[key]+HS}))
            - G.rhs(st, dict(pr, **{key: pr[key]-HS})))/(2*HS)


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


def bisect(pred, lo, hi, nit=17):
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
RATS = [0.05, 0.1, 0.3, 0.5, 0.9, 1.5, 3.0]
for tag, nm, Xg, frac in CELLS:
    _, Pm = G.fold(G.mset(nm, Xg=Xg))
    pr = G.mset(nm, Xg=Xg, Pref=frac*Pm)
    st = G.equil(pr); A = G.jac(st, pr)
    lam = G.crit_mode(A); w0 = lam.imag
    c1r = G.hopf_c1(pr)['c1'].real
    xs = G.equil(pr, branch='saddle'); As = G.jac(xs, pr)
    ev, VL, _ = eig(As, left=True, right=True)
    k = int(np.argmax(ev.real))
    nvec = VL[:, k].real.copy(); nvec /= np.linalg.norm(nvec)
    d_geom = float(np.dot(nvec, xs - st))
    if d_geom < 0:
        nvec = -nvec; d_geom = -d_geom
    fu0 = fu_of(st, pr, KEY); fus = fu_of(xs, pr, KEY)
    e_qs = quasi_static(pr, KEY)
    s0 = abs(float(np.dot(nvec, -np.linalg.solve(A, fu0)
                          + np.linalg.solve(As, fus))))
    out(f"=== {tag}: Pref={pr['Pref']:.4f} (P_max={Pm:.4f}) alpha="
        f"{-lam.real:.5f} w0={w0:.4f} Re c1={c1r:+.4e} supercritical="
        f"{c1r < 0}")
    out(f"    delta0={st[0]:.5f} delta_s={xs[0]:.5f} lam_u(saddle)="
        f"{ev[k].real:.4f}  <n,x_s-x_0>={d_geom:.6e}")
    out(f"    eps_qs (exact static fold) = {e_qs:.6e};  s_0 = {s0:.6e};  "
        f"linear-fold estimate d/s_0 = {d_geom/s0:.6e} "
        f"(ratio to eps_qs {d_geom/s0/e_qs:.4f}, sqrt-fold predicts ~2)")
    out("  w_p/w0 | measured    | eps_uni (4)      | eps_rel (2')     | "
        "eps_lin (2)")
    for rat in RATS:
        wp = rat*w0; Td = 2*math.pi/wp
        I = np.eye(4)
        H = np.linalg.solve(1j*wp*I - A, fu0.astype(complex))
        Hs = np.linalg.solve(1j*wp*I - As, fus.astype(complex))
        sw = abs(np.dot(nvec, H - Hs))
        e_lin = d_geom/abs(np.dot(nvec, H))
        e_rel = d_geom/sw
        e_uni = e_qs*s0/sw
        NP = 60 if rat >= 0.5 else 25

        def forced(eps):
            return escaped(pr, st.copy(), NP*Td,
                           lambda t: {KEY: pr[KEY] + eps*math.cos(wp*t)})
        e_m = bisect(forced, 0.6*e_uni, 1.4*e_uni, nit=17)

        def pc(x):
            if not (x == x) or not (e_m == e_m):
                return "    n/a "
            return f"{(x-e_m)/e_m*100:+7.2f}%"
        out(f"   {rat:5.2f} | {e_m:.5e} | {e_uni:.5e} {pc(e_uni)} | "
            f"{e_rel:.5e} {pc(e_rel)} | {e_lin:.5e} {pc(e_lin)}  "
            f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
