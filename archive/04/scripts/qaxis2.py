"""Two things the first pass left open, both of them substantive.

(1) The 8-state Q-channel threshold does NOT converge to the 6-state one as
    w_c -> infinity: the ratio settles at 0.9835 (r=0.60), 0.9948 (r=0.90).
    A leftover at infinite bandwidth cannot be a bandwidth effect.  The
    candidate explanation is that the erosion machinery treats a drive as
    ADDITIVE -- f(x, Q0+u) ~ f(x,Q0) + f_u u -- and therefore drops the mixed
    derivatives f_ux, f_uu, f_uxx, ... .  Promoting i_q to a state puts those
    terms back automatically, because then the drive multiplies states inside
    the vector field instead of being appended to it.  If that is the whole
    story, then extending the 6-state c_x with the mixed (state x drive)
    tensors must reproduce the 8-state number in the large-w_c limit.  That is
    a sharp test and it is run here.

    Extended forms: treat u as an extra coordinate with no dynamics.
        Btil(Y,Z)_i = sum_{j,k in states+u} d2 f_i /dX_j dX_k  Y_j Z_k
    with qtil=(q,0), Htil=(H,1) -- the drive's own "response" to itself is 1.
    All resolvent solves stay n-dimensional; only the contractions widen.

(2) The Q-V droop sign.  d|v_pcc|/d i_q = -Xg v_gd/|v| < 0 at this operating
    point, so a VOLTAGE-REGULATING law needs i_q* to DECREASE when the
    terminal voltage is low, i.e. i_q* = Q - k_v (Vref - |v_pcc|) with k_v>0.
    The first pass swept the opposite sign, which is anti-regulating positive
    feedback, so its instability at k_q=0.1 says nothing about a real AVR.
    Both signs are swept here and labelled.
"""
import math, time
import numpy as np
import sympy as sp
from scipy.linalg import eig

exec(open('selfhead.py').read())
_src = open('qaxis.py').read()
exec(_src.split('# ---------------------------------------------------'
                '-------------- models')[1].split('M6 = build')[0])

LOG = open('sweep20/qaxis2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

M6 = build('M6'); M8A = build('M8A'); M8B = build('M8B')

# ---- extended tensors for the 6-state: states + the drive coordinate Q
X6 = (TH, XP, VD, XI, ID, GD)
XE = X6 + (sQ,)
F6 = M6['F']
d1e = sp.derive_by_array(list(F6), XE)
d2e = sp.derive_by_array(d1e, XE)
d3e = sp.derive_by_array(d2e, XE)
AR6 = M6['AR']
H6e = sp.lambdify(AR6, d2e, 'numpy')
T6e = sp.lambdify(AR6, d3e, 'numpy')
out(f"extended tensors built [{time.time()-T0:.0f}s]")


def cx_ext(M, A, x, pr, q, p, w0, wp, fu):
    """c_x with the drive kept as a multiplicative coordinate."""
    a = av(M, x, pr)
    Hm = np.array(H6e(*a), float)      # [k][j][i], j,k over 7
    Tm = np.array(T6e(*a), float)      # [l][k][j][i]
    n = M['n']
    Bt = lambda u, v: np.einsum('kji,j,k->i', Hm, u, v)
    Ct = lambda u, v, w: np.einsum('lkji,j,k,l->i', Tm, u, v, w)
    ext = lambda v, last: np.concatenate([v, [last]])
    I = np.eye(n)
    Hv = np.linalg.solve(1j*wp*I - A, fu.astype(complex)); Hc = np.conj(Hv)
    qt = ext(q, 0.0); Ht = ext(Hv, 1.0); Hct = ext(Hc, 1.0)
    gp = np.linalg.solve(1j*(w0+wp)*I - A, Bt(qt, Ht))
    gm = np.linalg.solve(1j*(w0-wp)*I - A, Bt(qt, Hct))
    d0 = -np.linalg.solve(A, Bt(Ht, Hct))
    return (np.vdot(p, Ct(qt, Ht, Hct)) + np.vdot(p, Bt(Ht, ext(gm, 0.0)))
            + np.vdot(p, Bt(Hct, ext(gp, 0.0))) + np.vdot(p, Bt(qt, ext(d0, 0.0))))


prb = gset('G1')
Ps = 3*prb['V']**2/(4*prb['Xg'])
grid = np.linspace(0.05, 0.985, 60)*Ps
va = []
for P in grid:
    qd = dict(prb, P=P); xx = equil(qd)
    cm = crit_mode(jac(xx, qd)) if xx is not None else None
    va.append(None if cm is None else cm.real)
PH4 = None
for a_, b_, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
    if fa is not None and fb is not None and fa < 0 <= fb:
        lo, hi = a_, b_
        for _ in range(45):
            mm = 0.5*(lo+hi); qd = dict(prb, P=mm); xx = equil(qd)
            cm = crit_mode(jac(xx, qd)) if xx is not None else None
            if cm is None or cm.real >= 0: hi = mm
            else: lo = mm
        PH4 = 0.5*(lo+hi); break
P0 = margin_point(prb, PH4, 0.10)
co4 = nf_coeffs(dict(prb, P=P0))
w0ref = co4['w0']
BASE = dict(prb, P=P0, zc=0.707, kq=0.0, Vref=0.0)
st4 = equil(dict(prb, P=P0))

out("")
out("=== 1. is the residual the multiplicative (state x drive) part?")
out("    eps_c(8) / eps_c(6):  additive = old machinery, "
    "multiplicative = extended")
out("    x     r      eps_c(8)      eps_c6 additive  ratio    "
    "eps_c6 multiplic. ratio")
for x in (10., 30., 100., 300., 1000.):
    pr = dict(BASE, wc=x*w0ref)
    d8 = {}
    st8 = lift(M8A, st4, pr)
    A8, lam8, q8, p8, c18 = c1_of(M8A, st8, pr)
    st6 = lift(M6, st4, pr)
    A6, lam6, q6, p6, c16 = c1_of(M6, st6, pr)
    for rat in (0.60, 0.90, 1.00):
        w0 = lam6.imag; wp = rat*w0
        fu8 = np.array(M8A['fu'](*av(M8A, st8, pr)), float).ravel()
        F8 = abs(np.vdot(p8, fu8))
        J8 = abs(lam8)*F8/abs(wp**2 + lam8**2)
        cx8 = cx_of(M8A, A8, st8, pr, q8, p8, lam8.imag, wp, fu8).real
        e8 = eps_c(-lam8.real, c18.real, cx8, J8)
        fu6 = np.array(M6['fu'](*av(M6, st6, pr)), float).ravel()
        F6v = abs(np.vdot(p6, fu6))
        J6 = abs(lam6)*F6v/abs(wp**2 + lam6**2)
        cx6a = cx_of(M6, A6, st6, pr, q6, p6, w0, wp, fu6).real
        cx6m = cx_ext(M6, A6, st6, pr, q6, p6, w0, wp, fu6).real
        e6a = eps_c(-lam6.real, c16.real, cx6a, J6)
        e6m = eps_c(-lam6.real, c16.real, cx6m, J6)
        out(f"    {x:6.0f} {rat:.2f}  {e8:.6e}  {e6a:.6e}  {e8/e6a:.5f}  "
            f"{e6m:.6e}  {e8/e6m:.5f}")
    out(f"       (c_x additive {cx6a:+.6e}  multiplicative {cx6m:+.6e}  "
        f"ratio {cx6m/cx6a:.5f})")

out("")
out("=== 2. Q-V droop with the sign resolved")
x = 100.
pr0 = dict(BASE, wc=x*w0ref)
st8 = lift(M8A, st4, pr0)
th0, id0, iq0 = st8[0], st8[4], st8[6]
vgd0 = pr0['V']*math.cos(th0) - pr0['Xg']*iq0
vgq0 = -pr0['V']*math.sin(th0) + pr0['Xg']*id0
Vref0 = math.hypot(vgd0, vgq0)
dVdiq = -pr0['Xg']*vgd0/Vref0
out(f"    |v_pcc|={Vref0:.8f},  d|v_pcc|/d i_q = {dVdiq:+.6f}")
out(f"    -> voltage-regulating law is i_q* = Q + k_q (Vref-|v|) with "
    f"k_q {'<' if dVdiq < 0 else '>'} 0")
out("    k_q      role            alpha        w0        zeta      "
    "Re c1        residual")
for kq in (-30., -10., -3., -1., -0.3, -0.1, 0.0, 0.1, 0.3, 1.0, 3.0, 10.):
    pr = dict(pr0, kq=kq, Vref=Vref0)
    st = lift(M8B, st4, pr)
    res = np.max(np.abs(rhsn(M8B, st, pr)))
    A, lam, q, p, c1 = c1_of(M8B, st, pr)
    role = ('regulating' if kq*dVdiq < 0 else
            ('anti-regulating' if kq != 0 else 'open loop'))
    out(f"    {kq:+6.1f}  {role:15s} {-lam.real:+.6f}  {lam.imag:9.5f}  "
        f"{-lam.real/lam.imag:+.5f}  {c1.real:+.5e}  {res:.1e}")

out("")
out("    fine sweep of the regulating branch (alpha_open = "
    f"{-c1_of(M8B, lift(M8B, st4, dict(pr0, kq=0.0, Vref=Vref0)), dict(pr0, kq=0.0, Vref=Vref0))[1].real:.6f}):")
out("    k_q      alpha       w0        d(alpha)/alpha0")
a0 = None
for kq in (0.0, -0.02, -0.05, -0.1, -0.2, -0.5, -1.0, -2.0, -5.0):
    pr = dict(pr0, kq=kq, Vref=Vref0)
    A, lam, q, p, c1 = c1_of(M8B, lift(M8B, st4, pr), pr)
    if a0 is None:
        a0 = -lam.real
    out(f"    {kq:+6.2f}  {-lam.real:+.6f}  {lam.imag:9.5f}  "
        f"{(-lam.real-a0)/a0:+.4f}")
out(f"DONE wall={time.time()-T0:.0f}s")
