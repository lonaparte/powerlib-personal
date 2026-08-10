"""i_q is not a constant: what actually changes when the q axis is dynamic.

The 4-state GFL carries Q (i.e. i_q) as a PARAMETER, so every result derived
from it silently assumes the q-axis current is frozen.  That assumption has to
be removed, not defended.  Removing it means the q axis gets its own current
loop and its own two states, and the model becomes

    8-state: (th, x_p, V_dc, xi, i_d, g_d, i_q, g_q)

The question is then quantitative, and splits in two:

 (1) EXOGENOUS q-axis reference (fixed setpoint, or a reactive-power command
     that is dictated from outside).  Then the q rows contain no other state,
     so the Jacobian is block triangular and the SPECTRUM splits.  That is a
     structural statement with three testable consequences: alpha, w0 and
     Re c1 of the 8-state must equal those of the 6-state to machine
     precision -- i.e. the q-axis loop cannot move the autonomous stability
     data AT ALL, only the d-axis loop can.  Verified here rather than
     asserted.
     What it CAN move is the forced problem: a q-axis disturbance now reaches
     the d block through the current loop instead of instantly, so every
     recorded Q-channel threshold has to be re-scaled.  Whether that rescaling
     is exactly the prefilter |H(i w_p)|^-1 is decided by direct evaluation.

 (2) Q-V droop / AC voltage control, i.e. i_q* depends on the terminal
     voltage.  Then the q rows contain th and i_d, the block triangularity is
     gone, and alpha itself moves.  Swept in k_q, equilibrium-preserving so
     that only the Jacobian changes.

Nothing here is a small correction to be waved away: (1) says the recorded
autonomous numbers survive exactly, (2) says they do not survive at all once
a reactive controller is closed.  Both need numbers.
"""
import math, time
import numpy as np
import sympy as sp
from scipy.linalg import eig
from scipy.optimize import fsolve

exec(open('selfhead.py').read())

LOG = open('sweep20/qaxis.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

# ----------------------------------------------------------------- models
SY = sp.symbols('th xp Vdc xi i_d g_d i_q g_q', real=True)
TH, XP, VD, XI, ID, GD, IQ, GQ = SY
PP = sp.symbols('P Q V Xg kp ki kpv kiv C wc zc kq Vref', real=True)
sP, sQ, sV, sXg, skp, ski, skpv, skiv, sC, swc, szc, skq, sVref = PP


def _fields(iq_expr):
    idref = skpv*(1 - VD) + skiv*XI
    vgd = sV*sp.cos(TH) - sXg*iq_expr
    vgq = -sV*sp.sin(TH) + sXg*ID
    return idref, vgd, vgq


def build(kind):
    """kind in {'M6','M8A','M8B'}; returns dict of lambdified pieces."""
    if kind == 'M6':
        X = (TH, XP, VD, XI, ID, GD)
        iq = sQ                      # frozen, exactly as in the 4-state
        idref, vgd, vgq = _fields(iq)
        rows = [skp*vgq + ski*XP, vgq,
                (sP + sp.Rational(3, 2)*(vgd*ID + vgq*iq)/VD)/sC,
                1 - VD,
                2*szc*swc*(idref - ID) + swc**2*GD, idref - ID]
        drive = sQ                   # q-axis drive enters instantaneously
    else:
        X = SY
        idref, vgd, vgq = _fields(IQ)
        if kind == 'M8A':
            iqref = sQ
        else:
            vmag = sp.sqrt(vgd**2 + vgq**2)
            iqref = sQ + skq*(sVref - vmag)
        rows = [skp*vgq + ski*XP, vgq,
                (sP + sp.Rational(3, 2)*(vgd*ID + vgq*IQ)/VD)/sC,
                1 - VD,
                2*szc*swc*(idref - ID) + swc**2*GD, idref - ID,
                2*szc*swc*(iqref - IQ) + swc**2*GQ, iqref - IQ]
        drive = sQ
    F = sp.Matrix(rows)
    n = len(X)
    AR = tuple(X) + PP
    d1 = sp.derive_by_array(list(F), X)                 # [j][i]
    d2 = sp.derive_by_array(d1, X)                      # [k][j][i]
    d3 = sp.derive_by_array(d2, X)                      # [l][k][j][i]
    return dict(n=n, X=X, AR=AR, F=F,
                f=sp.lambdify(AR, F, 'numpy'),
                J=sp.lambdify(AR, F.jacobian(sp.Matrix(X)), 'numpy'),
                H=sp.lambdify(AR, d2, 'numpy'),
                T=sp.lambdify(AR, d3, 'numpy'),
                fu=sp.lambdify(AR, sp.Matrix([sp.diff(e, drive) for e in F]),
                               'numpy'),
                fV=sp.lambdify(AR, sp.Matrix([sp.diff(e, sV) for e in F]),
                               'numpy'),
                Jsym=F.jacobian(sp.Matrix(X)))


def av(M, x, pr):
    return tuple(x) + tuple(pr[k] for k in ('P', 'Q', 'V', 'Xg', 'kp', 'ki',
                                            'kpv', 'kiv', 'C', 'wc', 'zc',
                                            'kq', 'Vref'))


def rhsn(M, x, pr):
    return np.array(M['f'](*av(M, x, pr)), float).ravel()


def jacn(M, x, pr):
    return np.array(M['J'](*av(M, x, pr)), float)


def lift(M, st4, pr):
    idr = pr['kpv']*(1 - st4[2]) + pr['kiv']*st4[3]
    base = [st4[0], st4[1], st4[2], st4[3], idr, 0.0]
    if M['n'] == 8:
        base += [pr['Q'], 0.0]
    return np.array(base)


def tensors(M, x, pr):
    a = av(M, x, pr)
    Hm = np.array(M['H'](*a), float)     # [k][j][i]
    Tm = np.array(M['T'](*a), float)     # [l][k][j][i]
    B2 = lambda u, v: np.einsum('kji,j,k->i', Hm, u, v)
    C3 = lambda u, v, w: np.einsum('lkji,j,k,l->i', Tm, u, v, w)
    return B2, C3


def modal(M, x, pr, gauge=0):
    A = jacn(M, x, pr)
    n = M['n']
    ev, VL, VR = eig(A, left=True, right=True)
    k = max((i for i in range(n) if ev[i].imag > 1e-9),
            key=lambda i: ev[i].real)
    lam = ev[k]
    q = VR[:, k]; q = q/q[gauge]          # physical gauge: theta component
    p = VL[:, k]; p = p/np.vdot(q, p)
    return A, ev, lam, q, p


def c1_of(M, x, pr):
    A, ev, lam, q, p = modal(M, x, pr)
    B2, C3 = tensors(M, x, pr)
    n = M['n']; w0 = lam.imag
    h11 = np.linalg.solve(A, B2(q, q.conj()))
    h20 = np.linalg.solve(2j*w0*np.eye(n) - A, B2(q, q))
    g21 = (np.vdot(p, C3(q, q, q.conj())) - 2*np.vdot(p, B2(q, h11))
           + np.vdot(p, B2(q.conj(), h20)))
    return A, lam, q, p, g21/2


def cx_of(M, A, x, pr, q, p, w0, wp, fu):
    B2, C3 = tensors(M, x, pr)
    I = np.eye(M['n'])
    Hv = np.linalg.solve(1j*wp*I - A, fu.astype(complex)); Hc = np.conj(Hv)
    gp = np.linalg.solve(1j*(w0+wp)*I - A, B2(q, Hv))
    gm = np.linalg.solve(1j*(w0-wp)*I - A, B2(q, Hc))
    d0 = -np.linalg.solve(A, B2(Hv, Hc))
    return (np.vdot(p, C3(q, Hv, Hc)) + np.vdot(p, B2(Hv, gm))
            + np.vdot(p, B2(Hc, gp)) + np.vdot(p, B2(q, d0)))


def eps_c(alpha, c1r, cx, J):
    lo, hi = 1e-14, 1e3
    for _ in range(220):
        m = 0.5*(lo + hi)
        aeff = alpha - cx*0.25*m*m
        rg = math.sqrt(aeff/c1r) if (aeff > 0 and c1r > 0) else -1.0
        if rg < 0 or m*J > rg:
            hi = m
        else:
            lo = m
    return 0.5*(lo + hi)


M6 = build('M6'); M8A = build('M8A'); M8B = build('M8B')
out(f"models built [{time.time()-T0:.0f}s]")

# --------------------------------------------------- 0. structural check
Jq = M8A['Jsym'][6:8, 0:6]
out("")
out("=== 0. structure of the 8-state with an exogenous q reference")
out(f"    d(q-rows)/d(other 6 states) = {sp.simplify(Jq)}"
    f"   -> all zero: {Jq.is_zero_matrix}")
Jdq = M8A['Jsym'][0:6, 6:8]
out(f"    d(d-rows)/d(i_q) nonzero in rows: "
    f"{[i for i in range(6) if sp.simplify(Jdq[i, 0]) != 0]}"
    f"    (so the q block DRIVES the d block, one way)")
Jq2 = M8B['Jsym'][6:8, 0:6]
out(f"    with Q-V droop, d(q-rows)/d(other) nonzero in columns: "
    f"{[j for j in range(6) if any(sp.simplify(Jq2[i, j]) != 0 for i in range(2))]}"
    f"   (0=th, 4=i_d)")

# ------------------------------------------------------- operating point
prb = gset('G1')
PH4 = None
Ps = 3*prb['V']**2/(4*prb['Xg'])
grid = np.linspace(0.05, 0.985, 60)*Ps
va = []
for P in grid:
    qd = dict(prb, P=P); xx = equil(qd)
    cm = crit_mode(jac(xx, qd)) if xx is not None else None
    va.append(None if cm is None else cm.real)
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
out("")
out(f"=== operating point: P_Hopf(4-state)={PH4:.6f}, P0(margin .10)={P0:.10f}")
out(f"    4-state: alpha={co4['alpha']:.6f}  w0={co4['w0']:.5f}  "
    f"Re c1={co4['c1'].real:.6e}  zeta={co4['alpha']/co4['w0']:.5f}")

BASE = dict(prb, P=P0, zc=0.707, kq=0.0, Vref=0.0)
st4 = equil(dict(prb, P=P0))

# ------------------- 1. exogenous q reference: does the q loop move alpha?
out("")
out("=== 1. exogenous q-axis reference: 6-state (i_q frozen) vs 8-state")
out("    x=w_c/w0    alpha_6        alpha_8       reldiff     "
    "w0_6        w0_8       Re c1_6        Re c1_8       reldiff")
w0ref = co4['w0']
store = {}
for x in (10., 30., 100., 300.):
    pr = dict(BASE, wc=x*w0ref)
    r = {}
    for tag, M in (('6', M6), ('8', M8A)):
        st = lift(M, st4, pr)
        res = np.max(np.abs(rhsn(M, st, pr)))
        A, lam, q, p, c1 = c1_of(M, st, pr)
        r[tag] = dict(st=st, A=A, lam=lam, q=q, p=p, c1=c1, res=res, M=M)
    a6 = -r['6']['lam'].real; a8 = -r['8']['lam'].real
    w6 = r['6']['lam'].imag; w8 = r['8']['lam'].imag
    c6 = r['6']['c1'].real; c8 = r['8']['c1'].real
    out(f"    {x:6.0f}   {a6:.9f}  {a8:.9f}  {abs(a8-a6)/abs(a6):.2e}   "
        f"{w6:.6f}  {w8:.6f}   {c6:.7e}  {c8:.7e}  "
        f"{abs(c8-c6)/abs(c6):.2e}")
    store[x] = (pr, r)
out(f"    (equilibrium residuals: "
    f"{max(store[x][1][t]['res'] for x in store for t in '68'):.2e})")
out(f"    4-state for reference: alpha={co4['alpha']:.9f}  "
    f"w0={co4['w0']:.6f}  Re c1={co4['c1'].real:.7e}")

# ------------------------------ 2. the q-axis disturbance CHANNEL
out("")
out("=== 2. q-axis disturbance channel: threshold with a real current loop")
out("    the 6-state drive is i_q itself (instant); the 8-state drive is")
out("    i_q*, filtered by H(s) = wc(wc+2 zc s)/(s^2+2 zc wc s+wc^2)")
out("    x     r=wp/w0   |H(i wp)|   eps_c(6)      eps_c(8)      "
    "ratio 8/6   1/|H|     match")
for x in (10., 30., 100., 300.):
    pr, r = store[x]
    for rat in (0.60, 0.90, 1.00):
        line = {}
        for tag in ('6', '8'):
            d = r[tag]; M = d['M']
            w0 = d['lam'].imag; wp = rat*w0
            fu = np.array(M['fu'](*av(M, d['st'], pr)), float).ravel()
            F = abs(np.vdot(d['p'], fu))
            J = abs(d['lam'])*F/abs(wp**2 + d['lam']**2)
            cx = cx_of(M, d['A'], d['st'], pr, d['q'], d['p'], w0, wp,
                       fu).real
            line[tag] = (eps_c(-d['lam'].real, d['c1'].real, cx, J), F, cx)
        wp = rat*r['6']['lam'].imag
        wc = pr['wc']; zc = pr['zc']
        Hj = wc*(wc + 2j*zc*wp)/((1j*wp)**2 + 2*zc*wc*(1j*wp) + wc**2)
        e6, e8 = line['6'][0], line['8'][0]
        out(f"    {x:5.0f}  {rat:.2f}     {abs(Hj):.6f}    {e6:.6e}  "
            f"{e8:.6e}  {e8/e6:.5f}   {1/abs(Hj):.5f}  "
            f"{abs(e8/e6*abs(Hj) - 1):.2e}")

# ---------------------- 2b. control: a d-side channel must be untouched
out("")
out("    control -- the V channel (no q-axis component) must give the SAME")
out("    threshold in 6 and 8 states:")
for x in (30., 300.):
    pr, r = store[x]
    rat = 0.90
    vals = {}
    for tag in ('6', '8'):
        d = r[tag]; M = d['M']
        w0 = d['lam'].imag; wp = rat*w0
        fv = np.array(M['fV'](*av(M, d['st'], pr)), float).ravel()
        F = abs(np.vdot(d['p'], fv))
        J = abs(d['lam'])*F/abs(wp**2 + d['lam']**2)
        cx = cx_of(M, d['A'], d['st'], pr, d['q'], d['p'], w0, wp, fv).real
        vals[tag] = eps_c(-d['lam'].real, d['c1'].real, cx, J)
    out(f"    x={x:5.0f}  eps_c(6)={vals['6']:.8e}  "
        f"eps_c(8)={vals['8']:.8e}  reldiff={abs(vals['8']/vals['6']-1):.2e}")

# ------------------------------------------- 3. Q-V droop: real feedback
out("")
out("=== 3. Q-V droop i_q* = Q + k_q (Vref - |v_pcc|): block structure gone")
out("    equilibrium-preserving (Vref := |v_pcc| at the base equilibrium)")
x = 100.
pr0 = dict(BASE, wc=x*w0ref)
st8 = lift(M8A, st4, pr0)
th0, id0, iq0 = st8[0], st8[4], st8[6]
vgd0 = pr0['V']*math.cos(th0) - pr0['Xg']*iq0
vgq0 = -pr0['V']*math.sin(th0) + pr0['Xg']*id0
Vref0 = math.hypot(vgd0, vgq0)
out(f"    |v_pcc| at the base equilibrium = {Vref0:.8f}")
out("    k_q      alpha         w0        zeta      Re c1        "
    "2nd mode Re    residual")
for kq in (0.0, 0.1, 0.3, 1.0, 3.0, 10.0, 30.0):
    pr = dict(pr0, kq=kq, Vref=Vref0)
    st = lift(M8B, st4, pr)
    res = np.max(np.abs(rhsn(M8B, st, pr)))
    A, lam, q, p, c1 = c1_of(M8B, st, pr)
    ev = np.linalg.eigvals(A)
    cx = sorted([e for e in ev if e.imag > 1e-9], key=lambda z: -z.real)
    m2 = cx[1].real if len(cx) > 1 else float('nan')
    out(f"    {kq:5.1f}  {-lam.real:+.7f}  {lam.imag:9.5f}  "
        f"{-lam.real/lam.imag:+.5f}  {c1.real:+.5e}  {m2:+.6f}   {res:.1e}")
out(f"DONE wall={time.time()-T0:.0f}s")
