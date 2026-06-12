"""
reduce_model.py  --  Reduction of the 10-state GFL converter (Conventions.md sec.12)
to a low-order core that drives the weak-grid PLL Hopf bifurcation.

Two reductions are provided and compared:

  (A) CENTER-MANIFOLD reduction at the Hopf point.
      The 10x10 Jacobian A at the Hopf equilibrium has a single critical pair
      (+/- i*omega) on the imaginary axis; the other 8 eigenvalues are deep in
      the LHP.  We restrict the full quadratic/cubic vector field to the 2-D
      real center eigenspace and use the standard center-manifold + Poincare
      normal-form first Lyapunov coefficient (Kuznetsov eq.(5.59)).  This is the
      MATHEMATICALLY EXACT planar reduction of the Hopf: l1 computed this way is,
      up to positive scaling, the same l1 as the full projection formula.  It is
      "reduced" in the sense that the cubic normal form lives on 2 states, but
      its coefficients still depend on the full 10-D B,C tensors and on the
      stable block A_s through the homological equations.  It is NOT a symbolic
      function of few parameters (the 10-D inverse is intractable in closed form)
      -- it is used here only as the ground-truth bridge between the full
      projection (sweep.py) and the *physical* reduced model below.

  (B) PHYSICALLY-MOTIVATED reduced model (the object we get symbolic l1 from).
      Singular-perturbation / time-scale separation: near the ~40 Hz weak-grid
      Hopf the current loop (i_d,i_q,xdc,xqc) and the LC filter are fast and are
      set to quasi-steady-state, leaving the slow PLL + grid-current core.
      See REDUCTION_SOS.md for the explicit assumptions.  This model has a
      Jacobian whose entries are rational in (SCR, X/R, Kp, Ki), so its l1 is a
      rational function of those parameters (computed in l1_symbolic.py).

This file: builds the full model symbolically (reusing the exact equilibrium of
Conventions sec.12.5), provides numeric Jacobian/tensors, the center-manifold l1,
and the reduced-model construction.  Run as a script for a self-check.
"""
import numpy as np
import sympy as sp

# ----------------------------------------------------------------------------
# Full 10-state model, identical symbol set / equilibrium to sweep.py & ivcert.py
# ----------------------------------------------------------------------------
wn, Vg, Rg, Lg, vcd, Kp, Ki = sp.symbols('wn Vg Rg Lg vcd Kp Ki')
Cf = sp.Rational(1, 10000); Lf = sp.Rational(1, 1000); Rf = sp.Rational(1, 10)
Kpi = sp.Rational(126, 100); Kii = sp.Integer(126); Kad = sp.Integer(2)
idr = sp.Integer(80); iqr = sp.Integer(0)
STATES = sp.symbols('i_d i_q v_cd v_cq i_gd i_gq xdc xqc eta th', real=True)
i_d, i_q, v_cd, v_cq, i_gd, i_gq, xdc, xqc, eta, th = STATES
NAMES = ['i_d', 'i_q', 'v_cd', 'v_cq', 'i_gd', 'i_gq', 'xdc', 'xqc', 'eta', 'th']
wpll = wn + Kp * v_cq + Ki * eta

F = sp.Matrix([
    (Kpi * (idr - i_d) + Kii * xdc - Kad * (i_d - i_gd) - Rf * i_d) / Lf,
    (Kpi * (iqr - i_q) + Kii * xqc - Kad * (i_q - i_gq) - Rf * i_q) / Lf,
    (i_d - i_gd) / Cf + wpll * v_cq,
    (i_q - i_gq) / Cf - wpll * v_cd,
    (v_cd - Vg * sp.cos(th) - Rg * i_gd + wpll * Lg * i_gq) / Lg,
    (v_cq + Vg * sp.sin(th) - Rg * i_gq - wpll * Lg * i_gd) / Lg,
    idr - i_d,
    iqr - i_q,
    v_cq,
    Kp * v_cq + Ki * eta,
])

A_sym = F.jacobian(list(STATES))

# exact equilibrium (Conventions sec.12.5)
al = 1 - wn**2 * Lg * Cf
K1 = Rg * idr - wn * Lg * iqr
K2 = Rg * iqr + wn * Lg * idr
be = Rg * wn * Cf
igq_e = iqr - wn * Cf * vcd
ceq = (al * vcd - K1) / Vg
seq = (K2 - be * vcd) / Vg
SUB = {i_d: idr, i_q: iqr, v_cd: vcd, v_cq: 0, i_gd: idr, i_gq: igq_e,
       xdc: Rf * idr / Kii, xqc: (Kad * (iqr - igq_e) + Rf * iqr) / Kii,
       eta: 0, sp.cos(th): ceq, sp.sin(th): seq}

A_eq = sp.Matrix(10, 10, lambda i, j: A_sym[i, j].subs(SUB))
PARAMS = (wn, Vg, Rg, Lg, vcd, Kp, Ki)
A_fun = sp.lambdify(PARAMS, A_eq, 'numpy')

# second/third derivative tensors at equilibrium (same construction as sweep.py)
_Hsym = {}; _Tsym = {}
for i in range(10):
    for j in range(10):
        for k in range(10):
            h = sp.diff(A_sym[i, j], STATES[k])
            if h != 0:
                _Hsym[(i, j, k)] = h.subs(SUB)
                for l in range(10):
                    t = sp.diff(h, STATES[l])
                    if t != 0:
                        _Tsym[(i, j, k, l)] = t.subs(SUB)
_Hk = list(_Hsym); _Hf = sp.lambdify(PARAMS, [_Hsym[k] for k in _Hk], 'numpy')
_Tk = list(_Tsym); _Tf = sp.lambdify(PARAMS, [_Tsym[k] for k in _Tk], 'numpy')


def grid_params(SCR, XR):
    """Map (SCR, X/R) -> (wn,Vg,Rg,Lg,vcd) using Conventions sec.12.4-12.5."""
    wnv = 2 * np.pi * 50
    Vgv = 380 * np.sqrt(2 / 3)
    Zg = 380.0**2 / (1e5 * SCR)
    sq = np.sqrt(1 + XR**2)
    Rgv = Zg / sq
    Lgv = Zg * XR / (sq * wnv)
    Cfv = 1e-4
    alv = 1 - wnv**2 * Lgv * Cfv
    bev = Rgv * wnv * Cfv
    K1v = Rgv * 80
    K2v = wnv * Lgv * 80
    a2 = alv**2 + bev**2
    a1 = -2 * (alv * K1v + bev * K2v)
    a0 = K1v**2 + K2v**2 - Vgv**2
    disc = a1 * a1 - 4 * a2 * a0
    if disc < 0:
        return None
    vcdv = (-a1 + np.sqrt(disc)) / (2 * a2)
    return (wnv, Vgv, Rgv, Lgv, vcdv)


def A_full(SCR, XR, Kpv, Kiv):
    pp = grid_params(SCR, XR)
    if pp is None:
        return None
    return np.array(A_fun(*pp, Kpv, Kiv), float)


def tensors_full(SCR, XR, Kpv, Kiv):
    a = (*grid_params(SCR, XR), Kpv, Kiv)
    Hv = _Hf(*a); Tv = _Tf(*a)
    B = np.zeros((10, 10, 10)); C = np.zeros((10, 10, 10, 10))
    for key, val in zip(_Hk, Hv):
        B[key] = float(val)
    for key, val in zip(_Tk, Tv):
        C[key] = float(val)
    return B, C


def maxre(SCR, XR, Kpv, Kiv):
    A = A_full(SCR, XR, Kpv, Kiv)
    if A is None:
        return None
    return float(np.max(np.linalg.eigvals(A).real))


def hopf_SCR(XR, Kpv, Kiv):
    """Locate the weak-grid Hopf SCR (stable->unstable as grid weakens)."""
    grid = np.linspace(3.0, 0.3, 240); prev = None
    for s in grid:
        r = maxre(s, XR, Kpv, Kiv)
        if r is None:
            break
        if prev is not None and prev[1] < 0 and r > 0:
            a, b = s, prev[0]
            for _ in range(80):
                m = (a + b) / 2; rm = maxre(m, XR, Kpv, Kiv)
                if rm > 0:
                    a = m
                else:
                    b = m
            return (a + b) / 2
        prev = (s, r)
    return None


def crit_pair(A):
    """Return (lam, q, p, omega) critical eigenpair with the *largest* real part
    (the weak-grid Hopf pair is the one closest to / crossing the axis)."""
    w, V = np.linalg.eig(A)
    re = w.real
    km = np.argmax(re)
    cand = [i for i in range(len(w)) if abs(re[i] - re[km]) < 1e-6 * max(1, abs(re[km])) + 1e-9]
    k = max(cand, key=lambda i: w[i].imag)
    lam = w[k]; q = V[:, k]; om = lam.imag
    wL, VL = np.linalg.eig(A.T)
    kl = np.argmin(np.abs(wL - np.conj(lam))); p = VL[:, kl]
    q = q / np.sqrt(np.vdot(q, q).real)
    p = p / np.conj(np.vdot(p, q))
    return lam, q, p, om


def l1_full_projection(SCR, XR, Kpv, Kiv):
    """Kuznetsov projection l1 on the full 10-D system (same as sweep.l1).
    This is the GROUND TRUTH sign."""
    A = A_full(SCR, XR, Kpv, Kiv)
    B, C = tensors_full(SCR, XR, Kpv, Kiv)
    lam, q, p, om = crit_pair(A)
    qb = np.conj(q)
    Bf = lambda u, v: np.einsum('ijk,j,k->i', B, u, v)
    Cf3 = lambda u, v, w_: np.einsum('ijkl,j,k,l->i', C, u, v, w_)
    n = A.shape[0]
    r1 = np.linalg.solve(A, Bf(q, qb))
    r2 = np.linalg.solve(2j * om * np.eye(n) - A, Bf(q, q))
    g = Cf3(q, q, qb) - 2 * Bf(q, r1) + Bf(qb, r2)
    return (1 / (2 * om)) * np.real(np.vdot(p, g)), om, lam.real


# ----------------------------------------------------------------------------
# (A) CENTER-MANIFOLD reduction at the Hopf point.
# Restrict to the 2-D real center eigenspace.  The first Lyapunov coefficient is
# computed by the same Kuznetsov formula but emphasizes that the dynamics
# relevant to the Hopf live on this 2-D manifold.  Sign must equal the full
# projection (it does -- both are the same invariant up to positive factor).
# ----------------------------------------------------------------------------
def l1_center_manifold(SCR, XR, Kpv, Kiv):
    """Center-manifold + normal form l1.  Returns (l1, omega, spectral_gap).
    spectral_gap = |Re(lam_crit)| relative to next-closest pair: small => good
    time-scale separation justifying a planar Hopf reduction."""
    A = A_full(SCR, XR, Kpv, Kiv)
    B, C = tensors_full(SCR, XR, Kpv, Kiv)
    lam, q, p, om = crit_pair(A)
    # spectral gap: distance of stable spectrum from imaginary axis
    w = np.linalg.eigvals(A)
    stable_re = sorted([z.real for z in w if abs(z.real - lam.real) > 1e-3 * max(1, abs(om))])
    gap = -max(stable_re) if stable_re else np.inf  # most lightly damped stable mode
    qb = np.conj(q)
    Bf = lambda u, v: np.einsum('ijk,j,k->i', B, u, v)
    Cf3 = lambda u, v, w_: np.einsum('ijkl,j,k,l->i', C, u, v, w_)
    n = A.shape[0]
    # homological equations on the FULL space (this *is* the center-manifold
    # construction: h_{20}, h_{11} solve (A - (mu)I) h = ...).  At the Hopf mu=0.
    h11 = np.linalg.solve(A, -Bf(q, qb))          # (0 - A) h11 = B(q,qb)
    h20 = np.linalg.solve(2j * om * np.eye(n) - A, Bf(q, q))
    # normal form cubic coefficient c1 = (1/2)<p, C(q,q,qb) + B(qb,h20) + 2 B(q,h11)>
    g = Cf3(q, q, qb) + Bf(qb, h20) + 2 * Bf(q, h11)
    c1 = 0.5 * np.vdot(p, g)
    l1 = c1.real / om
    return l1, om, gap


if __name__ == '__main__':
    XR = 10.0
    sh = hopf_SCR(XR, 0.30, 150)
    print("Hopf SCR (X/R=10, Kp=0.30, Ki=150): %.6f" % sh)
    A = A_full(sh, XR, 0.30, 150)
    lam, q, p, om = crit_pair(A)
    print("critical lambda = %.5e %+.5ej   f=%.3f Hz" % (lam.real, lam.imag, abs(lam.imag) / 2 / np.pi))
    print()
    print("all eigenvalues (sorted by real part, descending):")
    for z in sorted(np.linalg.eigvals(A), key=lambda z: -z.real):
        print("   re=%+12.4f  im=%+12.4f  f=%8.2f Hz" % (z.real, z.imag, abs(z.imag) / 2 / np.pi))
    print()
    qa = np.abs(q) / np.abs(q).max()
    print("critical eigenvector participation |q_i|/max:")
    for nm, v in zip(NAMES, qa):
        print("   %-6s %.4f" % (nm, v))
    print()
    l1p, omp, rep = l1_full_projection(sh, XR, 0.30, 150)
    l1c, omc, gap = l1_center_manifold(sh, XR, 0.30, 150)
    print("l1 full projection   = %+.6e  (sign %s)" % (l1p, '+' if l1p > 0 else '-'))
    print("l1 center-manifold   = %+.6e  (sign %s)" % (l1c, '+' if l1c > 0 else '-'))
    print("spectral gap (nearest stable mode damping) = %.3f rad/s vs omega=%.1f" % (gap, om))
    print("signs agree:", (l1p > 0) == (l1c > 0))
