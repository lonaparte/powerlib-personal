"""
RIGOROUS BAUTIN ENCLOSURE for the GFL 10-state weak-grid Hopf (Ki_pll = 150).
================================================================================

GOAL
----
bautin.py (FLOAT) found that, fixing Ki_pll=150 and the grid angle X/R=10, the
first Lyapunov coefficient l1 at the weak-grid Hopf changes SIGN as the PLL
proportional gain Kp_pll is varied, near Kp* ~ 0.404 (the Bautin / generalized-Hopf
point: l1=0, boundary between subcritical/hard and supercritical/soft Hopf).

This script turns that float evidence into an INTERVAL-SOUND proof:
choose Kp_lo < Kp* < Kp_hi, and at EACH endpoint produce a RIGOROUS interval
enclosure of l1 *at a certified Hopf*, such that the two enclosures have DEFINITE
OPPOSITE SIGNS. By the intermediate value theorem (l1 is continuous along the Hopf
locus), l1 must vanish for some Kp* in [Kp_lo, Kp_hi] -- a Bautin point is
rigorously bracketed.

WHY l1 MUST BE EVALUATED *AT* A HOPF (the critical subtlety)
-----------------------------------------------------------
l1 is only defined when Re(lambda)=0 (the projection formula divides by, and is
derived at, a purely imaginary critical pair lambda = +- i*omega). At each endpoint
Kp we therefore do NOT evaluate l1 at an arbitrary SCR: we take a small SCR
INTERVAL [SClo,SChi] straddling the float Hopf SCR_H(Kp), so that the interval
Jacobian's critical eigenvalue has a real-part enclosure that PROVABLY CONTAINS 0.
That guarantees the box contains a true Re(lambda)=0 Hopf, and the interval l1 over
the box then ENCLOSES the value of l1 at that Hopf. This is exactly the
"box straddles the Hopf surface" technique of ivparam.py / ivgrid.py / ivlocus.py.
(Route (i) of the task; Route (ii), the bordered Re lambda=0 system, would give a
tighter SCR but is not needed for the sign conclusion.)

SIGN vs MAGNITUDE
-----------------
Per Conventions.md 12.6 and numerical/README.md: the MAGNITUDE of l1 is
normalization/coordinate dependent (balanced vs unbalanced coords differ ~100x),
but the SIGN of l1 is the coordinate-invariant physical quantity (sub/supercritical).
We work in BALANCED coordinates throughout (same as ivparam.py), purely to lower the
condition number; the sign is what the Bautin conclusion rests on.

SOUNDNESS
---------
- Model, equilibrium (closed-form quadratic), Jacobian, and the exact symbolic
  2nd/3rd derivative tensors (B,C) are IDENTICAL to sweep.py / ivparam.py.
- All parameter and tensor entries are evaluated in mpmath interval arithmetic
  (directed rounding) over the (SCR-interval, fixed Kp) box.
- The critical right eigenpair (i*omega, q) and the left eigenpair p are
  VERIFIED existent-and-unique over the whole box by Krawczyk on the bordered
  eigen-system (Rump's method); if Krawczyk fails to contract we RAISE (never
  return an unverified result).
- The two linear solves in Kuznetsov's formula are enclosed by a rigorous Neumann
  bound (||I - R M||_inf < 1 verified); raises otherwise.
- The opposite-sign claim is read off the interval ENCLOSURES (l1.b<0 vs l1.a>0),
  never off float midpoints.

This file is standalone (mirrors ivparam.py's structure). Run:
    cd formalization/numerical && python3 bautin_cert/bautin_cert.py
Requires numpy/scipy/sympy/mpmath. Produces the bracket and the two enclosures, and
(when run as __main__) writes the machine-readable summary consumed by RESULTS.md.
"""
import sys, os, time, json
import sympy as sp, numpy as np, mpmath as mp
from mpmath import iv

iv.dps = 50
mp.mp.dps = 50

# fixed operating point for the Bautin study (task: Ki_pll = 150; grid angle X/R = 10)
KI_FIXED = mp.mpf('150')
XR_FIXED = mp.mpf('10')

# ============================================================================
# MODEL  (identical to sweep.py / ivparam.py ; Conventions.md 12.3)
# ============================================================================
wn, Vg, Rg, Lg, vcd, Kp, Ki = sp.symbols('wn Vg Rg Lg vcd Kp Ki')
Cf = sp.Rational(1, 10000); Lf = sp.Rational(1, 1000); Rf = sp.Rational(1, 10)
Kpi = sp.Rational(126, 100); Kii = sp.Integer(126); Kad = sp.Integer(2)
idr = sp.Integer(80); iqr = sp.Integer(0)
S = sp.symbols('i_d i_q v_cd v_cq i_gd i_gq xdc xqc eta th', real=True)
i_d, i_q, v_cd, v_cq, i_gd, i_gq, xdc, xqc, eta, th = S
wpll = wn + Kp * v_cq + Ki * eta
f = sp.Matrix([
    (Kpi * (idr - i_d) + Kii * xdc - Kad * (i_d - i_gd) - Rf * i_d) / Lf,
    (Kpi * (iqr - i_q) + Kii * xqc - Kad * (i_q - i_gq) - Rf * i_q) / Lf,
    (i_d - i_gd) / Cf + wpll * v_cq,
    (i_q - i_gq) / Cf - wpll * v_cd,
    (v_cd - Vg * sp.cos(th) - Rg * i_gd + wpll * Lg * i_gq) / Lg,
    (v_cq + Vg * sp.sin(th) - Rg * i_gq - wpll * Lg * i_gd) / Lg,
    idr - i_d, iqr - i_q, v_cq, Kp * v_cq + Ki * eta])
Asym = f.jacobian(list(S))
al = 1 - wn**2 * Lg * Cf; K1 = Rg * idr - wn * Lg * iqr
K2 = Rg * iqr + wn * Lg * idr; be = Rg * wn * Cf
igq_e = iqr - wn * Cf * vcd; ceq = (al * vcd - K1) / Vg; seq = (K2 - be * vcd) / Vg
sub = {i_d: idr, i_q: iqr, v_cd: vcd, v_cq: 0, i_gd: idr, i_gq: igq_e,
       xdc: Rf * idr / Kii, xqc: (Kad * (iqr - igq_e) + Rf * iqr) / Kii,
       sp.cos(th): ceq, sp.sin(th): seq, eta: 0}
Ae = sp.Matrix(10, 10, lambda i, j: Asym[i, j].subs(sub))
Afun = sp.lambdify((wn, Vg, Rg, Lg, vcd, Kp, Ki), Ae, 'mpmath')
Afun_np = sp.lambdify((wn, Vg, Rg, Lg, vcd, Kp, Ki), Ae, 'numpy')

# exact symbolic nonzero 2nd (Hessian H) and 3rd (T) derivative tensors of f
Hsym = {}; Tsym = {}
for i in range(10):
    for j in range(10):
        for k in range(10):
            h = sp.diff(Asym[i, j], S[k])
            if h != 0:
                Hsym[(i, j, k)] = h.subs(sub)
                for l in range(10):
                    t = sp.diff(h, S[l])
                    if t != 0:
                        Tsym[(i, j, k, l)] = t.subs(sub)


# ----------------------------------------------------------------------------
# interval evaluation of a sympy expression (poly in wn,Vg,Rg,Lg,vcd,Kp,Ki)
# ----------------------------------------------------------------------------
def ev(e, env, cache):
    if e in cache:
        return cache[e]
    if e.is_Integer:
        r = iv.mpf([int(e), int(e)])
    elif e.is_Rational:
        r = iv.mpf([int(e.p), int(e.p)]) / iv.mpf([int(e.q), int(e.q)])
    elif e.is_Symbol:
        r = env[e]
    elif e.is_Add:
        r = iv.mpf([0, 0])
        for a in e.args:
            r = r + ev(a, env, cache)
    elif e.is_Mul:
        r = iv.mpf([1, 1])
        for a in e.args:
            r = r * ev(a, env, cache)
    elif e.is_Pow:
        b = ev(e.base, env, cache); n = int(e.exp); r = iv.mpf([1, 1])
        for _ in range(abs(n)):
            r = r * b
        if n < 0:
            r = iv.mpf([1, 1]) / r
    else:
        raise ValueError(str(type(e)))
    cache[e] = r
    return r


# ----------------------------------------------------------------------------
# float helpers: equilibrium params, Jacobian, Hopf-SCR locating
# (X/R fixed, Ki fixed; Kp is the Bautin sweep variable)
# ----------------------------------------------------------------------------
def params_pt(SCRv, XRv):
    wnv = 2 * mp.pi * 50; Vgv = 380 * mp.sqrt(mp.mpf(2) / 3)
    Zg = mp.mpf(380)**2 / (mp.mpf('1e5') * SCRv)
    sq = mp.sqrt(1 + XRv**2); Rgv = Zg / sq; Lgv = Zg * XRv / (sq * wnv); Cfv = mp.mpf(1) / 10000
    alv = 1 - wnv**2 * Lgv * Cfv; bev = Rgv * wnv * Cfv; K1v = Rgv * 80; K2v = wnv * Lgv * 80
    a2 = alv**2 + bev**2; a1 = -2 * (alv * K1v + bev * K2v); a0 = K1v**2 + K2v**2 - Vgv**2
    disc = a1 * a1 - 4 * a2 * a0
    if disc < 0:
        return None
    vcdv = (-a1 + mp.sqrt(disc)) / (2 * a2)
    return wnv, Vgv, Rgv, Lgv, vcdv


def An_at(SCRv, Kpv):
    pp = params_pt(mp.mpf(SCRv), XR_FIXED)
    if pp is None:
        return None
    M = Afun_np(*[float(x) for x in pp], float(Kpv), float(KI_FIXED))
    return np.array(M, float)


def maxre(SCRv, Kpv):
    A = An_at(SCRv, Kpv)
    if A is None:
        return None
    return float(np.max(np.linalg.eigvals(A).real))


def hopf_SCR(Kpv, lo=0.3, hi=3.0, ng=240):
    """float weak-grid Hopf SCR at this Kp (scan grid strong->weak; first stable->unstable)."""
    prev = None
    for s in np.linspace(hi, lo, ng):
        r = maxre(s, Kpv)
        if r is None:
            break
        if prev is not None and prev[1] < 0 and r > 0:
            a, b = s, prev[0]
            for _ in range(90):
                m = (a + b) / 2; rm = maxre(m, Kpv)
                if rm > 0:
                    a = m
                else:
                    b = m
            return (a + b) / 2
        prev = (s, r)
    return None


# ----------------------------------------------------------------------------
# interval environment over a box: SCR in [SClo,SChi], Kp FIXED (=Kpc), Ki,X/R fixed
# ----------------------------------------------------------------------------
def env_box(SClo, SChi, Kpc):
    SH = iv.mpf([mp.nstr(SClo, 30), mp.nstr(SChi, 30)])     # SCR box straddling the Hopf
    XR = iv.mpf([mp.nstr(XR_FIXED, 30), mp.nstr(XR_FIXED, 30)])
    wnI = 2 * iv.pi * 50; VgI = 380 * iv.sqrt(iv.mpf([2, 2]) / 3)
    Zg = iv.mpf([380, 380])**2 / (iv.mpf([100000, 100000]) * SH)
    sqI = iv.sqrt(1 + XR**2)
    RgI = Zg / sqI; LgI = Zg * XR / (sqI * wnI); CfI = iv.mpf([1, 1]) / 10000
    alv = 1 - wnI**2 * LgI * CfI; bev = RgI * wnI * CfI; K1v = RgI * 80; K2v = wnI * LgI * 80
    a2 = alv**2 + bev**2; a1 = -2 * (alv * K1v + bev * K2v); a0 = K1v**2 + K2v**2 - VgI**2
    vcdI = (-a1 + iv.sqrt(a1 * a1 - 4 * a2 * a0)) / (2 * a2)
    KpI = iv.mpf([mp.nstr(Kpc, 30), mp.nstr(Kpc, 30)])      # Kp FIXED at the endpoint value
    KiI = iv.mpf([mp.nstr(KI_FIXED, 30), mp.nstr(KI_FIXED, 30)])
    return {wn: wnI, Vg: VgI, Rg: RgI, Lg: LgI, vcd: vcdI, Kp: KpI, Ki: KiI}


# ----------------------------------------------------------------------------
# core: rigorous interval l1 over the box (balanced coords), with verified
# eigenpairs (Krawczyk) and verified linear solves (Neumann). Mirrors ivparam.py.
# Returns ((l1_lo,l1_hi), (relam_lo,relam_hi), (om_lo,om_hi), rq) or (None, err).
# ----------------------------------------------------------------------------
def C(re, im=0.0):
    return iv.mpc(iv.mpf([re, re]) if not isinstance(re, iv.mpf) else re,
                  iv.mpf([im, im]) if not isinstance(im, iv.mpf) else im)


def matvec(M, v):
    return [sum((M[i][j] * v[j] for j in range(len(v))), iv.mpc(0, 0)) for i in range(len(M))]


def certify_box(env, An, _dbg=[False]):
    cache = {}
    Aiv = [[iv.mpc(ev(Ae[i, j], env, cache), iv.mpf([0, 0])) for j in range(10)] for i in range(10)]
    Hnz = {k: ev(e, env, cache) for k, e in Hsym.items()}
    Tnz = {k: ev(e, env, cache) for k, e in Tsym.items()}

    # BALANCE (l1 invariant under x = D x~; sign unchanged): lower condition number
    import scipy.linalg
    _, T = scipy.linalg.matrix_balance(An, permute=False); d = np.diag(T).copy()

    def R2(x):
        return iv.mpf([float(x), float(x)])
    Aiv = [[Aiv[i][j] * R2(d[j] / d[i]) for j in range(10)] for i in range(10)]
    Hnz = {(i, j, k): H * R2(d[j] * d[k] / d[i]) for (i, j, k), H in Hnz.items()}
    Tnz = {(i, j, k, l): Tt * R2(d[j] * d[k] * d[l] / d[i]) for (i, j, k, l), Tt in Tnz.items()}
    Anb = (np.diag(1 / d) @ An @ np.diag(d))

    # float seed eigenpair (balanced)
    w, V = np.linalg.eig(Anb); kk = np.argmax(w.real); lam0 = complex(w[kk]); q0 = V[:, kk].astype(complex)
    s = int(np.argmax(np.abs(q0))); q0 = q0 / q0[s]

    def verify_ep(Miv, lam0, v0, sidx):
        # bordered eigen-system: [M v - lam v ; v[sidx]-1] = 0 ; Krawczyk (Rump)
        Mc = np.array([[(float(Miv[i][j].real.a) + float(Miv[i][j].real.b)) / 2
                        + 1j * (float(Miv[i][j].imag.a) + float(Miv[i][j].imag.b)) / 2
                        for j in range(10)] for i in range(10)])
        Jn = np.zeros((11, 11), complex)
        for i in range(10):
            for j in range(10):
                Jn[i, j] = Mc[i, j] - (lam0 if i == j else 0)
            Jn[i, 10] = -v0[i]
        Jn[10, sidx] = 1.0
        Rn = np.linalg.inv(Jn)
        Riv = [[C(Rn[i, j].real, Rn[i, j].imag) for j in range(11)] for i in range(11)]
        yhat = [C(v0[i].real, v0[i].imag) for i in range(10)] + [C(lam0.real, lam0.imag)]

        def Fv(y):
            q = y[:10]; lam = y[10]
            out = [sum((Miv[i][j] * q[j] for j in range(10)), iv.mpc(0, 0)) - lam * q[i] for i in range(10)]
            out.append(q[sidx] - C(1.0)); return out

        def Jm(y):
            q = y[:10]; lam = y[10]; JJ = [[iv.mpc(0, 0)] * 11 for _ in range(11)]
            for i in range(10):
                for j in range(10):
                    JJ[i][j] = Miv[i][j] - (lam if i == j else iv.mpc(0, 0))
                JJ[i][10] = -q[i]
            JJ[10][sidx] = C(1.0); return JJ
        for r in [1e-7 * (1.3 ** k) for k in range(70)]:
            Y = [yh + iv.mpc(iv.mpf([-r, r]), iv.mpf([-r, r])) for yh in yhat]
            RF = matvec(Riv, Fv(yhat)); JJ = Jm(Y)
            RJ = [[sum((Riv[i][k] * JJ[k][j] for k in range(11)), iv.mpc(0, 0)) for j in range(11)] for i in range(11)]
            dY = [Y[i] - yhat[i] for i in range(11)]
            cor = [sum((((iv.mpc(1, 0) if i == j else iv.mpc(0, 0)) - RJ[i][j]) * dY[j] for j in range(11)), iv.mpc(0, 0)) for i in range(11)]
            Kk = [yhat[i] - RF[i] + cor[i] for i in range(11)]
            if all((Y[i].real.a < Kk[i].real.a and Kk[i].real.b < Y[i].real.b and
                    Y[i].imag.a < Kk[i].imag.a and Kk[i].imag.b < Y[i].imag.b) for i in range(11)):
                return Kk, r
        return None, None

    Kq, rq = verify_ep(Aiv, lam0, q0, s)
    if Kq is None:
        return None, "eigenpair(q) Krawczyk failed"
    ATiv = [[Aiv[j][i] for j in range(10)] for i in range(10)]
    w2, V2 = np.linalg.eig(Anb.T)
    kl = np.argmin(np.abs(w2 - (-1j * lam0.imag))); p0 = V2[:, kl].astype(complex)
    spx = int(np.argmax(np.abs(p0))); p0 = p0 / p0[spx]
    Kp_, rp = verify_ep(ATiv, complex(w2[kl]), p0, spx)
    if Kp_ is None:
        return None, "eigenpair(p) Krawczyk failed"

    qI = Kq[:10]; lamI = Kq[10]; omI = lamI.imag; pI = Kp_[:10]

    def conj(z):
        return iv.mpc(z.real, -z.imag)

    def ipc(a, bv):
        return sum((conj(a[i]) * bv[i] for i in range(10)), iv.mpc(0, 0))
    qq = ipc(qI, qI); qn = [qI[i] / iv.sqrt(qq.real) for i in range(10)]
    pqi = ipc(pI, qn); pn = [pI[i] / conj(pqi) for i in range(10)]; qb = [conj(qn[i]) for i in range(10)]

    def Bf(u, v):
        o = [iv.mpc(0, 0)] * 10
        for (i, j, k), H in Hnz.items():
            o[i] = o[i] + H * u[j] * v[k]
        return o

    def Cf3(u, v, w):
        o = [iv.mpc(0, 0)] * 10
        for (i, j, k, l), Tt in Tnz.items():
            o[i] = o[i] + Tt * u[j] * v[k] * w[l]
        return o

    def vsolve(Miv, bb):
        Mmid = np.array([[(float(Miv[i][j].real.a) + float(Miv[i][j].real.b)) / 2
                          + 1j * (float(Miv[i][j].imag.a) + float(Miv[i][j].imag.b)) / 2
                          for j in range(10)] for i in range(10)])
        Rm = np.linalg.inv(Mmid); Riv = [[C(Rm[i, j].real, Rm[i, j].imag) for j in range(10)] for i in range(10)]
        x0 = matvec(Riv, bb)
        resid = [bb[i] - sum((Miv[i][j] * x0[j] for j in range(10)), iv.mpc(0, 0)) for i in range(10)]
        dd = matvec(Riv, resid)
        G = [[((iv.mpc(1, 0) if i == j else iv.mpc(0, 0)) - sum((Riv[i][k] * Miv[k][j] for k in range(10)), iv.mpc(0, 0))) for j in range(10)] for i in range(10)]

        def mag(z):
            ar = mp.mpf(max(abs(z.real.a), abs(z.real.b))); ai = mp.mpf(max(abs(z.imag.a), abs(z.imag.b)))
            return mp.sqrt(ar * ar + ai * ai)
        Ginf = max(sum((mag(G[i][j]) for j in range(10)), mp.mpf(0)) for i in range(10))
        dinf = max(mag(dd[i]) for i in range(10))
        if not (Ginf < 1):
            raise RuntimeError("noncontractive solve %s" % float(Ginf))
        sb = float(Ginf * dinf / (1 - Ginf)) * 1.0001
        ball = iv.mpc(iv.mpf([-sb, sb]), iv.mpf([-sb, sb]))
        return [x0[i] + dd[i] + ball for i in range(10)]

    g1 = Cf3(qn, qn, qb); r1 = vsolve(Aiv, Bf(qn, qb)); g2 = Bf(qn, r1)
    M2 = [[(iv.mpc(iv.mpf([0, 0]), 2 * omI) - Aiv[i][j]) if i == j else (iv.mpc(0, 0) - Aiv[i][j]) for j in range(10)] for i in range(10)]
    r2 = vsolve(M2, Bf(qn, qn)); g3 = Bf(qb, r2)
    val = ipc(pn, [g1[i] - 2 * g2[i] + g3[i] for i in range(10)])
    l1 = (iv.mpf([1, 1]) / (2 * omI)) * val.real
    relam = lamI.real
    return ((float(l1.a), float(l1.b)),
            (float(relam.a), float(relam.b)),
            (float(omI.a), float(omI.b)), rq), None


# ----------------------------------------------------------------------------
# endpoint certificate: choose SCR box straddling Hopf SCR_H(Kp); certify l1
# ----------------------------------------------------------------------------
def endpoint_l1(Kpc, pad, verbose=True):
    Kpc = mp.mpf(Kpc)
    sH = hopf_SCR(Kpc)
    if sH is None:
        return None, "no weak-grid Hopf found at Kp=%s" % mp.nstr(Kpc, 6)
    SClo, SChi = sH - pad, sH + pad
    env = env_box(SClo, SChi, Kpc)
    An = An_at((SClo + SChi) / 2, Kpc)
    res, err = certify_box(env, An)
    if res is None:
        return None, err
    (l1lo, l1hi), (relo, rehi), (omlo, omhi), rq = res
    info = dict(Kp=float(Kpc), SCR_H=float(sH), SClo=float(SClo), SChi=float(SChi),
                l1=[l1lo, l1hi], relam=[relo, rehi], omega=[omlo, omhi], r=rq,
                straddles0=bool(relo <= 0.0 <= rehi))
    if verbose:
        f_osc_lo = omlo / (2 * np.pi); f_osc_hi = omhi / (2 * np.pi)
        print("  Kp=%.5f  Hopf SCR_H~%.6f  SCR box=[%.6f,%.6f]" % (float(Kpc), float(sH), float(SClo), float(SChi)))
        print("     Re(lambda) enclosure = [%+.3e, %+.3e]   straddles 0 (=> box contains a Hopf): %s"
              % (relo, rehi, info['straddles0']))
        print("     omega enclosure      = [%.5f, %.5f]  (f_osc in [%.3f,%.3f] Hz)" % (omlo, omhi, f_osc_lo, f_osc_hi))
        print("     l1 enclosure         = [%+.6e, %+.6e]   (Krawczyk r=%.0e)" % (l1lo, l1hi, rq))
        sign = 'l1<0 (supercritical/soft)' if l1hi < 0 else ('l1>0 (subcritical/hard)' if l1lo > 0 else 'STRADDLES 0 (inconclusive)')
        print("     SIGN: %s" % sign)
    return info, None


def opposite_signs(infoA, infoB):
    alo, ahi = infoA['l1']; blo, bhi = infoB['l1']
    a_neg = ahi < 0; a_pos = alo > 0
    b_neg = bhi < 0; b_pos = blo > 0
    return (a_neg and b_pos) or (a_pos and b_neg)


def run(Kp_lo=0.39, Kp_hi=0.42, pad=1e-6, do_narrow=True):
    print("=" * 78)
    print("RIGOROUS BAUTIN ENCLOSURE  (Ki_pll=%s fixed, X/R=%s fixed)" % (mp.nstr(KI_FIXED, 6), mp.nstr(XR_FIXED, 4)))
    print("  bracket endpoints Kp_lo=%.5f, Kp_hi=%.5f ; SCR-box half-width pad=%.0e" % (Kp_lo, Kp_hi, pad))
    print("=" * 78)
    print("\n[endpoint LO] Kp = %.5f" % Kp_lo)
    infoLo, errLo = endpoint_l1(Kp_lo, pad)
    if infoLo is None:
        print("  FAILED:", errLo); return None
    print("\n[endpoint HI] Kp = %.5f" % Kp_hi)
    infoHi, errHi = endpoint_l1(Kp_hi, pad)
    if infoHi is None:
        print("  FAILED:", errHi); return None

    print("\n" + "-" * 78)
    ok_straddle = infoLo['straddles0'] and infoHi['straddles0']
    ok_signs = opposite_signs(infoLo, infoHi)
    print("BOTH endpoints are certified Hopf (Re lambda enclosure straddles 0): %s" % ok_straddle)
    print("l1 enclosures have DEFINITE OPPOSITE SIGNS:                          %s" % ok_signs)
    if ok_straddle and ok_signs:
        print("\n  ==> RIGOROUS BAUTIN BRACKET:  Kp* in [%.5f, %.5f]   (width %.5f)" % (Kp_lo, Kp_hi, Kp_hi - Kp_lo))
        print("      l1(Kp_lo=%.5f) in [%+.4e, %+.4e]" % (Kp_lo, *infoLo['l1']))
        print("      l1(Kp_hi=%.5f) in [%+.4e, %+.4e]" % (Kp_hi, *infoHi['l1']))
        print("      (signs opposite => l1=0 for some Kp* in the bracket: a Bautin / generalized-Hopf point)")
    else:
        print("\n  bracket NOT established at this (Kp_lo,Kp_hi,pad); widen the bracket or pad.")
    result = dict(Ki=float(KI_FIXED), XR=float(XR_FIXED), Kp_lo=Kp_lo, Kp_hi=Kp_hi,
                  pad=pad, width=Kp_hi - Kp_lo, endpointLo=infoLo, endpointHi=infoHi,
                  ok_straddle=ok_straddle, ok_signs=ok_signs)
    return result


if __name__ == "__main__":
    t0 = time.time()
    # primary bracket
    res = run(Kp_lo=0.39, Kp_hi=0.42, pad=1e-6)
    results = {"primary": res}

    # narrowing attempts (report how tight conditioning allows)
    if res and res['ok_signs']:
        print("\n" + "=" * 78)
        print("NARROWING the bracket (each must keep opposite definite signs):")
        print("=" * 78)
        for lo, hi, pad in [(0.395, 0.41, 1e-6), (0.40, 0.408, 1e-6), (0.402, 0.406, 1e-6)]:
            print("\n--- try [%.5f, %.5f] pad=%.0e ---" % (lo, hi, pad))
            r = run(Kp_lo=lo, Kp_hi=hi, pad=pad)
            results["narrow_%.3f_%.3f" % (lo, hi)] = r
            if not (r and r['ok_signs']):
                print("   (narrowing stopped: bracket not rigorously established here)")
                break

    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")
    with open(out, "w") as fh:
        json.dump(results, fh, indent=2, default=float)
    print("\n[wrote %s]  total %.1fs" % (out, time.time() - t0))
