"""
run_all.py -- end-to-end driver, all results written to results/RESULTS.txt:

  STEP 0  full-model ground truth l1 (validated pipeline = sweep.py)
  STEP 1  center-manifold l1 on the full 10-D system (exact planar Hopf bridge)
  STEP 2  CORRECT 4-state QSS reduction {v_cd,v_cq,eta,th}: Hopf + l1
  STEP 3  full-vs-reduced cross-validation table (the deliverable)
  STEP 4  symbolic reduced field + symbolic Jacobian self-check
  STEP 5  Sturm sign-certificate self-test + SOS availability

Run:  cd formalization/numerical/reduction_sos && python3 run_all.py
"""
import os, sys, time
import numpy as np
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))   # so 'import sweep' works

import reduce_model as RM
import qss_reduction as QR
import certify as CERT

OUT = []
def log(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    OUT.append(s)


def reduced_l1(SCR, XR, Kpv, Kiv, keep=QR.KEEP_IDX, want_l1=True):
    """Nonlinear-QSS reduced model: max Re(eig) and (optionally) Kuznetsov l1."""
    g, xke = QR.reduced_field_factory(SCR, XR, Kpv, Kiv, keep)
    nk = len(keep)
    h = 1e-6
    Jr = np.zeros((nk, nk))
    for j in range(nk):
        xp = xke.copy(); xp[j] += h
        xm = xke.copy(); xm[j] -= h
        Jr[:, j] = (g(xp) - g(xm)) / (2 * h)
    maxre = float(np.max(np.linalg.eigvals(Jr).real))
    if not want_l1:
        return maxre, None, None
    e = np.eye(nk); hh = 2e-3
    B = np.zeros((nk, nk, nk)); C = np.zeros((nk, nk, nk, nk))
    for j in range(nk):
        for k in range(nk):
            B[:, j, k] = (g(xke + hh*e[j] + hh*e[k]) - g(xke + hh*e[j] - hh*e[k])
                          - g(xke - hh*e[j] + hh*e[k]) + g(xke - hh*e[j] - hh*e[k])) / (4*hh*hh)
    for j in range(nk):
        for k in range(nk):
            for l in range(nk):
                def d2(xc):
                    return (g(xc + hh*e[k] + hh*e[l]) - g(xc + hh*e[k] - hh*e[l])
                            - g(xc - hh*e[k] + hh*e[l]) + g(xc - hh*e[k] - hh*e[l])) / (4*hh*hh)
                C[:, j, k, l] = (d2(xke + hh*e[j]) - d2(xke - hh*e[j])) / (2*hh)
    W, V = np.linalg.eig(Jr); re = W.real; km = np.argmax(re)
    cand = [i for i in range(nk) if abs(re[i] - re[km]) < 1e-3*max(1, abs(re[km])) + 1e-6]
    if not any(abs(W[i].imag) > 1e-6 for i in cand):
        return maxre, None, None
    k = max(cand, key=lambda i: W[i].imag); lam = W[k]; q = V[:, k]; om = lam.imag
    WL, VL = np.linalg.eig(Jr.T); kl = np.argmin(np.abs(WL - np.conj(lam))); p = VL[:, kl]
    q = q/np.sqrt(np.vdot(q, q).real); p = p/np.conj(np.vdot(p, q)); qb = np.conj(q)
    Bf = lambda u, v: np.einsum('ijk,j,k->i', B, u, v)
    Cf3 = lambda u, v, wv: np.einsum('ijkl,j,k,l->i', C, u, v, wv)
    r1 = np.linalg.solve(Jr, Bf(q, qb))
    r2 = np.linalg.solve(2j*om*np.eye(nk) - Jr, Bf(q, q))
    gg = Cf3(q, q, qb) - 2*Bf(q, r1) + Bf(qb, r2)
    return maxre, (1/(2*om))*np.real(np.vdot(p, gg)), om


def reduced_hopf_SCR(XR, Kpv, Kiv, keep=QR.KEEP_IDX):
    grid = np.linspace(2.0, 0.4, 140); prev = None
    for s in grid:
        r = reduced_l1(s, XR, Kpv, Kiv, keep, want_l1=False)[0]
        if prev is not None and prev[1] < 0 and r > 0:
            a, b = s, prev[0]
            for _ in range(55):
                m = (a + b) / 2
                rm = reduced_l1(m, XR, Kpv, Kiv, keep, want_l1=False)[0]
                if rm > 0: a = m
                else: b = m
            return (a + b) / 2
        prev = (s, r)
    return None


XRs = [2, 5, 10, 20, 30]

log("="*82)
log("STEP 0.  Full 10-state ground truth (validated pipeline, = sweep.l1)")
log("="*82)
full = {}
for XR in XRs:
    sh = RM.hopf_SCR(XR, 0.30, 150)
    l1f, om, re = RM.l1_full_projection(sh, XR, 0.30, 150)
    full[XR] = (sh, l1f, om)
    log("  X/R=%2d  SCR_H=%.5f  f=%.2fHz  l1_full=%+.4e -> %s"
        % (XR, sh, om/2/np.pi, l1f, 'subcritical' if l1f > 0 else 'supercritical'))

log("")
log("="*82)
log("STEP 1.  Center-manifold l1 on full 10-D (exact planar Hopf reduction)")
log("="*82)
for XR in XRs:
    sh = full[XR][0]
    l1c, om, gap = RM.l1_center_manifold(sh, XR, 0.30, 150)
    l1p = full[XR][1]
    log("  X/R=%2d  l1_proj=%+.4e  l1_centermfd=%+.4e  signs_agree=%s  (rel.diff=%.1e)"
        % (XR, l1p, l1c, (l1p > 0) == (l1c > 0), abs(l1c - l1p)/abs(l1p)))

log("")
log("="*82)
log("STEP 2.  CORRECT 4-state QSS reduction {v_cd,v_cq,eta,th}")
log("="*82)
red = {}
for XR in XRs:
    sh = reduced_hopf_SCR(XR, 0.30, 150)
    if sh is None:
        red[XR] = None
        log("  X/R=%2d  reduced: NO Hopf in SCR in [0.4,2]" % XR)
        continue
    mr, l1r, om = reduced_l1(sh, XR, 0.30, 150)
    red[XR] = (sh, l1r, om)
    log("  X/R=%2d  SCR_H_red=%.5f  f_red=%.2fHz  l1_red=%+.4e -> %s"
        % (XR, sh, om/2/np.pi, l1r, 'subcritical' if l1r > 0 else 'supercritical'))

log("")
log("="*82)
log("STEP 3.  CROSS-VALIDATION  full (10-state) vs reduced (4-state {v_cd,v_cq,eta,th})")
log("="*82)
log("  %-4s | %-9s %-12s %-4s | %-9s %-12s %-4s | %-6s | f_full/f_red"
    % ("X/R", "SCR_H", "l1_full", "sgn", "SCR_H", "l1_red", "sgn", "MATCH"))
log("  " + "-"*92)
nm = 0; ntot = 0
for XR in XRs:
    shf, l1f, omf = full[XR]
    if red[XR] is None:
        log("  %-4d | %.5f  %+.4e  %-4s | %-9s NO-HOPF"
            % (XR, shf, l1f, '+' if l1f > 0 else '-', "---"))
        continue
    shr, l1r, omr = red[XR]
    sf = '+' if l1f > 0 else '-'; sr = '+' if l1r > 0 else '-'
    m = (l1f > 0) == (l1r > 0); nm += int(m); ntot += 1
    log("  %-4d | %.5f  %+.4e  %-4s | %.5f  %+.4e  %-4s | %-6s | %.1f/%.1f Hz"
        % (XR, shf, l1f, sf, shr, l1r, sr, "YES" if m else "NO", omf/2/np.pi, omr/2/np.pi))
log("  " + "-"*92)
log("  SIGN AGREEMENT: %d / %d points" % (nm, ntot))

log("")
log("="*82)
log("STEP 4.  Symbolic reduced field + Jacobian self-check")
log("="*82)
t0 = time.time()
g_sym, keep, (cth, sth), (igd_q, igq_q) = QR.build_reduced_field()
log("  symbolic 4-state field built (%.1fs). Rational in (wn,Vg,Rg,Lg,Kp,Ki)." % (time.time() - t0))
log("  grid-current QSS denominator = (wpll*Lg)^2 + Rg^2 > 0  (non-singular).")
X = [QR.v_cd, QR.v_cq, QR.eta, QR.th]
J_sym = g_sym.jacobian(X)
Jlam = sp.lambdify((QR.wn, QR.Vg, QR.Rg, QR.Lg, QR.Kp, QR.Ki, *X), J_sym, 'numpy')
XR = 10.0
shr = reduced_hopf_SCR(XR, 0.30, 150)
xe = QR.reduced_equilibrium(shr, XR)
wnv, Vgv, Rgv, Lgv, vcdv = RM.grid_params(shr, XR)
Jn = np.array(Jlam(wnv, Vgv, Rgv, Lgv, 0.30, 150, *xe), float)
evs = sorted(np.linalg.eigvals(Jn), key=lambda z: -z.real)
log("  symbolic reduced Jacobian eigenvalues at reduced Hopf (X/R=10):")
for ev in evs:
    log("     re=%+9.3f im=%+9.3f  f=%.2fHz" % (ev.real, ev.imag, abs(ev.imag)/2/np.pi))
log("  max Re = %.3e (should be ~0 at the reduced Hopf SCR)" % np.max(np.linalg.eigvals(Jn).real))

log("")
log("="*82)
log("STEP 5.  Sturm sign-certificate self-test + SOS availability")
log("="*82)
log("  SOS solver available (cvxpy/scs): %s" % CERT.have_sos_solver())
t = sp.symbols('t', real=True)
N0 = t**2 - 3*t + 5     # no real roots -> constant sign
c0 = CERT.sturm_sign_constant(N0, t, 2, 30)
log("  Sturm on N=t^2-3t+5 over [2,30]: constant_sign=%s n_roots=%d sign=%s" % c0)
N1 = (t - 2) * (t - 30)
part = CERT.region_l1_positive_univariate(N1, t, 0, 40)
log("  exact sign partition of (t-2)(t-30) on [0,40]: %s" % part)
log("  (Decision procedure is exact. Extracting the reduced-l1 numerator as a")
log("   univariate polynomial in X/R for a completed Sturm proof is future work;")
log("   the load-bearing evidence is the STEP 3 cross-validation. See REDUCTION_SOS.md.)")

os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
with open(os.path.join(HERE, 'results', 'RESULTS.txt'), 'w') as fh:
    fh.write("\n".join(OUT) + "\n")
log("")
log("wrote results/RESULTS.txt")
