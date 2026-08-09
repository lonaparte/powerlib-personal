"""P/Q-channel parametric tongues (4 cells) + GFM mq-gating check.
Per channel u: f_u (FD), M1 = dA/du at fixed state (FD), h_F =
(2i w0 I - A)^-1 f_u, pi = <p,M1 qbar> + <p,B(h_F,qbar)>, pred
eps_t = 2 alpha/|pi| (absolute units of u). Measure: Newton fixed
point of the strobe map with u(t)=u0+eps cos(2 w0 t) + monodromy
multiplier bisection. Structural checks: M1(P)=0 exactly (both
devices); f_Q(GFM) ~ mq -> 0. Budget ~6 min.
"""
import sys, time, os, math
import numpy as np
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/pqtongue.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

# ---------------- GFL ----------------
exec(open('selfhead.py').read())
_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])

def gfl_build(over, marg):
    prb = gset('G1', **over)
    Psn = 3*prb['V']**2/(4*prb['Xg'])
    def reA(P):
        q = dict(prb, P=P)
        x = equil(q)
        if x is None: return None
        cm = crit_mode(jac(x, q))
        return None if cm is None else cm.real
    grid = np.linspace(0.05, 0.985, 60)*Psn
    va = [reA(P) for P in grid]
    br = None
    for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
        if fa is not None and fb is not None and fa < 0 <= fb:
            br = (a, b); break
    if br is None: return None
    lo, hi = br
    for _ in range(45):
        m = 0.5*(lo+hi)
        v = reA(m)
        if v is None or v >= 0: hi = m
        else: lo = m
    P = margin_point(prb, 0.5*(lo+hi), marg)
    pr = dict(prb, P=P)
    co = nf_coeffs(pr)
    return pr, co

def tongue(tag, dev, pr, co, key, strobe_jac, Bfun, rhsf, cap=None):
    st = co['st']; alpha = co['alpha']; w0 = co['w0']
    qv = co['q']; pv = co['p']
    u0 = pr[key]
    h = 1e-6*max(1.0, abs(u0))
    fu = (rhsf(st, dict(pr, **{key: u0+h}))
          - rhsf(st, dict(pr, **{key: u0-h})))/(2*h)
    A = strobe_jac(st, pr)
    M1 = (strobe_jac(st, dict(pr, **{key: u0+h}))
          - strobe_jac(st, dict(pr, **{key: u0-h})))/(2*h)
    hF = np.linalg.solve(2j*w0*np.eye(4) - A, fu)
    t1 = np.vdot(pv, M1 @ np.conj(qv))
    t2 = np.vdot(pv, Bfun(st, pr, hF, np.conj(qv)))
    pi = t1 + t2
    if abs(pi) < 1e-12:
        out(f"{tag}: |f_u|={np.linalg.norm(fu):.2e} |M1|={np.max(np.abs(M1)):.2e}"
            f" |pi|~0 -> tongue ABSENT (channel switched off)")
        return
    pred = 2*alpha/abs(pi)
    line = (f"{tag}: alpha={alpha:.4f} w0={w0:.3f} |M1q|={abs(t1):.3g} "
            f"|Bh|={abs(t2):.3g} |pi|={abs(pi):.3g} pred={pred:.4e}")
    if cap is not None and pred > cap:
        out(line + f"  (pred > cap {cap:.2g}, measurement skipped)")
        return
    wp = 2*w0
    Td = 2*math.pi/wp
    def strobe_var(x0, eps):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, **{key: u0 + eps*math.cos(wp*t)})
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhsf(x, qq),
                                   (strobe_jac(x, qq) @ Phi).ravel()])
        y0 = np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-10,
                      atol=1e-12)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def newton_fp(xg, eps, itmax=25):
        x = xg.copy(); M = None
        for it in range(itmax):
            xT, M = strobe_var(x, eps)
            Fx = xT - x
            if np.max(np.abs(Fx)) < 1e-10:
                return x, M, True
            try:
                dx = np.linalg.solve(M - np.eye(4), -Fx)
            except np.linalg.LinAlgError:
                return x, M, False
            n = np.max(np.abs(dx))
            if n > 0.3:
                dx *= 0.3/n
            x = x + dx
        return x, M, np.max(np.abs(Fx)) < 1e-8
    def stab(e):
        xn, Mn, okn = newton_fp(st.copy(), e)
        if not okn:
            return False
        return float(np.max(np.abs(np.linalg.eigvals(Mn)))) < 1.0
    elo, ehi = 0.6*pred, 1.6*pred
    n = 0
    while not stab(elo) and n < 6:
        elo /= 1.7; n += 1
    n = 0
    while stab(ehi) and n < 6:
        ehi *= 1.7; n += 1
    if not stab(elo) or stab(ehi):
        out(line + "  bracket failed"); return
    for _ in range(12):
        em = 0.5*(elo+ehi)
        if stab(em): elo = em
        else: ehi = em
    meas = 0.5*(elo+ehi)
    out(line + f" meas={meas:.4e} err={(pred-meas)/meas*100:+.2f}%"
        f" [{time.time()-T0:.0f}s]")

def gfl_B(st, pr, u, v):
    a = _avl(st, pr)
    return np.array([sum(_Hl[i][j][k](*a)*u[j]*v[k]
                         for j in range(4) for k in range(4))
                     for i in range(4)])

GFL_CASES = [('G1', {}, 0.10), ('Xg=0.35', dict(Xg=0.35), 0.10),
             ('kp30ki600', dict(kp=30., ki=600.), 0.10)]
for name, over, marg in GFL_CASES:
    r = gfl_build(over, marg)
    if r is None:
        out(f"GFL {name}: no window"); continue
    pr, co = r
    for key in ('P', 'Q'):
        tongue(f"GFL {name} u={key}", 'gfl', pr, co, key,
               jac_a, gfl_B, rhs)

# ---------------- GFM ----------------
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gfmlib as G
from scipy.linalg import eig as _eig

def gfm_build(name, Xg, **mod):
    pr = G.mset(name, Xg=Xg, **mod)
    dfold, Pm = G.fold(pr)
    q = G.hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
    if q is None: return None
    P_H = q['Pref']
    def g(P):
        r = G.maxre_cx(dict(pr, Pref=P))
        return 1.0 if r is None else r
    Phi_ = min(0.95*Pm, 2.5*P_H)
    tt = 0.10
    if g(Phi_) > -tt:
        tt = max(0.3*abs(g(Phi_)), 0.02)
    lo2, hi2 = P_H, Phi_
    for _ in range(45):
        m = 0.5*(lo2+hi2)
        if g(m) > -tt: lo2 = m
        else: hi2 = m
    prm = dict(pr, Pref=0.5*(lo2+hi2))
    st = G.equil(prm)
    A = G.jac(st, prm)
    lam = G.crit_mode(A)
    ev, VL, VR = _eig(A, left=True, right=True)
    k = int(np.argmin(np.abs(ev - lam)))
    qv = VR[:, k]; pv = VL[:, k]
    pv = pv/np.vdot(qv, pv)
    co = dict(st=st, alpha=-lam.real, w0=lam.imag, q=qv, p=pv)
    return prm, co

GFM_CASES = [('M3', 0.05), ('M2', 0.03), ('M5', 0.15)]
for name, Xg in GFM_CASES:
    r = gfm_build(name, Xg)
    if r is None:
        out(f"GFM {name}@{Xg}: no window"); continue
    pr, co = r
    for key in ('Pref', 'Qref'):
        tongue(f"GFM {name}@{Xg} u={key}", 'gfm', pr, co, key,
               G.jac, G.Bform, G.rhs, cap=5.0)

# ---- mq gating (Q-GFM design claim) ----
out("--- mq gating (M3@0.05, u=Qref) ---")
for mq in (0.2, 0.1, 0.05, 0.02, 0.0):
    r = gfm_build('M3', 0.05, mq=mq)
    if r is None:
        out(f"  mq={mq}: no window"); continue
    pr, co = r
    st = co['st']; u0 = pr['Qref']
    h = 1e-6
    fu = (G.rhs(st, dict(pr, Qref=u0+h))
          - G.rhs(st, dict(pr, Qref=u0-h)))/(2*h)
    A = G.jac(st, pr)
    M1 = (G.jac(st, dict(pr, Qref=u0+h))
          - G.jac(st, dict(pr, Qref=u0-h)))/(2*h)
    hF = np.linalg.solve(2j*co['w0']*np.eye(4) - A, fu)
    pi = (np.vdot(co['p'], M1 @ np.conj(co['q']))
          + np.vdot(co['p'], G.Bform(st, pr, hF, np.conj(co['q']))))
    pred = 2*co['alpha']/abs(pi) if abs(pi) > 1e-14 else float('inf')
    out(f"  mq={mq}: |f_Q|={np.linalg.norm(fu):.3e} |pi|={abs(pi):.3e} "
        f"pred_eps_t={pred:.3e}")
out(f"DONE wall={time.time()-T0:.0f}s")
