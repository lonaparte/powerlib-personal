"""Two audit gaps, checked directly.
G1: GFL combination-resonance tongue: pump V at w1+w2 (both complex
    pairs), Floquet continuation of the locked orbit to eps=0.05;
    also at |w2-w1| for completeness.
G2: GFM direct forced-desync threshold: sudden-on V oscillation at
    resonance and r=0.9, compound detector (delta-saddle / E-low /
    death), scan + bisect; compare with the linear-swing estimate
    eps ~ dw0/(kt*|H_w|).
Budget ~10 min total, guarded, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/quickgaps.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

# ---------- G1: GFL combination tongue ----------
pr0 = gset('G1', Xg=0.5)
lo, hi = 0.9, 1.4775
def g0(P):
    x = equil(dict(pr0, P=P))
    return crit_mode(jac(x, dict(pr0, P=P))).real
for _ in range(45):
    m = 0.5*(lo+hi)
    if g0(m) < 0: lo = m
    else: hi = m
P = margin_point(pr0, 0.5*(lo+hi), 0.10)
pr = dict(pr0, P=P)
st = equil(pr)
A = jac(st, pr)
ev = np.linalg.eigvals(A)
cx = sorted([e for e in ev if e.imag > 1e-9], key=lambda z: -z.real)
lam1, lam2 = cx[0], cx[1]
w1, w2 = lam1.imag, lam2.imag
a1, a2 = -lam1.real, -lam2.real
out(f"G1 modes: lam1={lam1:.4f} (f={w1/2/math.pi:.2f}Hz) "
    f"lam2={lam2:.4f} (f={w2/2/math.pi:.2f}Hz)")
_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])
def strobe_var(x0, eps, wp, Td):
    def f(t, y):
        x = y[:4]
        qq = dict(pr, V=pr['V'] + eps*math.cos(wp*t))
        Phi = y[4:].reshape(4, 4)
        return np.concatenate([rhs(x, qq), (jac_a(x, qq) @ Phi).ravel()])
    y0 = np.concatenate([x0, np.eye(4).ravel()])
    s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11, atol=1e-13)
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
def newton_fp(xg, eps, wp, Td, itmax=25):
    x = xg.copy(); M = None
    for it in range(itmax):
        xT, M = strobe_var(x, eps, wp, Td)
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
for wp, tagp in ((w1 + w2, 'w1+w2'), (w2 - w1, 'w2-w1')):
    Td = 2*math.pi/wp
    xL = st.copy()
    eps = 0.0
    deps = 2e-3
    cross = None
    while eps < 0.05:
        e_try = eps + deps
        xn, Mn, okn = newton_fp(xL.copy(), e_try, wp, Td)
        if not okn:
            deps *= 0.5
            if deps < 1e-5:
                out(f"G1 {tagp}: continuation stall at {eps:.4e}")
                break
            continue
        am = float(np.max(np.abs(np.linalg.eigvals(Mn))))
        if am > 1.0:
            cross = e_try
            break
        xL, eps = xn, e_try
        deps = min(deps*1.5, 5e-3)
    if cross is None:
        out(f"G1 combi {tagp} (wp={wp:.2f}): NO instability below eps=0.05 "
            f"(theory: threshold ~ 2*sqrt(a1*a2)/|coupling|, "
            f"a1={a1:.3f} a2={a2:.3f}) [{time.time()-T0:.0f}s]")
    else:
        out(f"G1 combi {tagp} (wp={wp:.2f}): instability at eps~{cross:.4e} "
            f"[{time.time()-T0:.0f}s]")

# ---------- G2: GFM direct forced-desync threshold ----------
from gfmlib import (rhs as grhs, jac as gjac, equil as gequil,
                    crit_mode as gcrit, maxre_cx, hopf_in, mset, fold,
                    escape_event, Enom)
prg = mset('M1', Xg=0.10)
dfold, Pm = fold(prg)
qh = hopf_in(prg, 'Pref', 0.02*Pm, 0.95*Pm)
P_H = qh['Pref']
def gg(P):
    r = maxre_cx(dict(prg, Pref=P))
    return 1.0 if r is None else r
Phi_ = min(0.95*Pm, 2.5*P_H)
tt_ = 0.10
if gg(Phi_) > -tt_:
    tt_ = max(0.3*abs(gg(Phi_)), 0.02)
lo2, hi2 = P_H, Phi_
for _ in range(45):
    m = 0.5*(lo2+hi2)
    if gg(m) > -tt_: lo2 = m
    else: hi2 = m
prm = dict(prg, Pref=0.5*(lo2+hi2))
stg = gequil(prm)
Ag = gjac(stg, prm)
lamg = gcrit(Ag)
w0g = lamg.imag
evd, dsadg = escape_event(prm)
h = 1e-6
BVg = (grhs(stg, dict(prm, V=prm['V']+h))
       - grhs(stg, dict(prm, V=prm['V']-h)))/(2*h)
for r_, tagr in ((1.0, 'res'), (0.9, 'r=0.9')):
    wp = r_*w0g
    Hg = np.linalg.solve(1j*wp*np.eye(4) - Ag, BVg)
    Hw = abs(Hg[1])
    kt = 1 + math.exp(-math.pi*(-lamg.real)/abs(w0g-wp)) if r_ != 1.0 else 2.0
    dw0 = 32.8125
    est = dw0/(kt*Hw)
    def probe(eps, T=120):
        def f(t, x):
            qq = dict(prm, V=prm['V']*(1 + eps*math.cos(wp*t)))
            return grhs(x, qq)
        def eE(t, x):
            return (Enom - prm['mq']*(x[3]-prm['Qref'])) - 0.2
        eE.terminal = True; eE.direction = -1
        s = solve_ivp(f, (0, T), stg.copy(), method='DOP853', rtol=1e-9,
                      atol=1e-12, events=[evd, eE])
        if len(s.t_events[0]):
            return 'DELTA'
        if len(s.t_events[1]):
            return 'E-LOW'
        if s.status == -1 or s.t[-1] < T - 1:
            return 'DEATH'
        return 'OK'
    elo, ehi = None, None
    for fe in (0.02, 0.05, 0.1, 0.2, 0.4):
        r = probe(fe)
        out(f"  GFM {tagr} eps={fe}: {r} [{time.time()-T0:.0f}s]")
        if r == 'OK':
            elo = fe
        elif ehi is None:
            ehi = fe
            break
    if elo is not None and ehi is not None:
        mode = '?'
        for _ in range(7):
            em = 0.5*(elo+ehi)
            r = probe(em)
            if r == 'OK': elo = em
            else: ehi = em; mode = r
        out(f"G2 GFM {tagr}: eps_direct={0.5*(elo+ehi):.4f} mode={mode} "
            f"linear-swing est={est:.4f} (|H_w|={Hw:.1f}, kt={kt:.2f}) "
            f"[{time.time()-T0:.0f}s]")
    elif elo is not None:
        out(f"G2 GFM {tagr}: no desync up to eps=0.4 (40% V!) "
            f"est={est:.4f}")
    else:
        out(f"G2 GFM {tagr}: unstable already at 0.02; est={est:.4f}")
out(f"DONE wall={time.time()-T0:.0f}s")
