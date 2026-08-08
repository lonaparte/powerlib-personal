"""GFL exhaustive closure of the remaining mechanism slots.
  D: 2:1 parametric tongue (pump V at 2*w0), Floquet threshold vs margin
     alpha in {0.05, 0.10, 0.20}; scaling test (tongue ~ alpha) vs the
     basin-crossing route (measured 8.44e-5 / 1.187e-4 / 1.662e-4);
     fate confirmation on both sides.
  E: erosion of the kick (transient) threshold by sustained background
     oscillation at r=0.90: kappa_c(eps_bg) for eps_bg/eps_c in
     {0, 0.3, 0.6, 0.85}, kick along +Re(q), 4 drive phases.
  F: slow V oscillation (w_s = 0.2, 1.0 rad/s): escape amplitude a_c vs
     quasi-static frozen-instability amplitude a_qs and vs the resonant
     threshold 1.187e-4.
Usage: python gflcases.py {D|E|F}
"""
import sys
MODE = sys.argv[1]
exec(open('selfhead.py').read())
import time, os
os.makedirs('sweep20', exist_ok=True)
LOG = open(f'sweep20/gfl-{MODE}.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

pr0 = gset('G1', Xg=0.5)
lo, hi = 0.9, 1.4775
def g0(P):
    x = equil(dict(pr0, P=P))
    return crit_mode(jac(x, dict(pr0, P=P))).real
for _ in range(45):
    m = 0.5*(lo+hi)
    if g0(m) < 0: lo = m
    else: hi = m
PH = 0.5*(lo+hi)

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])

def build(marg):
    P = margin_point(pr0, PH, marg)
    pr = dict(pr0, P=P)
    co = nf_coeffs(pr)
    return pr, co

def strobe_var(x0, pr, eps, wd, Td):
    def f(t, y):
        x = y[:4]
        qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        Phi = y[4:].reshape(4, 4)
        return np.concatenate([rhs(x, qq), (jac_a(x, qq) @ Phi).ravel()])
    y0 = np.concatenate([x0, np.eye(4).ravel()])
    s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11, atol=1e-13)
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)

def newton_fp(xg, pr, eps, wd, Td, itmax=25):
    x = xg.copy(); M = None
    for it in range(itmax):
        xT, M = strobe_var(x, pr, eps, wd, Td)
        Fx = xT - x
        if np.max(np.abs(Fx)) < 1e-11:
            return x, M, True
        try:
            dx = np.linalg.solve(M - np.eye(4), -Fx)
        except np.linalg.LinAlgError:
            return x, M, False
        n = np.max(np.abs(dx))
        if n > 0.2:
            dx *= 0.2/n
        x = x + dx
    return x, M, np.max(np.abs(Fx)) < 1e-9

def fate(pr, st, eps, wd, T=300, x0=None, t0=0.0, rtol=1e-9):
    def f(t, x):
        qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        return rhs(x, qq)
    def blow(t, x): return abs(x[0] - st[0]) - 1.2
    blow.terminal = True; blow.direction = 1
    s = solve_ivp(f, (t0, t0+T), st.copy() if x0 is None else x0,
                  method='DOP853', rtol=rtol, atol=1e-12, events=blow)
    return len(s.t_events[0]) > 0

# ---------------------- D: 2:1 parametric tongue --------------------------
if MODE == 'D':
    AVAL = {0.05: 8.44092e-5, 0.10: 1.1865e-4, 0.20: 1.66230e-4}
    for marg in (0.05, 0.10, 0.20):
        pr, co = build(marg)
        st = co['st']; w0 = co['w0']; alpha = co['alpha']
        wd = 2.0*w0
        Td = 2*math.pi/wd
        out(f"marg={marg}: P={pr['P']:.5f} alpha={alpha:.4f} w0={w0:.4f} "
            f"pump at 2*w0={wd:.4f}")
        xL = st.copy()
        eps = 0.0
        deps = 2e-4
        cross = None
        hist = []
        while eps < 0.05:
            e_try = eps + deps
            xn, Mn, okn = newton_fp(xL.copy(), pr, e_try, wd, Td)
            if not okn:
                deps *= 0.5
                if deps < 1e-6:
                    out(f"  continuation stall at eps={eps:.4e}")
                    break
                continue
            mu = np.linalg.eigvals(Mn)
            am = float(np.max(np.abs(mu)))
            k = int(np.argmax(np.abs(mu)))
            hist.append((e_try, am, mu[k]))
            if am > 1.0:
                elo, ehi = eps, e_try
                xb = xL.copy()
                for _ in range(12):
                    em = 0.5*(elo+ehi)
                    xm, Mm, okm = newton_fp(xb.copy(), pr, em, wd, Td)
                    if not okm:
                        ehi = em; continue
                    if float(np.max(np.abs(np.linalg.eigvals(Mm)))) > 1.0:
                        ehi = em
                    else:
                        elo = em; xb = xm
                mu_at = hist[-1][2]
                typ = ('PD' if abs(mu_at.imag) < 5e-2 and mu_at.real < 0
                       else 'fold' if abs(mu_at.imag) < 5e-2 else 'NS')
                cross = (0.5*(elo+ehi), typ)
                break
            xL, eps = xn, e_try
            deps = min(deps*1.4, 2e-3)
        for e, am, m in hist[-4:]:
            out(f"    eps={e:.4e} max|mult|={am:.5f} mult={m:.4f}")
        if cross is None:
            out(f"  RESULT D marg={marg}: no tongue crossing below eps=0.05 "
                f"(basin route at {AVAL[marg]:.3e} wins by >{0.05/AVAL[marg]:.0f}x)")
        else:
            et, typ = cross
            fb = fate(pr, st, 0.9*et, wd)
            fa = fate(pr, st, 1.1*et, wd)
            out(f"  RESULT D marg={marg}: tongue eps={et:.4e} type={typ} "
                f"ratio_to_basin={et/AVAL[marg]:.2f} "
                f"fate(0.9x)={'esc' if fb else 'cap'} "
                f"fate(1.1x)={'esc' if fa else 'cap'}")
    out(f"DONE wall={time.time()-T0:.0f}s")

# ---------------------- E: kick-threshold erosion -------------------------
elif MODE == 'E':
    pr, co = build(0.10)
    st = co['st']; w0 = co['w0']; qv = co['q']; pv = co['p']
    wd = 0.9*w0
    Td = 2*math.pi/wd
    EPSC = 1.1865e-4
    out(f"P={pr['P']:.5f} w0={w0:.4f} r=0.90 eps_c={EPSC:.4e} "
        f"guard modal radius (unforced) = 8.47e-3")
    def settle(eps, T):
        def f(t, x):
            qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
            return rhs(x, qq)
        s = solve_ivp(f, (0, T), st.copy(), method='DOP853', rtol=1e-9,
                      atol=1e-12)
        return s.y[:, -1]
    def kick_escapes(eps, xbase, tk, kap):
        xk = xbase + 2*np.real(kap*qv)
        return fate(pr, st, eps, wd, T=150, x0=xk, t0=tk, rtol=1e-8)
    for fbg in (0.0, 0.3, 0.6, 0.85):
        eps = fbg*EPSC
        Tset = Td*math.ceil(150/Td)
        xb0 = settle(eps, Tset) if eps > 0 else st.copy()
        kmins = []
        for jph in range(4):
            tk = Tset + jph*Td/4
            if eps > 0 and jph > 0:
                def f(t, x):
                    qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
                    return rhs(x, qq)
                s = solve_ivp(f, (Tset, tk), xb0, method='DOP853',
                              rtol=1e-10, atol=1e-13)
                xb = s.y[:, -1]
            else:
                xb = xb0.copy()
            klo, khi = 0.0, 0.02
            if not kick_escapes(eps, xb, tk, khi):
                khi = 0.05
                if not kick_escapes(eps, xb, tk, khi):
                    out(f"  eps_bg={fbg:.2f}x ph={jph}: no escape at kap=0.05")
                    kmins.append(float('inf'))
                    continue
            for _ in range(8):
                km = 0.5*(klo+khi)
                if kick_escapes(eps, xb, tk, km): khi = km
                else: klo = km
            kmins.append(0.5*(klo+khi))
        kmin = min(kmins)
        out(f"  RESULT E eps_bg={fbg:.2f}x eps_c: kappa_c per phase = "
            + ", ".join(f"{k:.4e}" for k in kmins)
            + f"  min={kmin:.4e}")
    out(f"DONE wall={time.time()-T0:.0f}s")

# ---------------------- F: slow-oscillation rate effects ------------------
elif MODE == 'F':
    pr, co = build(0.10)
    st = co['st']; w0 = co['w0']; alpha = co['alpha']
    out(f"P={pr['P']:.5f} alpha={alpha:.4f} w0={w0:.4f}")
    # frozen instability amplitude a_qs: Re lam(V=1-a) = 0
    def frozen_re(V):
        q = dict(pr, V=V)
        x = equil(q)
        if x is None:
            return 1.0
        cm = crit_mode(jac(x, q))
        return 1.0 if cm is None else cm.real
    alo, ahi = 0.0, 0.05
    for _ in range(40):
        am = 0.5*(alo+ahi)
        if frozen_re(1.0-am) < 0: alo = am
        else: ahi = am
    aqs = 0.5*(alo+ahi)
    out(f"a_qs (frozen Re=0 at V=1-a) = {aqs:.5e}")
    def fateF(a, ws, nper=3):
        def f(t, x):
            qq = dict(pr, V=pr['V'] - a*math.sin(ws*t))
            return rhs(x, qq)
        def blow(t, x): return abs(x[0] - st[0]) - 1.2
        blow.terminal = True; blow.direction = 1
        T = nper*2*math.pi/ws
        s = solve_ivp(f, (0, T), st.copy(), method='DOP853', rtol=1e-9,
                      atol=1e-12, events=blow)
        return len(s.t_events[0]) > 0
    for ws in (0.2, 1.0, 5.0):
        alo2, ahi2 = 0.0, 0.05
        assert fateF(ahi2, ws), f"no escape at a=0.05, ws={ws}"
        for _ in range(14):
            am = 0.5*(alo2+ahi2)
            if fateF(am, ws): ahi2 = am
            else: alo2 = am
        ac = 0.5*(alo2+ahi2)
        out(f"  RESULT F ws={ws}: a_c={ac:.5e}  a_c/a_qs={ac/aqs:.2f}  "
            f"(resonant eps_c at r=0.9: 1.187e-4)")
    out(f"DONE wall={time.time()-T0:.0f}s")
