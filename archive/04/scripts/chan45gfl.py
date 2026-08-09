"""GFL: bring the two remaining exogenous channels (X_g, omega_g) to the
same depth as V/P/Q.
 (0) five-channel coupling table in natural units;
 (1) structural check: does the channel move the frozen spectrum?
     alpha(u) sensitivity -> decides whether B4 (slow passage) exists;
 (2) B2 parametric tongue, pred vs monodromy measurement (3 sets);
 (3) B3-i sudden-on threshold (compound detector) vs winding flip
     (G1 strong, idx2 weak);
 (4) B4 slow band where it exists.
omega_g enters additively in the angle equation (rhs_w); X_g enters
multiplicatively in both voltage components.
Budget ~25 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/chan45gfl.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
from scipy.interpolate import CubicSpline

def rhs_w(x, pr):
    y = rhs(x, pr).copy()
    y[0] -= pr.get('dw', 0.0)
    return y
_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])
def equil_w(pr):
    """equilibrium with a constant frequency offset: only x_pll shifts"""
    st0 = equil(dict(pr, dw=0.0))
    if st0 is None: return None
    st = st0.copy()
    st[1] = st0[1] + pr.get('dw', 0.0)/pr['ki']
    return st
K = 32
mfreq = np.fft.fftfreq(K)*K
I4 = np.eye(4)
def shift_mat(r):
    ph = np.exp(1j*mfreq*r)
    return np.real(np.fft.ifft(np.fft.fft(np.eye(K), axis=0)*ph[:, None],
                               axis=0))
def dshift_mat(r):
    ph = 1j*mfreq*np.exp(1j*mfreq*r)
    return np.real(np.fft.ifft(np.fft.fft(np.eye(K), axis=0)*ph[:, None],
                               axis=0))
def dtheta_(Ua):
    return np.real(np.fft.ifft(np.fft.fft(Ua, axis=0)
                               * (1j*mfreq)[:, None], axis=0))
def upsample(Ua, N):
    C = np.fft.fft(Ua, axis=0)
    Cp = np.zeros((N, Ua.shape[1]), complex)
    hf = K//2
    Cp[:hf] = C[:hf]; Cp[N-hf+1:] = C[hf+1:]
    Cp[hf] = 0.5*C[hf]; Cp[N-hf] = 0.5*C[hf]
    return np.real(np.fft.ifft(Cp, axis=0))*(N/K)

SETS = [('G1 strong', {}, 0.10, True),
        ('Xg=0.35', dict(Xg=0.35), 0.10, False),
        ('idx2 weak', dict(kp=30., ki=600.), 0.10, True)]

for tag, over, marg, do_boundary in SETS:
    prb = gset('G1', **over)
    Psn = 3*prb['V']**2/(4*prb['Xg'])
    def reA(P):
        q = dict(prb, P=P); x = equil(q)
        if x is None: return None
        cm = crit_mode(jac(x, q))
        return None if cm is None else cm.real
    grid = np.linspace(0.05, 0.985, 60)*Psn
    va = [reA(P) for P in grid]
    br = None
    for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
        if fa is not None and fb is not None and fa < 0 <= fb:
            br = (a, b); break
    lo, hi = br
    for _ in range(45):
        m = 0.5*(lo+hi); v = reA(m)
        if v is None or v >= 0: hi = m
        else: lo = m
    P0 = margin_point(prb, 0.5*(lo+hi), marg)
    pr = dict(prb, P=P0, dw=0.0)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; qv = co['q']; pv = co['p']
    c1v = co['c1']; alpha = co['alpha']
    zg = math.sqrt(alpha/c1v.real)
    dsad = math.pi - 2*abs(st[0])
    A = jac_a(st, pr)
    hq = 1e-6
    fs = {}
    fs['V'] = (rhs(st, dict(pr, V=pr['V']+hq))
               - rhs(st, dict(pr, V=pr['V']-hq)))/(2*hq)
    fs['P'] = np.array([0., 0., 1.0/pr['C'], 0.])
    fs['Q'] = (rhs(st, dict(pr, Q=pr['Q']+hq))
               - rhs(st, dict(pr, Q=pr['Q']-hq)))/(2*hq)
    fs['Xg'] = (rhs(st, dict(pr, Xg=pr['Xg']+hq))
                - rhs(st, dict(pr, Xg=pr['Xg']-hq)))/(2*hq)
    fs['dw'] = np.array([-1., 0., 0., 0.])
    out(f"{tag}: P0={P0:.5f} w0={w0:.3f} zg={zg:.3e} Psn={Psn:.4f} "
        f"(P0/Psn={P0/Psn:.3f})")
    out("  coupling |<p,f_u>|: " + "  ".join(
        f"{k}={abs(np.vdot(pv, v)):.4g}" for k, v in fs.items()))
    # (1) does the channel move the frozen spectrum?
    sens = {}
    for key, base in (('V', pr['V']), ('P', pr['P']), ('Q', pr['Q']),
                      ('Xg', pr['Xg'])):
        d = 1e-4*max(abs(base), 1.0)
        a1 = crit_mode(jac(equil(dict(pr, **{key: base+d})),
                           dict(pr, **{key: base+d})))
        a2 = crit_mode(jac(equil(dict(pr, **{key: base-d})),
                           dict(pr, **{key: base-d})))
        sens[key] = abs((a1.real - a2.real)/(2*d))
    stw = equil_w(dict(pr, dw=1e-3))
    aw = crit_mode(jac_a(stw, dict(pr, dw=1e-3)))
    sens['dw'] = abs((aw.real - (-alpha))/1e-3)
    out("  |d(Re lam)/du| (frozen-spectrum motion): " + "  ".join(
        f"{k}={v:.4g}" for k, v in sens.items()))
    # (2) tongue for Xg and dw
    def B2c(u, v):
        a = _avl(st, pr)
        return np.array([sum(_Hl[i][j][k](*a)*u[j]*v[k]
                             for j in range(4) for k in range(4))
                         for i in range(4)])
    wp = 2*w0; Tdp = 2*math.pi/wp
    for key in ('Xg', 'dw'):
        fu = fs[key]
        if key == 'Xg':
            M1 = (jac_a(st, dict(pr, Xg=pr['Xg']+hq))
                  - jac_a(st, dict(pr, Xg=pr['Xg']-hq)))/(2*hq)
        else:
            M1 = np.zeros((4, 4))
        hF = np.linalg.solve(2j*w0*np.eye(4) - A, fu)
        pi_eff = np.vdot(pv, M1 @ np.conj(qv)) + np.vdot(pv, B2c(hF,
                                                    np.conj(qv)))
        eps_t = 2*alpha/abs(pi_eff)
        def strobe_var(x0, eps, wpp, Tdd, kk):
            def f(t, y):
                x = y[:4]
                qq = dict(pr, **{kk: pr.get(kk, 0.0)
                                 + eps*math.cos(wpp*t)})
                Phi = y[4:].reshape(4, 4)
                return np.concatenate([rhs_w(x, qq),
                                       (jac_a(x, qq) @ Phi).ravel()])
            y0 = np.concatenate([x0, np.eye(4).ravel()])
            s = solve_ivp(f, (0, Tdd), y0, method='DOP853', rtol=1e-11,
                          atol=1e-13)
            return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
        def newton_fp(xg0, eps, wpp, Tdd, kk, itmax=25):
            x = xg0.copy(); M = None
            for it in range(itmax):
                xT, M = strobe_var(x, eps, wpp, Tdd, kk)
                Fx = xT - x
                if np.max(np.abs(Fx)) < 1e-10:
                    return x, M, True
                try:
                    dx = np.linalg.solve(M - np.eye(4), -Fx)
                except np.linalg.LinAlgError:
                    return x, M, False
                n = np.max(np.abs(dx))
                if n > 0.3: dx *= 0.3/n
                x = x + dx
            return x, M, np.max(np.abs(Fx)) < 1e-8
        def stab(e):
            xn, Mn, okn = newton_fp(st.copy(), e, wp, Tdp, key)
            if not okn: return False
            return float(np.max(np.abs(np.linalg.eigvals(Mn)))) < 1.0
        cap = 0.028*pr['Xg'] if key == 'Xg' else 1e9
        elo, ehi = 0.6*eps_t, min(1.6*eps_t, cap)
        n = 0
        while not stab(elo) and n < 6:
            elo /= 1.7; n += 1
        n = 0
        while stab(ehi) and ehi < cap and n < 6:
            ehi = min(ehi*1.7, cap); n += 1
        if stab(elo) and not stab(ehi):
            for _ in range(12):
                em = 0.5*(elo+ehi)
                if stab(em): elo = em
                else: ehi = em
            e_meas = 0.5*(elo+ehi)
            extra = (f" = {e_meas/pr['Xg']*100:.4f}% of Xg"
                     if key == 'Xg'
                     else f" = {e_meas/(2*math.pi)*1e3:.3f} mHz")
            out(f"  TONGUE u={key}: |pi|={abs(pi_eff):.4g} "
                f"pred={eps_t:.4e} meas={e_meas:.4e}{extra} "
                f"err={(eps_t-e_meas)/e_meas*100:+.2f}% "
                f"[{time.time()-T0:.0f}s]")
        else:
            out(f"  TONGUE u={key}: bracket failed (pred {eps_t:.3e}, "
                f"cap {cap:.3e})")
    if not do_boundary:
        continue
    # (3) sudden-on + winding, Xg channel
    wd = 0.9*w0; Td = 2*math.pi/wd
    key = 'Xg'
    def probe(eps, NPn):
        def f(t, x):
            return rhs_w(x, dict(pr, Xg=pr['Xg'] + eps*math.cos(wd*t)))
        def e_th(t, x): return abs(x[0] - st[0]) - (dsad + 0.15)
        def e_vlo(t, x): return x[2] - 0.2
        def e_vhi(t, x): return x[2] - 2.5
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
        ev = [len(s.t_events[i]) > 0 for i in range(3)]
        if any(ev) or s.status < 0:
            return ('TH' if ev[0] else 'VLO' if ev[1]
                    else 'VHI' if ev[2] else 'SOLVER')
        return None
    CAP = 0.025*pr['Xg']
    elo, ehi = 1e-6, 3e-6
    n = 0
    while probe(ehi, 300) is None and ehi < CAP and n < 24:
        elo = ehi; ehi *= 1.5; n += 1
    if probe(min(ehi, CAP), 300) is None:
        out(f"  SUDDEN-ON Xg: no escape to cap {CAP:.3e} "
            f"({CAP/pr['Xg']*100:.1f}% of Xg)")
        continue
    ehi = min(ehi, CAP)
    for _ in range(12):
        em = 0.5*(elo+ehi)
        if probe(em, 300) is not None: ehi = em
        else: elo = em
    if probe(elo, 900) is not None:
        ehi = elo; elo = 0.7*elo
        for _ in range(10):
            em = 0.5*(elo+ehi)
            if probe(em, 900) is not None: ehi = em
            else: elo = em
    emeas = 0.5*(elo+ehi)
    mode = probe(ehi, 900)
    out(f"  SUDDEN-ON Xg: eps_c={emeas:.4e} "
        f"({emeas/pr['Xg']*100:.4f}% of Xg) mode={mode} "
        f"[{time.time()-T0:.0f}s]")
    # winding criterion
    def flow_auto(x0, T, with_var=False):
        def f(t, y):
            x = y[:4]
            if not with_var:
                return rhs_w(x, pr)
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs_w(x, pr),
                                   (jac_a(x, pr) @ Phi).ravel()])
        y0 = (x0 if not with_var
              else np.concatenate([x0, np.eye(4).ravel()]))
        s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12,
                      atol=1e-14)
        return (s.y[:4, -1] if not with_var
                else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
    def cyc(xs, Ts, itmax=40):
        x, T = xs.copy(), Ts
        fref = rhs_w(xs, pr)
        for it in range(itmax):
            xT, M = flow_auto(x, T, with_var=True)
            R = np.append(xT - x, np.dot(fref, x - xs))
            if np.max(np.abs(R)) < 1e-12:
                return x, T, True
            A5 = np.zeros((5, 5))
            A5[:4, :4] = M - np.eye(4)
            A5[:4, 4] = rhs_w(xT, pr)
            A5[4, :4] = fref
            dy = np.linalg.solve(A5, -R)
            n2 = np.linalg.norm(dy[:4])
            cap2 = max(0.01, 0.5*zg)
            if n2 > cap2: dy *= cap2/n2
            if abs(dy[4]) > 0.1*T: dy *= 0.1*T/abs(dy[4])
            x = x + dy[:4]; T = T + dy[4]
        return x, T, np.max(np.abs(R)) < 1e-9
    got = False
    for fac in (1.0, 0.85, 0.7, 1.2):
        xs = st + 2*np.real(fac*zg*qv)
        Ts = 2*math.pi/(w0 + c1v.imag*(fac*zg)**2)
        x0c, Tc, okc = cyc(xs, Ts)
        if okc and abs(np.vdot(pv, x0c - st)) > 0.2*zg:
            got = True; break
    if not got:
        out("  cycle failed"); continue
    scc = solve_ivp(lambda t, x: rhs_w(x, pr), (0, Tc), x0c,
                    method='DOP853', rtol=1e-12, atol=1e-14,
                    t_eval=np.arange(K)*Tc/K)
    U = scc.y.T.copy()
    def strobe_x(x0, eps):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, Xg=pr['Xg'] + eps*math.cos(wd*t))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs_w(x, qq),
                                   (jac_a(x, qq) @ Phi).ravel()])
        y0 = np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11,
                      atol=1e-13)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def torus_newton(U, rho, eps, itmax=25, tol=1e-10):
        Uref = U.copy(); dUref = dtheta_(Uref)
        res = None
        for it in range(itmax):
            Sh = shift_mat(rho)
            PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
            for j in range(K):
                PhiU[j], Ms[j] = strobe_x(U[j], eps)
            R = PhiU - Sh @ U
            c = float(np.sum(dUref*(U - Uref)))
            res = max(np.max(np.abs(R)), abs(c))
            if res < tol:
                return U, rho, True
            Am = np.zeros((4*K+1, 4*K+1))
            for j in range(K):
                Am[4*j:4*j+4, 4*j:4*j+4] += Ms[j]
            Am[:4*K, :4*K] -= np.kron(Sh, I4)
            Am[:4*K, -1] = -(dshift_mat(rho) @ U).flatten()
            Am[-1, :4*K] = dUref.flatten()
            dy = np.linalg.solve(Am, -np.concatenate([R.flatten(), [c]]))
            nU = np.max(np.abs(dy[:4*K]))
            cap2 = max(0.005, 0.5*zg)
            if nU > cap2: dy *= cap2/nU
            U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
        return U, rho, res < 1e-9
    def winding(Ua):
        dens = upsample(Ua, 2048)
        Z = (dens - st) @ np.conj(pv)
        dph = np.angle(Z*np.conj(np.roll(Z, 1)))
        return int(round(float(np.sum(dph))/(2*math.pi)))
    rho = 2*math.pi*((Td/Tc) % 1.0)
    U, rho, ok = torus_newton(U, rho, 0.0)
    if not ok:
        out("  eps=0 torus Newton failed"); continue
    wref = winding(U)
    eps = 0.0; deps = 0.04*emeas; flip = None
    while eps < 1.3*emeas:
        e_try = eps + deps
        Un, rn, okn = torus_newton(U.copy(), rho, e_try)
        if not okn:
            deps *= 0.5
            if deps < 2e-4*emeas: break
            continue
        if winding(Un) != wref:
            flip = (eps, e_try); break
        U, rho, eps = Un, rn, e_try
        deps = min(deps*1.3, 0.05*emeas)
    if flip:
        ea, eb = flip
        Ua, ra = U.copy(), rho
        for _ in range(10):
            em = 0.5*(ea+eb)
            Um, rm, okm = torus_newton(Ua.copy(), ra, em)
            if not okm:
                eb = em; continue
            if winding(Um) == wref:
                ea, Ua, ra = em, Um, rm
            else:
                eb = em
        ef = 0.5*(ea+eb)
        out(f"  RESULT flip(Xg)={ef:.4e} meas={emeas:.4e} "
            f"err={(ef-emeas)/emeas*100:+.2f}% [{time.time()-T0:.0f}s]")
    else:
        out("  no winding flip up to 1.3x meas")
out(f"DONE wall={time.time()-T0:.0f}s")
