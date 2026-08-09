"""The untested exogenous channel: far-grid frequency.
theta is the PLL angle relative to the grid EMF, so a grid frequency
deviation enters the angle equation additively:
      thetadot = kp*vgq + ki*xp - dw(t)
=> f_dw = -e1 (points exactly at the angle state), M1 = 0 exactly
   (dw does not appear in the Jacobian at fixed state).
Structural prediction: for the angle-dominant (strong) family this is
the most strongly coupled channel of all.
Per set: coupling |<p,f_u>| for V/P/Q/dw side by side; the 2w0
parametric tongue (pred vs monodromy measurement); the sudden-on
threshold at 0.9 w0 (compound detector) vs the winding-flip criterion.
Report in rad/s and in mHz of grid-frequency oscillation.
Sets: G1 (strong, angle family), idx2 (weak, DC family).
Budget ~12 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/wchannel.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def rhs_w(x, pr):
    """model with an added grid-frequency deviation pr['dw']"""
    y = rhs(x, pr)
    y = y.copy()
    y[0] -= pr.get('dw', 0.0)
    return y

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])
# dw enters additively -> Jacobian unchanged
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

SETS = [('G1 strong', {}, 0.10, 1.1865e-4),
        ('idx2 weak', dict(kp=30., ki=600.), 0.10, 7.40969e-3)]

for tag, over, marg, vflip in SETS:
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
    fV = (rhs(st, dict(pr, V=pr['V']+hq))
          - rhs(st, dict(pr, V=pr['V']-hq)))/(2*hq)
    fP = np.zeros(4); fP[2] = 1.0/pr['C']
    fQ = (rhs(st, dict(pr, Q=pr['Q']+hq))
          - rhs(st, dict(pr, Q=pr['Q']-hq)))/(2*hq)
    fW = np.array([-1.0, 0.0, 0.0, 0.0])
    qn = qv/np.linalg.norm(qv)
    out(f"{tag}: P0={P0:.5f} w0={w0:.3f} ({w0/(2*math.pi):.2f} Hz) "
        f"zg={zg:.3e} |q|=({abs(qn[0]):.3f},{abs(qn[1]):.3f},"
        f"{abs(qn[2]):.3f},{abs(qn[3]):.3f})")
    out(f"  coupling |<p,f_u>|:  V={abs(np.vdot(pv,fV)):.4g}  "
        f"P={abs(np.vdot(pv,fP)):.4g}  Q={abs(np.vdot(pv,fQ)):.4g}  "
        f"dw={abs(np.vdot(pv,fW)):.4g}")
    # ---------- parametric tongue at 2 w0 ----------
    def B2c(u, v):
        a = _avl(st, pr)
        return np.array([sum(_Hl[i][j][k](*a)*u[j]*v[k]
                             for j in range(4) for k in range(4))
                         for i in range(4)])
    wp = 2*w0; Tdp = 2*math.pi/wp
    hF = np.linalg.solve(2j*w0*np.eye(4) - A, fW)
    pi_eff = np.vdot(pv, B2c(hF, np.conj(qv)))     # M1 = 0 exactly
    eps_t = 2*alpha/abs(pi_eff)
    def strobe_var(x0, eps, wpp, Tdd):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, dw=eps*math.cos(wpp*t))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs_w(x, qq),
                                   (jac_a(x, qq) @ Phi).ravel()])
        y0 = np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, Tdd), y0, method='DOP853', rtol=1e-11,
                      atol=1e-13)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def newton_fp(xg, eps, wpp, Tdd, itmax=25):
        x = xg.copy(); M = None
        for it in range(itmax):
            xT, M = strobe_var(x, eps, wpp, Tdd)
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
        xn, Mn, okn = newton_fp(st.copy(), e, wp, Tdp)
        if not okn: return False
        return float(np.max(np.abs(np.linalg.eigvals(Mn)))) < 1.0
    elo, ehi = 0.6*eps_t, 1.6*eps_t
    n = 0
    while not stab(elo) and n < 6:
        elo /= 1.7; n += 1
    n = 0
    while stab(ehi) and n < 6:
        ehi *= 1.7; n += 1
    if stab(elo) and not stab(ehi):
        for _ in range(12):
            em = 0.5*(elo+ehi)
            if stab(em): elo = em
            else: ehi = em
        e_meas = 0.5*(elo+ehi)
        out(f"  TONGUE(2w0): |pi|={abs(pi_eff):.4g} pred={eps_t:.4e} "
            f"meas={e_meas:.4e} rad/s "
            f"({e_meas/(2*math.pi)*1e3:.3f} mHz) "
            f"err={(eps_t-e_meas)/e_meas*100:+.2f}% "
            f"[{time.time()-T0:.0f}s]")
    else:
        out(f"  TONGUE: bracket failed (pred {eps_t:.3e})")
    # ---------- sudden-on at 0.9 w0 ----------
    wd = 0.9*w0; Td = 2*math.pi/wd
    def probe(eps, NPn):
        def f(t, x):
            return rhs_w(x, dict(pr, dw=eps*math.cos(wd*t)))
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
    elo, ehi = 1e-5, 3e-5
    n = 0
    while probe(ehi, 300) is None and ehi < 5.0 and n < 24:
        elo = ehi; ehi *= 1.5; n += 1
    if probe(ehi, 300) is None:
        out(f"  SUDDEN-ON: no escape up to {ehi:.3e} rad/s")
        continue
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
    out(f"  SUDDEN-ON(0.9w0): eps_c={emeas:.4e} rad/s "
        f"({emeas/(2*math.pi)*1e3:.3f} mHz) mode={mode}  "
        f"[V-channel flip {vflip:.3e} pu] [{time.time()-T0:.0f}s]")
    # ---------- winding-flip criterion ----------
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
    def torus_newton(U, rho, eps, itmax=25, tol=1e-10):
        Uref = U.copy(); dUref = dtheta_(Uref)
        res = None
        for it in range(itmax):
            Sh = shift_mat(rho)
            PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
            for j in range(K):
                PhiU[j], Ms[j] = strobe_var(U[j], eps, wd, Td)
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
        out(f"  RESULT flip(dw)={ef:.4e} meas={emeas:.4e} "
            f"err={(ef-emeas)/emeas*100:+.2f}% [{time.time()-T0:.0f}s]")
    else:
        out(f"  no winding flip up to 1.3x meas")
out(f"DONE wall={time.time()-T0:.0f}s")
