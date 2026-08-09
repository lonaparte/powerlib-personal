"""P-channel sudden-on thresholds for GFL (flagged cell).
Forcing P(t) = P0 + eps_P cos(0.9 w0 t). Per set:
(1) measurement: compound detector (theta/Vdc/solver events),
    300-period bisection + 900-period low-edge recheck;
(2) criterion: guard-cycle -> invariant-curve continuation with
    P-forcing strobe map, winding flip of <p, U(theta)-st>;
(3) report <p,f_P> coupling and V-channel flip for comparison.
Sets: G1 (strong, theta-family), idx2 kp30ki600 (weak, Vdc-family),
idx11 V=1.06 (weak, Vdc-family). Budget ~25 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/pgflsudden.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])
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
        ('idx2 kp30ki600 weak', dict(kp=30., ki=600.), 0.10, 7.40969e-3),
        ('idx11 V=1.06 weak', dict(V=1.06), 0.10, 6.61695e-3)]

for tag, over, marg, vflip in SETS:
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
    lo, hi = br
    for _ in range(45):
        m = 0.5*(lo+hi)
        v = reA(m)
        if v is None or v >= 0: hi = m
        else: lo = m
    P0 = margin_point(prb, 0.5*(lo+hi), marg)
    pr = dict(prb, P=P0)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; qv = co['q']; pv = co['p']
    c1v = co['c1']; alpha = co['alpha']
    zg = math.sqrt(alpha/c1v.real)
    dsad = math.pi - 2*abs(st[0])
    wd = 0.90*w0
    Td = 2*math.pi/wd
    fP = np.zeros(4); fP[2] = 1.0/pr['C']
    pfP = abs(np.vdot(pv, fP))
    hq = 1e-6
    fV = (rhs(st, dict(pr, V=pr['V']+hq))
          - rhs(st, dict(pr, V=pr['V']-hq)))/(2*hq)
    pfV = abs(np.vdot(pv, fV))
    qn = qv/np.linalg.norm(qv)
    out(f"{tag}: P0={P0:.5f} w0={w0:.3f} zg={zg:.3e} "
        f"|q|=({abs(qn[0]):.2f},{abs(qn[1]):.2f},{abs(qn[2]):.2f},"
        f"{abs(qn[3]):.2f}) |<p,fP>|={pfP:.3g} |<p,fV>|={pfV:.3g}")
    # ---- (1) measurement ----
    CAP = 0.5*P0
    def probe(eps, NPn):
        def f(t, x):
            return rhs(x, dict(pr, P=P0 + eps*math.cos(wd*t)))
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
            which = ('TH' if ev[0] else 'VLO' if ev[1]
                     else 'VHI' if ev[2] else 'SOLVER')
            return which
        return None
    elo, ehi = 1e-5, 3e-5
    n = 0
    while probe(ehi, 300) is None and ehi < CAP and n < 24:
        elo = ehi; ehi *= 1.5; n += 1
    if probe(ehi, 300) is None:
        out(f"  MEAS: no escape up to cap {CAP:.3e} (saturation) "
            f"[{time.time()-T0:.0f}s]")
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
    out(f"  MEAS eps_c(P)={emeas:.4e} mode={mode} "
        f"(V-channel flip {vflip:.3e}) [{time.time()-T0:.0f}s]")
    # ---- (2) winding-flip criterion with P forcing ----
    def flow_auto(x0, T, with_var=False):
        def f(t, y):
            x = y[:4]
            if not with_var:
                return rhs(x, pr)
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, pr),
                                   (jac_a(x, pr) @ Phi).ravel()])
        y0 = (x0 if not with_var
              else np.concatenate([x0, np.eye(4).ravel()]))
        s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12,
                      atol=1e-14)
        return (s.y[:4, -1] if not with_var
                else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
    def cyc(xs, Ts, itmax=40):
        x, T = xs.copy(), Ts
        fref = rhs(xs, pr)
        for it in range(itmax):
            xT, M = flow_auto(x, T, with_var=True)
            R = np.append(xT - x, np.dot(fref, x - xs))
            if np.max(np.abs(R)) < 1e-12:
                return x, T, True
            A5 = np.zeros((5, 5))
            A5[:4, :4] = M - np.eye(4)
            A5[:4, 4] = rhs(xT, pr)
            A5[4, :4] = fref
            dy = np.linalg.solve(A5, -R)
            n2 = np.linalg.norm(dy[:4])
            cap2 = max(0.01, 0.5*zg)
            if n2 > cap2:
                dy *= cap2/n2
            if abs(dy[4]) > 0.1*T:
                dy *= 0.1*T/abs(dy[4])
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
    scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c,
                    method='DOP853', rtol=1e-12, atol=1e-14,
                    t_eval=np.arange(K)*Tc/K)
    U = scc.y.T.copy()
    def strobe_var(x0, eps):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, P=P0 + eps*math.cos(wd*t))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq),
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
                PhiU[j], Ms[j] = strobe_var(U[j], eps)
            R = PhiU - Sh @ U
            c = float(np.sum(dUref*(U - Uref)))
            res = max(np.max(np.abs(R)), abs(c))
            if res < tol:
                return U, rho, True
            A = np.zeros((4*K+1, 4*K+1))
            for j in range(K):
                A[4*j:4*j+4, 4*j:4*j+4] += Ms[j]
            A[:4*K, :4*K] -= np.kron(Sh, I4)
            A[:4*K, -1] = -(dshift_mat(rho) @ U).flatten()
            A[-1, :4*K] = dUref.flatten()
            dy = np.linalg.solve(A, -np.concatenate([R.flatten(), [c]]))
            nU = np.max(np.abs(dy[:4*K]))
            cap2 = max(0.005, 0.5*zg)
            if nU > cap2:
                dy *= cap2/nU
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
    eps = 0.0
    deps = 0.04*emeas
    flip = None
    while eps < 1.3*emeas:
        e_try = eps + deps
        Un, rn, okn = torus_newton(U.copy(), rho, e_try)
        if not okn:
            deps *= 0.5
            if deps < 2e-4*emeas:
                out(f"  continuation stall at {eps/emeas:.3f}x meas")
                break
            continue
        if winding(Un) != wref:
            flip = (eps, e_try)
            break
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
        out(f"  RESULT flip(P)={ef:.4e} meas={emeas:.4e} "
            f"err={(ef-emeas)/emeas*100:+.2f}% [{time.time()-T0:.0f}s]")
    else:
        out(f"  no winding flip up to 1.3x meas [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
