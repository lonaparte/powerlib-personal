"""Deep-detuning residual mechanism at r=0.70 (+1.21% flip vs meas).
(1) K=64 continuation -> flip64 vs flip32=4.0270e-4 (collocation
    convergence check).
(2) fiber-corrected membership crossing at K=32: g_fib(eps) =
    min_theta ||st - u(theta) - span(stable plane)||, planes from
    unforced guard-cycle Floquet (idx17fib approx). Crossing vs
    meas=3.9789e-4. Expected: crossing < flip (tilt), nearer meas.
(3) r=0.60: meas + flip32 to map the detuning trend.
Budget ~18 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/gflr70b.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])

prb = gset('G1')
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
P = margin_point(prb, 0.5*(lo+hi), 0.10)
pr = dict(prb, P=P)
co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; qv = co['q']; pv = co['p']
c1v = co['c1']; alpha = co['alpha']
zg = math.sqrt(alpha/c1v.real)
dsad = math.pi - 2*abs(st[0])

def flow_auto(x0, T, with_var=False):
    def f(t, y):
        x = y[:4]
        if not with_var:
            return rhs(x, pr)
        Phi = y[4:].reshape(4, 4)
        return np.concatenate([rhs(x, pr), (jac_a(x, pr) @ Phi).ravel()])
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
        n = np.linalg.norm(dy[:4])
        cap = max(0.01, 0.5*zg)
        if n > cap:
            dy *= cap/n
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
    out("cycle failed"); raise SystemExit
out(f"G1: P={P:.5f} w0={w0:.3f} Tc={Tc:.5f} [{time.time()-T0:.0f}s]")

def machinery(K):
    mfreq = np.fft.fftfreq(K)*K
    I4 = np.eye(4)
    def shift_mat(r):
        ph = np.exp(1j*mfreq*r)
        return np.real(np.fft.ifft(np.fft.fft(np.eye(K), axis=0)
                                   * ph[:, None], axis=0))
    def dshift_mat(r):
        ph = 1j*mfreq*np.exp(1j*mfreq*r)
        return np.real(np.fft.ifft(np.fft.fft(np.eye(K), axis=0)
                                   * ph[:, None], axis=0))
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
    def winding(Ua):
        dens = upsample(Ua, 2048)
        Z = (dens - st) @ np.conj(pv)
        dph = np.angle(Z*np.conj(np.roll(Z, 1)))
        return int(round(float(np.sum(dph))/(2*math.pi)))
    return dict(K=K, shift=shift_mat, dshift=dshift_mat, dth=dtheta_,
                up=upsample, wind=winding, I4=I4)

def run_flip(rr, K, emeas, do_fiber=False):
    mc = machinery(K)
    wd = rr*w0
    Td = 2*math.pi/wd
    def strobe_var(x0, eps):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq),
                                   (jac_a(x, qq) @ Phi).ravel()])
        y0 = np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11,
                      atol=1e-13)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def torus_newton(U, rho, eps, itmax=25, tol=1e-10):
        Uref = U.copy(); dUref = mc['dth'](Uref)
        res = None
        for it in range(itmax):
            Sh = mc['shift'](rho)
            PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
            for j in range(K):
                PhiU[j], Ms[j] = strobe_var(U[j], eps)
            R = PhiU - Sh @ U
            c = float(np.sum(dUref*(U - Uref)))
            res = max(np.max(np.abs(R)), abs(c))
            if res < tol:
                return U, rho, True, res
            A = np.zeros((4*K+1, 4*K+1))
            for j in range(K):
                A[4*j:4*j+4, 4*j:4*j+4] += Ms[j]
            A[:4*K, :4*K] -= np.kron(Sh, mc['I4'])
            A[:4*K, -1] = -(mc['dshift'](rho) @ U).flatten()
            A[-1, :4*K] = dUref.flatten()
            dy = np.linalg.solve(A, -np.concatenate([R.flatten(), [c]]))
            nU = np.max(np.abs(dy[:4*K]))
            cap = max(0.005, 0.5*zg)
            if nU > cap:
                dy *= cap/nU
            U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
        return U, rho, res < 1e-9, res
    scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c,
                    method='DOP853', rtol=1e-12, atol=1e-14,
                    t_eval=np.arange(K)*Tc/K)
    U = scc.y.T.copy()
    rho = 2*math.pi*((Td/Tc) % 1.0)
    U, rho, ok, res = torus_newton(U, rho, 0.0)
    if not ok:
        out(f"r={rr} K={K}: eps=0 Newton failed"); return None
    wref = mc['wind'](U)
    planes = None
    if do_fiber:
        planes = []
        for j in range(K):
            xT, Mj = flow_auto(U[j], Tc, with_var=True)
            ev2, V2 = np.linalg.eig(Mj)
            ks = np.argsort(np.abs(ev2))
            v = V2[:, ks[0]]
            if abs(ev2[ks[0]].imag) > 1e-12:
                Bm = np.stack([v.real, v.imag], axis=1)
            else:
                Bm = np.stack([V2[:, ks[0]].real, V2[:, ks[1]].real],
                              axis=1)
            Q2, _ = np.linalg.qr(Bm)
            planes.append(Q2)
        planes = np.array(planes)
    def gfib(Ua):
        best = None
        for j in range(K):
            A2 = planes[j]
            bvec = st - Ua[j]
            sol, _, _, _ = np.linalg.lstsq(A2, bvec, rcond=None)
            r2 = np.linalg.norm(A2 @ sol - bvec)
            if best is None or r2 < best:
                best = r2
        return best
    eps = 0.0
    deps = 0.04*emeas
    flip = None
    fibx = None
    gprev = gfib(U) if do_fiber else None
    while eps < 1.35*emeas:
        e_try = eps + deps
        Un, rn, okn, resn = torus_newton(U.copy(), rho, e_try)
        if not okn:
            deps *= 0.5
            if deps < 2e-4*emeas:
                out(f"r={rr} K={K}: stall at {eps/emeas:.3f}x"); break
            continue
        if mc['wind'](Un) != wref:
            flip = (eps, e_try)
            break
        U, rho, eps = Un, rn, e_try
        if do_fiber:
            g = gfib(U)
            if fibx is None and g < 0.08*zg:
                fibx = eps
                out(f"  r={rr} K={K}: g_fib crossing (<0.08zg) at "
                    f"eps={eps:.4e} = {eps/emeas:.3f}x meas "
                    f"g={g:.2e} [{time.time()-T0:.0f}s]")
            gprev = g
        deps = min(deps*1.3, 0.05*emeas)
    ef = None
    if flip:
        ea, eb = flip
        Ua, ra = U.copy(), rho
        for _ in range(10):
            em = 0.5*(ea+eb)
            Um, rm, okm, _ = torus_newton(Ua.copy(), ra, em)
            if not okm:
                eb = em; continue
            if mc['wind'](Um) == wref:
                ea, Ua, ra = em, Um, rm
            else:
                eb = em
        ef = 0.5*(ea+eb)
    return ef, fibx

# (1) K=64 at r=0.70
r = run_flip(0.70, 64, 3.9789e-4)
if r and r[0]:
    out(f"r=0.70 K=64: flip={r[0]:.4e} (K=32: 4.0270e-4) "
        f"meas=3.9789e-4 err={(r[0]-3.9789e-4)/3.9789e-4*100:+.2f}% "
        f"[{time.time()-T0:.0f}s]")
# (2) fiber crossing at r=0.70, K=32
r = run_flip(0.70, 32, 3.9789e-4, do_fiber=True)
if r:
    ef, fibx = r
    if fibx:
        out(f"r=0.70 K=32 fiber: crossing={fibx:.4e} "
            f"err vs meas={(fibx-3.9789e-4)/3.9789e-4*100:+.2f}%")
# (3) r=0.60: measure + flip
wd6 = 0.60*w0
Td6 = 2*math.pi/wd6
def probe6(eps, NPn):
    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd6*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - (dsad + 0.15)
    def e_vlo(t, x): return x[2] - 0.2
    def e_vhi(t, x): return x[2] - 2.5
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NPn*Td6), st.copy(), method='DOP853',
                  rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
    ev2 = [len(s.t_events[i]) > 0 for i in range(3)]
    if any(ev2):
        which = 'TH' if ev2[0] else 'VLO' if ev2[1] else 'VHI'
        return which
    return None
elo, ehi = 2e-4, 4e-4
n = 0
while probe6(ehi, 300) is None and n < 12:
    elo = ehi; ehi *= 1.5; n += 1
if probe6(ehi, 300) is not None:
    for _ in range(11):
        em = 0.5*(elo+ehi)
        if probe6(em, 300) is not None: ehi = em
        else: elo = em
    if probe6(elo, 900) is not None:
        ehi = elo; elo = 0.7*elo
        for _ in range(9):
            em = 0.5*(elo+ehi)
            if probe6(em, 900) is not None: ehi = em
            else: elo = em
    meas6 = 0.5*(elo+ehi)
    out(f"r=0.60: MEAS={meas6:.4e} mode={probe6(ehi, 900)} "
        f"[{time.time()-T0:.0f}s]")
    r = run_flip(0.60, 32, meas6, do_fiber=True)
    if r and r[0]:
        out(f"r=0.60 K=32: flip={r[0]:.4e} err={(r[0]-meas6)/meas6*100:+.2f}%"
            + (f" fiber crossing={r[1]:.4e} "
               f"err={(r[1]-meas6)/meas6*100:+.2f}%" if r[1] else ""))
out(f"DONE wall={time.time()-T0:.0f}s")
