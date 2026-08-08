"""idx17 anomaly: is the +22% the fiber-tilt correction?
Fiber-corrected membership: st in W^s(Gamma) iff some torus point's
stable Floquet plane passes through st:
   g(eps) = min_theta || st - u(theta) - span(v1,v2) ||  -> 0
Find the eps where g bottoms out / crosses ~0; compare with the
measured threshold 8.6656e-3 (=1.22x modal flip). Control set: idx2
(expect eps*_fib ~ 1.00x flip). Budget ~15 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/idx17fib.log', 'w')
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

def run_case(tag, over, marg, rr, eflip, emeas):
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
    P = margin_point(prb, 0.5*(lo+hi), marg)
    pr = dict(prb, P=P)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; qv = co['q']; pv = co['p']
    c1v = co['c1']; alpha = co['alpha']
    wd = rr*w0
    Td = 2*math.pi/wd
    zg = math.sqrt(alpha/c1v.real)
    qn = qv/np.linalg.norm(qv)
    out(f"{tag}: alpha={alpha:.4f} w0={w0:.3f} r={rr} "
        f"|q|=({abs(qn[0]):.3f},{abs(qn[1]):.3f},{abs(qn[2]):.3f},"
        f"{abs(qn[3]):.3f})")
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
        out("  cycle failed"); return
    scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
                    rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
    Uc = scc.y.T.copy()
    planes = []
    for j in range(K):
        xT, Mj = flow_auto(Uc[j], Tc, with_var=True)
        ev, V = np.linalg.eig(Mj)
        ks = np.argsort(np.abs(ev))
        v = V[:, ks[0]]
        if abs(ev[ks[0]].imag) > 1e-12:
            B = np.stack([v.real, v.imag], axis=1)
        else:
            B = np.stack([V[:, ks[0]].real, V[:, ks[1]].real], axis=1)
        Q, _ = np.linalg.qr(B)
        planes.append(Q)
    planes = np.array(planes)
    def strobe_var(x0, eps):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq), (jac_a(x, qq) @ Phi).ravel()])
        y0 = np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11,
                      atol=1e-13)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def torus_newton(U, rho, eps, itmax=25, tol=1e-10):
        Uref = U.copy(); dUref = dtheta_(Uref)
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
            cap = max(0.005, 0.5*zg)
            if nU > cap:
                dy *= cap/nU
            U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
        return U, rho, res < 1e-9
    def gfib(U):
        best = None
        for j in range(K):
            A = planes[j]                       # 4x2
            bvec = st - U[j]
            sol, _, _, _ = np.linalg.lstsq(A, bvec, rcond=None)
            r = np.linalg.norm(A @ sol - bvec)
            if best is None or r < best:
                best = r
        return best
    U = Uc.copy()
    rho = 2*math.pi*((Td/Tc) % 1.0)
    U, rho, ok = torus_newton(U, rho, 0.0)
    eps = 0.0
    deps = 0.02*eflip
    prev_g = gfib(U)
    out(f"  eps=0: g_fib={prev_g:.4e}")
    hist = []
    while eps < 1.32*eflip:
        e_try = eps + deps
        Un, rn, okn = torus_newton(U.copy(), rho, e_try)
        if not okn:
            deps *= 0.5
            if deps < 1e-4*eflip:
                out(f"  stall at {eps:.4e}"); break
            continue
        U, rho, eps = Un, rn, e_try
        g = gfib(U)
        hist.append((eps, g))
        out(f"  eps={eps/eflip:.3f}x flip: g_fib={g:.4e} "
            f"[{time.time()-T0:.0f}s]")
        deps = min(deps*1.3, 0.03*eflip)
    if hist:
        gmin = min(hist, key=lambda t: t[1])
        out(f"  RESULT {tag}: g_fib minimum {gmin[1]:.3e} at "
            f"eps={gmin[0]:.4e} = {gmin[0]/eflip:.3f}x flip; "
            f"measured threshold {emeas:.4e} = {emeas/eflip:.2f}x flip")

run_case('idx17', dict(kp=55., ki=1200., Xg=0.40), 0.08, 0.92,
         7.0991e-3, 8.6656e-3)
out(f"DONE wall={time.time()-T0:.0f}s")
