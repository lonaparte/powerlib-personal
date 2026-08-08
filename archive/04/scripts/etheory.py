"""GFL erosion law — mechanistic prediction and check.
Claim: the kick threshold is the modal-plane distance from the locked
point z_L(eps) to the guard-torus modal loop Z_G(eps) along the kick
direction d = 1 + <p, qbar>  (stable fibers extend along fast directions,
so W^s(Gamma) membership is a modal-plane condition — m5 result).
  kappa_c(eps) = min{k>0 : z_L + k*d  hits  Z_G(eps)}
Zero fitting: all objects (xL, Gamma) computed by Newton/collocation.
Check vs measured phase-0 kick bisection: G1 (existing) + C=0.02 (fresh).
"""
exec(open('selfhead.py').read())
import time, os
os.makedirs('sweep20', exist_ok=True)
LOG = open('sweep20/etheory.log', 'w')
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
def dtheta(Ua):
    return np.real(np.fft.ifft(np.fft.fft(Ua, axis=0)
                               * (1j*mfreq)[:, None], axis=0))
def upsample(Ua, N):
    C = np.fft.fft(Ua, axis=0)
    Cp = np.zeros((N, Ua.shape[1]), complex)
    hf = K//2
    Cp[:hf] = C[:hf]; Cp[N-hf+1:] = C[hf+1:]
    Cp[hf] = 0.5*C[hf]; Cp[N-hf] = 0.5*C[hf]
    return np.real(np.fft.ifft(Cp, axis=0))*(N/K)

def run_case(tag, over, marg, epsc, targets, meas=None):
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
    PH = 0.5*(lo+hi)
    P = margin_point(prb, PH, marg)
    pr = dict(prb, P=P)
    co = nf_coeffs(pr)
    st = co['st']; alpha = co['alpha']; w0 = co['w0']
    c1v = co['c1']; qv = co['q']; pv = co['p']
    wd = 0.9*w0
    Td = 2*math.pi/wd
    zg = math.sqrt(alpha/c1v.real)
    out(f"{tag}: P={P:.5f} alpha={alpha:.4f} w0={w0:.4f} zg={zg:.4e}")

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
        Uref = U.copy(); dUref = dtheta(Uref); Ms = None
        for it in range(itmax):
            Sh = shift_mat(rho)
            PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
            for j in range(K):
                PhiU[j], Ms[j] = strobe_var(U[j], eps)
            R = PhiU - Sh @ U
            c = float(np.sum(dUref*(U - Uref)))
            res = max(np.max(np.abs(R)), abs(c))
            if res < tol:
                return U, rho, Ms, True
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
        return U, rho, Ms, res < 1e-9

    def newton_fp(xg, eps, itmax=25):
        x = xg.copy()
        for it in range(itmax):
            xT, M = strobe_var(x, eps)
            Fx = xT - x
            if np.max(np.abs(Fx)) < 1e-11:
                return x, True
            x = x + np.linalg.solve(M - np.eye(4), -Fx)
        return x, np.max(np.abs(Fx)) < 1e-9

    def flow_auto(x0, T, with_var=False):
        def f(t, y):
            x = y[:4]
            if not with_var:
                return rhs(x, pr)
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, pr), (jac_a(x, pr) @ Phi).ravel()])
        y0 = x0 if not with_var else np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12, atol=1e-14)
        return (s.y[:4, -1] if not with_var
                else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
    def cycle_newton(xs, Ts, itmax=40):
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
    cyc = None
    for fac in (1.0, 0.85, 0.7, 0.6, 1.2, 1.4):
        xs = st + 2*np.real(fac*zg*qv)
        Ts = 2*math.pi/(w0 + c1v.imag*(fac*zg)**2)
        x0c, Tc, okc = cycle_newton(xs, Ts)
        if okc and abs(np.vdot(pv, x0c - st)) > 0.2*zg:
            cyc = (x0c, Tc); break
    x0c, Tc = cyc
    scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
                    rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
    U = scc.y.T.copy()
    rho = 2*math.pi*((Td/Tc) % 1.0)
    U, rho, Ms, ok = torus_newton(U, rho, 0.0)

    ddir = 1 + np.vdot(pv, np.conj(qv))    # <p, 2Re(q)>
    def kray(zL, Zloop):
        # min k>0 with zL + k*ddir on the loop (segment intersection)
        best = None
        Zn = np.append(Zloop, Zloop[0])
        for i in range(len(Zloop)):
            a2 = Zn[i] - zL; b2 = Zn[i+1] - Zn[i]
            Adet = ddir.real*(-b2.real) - (-b2.imag)*(-0)  # build 2x2
            Amat = np.array([[ddir.real, -b2.real], [ddir.imag, -b2.imag]])
            rv = np.array([a2.real, a2.imag])
            try:
                sol = np.linalg.solve(Amat, rv)
            except np.linalg.LinAlgError:
                continue
            k, s = sol
            if k > 0 and 0 <= s < 1:
                if best is None or k < best:
                    best = k
        return best

    # baseline eps=0
    Z0 = (upsample(U, 4096) - st) @ np.conj(pv)
    k0 = kray(0j, Z0)
    out(f"  eps_bg=0: pred kappa_c={k0:.4e}"
        + (f"  meas={meas[0]:.4e}  err={(k0-meas[0])/meas[0]*100:+.2f}%"
           if meas else ""))
    # continuation to targets
    eps = 0.0
    deps = 0.1*epsc
    res_list = []
    for it_t, tgt in enumerate(targets):
        while eps < tgt*0.9999:
            e_try = min(eps + deps, tgt)
            Un, rn, Msn, okn = torus_newton(U.copy(), rho, e_try)
            if not okn:
                deps *= 0.5
                continue
            U, rho, eps = Un, rn, e_try
            deps = min(deps*1.4, 0.15*epsc)
        xL, okL = newton_fp(st.copy(), eps)
        zL = np.vdot(pv, xL - st)
        ZG = (upsample(U, 4096) - st) @ np.conj(pv)
        kp = kray(zL, ZG)
        row = f"  eps_bg={tgt/epsc:.2f}x: pred kappa_c={kp:.4e}"
        if meas:
            mm = meas[1+it_t]
            row += f"  meas={mm:.4e}  err={(kp-mm)/mm*100:+.2f}%"
        out(row)
        res_list.append(kp)
    return res_list

# G1: measured phase-0 values from gfl-E run
run_case('G1 marg0.10', {}, 0.10, 1.1865e-4,
         [0.3*1.1865e-4, 0.6*1.1865e-4, 0.85*1.1865e-4],
         meas=[8.4766e-3, 8.0078e-3, 7.1484e-3, 6.0547e-3])

# C=0.02 set: fresh measurement (phase 0) at 0 and 0.6x its eps_c
def measure_kick(over, marg, epsc, fbg):
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
    for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
        if fa is not None and fb is not None and fa < 0 <= fb:
            lo, hi = a, b; break
    for _ in range(45):
        m = 0.5*(lo+hi)
        v = reA(m)
        if v is None or v >= 0: hi = m
        else: lo = m
    P = margin_point(prb, 0.5*(lo+hi), marg)
    pr = dict(prb, P=P)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; qv = co['q']
    wd = 0.9*w0
    Td = 2*math.pi/wd
    eps = fbg*epsc
    def frc(t, x):
        qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        return rhs(x, qq)
    Tset = Td*math.ceil(150/Td)
    if eps > 0:
        s = solve_ivp(frc, (0, Tset), st.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12)
        xb = s.y[:, -1]
    else:
        xb = st.copy()
    def esc(kap):
        xk = xb + 2*np.real(kap*qv)
        def blow(t, x): return abs(x[0] - st[0]) - 1.2
        blow.terminal = True; blow.direction = 1
        s = solve_ivp(frc, (Tset, Tset+150), xk, method='DOP853',
                      rtol=1e-8, atol=1e-12, events=blow)
        return len(s.t_events[0]) > 0
    klo, khi = 0.0, 0.05
    for _ in range(9):
        km = 0.5*(klo+khi)
        if esc(km): khi = km
        else: klo = km
    return 0.5*(klo+khi)

EPSC6 = 8.2643e-4
m0 = measure_kick(dict(C=0.02), 0.10, EPSC6, 0.0)
m6 = measure_kick(dict(C=0.02), 0.10, EPSC6, 0.6)
out(f"C=0.02 measured: kappa_c(0)={m0:.4e} kappa_c(0.6x)={m6:.4e}")
run_case('C=0.02 marg0.10', dict(C=0.02), 0.10, EPSC6,
         [0.6*EPSC6], meas=[m0, m6])
out(f"DONE wall={time.time()-T0:.0f}s")
