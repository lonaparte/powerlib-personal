"""GFL erosion cells for P and Q backgrounds (e5 fiber protocol,
forcing channel parameterized). Sets: G1 m0.10, Xg=0.70, mix16;
channels P, Q. Per (set,channel): flip search (channel-scaled steps,
G1-P flip known from pgflsudden), torus continuation to
eps_bg = 0.6 eps_c, pre-kick state = strobe fixed point, prediction =
kick ray (2 Re q) x stable-plane family of torus points, measurement =
kick bisection with compound events under continuing forcing.
Budget ~35 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/pqgflerosion.log', 'w')
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

SETS = [
    dict(tag='G1 m0.10', over={}, marg=0.10, epscV=1.1865e-4,
         known={'P': 2.7914e-4}),
    dict(tag='Xg=0.70', over=dict(Xg=0.70), marg=0.10, epscV=4.0434e-4,
         known={}),
    dict(tag='mix16', over=dict(kp=45., ki=900., Xg=0.55), marg=0.10,
         epscV=5.0766e-4, known={}),
]

for S in SETS:
    prb = gset('G1', **S['over'])
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
    P0 = margin_point(prb, 0.5*(lo+hi), S['marg'])
    pr = dict(prb, P=P0)
    co = nf_coeffs(pr)
    st = co['st']; alpha = co['alpha']; w0 = co['w0']
    c1v = co['c1']; qv = co['q']; pv = co['p']
    wd = 0.9*w0
    Td = 2*math.pi/wd
    zg = math.sqrt(alpha/c1v.real)
    hq = 1e-6
    fV = (rhs(st, dict(pr, V=pr['V']+hq))
          - rhs(st, dict(pr, V=pr['V']-hq)))/(2*hq)
    fP = np.zeros(4); fP[2] = 1.0/pr['C']
    fQ = (rhs(st, dict(pr, Q=pr['Q']+hq))
          - rhs(st, dict(pr, Q=pr['Q']-hq)))/(2*hq)
    pf = {'V': abs(np.vdot(pv, fV)), 'P': abs(np.vdot(pv, fP)),
          'Q': abs(np.vdot(pv, fQ))}
    out(f"{S['tag']}: P0={P0:.5f} w0={w0:.3f} zg={zg:.3e} "
        f"|pf|V/P/Q={pf['V']:.3g}/{pf['P']:.3g}/{pf['Q']:.3g}")
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
    if cyc is None:
        out("  cycle failed — skip set"); continue
    x0c, Tc = cyc
    scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c,
                    method='DOP853', rtol=1e-12, atol=1e-14,
                    t_eval=np.arange(K)*Tc/K)
    Uc = scc.y.T.copy()
    planes = []
    for j in range(K):
        xT, Mj = flow_auto(Uc[j], Tc, with_var=True)
        ev2, V2 = np.linalg.eig(Mj)
        ks = np.argsort(np.abs(ev2))
        v = V2[:, ks[0]]
        if abs(ev2[ks[0]].imag) > 1e-12:
            B = np.stack([v.real, v.imag], axis=1)
        else:
            B = np.stack([V2[:, ks[0]].real, V2[:, ks[1]].real], axis=1)
        Q2, _ = np.linalg.qr(B)
        planes.append(Q2)
    planes = np.array(planes)
    khat = 2*np.real(qv)
    def kappa_fiber(xb, Upts):
        res_arr = np.zeros(K); kap_arr = np.zeros(K)
        for j in range(K):
            A = np.column_stack([khat, -planes[j][:, 0],
                                 -planes[j][:, 1]])
            bvec = Upts[j] - xb
            sol, _, _, _ = np.linalg.lstsq(A, bvec, rcond=None)
            res_arr[j] = np.linalg.norm(A @ sol - bvec)
            kap_arr[j] = sol[0]
        cands = sorted((res_arr[j], kap_arr[j]) for j in range(K)
                       if kap_arr[j] > 0
                       and res_arr[j] <= res_arr[(j-1) % K]
                       and res_arr[j] <= res_arr[(j+1) % K])
        return cands[0][1] if cands else None
    def make_forced(key, u0):
        def strobe_var(x0, eps):
            def f(t, y):
                x = y[:4]
                qq = dict(pr, **{key: u0 + eps*math.cos(wd*t)})
                Phi = y[4:].reshape(4, 4)
                return np.concatenate([rhs(x, qq),
                                       (jac_a(x, qq) @ Phi).ravel()])
            y0 = np.concatenate([x0, np.eye(4).ravel()])
            s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11,
                          atol=1e-13)
            return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
        def frc(t, x, eps):
            return rhs(x, dict(pr, **{key: u0 + eps*math.cos(wd*t)}))
        return strobe_var, frc
    def torus_newton(strobe_var, U, rho, eps, itmax=25, tol=1e-10):
        Uref = U.copy(); dUref = dtheta(Uref)
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
            cap = max(0.005, 0.5*zg)
            if nU > cap:
                dy *= cap/nU
            U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
        return U, rho, res < 1e-9
    def newton_fp(strobe_var, xg, eps, itmax=25):
        x = xg.copy()
        for it in range(itmax):
            xT, M = strobe_var(x, eps)
            Fx = xT - x
            if np.max(np.abs(Fx)) < 1e-11:
                return x
            x = x + np.linalg.solve(M - np.eye(4), -Fx)
        return x
    def winding(Ua):
        dens = upsample(Ua, 2048)
        Z = (dens - st) @ np.conj(pv)
        dph = np.angle(Z*np.conj(np.roll(Z, 1)))
        return int(round(float(np.sum(dph))/(2*math.pi)))
    def measure(frc, eps, pred):
        Tset = Td*math.ceil(150/Td)
        if eps > 0:
            s = solve_ivp(lambda t, x: frc(t, x, eps), (0, Tset),
                          st.copy(), method='DOP853', rtol=1e-9,
                          atol=1e-12)
            xb = s.y[:, -1]
        else:
            xb = st.copy()
        def esc(kap):
            xk = xb + kap*khat
            def e_th(t, x): return abs(x[0] - st[0]) - 1.2
            def e_vlo(t, x): return x[2] - 0.2
            def e_vhi(t, x): return x[2] - 2.5
            for e in (e_th, e_vlo, e_vhi):
                e.terminal = True
            e_th.direction = 1; e_vlo.direction = -1
            e_vhi.direction = 1
            s = solve_ivp(lambda t, x: frc(t, x, eps),
                          (Tset, Tset+150), xk, method='DOP853',
                          rtol=1e-8, atol=1e-12,
                          events=(e_th, e_vlo, e_vhi))
            return (any(len(t) > 0 for t in s.t_events)
                    or s.status < 0)
        klo, khi = 0.0, 2.5*pred
        if not esc(khi):
            khi = 5*pred
        for _ in range(12):
            km = 0.5*(klo+khi)
            if esc(km): khi = km
            else: klo = km
        return 0.5*(klo+khi)
    # unforced anchor (channel-independent)
    sv0, frc0 = make_forced('V', pr['V'])
    kp0 = kappa_fiber(st.copy(), Uc)
    m0 = measure(frc0, 0.0, kp0)
    out(f"  anchor eps_bg=0: pred={kp0:.4e} meas={m0:.4e} "
        f"err={(kp0-m0)/m0*100:+.2f}% [{time.time()-T0:.0f}s]")
    for key in ('P', 'Q'):
        u0 = pr[key]
        strobe_var, frc = make_forced(key, u0)
        epsc = S['known'].get(key)
        U = Uc.copy()
        rho = 2*math.pi*((Td/Tc) % 1.0)
        U, rho, ok = torus_newton(strobe_var, U, rho, 0.0)
        if not ok:
            out(f"  {key}: eps=0 Newton failed"); continue
        if epsc is None:
            eguess = S['epscV']*pf['V']/pf[key]
            w_ref = winding(U)
            eps = 0.0; deps = 0.05*eguess
            Uf, rf = U.copy(), rho
            flip = None
            while eps < 3.0*eguess:
                e_try = eps + deps
                Un, rn, okn = torus_newton(strobe_var, Uf.copy(), rf,
                                           e_try)
                if not okn:
                    deps *= 0.5
                    if deps < 1e-3*eguess:
                        break
                    continue
                if winding(Un) != w_ref:
                    flip = (eps, e_try)
                    break
                Uf, rf, eps = Un, rn, e_try
                deps = min(deps*1.35, 0.08*eguess)
            if flip is None:
                out(f"  {key}: no flip found (guess {eguess:.2e})")
                continue
            ea, eb = flip
            for _ in range(8):
                em = 0.5*(ea+eb)
                Um, rm, okm = torus_newton(strobe_var, Uf.copy(), rf, em)
                if not okm:
                    eb = em; continue
                if winding(Um) == w_ref:
                    ea, Uf, rf = em, Um, rm
                else:
                    eb = em
            epsc = 0.5*(ea+eb)
            out(f"  {key}: flip eps_c={epsc:.4e} "
                f"(guess {eguess:.2e}) [{time.time()-T0:.0f}s]")
        ebg = 0.6*epsc
        U2 = Uc.copy()
        rho2 = 2*math.pi*((Td/Tc) % 1.0)
        U2, rho2, ok = torus_newton(strobe_var, U2, rho2, 0.0)
        eps = 0.0; deps = 0.15*ebg
        while eps < ebg*0.9999:
            e_try = min(eps + deps, ebg)
            Un, rn, okn = torus_newton(strobe_var, U2.copy(), rho2,
                                       e_try)
            if not okn:
                deps *= 0.5; continue
            U2, rho2, eps = Un, rn, e_try
            deps = min(deps*1.4, 0.25*ebg)
        xL = newton_fp(strobe_var, st.copy(), ebg)
        kpb = kappa_fiber(xL, U2)
        mb = measure(frc, ebg, kpb)
        out(f"  RESULT {S['tag']} bg={key} 0.6x: pred={kpb:.4e} "
            f"meas={mb:.4e} err={(kpb-mb)/mb*100:+.2f}% "
            f"erosion={(m0-mb)/m0*100:+.1f}% [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
