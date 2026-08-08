"""Deep-detuned closure via connection identity (r=0.70, r=0.60).
Threshold mechanism = point-to-torus heteroclinic connection (exactly
verified at r=0.90, landing 2.8e-8). Here: (1) refine measurement with
1500-period window around old bracket; (2) continue guard torus to
eps_c; (3) integrate critical orbit from st at 1.001x/0.999x eps_c,
record min strobe-distance to torus curve -> landing ~0 above, no
landing below = connection identity. (4) transverse decomposition of
st - u(theta*) at flip eps: modal (p,q-plane) vs transverse fraction
-> quantifies why winding proxy degrades with detuning.
Budget ~20 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/gflr70d.log', 'w')
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

RES = {0.70: dict(meas=3.9789e-4, flip=4.0270e-4),
       0.60: dict(meas=5.4360e-4, flip=5.5591e-4)}
for rr in (0.70, 0.60):
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
            cap = max(0.005, 0.5*zg)
            if nU > cap:
                dy *= cap/nU
            U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
        return U, rho, res < 1e-9
    meas0 = RES[rr]['meas']
    # (1) refine measurement, 1500-period window
    def probe(eps, NPn=1500):
        def f(t, x):
            return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
        def e_th(t, x): return abs(x[0] - st[0]) - (dsad + 0.15)
        def e_vlo(t, x): return x[2] - 0.2
        def e_vhi(t, x): return x[2] - 2.5
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
        return any(len(s.t_events[i]) > 0 for i in range(3)) \
            or s.status < 0
    elo, ehi = 0.90*meas0, 1.05*meas0
    if probe(elo):
        elo = 0.75*meas0
    if not probe(ehi):
        ehi = 1.2*meas0
    for _ in range(12):
        em = 0.5*(elo+ehi)
        if probe(em): ehi = em
        else: elo = em
    epsc = 0.5*(elo+ehi)
    out(f"r={rr}: eps_c(1500p)={epsc:.5e} (old 300/900p {meas0:.4e}, "
        f"shift {(epsc-meas0)/meas0*100:+.2f}%) [{time.time()-T0:.0f}s]")
    # (2) torus at eps_c
    scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c,
                    method='DOP853', rtol=1e-12, atol=1e-14,
                    t_eval=np.arange(K)*Tc/K)
    U = scc.y.T.copy()
    rho = 2*math.pi*((Td/Tc) % 1.0)
    U, rho, ok = torus_newton(U, rho, 0.0)
    eps = 0.0
    deps = 0.05*epsc
    while eps < epsc - 1e-12:
        e_try = min(eps + deps, epsc)
        Un, rn, okn = torus_newton(U.copy(), rho, e_try)
        if not okn:
            deps *= 0.5
            if deps < 1e-4*epsc:
                out(f"r={rr}: torus stall {eps/epsc:.3f}x"); break
            continue
        U, rho, eps = Un, rn, e_try
        deps = min(deps*1.3, 0.06*epsc)
    if abs(eps - epsc) > 1e-12:
        continue
    dense = upsample(U, 1024)
    # (3) landing test just above/below eps_c
    def landing(eps, NPn=1500):
        def f(t, x):
            return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
        def e_th(t, x): return abs(x[0] - st[0]) - (dsad + 0.15)
        def e_vlo(t, x): return x[2] - 0.2
        def e_vhi(t, x): return x[2] - 2.5
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        tev = np.arange(NPn)*Td
        s = solve_ivp(f, (0, (NPn-1)*Td), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13,
                      events=(e_th, e_vlo, e_vhi), t_eval=tev)
        X = s.y.T
        dmin = np.inf
        for x in X:
            d = float(np.min(np.linalg.norm(dense - x, axis=1)))
            if d < dmin:
                dmin = d
        esc = any(len(s.t_events[i]) > 0 for i in range(3))
        return dmin, esc
    dup, escup = landing(ehi)
    ddn, escdn = landing(elo)
    out(f"r={rr}: landing above: min dist(orbit,torus)={dup:.2e} "
        f"({dup/zg:.3f} zg) esc={escup}; below: {ddn:.2e} "
        f"({ddn/zg:.3f} zg) esc={escdn} [{time.time()-T0:.0f}s]")
    # (4) transverse decomposition at contact
    dif = dense - st
    j0 = int(np.argmin(np.linalg.norm(dif, axis=1)))
    v = dif[j0]
    zc = np.vdot(pv, v)
    vmod = 2*np.real(zc*qv/np.vdot(qv, qv))  # crude modal-plane part
    # proper modal projector: span{Re q, Im q}
    Qm = np.linalg.qr(np.stack([qv.real, qv.imag], axis=1))[0]
    vm = Qm @ (Qm.T @ v)
    vt = v - vm
    out(f"r={rr}: contact |st-u|={np.linalg.norm(v):.3e}: modal-plane "
        f"part {np.linalg.norm(vm):.3e}, transverse "
        f"{np.linalg.norm(vt):.3e} "
        f"(transverse fraction {np.linalg.norm(vt)/np.linalg.norm(v):.2f})")
    out(f"r={rr}: SUMMARY flip={RES[rr]['flip']:.4e} "
        f"({(RES[rr]['flip']-epsc)/epsc*100:+.2f}% vs eps_c(1500p))")
out(f"DONE wall={time.time()-T0:.0f}s")
