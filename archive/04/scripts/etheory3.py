"""E-GFL fiber-corrected prediction.
Correction over etheory: W^s membership is tested against the TRUE stable
fibers — planes spanned by the guard cycle's stable Floquet eigenvectors
at each phase (the fibers tilt away from st's eigenplanes by O(guard
amplitude); etheory's modal-loop test ignored the tilt).
  solve  x_b + kappa*khat = u(theta) + c1 v1(theta) + c2 v2(theta)
over (kappa, theta, c1, c2); kappa_c = smallest positive root.
Planes: cycle Floquet (theta-matched, also used for eps>0 torus — the
fiber tilt is O(zg), the torus correction to it is O(eps) smaller).
Compare with the 14-bit measurements of etheory2.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/etheory3.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])

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
co = nf_coeffs(pr)
st = co['st']; alpha = co['alpha']; w0 = co['w0']
c1v = co['c1']; qv = co['q']; pv = co['p']
wd = 0.9*w0
Td = 2*math.pi/wd
zg = math.sqrt(alpha/c1v.real)
EPSC = 1.1865e-4
K = 32

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
        if n > 0.01:
            dy *= 0.01/n
        if abs(dy[4]) > 0.1*T:
            dy *= 0.1*T/abs(dy[4])
        x = x + dy[:4]; T = T + dy[4]
    return x, T, np.max(np.abs(R)) < 1e-9
cyc = None
for fac in (1.0, 0.85, 0.7, 1.2):
    xs = st + 2*np.real(fac*zg*qv)
    Ts = 2*math.pi/(w0 + c1v.imag*(fac*zg)**2)
    x0c, Tc, okc = cycle_newton(xs, Ts)
    if okc and abs(np.vdot(pv, x0c - st)) > 0.2*zg:
        cyc = (x0c, Tc); break
x0c, Tc = cyc
out(f"cycle T={Tc:.6f}")
# sample points and per-point monodromy -> stable Floquet planes
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
planes = np.array(planes)          # (K,4,2)

# torus machinery for eps>0 sections
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
def strobe_var(x0, eps):
    def f(t, y):
        x = y[:4]
        qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        Phi = y[4:].reshape(4, 4)
        return np.concatenate([rhs(x, qq), (jac_a(x, qq) @ Phi).ravel()])
    y0 = np.concatenate([x0, np.eye(4).ravel()])
    s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11, atol=1e-13)
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
def torus_newton(U, rho, eps, itmax=25, tol=1e-10):
    Uref = U.copy(); dUref = dtheta(Uref)
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
        if nU > 0.005:
            dy *= 0.005/nU
        U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
    return U, rho, res < 1e-9
def newton_fp(xg, eps, itmax=25):
    x = xg.copy()
    for it in range(itmax):
        xT, M = strobe_var(x, eps)
        Fx = xT - x
        if np.max(np.abs(Fx)) < 1e-11:
            return x
        x = x + np.linalg.solve(M - np.eye(4), -Fx)
    return x

khat = 2*np.real(qv)               # kick direction (kappa in modal units)
def kappa_fiber(xb, Upts):
    # for each theta_j: LSQ solve xb + k*khat = u_j + c1 v1 + c2 v2
    best = None
    res_arr = np.zeros(K); kap_arr = np.zeros(K)
    for j in range(K):
        A = np.column_stack([khat, -planes[j][:, 0], -planes[j][:, 1]])
        bvec = Upts[j] - xb
        sol, res, rk, sv = np.linalg.lstsq(A, bvec, rcond=None)
        r = np.linalg.norm(A @ sol - bvec)
        res_arr[j] = r; kap_arr[j] = sol[0]
    # crossings: local minima of residual with kappa>0; refine by parabola
    cands = []
    for j in range(K):
        jm, jp = (j-1) % K, (j+1) % K
        if res_arr[j] <= res_arr[jm] and res_arr[j] <= res_arr[jp] \
           and kap_arr[j] > 0:
            cands.append((res_arr[j], kap_arr[j]))
    cands.sort()
    return cands[0][1] if cands else None, cands[0][0] if cands else None

MEAS = {0.0: 8.49670e-3, 0.3: 7.99866e-3, 0.6: 7.13684e-3,
        0.85: 6.08582e-3}
# eps=0
kp, rr = kappa_fiber(st.copy(), Uc)
out(f"eps_bg=0.00x: pred={kp:.5e} (fiber res {rr:.1e}) "
    f"meas={MEAS[0.0]:.5e} err={(kp-MEAS[0.0])/MEAS[0.0]*100:+.2f}%")
# eps>0: continue torus, locked orbit; planes theta-matched from cycle
U = Uc.copy()
rho = 2*math.pi*((Td/Tc) % 1.0)
U, rho, ok = torus_newton(U, rho, 0.0)
eps = 0.0
deps = 0.1*EPSC
for fbg in (0.3, 0.6, 0.85):
    tgt = fbg*EPSC
    while eps < tgt*0.9999:
        e_try = min(eps + deps, tgt)
        Un, rn, okn = torus_newton(U.copy(), rho, e_try)
        if not okn:
            deps *= 0.5; continue
        U, rho, eps = Un, rn, e_try
        deps = min(deps*1.4, 0.15*EPSC)
    xL = newton_fp(st.copy(), eps)
    kp, rr = kappa_fiber(xL, U)
    mm = MEAS[fbg]
    out(f"eps_bg={fbg:.2f}x: pred={kp:.5e} (fiber res {rr:.1e}) "
        f"meas={mm:.5e} err={(kp-mm)/mm*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
