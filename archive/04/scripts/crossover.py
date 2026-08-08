"""Crossover-band test: does the guard-torus winding criterion extend to
the intermediate drive frequency wd=5.0 rad/s (r=0.154, the point where
the slow reduction erred -33%)? Measured escape amplitude: 3.163e-3.
Watch for 1:2 locking (rho0 = 2.968 vs pi = 3.142).
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/crossover.log', 'w')
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
wd = 5.0
Td = 2*math.pi/wd
zg = math.sqrt(alpha/c1v.real)
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
def strobe_var(x0, eps):
    def f(t, y):
        x = y[:4]
        qq = dict(pr, V=pr['V'] - eps*math.sin(wd*t))
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
            return U, rho, True, res
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
    return U, rho, res < 1e-9, res
def winding(Ua):
    dens = upsample(Ua, 4096)
    Z = (dens - st) @ np.conj(pv)
    dph = np.angle(Z*np.conj(np.roll(Z, 1)))
    return int(round(float(np.sum(dph))/(2*math.pi)))
def spread(Ua):
    return float(np.max(np.linalg.norm(Ua - Ua.mean(axis=0), axis=1)))
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
scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
                rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
U = scc.y.T.copy()
rho = 2*math.pi*((Td/Tc) % 1.0)
out(f"wd=5.0 Td={Td:.4f} rho0={rho:.4f} (pi={math.pi:.4f})")
U, rho, ok, res = torus_newton(U, rho, 0.0)
sp0 = spread(U)
w_ref = winding(U)
eps = 0.0
deps = 1e-4
flip = None
while True:
    e_try = eps + deps
    Un, rn, okn, resn = torus_newton(U.copy(), rho, e_try)
    if not okn or spread(Un) < 0.4*sp0:
        deps *= 0.5
        if deps < 1e-7:
            out(f"stall at eps={eps:.4e} rho={rho:.4f} "
                f"(1:2 locking suspected)")
            break
        continue
    wn = winding(Un)
    if wn != w_ref:
        flip = (eps, e_try)
        break
    U, rho, eps = Un, rn, e_try
    out(f"  eps={eps:.4e} rho={rho:.5f} "
        f"min|z|={np.min(np.abs((upsample(U,1024)-st)@np.conj(pv))):.3e}")
    if eps > 6e-3:
        out("no flip by 6e-3"); break
    deps = min(deps*1.4, 4e-4)
if flip is not None:
    ea, eb = flip
    Ua, ra = U.copy(), rho
    for _ in range(12):
        em = 0.5*(ea+eb)
        Um, rm, okm, resm = torus_newton(Ua.copy(), ra, em)
        if not okm:
            eb = em; continue
        if winding(Um) == w_ref:
            ea, Ua, ra = em, Um, rm
        else:
            eb = em
    ef = 0.5*(ea+eb)
    MEAS = 3.163e-3
    out(f"RESULT crossover: eps_flip={ef:.4e} meas_a_c={MEAS:.4e} "
        f"err={(ef-MEAS)/MEAS*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
