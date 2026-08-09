"""Trajectory measurement of lambda_u, done in the regime where it means
something.

lamu6 ran the departure fit at eps = eps_c(400), which is 2.7% ABOVE the
true threshold.  There the trajectory never shadows the guard curve: it
came within 0.033 r_g and then left across a range 0.033 -> 0.41 r_g,
where the linearisation about the curve is meaningless.  The fit deviated
from a pure exponential by 87% and returned +64% -- that measurement is
withdrawn.

Done properly: drive just above the converged threshold, so the
trajectory spends hundreds of drive periods next to the guard curve, and
fit the growth only over distances small compared with the curve's own
size.  The prediction is the transverse exponent of the same curve at the
same drive amplitude, so both sides are evaluated at one operating point
and no threshold precision enters the comparison.
Set: idx17 (G1 with kp=55, ki=1200, Xg=0.40), margin 0.08, r = 0.92.
Budget ~20 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/lamu7.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])
K = 64
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
def dth_(U):
    return np.real(np.fft.ifft(np.fft.fft(U, axis=0)
                               * (1j*mfreq)[:, None], axis=0))
def upsample(U, N):
    C = np.fft.fft(U, axis=0)
    Cp = np.zeros((N, U.shape[1]), complex)
    hf = K//2
    Cp[:hf] = C[:hf]; Cp[N-hf+1:] = C[hf+1:]
    Cp[hf] = 0.5*C[hf]; Cp[N-hf] = 0.5*C[hf]
    return np.real(np.fft.ifft(Cp, axis=0))*(N/K)

over = dict(kp=55., ki=1200., Xg=0.40)
prb = gset('G1', **over)
Psn = 3*prb['V']**2/(4*prb['Xg'])
def reA(P):
    q = dict(prb, P=P); x = equil(q)
    if x is None: return None
    cm = crit_mode(jac(x, q))
    return None if cm is None else cm.real
grid = np.linspace(0.05, 0.985, 60)*Psn
va = [reA(P) for P in grid]; br = None
for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
    if fa is not None and fb is not None and fa < 0 <= fb:
        br = (a, b); break
lo, hi = br
for _ in range(45):
    m = 0.5*(lo+hi); v = reA(m)
    if v is None or v >= 0: hi = m
    else: lo = m
P0 = margin_point(prb, 0.5*(lo+hi), 0.08)
pr = dict(prb, P=P0)
co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']; c1v = co['c1']
qv = co['q']; pv = co['p']
rg = math.sqrt(alpha/c1v.real)
dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
wd = 0.92*w0; Td = 2*math.pi/wd
out(f"idx17: r_g={rg:.5e} T_d={Td:.6f}s")
def esc_time(eps, NP):
    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NP*Td), st.copy(), method='DOP853',
                  rtol=1e-11, atol=1e-14, events=(e_th, e_vlo, e_vhi))
    ts = [t[0] for t in s.t_events if len(t)]
    if ts: return min(ts)/Td
    if s.status < 0: return s.t[-1]/Td
    return None
elo, ehi = 5e-3, 1.2e-2
while esc_time(ehi, 400) is None and ehi < 5e-2:
    elo = ehi; ehi *= 1.4
while esc_time(elo, 400) is not None and elo > 1e-4:
    ehi = elo; elo *= 0.7
for _ in range(14):
    em = 0.5*(elo+ehi)
    if esc_time(em, 400) is not None: ehi = em
    else: elo = em
e400 = 0.5*(elo+ehi)
elo, ehi = 0.96*e400, e400
for _ in range(22):
    em = 0.5*(elo+ehi)
    if esc_time(em, 4000) is not None: ehi = em
    else: elo = em
estar = 0.5*(elo+ehi)
out(f"eps_c(400)={e400:.8e}, converged eps*={estar:.9e} "
    f"({(estar-e400)/e400*100:+.3f}%)  [{time.time()-T0:.0f}s]")
etest = estar*(1.0 + 3e-4)

def flow(x0, T, var=False):
    def f(t, y):
        x = y[:4]
        if not var:
            return rhs(x, pr)
        return np.concatenate([rhs(x, pr),
                               (jac_a(x, pr) @ y[4:].reshape(4, 4)).ravel()])
    y0 = x0 if not var else np.concatenate([x0, np.eye(4).ravel()])
    s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12, atol=1e-14)
    return (s.y[:4, -1] if not var
            else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
def cyc(xs, Ts):
    x, T = xs.copy(), Ts; fref = rhs(xs, pr); R = np.ones(5)
    for it in range(40):
        xT, M = flow(x, T, var=True)
        R = np.append(xT - x, np.dot(fref, x - xs))
        if np.max(np.abs(R)) < 1e-12:
            return x, T, True
        A5 = np.zeros((5, 5)); A5[:4, :4] = M - np.eye(4)
        A5[:4, 4] = rhs(xT, pr); A5[4, :4] = fref
        dy = np.linalg.solve(A5, -R)
        n2 = np.linalg.norm(dy[:4]); cap = max(0.01, 0.5*rg)
        if n2 > cap: dy *= cap/n2
        if abs(dy[4]) > 0.1*T: dy *= 0.1*T/abs(dy[4])
        x = x + dy[:4]; T = T + dy[4]
    return x, T, np.max(np.abs(R)) < 1e-9
for fac in (1.0, 0.85, 0.7, 1.2):
    xs = st + 2*np.real(fac*rg*qv)
    Ts = 2*math.pi/(w0 + c1v.imag*(fac*rg)**2)
    x0c, Tc, ok = cyc(xs, Ts)
    if ok and abs(np.vdot(pv, x0c - st)) > 0.2*rg:
        break
def strobe(x0, eps):
    def f(t, y):
        x = y[:4]; qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        return np.concatenate([rhs(x, qq),
                               (jac_a(x, qq) @ y[4:].reshape(4, 4)).ravel()])
    s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                  method='DOP853', rtol=1e-12, atol=1e-14)
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
def tn(U, rho, eps, itmax=20, tol=1e-10):
    Uref = U.copy(); dUref = dth_(Uref); res = None
    for it in range(itmax):
        Sh = shift_mat(rho); PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
        for j in range(K):
            PhiU[j], Ms[j] = strobe(U[j], eps)
        R = PhiU - Sh @ U; c = float(np.sum(dUref*(U - Uref)))
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
        nU = np.max(np.abs(dy[:4*K])); cap = max(0.005, 0.5*rg)
        if nU > cap: dy *= cap/nU
        U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
    return U, rho, res < 1e-9
def lam_ring(U, rho, eps, iters=900):
    Sh = shift_mat(rho); Shm = shift_mat(-rho)
    Ms = np.zeros((K, 4, 4))
    for j in range(K):
        _, Ms[j] = strobe(U[j], eps)
    dU = dth_(U); dUs = Sh @ dU
    V = np.tile(np.array([0.7, 0.31, -0.22, 0.53]), (K, 1))
    for j in range(K):
        d = dU[j]; V[j] -= d*(d @ V[j])/(d @ d)
    V /= np.linalg.norm(V, axis=1, keepdims=True)
    for it in range(iters):
        Wp = np.empty((K, 4))
        for j in range(K):
            w = Ms[j] @ V[j]; d2 = dUs[j]
            Wp[j] = w - d2*(d2 @ w)/(d2 @ d2)
        Vn = Shm @ Wp
        for j in range(K):
            d = dU[j]; Vn[j] -= d*(d @ Vn[j])/(d @ d)
        Vn /= np.linalg.norm(Vn, axis=1, keepdims=True)
        for j in range(K):
            if Vn[j] @ V[j] < 0: Vn[j] = -Vn[j]
        V = Vn
    g = np.empty(K)
    for j in range(K):
        w = Ms[j] @ V[j]; d2 = dUs[j]
        w = w - d2*(d2 @ w)/(d2 @ d2)
        g[j] = math.log(np.linalg.norm(w))
    return float(np.mean(g))/Td
s0 = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
               rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
U = s0.y.T.copy(); rho = 2*math.pi*((Td/Tc) % 1.0)
U, rho, ok = tn(U, rho, 0.0)
cur = 0.0
while cur < etest - 1e-15:
    stp = min(0.05*etest, etest-cur)
    for _t in range(4):
        Un, rn, okn = tn(U.copy(), rho, cur+stp)
        if okn: break
        stp *= 0.5
    if not okn:
        out(f"continuation failed at {cur/etest:.4f}"); break
    U, rho, cur = Un, rn, cur+stp
lring = lam_ring(U, rho, cur)
out(f"at eps = eps*(1+3e-4): lambda_u(ring,K={K}) = {lring:.7f} /s "
    f"-> 1/(lambda_u T_d) = {1.0/(lring*Td):.3f} periods  "
    f"[{time.time()-T0:.0f}s]")
dens = upsample(U, 8192)
def f(t, x):
    return rhs(x, dict(pr, V=pr['V'] + cur*math.cos(wd*t)))
def e_th(t, x): return abs(x[0] - st[0]) - dsad
def e_vlo(t, x): return x[2] - 0.20*Vdc0
def e_vhi(t, x): return x[2] - 2.50*Vdc0
for e in (e_th, e_vlo, e_vhi):
    e.terminal = True
e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
s = solve_ivp(f, (0, 4000*Td), st.copy(), method='DOP853', rtol=1e-13,
              atol=1e-16, events=(e_th, e_vlo, e_vhi), dense_output=True)
tend = s.t[-1]; ns = int(tend/Td)
D = np.array([np.min(np.linalg.norm(dens - s.sol(n*Td), axis=1))
              for n in range(ns+1)])
nmin = int(np.argmin(D))
out(f"trajectory escapes at {tend/Td:.1f} periods; closest approach to "
    f"the guard curve {D[nmin]/rg:.3e} r_g at strobe {nmin}")
for lo_f, hi_f in ((1e-3, 1e-2), (2e-3, 3e-2), (1e-2, 1e-1)):
    seg = [n for n in range(nmin, ns+1)
           if lo_f*rg <= D[n] <= hi_f*rg]
    if len(seg) < 10:
        out(f"  window [{lo_f:.0e},{hi_f:.0e}] r_g: too few points")
        continue
    n0, n1 = seg[0], seg[-1]
    A = np.vstack([np.arange(n0, n1+1), np.ones(n1-n0+1)]).T
    cf, _, _, _ = np.linalg.lstsq(A, np.log(D[n0:n1+1]), rcond=None)
    ltraj = cf[0]/Td
    dev = float(np.max(np.abs(np.exp(A @ cf) - D[n0:n1+1])/D[n0:n1+1]))
    out(f"  window [{lo_f:.0e},{hi_f:.0e}] r_g: strobes {n0}..{n1} "
        f"({n1-n0+1} pts), max deviation from a pure exponential "
        f"{dev*100:.2f}%, lambda_u(traj) = {ltraj:.7f} /s "
        f"({(ltraj-lring)/lring*100:+.2f}% vs ring)")
out(f"DONE wall={time.time()-T0:.0f}s")
