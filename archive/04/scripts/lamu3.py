"""lambda_u and the escape-time law, both done to spectral accuracy.

Two defects of the previous attempt are fixed here.

(a) lambda_u by power iteration along the orbit converges only like
    (fluctuation)/N; 1200 strobe steps left a 3.8% error, visible as a
    3.8% mismatch against the guard cycle's exact Floquet exponent at
    eps = 0.  Replaced by the invariant transverse DIRECTION FIELD:
    solve  P_perp(th+rho) M(th) v(th) = g(th) v(th+rho)  by iteration on
    the collocation ring (the strobe Jacobians M(th_j) are computed once,
    the iteration is pure linear algebra plus Fourier shifts), then
        lambda_u = (1/T_d) * ring average of log g
    which is a periodic trapezoid rule = spectrally accurate.
    Validation: at eps = 0 it must reproduce ln|mu_u|/T_c exactly.

(b) The escape-time exponent was fitted against d = eps/eps_c - 1 with
    eps_c taken from a 400-period bisection.  But the threshold measured
    with a finite window IS the point where t_esc equals that window, so
    it sits above the true threshold and distorts every small-d point.
    Fixed by fitting the three-parameter law
        t_esc(eps) = S ln(1/(eps/eps* - 1)) + C
    with eps* a fit parameter, over eps values spanning four decades of
    d, each run with a window long enough to contain its own escape.
    S and eps* then come out together, and eps* is compared with the
    finite-window thresholds to size the systematic.

Comparison: 1/(lambda_u T_d) at eps -> eps* against S.
Set: idx17 (G1 with kp=55, ki=1200, Xg=0.40), margin 0.08, r = 0.92.
Budget ~35 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
from scipy.optimize import least_squares
LOG = open('sweep20/lamu3.log', 'w')
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
def dth_(U):
    return np.real(np.fft.ifft(np.fft.fft(U, axis=0)
                               * (1j*mfreq)[:, None], axis=0))

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
out(f"idx17: w0={w0:.4f} alpha={alpha:.5f} r_g={rg:.5e} T_d={Td:.6f}s "
    f"2alpha={2*alpha:.5f}")

# ---------- escape time with a window that adapts to the answer ----------
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
    if ts:
        return min(ts)/Td
    if s.status < 0:
        return s.t[-1]/Td
    return None
def thresh(NP):
    elo, ehi = 5e-3, 1.2e-2
    while esc_time(ehi, NP) is None and ehi < 5e-2:
        elo = ehi; ehi *= 1.4
    while esc_time(elo, NP) is not None and elo > 1e-4:
        ehi = elo; elo *= 0.7
    for _ in range(22):
        em = 0.5*(elo+ehi)
        if esc_time(em, NP) is not None: ehi = em
        else: elo = em
    return 0.5*(elo+ehi)
ec400 = thresh(400)
out(f"(1) finite-window thresholds: eps_c(400 periods) = {ec400:.8e} "
    f"[{time.time()-T0:.0f}s]")
ec4000 = thresh(4000)
out(f"    eps_c(4000 periods) = {ec4000:.8e} "
    f"({(ec4000-ec400)/ec400*100:+.3f}% vs 400)  [{time.time()-T0:.0f}s]")

ds = np.array([1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2, 1e-1, 2e-1, 4e-1, 8e-1])
EE, TT = [], []
for d in ds:
    e = ec4000*(1.0 + d)
    te = esc_time(e, 20000)
    if te is None:
        out(f"    d={d:.1e}: no escape within 20000 periods"); continue
    EE.append(e); TT.append(te)
    out(f"    d={d:.1e}  eps={e:.8e}  t_esc={te:.2f} periods "
        f"[{time.time()-T0:.0f}s]")
EE = np.array(EE); TT = np.array(TT)
def resid(p):
    S, C, es = p
    dd = EE/es - 1.0
    dd = np.maximum(dd, 1e-14)
    return S*np.log(1.0/dd) + C - TT
p0 = [81.0, -5.0, ec4000*(1 - 1e-4)]
sol = least_squares(resid, p0, x_scale=[10.0, 10.0, ec4000*1e-4])
S, C, estar = sol.x
rms = float(np.sqrt(np.mean(sol.fun**2)))
out(f"(2) 3-parameter ln-law fit: S={S:.3f} periods, C={C:+.3f}, "
    f"eps*={estar:.8e} ({(estar-ec4000)/ec4000*100:+.4f}% vs the "
    f"4000-period threshold), rms residual {rms:.3f} periods")
M2 = np.vstack([(EE/estar - 1.0)**-0.5, np.ones_like(EE)]).T
c2, _, _, _ = np.linalg.lstsq(M2, TT, rcond=None)
out(f"    saddle-node form t = A d^-1/2 + B at the same eps*: "
    f"rms {float(np.sqrt(np.mean((M2 @ c2 - TT)**2))):.3f} periods")

# ---------- guard cycle and the transverse direction field ----------
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
got = False
for fac in (1.0, 0.85, 0.7, 1.2):
    xs = st + 2*np.real(fac*rg*qv)
    Ts = 2*math.pi/(w0 + c1v.imag*(fac*rg)**2)
    x0c, Tc, ok = cyc(xs, Ts)
    if ok and abs(np.vdot(pv, x0c - st)) > 0.2*rg:
        got = True; break
if not got:
    out("guard cycle Newton failed"); raise SystemExit
_, Mon = flow(x0c, Tc, var=True)
mu = np.linalg.eigvals(Mon)
lfl = math.log(abs(max(mu, key=lambda z: abs(z))))/Tc
out(f"(3) guard cycle T_c={Tc:.6f}s, exact Floquet exponent "
    f"{lfl:.8f} /s (2 alpha = {2*alpha:.6f})")

def strobe(x0, eps):
    def f(t, y):
        x = y[:4]; qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        return np.concatenate([rhs(x, qq),
                               (jac_a(x, qq) @ y[4:].reshape(4, 4)).ravel()])
    s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                  method='DOP853', rtol=1e-12, atol=1e-14)
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
def tn(U, rho, eps, itmax=25, tol=1e-10):
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
def lam_ring(U, rho, eps, iters=600):
    Sh = shift_mat(rho); Shm = shift_mat(-rho)
    Ms = np.zeros((K, 4, 4))
    for j in range(K):
        _, Ms[j] = strobe(U[j], eps)
    dU = dth_(U); dUs = Sh @ dU
    V = np.tile(np.array([0.7, 0.31, -0.22, 0.53]), (K, 1))
    for j in range(K):
        d = dU[j]; V[j] -= d*(d @ V[j])/(d @ d)
    V /= np.linalg.norm(V, axis=1, keepdims=True)
    prev = None; conv = None
    for it in range(iters):
        Wp = np.empty((K, 4))
        for j in range(K):
            w = Ms[j] @ V[j]; d2 = dUs[j]
            Wp[j] = w - d2*(d2 @ w)/(d2 @ d2)
        Vn = Shm @ Wp
        for j in range(K):
            d = dU[j]; Vn[j] -= d*(d @ Vn[j])/(d @ d)
        Vn /= np.linalg.norm(Vn, axis=1, keepdims=True)
        conv = float(np.max(np.abs(np.abs(np.sum(Vn*V, axis=1)) - 1.0)))
        V = Vn
        if conv < 1e-14 and it > 20:
            break
        prev = conv
    Vs = Sh @ V
    g = np.empty(K)
    for j in range(K):
        w = Ms[j] @ V[j]; d2 = dUs[j]
        w = w - d2*(d2 @ w)/(d2 @ d2)
        g[j] = math.log(np.linalg.norm(w)/np.linalg.norm(Vs[j]))
    return float(np.mean(g))/Td, conv
scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
                rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
U = scc.y.T.copy()
rho = 2*math.pi*((Td/Tc) % 1.0)
U, rho, ok = tn(U, rho, 0.0)
lu0, cv = lam_ring(U, rho, 0.0)
out(f"    ring-average lam_u(0) = {lu0:.8f} /s, direction-field "
    f"convergence {cv:.1e}; vs Floquet {(lu0-lfl)/lfl*100:+.4f}%  "
    f"[{time.time()-T0:.0f}s]")
out("    eps/eps* |  rho/2pi   lam_u [1/s]   1/(lam_u T_d) [periods]")
cur = 0.0
for fr in (0.30, 0.60, 0.80, 0.90, 0.95, 0.98, 0.995, 0.999):
    tgt = fr*estar; okc = True
    while cur < tgt - 1e-15:
        stp = min(0.04*estar, tgt - cur)
        Un, rn, okn = tn(U.copy(), rho, cur + stp)
        if not okn:
            stp *= 0.5
            Un, rn, okn = tn(U.copy(), rho, cur + stp)
            if not okn:
                okc = False; break
        U, rho, cur = Un, rn, cur + stp
    if not okc:
        out(f"    {fr:.3f} | continuation failed at {cur/estar:.4f}")
        break
    lu, cv = lam_ring(U, rho, cur)
    out(f"    {fr:8.3f} | {rho/(2*math.pi):.6f}  {lu:.6f}   "
        f"{1.0/(lu*Td):10.3f}   (conv {cv:.0e})  [{time.time()-T0:.0f}s]")
out(f"(4) measured ln-law slope S = {S:.3f} periods; unforced surrogate "
    f"1/(2 alpha T_d) = {1.0/(2*alpha)/Td:.3f}")
out(f"DONE wall={time.time()-T0:.0f}s")
