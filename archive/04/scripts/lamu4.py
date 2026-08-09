"""lambda_u, validated, and the asymptotic escape-time slope.

Two things are settled here.

(A) Which estimator of the transverse exponent is trustworthy.  At
    eps = 0 the answer is known exactly -- it is the guard cycle's
    unstable Floquet exponent ln|mu_u|/T_c -- so both candidates are
    scored against it:
      * ring average over the invariant transverse direction field
        (spectral in principle; gave +92% in the previous run, so it is
        on trial here at K = 32 and K = 64);
      * power iteration along the orbit with renormalisation, whose
        error decays like 1/N; reported as a convergence ladder plus a
        tail-averaged estimate that cancels the leading 1/N oscillation.
    Only the estimator that reproduces the Floquet exponent is used.

(B) The asymptotic slope of the escape-time law.  A single ln-law fitted
    over d = 0.02 ... 0.8 returns a chord, not the asymptote: the local
    slope of that data still rises as d falls.  Measured here from the
    smallest-d chords, at a threshold determined with a window long
    enough that its own bias is negligible.

The claim under test: asymptotic slope = 1/(lambda_u T_d) with lambda_u
evaluated on the guard invariant curve AT the threshold.
Set: idx17 (G1 with kp=55, ki=1200, Xg=0.40), margin 0.08, r = 0.92.
Budget ~30 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/lamu4.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])
def mk(K):
    mf = np.fft.fftfreq(K)*K
    def sh(r):
        ph = np.exp(1j*mf*r)
        return np.real(np.fft.ifft(np.fft.fft(np.eye(K), axis=0)*ph[:, None],
                                   axis=0))
    def dsh(r):
        ph = 1j*mf*np.exp(1j*mf*r)
        return np.real(np.fft.ifft(np.fft.fft(np.eye(K), axis=0)*ph[:, None],
                                   axis=0))
    def dth(U):
        return np.real(np.fft.ifft(np.fft.fft(U, axis=0)
                                   * (1j*mf)[:, None], axis=0))
    def coef(U):
        return np.fft.fft(U, axis=0)/K
    def evat(C, th):
        return np.real(np.exp(1j*mf*th) @ C)
    def devat(C, th):
        return np.real(((1j*mf)*np.exp(1j*mf*th)) @ C)
    return sh, dsh, dth, coef, evat, devat

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
out(f"idx17: w0={w0:.4f} alpha={alpha:.5f} r_g={rg:.5e} T_d={Td:.6f}s")

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
while esc_time(ehi, 4000) is None and ehi < 5e-2:
    elo = ehi; ehi *= 1.4
while esc_time(elo, 4000) is not None and elo > 1e-4:
    ehi = elo; elo *= 0.7
for _ in range(24):
    em = 0.5*(elo+ehi)
    if esc_time(em, 4000) is not None: ehi = em
    else: elo = em
estar = 0.5*(elo+ehi)
out(f"(B) threshold at a 4000-period window: eps* = {estar:.9e} "
    f"[{time.time()-T0:.0f}s]")
dl = [3e-5, 1e-4, 3e-4, 1e-3]
tl = []
for d in dl:
    te = esc_time(estar*(1+d), 200000)
    tl.append(te)
    out(f"    d={d:.1e}  t_esc={te:.2f} periods  [{time.time()-T0:.0f}s]")
sls = [(tl[i]-tl[i+1])/math.log(dl[i+1]/dl[i]) for i in range(len(dl)-1)]
out(f"    local ln-law slopes (smallest d first): "
    + ", ".join(f"{s:.2f}" for s in sls) + " periods per e-fold")
Sasym = sls[0]

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
lfl = math.log(abs(max(np.linalg.eigvals(Mon), key=lambda z: abs(z))))/Tc
out(f"(A) exact Floquet exponent at eps=0: {lfl:.8f} /s  (2 alpha = "
    f"{2*alpha:.6f})  [{time.time()-T0:.0f}s]")

def strobe(x0, eps, rt=1e-11):
    def f(t, y):
        x = y[:4]; qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        return np.concatenate([rhs(x, qq),
                               (jac_a(x, qq) @ y[4:].reshape(4, 4)).ravel()])
    s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                  method='DOP853', rtol=rt, atol=rt*1e-2)
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
def curve(K, eps, U0=None, rho0=None, itmax=25, tol=1e-10):
    sh, dsh, dth, _, _, _ = mk(K)
    if U0 is None:
        s = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
                      rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
        U = s.y.T.copy(); rho = 2*math.pi*((Td/Tc) % 1.0)
    else:
        U, rho = U0.copy(), rho0
    Uref = U.copy(); dUref = dth(Uref); I4 = np.eye(4); res = None
    for it in range(itmax):
        Sh = sh(rho); PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
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
        A[:4*K, -1] = -(dsh(rho) @ U).flatten()
        A[-1, :4*K] = dUref.flatten()
        dy = np.linalg.solve(A, -np.concatenate([R.flatten(), [c]]))
        nU = np.max(np.abs(dy[:4*K])); cap = max(0.005, 0.5*rg)
        if nU > cap: dy *= cap/nU
        U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
    return U, rho, res < 1e-9
def lam_ring(U, rho, eps, K, iters=800):
    sh, _, dth, _, _, _ = mk(K)
    Sh = sh(rho); Shm = sh(-rho)
    Ms = np.zeros((K, 4, 4))
    for j in range(K):
        _, Ms[j] = strobe(U[j], eps)
    dU = dth(U); dUs = Sh @ dU
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
def lam_power(U, rho, eps, K, N, burn=200):
    _, _, dth, coef, evat, devat = mk(K)
    C = coef(U)
    th = 0.0; v = np.array([0.7, 0.31, -0.22, 0.53])
    acc = []; s = 0.0
    for n in range(N):
        x = evat(C, th); d = devat(C, th)
        v = v - d*(d @ v)/(d @ d); v /= np.linalg.norm(v)
        _, M = strobe(x, eps, rt=1e-10)
        th2 = th + rho
        d2 = devat(C, th2)
        w = M @ v
        w = w - d2*(d2 @ w)/(d2 @ d2)
        nn = float(np.linalg.norm(w))
        if n >= burn:
            s += math.log(nn); acc.append(s/(len(acc)+1)/Td)
        v = w/nn; th = th2 % (2*math.pi)
    a = np.array(acc)
    return a, float(np.mean(a[len(a)//2:]))

U32, r32, ok32 = curve(32, 0.0)
U64, r64, ok64 = curve(64, 0.0)
out(f"    invariant curve at eps=0: K=32 {'ok' if ok32 else 'FAIL'}, "
    f"K=64 {'ok' if ok64 else 'FAIL'}")
lr32 = lam_ring(U32, r32, 0.0, 32)
lr64 = lam_ring(U64, r64, 0.0, 64)
out(f"    ring estimator: K=32 {lr32:.6f} ({(lr32-lfl)/lfl*100:+.2f}%), "
    f"K=64 {lr64:.6f} ({(lr64-lfl)/lfl*100:+.2f}%)  [{time.time()-T0:.0f}s]")
acc, tail = lam_power(U32, r32, 0.0, 32, 16000)
for n in (1000, 2000, 4000, 8000, len(acc)):
    if n <= len(acc):
        out(f"    power estimator N={n:6d}: {acc[n-1]:.6f} "
            f"({(acc[n-1]-lfl)/lfl*100:+.2f}%)")
out(f"    power estimator, tail-averaged: {tail:.6f} "
    f"({(tail-lfl)/lfl*100:+.2f}%)  [{time.time()-T0:.0f}s]")
best = 'power' if abs(tail-lfl) < abs(lr64-lfl) else 'ring'
out(f"    validated estimator: {best}")

U, rho = U32.copy(), r32
cur = 0.0
while cur < estar - 1e-15:
    stp = min(0.05*estar, estar - cur)
    Un, rn, okn = curve(32, cur+stp, U, rho)
    if not okn:
        stp *= 0.5
        Un, rn, okn = curve(32, cur+stp, U, rho)
        if not okn:
            out(f"    continuation failed at {cur/estar:.4f}"); break
    U, rho, cur = Un, rn, cur+stp
out(f"(C) invariant curve continued to eps/eps* = {cur/estar:.5f}, "
    f"rho/2pi = {rho/(2*math.pi):.6f}  [{time.time()-T0:.0f}s]")
if best == 'power':
    acc2, lu = lam_power(U, rho, cur, 32, 16000)
else:
    lu = lam_ring(U, rho, cur, 32)
out(f"    lambda_u(eps*) = {lu:.6f} /s -> 1/(lambda_u T_d) = "
    f"{1.0/(lu*Td):.2f} periods  [{time.time()-T0:.0f}s]")
out(f"(D) asymptotic escape slope {Sasym:.2f} periods vs 1/(lambda_u T_d) "
    f"{1.0/(lu*Td):.2f}: err = {(1.0/(lu*Td)-Sasym)/Sasym*100:+.2f}%")
out(f"    unforced surrogate 1/(2 alpha T_d) = {1.0/(2*alpha)/Td:.2f} "
    f"periods: err = {(1.0/(2*alpha)/Td-Sasym)/Sasym*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
