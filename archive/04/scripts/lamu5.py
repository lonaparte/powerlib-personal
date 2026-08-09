"""Tighten the escape-law closure to the 1% standard.

lamu4 gave: asymptotic slope 208.67 periods (smallest-d chord; the three
chords were 208.67 / 201.98 / 203.35) against 1/(lambda_u T_d) = 206.19
computed with the ring estimator at K = 32, whose own bias against the
exact Floquet exponent is -0.24%.  So both sides carry ~1% uncertainty
and the comparison is -1.19%.  Both are tightened here:
  * lambda_u at K = 64, where the estimator reproduced the exact Floquet
    exponent to -0.02%;
  * the threshold and the asymptotic slope from a joint three-parameter
    fit restricted to small d, which removes the finite-window bias
    (lamu3 showed the fitted eps* agrees with a 4000-period bisection to
    0.006%) and is far cheaper than bisecting with a long window;
  * more escape-time points in the small-d decade, so the slope is an
    average over chords rather than one chord.
Set: idx17 (G1 with kp=55, ki=1200, Xg=0.40), margin 0.08, r = 0.92.
Budget ~15 min.
"""
exec(open('selfhead.py').read())
import time
from scipy.optimize import least_squares
LOG = open('sweep20/lamu5.log', 'w')
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
while esc_time(ehi, 400) is None and ehi < 5e-2:
    elo = ehi; ehi *= 1.4
while esc_time(elo, 400) is not None and elo > 1e-4:
    ehi = elo; elo *= 0.7
for _ in range(14):
    em = 0.5*(elo+ehi)
    if esc_time(em, 400) is not None: ehi = em
    else: elo = em
e400 = 0.5*(elo+ehi)
out(f"coarse 400-period threshold {e400:.7e}  [{time.time()-T0:.0f}s]")
EE, TT = [], []
for fac in (0.9736, 0.9738, 0.9740, 0.9745, 0.9750, 0.9760, 0.9775,
            0.9800, 0.9850, 0.9950):
    e = e400*fac
    te = esc_time(e, 300000)
    if te is None:
        out(f"  fac={fac}: no escape"); continue
    EE.append(e); TT.append(te)
    out(f"  eps={e:.8e}  t_esc={te:.2f} periods  [{time.time()-T0:.0f}s]")
EE = np.array(EE); TT = np.array(TT)
def resid(p):
    S, C, es = p
    dd = np.maximum(EE/es - 1.0, 1e-15)
    return S*np.log(1.0/dd) + C - TT
sol = least_squares(resid, [205.0, -50.0, EE.min()*(1-1e-4)],
                    x_scale=[10.0, 10.0, EE.min()*1e-4])
S, C, estar = sol.x
rms = float(np.sqrt(np.mean(sol.fun**2)))
out(f"joint fit: S={S:.3f} periods, C={C:+.3f}, eps*={estar:.9e}, "
    f"rms {rms:.3f} periods over {len(TT)} points")
ch = [(TT[i]-TT[i+1])/math.log((EE[i+1]/estar-1)/(EE[i]/estar-1))
      for i in range(len(TT)-1)]
out("  chord slopes: " + ", ".join(f"{c:.2f}" for c in ch))

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
_, Mon = flow(x0c, Tc, var=True)
lfl = math.log(abs(max(np.linalg.eigvals(Mon), key=lambda z: abs(z))))/Tc
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
l0 = lam_ring(U, rho, 0.0)
out(f"K={K} ring estimator at eps=0: {l0:.8f} vs exact Floquet "
    f"{lfl:.8f} ({(l0-lfl)/lfl*100:+.3f}%)  [{time.time()-T0:.0f}s]")
cur = 0.0
while cur < estar - 1e-15:
    stp = min(0.05*estar, estar-cur)
    for _t in range(4):
        Un, rn, okn = tn(U.copy(), rho, cur+stp)
        if okn: break
        stp *= 0.5
    if not okn:
        out(f"continuation failed at {cur/estar:.4f}"); break
    U, rho, cur = Un, rn, cur+stp
lu = lam_ring(U, rho, cur)
out(f"lambda_u(eps*) = {lu:.7f} /s at eps/eps*={cur/estar:.6f} -> "
    f"1/(lambda_u T_d) = {1.0/(lu*Td):.3f} periods  [{time.time()-T0:.0f}s]")
out(f"RESULT asymptotic escape slope {S:.3f} vs 1/(lambda_u T_d) "
    f"{1.0/(lu*Td):.3f}: err = {(1.0/(lu*Td)-S)/S*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
