"""idx17 anomaly, locking-tongue / outer-attractor discrimination.
Part A (decisive, cheap): sudden-on fate probes at eps/flip in
  {1.02..1.30}: compound detector + 400-period horizon; if bounded,
  record early/late amplitude stats, strobe-cluster period test
  (min_q max_n |x_{n+q}-x_n|) and attractor rotation number.
  Distinguishes: capture proper (stays ~zg) / outer bounded state
  (large but bounded) / collapse.
Part B: torus continuation (idx17fib machinery) logging rho(eps) +
  Newton residual + min|st-u| -> rational plateau = tongue.
Budget ~12 min total, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/idx17rho.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])

# --- build idx17 operating point (same as idx17fib) ---
over = dict(kp=55., ki=1200., Xg=0.40)
marg = 0.08; rr = 0.92
eflip = 7.0991e-3; emeas = 8.6656e-3
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
out(f"idx17: P={P:.5f} alpha={alpha:.4f} w0={w0:.3f} zg={zg:.4e} "
    f"Td={Td:.5f}")

# ================= Part A: fate probes =================
NP = 400
def probe(eps):
    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - 1.2
    def e_vlo(t, x): return x[2] - 0.2
    def e_vhi(t, x): return x[2] - 2.5
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    tev = np.arange(NP)*Td
    s = solve_ivp(f, (0, (NP-1)*Td), st.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-12, events=(e_th, e_vlo, e_vhi),
                  t_eval=tev)
    ev = [len(s.t_events[i]) > 0 for i in range(3)]
    if any(ev) or s.status < 0:
        which = ('TH' if ev[0] else 'VLO' if ev[1]
                 else 'VHI' if ev[2] else 'SOLVER')
        tend = (min(t[0] for t in s.t_events if len(t))
                if any(ev) else s.t[-1] if len(s.t) else 0.0)
        return dict(fate=which, t=tend)
    X = s.y.T                       # strobe samples
    n3 = len(X)//3
    def amp(block):
        return (np.max(np.abs(block[:, 0] - st[0])),
                np.max(np.abs(block[:, 2] - 1.0)))
    a_th, a_v = amp(X[:n3])
    b_th, b_v = amp(X[-n3:])
    tail = X[-150:]
    zeta = np.array([np.vdot(pv, x - st) for x in tail])
    rots = np.angle(zeta[1:]/zeta[:-1])
    rot = float(np.mean(rots)) % (2*math.pi)
    best_q, best_d = None, None
    for qq in range(1, 41):
        if len(tail) <= qq: break
        d = np.max(np.linalg.norm(tail[qq:] - tail[:-qq], axis=1))
        if best_d is None or d < best_d:
            best_q, best_d = qq, d
    return dict(fate='BOUNDED', early=(a_th, a_v), late=(b_th, b_v),
                zmin=float(np.min(np.abs(zeta))),
                zmax=float(np.max(np.abs(zeta))),
                rot=rot, q=best_q, dq=best_d)

for fac in (0.90, 0.96, 1.02, 1.06, 1.10, 1.14, 1.18, 1.22, 1.26,
            1.30):
    r = probe(fac*eflip)
    if r['fate'] != 'BOUNDED':
        out(f"A eps={fac:.2f}x: {r['fate']} at t={r['t']:.2f}s "
            f"({r['t']/Td:.0f} periods) [{time.time()-T0:.0f}s]")
    else:
        out(f"A eps={fac:.2f}x: BOUNDED early(th,V)="
            f"({r['early'][0]:.3f},{r['early'][1]:.3f}) "
            f"late=({r['late'][0]:.3f},{r['late'][1]:.3f}) "
            f"|zeta|=[{r['zmin']:.2e},{r['zmax']:.2e}] "
            f"rot={r['rot']:.4f} bestq={r['q']} dq={r['dq']:.2e} "
            f"[{time.time()-T0:.0f}s]")

# ================= Part B: rho(eps) continuation =================
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
    out("B: cycle failed"); raise SystemExit
scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
                rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
Uc = scc.y.T.copy()
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
            return U, rho, True, res
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
    return U, rho, res < 1e-9, res
U = Uc.copy()
rho = 2*math.pi*((Td/Tc) % 1.0)
U, rho, ok, res = torus_newton(U, rho, 0.0)
out(f"B eps=0: rho={rho:.6f} rho/2pi={rho/(2*math.pi):.6f} res={res:.1e}")
eps = 0.0
deps = 0.02*eflip
while eps < 1.32*eflip:
    e_try = eps + deps
    Un, rn, okn, resn = torus_newton(U.copy(), rho, e_try)
    if not okn:
        deps *= 0.5
        if deps < 1e-4*eflip:
            out(f"B stall at {eps/eflip:.3f}x res={resn:.1e}"); break
        continue
    U, rho, eps = Un, rn, e_try
    dmin = float(np.min(np.linalg.norm(U - st, axis=1)))
    out(f"B eps={eps/eflip:.3f}x: rho={rho:.6f} "
        f"rho/2pi={rho/(2*math.pi):.6f} res={resn:.1e} "
        f"min|st-u|={dmin:.3e} [{time.time()-T0:.0f}s]")
    deps = min(deps*1.3, 0.03*eflip)
out(f"DONE wall={time.time()-T0:.0f}s")
