"""lambda_u done correctly: the transverse cocycle over the forced
invariant curve.

The escape-time law above threshold was measured to be logarithmic,
    t_esc = S ln(1/d) + const,   d = eps/eps_c - 1,
with S = 81.114 drive periods, while the unforced surrogate 1/(2 alpha)
gives 65.80 -- an 18.9% gap.  The claim to be tested is that S = 1/lam_u
with lam_u the transverse (normal) Lyapunov exponent of the SADDLE
invariant curve of the stroboscopic map at eps = eps_c.

Two earlier implementations were wrong: (a) multiplying the collocation
Jacobians in index order is meaningless because for irrational rho the
collocation points do not cycle by index; (b) projecting out the tangent
only at the source point does not define the quotient cocycle.

Correct object: the base dynamics on the invariant curve is the RIGID
rotation theta -> theta + rho, the curve is U(theta), the strobe map
linearisation M(theta) = DPhi(U(theta)) carries the tangent U'(theta)
to U'(theta+rho), so the quotient cocycle on the normal bundle is
    A(theta) = P_perp(theta+rho) . M(theta) . P_perp(theta),
    P_perp(theta) = I - U'U'^T/|U'|^2 ,
and lam_u = lim (1/(N T_d)) sum log |A ... A v| (Oseledets, power
iteration with renormalisation).  Base points are taken from the
Fourier interpolation of U so the iteration rides the curve exactly;
M(theta) is obtained by integrating the variational equations from the
interpolated point, never by interpolating M.

Validation ladder:
  (0) eps=0: lam_u must equal the unstable Floquet exponent of the guard
      cycle, ln(mu_u)/T_c, computed independently from the monodromy;
      and both must be near the normal-form value 2 alpha.
  (1) lam_u(eps) tracked along the continuation to eps_c.
  (2) 1/(lam_u(eps_c) T_d) compared with the measured slope S.
Everything is re-measured in this script; no number is carried in.
Set: idx17 (G1 with kp=55, ki=1200, Xg=0.40), margin 0.08, r = 0.92.
Budget ~35 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/lamu2.log', 'w')
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
def fcoef(U):
    return np.fft.fft(U, axis=0)/K
def ev_at(C, th):
    return np.real(np.exp(1j*mfreq*th) @ C)
def dev_at(C, th):
    return np.real(((1j*mfreq)*np.exp(1j*mfreq*th)) @ C)

# ---------------- operating point ----------------
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
qv = co['q']; pv = co['p']; lam = co['lam']
rg = math.sqrt(alpha/c1v.real)
dsad = math.pi - 2*abs(st[0])
wd = 0.92*w0; Td = 2*math.pi/wd
Vdc0 = st[2]
out(f"idx17: P0={P0:.5f} w0={w0:.4f} alpha={alpha:.5f} r_g={rg:.5e} "
    f"d_sad={dsad:.5f} T_d={Td:.6f}s  2alpha={2*alpha:.5f}")

# ---------------- (1) threshold + escape-time law ----------------
def probe(eps, NPn=400):
    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                  rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
    ev = [len(s.t_events[i]) > 0 for i in range(3)]
    if any(ev) or s.status < 0:
        te = min([t[0] for t in s.t_events if len(t)], default=s.t[-1])
        return True, te
    return False, None
elo, ehi = 5e-3, 1.2e-2
while not probe(ehi)[0] and ehi < 5e-2:
    elo = ehi; ehi *= 1.4
while probe(elo)[0] and elo > 1e-4:
    ehi = elo; elo *= 0.7
for _ in range(13):
    em = 0.5*(elo+ehi)
    if probe(em)[0]: ehi = em
    else: elo = em
epsc = 0.5*(elo+ehi)
out(f"(1) eps_c (intrinsic detectors) = {epsc:.6e}  [{time.time()-T0:.0f}s]")
facs = (1.02, 1.05, 1.10, 1.20, 1.35, 1.55, 1.80)
dd, tt = [], []
for fa in facs:
    esc, te = probe(fa*epsc, NPn=3000)
    if te is None: continue
    dd.append(fa-1.0); tt.append(te/Td)
dd = np.array(dd); tt = np.array(tt)
M1 = np.vstack([np.log(1.0/dd), np.ones_like(dd)]).T
cf, _, _, _ = np.linalg.lstsq(M1, tt, rcond=None)
S = float(cf[0])
out(f"    escape-time ln-law slope S = {S:.3f} drive periods "
    f"(intercept {cf[1]:+.3f}); unforced surrogate 1/(2 alpha T_d) = "
    f"{1.0/(2*alpha)/Td:.3f}  [{time.time()-T0:.0f}s]")

# ---------------- (2) guard cycle at eps = 0 ----------------
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
mu_u = max(mu, key=lambda z: abs(z))
lfl = math.log(abs(mu_u))/Tc
out(f"(2) guard cycle: T_c={Tc:.6f}s  multipliers |mu| = "
    f"{', '.join(f'{abs(z):.4e}' for z in sorted(mu, key=lambda z: -abs(z)))}")
out(f"    Floquet exponent of the guard cycle = {lfl:.6f} /s "
    f"(normal-form 2 alpha = {2*alpha:.6f}, dev {(lfl-2*alpha)/(2*alpha)*100:+.2f}%)")

# ---------------- (3) invariant curve + transverse cocycle ----------------
def strobe(x0, eps):
    def f(t, y):
        x = y[:4]; qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        return np.concatenate([rhs(x, qq),
                               (jac_a(x, qq) @ y[4:].reshape(4, 4)).ravel()])
    s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                  method='DOP853', rtol=1e-11, atol=1e-13)
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
def lam_u(U, rho, eps, N=1200, burn=120):
    C = fcoef(U)
    th = 0.0
    v = np.array([0.7, 0.31, -0.22, 0.53])
    s = 0.0; cnt = 0; resmax = 0.0
    for n in range(N):
        x = ev_at(C, th); d = dev_at(C, th)
        v = v - d*(d @ v)/(d @ d)
        v = v/np.linalg.norm(v)
        xT, M = strobe(x, eps)
        th2 = th + rho
        x2 = ev_at(C, th2); d2 = dev_at(C, th2)
        resmax = max(resmax, float(np.max(np.abs(xT - x2))))
        w = M @ v
        w = w - d2*(d2 @ w)/(d2 @ d2)
        nn = float(np.linalg.norm(w))
        if n >= burn:
            s += math.log(nn); cnt += 1
        v = w/nn; th = th2 % (2*math.pi)
    return s/(cnt*Td), resmax

scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
                rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
U = scc.y.T.copy()
rho = 2*math.pi*((Td/Tc) % 1.0)
U, rho, ok = tn(U, rho, 0.0)
out(f"(3) invariant curve at eps=0: Newton {'ok' if ok else 'FAILED'}, "
    f"rho/2pi = {rho/(2*math.pi):.6f}  [{time.time()-T0:.0f}s]")
lu0, rmax = lam_u(U, rho, 0.0)
out(f"    lam_u(0) = {lu0:.6f} /s  (curve residual {rmax:.2e}); "
    f"vs Floquet {lfl:.6f} ({(lu0-lfl)/lfl*100:+.3f}%), "
    f"vs 2 alpha ({(lu0-2*alpha)/(2*alpha)*100:+.2f}%)  [{time.time()-T0:.0f}s]")
out("    eps/eps_c |  rho/2pi   lam_u [1/s]   1/(lam_u T_d) [periods]  "
    "resid")
fracs = [0.20, 0.40, 0.60, 0.75, 0.85, 0.92, 0.96, 0.99]
cur = 0.0
Sp = None
for fr in fracs:
    tgt = fr*epsc
    okc = True
    while cur < tgt - 1e-15:
        stp = min(0.05*epsc, tgt - cur)
        Un, rn, okn = tn(U.copy(), rho, cur + stp)
        if not okn:
            stp *= 0.5
            Un, rn, okn = tn(U.copy(), rho, cur + stp)
            if not okn:
                okc = False; break
        U, rho, cur = Un, rn, cur + stp
    if not okc:
        out(f"    {fr:.2f} | continuation failed at eps/eps_c={cur/epsc:.3f}")
        break
    lu, rmax = lam_u(U, rho, cur)
    Sp = 1.0/(lu*Td)
    out(f"    {fr:8.2f} | {rho/(2*math.pi):.6f}  {lu:.6f}     "
        f"{Sp:10.3f}          {rmax:.1e}  [{time.time()-T0:.0f}s]")
if Sp is not None:
    out(f"(4) predicted ln-law slope 1/(lam_u T_d) = {Sp:.3f} periods vs "
        f"measured S = {S:.3f}  err = {(Sp-S)/S*100:+.2f}%")
    out(f"    unforced surrogate 1/(2 alpha T_d) = {1.0/(2*alpha)/Td:.3f} "
        f"periods, err = {(1.0/(2*alpha)/Td-S)/S*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
