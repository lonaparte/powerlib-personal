"""omega_g slow band closed with the EXISTING B3 machinery.

The audit left this cell open.  Two candidate criteria were refuted:
the frozen-Jacobian criterion (instantaneous instability does not imply
escape -- measured: unstable Jacobian already at 0.2 r_g displacement
while the system still returns from 1.35 r_g), and the accumulated-growth
criterion (its "unstable window" was the switch-on transient, and its
linear base trajectory was evaluated outside its own validity).

The correct move is not a new criterion: the cell belongs to the B3
family, so the B3 criterion -- continuation of the guard invariant curve
of the stroboscopic map and the change of its winding number about the
operating point -- must be evaluated here.  It never was, for a technical
reason: the frequencies used (w0/160, w0/32, w0/8) make T_d/T_c an
integer, so rho = 0 sits exactly on the strongest locking point and the
invariant curve is not the right object.

Fix: choose the drive period from the guard cycle itself,
    T_d = (8 + phi) T_c,   phi = (sqrt(5)-1)/2,
so that at a = 0 the rotation number is rho/2pi = phi exactly -- the
most badly approximable rotation number, maximally far from every
locking tongue.  The resulting w_s lands in the same slow band as the
previously measured w0/8 cell.  No fitted constant: T_c is a model
quantity and phi is the choice of an irrational.

Protocol identical to the earlier omega_g measurements: dw(t) =
a sin(w_s t) switched on at the operating point, intrinsic detectors
(theta at the saddle angular distance, Vdc at fractions of Vdc*).
Observation-window convergence is checked (12 vs 30 drive periods).
Budget ~45 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/wg_b3.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def rhs_w(x, prm):
    y = rhs(x, prm).copy(); y[0] -= prm.get('dw', 0.0); return y
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
def upsample(U, N):
    C = np.fft.fft(U, axis=0)
    Cp = np.zeros((N, U.shape[1]), complex)
    hf = K//2
    Cp[:hf] = C[:hf]; Cp[N-hf+1:] = C[hf+1:]
    Cp[hf] = 0.5*C[hf]; Cp[N-hf] = 0.5*C[hf]
    return np.real(np.fft.ifft(Cp, axis=0))*(N/K)

# ---------------- operating point (same as the earlier omega_g runs) ----
prb = gset('G1'); Psn = 3*prb['V']**2/(4*prb['Xg'])
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
P0 = margin_point(prb, 0.5*(lo+hi), 0.10)
pr = dict(prb, P=P0, dw=0.0)
co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']; c1v = co['c1']
qv = co['q']; pv = co['p']
rg = math.sqrt(alpha/c1v.real)
dsad = math.pi - 2*abs(st[0])
Vdc0 = st[2]
out(f"G1: P0={P0:.5f} w0={w0:.4f} alpha={alpha:.4f} r_g={rg:.5e} "
    f"d_sad={dsad:.5f}")

# ---------------- guard cycle at a = 0, and the drive period ----------
def flow(x0, T, var=False):
    def f(t, y):
        x = y[:4]
        if not var:
            return rhs_w(x, pr)
        return np.concatenate([rhs_w(x, pr),
                               (jac_a(x, pr) @ y[4:].reshape(4, 4)).ravel()])
    y0 = x0 if not var else np.concatenate([x0, np.eye(4).ravel()])
    s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12, atol=1e-14)
    return (s.y[:4, -1] if not var
            else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
def cyc(xs, Ts):
    x, T = xs.copy(), Ts; fref = rhs_w(xs, pr); R = np.ones(5)
    for it in range(40):
        xT, M = flow(x, T, var=True)
        R = np.append(xT - x, np.dot(fref, x - xs))
        if np.max(np.abs(R)) < 1e-12:
            return x, T, True
        A5 = np.zeros((5, 5)); A5[:4, :4] = M - np.eye(4)
        A5[:4, 4] = rhs_w(xT, pr); A5[4, :4] = fref
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
out(f"guard cycle: T_c={Tc:.6f}s  |mu_u|={abs(mu_u):.5f}  "
    f"exponent={math.log(abs(mu_u))/Tc:.5f} /s (2 alpha={2*alpha:.5f})")
phi = 0.5*(math.sqrt(5.0) - 1.0)
Td = (8.0 + phi)*Tc
ws = 2*math.pi/Td
out(f"drive: T_d=(8+phi) T_c={Td:.6f}s  w_s={ws:.5f} rad/s "
    f"(= w0/{w0/ws:.4f}); rho/2pi at a=0 is phi={phi:.6f}")

# ---------------- measured threshold (sudden-on, intrinsic detectors) --
def fate(a, NP):
    def f(t, x):
        return rhs_w(x, dict(pr, dw=a*math.sin(ws*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NP*Td), st.copy(), method='DOP853',
                  rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0
def thresh(NP):
    alo, ahi = 0.05, 0.5
    n = 0
    while not fate(ahi, NP) and ahi < 20.0 and n < 20:
        alo = ahi; ahi *= 1.5; n += 1
    n = 0
    while fate(alo, NP) and alo > 1e-3 and n < 20:
        ahi = alo; alo *= 0.6; n += 1
    if fate(alo, NP) or not fate(ahi, NP):
        return None
    for _ in range(15):
        am = 0.5*(alo+ahi)
        if fate(am, NP): ahi = am
        else: alo = am
    return 0.5*(alo+ahi)
a12 = thresh(12)
out(f"measured a_c (12 drive periods) = {a12:.5f} rad/s "
    f"({a12/(2*math.pi)*1e3:.2f} mHz, phase amplitude "
    f"{math.degrees(a12/ws):.2f} deg)  [{time.time()-T0:.0f}s]")
a30 = thresh(30)
out(f"measured a_c (30 drive periods) = {a30:.5f} rad/s "
    f"(window convergence {(a30-a12)/a12*100:+.2f}%)  [{time.time()-T0:.0f}s]")
ameas = a30

# ---------------- B3: guard invariant curve, winding flip -------------
def strobe(x0, a):
    def f(t, y):
        x = y[:4]; qq = dict(pr, dw=a*math.sin(ws*t))
        return np.concatenate([rhs_w(x, qq),
                               (jac_a(x, qq) @ y[4:].reshape(4, 4)).ravel()])
    s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                  method='DOP853', rtol=1e-10, atol=1e-12)
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
def tn(U, rho, a, itmax=20, tol=1e-8):
    Uref = U.copy(); dUref = dth_(Uref); res = None
    for it in range(itmax):
        Sh = shift_mat(rho); PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
        for j in range(K):
            PhiU[j], Ms[j] = strobe(U[j], a)
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
    return U, rho, (res is not None and res < 1e-6)
def wind(Ua):
    dens = upsample(Ua, 2048)
    Z = (dens - st) @ np.conj(pv)
    dph = np.angle(Z*np.conj(np.roll(Z, 1)))
    return int(round(float(np.sum(dph))/(2*math.pi)))
scc = solve_ivp(lambda t, x: rhs_w(x, pr), (0, Tc), x0c, method='DOP853',
                rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
U = scc.y.T.copy()
rho = 2*math.pi*((Td/Tc) % 1.0)
t1 = time.time(); U, rho, ok = tn(U, rho, 0.0)
out(f"B3: invariant curve at a=0 Newton {'ok' if ok else 'FAILED'}, "
    f"rho/2pi={rho/(2*math.pi):.6f}, one Newton solve took "
    f"{time.time()-t1:.1f}s  [{time.time()-T0:.0f}s]")
if not ok:
    out("cannot continue"); raise SystemExit
wref = wind(U)
out(f"    winding at a=0: {wref}")
aa = 0.0; da = 0.06*ameas; flip = None
while aa < 1.4*ameas:
    an = aa + da
    Un, rn, okn = tn(U.copy(), rho, an)
    if not okn:
        da *= 0.5
        if da < 3e-3*ameas:
            out(f"    Newton stalls at a={an:.5f} "
                f"(a/a_meas={an/ameas:.3f}); treating as curve loss")
            flip = (aa, an); break
        continue
    wn = wind(Un)
    out(f"    a={an:.5f} (a/a_meas={an/ameas:.3f}) rho/2pi={rn/(2*math.pi):.6f} "
        f"wind={wn}  [{time.time()-T0:.0f}s]")
    if wn != wref:
        flip = (aa, an); break
    U, rho, aa = Un, rn, an
    da = min(da*1.25, 0.08*ameas)
if flip is None:
    out(f"no winding flip up to 1.4 a_meas; criterion does not fire")
else:
    ea, eb = flip; Ua, ra = U.copy(), rho
    for _ in range(10):
        em = 0.5*(ea+eb)
        Um, rm, okm = tn(Ua.copy(), ra, em)
        if not okm:
            eb = em; continue
        if wind(Um) == wref: ea, Ua, ra = em, Um, rm
        else: eb = em
    af = 0.5*(ea+eb)
    out(f"B3 winding-flip threshold a_flip = {af:.5f} rad/s vs measured "
        f"a_c = {ameas:.5f}  err = {(af-ameas)/ameas*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
