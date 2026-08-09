"""omega_g slow band: the sharp criterion is the landing, not the winding.

flipfix settled what the winding criterion is really doing.  On the V
channel the winding of the guard curve about the OPERATING POINT st is
the right object (the protocol starts the system at st): it flips at the
threshold, +0.1%.  Computing it about the forced fixed point x_a instead
does not flip at all -- so the earlier worry was misplaced, st is
correct.

On the omega_g slow cell the same winding is 9.1% low (wg_b3b:
a_flip = 0.857 vs a_c = 0.943).  The reason is geometric: the winding of
the curve in the modal plane is a PROXY for "st lies inside the guard's
stable manifold", and the two agree only while the forced excursion is
small.  Here the forced fixed point sits 1.6 r_g away from st, the curve
is strongly deformed, and its rotation number is dragged from 0.618 down
through 0.5, so the proxy degrades.

The sharp object needs no proxy and is the one already used on the V
channel at r = 0.90: at threshold the trajectory launched from st lands
ON the guard invariant curve -- a point-to-invariant-curve heteroclinic
connection.  Below threshold it is repelled inward, above it passes and
escapes.  So the criterion is measured here as the minimum stroboscopic
distance from the launched trajectory to the continued guard curve, as a
function of the drive amplitude; the landing amplitude is where that
distance collapses.
Budget ~25 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/wgland.log', 'w')
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
K = 24
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
dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
out(f"G1 margin 0.10: w0={w0:.4f} r_g={rg:.5e}")

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
phi = 0.5*(math.sqrt(5.0) - 1.0)
Td = (8.0 + phi)*Tc
ws = 2*math.pi/Td
out(f"drive: T_d={Td:.6f}s w_s={ws:.5f} rad/s (w0/{w0/ws:.4f}), T_c={Tc:.6f}s")

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
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0
alo, ahi = 0.4, 1.4
for _ in range(18):
    am = 0.5*(alo+ahi)
    if fate(am, 40): ahi = am
    else: alo = am
ameas = 0.5*(alo+ahi)
out(f"measured a_c = {ameas:.7f} rad/s  [{time.time()-T0:.0f}s]")

BOX = 3.0
def strobe(x0, a):
    def f(t, y):
        x = y[:4]; qq = dict(pr, dw=a*math.sin(ws*t))
        return np.concatenate([rhs_w(x, qq),
                               (jac_a(x, qq) @ y[4:].reshape(4, 4)).ravel()])
    def gth(t, y): return abs(y[0] - st[0]) - BOX*dsad
    def gvl(t, y): return y[2] - 0.05*Vdc0
    def gvh(t, y): return y[2] - 8.0*Vdc0
    for e in (gth, gvl, gvh):
        e.terminal = True
    gth.direction = 1; gvl.direction = -1; gvh.direction = 1
    s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                  method='DOP853', rtol=1e-10, atol=1e-12,
                  events=(gth, gvl, gvh))
    if s.status != 0 or any(len(t) > 0 for t in s.t_events):
        return None, None
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
def tn(U, rho, a, itmax=14, tol=1e-9):
    Uref = U.copy(); dUref = dth_(Uref); res = None
    for it in range(itmax):
        Sh = shift_mat(rho); PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
        for j in range(K):
            pj, mj = strobe(U[j], a)
            if pj is None:
                return U, rho, False, None
            PhiU[j], Ms[j] = pj, mj
        R = PhiU - Sh @ U; c = float(np.sum(dUref*(U - Uref)))
        res = max(np.max(np.abs(R)), abs(c))
        if res < tol:
            return U, rho, True, res
        A = np.zeros((4*K+1, 4*K+1))
        for j in range(K):
            A[4*j:4*j+4, 4*j:4*j+4] += Ms[j]
        A[:4*K, :4*K] -= np.kron(Sh, I4)
        A[:4*K, -1] = -(dshift_mat(rho) @ U).flatten()
        A[-1, :4*K] = dUref.flatten()
        try:
            dy = np.linalg.solve(A, -np.concatenate([R.flatten(), [c]]))
        except np.linalg.LinAlgError:
            return U, rho, False, res
        nU = np.max(np.abs(dy[:4*K])); cap = max(0.005, 0.5*rg)
        if nU > cap: dy *= cap/nU
        U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
    return U, rho, False, res
scc = solve_ivp(lambda t, x: rhs_w(x, pr), (0, Tc), x0c, method='DOP853',
                rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
U = scc.y.T.copy()
rho = 2*math.pi*((Td/Tc) % 1.0)
U, rho, ok, res = tn(U, rho, 0.0)
out(f"guard curve at a=0: {'ok' if ok else 'FAIL'} residual {res:.2e}, "
    f"rho/2pi={rho/(2*math.pi):.6f}")
targets = [0.90, 0.95, 0.98, 1.00, 1.02, 1.05]
store = {}
cur = 0.0
for fr in targets:
    tgt = fr*ameas; okc = True
    while cur < tgt - 1e-12:
        stp = min(0.05*ameas, tgt-cur)
        for _try in range(4):
            Un, rn, okn, rs = tn(U.copy(), rho, cur+stp)
            if okn: break
            stp *= 0.5
        if not okn:
            okc = False; break
        U, rho, cur = Un, rn, cur+stp
    if not okc:
        out(f"  continuation stalled at a/a_c={cur/ameas:.3f}"); break
    store[fr] = (U.copy(), rho)
    out(f"  guard curve continued to a/a_c={fr:.3f} "
        f"(rho/2pi={rho/(2*math.pi):.6f}, residual {rs:.1e})  "
        f"[{time.time()-T0:.0f}s]")
out("landing test: min stroboscopic distance from the launched trajectory "
    "to the guard curve, in units of r_g")
for fr in sorted(store):
    Uc, rc = store[fr]
    dens = upsample(Uc, 1024)
    a = fr*ameas
    def f(t, x):
        return rhs_w(x, dict(pr, dw=a*math.sin(ws*t)))
    NP = 25
    s = solve_ivp(f, (0, NP*Td), st.copy(), method='DOP853',
                  rtol=1e-11, atol=1e-14,
                  t_eval=np.arange(NP+1)*Td)
    Y = s.y.T
    dmin = 1e9; nbest = -1
    for n in range(Y.shape[0]):
        dd = np.min(np.linalg.norm(dens - Y[n], axis=1))
        if dd < dmin:
            dmin = dd; nbest = n
    out(f"  a/a_c={fr:.3f}: min distance {dmin/rg:.5f} r_g at strobe step "
        f"{nbest} of {NP}  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
