"""idx17 resolution: the 1.22x 'anomaly' compared a measurement at
r=0.90 (recheck.py hardcoded wd=0.9*w0, 250s window) against the flip
criterion evaluated at the set's own r=0.92.
Part 1: winding-flip continuation at r=0.90 -> eflip90; compare vs the
        r=0.90 measurement 8.6656e-3 (criterion holds iff ratio ~1).
Part 2: r=0.92 long-horizon (1200-period) probes at 1.00/1.02/1.04x
        flip92 + escape-time power-law fit t=T0*(fac-fc)^-gamma over
        all r=0.92 escape times -> true eps_c(0.92) vs flip92.
Budget ~14 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/idx17r90.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])

over = dict(kp=55., ki=1200., Xg=0.40)
marg = 0.08
flip92 = 7.0991e-3
meas90 = 8.6656e-3
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
zg = math.sqrt(alpha/c1v.real)
out(f"idx17: P={P:.5f} w0={w0:.3f} zg={zg:.4e}")

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
def upsample(Ua, N):
    C = np.fft.fft(Ua, axis=0)
    Cp = np.zeros((N, Ua.shape[1]), complex)
    hf = K//2
    Cp[:hf] = C[:hf]; Cp[N-hf+1:] = C[hf+1:]
    Cp[hf] = 0.5*C[hf]; Cp[N-hf] = 0.5*C[hf]
    return np.real(np.fft.ifft(Cp, axis=0))*(N/K)
def winding(Ua):
    dens = upsample(Ua, 2048)
    Z = (dens - st) @ np.conj(pv)
    dph = np.angle(Z*np.conj(np.roll(Z, 1)))
    return int(round(float(np.sum(dph))/(2*math.pi)))
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
    out("cycle failed"); raise SystemExit
scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
                rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
Uc = scc.y.T.copy()

def make_strobe(wd, Td):
    def strobe_var(x0, eps):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq),
                                   (jac_a(x, qq) @ Phi).ravel()])
        y0 = np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11,
                      atol=1e-13)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    return strobe_var
def make_newton(strobe_var):
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
                return U, rho, True
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
        return U, rho, res < 1e-9
    return torus_newton

# ---- Part 1: winding flip at r=0.90 ----
wd90 = 0.90*w0
Td90 = 2*math.pi/wd90
tn90 = make_newton(make_strobe(wd90, Td90))
U = Uc.copy()
rho = 2*math.pi*((Td90/Tc) % 1.0)
U, rho, ok = tn90(U, rho, 0.0)
if not ok:
    out("P1: eps=0 Newton failed"); raise SystemExit
wref = winding(U)
out(f"P1 r=0.90: rho0={rho:.6f} winding_ref={wref}")
eps = 0.0; deps = 4e-4
flip = None
while eps < 1.3*meas90:
    e_try = eps + deps
    Un, rn, okn = tn90(U.copy(), rho, e_try)
    if not okn:
        deps *= 0.5
        if deps < 1e-6:
            out(f"P1 stall at {eps:.4e}"); break
        continue
    if winding(Un) != wref:
        flip = (eps, e_try)
        break
    U, rho, eps = Un, rn, e_try
    if eps > 0.85*meas90:
        deps = min(deps*1.2, 3e-4)
    else:
        deps = min(deps*1.4, 8e-4)
out(f"P1 bracket: {flip} [{time.time()-T0:.0f}s]")
if flip:
    ea, eb = flip
    Ua, ra = U.copy(), rho
    for _ in range(10):
        em = 0.5*(ea+eb)
        Um, rm, okm = tn90(Ua.copy(), ra, em)
        if not okm:
            eb = em; continue
        if winding(Um) == wref:
            ea, Ua, ra = em, Um, rm
        else:
            eb = em
    eflip90 = 0.5*(ea+eb)
    out(f"P1 RESULT: flip(r=0.90)={eflip90:.4e}  meas(r=0.90)={meas90:.4e}"
        f"  ratio meas/flip={meas90/eflip90:.3f} "
        f"err={(eflip90-meas90)/meas90*100:+.2f}% [{time.time()-T0:.0f}s]")

# ---- Part 2: r=0.92 long-horizon probes + escape-time fit ----
wd92 = 0.92*w0
Td92 = 2*math.pi/wd92
NP = 1200
def probe92(eps):
    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd92*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - 1.2
    def e_vlo(t, x): return x[2] - 0.2
    def e_vhi(t, x): return x[2] - 2.5
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NP*Td92), st.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-12, events=(e_th, e_vlo, e_vhi))
    ev = [len(s.t_events[i]) > 0 for i in range(3)]
    if any(ev):
        te = min(t[0] for t in s.t_events if len(t))
        which = 'TH' if ev[0] else 'VLO' if ev[1] else 'VHI'
        return which, te/Td92
    if s.status < 0:
        return 'SOLVER', s.t[-1]/Td92
    return 'BOUNDED', NP
tesc = [(1.06, 281), (1.10, 211), (1.14, 167), (1.18, 142),
        (1.22, 120), (1.26, 106), (1.30, 94)]     # from idx17rho
for fac in (1.00, 1.02, 1.04):
    which, np_ = probe92(fac*flip92)
    out(f"P2 fac={fac:.2f}: {which} at {np_:.0f} periods "
        f"[{time.time()-T0:.0f}s]")
    if which != 'BOUNDED':
        tesc.append((fac, np_))
tesc.sort()
fs = np.array([t[0] for t in tesc]); ts = np.array([t[1] for t in tesc])
best = None
for fc in np.linspace(0.85, min(fs)-0.005, 400):
    xlg = np.log(fs - fc); ylg = np.log(ts)
    A1 = np.vstack([np.ones_like(xlg), xlg]).T
    cf, res_, _, _ = np.linalg.lstsq(A1, ylg, rcond=None)
    sse = float(np.sum((A1 @ cf - ylg)**2))
    if best is None or sse < best[0]:
        best = (sse, fc, cf[0], cf[1])
sse, fc, lnT0, gam = best
out(f"P2 RESULT: escape-time fit t=T0*(fac-fc)^gamma: "
    f"fc={fc:.4f}x flip92, gamma={gam:.3f}, T0={math.exp(lnT0):.1f} "
    f"periods, sse={sse:.3e}")
out(f"P2: eps_c(r=0.92)={fc*flip92:.4e} vs flip92={flip92:.4e} "
    f"-> criterion err={(flip92-fc*flip92)/(fc*flip92)*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
