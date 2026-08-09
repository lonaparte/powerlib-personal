"""Where the margin sweep ends, and why.

The eps_c(alpha) sweep stopped at alpha = 0.30 with a domain error in
r_g = sqrt(alpha / Re c1).  That is not a numerical accident: along the
path P0(alpha) the first Lyapunov coefficient Re c1 changes sign, i.e.
the Hopf turns from subcritical to supercritical.  Past that margin the
guard cycle does not exist and the whole A4/A5 branch of the tree does
not apply -- the object that fails is a different one.  The sweep
therefore has a physical endpoint, and it should be located, not
worked around.

Located here: the margin alpha_deg at which Re c1 = 0 (a degenerate Hopf
/ Bautin point on the operating path), by bisection on the same P0(alpha)
map used by the sweep, plus a table of Re c1 along the way.  One more
sweep row is then measured at a margin inside the subcritical range but
above the previous top, to confirm the criterion still holds where r_g is
already inflated by the approach to the degeneracy.
Budget ~12 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/alphatop.log', 'w')
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
PH = 0.5*(lo+hi)
out(f"G1: P_H={PH:.6f}")
out("margin |   P0        Re c1        Im c1     r_g")
def cof(marg):
    P0 = margin_point(prb, PH, marg)
    return P0, nf_coeffs(dict(prb, P=P0))
for marg in (0.05, 0.10, 0.15, 0.20, 0.22, 0.24, 0.26, 0.28, 0.30):
    P0, co = cof(marg)
    c1v = co['c1']
    rgs = (f"{math.sqrt(co['alpha']/c1v.real):.5e}" if c1v.real > 0
           else "   ---   ")
    out(f"{marg:.3f}  | {P0:.6f}  {c1v.real:+.4e}  {c1v.imag:+.4e}  {rgs}")
mlo, mhi = 0.20, 0.30
for _ in range(30):
    mm = 0.5*(mlo+mhi)
    _, co = cof(mm)
    if co['c1'].real > 0: mlo = mm
    else: mhi = mm
mdeg = 0.5*(mlo+mhi)
P0d, cod = cof(mdeg)
out(f"degenerate (Bautin) margin alpha_deg = {mdeg:.6f} at P0={P0d:.6f}, "
    f"Re c1 = {cod['c1'].real:+.3e}  [{time.time()-T0:.0f}s]")
out("subcritical guard exists for alpha < alpha_deg; above it the Hopf is "
    "supercritical and the A4/A5 guard object is absent")

marg = 0.90*mdeg
P0, co = cof(marg)
pr = dict(prb, P=P0)
st = co['st']; w0 = co['w0']; alpha = co['alpha']; c1v = co['c1']
qv = co['q']; pv = co['p']; lam = co['lam']
rg = math.sqrt(alpha/c1v.real)
dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
wd = 0.9*w0; Td = 2*math.pi/wd
hh = 1e-6
fV = (rhs(st, dict(pr, V=pr['V']+hh))
      - rhs(st, dict(pr, V=pr['V']-hh)))/(2*hh)
cpl = abs(np.vdot(pv, fV))
est = 2*rg*abs(lam - 1j*wd)/cpl
out(f"extra sweep row at margin {marg:.5f} (0.9 alpha_deg): "
    f"r_g={rg:.5e} |<p,f_V>|={cpl:.2f} est={est:.5e}")
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
    return (any(len(s.t_events[i]) > 0 for i in range(3)) or s.status < 0)
elo, ehi = 0.3*est, 1.2*est
n = 0
while not probe(ehi) and n < 12:
    elo = ehi; ehi *= 1.4; n += 1
n = 0
while probe(elo) and n < 12:
    ehi = elo; elo *= 0.6; n += 1
emeas = float('nan')
if not probe(elo) and probe(ehi):
    for _ in range(16):
        em = 0.5*(elo+ehi)
        if probe(em): ehi = em
        else: elo = em
    emeas = 0.5*(elo+ehi)
out(f"  measured eps_c(400 periods) = {emeas:.5e}  "
    f"est/meas = {est/emeas:.4f}  eps_c/sqrt(alpha) = "
    f"{emeas/math.sqrt(alpha):.5e}  [{time.time()-T0:.0f}s]")

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
    out("  guard cycle Newton failed"); raise SystemExit
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
def wind(Ua):
    dens = upsample(Ua, 2048)
    Z = (dens - st) @ np.conj(pv)
    dph = np.angle(Z*np.conj(np.roll(Z, 1)))
    return int(round(float(np.sum(dph))/(2*math.pi)))
scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
                rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
U = scc.y.T.copy()
rho = 2*math.pi*((Td/Tc) % 1.0)
U, rho, ok = tn(U, rho, 0.0)
wref = wind(U); eps = 0.0; deps = 0.04*emeas; flip = None
while eps < 1.3*emeas:
    e = eps + deps
    Un, rn, okn = tn(U.copy(), rho, e)
    if not okn:
        deps *= 0.5
        if deps < 2e-4*emeas: break
        continue
    if wind(Un) != wref:
        flip = (eps, e); break
    U, rho, eps = Un, rn, e
    deps = min(deps*1.3, 0.05*emeas)
ef = float('nan')
if flip:
    ea, eb = flip; Ua, ra = U.copy(), rho
    for _ in range(12):
        em = 0.5*(ea+eb)
        Um, rm, okm = tn(Ua.copy(), ra, em)
        if not okm:
            eb = em; continue
        if wind(Um) == wref: ea, Ua, ra = em, Um, rm
        else: eb = em
    ef = 0.5*(ea+eb)
out(f"  winding flip = {ef:.5e}  err vs measured = "
    f"{(ef-emeas)/emeas*100:+.2f}%  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
