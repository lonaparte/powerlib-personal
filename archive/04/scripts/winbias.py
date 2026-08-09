"""How much of a threshold is the observation window?

lamu3 showed, on the idx17 cell, that the 400-period threshold sits
2.66% above the true (infinite-window) one, because the escape time
diverges logarithmically and 400 periods only reaches d ~ 3e-2.  Every
threshold in the campaign was measured with a finite window, so the size
of that systematic has to be established on the cell where the winding
criterion was checked, not only where it was discovered.

Cell: G1, V channel, r = 0.9, margin alpha = 0.10 -- the same cell as the
eps_c(alpha) sweep.  Measured here:
  (1) eps_c at windows of 200 / 400 / 1000 / 4000 / 20000 drive periods;
  (2) the escape-time curve and the three-parameter law
      t = S ln(1/(eps/eps* - 1)) + C, giving the converged threshold eps*
      and the asymptotic slope, plus the local slope of the two smallest-d
      chords (which is what "asymptotic" means operationally);
  (3) the winding-flip criterion value on the same cell.
Then: is the criterion the FINITE-window threshold or the converged one?
That decides whether the +-0.4% agreement reported over the margin sweep
is against the right target.
Budget ~20 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
from scipy.optimize import least_squares
LOG = open('sweep20/winbias.log', 'w')
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
P0 = margin_point(prb, 0.5*(lo+hi), 0.10)
pr = dict(prb, P=P0)
co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']; c1v = co['c1']
qv = co['q']; pv = co['p']; lam = co['lam']
rg = math.sqrt(alpha/c1v.real)
dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
wd = 0.9*w0; Td = 2*math.pi/wd
out(f"G1 margin 0.10: w0={w0:.4f} r_g={rg:.5e} T_d={Td:.6f}s "
    f"2alpha={2*alpha:.4f}")

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
    elo, ehi = 6e-5, 3e-4
    while esc_time(ehi, NP) is None and ehi < 5e-3:
        elo = ehi; ehi *= 1.4
    while esc_time(elo, NP) is not None and elo > 1e-6:
        ehi = elo; elo *= 0.7
    for _ in range(22):
        em = 0.5*(elo+ehi)
        if esc_time(em, NP) is not None: ehi = em
        else: elo = em
    return 0.5*(elo+ehi)
tab = {}
for NP in (200, 400, 1000, 4000, 20000):
    tab[NP] = thresh(NP)
    out(f"(1) eps_c({NP:6d} periods) = {tab[NP]:.8e}  "
        f"[{time.time()-T0:.0f}s]")
base = tab[20000]
for NP in (200, 400, 1000, 4000):
    out(f"    window bias at {NP:6d} periods: "
        f"{(tab[NP]-base)/base*100:+.3f}%")

ds = np.array([1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2, 1e-1, 3e-1, 8e-1])
EE, TT = [], []
for d in ds:
    e = base*(1.0 + d)
    te = esc_time(e, 200000)
    if te is None:
        out(f"    d={d:.1e}: no escape"); continue
    EE.append(e); TT.append(te)
    out(f"    d={d:.1e}  t_esc={te:.2f} periods  [{time.time()-T0:.0f}s]")
EE = np.array(EE); TT = np.array(TT)
def resid(p):
    S, C, es = p
    dd = np.maximum(EE/es - 1.0, 1e-14)
    return S*np.log(1.0/dd) + C - TT
sol = least_squares(resid, [150.0, -50.0, base*(1-1e-5)],
                    x_scale=[10.0, 10.0, base*1e-5])
S, C, estar = sol.x
out(f"(2) 3-parameter fit: S={S:.3f} periods, C={C:+.3f}, "
    f"eps*={estar:.8e} ({(estar-base)/base*100:+.4f}% vs the 20000-period "
    f"threshold), rms {float(np.sqrt(np.mean(sol.fun**2))):.2f} periods")
if len(TT) >= 3:
    sl1 = (TT[0]-TT[1])/math.log(ds[1]/ds[0])
    sl2 = (TT[1]-TT[2])/math.log(ds[2]/ds[1])
    out(f"    local slope of the two smallest-d chords: {sl1:.2f} and "
        f"{sl2:.2f} periods per e-fold in d")

# ---------------- winding-flip criterion on the same cell -------------
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
wref = wind(U); eps = 0.0; deps = 0.04*base; flip = None
while eps < 1.3*base:
    e = eps + deps
    Un, rn, okn = tn(U.copy(), rho, e)
    if not okn:
        deps *= 0.5
        if deps < 2e-4*base: break
        continue
    if wind(Un) != wref:
        flip = (eps, e); break
    U, rho, eps = Un, rn, e
    deps = min(deps*1.3, 0.05*base)
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
out(f"(3) winding-flip threshold = {ef:.8e}")
out(f"    vs converged eps* : {(ef-estar)/estar*100:+.3f}%")
out(f"    vs eps_c(400)     : {(ef-tab[400])/tab[400]*100:+.3f}%")
out(f"    vs eps_c(20000)   : {(ef-base)/base*100:+.3f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
