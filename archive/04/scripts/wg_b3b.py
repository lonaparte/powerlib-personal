"""omega_g slow band with the B3 machinery -- second attempt, with the
cost pathology fixed and the rotation number watched.

First attempt (wg_b3.py) reached a/a_c = 0.695 and then stalled: the
stroboscopic integration over the slow drive period was being asked to
follow Newton iterates that wander into the region where the DC-link
term 1/Vdc is nearly singular, where the adaptive solver spends
unbounded time.  Killed at 33 min.

Fixes here, all mechanical:
  * the stroboscopic integration carries a box guard (theta within the
    saddle distance, Vdc within a wide band around Vdc*); leaving the box
    aborts that integration and is reported as a Newton failure instead
    of costing minutes;
  * K = 24 collocation points with a secant predictor in the drive
    amplitude, so each Newton needs a few iterations instead of twenty;
  * the rotation number is printed at every step.  In the first attempt
    rho/2pi fell from 0.618 towards 0.5 as the drive grew, i.e. the guard
    invariant curve is being dragged into the 1:2 lock.  If the curve is
    destroyed by the lock BEFORE its winding about the operating point
    flips, that is the mechanism -- and it is a different node of the
    tree (rotation-number locking) than the winding flip.  Both outcomes
    are reported explicitly rather than being merged into one number.
Drive period fixed to (8+phi) T_c with phi the golden mean, so that the
unforced rotation number is maximally far from every lock.
Budget ~25 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/wg_b3b.log', 'w')
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
out(f"G1: P0={P0:.5f} w0={w0:.4f} alpha={alpha:.4f} r_g={rg:.5e} "
    f"d_sad={dsad:.5f}")

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
mu_u = max(np.linalg.eigvals(Mon), key=lambda z: abs(z))
out(f"guard cycle: T_c={Tc:.6f}s exponent={math.log(abs(mu_u))/Tc:.5f}/s "
    f"(2 alpha={2*alpha:.5f})")
phi = 0.5*(math.sqrt(5.0) - 1.0)
Td = (8.0 + phi)*Tc
ws = 2*math.pi/Td
out(f"drive: T_d=(8+phi) T_c={Td:.6f}s w_s={ws:.5f} rad/s (w0/{w0/ws:.4f})")

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
a12 = thresh(12); a40 = thresh(40)
out(f"measured a_c: 12 periods {a12:.5f}, 40 periods {a40:.5f} rad/s "
    f"(window bias {(a12-a40)/a40*100:+.3f}%); phase amplitude "
    f"{math.degrees(a40/ws):.2f} deg  [{time.time()-T0:.0f}s]")
ameas = a40

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
                  method='DOP853', rtol=1e-9, atol=1e-11,
                  events=(gth, gvl, gvh))
    if s.status != 0 or any(len(t) > 0 for t in s.t_events):
        return None, None
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
def tn(U, rho, a, itmax=12, tol=1e-7):
    Uref = U.copy(); dUref = dth_(Uref); res = None
    for it in range(itmax):
        Sh = shift_mat(rho); PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
        for j in range(K):
            pj, mj = strobe(U[j], a)
            if pj is None:
                return U, rho, False
            PhiU[j], Ms[j] = pj, mj
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
        try:
            dy = np.linalg.solve(A, -np.concatenate([R.flatten(), [c]]))
        except np.linalg.LinAlgError:
            return U, rho, False
        nU = np.max(np.abs(dy[:4*K])); cap = max(0.005, 0.5*rg)
        if nU > cap: dy *= cap/nU
        U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
    return U, rho, False
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
out(f"B3: a=0 Newton {'ok' if ok else 'FAILED'} in {time.time()-t1:.1f}s, "
    f"rho/2pi={rho/(2*math.pi):.6f}, wind={wind(U)}")
if not ok:
    out("cannot continue"); raise SystemExit
wref = wind(U)
prev = (0.0, U.copy(), rho)
aa = 0.0; da = 0.05*ameas; flip = None; brk = None
while aa < 1.5*ameas:
    an = aa + da
    if prev[0] < aa:                      # secant predictor
        f_ = (an - prev[0])/(aa - prev[0])
        Up = prev[1] + f_*(U - prev[1]); rp = prev[2] + f_*(rho - prev[2])
    else:
        Up, rp = U.copy(), rho
    Un, rn, okn = tn(Up, rp, an)
    if not okn:
        da *= 0.5
        if da < 5e-3*ameas:
            brk = (aa, an); break
        continue
    wn = wind(Un)
    out(f"    a={an:.5f} (a/a_c={an/ameas:.3f}) rho/2pi={rn/(2*math.pi):.6f} "
        f"wind={wn}  [{time.time()-T0:.0f}s]")
    if wn != wref:
        flip = (aa, an); break
    prev = (aa, U.copy(), rho)
    U, rho, aa = Un, rn, an
    da = min(da*1.2, 0.06*ameas)
def refine(br, wtest):
    ea, eb = br; Ua, ra = U.copy(), rho
    for _ in range(9):
        em = 0.5*(ea+eb)
        Um, rm, okm = tn(Ua.copy(), ra, em)
        if not okm:
            eb = em; continue
        if wtest(Um): ea, Ua, ra = em, Um, rm
        else: eb = em
    return 0.5*(ea+eb)
if flip:
    af = refine(flip, lambda Um: wind(Um) == wref)
    out(f"RESULT winding flip a_flip={af:.5f} vs measured a_c={ameas:.5f}: "
        f"{(af-ameas)/ameas*100:+.2f}%")
elif brk:
    ab = refine(brk, lambda Um: True)
    out(f"RESULT the guard invariant curve is destroyed before its winding "
        f"flips: last continuable amplitude a_break={ab:.5f} "
        f"(a/a_c={ab/ameas:.3f}), rho/2pi there = {rho/(2*math.pi):.6f}")
    out("       mechanism is rotation-number locking of the guard object, "
        "not loss of enclosure")
else:
    out(f"RESULT no flip and no breakdown up to 1.5 a_c")
out(f"DONE wall={time.time()-T0:.0f}s")
