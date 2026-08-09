"""The winding criterion, stated about the right point.

The B3 criterion is "the guard object stops enclosing the state the
system actually sits at".  It has been evaluated as the winding of the
guard invariant curve about the UNFORCED equilibrium st.  That is only a
proxy: under forcing the system does not sit at st, it sits on the forced
orbit, which in the stroboscopic map is a fixed point x_a(eps) obtained
by continuing st.  The proxy is harmless while |x_a - st| is small
compared with the guard radius -- and it is NOT small here: at threshold
the linear modal response is 0.65 r_g on the V channel and 1.6 r_g on the
omega_g channel.  The omega_g cell measured with the proxy came out about
6% low, which is the size one would expect from exactly this error.

Evaluated here on both cells, in one script, so the correction is applied
to a channel where it should matter little and to one where it should
matter a lot:
    winding of the guard curve about st        (proxy, as before)
    winding of the guard curve about x_a(eps)  (corrected)
x_a is continued alongside the curve by Newton on Phi(x) = x using the
same stroboscopic map and its variational Jacobian.
Budget ~30 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/flipfix.log', 'w')
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
out(f"G1 margin 0.10: w0={w0:.4f} r_g={rg:.5e} d_sad={dsad:.5f}")

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

CELLS = [('V', 0.9*w0, None), ('dw', 2*math.pi/((8.0+phi)*Tc), None)]
for chan, wdr, _ in CELLS:
    Td = 2*math.pi/wdr
    out(f"=== channel {chan}: w_drive={wdr:.5f} rad/s, T_d={Td:.6f}s, "
        f"T_d/T_c={Td/Tc:.5f}")
    def prm_at(t, a):
        if chan == 'V':
            return dict(pr, V=pr['V'] + a*math.cos(wdr*t))
        return dict(pr, dw=a*math.sin(wdr*t))
    def fate(a, NP):
        def f(t, x):
            return rhs_w(x, prm_at(t, a))
        def e_th(t, x): return abs(x[0] - st[0]) - dsad
        def e_vlo(t, x): return x[2] - 0.20*Vdc0
        def e_vhi(t, x): return x[2] - 2.50*Vdc0
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, NP*Td), st.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
        return any(len(t) > 0 for t in s.t_events) or s.status < 0
    seed = 1.2e-4 if chan == 'V' else 0.9
    alo, ahi = 0.4*seed, 1.3*seed
    n = 0
    while not fate(ahi, 400 if chan == 'V' else 40) and n < 16:
        alo = ahi; ahi *= 1.4; n += 1
    n = 0
    while fate(alo, 400 if chan == 'V' else 40) and n < 16:
        ahi = alo; alo *= 0.6; n += 1
    NPu = 400 if chan == 'V' else 40
    for _ in range(16):
        am = 0.5*(alo+ahi)
        if fate(am, NPu): ahi = am
        else: alo = am
    ameas = 0.5*(alo+ahi)
    out(f"  measured threshold = {ameas:.6e}  [{time.time()-T0:.0f}s]")
    BOX = 3.0
    def strobe(x0, a):
        def f(t, y):
            x = y[:4]; qq = prm_at(t, a)
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
    def fixpt(x0, a, itmax=20):
        x = x0.copy()
        for it in range(itmax):
            xT, M = strobe(x, a)
            if xT is None:
                return None
            R = xT - x
            if np.max(np.abs(R)) < 1e-11:
                return x
            try:
                dx = np.linalg.solve(M - np.eye(4), -R)
            except np.linalg.LinAlgError:
                return None
            n2 = np.linalg.norm(dx)
            if n2 > 0.5*rg: dx *= 0.5*rg/n2
            x = x + dx
        return None
    def tn(U, rho, a, itmax=12, tol=1e-7):
        Uref = U.copy(); dUref = dth_(Uref); res = None
        for it in range(itmax):
            Sh = shift_mat(rho); PhiU = np.zeros((K, 4))
            Ms = np.zeros((K, 4, 4))
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
    def wind(Ua, ctr):
        dens = upsample(Ua, 2048)
        Z = (dens - ctr) @ np.conj(pv)
        dph = np.angle(Z*np.conj(np.roll(Z, 1)))
        return int(round(float(np.sum(dph))/(2*math.pi)))
    scc = solve_ivp(lambda t, x: rhs_w(x, pr), (0, Tc), x0c,
                    method='DOP853', rtol=1e-12, atol=1e-14,
                    t_eval=np.arange(K)*Tc/K)
    U = scc.y.T.copy()
    rho = 2*math.pi*((Td/Tc) % 1.0)
    U, rho, ok = tn(U, rho, 0.0)
    xa = st.copy()
    if not ok:
        out("  a=0 Newton failed"); continue
    wst0 = wind(U, st); wxa0 = wind(U, xa)
    out(f"  a=0: rho/2pi={rho/(2*math.pi):.6f} wind(st)={wst0} "
        f"wind(x_a)={wxa0}")
    aa = 0.0; da = 0.05*ameas
    fl_st = None; fl_xa = None; hist = []
    while aa < 1.35*ameas:
        an = aa + da
        Un, rn, okn = tn(U.copy(), rho, an)
        xn = fixpt(xa, an)
        if (not okn) or xn is None:
            da *= 0.5
            if da < 5e-3*ameas:
                out(f"  continuation stops at a={an:.6e} "
                    f"(a/a_c={an/ameas:.3f})")
                break
            continue
        wst = wind(Un, st); wxa = wind(Un, xn)
        hist.append((an, Un.copy(), rn, xn.copy()))
        out(f"    a={an:.6e} (a/a_c={an/ameas:.3f}) rho/2pi="
            f"{rn/(2*math.pi):.6f} |x_a-st|_modal="
            f"{abs(np.vdot(pv, xn-st))/rg:.3f} r_g  wind(st)={wst} "
            f"wind(x_a)={wxa}  [{time.time()-T0:.0f}s]")
        if fl_st is None and wst != wst0:
            fl_st = (aa, an)
        if fl_xa is None and wxa != wxa0:
            fl_xa = (aa, an)
        if fl_st is not None and fl_xa is not None:
            break
        U, rho, xa, aa = Un, rn, xn, an
        da = min(da*1.2, 0.06*ameas)
    def refine(brk, about):
        ea, eb = brk
        Ua = None; ra = None; xr = None
        for h in hist:
            if h[0] <= ea + 1e-15:
                Ua, ra, xr = h[1].copy(), h[2], h[3].copy()
        if Ua is None:
            Ua, ra, xr = U.copy(), rho, xa.copy()
        w0r = wst0 if about == 'st' else wxa0
        for _ in range(9):
            em = 0.5*(ea+eb)
            Um, rm, okm = tn(Ua.copy(), ra, em)
            xm = fixpt(xr, em)
            if (not okm) or xm is None:
                eb = em; continue
            ctr = st if about == 'st' else xm
            if wind(Um, ctr) == w0r:
                ea, Ua, ra, xr = em, Um, rm, xm
            else:
                eb = em
        return 0.5*(ea+eb)
    if fl_st:
        v1 = refine(fl_st, 'st')
        out(f"  RESULT winding about st     : {v1:.6e}  "
            f"err vs measured {(v1-ameas)/ameas*100:+.2f}%")
    else:
        out("  RESULT winding about st     : no flip below 1.35 a_c")
    if fl_xa:
        v2 = refine(fl_xa, 'xa')
        out(f"  RESULT winding about x_a    : {v2:.6e}  "
            f"err vs measured {(v2-ameas)/ameas*100:+.2f}%")
    else:
        out("  RESULT winding about x_a    : no flip below 1.35 a_c")
out(f"DONE wall={time.time()-T0:.0f}s")
