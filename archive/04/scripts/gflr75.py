"""Deep-detuned band closure: G1 marg=0.10 at r=0.75 and r=0.70.
Per r: (1) compound-detector sudden-on threshold (escape-time aware:
window 300 periods, re-verify final bracket at 900); (2) guard-torus
continuation at the same wd with rho(eps) log + winding flip;
(3) compare. Watch rho0 near low-order rationals (r=0.75 -> ~2pi/3):
Newton stall there = criterion domain boundary (locking), report as
such. Budget ~30 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/gflr75.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])

prb = gset('G1')
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
P = margin_point(prb, 0.5*(lo+hi), 0.10)
pr = dict(prb, P=P)
co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; qv = co['q']; pv = co['p']
c1v = co['c1']; alpha = co['alpha']
zg = math.sqrt(alpha/c1v.real)
dsad = math.pi - 2*abs(st[0])
out(f"G1 marg0.10: P={P:.5f} w0={w0:.3f} zg={zg:.4e} dsad={dsad:.3f}")

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
out(f"guard cycle: Tc={Tc:.5f}")

for rr in (0.75, 0.70):
    wd = rr*w0
    Td = 2*math.pi/wd
    # ---- (1) measurement, escape-time aware ----
    def probe(eps, NPn):
        def f(t, x):
            return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
        def e_th(t, x): return abs(x[0] - st[0]) - (dsad + 0.15)
        def e_vlo(t, x): return x[2] - 0.2
        def e_vhi(t, x): return x[2] - 2.5
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
        ev = [len(s.t_events[i]) > 0 for i in range(3)]
        if any(ev):
            which = 'TH' if ev[0] else 'VLO' if ev[1] else 'VHI'
            te = min(t[0] for t in s.t_events if len(t))
            return which, te/Td
        if s.status < 0:
            return 'SOLVER', s.t[-1]/Td
        return None, NPn
    elo, ehi = 1e-4, 2e-4
    n = 0
    while probe(ehi, 300)[0] is None and n < 12:
        elo = ehi; ehi *= 1.5; n += 1
    if probe(ehi, 300)[0] is None:
        out(f"r={rr}: no escape up to {ehi:.3e} — skip"); continue
    for _ in range(11):
        em = 0.5*(elo+ehi)
        if probe(em, 300)[0] is not None: ehi = em
        else: elo = em
    w9, t9 = probe(elo, 900)
    if w9 is not None:
        out(f"r={rr}: NOTE window effect — lo edge escapes at 900p "
            f"({w9} {t9:.0f}p); rebisect")
        ehi = elo; elo = 0.7*elo
        for _ in range(9):
            em = 0.5*(elo+ehi)
            if probe(em, 900)[0] is not None: ehi = em
            else: elo = em
    emeas = 0.5*(elo+ehi)
    wm, tm = probe(ehi, 900)
    out(f"r={rr}: MEAS eps_c={emeas:.4e} mode={wm} t_esc={tm:.0f}p "
        f"[{time.time()-T0:.0f}s]")
    # ---- (2) torus continuation + winding flip ----
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
    out(f"r={rr}: rho0_guess={rho:.6f} (={rho/(2*math.pi):.4f} of 2pi)")
    U, rho, ok, res = torus_newton(U, rho, 0.0)
    if not ok:
        out(f"r={rr}: eps=0 Newton FAILED res={res:.1e} "
            f"(strong resonance?) — criterion domain boundary")
        continue
    wref = winding(U)
    out(f"r={rr}: rho(0)={rho:.6f} winding_ref={wref} res={res:.1e}")
    eps = 0.0
    deps = 0.04*emeas
    flip = None
    nlog = 0
    while eps < 1.35*emeas:
        e_try = eps + deps
        Un, rn, okn, resn = torus_newton(U.copy(), rho, e_try)
        if not okn:
            deps *= 0.5
            if deps < 2e-4*emeas:
                out(f"r={rr}: continuation STALL at {eps/emeas:.3f}x "
                    f"meas, res={resn:.1e} (locking/breakup)")
                break
            continue
        if winding(Un) != wref:
            flip = (eps, e_try)
            break
        U, rho, eps = Un, rn, e_try
        nlog += 1
        if nlog % 5 == 0 or eps > 0.85*emeas:
            out(f"  r={rr} eps={eps/emeas:.3f}x: rho={rho:.6f} "
                f"[{time.time()-T0:.0f}s]")
        deps = min(deps*1.3, 0.05*emeas)
    if flip:
        ea, eb = flip
        Ua, ra = U.copy(), rho
        for _ in range(10):
            em = 0.5*(ea+eb)
            Um, rm, okm, _ = torus_newton(Ua.copy(), ra, em)
            if not okm:
                eb = em; continue
            if winding(Um) == wref:
                ea, Ua, ra = em, Um, rm
            else:
                eb = em
        ef = 0.5*(ea+eb)
        out(f"r={rr}: RESULT flip={ef:.4e} meas={emeas:.4e} "
            f"err={(ef-emeas)/emeas*100:+.2f}% [{time.time()-T0:.0f}s]")
    else:
        out(f"r={rr}: no winding flip up to 1.35x meas "
            f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
