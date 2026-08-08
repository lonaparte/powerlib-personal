"""Audit of remaining conclusions against the detector lesson.
A. Strong-class thresholds re-bisected with the compound detector
   (G1, Xg=0.70): expect equality with theta-only values.
A2. G1 kick threshold kappa_c(0) with compound detector.
B. idx17: fresh winding-flip continuation (its 1.22x anomaly).
C. idx0: compound-detector threshold vs its flip.
D. C=0.02 @ ws=w0/32: re-measure a_c with compound detector + mode
   (the +26% outlier suspect).
E. idx2 unforced outer attractor with guards: bounded? Vdc range?
F. GFM M1 kick threshold with E-guard: expect unchanged.
Budget ~20 min; progress timestamps per block.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/verify.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def build(over, marg):
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
    return dict(prb, P=P)

def compound_probe(pr, st, wd, eps, T, x0=None, t0=0.0):
    dsad = math.pi - 2*abs(st[0])
    def f(t, x):
        qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        return rhs(x, qq)
    def e_th(t, x): return abs(x[0] - st[0]) - min(1.2, dsad)
    def e_vlo(t, x): return x[2] - 0.2
    def e_vhi(t, x): return x[2] - 2.5
    e_th.terminal = True; e_th.direction = 1
    e_vlo.terminal = True; e_vlo.direction = -1
    e_vhi.terminal = True; e_vhi.direction = 1
    s = solve_ivp(f, (t0, t0+T), st.copy() if x0 is None else x0,
                  method='DOP853', rtol=1e-9, atol=1e-12,
                  events=[e_th, e_vlo, e_vhi])
    for i, m in ((0, 'TH'), (1, 'VLO'), (2, 'VHI')):
        if len(s.t_events[i]):
            return m
    if s.status == -1 or s.t[-1] < t0 + T - 1:
        return 'DEATH'
    return 'OK'

# ---- A: strong-class thresholds with compound detector ----
for tag, over, marg, wfac, ecref, lo0, hi0 in (
        ('G1', {}, 0.10, 0.90, 1.1865e-4, 1.16e-4, 1.22e-4),
        ('Xg=0.70', dict(Xg=0.70), 0.10, 0.90, 4.0422e-4, 3.9e-4, 4.2e-4)):
    pr = build(over, marg)
    co = nf_coeffs(pr)
    st = co['st']; wd = wfac*co['w0']
    lo, hi = lo0, hi0
    aok = compound_probe(pr, st, wd, lo, 450) == 'OK'
    bbad = compound_probe(pr, st, wd, hi, 450) != 'OK'
    if not (aok and bbad):
        out(f"A {tag}: bracket invalid (lo_ok={aok}, hi_bad={bbad})")
        continue
    mode = '?'
    for _ in range(9):
        m = 0.5*(lo+hi)
        r = compound_probe(pr, st, wd, m, 450)
        if r == 'OK': lo = m
        else: hi = m; mode = r
    ec = 0.5*(lo+hi)
    out(f"A {tag}: eps_c(compound)={ec:.5e} vs theta-only {ecref:.5e} "
        f"diff={(ec-ecref)/ecref*100:+.2f}% first-trip={mode} "
        f"[{time.time()-T0:.0f}s]")

# ---- A2: G1 kick threshold with compound detector ----
pr = build({}, 0.10)
co = nf_coeffs(pr)
st = co['st']; qv = co['q']; wd = 0.9*co['w0']
def kickprobe(kap):
    xk = st + 2*np.real(kap*qv)
    return compound_probe(pr, st, wd, 0.0, 150, x0=xk)
klo, khi = 0.0, 0.02
mode = '?'
for _ in range(10):
    km = 0.5*(klo+khi)
    r = kickprobe(km)
    if r == 'OK': klo = km
    else: khi = km; mode = r
out(f"A2 G1 kappa_c(0) compound={0.5*(klo+khi):.4e} vs theta-only "
    f"8.4967e-03 mode={mode} [{time.time()-T0:.0f}s]")

# ---- B: idx17 fresh winding flip ----
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
pr17 = build(dict(kp=55., ki=1200., Xg=0.40), 0.08)
co17 = nf_coeffs(pr17)
st17 = co17['st']; w017 = co17['w0']; q17 = co17['q']; p17 = co17['p']
c117 = co17['c1']; a17 = co17['alpha']
wd17 = 0.92*w017
Td17 = 2*math.pi/wd17
zg17 = math.sqrt(a17/c117.real)
def strobe_var17(x0, eps):
    def f(t, y):
        x = y[:4]
        qq = dict(pr17, V=pr17['V'] + eps*math.cos(wd17*t))
        Phi = y[4:].reshape(4, 4)
        return np.concatenate([rhs(x, qq), (jac_a(x, qq) @ Phi).ravel()])
    y0 = np.concatenate([x0, np.eye(4).ravel()])
    s = solve_ivp(f, (0, Td17), y0, method='DOP853', rtol=1e-11,
                  atol=1e-13)
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
def torus_newton17(U, rho, eps, itmax=25, tol=1e-10):
    Uref = U.copy(); dUref = dtheta_(Uref)
    for it in range(itmax):
        Sh = shift_mat(rho)
        PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
        for j in range(K):
            PhiU[j], Ms[j] = strobe_var17(U[j], eps)
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
        cap = max(0.005, 0.5*zg17)
        if nU > cap:
            dy *= cap/nU
        U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
    return U, rho, res < 1e-9
def winding17(Ua):
    dens = upsample(Ua, 2048)
    Z = (dens - st17) @ np.conj(p17)
    dph = np.angle(Z*np.conj(np.roll(Z, 1)))
    return int(round(float(np.sum(dph))/(2*math.pi)))
def flow_auto17(x0, T, with_var=False):
    def f(t, y):
        x = y[:4]
        if not with_var:
            return rhs(x, pr17)
        Phi = y[4:].reshape(4, 4)
        return np.concatenate([rhs(x, pr17),
                               (jac_a(x, pr17) @ Phi).ravel()])
    y0 = x0 if not with_var else np.concatenate([x0, np.eye(4).ravel()])
    s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12, atol=1e-14)
    return (s.y[:4, -1] if not with_var
            else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
def cyc_newton17(xs, Ts, itmax=40):
    x, T = xs.copy(), Ts
    fref = rhs(xs, pr17)
    for it in range(itmax):
        xT, M = flow_auto17(x, T, with_var=True)
        R = np.append(xT - x, np.dot(fref, x - xs))
        if np.max(np.abs(R)) < 1e-12:
            return x, T, True
        A5 = np.zeros((5, 5))
        A5[:4, :4] = M - np.eye(4)
        A5[:4, 4] = rhs(xT, pr17)
        A5[4, :4] = fref
        dy = np.linalg.solve(A5, -R)
        n = np.linalg.norm(dy[:4])
        cap = max(0.01, 0.5*zg17)
        if n > cap:
            dy *= cap/n
        if abs(dy[4]) > 0.1*T:
            dy *= 0.1*T/abs(dy[4])
        x = x + dy[:4]; T = T + dy[4]
    return x, T, np.max(np.abs(R)) < 1e-9
got = False
for fac in (1.0, 0.85, 0.7, 1.2):
    xs = st17 + 2*np.real(fac*zg17*q17)
    Ts = 2*math.pi/(w017 + c117.imag*(fac*zg17)**2)
    x0c, Tc, okc = cyc_newton17(xs, Ts)
    if okc and abs(np.vdot(p17, x0c - st17)) > 0.2*zg17:
        got = True; break
if got:
    scc = solve_ivp(lambda t, x: rhs(x, pr17), (0, Tc), x0c,
                    method='DOP853', rtol=1e-12, atol=1e-14,
                    t_eval=np.arange(K)*Tc/K)
    U = scc.y.T.copy()
    rho = 2*math.pi*((Td17/Tc) % 1.0)
    U, rho, ok = torus_newton17(U, rho, 0.0)
    wref = winding17(U)
    eps = 0.0; deps = 4e-4
    flip = None
    while eps < 1.2e-2:
        e_try = eps + deps
        Un, rn, okn = torus_newton17(U.copy(), rho, e_try)
        if not okn:
            deps *= 0.5
            if deps < 1e-6:
                out(f"B idx17: continuation stall at {eps:.4e}")
                break
            continue
        if winding17(Un) != wref:
            flip = (eps, e_try)
            break
        U, rho, eps = Un, rn, e_try
        deps = min(deps*1.4, 8e-4)
    if flip:
        ea, eb = flip
        Ua, ra = U.copy(), rho
        for _ in range(10):
            em = 0.5*(ea+eb)
            Um, rm, okm = torus_newton17(Ua.copy(), ra, em)
            if not okm:
                eb = em; continue
            if winding17(Um) == wref:
                ea, Ua, ra = em, Um, rm
            else:
                eb = em
        out(f"B idx17: fresh flip={0.5*(ea+eb):.4e} (old 7.0700e-03? "
            f"sweep 7.09997e-3), compound eps_true=8.6656e-3 "
            f"[{time.time()-T0:.0f}s]")
else:
    out("B idx17: cycle Newton failed")

# ---- C: idx0 compound threshold ----
pr0c = build(dict(Xg=0.35), 0.10)
co0 = nf_coeffs(pr0c)
st0 = co0['st']; wd0 = 0.9*co0['w0']
FL0 = 1.34613e-2
rows = []
for fe in (0.9, 0.98, 1.05, 1.2, 1.6):
    r = compound_probe(pr0c, st0, wd0, fe*FL0, 250)
    rows.append((fe, r))
out(f"C idx0 scan (x flip): " + ", ".join(f"{fe}:{r}" for fe, r in rows)
    + f" [{time.time()-T0:.0f}s]")

# ---- D: C=0.02 slow-drive outlier with compound detector ----
prd = build(dict(C=0.02), 0.10)
cod = nf_coeffs(prd)
std = cod['st']; w0d = cod['w0']
wsd = w0d/32
def probe_slow(a):
    dsad = math.pi - 2*abs(std[0])
    def f(t, x):
        qq = dict(prd, V=prd['V'] - a*math.sin(wsd*t))
        return rhs(x, qq)
    def e_th(t, x): return abs(x[0] - std[0]) - min(1.2, dsad)
    def e_vlo(t, x): return x[2] - 0.2
    def e_vhi(t, x): return x[2] - 2.5
    e_th.terminal = True; e_th.direction = 1
    e_vlo.terminal = True; e_vlo.direction = -1
    e_vhi.terminal = True; e_vhi.direction = 1
    T = 12*2*math.pi/wsd
    s = solve_ivp(f, (0, T), std.copy(), method='DOP853', rtol=1e-9,
                  atol=1e-12, events=[e_th, e_vlo, e_vhi])
    for i, m in ((0, 'TH'), (1, 'VLO'), (2, 'VHI')):
        if len(s.t_events[i]):
            return m
    if s.status == -1 or s.t[-1] < T - 1:
        return 'DEATH'
    return 'OK'
alo, ahi = 1e-4, 1.2e-2
mode = '?'
for _ in range(10):
    am = 0.5*(alo+ahi)
    r = probe_slow(am)
    if r == 'OK': alo = am
    else: ahi = am; mode = r
out(f"D C=0.02 ws=w0/32: a_c(compound)={0.5*(alo+ahi):.4e} vs "
    f"theta-only 5.7478e-3, 1D pred 7.268e-3, mode={mode} "
    f"[{time.time()-T0:.0f}s]")

# ---- E: idx2 unforced outer attractor with guards ----
pr2 = build(dict(kp=30., ki=600.), 0.10)
co2 = nf_coeffs(pr2)
st2 = co2['st']; q2 = co2['q']; p2 = co2['p']; c12 = co2['c1']
w02 = co2['w0']; zg2 = math.sqrt(co2['alpha']/c12.real)
def flow_auto2(x0, T, with_var=False):
    def f(t, y):
        x = y[:4]
        if not with_var:
            return rhs(x, pr2)
        Phi = y[4:].reshape(4, 4)
        return np.concatenate([rhs(x, pr2), (jac_a(x, pr2) @ Phi).ravel()])
    y0 = x0 if not with_var else np.concatenate([x0, np.eye(4).ravel()])
    s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12, atol=1e-14)
    return (s.y[:4, -1] if not with_var
            else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
def cyc2(xs, Ts, itmax=40):
    x, T = xs.copy(), Ts
    fref = rhs(xs, pr2)
    for it in range(itmax):
        xT, M = flow_auto2(x, T, with_var=True)
        R = np.append(xT - x, np.dot(fref, x - xs))
        if np.max(np.abs(R)) < 1e-12:
            return x, T, True
        A5 = np.zeros((5, 5))
        A5[:4, :4] = M - np.eye(4)
        A5[:4, 4] = rhs(xT, pr2)
        A5[4, :4] = fref
        dy = np.linalg.solve(A5, -R)
        n = np.linalg.norm(dy[:4])
        cap = max(0.01, 0.5*zg2)
        if n > cap:
            dy *= cap/n
        if abs(dy[4]) > 0.1*T:
            dy *= 0.1*T/abs(dy[4])
        x = x + dy[:4]; T = T + dy[4]
    return x, T, np.max(np.abs(R)) < 1e-9
got2 = False
for fac in (1.0, 0.85, 0.7, 1.2):
    xs = st2 + 2*np.real(fac*zg2*q2)
    Ts = 2*math.pi/(w02 + c12.imag*(fac*zg2)**2)
    x0c2, Tc2, okc = cyc2(xs, Ts)
    if okc and abs(np.vdot(p2, x0c2 - st2)) > 0.2*zg2:
        got2 = True; break
if got2:
    xout = st2 + 1.4*(x0c2 - st2)
    dsad2 = math.pi - 2*abs(st2[0])
    def f(t, x): return rhs(x, pr2)
    def e_th(t, x): return abs(x[0] - st2[0]) - (dsad2 + 0.15)
    def e_vlo(t, x): return x[2] - 0.2
    def e_vhi(t, x): return x[2] - 2.5
    e_th.terminal = True; e_th.direction = 1
    e_vlo.terminal = True; e_vlo.direction = -1
    e_vhi.terminal = True; e_vhi.direction = 1
    s = solve_ivp(f, (0, 120), xout, method='DOP853', rtol=1e-10,
                  atol=1e-13, events=[e_th, e_vlo, e_vhi],
                  dense_output=True)
    trig = [len(s.t_events[i]) for i in range(3)]
    if any(trig) or s.t[-1] < 119:
        out(f"E idx2 unforced outer: NOT bounded (events={trig}, "
            f"t_end={s.t[-1]:.1f})")
    else:
        tt = np.linspace(40, 120, 3000)
        xa = s.sol(tt)
        out(f"E idx2 unforced outer: bounded; Vdc range "
            f"[{float(np.min(xa[2])):.3f}, {float(np.max(xa[2])):.3f}], "
            f"theta-swing {float(np.max(np.abs(xa[0]-st2[0]))):.3f} "
            f"[{time.time()-T0:.0f}s]")
else:
    out("E idx2: cycle Newton failed")

# ---- F: GFM M1 kick with E-guard ----
from gfmlib import (rhs as grhs, jac as gjac, equil as gequil,
                    crit_mode as gcrit, maxre_cx, hopf_in, mset, fold,
                    escape_event, Enom)
prg = mset('M1', Xg=0.10)
dfold, Pm = fold(prg)
qh = hopf_in(prg, 'Pref', 0.02*Pm, 0.95*Pm)
P_H = qh['Pref']
def gg(P):
    r = maxre_cx(dict(prg, Pref=P))
    return 1.0 if r is None else r
Phi_ = min(0.95*Pm, 2.5*P_H)
tt_ = 0.10
if gg(Phi_) > -tt_:
    tt_ = max(0.3*abs(gg(Phi_)), 0.02)
lo2, hi2 = P_H, Phi_
for _ in range(45):
    m = 0.5*(lo2+hi2)
    if gg(m) > -tt_: lo2 = m
    else: hi2 = m
prm = dict(prg, Pref=0.5*(lo2+hi2))
stg = gequil(prm)
evd, dsadg = escape_event(prm)
E0g = Enom - prm['mq']*(stg[3] - prm['Qref'])
def kickg(dw):
    xk = stg.copy(); xk[1] += dw
    def f(t, x): return grhs(x, prm)
    def eE(t, x):
        return (Enom - prm['mq']*(x[3]-prm['Qref'])) - 0.2
    eE.terminal = True; eE.direction = -1
    s = solve_ivp(f, (0, 60), xk, method='DOP853', rtol=1e-9,
                  atol=1e-12, events=[evd, eE])
    if len(s.t_events[0]):
        return 'DELTA'
    if len(s.t_events[1]):
        return 'E-LOW'
    return 'OK'
lo3, hi3 = 20.0, 45.0
mode = '?'
for _ in range(10):
    dm = 0.5*(lo3+hi3)
    r = kickg(dm)
    if r == 'OK': lo3 = dm
    else: hi3 = dm; mode = r
out(f"F GFM M1: dw0(compound)={0.5*(lo3+hi3):.4f} vs delta-only "
    f"32.8125 mode={mode} [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
