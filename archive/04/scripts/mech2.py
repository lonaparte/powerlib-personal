"""Re-derive the two cells where the closed form still misses.

The cross-saturation coefficient c_x closes the V channel at r = 0.9 to
<=0.49% over four margins and reproduces both the constant 1.545 and the
alpha exponent.  Two cells are still off and are attacked here at the
level of the derivation, not by fitting.

(A) idx17 (r = 0.92): eps_c +2.53%, lambda_u -2.17%.  Its X = 2.202
    versus 1.15 on the V cells, i.e. the drive removes 69% of the damping
    rather than 53%, so the expansion in a^2 is being used harder; and
    its guard radius r_g = 0.0987 is 11x larger than the V cell's, so the
    cubic truncation of the vector field is used harder too.  The two are
    separated by measuring the same threshold on the 4D CUBIC TAYLOR
    field (which isolates polynomial truncation, as in taylor4) and by
    adding the quintic term to the radial equation:
        rho' = -alpha_eff rho + Re c1 rho^3 + Re c2 rho^5
    with c2 from the 5th-order normal form (nf5's homological solution),
    so the guard is the root of a quadratic in rho^2 instead of a ratio.

(B) The direct test of c_x itself.  The coefficient predicts not only the
    threshold but the whole damping budget:
        alpha_eff(a) = alpha - Re c_x |a|^2 ,
        guard radius  rho_g^2 = alpha_eff/Re c1 ,
        transverse exponent of the guard curve  lambda_u = 2 alpha_eff .
    lambda_u(eps) is measured with the validated ring estimator at several
    drive amplitudes on the V cell and compared with 2(alpha - Re c_x
    eps^2/4).  This tests the coefficient directly rather than through the
    threshold.

(C) omega_g slow cell.  The kick is right (closed form 1.48 r_g against
    the measured forced-fixed-point offset 1.49 r_g) and the SIGN of the
    guard change is right (the drive enlarges the guard), but the
    magnitude is not: the formula predicts no escape at all.  Printed
    here: c_x split into its four channels (direct cubic, difference
    frequency, sum frequency, DC), the implied guard radius, and the
    guard radius measured from the continued invariant curve of the 4D
    system at the same drive amplitudes -- which decides between "c_x is
    wrong" and "the cubic normal form is being evaluated outside its
    range at 1.5 r_g".
Budget ~30 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/mech2.log', 'w')
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
def tensors(pr, st):
    av = _avl(st, pr)
    def B2(u, v):
        return np.array([sum(_Hl[i][j][k](*av)*u[j]*v[k]
                             for j in range(4) for k in range(4))
                         for i in range(4)])
    def C3(u, v, w):
        return np.array([sum(_Tl[i][j][k][l](*av)*u[j]*v[k]*w[l]
                             for j in range(4) for k in range(4)
                             for l in range(4)) for i in range(4)])
    return B2, C3
def cross_sat(pr, co, fu, wp, split=False):
    st = co['st']; qv = co['q']; pv = co['p']; w0 = co['w0']
    A = jac(st, pr); B2, C3 = tensors(pr, st); I = np.eye(4)
    H = np.linalg.solve(1j*wp*I - A, fu.astype(complex))
    Hc = np.conj(H)
    gp = np.linalg.solve(1j*(w0+wp)*I - A, B2(qv, H))
    gm = np.linalg.solve(1j*(w0-wp)*I - A, B2(qv, Hc))
    d0 = -np.linalg.solve(A, B2(H, Hc))
    t1 = np.vdot(pv, C3(qv, H, Hc)); t2 = np.vdot(pv, B2(H, gm))
    t3 = np.vdot(pv, B2(Hc, gp)); t4 = np.vdot(pv, B2(qv, d0))
    cx = t1 + t2 + t3 + t4
    return (cx, H, (t1, t2, t3, t4)) if split else (cx, H)
def hopf(base):
    Ps = 3*base['V']**2/(4*base['Xg'])
    def reA(P):
        q = dict(base, P=P); x = equil(q)
        if x is None: return None
        cm = crit_mode(jac(x, q))
        return None if cm is None else cm.real
    grid = np.linspace(0.05, 0.985, 60)*Ps
    va = [reA(P) for P in grid]; br = None
    for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
        if fa is not None and fb is not None and fa < 0 <= fb:
            br = (a, b); break
    lo, hi = br
    for _ in range(45):
        m = 0.5*(lo+hi); v = reA(m)
        if v is None or v >= 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)

# ============ (A) idx17: truncation vs a^2 expansion ============
over = dict(kp=55., ki=1200., Xg=0.40)
prb2 = gset('G1', **over)
P02 = margin_point(prb2, hopf(prb2), 0.08)
pr2 = dict(prb2, P=P02)
co2 = nf_coeffs(pr2)
st2 = co2['st']; w02 = co2['w0']; al2 = co2['alpha']; c12 = co2['c1']
lam2 = co2['lam']; pv2 = co2['p']; qv2 = co2['q']
rg2 = math.sqrt(al2/c12.real)
dsad2 = math.pi - 2*abs(st2[0]); Vdc02 = st2[2]
wp2 = 0.92*w02; Td2 = 2*math.pi/wp2
A2 = jac(st2, pr2)
hh = 1e-6
fV2 = (rhs(st2, dict(pr2, V=pr2['V']+hh))
       - rhs(st2, dict(pr2, V=pr2['V']-hh)))/(2*hh)
F2 = np.vdot(pv2, fV2)
cx2, H2 = cross_sat(pr2, co2, fV2, wp2)
J2 = abs(lam2)*abs(F2)/abs(wp2**2 + lam2**2)
X2 = cx2.real/(4*c12.real*J2**2)
epred2 = rg2/math.sqrt(J2**2 + cx2.real/(4*c12.real))
out(f"(A) idx17: r_g={rg2:.5e} (V cell has 9.06e-3), X={X2:.4f}, "
    f"cubic closed form eps_c={epred2:.6e}")
av2 = _avl(st2, pr2)
Hm2 = np.array([[[float(_Hl[i][j][k](*av2)) for k in range(4)]
                 for j in range(4)] for i in range(4)])
Cm2 = np.array([[[[float(_Tl[i][j][k][l](*av2)) for l in range(4)]
                  for k in range(4)] for j in range(4)] for i in range(4)])
def esc_kind(eps, kind, NP=400):
    if kind == 'exact':
        def f(t, y):
            return rhs(y + st2, dict(pr2, V=pr2['V'] + eps*math.cos(wp2*t)))
    else:
        def f(t, y):
            return (A2 @ y + 0.5*np.einsum('ijk,j,k->i', Hm2, y, y)
                    + np.einsum('ijkl,j,k,l->i', Cm2, y, y, y)/6.0
                    + eps*fV2*math.cos(wp2*t))
    def e_r(t, y):
        return abs(np.vdot(pv2, y)) - 5.0*rg2
    e_r.terminal = True; e_r.direction = 1
    s = solve_ivp(f, (0, NP*Td2), np.zeros(4), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_r,))
    return len(s.t_events[0]) > 0 or s.status < 0
def thr_kind(kind, seed):
    elo, ehi = 0.6*seed, 1.4*seed
    n = 0
    while not esc_kind(ehi, kind) and n < 12:
        elo = ehi; ehi *= 1.3; n += 1
    n = 0
    while esc_kind(elo, kind) and n < 12:
        ehi = elo; elo *= 0.7; n += 1
    if esc_kind(elo, kind) or not esc_kind(ehi, kind):
        return None
    for _ in range(16):
        em = 0.5*(elo+ehi)
        if esc_kind(em, kind): ehi = em
        else: elo = em
    return 0.5*(elo+ehi)
e_ex = thr_kind('exact', epred2)
e_ta = thr_kind('tay', epred2)
out(f"    4D exact (modal readout, 400 periods) {e_ex:.6e}; "
    f"4D cubic Taylor {e_ta:.6e}  -> polynomial truncation costs "
    f"{(e_ta-e_ex)/e_ex*100:+.2f}%  [{time.time()-T0:.0f}s]")
out(f"    closed form vs 4D cubic Taylor: "
    f"{(epred2-e_ta)/e_ta*100:+.2f}%  (this part is the a^2 expansion + "
    f"the one-carrier-per-frequency truncation)")

# ============ (B) direct test of c_x through lambda_u(eps) ============
prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0)
co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']; c1v = co['c1']
lam = co['lam']; pv = co['p']; qv = co['q']
rg = math.sqrt(alpha/c1v.real)
wp = 0.9*w0; Td = 2*math.pi/wp
fV = (rhs(st, dict(pr, V=pr['V']+hh)) - rhs(st, dict(pr, V=pr['V']-hh)))/(2*hh)
F = np.vdot(pv, fV)
cx, H = cross_sat(pr, co, fV, wp)
J = abs(lam)*abs(F)/abs(wp**2 + lam**2)
epred = rg/math.sqrt(J**2 + cx.real/(4*c1v.real))
K = 64
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
    return np.real(np.fft.ifft(np.fft.fft(U, axis=0)*(1j*mfreq)[:, None],
                               axis=0))
def mk_cell(prm, stv, rgv, wdr, chan):
    def prm_at(t, a):
        if chan == 'V':
            return dict(prm, V=prm['V'] + a*math.cos(wdr*t))
        return dict(prm, dw=a*math.sin(wdr*t))
    Tdr = 2*math.pi/wdr
    def strobe(x0, a):
        def f(t, y):
            x = y[:4]; qq = prm_at(t, a)
            return np.concatenate([rhs_w(x, qq),
                                   (jac_a(x, qq) @ y[4:].reshape(4, 4)).ravel()])
        s = solve_ivp(f, (0, Tdr), np.concatenate([x0, np.eye(4).ravel()]),
                      method='DOP853', rtol=1e-11, atol=1e-13)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    return prm_at, Tdr, strobe
def guard_cycle(prm, stv, rgv, qvv, pvv, w0v, c1vv):
    def flow(x0, T, var=False):
        def f(t, y):
            x = y[:4]
            if not var:
                return rhs_w(x, prm)
            return np.concatenate([rhs_w(x, prm),
                                   (jac_a(x, prm) @ y[4:].reshape(4, 4)).ravel()])
        y0 = x0 if not var else np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12, atol=1e-14)
        return (s.y[:4, -1] if not var
                else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
    for fac in (1.0, 0.85, 0.7, 1.2):
        xs = stv + 2*np.real(fac*rgv*qvv)
        T = 2*math.pi/(w0v + c1vv.imag*(fac*rgv)**2)
        x, R = xs.copy(), np.ones(5)
        fref = rhs_w(xs, prm)
        for it in range(40):
            xT, M = flow(x, T, var=True)
            R = np.append(xT - x, np.dot(fref, x - xs))
            if np.max(np.abs(R)) < 1e-12: break
            A5 = np.zeros((5, 5)); A5[:4, :4] = M - np.eye(4)
            A5[:4, 4] = rhs_w(xT, prm); A5[4, :4] = fref
            dy = np.linalg.solve(A5, -R)
            n2 = np.linalg.norm(dy[:4]); cap = max(0.01, 0.5*rgv)
            if n2 > cap: dy *= cap/n2
            if abs(dy[4]) > 0.1*T: dy *= 0.1*T/abs(dy[4])
            x = x + dy[:4]; T = T + dy[4]
        if np.max(np.abs(R)) < 1e-9 and abs(np.vdot(pvv, x - stv)) > 0.2*rgv:
            return x, T
    return None, None
def tn(U, rho, a, strobe, rgv, itmax=18, tol=1e-9):
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
        nU = np.max(np.abs(dy[:4*K])); cap = max(0.005, 0.5*rgv)
        if nU > cap: dy *= cap/nU
        U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
    return U, rho, False
def lam_ring(U, rho, a, strobe, Tdr, iters=700):
    Sh = shift_mat(rho); Shm = shift_mat(-rho)
    Ms = np.zeros((K, 4, 4))
    for j in range(K):
        _, Ms[j] = strobe(U[j], a)
    dU = dth_(U); dUs = Sh @ dU
    V = np.tile(np.array([0.7, 0.31, -0.22, 0.53]), (K, 1))
    for j in range(K):
        d = dU[j]; V[j] -= d*(d @ V[j])/(d @ d)
    V /= np.linalg.norm(V, axis=1, keepdims=True)
    for it in range(iters):
        Wp = np.empty((K, 4))
        for j in range(K):
            w = Ms[j] @ V[j]; d2 = dUs[j]
            Wp[j] = w - d2*(d2 @ w)/(d2 @ d2)
        Vn = Shm @ Wp
        for j in range(K):
            d = dU[j]; Vn[j] -= d*(d @ Vn[j])/(d @ d)
        Vn /= np.linalg.norm(Vn, axis=1, keepdims=True)
        for j in range(K):
            if Vn[j] @ V[j] < 0: Vn[j] = -Vn[j]
        V = Vn
    g = np.empty(K)
    for j in range(K):
        w = Ms[j] @ V[j]; d2 = dUs[j]
        w = w - d2*(d2 @ w)/(d2 @ d2)
        g[j] = math.log(np.linalg.norm(w))
    return float(np.mean(g))/Tdr
def modal_radius(U, ctr, pvv):
    Z = np.array([np.vdot(pvv, U[j] - ctr) for j in range(K)])
    th = 2*math.pi*np.arange(K)/K
    return abs(np.mean(Z*np.exp(-1j*th)))
def fixpt(x0, a, strobe):
    x = x0.copy()
    for it in range(25):
        xT, M = strobe(x, a)
        R = xT - x
        if np.max(np.abs(R)) < 1e-11: return x
        dx = np.linalg.solve(M - np.eye(4), -R)
        n2 = np.linalg.norm(dx)
        if n2 > 0.5: dx *= 0.5/n2
        x = x + dx
    return x

out("(B) direct test of c_x on the V cell (alpha=0.10, r=0.9): "
    "lambda_u and guard radius against alpha_eff = alpha - Re c_x a^2")
prm_at, Tdr, strobeV = mk_cell(pr, st, rg, wp, 'V')
x0c, Tc = guard_cycle(pr, st, rg, qv, pv, w0, c1v)
s0 = solve_ivp(lambda t, x: rhs_w(x, pr), (0, Tc), x0c, method='DOP853',
               rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
U = s0.y.T.copy(); rho = 2*math.pi*((Tdr/Tc) % 1.0)
U, rho, ok = tn(U, rho, 0.0, strobeV, rg)
out(f"    a=0: guard modal radius {modal_radius(U, st, pv)/rg:.5f} r_g, "
    f"lambda_u {lam_ring(U, rho, 0.0, strobeV, Tdr):.6f} (2 alpha="
    f"{2*alpha:.4f})  [{time.time()-T0:.0f}s]")
out("    eps/eps_c |  lam_u meas   2(alpha-Rec_x eps^2/4)  err    | "
    "rho_g meas/pred")
cur = 0.0
for fr in (0.30, 0.50, 0.70, 0.85, 1.00):
    tgt = fr*epred; okc = True
    while cur < tgt - 1e-15:
        stp = min(0.05*epred, tgt-cur)
        for _t in range(4):
            Un, rn, okn = tn(U.copy(), rho, cur+stp, strobeV, rg)
            if okn: break
            stp *= 0.5
        if not okn:
            okc = False; break
        U, rho, cur = Un, rn, cur+stp
    if not okc:
        out(f"    {fr:.2f} | continuation failed"); break
    lu = lam_ring(U, rho, cur, strobeV, Tdr)
    aeff = alpha - cx.real*cur**2/4
    xa = fixpt(st, cur, strobeV)
    rmeas = modal_radius(U, xa, pv)
    rpred = math.sqrt(max(aeff, 0)/c1v.real)
    out(f"    {fr:8.2f} | {lu:.6f}    {2*aeff:.6f}          "
        f"{(2*aeff-lu)/lu*100:+6.2f}%  | {rmeas/rg:.4f}/{rpred/rg:.4f} "
        f"({(rpred-rmeas)/rmeas*100:+.2f}%)  [{time.time()-T0:.0f}s]")

# ============ (C) omega_g slow cell diagnostics ============
pr3 = dict(pr, dw=0.0)
phi = 0.5*(math.sqrt(5.0) - 1.0)
x0c3, Tc3 = guard_cycle(pr3, st, rg, qv, pv, w0, c1v)
Td3 = (8.0 + phi)*Tc3
ws = 2*math.pi/Td3
fdw = -np.eye(4)[0]
cx3, H3, parts = cross_sat(pr3, co, fdw, ws, split=True)
out(f"(C) omega_g cell, w_s={ws:.5f}: Re c_x = {cx3.real:+.6e}")
nm = ('C(q,H,Hbar)', 'B(H,g_-)', 'B(Hbar,g_+)', 'B(q,d0)')
for n_, t_ in zip(nm, parts):
    out(f"      {n_:14s} Re = {t_.real:+.6e}")
out(f"      |<p,H>| = {abs(np.vdot(pv, H3)):.6e}, |H| = "
    f"{np.linalg.norm(H3):.4e}, r_g = {rg:.4e}")
prm_at3, Tdr3, strobeW = mk_cell(pr3, st, rg, ws, 'dw')
s3 = solve_ivp(lambda t, x: rhs_w(x, pr3), (0, Tc3), x0c3, method='DOP853',
               rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc3/K)
U3 = s3.y.T.copy(); rho3 = 2*math.pi*((Tdr3/Tc3) % 1.0)
U3, rho3, ok3 = tn(U3, rho3, 0.0, strobeW, rg)
out(f"    a=0: guard modal radius {modal_radius(U3, st, pv)/rg:.5f} r_g "
    f"(Newton {'ok' if ok3 else 'FAIL'})")
out("     a      |Z(0)|/r_g | rho_g meas/r_g   rho_g pred/r_g  lam_u meas "
    "   2 alpha_eff")
cur3 = 0.0
AC = 0.9427837
for fr in (0.30, 0.60, 0.85, 1.00):
    tgt = fr*AC; okc = True
    while cur3 < tgt - 1e-12:
        stp = min(0.05*AC, tgt-cur3)
        for _t in range(4):
            Un, rn, okn = tn(U3.copy(), rho3, cur3+stp, strobeW, rg)
            if okn: break
            stp *= 0.5
        if not okn:
            okc = False; break
        U3, rho3, cur3 = Un, rn, cur3+stp
    if not okc:
        out(f"    {fr:.2f} | continuation failed at {cur3/AC:.3f}"); break
    xa3 = fixpt(st, cur3, strobeW)
    rmeas = modal_radius(U3, xa3, pv)
    aeff3 = alpha - cx3.real*(cur3/2)**2
    rpred = math.sqrt(max(aeff3, 0)/c1v.real)
    lu3 = lam_ring(U3, rho3, cur3, strobeW, Tdr3)
    z0 = abs(np.vdot(pv, xa3 - st))
    out(f"    {cur3:.4f}   {z0/rg:8.4f}  | {rmeas/rg:11.4f}   "
        f"{rpred/rg:11.4f}    {lu3:.6f}   {2*aeff3:.6f}  "
        f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
