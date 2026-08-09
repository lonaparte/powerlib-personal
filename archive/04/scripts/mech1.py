"""Replace the measured constants by a derived coefficient.

What is still a number rather than a mechanism after the last round:
  * the constant 1.545 = eps_est/eps_c (five margins, +-0.2%),
  * the exponent 0.4867 in eps_c ~ alpha^0.4867,
  * the -12 to -14% of the single-mode reduction,
  * lambda_u itself (computed from a cocycle, not from a formula),
  * the omega_g slow-band threshold (measured only).
All five collapse onto ONE derived quantity if the reduction is done with
two carriers instead of one.

DERIVATION (slowly varying amplitude, two carriers).
Write the state as a free-mode carrier at w0 plus a drive carrier at w_p:
    y = 2Re(Z q e^{i w0 t}) + 2Re(a H e^{i w_p t}) + O(2),
    H = (i w_p I - A)^{-1} f_u ,   a = (complex drive amplitude)/2 .
The quadratic term feeds three second-order channels that the one-mode
reduction does not have -- sum frequency, difference frequency and DC:
    g_+ = (i(w0+w_p) I - A)^{-1} B(q, H)
    g_- = (i(w0-w_p) I - A)^{-1} B(q, Hbar)
    d0hat = -A^{-1} B(H, Hbar)
and at third order they return to w0, together with the direct cubic
C(q,H,Hbar), as a CROSS-SATURATION term:
    Zdot = lam Z + c1 |Z|^2 Z + c_x |a|^2 Z ,
    c_x = <p,C(q,H,Hbar)> + <p,B(H,g_-)> + <p,B(Hbar,g_+)> + <p,B(q,d0hat)>.
Setting H = q and w_p = w0 gives c_x = g21 = 2 c1 exactly, which is the
one-mode assumption; that identity is checked numerically below.

CONSEQUENCES (all closed form, no fitted constant):
  guard radius under drive     rho_g^2 = r_g^2 - (Re c_x/Re c1)|a|^2
  switch-on kick of the free mode
                               Z(0) = -(a <p,H> + abar <p,Hbar>)
  escape iff |Z(0)| > rho_g, hence for a cosine drive of amplitude eps
                               eps_c = r_g / sqrt(J^2 + Re c_x/(4 Re c1)),
                               J = |lam| |<p,f_u>| / |w_p^2 + lam^2|
  transverse exponent at the threshold
                               lambda_u = 2 alpha /(1 + X),
                               X = Re c_x /(4 Re c1 J^2)
  one-mode limit               eps_est/eps_c -> sqrt(3),  zeta = 2|lam|/|lam+i w_p|
  slow band, sine switch-on    |Z(0)| ~ w_p/|lam| -> 0, so the threshold is
                               where the guard itself vanishes:
                               Re c_x |a|^2 = alpha
Everything is evaluated from A, B, C, p, q at the operating point.

TESTED HERE
  (1) the identity c_x = 2 c1 at H=q, w_p=w0 (self-check of the algebra);
  (2) V channel, r=0.9, four margins: eps_c predicted vs measured, and the
      predicted ratio eps_est/eps_c against the observed constant 1.545;
  (3) the alpha exponent from the formula vs the measured 0.4867;
  (4) idx17 (r=0.92): eps_c AND lambda_u(eps_c) from the same c_x;
  (5) omega_g slow cell (sine switch-on): a_c from the vanishing-guard
      branch of the same formula.
Budget ~25 min, progress lines.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/mech1.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def rhs_w(x, prm):
    y = rhs(x, prm).copy(); y[0] -= prm.get('dw', 0.0); return y

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

def cross_sat(pr, co, fu, wp):
    """c_x, H, and the auxiliary second-order responses."""
    st = co['st']; qv = co['q']; pv = co['p']; w0 = co['w0']
    A = jac(st, pr)
    B2, C3 = tensors(pr, st)
    I = np.eye(4)
    H = np.linalg.solve(1j*wp*I - A, fu.astype(complex))
    Hc = np.conj(H)
    gp = np.linalg.solve(1j*(w0+wp)*I - A, B2(qv, H))
    gm = np.linalg.solve(1j*(w0-wp)*I - A, B2(qv, Hc))
    d0 = -np.linalg.solve(A, B2(H, Hc))
    cx = (np.vdot(pv, C3(qv, H, Hc)) + np.vdot(pv, B2(H, gm))
          + np.vdot(pv, B2(Hc, gp)) + np.vdot(pv, B2(qv, d0)))
    return cx, H

# ---------------- (1) algebra self-check: c_x = 2 c1 ----------------
prb = gset('G1'); Psn = 3*prb['V']**2/(4*prb['Xg'])
def reA(P, base):
    q = dict(base, P=P); x = equil(q)
    if x is None: return None
    cm = crit_mode(jac(x, q))
    return None if cm is None else cm.real
def hopf(base):
    Ps = 3*base['V']**2/(4*base['Xg'])
    grid = np.linspace(0.05, 0.985, 60)*Ps
    va = [reA(P, base) for P in grid]; br = None
    for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
        if fa is not None and fb is not None and fa < 0 <= fb:
            br = (a, b); break
    lo, hi = br
    for _ in range(45):
        m = 0.5*(lo+hi); v = reA(m, base)
        if v is None or v >= 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)
PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0)
co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; qv = co['q']; pv = co['p']; c1v = co['c1']
A = jac(st, pr)
B2, C3 = tensors(pr, st)
I = np.eye(4)
# c_x with H replaced by q and w_p by w0 must reproduce g21 = 2 c1
gp0 = np.linalg.solve(2j*w0*I - A, B2(qv, qv))
gm0 = -np.linalg.solve(A, B2(qv, np.conj(qv)))
cx0 = (np.vdot(pv, C3(qv, qv, np.conj(qv))) + np.vdot(pv, B2(qv, gm0))
       + np.vdot(pv, B2(np.conj(qv), gp0))
       + np.vdot(pv, B2(qv, -np.linalg.solve(A, B2(qv, np.conj(qv))))))
out(f"(1) algebra self-check at H=q, w_p=w0:  c_x = {cx0:.6e}")
out(f"    2 c1                                 = {2*c1v:.6e}   "
    f"relative difference {abs(cx0-2*c1v)/abs(2*c1v):.2e}")

# ---------------- (2)(3) V channel, four margins ----------------
out("(2) V channel, r = 0.9, cosine switch-on")
out(" alpha |  X=Rec_x/(4Rec1 J^2)  zeta   eps_c(pred)   eps_c(meas)  err "
    "  | eps_est/eps_c pred / meas")
rows = []
for marg in (0.05, 0.10, 0.15, 0.20):
    P0 = margin_point(prb, PH, marg)
    pr = dict(prb, P=P0)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; alpha = co['alpha']
    c1v = co['c1']; lam = co['lam']; pv = co['p']
    rg = math.sqrt(alpha/c1v.real)
    dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
    wp = 0.9*w0; Td = 2*math.pi/wp
    hh = 1e-6
    fV = (rhs(st, dict(pr, V=pr['V']+hh))
          - rhs(st, dict(pr, V=pr['V']-hh)))/(2*hh)
    F = np.vdot(pv, fV)
    cx, H = cross_sat(pr, co, fV, wp)
    J = abs(lam)*abs(F)/abs(wp**2 + lam**2)
    X = cx.real/(4*c1v.real*J**2)
    zeta = 2*abs(lam)/abs(lam + 1j*wp)
    epred = rg/math.sqrt(J**2 + cx.real/(4*c1v.real))
    eest = 2*rg*abs(lam - 1j*wp)/abs(F)
    def probe(eps, NPn=1000):
        def f(t, x):
            return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
        def e_th(t, x): return abs(x[0] - st[0]) - dsad
        def e_vlo(t, x): return x[2] - 0.20*Vdc0
        def e_vhi(t, x): return x[2] - 2.50*Vdc0
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
        return (any(len(s.t_events[i]) > 0 for i in range(3))
                or s.status < 0)
    elo, ehi = 0.5*epred, 1.5*epred
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
    rows.append((alpha, epred, emeas))
    out(f" {marg:.2f} |  {X:8.4f}   {zeta:.5f}  {epred:.5e}  {emeas:.5e} "
        f"{(epred-emeas)/emeas*100:+7.2f}%  | {zeta*math.sqrt(1+X):.4f} / "
        f"{eest/emeas:.4f}   [{time.time()-T0:.0f}s]")
if len(rows) >= 2:
    a0, p0, m0 = rows[0]; a1, p1, m1 = rows[-1]
    out(f"(3) alpha exponent  d ln eps_c / d ln alpha : "
        f"predicted {math.log(p1/p0)/math.log(a1/a0):.4f}, "
        f"measured {math.log(m1/m0)/math.log(a1/a0):.4f}")

# ---------------- (4) idx17: threshold and lambda_u ----------------
over = dict(kp=55., ki=1200., Xg=0.40)
prb2 = gset('G1', **over)
PH2 = hopf(prb2)
P02 = margin_point(prb2, PH2, 0.08)
pr2 = dict(prb2, P=P02)
co2 = nf_coeffs(pr2)
st2 = co2['st']; w02 = co2['w0']; alpha2 = co2['alpha']
c12 = co2['c1']; lam2 = co2['lam']; pv2 = co2['p']
rg2 = math.sqrt(alpha2/c12.real)
dsad2 = math.pi - 2*abs(st2[0]); Vdc02 = st2[2]
wp2 = 0.92*w02; Td2 = 2*math.pi/wp2
hh = 1e-6
fV2 = (rhs(st2, dict(pr2, V=pr2['V']+hh))
       - rhs(st2, dict(pr2, V=pr2['V']-hh)))/(2*hh)
F2 = np.vdot(pv2, fV2)
cx2, H2 = cross_sat(pr2, co2, fV2, wp2)
J2 = abs(lam2)*abs(F2)/abs(wp2**2 + lam2**2)
X2 = cx2.real/(4*c12.real*J2**2)
epred2 = rg2/math.sqrt(J2**2 + cx2.real/(4*c12.real))
lupred = 2*alpha2/(1 + X2)
def esc2(eps, NP):
    def f(t, x):
        return rhs(x, dict(pr2, V=pr2['V'] + eps*math.cos(wp2*t)))
    def e_th(t, x): return abs(x[0] - st2[0]) - dsad2
    def e_vlo(t, x): return x[2] - 0.20*Vdc02
    def e_vhi(t, x): return x[2] - 2.50*Vdc02
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NP*Td2), st2.copy(), method='DOP853',
                  rtol=1e-11, atol=1e-14, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0
elo, ehi = 0.5*epred2, 1.5*epred2
n = 0
while not esc2(ehi, 400) and n < 12:
    elo = ehi; ehi *= 1.4; n += 1
n = 0
while esc2(elo, 400) and n < 12:
    ehi = elo; elo *= 0.6; n += 1
for _ in range(14):
    em = 0.5*(elo+ehi)
    if esc2(em, 400): ehi = em
    else: elo = em
e4 = 0.5*(elo+ehi)
elo, ehi = 0.95*e4, e4
for _ in range(20):
    em = 0.5*(elo+ehi)
    if esc2(em, 4000): ehi = em
    else: elo = em
emeas2 = 0.5*(elo+ehi)
out(f"(4) idx17 (r=0.92): X={X2:.4f}  eps_c pred {epred2:.6e} vs meas "
    f"{emeas2:.6e}  err {(epred2-emeas2)/emeas2*100:+.2f}%")
out(f"    lambda_u(eps_c) pred 2 alpha/(1+X) = {lupred:.6f} /s "
    f"-> 1/(lambda_u T_d) = {1.0/(lupred*Td2):.2f} periods  "
    f"[{time.time()-T0:.0f}s]")

# ---------------- (5) omega_g slow cell, sine switch-on ----------------
P03 = margin_point(prb, PH, 0.10)
pr3 = dict(prb, P=P03, dw=0.0)
co3 = nf_coeffs(pr3)
st3 = co3['st']; w03 = co3['w0']; alpha3 = co3['alpha']
c13 = co3['c1']; lam3 = co3['lam']; pv3 = co3['p']; qv3 = co3['q']
rg3 = math.sqrt(alpha3/c13.real)
dsad3 = math.pi - 2*abs(st3[0]); Vdc03 = st3[2]
def flow3(x0, T):
    s = solve_ivp(lambda t, y: rhs_w(y, pr3), (0, T), x0,
                  method='DOP853', rtol=1e-12, atol=1e-14)
    return s.y[:, -1]
xs = st3 + 2*np.real(rg3*qv3)
xg, Tc3 = xs.copy(), 2*math.pi/(w03 + c13.imag*rg3**2)
for it in range(40):
    def fv(t, y):
        x = y[:4]
        Jm = np.array([[0.0]*4 for _ in range(4)])
        return np.concatenate([rhs_w(x, pr3), np.zeros(16)])
    break
# guard cycle period only needed for the drive frequency; use the
# normal-form value (the drive frequency definition itself)
phi = 0.5*(math.sqrt(5.0) - 1.0)
Tc_nf = 2*math.pi/(w03 + c13.imag*rg3**2)
Td3 = (8.0 + phi)*Tc_nf
ws = 2*math.pi/Td3
fdw = -np.eye(4)[0]
cx3, H3 = cross_sat(pr3, co3, fdw, ws)
F3 = np.vdot(pv3, fdw)
# sine switch-on: complex drive amplitude Atil = -i a  ->  aa = -i a/2
def predict_sine(a):
    aa = -0.5j*a
    Z0 = -(aa*np.vdot(pv3, H3) + np.conj(aa)*np.vdot(pv3, np.conj(H3)))
    rho_g2 = rg3**2 - (cx3.real/c13.real)*abs(aa)**2
    return abs(Z0), rho_g2
alo, ahi = 1e-3, 20.0
for _ in range(60):
    am = 0.5*(alo+ahi)
    z0, rg2v = predict_sine(am)
    if rg2v <= 0 or z0**2 > rg2v: ahi = am
    else: alo = am
apred = 0.5*(alo+ahi)
z0c, rgc = predict_sine(apred)
avanish = 2*math.sqrt(alpha3/cx3.real) if cx3.real > 0 else float('nan')
def fate3(a, NP):
    def f(t, x):
        return rhs_w(x, dict(pr3, dw=a*math.sin(ws*t)))
    def e_th(t, x): return abs(x[0] - st3[0]) - dsad3
    def e_vlo(t, x): return x[2] - 0.20*Vdc03
    def e_vhi(t, x): return x[2] - 2.50*Vdc03
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NP*Td3), st3.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0
alo, ahi = 0.4, 1.6
for _ in range(18):
    am = 0.5*(alo+ahi)
    if fate3(am, 40): ahi = am
    else: alo = am
ameas = 0.5*(alo+ahi)
out(f"(5) omega_g slow cell, w_s = {ws:.5f} rad/s (w0/{w03/ws:.4f}), "
    f"sine switch-on")
out(f"    kick at threshold |Z(0)| = {z0c:.4e} = {z0c/rg3:.4f} r_g "
    f"(cosine drive would give {2*abs(lam3)/ws:.1f} times more)")
out(f"    a_c predicted {apred:.5f} vs measured {ameas:.5f}  "
    f"err {(apred-ameas)/ameas*100:+.2f}%")
out(f"    vanishing-guard branch a = 2 sqrt(alpha/Re c_x) = {avanish:.5f} "
    f"({(avanish-ameas)/ameas*100:+.2f}%)  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
