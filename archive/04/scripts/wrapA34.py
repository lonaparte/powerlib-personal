"""Two more wrap-ups: the GFM criticality sign, and observation-window bias.

A3 -- "GFM is generically supercritical" was asserted after gfmobs2, but
M4's measured decay-rate-versus-amplitude slope came out with the opposite
sign and was never reconciled.  The law is exact and has no free constant:
in the coordinate z = <p, x - x_eq> the reduced radial equation is
    rho' = -alpha rho + Re c1 rho^3 ,  so  D(rho) := -d ln rho/dt
                                             = alpha - Re c1 rho^2 ,
i.e. the slope of D against rho^2 is MINUS Re c1.  Negative slope means
Re c1 > 0 means SUBcritical.  So the check is a two-line consistency test
per cell: measure D(rho) by free decay from several launch amplitudes,
regress on rho^2, and compare intercept with alpha and slope with -Re c1
computed analytically from the Kuznetsov g21.  If M4's slope really is
negative and its analytic Re c1 really is positive, the generic claim is
false and gets retracted, not patched.

A4 -- observation-window bias.  A finite-window threshold is not the true
threshold: it is the drive level at which the escape time equals the
window.  On the V cell that bias was measured (+0.008%) and on idx17 it was
large (+2.73%), because escape time diverges logarithmically as the drive
approaches threshold and the divergence is set by lambda_u.  It was never
checked on the omega_g slow cell (whose reported a_c = 0.9427837 came from
a 40-period window) nor on any GFM cell.  Measured here by re-running each
threshold at doubling windows and reporting the drift; if the drift is
still falling geometrically the reported number is an upper bound and its
error bar is the last decrement.
Budget ~45 min.
"""
exec(open('selfhead.py').read())
import time
import gfmlib as G
LOG = open('sweep20/wrapA34.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']

# =====================================================================
# A3: GFM criticality, measured slope vs analytic -Re c1
# =====================================================================
out("=== A3: D(rho) = alpha - Re c1 rho^2 in the coordinate z = <p, x-x_eq>")
out(" cell | alpha (eig) | alpha (fit) | -Re c1 (analytic) | slope (fit) | "
    "verdict")
for nm in ('M1', 'M2', 'M3', 'M4', 'M5'):
    pr = G.mset(nm)
    st = G.equil(pr)
    if st is None:
        out(f" {nm}: no stable equilibrium"); continue
    A = G.jac(st, pr)
    lam = G.crit_mode(A)
    if lam is None:
        out(f" {nm}: no complex pair"); continue
    co = G.hopf_c1(pr)
    pvec = co['p']; qvec = co['q']
    alpha = -lam.real; w0 = lam.imag; Tc = 2*math.pi/w0
    c1r = co['c1'].real
    xs = G.equil(pr, branch='saddle')
    rmax = 0.35*abs(np.vdot(pvec, xs - st)) if xs is not None else 0.1
    rows = []
    for frac in (0.15, 0.30, 0.45, 0.60, 0.75):
        r0 = frac*rmax
        x0 = st + 2*np.real(r0*qvec)
        s = solve_ivp(lambda t, x: G.rhs(x, pr), (0, 6*Tc), x0,
                      method='DOP853', rtol=1e-12, atol=1e-15,
                      dense_output=True)
        ts = np.linspace(0.25*Tc, 3.25*Tc, 600)
        zz = np.array([abs(np.vdot(pvec, s.sol(t) - st)) for t in ts])
        if np.min(zz) <= 0 or not np.all(np.isfinite(zz)):
            continue
        g = np.log(zz)
        sl, ic = np.polyfit(ts, g, 1)
        rows.append((float(np.exp(np.polyval([sl, ic], ts.mean()))), -sl))
    if len(rows) < 3:
        out(f" {nm}: decay fit failed"); continue
    rr = np.array([r for r, _ in rows]); dd = np.array([d for _, d in rows])
    Mfit = np.vstack([np.ones_like(rr), rr**2]).T
    a_fit, s_fit = np.linalg.lstsq(Mfit, dd, rcond=None)[0]
    verdict = ('subcritical' if c1r > 0 else 'supercritical')
    agree = 'OK' if (s_fit < 0) == (c1r > 0) else 'MISMATCH'
    out(f" {nm}  | {alpha:11.6f} | {a_fit:11.6f} | {-c1r:+17.6e} | "
        f"{s_fit:+11.4e} | analytic {verdict}, sign {agree}  "
        f"[{time.time()-T0:.0f}s]")
    out(f"       w0={w0:.4f}  Re c1={c1r:+.6e}  launch radii "
        f"{rr.min():.3e}..{rr.max():.3e}  D range {dd.min():.5f}..{dd.max():.5f}")

# =====================================================================
# A4a: omega_g slow cell, window convergence
# =====================================================================
out("")
out("=== A4a: omega_g slow cell (drive on grid frequency), a_c vs window")


def rhs_w(x, prm):
    y = rhs(x, prm).copy(); y[0] -= prm.get('dw', 0.0); return y


prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
prw = dict(prb, P=P0, dw=0.0)
cow = nf_coeffs(prw)
stw = cow['st']; w0w = cow['w0']; alw = cow['alpha']
c1w = cow['c1']; qw = cow['q']; pw = cow['p']
rgw = math.sqrt(alw/c1w.real)
dsadw = math.pi - 2*abs(stw[0]); Vdc0w = stw[2]


def flow_w(x0, T, var=False):
    def f(t, y):
        return rhs_w(y, prw)
    s = solve_ivp(f, (0, T), x0, method='DOP853', rtol=1e-12, atol=1e-14)
    return s.y[:, -1]


def cyc_w(xs, Ts):
    x, T = xs.copy(), Ts
    fref = rhs_w(xs, prw)
    for _ in range(50):
        R = np.append(flow_w(x, T) - x, float(np.dot(fref, x - xs)))
        if np.max(np.abs(R)) < 1e-11:
            return x, T, True
        Jm = np.zeros((5, 5))
        z = np.append(x, T)
        for i in range(5):
            h = 1e-7*max(1e-4, abs(z[i]))
            zp = z.copy(); zp[i] += h
            Rp = np.append(flow_w(zp[:4], zp[4]) - zp[:4],
                           float(np.dot(fref, zp[:4] - xs)))
            Jm[:, i] = (Rp - R)/h
        dz = np.linalg.solve(Jm, -R)
        n2 = np.linalg.norm(dz[:4]); cap = max(0.01, 0.5*rgw)
        if n2 > cap: dz *= cap/n2
        if abs(dz[4]) > 0.1*T: dz *= 0.1*T/abs(dz[4])
        x = x + dz[:4]; T = T + dz[4]
    return x, T, False


Tc = None
for fac in (1.0, 0.85, 0.7, 1.2):
    xg = stw + 2*np.real(fac*rgw*qw)
    Tg = 2*math.pi/(w0w + c1w.imag*(fac*rgw)**2)
    xc, Tc_, ok = cyc_w(xg, Tg)
    if ok and abs(np.vdot(pw, xc - stw)) > 0.2*rgw:
        Tc = Tc_; break
if Tc is None:
    out("  guard cycle Newton failed; using 2pi/w0 as T_c")
    Tc = 2*math.pi/w0w
PHI = 0.5*(math.sqrt(5.0) - 1.0)
Tdw = (8.0 + PHI)*Tc
wsw = 2*math.pi/Tdw
out(f"  T_c={Tc:.6f}s  T_d={Tdw:.6f}s  w_s={wsw:.5f} rad/s  r_g={rgw:.5e}")


def fate_w(a, NP):
    def f(t, x):
        return rhs_w(x, dict(prw, dw=a*math.sin(wsw*t)))
    def e_th(t, x): return abs(x[0] - stw[0]) - dsadw
    def e_vlo(t, x): return x[2] - 0.20*Vdc0w
    def e_vhi(t, x): return x[2] - 2.50*Vdc0w
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NP*Tdw), stw.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0


prev = None
for NP in (40, 80, 160, 320, 640):
    alo, ahi = 0.4, 1.4
    for _ in range(19):
        am = 0.5*(alo+ahi)
        if fate_w(am, NP): ahi = am
        else: alo = am
    ac = 0.5*(alo+ahi)
    dr = "" if prev is None else f"  drift {(ac-prev)/prev*100:+.4f}%"
    out(f"  NP={NP:4d}  a_c = {ac:.7f}{dr}  [{time.time()-T0:.0f}s]")
    prev = ac

# =====================================================================
# A4b: idx17 GFL cell, window convergence
# =====================================================================
out("")
out("=== A4b: idx17 (kp=55 ki=1200 Xg=0.40), margin 0.08, r=0.92")
pb17 = gset('G1', kp=55., ki=1200., Xg=0.40)
PH17 = hopf(pb17)
P17 = margin_point(pb17, PH17, 0.08)
pr17 = dict(pb17, P=P17); co17 = nf_coeffs(pr17)
st17 = co17['st']; w017 = co17['w0']; al17 = co17['alpha']
rg17 = math.sqrt(al17/co17['c1'].real)
ds17 = math.pi - 2*abs(st17[0]); Vd17 = st17[2]
wp17 = 0.92*w017; Td17 = 2*math.pi/wp17
out(f"  alpha={al17:.5f} w0={w017:.4f} r_g={rg17:.5e}")


def fate17(eps, NP):
    def f(t, x):
        return rhs(x, dict(pr17, V=pr17['V'] + eps*math.cos(wp17*t)))
    def e_th(t, x): return abs(x[0] - st17[0]) - ds17
    def e_vlo(t, x): return x[2] - 0.20*Vd17
    def e_vhi(t, x): return x[2] - 2.50*Vd17
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NP*Td17), st17.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0


prev = None
for NP in (1000, 2000, 4000, 8000):
    elo, ehi = 3.0e-3, 1.5e-2
    n = 0
    while not fate17(ehi, NP) and n < 8:
        elo = ehi; ehi *= 1.3; n += 1
    for _ in range(17):
        em = 0.5*(elo+ehi)
        if fate17(em, NP): ehi = em
        else: elo = em
    ec = 0.5*(elo+ehi)
    dr = "" if prev is None else f"  drift {(ec-prev)/prev*100:+.4f}%"
    out(f"  NP={NP:5d}  eps_c = {ec:.7e}{dr}  [{time.time()-T0:.0f}s]")
    prev = ec

# =====================================================================
# A4c: GFM cells, window convergence
# =====================================================================
out("")
out("=== A4c: GFM cells M1/M2/M4, drive on V at r=0.9, eps_c vs window")
for nm in ('M1', 'M2', 'M4'):
    pr = G.mset(nm)
    st = G.equil(pr)
    lam = G.crit_mode(G.jac(st, pr))
    w0 = lam.imag; wp = 0.9*w0; Td = 2*math.pi/wp
    dlim = math.pi + 0.20

    def fateM(eps, NP):
        def f(t, x):
            return G.rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
        def ev(t, x): return x[0] - dlim
        ev.terminal = True; ev.direction = 1
        s = solve_ivp(f, (0, NP*Td), st.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=(ev,))
        return len(s.t_events[0]) > 0 or s.status < 0

    prev = None
    out(f"  {nm}: alpha={-lam.real:.5f} w0={w0:.4f}")
    for NP in (40, 80, 160, 320, 640):
        elo, ehi = 1e-4, 0.5
        n = 0
        while not fateM(ehi, NP) and n < 6:
            elo = ehi; ehi *= 1.4; n += 1
        if not fateM(ehi, NP):
            out(f"    NP={NP:4d}  no escape up to eps={ehi:.3e}")
            continue
        for _ in range(18):
            em = 0.5*(elo+ehi)
            if fateM(em, NP): ehi = em
            else: elo = em
        ec = 0.5*(elo+ehi)
        dr = "" if prev is None else f"  drift {(ec-prev)/prev*100:+.4f}%"
        out(f"    NP={NP:4d}  eps_c = {ec:.7e}{dr}  [{time.time()-T0:.0f}s]")
        prev = ec
out(f"DONE wall={time.time()-T0:.0f}s")
