"""Can the margin be read off one raw signal, with no model and no modal
identification?

The radial normal form says the decay rate of the critical oscillation is
linear in the SQUARE of its amplitude,
    rate(rho) = alpha_eff - Re c1 rho^2 ,
so the intercept is the eroded damping and the zero crossing is the
guard.  Written in any raw observable g, with a_g = 2|Z||C_g q|,
    rate = alpha_eff - (Re c1/|2 C_g q|^2) a_g^2 ,
    a_g^crit = 2 |C_g q| rho_g ,
i.e. the mode-shape entry cancels out of both the slope and the zero
crossing.  If that holds, one bandpassed signal is enough: fit a line,
extrapolate to zero, divide the present swing by the crossing.

Tested by kicking the settled state along the critical direction and
reading the decay of the PCC VOLTAGE envelope from successive peaks --
no projection, no eigenvector, no model.  Done at zero drive and at
0.7 eps_c, where the line must shift down by exactly the erosion.
Reference values (which the fit must recover, not use): alpha,
alpha_eff = alpha - Re c_x eps^2/4, and the critical swing measured
independently.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/decayline.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"), 'm4', 'exec'), _ns)
cx_hand = _ns['cx_hand']; hopf = _ns['hopf']
prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
lam = co['lam']; pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr); rg = math.sqrt(alpha/c1.real)
wp = 0.90*w0; Td = 2*math.pi/wp
hs = 1e-6
fV = (rhs(st, dict(pr, V=pr['V']+hs)) - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
cx = cx_hand(A, st, pr, qv, pv, w0, wp, fV).real
J = abs(lam)*abs(np.vdot(pv, fV))/abs(wp**2 + lam**2)
lo, hi = 1e-14, 1.0
for _ in range(200):
    m = 0.5*(lo+hi); a2 = 0.25*m*m
    ae = alpha - cx*a2
    rv = math.sqrt(ae/c1.real) if ae > 0 else -1.0
    if rv < 0 or m*J > rv: hi = m
    else: lo = m
epsc = 0.5*(lo+hi)
def Vm(x, prq):
    th, xp, Vdc, xi = x
    idq = prq['kpv']*(1 - Vdc) + prq['kiv']*xi
    vd = prq['V']*math.cos(th) - prq['Xg']*prq['Q']
    vq = -prq['V']*math.sin(th) + prq['Xg']*idq
    return math.hypot(vd, vq)
out(f"G1 margin 0.10: alpha={alpha:.5f}, r_g={rg:.5e}, eps_c={epsc:.5e}")
for eps in (0.0, 0.7*epsc):
    ae_ref = alpha - cx*(0.5*eps)**2
    # settle on the forced orbit, then kick along the critical direction
    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
    if eps > 0:
        s0 = solve_ivp(f, (0, 200*Td), st.copy(), method='DOP853',
                       rtol=1e-11, atol=1e-14)
        base = s0.y[:, -1]; t0 = 200*Td
    else:
        base = st.copy(); t0 = 0.0
    rgs = math.sqrt(max(ae_ref, 1e-9)/c1.real)
    x0 = base + 2*np.real(0.92*rgs*qv)
    def f2(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*(t+t0))))
    NT = 260
    s = solve_ivp(f2, (0, NT*Td), x0, method='DOP853', rtol=1e-11,
                  atol=1e-14, dense_output=True)
    # reference: the settled forced orbit alone, to subtract
    sref = solve_ivp(f2, (0, NT*Td), base, method='DOP853', rtol=1e-11,
                     atol=1e-14, dense_output=True)
    tt = np.linspace(0, NT*Td, 40000)
    Y = s.sol(tt); Yr = sref.sol(tt)
    Vd = pr['V'] + eps*np.cos(wp*(tt+t0))
    def VmA(Yx):
        idq = pr['kpv']*(1 - Yx[2]) + pr['kiv']*Yx[3]
        vd = Vd*np.cos(Yx[0]) - pr['Xg']*pr['Q']
        vq = -Vd*np.sin(Yx[0]) + pr['Xg']*idq
        return np.hypot(vd, vq)
    dv = VmA(Y) - VmA(Yr)
    # envelope from successive local extrema of the raw difference signal
    d1 = np.diff(dv)
    idx = np.where(d1[:-1]*d1[1:] < 0)[0] + 1
    pk = [(tt[i], abs(dv[i])) for i in idx if abs(dv[i]) > 1e-9]
    amp, rate = [], []
    for i in range(0, len(pk)-2, 2):
        t1, a1 = pk[i]; t2, a2 = pk[i+2]
        if a1 <= 0 or a2 <= 0 or t2 <= t1:
            continue
        amp.append(0.5*(a1+a2)); rate.append(-math.log(a2/a1)/(t2-t1))
    amp = np.array(amp); rate = np.array(rate)
    m = (amp > 0.15*amp.max()) & (amp < 0.95*amp.max())
    if m.sum() < 6:
        out(f"  eps={eps:.4e}: too few envelope points"); continue
    Xf = np.vstack([amp[m]**2, np.ones(m.sum())]).T
    cf, *_ = np.linalg.lstsq(Xf, rate[m], rcond=None)
    slope, inter = cf
    acrit = math.sqrt(-inter/slope) if slope < 0 else float('nan')
    pred_crit = 2*rgs*abs(np.vdot(pv, fV)*0 + 1)  # placeholder, see below
    # independent reference for the critical swing: kick exactly at rho_g
    xg = base + 2*np.real(rgs*qv)
    sg = solve_ivp(f2, (0, 3*Td), xg, method='DOP853', rtol=1e-12, atol=1e-15,
                   dense_output=True)
    tg = np.linspace(0, 3*Td, 6000)
    Vg = pr['V'] + eps*np.cos(wp*(tg+t0))
    def VmB(Yx):
        idq = pr['kpv']*(1 - Yx[2]) + pr['kiv']*Yx[3]
        vd = Vg*np.cos(Yx[0]) - pr['Xg']*pr['Q']
        vq = -Vg*np.sin(Yx[0]) + pr['Xg']*idq
        return np.hypot(vd, vq)
    dg = VmB(sg.sol(tg)) - VmB(sref.sol(tg))
    ref_crit = 0.5*(dg.max()-dg.min())
    out(f"  eps={eps:.4e}: {m.sum()} envelope points, "
        f"fit rate = {inter:.6f} {slope:+.4e} a^2")
    out(f"     intercept {inter:.6f}  vs alpha_eff {ae_ref:.6f}  "
        f"({(inter-ae_ref)/ae_ref*100:+.2f}%)")
    out(f"     zero crossing {acrit:.5e}  vs the swing at rho_g "
        f"{ref_crit:.5e}  ({(acrit-ref_crit)/ref_crit*100:+.2f}%)")
out("DONE")
