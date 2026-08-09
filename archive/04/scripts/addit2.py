"""Additivity, done right, and split by protocol.

addit gave the two single-channel cases correctly (+0.31%, +0.19%) but
its mixed-channel predictions were meaningless: the scale bisection was
capped at 1.0 while the true predicted scale is larger than 1, so every
mix reported "predicted 1.000000".  The cap is removed here.

The reason the mixed threshold sits ABOVE both single-channel ones is
visible in the coefficients: the two switch-on kicks come out at -137.0
and +62.0 degrees, i.e. 199 degrees apart -- nearly anti-phase -- so with
both drives applied as cosines starting at their peak the kicks largely
CANCEL and more drive is needed.  That makes the sudden-onset threshold
depend on the relative phase of the disturbances, which is exactly the
information one does not have when everything is only observed.

But the kick exists only for sudden onset.  For a slowly growing
disturbance there is no kick and the threshold is set by the erosion
alone, which is a scalar sum over channels:

    sum_i Re c_x^(i) |a_i|^2 = alpha      ->    attribution-free

Both protocols are tested here against the same measurements.
Set: G1 margin 0.10, V channel at r = 0.90 and P channel at r = 0.62.
Budget ~25 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/addit2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"), 'm4', 'exec'), _ns)
cx_hand = _ns['cx_hand']; hopf = _ns['hopf']
prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr)
dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
hs = 1e-6
fV = (rhs(st, dict(pr, V=pr['V']+hs)) - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
fP = (rhs(st, dict(pr, P=pr['P']+hs)) - rhs(st, dict(pr, P=pr['P']-hs)))/(2*hs)
CH = {'V': (fV, 0.90*w0), 'P': (fP, 0.62*w0)}
info = {}
for k, (fu, wp) in CH.items():
    cx = cx_hand(A, st, pr, qv, pv, w0, wp, fu)
    Hk = np.linalg.solve(1j*wp*np.eye(4) - A, fu.astype(complex))
    kick1 = -(0.5*np.vdot(pv, Hk) + 0.5*np.vdot(pv, np.conj(Hk)))
    info[k] = dict(cx=cx.real, kick=kick1, wp=wp)
    out(f"channel {k}: Re c_x={cx.real:.6e}  kick/eps={abs(kick1):.5f} "
        f"@ {math.degrees(np.angle(kick1)):+.2f} deg")
out(f"kick phase difference V-P = "
    f"{math.degrees(np.angle(info['V']['kick']/info['P']['kick'])):+.2f} deg")
wV = info['V']['wp']; wP = info['P']['wp']
Tref = 2*math.pi/min(wV, wP)
def gap_sudden(eV, eP):
    aeff = alpha - info['V']['cx']*(0.5*eV)**2 - info['P']['cx']*(0.5*eP)**2
    if aeff <= 0:
        return 1.0
    z0 = eV*info['V']['kick'] + eP*info['P']['kick']
    return abs(z0) - math.sqrt(aeff/c1.real)
def pred_sudden(rv, rp):
    lo, hi = 1e-12, 1.0
    n = 0
    while gap_sudden(hi*rv, hi*rp) <= 0 and n < 60:
        lo = hi; hi *= 1.5; n += 1
    for _ in range(200):
        m = 0.5*(lo+hi)
        if gap_sudden(m*rv, m*rp) > 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)
def pred_ramp(rv, rp):
    den = info['V']['cx']*(0.5*rv)**2 + info['P']['cx']*(0.5*rp)**2
    return math.sqrt(alpha/den)
def run(eV, eP, NP, ramp=0):
    def f(t, x):
        s = min(1.0, t/(ramp*Tref)) if ramp > 0 else 1.0
        return rhs(x, dict(pr, V=pr['V'] + s*eV*math.cos(wV*t),
                           P=pr['P'] + s*eP*math.cos(wP*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, (NP+ramp)*Tref), st.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0
def meas(rv, rp, NP, ramp, seed):
    lo, hi = 0.5*seed, 1.6*seed
    n = 0
    while not run(hi*rv, hi*rp, NP, ramp) and n < 14:
        lo = hi; hi *= 1.3; n += 1
    n = 0
    while run(lo*rv, lo*rp, NP, ramp) and n < 14:
        hi = lo; lo *= 0.75; n += 1
    for _ in range(15):
        m = 0.5*(lo+hi)
        if run(m*rv, m*rp, NP, ramp): hi = m
        else: lo = m
    return 0.5*(lo+hi)
eV0 = pred_sudden(1.0, 0.0); eP0 = pred_sudden(0.0, 1.0)
out(f"single-channel sudden thresholds (closed form): V {eV0:.5e}, "
    f"P {eP0:.5e}")
out("A) sudden onset -- kick adds as a phasor")
out("   s   |  eps_V       eps_P      | predicted   measured    err")
for s in (1.0, 0.75, 0.5, 0.25, 0.0):
    rv, rp = s*eV0, (1.0-s)*eP0
    kp = pred_sudden(rv, rp)
    km = meas(rv, rp, 600, 0, kp)
    out(f"  {s:.2f}  | {km*rv:.5e} {km*rp:.5e} | {kp:.6f}   {km:.6f}   "
        f"{(kp-km)/km*100:+6.2f}%  [{time.time()-T0:.0f}s]")
out("B) slowly raised -- no kick, erosion adds as a scalar sum")
out("   s   |  eps_V       eps_P      | predicted   measured    err   hold")
for s, hold in ((1.0, 1600), (0.5, 1600), (0.0, 1600), (0.5, 4800)):
    rv, rp = s*eV0, (1.0-s)*eP0
    kp = pred_ramp(rv, rp)
    km = meas(rv, rp, hold, 200, kp)
    out(f"  {s:.2f}  | {km*rv:.5e} {km*rp:.5e} | {kp:.6f}   {km:.6f}   "
        f"{(kp-km)/km*100:+6.2f}%  {hold}  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
