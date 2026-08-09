"""Do independent disturbances add?

The step that decides whether the single-machine picture can be carried
to many machines and many measurement points is this: when several
channels fluctuate at once, does the closed form still hold with

    alpha_eff = alpha - sum_i Re c_x^(i) |a_i|^2        (erosion: scalar sum)
    Z(0)      = sum_i eps_i J_i e^{i psi_i}             (kick: phasor sum)

If it does, then "which source caused it" -- the question that cannot be
answered from observations anyway -- does not need to be answered: the
erosions simply add, and the margin follows without attribution.

Tested on G1 (margin 0.10) by driving the V channel at r = 0.90 and the
P channel at r = 0.62 simultaneously, with the amplitude ratio fixed so
both contribute comparably, and bisecting on a common scale.  Mixing
parameter s sets eps_V : eps_P = s*eV0 : (1-s)*eP0 with eV0, eP0 the
single-channel thresholds, so s = 1 and s = 0 recover the single-channel
cases and s = 0.5 is an even split.  Prediction versus measurement at
five mixes.  Both drives are cosines starting at their peak, so the
relative phase of the two kicks is fixed by the model, not chosen.
Budget ~20 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/addit.log', 'w')
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
lam = co['lam']; pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr); rg = math.sqrt(alpha/c1.real)
dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
hs = 1e-6
fV = (rhs(st, dict(pr, V=pr['V']+hs)) - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
fP = (rhs(st, dict(pr, P=pr['P']+hs)) - rhs(st, dict(pr, P=pr['P']-hs)))/(2*hs)
CH = {'V': (fV, 0.90*w0), 'P': (fP, 0.62*w0)}
info = {}
for k, (fu, wp) in CH.items():
    cx = cx_hand(A, st, pr, qv, pv, w0, wp, fu)
    Fk = np.vdot(pv, fu)
    Hk = np.linalg.solve(1j*wp*np.eye(4) - A, fu.astype(complex))
    Hb = np.conj(Hk)
    kick1 = -(0.5*np.vdot(pv, Hk) + 0.5*np.vdot(pv, Hb))   # per unit eps
    info[k] = dict(cx=cx.real, kick=kick1, wp=wp)
    out(f"channel {k}: w_p={wp:.4f} ({wp/w0:.2f} w0)  Re c_x={cx.real:.6e}  "
        f"kick/eps={abs(kick1):.5f} @ {math.degrees(np.angle(kick1)):+.2f} deg")
def predict(eV, eP):
    aeff = alpha - info['V']['cx']*(0.5*eV)**2 - info['P']['cx']*(0.5*eP)**2
    if aeff <= 0:
        return None
    z0 = eV*info['V']['kick'] + eP*info['P']['kick']
    return abs(z0) - math.sqrt(aeff/c1.real)
def run(eV, eP, NP=600):
    wV = info['V']['wp']; wP = info['P']['wp']
    Tref = 2*math.pi/min(wV, wP)
    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eV*math.cos(wV*t),
                           P=pr['P'] + eP*math.cos(wP*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NP*Tref), st.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0
def solve_pred(rv, rp):
    lo, hi = 1e-12, 1.0
    for _ in range(200):
        m = 0.5*(lo+hi); g = predict(m*rv, m*rp)
        if g is None or g > 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)
# single-channel references from the closed form, used only to set the mix
eV0 = solve_pred(1.0, 0.0); eP0 = solve_pred(0.0, 1.0)
out(f"single-channel closed-form thresholds: V {eV0:.5e}, P {eP0:.5e}")
out("   s    eps_V        eps_P        predicted k  measured k   err")
for s in (1.0, 0.75, 0.5, 0.25, 0.0):
    rv, rp = s*eV0, (1.0-s)*eP0
    if rv == 0 and rp == 0:
        continue
    kpred = solve_pred(rv, rp)
    lo, hi = 0.5*kpred, 1.6*kpred
    n = 0
    while not run(hi*rv, hi*rp) and n < 14:
        lo = hi; hi *= 1.3; n += 1
    n = 0
    while run(lo*rv, lo*rp) and n < 14:
        hi = lo; lo *= 0.75; n += 1
    for _ in range(16):
        m = 0.5*(lo+hi)
        if run(m*rv, m*rp): hi = m
        else: lo = m
    kmeas = 0.5*(lo+hi)
    out(f"  {s:.2f}  {kmeas*rv:.5e}  {kmeas*rp:.5e}  {kpred:.6f}     "
        f"{kmeas:.6f}    {(kpred-kmeas)/kmeas*100:+6.2f}%  "
        f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
