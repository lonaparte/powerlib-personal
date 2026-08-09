"""Is the critical PCC swing a usable indicator, or only a coincidence at
one drive frequency?

The PCC quantities are observations, not inputs, so any criterion written
in them has to hold without knowing what drove the disturbance.  pccmap
showed the critical PCC state is nearly channel-independent (V, P, Q all
give 0.53-0.55% voltage swing at their own thresholds) -- but only at
r = w_p/w0 = 0.9.  Across frequency two things move in opposite
directions: eps_c collapses near resonance (the campaign measured
eps_c(r=1) = 2.2e-6, fifty times below the r=0.9 value) while the PCC
response per unit eps grows.  Whether they cancel decides whether
"PCC voltage swing > X%" is a frequency-blind indicator or has to be
read together with the observed frequency.

Measured here for G1 (angle family, margin 0.10): the sudden-onset
threshold and the PCC observable swings at 0.9 eps_c, for
r = 0.6 / 0.75 / 0.9 / 1.0 / 1.15 on the V channel, plus the P and Q
channels at r = 0.6 and 1.0 to see whether channel-independence survives
away from the frequency where it was found.
NOTE on protocol: the swing must be read on the SETTLED forced orbit.
A first pass sampled 200 drive periods after a sudden switch-on and came
out 27% high at r = 0.9 (0.697% against pccobs's 0.547%): near threshold
the free mode decays at alpha_eff ~ 0.47 alpha, a 99-period time
constant, so 200 periods still carries 13% of the switch-on kick and its
beat against the forced line inflates max-min.  Fixed by raising the
drive over 200 periods (no kick) and settling another 400 before
sampling.  The threshold itself is still measured with sudden onset.
Budget ~25 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/pccrobust.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def obs(x, prq):
    th, xp, Vdc, xi = x
    idq = prq['kpv']*(1 - Vdc) + prq['kiv']*xi
    iq = prq['Q']
    vd = prq['V']*math.cos(th) - prq['Xg']*iq
    vq = -prq['V']*math.sin(th) + prq['Xg']*idq
    return dict(Vm=math.hypot(vd, vq),
                P=1.5*(vd*idq + vq*iq), Q=1.5*(vq*idq - vd*iq),
                Im=math.hypot(idq, iq),
                f=(prq['kp']*vq + prq['ki']*xp)/(2*math.pi))
KEYS = ('Vm', 'P', 'Im', 'f')

prb = gset('G1')
Psn = 3*prb['V']**2/(4*prb['Xg'])
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
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
o0 = obs(st, pr)
out(f"G1 margin 0.10: P0={P0:.5f}, w0={w0:.3f} rad/s ({w0/(2*math.pi):.2f} Hz)")
out(f"  steady PCC: |v|={o0['Vm']:.5f} P={o0['P']:.5f} |i|={o0['Im']:.5f}")
out("  chan   r     eps_c        |  PCC swing at 0.9 eps_c: |v|      P       "
    " |i|      f [Hz]")

def drive(prq, chan, eps, t, wp):
    d = dict(prq)
    if chan == 'V':
        d['V'] = prq['V'] + eps*math.cos(wp*t)
    elif chan == 'P':
        d['P'] = prq['P'] + eps*math.cos(wp*t)
    else:
        d['Q'] = prq['Q'] + eps*math.cos(wp*t)
    return d
def run(chan, eps, wp, NP, ramp=0):
    Td = 2*math.pi/wp
    def f(t, x):
        e = eps*min(1.0, t/(ramp*Td)) if ramp > 0 else eps
        return rhs(x, drive(pr, chan, e, t, wp))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, (NP+ramp)*Td), st.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi),
                  dense_output=True)
    return (any(len(t) > 0 for t in s.t_events) or s.status < 0), s
def thr(chan, wp, seed):
    lo2, hi2 = 0.3*seed, 2.0*seed
    n = 0
    while not run(chan, hi2, wp, 400)[0] and n < 22:
        lo2 = hi2; hi2 *= 1.5; n += 1
    n = 0
    while run(chan, lo2, wp, 400)[0] and n < 22:
        hi2 = lo2; lo2 *= 0.5; n += 1
    if run(chan, lo2, wp, 400)[0] or not run(chan, hi2, wp, 400)[0]:
        return float('nan')
    for _ in range(16):
        m = 0.5*(lo2+hi2)
        if run(chan, m, wp, 400)[0]: hi2 = m
        else: lo2 = m
    return 0.5*(lo2+hi2)
CASES = [('V', 0.60), ('V', 0.75), ('V', 0.90), ('V', 1.00), ('V', 1.15),
         ('P', 0.60), ('P', 1.00), ('Q', 0.60), ('Q', 1.00)]
seeds = {'V': 1.2e-4, 'P': 2.8e-4, 'Q': 3.0e-4}
for chan, r in CASES:
    wp = r*w0; Td = 2*math.pi/wp
    ec = thr(chan, wp, seeds[chan])
    if not (ec == ec):
        out(f"  {chan}   {r:.2f}  bracket failed"); continue
    esc, s = run(chan, 0.9*ec, wp, 400, ramp=200)
    tt = np.linspace(s.t[-1]-40*Td, s.t[-1], 4000)
    Y = s.sol(tt)
    rec = {k: [] for k in KEYS}
    for i in range(len(tt)):
        o = obs(Y[:, i], drive(pr, chan, 0.9*ec, tt[i], wp))
        for k in KEYS:
            rec[k].append(o[k])
    sw = {k: 0.5*(np.max(rec[k])-np.min(rec[k])) for k in KEYS}
    out(f"  {chan}   {r:.2f}  {ec:.4e}  |  "
        f"{sw['Vm']/o0['Vm']*100:6.3f}%  {sw['P']/abs(o0['P'])*100:6.3f}%  "
        f"{sw['Im']/o0['Im']*100:6.3f}%  {sw['f']:8.4f}   "
        f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
