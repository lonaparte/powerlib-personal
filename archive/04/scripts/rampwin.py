"""Is the ramped-threshold gap real, or the observation window again?

pccobs measured the slowly-raised threshold 20-33% above the closed-form
branch eps = 2 sqrt(alpha / Re c_x).  That branch is defined by the guard
vanishing (alpha_eff = 0), and exactly there the escape rate 2|alpha_eff|
vanishes too -- so the finite hold time after the ramp biases the
measurement upward by construction, the same systematic that made the
400-period threshold 2.7% high on idx17.  Measured here with the hold
lengthened 1 -> 4 -> 16 x to see whether it converges onto the branch.
Set: G1, V channel, r = 0.9, ramp over 300 drive periods.
Budget ~15 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/rampwin.log', 'w')
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
st = co['st']; w0 = co['w0']; alpha = co['alpha']; lam = co['lam']
pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr); rg = math.sqrt(alpha/c1.real)
dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
wp = 0.9*w0; Td = 2*math.pi/wp
hs = 1e-6
fV = (rhs(st, dict(pr, V=pr['V']+hs)) - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
cx = cx_hand(A, st, pr, qv, pv, w0, wp, fV)
epred = 2*math.sqrt(alpha/cx.real)
out(f"G1: closed-form ramped branch 2 sqrt(alpha/Re c_x) = {epred:.6e}")
def run(eps, ramp, hold):
    def f(t, x):
        e = eps*min(1.0, t/(ramp*Td))
        return rhs(x, dict(pr, V=pr['V'] + e*math.cos(wp*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, (ramp+hold)*Td), st.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0
for hold in (400, 1600, 6400):
    lo, hi = 0.8*epred, 2.0*epred
    n = 0
    while not run(hi, 300, hold) and n < 8:
        lo = hi; hi *= 1.25; n += 1
    n = 0
    while run(lo, 300, hold) and n < 8:
        hi = lo; lo *= 0.85; n += 1
    for _ in range(14):
        m = 0.5*(lo+hi)
        if run(m, 300, hold): hi = m
        else: lo = m
    e = 0.5*(lo+hi)
    out(f"  hold {hold:5d} periods: threshold {e:.6e}  "
        f"{(e-epred)/epred*100:+.2f}% vs the branch  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
