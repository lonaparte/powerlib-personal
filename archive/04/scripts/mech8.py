"""Coverage check: the fifth-order closed form has only ever been run on
the V channel.

mech7 validated the full closed form (fifth order, additive + multiplicative
drive) to +0.01...+0.12% -- but every one of those five cells was the V
channel at r ~ 0.9.  The cubic version was checked across channels
(pccrobust), the fifth-order one never was.  Since the parametric
(multiplicative) part enters through d^2 f/dy du, and P and Q enter the
GFL only through the DC-link balance while V also appears in the network
algebra, there is no reason to assume the same accuracy carries over.

Run here: G1 margin 0.10, r = 0.90, channels V / P / Q, closed form with
and without the multiplicative channel, against the measured threshold.
"""
exec(open('selfhead.py').read())
import itertools, time
from math import factorial
LOG = open('sweep20/mech8.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_s7 = open('mech7.py').read().split(chr(10)+'CELLS = [')[0]
_ns = {}
exec(compile(_s7.replace("LOG = open('sweep20/mech7.log', 'w')",
                         "LOG = open('/dev/null','w')"), 'm7', 'exec'), _ns)
two_carrier_nf5 = _ns['two_carrier_nf5']; guard_root = _ns['guard_root']
hopf = _ns['hopf']; cx_hand = _ns['cx_hand']
prb = gset('G1'); PH = hopf(prb)
prH = dict(prb, P=PH); stH = equil(prH); coH = nf_coeffs(prH)
w0H = coH['w0']; wpH = 0.90*w0H; hs = 1e-6
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
lam = co['lam']; pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr); dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
wp = 0.90*w0; Td = 2*math.pi/wp
out(f"G1 margin 0.10, r=0.90: alpha={alpha:.5f}, Re c1={c1.real:.5e}")
out(" ch | measured      | 5th additive   | 5th add+param  | cubic add-only")
for k in ('V', 'P', 'Q'):
    fuH = (rhs(stH, dict(prH, **{k: prH[k]+hs}))
           - rhs(stH, dict(prH, **{k: prH[k]-hs})))/(2*hs)
    Rp = two_carrier_nf5(prH, wpH, fuH, param=True)
    Ra = two_carrier_nf5(prH, wpH, fuH, param=False)
    fu = (rhs(st, dict(pr, **{k: pr[k]+hs}))
          - rhs(st, dict(pr, **{k: pr[k]-hs})))/(2*hs)
    cx_add = cx_hand(A, st, pr, qv, pv, w0, wp, fu).real
    dcx = Rp['c_x'].real - Ra['c_x'].real
    J = abs(lam)*abs(np.vdot(pv, fu))/abs(wp**2 + lam**2)
    def thr(cxr, c2r, cxxr, ca4r):
        lo, hi = 1e-14, 1.0
        for _ in range(200):
            m = 0.5*(lo+hi); a2 = 0.25*m*m
            ae = alpha - cxr*a2 - ca4r*a2*a2
            rgv = guard_root(ae, c1.real + cxxr*a2, c2r)
            if not (rgv == rgv) or m*J > rgv: hi = m
            else: lo = m
        return 0.5*(lo+hi)
    e_add = thr(cx_add, Ra['c2'].real, Ra['c_xx'].real, Ra['c_a4'].real)
    e_par = thr(cx_add + dcx, Rp['c2'].real, Rp['c_xx'].real, Rp['c_a4'].real)
    e_cub = thr(cx_add, 0.0, 0.0, 0.0)
    def probe(eps):
        def f(t, x):
            return rhs(x, dict(pr, **{k: pr[k] + eps*math.cos(wp*t)}))
        def e_th(t, x): return abs(x[0] - st[0]) - dsad
        def e_vlo(t, x): return x[2] - 0.20*Vdc0
        def e_vhi(t, x): return x[2] - 2.50*Vdc0
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, 1000*Td), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
        return (any(len(s.t_events[i]) > 0 for i in range(3))
                or s.status < 0)
    elo, ehi = 0.6*e_par, 1.4*e_par
    n = 0
    while not probe(ehi) and n < 12:
        elo = ehi; ehi *= 1.3; n += 1
    n = 0
    while probe(elo) and n < 12:
        ehi = elo; elo *= 0.75; n += 1
    for _ in range(18):
        em = 0.5*(elo+ehi)
        if probe(em): ehi = em
        else: elo = em
    emeas = 0.5*(elo+ehi)
    def pc(x):
        return f"{(x-emeas)/emeas*100:+6.2f}%"
    out(f" {k}  | {emeas:.6e} | {e_add:.6e} {pc(e_add)} | "
        f"{e_par:.6e} {pc(e_par)} | {e_cub:.6e} {pc(e_cub)}  "
        f"[{time.time()-T0:.0f}s]")
    out(f"      parametric share of Re c_x = "
        f"{dcx/(cx_add+dcx)*100:+.2f}%")
out("DONE")
