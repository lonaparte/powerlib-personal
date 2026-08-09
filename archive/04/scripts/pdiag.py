"""Why does the pure-P ramped threshold come out 23% BELOW the erosion
branch, when pure-V and the V-dominated mix both sit ~3% above it (the
known observation-window bias)?

Printed: which detector fires, the steady forced swing of every state
just below the measured threshold, and the erosion budget there.  If the
erosion is still far from alpha when the trajectory leaves, the escape is
not the guard-vanishing mechanism and the pure-P ramped number does not
belong in the additivity test.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/pdiag.log', 'w')
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
st = co['st']; w0 = co['w0']; alpha = co['alpha']; pv = co['p']; qv = co['q']
A = jac(st, pr); dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
hs = 1e-6
fP = (rhs(st, dict(pr, P=pr['P']+hs)) - rhs(st, dict(pr, P=pr['P']-hs)))/(2*hs)
wp = 0.62*w0; Tref = 2*math.pi/wp
cxP = cx_hand(A, st, pr, qv, pv, w0, wp, fP).real
out(f"P channel r=0.62: Re c_x={cxP:.5e}, erosion branch "
    f"2 sqrt(alpha/Re c_x) = {2*math.sqrt(alpha/cxP):.5e}")
for fac, tag in ((0.98, 'just below measured'), (1.02, 'just above')):
    eps = fac*3.08122e-03
    def f(t, x):
        s = min(1.0, t/(200*Tref))
        return rhs(x, dict(pr, P=pr['P'] + s*eps*math.cos(wp*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, 1800*Tref), st.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi),
                  dense_output=True)
    ev = ['TH', 'VLO', 'VHI']
    fired = [ev[i] for i in range(3) if len(s.t_events[i])]
    tt = np.linspace(max(0, s.t[-1]-40*Tref), s.t[-1], 3000)
    Y = s.sol(tt)
    sw = [0.5*(Y[i].max()-Y[i].min()) for i in range(4)]
    zmod = [abs(np.vdot(pv, Y[:, i]-st)) for i in range(len(tt))]
    out(f"  eps={eps:.5e} ({tag}): escaped={bool(fired) or s.status<0} "
        f"{fired} at t={s.t[-1]/Tref:.0f} ref-periods")
    out(f"     state swings: th {sw[0]:.4e} (d_sad {dsad:.3f})  "
        f"x_pll {sw[1]:.4e}  Vdc {sw[2]:.4e} ({sw[2]/Vdc0*100:.2f}%)  "
        f"xi {sw[3]:.4e}")
    out(f"     modal |<p,y>| max over the last 40 periods = {max(zmod):.4e}; "
        f"erosion Re c_x a^2/alpha = {cxP*(0.5*eps)**2/alpha:.4f}")
out("DONE")
