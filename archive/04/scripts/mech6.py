"""Where idx17's remaining 1.14% lives: field truncation or reduction?

After the fifth-order two-carrier terms the closed form reads
    V cell   +0.13 / +0.14 / +0.15 / +0.16%   (flat in alpha)
    idx17    +1.14%   (was +2.53% at cubic order)
and at idx17 neither series is to blame on its own: the drive series has
|a^4 term| / |a^2 term| = 0.017 and the amplitude series has
Re c2 rho_g^2 / Re c1 = 0.009, so both converge fast.  Two candidates
remain: the Taylor truncation of the FIELD (idx17's guard sits at
r_g = 0.0987, eleven times the V cell's, so quartic and quintic field
terms act where the cubic field was being used), and the averaging step
that turns the two-carrier equation into an autonomous radial equation.

They are separated by running the same protocol on the 4D Taylor field
truncated at order 3, 4 and 5 -- same states, same drive, same readout,
only the polynomial order changes:
    ydot = A y + B(y,y)/2 + C(y^3)/6 [+ D(y^4)/24 [+ E(y^5)/120]] + eps f_u cos
If the order-5 field reproduces the exact threshold, the field truncation
is settled and what is left belongs to the reduction; if it does not, the
field is the culprit and the reduction is already better than it looked.
Budget ~25 min.
"""
exec(open('selfhead.py').read())
import itertools, time
from math import factorial
LOG = open('sweep20/mech6.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
taylor_tensors = _ns['taylor_tensors']
mult_count = _ns['mult_count']
hopf = _ns['hopf']

def build_field(Dk, order):
    """dense symmetric arrays for orders 2..order"""
    T = {}
    for k in range(2, order+1):
        shape = (4,)*(k+1)
        M = np.zeros(shape)
        for i in range(4):
            for combo, val in Dk[k][i].items():
                for perm in set(itertools.permutations(combo)):
                    M[(i,)+perm] = val.real
        T[k] = M/factorial(k)
    return T
def field_rhs(T, A, y, order):
    v = A @ y
    for k in range(2, order+1):
        M = T[k]
        w = M
        for _ in range(k):
            w = np.tensordot(w, y, axes=([w.ndim-1], [0]))
        v = v + w
    return v

CELLS = [('G1 V r=0.9 alpha=0.10', {}, 0.9, 0.10, 1000),
         ('idx17 r=0.92 alpha=0.08', dict(kp=55., ki=1200., Xg=0.40),
          0.92, 0.08, 4000)]
for tag, over, rat, marg, NPw in CELLS:
    prb = gset('G1', **over)
    PH = hopf(prb)
    P0 = margin_point(prb, PH, marg)
    pr = dict(prb, P=P0); co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; alpha = co['alpha']; c1 = co['c1']
    pv = co['p']; A = jac(st, pr)
    rg = math.sqrt(alpha/c1.real)
    wp = rat*w0; Td = 2*math.pi/wp
    hs = 1e-6
    fV = (rhs(st, dict(pr, V=pr['V']+hs))
          - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
    Dk = taylor_tensors(pr, st)
    T = build_field(Dk, 5)
    out(f"=== {tag}: r_g={rg:.5e}, w_p={wp:.4f}, window {NPw} periods "
        f"[{time.time()-T0:.0f}s]")
    def esc(eps, order, NPn):
        if order == 0:
            def f(t, y):
                return rhs(y + st, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
        else:
            def f(t, y):
                return (field_rhs(T, A, y, order)
                        + eps*fV*math.cos(wp*t))
        def e_r(t, y):
            return abs(np.vdot(pv, y)) - 5.0*rg
        e_r.terminal = True; e_r.direction = 1
        s = solve_ivp(f, (0, NPn*Td), np.zeros(4), method='DOP853',
                      rtol=1e-10, atol=1e-13, events=(e_r,))
        return len(s.t_events[0]) > 0 or s.status < 0
    def thr(order, seed):
        elo, ehi = 0.7*seed, 1.3*seed
        n = 0
        while not esc(ehi, order, 400) and n < 12:
            elo = ehi; ehi *= 1.25; n += 1
        n = 0
        while esc(elo, order, 400) and n < 12:
            ehi = elo; elo *= 0.8; n += 1
        if esc(elo, order, 400) or not esc(ehi, order, 400):
            return float('nan')
        for _ in range(17):
            em = 0.5*(elo+ehi)
            if esc(em, order, NPw): ehi = em
            else: elo = em
        return 0.5*(elo+ehi)
    e_ex = thr(0, 1.2e-4 if rat == 0.9 else 7.1e-3)
    out(f"    exact field      {e_ex:.6e}  [{time.time()-T0:.0f}s]")
    for order in (3, 4, 5):
        e = thr(order, e_ex)
        out(f"    Taylor order {order}   {e:.6e}   "
            f"{(e-e_ex)/e_ex*100:+6.2f}%  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
