"""A1's second-order kick term, derived instead of bounded.

On record: "the A1 kick is linear (+0.00134%, the eps^2 term is <=10% of the
<p,Phi>=0 prediction)".  That is an ABSENT UPPER BOUND, not an absent
formula -- it says the correction did not matter at the amplitudes tested,
not what the correction is.  The correction is a one-line homological
equation and it has a closed form.

The object is the ISOCHRON PROJECTION: the map pi(x) that sends a state to
the amplitude of the critical mode it will settle onto, exact to second
order rather than pi(x) = <p, x>.  Write pi(x) = <p,x> + Q(x,x) with Q a
symmetric bilinear form and require pi to transport correctly under the flow
xdot = Ax + (1/2)B(x,x):

    pidot = <p,Ax> + (1/2)<p,B(x,x)> + 2Q(x,Ax) + O(3)  ==  lambda pi
    ==> 2Q(x,Ax) - lambda Q(x,x) = -(1/2) <p, B(x,x)>

In the eigenbasis A e_i = lambda_i e_i this is diagonal and inverts term by
term -- no PDE, no iteration:

    Q_ij = -(1/2) <p, B(e_i,e_j)> / (lambda_i + lambda_j - lambda)      (I)

resonant only if lambda_i + lambda_j = lambda, which does not happen here
(the candidate lambda + lambda-bar = -2 alpha is not lambda).  So the kick
criterion becomes

    escape  <==>  | <p, dx> + sum_ij Q_ij a_i a_j |  >  rho_g ,
    dx = sum_i a_i e_i

and the linear criterion is its leading term.  (I) is what "the second-order
term of the nonlinear isochron projection" means; it was never written down.

The test has to be run where the term MATTERS, i.e. at kicks large enough
that the two criteria differ -- the earlier measurement used kicks small
enough that they agree, which is exactly why it could only produce a bound.
So: sweep the kick DIRECTION over the 4-sphere, bisect the critical kick
magnitude in the full 4-state system, and compare against both criteria.
Budget ~10 min.
"""
exec(open('selfhead.py').read())
import time
from scipy.optimize import brentq
LOG = open('sweep20/a1iso.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"), 'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']

prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']; c1r = co['c1'].real
lam = co['lam']; pv = co['p']; qv = co['q']
rg = math.sqrt(alpha/c1r)
A = jac(st, pr)
out(f"G1 margin 0.10: alpha={alpha:.6f} w0={w0:.5f} Re c1={c1r:.6e} "
    f"rho_g={rg:.6e}   lam={lam:.6f}")

_al = _avl(st, pr)


def B2(u, v):
    return np.array([sum(_Hl[i][j][k](*_al)*u[j]*v[k]
                         for j in range(4) for k in range(4))
                     for i in range(4)])


ev, VL, VR = eig(A, left=True, right=True)
P = np.array([VL[:, i]/np.vdot(VR[:, i], VL[:, i]) for i in range(4)])
Qt = np.zeros((4, 4), complex)
for i in range(4):
    for j in range(4):
        Qt[i, j] = -0.5*np.vdot(pv, B2(VR[:, i], VR[:, j])) \
            / (ev[i] + ev[j] - lam)
out("  check: sum_i a_i e_i must reconstruct dx -- residual "
    f"{np.max(np.abs(sum(np.vdot(VL[:, i]/np.vdot(VR[:, i], VL[:, i]), np.array([0.3, -0.2, 0.5, 0.1]))*VR[:, i] for i in range(4)) - np.array([0.3, -0.2, 0.5, 0.1]))):.2e}")
out("  eigenvalues: " + ", ".join(f"{e:.5f}" for e in ev))
out("  resonance denominators |lam_i+lam_j-lam| min = "
    f"{min(abs(ev[i]+ev[j]-lam) for i in range(4) for j in range(4)):.4e}"
    "   (zero would mean the projection does not exist)")


def zeta_lin(dx):
    return np.vdot(pv, dx)


def zeta_2(dx):
    a = np.array([np.vdot(P[i], dx) for i in range(4)])
    return zeta_lin(dx) + complex(np.einsum('ij,i,j->', Qt, a, a))


dsad = math.pi - 2*abs(st[0])


def escapes(dx):
    x0 = st + dx
    def _e(t, x):
        return abs(x[0] - st[0]) - dsad
    _e.terminal = True; _e.direction = 1
    def _c(t, x):
        return abs(np.vdot(np.conj(pv), x - st)) - 0.25*rg
    _c.terminal = True; _c.direction = -1
    s = solve_ivp(lambda t, x: rhs(x, pr), (0, 150.0), x0,
                  method='DOP853', rtol=1e-8, atol=1e-11, events=(_e, _c))
    if len(s.t_events[0]) > 0:
        return True
    if len(s.t_events[1]) > 0:
        return False
    xf = s.y[:, -1]
    return abs(np.vdot(np.conj(pv), xf - st)) > 3*rg


def crit(u):
    lo, hi = 0.2*rg/abs(zeta_lin(u)), 6.0*rg/abs(zeta_lin(u))
    n = 0
    while not escapes(hi*u) and n < 12:
        lo = hi; hi *= 1.4; n += 1
    if not escapes(hi*u) or escapes(lo*u):
        return float('nan')
    for _ in range(26):
        m = 0.5*(lo+hi)
        if escapes(m*u): hi = m
        else: lo = m
    return 0.5*(lo+hi)


def solve_s2(u):
    """smallest s with |zeta_2(s u)| = rho_g"""
    f = lambda s: abs(zeta_2(s*u)) - rg
    lo, hi = 1e-9, 8.0*rg/abs(zeta_lin(u))
    if f(hi) < 0:
        return float('nan')
    return brentq(f, lo, hi, xtol=1e-14, rtol=1e-15)


rng = np.random.default_rng(4)
DIRS = [('q real part      ', np.real(qv)),
        ('q imag part      ', np.imag(qv)),
        ('state theta      ', np.array([1.0, 0, 0, 0])),
        ('state Vdc        ', np.array([0, 0, 1.0, 0])),
        ('state xi         ', np.array([0, 0, 0, 1.0]))]
for i in range(3):
    DIRS.append((f'random dir {i}     ', rng.standard_normal(4)))
out("")
out("  direction        |  s_crit (4-state) |  linear    err   |  2nd order"
    "   err   | |zeta2/zeta1|-1")
e1 = []; e2 = []
for tag, u in DIRS:
    u = u/np.linalg.norm(u)
    if abs(zeta_lin(u)) < 1e-6:
        out(f"  {tag} | blind direction, skipped"); continue
    sc = crit(u)
    if sc != sc:
        out(f"  {tag} | no bracket"); continue
    s1 = rg/abs(zeta_lin(u))
    s2 = solve_s2(u)
    d1 = (s1 - sc)/sc*100; d2 = (s2 - sc)/sc*100
    e1.append(abs(d1)); e2.append(abs(d2))
    out(f"  {tag} | {sc:.6e}     | {s1:.4e} {d1:+7.2f}% | "
        f"{s2:.4e} {d2:+7.2f}% | "
        f"{abs(zeta_2(sc*u)/zeta_lin(sc*u))-1:+8.4f}   "
        f"[{time.time()-T0:.0f}s]")
e1 = np.array(e1); e2 = np.array(e2)
out(f"    mean |err|  linear {e1.mean():.3f}%  ->  2nd order {e2.mean():.3f}%")
out(f"    max  |err|  linear {e1.max():.3f}%  ->  2nd order {e2.max():.3f}%")
out(f"    improved in {int((e2 < e1).sum())}/{len(e1)} directions")
out(f"DONE wall={time.time()-T0:.0f}s")
