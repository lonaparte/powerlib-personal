"""Is the eroded damping alpha_eff observable, and is the relation
channel-free?

The decision tree indexes B2/B3/B4 by channel, which looks fatal if the
disturbance cannot be attributed.  But the channel reaches the criterion
through only two scalars, and both are measurable:

  (i) the kick, whose ratio to the OBSERVED forced modal amplitude is
      |Z(0)|/A_obs = |lam| / |lam + i w_p|   -- f_u cancels exactly;
  (ii) the eroded damping alpha_eff = alpha - Re c_x |a|^2, which is the
       Floquet decay rate of the forced orbit, i.e. exactly what modal
       identification measures on ambient data.

(ii) is tested here: the forced orbit is continued as a stroboscopic
fixed point on the V, P and Q channels at r = 0.9, its dominant
multiplier read, and the decay rate -ln|mu|/T_d compared with
alpha - Re c_x |a|^2.  Drive levels are set as fractions of each
channel's OWN threshold, so if the relation is channel-free all three
channels must give the same rate at the same fraction.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/obsalpha.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"), 'm4', 'exec'), _ns)
cx_hand = _ns['cx_hand']; hopf = _ns['hopf']
_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])
prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
lam = co['lam']; pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr); wp = 0.90*w0; Td = 2*math.pi/wp
hs = 1e-6
out(f"G1 margin 0.10, r=0.90: alpha={alpha:.5f}, "
    f"|lam|/|lam+i w_p| = {abs(lam)/abs(lam+1j*wp):.5f} (channel-free)")
out(" ch  frac  eps          A_obs/r_g  Floquet rate  alpha-Re c_x a^2  err")
for k in ('V', 'P', 'Q'):
    fu = (rhs(st, dict(pr, **{k: pr[k]+hs}))
          - rhs(st, dict(pr, **{k: pr[k]-hs})))/(2*hs)
    F = np.vdot(pv, fu)
    cx = cx_hand(A, st, pr, qv, pv, w0, wp, fu).real
    J = abs(lam)*abs(F)/abs(wp**2 + lam**2)
    rg = math.sqrt(alpha/c1.real)
    lo, hi = 1e-14, 1.0
    for _ in range(200):
        m = 0.5*(lo+hi); a2 = 0.25*m*m
        ae = alpha - cx*a2
        rv = math.sqrt(ae/c1.real) if ae > 0 else -1.0
        if rv < 0 or m*J > rv: hi = m
        else: lo = m
    ec = 0.5*(lo+hi)
    x = st.copy()
    for frac in (0.3, 0.5, 0.7, 0.9):
        eps = frac*ec
        def strobe(x0):
            def f(t, y):
                xx = y[:4]
                q = dict(pr, **{k: pr[k] + eps*math.cos(wp*t)})
                return np.concatenate([rhs(xx, q),
                                       (jac_a(xx, q) @ y[4:].reshape(4, 4)).ravel()])
            s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                          method='DOP853', rtol=1e-12, atol=1e-14)
            return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
        for it in range(30):
            xT, M = strobe(x)
            R = xT - x
            if np.max(np.abs(R)) < 1e-12: break
            dx = np.linalg.solve(M - np.eye(4), -R)
            n = np.linalg.norm(dx)
            if n > 0.3: dx *= 0.3/n
            x = x + dx
        _, M = strobe(x)
        mu = max(np.linalg.eigvals(M), key=lambda z: abs(z))
        rate = -math.log(abs(mu))/Td
        a2 = 0.25*eps*eps
        ae = alpha - cx*a2
        Aobs = eps*abs(F)/abs(1j*wp - lam)
        out(f" {k}  {frac:.1f}   {eps:.4e}   {Aobs/rg:7.4f}   {rate:.6f}      "
            f"{ae:.6f}       {(ae-rate)/rate*100:+6.2f}%")
out("DONE")
