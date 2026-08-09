"""Which node binds in the pure-P ramped cell?

pdiag showed the trajectory leaves at erosion Re c_x a^2/alpha = 0.687,
i.e. while the guard still exists (alpha_eff = 0.31 alpha) -- so B3
(guard shrinks onto the state) is not what fires there.  The candidate is
B1b: the FORCED ORBIT itself loses stability.  Tested directly by
continuing the stroboscopic fixed point in eps and reading its Floquet
multipliers.  If the dominant multiplier crosses the unit circle at the
measured threshold, the cell belongs to B1b and the erosion branch is
simply not the binding node there.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/pdiag2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"), 'm4', 'exec'), _ns)
hopf = _ns['hopf']
_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])
prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']
wp = 0.62*w0; Td = 2*math.pi/wp
def strobe(x0, eps):
    def f(t, y):
        x = y[:4]; q = dict(pr, P=pr['P'] + eps*math.cos(wp*t))
        return np.concatenate([rhs(x, q),
                               (jac_a(x, q) @ y[4:].reshape(4, 4)).ravel()])
    s = solve_ivp(f, (0, Td), np.concatenate([x0, np.eye(4).ravel()]),
                  method='DOP853', rtol=1e-12, atol=1e-14)
    return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
out("  eps          |mu| of the forced orbit (stroboscopic map)")
x = st.copy()
for fac in (0.2, 0.4, 0.6, 0.8, 0.9, 0.95, 0.98, 1.0, 1.02):
    eps = fac*3.08122e-03
    ok = True
    for it in range(30):
        xT, M = strobe(x, eps)
        R = xT - x
        if np.max(np.abs(R)) < 1e-11:
            break
        try:
            dx = np.linalg.solve(M - np.eye(4), -R)
        except np.linalg.LinAlgError:
            ok = False; break
        n = np.linalg.norm(dx)
        if n > 0.3: dx *= 0.3/n
        x = x + dx
    if not ok or np.max(np.abs(strobe(x, eps)[0] - x)) > 1e-8:
        out(f"  {eps:.5e}  forced-orbit Newton failed (orbit gone)")
        continue
    _, M = strobe(x, eps)
    mu = sorted(np.linalg.eigvals(M), key=lambda z: -abs(z))
    out(f"  {eps:.5e}  " + "  ".join(f"{abs(z):.5f}" for z in mu)
        + f"   (eps/eps_meas = {fac:.2f})")
out("DONE")
