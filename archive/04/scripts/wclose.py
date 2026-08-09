"""Close the omega_g slow-band cell with a zero-fitting predictor.

Mechanism (established): slow forcing displaces the state inside state
space; along the displaced trajectory the instantaneous Jacobian
becomes unstable over a window; escape requires the accumulated growth
in that window to carry the deviation from its entry size up to the
guard object.  The frozen-Jacobian criterion alone captures the whole
frequency dependence but omits the accumulation, hence its constant
factor.  The accumulation criterion supplies exactly that factor:

    A(a) = int_window max Re eig( J(x_base(t)) ) dt   >=   ln( r_g / d_entry )

with   r_g   = guard radius expressed in the same norm as the deviation
       d_entry = deviation size when the window opens.
Both sides are computed from the model; no fitted constant.

Deviation norm: modal amplitude |<p, x - st(dw(t))>| (the same object
whose guard value is r_g = sqrt(alpha/Re l1)).
Base trajectory: the LINEAR forced response about the moving
equilibrium (a genuine predictor: no nonlinear simulation needed).

Test at ws = w0/160, w0/32, w0/8 against the measured thresholds
1.9747, 1.2290, 0.93297 rad/s.  Budget ~10 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/wclose.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def rhs_w(x, pr):
    y = rhs(x, pr).copy(); y[0] -= pr.get('dw', 0.0); return y

prb = gset('G1'); Psn = 3*prb['V']**2/(4*prb['Xg'])
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
pr = dict(prb, P=P0, dw=0.0)
co = nf_coeffs(pr)
st0 = co['st']; w0 = co['w0']; pv = co['p']; lam = co['lam']
alpha = co['alpha']; c1v = co['c1']
rg = math.sqrt(alpha/c1v.real)           # guard radius (modal amplitude)
A0 = jac(st0, pr)
st_dw = np.array([0.0, 1.0/pr['ki'], 0.0, 0.0])   # exact: A^-1 e1
G = np.vdot(pv, st_dw)
out(f"G1: w0={w0:.4f} alpha={alpha:.4f} r_g={rg:.5e} |<p,st_dw>|={abs(G):.5f}")
out("criterion: int_window maxRe eig J(x_base) dt >= ln(r_g/d_entry), "
    "x_base = moving equilibrium + linear forced response")

CASES = [(w0/160, 1.9747), (w0/32, 1.2290), (w0/8, 0.93297)]
for ws, meas in CASES:
    Tspan = min(0.75*2*math.pi/ws, 60.0)
    def base_traj(a, N=3000):
        """linear response about the moving equilibrium (exact at O(a))"""
        def fl(t, y):
            return A0 @ y - st_dw*(a*ws*math.cos(ws*t))
        s = solve_ivp(fl, (0, Tspan), np.zeros(4), method='DOP853',
                      rtol=1e-12, atol=1e-15, dense_output=True)
        tt = np.linspace(0, Tspan, N)
        Y = s.sol(tt)
        X = np.zeros_like(Y)
        for i in range(N):
            X[:, i] = st0 + Y[:, i]
            X[1, i] += a*math.sin(ws*tt[i])/pr['ki']
        z = np.array([np.vdot(pv, Y[:, i]) for i in range(N)])
        return tt, X, Y, z
    def accum(a):
        tt, X, Y, z = base_traj(a)
        mu = np.empty(len(tt))
        for i in range(len(tt)):
            mu[i] = float(np.max(np.linalg.eigvals(jac(X[:, i], pr)).real))
        pos = mu > 0.0
        if not pos.any():
            return None, None, None, mu.max()
        # first contiguous unstable window
        idx = np.where(pos)[0]
        i0 = idx[0]
        i1 = i0
        while i1+1 < len(mu) and pos[i1+1]:
            i1 += 1
        Aacc = float(np.trapezoid(mu[i0:i1+1], tt[i0:i1+1]))
        d_entry = abs(z[i0])
        need = math.log(rg/max(d_entry, 1e-300))
        return Aacc, need, (tt[i0], tt[i1], d_entry), mu.max()
    # bisect on the accumulation criterion
    alo, ahi = 0.2*meas, 2.0*meas
    def crit(a):
        Aacc, need, info, mumax = accum(a)
        if Aacc is None:
            return -1.0
        return Aacc - need
    n = 0
    while crit(ahi) < 0 and n < 8:
        ahi *= 1.4; n += 1
    n = 0
    while crit(alo) > 0 and n < 8:
        alo *= 0.6; n += 1
    if crit(alo) > 0 or crit(ahi) < 0:
        out(f"  ws=w0/{w0/ws:.0f}: bracket failed "
            f"(crit(lo)={crit(alo):.3f}, crit(hi)={crit(ahi):.3f})")
        continue
    for _ in range(15):
        am = 0.5*(alo+ahi)
        if crit(am) > 0: ahi = am
        else: alo = am
    ac = 0.5*(alo+ahi)
    Aacc, need, info, mumax = accum(ac)
    out(f"  ws=w0/{w0/ws:.0f} ({ws:.4f} rad/s): a_c(criterion)={ac:.4f} "
        f"meas={meas:.4f} err={(ac-meas)/meas*100:+.2f}%")
    out(f"      window [{info[0]:.2f},{info[1]:.2f}] s  "
        f"accumulated growth={Aacc:.4f}  required ln(r_g/d_entry)={need:.4f}"
        f"  d_entry={info[2]:.3e} ({info[2]/rg:.3f} r_g)  "
        f"max mu={mumax:.4f} [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
