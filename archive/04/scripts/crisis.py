"""Weak-class desync threshold as a boundary crisis: the outer bounded
attractor's theta-swing grows with eps and collides with the PLL saddle
distance (pi - 2*theta_st); predicted eps_crisis = level crossing of the
measured swing curve, compared with the measured sudden-on threshold.
Sets: idx2 (kp30ki600), idx7 (C=0.005), idx9 (Q=-0.15).
Budget: ~20 min (5-6 eps x 3 sets x ~200 s sims).
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/crisis.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

CASES = [
    ('idx2 kp30ki600', dict(kp=30., ki=600.), 0.10, 8.49451e-2),
    ('idx7 C=0.005',   dict(C=0.005),         0.10, 2.77267e-2),
    ('idx9 Q=-0.15',   dict(Q=-0.15),         0.10, 4.79005e-2),
]
for tag, over, marg, epsc in CASES:
    prb = gset('G1', **over)
    Psn = 3*prb['V']**2/(4*prb['Xg'])
    def reA(P):
        q = dict(prb, P=P)
        x = equil(q)
        if x is None: return None
        cm = crit_mode(jac(x, q))
        return None if cm is None else cm.real
    grid = np.linspace(0.05, 0.985, 60)*Psn
    br = None
    va = [reA(P) for P in grid]
    for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
        if fa is not None and fb is not None and fa < 0 <= fb:
            br = (a, b); break
    lo, hi = br
    for _ in range(45):
        m = 0.5*(lo+hi)
        v = reA(m)
        if v is None or v >= 0: hi = m
        else: lo = m
    P = margin_point(prb, 0.5*(lo+hi), marg)
    pr = dict(prb, P=P)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; qv = co['q']; c1v = co['c1']
    alpha = co['alpha']
    wd = 0.9*w0
    zg = math.sqrt(alpha/c1v.real)
    dsad = math.pi - 2*abs(st[0])
    out(f"{tag}: P={P:.5f} w0={w0:.3f} theta_st={st[0]:.4f} "
        f"dtheta_sad={dsad:.4f} eps_c(meas)={epsc:.4e}")
    # guard cycle for the outer seed
    _Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
            for j in range(4)] for i in range(4)]
    def jac_a(x, prm):
        a = _avl(x, prm)
        return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                         for i in range(4)])
    def flow_auto(x0, T, with_var=False):
        def f(t, y):
            x = y[:4]
            if not with_var:
                return rhs(x, pr)
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, pr), (jac_a(x, pr) @ Phi).ravel()])
        y0 = (x0 if not with_var
              else np.concatenate([x0, np.eye(4).ravel()]))
        s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12,
                      atol=1e-14)
        return (s.y[:4, -1] if not with_var
                else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
    def cycle_newton(xs, Ts, itmax=40):
        x, T = xs.copy(), Ts
        fref = rhs(xs, pr)
        for it in range(itmax):
            xT, M = flow_auto(x, T, with_var=True)
            R = np.append(xT - x, np.dot(fref, x - xs))
            if np.max(np.abs(R)) < 1e-12:
                return x, T, True
            A5 = np.zeros((5, 5))
            A5[:4, :4] = M - np.eye(4)
            A5[:4, 4] = rhs(xT, pr)
            A5[4, :4] = fref
            dy = np.linalg.solve(A5, -R)
            n = np.linalg.norm(dy[:4])
            cap = max(0.01, 0.5*zg)
            if n > cap:
                dy *= cap/n
            if abs(dy[4]) > 0.1*T:
                dy *= 0.1*T/abs(dy[4])
            x = x + dy[:4]; T = T + dy[4]
        return x, T, np.max(np.abs(R)) < 1e-9
    cyc = None
    for fac in (1.0, 0.85, 0.7, 1.2):
        xs = st + 2*np.real(fac*zg*qv)
        Ts = 2*math.pi/(w0 + c1v.imag*(fac*zg)**2)
        x0c, Tc, okc = cycle_newton(xs, Ts)
        if okc and abs(np.vdot(qv, x0c - st)) > 1e-4:
            cyc = (x0c, Tc); break
    x0c, Tc = cyc
    # unforced outer-attractor point (m6 protocol)
    xout0 = st + 1.4*(x0c - st)
    su = solve_ivp(lambda t, x: rhs(x, pr), (0, 60), xout0,
                   method='DOP853', rtol=1e-10, atol=1e-13)
    xout = su.y[:, -1]
    rows = []
    for fe in (0.3, 0.5, 0.7, 0.85, 0.95):
        eps = fe*epsc
        def f(t, x):
            qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
            return rhs(x, qq)
        def blow(t, x): return abs(x[0] - st[0]) - (dsad + 0.2)
        blow.terminal = True; blow.direction = 1
        s = solve_ivp(f, (0, 220), xout.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=blow,
                      dense_output=True)
        if len(s.t_events[0]):
            out(f"  eps={fe:.2f}x eps_c: ESCAPED at t={s.t_events[0][0]:.0f}s")
            rows.append((eps, None))
            continue
        tt = np.linspace(70, 220, 4000)
        xa = s.sol(tt)
        sw = float(np.max(np.abs(xa[0] - st[0])))
        rows.append((eps, sw))
        out(f"  eps={fe:.2f}x eps_c: theta-swing={sw:.4f} "
            f"({sw/dsad*100:.0f}% of saddle)")
    good = [(e, s2) for e, s2 in rows if s2 is not None]
    if len(good) >= 3:
        ee = np.array([g[0] for g in good])
        ss = np.array([g[1] for g in good])
        # level crossing of the swing curve at dsad via quadratic fit
        cfs = np.polyfit(ee, ss, 2)
        r = np.roots(np.array([cfs[0], cfs[1], cfs[2]-dsad]))
        r = [x.real for x in r if abs(x.imag) < 1e-12 and x.real > ee[-1]*0.5]
        if r:
            epred = min(r)
            out(f"  RESULT {tag}: eps_crisis_pred={epred:.4e} "
                f"eps_c_meas={epsc:.4e} err={(epred-epsc)/epsc*100:+.1f}%")
        else:
            out(f"  RESULT {tag}: swing curve does not reach dsad in fit "
                f"range (max {ss.max():.3f} vs {dsad:.3f})")
out(f"DONE wall={time.time()-T0:.0f}s")
