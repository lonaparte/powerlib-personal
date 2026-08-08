"""Weak-class desync threshold as boundary crisis, v2.
Protocol: sudden-on from the equilibrium at each eps (lands on the
bounded attractor in the capture range), guard event at the saddle
distance; measure the attractor's theta-swing over the last 150 s.
Criterion: crisis when swing reaches dtheta_sad = pi - 2|theta_st|.
Every integration guarded; rtol 1e-8 (amplitudes only).
Budget: 3 sets x 6 eps x ~15 s = ~5 min. Progress printed per sim.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/crisis2.log', 'w')
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
    va = [reA(P) for P in grid]
    br = None
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
    st = co['st']; w0 = co['w0']
    wd = 0.9*w0
    dsad = math.pi - 2*abs(st[0])
    out(f"{tag}: theta_st={st[0]:.4f} dtheta_sad={dsad:.4f} "
        f"eps_c(meas)={epsc:.4e}")
    rows = []
    for fe in (0.3, 0.5, 0.7, 0.85, 0.95):
        eps = fe*epsc
        def f(t, x):
            qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
            return rhs(x, qq)
        def blow(t, x): return abs(x[0] - st[0]) - (dsad + 0.15)
        blow.terminal = True; blow.direction = 1
        s = solve_ivp(f, (0, 250), st.copy(), method='DOP853', rtol=1e-8,
                      atol=1e-11, events=blow, dense_output=True)
        if len(s.t_events[0]):
            out(f"  eps={fe:.2f}x: ESCAPED at t={s.t_events[0][0]:.0f}s")
            rows.append((eps, None))
            continue
        tt = np.linspace(100, 250, 4000)
        xa = s.sol(tt)
        sw = float(np.max(np.abs(xa[0] - st[0])))
        rows.append((eps, sw))
        out(f"  eps={fe:.2f}x: swing={sw:.4f} ({sw/dsad*100:.0f}% of sad) "
            f"[{time.time()-T0:.0f}s]")
    good = [(e, s2) for e, s2 in rows if s2 is not None]
    if len(good) >= 3:
        ee = np.array([g[0] for g in good])
        ss = np.array([g[1] for g in good])
        cfs = np.polyfit(ee, ss, 2)
        r = np.roots(np.array([cfs[0], cfs[1], cfs[2]-dsad]))
        r = [x.real for x in r if abs(x.imag) < 1e-12
             and x.real > 0.5*ee[-1]]
        if r:
            epred = min(r)
            out(f"  RESULT {tag}: eps_crisis_pred={epred:.4e} "
                f"eps_c_meas={epsc:.4e} err={(epred-epsc)/epsc*100:+.1f}%")
        else:
            out(f"  RESULT {tag}: swing max {ss.max():.3f} < dsad "
                f"{dsad:.3f}, no crossing in range")
out(f"DONE wall={time.time()-T0:.0f}s")
