"""Weak-class re-measurement with a compound instability detector.
Old fate used theta-blow only; amplitude-dominated modes fail through
the Vdc channel (collapse to 0 / overvoltage), which the old detector
recorded as 'capture' (integrator death unnoticed).
Detector: theta-blow (|dth| > dsad+0.15) OR Vdc < 0.2 OR Vdc > 2.5 OR
solver early death. Scan eps/flip grid, then bisect the first
instability threshold. Sets: idx2, idx7, idx9, idx11, idx17.
Budget ~15 min; per-sim progress timestamps.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/recheck.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

CASES = [
    ('idx2 kp30ki600', dict(kp=30., ki=600.), 0.10, 7.40969e-3),
    ('idx7 C=0.005',   dict(C=0.005),         0.10, 3.82242e-3),
    ('idx9 Q=-0.15',   dict(Q=-0.15),         0.10, 8.14083e-3),
    ('idx11 V=1.06',   dict(V=1.06),          0.10, 6.61695e-3),
    ('idx17 kp55ki1200Xg.40', dict(kp=55., ki=1200., Xg=0.40), 0.08,
     7.09997e-3),
]
for tag, over, marg, eflip in CASES:
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
    def probe(eps, T=250):
        def f(t, x):
            qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
            return rhs(x, qq)
        def e_th(t, x): return abs(x[0] - st[0]) - (dsad + 0.15)
        def e_vlo(t, x): return x[2] - 0.2
        def e_vhi(t, x): return x[2] - 2.5
        e_th.terminal = True; e_th.direction = 1
        e_vlo.terminal = True; e_vlo.direction = -1
        e_vhi.terminal = True; e_vhi.direction = 1
        s = solve_ivp(f, (0, T), st.copy(), method='DOP853', rtol=1e-9,
                      atol=1e-12, events=[e_th, e_vlo, e_vhi],
                      dense_output=True)
        if len(s.t_events[0]):
            return 'DESYNC-th', s.t_events[0][0], None, None
        if len(s.t_events[1]):
            return 'VDC-COLLAPSE', s.t_events[1][0], None, None
        if len(s.t_events[2]):
            return 'VDC-OVER', s.t_events[2][0], None, None
        if s.status == -1 or s.t[-1] < T - 1:
            return 'SOLVER-DEATH', s.t[-1], None, None
        tt = np.linspace(0.4*T, T, 3000)
        xa = s.sol(tt)
        return ('BOUNDED', None,
                float(np.max(np.abs(xa[0]-st[0]))),
                float(np.max(np.abs(xa[2]-st[2]))))
    out(f"{tag}: flip={eflip:.4e} dsad={dsad:.3f}")
    last_ok = None; first_bad = None
    for fe in (0.95, 1.05, 1.2, 1.5, 2.0, 2.7, 3.5):
        r, tev, swt, swv = probe(fe*eflip)
        if r == 'BOUNDED':
            out(f"  {fe:4.2f}x flip: BOUNDED th-swing={swt:.3f} "
                f"Vdc-swing={swv:.3f} [{time.time()-T0:.0f}s]")
            if first_bad is None:
                last_ok = fe
        else:
            out(f"  {fe:4.2f}x flip: {r} at t={tev:.1f}s "
                f"[{time.time()-T0:.0f}s]")
            if first_bad is None:
                first_bad = fe
    if last_ok is not None and first_bad is not None and last_ok < first_bad:
        lo2, hi2 = last_ok*eflip, first_bad*eflip
        mode = '?'
        for _ in range(8):
            mid = 0.5*(lo2+hi2)
            r, tev, _, _ = probe(mid)
            if r == 'BOUNDED': lo2 = mid
            else: hi2 = mid; mode = r
        et = 0.5*(lo2+hi2)
        out(f"  RESULT {tag}: eps_true={et:.4e} = {et/eflip:.2f}x flip "
            f"mode={mode}")
    else:
        out(f"  RESULT {tag}: ordering irregular (bands) — "
            f"last_ok={last_ok} first_bad={first_bad}")
out(f"DONE wall={time.time()-T0:.0f}s")
