"""Window-convergence re-measurement of the slow-drive escape amplitudes
a_c(ws) at G1 marg0.1 (the F experiment used 3 slow periods — at ws=5
that is 3.77 s, likely window-limited). Bisect with nper = 3, 12, 36.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/remeasure.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
pr0 = gset('G1', Xg=0.5)
lo, hi = 0.9, 1.4775
def g0(P):
    x = equil(dict(pr0, P=P))
    return crit_mode(jac(x, dict(pr0, P=P))).real
for _ in range(45):
    m = 0.5*(lo+hi)
    if g0(m) < 0: lo = m
    else: hi = m
P = margin_point(pr0, 0.5*(lo+hi), 0.10)
pr = dict(pr0, P=P)
co = nf_coeffs(pr)
st = co['st']
def fateF(a, ws, nper):
    def f(t, x):
        qq = dict(pr, V=pr['V'] - a*math.sin(ws*t))
        return rhs(x, qq)
    def blow(t, x): return abs(x[0] - st[0]) - 1.2
    blow.terminal = True; blow.direction = 1
    T = nper*2*math.pi/ws
    s = solve_ivp(f, (0, T), st.copy(), method='DOP853', rtol=1e-9,
                  atol=1e-12, events=blow)
    return len(s.t_events[0]) > 0
for ws in (1.0, 5.0):
    for nper in (3, 12, 36):
        alo, ahi = 1e-5, 0.02
        if not fateF(ahi, ws, nper):
            out(f"ws={ws} nper={nper}: no escape at 0.02"); continue
        for _ in range(14):
            am = 0.5*(alo+ahi)
            if fateF(am, ws, nper): ahi = am
            else: alo = am
        out(f"RESULT ws={ws} nper={nper}: a_c={0.5*(alo+ahi):.4e}")
out(f"DONE wall={time.time()-T0:.0f}s")
