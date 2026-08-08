"""Re-measure the G1 phase-0 kick thresholds with 14-bisection resolution
(0.02/2^14 = 1.2e-6, i.e. 0.02% of kappa) to separate measurement
quantization from the fiber-curvature residual of the etheory prediction.
Predictions (etheory.py): 8.4239e-3 / 7.8782e-3 / 6.9805e-3 / 5.9217e-3.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/etheory2.log', 'w')
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
st = co['st']; w0 = co['w0']; qv = co['q']
wd = 0.9*w0
Td = 2*math.pi/wd
EPSC = 1.1865e-4
PRED = {0.0: 8.4239e-3, 0.3: 7.8782e-3, 0.6: 6.9805e-3, 0.85: 5.9217e-3}
for fbg in (0.0, 0.3, 0.6, 0.85):
    eps = fbg*EPSC
    def frc(t, x):
        qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
        return rhs(x, qq)
    Tset = Td*math.ceil(150/Td)
    if eps > 0:
        s = solve_ivp(frc, (0, Tset), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13)
        xb = s.y[:, -1]
    else:
        xb = st.copy()
    def esc(kap):
        xk = xb + 2*np.real(kap*qv)
        def blow(t, x): return abs(x[0] - st[0]) - 1.2
        blow.terminal = True; blow.direction = 1
        s = solve_ivp(frc, (Tset, Tset+200), xk, method='DOP853',
                      rtol=1e-9, atol=1e-12, events=blow)
        return len(s.t_events[0]) > 0
    klo, khi = 0.0, 0.02
    for _ in range(14):
        km = 0.5*(klo+khi)
        if esc(km): khi = km
        else: klo = km
    kc = 0.5*(klo+khi)
    pd = PRED[fbg]
    out(f"RESULT eps_bg={fbg:.2f}x: meas={kc:.5e} pred={pd:.5e} "
        f"err={(pd-kc)/kc*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
