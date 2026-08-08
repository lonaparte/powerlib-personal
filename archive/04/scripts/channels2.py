"""Channel shares for the weak-subcritical family + Vdc swing of the
bounded jump state (idx2, verified bounded at 1.1x flip by m6) and of
the unforced outer attractor. Budget ~3 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/channels2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def build_gfl(over, marg):
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
    return pr, nf_coeffs(pr)

SETS = [
    ('Xg=0.35 (weak)',      dict(Xg=0.35),          0.10),
    ('kp30ki600 (weak)',    dict(kp=30., ki=600.),  0.10),
    ('C=0.005 (weak)',      dict(C=0.005),          0.10),
    ('Q=-0.15 (weak)',      dict(Q=-0.15),          0.10),
    ('mix13 (trans)',       dict(kp=65., ki=1600., kpv=0.8, kiv=35.,
                                 C=0.008, Xg=0.60), 0.10),
    ('Q=+0.15 (strong)',    dict(Q=0.15),           0.10),
    ('mix12 (strong)',      dict(kp=40., ki=800., kpv=1.5, kiv=60.,
                                 C=0.015, Xg=0.45), 0.10),
    ('mix16 (strong)',      dict(kp=45., ki=900., Xg=0.55), 0.10),
]
for tag, over, marg in SETS:
    pr, co = build_gfl(over, marg)
    qn = co['q']/np.linalg.norm(co['q'])
    sf = math.hypot(abs(qn[0]), abs(qn[1]))
    sa = math.hypot(abs(qn[2]), abs(qn[3]))
    out(f"{tag}: f0={co['w0']/2/math.pi:5.2f}Hz Re_c1={co['c1'].real:7.1f} "
        f"theta={abs(qn[0]):.3f} Vdc={abs(qn[2]):.3f} "
        f"freq_share={sf:.3f} amp_share={sa:.3f}")

# bounded jump state for idx2 (kp30ki600), 1.1x flip = 8.151e-3
pr, co = build_gfl(dict(kp=30., ki=600.), 0.10)
st = co['st']; w0 = co['w0']; qv = co['q']; pv = co['p']
c1v = co['c1']
wd = 0.9*w0
eps = 1.1*7.40969e-3
def f(t, x):
    qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
    return rhs(x, qq)
def guard(t, x): return abs(x[2] - st[2]) - 0.8
guard.terminal = True; guard.direction = 1
s = solve_ivp(f, (0, 200), st.copy(), method='DOP853', rtol=1e-9,
              atol=1e-12, events=guard, dense_output=True)
if len(s.t_events[0]):
    out(f"idx2 @1.1x flip: DIVERGED at t={s.t_events[0][0]:.1f} "
        f"(band hit, not bounded)")
else:
    tt = np.linspace(0.5*s.t[-1], s.t[-1], 3000)
    xa = s.sol(tt)
    out(f"idx2 jump state @1.1x flip: theta-swing="
        f"{float(np.max(np.abs(xa[0]-st[0]))):.3f} rad  "
        f"Vdc-swing={float(np.max(np.abs(xa[2]-st[2]))):.4f} pu")
# below flip for contrast
eps = 0.9*7.40969e-3
s = solve_ivp(f, (0, 150), st.copy(), method='DOP853', rtol=1e-9,
              atol=1e-12, dense_output=True)
tt = np.linspace(0.5*150, 150, 3000)
xa = s.sol(tt)
out(f"idx2 locked state @0.9x flip: theta-swing="
    f"{float(np.max(np.abs(xa[0]-st[0]))):.3f} rad  "
    f"Vdc-swing={float(np.max(np.abs(xa[2]-st[2]))):.4f} pu")
# unforced outer attractor (from outside the guard cycle)
zg = math.sqrt(co['alpha']/c1v.real)
def flow_cyc():
    # crude guard-cycle point: st + 2Re(fac*zg*q), integrate unforced
    x0 = st + 2*np.real(1.4*zg*qv)
    def fu(t, x): return rhs(x, pr)
    su = solve_ivp(fu, (0, 100), x0, method='DOP853', rtol=1e-9,
                   atol=1e-12, dense_output=True)
    tt = np.linspace(50, 100, 3000)
    return su.sol(tt)
xa = flow_cyc()
out(f"idx2 unforced outer attractor: theta-swing="
    f"{float(np.max(np.abs(xa[0]-st[0]))):.3f} rad  "
    f"Vdc-swing={float(np.max(np.abs(xa[2]-st[2]))):.4f} pu")
out(f"DONE wall={time.time()-T0:.0f}s")
