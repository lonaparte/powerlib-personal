"""Slow-band P/Q cells, corrected.
(1) P-GFL: AH enlarged (G1's Hopf lies 1.5e-4 pu above P0 — R17
    cliff); thresholds a_c at w0/160, w0/32: 1D amplitude eq vs 4D.
(2) Q-GFL: two-sided boundary (alpha crossing at Q<0, equilibrium
    fold at Q>0). Q-grid within existence window; thresholds both
    rates, 1D vs 4D.
(3) Q-GFM: full linear co-moving 4D model wdot = A(Q(t))w - st_Q Qd
    (all modes, no critical-mode truncation) vs 4D nonlinear.
Budget ~18 min.
"""
exec(open('selfhead.py').read())
import time, sys, os
LOG = open('sweep20/pqslow2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
from scipy.interpolate import CubicSpline

def align(qs, ps):
    for i in range(1, len(qs)):
        c = np.vdot(qs[i-1], qs[i])
        ph = c/abs(c)
        qs[i] = qs[i]/ph
        ps[i] = ps[i]/ph
    return qs, ps

prb = gset('G1')
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
PH = 0.5*(lo+hi)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0)
co0 = nf_coeffs(pr)
st0 = co0['st']; w0 = co0['w0']
zg = math.sqrt(co0['alpha']/co0['c1'].real)

def run_1d4d(tag, key, ug, u0, AH, ws_list, base_pr):
    """generic slow-band threshold: grid over parameter key."""
    sts, lams, c1s, qs, ps = [], [], [], [], []
    for uq in ug:
        try:
            co = nf_coeffs(dict(base_pr, **{key: uq}))
        except Exception:
            return out(f"  {tag}: grid nf_coeffs failed at {uq:.4f}")
        sts.append(co['st']); lams.append(co['lam'])
        c1s.append(co['c1']); qs.append(co['q']); ps.append(co['p'])
    qs, ps = align(qs, ps)
    sts = np.array(sts); lams = np.array(lams); c1s = np.array(c1s)
    qs = np.array(qs); ps = np.array(ps)
    du = ug[1] - ug[0]
    st_u = np.gradient(sts, du, axis=0)
    q_u = np.gradient(qs, du, axis=0)
    p_u = np.gradient(ps, du, axis=0)
    n = len(ug)
    pstU = np.array([np.vdot(ps[i], st_u[i]) for i in range(n)])
    pqU = np.array([np.vdot(ps[i], q_u[i]) for i in range(n)])
    pUqb = np.array([np.vdot(p_u[i], np.conj(qs[i])) for i in range(n)])
    _spl = {}
    def itp(arr, uq):
        k2 = id(arr)
        if k2 not in _spl:
            _spl[k2] = (CubicSpline(ug, arr.real),
                        CubicSpline(ug, arr.imag))
        uq = min(max(uq, ug[0]), ug[-1])
        sr, si = _spl[k2]
        return complex(sr(uq), si(uq))
    for ws in ws_list:
        Tt1 = 12*2*math.pi/ws
        def escape1d(a):
            def f(t, y):
                z = y[0] + 1j*y[1]
                zb = np.conj(z)
                uq = u0 + a*math.sin(ws*t)
                ud = a*ws*math.cos(ws*t)
                dz = (itp(lams, uq)*z - itp(pstU, uq)*ud
                      - itp(pqU, uq)*ud*z + itp(pUqb, uq)*ud*zb
                      + itp(c1s, uq)*abs(z)**2*z)
                return [dz.real, dz.imag]
            def blow(t, y):
                return math.hypot(y[0], y[1]) - 5*zg
            blow.terminal = True; blow.direction = 1
            s = solve_ivp(f, (0, Tt1), [0.0, 0.0], method='DOP853',
                          rtol=1e-10, atol=1e-14, events=blow)
            return len(s.t_events[0]) > 0
        def fate4(a):
            def f(t, x):
                return rhs(x, dict(base_pr,
                                   **{key: u0 + a*math.sin(ws*t)}))
            def e_th(t, x): return abs(x[0] - st0[0]) - 1.2
            def e_vlo(t, x): return x[2] - 0.2
            def e_vhi(t, x): return x[2] - 2.5
            for e in (e_th, e_vlo, e_vhi):
                e.terminal = True
            e_th.direction = 1; e_vlo.direction = -1
            e_vhi.direction = 1
            s = solve_ivp(f, (0, Tt1), st0.copy(), method='DOP853',
                          rtol=1e-9, atol=1e-12,
                          events=(e_th, e_vlo, e_vhi))
            return (any(len(t) > 0 for t in s.t_events)
                    or s.status < 0)
        alo, ahi = 1e-4*AH, AH
        if not escape1d(ahi):
            out(f"  {tag} ws=w0/{w0/ws:.0f}: 1D no escape at AH={AH:.3e}")
            continue
        for _ in range(14):
            am = 0.5*(alo+ahi)
            if escape1d(am): ahi = am
            else: alo = am
        ap = 0.5*(alo+ahi)
        alo, ahi = 1e-4*AH, AH
        if not fate4(ahi):
            out(f"  {tag} ws=w0/{w0/ws:.0f}: 4D no escape at AH")
            continue
        for _ in range(13):
            am = 0.5*(alo+ahi)
            if fate4(am): ahi = am
            else: alo = am
        ameas = 0.5*(alo+ahi)
        out(f"  RESULT {tag} ws=w0/{w0/ws:.0f}: pred={ap:.4e} "
            f"meas={ameas:.4e} err={(ap-ameas)/ameas*100:+.1f}% "
            f"[{time.time()-T0:.0f}s]")

# ---- (1) P-GFL, enlarged AH ----
AH = min(0.028, 0.985*Psn - P0)
out(f"P-GFL G1: P0={P0:.5f} PH={PH:.5f} (PH-P0={PH-P0:.2e}, cliff) "
    f"AH={AH:.3e} w0={w0:.3f}")
Pg = P0 + np.linspace(-1.05*AH, 1.05*AH, 181)
run_1d4d('P-GFL', 'P', Pg, P0, AH, (w0/160, w0/32), pr)

# ---- (2) Q-GFL, two-sided window ----
qlo, qhi = -0.4, 0.4
for _ in range(30):                       # positive-side existence edge
    m = 0.5*(qlo+qhi) if equil(dict(pr, Q=0.5*(qlo+qhi))) is None \
        else None
    break
lo2, hi2 = 0.0, 0.4
while equil(dict(pr, Q=hi2)) is None:
    hi2 *= 0.8
for _ in range(30):
    m = 0.5*(lo2+hi2)
    if equil(dict(pr, Q=m)) is None: hi2 = m
    else: lo2 = m
Qf = lo2
lo3, hi3 = -0.4, 0.0                      # negative-side alpha crossing
def aQ(Qq):
    x = equil(dict(pr, Q=Qq))
    if x is None: return None
    cm = crit_mode(jac(x, dict(pr, Q=Qq)))
    return None if cm is None else -cm.real
while aQ(lo3) is None:
    lo3 *= 0.8
for _ in range(30):
    m = 0.5*(lo3+hi3)
    v = aQ(m)
    if v is None or v <= 0: lo3 = m
    else: hi3 = m
QHm = 0.5*(lo3+hi3)
out(f"Q-GFL G1: existence edge Q+={Qf:.4f}, alpha-crossing Q-={QHm:.4f}")
AHq = 0.92*min(Qf, -QHm*1.6 if QHm < 0 else 0.4)
AHq = min(AHq, 0.95*Qf)
Qgrid = np.linspace(max(1.25*QHm, -0.4), 0.97*Qf, 181)
run_1d4d('Q-GFL', 'Q', Qgrid, 0.0, AHq, (w0/160, w0/32), pr)

# ---- (3) Q-GFM full linear co-moving model ----
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gfmlib as G
prm0 = G.mset('M1', Xg=0.10)
dfold, Pm = G.fold(prm0)
qh = G.hopf_in(prm0, 'Pref', 0.02*Pm, 0.95*Pm)
P_H = qh['Pref']
def g2(P):
    r = G.maxre_cx(dict(prm0, Pref=P))
    return 1.0 if r is None else r
Phi_ = min(0.95*Pm, 2.5*P_H)
tt = 0.10
if g2(Phi_) > -tt:
    tt = max(0.3*abs(g2(Phi_)), 0.02)
lo2, hi2 = P_H, Phi_
for _ in range(45):
    m = 0.5*(lo2+hi2)
    if g2(m) > -tt: lo2 = m
    else: hi2 = m
P0g = 0.5*(lo2+hi2)
prg = dict(prm0, Pref=P0g)
stg = G.equil(prg)
w0g = G.crit_mode(G.jac(stg, prg)).imag
Qg2 = np.linspace(-0.17, 0.17, 121)
stsg = []
Ag = np.zeros((len(Qg2), 4, 4))
for i2, Qq in enumerate(Qg2):
    prq = dict(prg, Qref=Qq)
    x = G.equil(prq)
    stsg.append(x)
    Ag[i2] = G.jac(x, prq)
stsg = np.array(stsg)
st_Q = np.gradient(stsg, Qg2[1]-Qg2[0], axis=0)
spA = CubicSpline(Qg2, Ag); spSQ = CubicSpline(Qg2, st_Q)
ws = w0g/100
out(f"Q-GFM M1@0.10: P0={P0g:.4f} w0={w0g:.3f} (full linear co-moving)")
for aQ2 in (0.05, 0.15):
    Tt = 2*2*math.pi/ws
    def fl(t, w):
        Qq = aQ2*math.sin(ws*t)
        Qq = min(max(Qq, Qg2[0]), Qg2[-1])
        Qd = aQ2*ws*math.cos(ws*t)
        return spA(Qq) @ w - spSQ(Qq)*Qd
    sl = solve_ivp(fl, (0, Tt), np.zeros(4), method='DOP853',
                   rtol=1e-10, atol=1e-14, dense_output=True)
    tt2 = np.linspace(0, Tt, 4000)
    pred = float(np.max(np.abs(sl.sol(tt2)[1])))
    def f4(t, x):
        return G.rhs(x, dict(prg, Qref=aQ2*math.sin(ws*t)))
    s4 = solve_ivp(f4, (0, Tt), stg + np.array([1e-5, 0, 0, 0]),
                   method='DOP853', rtol=1e-10, atol=1e-13,
                   dense_output=True)
    meas = float(np.max(np.abs(s4.sol(tt2)[1])))
    out(f"  RESULT Q-GFM ws=w0/100 a={aQ2}: pred={pred:.6f} "
        f"meas={meas:.6f} err={(pred-meas)/meas*100:+.1f}% "
        f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
