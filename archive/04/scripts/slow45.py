"""Wave 2a: B4 slow band for the two newly added channels.
X_g moves the frozen spectrum strongly (GFL G1: |dRe(lam)/dXg| = 1830,
same order as V) -> a genuine slow-passage mechanism exists; predict
with the co-moving amplitude equation and measure in 4D.
omega_g moves it by 1.4e-4 (seven orders below V) -> structurally no
boundary to cross; verify by driving a large slow omega_g swing and
confirming no escape, and by checking alpha(dw) constancy analytically
(x_pll does not enter any Jacobian entry).
Sets: GFL G1 (Xg, two rates; dw control), GFM M1@0.10 (Xg response).
Budget ~20 min.
"""
exec(open('selfhead.py').read())
import time, sys, os
LOG = open('sweep20/slow45.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
from scipy.interpolate import CubicSpline

def rhs_w(x, pr):
    y = rhs(x, pr).copy()
    y[0] -= pr.get('dw', 0.0)
    return y
def align(qs, ps):
    for i in range(1, len(qs)):
        c = np.vdot(qs[i-1], qs[i]); ph = c/abs(c)
        qs[i] = qs[i]/ph; ps[i] = ps[i]/ph
    return qs, ps

prb = gset('G1')
Psn = 3*prb['V']**2/(4*prb['Xg'])
def reA(P):
    q = dict(prb, P=P); x = equil(q)
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
    m = 0.5*(lo+hi); v = reA(m)
    if v is None or v >= 0: hi = m
    else: lo = m
P0 = margin_point(prb, 0.5*(lo+hi), 0.10)
pr = dict(prb, P=P0, dw=0.0)
co0 = nf_coeffs(pr)
st0 = co0['st']; w0 = co0['w0']
zg = math.sqrt(co0['alpha']/co0['c1'].real)
# Xg existence edge: Psn(Xg) = 0.75/Xg must exceed P0
Xg_edge = 0.75/P0
AH = 0.90*(Xg_edge - pr['Xg'])
out(f"GFL G1: P0={P0:.5f} w0={w0:.3f} Xg0={pr['Xg']} "
    f"Xg_edge={Xg_edge:.5f} (margin {(Xg_edge-pr['Xg'])/pr['Xg']*100:.2f}%) "
    f"AH={AH:.4e}")
Xgrid = pr['Xg'] + np.linspace(-1.05*AH, 1.05*AH, 181)
sts, lams, c1s, qs, ps = [], [], [], [], []
ok = True
for xq in Xgrid:
    try:
        c = nf_coeffs(dict(pr, Xg=xq))
    except Exception:
        ok = False; break
    sts.append(c['st']); lams.append(c['lam']); c1s.append(c['c1'])
    qs.append(c['q']); ps.append(c['p'])
if not ok:
    out("  Xg grid failed")
else:
    qs, ps = align(qs, ps)
    sts = np.array(sts); lams = np.array(lams); c1s = np.array(c1s)
    qs = np.array(qs); ps = np.array(ps)
    dX = Xgrid[1] - Xgrid[0]
    st_u = np.gradient(sts, dX, axis=0)
    q_u = np.gradient(qs, dX, axis=0)
    p_u = np.gradient(ps, dX, axis=0)
    n = len(Xgrid)
    pstU = np.array([np.vdot(ps[i], st_u[i]) for i in range(n)])
    pqU = np.array([np.vdot(ps[i], q_u[i]) for i in range(n)])
    pUqb = np.array([np.vdot(p_u[i], np.conj(qs[i])) for i in range(n)])
    out(f"  alpha over Xg grid: {(-lams.real).min():.4f} .. "
        f"{(-lams.real).max():.4f}  (crossing="
        f"{'yes' if (-lams.real).min() <= 0 else 'no'})")
    _spl = {}
    def itp(arr, xq):
        k2 = id(arr)
        if k2 not in _spl:
            _spl[k2] = (CubicSpline(Xgrid, arr.real),
                        CubicSpline(Xgrid, arr.imag))
        xq = min(max(xq, Xgrid[0]), Xgrid[-1])
        sr, si = _spl[k2]
        return complex(sr(xq), si(xq))
    for ws in (w0/160, w0/32):
        Tt1 = 12*2*math.pi/ws
        def escape1d(a):
            def f(t, y):
                z = y[0] + 1j*y[1]; zb = np.conj(z)
                xq = pr['Xg'] + a*math.sin(ws*t)
                xd = a*ws*math.cos(ws*t)
                dz = (itp(lams, xq)*z - itp(pstU, xq)*xd
                      - itp(pqU, xq)*xd*z + itp(pUqb, xq)*xd*zb
                      + itp(c1s, xq)*abs(z)**2*z)
                return [dz.real, dz.imag]
            def blow(t, y):
                return math.hypot(y[0], y[1]) - 5*zg
            blow.terminal = True; blow.direction = 1
            s = solve_ivp(f, (0, Tt1), [0.0, 0.0], method='DOP853',
                          rtol=1e-10, atol=1e-14, events=blow)
            return len(s.t_events[0]) > 0
        def fate4(a):
            def f(t, x):
                return rhs(x, dict(pr, Xg=pr['Xg'] + a*math.sin(ws*t)))
            def e_th(t, x): return abs(x[0] - st0[0]) - 1.2
            def e_vlo(t, x): return x[2] - 0.2
            def e_vhi(t, x): return x[2] - 2.5
            for e in (e_th, e_vlo, e_vhi):
                e.terminal = True
            e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
            s = solve_ivp(f, (0, Tt1), st0.copy(), method='DOP853',
                          rtol=1e-9, atol=1e-12,
                          events=(e_th, e_vlo, e_vhi))
            return (any(len(t) > 0 for t in s.t_events)
                    or s.status < 0)
        alo, ahi = 1e-4*AH, AH
        if not escape1d(ahi):
            out(f"  Xg ws=w0/{w0/ws:.0f}: 1D no escape at AH"); continue
        for _ in range(14):
            am = 0.5*(alo+ahi)
            if escape1d(am): ahi = am
            else: alo = am
        ap = 0.5*(alo+ahi)
        alo, ahi = 1e-4*AH, AH
        if not fate4(ahi):
            out(f"  Xg ws=w0/{w0/ws:.0f}: 4D no escape at AH"); continue
        for _ in range(13):
            am = 0.5*(alo+ahi)
            if fate4(am): ahi = am
            else: alo = am
        ameas = 0.5*(alo+ahi)
        out(f"  RESULT Xg-slow ws=w0/{w0/ws:.0f}: pred={ap:.4e} "
            f"meas={ameas:.4e} ({ameas/pr['Xg']*100:.3f}% of Xg) "
            f"err={(ap-ameas)/ameas*100:+.1f}% [{time.time()-T0:.0f}s]")
# --- dw: structural absence of the slow-band mechanism ---
out("  dw structural check: x_pll enters only f[0] linearly, so the "
    "Jacobian is x_pll-independent and a constant dw shifts only "
    "x_pll* = dw/ki")
for dwv in (0.0, 0.05, 0.2, 1.0):
    stq = equil(dict(pr, dw=0.0)).copy()
    stq[1] += dwv/pr['ki']
    a = crit_mode(jac_a_ := np.array(
        [[float(sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')(
            *_avl(stq, dict(pr, dw=dwv)))) for j in range(4)]
         for i in range(4)]))
    out(f"    dw={dwv}: alpha={-a.real:.10f} w0={a.imag:.6f}")
for ws in (w0/160, w0/32):
    Tt1 = 12*2*math.pi/ws
    def fate4w(a):
        def f(t, x):
            return rhs_w(x, dict(pr, dw=a*math.sin(ws*t)))
        def e_th(t, x): return abs(x[0] - st0[0]) - 1.2
        def e_vlo(t, x): return x[2] - 0.2
        for e in (e_th, e_vlo):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1
        s = solve_ivp(f, (0, Tt1), st0.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=(e_th, e_vlo))
        return any(len(t) > 0 for t in s.t_events) or s.status < 0
    big = 2.0
    out(f"  dw-slow ws=w0/{w0/ws:.0f}: escape at a={big} rad/s "
        f"({big/(2*math.pi)*1e3:.0f} mHz)? "
        f"{fate4w(big)} [{time.time()-T0:.0f}s]")
# --- GFM Xg slow response ---
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gfmlib as G
from scipy.linalg import eig as _eig
pr0 = G.mset('M1', Xg=0.10)
dfold, Pm = G.fold(pr0)
qh = G.hopf_in(pr0, 'Pref', 0.02*Pm, 0.95*Pm)
P_H = qh['Pref']
def g2(P):
    r = G.maxre_cx(dict(pr0, Pref=P))
    return 1.0 if r is None else r
Phi_ = min(0.95*Pm, 2.5*P_H); tt = 0.10
if g2(Phi_) > -tt: tt = max(0.3*abs(g2(Phi_)), 0.02)
lo2, hi2 = P_H, Phi_
for _ in range(45):
    m = 0.5*(lo2+hi2)
    if g2(m) > -tt: lo2 = m
    else: hi2 = m
prg = dict(pr0, Pref=0.5*(lo2+hi2))
stg = G.equil(prg)
w0g = G.crit_mode(G.jac(stg, prg)).imag
Xg2 = np.linspace(0.07, 0.135, 121)
sts2 = []; Ag = np.zeros((len(Xg2), 4, 4))
okg = True
for i2, xq in enumerate(Xg2):
    x = G.equil(dict(prg, Xg=xq))
    if x is None:
        okg = False; break
    sts2.append(x); Ag[i2] = G.jac(x, dict(prg, Xg=xq))
if okg:
    sts2 = np.array(sts2)
    st_X = np.gradient(sts2, Xg2[1]-Xg2[0], axis=0)
    spA = CubicSpline(Xg2, Ag); spSX = CubicSpline(Xg2, st_X)
    ws = w0g/100
    out(f"GFM M1@0.10: P0={prg['Pref']:.4f} w0={w0g:.3f} "
        f"(full linear co-moving, Xg channel)")
    for aX in (0.005, 0.015):
        Tt = 3*2*math.pi/ws
        def fl(t, w):
            xq = min(max(prg['Xg'] + aX*math.sin(ws*t), Xg2[0]), Xg2[-1])
            xd = aX*ws*math.cos(ws*t)
            return spA(xq) @ w - spSX(xq)*xd
        sl = solve_ivp(fl, (0, Tt), np.zeros(4), method='DOP853',
                       rtol=1e-10, atol=1e-14, dense_output=True)
        tt2 = np.linspace(Tt/3, Tt, 4000)
        pred = float(np.max(np.abs(sl.sol(tt2)[1])))
        def f4(t, x):
            return G.rhs(x, dict(prg,
                                 Xg=prg['Xg'] + aX*math.sin(ws*t)))
        s4 = solve_ivp(f4, (0, Tt), stg.copy(), method='DOP853',
                       rtol=1e-11, atol=1e-14, dense_output=True)
        meas = float(np.max(np.abs(s4.sol(tt2)[1])))
        out(f"  RESULT GFM Xg-slow a={aX} ({aX/prg['Xg']*100:.0f}%): "
            f"pred={pred:.6f} meas={meas:.6f} "
            f"err={(pred-meas)/meas*100:+.2f}% [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
