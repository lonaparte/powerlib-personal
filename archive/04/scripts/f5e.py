"""Q=+0.15@w0/32 last-point dissection.
(1) 1D A5 criterion-radius sensitivity: R_esc in {2.5,3,4,5}zg ->
    spread quantifies amplitude-truncation honesty.
(2) 4D window test: fate bisection with nper=24 vs logged nper=12
    measurement 3.1040e-3 (and matching 1D window).
Budget ~15 min.
"""
exec(open('selfhead.py').read())
import itertools, time
LOG = open('sweep20/f5e.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
from scipy.interpolate import CubicSpline
from scipy.linalg import eig as _eig

# --- rebuild Q=+0.15 case exactly as f5d ---
TRUNC = 5
exec(open('f5d.py').read().split('def nfc12')[0].split('TRUNC = 5')[1]
     .split('def align')[0])  # pmul..nf_sweep reuse
def align(qs, ps):
    for i in range(1, len(qs)):
        c = np.vdot(qs[i-1], qs[i])
        ph = c/abs(c)
        qs[i] = qs[i]/ph
        ps[i] = ps[i]/ph
    return qs, ps
# nfc12 copied from f5d
exec("def nfc12(pr):\n" + open('f5d.py').read()
     .split("def nfc12(pr):\n")[1].split("\ndef align")[0])

prb = gset('G1', Q=0.15)
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
P = margin_point(prb, 0.5*(lo+hi), 0.10)
pr = dict(prb, P=P)
co0 = nf_coeffs(pr)
st0 = co0['st']; w0 = co0['w0']
zg = math.sqrt(co0['alpha']/co0['c1'].real)
vlo, vhi = pr['V'] - 0.05, pr['V']
for _ in range(30):
    vm = 0.5*(vlo+vhi)
    if equil(dict(pr, V=vm)) is None: vlo = vm
    else: vhi = vm
AH = min(0.012, 0.85*(pr['V'] - vhi))
Vg = pr['V'] + np.linspace(-1.05*AH, 1.05*AH, 181)
sts, lams, c1s, qs, ps = [], [], [], [], []
for V in Vg:
    co = nf_coeffs(dict(pr, V=V))
    sts.append(co['st']); lams.append(co['lam'])
    c1s.append(co['c1']); qs.append(co['q']); ps.append(co['p'])
qs, ps = align(qs, ps)
sts = np.array(sts); lams = np.array(lams); c1s = np.array(c1s)
qs = np.array(qs); ps = np.array(ps)
dV = Vg[1] - Vg[0]
st_V = np.gradient(sts, dV, axis=0)
q_V = np.gradient(qs, dV, axis=0)
p_V = np.gradient(ps, dV, axis=0)
n = len(Vg)
pstV = np.array([np.vdot(ps[i], st_V[i]) for i in range(n)])
pqV = np.array([np.vdot(ps[i], q_V[i]) for i in range(n)])
pVqb = np.array([np.vdot(p_V[i], np.conj(qs[i])) for i in range(n)])
Gsa = np.zeros(n, complex); Gsb = np.zeros(n, complex)
Gs0 = np.zeros(n, complex)
for i in range(n):
    pri = dict(pr, V=Vg[i])
    av = _avl(sts[i], pri)
    def B2c(u, v):
        return np.array([sum(_Hl[ii][j][kk](*av)*u[j]*v[kk]
                             for j in range(4) for kk in range(4))
                         for ii in range(4)])
    qi, pi = qs[i], ps[i]
    Ai = jac(sts[i], pri)
    w = st_V[i].astype(complex)
    Pw = w - qi*np.vdot(pi, w) - np.conj(qi)*np.vdot(np.conj(pi), w)
    y1 = np.real(np.linalg.solve(Ai, Pw))
    Gsa[i] = np.vdot(pi, B2c(y1, qi))
    Gsb[i] = np.vdot(pi, B2c(y1, np.conj(qi)))
    Gs0[i] = 0.5*np.vdot(pi, B2c(y1, y1)) + np.vdot(p_V[i], y1)
Vg2 = np.linspace(Vg[3], Vg[-4], 15)
c2v = []
for V in Vg2:
    r = nfc12(dict(pr, V=V))
    c2v.append(r['c2'])
c2v = np.array(c2v)
c2sp = (CubicSpline(Vg2, c2v.real), CubicSpline(Vg2, c2v.imag))
def c2f(V):
    V = min(max(V, Vg2[0]), Vg2[-1])
    return complex(c2sp[0](V), c2sp[1](V))
out(f"Q=+0.15 rebuilt: zg={zg:.4e} [{time.time()-T0:.0f}s]")
_spl = {}
def itp(arr, V):
    key = id(arr)
    if key not in _spl:
        _spl[key] = (CubicSpline(Vg, arr.real), CubicSpline(Vg, arr.imag))
    V = min(max(V, Vg[0]), Vg[-1])
    sr, si = _spl[key]
    return complex(sr(V), si(V))
ws = w0/32
def escape1d(a, Resc, npw=12):
    Tt1 = npw*2*math.pi/ws
    def f(t, y):
        z = y[0] + 1j*y[1]
        zb = np.conj(z)
        V = pr['V'] - a*math.sin(ws*t)
        Vd = -a*ws*math.cos(ws*t)
        az2 = (y[0]*y[0] + y[1]*y[1])
        dz_ = (itp(lams, V)*z - itp(pstV, V)*Vd
               - itp(pqV, V)*Vd*z + itp(pVqb, V)*Vd*zb
               + itp(Gsa, V)*Vd*z + itp(Gsb, V)*Vd*zb
               + itp(Gs0, V)*Vd*Vd
               + itp(c1s, V)*az2*z + c2f(V)*az2*az2*z)
        return [dz_.real, dz_.imag]
    def blow(t, y):
        return math.hypot(y[0], y[1]) - Resc*zg
    blow.terminal = True; blow.direction = 1
    s = solve_ivp(f, (0, Tt1), [0.0, 0.0], method='DOP853',
                  rtol=1e-10, atol=1e-14, events=blow)
    return len(s.t_events[0]) > 0
meas12 = 3.1040e-3
for Resc in (2.5, 3.0, 4.0, 5.0):
    alo, ahi = 1e-6, AH
    if not escape1d(ahi, Resc):
        out(f"  A5 Resc={Resc}zg: noesc"); continue
    for _ in range(14):
        am = 0.5*(alo+ahi)
        if escape1d(am, Resc): ahi = am
        else: alo = am
    ap = 0.5*(alo+ahi)
    out(f"  A5 Resc={Resc}zg npw=12: pred={ap:.4e} "
        f"errvs12={(ap-meas12)/meas12*100:+.1f}% [{time.time()-T0:.0f}s]")
# 4D window test
def fate4(a, npw):
    def f(t, x):
        qq = dict(pr, V=pr['V'] - a*math.sin(ws*t))
        return rhs(x, qq)
    def blow(t, x): return abs(x[0] - st0[0]) - 1.2
    blow.terminal = True; blow.direction = 1
    def vlo_(t, x): return x[2] - 0.2
    vlo_.terminal = True; vlo_.direction = -1
    Tt = npw*2*math.pi/ws
    s = solve_ivp(f, (0, Tt), st0.copy(), method='DOP853',
                  rtol=1e-9, atol=1e-12, events=(blow, vlo_))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0
alo, ahi = 1e-6, AH
if fate4(ahi, 24):
    for _ in range(13):
        am = 0.5*(alo+ahi)
        if fate4(am, 24): ahi = am
        else: alo = am
    meas24 = 0.5*(alo+ahi)
    out(f"4D nper=24: meas={meas24:.4e} (nper=12: {meas12:.4e}, "
        f"shift {(meas24-meas12)/meas12*100:+.2f}%) [{time.time()-T0:.0f}s]")
    # matched 24-period 1D prediction at 5zg
    alo, ahi = 1e-6, AH
    if escape1d(ahi, 5.0, 24):
        for _ in range(14):
            am = 0.5*(alo+ahi)
            if escape1d(am, 5.0, 24): ahi = am
            else: alo = am
        ap24 = 0.5*(alo+ahi)
        out(f"A5 npw=24 Resc=5zg: pred={ap24:.4e} "
            f"err vs meas24={(ap24-meas24)/meas24*100:+.1f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
