"""Shifted-origin full 4D Taylor model (T5) for the last F-GFL point.
w = x - st(V(t)):  wdot = A(V)w + 1/2 B_V(w,w) + 1/6 C_V(w,w,w)
                        + 1/24 D4(w^4) + 1/120 D5(w^5) - st_V(V)*Vd
No eigen-reduction: stable-mode dynamics (CM lag) fully retained;
no moving-basis frame terms needed. Tensors on the 181-point V-grid
via vector-valued CubicSpline. Escape: |<p(V),w>| > 5 zg, 12-period
window (protocol-matched). Points: Q=+0.15@w0/32 (A5:+1.3%),
regression mix16@w0/32 (A5:+0.3%), G1m0.05@w0/32 (A5:-0.7%).
Difference T5 - A5 isolates the stable-CM dynamic-lag mechanism.
Budget ~25 min.
"""
exec(open('selfhead.py').read())
import itertools, time
LOG = open('sweep20/f5f.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
from scipy.interpolate import CubicSpline

# order-4/5 derivative lambdas (combo-indexed, built once)
_Q4l = [dict() for _ in range(4)]
_Q5l = [dict() for _ in range(4)]
for i in range(4):
    for combo in itertools.combinations_with_replacement(range(4), 4):
        e = f_[i]
        for j in combo:
            e = sp.diff(e, _x[j])
        _Q4l[i][combo] = sp.lambdify(_args, e, 'numpy')
    for combo in itertools.combinations_with_replacement(range(4), 5):
        e = f_[i]
        for j in combo:
            e = sp.diff(e, _x[j])
        _Q5l[i][combo] = sp.lambdify(_args, e, 'numpy')
out(f"order-4/5 lambdas built [{time.time()-T0:.0f}s]")

def align(qs, ps):
    for i in range(1, len(qs)):
        c = np.vdot(qs[i-1], qs[i])
        ph = c/abs(c)
        qs[i] = qs[i]/ph
        ps[i] = ps[i]/ph
    return qs, ps

MEAS = {'Q=+0.15': 3.1040e-3, 'mix16': 2.3619e-3,
        'G1 m=0.05': 1.2409e-3}
CASES = [
    dict(tag='Q=+0.15', over=dict(Q=0.15), marg=0.10),
    dict(tag='mix16', over=dict(kp=45., ki=900., Xg=0.55), marg=0.10),
    dict(tag='G1 m=0.05', over={}, marg=0.05),
]
for case in CASES:
    prb = gset('G1', **case['over'])
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
    P = margin_point(prb, 0.5*(lo+hi), case['marg'])
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
    n = len(Vg)
    sts = np.zeros((n, 4)); Ag = np.zeros((n, 4, 4))
    Hg = np.zeros((n, 4, 4, 4)); Cg = np.zeros((n, 4, 4, 4, 4))
    D4g = np.zeros((n, 4, 4, 4, 4, 4))
    D5g = np.zeros((n, 4, 4, 4, 4, 4, 4))
    qs, ps = [], []
    for iV, V in enumerate(Vg):
        pri = dict(pr, V=V)
        co = nf_coeffs(pri)
        sts[iV] = co['st']; qs.append(co['q']); ps.append(co['p'])
        Ag[iV] = jac(co['st'], pri)
        av = _avl(co['st'], pri)
        for i in range(4):
            for j in range(4):
                for k in range(4):
                    Hg[iV, i, j, k] = float(_Hl[i][j][k](*av))
                    for l in range(4):
                        Cg[iV, i, j, k, l] = float(_Tl[i][j][k][l](*av))
        for i in range(4):
            for combo, fn in _Q4l[i].items():
                val = float(fn(*av))
                if val == 0.0:
                    continue
                for perm in set(itertools.permutations(combo)):
                    D4g[(iV, i) + perm] = val
            for combo, fn in _Q5l[i].items():
                val = float(fn(*av))
                if val == 0.0:
                    continue
                for perm in set(itertools.permutations(combo)):
                    D5g[(iV, i) + perm] = val
    qs, ps = align(qs, ps)
    ps = np.array(ps)
    st_V = np.gradient(sts, Vg[1]-Vg[0], axis=0)
    spA = CubicSpline(Vg, Ag); spH = CubicSpline(Vg, Hg)
    spC = CubicSpline(Vg, Cg); spD4 = CubicSpline(Vg, D4g)
    spD5 = CubicSpline(Vg, D5g)
    spst = CubicSpline(Vg, sts); spstV = CubicSpline(Vg, st_V)
    spPr = CubicSpline(Vg, ps.real); spPi = CubicSpline(Vg, ps.imag)
    out(f"{case['tag']}: grid+tensors done zg={zg:.4e} "
        f"[{time.time()-T0:.0f}s]")
    ws = w0/32
    Tt1 = 12*2*math.pi/ws
    Vlo_, Vhi_ = Vg[0], Vg[-1]
    def escape4T(a, order=5):
        def f(t, y):
            V = pr['V'] - a*math.sin(ws*t)
            V = min(max(V, Vlo_), Vhi_)
            Vd = -a*ws*math.cos(ws*t)
            w = y
            Aw = spA(V) @ w
            Hw = np.einsum('ijk,j,k->i', spH(V), w, w)
            Cw = np.einsum('ijkl,j,k,l->i', spC(V), w, w, w)
            dw = Aw + 0.5*Hw + Cw/6.0 - spstV(V)*Vd
            if order >= 5:
                dw = dw + np.einsum('ijklm,j,k,l,m->i',
                                    spD4(V), w, w, w, w)/24.0 \
                        + np.einsum('ijklmn,j,k,l,m,n->i',
                                    spD5(V), w, w, w, w, w)/120.0
            return dw
        def blow(t, y):
            V = pr['V'] - a*math.sin(ws*t)
            V = min(max(V, Vlo_), Vhi_)
            pV = spPr(V) + 1j*spPi(V)
            return abs(np.vdot(pV, y)) - 5*zg
        blow.terminal = True; blow.direction = 1
        s = solve_ivp(f, (0, Tt1), np.zeros(4), method='DOP853',
                      rtol=1e-9, atol=1e-13, events=blow)
        return len(s.t_events[0]) > 0
    meas = MEAS[case['tag']]
    line = f"  {case['tag']} w0/32: meas={meas:.4e}"
    for order, name in ((5, 'T5'), (3, 'T3')):
        alo, ahi = 1e-6, AH
        if not escape4T(ahi, order):
            line += f"  {name}:noesc"
            continue
        for _ in range(14):
            am = 0.5*(alo+ahi)
            if escape4T(am, order): ahi = am
            else: alo = am
        ap = 0.5*(alo+ahi)
        line += f"  {name}:{(ap-meas)/meas*100:+.1f}%"
        out(line + f" [{time.time()-T0:.0f}s]")
    out(f"  {case['tag']} final: {line}")
out(f"DONE wall={time.time()-T0:.0f}s")
