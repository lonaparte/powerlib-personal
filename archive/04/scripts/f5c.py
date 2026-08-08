"""Second-order lag correction test on the two remaining F-GFL points
(mix16@w0/32 B:+1.1%; G1m0.05@w0/32 B:-2.7% A:-0.9%).
Fast-mode response beyond quasi-static:
  y = y1s*Vd - A^-1*y1s*Vdd - A^-1*y1s_V*Vd^2 + O(3rd)
  (Vdd = a*ws^2*sin(ws t) = -(V-V0)*ws^2)
New z-linear terms: -<p,B(y2,q)>Vdd*z - <p,B(y2b,q)>Vd^2*z (+zbar
analogues, + forcing corrections via p_V couplings), y2=A^-1 y1s,
y2b=A^-1 y1s_V. Models: B2 = model B + these; A2 = model A + these
(for G1m0.05). Budget ~15 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/f5c.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
from scipy.interpolate import CubicSpline

MEAS = {'mix16': 2.3619e-3, 'G1 m=0.05': 1.2409e-3}

def align(qs, ps):
    for i in range(1, len(qs)):
        c = np.vdot(qs[i-1], qs[i])
        ph = c/abs(c)
        qs[i] = qs[i]/ph
        ps[i] = ps[i]/ph
    return qs, ps

def cquad(lam, G20, G11, G02):
    TR = 3
    def pmul(a, b):
        r = {}
        for ka, va in a.items():
            for kb, vb in b.items():
                k = (ka[0]+kb[0], ka[1]+kb[1])
                if k[0]+k[1] > TR:
                    continue
                r[k] = r.get(k, 0) + va*vb
        return r
    def padd(a, b):
        r = dict(a)
        for k, v in b.items():
            r[k] = r.get(k, 0) + v
        return r
    def pscale(a, c):
        return {k: v*c for k, v in a.items()}
    def conj2(a):
        return {(k[1], k[0]): np.conj(v) for k, v in a.items()}
    def dz(a):
        r = {}
        for (j, k), v in a.items():
            if j > 0:
                r[(j-1, k)] = r.get((j-1, k), 0) + j*v
        return r
    def dzb(a):
        r = {}
        for (j, k), v in a.items():
            if k > 0:
                r[(j, k-1)] = r.get((j, k-1), 0) + k*v
        return r
    def transform(gcur, j, k, phi):
        T = {(1, 0): 1.0, (j, k): phi}
        G = dict(gcur)
        for _ in range(4):
            gT = {}
            for (a2, b2), v in gcur.items():
                term = {(0, 0): v}
                for _ in range(a2):
                    term = pmul(term, T)
                Tb = conj2(T)
                for _ in range(b2):
                    term = pmul(term, Tb)
                for kk, vv in term.items():
                    gT[kk] = gT.get(kk, 0) + vv
            Gb = conj2(G)
            r_ = padd(pscale({kk: vv for kk, vv in T.items()
                              if kk != (1, 0)}, lam), gT)
            r_ = padd(r_, pscale(pmul(
                {kk: vv for kk, vv in dz(T).items() if kk != (0, 0)},
                padd({(1, 0): lam}, G)), -1))
            r_ = padd(r_, pscale(pmul(
                dzb(T), padd({(0, 1): np.conj(lam)}, Gb)), -1))
            G = {kk: vv for kk, vv in r_.items() if sum(kk) >= 2}
        return G
    g = {(2, 0): G20/2, (1, 1): G11, (0, 2): G02/2}
    for (j, k) in ((2, 0), (1, 1), (0, 2)):
        den = j*lam + k*np.conj(lam) - lam
        g = transform(g, j, k, g[(j, k)]/den)
    return g.get((2, 1), 0.0)

CASES = [
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
    y1s_all = np.zeros((n, 4))
    g20s = np.zeros(n, complex); g11s = np.zeros(n, complex)
    g02s = np.zeros(n, complex); c3s = np.zeros(n, complex)
    Gsa = np.zeros(n, complex); Gsb = np.zeros(n, complex)
    Gs0 = np.zeros(n, complex)
    Bfuncs = []
    for i in range(n):
        pri = dict(pr, V=Vg[i])
        av = _avl(sts[i], pri)
        def B2c(u, v, av=av):
            return np.array([sum(_Hl[ii][j][kk](*av)*u[j]*v[kk]
                                 for j in range(4) for kk in range(4))
                             for ii in range(4)])
        Bfuncs.append(B2c)
        qi, pi = qs[i], ps[i]
        g20s[i] = np.vdot(pi, B2c(qi, qi))
        g11s[i] = np.vdot(pi, B2c(qi, np.conj(qi)))
        g02s[i] = np.vdot(pi, B2c(np.conj(qi), np.conj(qi)))
        Ai = jac(sts[i], pri)
        w = st_V[i].astype(complex)
        Pw = w - qi*np.vdot(pi, w) - np.conj(qi)*np.vdot(np.conj(pi), w)
        y1 = np.real(np.linalg.solve(Ai, Pw))
        y1s_all[i] = y1
        Gsa[i] = np.vdot(pi, B2c(y1, qi))
        Gsb[i] = np.vdot(pi, B2c(y1, np.conj(qi)))
        Gs0[i] = 0.5*np.vdot(pi, B2c(y1, y1)) + np.vdot(p_V[i], y1)
        c3s[i] = c1s[i] - cquad(lams[i], g20s[i], g11s[i], g02s[i])
    # second-order lag vectors and couplings
    y1s_V = np.gradient(y1s_all, dV, axis=0)
    G2a = np.zeros(n, complex); G2b = np.zeros(n, complex)
    G3a = np.zeros(n, complex); G3b = np.zeros(n, complex)
    P2 = np.zeros(n, complex); P3 = np.zeros(n, complex)
    for i in range(n):
        pri = dict(pr, V=Vg[i])
        Ai = jac(sts[i], pri)
        y2 = np.linalg.solve(Ai, y1s_all[i])
        y2b = np.linalg.solve(Ai, y1s_V[i])
        B2c = Bfuncs[i]
        qi, pi = qs[i], ps[i]
        G2a[i] = np.vdot(pi, B2c(y2, qi))     # coeff of Vdd*z
        G2b[i] = np.vdot(pi, B2c(y2, np.conj(qi)))
        G3a[i] = np.vdot(pi, B2c(y2b, qi))    # coeff of Vd^2*z
        G3b[i] = np.vdot(pi, B2c(y2b, np.conj(qi)))
        P2[i] = np.vdot(p_V[i], y2)           # forcing Vdd*Vd corr
        P3[i] = np.vdot(p_V[i], y2b)
    i0 = n//2
    out(f"{case['tag']}: |G2a|={abs(G2a[i0]):.2f} |G3a|={abs(G3a[i0]):.2f}"
        f" |P2|={abs(P2[i0]):.2f} [{time.time()-T0:.0f}s]")
    _spl = {}
    def itp(arr, V):
        key = id(arr)
        if key not in _spl:
            _spl[key] = (CubicSpline(Vg, arr.real),
                         CubicSpline(Vg, arr.imag))
        V = min(max(V, Vg[0]), Vg[-1])
        sr, si = _spl[key]
        return complex(sr(V), si(V))
    ws = w0/32
    Tt1 = 12*2*math.pi/ws
    def escape1d(a, model):
        def f(t, y):
            z = y[0] + 1j*y[1]
            zb = np.conj(z)
            V = pr['V'] - a*math.sin(ws*t)
            Vd = -a*ws*math.cos(ws*t)
            Vdd = a*ws*ws*math.sin(ws*t)
            dz = (itp(lams, V)*z - itp(pstV, V)*Vd
                  - itp(pqV, V)*Vd*z + itp(pVqb, V)*Vd*zb
                  + itp(Gsa, V)*Vd*z + itp(Gsb, V)*Vd*zb
                  + itp(Gs0, V)*Vd*Vd)
            if '2' in model:
                dz += (-itp(G2a, V)*Vdd*z - itp(G2b, V)*Vdd*zb
                       - itp(G3a, V)*Vd*Vd*z - itp(G3b, V)*Vd*Vd*zb
                       - itp(P2, V)*Vdd*Vd - itp(P3, V)*Vd*Vd*Vd)
            if model.startswith('A'):
                dz += itp(c1s, V)*abs(z)**2*z
            else:
                dz += (0.5*itp(g20s, V)*z*z + itp(g11s, V)*z*zb
                       + 0.5*itp(g02s, V)*zb*zb
                       + itp(c3s, V)*abs(z)**2*z)
            return [dz.real, dz.imag]
        def blow(t, y):
            return math.hypot(y[0], y[1]) - 5*zg
        blow.terminal = True; blow.direction = 1
        s = solve_ivp(f, (0, Tt1), [0.0, 0.0], method='DOP853',
                      rtol=1e-10, atol=1e-14, events=blow)
        return len(s.t_events[0]) > 0
    meas = MEAS[case['tag']]
    line = f"  {case['tag']} w0/32: meas={meas:.4e}"
    for model in ('A', 'A2', 'B', 'B2'):
        alo, ahi = 1e-6, AH
        if not escape1d(ahi, model):
            line += f"  {model}:noesc"
            continue
        for _ in range(14):
            am = 0.5*(alo+ahi)
            if escape1d(am, model): ahi = am
            else: alo = am
        ap = 0.5*(alo+ahi)
        line += f"  {model}:{(ap-meas)/meas*100:+.1f}%"
    out(line + f" [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
