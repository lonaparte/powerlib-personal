"""Slow-band P/Q cells.
(1) P-GFL (G1 marg0.10): path P(t)=P0+a sin(ws t) toward Hopf;
    1D amplitude equation on P-grid vs 4D compound-detector fate,
    ws = w0/160 and w0/32, matched 12-period windows.
(2) Q-GFL (G1): alpha(Q) curve on |Q|<=0.4; threshold if a boundary
    crossing exists in range, else max-response check at cap.
(3) Q-GFM (M1@0.10): slow Qref response prediction vs 4D
    (ws=w0/100, a in {0.05,0.15}), rates2-style.
Budget ~20 min.
"""
exec(open('selfhead.py').read())
import time, sys, os
LOG = open('sweep20/pqslow.log', 'w')
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

# ---------- (1) P-GFL ----------
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
dsad = math.pi - 2*abs(st0[0])
Dl = PH - P0
AH = min(2.2*Dl, 0.98*Psn - P0)
out(f"P-GFL G1: P0={P0:.5f} PH={PH:.5f} Delta={Dl:.4e} AH={AH:.4e} "
    f"w0={w0:.3f} zg={zg:.3e}")
Pg = P0 + np.linspace(-1.05*AH, 1.05*AH, 181)
sts, lams, c1s, qs, ps = [], [], [], [], []
okg = True
for Pq in Pg:
    try:
        co = nf_coeffs(dict(pr, P=Pq))
    except Exception:
        okg = False; break
    sts.append(co['st']); lams.append(co['lam'])
    c1s.append(co['c1']); qs.append(co['q']); ps.append(co['p'])
if not okg:
    out("  P-grid failed")
else:
    qs, ps = align(qs, ps)
    sts = np.array(sts); lams = np.array(lams); c1s = np.array(c1s)
    qs = np.array(qs); ps = np.array(ps)
    dP = Pg[1] - Pg[0]
    st_P = np.gradient(sts, dP, axis=0)
    q_P = np.gradient(qs, dP, axis=0)
    p_V = np.gradient(ps, dP, axis=0)
    n = len(Pg)
    pstP = np.array([np.vdot(ps[i], st_P[i]) for i in range(n)])
    pqP = np.array([np.vdot(ps[i], q_P[i]) for i in range(n)])
    pVqb = np.array([np.vdot(p_V[i], np.conj(qs[i])) for i in range(n)])
    _spl = {}
    def itp(arr, Pq):
        key = id(arr)
        if key not in _spl:
            _spl[key] = (CubicSpline(Pg, arr.real),
                         CubicSpline(Pg, arr.imag))
        Pq = min(max(Pq, Pg[0]), Pg[-1])
        sr, si = _spl[key]
        return complex(sr(Pq), si(Pq))
    for ws in (w0/160, w0/32):
        Tt1 = 12*2*math.pi/ws
        def escape1d(a):
            def f(t, y):
                z = y[0] + 1j*y[1]
                zb = np.conj(z)
                Pq = P0 + a*math.sin(ws*t)
                Pd = a*ws*math.cos(ws*t)
                dz = (itp(lams, Pq)*z - itp(pstP, Pq)*Pd
                      - itp(pqP, Pq)*Pd*z + itp(pVqb, Pq)*Pd*zb
                      + itp(c1s, Pq)*abs(z)**2*z)
                return [dz.real, dz.imag]
            def blow(t, y):
                return math.hypot(y[0], y[1]) - 5*zg
            blow.terminal = True; blow.direction = 1
            s = solve_ivp(f, (0, Tt1), [0.0, 0.0], method='DOP853',
                          rtol=1e-10, atol=1e-14, events=blow)
            return len(s.t_events[0]) > 0
        def fate4(a):
            def f(t, x):
                return rhs(x, dict(pr, P=P0 + a*math.sin(ws*t)))
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
            out(f"  ws=w0/{w0/ws:.0f}: 1D no escape at AH"); continue
        for _ in range(14):
            am = 0.5*(alo+ahi)
            if escape1d(am): ahi = am
            else: alo = am
        ap = 0.5*(alo+ahi)
        alo, ahi = 1e-4*AH, AH
        if not fate4(ahi):
            out(f"  ws=w0/{w0/ws:.0f}: 4D no escape at AH"); continue
        for _ in range(13):
            am = 0.5*(alo+ahi)
            if fate4(am): ahi = am
            else: alo = am
        ameas = 0.5*(alo+ahi)
        out(f"  RESULT P-GFL ws=w0/{w0/ws:.0f}: pred={ap:.4e} "
            f"meas={ameas:.4e} err={(ap-ameas)/ameas*100:+.1f}% "
            f"[{time.time()-T0:.0f}s]")

# ---------- (2) Q-GFL alpha(Q) curve ----------
Qg = np.linspace(-0.4, 0.4, 41)
avals = []
for Qq in Qg:
    x = equil(dict(pr, Q=Qq))
    if x is None:
        avals.append(None); continue
    cm = crit_mode(jac(x, dict(pr, Q=Qq)))
    avals.append(None if cm is None else -cm.real)
amin = min((a for a in avals if a is not None), default=None)
across = any(a is not None and a <= 0 for a in avals)
out(f"Q-GFL G1: alpha(Q) on |Q|<=0.4: min={amin:.4f} "
    f"crossing={'yes' if across else 'no'} "
    f"alpha(0)={avals[20]:.4f} alpha(+0.4)={avals[-1]}"
    f" alpha(-0.4)={avals[0]}")
if not across:
    ws = w0/32
    Tt1 = 12*2*math.pi/ws
    aQ = 0.4
    def f(t, x):
        return rhs(x, dict(pr, Q=aQ*math.sin(ws*t)))
    def e_th(t, x): return abs(x[0] - st0[0]) - 1.2
    e_th.terminal = True; e_th.direction = 1
    def e_vlo(t, x): return x[2] - 0.2
    e_vlo.terminal = True; e_vlo.direction = -1
    s = solve_ivp(f, (0, Tt1), st0.copy(), method='DOP853',
                  rtol=1e-9, atol=1e-12, events=(e_th, e_vlo),
                  dense_output=True)
    esc = any(len(t) > 0 for t in s.t_events) or s.status < 0
    if esc:
        out(f"  Q slow a=0.4 ws=w0/32: ESCAPE (unexpected — "
            f"crossing-free path escaped) [{time.time()-T0:.0f}s]")
    else:
        tt2 = np.linspace(0, Tt1, 4000)
        xa = s.sol(tt2)
        out(f"  Q slow a=0.4 ws=w0/32: bounded; max|dth|="
            f"{np.max(np.abs(xa[0]-st0[0])):.4f} "
            f"max|dVdc|={np.max(np.abs(xa[2]-1)):.4f} — no escape, "
            f"consistent with no boundary in range "
            f"[{time.time()-T0:.0f}s]")

# ---------- (3) Q-GFM slow response ----------
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gfmlib as G
from scipy.linalg import eig as _eig
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
lamg = G.crit_mode(G.jac(stg, prg))
w0g = lamg.imag
out(f"Q-GFM M1@0.10: P0={P0g:.4f} w0={w0g:.3f}")
Qg2 = np.linspace(-0.25, 0.25, 61)
stsg, lamsg, qsg, psg = [], [], [], []
okg = True
for Qq in Qg2:
    prq = dict(prg, Qref=Qq)
    x = G.equil(prq)
    if x is None:
        okg = False; break
    A = G.jac(x, prq)
    lam = G.crit_mode(A)
    ev, VL, VR = _eig(A, left=True, right=True)
    k = int(np.argmin(np.abs(ev - lam)))
    qv = VR[:, k]; pv = VL[:, k]
    pv = pv/np.vdot(qv, pv)
    stsg.append(x); lamsg.append(lam); qsg.append(qv); psg.append(pv)
if not okg:
    out("  Qref grid failed")
else:
    qsg, psg = align(qsg, psg)
    stsg = np.array(stsg); lamsg = np.array(lamsg)
    qsg = np.array(qsg); psg = np.array(psg)
    dQ = Qg2[1] - Qg2[0]
    st_Q = np.gradient(stsg, dQ, axis=0)
    q_Q = np.gradient(qsg, dQ, axis=0)
    pstQ = np.array([np.vdot(psg[i], st_Q[i]) for i in range(len(Qg2))])
    pqQ = np.array([np.vdot(psg[i], q_Q[i]) for i in range(len(Qg2))])
    def itpC(arr, Qq):
        Qq = min(max(Qq, Qg2[0]), Qg2[-1])
        return complex(np.interp(Qq, Qg2, arr.real),
                       np.interp(Qq, Qg2, arr.imag))
    def itpq(Qq):
        Qq = min(max(Qq, Qg2[0]), Qg2[-1])
        return complex(np.interp(Qq, Qg2, qsg[:, 1].real),
                       np.interp(Qq, Qg2, qsg[:, 1].imag))
    ws = w0g/100
    for aQ in (0.05, 0.15):
        Tt = 2*2*math.pi/ws
        def f1(t, y):
            z = y[0] + 1j*y[1]
            Qq = aQ*math.sin(ws*t)
            Qd = aQ*ws*math.cos(ws*t)
            dz = (itpC(lamsg, Qq)*z - itpC(pstQ, Qq)*Qd
                  - itpC(pqQ, Qq)*Qd*z)
            return [dz.real, dz.imag]
        s1 = solve_ivp(f1, (0, Tt), [0.0, 0.0], method='DOP853',
                       rtol=1e-9, atol=1e-13, dense_output=True)
        tt2 = np.linspace(0, Tt, 4000)
        ys = s1.sol(tt2)
        zs = ys[0] + 1j*ys[1]
        oms = np.array([2*(zs[i]*itpq(aQ*math.sin(ws*tt2[i]))).real
                        for i in range(len(tt2))])
        pred = float(np.max(np.abs(oms)))
        def f4(t, x):
            return G.rhs(x, dict(prg, Qref=aQ*math.sin(ws*t)))
        s4 = solve_ivp(f4, (0, Tt), stg + np.array([1e-5, 0, 0, 0]),
                       method='DOP853', rtol=1e-9, atol=1e-12,
                       dense_output=True)
        meas = float(np.max(np.abs(s4.sol(tt2)[1])))
        out(f"  RESULT Q-GFM ws=w0/100 a={aQ}: pred={pred:.5f} "
            f"meas={meas:.5f} err={(pred-meas)/meas*100:+.1f}% "
            f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
