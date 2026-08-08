"""Slot F, 5 fresh parameter sets per converter (co-moving-frame 1D
reduction, rates2 machinery generalized).
GFL: predict a_c at ws = w0/160 and w0/32 (slow band), measure with
     nper=12 window.  GFM: predict max|om| at ws = w0/100 for dips
     {1.5, 3.0} x margin, measure from 4D simulation.
Usage: python f5.py {gfl|gfm}
"""
import sys
WHICH = sys.argv[1]
import time, os
os.makedirs('sweep20', exist_ok=True)
LOG = open(f'sweep20/f5-{WHICH}.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
import math, numpy as np
from scipy.integrate import solve_ivp

def align(qs, ps):
    for i in range(1, len(qs)):
        c = np.vdot(qs[i-1], qs[i])
        ph = c/abs(c)
        qs[i] = qs[i]/ph
        ps[i] = ps[i]/ph
    return qs, ps

if WHICH == 'gfl':
    exec(open('selfhead.py').read())
    CASES = [
        dict(tag='Xg=0.70',  over=dict(Xg=0.70), marg=0.10),
        dict(tag='C=0.02',   over=dict(C=0.02), marg=0.10),
        dict(tag='mix16',    over=dict(kp=45., ki=900., Xg=0.55), marg=0.10),
        dict(tag='Q=+0.15',  over=dict(Q=0.15), marg=0.10),
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
        out(f"{case['tag']}: P={P:.5f} alpha={co0['alpha']:.4f} "
            f"w0={w0:.3f} zg={zg:.4e}")
        # adaptive grid: stay inside the equilibrium-existence range
        vlo, vhi = pr['V'] - 0.05, pr['V']
        for _ in range(30):
            vm = 0.5*(vlo+vhi)
            if equil(dict(pr, V=vm)) is None: vlo = vm
            else: vhi = vm
        Vmin = vhi
        AH = min(0.012, 0.85*(pr['V'] - Vmin))
        out(f"  equil edge V_min={Vmin:.5f} -> amplitude cap AH={AH:.4e}")
        Vg = pr['V'] + np.linspace(-1.05*AH, 1.05*AH, 181)
        sts, lams, c1s, qs, ps = [], [], [], [], []
        okgrid = True
        for V in Vg:
            try:
                co = nf_coeffs(dict(pr, V=V))
            except Exception:
                okgrid = False; break
            sts.append(co['st']); lams.append(co['lam'])
            c1s.append(co['c1']); qs.append(co['q']); ps.append(co['p'])
        if not okgrid:
            out("  V-grid nf_coeffs failed — skip"); continue
        qs, ps = align(qs, ps)
        sts = np.array(sts); lams = np.array(lams); c1s = np.array(c1s)
        qs = np.array(qs); ps = np.array(ps)
        dV = Vg[1] - Vg[0]
        st_V = np.gradient(sts, dV, axis=0)
        q_V = np.gradient(qs, dV, axis=0)
        pstV = np.array([np.vdot(ps[i], st_V[i]) for i in range(len(Vg))])
        pqV = np.array([np.vdot(ps[i], q_V[i]) for i in range(len(Vg))])
        from scipy.interpolate import CubicSpline
        _spl = {}
        def itp(arr, V):
            key = id(arr)
            if key not in _spl:
                _spl[key] = (CubicSpline(Vg, arr.real),
                             CubicSpline(Vg, arr.imag))
            V = min(max(V, Vg[0]), Vg[-1])
            sr, si = _spl[key]
            return complex(sr(V), si(V))
        def fateF(a, ws, nper=12):
            def f(t, x):
                qq = dict(pr, V=pr['V'] - a*math.sin(ws*t))
                return rhs(x, qq)
            def blow(t, x): return abs(x[0] - st0[0]) - 1.2
            blow.terminal = True; blow.direction = 1
            Tt = nper*2*math.pi/ws
            s = solve_ivp(f, (0, Tt), st0.copy(), method='DOP853',
                          rtol=1e-9, atol=1e-12, events=blow)
            return len(s.t_events[0]) > 0
        for ws in (w0/160, w0/32):
            Tt1 = 12*2*math.pi/ws
            def escape1d(a):
                def f(t, y):
                    z = y[0] + 1j*y[1]
                    V = pr['V'] - a*math.sin(ws*t)
                    Vd = -a*ws*math.cos(ws*t)
                    dz = (itp(lams, V)*z - itp(pstV, V)*Vd
                          - itp(pqV, V)*Vd*z + itp(c1s, V)*abs(z)**2*z)
                    return [dz.real, dz.imag]
                def blow(t, y):
                    return math.hypot(y[0], y[1]) - 5*zg
                blow.terminal = True; blow.direction = 1
                s = solve_ivp(f, (0, Tt1), [0.0, 0.0], method='DOP853',
                              rtol=1e-10, atol=1e-14, events=blow)
                return len(s.t_events[0]) > 0
            alo, ahi = 1e-6, AH
            if not escape1d(ahi):
                out(f"  ws={ws:.3f}: 1D no escape at AH={AH:.3e}"); continue
            for _ in range(14):
                am = 0.5*(alo+ahi)
                if escape1d(am): ahi = am
                else: alo = am
            ap = 0.5*(alo+ahi)
            alo, ahi = 1e-6, AH
            if not fateF(ahi, ws):
                out(f"  ws={ws:.3f}: 4D no escape at AH={AH:.3e}"); continue
            for _ in range(13):
                am = 0.5*(alo+ahi)
                if fateF(am, ws): ahi = am
                else: alo = am
            ameas = 0.5*(alo+ahi)
            out(f"  RESULT {case['tag']} ws={ws:.3f} (w0/{w0/ws:.0f}): "
                f"pred={ap:.4e} meas={ameas:.4e} "
                f"err={(ap-ameas)/ameas*100:+.1f}%")
    out(f"DONE wall={time.time()-T0:.0f}s")

else:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                        mset, fold, hopf_c1)
    def build(name, Xg):
        pr = mset(name, Xg=Xg)
        dfold, Pm = fold(pr)
        q = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
        if q is None:
            return None
        P_H = q['Pref']
        def g(P):
            r = maxre_cx(dict(pr, Pref=P))
            return 1.0 if r is None else r
        Phi_ = min(0.95*Pm, 2.5*P_H)
        tt = 0.10
        if g(Phi_) > -tt:
            tt = max(0.3*abs(g(Phi_)), 0.02)
        lo2, hi2 = P_H, Phi_
        for _ in range(45):
            m = 0.5*(lo2+hi2)
            if g(m) > -tt: lo2 = m
            else: hi2 = m
        return dict(pr=pr, P_H=P_H, P0=0.5*(lo2+hi2))
    CAND = [('M3', 0.10), ('M4', 0.10), ('M3', 0.05), ('M4', 0.05),
            ('M1', 0.05), ('M5', 0.10), ('M1', 0.15), ('M2', 0.03)]
    ndone = 0
    for name, Xg in CAND:
        if ndone >= 5:
            break
        b = build(name, Xg)
        if b is None:
            out(f"{name}@Xg={Xg}: no window — skip")
            continue
        ndone += 1
        pr0, P_H, P0 = b['pr'], b['P_H'], b['P0']
        dP = P0 - P_H
        prm = dict(pr0, Pref=P0)
        st = equil(prm)
        lam0 = crit_mode(jac(st, prm))
        w0 = lam0.imag
        out(f"{name}@Xg={Xg}: P_H={P_H:.4f} P0={P0:.4f} dP={dP:.4f} "
            f"w0={w0:.3f}")
        Pmin = 0.06*P_H
        Pg = np.linspace(max(Pmin, P0-3.4*dP), P0+0.25*dP, 47)
        sts, lams, c1s, qs, ps = [], [], [], [], []
        okg = True
        for Pq in Pg:
            try:
                co = hopf_c1(dict(pr0, Pref=Pq))
            except Exception:
                okg = False; break
            sts.append(co['st']); lams.append(co['lam'])
            c1s.append(co['c1']); qs.append(co['q']); ps.append(co['p'])
        if not okg:
            out("  P-grid hopf_c1 failed — skip"); continue
        qs, ps = align(qs, ps)
        sts = np.array(sts); lams = np.array(lams); c1s = np.array(c1s)
        qs = np.array(qs); ps = np.array(ps)
        dPg = Pg[1] - Pg[0]
        st_P = np.gradient(sts, dPg, axis=0)
        q_P = np.gradient(qs, dPg, axis=0)
        pstP = np.array([np.vdot(ps[i], st_P[i]) for i in range(len(Pg))])
        pqP = np.array([np.vdot(ps[i], q_P[i]) for i in range(len(Pg))])
        def itpC(arr, Pq):
            Pq = min(max(Pq, Pg[0]), Pg[-1])
            return complex(np.interp(Pq, Pg, arr.real),
                           np.interp(Pq, Pg, arr.imag))
        def itpq(Pq):
            Pq = min(max(Pq, Pg[0]), Pg[-1])
            return complex(np.interp(Pq, Pg, qs[:, 1].real),
                           np.interp(Pq, Pg, qs[:, 1].imag))
        ws = w0/100
        for fdip in (1.5, 3.0):
            a = fdip*dP
            Tt = 2*2*math.pi/ws
            def f1(t, y):
                z = y[0] + 1j*y[1]
                Pq = P0 - a*math.sin(ws*t)
                Pd = -a*ws*math.cos(ws*t)
                dz = (itpC(lams, Pq)*z - itpC(pstP, Pq)*Pd
                      - itpC(pqP, Pq)*Pd*z + itpC(c1s, Pq)*abs(z)**2*z)
                return [dz.real, dz.imag]
            s1 = solve_ivp(f1, (0, Tt), [0.0, 0.0], method='DOP853',
                           rtol=1e-9, atol=1e-13, dense_output=True)
            tt2 = np.linspace(0, Tt, 4000)
            ys = s1.sol(tt2)
            zs = ys[0] + 1j*ys[1]
            oms = np.array([2*(zs[i]*itpq(P0 - a*math.sin(ws*tt2[i]))).real
                            for i in range(len(tt2))])
            pred = float(np.max(np.abs(oms)))
            def f4(t, x):
                return rhs(x, dict(pr0, Pref=P0 - a*math.sin(ws*t)))
            s4 = solve_ivp(f4, (0, Tt), st + np.array([1e-5, 0, 0, 0]),
                           method='DOP853', rtol=1e-9, atol=1e-12,
                           dense_output=True)
            y4 = s4.sol(tt2)
            meas = float(np.max(np.abs(y4[1])))
            out(f"  RESULT {name}@Xg={Xg} ws={ws:.3f} dip={fdip}: "
                f"pred={pred:.4f} meas={meas:.4f} "
                f"err={(pred-meas)/meas*100:+.1f}%")
    out(f"DONE wall={time.time()-T0:.0f}s")
