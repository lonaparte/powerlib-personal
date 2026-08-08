"""Rate-effect (slot F) mechanistic reduction and check.
GFL: 1D reduced modal ODE with frozen-eigenvalue path and slow forcing:
    zdot = lam(V(t)) z + c1 |z|^2 z + fcoef * dV(t),  dV = -a sin(ws t)
  (all coefficients computed from the model; no fitting)
  a_c^pred(ws) = smallest a with finite escape (|z| > 5 zg) in 3 periods.
GFM: slow Pref crossing of P_H decomposed as tracking + slow-passage mode:
    max|om| ~ a ws (d delta_eq/dP)  +  2|q_om| r_max,
    rdot = Re lam(P(t)) r - |Re c1| r^3, r(0) = modal tracking lag.
Usage: python rates.py {gfl|gfm}
"""
import sys
WHICH = sys.argv[1]
import time, os
os.makedirs('sweep20', exist_ok=True)
LOG = open(f'sweep20/rates-{WHICH}.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

if WHICH == 'gfl':
    exec(open('selfhead.py').read())
    pr0 = gset('G1', Xg=0.5)
    lo, hi = 0.9, 1.4775
    def g0(P):
        x = equil(dict(pr0, P=P))
        return crit_mode(jac(x, dict(pr0, P=P))).real
    for _ in range(45):
        m = 0.5*(lo+hi)
        if g0(m) < 0: lo = m
        else: hi = m
    PH = 0.5*(lo+hi)
    P = margin_point(pr0, PH, 0.10)
    pr = dict(pr0, P=P)
    co = nf_coeffs(pr)
    st = co['st']; alpha = co['alpha']; w0 = co['w0']
    c1v = co['c1']; fc = co['fcoef']
    zg = math.sqrt(alpha/c1v.real)
    out(f"P={P:.5f} alpha={alpha:.4f} w0={w0:.4f} c1={c1v:.1f} "
        f"fcoef={fc:.3f} zg={zg:.4e}")
    # frozen eigenvalue path lam(V) on a dense local grid
    amax = 4.5e-3
    Vg = 1.0 + np.linspace(-1.25*amax, 1.25*amax, 41)
    lams = []
    for V in Vg:
        q = dict(pr, V=V)
        x = equil(q)
        lams.append(crit_mode(jac(x, q)))
    lams = np.array(lams)
    out(f"lam(V) range: Re [{lams.real.min():.3f}, {lams.real.max():.3f}]")
    def lamV(V):
        return complex(np.interp(V, Vg, lams.real),
                       np.interp(V, Vg, lams.imag))
    MEAS = {0.2: 4.227e-4, 1.0: 1.274e-3, 5.0: 3.163e-3}
    for ws in (0.2, 1.0, 5.0):
        Tt = 3*2*math.pi/ws
        def escape1d(a):
            def f(t, y):
                z = y[0] + 1j*y[1]
                V = 1.0 - a*math.sin(ws*t)
                dz = (lamV(V)*z + c1v*abs(z)**2*z + fc*(-a*math.sin(ws*t)))
                return [dz.real, dz.imag]
            def blow(t, y):
                return math.hypot(y[0], y[1]) - 5*zg
            blow.terminal = True; blow.direction = 1
            s = solve_ivp(f, (0, Tt), [0.0, 0.0], method='DOP853',
                          rtol=1e-10, atol=1e-14, events=blow)
            return len(s.t_events[0]) > 0
        alo, ahi = 1e-5, 0.02
        if not escape1d(ahi):
            out(f"  ws={ws}: 1D no escape at a=0.02"); continue
        for _ in range(14):
            am = 0.5*(alo+ahi)
            if escape1d(am): ahi = am
            else: alo = am
        ap = 0.5*(alo+ahi)
        ms = MEAS[ws]
        out(f"  RESULT ws={ws}: a_pred={ap:.4e} a_meas={ms:.4e} "
            f"err={(ap-ms)/ms*100:+.1f}%")
    out(f"DONE wall={time.time()-T0:.0f}s")

else:
    import math, numpy as np
    from scipy.integrate import solve_ivp
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                        mset, fold, hopf_c1)
    pr = mset('M1', Xg=0.10)
    dfold, Pm = fold(pr)
    q = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
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
    P0 = 0.5*(lo2+hi2)
    prm = dict(pr, Pref=P0)
    st = equil(prm)
    lam0 = crit_mode(jac(st, prm))
    dP = P0 - P_H
    hc = hopf_c1(q)          # c1 and eigvecs at the Hopf crossing
    c1H = hc['c1']; qH = hc['q']
    out(f"M1: P_H={P_H:.4f} P0={P0:.4f} dP={dP:.4f} "
        f"lam0={lam0:.4f} c1(PH)={c1H:.2f} |q_om|={abs(qH[1]):.3f}")
    # lam(P) and delta_eq(P), modal lag vector on the swept range
    Pg = np.linspace(P0 - 3.2*dP, P0 + 0.2*dP, 41)
    lams, deltas = [], []
    for Pq in Pg:
        prq = dict(pr, Pref=Pq)
        x = equil(prq)
        lams.append(crit_mode(jac(x, prq)))
        deltas.append(x[0])
    lams = np.array(lams); deltas = np.array(deltas)
    def relamP(Pq): return float(np.interp(Pq, Pg, lams.real))
    dddP = float(np.gradient(deltas, Pg).mean())
    h = 1e-4
    xp = equil(dict(pr, Pref=P0+h)); xm = equil(dict(pr, Pref=P0-h))
    dxdP = (xp - xm)/(2*h)
    pH = hc['p']
    zlag_coef = abs(np.vdot(pH, dxdP))/abs(lam0)
    out(f"d delta_eq/dP = {dddP:.4f}  |<p,dx/dP>|/|lam| = {zlag_coef:.4f}")
    MEAS = {(0.1, 0.5): 0.0060, (0.1, 1.5): 0.0179, (0.1, 3.0): 0.0416,
            (0.5, 0.5): 0.0299, (0.5, 1.5): 0.0897, (0.5, 3.0): 0.1847}
    for ws in (0.1, 0.5):
        for fdip in (0.5, 1.5, 3.0):
            a = fdip*dP
            om_track = a*ws*abs(dddP)
            r0 = zlag_coef*a*ws
            Tt = 2*2*math.pi/ws
            def f(t, y):
                Pq = P0 - a*math.sin(ws*t)
                Pq = min(max(Pq, Pg[0]), Pg[-1])
                return [relamP(Pq)*y[0] - abs(c1H.real)*y[0]**3]
            s = solve_ivp(f, (0, Tt), [r0], method='DOP853', rtol=1e-9,
                          atol=1e-14)
            rmax = float(np.max(s.y[0]))
            om_mode = 2*abs(qH[1])*rmax
            pred = om_track + om_mode
            ms = MEAS[(ws, fdip)]
            out(f"  RESULT ws={ws} dip={fdip}: track={om_track:.4f} "
                f"mode={om_mode:.4f} pred={pred:.4f} meas={ms:.4f} "
                f"err={(pred-ms)/ms*100:+.1f}%")
    out(f"DONE wall={time.time()-T0:.0f}s")
