"""Three closures in one guarded script (modes via argv):
  map : S1-S2 interaction map at G1 marg0.1 — locked-orbit fold/PD/NS
        vs r in [0.95, 1.05] (does the response fold (S2) appear before
        the basin event near resonance?) + compound sudden-on threshold
        at 4 r values.
  hh  : locate the Hopf-Hopf codim-2 point (both complex pairs
        simultaneously marginal) near the V-handover of G1@Xg=0.5.
  egfm: E-GFM second-order fix — replace the energy-superposition
        shortcut with the full BVP profile prediction started from the
        forced pre-kick state; test on the worst case M5@Xg=0.10
        (old errors +2.9/+9.3/-4.0/+2.9%).
Usage: python round9.py {map|hh|egfm}
"""
import sys
MODE = sys.argv[1]
import time, os
os.makedirs('sweep20', exist_ok=True)
LOG = open(f'sweep20/round9-{MODE}.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

if MODE in ('map', 'hh'):
    exec(open('selfhead.py').read())
    _Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
            for j in range(4)] for i in range(4)]
    def jac_a(x, prm):
        a = _avl(x, prm)
        return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                         for i in range(4)])

if MODE == 'map':
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
    st = co['st']; w0 = co['w0']
    dsad = math.pi - 2*abs(st[0])
    def strobe_var(x0, eps, wd, Td):
        def f(t, y):
            x = y[:4]
            qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, qq), (jac_a(x, qq) @ Phi).ravel()])
        y0 = np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11,
                      atol=1e-13)
        return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
    def newton_fp(xg, eps, wd, Td, itmax=25):
        x = xg.copy(); M = None
        for it in range(itmax):
            xT, M = strobe_var(x, eps, wd, Td)
            Fx = xT - x
            if np.max(np.abs(Fx)) < 1e-10:
                return x, M, True
            try:
                dx = np.linalg.solve(M - np.eye(4), -Fx)
            except np.linalg.LinAlgError:
                return x, M, False
            n = np.max(np.abs(dx))
            if n > 0.3:
                dx *= 0.3/n
            x = x + dx
        return x, M, np.max(np.abs(Fx)) < 1e-8
    def probe(eps, wd, T=250):
        def f(t, x):
            qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
            return rhs(x, qq)
        def e_th(t, x): return abs(x[0] - st[0]) - min(1.2, dsad)
        def e_vlo(t, x): return x[2] - 0.2
        def e_vhi(t, x): return x[2] - 2.5
        e_th.terminal = True; e_th.direction = 1
        e_vlo.terminal = True; e_vlo.direction = -1
        e_vhi.terminal = True; e_vhi.direction = 1
        s = solve_ivp(f, (0, T), st.copy(), method='DOP853', rtol=1e-9,
                      atol=1e-12, events=[e_th, e_vlo, e_vhi])
        if any(len(s.t_events[i]) for i in range(3)):
            return False
        if s.status == -1 or s.t[-1] < T - 1:
            return False
        return True
    for rr in (0.95, 0.97, 0.99, 1.00, 1.01, 1.03, 1.05):
        wd = rr*w0
        Td = 2*math.pi/wd
        xL = st.copy()
        eps = 0.0
        deps = 5e-6
        loss = None
        while eps < 5e-4:
            e_try = eps + deps
            xn, Mn, okn = newton_fp(xL.copy(), e_try, wd, Td)
            if not okn:
                loss = ('newton-fail(fold?)', eps)
                break
            mu = np.linalg.eigvals(Mn)
            am = float(np.max(np.abs(mu)))
            k = int(np.argmax(np.abs(mu)))
            if am > 1.0:
                typ = ('fold' if abs(mu[k].imag) < 1e-3 and mu[k].real > 0
                       else 'PD' if abs(mu[k].imag) < 1e-3 else 'NS')
                loss = (typ, e_try)
                break
            xL, eps = xn, e_try
            deps = min(deps*1.4, 4e-5)
        # sudden-on threshold (compound) at this r
        elo, ehi = 1e-6, 5e-4
        if probe(ehi, wd):
            ec = None
        else:
            for _ in range(10):
                em = 0.5*(elo+ehi)
                if probe(em, wd): elo = em
                else: ehi = em
            ec = 0.5*(elo+ehi)
        out(f"r={rr}: locked-orbit loss={loss}  "
            f"sudden-on eps_c={'>5e-4' if ec is None else f'{ec:.4e}'} "
            f"[{time.time()-T0:.0f}s]")
    out(f"DONE wall={time.time()-T0:.0f}s")

elif MODE == 'hh':
    pr0 = gset('G1', Xg=0.5)
    def both_re(P, V):
        prq = dict(pr0, P=P, V=V)
        x = equil(prq)
        if x is None:
            return None
        ev = np.linalg.eigvals(jac(x, prq))
        cx = sorted([e for e in ev if e.imag > 1e-9],
                    key=lambda z: z.imag)
        if len(cx) < 2:
            return None
        return cx[0].real, cx[1].real, cx[0].imag, cx[1].imag
    # for V in a grid, find P where each pair crosses zero (if any)
    out("V, P_H(low mode), P_H(high mode):")
    found = []
    for V in np.linspace(0.995, 1.03, 15):
        rows = []
        for P in np.linspace(1.30, 1.55, 26):
            r = both_re(P, V)
            rows.append((P, r))
        Ph = [None, None]
        for i in (0, 1):
            for (Pa, ra), (Pb, rb) in zip(rows[:-1], rows[1:]):
                if ra is None or rb is None:
                    continue
                if ra[i] < 0 <= rb[i]:
                    lo, hi = Pa, Pb
                    for _ in range(40):
                        m = 0.5*(lo+hi)
                        rm = both_re(m, V)
                        if rm is None or rm[i] >= 0: hi = m
                        else: lo = m
                    Ph[i] = 0.5*(lo+hi)
                    break
        out(f"  V={V:.4f}: PH_low={Ph[0]} PH_high={Ph[1]}")
        if Ph[0] is not None and Ph[1] is not None:
            found.append((V, Ph[0], Ph[1]))
    if found:
        best = min(found, key=lambda t: abs(t[1]-t[2]))
        V, P1, P2 = best
        r = both_re(0.5*(P1+P2), V)
        out(f"RESULT hh: closest approach at V={V:.4f}: "
            f"PH_low={P1:.5f} PH_high={P2:.5f} gap={abs(P1-P2):.2e}; "
            f"freqs {r[2]:.2f}/{r[3]:.2f} rad/s ratio={r[3]/r[2]:.3f}")
    else:
        out("RESULT hh: no V with both boundaries in P-range — "
            f"modes never simultaneously marginal in scanned window")
    out(f"DONE wall={time.time()-T0:.0f}s")

elif MODE == 'egfm':
    import math, numpy as np
    from scipy.integrate import solve_ivp
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                        mset, fold, P_of, escape_event, Enom)
    pr = mset('M5', Xg=0.10)
    dfold, Pm = fold(pr)
    qh = hopf_in(pr, 'Pref', 0.02*Pm, 0.95*Pm)
    P_H = qh['Pref']
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
    prm = dict(pr, Pref=0.5*(lo2+hi2))
    st = equil(prm)
    lam = crit_mode(jac(st, prm))
    w0 = lam.imag
    M, D, wc, mq, V, Xgv = (prm['M'], prm['D'], prm['wc'], prm['mq'],
                            prm['V'], prm['Xg'])
    ev, dsad = escape_event(prm)
    out(f"M5@0.10: P0={prm['Pref']:.4f} w0={w0:.3f} dsad={dsad:.4f}")
    def Pe_of(d, E): return E*V*math.sin(d)/Xgv
    def Qe_of(d, E): return (E*E - E*V*math.cos(d))/Xgv
    def bvp_dw(x0):
        # threshold kick from state x0=(d,om,Pf,Qf): total initial
        # v = om + dw; profiles integrated from d0=x0[0] to dsad
        d0, om0, Pf0, Qf0 = x0
        N = 3000
        dg = np.linspace(d0, dsad, N)
        dd = dg[1] - dg[0]
        def endE(dw):
            v = np.full(N, max(om0 + dw, 1e-3))
            for it in range(22):
                Pf = np.empty(N); Qf = np.empty(N)
                Pf[0] = Pf0; Qf[0] = Qf0
                for n in range(1, N):
                    vn = max(v[n-1], 0.05*(om0+dw))
                    E = Enom - mq*(Qf[n-1] - prm['Qref'])
                    ex = math.exp(-wc*dd/vn)
                    Pf[n] = Pe_of(dg[n], E) + (Pf[n-1] - Pe_of(dg[n], E))*ex
                    Qf[n] = Qe_of(dg[n], E) + (Qf[n-1] - Qe_of(dg[n], E))*ex
                E2 = np.empty(N)
                E2[0] = 0.5*M*(om0+dw)**2
                for n in range(1, N):
                    E2[n] = E2[n-1] + (prm['Pref'] - Pf[n]
                                       - D*max(v[n-1], 0.05*(om0+dw)))*dd
                v = 0.5*v + 0.5*np.sqrt(np.maximum(
                    2*np.maximum(E2, 0)/M, (0.05*(om0+dw))**2))
            return E2[-1]
        lo3, hi3 = 0.5, 30.0
        for _ in range(35):
            mid = 0.5*(lo3+hi3)
            if endE(mid) > 0: hi3 = mid
            else: lo3 = mid
        return 0.5*(lo3+hi3)
    # forced state at 1% resonant, 4 phases (same protocol as e5)
    wp = w0
    eps = 0.010
    Tset = 60.0
    Tdp = 2*math.pi/wp
    def f(t, xx):
        qq = dict(prm, V=prm['V']*(1 + eps*math.cos(wp*t)))
        return rhs(xx, qq)
    s = solve_ivp(f, (0, Tset+Tdp), st.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, dense_output=True)
    MEAS = [6.945, 4.914, 2.348, 3.668]
    OLD = [+2.9, +9.3, -4.0, +2.9]
    for j in range(4):
        tk = Tset + j*Tdp/4
        xb = s.sol(tk)
        pred = bvp_dw(xb)
        msd = MEAS[j]
        out(f"  ph{j}: BVP pred={pred:.3f} meas={msd:.3f} "
            f"err={(pred-msd)/msd*100:+.1f}%  (old energy-formula "
            f"{OLD[j]:+.1f}%) [{time.time()-T0:.0f}s]")
    out(f"DONE wall={time.time()-T0:.0f}s")
