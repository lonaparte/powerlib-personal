"""Slot E, 5 fresh parameter sets per converter.
GFL: fiber-corrected kick-threshold prediction (etheory3 machinery) vs
     phase-0 measurement, at eps_bg = 0 and 0.6*eps_c per set.
GFM: energy-superposition prediction vs measurement, 1%% resonant
     background, 4 phases, on 5 fresh Hopf-window sets.
Usage: python e5.py {gfl|gfm}
"""
import sys
WHICH = sys.argv[1]
import time, os
os.makedirs('sweep20', exist_ok=True)
LOG = open(f'sweep20/e5-{WHICH}.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

if WHICH == 'gfl':
    exec(open('selfhead.py').read())
    _Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
            for j in range(4)] for i in range(4)]
    def jac_a(x, prm):
        a = _avl(x, prm)
        return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                         for i in range(4)])
    K = 32
    mfreq = np.fft.fftfreq(K)*K
    I4 = np.eye(4)
    def shift_mat(r):
        ph = np.exp(1j*mfreq*r)
        return np.real(np.fft.ifft(np.fft.fft(np.eye(K), axis=0)
                                   * ph[:, None], axis=0))
    def dshift_mat(r):
        ph = 1j*mfreq*np.exp(1j*mfreq*r)
        return np.real(np.fft.ifft(np.fft.fft(np.eye(K), axis=0)
                                   * ph[:, None], axis=0))
    def dtheta(Ua):
        return np.real(np.fft.ifft(np.fft.fft(Ua, axis=0)
                                   * (1j*mfreq)[:, None], axis=0))
    def upsample(Ua, N):
        C = np.fft.fft(Ua, axis=0)
        Cp = np.zeros((N, Ua.shape[1]), complex)
        hf = K//2
        Cp[:hf] = C[:hf]; Cp[N-hf+1:] = C[hf+1:]
        Cp[hf] = 0.5*C[hf]; Cp[N-hf] = 0.5*C[hf]
        return np.real(np.fft.ifft(Cp, axis=0))*(N/K)
    CASES = [
        dict(tag='Xg=0.70',  over=dict(Xg=0.70), marg=0.10, epsc=4.0434e-4),
        dict(tag='Q=+0.15',  over=dict(Q=0.15), marg=0.10, epsc=6.8388e-4),
        dict(tag='mix12',    over=dict(kp=40., ki=800., kpv=1.5, kiv=60.,
                                       C=0.015, Xg=0.45), marg=0.10,
             epsc=5.6992e-4),
        dict(tag='mix16',    over=dict(kp=45., ki=900., Xg=0.55), marg=0.10,
             epsc=5.0766e-4),
        dict(tag='G1 m=0.15', over={}, marg=0.15, epsc=None),
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
        co = nf_coeffs(pr)
        st = co['st']; alpha = co['alpha']; w0 = co['w0']
        c1v = co['c1']; qv = co['q']; pv = co['p']
        wd = 0.9*w0
        Td = 2*math.pi/wd
        zg = math.sqrt(alpha/c1v.real)
        out(f"{case['tag']}: P={P:.5f} alpha={alpha:.4f} w0={w0:.3f} "
            f"zg={zg:.4e}")
        def flow_auto(x0, T, with_var=False):
            def f(t, y):
                x = y[:4]
                if not with_var:
                    return rhs(x, pr)
                Phi = y[4:].reshape(4, 4)
                return np.concatenate([rhs(x, pr),
                                       (jac_a(x, pr) @ Phi).ravel()])
            y0 = (x0 if not with_var
                  else np.concatenate([x0, np.eye(4).ravel()]))
            s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12,
                          atol=1e-14)
            return (s.y[:4, -1] if not with_var
                    else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
        def cycle_newton(xs, Ts, itmax=40):
            x, T = xs.copy(), Ts
            fref = rhs(xs, pr)
            for it in range(itmax):
                xT, M = flow_auto(x, T, with_var=True)
                R = np.append(xT - x, np.dot(fref, x - xs))
                if np.max(np.abs(R)) < 1e-12:
                    return x, T, True
                A5 = np.zeros((5, 5))
                A5[:4, :4] = M - np.eye(4)
                A5[:4, 4] = rhs(xT, pr)
                A5[4, :4] = fref
                dy = np.linalg.solve(A5, -R)
                n = np.linalg.norm(dy[:4])
                cap = max(0.01, 0.5*zg)
                if n > cap:
                    dy *= cap/n
                if abs(dy[4]) > 0.1*T:
                    dy *= 0.1*T/abs(dy[4])
                x = x + dy[:4]; T = T + dy[4]
            return x, T, np.max(np.abs(R)) < 1e-9
        cyc = None
        for fac in (1.0, 0.85, 0.7, 0.6, 1.2, 1.4):
            xs = st + 2*np.real(fac*zg*qv)
            Ts = 2*math.pi/(w0 + c1v.imag*(fac*zg)**2)
            x0c, Tc, okc = cycle_newton(xs, Ts)
            if okc and abs(np.vdot(pv, x0c - st)) > 0.2*zg:
                cyc = (x0c, Tc); break
        if cyc is None:
            out("  guard cycle Newton failed — skip"); continue
        x0c, Tc = cyc
        scc = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c,
                        method='DOP853', rtol=1e-12, atol=1e-14,
                        t_eval=np.arange(K)*Tc/K)
        Uc = scc.y.T.copy()
        planes = []
        for j in range(K):
            xT, Mj = flow_auto(Uc[j], Tc, with_var=True)
            ev, V = np.linalg.eig(Mj)
            ks = np.argsort(np.abs(ev))
            v = V[:, ks[0]]
            if abs(ev[ks[0]].imag) > 1e-12:
                B = np.stack([v.real, v.imag], axis=1)
            else:
                B = np.stack([V[:, ks[0]].real, V[:, ks[1]].real], axis=1)
            Q, _ = np.linalg.qr(B)
            planes.append(Q)
        planes = np.array(planes)
        def strobe_var(x0, eps):
            def f(t, y):
                x = y[:4]
                qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
                Phi = y[4:].reshape(4, 4)
                return np.concatenate([rhs(x, qq),
                                       (jac_a(x, qq) @ Phi).ravel()])
            y0 = np.concatenate([x0, np.eye(4).ravel()])
            s = solve_ivp(f, (0, Td), y0, method='DOP853', rtol=1e-11,
                          atol=1e-13)
            return s.y[:4, -1], s.y[4:, -1].reshape(4, 4)
        def torus_newton(U, rho, eps, itmax=25, tol=1e-10):
            Uref = U.copy(); dUref = dtheta(Uref)
            for it in range(itmax):
                Sh = shift_mat(rho)
                PhiU = np.zeros((K, 4)); Ms = np.zeros((K, 4, 4))
                for j in range(K):
                    PhiU[j], Ms[j] = strobe_var(U[j], eps)
                R = PhiU - Sh @ U
                c = float(np.sum(dUref*(U - Uref)))
                res = max(np.max(np.abs(R)), abs(c))
                if res < tol:
                    return U, rho, True
                A = np.zeros((4*K+1, 4*K+1))
                for j in range(K):
                    A[4*j:4*j+4, 4*j:4*j+4] += Ms[j]
                A[:4*K, :4*K] -= np.kron(Sh, I4)
                A[:4*K, -1] = -(dshift_mat(rho) @ U).flatten()
                A[-1, :4*K] = dUref.flatten()
                dy = np.linalg.solve(A, -np.concatenate([R.flatten(),
                                                         [c]]))
                nU = np.max(np.abs(dy[:4*K]))
                cap = max(0.005, 0.5*zg)
                if nU > cap:
                    dy *= cap/nU
                U = U + dy[:4*K].reshape(K, 4); rho = rho + dy[-1]
            return U, rho, res < 1e-9
        def newton_fp(xg, eps, itmax=25):
            x = xg.copy()
            for it in range(itmax):
                xT, M = strobe_var(x, eps)
                Fx = xT - x
                if np.max(np.abs(Fx)) < 1e-11:
                    return x
                x = x + np.linalg.solve(M - np.eye(4), -Fx)
            return x
        def winding(Ua):
            dens = upsample(Ua, 2048)
            Z = (dens - st) @ np.conj(pv)
            dph = np.angle(Z*np.conj(np.roll(Z, 1)))
            return int(round(float(np.sum(dph))/(2*math.pi)))
        khat = 2*np.real(qv)
        def kappa_fiber(xb, Upts):
            res_arr = np.zeros(K); kap_arr = np.zeros(K)
            for j in range(K):
                A = np.column_stack([khat, -planes[j][:, 0],
                                     -planes[j][:, 1]])
                bvec = Upts[j] - xb
                sol, _, _, _ = np.linalg.lstsq(A, bvec, rcond=None)
                res_arr[j] = np.linalg.norm(A @ sol - bvec)
                kap_arr[j] = sol[0]
            cands = sorted((res_arr[j], kap_arr[j]) for j in range(K)
                           if kap_arr[j] > 0
                           and res_arr[j] <= res_arr[(j-1) % K]
                           and res_arr[j] <= res_arr[(j+1) % K])
            return cands[0][1] if cands else None
        # torus continuation (flip search if epsc unknown)
        U = Uc.copy()
        rho = 2*math.pi*((Td/Tc) % 1.0)
        U, rho, ok = torus_newton(U, rho, 0.0)
        epsc = case['epsc']
        if epsc is None:
            w_ref = winding(U)
            eps = 0.0; deps = 2e-5
            Uf, rf = U.copy(), rho
            while True:
                e_try = eps + deps
                Un, rn, okn = torus_newton(Uf.copy(), rf, e_try)
                if not okn:
                    deps *= 0.5
                    if deps < 1e-8:
                        break
                    continue
                if winding(Un) != w_ref:
                    epsc = 0.5*(eps + e_try)
                    break
                Uf, rf, eps = Un, rn, e_try
                deps = min(deps*1.4, 3e-5)
            out(f"  flip found: eps_c={epsc:.4e}")
        ebg = 0.6*epsc
        eps = 0.0; deps = 0.15*ebg
        while eps < ebg*0.9999:
            e_try = min(eps + deps, ebg)
            Un, rn, okn = torus_newton(U.copy(), rho, e_try)
            if not okn:
                deps *= 0.5; continue
            U, rho, eps = Un, rn, e_try
            deps = min(deps*1.4, 0.25*ebg)
        xL = newton_fp(st.copy(), ebg)
        kp0 = kappa_fiber(st.copy(), Uc)
        kpb = kappa_fiber(xL, U)
        # measurements (phase 0)
        def measure(eps, pred):
            def frc(t, x):
                qq = dict(pr, V=pr['V'] + eps*math.cos(wd*t))
                return rhs(x, qq)
            Tset = Td*math.ceil(150/Td)
            if eps > 0:
                s = solve_ivp(frc, (0, Tset), st.copy(), method='DOP853',
                              rtol=1e-9, atol=1e-12)
                xb = s.y[:, -1]
            else:
                xb = st.copy()
            def esc(kap):
                xk = xb + 2*np.real(kap*qv)
                def blow(t, x): return abs(x[0] - st[0]) - 1.2
                blow.terminal = True; blow.direction = 1
                s = solve_ivp(frc, (Tset, Tset+150), xk, method='DOP853',
                              rtol=1e-8, atol=1e-12, events=blow)
                return len(s.t_events[0]) > 0
            klo, khi = 0.0, 2.5*pred
            if not esc(khi):
                khi = 5*pred
            for _ in range(12):
                km = 0.5*(klo+khi)
                if esc(km): khi = km
                else: klo = km
            return 0.5*(klo+khi)
        m0 = measure(0.0, kp0)
        mb = measure(ebg, kpb)
        out(f"  RESULT {case['tag']} eps_bg=0: pred={kp0:.4e} "
            f"meas={m0:.4e} err={(kp0-m0)/m0*100:+.2f}%")
        out(f"  RESULT {case['tag']} eps_bg=0.6x: pred={kpb:.4e} "
            f"meas={mb:.4e} err={(kpb-mb)/mb*100:+.2f}%")
    out(f"DONE wall={time.time()-T0:.0f}s")

else:
    import math, numpy as np
    from scipy.integrate import solve_ivp
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from gfmlib import (rhs, jac, equil, crit_mode, maxre_cx, hopf_in,
                        mset, fold, P_of, escape_event)
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
        prm = dict(pr, Pref=0.5*(lo2+hi2))
        st = equil(prm)
        lam = crit_mode(jac(st, prm))
        return dict(pr=prm, st=st, alpha=-lam.real, w0=lam.imag)
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
        pr, st, w0 = b['pr'], b['st'], b['w0']
        M = pr['M']
        ev, dsad = escape_event(pr)
        out(f"{name}@Xg={Xg}: P0={pr['Pref']:.4f} alpha={b['alpha']:.4f} "
            f"w0={w0:.4f}")
        dg = np.linspace(st[0]-0.6, dsad+0.1, 3000)
        Pv = np.array([P_of(x, pr) - pr['Pref'] for x in dg])
        Ug = np.concatenate([[0], np.cumsum(0.5*(Pv[1:]+Pv[:-1])
                                            * np.diff(dg))])
        Ug -= np.interp(st[0], dg, Ug)
        def U(d): return float(np.interp(d, dg, Ug))
        def esc_from(x, tk, eps, wp, Tf=80.0):
            def f(t, xx):
                qq = dict(pr, V=pr['V']*(1 + eps*math.cos(wp*t)))
                return rhs(xx, qq)
            s = solve_ivp(f, (tk, tk+Tf), x, method='DOP853', rtol=1e-9,
                          atol=1e-12, events=ev)
            return len(s.t_events[0]) > 0
        def dwc_measure(xb, tk, eps, wp):
            lo2, hi2 = 0.0, 2.0
            while True:
                xk = xb.copy(); xk[1] += hi2
                if esc_from(xk, tk, eps, wp) or hi2 > 80:
                    break
                hi2 *= 2
            for _ in range(9):
                dm = 0.5*(lo2+hi2)
                xk = xb.copy(); xk[1] += dm
                if esc_from(xk, tk, eps, wp): hi2 = dm
                else: lo2 = dm
            return 0.5*(lo2+hi2)
        dw0 = dwc_measure(st.copy(), 0.0, 0.0, w0)
        Eesc = 0.5*M*dw0*dw0
        out(f"  dw0={dw0:.4f}")
        def pred_from_state(x):
            avail = 2*(Eesc - U(x[0]))/M
            return (math.sqrt(avail) if avail > 0 else 0.0) - x[1]
        eps, wp = 0.010, w0
        Tset = 60.0
        Tdp = 2*math.pi/wp
        def f(t, xx):
            qq = dict(pr, V=pr['V']*(1 + eps*math.cos(wp*t)))
            return rhs(xx, qq)
        s = solve_ivp(f, (0, Tset+Tdp), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13, dense_output=True)
        errs = []
        for j in range(4):
            tk = Tset + j*Tdp/4
            xb = s.sol(tk)
            pred = pred_from_state(xb)
            msd = dwc_measure(xb.copy(), tk, eps, wp)
            errs.append((pred, msd, (pred-msd)/msd*100))
        out(f"  RESULT {name}@Xg={Xg} res eps=0.010: "
            + "  ".join(f"[ph{j}: pred={r[0]:.3f} meas={r[1]:.3f} "
                        f"err={r[2]:+.1f}%]" for j, r in enumerate(errs)))
    out(f"DONE wall={time.time()-T0:.0f}s")
