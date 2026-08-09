"""Where the remaining gap in the closed form lives.

Sizing hierarchy for the direct-forcing threshold (V channel, r = 0.9):
  (i)   linear response reaches the guard radius        -> high by ~55%
  (ii)  cubic forced amplitude equation                  -> low by ~12%
  (iii) full 4D winding-flip criterion                   -> +-0.4%
Level (ii) keeps only the projection of the drive onto the critical
mode.  It throws away the O(eps) forced response in the NON-critical
directions, which does not just sit there: it beats against the critical
mode through the quadratic term and acts as a parametric (multiplicative)
modulation of that mode.  That is the same object that produces the
parametric tongues, here evaluated on the direct-forcing problem.

Augmented reduced model:
    x - st = z q + zbar qbar + w,     w = eps Re(W e^{i w_p t}),
    W = P_perp (i w_p I - A)^{-1} f_u ,  P_perp = I - 2 Re(q p^H),
    zdot = lam z + c1 |z|^2 z + eps <p,f_u> cos(w_p t)
           + (eps/2)[ z (b1 e^{i w_p t} + b2 e^{-i w_p t})
                    + zbar (b3 e^{i w_p t} + b4 e^{-i w_p t}) ],
    b1 = <p,B(q,W)>, b2 = <p,B(q,Wbar)>,
    b3 = <p,B(qbar,W)>, b4 = <p,B(qbar,Wbar)>.
Every symbol is a model quantity; nothing is fitted.  The test is
whether level (ii)+(this) closes the 12%.
The 4D threshold is re-measured in the same script so the comparison is
self-contained.  Budget ~12 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/ecscale2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

prb = gset('G1')
Psn = 3*prb['V']**2/(4*prb['Xg'])
def reA(P):
    q = dict(prb, P=P); x = equil(q)
    if x is None: return None
    cm = crit_mode(jac(x, q))
    return None if cm is None else cm.real
grid = np.linspace(0.05, 0.985, 60)*Psn
va = [reA(P) for P in grid]; br = None
for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
    if fa is not None and fb is not None and fa < 0 <= fb:
        br = (a, b); break
lo, hi = br
for _ in range(45):
    m = 0.5*(lo+hi); v = reA(m)
    if v is None or v >= 0: hi = m
    else: lo = m
PH = 0.5*(lo+hi)
out(f"G1: P_H={PH:.6f}, V channel, r = 0.9")
out("alpha | eps_4D        eps_cubic  err      eps_augmented err     "
    "| eps_linsize err      | |eps b|/alpha")

for marg in (0.05, 0.10, 0.20):
    P0 = margin_point(prb, PH, marg)
    pr = dict(prb, P=P0)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; alpha = co['alpha']
    c1v = co['c1']; lam = co['lam']; qv = co['q']; pv = co['p']
    rg = math.sqrt(alpha/c1v.real)
    dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
    wd = 0.9*w0; Td = 2*math.pi/wd
    A = jac(st, pr)
    hh = 1e-6
    fV = (rhs(st, dict(pr, V=pr['V']+hh))
          - rhs(st, dict(pr, V=pr['V']-hh)))/(2*hh)
    F = np.vdot(pv, fV)
    av = _avl(st, pr)
    def B2c(u, v):
        return np.array([sum(_Hl[i][j][k](*av)*u[j]*v[k]
                             for j in range(4) for k in range(4))
                         for i in range(4)])
    H = np.linalg.solve(1j*wd*np.eye(4) - A, fV.astype(complex))
    Ppar = 2*np.real(np.outer(qv, np.conj(pv)))
    W = (np.eye(4) - Ppar) @ H
    b1 = np.vdot(pv, B2c(qv, W)); b2 = np.vdot(pv, B2c(qv, np.conj(W)))
    b3 = np.vdot(pv, B2c(np.conj(qv), W))
    b4 = np.vdot(pv, B2c(np.conj(qv), np.conj(W)))
    bmax = max(abs(b1), abs(b2), abs(b3), abs(b4))
    # ---- 4D measurement, intrinsic detectors ----
    def probe(eps, NPn=400):
        def f(t, x):
            return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
        def e_th(t, x): return abs(x[0] - st[0]) - dsad
        def e_vlo(t, x): return x[2] - 0.20*Vdc0
        def e_vhi(t, x): return x[2] - 2.50*Vdc0
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
        return (any(len(s.t_events[i]) > 0 for i in range(3))
                or s.status < 0)
    est_lin = 2*rg*abs(lam - 1j*wd)/abs(F)
    elo, ehi = 0.3*est_lin, 1.2*est_lin
    n = 0
    while not probe(ehi) and n < 10:
        elo = ehi; ehi *= 1.4; n += 1
    n = 0
    while probe(elo) and n < 10:
        ehi = elo; elo *= 0.6; n += 1
    if probe(elo) or not probe(ehi):
        out(f"{marg:.2f} | 4D bracket failed"); continue
    for _ in range(16):
        em = 0.5*(elo+ehi)
        if probe(em): ehi = em
        else: elo = em
    e4 = 0.5*(elo+ehi)
    # ---- reduced models ----
    def esc(eps, aug, frad=5.0, NP=400):
        def f(t, y):
            z = y[0] + 1j*y[1]
            dz = lam*z + c1v*abs(z)**2*z + eps*F*math.cos(wd*t)
            if aug:
                ep = np.exp(1j*wd*t); em_ = np.conj(ep)
                dz += 0.5*eps*(z*(b1*ep + b2*em_)
                               + np.conj(z)*(b3*ep + b4*em_))
            return [dz.real, dz.imag]
        def blow(t, y):
            return math.hypot(y[0], y[1]) - frad*rg
        blow.terminal = True; blow.direction = 1
        s = solve_ivp(f, (0, NP*Td), [0.0, 0.0], method='DOP853',
                      rtol=1e-11, atol=1e-14, events=blow)
        return len(s.t_events[0]) > 0
    def thr(aug):
        elo2, ehi2 = 1e-7, 1e-2
        n = 0
        while not esc(ehi2, aug) and ehi2 < 1.0 and n < 20:
            elo2 = ehi2; ehi2 *= 1.6; n += 1
        n = 0
        while esc(elo2, aug) and elo2 > 1e-10 and n < 25:
            ehi2 = elo2; elo2 *= 0.5; n += 1
        if esc(elo2, aug) or not esc(ehi2, aug):
            return None
        for _ in range(18):
            em2 = 0.5*(elo2+ehi2)
            if esc(em2, aug): ehi2 = em2
            else: elo2 = em2
        return 0.5*(elo2+ehi2)
    e_cub = thr(False); e_aug = thr(True)
    def pc(x):
        return f"{(x-e4)/e4*100:+7.2f}%" if x else "   n/a  "
    out(f"{marg:.2f} | {e4:.5e}  {e_cub:.5e} {pc(e_cub)}  "
        f"{(e_aug if e_aug else 0):.5e} {pc(e_aug)} | "
        f"{est_lin:.5e} {pc(est_lin)} | {e4*bmax/alpha:.4f} "
        f"[{time.time()-T0:.0f}s]")
    out(f"       b1={abs(b1):.3e} b2={abs(b2):.3e} b3={abs(b3):.3e} "
        f"b4={abs(b4):.3e}  |F|={abs(F):.3f}  r_g={rg:.4e}")
out(f"DONE wall={time.time()-T0:.0f}s")
