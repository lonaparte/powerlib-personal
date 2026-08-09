"""Where the reduced model's remaining 12-14% comes from.

Two candidates were on the table for the gap between the cubic forced
amplitude equation and the 4D threshold:
  (a) the O(eps) response in the non-critical directions feeding back
      through the quadratic term  -- REFUTED (ecscale2: including it
      moves the threshold by 0.05%, because at r = 0.9 that term is
      far from every resonance and averages out);
  (b) truncation of the amplitude equation itself at cubic order.
(b) is measurable without any new theory: the cubic normal form predicts
that the unforced guard cycle sits at modal amplitude r_g = sqrt(alpha /
Re c1) and repels at rate 2 alpha.  The 4D guard cycle is computed
exactly by Newton, so both predictions can be checked directly, and the
reduced model can be re-run with the amplitude equation CALIBRATED to
the true guard (Re c1' = alpha / A_g^2, which reproduces the measured
guard amplitude by construction).  Still zero fitting: A_g is a computed
property of the model, not a free parameter.

Reported per margin: A_g/r_g, kappa_true/(2 alpha), the cubic threshold,
the guard-calibrated threshold, and both against the 4D measurement.
Budget ~8 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/guardamp.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)]
                     for i in range(4)])
prb = gset('G1'); Psn = 3*prb['V']**2/(4*prb['Xg'])
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
out("alpha | A_g/r_g  kappa/2alpha | eps_4D      eps_cubic  err     "
    " eps_calib   err")
K = 64
for marg in (0.05, 0.10, 0.15, 0.20):
    P0 = margin_point(prb, PH, marg)
    pr = dict(prb, P=P0)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; alpha = co['alpha']
    c1v = co['c1']; lam = co['lam']; qv = co['q']; pv = co['p']
    rg = math.sqrt(alpha/c1v.real)
    dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
    wd = 0.9*w0; Td = 2*math.pi/wd
    hh = 1e-6
    fV = (rhs(st, dict(pr, V=pr['V']+hh))
          - rhs(st, dict(pr, V=pr['V']-hh)))/(2*hh)
    F = np.vdot(pv, fV)
    def flow(x0, T, var=False):
        def f(t, y):
            x = y[:4]
            if not var:
                return rhs(x, pr)
            return np.concatenate([rhs(x, pr),
                                   (jac_a(x, pr) @ y[4:].reshape(4, 4)).ravel()])
        y0 = x0 if not var else np.concatenate([x0, np.eye(4).ravel()])
        s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12, atol=1e-14)
        return (s.y[:4, -1] if not var
                else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
    def cyc(xs, Ts):
        x, T = xs.copy(), Ts; fref = rhs(xs, pr); R = np.ones(5)
        for it in range(40):
            xT, M = flow(x, T, var=True)
            R = np.append(xT - x, np.dot(fref, x - xs))
            if np.max(np.abs(R)) < 1e-12:
                return x, T, True
            A5 = np.zeros((5, 5)); A5[:4, :4] = M - np.eye(4)
            A5[:4, 4] = rhs(xT, pr); A5[4, :4] = fref
            dy = np.linalg.solve(A5, -R)
            n2 = np.linalg.norm(dy[:4]); cap = max(0.01, 0.5*rg)
            if n2 > cap: dy *= cap/n2
            if abs(dy[4]) > 0.1*T: dy *= 0.1*T/abs(dy[4])
            x = x + dy[:4]; T = T + dy[4]
        return x, T, np.max(np.abs(R)) < 1e-9
    got = False
    for fac in (1.0, 0.85, 0.7, 1.2):
        xs = st + 2*np.real(fac*rg*qv)
        Ts = 2*math.pi/(w0 + c1v.imag*(fac*rg)**2)
        x0c, Tc, ok = cyc(xs, Ts)
        if ok and abs(np.vdot(pv, x0c - st)) > 0.2*rg:
            got = True; break
    if not got:
        out(f"{marg:.2f} | guard cycle Newton failed"); continue
    s = solve_ivp(lambda t, x: rhs(x, pr), (0, Tc), x0c, method='DOP853',
                  rtol=1e-12, atol=1e-14, t_eval=np.arange(K)*Tc/K)
    Uc = s.y.T
    Z = np.array([np.vdot(pv, Uc[j] - st) for j in range(K)])
    th = 2*math.pi*np.arange(K)/K
    Ag = abs(np.mean(Z*np.exp(-1j*th)))
    _, Mon = flow(x0c, Tc, var=True)
    kap = math.log(abs(max(np.linalg.eigvals(Mon), key=lambda z: abs(z))))/Tc
    def esc(eps, c1u, frad=5.0, NP=400):
        def f(t, y):
            z = y[0] + 1j*y[1]
            dz = lam*z + c1u*abs(z)**2*z + eps*F*math.cos(wd*t)
            return [dz.real, dz.imag]
        rgu = math.sqrt(alpha/c1u.real)
        def blow(t, y):
            return math.hypot(y[0], y[1]) - frad*rgu
        blow.terminal = True; blow.direction = 1
        so = solve_ivp(f, (0, NP*Td), [0.0, 0.0], method='DOP853',
                       rtol=1e-11, atol=1e-14, events=blow)
        return len(so.t_events[0]) > 0
    def thr(c1u):
        elo, ehi = 1e-7, 1e-2
        n = 0
        while not esc(ehi, c1u) and ehi < 1.0 and n < 20:
            elo = ehi; ehi *= 1.6; n += 1
        n = 0
        while esc(elo, c1u) and elo > 1e-10 and n < 25:
            ehi = elo; elo *= 0.5; n += 1
        if esc(elo, c1u) or not esc(ehi, c1u):
            return None
        for _ in range(18):
            em = 0.5*(elo+ehi)
            if esc(em, c1u): ehi = em
            else: elo = em
        return 0.5*(elo+ehi)
    def probe(eps, NPn=1000):
        def f(t, x):
            return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
        def e_th(t, x): return abs(x[0] - st[0]) - dsad
        def e_vlo(t, x): return x[2] - 0.20*Vdc0
        def e_vhi(t, x): return x[2] - 2.50*Vdc0
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        so = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                       rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
        return (any(len(so.t_events[i]) > 0 for i in range(3))
                or so.status < 0)
    e0 = 2*rg*abs(lam - 1j*wd)/abs(F)
    elo, ehi = 0.3*e0, 1.2*e0
    n = 0
    while not probe(ehi) and n < 12:
        elo = ehi; ehi *= 1.4; n += 1
    n = 0
    while probe(elo) and n < 12:
        ehi = elo; elo *= 0.6; n += 1
    e4 = float('nan')
    if not probe(elo) and probe(ehi):
        for _ in range(16):
            em = 0.5*(elo+ehi)
            if probe(em): ehi = em
            else: elo = em
        e4 = 0.5*(elo+ehi)
    ec = thr(c1v)
    c1cal = complex(alpha/Ag**2, c1v.imag)
    eca = thr(c1cal)
    out(f"{marg:.2f} | {Ag/rg:.5f}  {kap/(2*alpha):.5f}    | {e4:.5e}  "
        f"{ec:.5e} {(ec-e4)/e4*100:+6.2f}%  {eca:.5e} "
        f"{(eca-e4)/e4*100:+6.2f}%  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
