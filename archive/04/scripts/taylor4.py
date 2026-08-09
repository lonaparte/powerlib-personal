"""Is the residual 12% a polynomial-truncation error or a
mode-reduction error?

Established so far on the V channel at r = 0.9:
  * the cubic single-mode amplitude equation is low by 12-14%;
  * the non-critical directions' O(eps) response contributes 0.05%
    (ecscale2), so it is not that;
  * the cubic normal form reproduces the unforced guard geometry to
    0.36% in amplitude and 0.18% in repulsion rate (guardamp), so it is
    not the cubic truncation of the guard either.
Remaining suspects: the truncation of the vector field at cubic order in
the FORCED problem, versus the reduction from four states to one complex
mode.  They are separated by running the same protocol on the full
four-state CUBIC TAYLOR field
    ydot = A y + B(y,y)/2 + C(y,y,y)/6 + eps f_u cos(w_p t),
which truncates exactly like the amplitude equation but keeps all four
states.  If it matches the exact system, the truncation is innocent and
the 12% is the price of the one-mode reduction.

Escape is detected on the modal radius |<p,y>| so that all three systems
(exact, Taylor, reduced) are read out identically; the exact system is
also measured with the physical detectors to show the readout itself
does not move the threshold.
Budget ~12 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/taylor4.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

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
out(f"G1: P_H={PH:.6f}, V channel, r = 0.9, escape at |<p,y>| = 5 r_g")
out("alpha | exact(phys)  exact(modal) dev     cubic-Taylor  err      "
    "reduced 1-mode err")
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
    Hm = np.array([[[float(_Hl[i][j][k](*av)) for k in range(4)]
                    for j in range(4)] for i in range(4)])
    Cm = np.array([[[[float(_Tl[i][j][k][l](*av)) for l in range(4)]
                     for k in range(4)] for j in range(4)]
                   for i in range(4)])
    def rhs_tay(y, eps, t):
        q1 = np.einsum('ijk,j,k->i', Hm, y, y)
        c3 = np.einsum('ijkl,j,k,l->i', Cm, y, y, y)
        return (A @ y + 0.5*q1 + c3/6.0
                + eps*fV*math.cos(wd*t))
    def esc_generic(eps, kind, NP=1000):
        if kind == 'phys':
            def f(t, x):
                return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
            def e_th(t, x): return abs(x[0] - st[0]) - dsad
            def e_vlo(t, x): return x[2] - 0.20*Vdc0
            def e_vhi(t, x): return x[2] - 2.50*Vdc0
            evs = (e_th, e_vlo, e_vhi)
            for e in evs:
                e.terminal = True
            e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
            y0 = st.copy()
        else:
            if kind == 'exact':
                def f(t, x):
                    return rhs(x + st, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
            else:
                def f(t, x):
                    return rhs_tay(x, eps, t)
            def e_r(t, x):
                return abs(np.vdot(pv, x)) - 5.0*rg
            e_r.terminal = True; e_r.direction = 1
            evs = (e_r,)
            y0 = np.zeros(4)
        s = solve_ivp(f, (0, NP*Td), y0, method='DOP853',
                      rtol=1e-10, atol=1e-13, events=evs)
        return any(len(t) > 0 for t in s.t_events) or s.status < 0
    def thr(kind, seed):
        elo, ehi = 0.4*seed, 1.3*seed
        n = 0
        while not esc_generic(ehi, kind) and n < 14:
            elo = ehi; ehi *= 1.4; n += 1
        n = 0
        while esc_generic(elo, kind) and n < 14:
            ehi = elo; elo *= 0.6; n += 1
        if esc_generic(elo, kind) or not esc_generic(ehi, kind):
            return None
        for _ in range(16):
            em = 0.5*(elo+ehi)
            if esc_generic(em, kind): ehi = em
            else: elo = em
        return 0.5*(elo+ehi)
    seed = 2*rg*abs(lam - 1j*wd)/abs(F)/1.55
    ep = thr('phys', seed)
    em_ = thr('exact', seed)
    et = thr('tay', seed)
    def esc_red(eps, NP=1000):
        def f(t, y):
            z = y[0] + 1j*y[1]
            dz = lam*z + c1v*abs(z)**2*z + eps*F*math.cos(wd*t)
            return [dz.real, dz.imag]
        def blow(t, y):
            return math.hypot(y[0], y[1]) - 5.0*rg
        blow.terminal = True; blow.direction = 1
        s = solve_ivp(f, (0, NP*Td), [0.0, 0.0], method='DOP853',
                      rtol=1e-11, atol=1e-14, events=blow)
        return len(s.t_events[0]) > 0
    elo, ehi = 0.4*seed, 1.3*seed
    n = 0
    while not esc_red(ehi) and n < 14:
        elo = ehi; ehi *= 1.4; n += 1
    n = 0
    while esc_red(elo) and n < 14:
        ehi = elo; elo *= 0.6; n += 1
    er = None
    if not esc_red(elo) and esc_red(ehi):
        for _ in range(16):
            emm = 0.5*(elo+ehi)
            if esc_red(emm): ehi = emm
            else: elo = emm
        er = 0.5*(elo+ehi)
    def pc(x, ref):
        return f"{(x-ref)/ref*100:+7.2f}%" if x else "   n/a  "
    out(f"{marg:.2f} | {ep:.5e}  {em_:.5e} {pc(em_, ep)}  "
        f"{et:.5e} {pc(et, em_)}  {er:.5e} {pc(er, em_)} "
        f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
