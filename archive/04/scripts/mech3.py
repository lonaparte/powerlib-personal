"""Close the idx17 residual by carrying the radial equation to fifth
order, so no step of the closed form is truncated below the amplitude it
is evaluated at.

mech2 separated the idx17 error (+2.53% on eps_c) into two named parts:
  polynomial truncation of the vector field  +2.69%
  a^2 expansion + carrier truncation          -2.83%
The first is the cubic radial equation being used at r_g = 0.0987, eleven
times the V cell's guard radius.  It is removed by the fifth-order
normal form, whose coefficient c2 comes from the homological solver
already validated on this workspace (kappa = 2 alpha (1 + C alpha),
C = Re c2/Re c1^2, previously <=0.26% against measured guard exponents).
The drive enters exactly as before, through alpha_eff = alpha - Re c_x |a|^2,
so the guard is the positive root of

    Re c2 . rho^4 + Re c1 . rho^2 - alpha_eff = 0 ,

and escape is still |Z(0)| > rho_g.  Because c1 and c2 come out of an
expansion ABOUT the Hopf point (at the operating point the (2,1)
denominator is -2 alpha, near-resonant, so the homological removal is
not admissible there), the coefficients are taken at P_H and alpha
carries the unfolding.  Three variants are compared against the same
measurements so the convention is tested rather than assumed:
    (i)   cubic, c1 at the operating point   (what mech1 used)
    (ii)  cubic, c1 at the Hopf point
    (iii) quintic, c1 and c2 at the Hopf point
Cells: V channel r=0.9 at four margins, and idx17 at r=0.92.
Also reported: lambda_u at eps=0 and at eps_c under the same three
variants, since lambda_u = 2 alpha_eff (1 + C alpha_eff) is the same
formula differentiated.
Budget ~20 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/mech3.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('nf5lib.py').read()
_ns = {}
exec(compile(_src, 'nf5lib', 'exec'), _ns)
run_set = _ns['run_set']

def tensors(pr, st):
    av = _avl(st, pr)
    def B2(u, v):
        return np.array([sum(_Hl[i][j][k](*av)*u[j]*v[k]
                             for j in range(4) for k in range(4))
                         for i in range(4)])
    def C3(u, v, w):
        return np.array([sum(_Tl[i][j][k][l](*av)*u[j]*v[k]*w[l]
                             for j in range(4) for k in range(4)
                             for l in range(4)) for i in range(4)])
    return B2, C3
def cross_sat(pr, co, fu, wp):
    st = co['st']; qv = co['q']; pv = co['p']; w0 = co['w0']
    A = jac(st, pr); B2, C3 = tensors(pr, st); I = np.eye(4)
    H = np.linalg.solve(1j*wp*I - A, fu.astype(complex))
    Hc = np.conj(H)
    gp = np.linalg.solve(1j*(w0+wp)*I - A, B2(qv, H))
    gm = np.linalg.solve(1j*(w0-wp)*I - A, B2(qv, Hc))
    d0 = -np.linalg.solve(A, B2(H, Hc))
    cx = (np.vdot(pv, C3(qv, H, Hc)) + np.vdot(pv, B2(H, gm))
          + np.vdot(pv, B2(Hc, gp)) + np.vdot(pv, B2(qv, d0)))
    return cx, H
def guard_quintic(aeff, c1r, c2r):
    if abs(c2r) < 1e-12:
        return math.sqrt(max(aeff, 0.0)/c1r)
    disc = c1r**2 + 4*c2r*aeff
    if disc < 0:
        return float('nan')
    r2 = (-c1r + math.sqrt(disc))/(2*c2r)
    return math.sqrt(r2) if r2 > 0 else float('nan')
def eps_thresh(J, aeff_of, c1r, c2r, epsguess):
    """solve  eps J = rho_g(alpha - Re c_x eps^2/4)  by bisection"""
    def g(eps):
        return eps*J - guard_quintic(aeff_of(eps), c1r, c2r)
    lo, hi = 1e-12, 10*epsguess
    for _ in range(200):
        m = 0.5*(lo+hi)
        v = g(m)
        if not (v == v) or v > 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)

CELLS = [('G1 V r=0.9', {}, 0.9, (0.05, 0.10, 0.15, 0.20)),
         ('idx17 r=0.92', dict(kp=55., ki=1200., Xg=0.40), 0.92, (0.08,))]
for tag, over, rat, margs in CELLS:
    PH, c1H, c2H = run_set(tag, over, [])
    CC = c2H.real/c1H.real**2
    out(f"=== {tag}: P_H={PH:.6f}, c1(P_H)={c1H:.4f}, c2(P_H)={c2H:.4f}, "
        f"C=Re c2/Re c1^2 = {CC:+.5f}")
    prb = gset('G1', **over)
    for marg in margs:
        P0 = margin_point(prb, PH, marg)
        pr = dict(prb, P=P0)
        co = nf_coeffs(pr)
        st = co['st']; w0 = co['w0']; alpha = co['alpha']
        c1P = co['c1']; lam = co['lam']; pv = co['p']
        dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
        wp = rat*w0; Td = 2*math.pi/wp
        hh = 1e-6
        fV = (rhs(st, dict(pr, V=pr['V']+hh))
              - rhs(st, dict(pr, V=pr['V']-hh)))/(2*hh)
        F = np.vdot(pv, fV)
        cx, H = cross_sat(pr, co, fV, wp)
        J = abs(lam)*abs(F)/abs(wp**2 + lam**2)
        aeff_of = lambda e: alpha - cx.real*e*e/4.0
        e_i = eps_thresh(J, aeff_of, c1P.real, 0.0,
                         math.sqrt(alpha/c1P.real)/J)
        e_ii = eps_thresh(J, aeff_of, c1H.real, 0.0,
                          math.sqrt(alpha/c1H.real)/J)
        e_iii = eps_thresh(J, aeff_of, c1H.real, c2H.real,
                           math.sqrt(alpha/c1H.real)/J)
        # measurement, window chosen long enough for the cell
        NPw = 1000 if rat == 0.9 else 4000
        def probe(eps, NPn):
            def f(t, x):
                return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
            def e_th(t, x): return abs(x[0] - st[0]) - dsad
            def e_vlo(t, x): return x[2] - 0.20*Vdc0
            def e_vhi(t, x): return x[2] - 2.50*Vdc0
            for e in (e_th, e_vlo, e_vhi):
                e.terminal = True
            e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
            s = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                          rtol=1e-10, atol=1e-13,
                          events=(e_th, e_vlo, e_vhi))
            return (any(len(s.t_events[i]) > 0 for i in range(3))
                    or s.status < 0)
        elo, ehi = 0.6*e_iii, 1.4*e_iii
        n = 0
        while not probe(ehi, 400) and n < 12:
            elo = ehi; ehi *= 1.3; n += 1
        n = 0
        while probe(elo, 400) and n < 12:
            ehi = elo; elo *= 0.75; n += 1
        for _ in range(18):
            em = 0.5*(elo+ehi)
            if probe(em, NPw): ehi = em
            else: elo = em
        emeas = 0.5*(elo+ehi)
        aeff_c = aeff_of(emeas)
        lu_iii = 2*aeff_c*(1 + CC*aeff_c)
        lu_i = 2*aeff_c
        out(f"  alpha={alpha:.3f}: measured {emeas:.6e}"
            f"   (i) {e_i:.6e} {(e_i-emeas)/emeas*100:+6.2f}%"
            f"   (ii) {e_ii:.6e} {(e_ii-emeas)/emeas*100:+6.2f}%"
            f"   (iii) {e_iii:.6e} {(e_iii-emeas)/emeas*100:+6.2f}%"
            f"  [{time.time()-T0:.0f}s]")
        out(f"           alpha_eff(eps_c)/alpha = {aeff_c/alpha:.4f}, "
            f"lambda_u pred cubic {lu_i:.6f} / quintic {lu_iii:.6f} "
            f"(C alpha_eff = {CC*aeff_c:+.4f})")
out(f"DONE wall={time.time()-T0:.0f}s")
