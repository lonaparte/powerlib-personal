"""Fifth-order two-carrier normal form: c_xx and c_a4.

The third-order closed form leaves +2.2...+2.5% on idx17 and fails on the
omega_g slow cell because the guard's growth saturates.  Both are the
next order of the SAME expansion, so it is carried out here rather than
declared future work.

Set-up.  With zeta = Z e^{i w0 t} and alpha = a e^{i w_p t} the problem is
autonomous polynomial in the four variables (zeta, zetabar, alpha,
alphabar):
    zeta' = lam zeta + g(zeta,zetabar,alpha,alphabar),
    alpha' = i w_p alpha,
    y = Phi(zeta,zetabar,alpha,alphabar) = sum_pi h_pi zeta^j zetabar^k
                                                    alpha^l alphabar^m,
and the drive eps cos(w_p t) f_u is exactly f_u (alpha + alphabar), i.e.
a LINEAR term in the new variables, so no time dependence is left.
Invariance gives the homological equation at each multi-index

    [D_pi I - A] h_pi = N_pi - T_pi ,
    D_pi = j lam + k lambar + (l-m) i w_p ,

with N from the Taylor tensors B..E of the field and T the transport
d Phi/d zeta . g + d Phi/d zetabar . gbar.  At the Hopf point lam = i w0
so D_pi = lam exactly for pi = (j+1, j, l, l); those are the resonances
that survive in the reduced equation:

    (2,1,0,0) -> c1      (1,0,1,1) -> c_x
    (3,2,0,0) -> c2      (2,1,1,1) -> c_xx      (1,0,2,2) -> c_a4

so the radial equation to fifth order in both amplitudes is

    rho' = -alpha_eff rho + c1_eff rho^3 + Re c2 rho^5 ,
    alpha_eff = alpha - Re c_x |a|^2 - Re c_a4 |a|^4 ,
    c1_eff    = Re c1 + Re c_xx |a|^2 ,

the guard is the positive root of Re c2 rho^4 + c1_eff rho^2 - alpha_eff,
and the switch-on kick keeps its own second-order terms,
    Z(0) = -[ a<p,H> + abar<p,Hbar> + a^2<p,h_0020> + a abar<p,h_0011>
              + abar^2<p,h_0002> ].
Escape is still |Z(0)| > rho_g.

Three independent checks before any of it is used: c1 against the
Kuznetsov formula, c2 against the earlier homological solver, and c_x
against the hand-derived third-order expression (sum/difference/DC
channels).  Then eps_c on the V cell (four margins) and idx17, and the
guard radius on the omega_g slow cell where the cubic version saturated.
Budget ~25 min.
"""
exec(open('selfhead.py').read())
import itertools, time
from math import factorial
LOG = open('sweep20/mech4.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
TR = 5

def padd(dst, src, c=1.0):
    for k, v in src.items():
        dst[k] = dst.get(k, 0) + c*v
def pmul(a, b):
    r = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = (ka[0]+kb[0], ka[1]+kb[1], ka[2]+kb[2], ka[3]+kb[3])
            if k[0]+k[1]+k[2]+k[3] > TR:
                continue
            r[k] = r.get(k, 0) + va*vb
    return r
def deg(k):
    return k[0]+k[1]+k[2]+k[3]
def mult_count(combo):
    n = len(combo); r = factorial(n)
    for j in set(combo):
        r //= factorial(combo.count(j))
    return r

def taylor_tensors(pr, st):
    subs = {th_: st[0], xp_: st[1], Vdc_: st[2], xi_: st[3],
            P_: pr['P'], Q_: pr['Q'], V_: pr['V'], Xg_: pr['Xg'],
            kp_: pr['kp'], ki_: pr['ki'], kpv_: pr['kpv'],
            kiv_: pr['kiv'], C_: pr['C']}
    Dk = {}
    for k in range(2, 6):
        Dk[k] = [dict() for _ in range(4)]
        for i in range(4):
            for combo in itertools.combinations_with_replacement(range(4), k):
                e = f_[i]
                for j in combo:
                    e = sp.diff(e, _x[j])
                val = complex(e.subs(subs).evalf())
                if abs(val) > 1e-13:
                    Dk[k][i][combo] = val
    return Dk

def two_carrier_nf(pr, wp, fu, verbose=False):
    """Return the resonant coefficients of the two-carrier normal form,
    computed at the Hopf-point equilibrium of pr."""
    st = equil(pr)
    A = jac(st, pr)
    from scipy.linalg import eig as _eig
    ev, VL, VR = _eig(A, left=True, right=True)
    kk = max((i for i in range(4) if ev[i].imag > 1e-9),
             key=lambda i: ev[i].real)
    lam = ev[kk]; q = VR[:, kk]; p = VL[:, kk]; p = p/np.vdot(q, p)
    Dk = taylor_tensors(pr, st)
    I = np.eye(4)
    H = np.linalg.solve(1j*wp*I - A, fu.astype(complex))
    Y = [dict() for _ in range(4)]
    for i in range(4):
        Y[i][(1, 0, 0, 0)] = q[i]
        Y[i][(0, 1, 0, 0)] = np.conj(q[i])
        Y[i][(0, 0, 1, 0)] = H[i]
        Y[i][(0, 0, 0, 1)] = np.conj(H[i])
    g = {}
    lamb = np.conj(lam)
    qb = np.conj(q); pb = np.conj(p)
    for n in range(2, TR+1):
        # ---- nonlinear terms of order n ----
        N = {}
        for k in range(2, n+1):
            for combo in itertools.combinations_with_replacement(range(4), k):
                cf = mult_count(combo)/factorial(k)
                nz = [i for i in range(4) if combo in Dk[k][i]]
                if not nz:
                    continue
                prod = Y[combo[0]]
                for c in combo[1:]:
                    prod = pmul(prod, Y[c])
                for idx, v in prod.items():
                    if deg(idx) != n:
                        continue
                    if idx not in N:
                        N[idx] = np.zeros(4, complex)
                    for i in nz:
                        N[idx][i] += cf*Dk[k][i][combo]*v
        # ---- transport terms of order n (g known only below order n) ----
        gb = {(a2, a1, a4, a3): np.conj(v) for (a1, a2, a3, a4), v in g.items()}
        Tt = {}
        for i in range(4):
            dz = {}; dzb = {}
            for idx, v in Y[i].items():
                if idx[0] >= 1:
                    kk2 = (idx[0]-1, idx[1], idx[2], idx[3])
                    dz[kk2] = dz.get(kk2, 0) + idx[0]*v
                if idx[1] >= 1:
                    kk2 = (idx[0], idx[1]-1, idx[2], idx[3])
                    dzb[kk2] = dzb.get(kk2, 0) + idx[1]*v
            tot = pmul(dz, g) if g else {}
            tot2 = pmul(dzb, gb) if gb else {}
            for src in (tot, tot2):
                for idx, v in src.items():
                    if deg(idx) != n:
                        continue
                    if idx not in Tt:
                        Tt[idx] = np.zeros(4, complex)
                    Tt[idx][i] += v
        # ---- solve order n ----
        idxs = sorted(set(list(N.keys()) + list(Tt.keys())))
        newg = {}
        for idx in idxs:
            j, k2, l, m = idx
            D = j*lam + k2*lamb + (l-m)*1j*wp
            rhs = N.get(idx, np.zeros(4, complex)) - Tt.get(idx, np.zeros(4, complex))
            if np.max(np.abs(rhs)) < 1e-14:
                continue
            if abs(D - lam) < 1e-7*max(1.0, abs(lam)):
                cg = np.vdot(p, rhs)
                newg[idx] = cg
                M = np.zeros((5, 5), complex)
                M[:4, :4] = D*I - A; M[:4, 4] = q; M[4, :4] = np.conj(p)
                sol = np.linalg.solve(M, np.concatenate([rhs - cg*q, [0.0]]))
                h = sol[:4]
            elif abs(D - lamb) < 1e-7*max(1.0, abs(lam)):
                cg = np.dot(p, rhs)          # <pbar, rhs>
                M = np.zeros((5, 5), complex)
                M[:4, :4] = D*I - A; M[:4, 4] = qb; M[4, :4] = p
                sol = np.linalg.solve(M, np.concatenate([rhs - cg*qb, [0.0]]))
                h = sol[:4]
            else:
                Mx = D*I - A
                cond = np.linalg.cond(Mx)
                if cond > 1e12:
                    out(f"    WARNING near-resonant index {idx} cond={cond:.1e}")
                h = np.linalg.solve(Mx, rhs)
            for i in range(4):
                if abs(h[i]) > 0:
                    Y[i][idx] = Y[i].get(idx, 0) + h[i]
        g.update(newg)
    hh = {idx: np.array([Y[i].get(idx, 0) for i in range(4)])
          for idx in ((0, 0, 2, 0), (0, 0, 1, 1), (0, 0, 0, 2))}
    return dict(lam=lam, q=q, p=p, st=st, A=A, H=H,
                c1=g.get((2, 1, 0, 0), 0), c_x=g.get((1, 0, 1, 1), 0),
                c2=g.get((3, 2, 0, 0), 0), c_xx=g.get((2, 1, 1, 1), 0),
                c_a4=g.get((1, 0, 2, 2), 0), h=hh)

def hopf(base):
    Ps = 3*base['V']**2/(4*base['Xg'])
    def reA(P):
        qd = dict(base, P=P); x = equil(qd)
        if x is None: return None
        cm = crit_mode(jac(x, qd))
        return None if cm is None else cm.real
    grid = np.linspace(0.05, 0.985, 60)*Ps
    va = [reA(P) for P in grid]; br = None
    for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
        if fa is not None and fb is not None and fa < 0 <= fb:
            br = (a, b); break
    lo, hi = br
    for _ in range(45):
        mm = 0.5*(lo+hi); v = reA(mm)
        if v is None or v >= 0: hi = mm
        else: lo = mm
    return 0.5*(lo+hi)
def tensors_at(pr, st):
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
def cx_hand(A, st, pr, q, p, w0, wp, fu):
    B2, C3 = tensors_at(pr, st); I = np.eye(4)
    H = np.linalg.solve(1j*wp*I - A, fu.astype(complex)); Hc = np.conj(H)
    gp = np.linalg.solve(1j*(w0+wp)*I - A, B2(q, H))
    gm = np.linalg.solve(1j*(w0-wp)*I - A, B2(q, Hc))
    d0 = -np.linalg.solve(A, B2(H, Hc))
    return (np.vdot(p, C3(q, H, Hc)) + np.vdot(p, B2(H, gm))
            + np.vdot(p, B2(Hc, gp)) + np.vdot(p, B2(q, d0)))

def guard_root(aeff, c1e, c2e):
    if abs(c2e) < 1e-14:
        return math.sqrt(max(aeff, 0.0)/c1e) if c1e > 0 and aeff > 0 else float('nan')
    disc = c1e**2 + 4*c2e*aeff
    if disc < 0: return float('nan')
    r2 = (-c1e + math.sqrt(disc))/(2*c2e)
    if r2 <= 0:
        r2 = (-c1e - math.sqrt(disc))/(2*c2e)
    return math.sqrt(r2) if r2 > 0 else float('nan')

CELLS = [('G1 V r=0.9', {}, 0.9, (0.05, 0.10, 0.15, 0.20)),
         ('idx17 r=0.92', dict(kp=55., ki=1200., Xg=0.40), 0.92, (0.08,))]
for tag, over, rat, margs in CELLS:
    prb = gset('G1', **over)
    PH = hopf(prb)
    prH = dict(prb, P=PH)
    stH = equil(prH)
    coH = nf_coeffs(prH)
    w0H = coH['w0']
    wpH = rat*w0H
    hstep = 1e-6
    fuH = (rhs(stH, dict(prH, V=prH['V']+hstep))
           - rhs(stH, dict(prH, V=prH['V']-hstep)))/(2*hstep)
    R = two_carrier_nf(prH, wpH, fuH)
    cxh = cx_hand(R['A'], stH, prH, R['q'], R['p'], w0H, wpH, fuH)
    out(f"=== {tag}: P_H={PH:.6f}, w0={w0H:.4f}, w_p={wpH:.4f}")
    out(f"    c1   = {R['c1']:.6e}   Kuznetsov {coH['c1']:.6e}  "
        f"reldiff {abs(R['c1']-coH['c1'])/abs(coH['c1']):.2e}")
    out(f"    c_x  = {R['c_x']:.6e}   hand-derived {cxh:.6e}  "
        f"reldiff {abs(R['c_x']-cxh)/abs(cxh):.2e}")
    out(f"    c2   = {R['c2']:.6e}")
    out(f"    c_xx = {R['c_xx']:.6e}   (ratio to 2 c1: "
        f"{R['c_xx'].real/(2*R['c1'].real):+.4f})")
    out(f"    c_a4 = {R['c_a4']:.6e}  [{time.time()-T0:.0f}s]")
    lam = R['lam']; p = R['p']; H = R['H']
    hh2 = R['h']
    for marg in margs:
        P0 = margin_point(prb, PH, marg)
        pr = dict(prb, P=P0)
        co = nf_coeffs(pr)
        st = co['st']; w0 = co['w0']; alpha = co['alpha']
        lamO = co['lam']; pvO = co['p']
        dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
        wp = rat*w0; Td = 2*math.pi/wp
        fV = (rhs(st, dict(pr, V=pr['V']+hstep))
              - rhs(st, dict(pr, V=pr['V']-hstep)))/(2*hstep)
        F = np.vdot(pvO, fV)
        J = abs(lamO)*abs(F)/abs(wp**2 + lamO**2)
        c1r = R['c1'].real; c2r = R['c2'].real
        cxr = R['c_x'].real; cxxr = R['c_xx'].real; ca4r = R['c_a4'].real
        pH2 = np.vdot(R['p'], hh2[(0, 0, 2, 0)])
        pH11 = np.vdot(R['p'], hh2[(0, 0, 1, 1)])
        pH02 = np.vdot(R['p'], hh2[(0, 0, 0, 2)])
        def kick(eps):
            a = 0.5*eps
            return abs(eps*J + (a*a)*(pH2 + pH11 + pH02))
        def gap(eps, order):
            a2 = 0.25*eps*eps
            if order == 3:
                aeff = alpha - cxr*a2
                return kick(eps) - guard_root(aeff, c1r, 0.0)
            aeff = alpha - cxr*a2 - ca4r*a2*a2
            return kick(eps) - guard_root(aeff, c1r + cxxr*a2, c2r)
        def solve_thr(order, seed):
            lo, hi = 1e-9, 6*seed
            for _ in range(200):
                mm = 0.5*(lo+hi); v = gap(mm, order)
                if not (v == v) or v > 0: hi = mm
                else: lo = mm
            return 0.5*(lo+hi)
        seed = math.sqrt(alpha/c1r)/J
        e3 = solve_thr(3, seed); e5 = solve_thr(5, seed)
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
        elo, ehi = 0.6*e5, 1.4*e5
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
        a2c = 0.25*emeas*emeas
        out(f"  alpha={alpha:.3f}: measured {emeas:.6e}   3rd order "
            f"{e3:.6e} {(e3-emeas)/emeas*100:+6.2f}%   5th order "
            f"{e5:.6e} {(e5-emeas)/emeas*100:+6.2f}%  [{time.time()-T0:.0f}s]")
        out(f"           Re c_xx a^2/Re c1 = {cxxr*a2c/c1r:+.4f}, "
            f"Re c_a4 a^4/alpha = {ca4r*a2c*a2c/alpha:+.4f}, "
            f"kick 2nd-order correction "
            f"{(kick(emeas)-emeas*J)/(emeas*J)*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
