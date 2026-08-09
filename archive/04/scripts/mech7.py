"""The last named term: the drive acts multiplicatively too.

mech6 shows the 4D Taylor field reproduces the exact threshold to +0.14%
at order 3 AND at order 4 on the V cell -- a residual that does not fall
when the polynomial order rises, so it is not a Taylor truncation.  The
difference between the two runs is that the exact field carries the drive
inside the parameter (V0 + eps cos), so the drive also modulates A, B, C,
while the Taylor run (and the two-carrier reduction so far) kept only the
additive part f_u.  The missing object is the multiplicative channel
    M1 = dA/du,  f_uu = d^2 f/du^2,  d^2 f/dy du, ...
the same object that produces the parametric tongues, here acting on the
direct-forcing problem.

It is added without any new machinery by treating the drive as a fifth
expansion variable: with u = alpha + alphabar the field is expanded in
(y, u) jointly,
    F = sum_{k,m} (1/(k! m!)) d^{k+m}f/dy^k du^m [y^k] u^m ,
and since u is itself degree one in the carrier variables the whole
two-carrier homological solution runs unchanged -- only the tensor list
grows from four variables to five.  Consequences that were missing
before: the O(a^2) shift of the operating point through f_uu, the
parametric contributions to c_x through d^2f/dy du, and their fifth-order
partners in c_xx and c_a4.

Checks: c1 must be unchanged (it has no u dependence), and the additive
part of c_x must reproduce the earlier hand-derived value.  Then the
threshold on the V cell (four margins) and idx17.
Budget ~30 min.
"""
exec(open('selfhead.py').read())
import itertools, time
from math import factorial
LOG = open('sweep20/mech7.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
TR = 5
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']; cx_hand = _ns['cx_hand']; pmul = _ns['pmul']
deg = _ns['deg']; mult_count = _ns['mult_count']

def tensors5(pr, st):
    """d^{k} f_i / d(th,xp,Vdc,xi,V)^k at (st, V0), k = 2..5."""
    vars5 = list(_x) + [V_]
    subs = {th_: st[0], xp_: st[1], Vdc_: st[2], xi_: st[3],
            P_: pr['P'], Q_: pr['Q'], V_: pr['V'], Xg_: pr['Xg'],
            kp_: pr['kp'], ki_: pr['ki'], kpv_: pr['kpv'],
            kiv_: pr['kiv'], C_: pr['C']}
    Dk = {}
    for k in range(2, 6):
        Dk[k] = [dict() for _ in range(4)]
        for i in range(4):
            for combo in itertools.combinations_with_replacement(range(5), k):
                e = f_[i]
                for j in combo:
                    e = sp.diff(e, vars5[j])
                val = complex(e.subs(subs).evalf())
                if abs(val) > 1e-13:
                    Dk[k][i][combo] = val
    return Dk

def two_carrier_nf5(pr, wp, fu, param=True):
    st = equil(pr); A = jac(st, pr)
    from scipy.linalg import eig as _eig
    ev, VL, VR = _eig(A, left=True, right=True)
    kk = max((i for i in range(4) if ev[i].imag > 1e-9),
             key=lambda i: ev[i].real)
    lam = ev[kk]; q = VR[:, kk]; p = VL[:, kk]; p = p/np.vdot(q, p)
    Dk = tensors5(pr, st)
    if not param:                       # drop every derivative touching u
        for k in Dk:
            for i in range(4):
                Dk[k][i] = {c: v for c, v in Dk[k][i].items() if 4 not in c}
    I = np.eye(4)
    H = np.linalg.solve(1j*wp*I - A, fu.astype(complex))
    Y = [dict() for _ in range(5)]
    for i in range(4):
        Y[i][(1, 0, 0, 0)] = q[i]; Y[i][(0, 1, 0, 0)] = np.conj(q[i])
        Y[i][(0, 0, 1, 0)] = H[i]; Y[i][(0, 0, 0, 1)] = np.conj(H[i])
    Y[4][(0, 0, 1, 0)] = 1.0 + 0j; Y[4][(0, 0, 0, 1)] = 1.0 + 0j
    g = {}; lamb = np.conj(lam); qb = np.conj(q)
    for n in range(2, TR+1):
        N = {}
        for k in range(2, n+1):
            for combo in itertools.combinations_with_replacement(range(5), k):
                nz = [i for i in range(4) if combo in Dk[k][i]]
                if not nz:
                    continue
                cf = mult_count(combo)/factorial(k)
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
        gb = {(b, a, d, c): np.conj(v) for (a, b, c, d), v in g.items()}
        Tt = {}
        for i in range(4):
            dz = {}; dzb = {}
            for idx, v in Y[i].items():
                if idx[0] >= 1:
                    k2 = (idx[0]-1, idx[1], idx[2], idx[3])
                    dz[k2] = dz.get(k2, 0) + idx[0]*v
                if idx[1] >= 1:
                    k2 = (idx[0], idx[1]-1, idx[2], idx[3])
                    dzb[k2] = dzb.get(k2, 0) + idx[1]*v
            for src in ((pmul(dz, g) if g else {}),
                        (pmul(dzb, gb) if gb else {})):
                for idx, v in src.items():
                    if deg(idx) != n:
                        continue
                    if idx not in Tt:
                        Tt[idx] = np.zeros(4, complex)
                    Tt[idx][i] += v
        newg = {}
        for idx in sorted(set(list(N.keys()) + list(Tt.keys()))):
            j, k2, l, m = idx
            D = j*lam + k2*lamb + (l-m)*1j*wp
            rhs_v = (N.get(idx, np.zeros(4, complex))
                     - Tt.get(idx, np.zeros(4, complex)))
            if np.max(np.abs(rhs_v)) < 1e-14:
                continue
            if abs(D - lam) < 1e-7*max(1.0, abs(lam)):
                cg = np.vdot(p, rhs_v); newg[idx] = cg
                M = np.zeros((5, 5), complex)
                M[:4, :4] = D*I - A; M[:4, 4] = q; M[4, :4] = np.conj(p)
                h = np.linalg.solve(M, np.concatenate([rhs_v - cg*q, [0.0]]))[:4]
            elif abs(D - lamb) < 1e-7*max(1.0, abs(lam)):
                cg = np.dot(p, rhs_v)
                M = np.zeros((5, 5), complex)
                M[:4, :4] = D*I - A; M[:4, 4] = qb; M[4, :4] = p
                h = np.linalg.solve(M, np.concatenate([rhs_v - cg*qb, [0.0]]))[:4]
            else:
                h = np.linalg.solve(D*I - A, rhs_v)
            for i in range(4):
                if abs(h[i]) > 0:
                    Y[i][idx] = Y[i].get(idx, 0) + h[i]
        g.update(newg)
    return dict(lam=lam, q=q, p=p, st=st, A=A, H=H,
                c1=g.get((2, 1, 0, 0), 0), c_x=g.get((1, 0, 1, 1), 0),
                c2=g.get((3, 2, 0, 0), 0), c_xx=g.get((2, 1, 1, 1), 0),
                c_a4=g.get((1, 0, 2, 2), 0))

def guard_root(aeff, c1e, c2e):
    if aeff <= 0.0 or c1e <= 0.0:
        return float('nan')
    if abs(c2e)*aeff < 1e-12*c1e**2:
        return math.sqrt(aeff/c1e)
    disc = c1e**2 + 4*c2e*aeff
    if disc < 0.0:
        return float('nan')
    r2 = (-c1e + math.sqrt(disc))/(2*c2e)
    return math.sqrt(r2) if r2 > 0 else float('nan')

CELLS = [('G1 V r=0.9', {}, 0.9, (0.05, 0.10, 0.15, 0.20)),
         ('idx17 r=0.92', dict(kp=55., ki=1200., Xg=0.40), 0.92, (0.08,))]
for tag, over, rat, margs in CELLS:
    prb = gset('G1', **over)
    PH = hopf(prb)
    prH = dict(prb, P=PH); stH = equil(prH); coH = nf_coeffs(prH)
    w0H = coH['w0']; wpH = rat*w0H
    hs = 1e-6
    fuH = (rhs(stH, dict(prH, V=prH['V']+hs))
           - rhs(stH, dict(prH, V=prH['V']-hs)))/(2*hs)
    Rp = two_carrier_nf5(prH, wpH, fuH, param=True)
    Ra = two_carrier_nf5(prH, wpH, fuH, param=False)
    cxa = cx_hand(Ra['A'], stH, prH, Ra['q'], Ra['p'], w0H, wpH, fuH)
    out(f"=== {tag}: P_H={PH:.6f}")
    out(f"    c1 additive {Ra['c1']:.6e} | with parametric {Rp['c1']:.6e} "
        f"| Kuznetsov {coH['c1']:.6e}")
    out(f"    c_x additive {Ra['c_x']:.6e} (hand {cxa:.6e}, reldiff "
        f"{abs(Ra['c_x']-cxa)/abs(cxa):.1e})")
    out(f"    c_x FULL     {Rp['c_x']:.6e}   parametric share of Re: "
        f"{(Rp['c_x'].real-Ra['c_x'].real)/Rp['c_x'].real*100:+.2f}%")
    out(f"    Re c2 {Rp['c2'].real:.5e} (add {Ra['c2'].real:.5e}) | "
        f"Re c_xx {Rp['c_xx'].real:.5e} (add {Ra['c_xx'].real:.5e}) | "
        f"Re c_a4 {Rp['c_a4'].real:.5e} (add {Ra['c_a4'].real:.5e})  "
        f"[{time.time()-T0:.0f}s]")
    for marg in margs:
        P0 = margin_point(prb, PH, marg)
        pr = dict(prb, P=P0); co = nf_coeffs(pr)
        st = co['st']; w0 = co['w0']; alpha = co['alpha']
        lam = co['lam']; pv = co['p']; qv = co['q']; c1 = co['c1']
        A = jac(st, pr)
        dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
        wp = rat*w0; Td = 2*math.pi/wp
        fV = (rhs(st, dict(pr, V=pr['V']+hs))
              - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
        # c_x at the operating point: additive part from the closed
        # formula plus the parametric increment measured at P_H
        cx_add_O = cx_hand(A, st, pr, qv, pv, w0, wp, fV)
        dcx = Rp['c_x'].real - Ra['c_x'].real
        J = abs(lam)*abs(np.vdot(pv, fV))/abs(wp**2 + lam**2)
        c1r = c1.real
        for label, cxr, c2r, cxxr, ca4r in (
                ('additive only', cx_add_O.real, Ra['c2'].real,
                 Ra['c_xx'].real, Ra['c_a4'].real),
                ('with parametric', cx_add_O.real + dcx, Rp['c2'].real,
                 Rp['c_xx'].real, Rp['c_a4'].real)):
            def gap(eps):
                a2 = 0.25*eps*eps
                aeff = alpha - cxr*a2 - ca4r*a2*a2
                rgv = guard_root(aeff, c1r + cxxr*a2, c2r)
                return 1.0 if not (rgv == rgv) else eps*J - rgv
            lo, hi = 1e-12, 4*math.sqrt(alpha/c1r)/J
            e = float('nan')
            if gap(hi) > 0:
                for _ in range(200):
                    mm = 0.5*(lo+hi)
                    if gap(mm) > 0: hi = mm
                    else: lo = mm
                e = 0.5*(lo+hi)
            if label == 'additive only':
                e_add = e
            else:
                e_par = e
        NPw = 1000 if rat == 0.9 else 4000
        def probe(eps, NPn):
            def f(t, x):
                return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
            def e_th(t, x): return abs(x[0] - st[0]) - dsad
            def e_vlo(t, x): return x[2] - 0.20*Vdc0
            def e_vhi(t, x): return x[2] - 2.50*Vdc0
            for ee in (e_th, e_vlo, e_vhi):
                ee.terminal = True
            e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
            s = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                          rtol=1e-10, atol=1e-13,
                          events=(e_th, e_vlo, e_vhi))
            return (any(len(s.t_events[i]) > 0 for i in range(3))
                    or s.status < 0)
        elo, ehi = 0.6*e_par, 1.4*e_par
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
        out(f"  alpha={alpha:.3f} measured {emeas:.6e} | additive only "
            f"{(e_add-emeas)/emeas*100:+6.2f}% | with parametric "
            f"{(e_par-emeas)/emeas*100:+6.2f}%  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
