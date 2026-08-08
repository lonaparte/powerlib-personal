"""Analytic 5th-order normal form at the Hopf point (GFL).
Order-by-order homological solution: exact Taylor tensors (sympy) ->
eigenbasis polynomial -> center manifold h(z,zb) to O(4) -> reduced
z-equation to O(5) -> Poincare normal form via near-identity removals:
c1 = resonant (2,1), c2 = resonant (3,2).
Validation: c1 must equal nf_coeffs' Kuznetsov value at the Hopf point;
then kappa(alpha) = 2*alpha*(1 + (Re c2/Re c1^2)*alpha) is predicted and
checked against the measured guard-cycle exponents (2 sets x 3 margins),
target <1%. Budget ~10 min.
"""
exec(open('selfhead.py').read())
import itertools, time
LOG = open('sweep20/nf5.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

TRUNC = 5

def pmul(a, b):
    r = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = tuple(x+y for x, y in zip(ka, kb))
            if sum(k) > TRUNC:
                continue
            r[k] = r.get(k, 0) + va*vb
    return r

def padd(a, b):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, 0) + v
    return r

def pscale(a, c):
    return {k: v*c for k, v in a.items()}

def ppow(a, n):
    r = {(0,)*len(next(iter(a))) if a else (0, 0): 1} if n == 0 else None
    if n == 0:
        return {(0, 0): 1}
    r = dict(a)
    for _ in range(n-1):
        r = pmul(r, a)
    return r

def porder(a, n):
    return {k: v for k, v in a.items() if sum(k) == n}

def conj2(a):
    # conjugate of a poly in (z,zb): swap exponents, conj coeffs
    return {(k[1], k[0]): np.conj(v) for k, v in a.items()}

def dz(a):
    r = {}
    for (j, k), v in a.items():
        if j > 0:
            r[(j-1, k)] = r.get((j-1, k), 0) + j*v
    return r

def dzb(a):
    r = {}
    for (j, k), v in a.items():
        if k > 0:
            r[(j, k-1)] = r.get((j, k-1), 0) + k*v
    return r

def run_set(tag, over, kap_meas):
    prb = gset('G1', **over)
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
    for _ in range(50):
        m = 0.5*(lo+hi)
        v = reA(m)
        if v is None or v >= 0: hi = m
        else: lo = m
    PH = 0.5*(lo+hi)
    pr = dict(prb, P=PH)
    st = equil(pr)
    A = jac(st, pr)
    from scipy.linalg import eig as _eig
    ev, VL, VR = _eig(A, left=True, right=True)
    idx = [i for i in range(4) if ev[i].imag > 1e-9]
    idx.sort(key=lambda i: -ev[i].real)
    kc, ks = idx[0], idx[1]
    lam, lams = ev[kc], ev[ks]
    q = VR[:, kc]; p = VL[:, kc]
    p = p/np.vdot(q, p)
    s = VR[:, ks]; ps = VL[:, ks]
    ps = ps/np.vdot(s, ps)
    out(f"{tag}: PH={PH:.6f} lam={lam:.6f} lams={lams:.4f}")
    # exact Taylor derivative tensors (orders 2..5) at st
    subsmap = {th_: st[0], xp_: st[1], Vdc_: st[2], xi_: st[3],
               P_: pr['P'], Q_: pr['Q'], V_: pr['V'], Xg_: pr['Xg'],
               kp_: pr['kp'], ki_: pr['ki'], kpv_: pr['kpv'],
               kiv_: pr['kiv'], C_: pr['C']}
    Dk = {}
    for k in range(2, 6):
        Dk[k] = [dict() for _ in range(4)]
        for i in range(4):
            base = f_[i]
            for combo in itertools.combinations_with_replacement(
                    range(4), k):
                e = base
                for j in combo:
                    e = sp.diff(e, _x[j])
                val = complex(e.subs(subsmap).evalf())
                if abs(val) > 1e-14:
                    Dk[k][i][combo] = val
        out(f"  order {k} tensors: "
            f"{sum(len(Dk[k][i]) for i in range(4))} nonzero "
            f"[{time.time()-T0:.0f}s]")
    # eigen-variable degree-1 polys (4 vars: z, zb, w, wb)
    qb, sb = np.conj(q), np.conj(s)
    U = [{(1, 0, 0, 0): q[j], (0, 1, 0, 0): qb[j],
          (0, 0, 1, 0): s[j], (0, 0, 0, 1): sb[j]} for j in range(4)]
    def mult_count(combo):
        c = 1
        for _, g in itertools.groupby(combo):
            c *= math.factorial(len(list(g)))
        return c
    # (pmul for 4-var keys)
    def pmul4(a, b):
        r = {}
        for ka, va in a.items():
            for kb, vb in b.items():
                kk = tuple(x+y for x, y in zip(ka, kb))
                if sum(kk) > TRUNC:
                    continue
                r[kk] = r.get(kk, 0) + va*vb
        return r
    P4 = [dict() for _ in range(4)]
    for k in range(2, 6):
        for i in range(4):
            for combo, val in Dk[k][i].items():
                term = {(0, 0, 0, 0): val/mult_count(combo)}
                for j in combo:
                    term = pmul4(term, U[j])
                for kk, vv in term.items():
                    P4[i][kk] = P4[i].get(kk, 0) + vv
    Gz4 = {}
    Gw4 = {}
    for i in range(4):
        for kk, vv in P4[i].items():
            Gz4[kk] = Gz4.get(kk, 0) + np.conj(p[i])*vv
            Gw4[kk] = Gw4.get(kk, 0) + np.conj(ps[i])*vv
    # center manifold h(z,zb) for w (orders 2..4); wb = conj-swap
    h = {}
    g = {}
    def compose(G4, hcur):
        hb = conj2(hcur)
        res = {}
        for (a2, b2, c2_, d2), v in G4.items():
            base = {(a2, b2): v}
            if c2_:
                hp = dict(hcur)
                for _ in range(c2_-1):
                    hp = pmul(hp, hcur)
                base = pmul(base, hp)
            if d2:
                hp = dict(hb)
                for _ in range(d2-1):
                    hp = pmul(hp, hb)
                base = pmul(base, hp)
            for kk, vv in base.items():
                res[kk] = res.get(kk, 0) + vv
        return res
    for n in range(2, 6):
        Gz2 = compose(Gz4, h)
        gn = porder(Gz2, n)
        for k, v in gn.items():
            g[k] = g.get(k, 0) + v
        if n <= 4:
            Gw2 = compose(Gw4, h)
            gb = conj2(g)
            known = padd(pmul(dz(h), padd({(1, 0): lam}, g)),
                         pmul(dzb(h), padd({(0, 1): np.conj(lam)}, gb)))
            rhs_n = porder(padd(Gw2, pscale(known, -1)), n)
            for (j, k), v in rhs_n.items():
                den = j*lam + k*np.conj(lam) - lams
                h[(j, k)] = h.get((j, k), 0) + v/den
    # Poincare NF removals on zdot = lam*z + g
    def transform(gcur, j, k, phi):
        T = {(1, 0): 1.0, (j, k): phi}
        Tz = dz(T); Tzb = dzb(T)
        G = dict(gcur)
        for _ in range(4):
            gT = {}
            for (a2, b2), v in gcur.items():
                term = {(0, 0): v}
                for _ in range(a2):
                    term = pmul(term, T)
                Tb = conj2(T)
                for _ in range(b2):
                    term = pmul(term, Tb)
                for kk, vv in term.items():
                    gT[kk] = gT.get(kk, 0) + vv
            Gb = conj2(G)
            rhs = padd(pscale({kk: vv for kk, vv in T.items()
                               if kk != (1, 0)}, lam), gT)
            rhs = padd(rhs, pscale(pmul(
                {kk: vv for kk, vv in Tz.items() if kk != (0, 0)},
                padd({(1, 0): lam}, G)), -1))
            rhs = padd(rhs, pscale(pmul(
                Tzb, padd({(0, 1): np.conj(lam)}, Gb)), -1))
            G = {kk: vv for kk, vv in rhs.items() if sum(kk) >= 2}
        return G
    gnf = dict(g)
    for n in range(2, 6):
        for (j, k) in sorted([kk for kk in gnf if sum(kk) == n]):
            if (j, k) in ((2, 1), (3, 2)):
                continue
            den = j*lam + k*np.conj(lam) - lam
            if abs(den) < 1e-9:
                continue
            phi = gnf[(j, k)]/den
            gnf = transform(gnf, j, k, phi)
    c1 = gnf.get((2, 1), 0)
    c2 = gnf.get((3, 2), 0)
    co_ref = nf_coeffs(pr)
    out(f"  c1(homological)={c1:.4f}  c1(Kuznetsov)={co_ref['c1']:.4f} "
        f"reldiff={abs(c1-co_ref['c1'])/abs(co_ref['c1']):.2e}")
    out(f"  c2={c2:.4f}  C_set=Re(c2)/Re(c1)^2={c2.real/c1.real**2:+.5f}")
    C = c2.real/c1.real**2
    for al, km in kap_meas:
        kp2 = 2*al*(1 + C*al)
        out(f"  alpha={al}: kappa_pred={kp2:.5f} kappa_meas={km:.5f} "
            f"err={(kp2-km)/km*100:+.2f}%  (2a-only err="
            f"{(2*al-km)/km*100:+.2f}%)")

run_set('G1', {}, [(0.05, 0.09982), (0.10, 0.19924), (0.20, 0.39676)])
run_set('Xg=0.70', dict(Xg=0.70),
        [(0.05, 0.10127), (0.10, 0.20516), (0.20, 0.42121)])
out(f"DONE wall={time.time()-T0:.0f}s")
