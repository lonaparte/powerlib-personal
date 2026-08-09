"""mix16 erosion >1% closure: kick-threshold prediction via the
shifted-origin 5th-order Taylor model (protocol-identical events),
replacing the affine-fiber prediction whose tangent-plane truncation
accumulates curvature error over the kick distance (~2e-2).
Cases: mix16 bg=0 (anchor, fiber -0.97%), bg=P 0.6x (fiber -1.98%),
bg=Q 0.6x (fiber -1.75%). Measured values from pqgflerosion.log.
Budget ~20 min.
"""
exec(open('selfhead.py').read())
import itertools, time
LOG = open('sweep20/t5kick.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
from scipy.interpolate import CubicSpline

_Q4l = [dict() for _ in range(4)]
_Q5l = [dict() for _ in range(4)]
for i in range(4):
    for combo in itertools.combinations_with_replacement(range(4), 4):
        e = f_[i]
        for j in combo:
            e = sp.diff(e, _x[j])
        _Q4l[i][combo] = sp.lambdify(_args, e, 'numpy')
    for combo in itertools.combinations_with_replacement(range(4), 5):
        e = f_[i]
        for j in combo:
            e = sp.diff(e, _x[j])
        _Q5l[i][combo] = sp.lambdify(_args, e, 'numpy')

prb = gset('G1', kp=45., ki=900., Xg=0.55)
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
P0 = margin_point(prb, 0.5*(lo+hi), 0.10)
pr = dict(prb, P=P0)
co = nf_coeffs(pr)
st0 = co['st']; w0 = co['w0']; qv = co['q']
wd = 0.9*w0
Td = 2*math.pi/wd
khat = 2*np.real(qv)
out(f"mix16: P0={P0:.5f} w0={w0:.3f}")

CASES = [('bg=0', None, 0.0, 2.0603e-2),
         ('bg=P', 'P', 0.6*1.0057e-3, 1.7916e-2),
         ('bg=Q', 'Q', 0.6*1.0757e-3, 1.7938e-2)]

def build_grid(key, u0, half):
    """tensor grid over the forcing parameter."""
    ug = u0 + np.linspace(-1.05*half, 1.05*half, 41) if half > 0 \
        else np.array([u0 - 1e-4, u0, u0 + 1e-4])
    n = len(ug)
    sts = np.zeros((n, 4)); Ag = np.zeros((n, 4, 4))
    Hg = np.zeros((n, 4, 4, 4)); Cg = np.zeros((n, 4, 4, 4, 4))
    D4g = np.zeros((n, 4, 4, 4, 4, 4))
    D5g = np.zeros((n, 4, 4, 4, 4, 4, 4))
    for iu, uq in enumerate(ug):
        pri = dict(pr, **{key: uq})
        stq = equil(pri)
        sts[iu] = stq
        Ag[iu] = jac(stq, pri)
        av = _avl(stq, pri)
        for i in range(4):
            for j in range(4):
                for k in range(4):
                    Hg[iu, i, j, k] = float(_Hl[i][j][k](*av))
                    for l in range(4):
                        Cg[iu, i, j, k, l] = float(_Tl[i][j][k][l](*av))
        for i in range(4):
            for combo, fn in _Q4l[i].items():
                val = float(fn(*av))
                if val == 0.0:
                    continue
                for perm in set(itertools.permutations(combo)):
                    D4g[(iu, i) + perm] = val
            for combo, fn in _Q5l[i].items():
                val = float(fn(*av))
                if val == 0.0:
                    continue
                for perm in set(itertools.permutations(combo)):
                    D5g[(iu, i) + perm] = val
    st_u = np.gradient(sts, ug[1]-ug[0], axis=0)
    return (ug, CubicSpline(ug, sts), CubicSpline(ug, st_u),
            CubicSpline(ug, Ag), CubicSpline(ug, Hg),
            CubicSpline(ug, Cg), CubicSpline(ug, D4g),
            CubicSpline(ug, D5g))

for tag, key, ebg, meas in CASES:
    k2 = key if key else 'P'
    u0 = pr[k2]
    ug, spst, spstU, spA, spH, spC, spD4, spD5 = build_grid(k2, u0, ebg)
    ulo, uhi = ug[0], ug[-1]
    out(f"{tag}: grid done [{time.time()-T0:.0f}s]")
    Tset = Td*math.ceil(150/Td)
    def esc_model(kap):
        def fT(t, w, kicked):
            uq = u0 + ebg*math.cos(wd*t)
            uq = min(max(uq, ulo), uhi)
            ud = -ebg*wd*math.sin(wd*t)
            dw = (spA(uq) @ w
                  + 0.5*np.einsum('ijk,j,k->i', spH(uq), w, w)
                  + np.einsum('ijkl,j,k,l->i', spC(uq), w, w, w)/6.0
                  + np.einsum('ijklm,j,k,l,m->i', spD4(uq),
                              w, w, w, w)/24.0
                  + np.einsum('ijklmn,j,k,l,m,n->i', spD5(uq),
                              w, w, w, w, w)/120.0
                  - spstU(uq)*ud)
            return dw
        if ebg > 0:
            s1 = solve_ivp(lambda t, w: fT(t, w, False), (0, Tset),
                           np.zeros(4), method='DOP853', rtol=1e-10,
                           atol=1e-13)
            wb = s1.y[:, -1]
        else:
            wb = np.zeros(4)
        wk = wb + kap*khat
        def e_th(t, w):
            uq = min(max(u0 + ebg*math.cos(wd*t), ulo), uhi)
            return abs(w[0] + spst(uq)[0] - st0[0]) - 1.2
        def e_vlo(t, w):
            uq = min(max(u0 + ebg*math.cos(wd*t), ulo), uhi)
            return w[2] + spst(uq)[2] - 0.2
        def e_vhi(t, w):
            uq = min(max(u0 + ebg*math.cos(wd*t), ulo), uhi)
            return w[2] + spst(uq)[2] - 2.5
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(lambda t, w: fT(t, w, True), (Tset, Tset+150),
                      wk, method='DOP853', rtol=1e-9, atol=1e-13,
                      events=(e_th, e_vlo, e_vhi))
        return (any(len(t) > 0 for t in s.t_events) or s.status < 0)
    klo, khi = 0.0, 1.5*meas
    if not esc_model(khi):
        khi = 3.0*meas
        if not esc_model(khi):
            out(f"  {tag}: model no escape at {khi:.3e}"); continue
    for _ in range(12):
        km = 0.5*(klo+khi)
        if esc_model(km): khi = km
        else: klo = km
    pred = 0.5*(klo+khi)
    out(f"  RESULT {tag}: T5 pred={pred:.4e} meas={meas:.4e} "
        f"err={(pred-meas)/meas*100:+.2f}% [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
