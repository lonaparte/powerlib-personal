"""Self-check on the multi-tone closure: the comparison was not controlled.

noise1j concluded "the coefficients were never wrong, the scalar comparison
was", from mean |err| 2.862% -> 0.521%.  Re-reading the two predictors, they
do not differ in one thing.  They differ in TWO:

    closed form :  guard_root(alpha_eff, c1 + c_xx a2t, c2)   <- fifth order IN
                   |Z(0)| > rho_g                             <- beats OUT
    reduced ODE :  zetadot = -alpha z + c1 z|z|^2 + E(t) z    <- beats IN,
                                                                 fifth order OUT

So the improvement could be the beats, or it could be that dropping c_2,
c_xx and c_a4 happens to help.  Attributing it to the beats was not earned.

And there is a specific reason to suspect the omission matters: the two
WORST reduced-ODE cells are exactly the two cells with the largest fifth-
order content.

    cell                  a^4/alpha    reduced-ODE err
    0.7-0.8 s7  N=16       13.3%          +1.54%   <- worst
    0.7-0.8 s23 N= 4        9.5%          +1.16%   <- second worst

That is not a coincidence pattern one should publish an attribution over.
The stated home of the residual ("the narrow-band approximation for the
cross coefficients") is therefore probably wrong too.

Three controls, all cheap:

 A. DC-ONLY reduced ODE -- integrate the same equation with E(t) replaced by
    its time average.  For a constant E the cubic radial equation has
    rho_g as its exact separatrix, so this MUST reproduce the closed form.
    If it does, the integration method and the escape surface are not doing
    the work, and the beats are isolated.  If it does not, the whole
    attribution collapses.
 B. FULL reduced ODE -- beats AND the fifth-order terms (c_2 rho^5, c_xx,
    c_a4 driven by the instantaneous E(t)).  Then the two predictors differ
    in exactly one thing, and the two high-a^4 cells are the test.
 C. cross-coefficient sensitivity -- redo with c_x^{jk} taken as the
    geometric mean and as c_x at the midpoint frequency instead of the
    arithmetic mean.  If the answer barely moves, the closure does not
    depend on a guess; if it moves by the size of the residual, then the
    residual IS the guess and that should be said instead.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time, re
LOG = open('sweep20/noise1k.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']; cx_hand = _ns['cx_hand']
hs = 1e-6

prb = gset('G1'); PH = hopf(prb)
prH = dict(prb, P=PH); stH = equil(prH); coH = nf_coeffs(prH)
w0H = coH['w0']
AH = jac(stH, prH)
evH, VLH, VRH = eig(AH, left=True, right=True)
kH = max((i for i in range(4) if evH[i].imag > 1e-9),
         key=lambda i: evH[i].real)
lamH = evH[kH]; qH = VRH[:, kH]; pH = VLH[:, kH]; pH = pH/np.vdot(qH, pH)
fuH = (rhs(stH, dict(prH, V=prH['V']+hs))
       - rhs(stH, dict(prH, V=prH['V']-hs)))/(2*hs)
SYH = {P_: prH['P'], Q_: prH['Q'], V_: prH['V'], Xg_: prH['Xg'],
       kp_: prH['kp'], ki_: prH['ki'], kpv_: prH['kpv'],
       kiv_: prH['kiv'], C_: prH['C']}
DkV = make_tensors5(sp, f_, _x, SYH, prH, stH, V_)
R5 = solve_nf5(AH, lamH, qH, pH, fuH, 0.90*w0H, DkV, param=True)
R5a = solve_nf5(AH, lamH, qH, pH, fuH, 0.90*w0H, DkV, param=False)

P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr)
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
cx_ref = cx_hand(A, st, pr, qv, pv, w0, 0.90*w0, fV).real
dpar = R5['c_x'].real - R5a['c_x'].real
par_frac = dpar/(cx_ref + dpar)
c2r = R5['c2'].real; cxxr = R5['c_xx'].real; ca4r = R5['c_a4'].real
c1r = c1.real
rg0 = math.sqrt(alpha/c1r)
out(f"G1 margin 0.10: alpha={alpha:.6f}  Re c1={c1r:.6e}  Re c2={c2r:.5e}")
out(f"  Re c_xx={cxxr:.5e}  Re c_a4={ca4r:.5e}  rho_g(0)={rg0:.5e}")

_cache = {}


def cx_of(wk):
    k = round(wk, 9)
    if k not in _cache:
        _cache[k] = cx_hand(A, st, pr, qv, pv, w0, wk, fV).real \
            / (1.0 - par_frac)
    return _cache[k]


def patch(N, lo, hi, seed):
    rng = np.random.default_rng(seed)
    rs = np.linspace(lo, hi, N) if N > 1 else np.array([0.5*(lo+hi)])
    rs = rs*(1 + 1e-3*rng.standard_normal(N))
    phs = rng.uniform(0, 2*math.pi, N)
    return [(rs[i]*w0, 1.0/math.sqrt(N), float(phs[i])) for i in range(N)]


def kick_c(tu, eps):
    Z = 0.0 + 0j
    for wk, rk, ph in tu:
        aa = 0.5*eps*rk*np.exp(1j*ph)
        Hp = np.linalg.solve(1j*wk*np.eye(4) - A, fV.astype(complex))
        Hm = np.linalg.solve(-1j*wk*np.eye(4) - A, fV.astype(complex))
        Z -= (aa*np.vdot(pv, Hp) + np.conj(aa)*np.vdot(pv, Hm))
    return Z


def closed_form(tu, fifth=True):
    def gap(eps):
        a2s = [0.25*(eps*rk)**2 for _, rk, _ in tu]
        a2t = sum(a2s)
        aeff = alpha - sum(cx_of(wk)*a2 for (wk, _, _), a2 in zip(tu, a2s))
        if fifth:
            aeff -= sum(ca4r*a2*a2 for a2 in a2s)
            rg = guard_root(aeff, c1r + cxxr*a2t, c2r)
        else:
            rg = guard_root(aeff, c1r, 0.0)
        if not (rg == rg):
            return 1.0
        return abs(kick_c(tu, eps)) - rg
    lo, hi = 1e-12, 2.0
    if gap(hi) <= 0:
        return float('nan')
    for _ in range(200):
        m = 0.5*(lo+hi)
        if gap(m) > 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)


def make_E(tu, eps, xmode, dc_only):
    ws = np.array([wk for wk, _, _ in tu])
    aa = np.array([0.5*eps*rk*np.exp(1j*ph) for _, rk, ph in tu])
    cxv = np.array([cx_of(wk) for wk in ws])
    if xmode == 'arith':
        CX = 0.5*(cxv[:, None] + cxv[None, :])
    elif xmode == 'geom':
        CX = np.sqrt(np.abs(cxv[:, None]*cxv[None, :])) \
            * np.sign(cxv[:, None]*cxv[None, :])
    else:                      # c_x at the midpoint frequency
        CX = np.array([[cx_of(0.5*(wj+wk)) for wk in ws] for wj in ws])
    M = CX*(aa[:, None]*np.conj(aa)[None, :])
    dw = ws[:, None] - ws[None, :]
    Edc = float(np.real(np.trace(M)))
    if dc_only:
        return (lambda t: Edc), Edc
    if xmode == 'arith':
        ac = cxv*aa

        def E(t):
            e = np.exp(1j*ws*t)
            return float(np.real(np.dot(ac, e)*np.conj(np.dot(aa, e))))
    else:
        def E(t):
            return float(np.real(np.sum(M*np.exp(1j*dw*t))))
    return E, Edc


def red_escape(tu, eps, xmode='arith', dc_only=False, fifth=False):
    E, Edc = make_E(tu, eps, xmode, dc_only)
    a2t = sum(0.25*(eps*rk)**2 for _, rk, _ in tu)
    Z0 = kick_c(tu, eps)
    lim = 3.0*rg0

    def f(t, y):
        z = y[0] + 1j*y[1]
        r2 = abs(z)**2
        c1e = c1 + (cxxr*a2t if fifth else 0.0)
        dz = (-alpha + 0j)*z + c1e*z*r2 + E(t)*z
        if fifth:
            a4 = sum((0.25*(eps*rk)**2)**2 for _, rk, _ in tu)
            dz = dz + c2r*z*r2*r2 - ca4r*a4*z
        return [dz.real, dz.imag]

    def ev(t, y):
        return math.hypot(y[0], y[1]) - lim
    ev.terminal = True; ev.direction = 1

    def dead(t, y):
        return math.hypot(y[0], y[1]) - 1e-4*rg0
    dead.terminal = True; dead.direction = -1
    s = solve_ivp(f, (0, 60.0/alpha), [Z0.real, Z0.imag], method='DOP853',
                  rtol=1e-9, atol=1e-18, events=(ev, dead))
    return len(s.t_events[0]) > 0 or s.status < 0


def red_thr(tu, seed, **kw):
    lo, hi = 0.6*seed, 1.4*seed
    n = 0
    while not red_escape(tu, hi, **kw) and n < 14:
        lo = hi; hi *= 1.25; n += 1
    n = 0
    while red_escape(tu, lo, **kw) and n < 14:
        hi = lo; lo *= 0.8; n += 1
    if red_escape(tu, lo, **kw) or not red_escape(tu, hi, **kw):
        return float('nan')
    for _ in range(24):
        m = 0.5*(lo+hi)
        if red_escape(tu, m, **kw): hi = m
        else: lo = m
    return 0.5*(lo+hi)


CASES = []
for ln in open('sweep20/noise1b.log').read().split('\n'):
    m = re.match(r'\s*(\d+)\s*\|\s*[\d.]+\s*\|\s*[\d.]+\s*\|\s*'
                 r'([\d.eE+-]+)\s*\|', ln)
    if m:
        CASES.append((f'0.85-0.95 s7  N={m.group(1):>3s}',
                      patch(int(m.group(1)), 0.85, 0.95, 7),
                      float(m.group(2))))
for ln in open('sweep20/noise1c.log').read().split('\n'):
    m = re.match(r'\s*([\d.]+)-([\d.]+)\s+s(\d+)\s*\|\s*(\d+)\s*\|'
                 r'\s*[\d.]+\s*\|\s*([\d.eE+-]+)\s*\|', ln)
    if m:
        lo_, hi_ = float(m.group(1)), float(m.group(2))
        if hi_ > 0.93:
            continue
        CASES.append((f'{lo_}-{hi_} s{m.group(3):<2s} N={m.group(4):>3s}',
                      patch(int(m.group(4)), lo_, hi_, int(m.group(3))),
                      float(m.group(5))))

out("")
out("=== A. control: reduced ODE with the DC part only")
out("    must reproduce the closed form (constant E => rho_g is the exact")
out("    separatrix of the cubic radial equation)")
out("  cell                    | closed(no 5th) | ODE DC-only | diff")
dmax = 0.0
for tag, tu, em in CASES:
    cf = closed_form(tu, fifth=False)
    dc = red_thr(tu, cf, dc_only=True, fifth=False)
    d = (dc-cf)/cf*100
    dmax = max(dmax, abs(d))
    out(f"  {tag} | {cf:.6e} | {dc:.6e} | {d:+7.3f}%")
out(f"    worst |diff| = {dmax:.3f}%  -> "
    f"{'control PASSES' if dmax < 0.5 else 'CONTROL FAILS'}")

out("")
out("=== B. the two predictors differing in exactly one thing")
out("  cell                    | measured   | closed(5th) | ODE beats+5th |"
    " ODE beats only")
e_c = []; e_b5 = []; e_b = []
for tag, tu, em in CASES:
    cf = closed_form(tu, fifth=True)
    b5 = red_thr(tu, cf, dc_only=False, fifth=True)
    bo = red_thr(tu, cf, dc_only=False, fifth=False)
    dc_ = (cf-em)/em*100; d5 = (b5-em)/em*100; do = (bo-em)/em*100
    e_c.append(abs(dc_)); e_b5.append(abs(d5)); e_b.append(abs(do))
    a4f = ca4r*(0.25*em*em)**2/alpha*100
    out(f"  {tag} | {em:.4e} | {dc_:+7.2f}% | {d5:+9.2f}% | {do:+9.2f}%"
        f"   (a^4/alpha {a4f:5.2f}%)")
e_c = np.array(e_c); e_b5 = np.array(e_b5); e_b = np.array(e_b)
out(f"    mean |err|  closed(5th) {e_c.mean():.3f}%  "
    f"ODE beats+5th {e_b5.mean():.3f}%  ODE beats only {e_b.mean():.3f}%")
out(f"    max  |err|  closed(5th) {e_c.max():.3f}%  "
    f"ODE beats+5th {e_b5.max():.3f}%  ODE beats only {e_b.max():.3f}%")

out("")
out("=== C. sensitivity to the cross-coefficient guess")
out("  cell                    | arith mean | geom mean | midpoint freq")
sp = []
for tag, tu, em in CASES:
    cf = closed_form(tu, fifth=True)
    va = red_thr(tu, cf, xmode='arith', fifth=True)
    vg = red_thr(tu, cf, xmode='geom', fifth=True)
    vm = red_thr(tu, cf, xmode='mid', fifth=True)
    vals = [v for v in (va, vg, vm) if v == v]
    spread = (max(vals)-min(vals))/np.mean(vals)*100 if len(vals) > 1 else 0.0
    sp.append(spread)
    out(f"  {tag} | {(va-em)/em*100:+8.2f}% | {(vg-em)/em*100:+8.2f}% | "
        f"{(vm-em)/em*100:+8.2f}%   spread {spread:.3f}%")
out(f"    worst spread across the three interpolations: {max(sp):.3f}%")
out("")
out("  read: if A passes, B shows beats+5th beating both others, and C's")
out("  spread is well under the residual, then the attribution stands and")
out("  the residual's home is the fifth-order terms, not the cross guess.")
out(f"DONE wall={time.time()-T0:.0f}s")
