"""The multi-tone criterion is the wrong SHAPE, not the wrong coefficients.

Six candidates are excluded by measurement: beats as an N-scaling, band
placement, the expansion parameter, the early-time erosion weighting, the
multi-tone form of the a^4 term (the residual is identical where that term
is 0.006% of alpha and where it is 13%), and the rare-event / window story
(the multi-tone threshold is window-converged, -0.016% from 250 to 500
periods, exactly like a single-tone cell).

So the coefficients are right and the number being measured is the right
one.  What is left is the SHAPE of the comparison.

For a single tone the reduced equation is autonomous after averaging: the
erosion coefficient |alpha(t)|^2 = |a|^2 is constant, the guard sits at a
fixed rho_g, the free part decays monotonically, and "escape" is decided
once and for all at t = 0 by |Z(0)| > rho_g.  A single scalar comparison is
exactly right.

For N incommensurate tones nothing in that sentence survives.  The drive's
squared envelope

    |alpha_tot(t)|^2 = sum_{j,k} a_j abar_k e^{i(w_j - w_k) t}

has a mean of sum_k |a_k|^2 -- which is what the criterion uses -- and a
fluctuating part that never averages to zero over any finite stretch.  The
reduced equation is therefore NON-AUTONOMOUS,

    zetadot = lam zeta + c1 zeta |zeta|^2 + c_x |alpha_tot(t)|^2 zeta ,

the guard breathes, the free part's decay is modulated, and escape is
decided by

    max_t [ |zeta(t)| / rho_g(t) ] > 1

which is not the same as comparing two numbers at t = 0.  The difference is
phase-dependent (it depends on where the beats sit relative to switch-on),
carries either sign (the beat can help or hinder), and has no reason to
scale with N -- which is the exact signature the residual has and none of
the six excluded candidates has.

Tested by integrating that one complex ODE, with zeta(0) set to the linear
kick (verified to +0.00134% in wrapA1c) and the cross-tone coefficients
approximated by c_x^{jk} = (Re c_x(w_j) + Re c_x(w_k))/2, exact on the
diagonal and a narrow-band approximation off it.  If the reduced-equation
threshold reproduces the measurements where the closed-form comparison
leaves +-1-4%, the item closes: the coefficients were never wrong, the
scalar comparison was.
Budget ~20 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time, re
LOG = open('sweep20/noise1j.log', 'w')
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
lam = co['lam']; pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr)
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
cx_ref = cx_hand(A, st, pr, qv, pv, w0, 0.90*w0, fV).real
dpar = R5['c_x'].real - R5a['c_x'].real
par_frac = dpar/(cx_ref + dpar)
c2r = R5['c2'].real; cxxr = R5['c_xx'].real; ca4r = R5['c_a4'].real
c1r = c1.real
rg0 = math.sqrt(alpha/c1r)
out(f"G1 margin 0.10: alpha={alpha:.6f}  Re c1={c1r:.6e}  rho_g(0)={rg0:.5e}")

_cx_cache = {}


def cx_of(wk):
    k = round(wk, 9)
    if k not in _cx_cache:
        _cx_cache[k] = cx_hand(A, st, pr, qv, pv, w0, wk,
                               fV).real/(1.0 - par_frac)
    return _cx_cache[k]


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


def closed_form(tu):
    """the criterion as used: |Z(0)| > rho_g(mean erosion)."""
    def gap(eps):
        a2s = [0.25*(eps*rk)**2 for _, rk, _ in tu]
        a2t = sum(a2s)
        aeff = alpha - sum(cx_of(wk)*a2 for (wk, _, _), a2 in zip(tu, a2s))
        aeff -= sum(ca4r*a2*a2 for a2 in a2s)
        rg = guard_root(aeff, c1r + cxxr*a2t, c2r)
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


def reduced_escape(tu, eps, Tend):
    """integrate zetadot = lam zeta + c1 zeta|zeta|^2 + E(t) zeta,
    E(t) = sum_{j,k} cx^{jk} a_j abar_k e^{i(w_j-w_k)t}, real part used."""
    ws = np.array([wk for wk, _, _ in tu])
    aa = np.array([0.5*eps*rk*np.exp(1j*ph) for _, rk, ph in tu])
    cxv = np.array([cx_of(wk) for wk in ws])
    # With c_x^{jk} = (c_j + c_k)/2 the double sum factorises exactly:
    #   sum_{j,k} (c_j+c_k)/2 a_j abar_k e^{i(w_j-w_k)t} = Re[S_c(t) conj(S_1(t))]
    #   S_c = sum_j c_j a_j e^{i w_j t},  S_1 = sum_j a_j e^{i w_j t}
    # O(N) per evaluation instead of O(N^2).
    ac = cxv*aa

    def E(t):
        e = np.exp(1j*ws*t)
        return float(np.real(np.dot(ac, e)*np.conj(np.dot(aa, e))))
    Z0 = kick_c(tu, eps)
    lim = 3.0*rg0

    # Rotating frame: zeta = Z e^{i w0 t} removes the carrier, which carries
    # no information and would otherwise force the integrator through ~3000
    # oscillations per run.  lam - i w0 = -alpha exactly.
    def f(t, y):
        z = y[0] + 1j*y[1]
        # alpha_eff = alpha - Re c_x |a|^2, so the erosion enters with a PLUS.
        dz = (-alpha + 0j)*z + c1*z*abs(z)**2 + E(t)*z
        return [dz.real, dz.imag]

    def ev(t, y):
        return math.hypot(y[0], y[1]) - lim
    ev.terminal = True; ev.direction = 1

    def dead(t, y):
        # decayed far below the guard and past any beat that could help
        return math.hypot(y[0], y[1]) - 1e-4*rg0
    dead.terminal = True; dead.direction = -1
    s = solve_ivp(f, (0, Tend), [Z0.real, Z0.imag], method='DOP853',
                  rtol=1e-9, atol=1e-18, events=(ev, dead))
    return len(s.t_events[0]) > 0 or s.status < 0


def reduced_threshold(tu, seed):
    Tend = 60.0/alpha
    lo, hi = 0.6*seed, 1.4*seed
    n = 0
    while not reduced_escape(tu, hi, Tend) and n < 14:
        lo = hi; hi *= 1.25; n += 1
    n = 0
    while reduced_escape(tu, lo, Tend) and n < 14:
        hi = lo; lo *= 0.8; n += 1
    if reduced_escape(tu, lo, Tend) or not reduced_escape(tu, hi, Tend):
        return float('nan')
    for _ in range(24):
        m = 0.5*(lo+hi)
        if reduced_escape(tu, m, Tend): hi = m
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
out("  cell                    | measured   | closed form (scalar) | "
    "reduced ODE (max over t)")
ec_ = []; er_ = []
for tag, tu, em in CASES:
    p0 = closed_form(tu)
    p1 = reduced_threshold(tu, p0)
    d0 = (p0-em)/em*100
    d1 = (p1-em)/em*100 if p1 == p1 else float('nan')
    ec_.append(abs(d0))
    if d1 == d1:
        er_.append(abs(d1))
    out(f"  {tag} | {em:.4e} | {p0:.4e} {d0:+7.2f}% | "
        f"{p1:.4e} {d1:+7.2f}%   [{time.time()-T0:.0f}s]")
ec_ = np.array(ec_); er_ = np.array([e for e in er_])
out("")
out(f"  mean |err| closed form (scalar comparison) {ec_.mean():6.3f}%  "
    f"max {ec_.max():.2f}%")
if len(er_):
    out(f"  mean |err| reduced ODE (max over t)        {er_.mean():6.3f}%  "
        f"max {er_.max():.2f}%")
    if er_.mean() < 0.5*ec_.mean():
        out("")
        out("  VERDICT: the coefficients were never wrong -- the scalar")
        out("  comparison was.  For a quasi-periodic drive the reduced")
        out("  equation is non-autonomous and escape is a max over t, not a")
        out("  comparison of two numbers at t = 0.  Item closes.")
    elif er_.mean() < 0.8*ec_.mean():
        out("")
        out("  VERDICT: partial -- the non-autonomous criterion accounts for")
        out("  a real part of the residual but not all of it.")
    else:
        out("")
        out("  VERDICT: no improvement.  A seventh candidate excluded.")
out(f"DONE wall={time.time()-T0:.0f}s")
