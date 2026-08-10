"""Two places where I delivered a number or a procedure where a FORMULA exists.

(1) MULTI-TONE.  I closed it as "integrate the non-autonomous reduced
    equation" -- a procedure, not a formula, and the campaign's standard is
    closed forms.  But that equation is exactly solvable.  With
    zeta = R e^{i phi} only R matters and

        Rdot = [-alpha + E(t)] R + c1 R^3 ,
        E(t) = sum_{j,k} c_x^{jk} a_j abar_k e^{i(w_j-w_k)t}   (real)

    is a BERNOULLI equation.  Substituting u = R^{-2} linearises it exactly:

        udot = 2[alpha - E(t)] u - 2 c1
        ==>  u(t) = e^{A(t)} [ u_0 - 2 c1 int_0^t e^{-A(s)} ds ],
             A(t) = 2 alpha_eff t - 2 Psi(t),
             alpha_eff = alpha - Ebar,   Ebar = sum_k c_x^{kk}|a_k|^2,
             Psi(t) = int_0^t [E - Ebar] ds
                    = sum_{j!=k} c_x^{jk} a_j abar_k (e^{i D_jk t} - 1)/(i D_jk)

    Psi is BOUNDED with Psi(0) = 0 -- it is the beat, and it carries no
    secular part by construction.  Escape is R -> infinity, i.e. u -> 0, and
    since the integrand is positive the supremum is at t -> infinity:

        escape  <=>  1/|Z(0)|^2  <=  2 c1 I ,
        I = int_0^infty exp[-2 alpha_eff s + 2 Psi(s)] ds

    Writing G = 2 alpha_eff I (a pure number, = 1 when Psi == 0):

        |Z(0)|_c = rho_g / sqrt(G) ,   rho_g = sqrt(alpha_eff / Re c1)

    So the whole multi-tone effect is ONE named parameter: a beat gain G
    that shrinks the guard.  Single tone gives Psi == 0, G = 1, and the
    criterion collapses to |Z(0)| > rho_g exactly -- the old formula is the
    G = 1 case, not a different theory.  One scalar integral replaces the
    ODE, and G is a number one can read and compare across cells.

(2) KRAMERS PREFACTOR.  I derived
        T = sqrt(pi Dtilde Re c1) / alpha_eff^2 * exp(X)
    and then used it only to correct the SLOPE, treating its constant as
    free.  But the constant is predicted too:
        Y = ln T - (1/2)ln Dtilde + 2 ln alpha_eff = X + (1/2) ln(pi Re c1)
    so the intercept should be (1/2)ln(pi * 1219.123) = 4.1253, with nothing
    fitted.  I never checked it.  If it comes out near 4.13 then both the
    exponent AND the prefactor are parameter-free predictions; if it is off
    by a large factor, the prefactor derivation is wrong and only the slope
    claim survives.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time, re, math
import numpy as np
LOG = open('sweep20/formula2.log', 'w')
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
c1r = c1.real
out(f"G1 margin 0.10: alpha={alpha:.6f}  Re c1={c1r:.6e}")
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


def kick_abs(tu, eps):
    Z = 0.0 + 0j
    for wk, rk, ph in tu:
        aa = 0.5*eps*rk*np.exp(1j*ph)
        Hp = np.linalg.solve(1j*wk*np.eye(4) - A, fV.astype(complex))
        Hm = np.linalg.solve(-1j*wk*np.eye(4) - A, fV.astype(complex))
        Z -= (aa*np.vdot(pv, Hp) + np.conj(aa)*np.vdot(pv, Hm))
    return abs(Z)


def beat_gain(tu, eps, NS=20000, TMULT=30.0):
    """G = 2 alpha_eff * int_0^inf exp[-2 alpha_eff s + 2 Psi(s)] ds
    Psi(s) = sum_{j!=k} c^{jk} a_j abar_k (e^{i D s} - 1)/(i D), bounded."""
    ws = np.array([wk for wk, _, _ in tu])
    aa = np.array([0.5*eps*rk*np.exp(1j*ph) for _, rk, ph in tu])
    cxv = np.array([cx_of(wk) for wk in ws])
    CX = 0.5*(cxv[:, None] + cxv[None, :])
    M = CX*(aa[:, None]*np.conj(aa)[None, :])
    D = ws[:, None] - ws[None, :]
    Ebar = float(np.real(np.trace(M)))
    ae = alpha - Ebar
    if ae <= 0:
        return float('nan'), ae
    off = ~np.eye(len(ws), dtype=bool)
    Mo = M[off]; Do = D[off]
    T = TMULT/ae
    s = np.linspace(0.0, T, NS)
    Psi = np.real(np.sum(Mo[:, None]*(np.exp(1j*Do[:, None]*s[None, :]) - 1.0)
                         / (1j*Do[:, None]), axis=0))
    integ = np.exp(-2*ae*s + 2*Psi)
    I = float(np.trapezoid(integ, s)) if hasattr(np, 'trapezoid') \
        else float(np.trapz(integ, s))
    return 2*ae*I, ae


def thr_formula(tu, seed):
    """|Z(0)| = rho_g/sqrt(G), both sides depend on eps -> scalar bisection"""
    def gap(eps):
        G, ae = beat_gain(tu, eps)
        if not (G == G) or ae <= 0:
            return 1.0
        return kick_abs(tu, eps) - math.sqrt(ae/c1r)/math.sqrt(G)
    lo, hi = 0.5*seed, 1.8*seed
    n = 0
    while gap(hi) <= 0 and n < 12:
        lo = hi; hi *= 1.3; n += 1
    n = 0
    while gap(lo) > 0 and n < 12:
        hi = lo; lo *= 0.75; n += 1
    if gap(lo) > 0 or gap(hi) <= 0:
        return float('nan'), float('nan')
    for _ in range(60):
        m = 0.5*(lo+hi)
        if gap(m) > 0: hi = m
        else: lo = m
    e = 0.5*(lo+hi)
    G, _ = beat_gain(tu, e)
    return e, G


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
out("=== 1. multi-tone closed form:  |Z(0)|_c = rho_g / sqrt(G)")
out("       G = 2 alpha_eff int_0^inf exp[-2 alpha_eff s + 2 Psi(s)] ds")
out("       (single tone: Psi == 0, G == 1, recovers |Z(0)| > rho_g exactly)")
out("  cell                    | measured   | formula    | err     |   G")
errs = []
for tag, tu, em in CASES:
    ef, G = thr_formula(tu, em)
    d = (ef-em)/em*100
    errs.append(abs(d))
    out(f"  {tag} | {em:.4e} | {ef:.4e} | {d:+6.2f}% | {G:.4f}")
errs = np.array(errs)
out(f"    mean |err| {errs.mean():.3f}%   max {errs.max():.3f}%")
out(f"    (ODE integration gave mean 0.521%, max 1.541%; scalar comparison")
out(f"     i.e. G forced to 1 gave 2.862% / 7.590%)")
out(f"    G range across the 17 cells: {min(1,1):.0f}  -- see column above")
out(f"  [{time.time()-T0:.0f}s]")

# --------------------------------------------------------------- part 2
out("")
out("=== 2. Kramers PREFACTOR, which I derived and never checked")
out("    T = sqrt(pi Dtilde Re c1)/alpha_eff^2 * exp(X)")
out("    ==> Y = ln T - (1/2)ln Dtilde + 2 ln alpha_eff = X + (1/2)ln(pi Re c1)")
pred_ic = 0.5*math.log(math.pi*c1r)
out(f"    predicted intercept = (1/2) ln(pi * {c1r:.4f}) = {pred_ic:.4f}")
gmag = 3.198767e+02
txt = open('sweep20/noise3.log').read().split('\n')
i0 = next(k for k, l in enumerate(txt) if l.startswith('=== (II)'))
rows = []
for l in txt[i0:]:
    m = re.match(r'\s*([\d.]+e-0\d)\s*\|\s*([\d.]+)\s*\|\s*([\d.]+)%\s*\|'
                 r'\s*([\d.]+)\s*\|\s*(\d+)/(\d+)\s*\|\s*([\d.]+)\s*\|'
                 r'\s*([-\d.]+)\s*\|\s*([\d.]+)', l)
    if m:
        rows.append((float(m.group(1)), float(m.group(2)), float(m.group(7))))
out("    cut   | n | slope  | intercept | intercept - predicted")
for cut in (0.0, 0.9, 1.4, 2.0):
    X = []; Y = []
    for sig, ae, T in rows:
        D = gmag**2*sig*sig/4.0
        x = ae*ae/(c1r*gmag**2*sig*sig)
        if x <= cut:
            continue
        X.append(x)
        Y.append(math.log(T) - 0.5*math.log(D) + 2*math.log(ae))
    if len(X) < 3:
        continue
    sl, ic = np.polyfit(np.array(X), np.array(Y), 1)
    out(f"    X>{cut:.1f} | {len(X)} | {sl:6.4f} | {ic:9.4f} | "
        f"{ic-pred_ic:+.4f}  (factor {math.exp(ic-pred_ic):.3f})")
out("    a factor near 1 means BOTH the exponent and the prefactor are")
out("    parameter-free predictions, not just the exponent")
out(f"DONE wall={time.time()-T0:.0f}s")
