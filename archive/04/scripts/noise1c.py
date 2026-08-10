"""Why the multi-tone residual scatters: c_x is a resonance of width alpha.

noise1b swept the tone count at fixed band and fixed total power expecting
the residual to scale like alpha N / BW if beat terms were responsible:

    N     spacing   alpha/spacing   error
     2     3.2399      0.031        +0.31%
     4     1.0800      0.093        +3.08%
     8     0.4628      0.216        -3.80%
    16     0.2160      0.463        +7.59%
    32     0.1045      0.957        -2.71%

That is scatter of a few percent with no trend, so beats are not it and the
hypothesis is dropped.  The actual cause is visible in c_x itself:

    Re c_x(0.90 w0) = 1.508e+07        Re c_x(w0) = 2.483e+10

a factor 1650 between the working point and the peak.  The reason is
structural, not numerical: c_x is built from H = (i w I - A)^{-1} f_u, and A
has the eigenvalue lam = -alpha + i w0, so |H| ~ 1/|i w - lam| ~ 1/alpha
when w -> w0.  c_x goes as |H|^2, so Re c_x is a squared Lorentzian of
HALF-WIDTH alpha = 0.1 rad/s in the drive frequency.

Two consequences, and they are different statements:

 (1) the erosion sum is dominated by whichever tone happens to land nearest
     w0, so with a comb spacing of order alpha the sum is hypersensitive to
     the exact tone placement -- the +-1e-3 jitter deliberately added to
     break commensurability moves it by percent.  The N = 32 case has
     spacing 0.1045 against a width of 0.1, i.e. exactly the worst case.
 (2) more seriously, a tone INSIDE the resonance width drives the critical
     mode nearly resonantly, |H| ~ 1/alpha, and the two-carrier expansion
     is built on the drive being non-resonant.  Every single-tone cell in
     this whole campaign used r = 0.90 or 0.92 and never r = 1.00, for
     exactly this reason; the broadband patches quietly violated it.

The decisive test separates them.  If (2) dominates, a band placed entirely
OFF resonance must reproduce the two-tone accuracy (<1%) regardless of N,
while a band straddling w0 must not -- and that is a statement about where
the band sits, not how finely it is divided.

  A. off-resonance bands (0.70-0.80 and 0.80-0.88 w0), N = 4, 8, 16
  B. on-resonance band (0.95-1.05 w0), same N
  C. continuum convergence on an off-resonance band, N = 8, 32, 128, with
     the discrete sum compared against the spectral integral so it is clear
     which of the two the measurement actually follows.
Budget ~35 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/noise1c.log', 'w')
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
A = jac(st, pr); dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
cx_ref = cx_hand(A, st, pr, qv, pv, w0, 0.90*w0, fV).real
dpar = R5['c_x'].real - R5a['c_x'].real
par_frac = dpar/(cx_ref + dpar)
c2r = R5['c2'].real; cxxr = R5['c_xx'].real; ca4r = R5['c_a4'].real
out(f"G1 margin 0.10: alpha={alpha:.5f} w0={w0:.5f} Re c1={c1.real:.6e}")


def cx_of(wk):
    return cx_hand(A, st, pr, qv, pv, w0, wk, fV).real/(1.0 - par_frac)


out("  Re c_x profile (the resonance whose half-width is alpha):")
for r in (0.70, 0.80, 0.90, 0.95, 0.98, 0.995, 1.0, 1.005, 1.02, 1.10):
    out(f"    w/w0={r:6.3f}  (w-w0)/alpha={(r-1)*w0/alpha:+9.2f}  "
        f"Re c_x={cx_of(r*w0):.6e}")


def kick_phasor(tones):
    Z = 0.0 + 0j
    for wk, ak, ph in tones:
        a = 0.5*ak*np.exp(1j*ph)
        Hp = np.linalg.solve(1j*wk*np.eye(4) - A, fV.astype(complex))
        Hm = np.linalg.solve(-1j*wk*np.eye(4) - A, fV.astype(complex))
        Z -= (a*np.vdot(pv, Hp) + np.conj(a)*np.vdot(pv, Hm))
    return Z


def predict(tu):
    def gap(eps):
        aeff = alpha
        for wk, rk, ph in tu:
            a2 = 0.25*(eps*rk)**2
            aeff -= cx_of(wk)*a2 + ca4r*a2*a2
        a2t = sum(0.25*(eps*rk)**2 for _, rk, _ in tu)
        rg = guard_root(aeff, c1.real + cxxr*a2t, c2r)
        if not (rg == rg):
            return 1.0
        return abs(kick_phasor([(wk, eps*rk, ph)
                                for wk, rk, ph in tu])) - rg
    lo, hi = 1e-12, 2.0
    if gap(hi) <= 0:
        return float('nan')
    for _ in range(220):
        m = 0.5*(lo+hi)
        if gap(m) > 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)


def probe(tu, NP, eps):
    Tb = 2*math.pi/min(w for w, _, _ in tu)

    def f(t, x):
        du = eps*sum(rk*math.cos(wk*t + ph) for wk, rk, ph in tu)
        return rhs(x, dict(pr, V=pr['V'] + du))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NP*Tb), st.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0


def bisect(fn, seed, nit=17):
    elo, ehi = 0.6*seed, 1.4*seed
    n = 0
    while not fn(ehi) and n < 14:
        elo = ehi; ehi *= 1.3; n += 1
    n = 0
    while fn(elo) and n < 14:
        ehi = elo; elo *= 0.75; n += 1
    if fn(elo) or not fn(ehi):
        return float('nan')
    for _ in range(nit):
        em = 0.5*(elo+ehi)
        if fn(em): ehi = em
        else: elo = em
    return 0.5*(elo+ehi)


def patch(N, lo, hi, seed):
    rng = np.random.default_rng(seed)
    rs = np.linspace(lo, hi, N) if N > 1 else np.array([0.5*(lo+hi)])
    rs = rs*(1 + 1e-3*rng.standard_normal(N))
    phs = rng.uniform(0, 2*math.pi, N)
    return [(rs[i]*w0, 1.0/math.sqrt(N), float(phs[i])) for i in range(N)]


def nearest(tu):
    return min(abs(w - w0) for w, _, _ in tu)/alpha


out("")
out("=== A/B. band placement, N varied, total power fixed")
out("  band          |  N  | nearest tone |w-w0|/alpha | measured    | "
    "predicted   | err")
for lo, hi, tag in ((0.70, 0.80, '0.70-0.80'), (0.80, 0.88, '0.80-0.88'),
                    (0.95, 1.05, '0.95-1.05')):
    for N in (4, 8, 16):
        for seed in (7, 23):
            tu = patch(N, lo, hi, seed)
            ep = predict(tu)
            em = bisect(lambda e: probe(tu, 1000, e), ep)
            out(f"  {tag}  s{seed:<2d} | {N:3d} | {nearest(tu):20.2f} | "
                f"{em:.5e} | {ep:.5e} | {(ep-em)/em*100:+6.2f}%  "
                f"[{time.time()-T0:.0f}s]")

out("")
out("=== C. continuum convergence on an off-resonance band (0.70-0.80 w0)")
out("  discrete sum vs spectral integral (1/2) int Re c_x S_u dw")
out("   N   | spacing/alpha | sum          | integral     | ratio | "
    "measured    | err")
for N in (8, 32, 128):
    tu = patch(N, 0.70, 0.80, 7)
    ws = np.array([w for w, _, _ in tu])
    ssum = sum(cx_of(w)*0.25*rk*rk for w, rk, _ in tu)
    # continuum: S_u(w) = <u^2>/BW over the band, <u^2> = sum r_k^2/2
    BW = 0.10*w0
    u2 = sum(rk*rk for _, rk, _ in tu)/2.0
    wg = np.linspace(0.70*w0, 0.80*w0, 800)
    cg = np.array([cx_of(w) for w in wg])
    trap = np.trapezoid if hasattr(np, 'trapezoid') else np.trapz
    sint = 0.5*float(trap(cg, wg))*u2/BW
    ep = predict(tu)
    em = bisect(lambda e: probe(tu, 1000, e), ep)
    sp = (ws.max()-ws.min())/max(1, N-1)/alpha
    out(f"  {N:4d} | {sp:13.3f} | {ssum:.6e} | {sint:.6e} | "
        f"{ssum/sint:.4f} | {em:.5e} | {(ep-em)/em*100:+6.2f}%  "
        f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
