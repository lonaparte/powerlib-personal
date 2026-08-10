"""Broadband drive, step 1: is erosion a scalar sum over the spectrum?

Everything verified so far used a single tone.  The theory says more than
that, and it says it without any new object.  Write the drive as a sum of
carriers, u(t) = sum_k (a_k e^{i w_k t} + c.c.).  The resonance condition
for the reduced zeta equation is

    D_pi = j lam + k lambar + sum_k (l_k - m_k) i w_k  =  lam ,

so for INCOMMENSURATE w_k the only surviving cubic indices are j=k+1 with
l_k = m_k for every k.  Two consequences, both sharp and both free:

 (E1) no cross-erosion.  An index with l_1 - m_1 = +1, l_2 - m_2 = -1 has
      D = lam + i(w_1 - w_2) != lam, so it is NOT resonant.  Erosion is a
      pure scalar sum,
          alpha_eff = alpha - sum_k Re c_x(w_k) |a_k|^2 ,
      with the SAME c_x(w) already derived, evaluated tone by tone.  In the
      continuum limit, with one-sided PSD S_u (so <u^2> = int S_u dw),
          alpha_eff = alpha - (1/2) int Re c_x(w) S_u(w) dw .
 (E2) the switch-on kick is a PHASOR sum, not a scalar one,
          Z(0) = - sum_k [ a_k <p,H_k> + abar_k <p,Hbar_k> ]
               =   sum_k 2 a_k lam <p,f_u> / (w_k^2 + lam^2) ,
      because every tone shares the same channel direction f_u and differs
      only through the complex denominator.

Escape is still |Z(0)| > rho_g(alpha_eff), and the slowly-raised protocol
still has no kick, so its threshold is alpha_eff = 0 exactly.

Tested here on the GFL V channel, G1 margin 0.10:
  A. two tones, incommensurate and commensurate, equal and unequal split;
  B. an 8-tone narrowband patch with fixed random phases, sudden onset;
  C. the same patch, slowly raised -- threshold must be alpha_eff = 0 with
     no kick term at all.
Budget ~40 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/noise1.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']; cx_hand = _ns['cx_hand']

prb = gset('G1'); PH = hopf(prb)
prH = dict(prb, P=PH); stH = equil(prH); coH = nf_coeffs(prH)
w0H = coH['w0']; hs = 1e-6
AH = jac(stH, prH)
evH, VLH, VRH = eig(AH, left=True, right=True)
kH = max((i for i in range(4) if evH[i].imag > 1e-9),
         key=lambda i: evH[i].real)
lamH = evH[kH]; qH = VRH[:, kH]; pH = VLH[:, kH]; pH = pH/np.vdot(qH, pH)
fuH = (rhs(stH, dict(prH, V=prH['V']+hs))
       - rhs(stH, dict(prH, V=prH['V']-hs)))/(2*hs)

P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
lam = co['lam']; pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr); dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
pfu = np.vdot(pv, fV)
out(f"G1 margin 0.10: alpha={alpha:.5f}, w0={w0:.5f}, Re c1={c1.real:.6e}")
out(f"  rho_g(unforced) = {math.sqrt(alpha/c1.real):.6e}")

# fifth-order partners, computed once on the V channel at the Hopf point
DkV = make_tensors5(sp, f_, _x,
                    {P_: prH['P'], Q_: prH['Q'], V_: prH['V'],
                     Xg_: prH['Xg'], kp_: prH['kp'], ki_: prH['ki'],
                     kpv_: prH['kpv'], kiv_: prH['kiv'], C_: prH['C']},
                    prH, stH, V_)
R5 = solve_nf5(AH, lamH, qH, pH, fuH, 0.90*w0H, DkV, param=True)
R5a = solve_nf5(AH, lamH, qH, pH, fuH, 0.90*w0H, DkV, param=False)
dcx_par = R5['c_x'].real - R5a['c_x'].real
cx_ref = cx_hand(A, st, pr, qv, pv, w0, 0.90*w0, fV).real
par_frac = dcx_par/(cx_ref + dcx_par)
c2r = R5['c2'].real; cxxr = R5['c_xx'].real; ca4r = R5['c_a4'].real
out(f"  Re c2={c2r:.5e}, Re c_xx={cxxr:.5e}, Re c_a4={ca4r:.5e}")
out(f"  parametric share of Re c_x at w_p=0.9 w0: {par_frac*100:+.2f}% "
    f"(applied as a multiplicative factor to every tone)")


def cx_of(wk):
    """Re c_x at drive frequency wk, additive part from the closed formula
    times the parametric factor measured at 0.9 w0."""
    return cx_hand(A, st, pr, qv, pv, w0, wk, fV).real/(1.0 - par_frac)


def kick_phasor(tones):
    """Z(0) for a set of (w_k, amp_k, phase_k); amp is the peak of the
    cosine, so a_k = amp/2 e^{i phase}."""
    Z = 0.0 + 0j
    for wk, ak, ph in tones:
        a = 0.5*ak*np.exp(1j*ph)
        Hp = np.linalg.solve(1j*wk*np.eye(4) - A, fV.astype(complex))
        Hm = np.linalg.solve(-1j*wk*np.eye(4) - A, fV.astype(complex))
        Z -= (a*np.vdot(pv, Hp) + np.conj(a)*np.vdot(pv, Hm))
    return Z


def predict(tones_unit, protocol):
    """Threshold on the common scale factor eps: tones_unit gives the
    relative amplitude/phase of each tone at eps = 1."""
    def gap(eps):
        aeff = alpha
        for wk, rk, ph in tones_unit:
            a2 = 0.25*(eps*rk)**2
            aeff -= cx_of(wk)*a2 + ca4r*a2*a2
        a2t = sum(0.25*(eps*rk)**2 for _, rk, _ in tones_unit)
        rg = guard_root(aeff, c1.real + cxxr*a2t, c2r)
        if not (rg == rg):
            return 1.0
        if protocol == 'slow':
            return -1.0
        return abs(kick_phasor([(wk, eps*rk, ph)
                                for wk, rk, ph in tones_unit])) - rg
    lo, hi = 1e-12, 2.0
    if gap(hi) <= 0:
        return float('nan')
    for _ in range(220):
        m = 0.5*(lo+hi)
        if gap(m) > 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)


def make_probe(tones_unit, NP, ramp=0):
    wmin = min(w for w, _, _ in tones_unit)
    Td = 2*math.pi/wmin

    def probe(eps):
        def f(t, x):
            s = 1.0 if ramp <= 0 else min(1.0, t/(ramp*Td))
            du = s*eps*sum(rk*math.cos(wk*t + ph)
                           for wk, rk, ph in tones_unit)
            return rhs(x, dict(pr, V=pr['V'] + du))
        def e_th(t, x): return abs(x[0] - st[0]) - dsad
        def e_vlo(t, x): return x[2] - 0.20*Vdc0
        def e_vhi(t, x): return x[2] - 2.50*Vdc0
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, (NP + ramp)*Td), st.copy(), method='DOP853',
                      rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
        return (any(len(s.t_events[i]) > 0 for i in range(3))
                or s.status < 0)
    return probe


def bisect(probe, seed):
    elo, ehi = 0.6*seed, 1.4*seed
    n = 0
    while not probe(ehi) and n < 14:
        elo = ehi; ehi *= 1.3; n += 1
    n = 0
    while probe(elo) and n < 14:
        ehi = elo; elo *= 0.75; n += 1
    if probe(elo) or not probe(ehi):
        return float('nan')
    for _ in range(17):
        em = 0.5*(elo+ehi)
        if probe(em): ehi = em
        else: elo = em
    return 0.5*(elo+ehi)


PHI = 0.5*(1 + math.sqrt(5))
out("")
out("=== A. two tones, sudden onset (kick = phasor sum, erosion = scalar sum)")
out(" case                       | measured    | predicted   | err     | "
    "kick |Z0|/eps  erosion split")
CASES_A = [
    ('w1=0.90 w2=0.90/phi  1:1', [(0.90, 1.0, 0.0), (0.90/PHI, 1.0, 0.0)]),
    ('w1=0.90 w2=0.90/phi  1:0.5', [(0.90, 1.0, 0.0), (0.90/PHI, 0.5, 0.0)]),
    ('w1=0.90 w2=1.30      1:1', [(0.90, 1.0, 0.0), (1.30, 1.0, 0.0)]),
    ('w1=0.90 w2=0.45 (2:1) 1:1', [(0.90, 1.0, 0.0), (0.45, 1.0, 0.0)]),
    ('w1=0.90 w2=0.90/phi  antiphase',
     [(0.90, 1.0, 0.0), (0.90/PHI, 1.0, math.pi)]),
]
for tag, spec in CASES_A:
    tu = [(r*w0, amp, ph) for r, amp, ph in spec]
    ep = predict(tu, 'sudden')
    em = bisect(make_probe(tu, 1000), ep)
    kz = abs(kick_phasor([(wk, rk, ph) for wk, rk, ph in tu]))
    er = [cx_of(wk)*0.25*rk*rk for wk, rk, _ in tu]
    out(f" {tag:26s} | {em:.5e} | {ep:.5e} | "
        f"{(ep-em)/em*100:+6.2f}% | {kz:.4e}  "
        f"{er[0]/sum(er)*100:.1f}/{er[1]/sum(er)*100:.1f}  "
        f"[{time.time()-T0:.0f}s]")

out("")
out("=== B. 8-tone narrowband patch, fixed random phases, sudden onset")
rng = np.random.default_rng(0)
for bw, tag in ((0.10, 'band 0.85-0.95 w0'), (0.30, 'band 0.75-1.05 w0')):
    N = 8
    rs = np.linspace(0.90 - bw/2, 0.90 + bw/2, N)
    rs = rs*(1 + 1e-3*rng.standard_normal(N))       # break commensurability
    phs = rng.uniform(0, 2*math.pi, N)
    tu = [(rs[i]*w0, 1.0/math.sqrt(N), float(phs[i])) for i in range(N)]
    ep = predict(tu, 'sudden')
    em = bisect(make_probe(tu, 1000), ep)
    ercont = sum(cx_of(wk)*0.25*rk*rk for wk, rk, _ in tu)
    cx1 = cx_of(0.90*w0)
    out(f" {tag}: measured {em:.5e} | predicted {ep:.5e} | "
        f"{(ep-em)/em*100:+6.2f}%")
    out(f"    erosion coefficient sum_k Re c_x(w_k) r_k^2/4 = {ercont:.5e} "
        f"vs single tone at 0.9w0 {cx1*0.25:.5e} "
        f"(ratio {ercont/(cx1*0.25):.4f})")
    out(f"    kick |Z0|/eps = {abs(kick_phasor(tu)):.5e} vs single tone "
        f"{abs(kick_phasor([(0.90*w0, 1.0, 0.0)])):.5e}  "
        f"[{time.time()-T0:.0f}s]")

out("")
out("=== C. same patches, slowly raised (200-period ramp): no kick, so the")
out("    threshold must be exactly alpha_eff = 0")
rng = np.random.default_rng(0)
for bw, tag in ((0.10, 'band 0.85-0.95 w0'), (0.30, 'band 0.75-1.05 w0')):
    N = 8
    rs = np.linspace(0.90 - bw/2, 0.90 + bw/2, N)
    rs = rs*(1 + 1e-3*rng.standard_normal(N))
    phs = rng.uniform(0, 2*math.pi, N)
    tu = [(rs[i]*w0, 1.0/math.sqrt(N), float(phs[i])) for i in range(N)]
    ep = predict(tu, 'slow')
    em = bisect(make_probe(tu, 600, ramp=200), ep)
    out(f" {tag}: measured {em:.5e} | alpha_eff=0 gives {ep:.5e} | "
        f"{(ep-em)/em*100:+6.2f}%  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
