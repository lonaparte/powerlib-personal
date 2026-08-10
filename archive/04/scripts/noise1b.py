"""Broadband drive, step 1b: what the two residuals in noise1 actually are.

noise1 left two gaps, both small and both with a named suspect.

 (i) sudden onset, 8-tone patch: -2.08% (narrow band) and -2.43% (wide
     band), against -0.13...+0.07% for two tones.  The kick model is not to
     blame -- wrapA1c has since shown the switch-on kick is linear in the
     drive to 0.0013%, with the eps^2 term essentially absent -- so the
     error is in the erosion, and the erosion's one approximation is that
     cross terms between different tones are non-resonant.  They are, but
     only barely: the index with l_j - m_j = +1 and l_k - m_k = -1 has

         D_pi - lam = i (w_j - w_k) ,

     so it is suppressed by |w_j - w_k| rather than by anything large, and
     its effect on the reduced equation is a slow modulation of alpha_eff
     at the beat frequency with relative size ~ alpha/|w_j - w_k|.  Since
     the threshold is set by the WORST instant of alpha_eff and not its
     mean, a modulated erosion always lowers the threshold -- which is the
     observed sign.  Prediction: the error must scale like alpha N / BW at
     fixed band and power.  Tested by holding the band and the total power
     fixed and varying N over 2, 4, 8, 16, 32 -- a factor 16 in the
     predicted error.  If the residual is flat in N instead, the beat
     explanation is wrong and the erosion law needs a different repair.

 (ii) slowly raised: -5.21% and -6.30% against a criterion (alpha_eff = 0)
     that has no kick and therefore no approximation left in it at all.
     The suspect there is the protocol, not the theory: the ramp was 200
     periods of the slowest tone, i.e. 45.6 s, against an envelope
     relaxation time 1/alpha = 10 s.  Near alpha_eff = 0 the relaxation
     time diverges, so a fixed ramp is never adiabatic at the end and the
     state lags -- which raises the measured threshold, again the observed
     sign.  Tested by ramping over R/alpha with R = 5, 20, 80, 320: if
     non-adiabaticity is the cause the error must fall towards zero, and if
     it plateaus the criterion is wrong by that plateau.
Budget ~45 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/noise1b.log', 'w')
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
par_frac = (R5['c_x'].real - R5a['c_x'].real)/(cx_ref
                                               + R5['c_x'].real
                                               - R5a['c_x'].real)
c2r = R5['c2'].real; cxxr = R5['c_xx'].real; ca4r = R5['c_a4'].real
out(f"G1 margin 0.10: alpha={alpha:.5f} w0={w0:.5f} Re c1={c1.real:.6e} "
    f"rho_g={math.sqrt(alpha/c1.real):.5e}")
out(f"  envelope relaxation time 1/alpha = {1/alpha:.3f} s")


def cx_of(wk):
    return cx_hand(A, st, pr, qv, pv, w0, wk, fV).real/(1.0 - par_frac)


def kick_phasor(tones):
    Z = 0.0 + 0j
    for wk, ak, ph in tones:
        a = 0.5*ak*np.exp(1j*ph)
        Hp = np.linalg.solve(1j*wk*np.eye(4) - A, fV.astype(complex))
        Hm = np.linalg.solve(-1j*wk*np.eye(4) - A, fV.astype(complex))
        Z -= (a*np.vdot(pv, Hp) + np.conj(a)*np.vdot(pv, Hm))
    return Z


def predict(tu, protocol):
    def gap(eps):
        aeff = alpha
        for wk, rk, ph in tu:
            a2 = 0.25*(eps*rk)**2
            aeff -= cx_of(wk)*a2 + ca4r*a2*a2
        a2t = sum(0.25*(eps*rk)**2 for _, rk, _ in tu)
        rg = guard_root(aeff, c1.real + cxxr*a2t, c2r)
        if not (rg == rg):
            return 1.0
        if protocol == 'slow':
            return -1.0
        return abs(kick_phasor([(wk, eps*rk, ph) for wk, rk, ph in tu])) - rg
    lo, hi = 1e-12, 2.0
    if gap(hi) <= 0:
        return float('nan')
    for _ in range(220):
        m = 0.5*(lo+hi)
        if gap(m) > 0: hi = m
        else: lo = m
    return 0.5*(lo+hi)


def probe(tu, Thold, Tramp, eps):
    def f(t, x):
        s = 1.0 if Tramp <= 0 else min(1.0, t/Tramp)
        du = s*eps*sum(rk*math.cos(wk*t + ph) for wk, rk, ph in tu)
        return rhs(x, dict(pr, V=pr['V'] + du))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, Tramp + Thold), st.copy(), method='DOP853',
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
    rs = (np.linspace(lo, hi, N) if N > 1 else np.array([0.5*(lo+hi)]))
    rs = rs*(1 + 1e-3*rng.standard_normal(N))
    phs = rng.uniform(0, 2*math.pi, N)
    return [(rs[i]*w0, 1.0/math.sqrt(N), float(phs[i])) for i in range(N)]


out("")
out("=== A. sudden onset, band 0.85-0.95 w0, total power fixed, N varied")
out("    beat suppression predicts error ~ alpha N / BW")
BW = 0.10*w0
out(f"    BW = {BW:.4f} rad/s")
out("  N  | spacing | alpha/spacing | measured    | predicted   | err")
for N in (2, 4, 8, 16, 32):
    tu = patch(N, 0.85, 0.95, 7)
    dw = BW/max(1, N-1) if N > 1 else float('inf')
    ep = predict(tu, 'sudden')
    Tw = 1000*2*math.pi/min(w for w, _, _ in tu)
    em = bisect(lambda e: probe(tu, Tw, 0.0, e), ep)
    out(f" {N:3d} | {dw:7.4f} | {alpha/dw:13.4f} | {em:.5e} | {ep:.5e} | "
        f"{(ep-em)/em*100:+6.2f}%  [{time.time()-T0:.0f}s]")

out("")
out("=== B. slowly raised, ramp length R/alpha; criterion is alpha_eff = 0")
out("  case            |   R  | ramp (s) | measured    | alpha_eff=0 | err")
for tag, tu in (('single tone 0.9', [(0.90*w0, 1.0, 0.0)]),
                ('8-tone 0.85-0.95', patch(8, 0.85, 0.95, 7))):
    ep = predict(tu, 'slow')
    for R in (5, 20, 80, 320):
        Tr = R/alpha
        em = bisect(lambda e: probe(tu, 30.0/alpha, Tr, e), ep, nit=15)
        out(f"  {tag:16s}| {R:4d} | {Tr:8.1f} | {em:.5e} | {ep:.5e} | "
            f"{(ep-em)/em*100:+6.2f}%  [{time.time()-T0:.0f}s]")

out("")
out("=== C. window convergence for the 8-tone sudden-onset threshold")
tu = patch(8, 0.85, 0.95, 7)
ep = predict(tu, 'sudden')
Tb = 2*math.pi/min(w for w, _, _ in tu)
prev = None
for NP in (500, 1000, 2000, 4000):
    em = bisect(lambda e: probe(tu, NP*Tb, 0.0, e), ep)
    dr = "" if prev is None else f" drift {(em-prev)/prev*100:+.4f}%"
    out(f"  NP={NP:5d}  measured {em:.6e}  pred err "
        f"{(ep-em)/em*100:+6.2f}%{dr}  [{time.time()-T0:.0f}s]")
    prev = em
out(f"DONE wall={time.time()-T0:.0f}s")
