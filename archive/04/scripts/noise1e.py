"""The slowly-raised protocol has no sharp threshold, and that is structural.

noise1b tested the slow-ramp criterion (no kick, so escape exactly when the
guard vanishes, alpha_eff = 0) by lengthening the ramp, on the theory that
the -5..-6% residual was non-adiabaticity.  It went the wrong way:

    single tone, ramp R/alpha    R = 5   measured 1.73113e-4   -6.19%
                                 R = 20  measured 1.76939e-4   -8.22%

Longer ramp, LARGER measured threshold, moving further from the predicted
1.62391e-4.  Non-adiabaticity cannot do that, and the sign tells you what
can.

Under a slow ramp the state rides the forced orbit, which in normal-form
coordinates is zeta = 0 exactly.  A state exactly on zeta = 0 never escapes
no matter how small the guard becomes; escape needs a residual excitation,
and the ramp itself is the only thing supplying it.  A longer ramp is more
adiabatic, supplies LESS residual, and therefore needs a larger drive --
which is the observed direction.  So the ramp length controls the residual,
not the error.

That leaves the real limit, and it is not fixable by a better protocol.
Escape from a residual r requires rho_g(eps) < r, and near the threshold the
escape RATE vanishes with the guard: lambda_u = 2 alpha_eff -> 0 as
alpha_eff -> 0.  The escape time therefore diverges at the very point the
criterion names.  Any finite observation window reports a threshold above
alpha_eff = 0, by an amount set by the window and not by the physics.  The
slow-ramp criterion is a limit point that is approached logarithmically,
never attained -- exactly the same structure as the sudden-onset
observation-window bias, but unavoidable rather than merely present.

Tested here by varying the thing that actually controls it -- the HOLD
length after the ramp, at fixed ramp -- and checking that the measured
threshold falls monotonically toward 1.62391e-4 as the hold grows.  If it
does, the criterion is right and the protocol is the limitation; if it
plateaus somewhere above, the erosion coefficient is wrong by that plateau.
Budget ~35 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/noise1e.log', 'w')
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
R5 = solve_nf5(AH, lamH, qH, pH, fuH, 0.90*w0H,
               make_tensors5(sp, f_, _x, SYH, prH, stH, V_), param=True)
R5a = solve_nf5(AH, lamH, qH, pH, fuH, 0.90*w0H,
                make_tensors5(sp, f_, _x, SYH, prH, stH, V_), param=False)

P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr); dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
wp = 0.90*w0; Td = 2*math.pi/wp
cx_ref = cx_hand(A, st, pr, qv, pv, w0, wp, fV).real
dpar = R5['c_x'].real - R5a['c_x'].real
cxr = cx_ref + dpar
c2r = R5['c2'].real; cxxr = R5['c_xx'].real; ca4r = R5['c_a4'].real
out(f"G1 margin 0.10: alpha={alpha:.6f} w0={w0:.5f} Re c1={c1.real:.6e}")
out(f"  Re c_x(0.9 w0) = {cxr:.6e} (additive {cx_ref:.6e} + parametric "
    f"{dpar:+.4e})")


def rho_g_of(eps):
    a2 = 0.25*eps*eps
    ae = alpha - cxr*a2 - ca4r*a2*a2
    return guard_root(ae, c1.real + cxxr*a2, c2r), ae


def eps_star():
    lo, hi = 1e-12, 1.0
    for _ in range(220):
        m = 0.5*(lo+hi)
        rg, ae = rho_g_of(m)
        if ae <= 0 or not (rg == rg): hi = m
        else: lo = m
    return 0.5*(lo+hi)


EST = eps_star()
out(f"  alpha_eff = 0 at eps* = {EST:.7e}   "
    f"(cubic-only 2 sqrt(alpha/Re c_x) = {2*math.sqrt(alpha/cxr):.7e})")
out("")
out("  guard radius and escape rate just below eps*:")
for f in (0.90, 0.97, 0.99, 0.995, 0.999):
    rg, ae = rho_g_of(f*EST)
    out(f"    eps/eps* = {f:.3f}:  alpha_eff = {ae:.6e},  rho_g = {rg:.4e},"
        f"  lambda_u = 2 alpha_eff = {2*ae:.4e},  1/lambda_u = {1/(2*ae):.1f} s")


def probe(eps, Tramp, Thold):
    def f(t, x):
        s = min(1.0, t/Tramp) if Tramp > 0 else 1.0
        return rhs(x, dict(pr, V=pr['V'] + s*eps*math.cos(wp*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, Tramp + Thold), st.copy(), method='DOP853',
                  rtol=1e-11, atol=1e-14, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0


def bisect(fn, seed, nit=18):
    elo, ehi = 0.75*seed, 1.35*seed
    n = 0
    while not fn(ehi) and n < 10:
        elo = ehi; ehi *= 1.2; n += 1
    n = 0
    while fn(elo) and n < 10:
        ehi = elo; elo *= 0.85; n += 1
    if fn(elo) or not fn(ehi):
        return float('nan')
    for _ in range(nit):
        em = 0.5*(elo+ehi)
        if fn(em): ehi = em
        else: elo = em
    return 0.5*(elo+ehi)


out("")
out("=== A. hold length varied at fixed ramp (R = 20/alpha = 200 s)")
out("   hold/alpha^-1 | hold (s) | measured    | vs eps*  | "
    "implied alpha_eff at threshold")
Tr = 20.0/alpha
prev = None
for H in (10, 30, 100, 300):
    Th = H/alpha
    em = bisect(lambda e: probe(e, Tr, Th), EST)
    rg, ae = rho_g_of(em)
    dr = "" if prev is None else f"  drift {(em-prev)/prev*100:+.3f}%"
    out(f"   {H:13d} | {Th:8.0f} | {em:.6e} | {(em-EST)/EST*100:+7.3f}% | "
        f"{ae:.4e} (1/lambda_u = {1/(2*ae) if ae > 0 else float('inf'):.0f} s)"
        f"{dr}  [{time.time()-T0:.0f}s]")
    prev = em

out("")
out("=== B. ramp length varied at fixed long hold (300/alpha = 3000 s)")
out("   (if the residual story is right, the threshold must now be almost")
out("    independent of the ramp -- the hold, not the ramp, is the limit)")
Th = 300.0/alpha
for R in (5, 20, 80):
    Tr = R/alpha
    em = bisect(lambda e: probe(e, Tr, Th), EST)
    out(f"   R={R:4d}  ramp {Tr:7.0f} s | measured {em:.6e} | "
        f"{(em-EST)/EST*100:+7.3f}%  [{time.time()-T0:.0f}s]")

out("")
out("=== C. the same statement seen directly: escape time vs drive level")
out("   eps/eps* | predicted 1/lambda_u | measured t_esc (ramp 200 s)")
Tr = 20.0/alpha
for f in (0.95, 0.98, 0.99, 0.995):
    eps = f*EST
    rg, ae = rho_g_of(eps)

    def ff(t, x):
        s = min(1.0, t/Tr)
        return rhs(x, dict(pr, V=pr['V'] + s*eps*math.cos(wp*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - dsad
    def e_vlo(t, x): return x[2] - 0.20*Vdc0
    def e_vhi(t, x): return x[2] - 2.50*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(ff, (0, Tr + 6000.0), st.copy(), method='DOP853',
                  rtol=1e-11, atol=1e-14, events=(e_th, e_vlo, e_vhi))
    te = min((t[0] for t in s.t_events if len(t) > 0), default=None)
    tv = f"{te-Tr:.1f} s" if te is not None else "> 6000 s (no escape)"
    out(f"   {f:8.3f} | {1/(2*ae) if ae > 0 else float('inf'):19.1f} s | "
        f"{tv}  [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
