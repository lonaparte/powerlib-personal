"""Fifth order, assembled correctly.

mech4 produced the coefficients and validated them (c1 against Kuznetsov
2e-8, c_x against the hand-derived sum/difference/DC expression 1e-8,
Re c2 against the earlier homological solver to five digits), but two
things were wrong in the way they were used.

  * The quartic guard equation Re c2 rho^4 + c1_eff rho^2 - alpha_eff = 0
    has a second positive root once alpha_eff turns negative.  That root
    is spurious -- when alpha_eff <= 0 the guard is gone and the system
    escapes -- and the threshold search was locking onto it (+785%).
  * The switch-on kick was corrected with only the a^2 terms of
    <p,Phi> = 0.  Since Z = O(a), the cross terms Z a are the same order,
    so that correction was inconsistent.  Done properly, Z(0) solves
        0 = Z + P_{0010} a + P_{0001} abar + Q(Z, Zbar, a, abar)
    with Q the full quadratic part of <p,Phi>, iterated to convergence.

Also settled here: where each coefficient is evaluated.  The two-carrier
homological solution needs the Hopf point (at the operating point the
(2,1,0,0) denominator is -2 alpha, near-resonant, so the removal is not
admissible).  But c1 and c_x have closed formulas that are regular at the
operating point, and evaluating them there resums their leading alpha
dependence -- mech3 measured that this is worth 0.2-0.45 points.  So:
c1 and c_x at the operating point, c2 / c_xx / c_a4 at the Hopf point
with alpha carrying the unfolding, order-2 h's (for the kick) at the
operating point.  Every one of these is a computed model quantity.

Reported: measured threshold against four variants -- cubic with the
leading kick (what mech1 had), cubic with the consistent kick, quintic
with the leading kick, quintic with the consistent kick -- so the size of
each ingredient is visible rather than merged.  Cells: V channel four
margins, idx17, and the omega_g slow cell where the term ratios show
whether ANY finite truncation can work there.
Budget ~30 min.
"""
exec(open('selfhead.py').read())
import itertools, time
from math import factorial
LOG = open('sweep20/mech5.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
TR = 5
_src = open('mech4.py').read()
_ns = {'__name__': 'mech4mod'}
_body = _src.split('CELLS = ')[0]
exec(compile(_body.replace("LOG = open('sweep20/mech4.log', 'w')",
                           "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
two_carrier_nf = _ns['two_carrier_nf']
hopf = _ns['hopf']
tensors_at = _ns['tensors_at']
cx_hand = _ns['cx_hand']

def rhs_w(x, prm):
    y = rhs(x, prm).copy(); y[0] -= prm.get('dw', 0.0); return y

def guard_root(aeff, c1e, c2e):
    """positive root continuing rho^2 = aeff/c1e as c2e -> 0;
    nan when the guard does not exist."""
    if aeff <= 0.0 or c1e <= 0.0:
        return float('nan')
    if abs(c2e)*aeff < 1e-12*c1e**2:
        return math.sqrt(aeff/c1e)
    disc = c1e**2 + 4*c2e*aeff
    if disc < 0.0:
        return float('nan')
    r2 = (-c1e + math.sqrt(disc))/(2*c2e)
    return math.sqrt(r2) if r2 > 0 else float('nan')

def order2_projections(pr, st, A, lam, q, p, wp, fu):
    """<p,h_pi> for every order-2 index, at the operating point."""
    B2, _ = tensors_at(pr, st)
    I = np.eye(4)
    H = np.linalg.solve(1j*wp*I - A, fu.astype(complex)); Hc = np.conj(H)
    qc = np.conj(q)
    def solve(D, v):
        return np.linalg.solve(D*I - A, v)
    h = {}
    h[(2, 0, 0, 0)] = solve(2*lam, 0.5*B2(q, q))
    h[(1, 1, 0, 0)] = solve(lam+np.conj(lam), B2(q, qc))
    h[(0, 2, 0, 0)] = np.conj(h[(2, 0, 0, 0)])
    h[(1, 0, 1, 0)] = solve(lam+1j*wp, B2(q, H))
    h[(1, 0, 0, 1)] = solve(lam-1j*wp, B2(q, Hc))
    h[(0, 1, 1, 0)] = np.conj(h[(1, 0, 0, 1)])
    h[(0, 1, 0, 1)] = np.conj(h[(1, 0, 1, 0)])
    h[(0, 0, 2, 0)] = solve(2j*wp, 0.5*B2(H, H))
    h[(0, 0, 1, 1)] = solve(0.0, B2(H, Hc))
    h[(0, 0, 0, 2)] = np.conj(h[(0, 0, 2, 0)])
    P = {k: np.vdot(p, v) for k, v in h.items()}
    P[(0, 0, 1, 0)] = np.vdot(p, H); P[(0, 0, 0, 1)] = np.vdot(p, Hc)
    return P
def kick(eps, P, order2=True):
    a = 0.5*eps
    z = -(P[(0, 0, 1, 0)]*a + P[(0, 0, 0, 1)]*a)
    if not order2:
        return z
    for _ in range(12):
        zb = np.conj(z)
        Q = (P[(2, 0, 0, 0)]*z*z + P[(1, 1, 0, 0)]*z*zb
             + P[(0, 2, 0, 0)]*zb*zb
             + P[(1, 0, 1, 0)]*z*a + P[(1, 0, 0, 1)]*z*a
             + P[(0, 1, 1, 0)]*zb*a + P[(0, 1, 0, 1)]*zb*a
             + P[(0, 0, 2, 0)]*a*a + P[(0, 0, 1, 1)]*a*a
             + P[(0, 0, 0, 2)]*a*a)
        zn = -(P[(0, 0, 1, 0)]*a + P[(0, 0, 0, 1)]*a) - Q
        if abs(zn - z) < 1e-15*max(1.0, abs(zn)):
            z = zn; break
        z = 0.5*(z + zn)
    return z

CELLS = [('G1 V r=0.9', {}, 0.9, 'V', (0.05, 0.10, 0.15, 0.20)),
         ('idx17 r=0.92', dict(kp=55., ki=1200., Xg=0.40), 0.92, 'V', (0.08,))]
for tag, over, rat, chan, margs in CELLS:
    prb = gset('G1', **over)
    PH = hopf(prb)
    prH = dict(prb, P=PH); stH = equil(prH); coH = nf_coeffs(prH)
    w0H = coH['w0']; wpH = rat*w0H
    hs = 1e-6
    fuH = (rhs(stH, dict(prH, V=prH['V']+hs))
           - rhs(stH, dict(prH, V=prH['V']-hs)))/(2*hs)
    R = two_carrier_nf(prH, wpH, fuH)
    c2r = R['c2'].real; cxxr = R['c_xx'].real; ca4r = R['c_a4'].real
    out(f"=== {tag}: P_H={PH:.6f}; Hopf-point quintic coefficients "
        f"Re c2={c2r:.4e}, Re c_xx={cxxr:.4e}, Re c_a4={ca4r:.4e} "
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
        cx = cx_hand(A, st, pr, qv, pv, w0, wp, fV)
        P = order2_projections(pr, st, A, lam, qv, pv, wp, fV)
        c1r = c1.real; cxr = cx.real
        def gap(eps, quintic, ord2):
            a2 = 0.25*eps*eps
            aeff = alpha - cxr*a2 - (ca4r*a2*a2 if quintic else 0.0)
            c1e = c1r + (cxxr*a2 if quintic else 0.0)
            rg = guard_root(aeff, c1e, c2r if quintic else 0.0)
            if not (rg == rg):
                return 1.0
            return abs(kick(eps, P, ord2)) - rg
        def thr(quintic, ord2, seed):
            lo, hi = 1e-12, 4*seed
            if gap(hi, quintic, ord2) <= 0:
                return float('nan')
            for _ in range(200):
                mm = 0.5*(lo+hi)
                if gap(mm, quintic, ord2) > 0: hi = mm
                else: lo = mm
            return 0.5*(lo+hi)
        seed = math.sqrt(alpha/c1r)/abs(P[(0, 0, 1, 0)] + P[(0, 0, 0, 1)])*2
        e_c1 = thr(False, False, seed); e_c2 = thr(False, True, seed)
        e_q1 = thr(True, False, seed); e_q2 = thr(True, True, seed)
        NPw = 1000 if rat == 0.9 else 4000
        def probe(eps, NPn):
            def f(t, x):
                return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
            def e_th(t, x): return abs(x[0] - st[0]) - dsad
            def e_vlo(t, x): return x[2] - 0.20*Vdc0
            def e_vhi(t, x): return x[2] - 2.50*Vdc0
            for e in (e_th, e_vlo, e_vhi):
                e.terminal = True
            e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
            s = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                          rtol=1e-10, atol=1e-13,
                          events=(e_th, e_vlo, e_vhi))
            return (any(len(s.t_events[i]) > 0 for i in range(3))
                    or s.status < 0)
        elo, ehi = 0.6*e_q2, 1.4*e_q2
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
        def pc(x):
            return f"{(x-emeas)/emeas*100:+6.2f}%" if x == x else "  n/a  "
        out(f"  alpha={alpha:.3f} measured {emeas:.6e} | cubic+lead "
            f"{pc(e_c1)} | cubic+2nd-order kick {pc(e_c2)} | quintic+lead "
            f"{pc(e_q1)} | quintic+2nd-order kick {pc(e_q2)}  "
            f"[{time.time()-T0:.0f}s]")
        a2c = 0.25*emeas*emeas
        out(f"          term sizes at the threshold: Re c_x a^2/alpha "
            f"{cxr*a2c/alpha:+.4f}, Re c_a4 a^4/alpha "
            f"{ca4r*a2c*a2c/alpha:+.5f}, Re c_xx a^2/Re c1 "
            f"{cxxr*a2c/c1r:+.5f}, Re c2 rho_g^2/Re c1 "
            f"{c2r*(alpha-cxr*a2c)/c1r**2:+.5f}, kick 2nd-order shift "
            f"{(abs(kick(emeas,P,True))-abs(kick(emeas,P,False)))/abs(kick(emeas,P,False))*100:+.2f}%")

# ---------------- omega_g slow cell: can any finite order work? -------
prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0, dw=0.0)
co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']; c1 = co['c1']
lam = co['lam']; pv = co['p']; qv = co['q']
A = jac(st, pr); rg0 = math.sqrt(alpha/c1.real)
phi = 0.5*(math.sqrt(5.0)-1.0)
Tc_nf = 2*math.pi/(w0 + c1.imag*rg0**2)
ws = 2*math.pi/((8.0+phi)*Tc_nf)
fdw = -np.eye(4)[0]
prH = dict(prb, P=PH, dw=0.0); stH = equil(prH); coH = nf_coeffs(prH)
Rw = two_carrier_nf(prH, ws, fdw)
cxw = cx_hand(A, st, pr, qv, pv, w0, ws, fdw)
AC = 0.9427837
a2c = 0.25*AC*AC
out(f"=== omega_g slow cell (w_s={ws:.5f}, a_c={AC:.5f}): term sizes at "
    f"the measured threshold")
out(f"    Re c_x a^2/alpha  = {cxw.real*a2c/alpha:+.4f}")
out(f"    Re c_a4 a^4/alpha = {Rw['c_a4'].real*a2c*a2c/alpha:+.4f}")
out(f"    Re c_xx a^2/Re c1 = {Rw['c_xx'].real*a2c/c1.real:+.4f}")
out("    -> the a^4 term relative to the a^2 term is the expansion's own "
    "ratio; if it is not small no finite truncation converges here")
out(f"    ratio |a^4 term| / |a^2 term| = "
    f"{abs(Rw['c_a4'].real*a2c*a2c)/abs(cxw.real*a2c):.4f}")
out(f"DONE wall={time.time()-T0:.0f}s")
