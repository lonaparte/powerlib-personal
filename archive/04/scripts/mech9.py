"""Q channel +0.57%: is it the drive channel being bound to the wrong symbol?

mech8's coverage run gave V +0.03% / P +0.04% / Q +0.57% for the fifth-order
closed form, and printed a parametric share of -0.02% for the P channel.
That last number cannot be right: P enters the GFL field only through P/C
in the DC-link balance, so

    df/dP = e3/C = const   ==>   d^2 f/dy dP == 0   ==>   share == 0 exactly.

The cause is that mech7's tensors5 hardcodes the fifth expansion variable to
V_, so the multiplicative operator is always d^2 f/dy dV no matter which
parameter carries the drive.  For P that injects a spurious operator; for Q
it substitutes the wrong one, and Q's own multiplicative channel

    d f3/dQ = 1.5 (-Xg idr + vgq)/(Vdc C)          (state-dependent)

is genuinely nonzero and not proportional to V's.  So the Q additive-only
residual +0.56% is exactly the size of a missing-but-real parametric term.

Run here, with nf5drv.py binding the drive symbol per channel:
 (1) symbolic audit of d^2 f/dy du for u = V, P, Q -- P's must be identically
     zero, and the V/Q operators must not be parallel;
 (2) V/P/Q thresholds, additive vs additive+parametric, correct binding,
     against the measured threshold;
 (3) the same with the OLD (V-bound) tensors, to confirm the diagnosis is
     the binding and nothing else;
 (4) per-channel window convergence (1000 vs 3000 periods) so protocol bias
     is separated from theory error.
Budget ~30 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/mech9.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']; cx_hand = _ns['cx_hand']

SYMS = lambda pr: {P_: pr['P'], Q_: pr['Q'], V_: pr['V'], Xg_: pr['Xg'],
                   kp_: pr['kp'], ki_: pr['ki'], kpv_: pr['kpv'],
                   kiv_: pr['kiv'], C_: pr['C']}
DRV = {'V': V_, 'P': P_, 'Q': Q_}

prb = gset('G1'); PH = hopf(prb)
prH = dict(prb, P=PH); stH = equil(prH); coH = nf_coeffs(prH)
w0H = coH['w0']; wpH = 0.90*w0H; hs = 1e-6
out(f"G1 Hopf P_H={PH:.6f}, w0_H={w0H:.5f}  [{time.time()-T0:.0f}s]")

# ---- (1) symbolic audit: d^2 f_i / dx_j du at the Hopf equilibrium ----
out("")
out("--- mixed second derivatives d^2 f_i/dx_j du at the Hopf point ---")
subsH = dict(SYMS(prH)); subsH.update({_x[i]: stH[i] for i in range(4)})
MIX = {}
for nm, u in DRV.items():
    Mx = np.zeros((4, 4))
    zero = True
    for i in range(4):
        for j in range(4):
            e = sp.diff(f_[i], _x[j], u)
            if e != 0:
                zero = False
                Mx[i, j] = float(sp.re(e.subs(subsH).evalf()))
    MIX[nm] = Mx
    out(f"  u={nm}: identically zero = {zero}, ||.||_max = "
        f"{np.max(np.abs(Mx)):.5e}")
for a, b in (('V', 'Q'), ('V', 'P'), ('P', 'Q')):
    na, nb = np.linalg.norm(MIX[a]), np.linalg.norm(MIX[b])
    if na > 0 and nb > 0:
        cs = float(np.sum(MIX[a]*MIX[b])/(na*nb))
        out(f"  cos angle({a},{b}) = {cs:+.5f}   (1 => parallel, so the "
            f"V-bound run would only rescale)")
    else:
        out(f"  cos angle({a},{b}) undefined: one operator is zero")

# ---- operating point ----
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
lam = co['lam']; pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr); dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
wp = 0.90*w0; Td = 2*math.pi/wp
AH = jac(stH, prH)
evH, VLH, VRH = eig(AH, left=True, right=True)
kH = max((i for i in range(4) if evH[i].imag > 1e-9),
         key=lambda i: evH[i].real)
lamH = evH[kH]; qH = VRH[:, kH]; pH = VLH[:, kH]; pH = pH/np.vdot(qH, pH)
out("")
out(f"operating point: alpha={alpha:.5f}, Re c1={c1.real:.6e}, "
    f"w_p={wp:.5f}")


def measured(k, NP):
    def probe(eps):
        def f(t, x):
            return rhs(x, dict(pr, **{k: pr[k] + eps*math.cos(wp*t)}))
        def e_th(t, x): return abs(x[0] - st[0]) - dsad
        def e_vlo(t, x): return x[2] - 0.20*Vdc0
        def e_vhi(t, x): return x[2] - 2.50*Vdc0
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, NP*Td), st.copy(), method='DOP853',
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
    for _ in range(18):
        em = 0.5*(elo+ehi)
        if probe(em): ehi = em
        else: elo = em
    return 0.5*(elo+ehi)


out("")
out("--- thresholds, drive symbol bound correctly ---")
out(" ch | measured(1000) | 5th additive   | 5th add+param  | share  | "
    "measured(3000)  drift")
RES = {}
for k in ('V', 'P', 'Q'):
    fuH = (rhs(stH, dict(prH, **{k: prH[k]+hs}))
           - rhs(stH, dict(prH, **{k: prH[k]-hs})))/(2*hs)
    DkC = make_tensors5(sp, f_, _x, SYMS(prH), prH, stH, DRV[k])
    Rp = solve_nf5(AH, lamH, qH, pH, fuH, wpH, DkC, param=True)
    Ra = solve_nf5(AH, lamH, qH, pH, fuH, wpH, DkC, param=False)
    DkV = make_tensors5(sp, f_, _x, SYMS(prH), prH, stH, V_)
    RpV = solve_nf5(AH, lamH, qH, pH, fuH, wpH, DkV, param=True)
    fu = (rhs(st, dict(pr, **{k: pr[k]+hs}))
          - rhs(st, dict(pr, **{k: pr[k]-hs})))/(2*hs)
    cx_add = cx_hand(A, st, pr, qv, pv, w0, wp, fu).real
    dcx = Rp['c_x'].real - Ra['c_x'].real
    dcxV = RpV['c_x'].real - Ra['c_x'].real
    J = abs(lam)*abs(np.vdot(pv, fu))/abs(wp**2 + lam**2)

    def thr(cxr, c2r, cxxr, ca4r):
        lo, hi = 1e-14, 1.0
        for _ in range(200):
            m = 0.5*(lo+hi); a2 = 0.25*m*m
            ae = alpha - cxr*a2 - ca4r*a2*a2
            rgv = guard_root(ae, c1.real + cxxr*a2, c2r)
            if not (rgv == rgv) or m*J > rgv: hi = m
            else: lo = m
        return 0.5*(lo+hi)
    e_add = thr(cx_add, Ra['c2'].real, Ra['c_xx'].real, Ra['c_a4'].real)
    e_par = thr(cx_add + dcx, Rp['c2'].real, Rp['c_xx'].real, Rp['c_a4'].real)
    e_parV = thr(cx_add + dcxV, RpV['c2'].real, RpV['c_xx'].real,
                 RpV['c_a4'].real)
    em1 = bisect(measured(k, 1000), e_par)
    em3 = bisect(measured(k, 3000), em1)
    RES[k] = (em1, em3, e_add, e_par, e_parV, dcx, dcxV, cx_add)

    def pc(x, ref):
        return f"{(x-ref)/ref*100:+6.2f}%"
    out(f" {k}  | {em1:.6e} | {e_add:.6e} {pc(e_add, em1)} | "
        f"{e_par:.6e} {pc(e_par, em1)} | "
        f"{dcx/(cx_add+dcx)*100:+6.2f}% | {em3:.6e} "
        f"{pc(em3, em1)}  [{time.time()-T0:.0f}s]")
    out(f"      V-bound (mech8's binding) would give {e_parV:.6e} "
        f"{pc(e_parV, em1)}, share {dcxV/(cx_add+dcxV)*100:+.2f}%")
    out(f"      Re c_x additive {cx_add:.6e}, parametric increment "
        f"{dcx:+.6e} (V-bound {dcxV:+.6e})")

out("")
out("--- against the converged (3000-period) measurement ---")
for k in ('V', 'P', 'Q'):
    em1, em3, e_add, e_par, e_parV, dcx, dcxV, cxa = RES[k]
    out(f" {k}: additive {(e_add-em3)/em3*100:+6.2f}%  add+param "
        f"{(e_par-em3)/em3*100:+6.2f}%  (V-bound {(e_parV-em3)/em3*100:+6.2f}%)")
out(f"DONE wall={time.time()-T0:.0f}s")
