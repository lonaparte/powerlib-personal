"""Is the multi-tone "threshold" even a threshold?

Five candidates are now excluded by measurement: beats, band placement,
expansion parameter, early-time erosion, and (this run's predecessor) the
multi-tone form of the a^4 term -- the residual is the same size in cells
where that term is 0.006% of alpha as in cells where it is 13%.

Which leaves a possibility that is not a correction to the criterion but a
question about what is being measured.

For a SINGLE tone the forced orbit is periodic and the criterion is sharp:
the switch-on kick either exceeds the guard or it does not, and once the
transient has decayed the state sits on the forced orbit forever with no
further chance to escape.  The threshold is a property of the system, and a
long enough window converges to it -- which is exactly what the single-tone
window sweeps showed (+0.00% from 1000 to 3000 periods).

For N incommensurate tones the forced orbit is quasi-periodic and never
repeats.  The drive's envelope beats, so the instantaneous erosion -- and
with it the instantaneous guard radius -- breathes.  Escape then does not
have to happen at t = 0: it can happen at any later moment when a rare
alignment of the tones makes the guard momentarily small enough to be
reached by whatever is left of the decaying free part.  If that is what is
happening, the multi-tone "threshold" is a rare-event threshold: it is
the drive level at which escape occurs SOMEWHERE IN THE WINDOW, and it must
drift downward as the window lengthens, without a limit that any finite run
can display.  That is the same structure as the noise branch, arrived at
from the deterministic side.

It also explains what the five excluded candidates could not: the residual
is phase-dependent (which draw has the deepest dip), has no trend in N (the
depth of the deepest dip does not care how many tones there are), and takes
either sign (the prediction is neither systematically high nor low, it is
just measuring a different quantity).

The test is a window sweep, single-tone style, on the multi-tone cells.
Sharp threshold => flat, like the single-tone cells.  Rare-event threshold
=> monotone downward drift with no sign of converging.  A cell with a LARGE
residual and a cell with a SMALL one are both run, because the prediction
is that the drift tracks the residual.
Budget ~40 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/noise1i.log', 'w')
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
A = jac(st, pr); dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
cx_ref = cx_hand(A, st, pr, qv, pv, w0, 0.90*w0, fV).real
dpar = R5['c_x'].real - R5a['c_x'].real
par_frac = dpar/(cx_ref + dpar)
c2r = R5['c2'].real; cxxr = R5['c_xx'].real; ca4r = R5['c_a4'].real
out(f"G1 margin 0.10: alpha={alpha:.6f}  rho_g(0)={math.sqrt(alpha/c1.real):.5e}")


def cx_of(wk):
    return cx_hand(A, st, pr, qv, pv, w0, wk, fV).real/(1.0 - par_frac)


def patch(N, lo, hi, seed):
    rng = np.random.default_rng(seed)
    rs = np.linspace(lo, hi, N) if N > 1 else np.array([0.5*(lo+hi)])
    rs = rs*(1 + 1e-3*rng.standard_normal(N))
    phs = rng.uniform(0, 2*math.pi, N)
    return [(rs[i]*w0, 1.0/math.sqrt(N), float(phs[i])) for i in range(N)]


def kick(tu, eps):
    Z = 0.0 + 0j
    for wk, rk, ph in tu:
        aa = 0.5*eps*rk*np.exp(1j*ph)
        Hp = np.linalg.solve(1j*wk*np.eye(4) - A, fV.astype(complex))
        Hm = np.linalg.solve(-1j*wk*np.eye(4) - A, fV.astype(complex))
        Z -= (aa*np.vdot(pv, Hp) + np.conj(aa)*np.vdot(pv, Hm))
    return abs(Z)


def predict(tu):
    def gap(eps):
        a2s = [0.25*(eps*rk)**2 for _, rk, _ in tu]
        a2t = sum(a2s)
        aeff = alpha - sum(cx_of(wk)*a2 for (wk, _, _), a2 in zip(tu, a2s))
        aeff -= sum(ca4r*a2*a2 for a2 in a2s)
        rg = guard_root(aeff, c1.real + cxxr*a2t, c2r)
        if not (rg == rg):
            return 1.0
        return kick(tu, eps) - rg
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
    ok = any(len(t) > 0 for t in s.t_events) or s.status < 0
    te = None
    if ok:
        cand = [t[0] for t in s.t_events if len(t) > 0]
        te = min(cand) if cand else s.t[-1]
    return ok, te


def bisect(tu, NP, seed):
    elo, ehi = 0.6*seed, 1.4*seed
    n = 0
    while not probe(tu, NP, ehi)[0] and n < 12:
        elo = ehi; ehi *= 1.25; n += 1
    n = 0
    while probe(tu, NP, elo)[0] and n < 12:
        ehi = elo; elo *= 0.8; n += 1
    if probe(tu, NP, elo)[0] or not probe(tu, NP, ehi)[0]:
        return float('nan'), None
    for _ in range(17):
        em = 0.5*(elo+ehi)
        if probe(tu, NP, em)[0]: ehi = em
        else: elo = em
    ec = 0.5*(elo+ehi)
    _, te = probe(tu, NP, ec*1.002)
    return ec, te


CELLS = [
    ('0.85-0.95 s7 N=8  (residual -3.80%)', patch(8, 0.85, 0.95, 7)),
    ('0.85-0.95 s7 N=16 (residual +7.59%)', patch(16, 0.85, 0.95, 7)),
    ('0.7-0.8   s7 N=4  (residual +0.53%)', patch(4, 0.70, 0.80, 7)),
    ('single tone 0.90 (control)', [(0.90*w0, 1.0, 0.0)]),
]
out("")
out("  window sweep: a sharp threshold is flat, a rare-event threshold "
    "drifts down")
for tag, tu in CELLS:
    ep = predict(tu)
    Tb = 2*math.pi/min(w for w, _, _ in tu)
    out("")
    out(f"  === {tag}")
    out(f"      predicted {ep:.6e}, slowest-tone period {Tb:.4f} s")
    out("       NP   | measured      | drift    | vs predicted | "
        "t_esc/T_slow at 1.002 eps_c")
    prev = None
    for NP in (250, 500, 1000, 2000, 4000):
        ec, te = bisect(tu, NP, prev if prev else ep)
        if not (ec == ec):
            out(f"      {NP:5d} | bisection failed"); continue
        dr = "" if prev is None else f"{(ec-prev)/prev*100:+8.4f}%"
        tt = f"{te/Tb:.1f}" if te else "n/a"
        out(f"      {NP:5d} | {ec:.6e} | {dr:>9s} | "
            f"{(ep-ec)/ec*100:+11.2f}% | {tt:>12s}  "
            f"[{time.time()-T0:.0f}s]")
        prev = ec
out("")
out("  read: if the multi-tone cells drift monotonically down while the")
out("  single-tone control stays flat, the multi-tone number is a")
out("  rare-event threshold and the residual is not an error in c_x.")
out(f"DONE wall={time.time()-T0:.0f}s")
