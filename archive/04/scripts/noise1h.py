"""The multi-tone residual: the a^4 term's multi-tone form is wrong.

Four candidates were excluded by measurement (beats, band placement,
expansion parameter, early-time erosion).  What none of them touched is the
FORM of the fifth-order drive term in the multi-tone prediction, and there
the code does two different things for two terms of the same kind:

    for each tone k:  aeff -= Re c_x(w_k) |a_k|^2 + Re c_a4 |a_k|^4
    once, on the total:  c1_eff = Re c1 + Re c_xx * sum_k |a_k|^2

c_x and c_xx are QUADRATIC in the drive amplitude, so summing per tone and
using the total are the same thing -- both correct.  c_a4 is QUARTIC, and
there they differ by a factor N.  Only one of the two can be right.

Derivation settles it.  The resonant quartic-in-drive indices for the zeta
equation are (1,0) in zeta with l_j = m_j and total drive degree 4, i.e.
both the pure terms (2,2) on a single tone and the cross terms (1,1)+(1,1)
across two tones.  Take the degenerate limit w_2 -> w_1, where the two tones
merge into one of amplitude a_1 + a_2 and the answer must reduce to
c_a4 |a_1+a_2|^4.  Now

    |a_1+a_2|^2 = |a_1|^2 + |a_2|^2 + 2 Re(a_1 abar_2)
    |a_1+a_2|^4 = (|a_1|^2+|a_2|^2)^2 + 4 Re(a_1 abar_2)(...) + 4 Re(...)^2

and for incommensurate tones every Re(a_1 abar_2) term oscillates at
w_1 - w_2 and drops.  What survives is (|a_1|^2+|a_2|^2)^2, i.e. the cross
coefficient is TWICE the pure one, and for N tones the whole quartic term
collapses to

    Re c_a4 * ( sum_k |a_k|^2 )^2      NOT   sum_k Re c_a4 |a_k|^4 .

They differ by exactly the factor N for equal amplitudes.

Why this was never caught: the single-tone cells that validated c_a4 all sit
where the term is negligible.  The V cell threshold is 1.19e-4, giving
c_a4 (eps^2/4)^2 / alpha = 0.04% -- unmeasurable either way.  The multi-tone
cells that show the residual sit at eps ~ 3-5e-4, where eps^4 is 100-250x
larger and the same term reaches several percent of alpha.  So c_a4 was
validated only in the regime where its multi-tone form cannot matter, and
then used in the regime where it can.

Tested here by re-predicting every measured multi-tone cell three ways --
per-tone (what was used), total-squared (what the derivation gives), and
omitted -- against the measurements already in the logs.  No new simulation.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time, re
LOG = open('sweep20/noise1h.log', 'w')
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
out(f"G1 margin 0.10: alpha={alpha:.6f}  Re c1={c1.real:.6e}")
out(f"  Re c_xx={cxxr:.5e}   Re c_a4={ca4r:.5e}")
out("")
out("  size of the a^4 term at a few thresholds, as a fraction of alpha:")
for eps in (1.19e-4, 2.2e-4, 3.0e-4, 5.0e-4):
    a2 = 0.25*eps*eps
    out(f"    eps={eps:.2e}:  c_a4 (eps^2/4)^2 / alpha = "
        f"{ca4r*a2*a2/alpha*100:8.4f}%")
out("  (the single-tone V cell that validated c_a4 sits at the first row)")


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


def predict(tu, mode):
    def gap(eps):
        a2s = [0.25*(eps*rk)**2 for _, rk, _ in tu]
        a2t = sum(a2s)
        aeff = alpha - sum(cx_of(wk)*a2
                           for (wk, _, _), a2 in zip(tu, a2s))
        if mode == 'pertone':
            aeff -= sum(ca4r*a2*a2 for a2 in a2s)
        elif mode == 'total':
            aeff -= ca4r*a2t*a2t
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
out("  cell                    | measured   | a^4/alpha | per-tone (used) |"
    " total (derived) | omitted")
e_p = []; e_t = []; e_o = []
for tag, tu, em in CASES:
    a2t = 0.25*em*em
    frac = ca4r*a2t*a2t/alpha*100
    pp = predict(tu, 'pertone'); pt = predict(tu, 'total')
    po = predict(tu, 'none')
    dp = (pp-em)/em*100; dt = (pt-em)/em*100; do = (po-em)/em*100
    e_p.append(abs(dp)); e_t.append(abs(dt)); e_o.append(abs(do))
    out(f"  {tag} | {em:.4e} | {frac:8.3f}% | {dp:+14.2f}% |"
        f" {dt:+14.2f}% | {do:+7.2f}%")
e_p = np.array(e_p); e_t = np.array(e_t); e_o = np.array(e_o)
out("")
out(f"  mean |err|  per-tone (used) {e_p.mean():6.3f}%   max {e_p.max():.2f}%")
out(f"  mean |err|  total (derived) {e_t.mean():6.3f}%   max {e_t.max():.2f}%")
out(f"  mean |err|  omitted         {e_o.mean():6.3f}%   max {e_o.max():.2f}%")
out("")
best = min((e_p.mean(), 'per-tone'), (e_t.mean(), 'total'),
           (e_o.mean(), 'omitted'))
out(f"  best: {best[1]}")
if e_t.mean() < 0.6*e_p.mean():
    out("  VERDICT: the derived (total-squared) form is right and the "
        "per-tone form")
    out("  was the residual.  The multi-tone item closes.")
elif e_t.mean() > e_p.mean():
    out("  VERDICT: the derived form is WORSE than what was used, which "
        "means the")
    out("  degenerate-limit argument for the cross coefficient is wrong, or "
        "c_a4")
    out("  itself is wrong at these amplitudes.  Either way the a^4 term is "
        "now")
    out("  implicated and is the next thing to derive properly.")
else:
    out("  VERDICT: partial.  The a^4 form matters but does not account for "
        "all of it.")
out(f"DONE wall={time.time()-T0:.0f}s")
