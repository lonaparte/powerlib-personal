"""Fourth candidate for the multi-tone residual: the EARLY-TIME erosion.

Three candidates are already excluded: beats (no trend in N), band placement
(off-resonance bands still scatter), and the expansion parameter (r = +0.20
against |err|).  A fourth is worth testing because it is the one thing that
is phase-dependent AND not already in the prediction, and the residual is
phase-dependent.

The prediction uses alpha_eff = alpha - sum_k Re c_x(w_k)|a_k|^2, i.e. the
LONG-TIME mean of the drive's squared envelope.  But escape, when it
happens, happens within a few envelope times of switch-on -- the free part
decays as e^{-alpha_eff t}, so the guard only has to be crossed early.  For
a single tone that distinction is empty: |alpha(t)|^2 is constant.  For N
tones it is not:

    |alpha(t)|^2 = sum_k |a_k|^2 + sum_{j != k} a_j abar_k e^{i(w_j-w_k)t}

and the cross terms only average away over times long compared with
2 pi/|w_j - w_k|.  For the 0.70-0.80 w0 band at N=4 the slowest beat period
is 5.8 s against an envelope time 1/alpha = 10 s, so over the window that
actually matters the beat has not averaged at all, and the effective
erosion during that window depends on the phase draw.

Testable with no new simulation.  Define the window-averaged ratio

    R_T = <|alpha(t)|^2>_[0,T] / sum_k |a_k|^2
        = 1 + (1/sum|a_k|^2) sum_{j!=k} a_j abar_k
                             (e^{i(w_j-w_k)T} - 1)/(i(w_j-w_k)T)

with T = 1/alpha, and re-predict each measured cell with the erosion scaled
by R_T.  If the residuals shrink, the effect is the early-time erosion and
the item closes with a stated correction; if they do not, a fourth
candidate is excluded and the item stays open with four eliminated.
Budget ~5 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time, re
LOG = open('sweep20/noise1g.log', 'w')
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
out(f"G1 margin 0.10: alpha={alpha:.6f}, envelope time 1/alpha = "
    f"{1/alpha:.2f} s")


def cx_of(wk):
    return cx_hand(A, st, pr, qv, pv, w0, wk, fV).real/(1.0 - par_frac)


def patch(N, lo, hi, seed):
    rng = np.random.default_rng(seed)
    rs = np.linspace(lo, hi, N) if N > 1 else np.array([0.5*(lo+hi)])
    rs = rs*(1 + 1e-3*rng.standard_normal(N))
    phs = rng.uniform(0, 2*math.pi, N)
    return [(rs[i]*w0, 1.0/math.sqrt(N), float(phs[i])) for i in range(N)]


def R_window(tu, T):
    """<|alpha(t)|^2>_[0,T] / sum|a_k|^2, unit eps."""
    a = [0.5*rk*np.exp(1j*ph) for _, rk, ph in tu]
    w = [wk for wk, _, _ in tu]
    base = sum(abs(x)**2 for x in a)
    cross = 0.0 + 0j
    for j in range(len(a)):
        for k in range(len(a)):
            if j == k:
                continue
            d = w[j] - w[k]
            cross += a[j]*np.conj(a[k])*(np.exp(1j*d*T) - 1)/(1j*d*T)
    return float(np.real(base + cross)/base)


def kick(tu, eps):
    Z = 0.0 + 0j
    for wk, rk, ph in tu:
        aa = 0.5*eps*rk*np.exp(1j*ph)
        Hp = np.linalg.solve(1j*wk*np.eye(4) - A, fV.astype(complex))
        Hm = np.linalg.solve(-1j*wk*np.eye(4) - A, fV.astype(complex))
        Z -= (aa*np.vdot(pv, Hp) + np.conj(aa)*np.vdot(pv, Hm))
    return abs(Z)


def predict(tu, scale):
    def gap(eps):
        aeff = alpha
        for wk, rk, ph in tu:
            a2 = 0.25*(eps*rk)**2
            aeff -= scale*cx_of(wk)*a2 + ca4r*a2*a2
        a2t = sum(0.25*(eps*rk)**2 for _, rk, _ in tu)
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
        CASES.append((f'0.85-0.95 s7 N={m.group(1)}',
                      patch(int(m.group(1)), 0.85, 0.95, 7),
                      float(m.group(2))))
for ln in open('sweep20/noise1c.log').read().split('\n'):
    m = re.match(r'\s*([\d.]+)-([\d.]+)\s+s(\d+)\s*\|\s*(\d+)\s*\|'
                 r'\s*[\d.]+\s*\|\s*([\d.eE+-]+)\s*\|', ln)
    if m:
        lo_, hi_ = float(m.group(1)), float(m.group(2))
        if hi_ > 0.93:          # skip the on-resonance band, explained already
            continue
        CASES.append((f'{lo_}-{hi_} s{m.group(3)} N={m.group(4)}',
                      patch(int(m.group(4)), lo_, hi_, int(m.group(3))),
                      float(m.group(5))))

out("")
out("  cell                        | R_T(1/alpha) | err as-is | "
    "err with R_T | improved?")
e0 = []; e1 = []
for tag, tu, em in CASES:
    RT = R_window(tu, 1.0/alpha)
    p0 = predict(tu, 1.0)
    p1 = predict(tu, RT)
    d0 = (p0 - em)/em*100
    d1 = (p1 - em)/em*100
    e0.append(abs(d0)); e1.append(abs(d1))
    out(f"  {tag:27s} | {RT:12.4f} | {d0:+8.2f}% | {d1:+11.2f}% | "
        f"{'yes' if abs(d1) < abs(d0) else 'no'}")
e0 = np.array(e0); e1 = np.array(e1)
out("")
out(f"  mean |err| as-is        {e0.mean():.3f}%   (max {e0.max():.2f}%)")
out(f"  mean |err| with R_T     {e1.mean():.3f}%   (max {e1.max():.2f}%)")
out(f"  improved in {int((e1 < e0).sum())} of {len(e0)} cells")
out(f"  R_T range across cells: {min(R_window(t, 1/alpha) for _, t, _ in CASES):.4f}"
    f" .. {max(R_window(t, 1/alpha) for _, t, _ in CASES):.4f}")
out("")
if e1.mean() < 0.7*e0.mean():
    out("  VERDICT: the early-time erosion accounts for most of the "
        "residual.")
elif e1.mean() > 1.1*e0.mean():
    out("  VERDICT: applying it makes things WORSE -- a fourth candidate is")
    out("  excluded, and the sign says the long-time mean is the right")
    out("  average after all.")
else:
    out("  VERDICT: no material change.  Fourth candidate excluded; the")
    out("  multi-tone residual stays open with beats, band placement,")
    out("  expansion parameter and early-time erosion all eliminated.")
out(f"DONE wall={time.time()-T0:.0f}s")
