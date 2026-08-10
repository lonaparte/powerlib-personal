"""The multi-tone residual: is the floor the KICK, not the fifth order?

The closed form |Z(0)|_c = rho_g/sqrt(G) is exact for the cubic reduced
equation, so the 0.521% mean / 1.541% max residual against the 4-state
measurement has to come from one of three places: fifth-order content, the
c_x(w) interpolation, or the map from the forced displacement to the
normal-form amplitude Z(0).  The recorded attempt addressed the first and
made it worse (0.521 -> 1.525%).

The third has never been touched, and it is now available: a1iso derived the
second-order isochron projection

    zeta(dx) = <p,dx> + sum_ij Q_ij a_i a_j ,
    Q_ij = -(1/2)<p,B(e_i,e_j)>/(lam_i+lam_j-lam) ,   dx = sum_i a_i e_i

which cut the single-kick error from 3.98% to 0.59% over eight directions.
The multi-tone Z(0) is exactly such a projection: the drive displaces the
state to dx = -sum_k [a_k H(w_k) + c.c.] and the criterion needs the
amplitude that displacement corresponds to.  Z(0) has so far been taken as
<p,dx>, the linear term only.

Two things get reported and not conflated:
 (a) does the second-order kick move the 17-cell residual, and which way;
 (b) the DOMAIN of the cubic closed form, as a number rather than a
     sentence: the recorded excuse for the residual is "the fifth order is
     out of its domain in the high-a^4 cells", which is testable by
     regressing the residual on the a^4/alpha the log already carries.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time, re
import numpy as np
LOG = open('sweep20/mt2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"), 'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']; cx_hand = _ns['cx_hand']
hs = 1e-6

prb = gset('G1'); PH = hopf(prb)
prH = dict(prb, P=PH); stH = equil(prH); coH = nf_coeffs(prH)
w0H = coH['w0']; AH = jac(stH, prH)
evH, VLH, VRH = eig(AH, left=True, right=True)
kH = max((i for i in range(4) if evH[i].imag > 1e-9), key=lambda i: evH[i].real)
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
pv = co['p']; qv = co['q']; lam = co['lam']; c1r = co['c1'].real
A = jac(st, pr)
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
cx_ref = cx_hand(A, st, pr, qv, pv, w0, 0.90*w0, fV).real
par_frac = (R5['c_x'].real - R5a['c_x'].real)/(cx_ref + R5['c_x'].real
                                               - R5a['c_x'].real)
rg0 = math.sqrt(alpha/c1r)
_al = _avl(st, pr)


def B2(u, v):
    return np.array([sum(_Hl[i][j][k](*_al)*u[j]*v[k]
                         for j in range(4) for k in range(4))
                     for i in range(4)])


ev, VL, VR = eig(A, left=True, right=True)
PP = np.array([VL[:, i]/np.vdot(VR[:, i], VL[:, i]) for i in range(4)])
Qt = np.zeros((4, 4), complex)
for i in range(4):
    for j in range(4):
        Qt[i, j] = -0.5*np.vdot(pv, B2(VR[:, i], VR[:, j])) \
            / (ev[i] + ev[j] - lam)
out(f"G1 margin 0.10: alpha={alpha:.6f} rho_g={rg0:.6e}")

_c = {}


def cx_of(wk):
    k = round(wk, 9)
    if k not in _c:
        _c[k] = cx_hand(A, st, pr, qv, pv, w0, wk, fV).real/(1.0 - par_frac)
    return _c[k]


def patch(N, lo, hi, seed):
    rng = np.random.default_rng(seed)
    rs = np.linspace(lo, hi, N) if N > 1 else np.array([0.5*(lo+hi)])
    rs = rs*(1 + 1e-3*rng.standard_normal(N))
    phs = rng.uniform(0, 2*math.pi, N)
    return [(rs[i]*w0, 1.0/math.sqrt(N), float(phs[i])) for i in range(N)]


def dx_of(tu, eps):
    d = np.zeros(4)
    for wk, rk, ph in tu:
        aa = 0.5*eps*rk*np.exp(1j*ph)
        Hp = np.linalg.solve(1j*wk*np.eye(4) - A, fV.astype(complex))
        Hm = np.linalg.solve(-1j*wk*np.eye(4) - A, fV.astype(complex))
        d = d - np.real(aa*Hp + np.conj(aa)*Hm)
    return d


def Z_lin(tu, eps):
    return np.vdot(pv, dx_of(tu, eps))


def Z_2(tu, eps):
    d = dx_of(tu, eps)
    a = np.array([np.vdot(PP[i], d) for i in range(4)])
    return np.vdot(pv, d) + complex(np.einsum('ij,i,j->', Qt, a, a))


trap = np.trapezoid if hasattr(np, 'trapezoid') else np.trapz


def beat_G(tu, eps, NS=20000, TM=30.0):
    ws = np.array([wk for wk, _, _ in tu])
    aa = np.array([0.5*eps*rk*np.exp(1j*ph) for _, rk, ph in tu])
    cxv = np.array([cx_of(wk) for wk in ws])
    CX = 0.5*(cxv[:, None] + cxv[None, :])
    M = CX*(aa[:, None]*np.conj(aa)[None, :])
    D = ws[:, None] - ws[None, :]
    ae = alpha - float(np.real(np.trace(M)))
    off = ~np.eye(len(ws), dtype=bool)
    Mo = M[off]; Do = D[off]
    s = np.linspace(0.0, TM/ae, NS)
    Psi = np.real(np.sum(Mo[:, None]*(np.exp(1j*Do[:, None]*s[None, :]) - 1.0)
                         / (1j*Do[:, None]), axis=0))
    return 2*ae*float(trap(np.exp(-2*ae*s + 2*Psi), s)), ae


def thr(tu, seed, zf):
    def esc(eps):
        Gv, ae = beat_G(tu, eps)
        if ae <= 0:
            return True
        return abs(zf(tu, eps)) > math.sqrt(ae/c1r)/math.sqrt(Gv)
    lo, hi = 0.6*seed, 1.4*seed
    n = 0
    while not esc(hi) and n < 14:
        lo = hi; hi *= 1.25; n += 1
    n = 0
    while esc(lo) and n < 14:
        hi = lo; lo *= 0.8; n += 1
    if esc(lo) or not esc(hi):
        return float('nan')
    for _ in range(30):
        m = 0.5*(lo+hi)
        if esc(m): hi = m
        else: lo = m
    return 0.5*(lo+hi)


CASES = []
for ln in open('sweep20/close2.log'):
    m = re.match(r'\s+([\d.]+)-([\d.]+)\s+s(\d+)\s+N=\s*(\d+)\s*\|\s*'
                 r'([+-][\d.]+)%\s*\|\s*([+-][\d.]+)%\s*\|\s*([\d.]+)%', ln)
    if m:
        CASES.append((f"{m.group(1)}-{m.group(2)} s{m.group(3):<2s} "
                      f"N={m.group(4):>3s}",
                      patch(int(m.group(4)), float(m.group(1)),
                            float(m.group(2)), int(m.group(3))),
                      float(m.group(5)), float(m.group(7))))
for ln in open('sweep20/close2.log'):
    m = re.match(r'\s+([\d.]+)-([\d.]+)\s+s(\d+)\s+N=\s*(\d+)', ln)
out(f"parsed {len(CASES)} cells")
MEAS = {}
for ln in open('sweep20/formula.log'):
    m = re.match(r'\s+(\S+\s+\S+\s+N=\s*\d+)\s*\|\s*([\d.e+-]+)\s', ln)
    if m:
        MEAS[re.sub(r'\s+', ' ', m.group(1))] = float(m.group(2))
out("")
out("  cell                 | a^4/alpha | linear kick | 2nd-order kick")
e1 = []; e2 = []; a4 = []
for tag, tu, err_rec, a4f in CASES:
    key = re.sub(r'\s+', ' ', tag)
    em = MEAS.get(key)
    if em is None:
        out(f"  {tag} | measurement not found, skipped"); continue
    p1 = thr(tu, em, Z_lin); p2 = thr(tu, em, Z_2)
    d1 = (p1-em)/em*100; d2 = (p2-em)/em*100
    e1.append(abs(d1)); e2.append(abs(d2)); a4.append(a4f)
    out(f"  {tag} | {a4f:8.2f}% | {d1:+8.3f}%  | {d2:+8.3f}%   "
        f"[{time.time()-T0:.0f}s]")
e1 = np.array(e1); e2 = np.array(e2); a4 = np.array(a4)
out(f"    mean |err|  linear {e1.mean():.3f}%  ->  2nd-order kick "
    f"{e2.mean():.3f}%")
out(f"    max  |err|  linear {e1.max():.3f}%  ->  {e2.max():.3f}%")
out(f"    improved in {int((e2 < e1).sum())}/{len(e1)} cells")
out("")
out("  domain of the cubic closed form, as a number:")
if len(a4) > 3:
    hi = a4 > 1.0
    out(f"    cells with a^4/alpha > 1%: n={int(hi.sum())}, mean |err| "
        f"{e1[hi].mean():.3f}% (2nd-order kick {e2[hi].mean():.3f}%)")
    out(f"    cells with a^4/alpha < 1%: n={int((~hi).sum())}, mean |err| "
        f"{e1[~hi].mean():.3f}% (2nd-order kick {e2[~hi].mean():.3f}%)")
    cc = float(np.corrcoef(a4, e1)[0, 1])
    out(f"    corr(a^4/alpha, |err_linear|) = {cc:+.3f};  "
        f"corr with 2nd-order kick = {float(np.corrcoef(a4, e2)[0, 1]):+.3f}")
out(f"DONE wall={time.time()-T0:.0f}s")
