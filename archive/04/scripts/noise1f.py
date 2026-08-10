"""Is the multi-tone residual just the known validity boundary?

The multi-tone residual has survived two hypotheses:
 - beats between tones (noise1b: swept N at fixed band and power, expecting
   error ~ alpha N / BW; got +0.31/+3.08/-3.80/+7.59/-2.71%, no trend);
 - a tone landing inside the resonance (noise1c: bands placed entirely
   off-resonance, nearest tone 39-65 alpha away from w0; still +-3%).

What both sweeps show instead is SEED dependence: the same band and the
same N with a different phase draw moves the answer by several percent.
Only one thing in the prediction is phase-dependent -- the kick, which is a
phasor sum.  And the phasor sum is exactly what sets how large the drive
has to be: when the random phases nearly cancel, the threshold eps must
grow to compensate, and a larger eps means a larger EROSION, which is the
expansion parameter of the whole construction.

The campaign already has a stated validity condition for that parameter:
|Re c_x| a^2 / alpha <~ 1 at threshold (V cell 0.53, idx17 0.65 pass;
omega_g slow band 7.9 fails, and that cell is handled by landing instead).
So the hypothesis here is not a new mechanism at all -- it is that the
multi-tone cells with cancelling phases are simply running the closed form
further out along its own known axis.

This needs no new simulation: for each cell already measured, the erosion
fraction at the MEASURED threshold is a closed-form evaluation.  If the
residual tracks that fraction, the multi-tone residual is the validity
boundary and not a defect; if it does not, the phase story is wrong too and
the item stays open with one fewer candidate.
Budget ~3 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time, re
LOG = open('sweep20/noise1f.log', 'w')
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
ca4r = R5['c_a4'].real
out(f"G1 margin 0.10: alpha={alpha:.6f} w0={w0:.5f} Re c1={c1.real:.6e}")
out("  reference: the single-tone V cell runs at erosion/alpha = 0.53 at")
out("  threshold and lands at +0.03%; the omega_g slow band runs at 7.9")
out("  and the closed form is unusable there.")


def cx_of(wk):
    return cx_hand(A, st, pr, qv, pv, w0, wk, fV).real/(1.0 - par_frac)


def patch(N, lo, hi, seed):
    rng = np.random.default_rng(seed)
    rs = np.linspace(lo, hi, N) if N > 1 else np.array([0.5*(lo+hi)])
    rs = rs*(1 + 1e-3*rng.standard_normal(N))
    phs = rng.uniform(0, 2*math.pi, N)
    return [(rs[i]*w0, 1.0/math.sqrt(N), float(phs[i])) for i in range(N)]


def kick_unit(tu):
    Z = 0.0 + 0j
    for wk, ak, ph in tu:
        a = 0.5*ak*np.exp(1j*ph)
        Hp = np.linalg.solve(1j*wk*np.eye(4) - A, fV.astype(complex))
        Hm = np.linalg.solve(-1j*wk*np.eye(4) - A, fV.astype(complex))
        Z -= (a*np.vdot(pv, Hp) + np.conj(a)*np.vdot(pv, Hm))
    return abs(Z)


ROWS = []
for src, tag in (('sweep20/noise1b.log', 'noise1b band 0.85-0.95'),
                 ('sweep20/noise1c.log', 'noise1c')):
    try:
        txt = open(src).read()
    except OSError:
        continue
    for ln in txt.split('\n'):
        m = re.match(r'\s*(\d+)\s*\|\s*[\d.]+\s*\|\s*[\d.]+\s*\|\s*'
                     r'([\d.eE+-]+)\s*\|\s*([\d.eE+-]+)\s*\|\s*([+-][\d.]+)%',
                     ln)
        if m and 'noise1b' in src:
            N = int(m.group(1)); em = float(m.group(2))
            err = float(m.group(4))
            ROWS.append((f'{tag} N={N}', patch(N, 0.85, 0.95, 7), em, err))
            continue
        m2 = re.match(r'\s*([\d.]+)-([\d.]+)\s+s(\d+)\s*\|\s*(\d+)\s*\|'
                      r'\s*[\d.]+\s*\|\s*([\d.eE+-]+)\s*\|\s*([\d.eE+-]+)'
                      r'\s*\|\s*([+-][\d.]+)%', ln)
        if m2 and 'noise1c' in src:
            lo = float(m2.group(1)); hi = float(m2.group(2))
            sd = int(m2.group(3)); N = int(m2.group(4))
            em = float(m2.group(5)); err = float(m2.group(7))
            ROWS.append((f'{tag} {lo}-{hi} s{sd} N={N}',
                         patch(N, lo, hi, sd), em, err))

out("")
out("  cell                                | eps_meas   | kick |Z0|/eps | "
    "erosion/alpha | |err|")
out("  (erosion evaluated at the MEASURED threshold, so it is the actual")
out("   expansion parameter each cell was run at)")
DAT = []
for tag, tu, em, err in ROWS:
    ero = sum(cx_of(wk)*0.25*(em*rk)**2 for wk, rk, _ in tu)
    ero += sum(ca4r*(0.25*(em*rk)**2)**2 for wk, rk, _ in tu)
    kk = kick_unit(tu)
    DAT.append((ero/alpha, abs(err), tag))
    out(f"  {tag:35s} | {em:.4e} | {kk:11.4e} | {ero/alpha:13.4f} | "
        f"{abs(err):5.2f}%")
out("")
if len(DAT) >= 4:
    x = np.array([d[0] for d in DAT]); y = np.array([d[1] for d in DAT])
    cc = float(np.corrcoef(x, y)[0, 1])
    sl, ic = np.polyfit(x, y, 1)
    out(f"  correlation of |err| with erosion/alpha: r = {cc:+.4f}")
    out(f"  linear fit |err| = {sl:.3f} * (erosion/alpha) + {ic:.3f} %")
    out(f"  erosion/alpha range across the multi-tone cells: "
        f"{x.min():.3f} .. {x.max():.3f}")
    out("")
    if cc > 0.6:
        out("  VERDICT: the residual tracks the expansion parameter, so the")
        out("  multi-tone cells are running the closed form further out")
        out("  along its own known validity axis -- not a new defect.")
    elif abs(cc) < 0.35:
        out("  VERDICT: no correlation.  The phase/expansion-parameter story")
        out("  fails too; the multi-tone residual stays OPEN with beats,")
        out("  band placement and expansion parameter all excluded.")
    else:
        out("  VERDICT: weak correlation -- not decisive either way; more")
        out("  cells needed before claiming this closed.")
out(f"DONE wall={time.time()-T0:.0f}s")
