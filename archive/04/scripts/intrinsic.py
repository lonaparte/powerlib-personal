"""Parameterization audit, part 1: replace the ad-hoc numbers in the
detectors and the escape-time law by intrinsic model quantities.

(A) Detector thresholds.  Currently |theta - theta*| > 1.2, Vdc < 0.2,
    Vdc > 2.5 -- all arbitrary.  Intrinsic replacements:
      theta   : the saddle angular distance  d_sad = pi - 2|theta*|
                (the unstable equilibrium of the synchronising torque)
      Vdc low : the model's own singularity Vdc -> 0 (the 1/Vdc term);
                use a fraction of the equilibrium value that is far
                below any recovery, and SHOW the threshold is
                insensitive over a wide band
      Vdc high: the DC-side power-balance turning point (no natural
                bound; show insensitivity instead)
    Test: recompute a known sudden-on threshold with detectors placed
    at several intrinsic multiples and report the spread.

(B) Escape-time law.  Currently t_esc ~ (eps-eps_c)^(-0.9), a fit.
    Two candidate derivations:
      hyperbolic bottleneck near the invariant curve -> t ~ K ln(1/d)
      saddle-node-like bottleneck                    -> t ~ K d^(-1/2)
    Fit both forms to the measured escape times and compare residuals;
    the winner has a derived exponent, no free power.
Budget ~12 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/intrinsic.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

over = dict(kp=55., ki=1200., Xg=0.40)
prb = gset('G1', **over)
Psn = 3*prb['V']**2/(4*prb['Xg'])
def reA(P):
    q = dict(prb, P=P); x = equil(q)
    if x is None: return None
    cm = crit_mode(jac(x, q))
    return None if cm is None else cm.real
grid = np.linspace(0.05, 0.985, 60)*Psn
va = [reA(P) for P in grid]; br = None
for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
    if fa is not None and fb is not None and fa < 0 <= fb:
        br = (a, b); break
lo, hi = br
for _ in range(45):
    m = 0.5*(lo+hi); v = reA(m)
    if v is None or v >= 0: hi = m
    else: lo = m
P0 = margin_point(prb, 0.5*(lo+hi), 0.08)
pr = dict(prb, P=P0)
co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']; c1v = co['c1']
rg = math.sqrt(alpha/c1v.real)
dsad = math.pi - 2*abs(st[0])
wd = 0.92*w0; Td = 2*math.pi/wd
kappa = 2*alpha
out(f"idx17 set: theta*={st[0]:.5f} d_sad={dsad:.5f} r_g={rg:.4e} "
    f"alpha={alpha:.4f} kappa=2alpha={kappa:.4f} w0={w0:.3f}")

# ---------- (A) intrinsic detectors ----------
out("(A) detector placement, expressed in intrinsic units")
def probe(eps, fth, fvlo, fvhi, NPn=400):
    """fth: multiple of d_sad; fvlo/fvhi: fractions of Vdc*"""
    Vdc0 = st[2]
    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wd*t)))
    def e_th(t, x): return abs(x[0] - st[0]) - fth*dsad
    def e_vlo(t, x): return x[2] - fvlo*Vdc0
    def e_vhi(t, x): return x[2] - fvhi*Vdc0
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NPn*Td), st.copy(), method='DOP853',
                  rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
    ev = [len(s.t_events[i]) > 0 for i in range(3)]
    if any(ev) or s.status < 0:
        te = min([t[0] for t in s.t_events if len(t)], default=s.t[-1])
        which = ('TH' if ev[0] else 'VLO' if ev[1]
                 else 'VHI' if ev[2] else 'SOLVER')
        return which, te
    return None, None
base = None
for fth, fvlo, fvhi in ((1.00, 0.20, 2.50), (0.90, 0.30, 2.00),
                        (1.00, 0.10, 3.00), (0.80, 0.40, 1.80)):
    elo, ehi = 5e-3, 1.2e-2
    while probe(ehi, fth, fvlo, fvhi)[0] is None and ehi < 5e-2:
        elo = ehi; ehi *= 1.4
    while probe(elo, fth, fvlo, fvhi)[0] is not None and elo > 1e-4:
        ehi = elo; elo *= 0.7
    for _ in range(13):
        em = 0.5*(elo+ehi)
        if probe(em, fth, fvlo, fvhi)[0] is not None: ehi = em
        else: elo = em
    ec = 0.5*(elo+ehi)
    kind, _ = probe(ehi, fth, fvlo, fvhi)
    if base is None:
        base = ec
    out(f"  theta at {fth:.2f} d_sad, Vdc in [{fvlo:.2f},{fvhi:.2f}] Vdc*: "
        f"eps_c={ec:.5e} ({(ec-base)/base*100:+.3f}% vs first) mode={kind} "
        f"[{time.time()-T0:.0f}s]")

# ---------- (B) escape-time law ----------
out("(B) escape-time law above the threshold")
epsc = base
facs = (1.02, 1.05, 1.10, 1.20, 1.35, 1.55, 1.80)
data = []
for fa in facs:
    kind, te = probe(fa*epsc, 1.00, 0.20, 2.50, NPn=3000)
    if te is None:
        out(f"  fac={fa}: no escape"); continue
    data.append((fa, te/Td))
    out(f"  fac={fa:.2f}: t_esc={te:.3f}s = {te/Td:.1f} drive periods "
        f"({kind})")
if len(data) >= 4:
    d = np.array([x[0]-1.0 for x in data])      # relative overshoot
    t = np.array([x[1] for x in data])
    # candidate 1: t = C1 * ln(1/d) + C0   (hyperbolic bottleneck)
    M1 = np.vstack([np.log(1.0/d), np.ones_like(d)]).T
    c1f, r1, _, _ = np.linalg.lstsq(M1, t, rcond=None)
    res1 = float(np.sum((M1 @ c1f - t)**2))
    # candidate 2: t = C * d^(-1/2)        (saddle-node bottleneck)
    M2 = np.vstack([d**-0.5, np.ones_like(d)]).T
    c2f, _, _, _ = np.linalg.lstsq(M2, t, rcond=None)
    res2 = float(np.sum((M2 @ c2f - t)**2))
    # candidate 3: free power law (what was fitted before)
    M3 = np.vstack([np.log(d), np.ones_like(d)]).T
    c3f, _, _, _ = np.linalg.lstsq(M3, np.log(t), rcond=None)
    res3 = float(np.sum((M3 @ c3f - np.log(t))**2))
    out(f"  ln-law  t = {c1f[0]:.3f} ln(1/d) + {c1f[1]:.3f} : sse={res1:.4e}")
    out(f"  d^-1/2  t = {c2f[0]:.3f} d^-1/2 + {c2f[1]:.3f} : sse={res2:.4e}")
    out(f"  free power  t ~ d^({c3f[0]:.3f})  : sse(log)={res3:.4e}")
    out(f"  predicted ln-law slope from the guard exponent: "
        f"1/kappa = {1.0/kappa:.3f} s = {1.0/kappa/Td:.2f} periods "
        f"(kappa = 2 alpha = {kappa:.4f})")
out(f"DONE wall={time.time()-T0:.0f}s")
