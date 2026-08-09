"""omega_g slow band: no boundary motion, but escape still occurs.
Which mechanism?  The frozen spectrum is exactly dw-independent
(alpha identical to 10 digits), so there is NO slow-passage boundary
crossing.  What remains in the co-moving amplitude equation is the
pure rate-forcing term:
      zdot = lam*z - <p, st_dw> * d(dw)/dt + c1 |z|^2 z ,
      st_dw = e2/ki   (constant),  lam, c1 constant.
Test: bisect the 4D escape threshold at ws = w0/160 and w0/32, and
compare with this reduced (constant-coefficient) amplitude equation.
Agreement => the omega_g slow-band escape is rate-forcing driven,
structurally distinct from the V/P/Q/Xg slow-passage mechanism.
Also report the implied grid phase amplitude at threshold.
Budget ~10 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/wslow.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def rhs_w(x, pr):
    y = rhs(x, pr).copy()
    y[0] -= pr.get('dw', 0.0)
    return y

prb = gset('G1')
Psn = 3*prb['V']**2/(4*prb['Xg'])
def reA(P):
    q = dict(prb, P=P); x = equil(q)
    if x is None: return None
    cm = crit_mode(jac(x, q))
    return None if cm is None else cm.real
grid = np.linspace(0.05, 0.985, 60)*Psn
va = [reA(P) for P in grid]
br = None
for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
    if fa is not None and fb is not None and fa < 0 <= fb:
        br = (a, b); break
lo, hi = br
for _ in range(45):
    m = 0.5*(lo+hi); v = reA(m)
    if v is None or v >= 0: hi = m
    else: lo = m
P0 = margin_point(prb, 0.5*(lo+hi), 0.10)
pr = dict(prb, P=P0, dw=0.0)
co = nf_coeffs(pr)
st0 = co['st']; w0 = co['w0']; pv = co['p']; c1v = co['c1']
lam = co['lam']
zg = math.sqrt(co['alpha']/c1v.real)
st_dw = np.array([0.0, 1.0/pr['ki'], 0.0, 0.0])
G = np.vdot(pv, st_dw)
out(f"G1: P0={P0:.5f} w0={w0:.3f} zg={zg:.4e} lam={lam:.5f} "
    f"c1={c1v:.2f}")
out(f"  rate-forcing coefficient <p,st_dw> = {G:.6f} "
    f"(|G|={abs(G):.6f}); st_dw = e2/ki, constant")
for ws in (w0/160, w0/32, w0/8):
    Tt1 = 12*2*math.pi/ws
    def escape1d(a):
        def f(t, y):
            z = y[0] + 1j*y[1]
            dwd = a*ws*math.cos(ws*t)          # d(dw)/dt
            dz = lam*z - G*dwd + c1v*abs(z)**2*z
            return [dz.real, dz.imag]
        def blow(t, y):
            return math.hypot(y[0], y[1]) - 5*zg
        blow.terminal = True; blow.direction = 1
        s = solve_ivp(f, (0, Tt1), [0.0, 0.0], method='DOP853',
                      rtol=1e-10, atol=1e-14, events=blow)
        return len(s.t_events[0]) > 0
    def fate4(a):
        def f(t, x):
            return rhs_w(x, dict(pr, dw=a*math.sin(ws*t)))
        def e_th(t, x): return abs(x[0] - st0[0]) - 1.2
        def e_vlo(t, x): return x[2] - 0.2
        def e_vhi(t, x): return x[2] - 2.5
        for e in (e_th, e_vlo, e_vhi):
            e.terminal = True
        e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
        s = solve_ivp(f, (0, Tt1), st0.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=(e_th, e_vlo, e_vhi))
        return any(len(t) > 0 for t in s.t_events) or s.status < 0
    AH = 20.0
    alo, ahi = 1e-3, 0.05
    n = 0
    while not fate4(ahi) and ahi < AH and n < 20:
        alo = ahi; ahi *= 1.6; n += 1
    if not fate4(min(ahi, AH)):
        out(f"  ws=w0/{w0/ws:.0f}: 4D no escape up to {AH} rad/s")
        continue
    ahi = min(ahi, AH)
    for _ in range(14):
        am = 0.5*(alo+ahi)
        if fate4(am): ahi = am
        else: alo = am
    ameas = 0.5*(alo+ahi)
    alo, ahi = 1e-3, AH
    if not escape1d(ahi):
        out(f"  ws=w0/{w0/ws:.0f}: 1D no escape at {AH}")
        pred = None
    else:
        for _ in range(15):
            am = 0.5*(alo+ahi)
            if escape1d(am): ahi = am
            else: alo = am
        pred = 0.5*(alo+ahi)
    phi = ameas/ws
    line = (f"  ws=w0/{w0/ws:.0f} ({ws:.4f} rad/s): meas={ameas:.4e} "
            f"rad/s ({ameas/(2*math.pi)*1e3:.1f} mHz, phase amp "
            f"{math.degrees(phi):.2f} deg)")
    if pred:
        line += (f"  pred(rate-forcing)={pred:.4e} "
                 f"err={(pred-ameas)/ameas*100:+.2f}%")
    out(line + f" [{time.time()-T0:.0f}s]")
    # scaling check: is the threshold set by a*ws (the rate) ?
    out(f"     rate at threshold a*ws = {ameas*ws:.4e} rad/s^2")
out(f"DONE wall={time.time()-T0:.0f}s")
