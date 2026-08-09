"""The closed form behind eps_c(alpha): replace the crude sizing by the
normal-form forced amplitude equation.

The sizing used so far,
    eps_est = 2 r_g |lam - i w_p| / |<p,f_u>|,
is "linear response reaches the guard radius".  Against the measured
thresholds it is high by a factor that is CONSTANT in alpha (~1.55),
i.e. its scaling is right and an O(1) geometric factor is missing.  The
missing factor is not free to fit: it is contained in the leading-order
forced amplitude equation itself,

    dz/dt = lam z + c1 |z|^2 z + eps <p,f_u> cos(w_p t),

whose escape threshold is a derived quantity.  Non-dimensionalising with
z = r_g Z gives a problem that depends only on
    s = (w0 - w_p)/alpha ,  gamma = Im c1 / Re c1 ,  w0/alpha ,
so the reduced threshold is reported as the dimensionless number
    E_c = eps_c |<p,f_u>| / (alpha r_g)
and the rotating-wave sizing is E_est = 2 sqrt(1 + s^2)... in the same
units, exposing what the factor is made of.

Protocol matched to the 4D measurement: switch-on at the operating point
(z = 0 at t = 0), same drive frequency ratio r = 0.9, escape when the
modal amplitude leaves the guard neighbourhood.  Escape-radius
insensitivity (3 / 5 / 8 r_g) is reported, since that is the only
discretisation-like choice in the reduced model.
Set: G1, V channel, r = 0.9, same alpha grid as the 4D sweep.
Budget ~4 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/ecscale.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

prb = gset('G1')
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
PH = 0.5*(lo+hi)
out(f"G1: P_H={PH:.6f}, drive ratio r = 0.9")
out("alpha |   s=sigma/alpha  gamma=Imc1/Rec1 | eps_NF(5rg)   E_c    "
    "E_est=2|lam-iwp|/alpha | rad 3rg   rad 8rg")

for marg in (0.05, 0.10, 0.15, 0.20, 0.30):
    P0 = margin_point(prb, PH, marg)
    pr = dict(prb, P=P0)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; alpha = co['alpha']
    c1v = co['c1']; lam = co['lam']
    rg = math.sqrt(alpha/c1v.real)
    h = 1e-6
    fV = (rhs(st, dict(pr, V=pr['V']+h))
          - rhs(st, dict(pr, V=pr['V']-h)))/(2*h)
    F = np.vdot(co['p'], fV)
    wd = 0.9*w0; Td = 2*math.pi/wd
    s = (w0 - wd)/alpha
    gam = c1v.imag/c1v.real
    def esc(eps, frad, NP=400):
        def f(t, y):
            z = y[0] + 1j*y[1]
            dz = lam*z + c1v*abs(z)**2*z + eps*F*math.cos(wd*t)
            return [dz.real, dz.imag]
        def blow(t, y):
            return math.hypot(y[0], y[1]) - frad*rg
        blow.terminal = True; blow.direction = 1
        sol = solve_ivp(f, (0, NP*Td), [0.0, 0.0], method='DOP853',
                        rtol=1e-11, atol=1e-14, events=blow)
        return len(sol.t_events[0]) > 0
    def thr(frad):
        elo, ehi = 1e-6, 1e-2
        n = 0
        while not esc(ehi, frad) and ehi < 1.0 and n < 20:
            elo = ehi; ehi *= 1.6; n += 1
        n = 0
        while esc(elo, frad) and elo > 1e-9 and n < 20:
            ehi = elo; elo *= 0.5; n += 1
        if esc(elo, frad) or not esc(ehi, frad):
            return None
        for _ in range(16):
            em = 0.5*(elo+ehi)
            if esc(em, frad): ehi = em
            else: elo = em
        return 0.5*(elo+ehi)
    e5 = thr(5.0); e3 = thr(3.0); e8 = thr(8.0)
    if e5 is None:
        out(f"{marg:.2f} | reduced model: no escape bracket"); continue
    Ec = e5*abs(F)/(alpha*rg)
    Eest = 2*abs(lam - 1j*wd)/alpha
    out(f"{marg:.2f} |   {s:9.3f}      {gam:+.5f}     | {e5:.5e}  "
        f"{Ec:8.3f}  {Eest:8.3f}          | "
        f"{(e3-e5)/e5*100:+.3f}%  {(e8-e5)/e5*100:+.3f}%  "
        f"[{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
