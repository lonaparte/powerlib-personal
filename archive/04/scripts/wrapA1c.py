"""A1, third attempt: subtract ALL of Phi, not just its drive-only part.

wrapA1b moved to small drive levels and the linear coefficient came out
right, but the plateau was still not flat: the relative spread of
Z(0) = zeta(t) e^{-lam t} was 8.0e-4 at eps/eps_c = 0.005 and grew exactly
in proportion to eps.  A residual proportional to eps means an eps^2 term
left in zeta_est, and the eps^2 term is precisely what the run is trying to
measure -- so the measurement was buried under its own systematic.

The cause is structural.  The subtraction removed the drive-only part of
Phi (h_0020 alpha^2, h_0011 |alpha|^2, h_0002 alphabar^2) but Phi also
carries the MIXED terms h_1010 zeta alpha, h_1001 zeta alphabar, and the
zeta-only terms h_2000 zeta^2, h_1100 |zeta|^2, ... all of which are
O(zeta a) = O(eps^2) while zeta is still alive, and all of which oscillate,
so they show up as spread rather than bias.  Averaging them to zero is why
R_meas came out at 2% of R_pred: the plateau mean was measuring the
cancellation of an oscillation, not the constant underneath it.

Fixed here by inverting the whole series instead of part of it:

    zeta_est(t) = <p, y(t) - x_eq> - sum_{deg(pi) >= 2} <p,h_pi>
                    zeta^j zetabar^k alpha^l alphabar^m
                  - <p,h_0010> alpha - <p,h_0001> alphabar ,

evaluated by fixed-point iteration in zeta (the sum needs zeta, which the
equation defines), through degree 3.  The free part is then fit as
    log zeta_est(t) - lam t  =  log Z0 + mu t
with mu a small complex slope, which absorbs the amplitude-dependent
detuning from c1 and c_x instead of assuming pure e^{lam t} decay.  If the
subtraction is complete the residual about that fit collapses by orders of
magnitude, and only then is the extracted eps^2 coefficient worth reading.

The verdict is the complex ratio R_meas/R_pred as eps -> 0: 1 in magnitude
AND 0 in phase means the <p,Phi> = 0 inversion is the right projection;
anything else means the asymptotic amplitude is not obtained by inverting
the transformation at fixed alpha, and the kick needs the nonlinear
isochron instead.
Budget ~25 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/wrapA1c.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']
hs = 1e-6

prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
lam = co['lam']; pvec = co['p']; qvec = co['q']; c1r = co['c1'].real
A = jac(st, pr)
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
wp = 0.90*w0; Td = 2*math.pi/wp
I4 = np.eye(4)
Gp = np.vdot(pvec, np.linalg.solve(1j*wp*I4 - A, fV.astype(complex)))
Gm = np.vdot(pvec, np.linalg.solve(-1j*wp*I4 - A, fV.astype(complex)))
J = abs(lam)*abs(np.vdot(pvec, fV))/abs(wp**2 + lam**2)
SYo = {P_: pr['P'], Q_: pr['Q'], V_: pr['V'], Xg_: pr['Xg'],
       kp_: pr['kp'], ki_: pr['ki'], kpv_: pr['kpv'],
       kiv_: pr['kiv'], C_: pr['C']}
Rop = solve_nf5(A, lam, qvec, pvec, fV, wp,
                make_tensors5(sp, f_, _x, SYo, pr, st, V_), param=True)
Y = Rop['Y']; c2r = Rop['c2'].real
rg = guard_root(alpha, c1r, c2r); eps_c = rg/J
out(f"G1 margin 0.10: alpha={alpha:.6f} w0={w0:.5f} Re c1={c1r:.5e}")
out(f"  rho_g={rg:.6e}  J={J:.6e}  crude eps_c={eps_c:.6e}")

# every <p, h_pi> with 1 <= deg <= 3, excluding the (1,0,0,0) identity
PIS = []
for idx in set().union(*[set(Y[i].keys()) for i in range(4)]):
    d = sum(idx)
    if d < 1 or d > 3 or idx == (1, 0, 0, 0):
        continue
    cf = np.vdot(pvec, np.array([Y[i].get(idx, 0) for i in range(4)]))
    if abs(cf) > 0:
        PIS.append((idx, cf))
PIS.sort(key=lambda t: (sum(t[0]), t[0]))
out(f"  {len(PIS)} non-identity terms of Phi through degree 3 subtracted")
for idx, cf in PIS:
    if sum(idx) <= 2:
        out(f"     {idx}  <p,h> = {cf:+.5e}")


def phi_sum(z, al):
    """sum over the non-identity terms, given arrays zeta(t), alpha(t)."""
    s = np.zeros_like(z)
    zb = np.conj(z); ab = np.conj(al)
    for idx, cf in PIS:
        j, k, l, m = idx
        s = s + cf*(z**j)*(zb**k)*(al**l)*(ab**m)
    return s


def z_lin(a):
    return -(a*Gp + np.conj(a)*Gm)


def z_quad(a):
    """the <p,Phi(zeta,zetabar,a,abar)> = 0 root, to O(a^2)."""
    zl = z_lin(a)
    corr = 0.0 + 0j
    for idx, cf in PIS:
        j, k, l, m = idx
        if j + k + l + m != 2:
            continue
        corr += cf*(zl**j)*(np.conj(zl)**k)*(a**l)*(np.conj(a)**m)
    return zl - corr


out("")
out(" eps/eps_c | |Z0|/rho_g | fit residual | iters | measured Z0"
    "               | R_meas=(Z0-Zlin)/eps^2  | R_pred")
ROWS = []
for frac in (0.005, 0.01, 0.02, 0.04, 0.08):
    eps = frac*eps_c
    a = 0.5*eps

    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
    NP = 24
    s = solve_ivp(f, (0, NP*Td), st.copy(), method='DOP853',
                  rtol=1e-13, atol=1e-18, dense_output=True)
    ts = np.linspace(4.0*Td, NP*Td, 8000)
    ys = s.sol(ts)
    yp = np.array([np.vdot(pvec, ys[:, i] - st) for i in range(len(ts))])
    al = a*np.exp(1j*wp*ts)
    z = yp - (al*Gp + np.conj(al)*Gm)      # first guess: linear only
    Z0 = None; resid = float('nan'); nit = 0
    Vm = np.vstack([np.ones_like(ts), ts]).T
    for nit in range(1, 13):
        zest = yp - phi_sum(z, al)
        L = np.log(zest) - lam*ts
        L = np.unwrap(L.imag)*1j + L.real
        cf = np.linalg.lstsq(Vm, L, rcond=None)[0]
        fit = Vm @ cf
        r = float(np.std(np.abs(L - fit)))
        Znew = np.exp(cf[0])
        znew = np.exp(fit + lam*ts)
        if Z0 is not None and abs(Znew - Z0) < 1e-13*abs(Znew):
            z = znew; resid = r; Z0 = Znew
            break
        z = znew; resid = r; Z0 = Znew
    Rm = (Z0 - z_lin(a))/eps**2
    Rp = (z_quad(a) - z_lin(a))/eps**2
    ROWS.append((eps, frac, Z0, Rm, Rp, resid))
    out(f"  {frac:7.3f}  | {abs(Z0)/rg:10.6f} | {resid:.3e}    | {nit:5d} | "
        f"{Z0.real:+.7e}{Z0.imag:+.7e}j | "
        f"{abs(Rm):.5e} @{np.angle(Rm):+.4f} | "
        f"{abs(Rp):.5e} @{np.angle(Rp):+.4f}  [{time.time()-T0:.0f}s]")
out("")
if len(ROWS) >= 3:
    out("  extrapolation of R_meas to eps -> 0 (linear in eps):")
    ee = np.array([r[0] for r in ROWS])
    Rm = np.array([r[3] for r in ROWS])
    Vm2 = np.vstack([np.ones_like(ee), ee]).T
    cRe = np.linalg.lstsq(Vm2, Rm.real, rcond=None)[0]
    cIm = np.linalg.lstsq(Vm2, Rm.imag, rcond=None)[0]
    R0 = cRe[0] + 1j*cIm[0]
    Rp = ROWS[0][4]
    out(f"    R_meas(0) = {R0.real:+.6e}{R0.imag:+.6e}j "
        f"(|.|={abs(R0):.6e} @{np.angle(R0):+.5f})")
    out(f"    R_pred    = {Rp.real:+.6e}{Rp.imag:+.6e}j "
        f"(|.|={abs(Rp):.6e} @{np.angle(Rp):+.5f})")
    out(f"    ratio |R_meas(0)|/|R_pred| = {abs(R0)/abs(Rp):.5f}, "
        f"phase difference {np.angle(R0)-np.angle(Rp):+.5f} rad")
    out(f"    linear check: |Z0|/eps at the smallest eps = "
        f"{abs(ROWS[0][2])/ROWS[0][0]:.7e} vs J = {J:.7e} "
        f"({(abs(ROWS[0][2])/ROWS[0][0]-J)/J*100:+.5f}%)")
    out(f"    residual improvement vs wrapA1b (which was 8.0e-4 at "
        f"eps/eps_c=0.005): {ROWS[0][5]:.2e}")
out(f"DONE wall={time.time()-T0:.0f}s")
