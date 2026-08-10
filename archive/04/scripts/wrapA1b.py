"""A1 redone: the switch-on kick, extracted where the extraction is valid.

The first attempt (wrapA12) measured the free part at eps = 0.20...0.65 of
the escape threshold.  At the top of that range the extracted |Z(0)| is
0.76 rho_g, so the amplitude equation is strongly nonlinear over the whole
decay and the "constant" Z(0) e^{-lam t} drifts by 9% across the fit window.
The tell is that the fitted LINEAR coefficient came out 4.68e1 against the
exact J = 5.19e1: a 10% error in a quantity that is analytically exact.
The measurement was outside its own domain of validity, so its verdict on
the quadratic term (ratio 0.30) carries no information.

Redone here at eps/eps_c = 0.005...0.08, where |Z(0)|/rho_g stays under
0.08 and the cubic term contributes < 1% to the decay.  The quadratic term
is then a small correction to a large linear one, so the extraction needs
precision rather than range: rtol 1e-13, the forced response subtracted
through second order, and the plateau spread reported so that any run whose
spread exceeds the effect being measured is discarded rather than fitted.

Read out as the complex ratio
    R(eps) = (Z_measured(0) - Z_lin) / (eps^2)
which must converge to the predicted quadratic coefficient as eps -> 0 if
the <p,Phi> = 0 inversion is the right projection, and to something else --
in a way visible in the PHASE, not just the magnitude -- if it is not.
Budget ~25 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/wrapA1b.log', 'w')
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
out(f"G1 margin 0.10: alpha={alpha:.6f} w0={w0:.5f} Re c1={c1r:.5e}")
out(f"  spectrum of A: " + ", ".join(f"{z:.4f}" for z in np.linalg.eigvals(A)))
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
wp = 0.90*w0; Td = 2*math.pi/wp
I4 = np.eye(4)
Hp = np.linalg.solve(1j*wp*I4 - A, fV.astype(complex))
Hm = np.linalg.solve(-1j*wp*I4 - A, fV.astype(complex))
Gp = np.vdot(pvec, Hp); Gm = np.vdot(pvec, Hm)
J = abs(lam)*abs(np.vdot(pvec, fV))/abs(wp**2 + lam**2)
SYo = {P_: pr['P'], Q_: pr['Q'], V_: pr['V'], Xg_: pr['Xg'],
       kp_: pr['kp'], ki_: pr['ki'], kpv_: pr['kpv'],
       kiv_: pr['kiv'], C_: pr['C']}
Rop = solve_nf5(A, lam, qvec, pvec, fV, wp,
                make_tensors5(sp, f_, _x, SYo, pr, st, V_), param=True)
Y = Rop['Y']
c2r = Rop['c2'].real


def hv(idx):
    return np.array([Y[i].get(idx, 0) for i in range(4)])


ph20 = np.vdot(pvec, hv((0, 0, 2, 0)))
ph11 = np.vdot(pvec, hv((0, 0, 1, 1)))
ph02 = np.vdot(pvec, hv((0, 0, 0, 2)))
m1010 = np.vdot(pvec, hv((1, 0, 1, 0)))
m1001 = np.vdot(pvec, hv((1, 0, 0, 1)))
m0110 = np.vdot(pvec, hv((0, 1, 1, 0)))
m0101 = np.vdot(pvec, hv((0, 1, 0, 1)))
rg = guard_root(alpha, c1r, c2r)
eps_c = rg/J
out(f"  rho_g={rg:.6e}  J={J:.6e}  crude eps_c={eps_c:.6e}")
out(f"  <p,h20>={ph20:.4e}  <p,h11>={ph11:.4e}  <p,h02>={ph02:.4e}")


def z_lin(a):
    return -(a*Gp + np.conj(a)*Gm)


def z_quad(a):
    zl = z_lin(a)
    return zl - (ph20*a**2 + ph11*abs(a)**2 + ph02*np.conj(a)**2) \
        - (zl*a*m1010 + zl*np.conj(a)*m1001
           + np.conj(zl)*a*m0110 + np.conj(zl)*np.conj(a)*m0101)


out("")
out(" eps/eps_c |  |Z0|/rho_g | plateau spread | measured Z0            | "
    "R_meas = (Z0-Zlin)/eps^2   | R_pred (from <p,Phi>=0)")
ROWS = []
for frac in (0.005, 0.01, 0.02, 0.04, 0.08, 0.16):
    eps = frac*eps_c
    a = 0.5*eps

    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
    NP = 20
    s = solve_ivp(f, (0, NP*Td), st.copy(), method='DOP853',
                  rtol=1e-13, atol=1e-18, dense_output=True)
    ts = np.linspace(3.0*Td, NP*Td, 6000)
    ys = s.sol(ts)
    zt = np.array([np.vdot(pvec, ys[:, i] - st) for i in range(len(ts))])
    al = a*np.exp(1j*wp*ts)
    zt = zt - (al*Gp + np.conj(al)*Gm)
    zt = zt - (ph20*al**2 + ph11*np.abs(al)**2 + ph02*np.conj(al)**2)
    zf = zt*np.exp(-lam*ts)
    n = len(ts)
    seg = slice(int(0.25*n), int(0.9*n))
    Z0 = complex(np.mean(zf[seg]))
    spread = float(np.std(zf[seg] - Z0)/abs(Z0))
    Rm = (Z0 - z_lin(a))/eps**2
    Rp = (z_quad(a) - z_lin(a))/eps**2
    ROWS.append((eps, frac, Z0, Rm, Rp, spread))
    out(f"  {frac:7.3f}  | {abs(Z0)/rg:9.5f} | {spread:.3e}      | "
        f"{Z0.real:+.6e}{Z0.imag:+.6e}j | "
        f"{abs(Rm):.6e} @{np.angle(Rm):+.4f} | "
        f"{abs(Rp):.6e} @{np.angle(Rp):+.4f}  [{time.time()-T0:.0f}s]")
out("")
good = [r for r in ROWS if r[5] < 1e-3]
out(f"  rows with plateau spread < 1e-3: {len(good)} of {len(ROWS)}")
if len(good) >= 2:
    e0, f0, Z0a, Rm0, Rp0, s0 = good[0]
    e1, f1, Z1a, Rm1, Rp1, s1 = good[-1]
    out(f"  R_meas drift over the clean range: "
        f"{abs(Rm1)/abs(Rm0)-1:+.4f} in magnitude, "
        f"{np.angle(Rm1)-np.angle(Rm0):+.4f} rad in phase "
        f"(a converged R_meas means the eps^2 term is being resolved)")
    out(f"  R_meas/R_pred at the smallest clean eps: "
        f"{abs(Rm0)/abs(Rp0):.4f} in magnitude, phase difference "
        f"{np.angle(Rm0)-np.angle(Rp0):+.4f} rad")
    out(f"  linear check: |Z0|/eps at the smallest clean eps = "
        f"{abs(Z0a)/e0:.6e} vs J = {J:.6e} "
        f"({(abs(Z0a)/e0-J)/J*100:+.4f}%)")
out(f"DONE wall={time.time()-T0:.0f}s")
