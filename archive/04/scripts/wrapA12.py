"""Two GFL wrap-ups that were left open by the audit.

A2 -- the escape rate to fifth order.  The radial equation
    rho' = -alpha_eff rho + c1_eff rho^3 + Re c2 rho^5
has its guard at the root of Re c2 rho^4 + c1_eff rho^2 - alpha_eff = 0, so
    lambda_u = d/drho (rho') |_{rho_g}
             = -alpha_eff + 3 c1_eff rho_g^2 + 5 Re c2 rho_g^4
             = 2 c1_eff rho_g^2 + 4 Re c2 rho_g^4
             = 2 alpha_eff + 2 Re c2 rho_g^4 ,
using alpha_eff = c1_eff rho_g^2 + Re c2 rho_g^4 to eliminate rho_g.  The
cubic limit is the familiar lambda_u = 2 alpha; the fifth-order term is the
correction that was never checked.  It is checked here against the EXACT
Floquet exponent of the unforced unstable limit cycle, located by Newton on
the (period, point) system and differentiated by its monodromy matrix.  No
drive is involved, so nothing about the two-carrier machinery can hide in
the answer.

A1 -- what the switch-on kick actually is.  The state at t = 0- is the
unforced equilibrium, y = 0, and the drive is already at full amplitude at
t = 0+, so the carrier variable starts at whatever value corresponds to
y = 0.  That inversion is ill-posed as stated: with alpha frozen at a, the
image of Phi is a 2D surface in R^4 and y = 0 does not lie on it.  The
object that IS well defined is the asymptotic amplitude -- follow the
trajectory, let the two strongly stable directions collapse, and read off
which free-oscillation solution it converges to.  Earlier attempts guessed
that projection (linear <p,.>, then <p,Phi> = 0 with the quadratic terms)
and the second guess made the threshold agreement WORSE, which is the
signature of using the wrong projection rather than a missing term.

Measured here directly: at four sub-threshold drive levels, integrate the
forced system, subtract the linear and second-order forced response, and
back-extrapolate the surviving free oscillation to t = 0.  That gives the
complex Z(0) with no assumption at all.  Then compare
    Z_lin = -(a G+ + abar G-)                                   O(eps)
    Z_quad = Z_lin - <p, h20 a^2 + h11 |a|^2 + h02 abar^2>
             - (mixed zeta-alpha second-order terms)            O(eps^2)
in magnitude AND phase.  Whichever reproduces the measured eps^2 slope is
the right object; if neither does, the projection is nonlinear and that is
the finding.
Budget ~35 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/wrapA12.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']; cx_hand = _ns['cx_hand']

prb = gset('G1'); PH = hopf(prb)
prH = dict(prb, P=PH); stH = equil(prH); coH = nf_coeffs(prH)
w0H = coH['w0']; hs = 1e-6
AH = jac(stH, prH)
evH, VLH, VRH = eig(AH, left=True, right=True)
kH = max((i for i in range(4) if evH[i].imag > 1e-9),
         key=lambda i: evH[i].real)
lamH = evH[kH]; qH = VRH[:, kH]; pH = VLH[:, kH]; pH = pH/np.vdot(qH, pH)
SY = {P_: prH['P'], Q_: prH['Q'], V_: prH['V'], Xg_: prH['Xg'],
      kp_: prH['kp'], ki_: prH['ki'], kpv_: prH['kpv'],
      kiv_: prH['kiv'], C_: prH['C']}
fuH = (rhs(stH, dict(prH, V=prH['V']+hs))
       - rhs(stH, dict(prH, V=prH['V']-hs)))/(2*hs)
DkV = make_tensors5(sp, f_, _x, SY, prH, stH, V_)
R5 = solve_nf5(AH, lamH, qH, pH, fuH, 0.90*w0H, DkV, param=True)
c2r = R5['c2'].real
out(f"G1: P_H={PH:.6f}, Re c2={c2r:.6e}  [{time.time()-T0:.0f}s]")

# =====================================================================
# A2: exact Floquet exponent of the unforced unstable limit cycle
# =====================================================================
out("")
out("=== A2: lambda_u = 2 alpha_eff + 2 Re c2 rho_g^4, against exact Floquet")
out(" alpha  | rho_g      | exact lambda_u | 2 alpha (cubic)   | "
    "fifth order        | period")


def flow(pr, x0, T):
    s = solve_ivp(lambda t, y: rhs(y, pr), (0, T), x0, method='DOP853',
                  rtol=1e-12, atol=1e-14)
    return s.y[:, -1]


def find_cycle(pr, st, pvec, x_guess, T_guess):
    """Newton on [phi(T,x) - x ; Im<p, x-st>] = 0 in (x, T)."""
    z = np.concatenate([x_guess, [T_guess]])
    for _ in range(60):
        x = z[:4]; T = z[4]
        F = np.zeros(5)
        F[:4] = flow(pr, x, T) - x
        F[4] = float(np.imag(np.vdot(pvec, x - st)))
        if np.max(np.abs(F)) < 1e-11:
            return x, T, True
        Jm = np.zeros((5, 5))
        for i in range(5):
            dz = np.zeros(5)
            dz[i] = 1e-7*max(1.0, abs(z[i]))
            zp = z + dz
            Fp = np.zeros(5)
            Fp[:4] = flow(pr, zp[:4], zp[4]) - zp[:4]
            Fp[4] = float(np.imag(np.vdot(pvec, zp[:4] - st)))
            Jm[:, i] = (Fp - F)/dz[i]
        try:
            dz = np.linalg.solve(Jm, -F)
        except np.linalg.LinAlgError:
            return x, T, False
        nrm = np.linalg.norm(dz)
        if nrm > 0.5*max(1.0, np.linalg.norm(z)):
            dz *= 0.5*max(1.0, np.linalg.norm(z))/nrm
        z = z + dz
    return z[:4], z[4], False


def monodromy(pr, x, T):
    M = np.zeros((4, 4))
    base = flow(pr, x, T)
    for i in range(4):
        h = 1e-7*max(1e-3, abs(x[i]))
        e = np.zeros(4); e[i] = h
        M[:, i] = (flow(pr, x+e, T) - flow(pr, x-e, T))/(2*h)
    return M, base


A2ROWS = []
for marg in (0.05, 0.10, 0.15, 0.20):
    P0 = margin_point(prb, PH, marg)
    pr = dict(prb, P=P0); co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; alpha = co['alpha']
    pvec = co['p']; qvec = co['q']; c1r = co['c1'].real
    rg = guard_root(alpha, c1r, c2r)
    rg3 = math.sqrt(alpha/c1r)
    x0 = st + 2*np.real(rg*qvec)
    xc, Tc, ok = find_cycle(pr, st, pvec, x0, 2*math.pi/w0)
    if not ok:
        out(f" {alpha:.3f}  | NEWTON FAILED  [{time.time()-T0:.0f}s]")
        continue
    M, _ = monodromy(pr, xc, Tc)
    mu = np.linalg.eigvals(M)
    mu = sorted(mu, key=lambda z: -abs(z))
    lu = math.log(abs(mu[0]))/Tc
    l_cub = 2*alpha
    l_5 = 2*alpha + 2*c2r*rg**4
    A2ROWS.append((alpha, rg, lu, l_cub, l_5, Tc, abs(mu[0]), abs(mu[1])))
    out(f" {alpha:.3f}  | {rg:.4e} | {lu:.8f}    | {l_cub:.8f} "
        f"{(l_cub-lu)/lu*100:+6.2f}% | {l_5:.8f} {(l_5-lu)/lu*100:+6.2f}% | "
        f"{Tc:.6f}  [{time.time()-T0:.0f}s]")
    out(f"         multipliers |mu| = {abs(mu[0]):.6f}, {abs(mu[1]):.6f} "
        f"(second must be ~1), rho_g cubic {rg3:.4e}")

# =====================================================================
# A1: the switch-on kick, measured as an asymptotic amplitude
# =====================================================================
out("")
out("=== A1: complex Z(0) measured by back-extrapolating the free part")
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
lam = co['lam']; pvec = co['p']; qvec = co['q']; c1r = co['c1'].real
A = jac(st, pr)
fV = (rhs(st, dict(pr, V=pr['V']+hs))
      - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
wp = 0.90*w0; Td = 2*math.pi/wp
I4 = np.eye(4)
Hp = np.linalg.solve(1j*wp*I4 - A, fV.astype(complex))
Hm = np.linalg.solve(-1j*wp*I4 - A, fV.astype(complex))
Gp = np.vdot(pvec, Hp); Gm = np.vdot(pvec, Hm)
J = abs(lam)*abs(np.vdot(pvec, fV))/abs(wp**2 + lam**2)
# second-order alpha-only response at the OPERATING point
Rop = solve_nf5(A, lam, qvec, pvec, fV, wp,
                make_tensors5(sp, f_, _x,
                              {P_: pr['P'], Q_: pr['Q'], V_: pr['V'],
                               Xg_: pr['Xg'], kp_: pr['kp'], ki_: pr['ki'],
                               kpv_: pr['kpv'], kiv_: pr['kiv'],
                               C_: pr['C']}, pr, st, V_),
                param=True)
Yop = Rop['Y']


def hvec(idx):
    return np.array([Yop[i].get(idx, 0) for i in range(4)])


h20 = hvec((0, 0, 2, 0)); h11 = hvec((0, 0, 1, 1)); h02 = hvec((0, 0, 0, 2))
m1010 = np.vdot(pvec, hvec((1, 0, 1, 0)))
m1001 = np.vdot(pvec, hvec((1, 0, 0, 1)))
m0110 = np.vdot(pvec, hvec((0, 1, 1, 0)))
m0101 = np.vdot(pvec, hvec((0, 1, 0, 1)))
out(f"  <p,H+> = {Gp:.5e}, <p,H-> = {Gm:.5e}, J = {J:.6e}")
out(f"  <p,h20>={np.vdot(pvec, h20):.4e} <p,h11>={np.vdot(pvec, h11):.4e} "
    f"<p,h02>={np.vdot(pvec, h02):.4e}")
out(f"  mixed: <p,h1010>={m1010:.4e} <p,h1001>={m1001:.4e} "
    f"<p,h0110>={m0110:.4e} <p,h0101>={m0101:.4e}")
rgO = guard_root(alpha, c1r, c2r)
eps_c_est = rgO/J
out(f"  rho_g = {rgO:.5e}, crude eps_c ~ {eps_c_est:.5e}")
out("")
out("  eps/eps_c | measured |Z0|   arg Z0  | linear pred      | "
    "quadratic pred")
ROWS = []
for frac in (0.20, 0.35, 0.50, 0.65):
    eps = frac*eps_c_est
    a = 0.5*eps

    def f(t, x):
        return rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
    NP = 12
    s = solve_ivp(f, (0, NP*Td), st.copy(), method='DOP853',
                  rtol=1e-13, atol=1e-16, dense_output=True)
    ts = np.linspace(0.8*Td, NP*Td, 4000)
    ys = s.sol(ts)
    zt = np.array([np.vdot(pvec, ys[:, i] - st) for i in range(len(ts))])
    al = np.exp(1j*wp*ts)*a
    zt = zt - (al*Gp + np.conj(al)*Gm)
    zt = zt - (np.vdot(pvec, h20)*al**2
               + np.vdot(pvec, h11)*np.abs(al)**2
               + np.vdot(pvec, h02)*np.conj(al)**2)
    zf = zt*np.exp(-lam*ts)          # should be constant = Z(0)
    n = len(ts)
    seg = slice(int(0.35*n), int(0.85*n))
    Z0 = complex(np.mean(zf[seg]))
    spread = float(np.std(np.abs(zf[seg]))/abs(Z0))
    zl = -(a*Gp + np.conj(a)*Gm)
    zq = zl - (np.vdot(pvec, h20)*a**2 + np.vdot(pvec, h11)*abs(a)**2
               + np.vdot(pvec, h02)*np.conj(a)**2) \
        - (zl*a*m1010 + zl*np.conj(a)*m1001
           + np.conj(zl)*a*m0110 + np.conj(zl)*np.conj(a)*m0101)
    ROWS.append((eps, Z0, zl, zq))
    out(f"   {frac:.2f}      | {abs(Z0):.6e} {np.angle(Z0):+.4f} | "
        f"{abs(zl):.6e} {(abs(zl)-abs(Z0))/abs(Z0)*100:+6.2f}% | "
        f"{abs(zq):.6e} {(abs(zq)-abs(Z0))/abs(Z0)*100:+6.2f}%   "
        f"(plateau spread {spread:.1e})  [{time.time()-T0:.0f}s]")
out("")
if len(ROWS) >= 3:
    ee = np.array([r[0] for r in ROWS])
    zm = np.array([abs(r[1]) for r in ROWS])
    zl = np.array([abs(r[2]) for r in ROWS])
    zq = np.array([abs(r[3]) for r in ROWS])
    Am = np.vstack([ee, ee**2]).T
    cm = np.linalg.lstsq(Am, zm, rcond=None)[0]
    cq = np.linalg.lstsq(Am, zq, rcond=None)[0]
    out(f"  |Z0| = K1 eps + K2 eps^2 :  measured K1={cm[0]:.6e} "
        f"K2={cm[1]:+.6e}")
    out(f"                              quadratic pred K1={cq[0]:.6e} "
        f"K2={cq[1]:+.6e}")
    out(f"  linear-only J = {J:.6e}  (K1 must match this to the fit noise)")
    out(f"  K2 ratio pred/meas = {cq[1]/cm[1]:+.4f}  "
        f"(1 => the <p,Phi>=0 inversion is the right projection)")
out(f"DONE wall={time.time()-T0:.0f}s")
