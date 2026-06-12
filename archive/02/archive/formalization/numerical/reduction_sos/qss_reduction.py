"""
qss_reduction.py -- CORRECT singular-perturbation (quasi-steady-state) reduction
of the 10-state GFL model (Conventions sec.12) to the low-order core that carries
the weak-grid PLL Hopf mode.

WHICH STATES TO KEEP -- decided by the Hopf mode shape, not by guessing.
At the nominal Hopf (X/R=10, Kp=0.30, Ki=150) the critical right eigenvector q
(the oscillation shape) is dominated by the LC capacitor voltages:
    |q|^2 participation:  v_cq 0.767, v_cd 0.217  (cum 0.985),  rest < 0.01
and the critical LEFT eigenvector p (where the cubic nonlinearity must project)
is dominated by the PLL/integrator states:
    |p|^2 participation:  th 0.503, xdc 0.182, eta 0.175, xqc 0.140.
So the Hopf lives on  {v_cd, v_cq}  (observability) x {th, eta, ...} (excitation).
A reduction MUST keep v_cd, v_cq, eta, th.  (An earlier version of this file kept
i_gd,i_gq,eta,th and collapsed v_cd,v_cq -- physically wrong, since it removes the
states that carry the mode, and numerically singular: the QSS solve for v_cq has
(i_gd-idr) -> 0 and wpll in the denominator, i.e. 0/0 at equilibrium.)

TIME-SCALE PARTITION (kept = slow core, collapsed = fast):
  KEEP (slow core, 4 states): v_cd, v_cq  (LC voltage, carry the ~40 Hz mode),
                               eta, th     (PLL integrator + phase).
  COLLAPSE (fast, QSS):        i_d, i_q    (current loop, BW ~Kpi/Lf~1260 rad/s),
                               xdc, xqc    (current-PI integrators),
                               i_gd, i_gq  (grid inductor).
  Fast block slowest pole ~ -38 rad/s vs omega_Hopf ~ 251 rad/s: separation ~6.6x,
  MODEST.  Hence QSS shifts the Hopf SCR (full ~0.905 -> reduced ~0.73) and f_osc
  (40 -> 36 Hz); the SIGN of l1 is preserved (validated 5/5 in run_all.py).

QSS ALGEBRA (all exact, closed form):
  xdc'=0, xqc'=0  =>  i_d = idr,  i_q = iqr   (exact)
  i_gd'=0, i_gq'=0 solved for (i_gd, i_gq): LINEAR in (i_gd,i_gq) -> closed form
    (see build_reduced_field; denominator = (wpll*Lg)^2 + Rg^2 > 0, NON-singular).
  Remaining slow ODEs:
    v_cd' = (idr - i_gd)/Cf + wpll*v_cq
    v_cq' = (iqr - i_gq)/Cf - wpll*v_cd
    eta'  = v_cq
    th'   = Kp*v_cq + Ki*eta
  with wpll = wn + Kp*v_cq + Ki*eta and i_gd,i_gq at QSS.
  This field is RATIONAL in (wn,Vg,Rg,Lg,Kp,Ki) and depends on th via cos/sin.
"""
import numpy as np
import sympy as sp

from reduce_model import (STATES, F, NAMES, wn, Vg, Rg, Lg, vcd as VCD_SYM, Kp, Ki,
                          Cf, Lf, Rf, Kpi, Kii, Kad, idr, iqr, grid_params,
                          A_full, l1_full_projection, hopf_SCR, crit_pair)

i_d, i_q, v_cd, v_cq, i_gd, i_gq, xdc, xqc, eta, th = STATES

KEEP_IDX = [2, 3, 8, 9]                 # v_cd, v_cq, eta, th
COLL_IDX = [0, 1, 4, 5, 6, 7]           # i_d, i_q, i_gd, i_gq, xdc, xqc
KEEP = [STATES[i] for i in KEEP_IDX]


def build_reduced_field():
    """Return (g, keep_states, (cth,sth), (igd_q,igq_q)) -- the symbolic 4-state
    reduced field g(v_cd,v_cq,eta,th) with cos(th),sin(th) written explicitly.
    Rational in the grid/control parameters. Grid current eliminated by exact QSS."""
    cth, sth = sp.cos(th), sp.sin(th)
    wpll = wn + Kp * v_cq + Ki * eta
    # i_gd'=0, i_gq'=0 (linear in i_gd,i_gq):
    igd_dot = (v_cd - Vg * cth - Rg * i_gd + wpll * Lg * i_gq) / Lg
    igq_dot = (v_cq + Vg * sth - Rg * i_gq - wpll * Lg * i_gd) / Lg
    sol = sp.solve([igd_dot, igq_dot], [i_gd, i_gq], dict=True)[0]
    igd_q, igq_q = sol[i_gd], sol[i_gq]
    g = sp.Matrix([
        (idr - i_gd) / Cf + wpll * v_cq,
        (iqr - i_gq) / Cf - wpll * v_cd,
        v_cq,
        Kp * v_cq + Ki * eta,
    ]).subs({i_gd: igd_q, i_gq: igq_q})
    return g, KEEP, (cth, sth), (igd_q, igq_q)


def reduced_equilibrium(SCR, XR):
    """Numeric equilibrium of the reduced 4 states [v_cd, v_cq, eta, th] from
    Conventions sec.12.5 (shared with the full model by construction)."""
    wnv, Vgv, Rgv, Lgv, vcdv = grid_params(SCR, XR)
    Cfv = 1e-4
    al = 1 - wnv**2 * Lgv * Cfv
    K1 = Rgv * 80
    K2 = wnv * Lgv * 80
    be = Rgv * wnv * Cfv
    ceq = (al * vcdv - K1) / Vgv
    seq = (K2 - be * vcdv) / Vgv
    return np.array([vcdv, 0.0, 0.0, np.arctan2(seq, ceq)])


# ----------------------------------------------------------------------------
# Numeric reduced model used for the cross-validation table.  Built via the
# *nonlinear* QSS implicit-function solve on the FULL field (so the B,C tensors
# transform correctly), which is the safe, convention-faithful route and avoids
# hand-truncating the QSS.  Its Jacobian is verified equal to the symbolic
# build_reduced_field Jacobian in run_all.py STEP 4.
# ----------------------------------------------------------------------------
_Pf = (wn, Vg, Rg, Lg, Kp, Ki)
_f_lam = sp.lambdify((*_Pf, *STATES), list(F), 'numpy')


def _full_f(x, pp5, Kpv, Kiv):
    wnv, Vgv, Rgv, Lgv, vcdv = pp5
    return np.array(_f_lam(wnv, Vgv, Rgv, Lgv, Kpv, Kiv, *x), float)


def _full_equilibrium(SCR, XR):
    wnv, Vgv, Rgv, Lgv, vcdv = grid_params(SCR, XR)
    Cfv = 1e-4
    igq = 0.0 - wnv * Cfv * vcdv
    al = 1 - wnv**2 * Lgv * Cfv
    K1 = Rgv * 80
    K2 = wnv * Lgv * 80
    be = Rgv * wnv * Cfv
    ceq = (al * vcdv - K1) / Vgv
    seq = (K2 - be * vcdv) / Vgv
    xe = np.array([80.0, 0.0, vcdv, 0.0, 80.0, igq, 0.1 * 80 / 126,
                   (2 * (0.0 - igq)) / 126, 0.0, np.arctan2(seq, ceq)])
    return xe, (wnv, Vgv, Rgv, Lgv, vcdv)


def reduced_field_factory(SCR, XR, Kpv, Kiv, keep=KEEP_IDX):
    """Return g(xk) : R^|keep| -> R^|keep|, the nonlinear-QSS reduced field, plus
    the reduced equilibrium xke.  Fast states solved by Newton on f[coll]=0."""
    xe, pp = _full_equilibrium(SCR, XR)
    coll = [i for i in range(10) if i not in keep]

    def solve_fast(xk):
        x = xe.copy()
        x[keep] = xk
        for _ in range(80):
            r = _full_f(x, pp, Kpv, Kiv)[coll]
            if np.max(np.abs(r)) < 1e-12:
                break
            J = np.zeros((len(coll), len(coll)))
            h = 1e-6
            for a, ca in enumerate(coll):
                xp = x.copy(); xp[ca] += h
                J[:, a] = (_full_f(xp, pp, Kpv, Kiv)[coll] - r) / h
            x[coll] += np.linalg.solve(J, -r)
        return x

    def g(xk):
        return _full_f(solve_fast(xk), pp, Kpv, Kiv)[keep]

    return g, np.array([xe[i] for i in keep])


if __name__ == '__main__':
    print("Building CORRECT symbolic reduced 4-state field {v_cd,v_cq,eta,th}...")
    g, keep, (cth, sth), (igd_q, igq_q) = build_reduced_field()
    print("keep states:", keep)
    print()
    print("grid-current QSS (closed form, denominator (wpll*Lg)^2+Rg^2 > 0):")
    print("  i_gd_qss =", sp.simplify(igd_q))
    print()
    for nm, e in zip(['v_cd', 'v_cq', 'eta', 'th'], g):
        s = str(e)
        print("  d/dt %-4s = %s" % (nm, s[:240] + (' ...' if len(s) > 240 else '')))
    print()
    glam = sp.lambdify((wn, Vg, Rg, Lg, Kp, Ki, v_cd, v_cq, eta, th), list(g), 'numpy')
    XR = 10.0
    sh = hopf_SCR(XR, 0.30, 150)
    xe = reduced_equilibrium(sh, XR)
    wnv, Vgv, Rgv, Lgv, vcdv = grid_params(sh, XR)
    ge = np.array(glam(wnv, Vgv, Rgv, Lgv, 0.30, 150, *xe), float)
    print("symbolic reduced field at full-model equilibrium (residual, ~0):", ge)
