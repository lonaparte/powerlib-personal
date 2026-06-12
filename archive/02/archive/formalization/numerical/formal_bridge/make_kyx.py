#!/usr/bin/env python3
"""
Generate conjecture_gfl_strong_grid_lyapunov.kyx from the EXACT rational matrices
produced by verify_strong_grid_lyapunov.py (via /tmp/strong_grid_matrices.json).

P (=P0) solves  A^T P + P A = -I  EXACTLY over the rationals (A = Atil_Q
rational), so along x' = A x:

    Vdot = x^T (A^T P + P A) x = -(x1^2 + ... + x10^2)  <= 0.

This is the cleanest dI certificate: the Lie derivative is exactly minus the
squared norm.  (We keep P as exact RATIONALS rather than clearing denominators:
the entry numerators/denominators are already ~168 digits -- intrinsic to the
exact rational Lyapunov solve -- and clearing the 55 largely-coprime denominators
to integers would push them to ~340 digits.)  We re-verify P > 0 (exact LDL^T) and
the exact Lyapunov identity here, independently of the producing script, before
writing the file.
"""
import json, sys
import sympy as sp
import numpy as np
from fractions import Fraction
sys.path.insert(0, "/home/user/metapower-personal/.claude/worktrees/agent-ab4ff779cb81b3c9f/formalization/numerical/formal_bridge")
import verify_strong_grid_lyapunov as VV

n = 10
_here = "/home/user/metapower-personal/.claude/worktrees/agent-ab4ff779cb81b3c9f/formalization/numerical/formal_bridge"
import os
# Prefer the checked-in snapshot; fall back to the /tmp one freshly emitted by verify_*.
_jpath = os.path.join(_here, "strong_grid_matrices.json")
if not os.path.exists(_jpath):
    _jpath = "/tmp/strong_grid_matrices.json"
J = json.load(open(_jpath))
A = sp.Matrix(n, n, lambda i, j: sp.Rational(J["A"][i][j]))
Pint = sp.Matrix(n, n, lambda i, j: sp.Rational(J["P"][i][j]))   # exact rational P
tau = J["tau"]; maxden = J["maxden"]
SCR = J["scr"]; XR = J["xr"]; KP = J["kp"]; KI = J["ki"]
m = 1   # certificate normalized so that A^T P + P A = -I exactly

# recompute the spectral numbers that go into the comment, so they can never drift:
A_phys = VV.Amat(SCR, XR, KP, KI)
maxre_phys = float(np.max(np.linalg.eigvals(A_phys).real))     # physical Hurwitz margin
A_Q_float = np.array(A.evalf(), dtype=float)
maxre_ratbal = float(np.max(np.linalg.eigvals(A_Q_float).real))  # rationalized balanced

assert Pint == Pint.T, "P not symmetric"

# exact Lyapunov identity:  A^T P + P A == -I
lhs = sp.simplify(A.T * Pint + Pint * A)
assert lhs == -m * sp.eye(n), "exact Lyapunov identity FAILED"

# exact PD of P via rational LDL^T
def ldlt_ok(S):
    F = [[Fraction(int(sp.Rational(S[i, j]).p), int(sp.Rational(S[i, j]).q)) for j in range(n)] for i in range(n)]
    L = [[Fraction(0)] * n for _ in range(n)]; D = [Fraction(0)] * n
    for j in range(n):
        s = F[j][j] - sum(L[j][k] * L[j][k] * D[k] for k in range(j)); D[j] = s
        L[j][j] = Fraction(1)
        if s == 0:
            return False, D
        for i in range(j + 1, n):
            L[i][j] = (F[i][j] - sum(L[i][k] * L[j][k] * D[k] for k in range(j))) / s
    return all(d > 0 for d in D), D
okP, Dp = ldlt_ok(Pint)
assert okP, "Pint not positive definite"

var = ["x%d" % (i + 1) for i in range(n)]

# ODE rhs strings
ode_lines = []
for i in range(n):
    terms = []
    for j in range(n):
        a = A[i, j]
        if a == 0:
            continue
        terms.append("(%s)*%s" % (str(a), var[j]))
    rhs = " + ".join(terms) if terms else "0"
    ode_lines.append("    %s' = %s" % (var[i], rhs))
ode_block = ",\n".join(ode_lines)

# V = x^T Pint x  (integer coeffs)
vterms = []
for i in range(n):
    for j in range(i, n):
        p = Pint[i, j]
        if p == 0:
            continue
        coeff = p if i == j else 2 * p
        vterms.append("(%s)*%s*%s" % (str(coeff), var[i], var[j]))
V = " + ".join(vterms)

# squared norm for the strict-positivity premise and Vdot
sumsq = " + ".join("%s^2" % v for v in var)

decls = "  " + "\n  ".join("Real %s;" % v for v in var)

minpiv = float(min(Dp))
Pnum = max(max(abs(int(sp.Rational(Pint[i, j]).p)), int(sp.Rational(Pint[i, j]).q))
           for i in range(n) for j in range(n))

header = f"""ArchiveEntry "Conjecture: GFL strong-grid local Lyapunov (10-state, quadratic V)"

/*
 * CONJECTURE (NOT machine-checked: KeYmaera X is not installed in this
 * environment -- only a JDK is present, no keymaerax jar/CLI).  This file
 * therefore has a Problem block but NO Tactic, per the project convention
 * (filename prefixed conjecture_).
 *
 * CLAIM (local / small-signal stability of the GFL equilibrium, strong grid)
 * ------------------------------------------------------------------------
 * For the 10-state grid-following converter of Conventions.md section 12 at the
 * STRONG-grid operating point
 *      SCR = {SCR}, X/R = {XR}, Kp = {KP}, Ki = {KI},
 * the linearization A = Df(x*) is Hurwitz (numerically verified:
 * max Re eig(A) = {maxre_phys:.4e}; the weak-grid Hopf is at SCR ~ 0.9051).
 *
 * We certify stability with a QUADRATIC Lyapunov function V = x^T P x for the
 * linear flow x' = A x, where (to obtain a manageable RATIONAL certificate) A
 * is taken in BALANCED, TIME-RESCALED coordinates:
 *      A := (1/tau) * Dinv * Df(x*) * D,   tau = {int(tau)},
 * D = diagonal balancing (a similarity transform: preserves the spectrum, hence
 * Hurwitz-ness and stability -- it is just a change of state basis), and the
 * uniform time rescale t -> t/tau preserves the sign of every eigenvalue's real
 * part and the sign of Vdot.  A is then rationalized (denominators <= {maxden});
 * the rationalized A (used as the ODE coefficient matrix below) is still Hurwitz
 * (max Re eig = {maxre_ratbal:.4e}) and lies inside the Hurwitz cone of the true
 * balanced linearization.  See
 * numerical/formal_bridge/verify_strong_grid_lyapunov.py and BRIDGE.md.
 *
 * The matrix P below solves  A^T P + P A = -I  EXACTLY over the rationals.
 * Hence along x' = A x the Lie derivative is
 *      Vdot = x^T (A^T P + P A) x = -({sumsq})  <=  0,
 * i.e. V is non-increasing.  P is positive definite (verified EXACTLY by
 * rational LDL^T, min pivot {minpiv:.3e}; entries are rationals with
 * numerator/denominator ~ 1e{len(str(Pnum))-1}, large because the balanced GFL
 * spectrum spans ~7 orders of magnitude -- see BRIDGE.md).
 *
 * NUMERICAL GROUNDING (all in verify_strong_grid_lyapunov.py):
 *   - A (physical) Hurwitz at SCR=2.0; unstable past SCR_H~0.9051  [3+ combos]
 *   - rationalized balanced A Hurwitz                              [float]
 *   - A^T P + P A = -I                                             [exact over Q]
 *   - P > 0                                                        [exact LDL^T]
 *
 * INTERPRETATION / SCOPE.  This is LOCAL (small-signal) stability of the GFL
 * equilibrium in the strong-grid regime, expressed on the linear system in an
 * exact change of variables (balancing + time scale).  It is the linear/Lyapunov
 * companion to the nonlinear weak-grid subcriticality result (l1 > 0) discussed
 * in BRIDGE.md; it does NOT itself address the D2<0 / l1>0 nonlinear question.
 *
 * The Problem encodes:
 *   (positivity)  away from the origin, V > 0   [stated as: sum xi^2 > 0 -> V > 0]
 *   (invariance)  [{{x' = A x}}] V non-increasing, witnessed against the initial
 *                 value v0 (v0' = 0): V <= v0 is maintained.
 */

ProgramVariables
{decls}
  Real v0;
End.

Problem
  (   ( {sumsq} > 0 -> {V} > 0 )
   &  ( v0 = {V}
        ->
        [{{
{ode_block},
    v0' = 0
        }}]
        {V} <= v0 )
  )
End.

End.
"""

out_path = "/home/user/metapower-personal/.claude/worktrees/agent-ab4ff779cb81b3c9f/formalization/numerical/formal_bridge/conjecture_gfl_strong_grid_lyapunov.kyx"
open(out_path, "w").write(header)

# small machine-readable report
rep = {
    "kyx": out_path,
    "n": n, "tau": tau, "maxden": maxden,
    "P_max_entry_digits": len(str(Pnum)),
    "P_min_pivot": minpiv,
    "lyapunov_identity_AtP_PA_eq_minus_I": bool(lhs == -m * sp.eye(n)),
    "P_positive_definite_exact": bool(okP),
}
json.dump(rep, open("/tmp/make_kyx_report.json", "w"), indent=2)
print("WROTE", out_path)
print("minpiv =", minpiv, " Pmax entry digits =", len(str(Pnum)))
print("exact Lyapunov A^T P + P A = -I :", lhs == -m * sp.eye(n))
print("P PD exact :", okP)
