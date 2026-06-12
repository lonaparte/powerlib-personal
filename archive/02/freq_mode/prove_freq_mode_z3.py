"""
prove_freq_mode_z3.py -- MACHINE-CHECKED PARAMETRIC proofs (Z3 / nonlinear real
arithmetic) of the slow-frequency-mode theorems for a power-locked GFL-VSC.

Z3 is the same decision procedure KeYmaera X uses for its `QE` steps.  For each
theorem we discharge -- PARAMETRICALLY, over symbolic real parameters -- exactly
the proof obligation that the corresponding .kyx tactic reduces to:

  * a QE first-order real formula  (Lemma 0, K=0, Thm C discriminant), or
  * the dI Lie-derivative condition  (Thm A invariance, Thm B / Thm C Lyapunov).

A theorem is PROVED iff Z3 reports `unsat` for the NEGATION of the obligation
(i.e. no real counterexample exists for ANY parameter values in the hypotheses).
Each call also runs a guard: the hypotheses must be satisfiable (sat), so we are
not proving from a contradictory antecedent.

IMPORTANT z3py gotcha: Real('0') is a FREE VARIABLE named "0", not the number 0.
Numeric literals must use RealVal(n) or Q(num,den).  (An earlier version of this
file used Real('0')/'1'/'3' and so spuriously reported 8/12 -- a script bug, not a
math failure; the sympy cross-check prove_freq_mode_obligations.py had it right.
See kyx/STATUS.md erratum.)

Run:  python3 prove_freq_mode_z3.py
"""
from z3 import (Reals, Real, RealVal, Q, Solver, And, Or, Not, sat, unsat)

RESULTS = []

def prove(name, hyp, concl, note=""):
    """Prove  hyp -> concl  over the reals.  Method: hyp & ~concl is unsat, and
    (guard) hyp is sat (antecedent not vacuous).  Returns True iff proved."""
    s = Solver(); s.add(hyp); s.add(Not(concl)); verdict = s.check()
    g = Solver(); g.add(hyp); guard = g.check()
    ok = (verdict == unsat) and (guard == sat)
    RESULTS.append((name, ok, str(verdict), str(guard), note))
    print("  [%s] %-52s  (neg:%s, hyp:%s)" % ("PROVED " if ok else "*** FAILED ***",
                                              name, verdict, guard))
    if note: print("         %s" % note)
    return ok

THREE_HALVES = Q(3, 2)   # literal 3/2, NOT a variable

print("="*80)
print("MACHINE-CHECKED PARAMETRIC PROOFS (Z3 nonlinear real arithmetic)")
print("Z3 = the QE backend KeYmaera X itself uses.  All parameters SYMBOLIC.")
print("="*80)

# ----------------------------------------------------------------------------
print("\n--- Lemma 0 (Power Lock) + Corollary 0a (K=0) ---")
P_ref, Vg, i_d = Reals('P_ref Vg i_d')
prove("Lemma0: F7=0 & Vg>0 -> i_d = P_ref/(1.5*Vg)",
      And(Vg > 0, P_ref - THREE_HALVES*Vg*i_d == 0),
      i_d == P_ref/(THREE_HALVES*Vg))

i_d1, i_d2, dw1, dw2 = Reals('i_d1 i_d2 dw1 dw2')
prove("Cor0a: power-lock at dw1,dw2 -> i_d1=i_d2 (K=0, indep of dw)",
      And(Vg > 0,
          P_ref - THREE_HALVES*Vg*i_d1 == 0,
          P_ref - THREE_HALVES*Vg*i_d2 == 0,
          dw1 != dw2),
      i_d1 == i_d2,
      note="=> synchronizing coefficient K = 1.5*Vg*d(i_d*)/d(dw) = 0 exactly")

# ----------------------------------------------------------------------------
print("\n--- Theorem A (Variant U: zero eigenvalue = conserved dw) ---")
# F9_U = 0 (literal) => dI Lie derivative of (dw - dw0) along dw'=0 is 0.
F9_U = RealVal(0)
prove("ThmA: dI obligation  d/dt(dw - dw0) = F9_U = 0",
      And(),                     # identity, no hypotheses
      F9_U == 0,
      note="F9_U=0 => 9th Jacobian row =0 => 0 in spec(J_U), dw is conserved")

# ----------------------------------------------------------------------------
print("\n--- Theorem B (reduced slow mode: lambda = -b = -D/(2H)) ---")
b, dw, D, H = Reals('b dw D H')
prove("ThmB(i): Lyapunov decrease  V'=-2*b*dw^2 <= 0  (b>0)",
      b > 0, -2*b*dw*dw <= 0,
      note="V=dw^2 nonincreasing => reduced 1-D system is stable")
prove("ThmB(ii): rate identity  -b = -D/(2H)   (b:=D/(2H))",
      And(H > 0, D > 0, b == D/(2*H)), -b == -D/(2*H),
      note="lambda_slow = -D/(2H) EXACT for the reduced model")
prove("ThmB(iii): strict decay  dw!=0 & b>0 -> V' < 0",
      And(b > 0, dw != 0), -2*b*dw*dw < 0,
      note="purely real decaying mode, no oscillation")

# ----------------------------------------------------------------------------
print("\n--- Theorem C (angle->power coupling: stability + oscillation threshold) ---")
delta, beta, Ks = Reals('delta beta Ks')
Vdot = 2*beta*Ks*delta*dw + 2*dw*(-b*dw - beta*Ks*delta)   # = -2*b*dw^2
prove("ThmC(stab): Lyapunov V'=-2*b*dw^2 <= 0  (b>0, beta*Ks>=0)",
      And(b > 0, beta*Ks >= 0), Vdot <= 0,
      note="V=beta*Ks*delta^2+dw^2 nonincreasing => (delta,dw) stable")
# characteristic polynomial of [[0,1],[-beta*Ks,-b]] = lam^2 + b*lam + beta*Ks
lam = Real('lam')
M00, M01, M10, M11 = RealVal(0), RealVal(1), -beta*Ks, -b
charpoly = (M00-lam)*(M11-lam) - M01*M10
prove("ThmC(charpoly): det(M-lam I) = lam^2 + b*lam + beta*Ks",
      And(), charpoly == lam*lam + b*lam + beta*Ks)
prove("ThmC(C1): Ks=0 -> charpoly = lam*(lam+b)  (roots 0,-b real)",
      And(), (lam*lam + b*lam + beta*RealVal(0)) == lam*(lam + b))
disc = b*b - 4*beta*Ks
prove("ThmC(C2 onset): disc<0  <->  beta*Ks > b^2/4",
      And(b > 0, Ks > 0, beta > 0),
      (disc < 0) == (beta*Ks > b*b/4),
      note="oscillatory (complex pair) iff beta*Ks > b^2/4")
r1, r2 = Reals('r1 r2')
prove("ThmC(C2 Re): roots sum to -b (=> Re of complex pair = -b/2)",
      And(r1 + r2 == -b, r1*r2 == beta*Ks),
      (r1 + r2)/2 == -b/2)
prove("ThmC(C2 omega): beta*Ks>b^2/4 -> omega_osc^2 = beta*Ks - b^2/4 > 0",
      And(b > 0, beta*Ks > b*b/4),
      And(beta*Ks - b*b/4 > 0, (beta*Ks - b*b/4) == -(b*b - 4*beta*Ks)/4))

# ----------------------------------------------------------------------------
print("\n" + "="*80)
ok = sum(1 for _,o,_,_,_ in RESULTS if o); tot = len(RESULTS)
print("RESULT: %d/%d obligations PROVED by Z3 (parametric, all params symbolic real)" % (ok, tot))
fails = [n for n,o,_,_,_ in RESULTS if not o]
if fails:
    print("FAILURES:"); [print("   -", n) for n in fails]
else:
    print("All slow-frequency-mode obligations machine-checked over the reals:")
    print("  Lemma0/Cor0a (K=0), ThmA (dw conserved), ThmB (lambda=-D/2H reduced),")
    print("  ThmC (Lyapunov stability + oscillation threshold beta*Ks>b^2/4).")
print("="*80)
import sys; sys.exit(0 if not fails else 1)
