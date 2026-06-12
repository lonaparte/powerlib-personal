"""
R2R3_model_audit.py -- audits whether the R2/R3 certificates' model objects match the
committed GFL model (sweep.py / Conventions sec.12), applying the same scrutiny that
retracted R1.  CONCLUSION (printed below): R2's variable M is traceable to the real
model, but R2's fold |M|=Vg and R3's swing core are NOT the real model -- they are the
classical single-axis pendulum / synchronous-machine model.

Run:  python3 R2R3_model_audit.py
"""
import numpy as np, sys, os
HERE=os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "archive", "formalization", "numerical")))
from sweep import pv

idr, iqr, Cf = 80.0, 0.0, 1e-4

print("="*74)
print("R2 audit: is the fold |M|=Vg the real model's loss-of-equilibrium condition?")
print("="*74)
print("Real sweep.py (sec.12) equilibrium: vcd solves ceq^2+seq^2=1 with")
print("  ceq=(al*vcd-K1)/Vg, seq=(K2-be*vcd)/Vg,")
print("  K1=Rg*idr-wn*Lg*iqr, K2=Rg*iqr+wn*Lg*idr (= R2's M), al=1-wn^2*Lg*Cf, be=Rg*wn*Cf")
print()
print("  SCR    Vg      M(=K2)   Cterm(d-axis)   M/Vg   real-fold quantity")
print("  ----   -----   ------   -------------   ----   sqrt(M^2+Cterm^2)/Vg")
for SCR in [2.0, 1.0, 0.905, 0.7, 0.5]:
    wn,Vg,Rg,Lg,vcd = pv(SCR,10)
    M     = Rg*iqr + wn*Lg*idr            # = K2, the R2 fold variable (traceable, real)
    Cterm = vcd - Rg*idr + wn*Lg*iqr      # d-axis term R2 dropped
    print("  %.3f  %.1f  %6.1f   %10.1f    %.3f   %.3f"
          % (SCR, Vg, M, Cterm, M/Vg, np.sqrt(M**2+Cterm**2)/Vg))
print()
print("=> M IS traceable (it equals K2 in the real equilibrium). BUT Cterm (d-axis) ~300,")
print("   larger than M -- NOT negligible. So |M|=Vg is the q-axis-only / classical-pendulum")
print("   fold, NOT the real sec.12 fold (which is the vcd-quadratic discriminant a1^2-4a2a0<0).")
print("   R2 (classical |M|=Vg) scope = classical pendulum / Wu boundary, not the repo GFL.")
print()
print("   *** CORRECTED: the real-model fold has been redone in kyx/R2real_fold.kyx (the")
print("   vcd-quadratic saddle-node disc=0, real coefficients) and cross-validated in")
print("   numerical/R2real_validate.py.  Real fold SCR*~0.370, deeper than PLL Hopf ~0.905.")

print()
print("="*74)
print("R3 audit: is the swing core in any committed model?")
print("="*74)
print("R3 core:  delta' = dw,  dw' = -b*dw - K*sin(delta) + Pm   (b=D/2H)")
print(" - sec.12 / sweep.py: stiff-bus current-controlled GFL. NO swing eq, NO H/D inertia,")
print("   NO sin(delta) synchronizing torque, NO angle state delta.  Not here.")
print(" - sec.13 / freq_mode: has swing F9_S=kappa*e_P - b*dw (b=D/2H), but NO sin(delta) and")
print("   NO angle state; sec.13.7 Thm C augments a LINEAR -beta*Ks*delta, not -K*sin(delta).")
print("=> R3 swing core = classical synchronous-machine pendulum (textbook), same family as R2.")
print("   Scope = classical pendulum, not the repo GFL (sec.12) nor freq_mode (sec.13).")
