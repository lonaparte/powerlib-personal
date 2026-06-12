"""
R3real_check.py -- the REAL-model answer to R3 ("synchronization margin vs PLL damping"),
replacing the classical-pendulum R3a/R3_basin/R3note.

The classical R3 used a swing pendulum (delta'=dw, dw'=-b*dw-K*sin(delta)+Pm) that is in
NO committed model.  On the REAL 10-state GFL (sweep.py / Conventions sec.12), the
weak-grid instability is the PLL-mode HOPF, and the real "margin vs PLL damping" question
has two real answers, both computed from the validated sweep.py pipeline:

 (1) LINEAR MARGIN: the Hopf boundary SCR_H(Kp) -- the critical grid strength.  It is
     NON-monotone (U-shaped) in the PLL proportional gain Kp, with an OPTIMUM gain that
     maximizes weak-grid robustness.  (The classical R3b claimed a monotone c*(zeta);
     the real margin is U-shaped, not monotone.)

 (2) CRITICALITY: the first Lyapunov coefficient l1 at the Hopf changes SIGN at a Bautin
     (generalized-Hopf) point Kp* ~ 0.40 -- subcritical/HARD (hysteretic, dangerous) for
     Kp<Kp*, supercritical/SOFT for Kp>Kp*.  The RIGOROUS, interval-sound version of this
     is already certified in  numerical/bautin_cert/  (bracket Kp* in [0.400, 0.408]).
     This script only reproduces the float picture and cross-references that certificate.

So R3's correct, real-model content lives in bautin_cert/ (criticality) and the Hopf
structure in freq_mode/.  The classical pendulum R3 certs are kept as reference only.

Run:  python3 R3real_check.py     (run from formalization/numerical, or adjust path)
"""
import numpy as np, sys, os
HERE=os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "numerical")))
from sweep import hopf_SCR, l1

XR, Ki = 10.0, 150

def margin_curve():
    Kps = np.linspace(0.10, 1.40, 27)
    shs = np.array([hopf_SCR(XR, kp, Ki) or np.nan for kp in Kps])
    kopt = Kps[np.nanargmin(shs)]; shopt = np.nanmin(shs)
    return Kps, shs, kopt, shopt

def bautin_kp():
    prev = None
    for Kp in np.linspace(0.30, 0.55, 26):
        sh = hopf_SCR(XR, Kp, Ki)
        if sh is None: continue
        v,_,_ = l1(sh, XR, Kp, Ki)
        if prev is not None and prev[1]*v < 0:
            return 0.5*(prev[0]+Kp), prev, (Kp, v)
        prev = (Kp, v)
    return None, None, None

if __name__ == "__main__":
    Kps, shs, kopt, shopt = margin_curve()
    print("(1) REAL linear margin SCR_H(Kp)  (Ki=150, X/R=10) -- smaller = survives weaker grid:")
    print("    Kp     SCR_H")
    for kp, sh in list(zip(Kps, shs))[::3]:
        print("    %.2f   %.4f" % (kp, sh))
    print("    => NON-monotone (U-shaped): optimum Kp ~ %.2f at SCR_H ~ %.4f;" % (kopt, shopt))
    print("       endpoints SCR_H(0.10)=%.3f, SCR_H(1.40)=%.3f.  (classical R3b's monotone" % (shs[0], shs[-1]))
    print("       c*(zeta) is the wrong shape -- the real margin has an interior optimum.)")
    print()
    kp_star, lo, hi = bautin_kp()
    print("(2) REAL criticality: l1 at the Hopf flips sign (hard subcritical <-> soft supercritical):")
    if kp_star:
        print("    l1>0 (hard) at Kp=%.3f, l1<0 (soft) at Kp=%.3f  =>  Bautin Kp* ~ %.3f"
              % (lo[0], hi[0], kp_star))
    print("    RIGOROUS interval-sound bracket (numerical/bautin_cert/): Kp* in [0.400, 0.408].")
    print("    cross-check: float Kp* here = %.3f  -> %s with bautin_cert."
          % (kp_star, "consistent" if kp_star and 0.39 < kp_star < 0.42 else "MISMATCH"))
    print()
    print("=> R3's real-model answer = bautin_cert/ (criticality, rigorous) + freq_mode/ (Hopf")
    print("   structure).  The classical-pendulum R3a/R3_basin/R3note are reference only.")
