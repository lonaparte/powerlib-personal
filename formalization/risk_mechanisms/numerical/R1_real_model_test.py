"""
R1_real_model_test.py -- tests the R1 premise on the REAL model (not a fabricated A_e).

R1 claimed a weak-grid ELECTRICAL mode crosses the imaginary axis, so one could study
the PLL-frozen electrical block A_e alone.  We extract A_e PROPERLY from the committed
sweep.py field (the real LC-filter + active-damping 10-state GFL, Conventions sec.12):
the full 10x10 Jacobian Afun(.) at the equilibrium, rows/cols 0..7 = electrical block
(states i_d,i_q,v_cd,v_cq,i_gd,i_gq,xdc,xqc; PLL states eta=8, th=9 dropped).

Result: the real A_e stays firmly Hurwitz as the grid weakens, while the full 10-state
system goes unstable at SCR~0.905.  => the weak-grid instability is a PLL/coupling mode,
NOT an electrical onset.  R1's premise is FALSE for this model (see ../R1_RETRACTED.md).

Run:  python3 R1_real_model_test.py     (run from formalization/numerical, or adjust path)
"""
import numpy as np, sys, os
HERE=os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..", "numerical")))
from sweep import Afun, pv

def J_full(SCR, XR=10, Kp=0.30, Ki=150):
    wn,Vg,Rg,Lg,vcd = pv(SCR,XR)
    return np.array(Afun(wn,Vg,Rg,Lg,vcd,Kp,Ki), float)

def maxre_full(SCR): return np.linalg.eigvals(J_full(SCR)).real.max()
def maxre_elec(SCR): return np.linalg.eigvals(J_full(SCR)[:8,:8]).real.max()

if __name__=="__main__":
    print("Real GFL (sweep.py) -- full 10D vs PLL-frozen electrical 8D, max Re(eig):")
    print("  SCR    Lg        maxRe(full)   maxRe(electrical A_e)")
    for SCR in [2.0,1.5,1.0,0.95,0.91,0.90,0.85,0.70]:
        wn,Vg,Rg,Lg,vcd = pv(SCR,10)
        print("  %.2f  %.5f   %+9.4f      %+9.4f" % (SCR, Lg, maxre_full(SCR), maxre_elec(SCR)))
    # dq-symmetry check at SCR=1 (rotation-form deviation of the 2x2 blocks)
    A=J_full(1.0)[:8,:8]; dev=0.0
    for k in range(4):
        for l in range(4):
            B=A[2*k:2*k+2,2*l:2*l+2]
            dev=max(dev, abs(B[0,0]-B[1,1]), abs(B[1,0]+B[0,1]))
    print("\n  dq mirror-symmetry deviation of A_e at SCR=1: %.2f  (~0 would allow 8->4 complex" % dev)
    print("  reduction; %.0f means it does NOT -- loaded equilibrium v_cd!=0 breaks the symmetry)" % dev)
    print("\n=> A_e never crosses 0 (stays ~ -100); full system crosses at SCR~0.905.")
    print("   The weak-grid instability is a PLL/coupling mode, not an electrical onset.")
    print("   R1's premise is FALSE for this model -> R1 retracted (see ../R1_RETRACTED.md).")
