"""
fh_reduce.py -- can the F-H Hopf of the 10-state task model be captured by a low-order
reduced model whose Hopf condition is SYMBOLICALLY certifiable?

The weak-grid Hopf is slow (~38 Hz) vs the electrical modes (~kHz).  Singular-perturbation:
partition states into fast (8 electrical: i_d,i_q,v_cd,v_cq,i_gd,i_gq,xi_dc,xi_qc) and slow
(2 PLL: eta,th_e).  Quasi-steady-state Schur complement gives the reduced slow Jacobian
   J_red(2x2) = A_ss - A_sf * A_ff^{-1} * A_fs.
For a 2x2 system a Hopf is simply  trace(J_red)=0  with  det(J_red)>0  (omega=sqrt(det)).
If trace(J_red)=0 reproduces SCR_H~0.950, then Sigma_H has a tractable reduced form and the
2x2 Routh condition (Hopf <=> tr=0 & det>0) is QE/KeYmaera-X certifiable.

We TEST this numerically here (no claim yet); the certifiable statement is built only if it holds.
"""
import numpy as np
from fh_gate import grid_RL, equilibrium, jac

FAST=[0,1,2,3,4,5,6,7]; SLOW=[8,9]

def reduced(SCR,Kp=0.30,Ki=150.0,XR=10.0):
    Rg,Lg=grid_RL(SCR,XR); x,res,ier=equilibrium(SCR,Kp,Ki,XR); assert res<1e-6
    J=jac(x,Rg,Lg,Kp,Ki)
    Aff=J[np.ix_(FAST,FAST)]; Afs=J[np.ix_(FAST,SLOW)]
    Asf=J[np.ix_(SLOW,FAST)]; Ass=J[np.ix_(SLOW,SLOW)]
    Jr=Ass-Asf@np.linalg.solve(Aff,Afs)
    return Jr, J

if __name__=="__main__":
    print("Singular-perturbation 2x2 PLL reduction vs full 10-state Hopf (SCR_H~0.950):")
    print("  SCR     tr(J_red)    det(J_red)   sqrt(det)[rad/s]   full maxRe   full |Im|crit")
    for SCR in [1.00,0.97,0.955,0.950,0.945,0.93,0.90]:
        Jr,J=reduced(SCR); tr=np.trace(Jr); dt=np.linalg.det(Jr)
        ev=np.linalg.eigvals(J); k=np.argmax(ev.real)
        print("  %.3f   %+.4f     %+.3e   %s          %+.4f      %.1f"
              %(SCR,tr,dt,("%.1f"%np.sqrt(dt)) if dt>0 else "  -  ",
                ev.real.max(), abs(ev[k].imag)))
    # where does tr(J_red)=0?
    lo,hi=0.90,1.00
    for _ in range(40):
        m=(lo+hi)/2; Jr,_=reduced(m)
        if np.trace(Jr)>0: hi=m
        else: lo=m
    Jr,J=reduced((lo+hi)/2)
    print("\n  reduced Hopf  tr(J_red)=0  at SCR=%.4f   (full Hopf 0.9501)"%((lo+hi)/2))
    print("  reduced omega=sqrt(det)=%.1f rad/s   vs full critical |Im|=238.7 rad/s"%np.sqrt(np.linalg.det(Jr)))
    print("  => if SCR and omega match, the 2x2 reduction IS the F-H Hopf (certifiable form).")
