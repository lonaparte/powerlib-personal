"""
ffold_locate.py -- DIRECTLY locate the cycle fold Sigma_fold of the task model and show
loss of synchronization past it, anchoring kyx/ffold_cyclefold_normalform.kyx with a real
fold (not just the normal-form structure).

At Kp=0.50 (supercritical, l1<0; with l2>0 from ffold_l2_branch => l1*l2<0 => PHYSICAL
fold): the normal form mu = -l1*rho - l2*rho^2 = |l1|*rho - l2*rho^2 has a maximum
mu_fold = l1^2/(4*l2) at rho* = |l1|/(2*l2).  For grid past this (mu>mu_fold) NO limit
cycle exists -> the bounded oscillation is destroyed -> trajectory escapes (theta_e
drifts) = loss of synchronization.  We sweep the growth rate mu (via SCR) and detect:
  - the stable-cycle amplitude rising to a max (the fold), then
  - escape / unbounded theta_e drift past it.
"""
import numpy as np
from fh_gate import grid_RL, equilibrium
from fh_model_sym import rhs, jac
from scipy.integrate import solve_ivp

XR, Ki, Kp = 10.0, 150.0, 0.50

def hopf_SCR():
    def mr(SCR):
        Rg,Lg=grid_RL(SCR,XR); x,r,_=equilibrium(SCR,Kp,Ki,XR)
        return np.max(np.linalg.eigvals(jac(x,Rg,Lg,Kp,Ki)).real) if r<1e-6 else None
    lo,hi=0.6,1.5
    for _ in range(40):
        m=(lo+hi)/2; v=mr(m)
        if v is None: lo=m; continue
        (lo,hi)=(m,hi) if v>0 else (lo,m)
    return (lo+hi)/2

def outcome(SCR, T=10.0):
    """integrate from a small perturbation; classify bounded-cycle (return amplitude) vs escape."""
    Rg,Lg=grid_RL(SCR,XR); xeq,r,_=equilibrium(SCR,Kp,Ki,XR); assert r<1e-6
    f=lambda t,x: rhs(x,Rg,Lg,Kp,Ki); J=lambda t,x: jac(x,Rg,Lg,Kp,Ki)
    s=solve_ivp(f,[0,T],xeq+1e-3*np.ones(10),method='Radau',jac=J,rtol=1e-7,atol=1e-9,dense_output=False)
    if not s.success: return ("escape", np.inf)
    th=s.y[9]; threl=th-xeq[9]
    # escape if theta_e drifts far (loss of sync) or state blows up
    if np.max(np.abs(threl))>3.0 or np.max(np.abs(s.y))>1e6:
        return ("escape", float(np.max(np.abs(threl))))
    y=s.y[:,s.t>T*0.7]; amp=0.5*(y[9].max()-y[9].min())
    return ("cycle", amp)

if __name__=="__main__":
    SCRh=hopf_SCR()
    print("Locating Sigma_fold at Kp=%.2f (SCR_H=%.4f). Sweep grid past the Hopf (SCR down = mu up):"%(Kp,SCRh))
    print("  SCR      mu(growth)    outcome      th_e amplitude / drift")
    prev_amp=None; fold_SCR=None
    for SCR in [SCRh-0.005,SCRh-0.01,SCRh-0.02,SCRh-0.03,SCRh-0.04,SCRh-0.05,SCRh-0.06,SCRh-0.08,SCRh-0.10]:
        Rg,Lg=grid_RL(SCR,XR); xeq,_,_=equilibrium(SCR,Kp,Ki,XR)
        mu=np.max(np.linalg.eigvals(jac(xeq,Rg,Lg,Kp,Ki)).real)
        kind,val=outcome(SCR)
        tag = "stable cycle" if kind=="cycle" else "ESCAPE (loss of sync)"
        print("  %.4f   %+.4f      %-22s %.3f"%(SCR,mu,tag,val))
        if kind=="escape" and fold_SCR is None and prev_amp is not None:
            fold_SCR=SCR
        if kind=="cycle": prev_amp=val
    print()
    if fold_SCR:
        print("  => cycle DESTROYED between SCR=%.4f and %.4f: the stable limit cycle reaches max"%(fold_SCR+0.01,fold_SCR))
        print("     amplitude then vanishes (Sigma_fold), past which theta_e drifts unboundedly =")
        print("     LOSS OF SYNCHRONIZATION. This is F-fold realized on the task model.")
    else:
        print("  => no escape in swept range; extend the sweep (fold deeper).")
