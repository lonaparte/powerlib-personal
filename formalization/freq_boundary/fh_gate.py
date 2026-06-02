"""
fh_gate.py -- OBJECT GATE for the F-H / F-fold task.  Transcribes the task's explicit
RHS (converter-oriented frame, c=cos(th_e), s=sin(th_e)) EXACTLY as written, and checks
whether its spectrum (hence Hopf onset SCR_H) matches the validated sweep.py (Conventions
sec.12) whose Hopf is at SCR_H ~ 0.905.  Eigenvalues are frame-invariant, so if the two
agree the F-H boundary Sigma_H is the same object and can be built on either.

NB: the task says the model = run_sde_schafer.full_dynamics_ad, which is NOT in this repo;
the authority used here is (a) the explicit RHS in the task and (b) the validated sweep.py.
"""
import numpy as np
from scipy.optimize import fsolve

# fixed device params (Conventions sec.12.2)
Lf, Cf, Rf = 1e-3, 1e-4, 0.1
Kpi, Kii, Kad = 1.26, 126.0, 2.0
idref, iqref = 80.0, 0.0
wn = 2*np.pi*50.0
Vg = 380.0*np.sqrt(2.0/3.0)

def grid_RL(SCR, XR=10.0):
    Zg = 380.0**2/(1e5*SCR); sq = np.sqrt(1+XR**2)
    return Zg/sq, Zg*XR/(sq*wn)          # Rg, Lg

def rhs(x, Rg, Lg, Kp_pll, Ki_pll):
    i_d,i_q,v_cd,v_cq,i_gd,i_gq,xi_dc,xi_qc,eta,th_e = x
    c, s = np.cos(th_e), np.sin(th_e)
    i_dc  = c*i_d - s*i_q;            i_qc  = s*i_d + c*i_q
    v_cdc = c*v_cd - s*v_cq;          v_cqc = s*v_cd + c*v_cq
    i_Cdc = c*(i_d-i_gd) - s*(i_q-i_gq); i_Cqc = s*(i_d-i_gd) + c*(i_q-i_gq)
    err_d = idref - i_dc;             err_q = iqref - i_qc
    u_dc = Kpi*err_d + Kii*xi_dc - wn*Lf*i_qc + v_cdc - Kad*i_Cdc
    u_qc = Kpi*err_q + Kii*xi_qc + wn*Lf*i_dc + v_cqc - Kad*i_Cqc
    u_d = c*u_dc + s*u_qc;            u_q = -s*u_dc + c*u_qc
    return np.array([
        (u_d - v_cd - Rf*i_d + wn*Lf*i_q)/Lf,
        (u_q - v_cq - Rf*i_q - wn*Lf*i_d)/Lf,
        (i_d - i_gd + wn*Cf*v_cq)/Cf,
        (i_q - i_gq - wn*Cf*v_cd)/Cf,
        (v_cd - Vg - Rg*i_gd + wn*Lg*i_gq)/Lg,
        (v_cq - Rg*i_gq - wn*Lg*i_gd)/Lg,
        err_d, err_q, v_cqc, -Kp_pll*v_cqc - Ki_pll*eta])

def jac(x, Rg, Lg, Kp, Ki, h=1e-6):
    n=len(x); J=np.zeros((n,n))
    for j in range(n):                       # central difference
        xp=x.copy(); xm=x.copy(); xp[j]+=h; xm[j]-=h
        J[:,j]=(rhs(xp,Rg,Lg,Kp,Ki)-rhs(xm,Rg,Lg,Kp,Ki))/(2*h)
    return J

def equilibrium(SCR, Kp=0.30, Ki=150.0, XR=10.0):
    Rg, Lg = grid_RL(SCR, XR)
    # initial guess: converter ~aligned, currents at ref, cap voltage ~ Vg
    x0 = np.array([idref,iqref,Vg,0.0,idref,0.0,Rf*idref/Kii,0.0,0.0,0.1])
    x, info, ier, msg = fsolve(rhs, x0, args=(Rg,Lg,Kp,Ki), full_output=True, xtol=1e-13)
    return x, np.linalg.norm(rhs(x,Rg,Lg,Kp,Ki)), ier

def maxre(SCR, Kp=0.30, Ki=150.0, XR=10.0):
    Rg, Lg = grid_RL(SCR, XR); x,res,ier = equilibrium(SCR,Kp,Ki,XR)
    if res>1e-6: return None
    return np.max(np.linalg.eigvals(jac(x,Rg,Lg,Kp,Ki)).real)

if __name__ == "__main__":
    print("Task RHS (converter frame): equilibrium residual + max Re(eig) vs grid strength")
    print("  SCR    ||f(x*)||   maxRe(J)     (sweep.py sec.12 Hopf at SCR_H~0.905)")
    for SCR in [1.5,1.2,1.0,0.95,0.92,0.905,0.90,0.88,0.85]:
        x,res,ier = equilibrium(SCR)
        mr = maxre(SCR)
        print("  %.3f   %.1e    %s" % (SCR, res, ("%+.4f"%mr) if mr is not None else "no eq"))
    # bisect the task model's Hopf
    lo,hi=0.85,1.0
    fa=maxre(lo);
    for _ in range(40):
        m=(lo+hi)/2; r=maxre(m)
        if r is None: break
        if r>0: lo=m
        else: hi=m
    print("\n  => task-model Hopf SCR_H ~ %.4f   (compare sweep.py 0.905)" % ((lo+hi)/2))
