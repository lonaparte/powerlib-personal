#!/usr/bin/env python3
"""
Is D|_{Kp_P=Kp_Q}=0 a property of the TRUE equilibrium of the 4-state reduced model, or only of the
T3 substitution point (power-reference currents i_d*=P_ref/(1.5Vg), i_q*=-Q_ref/(1.5Vg), η*=0)?

The reduced model has NO outer integrator (proportional droop), so its own F=0 equilibrium does NOT
pin i_d* to P_ref/(1.5Vg).  We solve F=0 (fsolve) for a weak grid (θ_e*≠0), then compare
D|_{sym} at: (i) the true equilibrium, (ii) the T3 substitution point.
"""
import numpy as np, sympy as sp
from scipy.optimize import fsolve

# symbolic model (same as derive_lfilter_T3 / T3_theta), all params symbolic -> lambdify
Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_P,Kp_Q,Kp_pll,Ki_pll,P_ref,Q_ref = sp.symbols(
    'Vg wn Lf Rf Lg Rg Kpi Kp_P Kp_Q Kp_pll Ki_pll P_ref Q_ref')
i_d,i_q,eta,th = sp.symbols('i_d i_q eta theta_e')
X=[i_d,i_q,eta,th]
Lt=Lf+Lg; Rt=Rf+Rg; gam=(Lf*Rg-Rf*Lg)/Lt; c,s=sp.cos(th),sp.sin(th)
err_P=P_ref-sp.Rational(3,2)*Vg*i_d; err_Q=Q_ref+sp.Rational(3,2)*Vg*i_q
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
err_d=Kp_P*err_P-i_dc; err_q=-Kp_Q*err_Q-i_qc
u_dc=(Lt/Lf)*(Kpi*err_d-wn*Lf*i_qc+(Lf/Lt)*c*Vg+gam*i_dc)
u_qc=(Lt/Lf)*(Kpi*err_q+wn*Lf*i_dc+(Lf/Lt)*s*Vg+gam*i_qc)
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
vPCCd=(Lg/Lt)*u_d+(Lf/Lt)*Vg+gam*i_d; vPCCq=(Lg/Lt)*u_q+gam*i_q
v_cqc=s*vPCCd+c*vPCCq
F=sp.Matrix([(u_d-Vg-Rt*i_d+Lt*wn*i_q)/Lt,(u_q-Rt*i_q-Lt*wn*i_d)/Lt,
             v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X)
PARAMS=[Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_P,Kp_Q,Kp_pll,Ki_pll,P_ref,Q_ref]
F_f=sp.lambdify(X+PARAMS,list(F),'numpy')
J_f=sp.lambdify(X+PARAMS,J,'numpy')
vcqc_f=sp.lambdify(X+PARAMS,v_cqc,'numpy')

def sigma_diff(Jn):
    """D = Σ_iq − Σ_id at numeric 4×4 Jacobian Jn (Schur A·B−C, eliminate i_d resp. i_q)."""
    def Sig(keep,rem):
        Jk=Jn[np.ix_(keep,keep)]; Jkr=Jn[np.ix_(keep,[rem])]
        Jrk=Jn[np.ix_([rem],keep)]; M=Jk-(Jkr@Jrk)/Jn[rem,rem]
        a=np.poly(M)          # [1, A, B, C]
        return a[1]*a[2]-a[3]
    return Sig([1,2,3],0)-Sig([0,2,3],1)

# weak grid, symmetric gains; sweep P_ref (load) -> grows |θ_e*|
base=dict(Vg=1.0,wn=1.0,Lf=0.05,Rf=0.005,Lg=0.6,Rg=0.06,Kpi=0.5,
          Kp_pll=2.0,Ki_pll=20.0,Q_ref=0.0)
KP=0.02   # symmetric: Kp_P=Kp_Q=KP
print(f"{'P_ref':>7} {'θ_e*(true)':>12} {'i_d*(true)':>11} {'P_ref/1.5Vg':>12} "
      f"{'D|sym(true eq)':>16} {'D|sym(T3 subst)':>16}")
for Pr in [0.0,0.2,0.5,0.8,1.0]:
    p=dict(base); p['P_ref']=Pr; p['Kp_P']=KP; p['Kp_Q']=KP
    pv=[p[str(k)] for k in PARAMS]
    # true equilibrium of the reduced model:
    g=lambda y: np.array(F_f(*y,*pv),dtype=float).ravel()
    y0=np.array([Pr/(1.5*p['Vg']),0.0,0.0,-0.2])
    sol=fsolve(g,y0,full_output=True); ystar=sol[0]; ok=np.max(np.abs(g(ystar)))
    Jtrue=np.array(J_f(*ystar,*pv),dtype=float)
    Dtrue=sigma_diff(Jtrue)
    # T3 substitution point: i_d*=P_ref/(1.5Vg), i_q*=0, η*=0, θ_e* solves v_cqc=0
    ID=Pr/(1.5*p['Vg']);
    th_sub=fsolve(lambda t: vcqc_f(ID,0.0,0.0,t[0],*pv), [-0.2])[0]
    Jsub=np.array(J_f(ID,0.0,0.0,th_sub,*pv),dtype=float)
    Dsub=sigma_diff(Jsub)
    print(f"{Pr:7.2f} {ystar[3]:12.5f} {ystar[0]:11.5f} {Pr/(1.5*p['Vg']):12.5f} "
          f"{Dtrue:16.3e} {Dsub:16.3e}   (|F|={ok:.1e})")
print("\nIf D|sym(true eq)=0 AND D|sym(T3 subst)=0 at θ_e*≠0  ⇒ reduced model is genuinely d/q-symmetric")
print("at symmetric gains for ALL power angles; the 9D asymmetry must come from DROPPED dynamics.")
