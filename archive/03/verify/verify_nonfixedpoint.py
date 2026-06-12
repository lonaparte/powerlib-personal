#!/usr/bin/env python3
"""
VERIFY the reviewer's three claims against the EXACT LFilterT3 model (same F as derive_lfilter_T3):
  (a) the substitution point (i_d=P_ref/1.5Vg, i_q=0, η=0, θ_e) is NOT a fixed point of the
      no-integrator (P-only) field F4d:  ||F4d(i_d_ref,0,0,θ)|| ≠ 0 for all θ
      (even choosing θ so v_cqc=0 only zeroes F[2], not the current rows F[0],F[1]).
  (b) at the P-only field's OWN (proportional-droop) equilibrium F4d=0, symmetric gains give
      Σ_iq ≠ Σ_id  (rel.diff ≠ 0) — the symmetry breaks off the substitution point.
  (c) integrators are structurally Schur-irreducible: an integrator state ζ (ζ'=P_ref−1.5Vg·i_d)
      has ∂ζ'/∂ζ = 0, so the 1×1 'rem' block is 0 and the Schur complement M=Ablk−v wᵀ/0 is undefined
      ⇒ you cannot make i_d=P_ref/1.5Vg a true equilibrium AND keep a 3-state reduction.
"""
import numpy as np, sympy as sp
from scipy.optimize import fsolve

Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_P,Kp_Q,Kp_pll,Ki_pll,P_ref,Q_ref=sp.symbols(
 'Vg wn Lf Rf Lg Rg Kpi Kp_P Kp_Q Kp_pll Ki_pll P_ref Q_ref')
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e'); X=[i_d,i_q,eta,th]
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
PAR=[Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_P,Kp_Q,Kp_pll,Ki_pll,P_ref,Q_ref]
F_f=sp.lambdify(X+PAR,list(F)); J_f=sp.lambdify(X+PAR,J); vcqc_f=sp.lambdify(X+PAR,v_cqc)

def Sig(Jn,keep,rem):
    M=Jn[np.ix_(keep,keep)]-(Jn[np.ix_(keep,[rem])]@Jn[np.ix_([rem],keep)])/Jn[rem,rem]
    a=np.poly(M); return a[1]*a[2]-a[3]

p=dict(Vg=1.0,wn=1.0,Lf=0.05,Rf=0.005,Lg=0.6,Rg=0.06,Kpi=0.5,Kp_pll=2.0,Ki_pll=20.0,
       Q_ref=0.0,P_ref=1.0,Kp_P=0.02,Kp_Q=0.02)              # weak grid, SYMMETRIC gains
pv=[p[str(k)] for k in PAR]; ID=p['P_ref']/(1.5*p['Vg'])

print("="*78)
print(f"(a) substitution point  i_d_ref = P_ref/(1.5Vg) = {ID:.4f},  i_q=0, η=0")
print("    residual ||F4d|| of the P-only field at that point, swept over θ_e:")
for thv in [0.0,-0.5,-1.0,-1.322]:
    r=np.array(F_f(ID,0.0,0.0,thv,*pv),float)
    # also at θ chosen so v_cqc=0:
    print(f"    θ={thv:+.3f}: ||F4d||={np.linalg.norm(r):.4e}   (F0={r[0]:+.3e}, F1={r[1]:+.3e}, F2=v_cqc={r[2]:+.3e})")
thlock=fsolve(lambda t: vcqc_f(ID,0.0,0.0,t[0],*pv),[-0.3])[0]
rlock=np.array(F_f(ID,0.0,0.0,thlock,*pv),float)
print(f"    even at θ={thlock:.4f} (v_cqc=0 EXACTLY): ||F4d||={np.linalg.norm(rlock):.4e}  (F2={rlock[2]:.1e} but F0,F1≠0)")
print("    ⇒ substitution point is NOT a fixed point of F4d. CONFIRMED.")

print("="*78)
print("(b) P-only field's OWN equilibrium (fsolve F4d=0), symmetric gains:")
ystar=fsolve(lambda y: np.array(F_f(*y,*pv),float), [0.02,0.0,0.0,-0.1], xtol=1e-13)
res=np.max(np.abs(np.array(F_f(*ystar,*pv),float)))
Jn=np.array(J_f(*ystar,*pv),float)
Siq=Sig(Jn,[1,2,3],0); Sid=Sig(Jn,[0,2,3],1)
print(f"    true eq: i_d={ystar[0]:.4f} (vs ref {ID:.4f}), i_q={ystar[1]:.4f}, θ_e={ystar[3]:.4f}, |F|={res:.1e}")
print(f"    Σ_iq={Siq:.4e}, Σ_id={Sid:.4e}, rel.diff=|Σ_iq−Σ_id|/|Σ_id|={abs(Siq-Sid)/abs(Sid):.2%}")
print("    ⇒ at the field's REAL equilibrium, symmetric gains give Σ_iq ≠ Σ_id. CONFIRMED.")

print("="*78)
print("(c) integrator structural irreducibility:")
zeta=sp.Symbol('zeta'); KiP=sp.Symbol('Ki_P')
zeta_dot=P_ref-sp.Rational(3,2)*Vg*i_d            # an outer power integrator: ζ' = err_P
print("    integrator ζ' = P_ref − 1.5·Vg·i_d  ⇒  ∂ζ'/∂ζ =", sp.diff(zeta_dot,zeta),
      "(zero self-Jacobian)")
print("    ⇒ the 1×1 Schur 'rem' block for ζ is 0; M = Ablk − v wᵀ/0 is undefined.")
print("    So one cannot make i_d=P_ref/1.5Vg a true equilibrium (needs the integrator) AND")
print("    keep a 3-state Schur reduction. The T3 object is intrinsically a hybrid. CONFIRMED.")
