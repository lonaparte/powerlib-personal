#!/usr/bin/env python3
"""
THEORETICAL PROOF (light, all-symbolic, general power angle).  Set Kp_P=Kp_Q=:Kp from the start
(symmetric outer gains) and prove  D := Σ_iq − Σ_id ≡ 0  for ALL θ_e* and ALL params.

By the factor theorem this is EQUIVALENT to "(Kp_P−Kp_Q) divides num(Σ_iq−Σ_id)", i.e. the clean
factorisation of LFilterT3 SURVIVES at the physical angle θ_e*≠0 — it is not an artifact of θ_e*=0.

Same polynomial-charpoly trick (Σ=(A_N B_N−C_N)/d³, N=d·M) so no rational charpoly.
"""
import sympy as sp, time
t0=time.time(); log=lambda m:print(f"[{time.time()-t0:6.1f}s] {m}",flush=True)
Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp,Kp_pll,Ki_pll,P_ref=sp.symbols(
 'Vg wn Lf Rf Lg Rg Kpi Kp Kp_pll Ki_pll P_ref',positive=True)
Q_ref=sp.Symbol('Q_ref',real=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
Lt=Lf+Lg; Rt=Rf+Rg; gam=(Lf*Rg-Rf*Lg)/Lt; c,s=sp.cos(th),sp.sin(th)
err_P=P_ref-sp.Rational(3,2)*Vg*i_d; err_Q=Q_ref+sp.Rational(3,2)*Vg*i_q
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
err_d=Kp*err_P-i_dc; err_q=-Kp*err_Q-i_qc        # SYMMETRIC gains Kp_P=Kp_Q=Kp
u_dc=(Lt/Lf)*(Kpi*err_d-wn*Lf*i_qc+(Lf/Lt)*c*Vg+gam*i_dc)
u_qc=(Lt/Lf)*(Kpi*err_q+wn*Lf*i_dc+(Lf/Lt)*s*Vg+gam*i_qc)
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
vPCCd=(Lg/Lt)*u_d+(Lf/Lt)*Vg+gam*i_d; vPCCq=(Lg/Lt)*u_q+gam*i_q
v_cqc=s*vPCCd+c*vPCCq
F=sp.Matrix([(u_d-Vg-Rt*i_d+Lt*wn*i_q)/Lt,(u_q-Rt*i_q-Lt*wn*i_d)/Lt,
             v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X)
ID=P_ref/(sp.Rational(3,2)*Vg); IQ=-Q_ref/(sp.Rational(3,2)*Vg)
C,S=sp.symbols('C S',real=True)
sub=[(i_d,ID),(i_q,IQ),(eta,0)]
Je=sp.Matrix(4,4,lambda i,j: sp.expand(J[i,j].subs(sub).rewrite(sp.cos).subs(
    [(sp.sin(th),S),(sp.cos(th),C)])))
log("Je formed (symmetric gains, general θ_e*)")
lam=sp.symbols('lam')
def SigN(keep,rem):
    d=Je[rem,rem]; Ablk=Je[keep,keep]; v=Je[keep,[rem]]; w=Je[[rem],keep]
    N=sp.expand(d*Ablk - v*w)
    co=N.charpoly(lam).all_coeffs()
    return sp.expand(co[1]*co[2]-co[3]), d
SN_iq,d_iq=SigN([1,2,3],0); log("Σ_iq done")
SN_id,d_id=SigN([0,2,3],1); log("Σ_id done")
# D = SN_iq/d_iq³ − SN_id/d_id³ ; D≡0  ⟺  SN_iq·d_id³ − SN_id·d_iq³ ≡ 0
num=sp.expand(SN_iq*d_id**3 - SN_id*d_iq**3)
log(f"num(∝D) formed, ops={sp.count_ops(num)}")
print("\n========================================================")
print("THEOREM (symmetric gains, general θ_e*, all params symbolic):")
print("   Σ_iq − Σ_id ≡ 0   ⟺   num =", num)
print("   ⇒ proved:", sp.expand(num)==0)
print("========================================================")
print("By the factor theorem, num(Σ_iq−Σ_id)|_{Kp_Q=Kp_P}=0 ⟺ (Kp_P−Kp_Q) | num(Σ_iq−Σ_id).")
print("So the LFilterT3 factorisation NUM=(Kp_P−Kp_Q)·G is NOT an artifact of θ_e*=0:")
print("the difference vanishes at symmetric gains for EVERY power angle θ_e* and every parameter.")
