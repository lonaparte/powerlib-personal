#!/usr/bin/env python3
"""
Cross-check: the NEW general-θ derivation (polynomial-charpoly Σ=(A_N B_N−C_N)/d³, this session)
must reproduce the EXISTING θ_e*=0 derivation (derive_lfilter_T3.py: cancelled rational charpoly)
when C=1,S=0.  Compare the reduced D as rational functions of (Kp_P,Kp_Q,P_ref,Q_ref) at network set#0.
If equal ⇒ the new derivation is consistent with the machine-checked LFilterT3 certificate.
"""
import sympy as sp
Kp_P,Kp_Q,P_ref,Q_ref=sp.symbols('Kp_P Kp_Q P_ref Q_ref',real=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
# network set#0 (rational):
Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_pll,Ki_pll=(1,1,sp.Rational(1,20),sp.Rational(1,200),
   sp.Rational(3,10),sp.Rational(3,100),sp.Rational(1,2),2,20)
Lt=Lf+Lg; Rt=Rf+Rg; gam=(Lf*Rg-Rf*Lg)/Lt; lam=sp.symbols('lam')

def model(c,s):
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
    return F.jacobian(X)

ID=P_ref/(sp.Rational(3,2)*Vg); IQ=-Q_ref/(sp.Rational(3,2)*Vg)
sub=[(i_d,ID),(i_q,IQ),(eta,0)]
Jsym=model(sp.cos(th),sp.sin(th))   # differentiate with th SYMBOLIC (preserves ∂/∂θ_e column)

# ---- Method A: EXISTING (derive_lfilter_T3): θ_e*=0 AFTER differentiating, cancelled rational charpoly ----
JeA=sp.Matrix(4,4,lambda a,b: sp.cancel(Jsym[a,b].subs(sub).subs([(sp.cos(th),1),(sp.sin(th),0),(th,0)])))
def SigA(keep):
    rem=[k for k in range(4) if k not in keep]
    M=JeA[keep,keep]-JeA[keep,rem]*JeA[rem,rem].inv()*JeA[rem,keep]
    co=sp.Matrix(M).charpoly(lam).all_coeffs(); return sp.cancel(co[1]*co[2]-co[3])
D_A=sp.cancel(SigA([1,2,3])-SigA([0,2,3]))

# ---- Method B: NEW (this session): general C,S then C=1,S=0, polynomial-charpoly ----
C,S=sp.symbols('C S',real=True)
JeB=sp.Matrix(4,4,lambda a,b: sp.expand(Jsym[a,b].subs(sub)
              .subs([(sp.sin(th),S),(sp.cos(th),C)])))
def SigNB(keep,rem):
    d=JeB[rem,rem]; Ab=JeB[keep,keep]; v=JeB[keep,[rem]]; w=JeB[[rem],keep]
    N=sp.expand(d*Ab-v*w); co=N.charpoly(lam).all_coeffs()
    return sp.expand(co[1]*co[2]-co[3]), d
SNiq,diq=SigNB([1,2,3],0); SNid,did=SigNB([0,2,3],1)
D_B_gen=sp.cancel(SNiq/diq**3 - SNid/did**3)
D_B=sp.cancel(D_B_gen.subs([(C,1),(S,0)]))

diff=sp.simplify(D_A-D_B)
print("Method A (existing θ_e*=0, cancelled charpoly)  reduced D at set#0 — ops:", sp.count_ops(D_A))
print("Method B (new general-θ, poly charpoly) at C=1,S=0 — ops:", sp.count_ops(D_B))
print("\nD_A - D_B  ≡ 0 (new derivation reproduces the existing θ_e*=0 certificate) :", diff==0)
# also confirm the factorisation matches at this slice:
nA=sp.fraction(sp.together(D_A))[0]
print("(Kp_P−Kp_Q) | numerator(D_A) :", sp.expand(sp.div(sp.expand(nA),(Kp_P-Kp_Q),Kp_P)[1])==0)
