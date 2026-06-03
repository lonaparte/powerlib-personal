#!/usr/bin/env python3
"""
THEOREM (general power angle).  Reduced 4-state model, equilibrium currents substituted, θ_e* KEPT
SYMBOLIC (C=cosθ_e*, S=sinθ_e*), ALL params symbolic.  Prove:
    num(Σ_iq − Σ_id) = (Kp_P − Kp_Q) · G(C,S,params)        [⇒ symmetric gains ⟹ Σ_iq≡Σ_id, ∀θ_e*]

Tractability: the eliminated 'rem' block is 1×1 (= scalar d), so the Schur complement M = Ablk − v wᵀ/d.
With N := d·M (a POLYNOMIAL 3×3), char poly coeffs scale as A_N=d·A, B_N=d²·B, C_N=d³·C, hence
    Σ := A·B − C = (A_N·B_N − C_N)/d³.
So Σ is got from charpoly of a POLYNOMIAL matrix (Faddeev–LeVerrier, fast) — no rational charpoly.
"""
import sympy as sp, time, pickle
t0=time.time(); log=lambda m:print(f"[{time.time()-t0:6.1f}s] {m}",flush=True)

Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_P,Kp_Q,Kp_pll,Ki_pll,P_ref=sp.symbols(
 'Vg wn Lf Rf Lg Rg Kpi Kp_P Kp_Q Kp_pll Ki_pll P_ref',positive=True)
Q_ref=sp.Symbol('Q_ref',real=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
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
ID=P_ref/(sp.Rational(3,2)*Vg); IQ=-Q_ref/(sp.Rational(3,2)*Vg)
C,S=sp.symbols('C S',real=True)
sub=[(i_d,ID),(i_q,IQ),(eta,0)]
# entries are polynomial in C,S; rational in params.  Do NOT cancel.
Je=sp.Matrix(4,4,lambda i,j: sp.expand(J[i,j].subs(sub).rewrite(sp.cos).subs(
    [(sp.sin(th),S),(sp.cos(th),C)])))
log("Je formed (all-symbolic, general θ_e*)")
lam=sp.symbols('lam')

def SigN(keep,rem):
    d=Je[rem,rem]; Ablk=Je[keep,keep]; v=Je[keep,[rem]]; w=Je[[rem],keep]
    N=sp.expand(d*Ablk - v*w)                  # polynomial 3×3
    co=N.charpoly(lam).all_coeffs()            # [1, A_N, B_N, C_N]
    return sp.expand(co[1]*co[2]-co[3]), d      # (A_N B_N − C_N) = d³·Σ ,   d

SN_iq,d_iq=SigN([1,2,3],0); log(f"Σ_iq: ops(SN)={sp.count_ops(SN_iq)}")
SN_id,d_id=SigN([0,2,3],1); log(f"Σ_id: ops(SN)={sp.count_ops(SN_id)}")

# D = SN_iq/d_iq³ − SN_id/d_id³ ; num over common denom = SN_iq·d_id³ − SN_id·d_iq³  (∝ D)
num_raw=sp.expand(SN_iq*d_id**3 - SN_id*d_iq**3)
log(f"num_raw formed, ops={sp.count_ops(num_raw)}")

# (A) SYMMETRIC GAINS ⇒ D ≡ 0 at general θ_e* (the user's conclusion, proved all-symbolic):
num_sym=sp.expand(num_raw.subs(Kp_Q,Kp_P))
print("\n(A) num(D)|_{Kp_P=Kp_Q} == 0  (all params & θ_e* symbolic) :", num_sym==0)

# (B) FACTORISATION: reduce D to lowest terms, then (Kp_P−Kp_Q) | numerator?
Dred=sp.cancel(SN_iq/d_iq**3 - SN_id/d_id**3); log("D cancelled to lowest terms")
num=sp.fraction(sp.together(Dred))[0]; num=sp.expand(num)
log(f"reduced num(D) ops={sp.count_ops(num)}")
qd,rd=sp.div(num,(Kp_P-Kp_Q),Kp_P)
print("(B) (Kp_P − Kp_Q) | reduced numerator(D)  [general θ_e*] :", sp.expand(rd)==0)
G=sp.expand(qd)
log(f"G = num/(Kp_P−Kp_Q), ops={sp.count_ops(G)}")

# Does the identity need C²+S²=1, or is it FREE in C,S?  (decides the Lean encoding)
chk=sp.expand(num-(Kp_P-Kp_Q)*G)
print("(C) num − (Kp_P−Kp_Q)·G  ≡ 0 as a FREE polynomial in C,S :", chk==0)
print("    (if True, Lean `ring` suffices with C,S as plain variables — no C²+S²=1 needed)")

pickle.dump({'num':str(num),'G':str(G)},open('/tmp/T3_general_theta.pkl','wb'))
log("saved reduced num(D), G to /tmp/T3_general_theta.pkl")
