#!/usr/bin/env python3
"""
UNIVERSAL (all network params symbolic) attempt via the rational-function field.
Network params live in the GROUND DOMAIN QQ(Lf,Rf,Lg,Rg,Kpi,Kp_pll,Ki_pll,Vg,wn); only the variables
the objection concerns (C,S,Kp_P,Kp_Q,P_ref,Q_ref) are polynomial generators.  Poly DMP arithmetic
(fraction-field coefficients) is far faster than Expr.expand — the prior all-symbolic wall.

Proves, fully parametrically: (Kp_P−Kp_Q) | num(Σ_iq−Σ_id) and D|_{Kp_P=Kp_Q}≡0 at general θ_e*.
"""
import sympy as sp, time
t0=time.time(); log=lambda m:print(f"[{time.time()-t0:6.1f}s] {m}",flush=True)
Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_pll,Ki_pll=sp.symbols('Vg wn Lf Rf Lg Rg Kpi Kp_pll Ki_pll')
C,S,Kp_P,Kp_Q,P_ref,Q_ref=sp.symbols('C S Kp_P Kp_Q P_ref Q_ref')
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e'); X=[i_d,i_q,eta,th]
gens=(C,S,Kp_P,Kp_Q,P_ref,Q_ref)
dom=sp.QQ.frac_field(Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_pll,Ki_pll)
def P(e): return sp.Poly(sp.expand(e),*gens,domain=dom)

Lt=Lf+Lg; Rt=Rf+Rg; gam=(Lf*Rg-Rf*Lg)/Lt
# build Jacobian with th symbolic, then substitute equilibrium + sin->S,cos->C
c,s=sp.cos(th),sp.sin(th)
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
sub=[(i_d,ID),(i_q,IQ),(eta,0)]
log("building Je as Poly over QQ(network)[C,S,Kp_P,Kp_Q,P_ref,Q_ref] ...")
Je=[[P(J[a,b].subs(sub).subs([(sp.sin(th),S),(sp.cos(th),C)])) for b in range(4)] for a in range(4)]
log("Je Poly matrix formed")

def SigN(keep,rem):
    d=Je[rem][rem]
    Ab=[[Je[keep[a]][keep[b]] for b in range(3)] for a in range(3)]
    v=[Je[keep[a]][rem] for a in range(3)]; w=[Je[rem][keep[b]] for b in range(3)]
    # N = d*Ab - v wᵀ  (3×3 Poly)
    N=[[d*Ab[a][b]-v[a]*w[b] for b in range(3)] for a in range(3)]
    # char poly coeffs of 3×3: A=-tr, B=sum principal 2-minors, Cc=-det
    A=-(N[0][0]+N[1][1]+N[2][2])
    B=(N[0][0]*N[1][1]-N[0][1]*N[1][0])+(N[0][0]*N[2][2]-N[0][2]*N[2][0])+(N[1][1]*N[2][2]-N[1][2]*N[2][1])
    det=(N[0][0]*(N[1][1]*N[2][2]-N[1][2]*N[2][1])
        -N[0][1]*(N[1][0]*N[2][2]-N[1][2]*N[2][0])
        +N[0][2]*(N[1][0]*N[2][1]-N[1][1]*N[2][0]))
    Cc=-det
    return A*B-Cc, d                                  # = d³·Σ
SN_iq,d_iq=SigN([1,2,3],0); log("Σ_iq (Poly) done")
SN_id,d_id=SigN([0,2,3],1); log("Σ_id (Poly) done")
num=SN_iq*d_id**3 - SN_id*d_iq**3                     # ∝ D, polynomial over the field
log(f"num formed (Poly), total_degree={num.total_degree()}")

# (Q2) symmetric gains ⇒ D≡0 :
num_sym=num.subs(Kp_Q,Kp_P)
print("\n(Q2) D|_{Kp_P=Kp_Q} ≡ 0  (ALL network params symbolic, general θ_e*) :", num_sym.is_zero)
# (Q1) (Kp_P−Kp_Q) | num :
q,r=sp.div(num,P(Kp_P-Kp_Q))
print("(Q1) (Kp_P−Kp_Q) | num(Σ_iq−Σ_id)  (ALL network params symbolic, general θ_e*) :", r.is_zero)
log("done — UNIVERSAL parametric proof complete" if num_sym.is_zero and r.is_zero else "done")
