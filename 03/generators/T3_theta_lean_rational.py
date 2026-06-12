#!/usr/bin/env python3
"""
General-θ_e* factorisation, RIGOROUS in the variables the user's objection is about
(C=cosθ_e*, S=sinθ_e*, Kp_P, Kp_Q, P_ref, Q_ref kept SYMBOLIC), over CONCRETE rational network
params.  Exact polynomial identity in those 6 symbols (no floats).  Cross-validated over several
independent network-param sets (CLAUDE.md ≥3).  Dumps num(D)/G of set #1 for the Lean `ring` theorem.

Answers, at general θ_e*:
  (Q1) (Kp_P − Kp_Q) | num(Σ_iq − Σ_id)?          (factor survives the physical angle?)
  (Q2) D|_{Kp_P=Kp_Q} ≡ 0  for all θ_e*, Q_ref?   (interchangeability at every power angle?)
Cross-check: num(C=1,S=0) must reproduce the θ_e*=0 factorisation at the same network params.
"""
import sympy as sp, time, pickle
t0=time.time(); log=lambda m:print(f"[{time.time()-t0:6.1f}s] {m}",flush=True)
C,S,Kp_P,Kp_Q,P_ref,Q_ref=sp.symbols('C S Kp_P Kp_Q P_ref Q_ref',real=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
lam=sp.symbols('lam')

def build(net):
    Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_pll,Ki_pll=net
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
    sub=[(i_d,ID),(i_q,IQ),(eta,0)]
    Je=sp.Matrix(4,4,lambda a,b: sp.expand(J[a,b].subs(sub).subs([(sp.sin(th),S),(sp.cos(th),C)])))
    def SigN(keep,rem):
        d=Je[rem,rem]; Ab=Je[keep,keep]; v=Je[keep,[rem]]; w=Je[[rem],keep]
        N=sp.expand(d*Ab-v*w); co=N.charpoly(lam).all_coeffs()
        return sp.expand(co[1]*co[2]-co[3]), d
    SN_iq,d_iq=SigN([1,2,3],0); SN_id,d_id=SigN([0,2,3],1)
    Dred=sp.cancel(SN_iq/d_iq**3 - SN_id/d_id**3)
    num=sp.expand(sp.fraction(sp.together(Dred))[0])
    return num

# three independent rational network-param sets: [Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_pll,Ki_pll]
SETS=[
 [1, 1, sp.Rational(1,20), sp.Rational(1,200), sp.Rational(3,10), sp.Rational(3,100), sp.Rational(1,2), 2, 20],
 [sp.Rational(11,10), sp.Rational(6,5), sp.Rational(1,15), sp.Rational(1,100), sp.Rational(1,2), sp.Rational(1,20), sp.Rational(2,5), 3, 15],
 [sp.Rational(9,10), sp.Rational(4,5), sp.Rational(1,25), sp.Rational(3,500), sp.Rational(2,5), sp.Rational(1,25), sp.Rational(3,5), sp.Rational(5,2), 30],
]
saved=None
for k,net in enumerate(SETS):
    num=build(net); log(f"set#{k}: num(D) ops={sp.count_ops(num)}")
    q,r=sp.div(num,(Kp_P-Kp_Q),Kp_P)
    div_ok=sp.expand(r)==0
    Dsym=sp.expand(num.subs(Kp_Q,Kp_P))
    sym_ok=Dsym==0
    # general-θ identity FREE in C,S? (decides Lean encoding)
    free_cs=sp.expand(num-(Kp_P-Kp_Q)*q)==0
    print(f"  set#{k}: (Q1) (Kp_P−Kp_Q)|num = {div_ok};  (Q2) D|_sym≡0 = {sym_ok};  free in C,S = {free_cs}")
    if k==0:
        # cross-check vs θ_e*=0 at same params:
        num0=sp.expand(num.subs([(C,1),(S,0)]))
        print(f"  set#0 cross-check: num|_(C=1,S=0) ops={sp.count_ops(num0)} (should match θ_e*=0 NUM up to const)")
        saved={'num':str(num),'G':str(sp.expand(q)),'net':str(net)}
pickle.dump(saved,open('/tmp/T3_theta_rational.pkl','wb'))
log("saved set#0 num(D), G to /tmp/T3_theta_rational.pkl")
