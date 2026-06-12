#!/usr/bin/env python3
"""
VERIFY (before Lean) the tracking-error decoupling chain T1–T3.  Lossless L-filter GFL, P-only outer.
General working point (i_d,i_q free; η=0; C=cosθ_e, S=sinθ_e free).  Per rule: do not trust the text.

  T1   J13 := ∂F_iq/∂θ_e =? −(Kpi/(2Lf))·( Kp_P·C·(2P_ref−3Vg·i_d) − Kp_Q·S·(2Q_ref+3Vg·i_q) )
  T1'  with err_P=P_ref−(3/2)Vg·i_d, err_Q=Q_ref+(3/2)Vg·i_q:  J13 = −(Kpi/Lf)(Kp_P·C·err_P − Kp_Q·S·err_Q)
  T2   J03 := ∂F_id/∂θ_e — derive explicit form; check ∝ errors and =0 at err=0
  T3   at true equilibrium i_d=P_ref/(1.5Vg), i_q=−Q_ref/(1.5Vg) (err=0):  J13=0 and J03=0
"""
import sympy as sp
Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,Kp_Q,P_ref=sp.symbols('Vg wn Lf Lg Kpi Kp_pll Ki_pll Kp_P Kp_Q P_ref',positive=True)
Q_ref=sp.Symbol('Q_ref',real=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
Lt=Lf+Lg; c,s=sp.cos(th),sp.sin(th)
err_P=P_ref-sp.Rational(3,2)*Vg*i_d; err_Q=Q_ref+sp.Rational(3,2)*Vg*i_q
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
err_d=Kp_P*err_P-i_dc; err_q=-Kp_Q*err_Q-i_qc
u_dc=(Lt/Lf)*(Kpi*err_d-wn*Lf*i_qc+(Lf/Lt)*c*Vg)
u_qc=(Lt/Lf)*(Kpi*err_q+wn*Lf*i_dc+(Lf/Lt)*s*Vg)
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
vPCCd=(Lg/Lt)*u_d+(Lf/Lt)*Vg; vPCCq=(Lg/Lt)*u_q; v_cqc=s*vPCCd+c*vPCCq
F=sp.Matrix([(u_d-Vg+Lt*wn*i_q)/Lt,(u_q-Lt*wn*i_d)/Lt,v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X)
C,S=sp.symbols('C S',real=True)
def at(e): return sp.cancel(e.subs(eta,0).subs([(sp.sin(th),S),(sp.cos(th),C)]))
J13=at(J[1,3]); J03=at(J[0,3])

# T1
T1rhs=-(Kpi/(2*Lf))*(Kp_P*C*(2*P_ref-3*Vg*i_d)-Kp_Q*S*(2*Q_ref+3*Vg*i_q))
print("T1  J13 = claimed formula ? :", sp.simplify(J13-T1rhs)==0)
print("    J13 =", sp.factor(J13))
# T1'
eP,eQ=P_ref-sp.Rational(3,2)*Vg*i_d, Q_ref+sp.Rational(3,2)*Vg*i_q
T1prhs=-(Kpi/Lf)*(Kp_P*C*eP-Kp_Q*S*eQ)
print("T1' J13 = −(Kpi/Lf)(Kp_P·C·err_P − Kp_Q·S·err_Q) ? :", sp.simplify(J13-T1prhs)==0)

# T2 : derive J03 explicitly, test err-form
print("\nT2  J03 = ∂F_id/∂θ_e =", sp.factor(J03))
# conjecture symmetric err-form: J03 = (Kpi/Lf)(Kp_P·S·err_P + Kp_Q·C·err_Q) ? try, else report
for name,cand in [("(Kpi/Lf)(Kp_P·S·err_P + Kp_Q·C·err_Q)", (Kpi/Lf)*(Kp_P*S*eP+Kp_Q*C*eQ)),
                  ("−(Kpi/Lf)(Kp_P·S·err_P + Kp_Q·C·err_Q)", -(Kpi/Lf)*(Kp_P*S*eP+Kp_Q*C*eQ)),
                  ("(Kpi/Lf)(Kp_P·S·err_P − Kp_Q·C·err_Q)", (Kpi/Lf)*(Kp_P*S*eP-Kp_Q*C*eQ))]:
    if sp.simplify(J03-cand)==0: print("    J03 matches:", name)

# does J03 vanish at err=0?  substitute equilibrium:
EQ=[(i_d,P_ref/(sp.Rational(3,2)*Vg)),(i_q,-Q_ref/(sp.Rational(3,2)*Vg))]
print("\nT3  J13|_eq =", sp.simplify(J13.subs(EQ)), "   J03|_eq =", sp.simplify(J03.subs(EQ)))
print("    (err_P|_eq, err_Q|_eq) =", sp.simplify(eP.subs(EQ)), sp.simplify(eQ.subs(EQ)))
