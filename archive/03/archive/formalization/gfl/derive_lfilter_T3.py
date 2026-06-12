import sympy as sp
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
F=sp.Matrix([(u_d-Vg-Rt*i_d+Lt*wn*i_q)/Lt,(u_q-Rt*i_q-Lt*wn*i_d)/Lt,v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X)
ID=P_ref/(sp.Rational(3,2)*Vg); IQ=-Q_ref/(sp.Rational(3,2)*Vg)
sub=[(sp.cos(th),sp.Integer(1)),(sp.sin(th),sp.Integer(0)),(th,0),(eta,0),(i_d,ID),(i_q,IQ)]
Je=sp.Matrix(4,4,lambda i,j: sp.cancel(J[i,j].subs(sub)))
sm=sp.symbols('s')
def Sig(keep):
    rem=[k for k in range(4) if k not in keep]
    M=Je[keep,keep]-Je[keep,rem]*Je[rem,rem].inv()*Je[rem,keep]
    co=sp.Matrix(M).charpoly(sm).all_coeffs(); return sp.cancel(co[1]*co[2]-co[3])
D=sp.cancel(Sig([1,2,3])-Sig([0,2,3]))
num,den=sp.fraction(sp.together(D))
print("D = Σ_iq − Σ_id  factors as:\n"); sp.pprint(sp.factor(num)); print("  /\n"); sp.pprint(den)
q,r=sp.div(sp.expand(num),(Kp_P-Kp_Q),Kp_P)
print("\n(Kp_P − Kp_Q) | numerator(D):", sp.expand(r)==0)
# D at Q_ref=0, factored:
D0=sp.factor(sp.cancel(D.subs(Q_ref,0)))
print("\nD|_{Q_ref=0} =\n"); sp.pprint(D0)
# T4: symmetric case Kp_P=Kp_Q ⇒ D≡0 (all Q_ref)?
print("\nKp_P=Kp_Q  ⇒  D ≡", sp.simplify(D.subs(Kp_Q,Kp_P)), " (for all Q_ref)")
