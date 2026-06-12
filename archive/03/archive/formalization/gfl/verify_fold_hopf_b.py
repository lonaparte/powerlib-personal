#!/usr/bin/env python3
"""(b)+(c) focused, Q_ref=0 (the M_3D^q-anchored case), lossless.  Fast: direct tr/det, cancel only."""
import sympy as sp
Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,P_ref=sp.symbols('Vg wn Lf Lg Kpi Kp_pll Ki_pll Kp_P P_ref',positive=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
Lt=Lf+Lg; c,s=sp.cos(th),sp.sin(th)
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
err_d=Kp_P*(P_ref-sp.Rational(3,2)*Vg*i_d)-i_dc
err_q=-Kp_P*(0-(-sp.Rational(3,2)*Vg*i_q))-i_qc          # Q_ref=0 ; Kp_Q irrelevant (i_q*=0)
err_q=-Kp_P*(sp.Rational(3,2)*Vg*i_q)-i_qc
u_dc=(Lt/Lf)*(Kpi*err_d-wn*Lf*i_qc+(Lf/Lt)*c*Vg)
u_qc=(Lt/Lf)*(Kpi*err_q+wn*Lf*i_dc+(Lf/Lt)*s*Vg)
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
vPCCd=(Lg/Lt)*u_d+(Lf/Lt)*Vg; vPCCq=(Lg/Lt)*u_q
v_cqc=s*vPCCd+c*vPCCq
F=sp.Matrix([(u_d-Vg+Lt*wn*i_q)/Lt,(u_q-Lt*wn*i_d)/Lt,v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X)
ID=P_ref/(sp.Rational(3,2)*Vg)
C,S=sp.symbols('C S',real=True)
sub=[(i_d,ID),(i_q,0),(eta,0)]
Je=sp.Matrix(4,4,lambda a,b: sp.cancel(J[a,b].subs(sub).subs([(sp.sin(th),S),(sp.cos(th),C)])))

# M_3D^q = rows/cols (i_q,η,θ_e) = indices 1,2,3
M=Je[[1,2,3],[1,2,3]]
a1=sp.cancel(-(M[0,0]+M[1,1]+M[2,2]))
minors=(M[0,0]*M[1,1]-M[0,1]*M[1,0])+(M[0,0]*M[2,2]-M[0,2]*M[2,0])+(M[1,1]*M[2,2]-M[1,2]*M[2,1])
a2=sp.cancel(minors); a3=sp.cancel(-M.det())
Sig=sp.cancel(a1*a2-a3)
det3=sp.cancel(M.det())
print("a3 = -det ? :",sp.simplify(a3+det3)==0)
print("\nfold Φ := det(M_3D^q) (×const), factored:"); sp.pprint(sp.factor(det3))
Snum=sp.factor(sp.expand(Sig*36*Lf**3*Vg**2))
print("\nΣ·36Lf³Vg²  factored:"); sp.pprint(Snum)
# divide by det-factor to expose Ψ:
print("\nΣ / det  (cancel) :"); sp.pprint(sp.cancel(Sig/det3))
print("\n(c) current pole:")
print(" a1(3D) =",sp.cancel(a1))
g_th=sp.cancel(Je[2,3]); print(" Kp_pll·g_θ (=a1 of 2D) =",sp.cancel(Kp_pll*g_th))
print(" a1(3D) − Kp_pll·g_θ = −J11 =",sp.cancel(a1-Kp_pll*g_th)," (current pole ∂F_iq/∂i_q)")
