#!/usr/bin/env python3
"""Extract the FULL 4×4 Jacobian (general working point, η=0, C,S free) and verify the block shape:
   top-right (current rows × (η,θ_e) cols) = [[0, J03],[0, J13]];  bottom-right = Dpll(gθ,Ki_pll,Kp_pll).
   Print A (current), B (PLL↔current) blocks for the Lean assembly."""
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
Je=sp.Matrix(4,4,lambda a,b: sp.cancel(J[a,b].subs(eta,0).subs([(sp.sin(th),S),(sp.cos(th),C)])))
# rows/cols: 0=i_d,1=i_q,2=η,3=θ_e
print("== top-right block (rows i_d,i_q × cols η,θ_e) ==")
print(" J02 ∂F_id/∂η =",Je[0,2],"   J03 ∂F_id/∂θ =",sp.factor(Je[0,3]))
print(" J12 ∂F_iq/∂η =",Je[1,2],"   J13 ∂F_iq/∂θ =",sp.factor(Je[1,3]))
print("== bottom-right block (rows η,θ_e × cols η,θ_e) — should be Dpll ==")
gth=Je[2,3]
print(" J22 ∂F_η/∂η =",Je[2,2]," J23 ∂F_η/∂θ = gθ =",sp.factor(gth))
print(" J32 ∂F_θ/∂η =",Je[3,2]," J33 ∂F_θ/∂θ =",sp.factor(Je[3,3]))
print(" D = Dpll(gθ,Ki_pll,Kp_pll)? :", Je[2,2]==0 and sp.simplify(Je[3,2]+Ki_pll)==0
      and sp.simplify(Je[3,3]+Kp_pll*gth)==0)
print("== bottom-left block B (rows η,θ_e × cols i_d,i_q) ==")
print(" J20 ∂F_η/∂i_d =",sp.factor(Je[2,0])); print(" J21 ∂F_η/∂i_q =",sp.factor(Je[2,1]))
print(" J30 ∂F_θ/∂i_d =",sp.factor(Je[3,0])); print(" J31 ∂F_θ/∂i_q =",sp.factor(Je[3,1]))
print(" B row2 = -Kp_pll·(B row1)? :", sp.simplify(Je[3,0]+Kp_pll*Je[2,0])==0 and sp.simplify(Je[3,1]+Kp_pll*Je[2,1])==0)
print("== top-left block A (current 2×2) ==")
for (a,b) in [(0,0),(0,1),(1,0),(1,1)]: print(f" J{a}{b} =",sp.factor(Je[a,b]))
