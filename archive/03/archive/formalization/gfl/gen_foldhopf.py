#!/usr/bin/env python3
"""Reduce Σ, Φ, Ψ mod C²+S²=1 → clean low-degree forms; verify reduced identity; emit for Lean."""
import sympy as sp
Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,P_ref=sp.symbols('Vg wn Lf Lg Kpi Kp_pll Ki_pll Kp_P P_ref',positive=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
Lt=Lf+Lg; c,s=sp.cos(th),sp.sin(th)
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
err_d=Kp_P*(P_ref-sp.Rational(3,2)*Vg*i_d)-i_dc
err_q=-Kp_P*(sp.Rational(3,2)*Vg*i_q)-i_qc
u_dc=(Lt/Lf)*(Kpi*err_d-wn*Lf*i_qc+(Lf/Lt)*c*Vg); u_qc=(Lt/Lf)*(Kpi*err_q+wn*Lf*i_dc+(Lf/Lt)*s*Vg)
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
vPCCd=(Lg/Lt)*u_d+(Lf/Lt)*Vg; vPCCq=(Lg/Lt)*u_q; v_cqc=s*vPCCd+c*vPCCq
F=sp.Matrix([(u_d-Vg+Lt*wn*i_q)/Lt,(u_q-Lt*wn*i_d)/Lt,v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X); ID=P_ref/(sp.Rational(3,2)*Vg)
C,S=sp.symbols('C S',real=True); sub=[(i_d,ID),(i_q,0),(eta,0)]
Je=sp.Matrix(4,4,lambda a,b: sp.cancel(J[a,b].subs(sub).subs([(sp.sin(th),S),(sp.cos(th),C)])))
M=Je[[1,2,3],[1,2,3]]
a1=sp.cancel(-(M[0,0]+M[1,1]+M[2,2]))
a2=sp.cancel((M[0,0]*M[1,1]-M[0,1]*M[1,0])+(M[0,0]*M[2,2]-M[0,2]*M[2,0])+(M[1,1]*M[2,2]-M[1,2]*M[2,1]))
a3=sp.cancel(-M.det()); Sig=sp.cancel(a1*a2-a3); det3=sp.cancel(M.det())

def red(e):  # reduce mod C²+S²=1 (eliminate S² → 1−C²), giving form linear in S
    n,d=sp.fraction(sp.together(e))
    n=sp.rem(sp.Poly(sp.expand(n),S),sp.Poly(S**2-(1-C**2),S)).as_expr()
    return sp.cancel(n/d)

g_th=red(Je[2,3])
print("g_θ (mod C²+S²=1) ="); sp.pprint(sp.factor(g_th))
# fold factor Φ from det:  det = Ki_pll·Kpi·(quad)·Φ /(6Lf²Vg(Lf+Lg)); take the non-quadratic factor
detf=sp.factor(det3); print("\ndet(M_3D^q) factored:"); sp.pprint(detf)
Phi=sp.factor(red(2*Lg*P_ref*(C*Kpi+Lf*S*wn)-3*C*Lf*Vg**2))   # conjectured clean fold (from hand calc)
print("\nΦ (clean fold, mod constraint) := 2·Lg·P_ref·(C·Kpi+Lf·S·wn) − 3·C·Lf·Vg² ="); sp.pprint(Phi)

# Ψ := (Σ·36Lf³Vg²)/(Kp_pll·Φ_full) ; reduce
Sig36=sp.cancel(Sig*36*Lf**3*Vg**2)
# full Φ (degree-3) = (Lf+Lg)*Phi  (verify divides):
Phi_full=sp.expand((Lf+Lg)*(2*Lg*P_ref*(C*Kpi+Lf*S*wn)-3*C*Lf*Vg**2))
q,r=sp.div(sp.expand(sp.numer(sp.together(Sig36))), sp.expand(Kp_pll*Phi_full), C)
print("\n(Σ·36Lf³Vg²) numerator divisible by Kp_pll·(Lf+Lg)·Φ ? remainder=0 :", sp.expand(r)==0)
Psi=sp.cancel(Sig36/(Kp_pll*Phi_full))
Psi_red=red(Psi)
print("\nΨ (mod C²+S²=1), factored:"); sp.pprint(sp.factor(Psi_red))
# verify reduced identity:
lhs=red(Sig*36*Lf**3*Vg**2); rhs=red(Kp_pll*Phi_full*Psi_red)
print("\nVERIFY  Σ·36Lf³Vg² = Kp_pll·(Lf+Lg)·Φ·Ψ  (mod C²+S²=1) :", sp.simplify(red(lhs-rhs))==0)
# (c) current pole, reduced:
cp=red(a1-Kp_pll*g_th)
print("\n(c) a1(3D)−a1(2D) (mod constraint) ="); sp.pprint(sp.factor(cp))
