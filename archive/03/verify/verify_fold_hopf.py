#!/usr/bin/env python3
"""
VERIFY (before any Lean) the lossless fold/Hopf-separation problem.  Per rule: do not trust the text.
Lossless L-filter GFL (Rf=Rg=0 ⇒ Rt=0,γ=0), P-only outer.  C=cosθ_e*, S=sinθ_e* FREE symbols.

Checks:
  G1  guard (genuine equilibrium of each (A) submodel): retained-state RHS = 0 at the work point.
  (a) M_2D charpoly = λ² + (Kp_pll·g_θ)λ + (Ki_pll·g_θ),  g_θ = ∂v_cqc/∂θ_e.
  (b) M_3D^q charpoly s³+a₁s²+a₂s+a₃;  Σ := a₁a₂−a₃ = Kp_pll·Φ·Ψ / (36 Lf³ Vg²);  Φ ∝ fold(det), Ψ⊥Φ.
  (c) a₁(3D) has a g_θ-independent current-pole term Kpi/Lf;  a₁(2D)=Kp_pll·g_θ does not.
Plus numeric: lossless Q_ref=0 ⇒ M_3D^q true equilibrium i_q*=0, θ_e*≈−1.466, residual<1e-13.
"""
import sympy as sp, numpy as np
from scipy.optimize import fsolve
Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,Kp_Q,P_ref=sp.symbols(
 'Vg wn Lf Lg Kpi Kp_pll Ki_pll Kp_P Kp_Q P_ref',positive=True)
Q_ref=sp.Symbol('Q_ref',real=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
Lt=Lf+Lg; c,s=sp.cos(th),sp.sin(th)              # lossless: Rt=0, γ=0
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
err_d=Kp_P*(P_ref-sp.Rational(3,2)*Vg*i_d)-i_dc
err_q=-Kp_Q*(Q_ref+sp.Rational(3,2)*Vg*i_q)-i_qc
u_dc=(Lt/Lf)*(Kpi*err_d-wn*Lf*i_qc+(Lf/Lt)*c*Vg)
u_qc=(Lt/Lf)*(Kpi*err_q+wn*Lf*i_dc+(Lf/Lt)*s*Vg)
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
vPCCd=(Lg/Lt)*u_d+(Lf/Lt)*Vg; vPCCq=(Lg/Lt)*u_q
v_cqc=s*vPCCd+c*vPCCq
F=sp.Matrix([(u_d-Vg+Lt*wn*i_q)/Lt,(u_q-Lt*wn*i_d)/Lt,v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X)
ID=P_ref/(sp.Rational(3,2)*Vg); IQ=-Q_ref/(sp.Rational(3,2)*Vg)
C,S=sp.symbols('C S',real=True)
subEq=[(i_d,ID),(i_q,IQ),(eta,0)]
def at_eq(e): return sp.simplify(sp.expand_trig(e).subs(subEq).subs([(sp.sin(th),S),(sp.cos(th),C)]))
Fe=[at_eq(F[k]) for k in range(4)]
Je=sp.Matrix(4,4,lambda a,b: at_eq(J[a,b]))

print("== GUARD G1 (retained-state RHS at work point) ==")
print(" i_d RHS* =",sp.simplify(Fe[0]),"   (M_3D^d keep-i_d: must be 0)")
print(" i_q RHS* =",sp.simplify(Fe[1].subs(Q_ref,0)),"  at Q_ref=0   (M_3D^q keep-i_q: must be 0)")
print(" η  RHS* =",sp.simplify(Fe[2]),"   θ_e RHS*(η=0) =",sp.simplify(Fe[3]),"   (need v_cqc=0 ⇒ defines θ_e*)")

lam=sp.symbols('lam')
def charpoly(idx):
    M=Je[idx,idx]; return sp.Matrix(M).charpoly(lam).all_coeffs(), M

print("\n== (a) M_2D (η,θ_e) ==")
co2,M2=charpoly([2,3]); g_th=sp.simplify(Je[2,3])
print(" g_θ = ∂v_cqc/∂θ_e =",g_th)
print(" charpoly =",[sp.simplify(x) for x in co2])
print(" matches λ²+Kp_pll·g_θ·λ+Ki_pll·g_θ ? :",
      sp.simplify(co2[1]-Kp_pll*g_th)==0 and sp.simplify(co2[2]-Ki_pll*g_th)==0)

print("\n== (b) M_3D^q (i_q,η,θ_e) ==")
co3,M3=charpoly([1,2,3]); a1,a2,a3=[sp.simplify(x) for x in co3[1:]]
Sig=sp.simplify(a1*a2-a3)
det3=sp.simplify(M3.det())            # fold ⟺ det=0 ⟺ a3=0
print(" a1 =",a1)
print(" a3 = -det? :",sp.simplify(a3+det3)==0,"   det(M_3D^q) =",sp.factor(det3))
SigN=sp.factor(sp.together(Sig))
print(" Σ = a1a2−a3 factored:"); sp.pprint(SigN)
# extract Φ (fold ∝ det) and Ψ : divide Σ·36Lf³Vg²/Kp_pll by Φ:=det-factor
print(" Σ·36Lf³Vg² =",sp.factor(sp.expand(Sig*36*Lf**3*Vg**2)))

print("\n== (c) current-pole term ==")
print(" a1(3D) =",a1)
print(" a1(2D) = Kp_pll·g_θ =",sp.simplify(co2[1]))
print(" a1(3D) − a1(2D) =",sp.simplify(a1-co2[1]),"  (should expose Kpi/Lf current pole)")

print("\n== numeric guard: lossless Q_ref=0 true equilibrium of M_3D^q ==")
pv={Vg:1.0,wn:1.0,Lf:0.05,Lg:0.6,Kpi:0.5,Kp_pll:2.0,Ki_pll:20.0,Kp_P:0.02,Kp_Q:0.02,P_ref:0.8,Q_ref:0.0}
# M_3D^q states (i_q,η,θ_e) with i_d=ID fixed; solve retained RHS=0
IDn=float(pv[P_ref]/(1.5*pv[Vg]))
g3=sp.lambdify((i_q,eta,th),[F[1].subs({i_d:ID}).subs(pv),F[2].subs({i_d:ID}).subs(pv),
                             F[3].subs({i_d:ID}).subs(pv)],'numpy')
solq=fsolve(lambda y:np.array(g3(*y),float),[0.0,0.0,-1.4],full_output=True)
yq=solq[0]; resq=np.max(np.abs(np.array(g3(*yq),float)))
print(f" M_3D^q eq: i_q*={yq[0]:.2e}, η*={yq[1]:.2e}, θ_e*={yq[2]:.4f} rad ({np.degrees(yq[2]):.1f}°), res={resq:.1e}")
