#!/usr/bin/env python3
"""Emit Lean-formatted polynomials (sigma_diff_factor style: coeffs (N:ℝ), bare-ℕ exponents) for the
fold/Hopf theorems, and VERIFY each identity in sympy before emitting."""
import sympy as sp
Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,P_ref=sp.symbols('Vg wn Lf Lg Kpi Kp_pll Ki_pll Kp_P P_ref',positive=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
Lt=Lf+Lg; c,s=sp.cos(th),sp.sin(th)
err_d=Kp_P*(P_ref-sp.Rational(3,2)*Vg*i_d)-(c*i_d-s*i_q); err_q=-Kp_P*(sp.Rational(3,2)*Vg*i_q)-(s*i_d+c*i_q)
u_dc=(Lt/Lf)*(Kpi*err_d-wn*Lf*(s*i_d+c*i_q)+(Lf/Lt)*c*Vg); u_qc=(Lt/Lf)*(Kpi*err_q+wn*Lf*(c*i_d-s*i_q)+(Lf/Lt)*s*Vg)
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
vPCCd=(Lg/Lt)*u_d+(Lf/Lt)*Vg; vPCCq=(Lg/Lt)*u_q; v_cqc=s*vPCCd+c*vPCCq
F=sp.Matrix([(u_d-Vg+Lt*wn*i_q)/Lt,(u_q-Lt*wn*i_d)/Lt,v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X); ID=P_ref/(sp.Rational(3,2)*Vg)
C,S=sp.symbols('C S',real=True); sub=[(i_d,ID),(i_q,0),(eta,0)]
Je=sp.Matrix(4,4,lambda a,b: sp.cancel(J[a,b].subs(sub).subs([(sp.sin(th),S),(sp.cos(th),C)])))
M=Je[[1,2,3],[1,2,3]]
a1=sp.cancel(-(M[0,0]+M[1,1]+M[2,2]))
a2=sp.cancel((M[0,0]*M[1,1]-M[0,1]*M[1,0])+(M[0,0]*M[2,2]-M[0,2]*M[2,0])+(M[1,1]*M[2,2]-M[1,2]*M[2,1]))
a3=sp.cancel(-M.det()); Sig=sp.cancel(a1*a2-a3)
num,den=sp.fraction(sp.together(Sig)); num=sp.expand(num)
facs=sorted([b**e for b,e in sp.factor_list(num)[1]],key=lambda b:sp.degree(b,C)+sp.degree(b,S))
Phi,Psi=facs[1],facs[2]
det3=sp.cancel(M.det()); dnum,dden=sp.fraction(sp.together(det3)); dnum=sp.expand(dnum)
quad=2*C**2+3*C*Kp_P*Vg+2*S**2
g_th=sp.cancel(Je[2,3])

VARS=[C,S,Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,P_ref]
def lean(expr):
    P=sp.Poly(sp.expand(expr),*VARS); out=[]
    for mon,co in sorted(P.terms(),key=lambda t:(-sum(t[0]),t[0])):
        co=sp.nsimplify(co); sign='-' if co<0 else '+'
        if co.is_Integer: cs=f"({abs(int(co))}:ℝ)"
        else: p,q=sp.fraction(abs(co)); cs=f"(({int(p)}:ℝ)/({int(q)}:ℝ))"
        parts=[cs]+[f"{v}^{e}" if e>1 else f"{v}" for v,e in zip(VARS,mon) if e>0]
        out.append((sign,'*'.join(parts)))
    if not out: return "(0:ℝ)"
    r=("- " if out[0][0]=='-' else "")+out[0][1]
    for sg,t in out[1:]: r+=f" {sg} {t}"
    return r

# VERIFY identities
print("num = Kp_pll·Φ·Ψ :", sp.expand(num-Kp_pll*Phi*Psi)==0)
print("detNum = Ki_pll·Kpi·quad·Φ :", sp.expand(dnum-Ki_pll*Kpi*quad*Phi)==0, " (else find const)")
k=sp.cancel(dnum/(Ki_pll*Kpi*quad*Phi)); print("  detNum/(Ki_pll·Kpi·quad·Φ) =",k)
cp=sp.cancel(a1-Kp_pll*g_th); print("a1−Kp_pll·gθ = Kpi·quad/(2Lf) :", sp.cancel(cp-Kpi*quad/(2*Lf))==0)

open('/tmp/foldhopf_lean.txt','w').write(
 "PHI:=\n"+lean(Phi)+"\n\nPSI:=\n"+lean(Psi)+"\n\nNUM:=\n"+lean(num)+
 "\n\nDETNUM:=\n"+lean(dnum)+"\n\nQUAD:=\n"+lean(quad)+
 "\n\nDETCOFACTOR(=detNum/Φ):=\n"+lean(sp.expand(Ki_pll*Kpi*quad))+"\n")
print("\nwrote /tmp/foldhopf_lean.txt ; Φ terms",len(sp.Poly(Phi,*VARS).terms()),
      "Ψ",len(sp.Poly(Psi,*VARS).terms()),"num",len(sp.Poly(num,*VARS).terms()),
      "detNum",len(sp.Poly(dnum,*VARS).terms()))
