#!/usr/bin/env python3
"""Extract EXACT free-(C,S) polynomials for the Lean fold/Hopf theorems and verify, then format."""
import sympy as sp, pickle
Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,P_ref=sp.symbols('Vg wn Lf Lg Kpi Kp_pll Ki_pll Kp_P P_ref',positive=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
Lt=Lf+Lg; c,s=sp.cos(th),sp.sin(th)
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
err_d=Kp_P*(P_ref-sp.Rational(3,2)*Vg*i_d)-i_dc; err_q=-Kp_P*(sp.Rational(3,2)*Vg*i_q)-i_qc
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
a3=sp.cancel(-M.det()); Sig=sp.cancel(a1*a2-a3)
num,den=sp.fraction(sp.together(Sig)); num=sp.expand(num)
print("den(Σ) =",sp.factor(den))
fl=sp.factor_list(num)
print("num(Σ) factor_list signs/consts:",fl[0],"; #factors:",len(fl[1]))
for base,e in fl[1]:
    print("  factor^%d, deg_C=%d deg_S=%d, #terms=%d :"%(e,sp.degree(base,C),sp.degree(base,S),
          len(sp.Poly(base,C,S).terms()) if base.free_symbols&{C,S} else 1), sp.factor(base) if sp.count_ops(base)<12 else "(big)")
# factor_list gives [Kp_pll, Φ_full(deg3), Ψ_full(deg5)]; sort by total C,S degree
facs=sorted([base**e for base,e in fl[1]], key=lambda b: sp.degree(b,C)+sp.degree(b,S))
Kpf,Phi,Psi=facs[0],facs[1],facs[2]
assert sp.expand(Kpf-Kp_pll)==0, ("first factor not Kp_pll", Kpf)
print("\nVERIFY num = Kp_pll·Φ_full·Ψ_full ? :", sp.expand(num-Kp_pll*Phi*Psi)==0)
# is Φ_full the FOLD factor (divides det)?
det3=sp.cancel(M.det()); dn=sp.numer(sp.together(det3))
print("Φ_full | det(M_3D^q) (⇒ Φ=fold) ? :", sp.rem(sp.expand(dn),sp.expand(Phi),C)==0
      if (Phi.free_symbols&{C}) else "n/a")
# g_θ = −Φ_clean/(3Lf Vg);  Σ ∝ Φ_full·Ψ_full ; fold shared with 2D (g_θ=0)
g_th=sp.cancel(Je[2,3]); cp=sp.cancel(a1-Kp_pll*g_th)
print("\n(c) a1(3D)−a1(2D) = ",sp.factor(cp))
print("    g_θ = ",sp.factor(g_th))
pickle.dump({'a1':str(a1),'a2':str(a2),'a3':str(a3),'Phi':str(sp.expand(Phi)),
             'Psi':str(sp.expand(Psi)),'den':str(den),'g_th':str(g_th),'cp':str(cp)},
            open('/tmp/foldhopf.pkl','wb'))
print("\nΦ_full =",sp.expand(Phi))
print("\nΨ_full =",sp.expand(Psi))
print("\nsizes: Φ #terms",len(sp.Poly(sp.expand(Phi),C,S,Vg,wn,Lf,Lg,Kpi,Kp_P,P_ref).terms()),
      " Ψ #terms",len(sp.Poly(sp.expand(Psi),C,S,Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,P_ref).terms()))
print("saved /tmp/foldhopf.pkl")
