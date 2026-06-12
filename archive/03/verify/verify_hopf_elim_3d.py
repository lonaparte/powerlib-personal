#!/usr/bin/env python3
"""Reproduce the 3D keep-i_d (Schur-eliminate i_q) Hopf-boundary elimination for the lossless GFL
surrogate, and cross-validate that p3's positive root is a GENUINE Hopf of the 3D Schur model.
Mirrors verify_hopf_elim.py (4D).  Independent of the embedded Lean coefficients."""
import sympy as sp, numpy as np
from scipy.optimize import fsolve
i_d,i_q,eta,c,s,Lg,T=sp.symbols('i_d i_q eta c s Lg T')
Vg=sp.Rational(3103,10); wn=sp.Rational(314159,1000); Lf=sp.Rational(1,1000)
Kpi=sp.Rational(126,100); Kp_pll=sp.Rational(573,1000); Ki_pll=sp.Rational(509,10)
Kp_P=sp.Rational(215,1000000); Kp_Q=Kp_P; P_ref=sp.Integer(37200)
Lt=Lf+Lg
eP=P_ref-sp.Rational(3,2)*Vg*i_d; eQ=sp.Rational(3,2)*Vg*i_q
idc=c*i_d-s*i_q; iqc=s*i_d+c*i_q; ed=Kp_P*eP-idc; eq=-Kp_Q*eQ-iqc
udc=(Lt/Lf)*(Kpi*ed-wn*Lf*iqc+(Lf/Lt)*c*Vg); uqc=(Lt/Lf)*(Kpi*eq+wn*Lf*idc+(Lf/Lt)*s*Vg)
ud=c*udc+s*uqc; uq=-s*udc+c*uqc
vPCCd=(Lg/Lt)*ud+(Lf/Lt)*Vg; vPCCq=(Lg/Lt)*uq; vcq=s*vPCCd+c*vPCCq
F=[(ud-Vg+Lt*wn*i_q)/Lt,(uq-Lt*wn*i_d)/Lt,vcq,-Kp_pll*vcq-Ki_pll*eta]
def col(v): return [sp.diff(Fk,v) for Fk in F]
cid,ciq,cet=col(i_d),col(i_q),col(eta); cth=[sp.diff(Fk,c)*(-s)+sp.diff(Fk,s)*c for Fk in F]
J=sp.Matrix([[cid[k],ciq[k],cet[k],cth[k]] for k in range(4)])
drop=1; keep=[0,2,3]
A=J[drop,drop]; B=J[drop,keep]; Cc=J[keep,drop]; Dd=J[keep,keep]; J3=Dd-(Cc*B)/A
sol=sp.solve([F[0],F[1]],[i_d,i_q],dict=True)[0]
co=J3.charpoly(sp.Symbol('lam')).all_coeffs(); a1,a2,a3=[sp.cancel(x.subs(sol)) for x in co[1:4]]
chi3=sp.cancel(a1*a2-a3); G=sp.cancel(F[2].subs(sol))
w={c:(1-T**2)/(1+T**2),s:2*T/(1+T**2)}
Gt=sp.expand(sp.numer(sp.cancel(G.subs(w)))); Xt=sp.expand(sp.numer(sp.cancel(chi3.subs(w))))
pe=sp.Poly(sp.expand(sp.numer(sp.cancel(sp.resultant(Gt,Xt,T)))),Lg)
m=0
while pe.coeff_monomial(1)==0: pe=sp.Poly(sp.cancel(pe.as_expr()/Lg),Lg); m+=1
roots=[float(r) for r in sp.real_roots(pe) if 0<r<1]
print(f"eliminated: raw deg {pe.degree()+m} (= Lg^{m}·p3), p3 deg {pe.degree()}, pos roots {roots}")
# cross-validate genuine Hopf
Fn=sp.lambdify((i_d,i_q,eta,sp.Symbol('th'),Lg),[Fk.subs({c:sp.cos(sp.Symbol('th')),s:sp.sin(sp.Symbol('th'))}) for Fk in F])
Jn=sp.lambdify((i_d,i_q,eta,sp.Symbol('th'),Lg),J.subs({c:sp.cos(sp.Symbol('th')),s:sp.sin(sp.Symbol('th'))}))
r=roots[0]; y=fsolve(lambda z:np.array(Fn(*z,r),float).ravel(),[80,0,0,-0.1],xtol=1e-13)
J4=np.array(Jn(*y,r),float); k=[0,2,3]; AA=J4[1,1]; BB=J4[1,k]; CC=J4[k,1]; DD=J4[np.ix_(k,k)]
J3n=DD-np.outer(CC,BB)/AA; ev=np.linalg.eigvals(J3n); ai=np.poly(J3n)[1:]
osc=[e for e in ev if abs(e.imag)>1e-3]; lc=max(osc,key=lambda e:e.real)
SCR=380.0**2/(1e5*r*314.159)
print(f"cross-val at root {r:.6f}: Schur J3 osc λ={np.round(lc,3)} (Re≈0), all_aᵢ>0={all(x>0 for x in ai)}, SCR≈{SCR:.4f}")
print("PASS: p3 root = genuine 3D Hopf" if abs(lc.real)<1e-1 and all(x>0 for x in ai) else "CHECK")
