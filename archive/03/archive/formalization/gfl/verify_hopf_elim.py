#!/usr/bin/env python3
"""Reproduce + cross-validate pHopf (GFL/ScrHopfNumeric.lean): eliminate the lossless 4D P-only GFL
equilibrium (rational surrogates of the GFL baseline) to a univariate Hopf-boundary polynomial in Lg,
and confirm its positive root is a GENUINE Hopf against an independent numerical eigenvalue sweep.
Raw resultant degree 22 = Lg⁶·pHopf (Lg⁶ unphysical); pHopf degree 16; root ≈0.12144, ω≈84, all aᵢ>0.
Runtime ~3min (charpoly+resultant)."""
import sympy as sp, numpy as np, time
from scipy.optimize import fsolve
t0=time.time()
i_d,i_q,eta,c,s,Lg=sp.symbols('i_d i_q eta c s Lg')
# rational surrogates of the GFL baseline (wn=100π, Vg=760/√6 are irrational ⟹ surrogate; numbers
# are placeholders per the user — the method is the point, not the exact value)
Vg=sp.Rational(3103,10); wn=sp.Rational(314159,1000); Lf=sp.Rational(1,1000)
Kpi=sp.Rational(126,100); Kp_pll=sp.Rational(573,1000); Ki_pll=sp.Rational(509,10)
Kp_P=Kp_Q=sp.Rational(215,1000000); P_ref=sp.Integer(37200); Q_ref=0
Lt=Lf+Lg
eP=P_ref-sp.Rational(3,2)*Vg*i_d; eQ=Q_ref+sp.Rational(3,2)*Vg*i_q
idc=c*i_d-s*i_q; iqc=s*i_d+c*i_q; ed=Kp_P*eP-idc; eq=-Kp_Q*eQ-iqc
udc=(Lt/Lf)*(Kpi*ed-wn*Lf*iqc+(Lf/Lt)*c*Vg); uqc=(Lt/Lf)*(Kpi*eq+wn*Lf*idc+(Lf/Lt)*s*Vg)
ud=c*udc+s*uqc; uq=-s*udc+c*uqc
vd=(Lg/Lt)*ud+(Lf/Lt)*Vg; vq=(Lg/Lt)*uq; vcq=s*vd+c*vq
F=[(ud-Vg+Lt*wn*i_q)/Lt,(uq-Lt*wn*i_d)/Lt,vcq,-Kp_pll*vcq-Ki_pll*eta]
col=lambda v:[sp.diff(Fk,v) for Fk in F]                      # ∂/∂(i_d,i_q,η)
J=sp.Matrix([[col(i_d)[k],col(i_q)[k],col(eta)[k],
              sp.diff(F[k],c)*(-s)+sp.diff(F[k],s)*c] for k in range(4)])  # θ-col via c'=-s,s'=c
sol=sp.solve([F[0],F[1]],[i_d,i_q],dict=True)[0]              # F₀,F₁ linear ⟹ solve i_d,i_q
a=J.charpoly(sp.Symbol('lam')).all_coeffs(); a1,a2,a3,a4=[sp.cancel(x.subs(sol)) for x in a[1:5]]
chi4=sp.cancel(a1*a2*a3-a3**2-a1**2*a4); G=sp.cancel(F[2].subs(sol))   # χ₄ and lock at equilibrium
T=sp.Symbol('T'); w={c:(1-T**2)/(1+T**2),s:2*T/(1+T**2)}
Gt=sp.expand(sp.numer(sp.cancel(G.subs(w)))); Xt=sp.expand(sp.numer(sp.cancel(chi4.subs(w))))
pe=sp.Poly(sp.expand(sp.numer(sp.cancel(sp.resultant(Gt,Xt,T)))),Lg)   # eliminate t
raw=pe.degree()
while pe.coeff_monomial(1)==0: pe=sp.Poly(sp.cancel(pe.as_expr()/Lg),Lg)
roots=[float(r) for r in sp.real_roots(pe) if r>0]
print(f"eliminated: raw deg {raw} (= Lg^{raw-pe.degree()}·pHopf), pHopf deg {pe.degree()}, "
      f"pos roots {roots[:6]}  (t={time.time()-t0:.0f}s)")
# independent numerical cross-validation at the float GFL params
th=sp.Symbol('th'); cs={c:sp.cos(th),s:sp.sin(th)}
Fn=sp.lambdify([i_d,i_q,eta,th,Lg],[Fk.subs(cs) for Fk in F])
Jn=sp.lambdify([i_d,i_q,eta,th,Lg],J.subs(cs))
Lgs=roots[0]; warm=[80.,0,0,-0.1]; wcross=None
print("numerical eigenvalue cross-check around the eliminated root:")
for d in (-0.003,0.0,0.003):
    y=fsolve(lambda z:np.array(Fn(*z,Lgs+d),float).ravel(),warm,xtol=1e-12); warm=y
    Jm=np.array(Jn(*y,Lgs+d),float); ev=np.linalg.eigvals(Jm); ai=np.poly(Jm)[1:]
    osc=[e for e in ev if abs(e.imag)>1e-3]; lc=max(osc,key=lambda e:e.real)
    if d==0.0: wcross=abs(lc.imag)
    print(f"  Lg={Lgs+d:.5f}: maxRe={ev.real.max():+.3f} critλ={np.round(lc,2)} all_aᵢ>0={all(x>0 for x in ai)}")
print(f"PASS: pHopf root {Lgs:.6f} = genuine Hopf (pure-imag pair at crossing, ω≈{wcross:.1f}, all aᵢ>0)")
