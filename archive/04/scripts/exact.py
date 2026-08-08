import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, sympy as sp
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg()

# ---- numeric gains (fixed) ----
KPP,KIP,KPV,KIV,CDC = 50.0,1000.0,1.0,50.0,0.01

# ---- symbolic: th=Δθ*, Xg, Q(=iq_ref), Vg, P(=idc_src) ----
th,Xg,Q,Vg,P = sp.symbols('theta X_g Q V_g P', real=True)
a  = Vg*sp.cos(th); b = Vg*sp.sin(th)
vgd0 = a - Xg*Q;    id0 = b/Xg
# exact 4x4 Jacobian (derived by hand above)
J = sp.Matrix([
 [-KPP*a,  KIP, -KPP*Xg*KPV,           KPP*Xg*KIV],
 [-a,      0,   -Xg*KPV,               Xg*KIV],
 [sp.Rational(3,2)/CDC*(-b*id0-Q*a), 0,
   sp.Rational(3,2)/CDC*(-(vgd0*KPV+Q*Xg*KPV+vgd0*id0)),
   sp.Rational(3,2)/CDC*( vgd0*KIV+Q*Xg*KIV)],
 [0,0,-1,0]])

# ---- verify J against numerical jacobian block at a test point ----
def numeric_point(Xg_,Q_,Vg_,P_):
    p=S.make_p(Xg=Xg_,iq_ref=Q_,Vg=Vg_,idc_src=P_); eq=S.stable_eq(p,cfg)
    return eq[0], S.jacobian(eq,p,cfg)[:4,:4]
th0,Jn = numeric_point(1.0,0.0,1.0,0.5)
Js = np.array(J.subs({th:th0,Xg:1.0,Q:0.0,Vg:1.0,P:0.5})).astype(float)
print("max|J_analytic - J_numeric| at Xg=1.0 :", np.max(np.abs(Js-Jn)), "  (should be ~0)")

# ---- characteristic polynomial & Routh-Hurwitz Hopf discriminant ----
lam=sp.symbols('lambda')
cp=sp.Poly(J.charpoly(lam).as_expr(),lam)
c3,c2,c1,c0=[cp.nth(k) for k in (3,2,1,0)]   # λ^4 + c3 λ^3 + c2 λ^2 + c1 λ + c0
R = sp.simplify(c1*c2*c3 - c1**2 - c0*c3**2) # >0 stable ; =0 Hopf

# equilibrium condition E(theta,params)=0  (power balance)
E = P + sp.Rational(3,2)*vgd0*id0

# ---- verify Routh R changes sign at the numerical Hopf, and locate it ----
def Rval(Xg_):
    p=S.make_p(Xg=Xg_); eq=S.stable_eq(p,cfg); t=eq[0]
    return float(R.subs({th:t,Xg:Xg_,Q:0.0,Vg:1.0,P:0.5}))
def maxRe(Xg_):
    p=S.make_p(Xg=Xg_); eq=S.stable_eq(p,cfg)
    return float(np.linalg.eigvals(S.jacobian(eq,p,cfg)[:4,:4]).real.max())
print("\n Xg     Routh_R        maxRe(eig)   (R and -maxRe should cross 0 together)")
for Xg_ in [1.0,1.3,1.45,1.48,1.49,1.495]:
    print(f" {Xg_:5.3f}  {Rval(Xg_):+.4e}   {maxRe(Xg_):+.4f}")

# ---- correct sensitivities: total dR/dparam = ∂R/∂p + ∂R/∂θ·(-E_p/E_θ) ----
Eth=sp.diff(E,th)
def dR_dparam(param, Xg_, Q_=0.0, Vg_=1.0, P_=0.5):
    p=S.make_p(Xg=Xg_,iq_ref=Q_,Vg=Vg_,idc_src=P_); eq=S.stable_eq(p,cfg); t=eq[0]
    sub={th:t,Xg:Xg_,Q:Q_,Vg:Vg_,P:P_}
    dth=-float(sp.diff(E,param).subs(sub))/float(Eth.subs(sub))
    return float(sp.diff(R,param).subs(sub)) + float(sp.diff(R,th).subs(sub))*dth

print("\n Correct analytic sensitivity dR/dθ (sign should be OPPOSITE to numeric dRe/dθ):")
print(" (numeric dRe/dθ at Xg=1.45:  P=+260  Q=+281  V=-265  grid=+89)")
for Xg_ in [1.0,1.45]:
    dP=dR_dparam(P,Xg_); dQ=dR_dparam(Q,Xg_); dV=dR_dparam(Vg,Xg_); dX=dR_dparam(Xg,Xg_)
    print(f"  Xg={Xg_}:  dR/dP={dP:+.3e}  dR/dQ={dQ:+.3e}  dR/dV={dV:+.3e}  dR/dXg={dX:+.3e}")
    # normalise to |dR/dP|
    n=abs(dP)
    print(f"           |ratio| P:Q:V:Xg = {abs(dP)/n:.2f} : {abs(dQ)/n:.2f} : {abs(dV)/n:.2f} : {abs(dX)/n:.2f}"
          f"   signs = {np.sign([dP,dQ,dV,dX]).astype(int)}")
