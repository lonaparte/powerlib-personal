#!/usr/bin/env python3
"""Crux check: along the P-only droop sweep, where do the Routh-Hurwitz Hopf conditions vanish?
   χ2 = a1(M_2D) = Kp_pll·gθ*           (Hopf-2D ⟺ gθ*=0 = fold)
   χ3 = a1a2−a3            of M_3D (keep i_q)
   χ4 = a1a2a3−a3²−a1²a4   of M_4D
   If χ4=0 at gθ*≠0 ⇒ 4D Hopf is SEPARATE from the (gθ*=0) PLL fold (mechanism holds).
   Also report a2(4D-equivalent ω²) sign to exclude spurious (ω²<0)."""
import numpy as np, sympy as sp
from scipy.optimize import fsolve
Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,Kp_Q,P_ref,Q_ref=sp.symbols(
 'Vg wn Lf Lg Kpi Kp_pll Ki_pll Kp_P Kp_Q P_ref Q_ref',real=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
Lt=Lf+Lg; c,s=sp.cos(th),sp.sin(th)
err_P=P_ref-sp.Rational(3,2)*Vg*i_d; err_Q=Q_ref+sp.Rational(3,2)*Vg*i_q
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
err_d=Kp_P*err_P-i_dc; err_q=-Kp_Q*err_Q-i_qc
u_dc=(Lt/Lf)*(Kpi*err_d-wn*Lf*i_qc+(Lf/Lt)*c*Vg); u_qc=(Lt/Lf)*(Kpi*err_q+wn*Lf*i_dc+(Lf/Lt)*s*Vg)
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
vPCCd=(Lg/Lt)*u_d+(Lf/Lt)*Vg; vPCCq=(Lg/Lt)*u_q; v_cqc=s*vPCCd+c*vPCCq
F=sp.Matrix([(u_d-Vg+Lt*wn*i_q)/Lt,(u_q-Lt*wn*i_d)/Lt,v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
Jm=F.jacobian(X)
PAR=[Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,Kp_Q,P_ref,Q_ref]
F_f=sp.lambdify(X+PAR,list(F)); J_f=sp.lambdify(X+PAR,Jm); gth_f=sp.lambdify(X+PAR,sp.diff(v_cqc,th))
def chi(M):
    a=np.poly(M)  # [1,a1,...]
    if len(a)==3: return a[1]                      # χ2 = a1
    if len(a)==4: return a[1]*a[2]-a[3]            # χ3
    return a[1]*a[2]*a[3]-a[3]**2-a[1]**2*a[4]     # χ4
p=dict(Vg=1.0,wn=1.0,Lf=0.05,Kpi=0.5,Kp_pll=2.0,Ki_pll=20.0,Kp_P=0.02,Kp_Q=0.02,P_ref=0.8,Q_ref=0.0)
warm=np.array([0.016,0,0,-0.1])
print(f"{'Lg':>6} {'gθ*':>9} {'χ2':>10} {'χ3':>11} {'χ4':>12} {'maxRe':>8}")
for Lgv in [3,5,6,6.4,6.5,7,9,13,20,28.6,36.6]:
    pv=[p['Vg'],p['wn'],p['Lf'],Lgv,p['Kpi'],p['Kp_pll'],p['Ki_pll'],p['Kp_P'],p['Kp_Q'],p['P_ref'],p['Q_ref']]
    y=fsolve(lambda z:np.array(F_f(*z,*pv),float).ravel(),warm,xtol=1e-13);
    if np.max(np.abs(F_f(*y,*pv)))<1e-8: warm=y.copy()
    J4=np.array(J_f(*y,*pv),float)
    chi2=chi(J4[np.ix_([2,3],[2,3])]); chi3=chi(J4[np.ix_([1,2,3],[1,2,3])]); chi4=chi(J4)
    gth=float(gth_f(*y,*pv)); mre=np.linalg.eigvals(J4).real.max()
    print(f"{Lgv:6.1f} {gth:9.4f} {chi2:10.4f} {chi3:11.5f} {chi4:12.5f} {mre:8.3f}")
print("\nχ2 ∝ gθ* (Hopf-2D bound to fold).  Read where χ3, χ4 cross 0 vs where gθ* crosses 0:")
print("  if χ4=0 at gθ*≠0 ⇒ 4D Hopf separate from fold (mechanism); if χ4=0 ≈ gθ*=0 ⇒ NOT separate here.")
