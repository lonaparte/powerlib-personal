#!/usr/bin/env python3
"""
VERIFY the empirical anchor (before any Lean): 4D P-only lossless GFL at its DROOP equilibrium (F=0,
err≠0, NOT references-met).  Continue in grid strength (Lg ↔ SCR); locate the Hopf (complex pair
crosses Re=0) and the fold (real eigenvalue → 0 / equilibrium vanishes).  Claim to check:
  Hopf occurs BEFORE fold (SCR_Hopf > SCR_fold), 4D has it on its own; 2D (PLL block at X*) does NOT
  (its char poly λ²+Kp_pll·gθ*·λ+Ki_pll·gθ* only crosses the axis at gθ*=0 = fold).
"""
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
J=F.jacobian(X)
PAR=[Vg,wn,Lf,Lg,Kpi,Kp_pll,Ki_pll,Kp_P,Kp_Q,P_ref,Q_ref]
F_f=sp.lambdify(X+PAR,list(F)); J_f=sp.lambdify(X+PAR,J)
vcqc_th=sp.lambdify(X+PAR, sp.diff(v_cqc,th))                 # gθ = ∂v_cqc/∂θ_e
Pf=sp.lambdify(X+PAR, sp.Rational(3,2)*(vPCCd*i_d+vPCCq*i_q))
Qf=sp.lambdify(X+PAR, sp.Rational(3,2)*(vPCCq*i_d-vPCCd*i_q))

p=dict(Vg=1.0,wn=1.0,Lf=0.05,Kpi=0.5,Kp_pll=2.0,Ki_pll=20.0,Kp_P=0.02,Kp_Q=0.02,P_ref=0.8,Q_ref=0.0)
def eqn(Lgv,warm):
    pv=[p['Vg'],p['wn'],p['Lf'],Lgv,p['Kpi'],p['Kp_pll'],p['Ki_pll'],p['Kp_P'],p['Kp_Q'],p['P_ref'],p['Q_ref']]
    g=lambda y:np.array(F_f(*y,*pv),float).ravel()
    y=fsolve(g,warm,xtol=1e-13,full_output=True)
    return y[0],np.max(np.abs(g(y[0]))),pv

print(f"{'Lg':>7} {'SCR':>8} {'i_d*':>8} {'errP*':>9} {'θe*(°)':>8} {'maxRe':>9} {'crit(osc)':>20} {'gθ*':>9} {'res':>8}")
warm=np.array([p['P_ref']*p['Kp_P'],0,0,-0.1]); prevRe=None; hopf=fold=None
for Lgv in np.concatenate([np.arange(0.5,5,0.5),np.arange(5,60,2.0)]):
    y,res,pv=eqn(Lgv,warm)
    if res<1e-8: warm=y.copy()
    ev=np.linalg.eigvals(np.array(J_f(*y,*pv),float))
    osc=[e for e in ev if abs(e.imag)>1e-6]; lc=max(osc,key=lambda e:e.real) if osc else complex(ev.real.max())
    gth=float(vcqc_th(*y,*pv)); errP=p['P_ref']-1.5*p['Vg']*y[0]
    Sm=abs(Pf(*y,*pv)+1j*Qf(*y,*pv)); SCR=p['Vg']**2/(Lgv*p['wn']*Sm) if Sm>1e-9 else float('inf')
    flag='' if res<1e-8 else f' |F|={res:.0e}'
    print(f"{Lgv:7.2f} {SCR:8.4f} {y[0]:8.4f} {errP:9.4f} {np.degrees(y[3]):8.1f} {ev.real.max():9.4f} "
          f"{str(np.round(lc,2)):>20} {gth:9.4f} {res:8.0e}{flag}")
    if prevRe is not None and prevRe<0<=ev.real.max() and abs(lc.imag)>1e-3 and hopf is None and res<1e-8:
        hopf=(Lgv,SCR,lc)
    prevRe=ev.real.max()
print("\nHopf (4D, osc pair crosses Re=0):", hopf)
print("2D check: M_2D char poly = λ²+Kp_pll·gθ*·λ+Ki_pll·gθ*; pure-imaginary ⟺ gθ*=0 (fold), never ω≠0 Hopf.")
print("  ⇒ along the sweep, 2D crosses the axis only where gθ* changes sign (fold), with ω=0 — no Hopf.")
