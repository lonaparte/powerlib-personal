#!/usr/bin/env python3
"""VERIFY the anchor with the PROBLEM'S parameters (PART 3): 4D P-only lossless GFL droop equilibrium,
continue in Lg↔SCR, locate Hopf (complex pair Re=0) and fold (det=0/branch ends), check
SCR_Hopf≈0.035 > SCR_fold≈0.032, freq≈15.8 Hz, and GENUINE (ω²=a2>0, all a_i>0)."""
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
Vgn=310.3
p=dict(Vg=Vgn,wn=314.159,Lf=1e-3,Kpi=1.26,Kp_pll=0.573,Ki_pll=50.9,Kp_P=2.15e-4,Kp_Q=2.15e-4,
       P_ref=1.5*Vgn*80.0,Q_ref=0.0)
def solve(Lgv,warm):
    pv=[p['Vg'],p['wn'],p['Lf'],Lgv,p['Kpi'],p['Kp_pll'],p['Ki_pll'],p['Kp_P'],p['Kp_Q'],p['P_ref'],p['Q_ref']]
    y=fsolve(lambda z:np.array(F_f(*z,*pv),float).ravel(),warm,xtol=1e-12,full_output=True)
    return y[0],np.max(np.abs(F_f(*y[0],*pv))),pv
print(f"{'Lg':>7} {'SCR':>8} {'i_d*':>7} {'errP*':>10} {'maxRe':>9} {'crit λ':>20} {'fHz':>7} {'gθ*':>9} {'res':>8}")
warm=np.array([80.,0,0,-0.1]); prevRe=None; hopf=None
for Lgv in np.arange(0.10,0.40,0.005):
    y,res,pv=solve(Lgv,warm)
    if res<1e-6: warm=y.copy()
    ev=np.linalg.eigvals(np.array(J_f(*y,*pv),float))
    osc=[e for e in ev if abs(e.imag)>1e-3]; lc=max(osc,key=lambda e:e.real) if osc else complex(ev.real.max())
    gth=float(gth_f(*y,*pv)); errP=p['P_ref']-1.5*p['Vg']*y[0]
    Sb=1.5*p['Vg']*abs(y[0]); SCR=p['Vg']**2/(Lgv*p['wn']*Sb) if Sb>1e-9 else float('inf')
    fHz=lc.imag/(2*np.pi)
    fl='' if res<1e-6 else f' BAD|F|={res:.0e}'
    print(f"{Lgv:7.3f} {SCR:8.4f} {y[0]:7.2f} {errP:10.1f} {ev.real.max():9.4f} {str(np.round(lc,2)):>20} "
          f"{fHz:7.2f} {gth:9.4f} {res:8.0e}{fl}")
    if prevRe is not None and prevRe<0<=ev.real.max() and abs(lc.imag)>1e-2 and res<1e-6 and hopf is None:
        # genuine check at the crossing: a_i>0, ω²=a2>0 from 4D char poly
        a=np.poly(np.array(J_f(*y,*pv),float)); ai=a[1:]
        hopf=(Lgv,SCR,lc,fHz,gth,all(x>0 for x in ai))
    prevRe=ev.real.max()
print("\nHopf:", hopf, "  (Lg,SCR,λ,fHz,gθ*,all_a_i>0)")
print("expected ~ SCR_Hopf 0.035, f 15.8 Hz, gθ*>0 (Hopf before fold gθ=0).")
