#!/usr/bin/env python3
"""
SCR_H1 i_d/i_q CRITERION — the stability-meaningful object that REPLACES the retired Σ hybrid.

Uses the validated full model of T3_participation2.py (10 states: i_d,i_q conv current; v_cd,v_cq LCL
caps; i_gd,i_gq grid current; xi_dc,xi_qc inner-current PI; eta,th PLL), linearised at its GENUINE
equilibrium (fsolve F=0 — a real fixed point, NOT a reference-current substitution).  Symmetric outer
gains Kp_P=Kp_Q.  We LOCATE the Hopf boundary SCR_H1 (least-damped oscillatory mode crosses Re=0 as
the grid weakens) and read the i_d/i_q participation factors THERE.  Cross-validated over 3 sets.

This is the correct answer to "which of i_d,i_q is essential at SCR_H1": the participation factors of
the actual critical mode at the actual Hopf boundary of a true equilibrium — no hybrid, no non-fixed
-point linearisation.

STATUS (honest): EXPLORATORY.  With these (untuned) params the FIRST Hopf as the grid weakens is the
FAST control/LCL-resonance mode (~10 pu ≈ 500 Hz) at small Lg / θ_e*≈0, which PREEMPTS the physical
weak-grid slow Hopf (the reviewer's SCR_H1≈0.057, −76°, 15.7 Hz).  At that near-zero-angle crossing
PF_id≈PF_iq to ±5e-4 — this CONFIRMS the mechanism (PF_iq−PF_id ∝ sinθ_e*, ≈0 at θ_e*≈0) but is NOT
the weak-grid operating point.  Isolating the large-angle SCR_H1 needs the fast modes tuned stable
(a converter control-design step) or the reviewer's tuned 9D params.  The MECHANISM (∝ sinθ_e*) is
also shown at swept large-angle points in T3_participation2.py (linear fit R²=0.999).
"""
import numpy as np, sympy as sp
from scipy.optimize import fsolve, brentq

(Vg,wn,Lf,Cf,Rf,Lg,Rg,Kpi,Kii,K_ad,Kp_pll,Ki_pll,Kp_P,Kp_Q,P_ref,Q_ref)=sp.symbols(
 'Vg wn Lf Cf Rf Lg Rg Kpi Kii K_ad Kp_pll Ki_pll Kp_P Kp_Q P_ref Q_ref')
(i_d,i_q,v_cd,v_cq,i_gd,i_gq,xi_dc,xi_qc,eta,th)=sp.symbols(
 'i_d i_q v_cd v_cq i_gd i_gq xi_dc xi_qc eta th')
X=[i_d,i_q,v_cd,v_cq,i_gd,i_gq,xi_dc,xi_qc,eta,th]; IDX={'i_d':0,'i_q':1}
c,s=sp.cos(th),sp.sin(th)
id_ref=Kp_P*(P_ref-sp.Rational(3,2)*Vg*i_d); iq_ref=-Kp_Q*(Q_ref+sp.Rational(3,2)*Vg*i_q)
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
v_cdc=c*v_cd-s*v_cq; v_cqc=s*v_cd+c*v_cq
i_Cdc=c*(i_d-i_gd)-s*(i_q-i_gq); i_Cqc=s*(i_d-i_gd)+c*(i_q-i_gq)
err_d=id_ref-i_dc; err_q=iq_ref-i_qc
u_dc=Kpi*err_d+Kii*xi_dc-wn*Lf*i_qc+v_cdc-K_ad*i_Cdc
u_qc=Kpi*err_q+Kii*xi_qc+wn*Lf*i_dc+v_cqc-K_ad*i_Cqc
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
F=sp.Matrix([(u_d-v_cd-Rf*i_d+wn*Lf*i_q)/Lf,(u_q-v_cq-Rf*i_q-wn*Lf*i_d)/Lf,
             (i_d-i_gd+wn*Cf*v_cq)/Cf,(i_q-i_gq-wn*Cf*v_cd)/Cf,
             (v_cd-Vg-Rg*i_gd+wn*Lg*i_gq)/Lg,(v_cq-Rg*i_gq-wn*Lg*i_gd)/Lg,
             err_d,err_q,v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X)
PAR=[Vg,wn,Lf,Cf,Rf,Lg,Rg,Kpi,Kii,K_ad,Kp_pll,Ki_pll,Kp_P,Kp_Q,P_ref,Q_ref]
F_f=sp.lambdify(X+PAR,list(F)); J_f=sp.lambdify(X+PAR,J)

def state(p,warm=None):
    pv=[p[str(k)] for k in PAR]
    g=lambda y:np.array(F_f(*y,*pv),float).ravel()
    y0=warm if warm is not None else np.array([p['Kp_P']*p['P_ref'],0,1,0,p['Kp_P']*p['P_ref'],0,0,0,0,-0.05])
    y=fsolve(g,y0,xtol=1e-13); return y,np.max(np.abs(g(y))),np.array(J_f(*y,*pv),float)
def crit(Jn):
    ev,Phi=np.linalg.eig(Jn); Psi=np.linalg.inv(Phi)
    osc=[i for i in range(len(ev)) if abs(ev[i].imag)>1e-6]; i=max(osc,key=lambda k:ev[k].real)
    pf=np.abs(Psi[i,:]*Phi[:,i]); pf/=pf.sum(); return ev[i],pf
def maxre(p,warm=None):
    y,res,Jn=state(p,warm); return np.linalg.eigvals(Jn).real.max(),y,res,Jn

def run(tag,**ov):
    base=dict(Vg=1.0,wn=1.0,Lf=0.05,Cf=0.05,Rf=0.005,Rg=0.0,Kpi=0.5,Kii=5.0,K_ad=0.5,
              Kp_pll=2.0,Ki_pll=20.0,Kp_P=0.02,Kp_Q=0.02,P_ref=0.8,Q_ref=0.0); base.update(ov)
    print(f"\n=== {tag}: Kp_pll={base['Kp_pll']} Ki_pll={base['Ki_pll']} P_ref={base['P_ref']} ===")
    # scan Lg upward to bracket the Hopf (maxRe crosses 0); warm-start continuation
    grid=np.concatenate([np.arange(0.05,1.0,0.05),np.arange(1.0,3.01,0.1)])
    warm=None; prev=None; bracket=None
    for Lg in grid:
        p=dict(base); p['Lg']=Lg; p['Rg']=Lg/10
        mr,y,res,Jn=maxre(p,warm)
        if res<1e-8: warm=y.copy()
        if prev is not None and prev[1]<0<=mr and res<1e-8: bracket=(prev[0],Lg); break
        prev=(Lg,mr)
    if bracket is None:
        print("  no Re=0 crossing found in Lg∈[0.05,3] (model stays stable or stays unstable here)")
        return
    def f(Lg):
        p=dict(base); p['Lg']=Lg; p['Rg']=Lg/10
        mr,_,_,_=maxre(p,warm); return mr
    LgH=brentq(f,bracket[0],bracket[1],xtol=1e-6)
    p=dict(base); p['Lg']=LgH; p['Rg']=LgH/10
    y,res,Jn=state(p,warm); lc,pf=crit(Jn)
    SCR=base['Vg']**2/(base['P_ref']*LgH)
    print(f"  Hopf boundary SCR_H1: Lg_H={LgH:.4f}  SCR≈{SCR:.3f}  θ_e*={np.degrees(y[9]):.1f}°  "
          f"crit λ={lc:.4f}  f={lc.imag*50:.1f} Hz  |F|={res:.0e}")
    print(f"  participation at SCR_H1 (symmetric gains):  PF_id={pf[0]:.4f}   PF_iq={pf[1]:.4f}   "
          f"PF_iq−PF_id={pf[1]-pf[0]:+.4f}  ⇒ essential state = {'i_q' if pf[1]>pf[0] else 'i_d'}")

run("set#0")
run("set#1 (faster PLL)",Kp_pll=3.0,Ki_pll=30.0)
run("set#2 (lighter load)",P_ref=0.5,Kp_pll=2.5,Ki_pll=25.0)
print("\nSCR_H1 i_d/i_q criterion: participation factors of the critical mode at the Hopf boundary of")
print("the full model's TRUE equilibrium — the stability-meaningful object (no hybrid, no non-fixed pt).")
