#!/usr/bin/env python3
"""
Tightened localization: (1) continuation-warm-started equilibria (fixes stiff-ablation convergence);
(2) both signs of θ_e*; (3) a FIXED-LOAD Lg sweep that moves θ_e* without touching P_ref — to show
the asymmetry tracks the POWER ANGLE, not P_ref directly.  Metric: |PF| of i_d vs i_q in the
least-damped oscillatory mode (scale-free), at SYMMETRIC gains Kp_P=Kp_Q.
"""
import numpy as np, sympy as sp
from scipy.optimize import fsolve

Vg,wn,Lf,Cf,Rf,Lg,Rg,Kpi,Kii,K_ad,Kp_pll,Ki_pll,Kp_P,Kp_Q,P_ref,Q_ref = sp.symbols(
    'Vg wn Lf Cf Rf Lg Rg Kpi Kii K_ad Kp_pll Ki_pll Kp_P Kp_Q P_ref Q_ref')
i_d,i_q,v_cd,v_cq,i_gd,i_gq,xi_dc,xi_qc,eta,th = sp.symbols(
    'i_d i_q v_cd v_cq i_gd i_gq xi_dc xi_qc eta theta_e')
X=[i_d,i_q,v_cd,v_cq,i_gd,i_gq,xi_dc,xi_qc,eta,th]
c,s=sp.cos(th),sp.sin(th)
id_ref=Kp_P*(P_ref-sp.Rational(3,2)*Vg*i_d); iq_ref=-Kp_Q*(Q_ref+sp.Rational(3,2)*Vg*i_q)
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
v_cdc=c*v_cd-s*v_cq; v_cqc=s*v_cd+c*v_cq
i_Cdc=c*(i_d-i_gd)-s*(i_q-i_gq); i_Cqc=s*(i_d-i_gd)+c*(i_q-i_gq)
err_d=id_ref-i_dc; err_q=iq_ref-i_qc
u_dc=Kpi*err_d+Kii*xi_dc-wn*Lf*i_qc+v_cdc-K_ad*i_Cdc
u_qc=Kpi*err_q+Kii*xi_qc+wn*Lf*i_dc+v_cqc-K_ad*i_Cqc
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
F=sp.Matrix([
    (u_d-v_cd-Rf*i_d+wn*Lf*i_q)/Lf, (u_q-v_cq-Rf*i_q-wn*Lf*i_d)/Lf,
    (i_d-i_gd+wn*Cf*v_cq)/Cf, (i_q-i_gq-wn*Cf*v_cd)/Cf,
    (v_cd-Vg-Rg*i_gd+wn*Lg*i_gq)/Lg, (v_cq-Rg*i_gq-wn*Lg*i_gd)/Lg,
    err_d, err_q, v_cqc, -Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X)
PARAMS=[Vg,wn,Lf,Cf,Rf,Lg,Rg,Kpi,Kii,K_ad,Kp_pll,Ki_pll,Kp_P,Kp_Q,P_ref,Q_ref]
F_f=sp.lambdify(X+PARAMS,list(F),'numpy'); J_f=sp.lambdify(X+PARAMS,J,'numpy')

def pf(Jn):
    lam,Phi=np.linalg.eig(Jn); Psi=np.linalg.inv(Phi)
    osc=[i for i in range(len(lam)) if abs(lam[i].imag)>1e-6]
    ic=max(osc,key=lambda i:lam[i].real)
    p=np.abs(Psi[ic,:]*Phi[:,ic]); p/=p.sum()
    return lam[ic],p[0],p[1]

def equilib(p,y0):
    pv=[p[str(k)] for k in PARAMS]
    g=lambda y: np.array(F_f(*y,*pv),dtype=float).ravel()
    y=fsolve(g,y0,xtol=1e-13); return y,np.max(np.abs(g(y))),np.array(J_f(*y,*pv),dtype=float)

KP=0.02
def sweep(tag,key,vals,**ov):
    base=dict(Vg=1.0,wn=1.0,Lf=0.05,Cf=0.05,Rf=0.005,Lg=0.6,Rg=0.06,Kpi=0.5,Kii=5.0,
              K_ad=0.5,Kp_pll=2.0,Ki_pll=20.0,Q_ref=0.0,P_ref=0.0,Kp_P=KP,Kp_Q=KP); base.update(ov)
    print(f"\n=== {tag} ===")
    print(f"{key:>8} {'θ_e*':>9} {'PF_id':>8} {'PF_iq':>8} {'PF_iq−PF_id':>12} {'Re λ_crit':>10}")
    y0=np.zeros(10); y0[2]=1.0; y0[9]=-0.05
    for v in vals:                                    # continuation: warm-start from previous
        p=dict(base); p[key]=v
        y0[0]=KP*p['P_ref']; y0[4]=KP*p['P_ref']
        y,res,Jn=equilib(p,y0)
        if res<1e-8: y0=y.copy()
        lam,pid,piq=pf(Jn)
        tag2='' if res<1e-8 else f' |F|={res:.0e}'
        print(f"{v:8.3f} {y[9]:9.5f} {pid:8.4f} {piq:8.4f} {piq-pid:12.5f} {lam.real:10.4f}{tag2}")

# (1) load sweep, both signs (θ_e* changes sign with P) — gap even in |θ_e*|?
sweep("FULL: load sweep P_ref (θ_e* tracks load), symmetric gains","P_ref",
      [-1.0,-0.5,0.0,0.5,1.0,1.5])
# (2) FIXED load, grid-strength sweep (θ_e* grows with Lg at fixed P) — isolates the angle
sweep("FULL: FIXED P_ref=0.8, sweep Lg (θ_e* via grid strength, load constant)","Lg",
      [0.1,0.3,0.6,0.9,1.2],P_ref=0.8)
# (3) ABLATION with continuation: shrink dropped dynamics
sweep("ABLATION (Kii=0,K_ad=0,Cf=5e-3): load sweep","P_ref",
      [0.0,0.3,0.6,0.9,1.2],Kii=0.0,K_ad=0.0,Cf=5e-3)
print("\nReading: gap≈0 at θ_e*≈0, grows with |θ_e*| under BOTH load and grid-strength sweeps (FULL);")
print("ablation suppresses it ⇒ asymmetry driver = power angle θ_e* THROUGH the dropped fast dynamics.")
