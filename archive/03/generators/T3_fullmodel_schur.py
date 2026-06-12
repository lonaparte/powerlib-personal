#!/usr/bin/env python3
"""
LOCALIZATION TEST.  Reduced model (4-state) gives D=Σ_iq−Σ_id with D|_{Kp_P=Kp_Q}≡0 at the physical
substitution point for ALL θ_e*.  The user's FULL model gives D|_{sym}≠0 growing with |θ_e*|.
Hypothesis: the asymmetry lives in the Schur contribution of the DROPPED dynamics (LCL caps v_cd,v_cq;
grid currents i_gd,i_gq; inner integrators ξ_dc,ξ_qc; active damping K_ad), which becomes
d/q-asymmetric only when θ_e*≠0.

Test: full 10-state model (SAME outer loop / grid as the reduced one), Schur-reduce the FULL Jacobian
to {i_q,η,θ} (Σ_iq) and {i_d,η,θ} (Σ_id); D|_{sym} vs load (θ_e*).  Predict ≈0 at θ_e*=0, ≠0 loaded.
Ablation: shrink the dropped dynamics (Kii,K_ad→0, Cf→0, fast LCL) to recover the reduced result.
"""
import numpy as np, sympy as sp
from scipy.optimize import fsolve

Vg,wn,Lf,Cf,Rf,Lg,Rg,Kpi,Kii,K_ad,Kp_pll,Ki_pll,Kp_P,Kp_Q,P_ref,Q_ref = sp.symbols(
    'Vg wn Lf Cf Rf Lg Rg Kpi Kii K_ad Kp_pll Ki_pll Kp_P Kp_Q P_ref Q_ref')
i_d,i_q,v_cd,v_cq,i_gd,i_gq,xi_dc,xi_qc,eta,th = sp.symbols(
    'i_d i_q v_cd v_cq i_gd i_gq xi_dc xi_qc eta theta_e')
X=[i_d,i_q,v_cd,v_cq,i_gd,i_gq,xi_dc,xi_qc,eta,th]
IDX={'i_d':0,'i_q':1,'eta':8,'th':9}
c,s=sp.cos(th),sp.sin(th)
# SAME outer loop as the reduced model: id_ref=Kp_P(P_ref−1.5Vg i_d), iq_ref=−Kp_Q(Q_ref+1.5Vg i_q)
id_ref=Kp_P*(P_ref-sp.Rational(3,2)*Vg*i_d)
iq_ref=-Kp_Q*(Q_ref+sp.Rational(3,2)*Vg*i_q)
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

def schur_sigma(Jn,keep):
    elim=[k for k in range(10) if k not in keep]
    A=Jn[np.ix_(keep,keep)]; B=Jn[np.ix_(keep,elim)]
    Cm=Jn[np.ix_(elim,keep)]; Dm=Jn[np.ix_(elim,elim)]
    M=A-B@np.linalg.solve(Dm,Cm)
    a=np.poly(M)                       # [1,A,B,C] for the 3×3
    return a[1]*a[2]-a[3]
def Dsym(Jn): return schur_sigma(Jn,[IDX['i_q'],IDX['eta'],IDX['th']]) \
                   - schur_sigma(Jn,[IDX['i_d'],IDX['eta'],IDX['th']])

def run(tag,**ov):
    base=dict(Vg=1.0,wn=1.0,Lf=0.05,Cf=0.05,Rf=0.005,Lg=0.6,Rg=0.06,Kpi=0.5,Kii=5.0,
              K_ad=0.5,Kp_pll=2.0,Ki_pll=20.0,Q_ref=0.0); base.update(ov)
    KP=0.02
    print(f"\n=== {tag}  (Kii={base['Kii']}, K_ad={base['K_ad']}, Cf={base['Cf']}, Lg={base['Lg']}) ===")
    print(f"{'P_ref':>7} {'θ_e*':>10} {'i_d*':>9} {'i_q*':>9} {'D|sym(full Schur)':>20}")
    for Pr in [0.0,0.2,0.5,0.8,1.0]:
        p=dict(base); p['P_ref']=Pr; p['Kp_P']=KP; p['Kp_Q']=KP
        pv=[p[str(k)] for k in PARAMS]
        g=lambda y: np.array(F_f(*y,*pv),dtype=float).ravel()
        y0=np.zeros(10); y0[0]=KP*Pr; y0[2]=1.0; y0[4]=KP*Pr; y0[9]=-0.2
        ystar=fsolve(g,y0); res=np.max(np.abs(g(ystar)))
        Jn=np.array(J_f(*ystar,*pv),dtype=float)
        d=Dsym(Jn)
        flag='' if res<1e-7 else f'  (|F|={res:.1e}!)'
        print(f"{Pr:7.2f} {ystar[9]:10.5f} {ystar[0]:9.5f} {ystar[1]:9.5f} {d:20.4e}{flag}")

run("FULL dynamics (LCL + inner integ + AD)")
run("ABLATION: shrink dropped dynamics (Kii→0,K_ad→0,fast LCL Cf→1e-4)",Kii=0.0,K_ad=0.0,Cf=1e-4)
print("\nIf FULL shows D|sym=0 at P_ref=0 (θ_e=0) but ≠0 growing with load (θ_e≠0),")
print("and ABLATION drives D|sym→0 at all loads, the DROPPED dynamics × power angle is the driver.")
