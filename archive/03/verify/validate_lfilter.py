#!/usr/bin/env python3
"""
Numerical cross-validation of the L-filter GFL Hopf theorems (post-hoc check, NOT a proof).
Run: python3 validate_lfilter.py

HONEST FINDINGS (this script's output):
  * Theorem 1 (2D PLL pendulum always stable, H'>0): CONFIRMED — J_2 eigenvalues have Re<0 and
    H' ≈ v_PCC_d ≈ Vg > 0 across all tested Lg.  (Also machine-verified in GFL/LFilterHopf.lean.)
  * Theorems 2.c/3 (cubic Hopf-surface ALGEBRA Σ=A·B−C=0, ω=√B): machine-verified in Lean
    (hopf_cubic_surface); this script only checks the model produces a cubic.
  * Theorem 2.b (a Hopf exists for some Lg): instability DOES appear at weak grid (max Re λ > 0
    at large Lg), so a crossing exists — BUT the equilibrium-angle bisection shows MULTIPLE sign
    changes (branch artifacts), so the boundary is not cleanly isolated here.
  * Theorem 4 (ordering Lg_id* > Lg_iq*): NOT SUPPORTED — the i_q and i_d reductions give the SAME
    crossing Lg in every scenario tested (both keep the PLL pair, which dominates).  The claimed
    strict ordering does not show up numerically.
  * Theorem 5 (ω_H → √(Vg·Ki_pll)): NOT SUPPORTED — √a₁ at the tested points is the FAST current
    mode (10³–10⁶ rad/s), not the slow PLL mode √(Vg·Ki_pll) ≈ 158 rad/s.
  * Theorem 6 (Lg_4D* ≈ Lg_iq*): ratio ≈ 1.9, not ≈ 1.

CONCLUSION: the STRUCTURAL theorems (1, and 2.c/3 as algebra) hold and are Lean-certified; the
model-specific QUANTITATIVE/ordering claims (4, 5, 6, and a clean 2.b) are NOT confirmed by this
check — they would need careful equilibrium-branch tracking and/or specific operating regimes, and
as stated they are in question.  Reported per the project's no-bluffing rule.
"""

import numpy as np
# numerically validate the 6 theorems of the L-filter GFL Hopf problem (post-hoc check, not proof)
def model(x,p):
    i_d,i_q,eta,th=x
    Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_P,Kp_Q,Kp_pll,Ki_pll,P_ref,Q_ref=p
    Ltot=Lf+Lg;Rtot=Rf+Rg;gam=(Lf*Rg-Rf*Lg)/Ltot;c,s=np.cos(th),np.sin(th)
    err_P=P_ref-1.5*Vg*i_d;err_Q=Q_ref+1.5*Vg*i_q
    i_d_ref=Kp_P*err_P;i_q_ref=-Kp_Q*err_Q
    i_dc=c*i_d-s*i_q;i_qc=s*i_d+c*i_q
    err_d=i_d_ref-i_dc;err_q=i_q_ref-i_qc
    u_dc=(Ltot/Lf)*(Kpi*err_d-wn*Lf*i_qc+(Lf/Ltot)*c*Vg+gam*i_dc)
    u_qc=(Ltot/Lf)*(Kpi*err_q+wn*Lf*i_dc+(Lf/Ltot)*s*Vg+gam*i_qc)
    u_d=c*u_dc+s*u_qc;u_q=-s*u_dc+c*u_qc
    vPCCd=(Lg/Ltot)*u_d+(Lf/Ltot)*Vg+gam*i_d
    vPCCq=(Lg/Ltot)*u_q+gam*i_q
    v_cqc=s*vPCCd+c*vPCCq
    return np.array([(u_d-Vg-Rtot*i_d+Ltot*wn*i_q)/Ltot,(u_q-Rtot*i_q-Ltot*wn*i_d)/Ltot,
                     v_cqc,-Kp_pll*v_cqc-Ki_pll*eta]),vPCCd,vPCCq
def equil(p):
    # solve F1=F2=0 (linear in i_d,i_q given th) and v_cqc=0 (1D in th) by bisection
    def currents(th):
        # F1,F2 linear in (i_d,i_q): A[i_d,i_q]=b
        x0=np.array([0,0,0,th]); F0=model(x0,p)[0][:2]
        A=np.zeros((2,2))
        for k in range(2):
            xe=np.array([0.,0.,0.,th]); xe[k]=1.0; A[:,k]=model(xe,p)[0][:2]-F0
        idq=np.linalg.solve(A,-F0); return idq
    def vcqc_of(th):
        idq=currents(th); return model([idq[0],idq[1],0,th],p)[0][2]
    a,b=-1.0,1.0
    while vcqc_of(a)*vcqc_of(b)>0: a-=0.5;b+=0.5
    for _ in range(80):
        m=(a+b)/2
        if vcqc_of(a)*vcqc_of(m)<=0: b=m
        else: a=m
    th=(a+b)/2; idq=currents(th); return np.array([idq[0],idq[1],0,th])
def jac(x,p,h=1e-7):
    n=4;J=np.zeros((n,n))
    for k in range(n):
        xp=x.copy();xp[k]+=h;xm=x.copy();xm[k]-=h
        J[:,k]=(model(xp,p)[0]-model(xm,p)[0])/(2*h)
    return J
def schur(J,keep):
    rem=[k for k in range(4) if k not in keep]
    A=J[np.ix_(keep,keep)];B=J[np.ix_(keep,rem)];C=J[np.ix_(rem,keep)];D=J[np.ix_(rem,rem)]
    return A-B@np.linalg.solve(D,C)
# base parameters (engineering-ish)
base=dict(Vg=311.0,wn=2*np.pi*50,Lf=2e-3,Rf=0.1,Lg=1e-3,Rg=0.05,Kpi=10.0,
          Kp_P=0.02,Kp_Q=0.02,Kp_pll=2.0,Ki_pll=80.0,P_ref=1e4,Q_ref=0.0)
order=['Vg','wn','Lf','Rf','Lg','Rg','Kpi','Kp_P','Kp_Q','Kp_pll','Ki_pll','P_ref','Q_ref']
def pvec(d): return [d[k] for k in order]
def sig3(J,keep):  # Σ = a2*a1 - a0 of the 3x3 reduction
    M=schur(J,keep); a=np.poly(M)  # [1,a2,a1,a0]
    return a[1]*a[2]-a[3], M
print("== Theorem 1: 2D PLL pendulum always stable, H'>0 ==")
for Lg in [1e-4,1e-3,5e-3,2e-2,1e-1]:
    d=dict(base);d['Lg']=Lg;p=pvec(d);xs=equil(p);J=jac(xs,p)
    J2=schur(J,[2,3]); ev=np.linalg.eigvals(J2); Hp=J2[0,1]
    print(f"  Lg={Lg:.0e}: J2 eig Re={ev.real}, H'={Hp:.3f}  (H'>0:{Hp>0}, stable:{all(ev.real<0)})")
print("\n== Theorems 2/3: Σ_iq, Σ_id sign change vs Lg; existence of Hopf ==")
def findcross(keep,d0):
    f=lambda Lg:(lambda dd:sig3(pvec_jac(dd),keep)[0])({**d0,'Lg':Lg})
    return f
def pvec_jac(d): p=pvec(d);xs=equil(p);return jac(xs,p)
for keep,name in [([1,2,3],'iq'),([0,2,3],'id')]:
    vals=[]
    for Lg in np.geomspace(1e-4,5e-1,18):
        d=dict(base);d['Lg']=Lg;S,_=sig3(pvec_jac(d),keep);vals.append((Lg,S))
    sign=[np.sign(v[1]) for v in vals]
    cross=[i for i in range(1,len(sign)) if sign[i]!=sign[i-1]]
    print(f"  Σ_{name}: small-Lg sign={sign[0]:+.0f}, large-Lg sign={sign[-1]:+.0f}, crossings at Lg≈{[f'{vals[i][0]:.2e}' for i in cross]}")
print("\n== Theorem 4: ordering Lg_id* > Lg_iq* ? ==")
def root_Lg(keep):
    lo,hi=1e-4,5e-1
    flo=sig3(pvec_jac({**base,'Lg':lo}),keep)[0]
    for _ in range(60):
        m=np.sqrt(lo*hi); fm=sig3(pvec_jac({**base,'Lg':m}),keep)[0]
        if flo*fm<=0: hi=m
        else: lo=m;flo=fm
    return np.sqrt(lo*hi)
Lg_iq=root_Lg([1,2,3]); Lg_id=root_Lg([0,2,3])
print(f"  Lg_iq*={Lg_iq:.4e},  Lg_id*={Lg_id:.4e},  Lg_id*>Lg_iq*: {Lg_id>Lg_iq}")
print("\n== Theorem 5: ω_H → sqrt(Vg*Ki_pll) as Lg·wn→∞ ==")
target=np.sqrt(base['Vg']*base['Ki_pll']); print(f"  sqrt(Vg*Ki_pll)={target:.3f}")
for Lg in [1e-2,1e-1,1.0,10.0]:
    d=dict(base);d['Lg']=Lg
    for keep,nm in [([1,2,3],'iq'),([0,2,3],'id')]:
        M=schur(pvec_jac(d),keep);a=np.poly(M);w=np.sqrt(abs(a[2])) # √a1
        print(f"  Lg={Lg:.0e} {nm}: ω_H≈√a1={w:.2f}")
print("\n== Theorem 6: 4D vs i_q-reduction Hopf Lg ==")
def sig4_root():
    def S4(Lg):
        J=pvec_jac({**base,'Lg':Lg});a=np.poly(J) # [1,a3,a2,a1,a0]
        return a[1]*a[2]*a[3]-a[3]**2-a[1]**2*a[4]  # quartic RH Hopf condition Δ3
    lo,hi=1e-4,5e-1;flo=S4(lo)
    for _ in range(60):
        m=np.sqrt(lo*hi);fm=S4(m)
        if flo*fm<=0:hi=m
        else:lo=m;flo=fm
    return np.sqrt(lo*hi)
Lg4=sig4_root()
print(f"  Lg_4D*={Lg4:.4e}, Lg_iq*={Lg_iq:.4e}, ratio={Lg4/Lg_iq:.4f}  (≈1 ⟹ iq dominates)")

print("\n\n===== WIDER SWEEP / aggressive PLL to provoke Hopf =====")
for scen in [dict(),dict(Ki_pll=500.0,Kp_pll=10.0),dict(Ki_pll=2000.0,Kp_pll=30.0,Kpi=3.0)]:
    d0=dict(base);d0.update(scen)
    print(f"\n scenario {scen if scen else 'base'}:")
    for keep,nm in [([1,2,3],'iq'),([0,2,3],'id')]:
        prev=None;crossed=[]
        for Lg in np.geomspace(1e-4,100,40):
            d=dict(d0);d['Lg']=Lg
            try:
                M=schur(pvec_jac(d),keep);a=np.poly(M);Sig=a[1]*a[2]-a[3]
                ev=np.linalg.eigvals(M);maxre=ev.real.max()
            except Exception:Sig=np.nan;maxre=np.nan
            sgn=np.sign(Sig)
            if prev is not None and sgn!=prev and not np.isnan(Sig):
                crossed.append(Lg)
            prev=sgn
        # report max Re eigenvalue over sweep to see if it goes positive (instability)
        maxres=[]
        for Lg in np.geomspace(1e-4,100,40):
            d=dict(d0);d['Lg']=Lg
            try:M=schur(pvec_jac(d),keep);maxres.append(np.linalg.eigvals(M).real.max())
            except Exception:maxres.append(np.nan)
        unstable=[Lg for Lg,mr in zip(np.geomspace(1e-4,100,40),maxres) if mr>1e-6]
        print(f"   {nm}: Σ crossings Lg≈{[f'{x:.2e}' for x in crossed]}; unstable(maxRe>0) at Lg≈{[f'{x:.2e}' for x in unstable[:3]]}{'...' if len(unstable)>3 else ''}")
