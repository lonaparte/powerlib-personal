import sympy as sp, time, pickle
t0=time.time()
def log(m): print(f"[{time.time()-t0:5.1f}s] {m}", flush=True)
Vg,wn,Lf,Rf,Lg,Rg,Kpi,Kp_P,Kp_Q,Kp_pll,Ki_pll,P_ref,Q_ref=sp.symbols(
 'Vg wn Lf Rf Lg Rg Kpi Kp_P Kp_Q Kp_pll Ki_pll P_ref Q_ref',real=True)
i_d,i_q,eta,th=sp.symbols('i_d i_q eta theta_e',real=True); X=[i_d,i_q,eta,th]
Ltot=Lf+Lg; Rtot=Rf+Rg; gam=(Lf*Rg-Rf*Lg)/Ltot
c,s=sp.cos(th),sp.sin(th)
err_P=P_ref-sp.Rational(3,2)*Vg*i_d; err_Q=Q_ref+sp.Rational(3,2)*Vg*i_q
i_d_ref=Kp_P*err_P; i_q_ref=-Kp_Q*err_Q
i_dc=c*i_d-s*i_q; i_qc=s*i_d+c*i_q
err_d=i_d_ref-i_dc; err_q=i_q_ref-i_qc
u_dc=(Ltot/Lf)*(Kpi*err_d-wn*Lf*i_qc+(Lf/Ltot)*c*Vg+gam*i_dc)
u_qc=(Ltot/Lf)*(Kpi*err_q+wn*Lf*i_dc+(Lf/Ltot)*s*Vg+gam*i_qc)
u_d=c*u_dc+s*u_qc; u_q=-s*u_dc+c*u_qc
vPCCd=(Lg/Ltot)*u_d+(Lf/Ltot)*Vg+gam*i_d
vPCCq=(Lg/Ltot)*u_q+gam*i_q
v_cqc=s*vPCCd+c*vPCCq
F=sp.Matrix([(u_d-Vg-Rtot*i_d+Ltot*wn*i_q)/Ltot,(u_q-Rtot*i_q-Ltot*wn*i_d)/Ltot,
             v_cqc,-Kp_pll*v_cqc-Ki_pll*eta])
J=F.jacobian(X)
C,Sy=sp.symbols('C S',real=True); J=J.subs([(sp.cos(th),C),(sp.sin(th),Sy)]); log("J built")
lam=sp.symbols('lam')
def schur(keep):
    rem=[k for k in range(4) if k not in keep]
    Akk=J[keep,keep];Akr=J[keep,rem];Ark=J[rem,keep];Arr=J[rem,rem]
    return Akk-Akr*Arr.inv()*Ark
def charcoeffs(M):
    n=M.shape[0]; cp=sp.Poly(sp.cancel((lam*sp.eye(n)-M).det()),lam); return cp.all_coeffs()
# 3D i_q kept {1,2,3}
Jiq=schur([1,2,3]); log("Jiq done")
ciq=charcoeffs(Jiq); log(f"χ_iq=[1,a2,a1,a0] op-counts {[sp.count_ops(x) for x in ciq]}")
Sig_iq=sp.cancel(ciq[1]*ciq[2]-ciq[3]); log(f"Σ_iq ops {sp.count_ops(Sig_iq)}")
# 3D i_d kept {0,2,3}
Jid=schur([0,2,3]); log("Jid done")
cid=charcoeffs(Jid); log(f"χ_id op-counts {[sp.count_ops(x) for x in cid]}")
Sig_id=sp.cancel(cid[1]*cid[2]-cid[3]); log(f"Σ_id ops {sp.count_ops(Sig_id)}")
# 2D {2,3}: check structure J2_00=0, J2_10=-Ki_pll, J2_11=-Kp_pll*J2_01
J2=schur([2,3]); log("J2 done")
for (i,j) in [(0,0),(0,1),(1,0),(1,1)]:
    log(f"  J2[{i},{j}] = {sp.cancel(J2[i,j])}")
pickle.dump({'ciq':[str(x) for x in ciq],'cid':[str(x) for x in cid],
 'Sig_iq':str(Sig_iq),'Sig_id':str(Sig_id),
 'J2':[[str(sp.cancel(J2[i,j])) for j in range(2)] for i in range(2)]},open('/tmp/lf.pkl','wb'))
log("saved")
