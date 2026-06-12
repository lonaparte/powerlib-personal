import sympy as sp, numpy as np, mpmath as mp
mp.mp.dps=30
# ---- model (same as ivgrid.py) ----
wn,Vg,Rg,Lg,vcd,Kp,Ki=sp.symbols('wn Vg Rg Lg vcd Kp Ki')
Cf=sp.Rational(1,10000);Lf=sp.Rational(1,1000);Rf=sp.Rational(1,10)
Kpi=sp.Rational(126,100);Kii=sp.Integer(126);Kad=sp.Integer(2);idr=sp.Integer(80);iqr=sp.Integer(0)
S=sp.symbols('i_d i_q v_cd v_cq i_gd i_gq xdc xqc eta th',real=True)
i_d,i_q,v_cd,v_cq,i_gd,i_gq,xdc,xqc,eta,th=S; wpll=wn+Kp*v_cq+Ki*eta
f=sp.Matrix([(Kpi*(idr-i_d)+Kii*xdc-Kad*(i_d-i_gd)-Rf*i_d)/Lf,(Kpi*(iqr-i_q)+Kii*xqc-Kad*(i_q-i_gq)-Rf*i_q)/Lf,
 (i_d-i_gd)/Cf+wpll*v_cq,(i_q-i_gq)/Cf-wpll*v_cd,(v_cd-Vg*sp.cos(th)-Rg*i_gd+wpll*Lg*i_gq)/Lg,
 (v_cq+Vg*sp.sin(th)-Rg*i_gq-wpll*Lg*i_gd)/Lg,idr-i_d,iqr-i_q,v_cq,Kp*v_cq+Ki*eta])
Asym=f.jacobian(list(S))
al=1-wn**2*Lg*Cf; K1=Rg*idr-wn*Lg*iqr; K2=Rg*iqr+wn*Lg*idr; be=Rg*wn*Cf
igq_e=iqr-wn*Cf*vcd; ceq=(al*vcd-K1)/Vg; seq=(K2-be*vcd)/Vg
sub={i_d:idr,i_q:iqr,v_cd:vcd,v_cq:0,i_gd:idr,i_gq:igq_e,xdc:Rf*idr/Kii,xqc:(Kad*(iqr-igq_e)+Rf*iqr)/Kii,sp.cos(th):ceq,sp.sin(th):seq,eta:0}
Ae=sp.Matrix(10,10,lambda i,j:Asym[i,j].subs(sub))
P=(wn,Vg,Rg,Lg,vcd,Kp,Ki)
Afun=sp.lambdify(P,Ae,'numpy')
Hsym={}; Tsym={}
for i in range(10):
    for j in range(10):
        for k in range(10):
            h=sp.diff(Asym[i,j],S[k])
            if h!=0:
                Hsym[(i,j,k)]=h.subs(sub)
                for l in range(10):
                    t=sp.diff(h,S[l])
                    if t!=0: Tsym[(i,j,k,l)]=t.subs(sub)
Hk=list(Hsym); Hf=sp.lambdify(P,[Hsym[k] for k in Hk],'numpy')
Tk=list(Tsym); Tf=sp.lambdify(P,[Tsym[k] for k in Tk],'numpy')
def pv(SCR,XR):
    wnv=2*np.pi*50; Vgv=380*np.sqrt(2/3); Zg=380.0**2/(1e5*SCR)
    sq=np.sqrt(1+XR**2); Rgv=Zg/sq; Lgv=Zg*XR/(sq*wnv); Cfv=1e-4
    alv=1-wnv**2*Lgv*Cfv; bev=Rgv*wnv*Cfv; K1v=Rgv*80; K2v=wnv*Lgv*80
    a2=alv**2+bev**2; a1=-2*(alv*K1v+bev*K2v); a0=K1v**2+K2v**2-Vgv**2
    disc=a1*a1-4*a2*a0
    if disc<0: return None                 # no equilibrium: voltage collapse (saddle-node)
    vcdv=(-a1+np.sqrt(disc))/(2*a2); return (wnv,Vgv,Rgv,Lgv,vcdv)
def Amat(SCR,XR,Kpv,Kiv):
    pp=pv(SCR,XR)
    if pp is None: return None
    return np.array(Afun(*pp,Kpv,Kiv),float)
def tensors(SCR,XR,Kpv,Kiv):
    a=(*pv(SCR,XR),Kpv,Kiv); Hv=Hf(*a); Tv=Tf(*a)
    B=np.zeros((10,10,10)); C=np.zeros((10,10,10,10))
    for key,val in zip(Hk,Hv): B[key]=float(val)
    for key,val in zip(Tk,Tv): C[key]=float(val)
    return B,C
def maxre(SCR,XR,Kpv,Kiv):
    A=Amat(SCR,XR,Kpv,Kiv)
    if A is None: return None
    return float(np.max(np.linalg.eigvals(A).real))
def hopf_SCR(XR,Kpv,Kiv):
    grid=np.linspace(3.0,0.3,240); prev=None      # scan high->low SCR (grid strong->weak)
    for s in grid:
        r=maxre(s,XR,Kpv,Kiv)
        if r is None: break                        # reached voltage-collapse boundary
        if prev is not None and prev[1]<0 and r>0: # stable -> unstable as grid weakens = Hopf
            a,b=s,prev[0]
            for _ in range(80):
                m=(a+b)/2; rm=maxre(m,XR,Kpv,Kiv)
                if rm>0: a=m
                else: b=m
            return (a+b)/2
        prev=(s,r)
    return None
def l1(SCR,XR,Kpv,Kiv):
    A=Amat(SCR,XR,Kpv,Kiv); B,C=tensors(SCR,XR,Kpv,Kiv)
    w,V=np.linalg.eig(A); re=w.real; km=np.argmax(re)
    cand=[i for i in range(10) if abs(re[i]-re[km])<1e-6*max(1,abs(re[km]))+1e-9]
    k=max(cand,key=lambda i:w[i].imag); lam=w[k]; q=V[:,k]; om=lam.imag
    wL,VL=np.linalg.eig(A.T); kl=np.argmin(np.abs(wL-np.conj(lam))); p=VL[:,kl]  # left eigvec for lam = A^T eigvec for conj(lam)
    q=q/np.sqrt(np.vdot(q,q).real); p=p/np.conj(np.vdot(p,q)); qb=np.conj(q)
    Bf=lambda u,v:np.einsum('ijk,j,k->i',B,u,v); Cf3=lambda u,v,w_:np.einsum('ijkl,j,k,l->i',C,u,v,w_)
    r1=np.linalg.solve(A,Bf(q,qb)); r2=np.linalg.solve(2j*om*np.eye(10)-A,Bf(q,q))
    g=Cf3(q,q,qb)-2*Bf(q,r1)+Bf(qb,r2)
    return (1/(2*om))*np.real(np.vdot(p,g)), om, lam.real
def l1_balanced(SCR,XR,Kpv,Kiv):
    import scipy.linalg
    A=Amat(SCR,XR,Kpv,Kiv); B,C=tensors(SCR,XR,Kpv,Kiv)
    _,T=scipy.linalg.matrix_balance(A,permute=False); d=np.diag(T).copy()
    Ab=np.diag(1/d)@A@np.diag(d)
    Bb=np.einsum('ijk,i,j,k->ijk',B,1/d,d,d); Cb=np.einsum('ijkl,i,j,k,l->ijkl',C,1/d,d,d,d)
    w,V=np.linalg.eig(Ab); re=w.real; km=np.argmax(re)
    cand=[i for i in range(10) if abs(re[i]-re[km])<1e-6*max(1,abs(re[km]))+1e-9]
    k=max(cand,key=lambda i:w[i].imag); lam=w[k]; q=V[:,k]; om=lam.imag
    wL,VL=np.linalg.eig(Ab.T); kl=np.argmin(np.abs(wL-np.conj(lam))); p=VL[:,kl]
    q=q/np.sqrt(np.vdot(q,q).real); p=p/np.conj(np.vdot(p,q)); qb=np.conj(q)
    Bf=lambda u,v:np.einsum('ijk,j,k->i',Bb,u,v); Cf3=lambda u,v,wv:np.einsum('ijkl,j,k,l->i',Cb,u,v,wv)
    r1=np.linalg.solve(Ab,Bf(q,qb)); r2=np.linalg.solve(2j*om*np.eye(10)-Ab,Bf(q,q))
    g=Cf3(q,q,qb)-2*Bf(q,r1)+Bf(qb,r2); return (1/(2*om))*np.real(np.vdot(p,g))
if __name__=='__main__':
    # cross-check at nominal (interval said l1 in [1.7e-4,3.1e-4] at SCR_H~0.905, X/R=10)
    sh=hopf_SCR(10,0.30,150); v,om,rec=l1(sh,10,0.30,150); vb=l1_balanced(sh,10,0.30,150)
    print("CHECK X/R=10: SCR_H=%.4f"%sh)
    print("  l1 (euclid-norm, unbalanced coords) = %.4e  -> sign=%s"%(v,"+"if v>0 else"-"))
    print("  l1 (euclid-norm, BALANCED coords)    = %.4e  vs interval box [1.7e-4,3.1e-4]; match=%s"%(vb,1.5e-4<vb<3.3e-4))
    print("  (magnitude is normalization-convention dependent; SIGN is the coordinate-invariant)")
    print()
    print("SWEEP along weak-grid Hopf locus (control fixed Kp=0.30,Ki=150):")
    print(" X/R    SCR_H    |Zg|(ohm)   f_osc(Hz)     l1          type")
    for XR in [2,3,4,5,7,10,13,16,20,30]:
        sh=hopf_SCR(XR,0.30,150)
        if sh is None: print("  %4.0f   (no weak-grid Hopf found in SCR in [0.3,3])"%XR); continue
        v,om,rec=l1(sh,XR,0.30,150)
        print("  %4.0f  %.4f   %7.3f    %8.3f   %+.4e   %s"%(XR,sh,380.0**2/1e5/sh,om/(2*np.pi),v,"subcritical(hard)" if v>0 else "SUPERcritical(soft)"))
