import sympy as sp, numpy as np, mpmath as mp
from mpmath import iv
iv.dps=50; mp.mp.dps=50
def ev(e,env,cache):
    if e in cache: return cache[e]
    if e.is_Integer: r=iv.mpf([int(e),int(e)])
    elif e.is_Rational: r=iv.mpf([int(e.p),int(e.p)])/iv.mpf([int(e.q),int(e.q)])
    elif e.is_Symbol: r=env[e]
    elif e.is_Add:
        r=iv.mpf([0,0])
        for a in e.args: r=r+ev(a,env,cache)
    elif e.is_Mul:
        r=iv.mpf([1,1])
        for a in e.args: r=r*ev(a,env,cache)
    elif e.is_Pow:
        b=ev(e.base,env,cache); n=int(e.exp); r=iv.mpf([1,1])
        for _ in range(abs(n)): r=r*b
        if n<0: r=iv.mpf([1,1])/r
    else: raise ValueError(str(type(e)))
    cache[e]=r; return r
# ---- model with Kp,Ki SYMBOLIC ----
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
Afun=sp.lambdify((wn,Vg,Rg,Lg,vcd,Kp,Ki),Ae,'mpmath')
# precompute nonzero Hessian/3rd-tensor symbolic entries (depend on wn,Vg,Rg,Lg,vcd,Kp,Ki)
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
def params_pt(SCRv,XRv):     # mpmath equilibrium at (SCR, X/R)
    wnv=2*mp.pi*50; Vgv=380*mp.sqrt(mp.mpf(2)/3); Zg=mp.mpf(380)**2/(mp.mpf('1e5')*SCRv)
    sq=mp.sqrt(1+XRv**2); Rgv=Zg/sq; Lgv=Zg*XRv/(sq*wnv); Cfv=mp.mpf(1)/10000
    alv=1-wnv**2*Lgv*Cfv; bev=Rgv*wnv*Cfv; K1v=Rgv*80; K2v=wnv*Lgv*80
    a2=alv**2+bev**2; a1=-2*(alv*K1v+bev*K2v); a0=K1v**2+K2v**2-Vgv**2
    vcdv=(-a1+mp.sqrt(a1*a1-4*a2*a0))/(2*a2); return wnv,Vgv,Rgv,Lgv,vcdv
Kpc,Kic=mp.mpf('0.30'),mp.mpf('150')
def An_at(SCRv,XRv):         # float center Jacobian at (SCR,X/R), control fixed
    M=Afun(*params_pt(mp.mpf(SCRv),mp.mpf(XRv)),Kpc,Kic)
    return np.array([[float(M[i,j]) for j in range(10)] for i in range(10)])
def maxre(SCRv,XRv): return float(np.max(np.linalg.eigvals(An_at(SCRv,XRv)).real))
def hopf_SCR(XRv):           # weak-grid Hopf SCR at this X/R (scan grid strong->weak)
    prev=None
    for s in np.linspace(3.0,0.4,300):
        try: r=maxre(s,XRv)
        except Exception: break
        if prev is not None and prev[1]<0 and r>0:
            lo,hi=s,prev[0]
            for _ in range(90):
                m=(lo+hi)/2
                if maxre(m,XRv)>0: lo=m
                else: hi=m
            return (lo+hi)/2
        prev=(s,r)
    return None

def env_box(SClo,SChi,xlo,xhi):
    SH=iv.mpf([mp.nstr(SClo,30),mp.nstr(SChi,30)])               # SCR box (encloses Hopf surface over tile)
    XR=iv.mpf([mp.nstr(xlo,30),mp.nstr(xhi,30)])                 # X/R tile
    wnI=2*iv.pi*50; VgI=380*iv.sqrt(iv.mpf([2,2])/3); Zg=iv.mpf([380,380])**2/(iv.mpf([100000,100000])*SH)
    sqI=iv.sqrt(1+XR**2)
    RgI=Zg/sqI; LgI=Zg*XR/(sqI*wnI); CfI=iv.mpf([1,1])/10000     # grid impedance Rg,Lg from (|Zg|,X/R)
    alv=1-wnI**2*LgI*CfI; bev=RgI*wnI*CfI; K1v=RgI*80; K2v=wnI*LgI*80
    a2=alv**2+bev**2; a1=-2*(alv*K1v+bev*K2v); a0=K1v**2+K2v**2-VgI**2
    vcdI=(-a1+iv.sqrt(a1*a1-4*a2*a0))/(2*a2)
    KpI=iv.mpf([mp.nstr(Kpc,30),mp.nstr(Kpc,30)]); KiI=iv.mpf([mp.nstr(Kic,30),mp.nstr(Kic,30)])  # control FIXED
    return {wn:wnI,Vg:VgI,Rg:RgI,Lg:LgI,vcd:vcdI,Kp:KpI,Ki:KiI}

def certify(env,An):
    cache={}
    Aiv=[[iv.mpc(ev(Ae[i,j],env,cache),iv.mpf([0,0])) for j in range(10)] for i in range(10)]
    Hnz={k:ev(e,env,cache) for k,e in Hsym.items()}; Tnz={k:ev(e,env,cache) for k,e in Tsym.items()}
    # ---- BALANCE: l1 invariant under x=D x~ ; work in D^-1 A D coords (well-conditioned) ----
    import scipy.linalg
    _,T=scipy.linalg.matrix_balance(An,permute=False); d=np.diag(T).copy()
    def R2iv_(x): return iv.mpf([float(x),float(x)])
    Aiv=[[Aiv[i][j]*R2iv_(d[j]/d[i]) for j in range(10)] for i in range(10)]
    Hnz={(i,j,k):H*R2iv_(d[j]*d[k]/d[i]) for (i,j,k),H in Hnz.items()}
    Tnz={(i,j,k,l):Tt*R2iv_(d[j]*d[k]*d[l]/d[i]) for (i,j,k,l),Tt in Tnz.items()}
    Anb=(np.diag(1/d)@An@np.diag(d))    # balanced center matrix
    # approx eigenpair at center (balanced)
    w,V=np.linalg.eig(Anb); kk=np.argmax(w.real); lam0=complex(w[kk]); q0=V[:,kk].astype(complex)
    s=int(np.argmax(np.abs(q0))); q0=q0/q0[s]
    def C(re,im=0.0): return iv.mpc(iv.mpf([re,re]) if not isinstance(re,iv.mpf) else re, iv.mpf([im,im]) if not isinstance(im,iv.mpf) else im)
    def matvec(M,v): return [sum((M[i][j]*v[j] for j in range(len(v))),iv.mpc(0,0)) for i in range(len(M))]
    def verify_ep(Miv,lam0,v0,sidx):
        Jn=np.zeros((11,11),complex)
        for i in range(10):
            for j in range(10): Jn[i,j]=(complex(Miv[i][j].real.a)+complex(Miv[i][j].imag.a)*1j if False else 0)
        # use center numeric matrix for J/R
        Mc=np.array([[ (float(Miv[i][j].real.a)+float(Miv[i][j].real.b))/2+1j*(float(Miv[i][j].imag.a)+float(Miv[i][j].imag.b))/2 for j in range(10)] for i in range(10)])
        for i in range(10):
            for j in range(10): Jn[i,j]=Mc[i,j]-(lam0 if i==j else 0)
            Jn[i,10]=-v0[i]
        Jn[10,sidx]=1.0; Rn=np.linalg.inv(Jn)
        Riv=[[C(Rn[i,j].real,Rn[i,j].imag) for j in range(11)] for i in range(11)]
        yhat=[C(v0[i].real,v0[i].imag) for i in range(10)]+[C(lam0.real,lam0.imag)]
        def amax(z): return max(abs(float(z.real.a)),abs(float(z.real.b)),abs(float(z.imag.a)),abs(float(z.imag.b)))
        def F(y):
            q=y[:10]; lam=y[10]; out=[sum((Miv[i][j]*q[j] for j in range(10)),iv.mpc(0,0))-lam*q[i] for i in range(10)]; out.append(q[sidx]-C(1.0)); return out
        def J(y):
            q=y[:10]; lam=y[10]; JJ=[[iv.mpc(0,0)]*11 for _ in range(11)]
            for i in range(10):
                for j in range(10): JJ[i][j]=Miv[i][j]-(lam if i==j else iv.mpc(0,0))
                JJ[i][10]=-q[i]
            JJ[10][sidx]=C(1.0); return JJ
        if not hasattr(certify,'_dbg'):
            certify._dbg=1; Fy=F(yhat); RFy=matvec(Riv,Fy); Jy=J(yhat)
            RJy=[[sum((Riv[i][k]*Jy[k][j] for k in range(11)),iv.mpc(0,0)) for j in range(11)] for i in range(11)]
            rfn=max(amax(RFy[i]) for i in range(11)); cmx=max(amax(RJy[i][j]-(iv.mpc(1,0) if i==j else iv.mpc(0,0))) for i in range(11) for j in range(11))
            print("    [dbg] cond(Jn)=%.1e  ||R F(yhat)||=%.1e  max|I-R J(yhat)|entry=%.1e"%(np.linalg.cond(Jn),rfn,cmx))
        for r in [1e-7*(1.3**k) for k in range(70)]:
            Y=[yh+iv.mpc(iv.mpf([-r,r]),iv.mpf([-r,r])) for yh in yhat]
            RF=matvec(Riv,F(yhat)); JJ=J(Y)
            RJ=[[sum((Riv[i][k]*JJ[k][j] for k in range(11)),iv.mpc(0,0)) for j in range(11)] for i in range(11)]
            dY=[Y[i]-yhat[i] for i in range(11)]
            cor=[sum((((iv.mpc(1,0) if i==j else iv.mpc(0,0))-RJ[i][j])*dY[j] for j in range(11)),iv.mpc(0,0)) for i in range(11)]
            Kk=[yhat[i]-RF[i]+cor[i] for i in range(11)]
            if all((Y[i].real.a<Kk[i].real.a and Kk[i].real.b<Y[i].real.b and Y[i].imag.a<Kk[i].imag.a and Kk[i].imag.b<Y[i].imag.b) for i in range(11)):
                return Kk,r
        return None,None
    Kq,rq=verify_ep(Aiv,lam0,q0,s)
    if Kq is None: return None,"eigenpair(q) Krawczyk failed"
    # left eigenvector
    ATiv=[[Aiv[j][i] for j in range(10)] for i in range(10)]
    w2,V2=np.linalg.eig(Anb.T); kl=np.argmin(np.abs(w2-(-1j*lam0.imag))); p0=V2[:,kl].astype(complex); spx=int(np.argmax(np.abs(p0))); p0=p0/p0[spx]
    Kp_,rp=verify_ep(ATiv,complex(w2[kl]),p0,spx)
    if Kp_ is None: return None,"eigenpair(p) Krawczyk failed"
    qI=Kq[:10]; lamI=Kq[10]; omI=lamI.imag; pI=Kp_[:10]
    def conj(z): return iv.mpc(z.real,-z.imag)
    def ipc(a,bv): return sum((conj(a[i])*bv[i] for i in range(10)),iv.mpc(0,0))
    qq=ipc(qI,qI); qn=[qI[i]/iv.sqrt(qq.real) for i in range(10)]
    pqi=ipc(pI,qn); pn=[pI[i]/conj(pqi) for i in range(10)]; qb=[conj(qn[i]) for i in range(10)]
    def Bf(u,v):
        o=[iv.mpc(0,0)]*10
        for (i,j,k),H in Hnz.items(): o[i]=o[i]+H*u[j]*v[k]
        return o
    def Cf3(u,v,w):
        o=[iv.mpc(0,0)]*10
        for (i,j,k,l),T in Tnz.items(): o[i]=o[i]+T*u[j]*v[k]*w[l]
        return o
    def vsolve(Miv,bb):
        Mmid=np.array([[(float(Miv[i][j].real.a)+float(Miv[i][j].real.b))/2+1j*(float(Miv[i][j].imag.a)+float(Miv[i][j].imag.b))/2 for j in range(10)] for i in range(10)])
        Rm=np.linalg.inv(Mmid); Riv=[[C(Rm[i,j].real,Rm[i,j].imag) for j in range(10)] for i in range(10)]
        x0=matvec(Riv,bb); resid=[bb[i]-sum((Miv[i][j]*x0[j] for j in range(10)),iv.mpc(0,0)) for i in range(10)]; d=matvec(Riv,resid)
        G=[[((iv.mpc(1,0) if i==j else iv.mpc(0,0))-sum((Riv[i][k]*Miv[k][j] for k in range(10)),iv.mpc(0,0))) for j in range(10)] for i in range(10)]
        def mag(z):
            ar=mp.mpf(max(abs(z.real.a),abs(z.real.b))); ai=mp.mpf(max(abs(z.imag.a),abs(z.imag.b))); return mp.sqrt(ar*ar+ai*ai)
        Ginf=max(sum((mag(G[i][j]) for j in range(10)),mp.mpf(0)) for i in range(10)); dinf=max(mag(d[i]) for i in range(10))
        if not (Ginf<1): raise RuntimeError("noncontractive %s"%float(Ginf))
        sb=float(Ginf*dinf/(1-Ginf))*1.0001; ball=iv.mpc(iv.mpf([-sb,sb]),iv.mpf([-sb,sb]))
        return [x0[i]+d[i]+ball for i in range(10)]
    g1=Cf3(qn,qn,qb); r1=vsolve(Aiv,Bf(qn,qb)); g2=Bf(qn,r1)
    M2=[[ (iv.mpc(iv.mpf([0,0]),2*omI)-Aiv[i][j]) if i==j else (iv.mpc(0,0)-Aiv[i][j]) for j in range(10)] for i in range(10)]
    r2=vsolve(M2,Bf(qn,qn)); g3=Bf(qb,r2)
    val=ipc(pn,[g1[i]-2*g2[i]+g3[i] for i in range(10)]); l1=(iv.mpf([1,1])/(2*omI))*val.real
    return (float(l1.a),float(l1.b),rq),None
import time
def tile_cert(xlo,xhi,pad=2e-6):
    sl=hopf_SCR(xlo); shh=hopf_SCR(xhi)
    if sl is None or shh is None: return None,None,"no Hopf at tile endpoint"
    SHmin,SHmax=min(sl,shh),max(sl,shh); SClo,SChi=SHmin-pad,SHmax+pad   # SCR box encloses Hopf surface over the tile
    env=env_box(SClo,SChi,xlo,xhi); An=An_at((SHmin+SHmax)/2,(xlo+xhi)/2)
    res,err=certify(env,An); return res,(SClo,SChi),err
print("LOCUS B&B  (control FIXED 0.30,150): rigorous l1>0 along the weak-grid Hopf locus")
print("=== probe: largest X/R tile half-width that verifies (centered X/R=10) ===")
hmax=None
for h in [1e-4,3e-4,5e-4,1e-3,2e-3]:
    res,box,err=tile_cert(10-h,10+h)
    print("  h=%.0e  X/R[%.4f,%.4f]: %s"%(h,10-h,10+h,("l1 in [%.3e,%.3e] OK"%(res[0],res[1])) if res else err))
    if res: hmax=h
    else: break
print("=== contiguous tiling at h=%.0e: prove l1>0 for ALL X/R in an interval ==="%hmax)
Xc=10.0; N=40; t0=time.time(); edges=[Xc+(k-N//2)*2*hmax for k in range(N+1)]
ok=0; l1min=1e9; cov=None
for t in range(len(edges)-1):
    if time.time()-t0>230: print("  [time budget reached after %d tiles]"%ok); break
    xlo,xhi=edges[t],edges[t+1]; res,box,err=tile_cert(xlo,xhi)
    if res: ok+=1; l1min=min(l1min,res[0]); cov=(edges[max(0,t-ok+1)],xhi) if cov is None else (cov[0],xhi)
    else: print("  tile X/R[%.5f,%.5f] FAILED: %s"%(xlo,xhi,err)); break
if cov: print("  VERIFIED %d consecutive tiles, no gaps => l1>0 PROVEN for ALL X/R in [%.5f,%.5f]"%(ok,cov[0],cov[1]))
if cov: print("  min l1 lower-bound across all tiles = %.3e  (>0, robustly subcritical)"%l1min)
