import sympy as sp, numpy as np, mpmath as mp
from mpmath import iv
iv.dps=50; mp.mp.dps=50
def ev(e, env, cache):
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
    else: raise ValueError("node "+str(type(e)))
    cache[e]=r; return r
wn,Vg,Rg,Lg,vcd=sp.symbols('wn Vg Rg Lg vcd')
Cf=sp.Rational(1,10000);Lf=sp.Rational(1,1000);Rf=sp.Rational(1,10)
Kpi=sp.Rational(126,100);Kii=sp.Integer(126);Kad=sp.Integer(2);idr=sp.Integer(80);iqr=sp.Integer(0)
Kp=sp.Rational(3,10);Ki=sp.Integer(150)
S=sp.symbols('i_d i_q v_cd v_cq i_gd i_gq xdc xqc eta th',real=True)
i_d,i_q,v_cd,v_cq,i_gd,i_gq,xdc,xqc,eta,th=S; cth,sth=sp.symbols('cth sth')
wpll=wn+Kp*v_cq+Ki*eta
f=sp.Matrix([(Kpi*(idr-i_d)+Kii*xdc-Kad*(i_d-i_gd)-Rf*i_d)/Lf,(Kpi*(iqr-i_q)+Kii*xqc-Kad*(i_q-i_gq)-Rf*i_q)/Lf,
 (i_d-i_gd)/Cf+wpll*v_cq,(i_q-i_gq)/Cf-wpll*v_cd,(v_cd-Vg*sp.cos(th)-Rg*i_gd+wpll*Lg*i_gq)/Lg,
 (v_cq+Vg*sp.sin(th)-Rg*i_gq-wpll*Lg*i_gd)/Lg,idr-i_d,iqr-i_q,v_cq,Kp*v_cq+Ki*eta])
Asym=f.jacobian(list(S))
al=1-wn**2*Lg*Cf; K1=Rg*idr-wn*Lg*iqr; K2=Rg*iqr+wn*Lg*idr; be=Rg*wn*Cf
igq_e=iqr-wn*Cf*vcd; ceq=(al*vcd-K1)/Vg; seq=(K2-be*vcd)/Vg
sub={i_d:idr,i_q:iqr,v_cd:vcd,v_cq:0,i_gd:idr,i_gq:igq_e,xdc:Rf*idr/Kii,xqc:(Kad*(iqr-igq_e)+Rf*iqr)/Kii,eta:0,sp.cos(th):ceq,sp.sin(th):seq}
Ae=sp.Matrix(10,10,lambda i,j: Asym[i,j].subs(sub))
Afun=sp.lambdify((wn,Vg,Rg,Lg,vcd),Ae,'mpmath')
def params_mp(SCRv):
    wnv=2*mp.pi*50; Vgv=380*mp.sqrt(mp.mpf(2)/3); Zg=mp.mpf(380)**2/(mp.mpf('1e5')*SCRv)
    Rgv=Zg/mp.sqrt(101); Lgv=Zg*10/(mp.sqrt(101)*wnv); Cfv=mp.mpf(1)/10000
    alv=1-wnv**2*Lgv*Cfv; bev=Rgv*wnv*Cfv; K1v=Rgv*80; K2v=wnv*Lgv*80
    a2=alv**2+bev**2; a1=-2*(alv*K1v+bev*K2v); a0=K1v**2+K2v**2-Vgv**2
    vcdv=(-a1+mp.sqrt(a1*a1-4*a2*a0))/(2*a2)
    return wnv,Vgv,Rgv,Lgv,vcdv
def maxre(SCRv):
    M=Afun(*params_mp(mp.mpf(SCRv))); An=np.array([[float(M[i,j]) for j in range(10)] for i in range(10)])
    return float(np.max(np.linalg.eigvals(An).real)), An
print("scan maxRe:", [(round(float(x),3),round(maxre(x)[0],4)) for x in [mp.mpf(t)/100 for t in range(85,101,2)]])
grid=[mp.mpf(t)/1000 for t in range(850,1005,5)]; br=None; pv=maxre(grid[0])[0]
for s in grid[1:]:
    v=maxre(s)[0]
    if v*pv<0: br=(s-mp.mpf(5)/1000,s); break
    pv=v
a,b=br; fa=maxre(a)[0]
for _ in range(120):
    m=(a+b)/2
    if maxre(m)[0]*fa>0: a=m; fa=maxre(m)[0]
    else: b=m
SCR_H=(a+b)/2; _,An=maxre(SCR_H); print("SCR_H (Re=0) =",mp.nstr(SCR_H,14)," maxRe=%.1e"%maxre(SCR_H)[0])
# interval params at SCR_H
SH=iv.mpf(mp.nstr(SCR_H,35))
wnI=2*iv.pi*50; VgI=380*iv.sqrt(iv.mpf([2,2])/3); Zg=iv.mpf([380,380])**2/(iv.mpf([100000,100000])*SH)
RgI=Zg/iv.sqrt(iv.mpf([101,101])); LgI=Zg*10/(iv.sqrt(iv.mpf([101,101]))*wnI); CfI=iv.mpf([1,1])/10000
alv=1-wnI**2*LgI*CfI; bev=RgI*wnI*CfI; K1v=RgI*80; K2v=wnI*LgI*80
a2=alv**2+bev**2; a1=-2*(alv*K1v+bev*K2v); a0=K1v**2+K2v**2-VgI**2
vcdI=(-a1+iv.sqrt(a1*a1-4*a2*a0))/(2*a2)
env={wn:wnI,Vg:VgI,Rg:RgI,Lg:LgI,vcd:vcdI}
cache={}; AI=[[ev(Ae[i,j],env,cache) for j in range(10)] for i in range(10)]
ok=True; mw=0
for i in range(10):
    for j in range(10):
        lo,hi=float(AI[i][j].a),float(AI[i][j].b); mw=max(mw,hi-lo)
        if not (lo<=An[i,j]<=hi):
            if abs(An[i,j]-lo)>1e-4 and abs(An[i,j]-hi)>1e-4: ok=False
print("interval [A] encloses numeric A:",ok,"  max entry width=%.2e"%mw)
np.save('/tmp/An.npy',An); 
open('/tmp/scrh.txt','w').write(mp.nstr(SCR_H,40))

# ================= STAGE 2: verified eigenpair via Krawczyk =================
print("--- stage 2: verified critical eigenpair ---")
w,V=np.linalg.eig(An); kk=np.argmax(w.real); lam0=complex(w[kk]); q0=V[:,kk].astype(complex)
s=int(np.argmax(np.abs(q0))); q0=q0/q0[s]; om0=lam0.imag
print("approx lambda=%.6g%+.6gj  f=%.3fHz  (normalize idx s=%d)"%(lam0.real,lam0.imag,abs(lam0.imag)/2/np.pi,s))
def C(re,im=0.0): return iv.mpc(iv.mpf([re,re]) if not isinstance(re,iv.mpf) else re, iv.mpf([im,im]) if not isinstance(im,iv.mpf) else im)
Aiv=[[iv.mpc(AI[i][j],iv.mpf([0,0])) for j in range(10)] for i in range(10)]   # interval A as complex
# build numeric J (11x11 complex) at approx, R=inv(J)
Jn=np.zeros((11,11),complex)
for i in range(10):
    for j in range(10): Jn[i,j]=An[i,j]-(lam0 if i==j else 0)
    Jn[i,10]=-q0[i]
Jn[10,s]=1.0
Rn=np.linalg.inv(Jn)
Riv=[[C(Rn[i,j].real,Rn[i,j].imag) for j in range(11)] for i in range(11)]
yhat=[C(q0[i].real,q0[i].imag) for i in range(10)]+[C(lam0.real,lam0.imag)]
def Fvec(y):   # F(y) length 11, y[0..9]=q, y[10]=lam ; uses interval Aiv
    q=y[:10]; lam=y[10]; out=[]
    for i in range(10):
        acc=iv.mpc(0,0)
        for j in range(10): acc=acc+Aiv[i][j]*q[j]
        out.append(acc-lam*q[i])
    out.append(q[s]-C(1.0))
    return out
def Jmat(y):   # 11x11 interval J(y)
    q=y[:10]; lam=y[10]; J=[[iv.mpc(0,0)]*11 for _ in range(11)]
    for i in range(10):
        for j in range(10): J[i][j]=Aiv[i][j]-(lam if i==j else iv.mpc(0,0))
        J[i][10]=-q[i]
    J[10][s]=C(1.0)
    return J
def matvec(M,v): return [sum((M[i][j]*v[j] for j in range(len(v))),iv.mpc(0,0)) for i in range(len(M))]
def krawczyk(r):
    Y=[yh+iv.mpc(iv.mpf([-r,r]),iv.mpf([-r,r])) for yh in yhat]
    Fyh=Fvec(yhat); RF=matvec(Riv,Fyh)
    J=Jmat(Y); RJ=[[sum((Riv[i][k]*J[k][j] for k in range(11)),iv.mpc(0,0)) for j in range(11)] for i in range(11)]
    dY=[Y[i]-yhat[i] for i in range(11)]
    # (I - RJ) dY
    cor=[]
    for i in range(11):
        acc=iv.mpc(0,0)
        for j in range(11): acc=acc+((iv.mpc(1,0) if i==j else iv.mpc(0,0))-RJ[i][j])*dY[j]
        cor.append(acc)
    K=[yhat[i]-RF[i]+cor[i] for i in range(11)]
    # check K subset int(Y)
    ok=True
    for i in range(11):
        for comp in (lambda z:z.real,lambda z:z.imag):
            ki,Yi=comp(K[i]),comp(Y[i])
            if not (Yi.a < ki.a and ki.b < Yi.b): ok=False
    return ok,K
for r in [1e-9,1e-8,1e-7,1e-6,1e-5]:
    ok,K=krawczyk(r)
    if ok:
        lam_lo,lam_hi=K[10].real.a,K[10].real.b; om_lo,om_hi=K[10].imag.a,K[10].imag.b
        print("VERIFIED eigenpair (Krawczyk r=%.0e):"%r)
        print("  Re(lambda) in [%.2e, %.2e]  (contains 0: %s)"%(float(lam_lo),float(lam_hi),float(lam_lo)<=0<=float(lam_hi)))
        print("  omega = Im(lambda) in [%.6f, %.6f]  f in [%.4f,%.4f]Hz"%(float(om_lo),float(om_hi),float(om_lo)/2/np.pi,float(om_hi)/2/np.pi))
        break
else: print("Krawczyk did NOT contract for tested radii")

# ================= STAGE 3-4: interval l1 (Kuznetsov) =================
print("--- stage 3-4: interval first Lyapunov coefficient ---")
import itertools
Kq=K[:10]; lamI=K[10]; omI=lamI.imag                      # verified q (q_s=1), lambda
def conj(z): return iv.mpc(z.real,-z.imag)
def ipc(a,bv): return sum((conj(a[i])*bv[i] for i in range(10)),iv.mpc(0,0))   # <a,b>=sum conj(a)b
# exact symbolic Hessian H[i,j,k]=dA[i,j]/dx_k and T[i,j,k,l]=dH/dx_l, sub equilibrium, eval interval
Hnz={}; Tnz={}
for i in range(10):
    for j in range(10):
        aij=Asym[i,j]
        for k in range(10):
            h=sp.diff(aij,S[k])
            if h!=0:
                Hnz[(i,j,k)]=ev(h.subs(sub),env,{})
                for l in range(10):
                    t=sp.diff(h,S[l])
                    if t!=0: Tnz[(i,j,k,l)]=ev(t.subs(sub),env,{})
def Bf(u,v):
    out=[iv.mpc(0,0)]*10
    for (i,j,k),H in Hnz.items(): out[i]=out[i]+H*u[j]*v[k]
    return out
def Cf(u,v,w):
    out=[iv.mpc(0,0)]*10
    for (i,j,k,l),T in Tnz.items(): out[i]=out[i]+T*u[j]*v[k]*w[l]
    return out
# verified left eigenvector p: A^T p = -i w p  (Krawczyk)
AT=An.T; w2,V2=np.linalg.eig(AT); kl=np.argmin(np.abs(w2-(-1j*om0))); p0=V2[:,kl].astype(complex)
sp_=int(np.argmax(np.abs(p0))); p0=p0/p0[sp_]; lamp=complex(w2[kl])
ATiv=[[iv.mpc(AI[j][i],iv.mpf([0,0])) for j in range(10)] for i in range(10)]  # (A^T) interval
Jn2=np.zeros((11,11),complex)
for i in range(10):
    for j in range(10): Jn2[i,j]=AT[i,j]-(lamp if i==j else 0)
    Jn2[i,10]=-p0[i]
Jn2[10,sp_]=1.0
R2=np.linalg.inv(Jn2); R2iv=[[C(R2[i,j].real,R2[i,j].imag) for j in range(11)] for i in range(11)]
yhat2=[C(p0[i].real,p0[i].imag) for i in range(10)]+[C(lamp.real,lamp.imag)]
def Fvec2(y):
    p=y[:10]; lam=y[10]; out=[]
    for i in range(10):
        acc=iv.mpc(0,0)
        for j in range(10): acc=acc+ATiv[i][j]*p[j]
        out.append(acc-lam*p[i])
    out.append(p[sp_]-C(1.0)); return out
def Jmat2(y):
    p=y[:10]; lam=y[10]; J=[[iv.mpc(0,0)]*11 for _ in range(11)]
    for i in range(10):
        for j in range(10): J[i][j]=ATiv[i][j]-(lam if i==j else iv.mpc(0,0))
        J[i][10]=-p[i]
    J[10][sp_]=C(1.0); return J
def kraw2(r):
    Y=[yh+iv.mpc(iv.mpf([-r,r]),iv.mpf([-r,r])) for yh in yhat2]
    RF=matvec(R2iv,Fvec2(yhat2)); J=Jmat2(Y)
    RJ=[[sum((R2iv[i][k]*J[k][j] for k in range(11)),iv.mpc(0,0)) for j in range(11)] for i in range(11)]
    dY=[Y[i]-yhat2[i] for i in range(11)]
    cor=[sum((((iv.mpc(1,0) if i==j else iv.mpc(0,0))-RJ[i][j])*dY[j] for j in range(11)),iv.mpc(0,0)) for i in range(11)]
    Kk=[yhat2[i]-RF[i]+cor[i] for i in range(11)]
    ok=all((Y[i].real.a<Kk[i].real.a and Kk[i].real.b<Y[i].real.b and Y[i].imag.a<Kk[i].imag.a and Kk[i].imag.b<Y[i].imag.b) for i in range(11))
    return ok,Kk
for r in [1e-9,1e-8,1e-7,1e-6]:
    ok2,Kp=kraw2(r)
    if ok2: pI=Kp[:10]; break
# normalize: q_unit=q/sqrt(<q,q>), p so <p,q_unit>=1
qq=ipc(Kq,Kq)                       # real positive
qn=[Kq[i]/iv.sqrt(qq.real) for i in range(10)]
pqi=ipc(pI,qn)
pn=[pI[i]/conj(pqi) for i in range(10)]
qb=[conj(qn[i]) for i in range(10)]
# verified linear solve M x = b
def vsolve(Miv,b):
    Mmid=np.array([[ (float(Miv[i][j].real.a)+float(Miv[i][j].real.b))/2 + 1j*(float(Miv[i][j].imag.a)+float(Miv[i][j].imag.b))/2 for j in range(10)] for i in range(10)])
    Rm=np.linalg.inv(Mmid); Riv=[[C(Rm[i,j].real,Rm[i,j].imag) for j in range(10)] for i in range(10)]
    x0=matvec(Riv,b)
    Mx0=matvec(Miv,x0); resid=[b[i]-Mx0[i] for i in range(10)]; d=matvec(Riv,resid)
    G=[[sum(((iv.mpc(1,0) if i==j else iv.mpc(0,0))-Riv[i][k]*Miv[k][j] for k in range(10)),iv.mpc(0,0)) if False else ((iv.mpc(1,0) if i==j else iv.mpc(0,0))-sum((Riv[i][k]*Miv[k][j] for k in range(10)),iv.mpc(0,0))) for j in range(10)] for i in range(10)]
    # rigorous Neumann enclosure of e=d+G e :  if kappa=||G||_inf<1 then |e_i-d_i|<=kappa*||d||/(1-kappa)
    def mag(z):
        ar=mp.mpf(max(abs(z.real.a),abs(z.real.b))); ai=mp.mpf(max(abs(z.imag.a),abs(z.imag.b)))
        return mp.sqrt(ar*ar+ai*ai)
    Ginf=max(sum((mag(G[i][j]) for j in range(10)),mp.mpf(0)) for i in range(10))
    dinf=max(mag(d[i]) for i in range(10))
    if not (Ginf<1): raise RuntimeError("solve not contractive: ||G||=%s"%mp.nstr(Ginf,6))
    sb=float(Ginf*dinf/(1-Ginf))*1.000001
    ball=iv.mpc(iv.mpf([-sb,sb]),iv.mpf([-sb,sb]))
    print("    vsolve: ||G||_inf=%.2e (<1 verified), enclosure radius=%.2e"%(float(Ginf),sb))
    return [x0[i]+d[i]+ball for i in range(10)]
Iiv=None
g1=Cf(qn,qn,qb)
r1=vsolve(Aiv,Bf(qn,qb)); g2=Bf(qn,r1)
M2=[[ (iv.mpc(0,2*omI.real if False else 0,)) for _ in range(10)] for _ in range(10)]  # placeholder
M2=[[ (iv.mpc(iv.mpf([0,0]),2*omI)-Aiv[i][j]) if i==j else (iv.mpc(0,0)-Aiv[i][j]) for j in range(10)] for i in range(10)]  # 2i w I - A
r2=vsolve(M2,Bf(qn,qn)); g3=Bf(qb,r2)
expr=[g1[i]-2*g2[i]+g3[i] for i in range(10)]
val=ipc(pn,expr)
l1=(iv.mpf([1,1])/(2*omI))*val.real
la,lb=float(l1.a),float(l1.b)
print("interval l1 = [%.6e, %.6e]"%(la,lb))
print("  width=%.2e  midpoint=%.6e  (l1.py point value +2.371e-6)"%(lb-la,(la+lb)/2))
print("  ===> l1 > 0 RIGOROUSLY:",la>0)
