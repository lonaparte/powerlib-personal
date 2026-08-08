import numpy as np, math
from scipy.optimize import brentq
Enom=1.0
def E_of(d,V,Xg,mq,Q):
    a=mq/Xg;b=1-mq*V*math.cos(d)/Xg;c=-(Enom+mq*Q)
    return (-b+math.sqrt(b*b-4*a*c))/(2*a)
def Pf_(d,V,Xg,mq,Q): return E_of(d,V,Xg,mq,Q)*V/Xg*math.sin(d)
def equil(P,Q,V,Xg,mq):
    dl=np.linspace(0.01,np.pi/2-1e-4,4000);Pr=[Pf_(x,V,Xg,mq,Q) for x in dl]
    i=int(np.argmax(Pr))
    if P>=Pr[i]: return None
    d=brentq(lambda x:Pf_(x,V,Xg,mq,Q)-P,1e-4,dl[i])
    E=E_of(d,V,Xg,mq,Q);Qf=(E*E-E*V*math.cos(d))/Xg
    return np.array([d,0.0,P,Qf])
def rhs(s,P,Q,V,Xg,M,D,mq,wc):
    d,om,Pf,Qf=s;E=Enom-mq*(Qf-Q)
    Pe=E*V/Xg*math.sin(d);Qe=(E*E-E*V*math.cos(d))/Xg
    return np.array([om,(P-Pf-D*om)/M,wc*(Pe-Pf),wc*(Qe-Qf)])
def ReC(P,Q,V,Xg,M,D,mq,wc,h=1e-7):
    st=equil(P,Q,V,Xg,mq)
    if st is None: return None
    A=np.zeros((4,4))
    for j in range(4):
        sp=st.copy();sp[j]+=h;sm=st.copy();sm[j]-=h
        A[:,j]=(rhs(sp,P,Q,V,Xg,M,D,mq,wc)-rhs(sm,P,Q,V,Xg,M,D,mq,wc))/(2*h)
    ev=np.linalg.eigvals(A);cx=[e for e in ev if abs(e.imag)>1e-7]
    return max(cx,key=lambda z:z.real) if cx else None
M,D,wc=0.02,0.05,2*np.pi*31.0
print("=== A. GFM 的 Q→V 汇率：|dRe/dQref|/|dRe/dV| 随 mq 与 Xg ===")
print(f"{'Xg':>5}{'mq':>6}{'dRe/dP':>9}{'dRe/dQ':>9}{'dRe/dV':>9}{'|Q/V|':>8}{'预测mq/(1+mq·g)':>16}")
P=1.30
for Xg,mq in [(0.1,0.05),(0.1,0.10),(0.1,0.20),(0.2,0.10),(0.3,0.10)]:
    h=1e-5;out={}
    for name,idx in [("P",0),("Q",1),("V",2)]:
        args=[P,0.0,1.0]
        ap=list(args);ap[idx]+=h;am=list(args);am[idx]-=h
        lp=ReC(ap[0],ap[1],ap[2],Xg,M,D,mq,wc);lm=ReC(am[0],am[1],am[2],Xg,M,D,mq,wc)
        out[name]=(lp.real-lm.real)/(2*h)
    st=equil(P,0.0,1.0,Xg,mq);d0=st[0];E0=E_of(d0,1.0,Xg,mq,0.0)
    g=(2*E0-1.0*math.cos(d0))/Xg; pred=mq/(1+mq*g)*(1.0/E0)
    print(f"{Xg:>5.2f}{mq:>6.2f}{out['P']:>9.4f}{out['Q']:>9.4f}{out['V']:>9.4f}"
          f"{abs(out['Q']/out['V']):>8.4f}{pred:>16.4f}")
print("(GFL 对照：|Q/V| ≈ Xg/(2cosθ*)，随 Xg 成正比，与控制参数无关)")
print()
print("=== B. GFM 频率选择性：纹波逃逸阈值 (P=1.30, Re=-0.015, f_H=3.50Hz) ===")
lam=ReC(P,0.0,1.0,0.1,M,D,0.1,wc); fH=abs(lam.imag)/2/np.pi
def escapes(ch,amp,fmod,T=40.0,dt=2e-4):
    st0=equil(P,0.0,1.0,0.1,0.1);s=st0.copy();s[0]+=1e-6
    W=2*np.pi*fmod;n=int(T/dt)
    for k in range(n):
        t=k*dt
        def f(ss,tt):
            Vg=1.0*(1+ (amp if ch=='V' else 0)*math.cos(W*tt))
            Pd=P+(amp if ch=='P' else 0)*math.cos(W*tt)
            return rhs(ss,Pd,0.0,Vg,0.1,M,D,0.1,wc)
        k1=f(s,t);k2=f(s+.5*dt*k1,t+.5*dt);k3=f(s+.5*dt*k2,t+.5*dt);k4=f(s+dt*k3,t+dt)
        s=s+dt/6*(k1+2*k2+2*k3+k4)
        if not np.isfinite(s[0]) or abs(s[0]-st0[0])>1.0: return True
    return False
def thresh(ch,fmod,lo,hi,it=4):
    if not escapes(ch,hi,fmod): return None,hi
    for _ in range(it):
        mid=math.sqrt(lo*hi)
        if escapes(ch,mid,fmod): hi=mid
        else: lo=mid
    return math.sqrt(lo*hi),None
print(f"  f_H={fH:.3f}Hz, 2f_H={2*fH:.3f}Hz")
print(f"{'通道':<6}{'频率':>9}{'阈值':>11}")
for ch,f,lo,hi in [('V',2*fH,1e-5,3e-2),('V',fH,1e-5,3e-2),('V',11.0,1e-4,1e-1),
                   ('P',2*fH,1e-4,3e-1),('P',fH,1e-4,3e-1),('P',11.0,1e-3,1.0)]:
    tc,no=thresh(ch,f,lo,hi)
    tag='2f_H' if abs(f-2*fH)<.1 else ('f_H' if abs(f-fH)<.1 else '离共振')
    if tc: print(f"{ch:<6}{f:>8.2f}Hz{tc:>11.5f}   {tag}")
    else:  print(f"{ch:<6}{f:>8.2f}Hz{'>'+format(no,'.3f'):>11}   {tag}：不逃逸")

print("\n=== B2. 换判据：稳态振荡幅值（V 纹波 ε=0.01,各频率）===")
def amp_response(ch,amp,fmod,T=60.0,dt=2e-4):
    st0=equil(P,0.0,1.0,0.1,0.1);s=st0.copy();s[0]+=1e-6
    W=2*np.pi*fmod;n=int(T/dt);mx=0.0
    for k in range(n):
        t=k*dt
        def f(ss,tt):
            Vg=1.0*(1+(amp if ch=='V' else 0)*math.cos(W*tt))
            Pd=P+(amp if ch=='P' else 0)*math.cos(W*tt)
            return rhs(ss,Pd,0.0,Vg,0.1,M,D,0.1,wc)
        k1=f(s,t);k2=f(s+.5*dt*k1,t+.5*dt);k3=f(s+.5*dt*k2,t+.5*dt);k4=f(s+dt*k3,t+dt)
        s=s+dt/6*(k1+2*k2+2*k3+k4)
        if k>int(40/dt): mx=max(mx,abs(s[0]-st0[0]))
    return mx
for f in [3.50,7.00,11.0]:
    mx=amp_response('V',0.01,f)
    print(f"  V ε=0.01 @ {f:5.2f}Hz: 稳态|Δδ|max={math.degrees(mx):8.3f}°")
for f in [3.50,7.00]:
    mx=amp_response('P',0.01,f)
    print(f"  P a=0.01 @ {f:5.2f}Hz: 稳态|Δδ|max={math.degrees(mx):8.3f}°")
