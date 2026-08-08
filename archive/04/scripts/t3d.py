import numpy as np, math
exec(open('/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/t3a.py').read().split('for tag,Q,V,Xg in')[0])
def P_margin2(g,Q,V,Xg,target=-0.15,n=500):
    # 先粗定 Hopf(零穿越),再牛顿抛光到 Re=target
    ps=Psn_num(Q,V,Xg);prev=None;ph=None
    for P in np.linspace(0.3*ps,0.9999*ps,n):
        lam=mrc(Amat(P,Q,V,Xg,g))
        if lam is None:continue
        if prev is not None and prev[1]<0<=lam.real: ph=0.5*(prev[0]+P);break
        prev=(P,lam.real)
    if ph is None:return None
    h=2e-6;s=(mrc(Amat(ph+h,Q,V,Xg,g)).real-mrc(Amat(ph-h,Q,V,Xg,g)).real)/(2*h)
    P0=ph-abs(target)/s
    for _ in range(4):
        r=mrc(Amat(P0,Q,V,Xg,g)).real
        P0-=(r-target)/s
    return P0
g=dict(kp=50,ki=1000,kpv=1,kiv=50,C=0.01)
print("== B-2 重做: 裕度标度 G1@Xg=1, V@2f_H ==")
for tgt in (-0.05,-0.15,-0.30):
    P0=P_margin2(g,0.0,1.0,1.0,target=tgt)
    lam=mrc(Amat(P0,0,1.0,1.0,g));fH=abs(lam.imag)/2/math.pi
    tc,no=thr(g,P0,0.0,1.0,1.0,'V',2*fH,5e-5,2e-2,it=5)
    print(f"  裕度={-tgt:.2f}: Re={lam.real:+.3f} f_H={fH:.2f} ε_c(2f_H)={'%.5f'%tc if tc else '>%.3f'%no}  ε_c/裕度={tc/abs(tgt) if tc else float('nan'):.5f}")
print("== B-3: 舌宽 G1@Xg=1 裕度0.15 ==")
P0=P_margin2(g,0.0,1.0,1.0);lam=mrc(Amat(P0,0,1.0,1.0,g));fH=abs(lam.imag)/2/math.pi
tc,_=thr(g,P0,0.0,1.0,1.0,'V',2*fH,1e-4,3e-2,it=5)
print(f"  基准: ε_c(2.00×f_H)={tc:.5f}")
for mult in (1.80,1.90,2.10,2.20):
    e=esc(g,P0,0.0,1.0,1.0,'V',3*tc,mult*fH)
    print(f"  V@{mult:.2f}×f_H 幅度=3×ε_c: {'逃逸' if e else '不逃逸'}")
print("== C 补: 高精度 P/V @2f_H 其余两配置 ==")
for tag,Q,V,Xg in [("Xg=1.0",0.0,1.0,1.0),("Q=0.15,Xg=1.0",0.15,1.0,1.0)]:
    P0=P_margin2(g,Q,V,Xg)
    lam=mrc(Amat(P0,Q,V,Xg,g));fH=abs(lam.imag)/2/math.pi
    tV,_=thr(g,P0,Q,V,Xg,'V',2*fH,2e-4,5e-3,it=6)
    tP,_=thr(g,P0,Q,V,Xg,'P',2*fH,2e-4,8e-3,it=6)
    print(f"  [{tag}] Re={lam.real:+.3f}: ε_c(V)={tV:.5f} ε_c(P)={tP:.5f}  P/V={tP/tV:.3f}")
