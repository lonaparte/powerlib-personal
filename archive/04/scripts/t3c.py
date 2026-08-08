import numpy as np, math
exec(open('/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/t3a.py').read().split('for tag,Q,V,Xg in')[0])
g=dict(kp=50,ki=1000,kpv=1,kiv=50,C=0.01)
print("== 高精度 P/V 阈值比 @2f_H（6 次二分,分辨率~±6%）==")
for tag,Q,V,Xg in [("C1:Xg=0.7",0.0,1.0,0.7),("原配置:Xg=1.0",0.0,1.0,1.0),("C3:Q=0.15",0.15,1.0,1.0)]:
    P0=P_margin(g,Q,V,Xg)
    lam=mrc(Amat(P0,Q,V,Xg,g));fH=abs(lam.imag)/2/math.pi
    tV,_=thr(g,P0,Q,V,Xg,'V',2*fH,3e-4,5e-3,it=6)
    tP,_=thr(g,P0,Q,V,Xg,'P',2*fH,3e-4,8e-3,it=6)
    print(f"  [{tag}] Re={lam.real:+.3f}: ε_c(V)={tV:.5f} ε_c(P)={tP:.5f}  P/V={tP/tV:.3f}")
