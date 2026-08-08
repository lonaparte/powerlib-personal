import numpy as np, math
exec(open('/tmp/claude-0/-home-user/1d9de531-4d6c-58ef-8110-d2e68526464e/scratchpad/t3a.py').read().split('for tag,Q,V,Xg in')[0])
G6=dict(kp=35,ki=600,kpv=1,kiv=50,C=0.01)
G7=dict(kp=70,ki=2000,kpv=1.5,kiv=75,C=0.008)
print("== 批B-1: 新增益组 G6/G7 @Xg=1.0 ==")
for tag,g in [("C4:G6(kp35,ki600)",G6),("C5:G7(kp70,ki2000,kpv1.5,C.008)",G7)]:
    P0=P_margin(g,0.0,1.0,1.0)
    if P0 is None: print(f"[{tag}] 无裕度点"); continue
    lam=mrc(Amat(P0,0,1.0,1.0,g));fH=abs(lam.imag)/2/math.pi
    gV=pump(P0,0,1.0,1.0,g,'V')
    print(f"[{tag}] P0={P0:.4f} Re={lam.real:+.3f} f_H={fH:.2f}Hz 泵|wC_Vv|={gV:.0f}")
    for ch,fm,lo,hi,t in [('V',fH,3e-5,2e-2,'f_H'),('V',2*fH,1e-4,3e-2,'2f_H'),
                           ('V',1.55*fH,3e-4,1e-1,'离共振'),('P',2*fH,1e-4,5e-2,'2f_H')]:
        tc,no=thr(g,P0,0.0,1.0,1.0,ch,fm,lo,hi)
        print(f"    {ch}@{t}({fm:.2f}Hz): {'ε_c≈%.5f'%tc if tc else '>%.3f 不逃逸'%no}")
print("== 批B-2: 裕度标度（G1@Xg=1, V@2f_H 阈值 vs 裕度）==")
g=dict(kp=50,ki=1000,kpv=1,kiv=50,C=0.01)
for tgt in (-0.05,-0.15,-0.30):
    P0=P_margin(g,0.0,1.0,1.0,target=tgt)
    lam=mrc(Amat(P0,0,1.0,1.0,g));fH=abs(lam.imag)/2/math.pi
    tc,no=thr(g,P0,0.0,1.0,1.0,'V',2*fH,5e-5,2e-2,it=4)
    print(f"  裕度={tgt}: P0={P0:.4f} f_H={fH:.2f} → ε_c(2f_H)={'%.5f'%tc if tc else '>%.3f'%no}  比值ε_c/|Re|={tc/abs(tgt) if tc else float('nan'):.5f}")
print("== 批B-3: 舌宽（G1@Xg=1,裕度-0.15,幅度=3×ε_c(2f_H), 频率偏离 ±15%）==")
P0=P_margin(g,0.0,1.0,1.0);lam=mrc(Amat(P0,0,1.0,1.0,g));fH=abs(lam.imag)/2/math.pi
tc,_=thr(g,P0,0.0,1.0,1.0,'V',2*fH,1e-4,3e-2)
for mult in (1.85,2.0,2.15):
    e=esc(g,P0,0.0,1.0,1.0,'V',3*tc,mult*fH)
    print(f"  V@{mult:.2f}×f_H 幅度={3*tc:.5f}: {'逃逸' if e else '不逃逸'}")
