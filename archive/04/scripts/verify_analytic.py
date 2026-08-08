import sys, math; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg()
kp=50.0
print("verify  δ = ½·kp_pll·Vg·cosΔθ*   (kp_pll=50):")
print(f"{'Xg':>6}{'Δθ*':>9}{'δ_pred':>9}{'δ_actual':>10}{'dRe/dV_pred':>13}{'dRe/dV_act':>12}")
for Xg in [0.5,1.0,1.45]:
    p=S.make_p(Xg=Xg); eq=S.stable_eq(p,cfg); A=S.jacobian(eq,p,cfg)
    ev=np.linalg.eigvals(A); comp=[e for e in ev if abs(e.imag)>1e-6]
    lam=max(comp,key=lambda z:z.real); th=eq[0]
    dpred=0.5*kp*p.Vg*math.cos(th)
    # dRe/dV direct term prediction = -½ kp cosΔθ*
    dReV_pred=-0.5*kp*math.cos(th)
    # actual dRe/dV numeric
    h=1e-4
    def remode(Vg):
        pp=S.make_p(Xg=Xg,Vg=Vg); e=S.stable_eq(pp,cfg); a=S.jacobian(e,pp,cfg)
        c=[z for z in np.linalg.eigvals(a) if abs(z.imag)>1e-6]; return max(c,key=lambda z:z.real).real
    dReV_act=(remode(1.0+h)-remode(1.0-h))/(2*h)
    print(f"{Xg:>6.2f}{th:>9.4f}{dpred:>9.2f}{-lam.real:>10.2f}{dReV_pred:>13.2f}{dReV_act:>12.2f}")

print("\nverify near-boundary collapse ratio  |dλ/dθ| ∝ |∂s/∂θ| = {P:1/P, V:2/V, Xg:1/Xg}")
print("  s = -4·P·Xg/(3·V²);  at P=0.5,V=1,Xg=1.45 →  1/P : 2/V : 1/Xg = %.2f : %.2f : %.2f"
      %(1/0.5, 2/1.0, 1/1.45))
print("  numeric |dλ/dθ| at Xg=1.45:  P=318.1  V=329.9  Xg=109.9  → ratio %.2f : %.2f : %.2f"
      %(318.1/109.9, 329.9/109.9, 109.9/109.9))
print("  predicted ratio normalised:  %.2f : %.2f : %.2f"%((1/0.5)/(1/1.45),(2/1.0)/(1/1.45),1.0))
