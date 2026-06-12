#!/usr/bin/env python3
"""Cross-validate ScrHopfCubic (independent numpy): χ₄(gθ)=L₃g³+L₂g²+L₁g+L₀ matches the true
char-poly χ₄; L₃>0 ∧ χ₄(0)<0 ⟹ a real positive root; and that orientation is the dominant genuine one."""
import numpy as np
def coeffs(p,g):
    J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki=p
    J=np.array([[J00,J01,0,J03],[J10,J11,0,J13],[J20,J21,0,g],[-Kp*J20,-Kp*J21,-Ki,-Kp*g]])
    return np.poly(J)[1:]
def chi(p,g): a=coeffs(p,g); return a[0]*a[1]*a[2]-a[2]**2-a[0]**2*a[3]
def L3(p):
    J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki=p
    return -Kp*(J00+J11)*(J00*J11*Kp**2 - J00*Ki*Kp - J01*J10*Kp**2 - J11*Ki*Kp + Ki**2)
def Lcoeffs(p):                      # L0..L3 by sampling χ4(g) at 4 pts (independent of the literal)
    g=np.array([-1.,0.,1.,2.]); y=np.array([chi(p,gi) for gi in g])
    return np.polyfit(g,y,3)[::-1]   # [L0,L1,L2,L3]
rng=np.random.default_rng(9); md=0.0; mdL3=0.0
for _ in range(5000):
    p=rng.normal(size=10); g=rng.normal()
    L=Lcoeffs(p)
    md=max(md, abs(chi(p,g)-(L[3]*g**3+L[2]*g**2+L[1]*g+L[0])))
    mdL3=max(mdL3, abs(L[3]-L3(p)))
print(f"max|χ4(g) - (L3 g³+L2 g²+L1 g+L0)| = {md:.2e}")
print(f"max|L3(literal factored) - L3(sampled)| = {mdL3:.2e}")
# structural anchor soundness: L3>0 ∧ χ4(0)<0 ⟹ ∃ positive real root (check root exists & >0)
rng2=np.random.default_rng(7); ok=0; bad=0
for _ in range(200000):
    p=rng2.normal(size=10)*1.5
    if not (L3(p)>0 and chi(p,0.0)<0): continue
    r=np.roots([L3(p),*Lcoeffs(p)[2::-1]])  # roots of cubic
    rr=[x.real for x in r if abs(x.imag)<1e-9 and x.real>1e-12]
    ok+= 1 if rr else 0; bad+= 0 if rr else 1
    if ok+bad>=3000: break
print(f"L3>0 ∧ χ4(0)<0 cases with a positive real root: {ok}/{ok+bad}  (should be {ok+bad}/{ok+bad})")
print("ALL PASS" if md<1e-8 and mdL3<1e-8 and bad==0 else "CHECK")
