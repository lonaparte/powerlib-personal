#!/usr/bin/env python3
"""Sanity-check ScrAxis (parametric): SCR(Lg)=Vn²/(Sn·Lg·wn·zfac) strictly decreasing, and a Hopf
root Lg*∈(Lg₀,Lg₁) maps to SCR*∈(SCR(Lg₁),SCR(Lg₀)) (anti-monotone interval)."""
import numpy as np
def scr(Vn,Sn,wn,zfac,Lg): return Vn**2/(Sn*Lg*wn*zfac)
rng=np.random.default_rng(1); ok=True
for _ in range(5):
    Vn,Sn,wn,zfac=rng.uniform(0.5,3,4); Lg0,Lg1=sorted(rng.uniform(0.05,0.5,2))
    Lgs=Lg0+(Lg1-Lg0)*rng.uniform(0.1,0.9)         # a root in (Lg0,Lg1)
    dec = scr(Vn,Sn,wn,zfac,Lg1) < scr(Vn,Sn,wn,zfac,Lgs) < scr(Vn,Sn,wn,zfac,Lg0)  # strict anti
    interval = scr(Vn,Sn,wn,zfac,Lg1) < scr(Vn,Sn,wn,zfac,Lgs) < scr(Vn,Sn,wn,zfac,Lg0)
    ok &= dec and interval
    print(f"Lg*={Lgs:.3f}∈({Lg0:.3f},{Lg1:.3f}) → SCR(Lg₁)={scr(Vn,Sn,wn,zfac,Lg1):.3f} < "
          f"SCR*={scr(Vn,Sn,wn,zfac,Lgs):.3f} < SCR(Lg₀)={scr(Vn,Sn,wn,zfac,Lg0):.3f}  {'OK' if dec else 'BAD'}")
print("PASS — SCR strictly anti in Lg; SCR*∈(SCR Lg₁, SCR Lg₀)" if ok else "FAIL")
