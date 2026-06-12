#!/usr/bin/env python3
"""Emit Lean-formatted a1..a4, χ4 err=0 part and droop term for M4droop; verify χ4 = err0 + droop."""
import sympy as sp
J00,J01,J03,J10,J11,J13,J20,J21,g,Kp,Ki,lam=sp.symbols(
 'J00 J01 J03 J10 J11 J13 J20 J21 g Kp Ki lam')
M=sp.Matrix([[J00,J01,0,J03],[J10,J11,0,J13],[J20,J21,0,g],[-Kp*J20,-Kp*J21,-Ki,-Kp*g]])
co=sp.Matrix(M).charpoly(lam).all_coeffs()
a1,a2,a3,a4=sp.expand(co[1]),sp.expand(co[2]),sp.expand(co[3]),sp.expand(co[4])
chi4=sp.expand(a1*a2*a3-a3**2-a1**2*a4)
err0=sp.expand(chi4.subs([(J03,0),(J13,0)]))     # err=0 part (∝ g)
droop=sp.expand(chi4-err0)                        # droop term (∝ J03,J13)
print("VERIFY χ4 = err0 + droop :", sp.expand(chi4-(err0+droop))==0)
print("VERIFY err0 has factor g (Kp*g | err0)? :", sp.rem(err0, Kp*g, g)==0)
print("VERIFY droop vanishes at J03=J13=0 :", sp.expand(droop.subs([(J03,0),(J13,0)]))==0)
print("sizes: a1",len(sp.Poly(a1).terms()),"a2",len(sp.Poly(a2).terms()),
      "a3",len(sp.Poly(a3).terms()),"a4",len(sp.Poly(a4).terms()),
      "err0",len(sp.Poly(err0).terms()),"droop",len(sp.Poly(droop).terms()))

VM={J00:'J00',J01:'J01',J03:'J03',J10:'J10',J11:'J11',J13:'J13',J20:'J20',J21:'J21',
    g:'gθ',Kp:'Kp_pll',Ki:'Ki_pll'}
VARS=[J00,J01,J03,J10,J11,J13,J20,J21,g,Kp,Ki]
def lean(expr):
    P=sp.Poly(sp.expand(expr),*VARS); out=[]
    for mon,c in sorted(P.terms(),key=lambda t:(-sum(t[0]),t[0])):
        c=int(c); sign='-' if c<0 else '+'
        parts=[f"({abs(c)}:ℝ)"]+[f"{VM[v]}^{e}" if e>1 else VM[v] for v,e in zip(VARS,mon) if e>0]
        out.append((sign,'*'.join(parts)))
    if not out: return "(0:ℝ)"
    r=("- " if out[0][0]=='-' else "")+out[0][1]
    for s,t in out[1:]: r+=f" {s} {t}"
    return r
open('/tmp/chi4_lean.txt','w').write(
 "A1:=\n"+lean(a1)+"\n\nA2:=\n"+lean(a2)+"\n\nA3:=\n"+lean(a3)+"\n\nA4:=\n"+lean(a4)+
 "\n\nERR0:=\n"+lean(err0)+"\n\nDROOP:=\n"+lean(droop)+"\n")
print("wrote /tmp/chi4_lean.txt")
