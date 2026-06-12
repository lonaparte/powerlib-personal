import sympy as sp
J00,J01,J03,J10,J11,J13,J20,J21,g,Kp,Ki,lam=sp.symbols(
 'J00 J01 J03 J10 J11 J13 J20 J21 g Kp Ki lam')
M=sp.Matrix([[J00,J01,0,J03],[J10,J11,0,J13],[J20,J21,0,g],[-Kp*J20,-Kp*J21,-Ki,-Kp*g]])
co=sp.Matrix(M).charpoly(lam).all_coeffs(); a1,a2,a3,a4=[sp.expand(c) for c in co[1:5]]
chi4=sp.expand(a1*a2*a3-a3**2-a1**2*a4)
P=sp.Poly(chi4,g); L=[sp.expand(P.coeff_monomial(g**k)) for k in range(4)]   # L0..L3
print("deg_g χ4 =",P.degree())
print("L3 (leading, gθ³) factored:", sp.factor(L[3]))
print("L3 #terms:", len(sp.Poly(L[3],J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki).terms()))
for k in range(4): print(f"L{k} #terms:", len(sp.Poly(L[k],J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki).terms()) if L[k]!=0 else 0)
# emit Lean literals (gθ-free; vars J.., Kp_pll, Ki_pll)
VM={J00:'J00',J01:'J01',J03:'J03',J10:'J10',J11:'J11',J13:'J13',J20:'J20',J21:'J21',Kp:'Kp_pll',Ki:'Ki_pll'}
VARS=[J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki]
def lean(e):
    Q=sp.Poly(sp.expand(e),*VARS); out=[]
    for mon,c in sorted(Q.terms(),key=lambda t:(-sum(t[0]),t[0])):
        c=int(c); sgn='-' if c<0 else '+'
        parts=[f"({abs(c)}:ℝ)"]+[f"{VM[v]}^{ex}" if ex>1 else VM[v] for v,ex in zip(VARS,mon) if ex>0]
        out.append((sgn,'*'.join(parts)))
    if not out: return "(0:ℝ)"
    r=("- " if out[0][0]=='-' else "")+out[0][1]
    for sg,t in out[1:]: r+=f" {sg} {t}"
    return r
open('/tmp/cubic_lean.txt','w').write("".join(f"L{k}:=\n"+lean(L[k])+"\n\n" for k in range(4)))
# verify numerically: chi4(g) == L3 g^3 + L2 g^2 + L1 g + L0 ; and orientation in genuine cases
import numpy as np
f=sp.lambdify((J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki,g),chi4,'numpy')
fl=[sp.lambdify((J00,J01,J03,J10,J11,J13,J20,J21,Kp,Ki),L[k],'numpy') for k in range(4)]
rng=np.random.default_rng(5); md=0.0
for _ in range(4000):
    p=rng.normal(size=10); gg=rng.normal()
    md=max(md,abs(f(*p,gg)-(fl[3](*p)*gg**3+fl[2](*p)*gg**2+fl[1](*p)*gg+fl[0](*p))))
print("max|chi4 - (L3g³+L2g²+L1g+L0)| =",f"{md:.2e}")
# orientation in GENUINE off-fold cases (sign-change + a1,a3>0 on interval), reuse logic
def coeffs(p,gv):
    J=np.array([[p[0],p[1],0,p[2]],[p[3],p[4],0,p[5]],[p[6],p[7],0,gv],[-p[8]*p[6],-p[8]*p[7],-p[9],-p[8]*gv]])
    return np.poly(J)[1:]
def chi(p,gv):a=coeffs(p,gv);return a[0]*a[1]*a[2]-a[2]**2-a[0]**2*a[3]
rng2=np.random.default_rng(202); seen={'L3>0,χ0<0':0,'L3<0,χ0>0':0,'other':0}
for _ in range(300000):
    p=rng2.normal(size=10)*1.5; g1=rng2.uniform(0.2,3)
    if not chi(p,0.0)<0<chi(p,g1): continue
    gg=np.linspace(1e-9,g1,40)
    if not all(coeffs(p,gv)[0]>0 and coeffs(p,gv)[2]>0 for gv in gg): continue
    L3=fl[3](*p); x0=chi(p,0.0)
    k='L3>0,χ0<0' if (L3>0 and x0<0) else ('L3<0,χ0>0' if (L3<0 and x0>0) else 'other')
    seen[k]+=1
    if sum(seen.values())>=200: break
print("genuine-case orientation tally:",seen)
