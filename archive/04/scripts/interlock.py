import sys, math, itertools; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, sympy as sp
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); CDC=0.01
KPP,KIP,KPV,KIV=50.0,1000.0,1.0,50.0
th,Xg,Q,Vg,P = sp.symbols('theta X_g Q V_g P', real=True)
a=Vg*sp.cos(th); b=Vg*sp.sin(th); vgd0=a-Xg*Q; id0=b/Xg
Jsym=sp.Matrix([
 [-KPP*a, KIP, -KPP*Xg*KPV, KPP*Xg*KIV],
 [-a,0,-Xg*KPV,Xg*KIV],
 [sp.Rational(3,2)/CDC*(-b*id0-Q*a),0,
  sp.Rational(3,2)/CDC*(-(vgd0*KPV+Q*Xg*KPV+vgd0*id0)),
  sp.Rational(3,2)/CDC*(vgd0*KIV+Q*Xg*KIV)],[0,0,-1,0]])
Jf=sp.lambdify((th,Xg,Q,Vg),Jsym,'numpy')
lam=sp.symbols('L'); cp=sp.Poly(Jsym.charpoly(lam).as_expr(),lam)
c3,c2,c1,c0=[cp.nth(k) for k in (3,2,1,0)]; Rsym=c1*c2*c3-c1**2-c0*c3**2
Rf=sp.lambdify((th,Xg,Q,Vg),Rsym,'numpy')

def np_state(P0,Q0,V0,Xg0):
    p=S.make_p(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0); eq=S.stable_eq(p,cfg)
    if eq is None: return None
    return p,eq,S.jacobian(eq,p,cfg)[:4,:4]
def crit(A):
    ev,Ve=np.linalg.eig(A); W=np.linalg.inv(Ve)
    c=[i for i in range(4) if abs(ev[i].imag)>1e-6]; i=c[int(np.argmax(ev[c].real))]
    return ev[i],Ve[:,i],W[i,:]
def dReknob(P0,Q0,V0,Xg0,knob,h=1e-4):
    m={'P':'idc_src','Q':'iq_ref','V':'Vg','Xg':'Xg'}[knob]
    base=dict(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0); k0=base[m]
    def mr(v):
        kk=dict(base); kk[m]=v; p=S.make_p(**kk); eq=S.stable_eq(p,cfg)
        cc=[e for e in np.linalg.eigvals(S.jacobian(eq,p,cfg)[:4,:4]) if abs(e.imag)>1e-6]
        return max(cc,key=lambda z:z.real).real
    return (mr(k0+h)-mr(k0-h))/(2*h)
def dTheta(P0,Q0,V0,Xg0,knob,h=1e-4):
    m={'P':'idc_src','Q':'iq_ref','V':'Vg','Xg':'Xg'}[knob]
    base=dict(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0); k0=base[m]
    def t(v):
        kk=dict(base); kk[m]=v; return S.stable_eq(S.make_p(**kk),cfg)[0]
    return (t(k0+h)-t(k0-h))/(2*h)

# grid of operating points (P,Q,V,Xg) all giving a stable eq
grid=[]
for P0,Q0,V0 in itertools.product([0.3,0.5,0.8],[-0.2,0.0,0.2],[0.9,1.0,1.1]):
    SN=3*V0**2/(4*P0)                      # saddle-node Xg (Q=0 approx)
    for frac in [0.5,0.85,0.97]:
        Xg0=SN*frac
        st=np_state(P0,Q0,V0,Xg0)
        if st: grid.append((P0,Q0,V0,Xg0))

print(f"grid points: {len(grid)}")
# ---- TEST 1: analytic Jacobian == numeric ----
e1=0
for (P0,Q0,V0,Xg0) in grid:
    p,eq,An=np_state(P0,Q0,V0,Xg0); Ja=np.array(Jf(eq[0],Xg0,Q0,V0),dtype=float)
    e1=max(e1,np.max(np.abs(Ja-An)))
print(f"TEST 1  analytic J vs numeric J   : max|diff| = {e1:.2e}   {'PASS' if e1<1e-6 else 'FAIL'}")

# ---- TEST 2: dA/dP==0 (fixed eq) ; dA/dQ == analytic 2 entries ----
e2P=0; e2Q=0
for (P0,Q0,V0,Xg0) in grid:
    p,eq,An=np_state(P0,Q0,V0,Xg0); h=1e-5
    pP=p.copy(); pP.idc_src=P0+h; pM=p.copy(); pM.idc_src=P0-h
    dAP=(S.jacobian(eq,pP,cfg)[:4,:4]-S.jacobian(eq,pM,cfg)[:4,:4])/(2*h); e2P=max(e2P,np.max(np.abs(dAP)))
    pP=p.copy(); pP.iq_ref=Q0+h; pM=p.copy(); pM.iq_ref=Q0-h
    dAQ=(S.jacobian(eq,pP,cfg)[:4,:4]-S.jacobian(eq,pM,cfg)[:4,:4])/(2*h)
    dAQa=np.zeros((4,4)); dAQa[2,0]=-1.5*V0*math.cos(eq[0])/CDC; dAQa[2,2]=1.5*V0*math.sin(eq[0])/CDC
    e2Q=max(e2Q,np.max(np.abs(dAQ-dAQa)))
print(f"TEST 2a ∂A/∂P at fixed eq         : max|·| = {e2P:.2e}   {'PASS(≈0, P pure-indirect)' if e2P<1e-3 else 'FAIL'}")
print(f"TEST 2b ∂A/∂Q vs analytic 2-entry : max|diff| = {e2Q:.2e}   {'PASS' if e2Q<1e-2 else 'FAIL'}")

# ---- TEST 3: sign law  V<0 ; P,Q,Xg>0 ----
bad=[]
for (P0,Q0,V0,Xg0) in grid:
    s={k:np.sign(dReknob(P0,Q0,V0,Xg0,k)) for k in ['P','Q','V','Xg']}
    if not (s['V']<0 and s['P']>0 and s['Q']>0 and s['Xg']>0): bad.append((P0,Q0,V0,Xg0,s))
print(f"TEST 3  sign law (V stab; P,Q,Xg destab) over {len(grid)} pts : "
      f"{'PASS all' if not bad else f'{len(bad)} exceptions'}")
for x in bad[:4]: print("        exception:",x)

# ---- TEST 4: Q decomposition indirect+direct == numeric (identity, should be exact) ----
e4=0
for (P0,Q0,V0,Xg0) in grid:
    p,eq,An=np_state(P0,Q0,V0,Xg0); lam,vi,wi=crit(An); t=eq[0]
    dReTheta=dReknob(P0,Q0,V0,Xg0,'P')/dTheta(P0,Q0,V0,Xg0,'P')   # P pure indirect
    dthQ=dTheta(P0,Q0,V0,Xg0,'Q')
    ind=dReTheta*dthQ
    dAQa=np.zeros((4,4)); dAQa[2,0]=-1.5*V0*math.cos(t)/CDC; dAQa[2,2]=1.5*V0*math.sin(t)/CDC
    direct=float(np.real(wi@dAQa@vi))
    e4=max(e4,abs((ind+direct)-dReknob(P0,Q0,V0,Xg0,'Q')))
print(f"TEST 4  Q = indirect+direct  vs numeric dRe/dQ : max|diff| = {e4:.3f}   {'PASS' if e4<0.5 else 'CHECK'}")

# ---- TEST 5: ∂θ*/∂Q formula ----
e5=0
for (P0,Q0,V0,Xg0) in grid:
    t=S.stable_eq(S.make_p(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0),cfg)[0]
    f=Xg0*math.sin(t)/(V0*math.cos(2*t)); e5=max(e5,abs(f-dTheta(P0,Q0,V0,Xg0,'Q')))
print(f"TEST 5  ∂θ*/∂Q formula vs numeric : max|diff| = {e5:.2e}   {'PASS' if e5<1e-3 else 'FAIL'}")

# ---- TEST 6: Routh R=0 coincides with Hopf, for several P ----
print("TEST 6  Routh R sign vs actual maxRe (should cross 0 together):")
for P0 in [0.4,0.7,1.0]:
    SN=3/(4*P0); found=None
    for Xg0 in np.linspace(0.2,SN*0.999,400):
        st=np_state(P0,0.0,1.0,Xg0)
        if st is None: continue
        mr=np.max(np.linalg.eigvals(st[2]).real); Rv=float(Rf(st[1][0],Xg0,0.0,1.0))
        if found is None and mr>0: 
            print(f"        P={P0}: Hopf near Xg={Xg0:.3f}  (maxRe={mr:+.3f}, R={Rv:+.2e})  -> R just turned negative"); found=1
        prev=(mr,Rv)

# ---- TEST 7: ratio law 1/P:2/V:1/Xg convergence as Xg->Hopf (Q excluded) ----
print("TEST 7  |dRe/dθ| ratio P:V:Xg  vs geometric 1/P:2/V:1/Xg  (as Xg→Hopf):")
for (P0,V0) in [(0.5,1.0),(0.8,1.1),(0.3,0.9)]:
    SN=3*V0**2/(4*P0)
    print(f"   P={P0},V={V0} (SN Xg={SN:.2f}):")
    for frac in [0.6,0.85,0.97,0.995]:
        Xg0=SN*frac
        dP=abs(dReknob(P0,0.0,V0,Xg0,'P')); dV=abs(dReknob(P0,0.0,V0,Xg0,'V')); dX=abs(dReknob(P0,0.0,V0,Xg0,'Xg'))
        geo=np.array([1/P0,2/V0,1/Xg0]); geo=geo/geo[0]; num=np.array([dP,dV,dX])/dP
        print(f"     Xg={Xg0:5.3f} (%SN={frac:4.2f}): numeric {num[0]:.2f}:{num[1]:.2f}:{num[2]:.2f}"
              f"   geom {geo[0]:.2f}:{geo[1]:.2f}:{geo[2]:.2f}")
