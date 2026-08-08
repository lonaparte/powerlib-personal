import sys, math, itertools; sys.path.insert(0,"/home/user/work-sync/codes/gfl-5d-ou/src")
import numpy as np, warnings; warnings.filterwarnings("ignore")
from gfl_5d_ou_sim import system as S
cfg=S.make_cfg(); CDC=0.01
def st(P0,Q0,V0,Xg0):
    p=S.make_p(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0); eq=S.stable_eq(p,cfg)
    if eq is None: return None
    A=S.jacobian(eq,p,cfg)[:4,:4]
    if np.max(np.linalg.eigvals(A).real)>0: return None
    return p,eq,A
def crit(A):
    ev,Ve=np.linalg.eig(A); W=np.linalg.inv(Ve); c=[i for i in range(4) if abs(ev[i].imag)>1e-6]
    if not c: return None
    i=c[int(np.argmax(ev[c].real))]; return ev[i],Ve[:,i],W[i,:]
def dRe(P0,Q0,V0,Xg0,kn,h=1e-4):
    m={'P':'idc_src','Q':'iq_ref','V':'Vg','Xg':'Xg'}[kn]; base=dict(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0)
    def mr(v):
        kk=dict(base); kk[m]=v; e=S.stable_eq(S.make_p(**kk),cfg)
        if e is None: return np.nan
        cc=[z for z in np.linalg.eigvals(S.jacobian(e,S.make_p(**kk),cfg)[:4,:4]) if abs(z.imag)>1e-6]
        return max(cc,key=lambda z:z.real).real if cc else np.nan
    return (mr(base[m]+h)-mr(base[m]-h))/(2*h)
def dTh(P0,Q0,V0,Xg0,kn,h=1e-4):
    m={'P':'idc_src','Q':'iq_ref','V':'Vg','Xg':'Xg'}[kn]; base=dict(idc_src=P0,iq_ref=Q0,Vg=V0,Xg=Xg0)
    def t(v):
        kk=dict(base); kk[m]=v; e=S.stable_eq(S.make_p(**kk),cfg); return e[0] if e is not None else np.nan
    return (t(base[m]+h)-t(base[m]-h))/(2*h)

grid=[]
for P0,Q0,V0 in itertools.product([0.3,0.5,0.8],[-0.2,0.0,0.2],[0.9,1.0,1.1]):
    SN=3*V0**2/(4*P0)
    for frac in [0.5,0.85,0.95]:
        if st(P0,Q0,V0,SN*frac): grid.append((P0,Q0,V0,SN*frac,frac))

# ---- Q decomposition using NUMERIC ∂θ*/∂Q (tests the identity, not the Q=0 formula) ----
e4=0; worst=None
for (P0,Q0,V0,Xg0,fr) in grid:
    p,eq,A=st(P0,Q0,V0,Xg0); cm=crit(A)
    if not cm: continue
    lam,vi,wi=cm; t=eq[0]
    dRT=dRe(P0,Q0,V0,Xg0,'P')/dTh(P0,Q0,V0,Xg0,'P')
    ind=dRT*dTh(P0,Q0,V0,Xg0,'Q')
    dAQ=np.zeros((4,4)); dAQ[2,0]=-1.5*V0*math.cos(t)/CDC; dAQ[2,2]=1.5*V0*math.sin(t)/CDC
    direct=float(np.real(wi@dAQ@vi))
    d=abs((ind+direct)-dRe(P0,Q0,V0,Xg0,'Q')); 
    if d>e4: e4=d; worst=(P0,Q0,V0,round(Xg0,2),fr)
print(f"Q decomposition (indirect_NUM + direct) vs dRe/dQ : max|diff|={e4:.3f}  worst={worst}")

# ---- ∂θ*/∂Q formula restricted to Q=0 ----
e5=0
for (P0,Q0,V0,Xg0,fr) in grid:
    if Q0!=0.0: continue
    t=st(P0,0,V0,Xg0)[1][0]
    f=Xg0*math.sin(t)/(V0*math.cos(2*t)); e5=max(e5,abs(f-dTh(P0,0,V0,Xg0,'Q')))
print(f"∂θ*/∂Q formula (Q=0 points only)               : max|diff|={e5:.2e}")

# ---- sign law: list exceptions and their distance-to-boundary ----
print("\nsign-law exceptions (which points, and how far from Hopf):")
exc=0
for (P0,Q0,V0,Xg0,fr) in grid:
    ss={k:dRe(P0,Q0,V0,Xg0,k) for k in ['P','Q','V','Xg']}
    if any(math.isnan(x) for x in ss.values()): continue
    ok = ss['V']<0 and ss['P']>0 and ss['Q']>0 and ss['Xg']>0
    if not ok:
        exc+=1
        flips=[k for k in ['P','Q','V','Xg'] if (k=='V' and ss[k]>=0) or (k!='V' and ss[k]<=0)]
        print(f"   P={P0} Q={Q0:+.1f} V={V0} Xg={Xg0:.2f} (%SN={fr:.2f}): flips={flips}  values={ {k:round(v,1) for k,v in ss.items()} }")
print(f"total exceptions: {exc}")
# breakdown by frac
from collections import Counter
byfrac=Counter()
for (P0,Q0,V0,Xg0,fr) in grid:
    ss={k:dRe(P0,Q0,V0,Xg0,k) for k in ['P','Q','V','Xg']}
    if any(math.isnan(x) for x in ss.values()): continue
    if not (ss['V']<0 and ss['P']>0 and ss['Q']>0 and ss['Xg']>0): byfrac[fr]+=1
    else: byfrac[('ok',fr)]+=1
print("exceptions by %SN:", dict(byfrac))
