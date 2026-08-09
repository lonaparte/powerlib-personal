"""Escape-time law: is the logarithmic slope the forced invariant
curve's unstable Floquet exponent?  Predicted t_esc = (1/lam_u) ln(1/d).
Compute lam_u(eps_c) from the invariant-curve continuation and compare
with the fitted slope (81.114 drive periods) for the idx17 set.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/lamu.log','w')
def out(m): LOG.write(m+'\n'); LOG.flush()
T0=time.time()
_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a=_avl(x,prm)
    return np.array([[float(_Jl[i][j](*a)) for j in range(4)] for i in range(4)])
prb = gset('G1', kp=55., ki=1200., Xg=0.40); Psn=3*prb['V']**2/(4*prb['Xg'])
def reA(P):
    q=dict(prb,P=P); x=equil(q)
    if x is None: return None
    cm=crit_mode(jac(x,q)); return None if cm is None else cm.real
grid=np.linspace(0.05,0.985,60)*Psn; va=[reA(P) for P in grid]; br=None
for a,b,fa,fb in zip(grid[:-1],grid[1:],va[:-1],va[1:]):
    if fa is not None and fb is not None and fa<0<=fb: br=(a,b); break
lo,hi=br
for _ in range(45):
    m=0.5*(lo+hi); v=reA(m)
    if v is None or v>=0: hi=m
    else: lo=m
P0=margin_point(prb,0.5*(lo+hi),0.08)
pr=dict(prb,P=P0); co=nf_coeffs(pr)
st=co['st']; w0=co['w0']; qv=co['q']; pv=co['p']; c1v=co['c1']; alpha=co['alpha']
zg=math.sqrt(alpha/c1v.real); wd=0.92*w0; Td=2*math.pi/wd
epsc=7.29303e-03
K=32; mfreq=np.fft.fftfreq(K)*K; I4=np.eye(4)
def shift_mat(r):
    ph=np.exp(1j*mfreq*r)
    return np.real(np.fft.ifft(np.fft.fft(np.eye(K),axis=0)*ph[:,None],axis=0))
def dshift_mat(r):
    ph=1j*mfreq*np.exp(1j*mfreq*r)
    return np.real(np.fft.ifft(np.fft.fft(np.eye(K),axis=0)*ph[:,None],axis=0))
def dth_(U): return np.real(np.fft.ifft(np.fft.fft(U,axis=0)*(1j*mfreq)[:,None],axis=0))
def flow(x0,T,var=False):
    def f(t,y):
        x=y[:4]
        if not var: return rhs(x,pr)
        return np.concatenate([rhs(x,pr),(jac_a(x,pr)@y[4:].reshape(4,4)).ravel()])
    y0=x0 if not var else np.concatenate([x0,np.eye(4).ravel()])
    s=solve_ivp(f,(0,T),y0,method='DOP853',rtol=1e-12,atol=1e-14)
    return (s.y[:4,-1] if not var else (s.y[:4,-1],s.y[4:,-1].reshape(4,4)))
def cyc(xs,Ts):
    x,T=xs.copy(),Ts; fref=rhs(xs,pr)
    for it in range(40):
        xT,M=flow(x,T,var=True); R=np.append(xT-x,np.dot(fref,x-xs))
        if np.max(np.abs(R))<1e-12: return x,T,True
        A5=np.zeros((5,5)); A5[:4,:4]=M-np.eye(4); A5[:4,4]=rhs(xT,pr); A5[4,:4]=fref
        dy=np.linalg.solve(A5,-R); n=np.linalg.norm(dy[:4]); cap=max(0.01,0.5*zg)
        if n>cap: dy*=cap/n
        if abs(dy[4])>0.1*T: dy*=0.1*T/abs(dy[4])
        x=x+dy[:4]; T=T+dy[4]
    return x,T,np.max(np.abs(R))<1e-9
got=False
for fac in (1.0,0.85,0.7,1.2):
    xs=st+2*np.real(fac*zg*qv); Ts=2*math.pi/(w0+c1v.imag*(fac*zg)**2)
    x0c,Tc,ok=cyc(xs,Ts)
    if ok and abs(np.vdot(pv,x0c-st))>0.2*zg: got=True; break
scc=solve_ivp(lambda t,x: rhs(x,pr),(0,Tc),x0c,method='DOP853',rtol=1e-12,
              atol=1e-14,t_eval=np.arange(K)*Tc/K)
U=scc.y.T.copy()
def strobe(x0,eps):
    def f(t,y):
        x=y[:4]; qq=dict(pr,V=pr['V']+eps*math.cos(wd*t))
        return np.concatenate([rhs(x,qq),(jac_a(x,qq)@y[4:].reshape(4,4)).ravel()])
    s=solve_ivp(f,(0,Td),np.concatenate([x0,np.eye(4).ravel()]),method='DOP853',
                rtol=1e-11,atol=1e-13)
    return s.y[:4,-1],s.y[4:,-1].reshape(4,4)
def tn(U,rho,eps,itmax=25,tol=1e-10):
    Uref=U.copy(); dUref=dth_(Uref); res=None
    for it in range(itmax):
        Sh=shift_mat(rho); PhiU=np.zeros((K,4)); Ms=np.zeros((K,4,4))
        for j in range(K): PhiU[j],Ms[j]=strobe(U[j],eps)
        R=PhiU-Sh@U; c=float(np.sum(dUref*(U-Uref)))
        res=max(np.max(np.abs(R)),abs(c))
        if res<tol: return U,rho,True,Ms
        A=np.zeros((4*K+1,4*K+1))
        for j in range(K): A[4*j:4*j+4,4*j:4*j+4]+=Ms[j]
        A[:4*K,:4*K]-=np.kron(Sh,I4); A[:4*K,-1]=-(dshift_mat(rho)@U).flatten()
        A[-1,:4*K]=dUref.flatten()
        dy=np.linalg.solve(A,-np.concatenate([R.flatten(),[c]]))
        nU=np.max(np.abs(dy[:4*K])); cap=max(0.005,0.5*zg)
        if nU>cap: dy*=cap/nU
        U=U+dy[:4*K].reshape(K,4); rho=rho+dy[-1]
    return U,rho,res<1e-9,Ms
rho=2*math.pi*((Td/Tc)%1.0)
U,rho,ok,Ms=tn(U,rho,0.0)
out(f"idx17: alpha={alpha:.4f} 2alpha={2*alpha:.4f} Td={Td:.5f}s eps_c={epsc:.4e}")
eps=0.0; deps=0.05*epsc
while eps<epsc-1e-12:
    e=min(eps+deps,epsc)
    Un,rn,okn,Msn=tn(U.copy(),rho,e)
    if not okn:
        deps*=0.5
        if deps<1e-4*epsc: break
        continue
    U,rho,eps,Ms=Un,rn,e,Msn
    deps=min(deps*1.3,0.08*epsc)
# transverse Floquet: product of the strobe Jacobians around the curve
# transverse Lyapunov exponent: ring average of log|transverse
# multiplier|, tangent direction projected out at each collocation point
dU = dth_(U)
lg = []
for j in range(K):
    tg = dU[j]/np.linalg.norm(dU[j])
    Pt = np.eye(4) - np.outer(tg, tg)
    Mt = Pt @ Ms[j] @ Pt
    ev2 = np.linalg.eigvals(Mt)
    ev2 = np.sort(np.abs(ev2))[::-1]
    lg.append(math.log(max(ev2[0], 1e-300)))
lam_u = float(np.mean(lg))/Td
out(f"  at eps={eps:.4e}: mean log|mu_perp|={np.mean(lg):.6f} per strobe "
    f"(Td={Td:.5f}s) -> lam_u={lam_u:.5f} 1/s")
out(f"  predicted log-slope 1/lam_u = {1/lam_u:.3f}s = {1/lam_u/Td:.2f} drive periods")
out(f"  fitted slope from escape times = 81.114 periods "
    f"-> err {(1/lam_u/Td-81.114)/81.114*100:+.2f}%")
out(f"  (unforced value 1/(2 alpha) = {1/(2*alpha)/Td:.2f} periods, "
    f"err {(1/(2*alpha)/Td-81.114)/81.114*100:+.2f}%)")
out(f"DONE wall={time.time()-T0:.0f}s")
