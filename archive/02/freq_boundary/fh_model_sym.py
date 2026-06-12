"""
fh_model_sym.py -- the task RHS (fh_gate.rhs) as SymPy, with analytic Jacobian, lambdified
to fast numpy callables.  Used by ffold_cycle.py / ffold_floquet_interval.py so the stiff
integrator gets an exact Jacobian (the finite-difference jac in fh_gate is too slow for the
variational/monodromy integrations).  Verified to match fh_gate.rhs/jac to ~1e-9.
"""
import numpy as np, sympy as sp

# fixed device params (Conventions sec.12.2) -- exact rationals where possible
Lf=sp.Rational(1,1000); Cf=sp.Rational(1,10000); Rf=sp.Rational(1,10)
Kpi=sp.Rational(126,100); Kii=sp.Integer(126); Kad=sp.Integer(2)
idref=sp.Integer(80); iqref=sp.Integer(0)
wn=2*sp.pi*50; Vg=380*sp.sqrt(sp.Rational(2,3))

S=sp.symbols('i_d i_q v_cd v_cq i_gd i_gq xi_dc xi_qc eta th_e', real=True)
i_d,i_q,v_cd,v_cq,i_gd,i_gq,xi_dc,xi_qc,eta,th_e=S
Rg,Lg,Kp,Ki=sp.symbols('Rg Lg Kp Ki', positive=True)

c=sp.cos(th_e); s=sp.sin(th_e)
i_dc=c*i_d-s*i_q;            i_qc=s*i_d+c*i_q
v_cdc=c*v_cd-s*v_cq;         v_cqc=s*v_cd+c*v_cq
i_Cdc=c*(i_d-i_gd)-s*(i_q-i_gq); i_Cqc=s*(i_d-i_gd)+c*(i_q-i_gq)
err_d=idref-i_dc;           err_q=iqref-i_qc
u_dc=Kpi*err_d+Kii*xi_dc-wn*Lf*i_qc+v_cdc-Kad*i_Cdc
u_qc=Kpi*err_q+Kii*xi_qc+wn*Lf*i_dc+v_cqc-Kad*i_Cqc
u_d=c*u_dc+s*u_qc;          u_q=-s*u_dc+c*u_qc
F=sp.Matrix([
    (u_d-v_cd-Rf*i_d+wn*Lf*i_q)/Lf,
    (u_q-v_cq-Rf*i_q-wn*Lf*i_d)/Lf,
    (i_d-i_gd+wn*Cf*v_cq)/Cf,
    (i_q-i_gq-wn*Cf*v_cd)/Cf,
    (v_cd-Vg-Rg*i_gd+wn*Lg*i_gq)/Lg,
    (v_cq-Rg*i_gq-wn*Lg*i_gd)/Lg,
    err_d, err_q, v_cqc, -Kp*v_cqc-Ki*eta])
Jsym=F.jacobian(sp.Matrix(S))

_args=(*S, Rg, Lg, Kp, Ki)
_f=sp.lambdify(_args, list(F), 'numpy')
_J=sp.lambdify(_args, Jsym.tolist(), 'numpy')

def rhs(x, Rg_, Lg_, Kp_, Ki_):
    return np.asarray(_f(*x, Rg_, Lg_, Kp_, Ki_), float)
def jac(x, Rg_, Lg_, Kp_, Ki_):
    return np.asarray(_J(*x, Rg_, Lg_, Kp_, Ki_), float)

if __name__=="__main__":
    import fh_gate
    rng=np.random.default_rng(0)
    Rg_,Lg_=fh_gate.grid_RL(0.8,10.0)
    x=fh_gate.equilibrium(0.8,0.5,150.0,10.0)[0]+0.1*rng.standard_normal(10)
    df=np.linalg.norm(rhs(x,Rg_,Lg_,0.5,150.0)-fh_gate.rhs(x,Rg_,Lg_,0.5,150.0))
    dJ=np.linalg.norm(jac(x,Rg_,Lg_,0.5,150.0)-fh_gate.jac(x,Rg_,Lg_,0.5,150.0))
    print("sym vs fh_gate: ||drhs||=%.2e  ||djac||=%.2e (jac diff ~ finite-diff error)"%(df,dJ))
