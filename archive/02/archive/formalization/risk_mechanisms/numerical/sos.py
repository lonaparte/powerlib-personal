import numpy as np, cvxpy as cp, sympy as sp, itertools
def monomials(vars, deg):
    mons=[sp.Integer(1)]
    for d in range(1,deg+1):
        for c in itertools.combinations_with_replacement(vars,d):
            m=sp.Integer(1)
            for v in c: m*=v
            mons.append(m)
    return mons
def sos_feasible(expr, vars, half_deg, eq_constraints=None, mult_deg=0, verbose=False):
    """Try to write expr = z^T Q z + sum_i lambda_i(x)*eq_i  with Q PSD (eq_i are the
    '=0' constraint polynomials, lambda_i free polynomials). Returns (status,Q,details)."""
    z=monomials(vars,half_deg)
    nQ=len(z)
    Q=cp.Variable((nQ,nQ),symmetric=True)
    # SOS part as symbolic with cvxpy entries kept symbolic via placeholder symbols
    qsyms=sp.symbols('q0:%d'%(nQ*nQ))
    Qs=sp.Matrix(nQ,nQ, lambda i,j: qsyms[i*nQ+j])
    zz=sp.Matrix(z)
    form=(zz.T*Qs*zz)[0]
    # multipliers for each equality constraint
    lam_syms=[]; lam_terms=sp.Integer(0); lam_cv=[]
    if eq_constraints:
        for ei,eq in enumerate(eq_constraints):
            lm=monomials(vars,mult_deg)
            ls=sp.symbols('l%d_0:%d'%(ei,len(lm)))
            lam_syms+= list(ls)
            lam_poly=sum(ls[k]*lm[k] for k in range(len(lm)))
            lam_terms+= lam_poly*eq
            lam_cv.append((ls,lm))
    diff=sp.expand(expr - form - lam_terms)
    poly=sp.Poly(diff, *vars)
    # linear constraints: each coeff == 0, linear in q's and l's
    cons=[Q>>0]
    # map symbolic q to cvxpy Q (symmetric)
    def qmap(sym):
        idx=qsyms.index(sym); i,j=divmod(idx,nQ); return Q[i,j]
    lam_cvx={}
    if eq_constraints:
        for ei,(ls,lm) in enumerate(lam_cv):
            v=cp.Variable(len(ls)); 
            for k,s_ in enumerate(ls): lam_cvx[s_]=v[k]
    for monom,coeff in poly.terms():
        cexpr=coeff
        # coeff is linear in qsyms and lam_syms -> build cvxpy expr
        terms=cexpr.as_coefficients_dict()
        e=0
        for sym,cf in terms.items():
            cf=float(cf)
            if sym==1: e=e+cf
            else:
                fs=sym.free_symbols
                if not fs: e=e+cf*float(sym)
                else:
                    s_=list(fs)[0]
                    # sym may be product symbol*number already separated; handle linear monomials in one q/l
                    if s_ in qsyms: e=e+cf*qmap(s_)
                    elif s_ in lam_cvx: e=e+cf*lam_cvx[s_]
        cons.append(e==0)
    prob=cp.Problem(cp.Minimize(0),cons)
    prob.solve(solver=cp.SCS, eps=1e-8, max_iters=50000, verbose=verbose)
    return prob.status, (Q.value if Q.value is not None else None)
