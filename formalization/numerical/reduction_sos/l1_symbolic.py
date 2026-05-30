"""
l1_symbolic.py -- SYMBOLIC first Lyapunov coefficient of a reduced planar model.

Strategy for a closed-form l1:
  1. Take the QSS-reduced 4-state slow model (qss_reduction.py).
  2. Reduce further to the 2-D center eigenspace AT THE HOPF, but keep it
     SYMBOLIC by working with a parametric 2-D planar system in (u,v) obtained
     from the slow PLL pair (th, eta) with grid current at QSS.  For a planar
     system  u' = f(u,v), v' = g(u,v)  with linear part [[0,-w],[w,0]] after a
     normalizing transform, the first Lyapunov coefficient is the classical
     Guckenheimer-Holmes (1983) formula:

       16*a = f_uuu + f_uvv + g_uuv + g_vvv
              + (1/w)*( f_uv*(f_uu+f_vv) - g_uv*(g_uu+g_vv)
                        - f_uu*g_uu + f_vv*g_vv )

     all partials at the origin.  sign(a) = sign(l1).  This is rational in the
     model parameters once f,g are rational.

  This module provides:
    * gh_l1_planar(fu, fv, u, v, w)  : symbolic G-H coefficient for a planar
      system already in normal-form linear part.
    * a numeric cross-check planar_l1_numeric(...) using the same formula.

  The planar reduced model itself is assembled in run_all.py (it needs the
  numeric Hopf point to fix the linear normal form), and its l1 is then a
  rational function of the *remaining* free parameters after substitution.
"""
import sympy as sp
import numpy as np


def gh_l1_planar(f, g, u, v, w):
    """Guckenheimer-Holmes first Lyapunov coefficient for a planar vector field
        u' = w*(-v) + f(u,v) ,  v' = w*(u) + g(u,v)
    i.e. linear part [[0,-w],[w,0]], f,g containing the >=2 order terms.
    Returns 16*a (sympy expr); sign(16a)=sign(a)=sign(l1).
    All derivatives evaluated at (u,v)=(0,0)."""
    def d(expr, *vars):
        e = expr
        for vv in vars:
            e = sp.diff(e, vv)
        return e.subs({u: 0, v: 0})
    fuu = d(f, u, u); fuv = d(f, u, v); fvv = d(f, v, v)
    guu = d(g, u, u); guv = d(g, u, v); gvv = d(g, v, v)
    fuuu = d(f, u, u, u); fuvv = d(f, u, v, v)
    guuv = d(g, u, u, v); gvvv = d(g, v, v, v)
    term_cubic = fuuu + fuvv + guuv + gvvv
    term_quad = (fuv * (fuu + fvv) - guv * (guu + gvv) - fuu * guu + fvv * gvv) / w
    return sp.expand(term_cubic + term_quad)


def planar_l1_numeric(f_np, g_np, w, h=1e-3):
    """Finite-difference G-H coefficient for numeric vector fields f_np,g_np:
    R^2->R taking (u,v).  Used to cross-check the symbolic formula and the
    full-model sign.  Returns 16*a."""
    def d1(F, i):
        e = [0.0, 0.0]; e[i] = h
        return (F(e[0], e[1]) - F(-e[0], -e[1])) / (2 * h)
    def d2(F, i, j):
        if i == j:
            ei = [0.0, 0.0]; ei[i] = h
            return (F(ei[0], ei[1]) - 2 * F(0, 0) + F(-ei[0], -ei[1])) / h**2
        ei = [0.0, 0.0]; ei[i] = h; ej = [0.0, 0.0]; ej[j] = h
        return (F(ei[0] + ej[0], ei[1] + ej[1]) - F(ei[0] - ej[0], ei[1] - ej[1])
                - F(-ei[0] + ej[0], -ei[1] + ej[1]) + F(-ei[0] - ej[0], -ei[1] - ej[1])) / (4 * h**2)
    def d3(F, idxs):
        # third derivative by composition (central, h)
        from itertools import product
        # simple: differentiate d2 numerically in the third index
        i, j, k = idxs
        ek = [0.0, 0.0]; ek[k] = h
        Fp = lambda a, b: F(a + ek[0], b + ek[1])
        Fm = lambda a, b: F(a - ek[0], b - ek[1])
        return (d2(Fp, i, j) - d2(Fm, i, j)) / (2 * h)
    fuu = d2(f_np, 0, 0); fuv = d2(f_np, 0, 1); fvv = d2(f_np, 1, 1)
    guu = d2(g_np, 0, 0); guv = d2(g_np, 0, 1); gvv = d2(g_np, 1, 1)
    fuuu = d3(f_np, (0, 0, 0)); fuvv = d3(f_np, (0, 1, 1))
    guuv = d3(g_np, (0, 0, 1)); gvvv = d3(g_np, (1, 1, 1))
    cubic = fuuu + fuvv + guuv + gvvv
    quad = (fuv * (fuu + fvv) - guv * (guu + gvv) - fuu * guu + fvv * gvv) / w
    return cubic + quad


if __name__ == '__main__':
    # sanity: Hopf normal form  u'=-w v - u(u^2+v^2)*0 ...; test on a known system
    # Use the supercritical example: u' = -v + (a u - v)(u^2+v^2) form is messy;
    # instead test van der Pol-like:  u'=v, v'=-u+mu*(1-u^2)*v at mu=0 (Hopf w=1)
    # Put in normal-form linear part: x'=-y, y'=x with rotation; here just verify
    # the formula returns the classic vdP value sign (supercritical => 16a<0).
    u, v = sp.symbols('u v', real=True)
    # vdP at Hopf: x' = y, y' = -x - x^2 y  (a standard cubic). Linear part [[0,1],[-1,0]]
    # -> bring to [[0,-w],[w,0]] with w=1 via (u,v)=(y,x)? We'll just trust full pipeline.
    f = -u * (u**2 + v**2)  # supercritical sample, 16a should be negative
    g = -v * (u**2 + v**2)
    print("sample supercritical 16a =", gh_l1_planar(f, g, u, v, 1))  # expect < 0
    f2 = u * (u**2 + v**2)
    g2 = v * (u**2 + v**2)
    print("sample subcritical   16a =", gh_l1_planar(f2, g2, u, v, 1))  # expect > 0
