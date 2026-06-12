#!/usr/bin/env python3
"""Format the general-θ_e* reduced num(D) and G (from /tmp/T3_general_theta.pkl) into Lean syntax,
mirroring sigma_diff_factor: coefficients cast (N:ℝ) (or rational ((p:ℝ)/q)), bare-ℕ exponents.
Emits the two theorem bodies (factorisation + symmetric⇒0) to /tmp/T3_theta_lean.txt."""
import sympy as sp, pickle, sys
d=pickle.load(open('/tmp/T3_general_theta.pkl','rb'))
num=sp.sympify(d['num']); G=sp.sympify(d['G'])
VARS=sp.symbols('Vg wn Lf Rf Lg Rg Kpi Kp_P Kp_Q Kp_pll Ki_pll P_ref Q_ref C S',real=True)
names={str(v):v for v in VARS}
# remap parsed symbols onto our ordered var list
num=num.subs({s:names[str(s)] for s in num.free_symbols if str(s) in names})
G=G.subs({s:names[str(s)] for s in G.free_symbols if str(s) in names})

def coeff_lean(co):
    co=sp.nsimplify(co)
    if co.is_Integer: return f"({int(co)}:ℝ)"
    p,q=sp.fraction(co); return f"(({int(p)}:ℝ)/({int(q)}:ℝ))"

def poly_to_lean(expr):
    P=sp.Poly(expr,*VARS)
    terms=[]
    for monom,co in sorted(P.terms(), key=lambda t:(-sum(t[0]),t[0])):
        if co==0: continue
        sign='-' if co<0 else '+'
        parts=[coeff_lean(abs(co))]
        for v,e in zip(VARS,monom):
            if e==1: parts.append(str(v))
            elif e>1: parts.append(f"{v}^{e}")
        terms.append((sign,'*'.join(parts)))
    if not terms: return "(0:ℝ)"
    out=("- " if terms[0][0]=='-' else "")+terms[0][1]
    for sign,t in terms[1:]:
        out+=f" {sign} {t}"
    return out

numL=poly_to_lean(num); GL=poly_to_lean(G)
# sanity: re-parse-free check that (Kp_P−Kp_Q)*G − num == 0 in sympy
chk=sp.expand((names['Kp_P']-names['Kp_Q'])*G-num)
print("sympy recheck  (Kp_P−Kp_Q)*G − num == 0 :", chk==0, file=sys.stderr)
print(f"num terms={len(sp.Poly(num,*VARS).terms())}, G terms={len(sp.Poly(G,*VARS).terms())}", file=sys.stderr)
open('/tmp/T3_theta_lean.txt','w').write("NUM:=\n"+numL+"\n\nG:=\n"+GL+"\n")
print("wrote /tmp/T3_theta_lean.txt", file=sys.stderr)
