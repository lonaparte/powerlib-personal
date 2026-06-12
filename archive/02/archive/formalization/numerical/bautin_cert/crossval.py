"""
Cross-validation for the rigorous Bautin enclosure.

Checks two INDEPENDENT things:

1. The independent FLOAT l1 pipeline in sweep.py (numpy einsum tensors, separate
   code path) lands INSIDE the rigorous interval enclosures produced by
   bautin_cert.py at the two bracket endpoints. (sweep.l1_balanced uses the SAME
   balanced coordinates as bautin_cert, so magnitudes are directly comparable.)

2. The float Bautin location Kp* from bautin.py (~0.4036 at Ki=150) lies inside the
   rigorous bracket.

Run AFTER bautin_cert.py (it reads results.json):
    cd formalization/numerical && python3 bautin_cert/crossval.py
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from sweep import hopf_SCR, l1_balanced

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    res = json.load(open(os.path.join(HERE, "results.json")))
    print("CROSS-VALIDATION 1: independent float l1 (sweep.py, balanced coords) inside rigorous enclosure")
    allok = True
    for tag, r in res.items():
        if r is None:
            continue
        for ep in ['endpointLo', 'endpointHi']:
            e = r[ep]; kp = e['Kp']
            sh = hopf_SCR(10.0, kp, 150.0)
            vb = l1_balanced(sh, 10.0, kp, 150.0)
            lo, hi = e['l1']
            inside = lo <= vb <= hi
            allok = allok and inside
            print("  [%s] Kp=%.4f: float l1_bal=%+.6e in [%+.6e,%+.6e]? %s"
                  % (tag, kp, vb, lo, hi, inside))
    print("  ALL float values inside their interval enclosures:", allok)

    print("\nCROSS-VALIDATION 2: float Bautin Kp* (bautin.py bisection) inside the rigorous bracket")
    # reproduce bautin.py's Kp* at Ki=150 by bisecting the float l1 sign change
    import numpy as np
    lo, hi = 0.30, 0.50
    f_lo = l1_balanced(hopf_SCR(10.0, lo, 150.0), 10.0, lo, 150.0)
    for _ in range(50):
        m = 0.5 * (lo + hi)
        fm = l1_balanced(hopf_SCR(10.0, m, 150.0), 10.0, m, 150.0)
        if (fm > 0) == (f_lo > 0):
            lo, f_lo = m, fm
        else:
            hi = m
    kp_star = 0.5 * (lo + hi)
    prim = res['primary']
    inb = prim['Kp_lo'] <= kp_star <= prim['Kp_hi']
    print("  float Kp*=%.5f ; rigorous primary bracket [%.5f,%.5f] contains it: %s"
          % (kp_star, prim['Kp_lo'], prim['Kp_hi'], inb))
    # tightest bracket
    tight = None
    for tag, r in res.items():
        if r and r.get('ok_signs'):
            if tight is None or (r['Kp_hi'] - r['Kp_lo']) < (tight['Kp_hi'] - tight['Kp_lo']):
                tight = r
    if tight:
        inb2 = tight['Kp_lo'] <= kp_star <= tight['Kp_hi']
        print("  tightest rigorous bracket [%.5f,%.5f] (width %.5f) contains float Kp*: %s"
              % (tight['Kp_lo'], tight['Kp_hi'], tight['Kp_hi'] - tight['Kp_lo'], inb2))


if __name__ == "__main__":
    main()
