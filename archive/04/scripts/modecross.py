"""Is the end of the margin sweep a degenerate Hopf, or a mode crossing?
alphatop found Re c1 flipping sign between margin 0.22 and 0.24 while P0
jumped from 1.4548 to 1.4092 -- a jump, not a continuous path.  A genuine
Bautin point keeps the operating point and the mode continuous and only
Re c1 crosses zero.  Printed here: for a fine margin grid, the operating
point, the frequency of the mode that margin_point locked onto, the full
complex spectrum, and Re c1.  A change of w0 across the step identifies a
mode crossing instead."""
exec(open('selfhead.py').read())
LOG = open('sweep20/modecross.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
prb = gset('G1'); Psn = 3*prb['V']**2/(4*prb['Xg'])
def reA(P):
    q = dict(prb, P=P); x = equil(q)
    if x is None: return None
    cm = crit_mode(jac(x, q))
    return None if cm is None else cm.real
grid = np.linspace(0.05, 0.985, 60)*Psn
va = [reA(P) for P in grid]; br = None
for a, b, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
    if fa is not None and fb is not None and fa < 0 <= fb:
        br = (a, b); break
lo, hi = br
for _ in range(45):
    m = 0.5*(lo+hi); v = reA(m)
    if v is None or v >= 0: hi = m
    else: lo = m
PH = 0.5*(lo+hi)
out(f"P_H={PH:.6f}")
out("margin |    P0      w0      Re c1       | complex eigenvalues")
for marg in (0.20, 0.21, 0.22, 0.225, 0.23, 0.235, 0.24, 0.26):
    P0 = margin_point(prb, PH, marg)
    pr = dict(prb, P=P0); co = nf_coeffs(pr)
    ev = np.linalg.eigvals(jac(co['st'], pr))
    cx = sorted([e for e in ev if e.imag > 1e-9], key=lambda z: -z.real)
    s = "  ".join(f"{e.real:+.4f}{e.imag:+.3f}j" for e in cx)
    out(f"{marg:.3f}  | {P0:.6f} {co['w0']:8.3f} {co['c1'].real:+.4e} | {s}")
out("also: sweep P directly through the region to see both modes")
for P in (1.40, 1.41, 1.42, 1.43, 1.44, 1.45, 1.4548):
    pr = dict(prb, P=P); x = equil(pr)
    ev = np.linalg.eigvals(jac(x, pr))
    cx = sorted([e for e in ev if e.imag > 1e-9], key=lambda z: -z.real)
    s = "  ".join(f"{e.real:+.4f}{e.imag:+.3f}j" for e in cx)
    out(f"  P={P:.4f}: {s}")
out("DONE")
