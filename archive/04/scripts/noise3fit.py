"""The Kramers regression needs the prefactor, which is not constant here.

noise3's raw slope of ln T against X came out 1.258, 0.874, 0.779 over
successive intervals -- passing through 1 and continuing down, which would
look like a failed test.  It is not: the sweep varies sigma, and sigma
moves BOTH the barrier-to-noise ratio X and the prefactor, so "intercept
constant" was never a valid assumption.

For dx = -grad U dt + sqrt(2 Dtilde) dW in 2D with a rotationally symmetric
well at the origin and a circular barrier at rho_g, the mean first-passage
time follows from flux-over-population in the radial coordinate (measure
rho drho):

    T = (1/Dtilde) int_0^{rho_g} dy (1/(y e^{-U(y)/Dtilde}))
                                  int_0^y rho e^{-U(rho)/Dtilde} drho

Inner integral, Gaussian well of curvature alpha_eff:  -> Dtilde/alpha_eff.
Outer integral, saddle point at rho_g with |U''(rho_g)| = 2 alpha_eff:
    -> (1/rho_g) e^{DeltaU/Dtilde} sqrt(pi Dtilde/alpha_eff).
With rho_g = sqrt(alpha_eff/Re c1),

    T = sqrt(pi Dtilde Re c1) / alpha_eff^2 * exp(X)
    ==>  ln T - (1/2) ln Dtilde + 2 ln alpha_eff = X + const .

So the quantity that must have slope exactly 1 against X, with a constant
intercept, is the LEFT side -- every piece of it derived, nothing fitted
except the single additive constant.  Applied to whatever rows noise3 has
logged.
"""
import math, re, sys
import numpy as np

LOGF = 'sweep20/noise3.log'
txt = open(LOGF).read()
lines = txt.split('\n')
i = next((k for k, l in enumerate(lines) if l.startswith('=== (II)')), None)
if i is None:
    print('no part II section yet'); sys.exit(1)
rows = []
for l in lines[i:]:
    m = re.match(r'\s*([\d.]+e-0\d)\s*\|\s*([\d.]+)\s*\|\s*([\d.]+)%\s*\|'
                 r'\s*([\d.]+)\s*\|\s*(\d+)/(\d+)\s*\|\s*([\d.]+)\s*\|'
                 r'\s*([-\d.]+)\s*\|\s*([\d.]+)', l)
    if m:
        rows.append(dict(sig=float(m.group(1)), ae=float(m.group(2)),
                         X=float(m.group(4)), nesc=int(m.group(5)),
                         M=int(m.group(6)), T=float(m.group(7)),
                         sm=float(m.group(9))))
if len(rows) < 3:
    print(f'only {len(rows)} rows so far'); sys.exit(1)

gmag = 3.198767e+02
c1r = 1.219123e+03
alpha = 0.1
out = []
out.append(f"rows parsed: {len(rows)}")
out.append("")
out.append("  X      | alpha_eff | Dtilde     | ln T   | "
           "Y = lnT - .5 ln D + 2 ln a_eff | std/mean")
X = []; Y = []; L = []
for r in rows:
    D = gmag**2*r['sig']**2/4.0
    y = math.log(r['T']) - 0.5*math.log(D) + 2*math.log(r['ae'])
    X.append(r['X']); Y.append(y); L.append(math.log(r['T']))
    out.append(f"  {r['X']:6.3f} | {r['ae']:9.6f} | {D:.4e} | "
               f"{math.log(r['T']):6.3f} | {y:29.4f} | {r['sm']:.3f}")
X = np.array(X); Y = np.array(Y); L = np.array(L)
out.append("")
out.append("  successive-interval slopes (raw ln T vs X):")
out.append("    " + ", ".join(f"{(L[i+1]-L[i])/(X[i+1]-X[i]):.3f}"
                              for i in range(len(X)-1)))
out.append("  successive-interval slopes (with the derived prefactor):")
out.append("    " + ", ".join(f"{(Y[i+1]-Y[i])/(X[i+1]-X[i]):.3f}"
                              for i in range(len(X)-1)))
sl, ic = np.polyfit(X, Y, 1)
out.append("")
out.append(f"  all rows:  Y = {sl:.4f} X + {ic:.4f}   "
           f"(Kramers requires slope 1)")
sel = X > 0.9
if sel.sum() >= 3:
    s2, i2 = np.polyfit(X[sel], Y[sel], 1)
    res = Y[sel] - (s2*X[sel] + i2)
    out.append(f"  X > 0.9:   Y = {s2:.4f} X + {i2:.4f}   rms "
               f"{float(np.sqrt(np.mean(res**2))):.4f}")
sel2 = X > 1.4
if sel2.sum() >= 3:
    s3, i3 = np.polyfit(X[sel2], Y[sel2], 1)
    out.append(f"  X > 1.4:   Y = {s3:.4f} X + {i3:.4f}")
out.append("")
out.append("  the raw slope drifting DOWN through 1 while the "
           "prefactor-corrected")
out.append("  slope drifts DOWN TOWARD 1 is the signature of a "
           "sub-asymptotic")
out.append("  correction of relative size O(1/X): only the corrected one "
           "has a")
out.append("  limit to converge to.")
out.append("")
out.append("  std/mean must approach 1 (exponential first passage): " +
           ", ".join(f"X={r['X']:.2f}:{r['sm']:.2f}" for r in rows))
X0 = np.array([alpha*alpha/(c1r*gmag**2*r['sig']**2) for r in rows])
Y0 = np.array([math.log(r['T']) - 0.5*math.log(gmag**2*r['sig']**2/4.0)
               + 2*math.log(alpha) for r in rows])
s0, ii0 = np.polyfit(X0, Y0, 1)
r0 = Y0 - (s0*X0 + ii0)
sA, iA = np.polyfit(X, Y, 1)
rA = Y - (sA*X + iA)
out.append("")
out.append(f"  erosion ignored (alpha in place of alpha_eff everywhere): "
           f"slope {s0:.4f}, rms {float(np.sqrt(np.mean(r0**2))):.4f}")
out.append(f"  with erosion:                                          "
           f"slope {sA:.4f}, rms {float(np.sqrt(np.mean(rA**2))):.4f}")
txtout = '\n'.join(out)
print(txtout)
open('sweep20/noise3fit.log', 'w').write(txtout + '\n')
