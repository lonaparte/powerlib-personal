"""Self-check: was the sensor run's common bias really the extraction?

sensor3 reported that the readout is kappa_g-invariant (alpha spread 0.17
percentage points across a 100x range of kappa_g) but sits on a common bias
of +1.6% in alpha and +14% in the slope, and I attributed that bias to "the
band-pass + Hilbert envelope extraction".  That attribution was asserted,
not measured.  It is cheap to measure and it should have been part of the
run: feed the SAME readout a synthetic signal whose alpha and Re c1 are
known exactly by construction, and see whether it returns them.

Synthetic signal: integrate the reduced radial law that the readout claims
to be measuring,
    rhodot = -alpha rho + Re c1 rho^3
with the cell's own alpha and Re c1, build y(t) = kappa_g rho(t) cos(w0 t +
phase), add the second mode with the cell's own decay rate, sample at the
same rate, and run the identical band-pass + Hilbert + sliding-log-slope
chain.  Whatever bias comes out is the extraction's, with no model error in
it at all, because the signal was manufactured from the law being fitted.

If the synthetic bias reproduces +1.6% / +14%, the attribution was right.
If it comes out near zero, the bias is NOT the extraction and something in
the 4-state cell is being mis-measured -- which would matter, because the
sensor conclusion is used to support "no modal identification needed".
"""
exec(open('selfhead.py').read())
import time
from scipy.signal import hilbert, butter, filtfilt
LOG = open('sweep20/sensor4.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']

prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
c1r = co['c1'].real
ev = np.linalg.eigvals(jac(st, pr))
rg = math.sqrt(alpha/c1r)
sec = [e for e in ev if e.imag > 1e-9 and abs(e.imag - w0) > 1e-6]
a2 = -sec[0].real; w2 = sec[0].imag
out(f"cell: alpha={alpha:.6f}  w0={w0:.5f}  Re c1={c1r:.6e}  rho_g={rg:.5e}")
out(f"second mode: decay {a2:.4f}, freq {w2:.4f}")

Tn = 2*math.pi/w0
fs = 40*w0/(2*math.pi)
ts = np.arange(0, 150*Tn, 1.0/fs)
r0 = 0.70*rg

# exact solution of rhodot = -alpha rho + Re c1 rho^3
#   rho(t)^-2 = (Re c1/alpha) + (r0^-2 - Re c1/alpha) e^{2 alpha t}
def rho_exact(t):
    inv2 = c1r/alpha + (1.0/r0**2 - c1r/alpha)*np.exp(2*alpha*t)
    return 1.0/np.sqrt(inv2)


bb, aa = butter(4, [0.93*w0/(2*math.pi)/(fs/2),
                    1.07*w0/(2*math.pi)/(fs/2)], btype='band')


def readout(y, seg=(0.20, 0.95)):
    yb = filtfilt(bb, aa, y)
    env = np.abs(hilbert(yb))
    n = len(env)
    i0, i1 = int(seg[0]*n), int(seg[1]*n)
    e = env[i0:i1]; t = ts[i0:i1]
    if np.any(e <= 0) or not np.all(np.isfinite(e)):
        return None
    g = np.log(e)
    m = 160
    rr = []; dd = []
    for j in range(0, len(t) - m, m//4):
        tt = t[j:j+m]; gg = g[j:j+m]
        rr.append(float(np.exp(np.mean(gg))))
        dd.append(-float(np.polyfit(tt, gg, 1)[0]))
    rr = np.array(rr); dd = np.array(dd)
    ok = np.isfinite(rr) & np.isfinite(dd) & (rr > 0)
    return (rr[ok], dd[ok]) if ok.sum() >= 4 else None


out("")
out("  synthetic signal built FROM the law being fitted, so any bias is")
out("  purely the extraction chain's:")
out("   case                         | alpha_fit    err     | -Re c1 fit    err")
KG = 1.6274
for tag, second, noise in (('pure mode, no 2nd, no noise', 0.0, 0.0),
                           ('with 2nd mode (0.30x)', 0.30, 0.0),
                           ('with 2nd mode + noise 1e-3', 0.30, 1e-3),
                           ('with 2nd mode + noise 1e-2', 0.30, 1e-2)):
    rho = rho_exact(ts)
    y = KG*rho*np.cos(w0*ts)
    if second > 0:
        y = y + KG*second*r0*np.exp(-a2*ts)*np.cos(w2*ts + 0.7)
    if noise > 0:
        rng = np.random.default_rng(11)
        y = y + noise*float(np.max(np.abs(y)))*rng.standard_normal(len(y))
    r = readout(y)
    if r is None:
        out(f"   {tag:28s} | envelope unusable"); continue
    rr, dd = r
    rr = rr/KG
    M = np.vstack([np.ones_like(rr), rr**2]).T
    a_f, s_f = np.linalg.lstsq(M, dd, rcond=None)[0]
    out(f"   {tag:28s} | {a_f:.6f} {(a_f-alpha)/alpha*100:+7.2f}% | "
        f"{s_f:+.5e} {(s_f+c1r)/(-c1r)*100:+7.2f}%")
out("")
out("  sensor3 measured, on the real 4-state cell: alpha +1.6%, slope +14%")
out("  (common to every non-blind direction).  Compare with the rows above:")
out("  if they match, the bias is the extraction and the attribution holds.")
out(f"DONE wall={time.time()-T0:.0f}s")
