"""What the "no modal identification needed" proof requires of a sensor.

The general argument: on a codim-1 normally hyperbolic boundary the reduced
dynamics is scalar, rho' = F(rho); any observable built from the critical
mode has amplitude a = kappa_g rho with kappa_g fixed by the sensor; and
both readouts the decision tree uses are invariant to kappa_g --

    margin   a/a_B = rho/rho_B                (a ratio: kappa_g cancels)
    rate     D = -d ln a/dt = -d ln rho/dt     (a log derivative: it
                                                differentiates away)

so no participation factor, mode shape, or modal transformation is needed.
Exact, and it hides two conditions, tested here rather than asserted.

CONDITION 1 -- kappa_g must not be zero.  For y = <w, x - x_eq> the critical
part is 2 Re(zeta <w,q>), so kappa_g = 2|<w,q>|, and {w : <w,q> = 0} is a
real codimension-2 subspace of R^4: a sensor CAN be blind.  What matters is
the neighbourhood of that set, since with a measurement noise floor eta the
readout error scales as eta/kappa_g.  Swept over directions from fully
aligned down to kappa_g 100x smaller, and onto the blind direction exactly,
at four noise floors.

CONDITION 2 -- the envelope must be the CRITICAL mode's envelope.  The real
observable carries every mode; this cell has a second pair at
-5.99 +- 41.24j alongside the critical -0.10 +- 32.40j.  Band selection is
therefore genuinely required -- but it needs one frequency, not a mode
shape, not a participation factor, and not a model, which is a far weaker
demand than modal identification.  The initial condition deliberately
excites both modes so the separation has to be done rather than assumed.

The launch amplitude is 0.70 rho_g with the second mode at 0.30 of that: an
earlier attempt at 0.90 rho_g plus 0.8 escaped, and the post-escape
integration (Vdc -> 0 makes the DC-link balance singular) simply stalled.
An escape event now guards it rather than letting it hang.

Reported: the fitted (alpha, -Re c1) per direction per noise floor, and --
the actual claim -- the SPREAD across directions, which must stay far below
the common extraction bias if the readout is really kappa_g-invariant.
Budget ~10 min.
"""
exec(open('selfhead.py').read())
import time
from scipy.signal import hilbert, butter, filtfilt
LOG = open('sweep20/sensor3.log', 'w')
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
lam = co['lam']; pvec = co['p']; qvec = co['q']; c1r = co['c1'].real
A = jac(st, pr)
ev, VRa = np.linalg.eig(A)
rg = math.sqrt(alpha/c1r)
out(f"G1 margin 0.10: alpha={alpha:.6f} w0={w0:.5f} Re c1={c1r:.6e} "
    f"rho_g={rg:.6e}")
out("  spectrum: " + ", ".join(f"{z:.4f}" for z in ev))

qr = np.real(qvec); qi = np.imag(qvec)
Bq = np.linalg.qr(np.vstack([qr, qi]).T)[0]
Nq = np.eye(4) - Bq @ Bq.T
wblind = np.linalg.svd(Nq)[0][:, 0]
walign = qr/np.linalg.norm(qr)
DIRS = [('aligned   ', walign)]
for f in (0.30, 0.10, 0.03, 0.01, 0.0):
    w = f*walign + math.sqrt(max(0.0, 1 - f*f))*wblind
    DIRS.append((f"mix f={f:4.2f} ", w/np.linalg.norm(w)))
DIRS.append(('state Vdc ', np.array([0., 0., 1., 0.])))
DIRS.append(('state th  ', np.array([1., 0., 0., 0.])))
out("")
out("  observation direction   kappa_g = 2|<w,q>|   relative")
K0 = 2*abs(np.dot(walign, qvec))
for tag, w in DIRS:
    kg = 2*abs(np.dot(w, qvec))
    out(f"   {tag}            {kg:.6e}      {kg/K0:.3e}")

k2 = int(np.argmin([e.real if e.imag > 1e-9 else 1e9 for e in ev]))
q2 = VRa[:, k2]
r0 = 0.70*rg
x0 = st + 2*np.real(r0*qvec) + 2*np.real(0.30*r0*q2)
Tn = 2*math.pi/w0


def _esc(t, x):
    return abs(x[0] - st[0]) - 0.5*(math.pi - 2*abs(st[0]))


_esc.terminal = True; _esc.direction = 1
s = solve_ivp(lambda t, x: rhs(x, pr), (0, 150*Tn), x0, method='DOP853',
              rtol=1e-11, atol=1e-14, dense_output=True, events=(_esc,))
if len(s.t_events[0]) > 0 or s.status != 0:
    out(f"launch escaped at t={s.t[-1]:.3f}: lower r0")
    out("DONE (aborted)")
    raise SystemExit
fs = 40*w0/(2*math.pi)
ts = np.arange(0, 150*Tn, 1.0/fs)
X = s.sol(ts)
out("")
out(f"  free decay: {len(ts)} samples at {fs:.1f} Hz over {150*Tn:.2f}s, "
    f"launch rho0={r0:.4e} ({r0/rg:.2f} rho_g), second mode at 0.30x")
env0 = np.abs(np.array([np.vdot(pvec, X[:, i] - st)
                        for i in range(len(ts))]))
out(f"  true modal amplitude falls {env0[0]:.4e} -> {env0[-1]:.4e} "
    f"({env0[0]/env0[-1]:.1f}x), so rho^2 spans "
    f"{(env0[0]/env0[-1])**2:.0f}x")

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
        sl = np.polyfit(tt, gg, 1)[0]
        rr.append(float(np.exp(np.mean(gg)))); dd.append(-float(sl))
    rr = np.array(rr); dd = np.array(dd)
    ok = np.isfinite(rr) & np.isfinite(dd) & (rr > 0)
    if ok.sum() < 4:
        return None
    return rr[ok], dd[ok]


def fit_dir(w, eta, kg):
    y = (X.T @ w) - float(np.dot(w, st))
    scale = float(np.max(np.abs(y)))
    rng = np.random.default_rng(11)
    yn = y + eta*scale*rng.standard_normal(len(y)) if eta > 0 else y
    r = readout(yn)
    if r is None or kg <= 0:
        return None
    rr, dd = r
    rho = rr/kg
    M = np.vstack([np.ones_like(rho), rho**2]).T
    return np.linalg.lstsq(M, dd, rcond=None)[0]


out("")
out("  sensor       noise   kappa_g     alpha_fit   err       "
    "-Re c1 fit      err")
for tag, w in DIRS:
    kg = 2*abs(np.dot(w, qvec))
    for eta in (0.0, 1e-4, 1e-3, 1e-2):
        if kg < 1e-8:
            out(f"   {tag} {eta:.0e}  {kg:.3e}   BLIND: no critical-mode "
                f"content, criterion has no input")
            continue
        r = fit_dir(w, eta, kg)
        if r is None:
            out(f"   {tag} {eta:.0e}  {kg:.3e}   envelope unusable")
            continue
        a_f, s_f = r
        out(f"   {tag} {eta:.0e}  {kg:.3e}   {a_f:.6f} {(a_f-alpha)/alpha*100:+8.2f}%  "
            f"{s_f:+.5e} {(s_f+c1r)/(-c1r)*100:+8.2f}%")
    out("")

out("=== the claim under test: spread ACROSS sensors at fixed noise ===")
out("  kappa_g varies 100x between 'aligned' and 'mix f=0.01'.  If the")
out("  readout is kappa_g-invariant, the spread must sit far below the")
out("  common bias, which is an extraction artefact shared by all.")
out("  noise  | alpha spread | slope spread | common bias (alpha, slope)")
for eta in (0.0, 1e-4, 1e-3, 1e-2):
    av = []; sv = []
    for tag, w in DIRS:
        kg = 2*abs(np.dot(w, qvec))
        if kg < 1e-8:
            continue
        r = fit_dir(w, eta, kg)
        if r is None:
            continue
        av.append(r[0]); sv.append(r[1])
    av = np.array(av); sv = np.array(sv)
    out(f"  {eta:.0e} | {(av.max()-av.min())/av.mean()*100:11.3f}% | "
        f"{(sv.max()-sv.min())/abs(sv.mean())*100:11.3f}% | "
        f"{(av.mean()-alpha)/alpha*100:+.2f}%, "
        f"{(sv.mean()+c1r)/(-c1r)*100:+.2f}%")
out("")
out("  tolerance: the readout error grows as eta/kappa_g, so a sensor with")
out("  kappa_g a factor K below the best available needs a noise floor K")
out("  times lower to reach the same accuracy.  The blind set is measure")
out("  zero but its neighbourhood is not, which is the real constraint --")
out("  and it is a signal-to-noise constraint, not a modelling one.")
out(f"DONE wall={time.time()-T0:.0f}s")
