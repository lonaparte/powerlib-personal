"""What the "no modal identification needed" proof actually requires of a sensor.

The general argument says: on a codim-1 normally hyperbolic boundary the
reduced dynamics is scalar, rho' = F(rho); any observable built from the
critical mode has amplitude a = kappa_g rho with kappa_g fixed by the
sensor; and both readouts used by the decision tree are invariant to
kappa_g --

    margin   a/a_B = rho/rho_B          (a ratio: kappa_g cancels)
    rate     D = -d ln a/dt = -d ln rho/dt   (a log derivative: kappa_g
                                              differentiates away)

so no participation factor, mode shape, or modal transformation is needed.
That is exact, and it hides two conditions that the audit flagged and that
are tested here rather than asserted.

CONDITION 1 -- kappa_g must not be zero.  For an observable
y = <w, x - x_eq> the critical part is 2 Re(zeta <w,q>), so
kappa_g = 2|<w,q>|.  The set of w with <w,q> = 0 is a real codimension-2
subspace of R^4 and is not empty: a sensor can be blind.  The proof does not
fail gracefully there, it has no input at all.  What matters in practice is
not the measure-zero blind set but the neighbourhood of it: with a
measurement noise floor eta the readout error scales as eta/kappa_g, so the
question is how small kappa_g may be before the criterion stops being
usable.  Swept here over observation directions from fully aligned to
near-blind, at several noise floors.

CONDITION 2 -- the envelope must be the CRITICAL mode's envelope.  The real
observable carries every mode.  This cell has a second pair at
-5.99 +- 41.24j alongside the critical -0.10 +- 32.40j, so a raw envelope of
y mixes them and the extracted D is neither one.  Isolating the critical
band is therefore genuinely required -- but band selection is a much weaker
demand than modal identification: it needs one frequency, not a mode shape,
not a participation factor, and not a model.  Tested here with a plain
band-pass plus Hilbert envelope, from an initial condition that deliberately
excites BOTH modes, so the separation has to be done rather than assumed.

Reported: the fitted (alpha, -Re c1) from each sensor against the analytic
values, across observation directions x noise floors.  The claim under test
is that they are independent of the direction until the noise floor eats
kappa_g, and that the failure when it does is visible in the fit rather
than silent.
Budget ~25 min.
"""
exec(open('selfhead.py').read())
import time
from scipy.signal import hilbert, butter, filtfilt
LOG = open('sweep20/sensor.log', 'w')
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
ev = np.linalg.eigvals(A)
rg = math.sqrt(alpha/c1r)
out(f"G1 margin 0.10: alpha={alpha:.6f} w0={w0:.5f} Re c1={c1r:.6e} "
    f"rho_g={rg:.6e}")
out(f"  spectrum: " + ", ".join(f"{z:.4f}" for z in ev))

# --- observation directions ---------------------------------------------
qr = np.real(qvec); qi = np.imag(qvec)
Bq = np.linalg.qr(np.vstack([qr, qi]).T)[0]        # onb of span{Re q, Im q}
Nq = np.eye(4) - Bq @ Bq.T                          # projector onto the blind
u, s_, vt = np.linalg.svd(Nq)
wblind = u[:, 0]                                    # <w,q> = 0 exactly
walign = qr/np.linalg.norm(qr)
DIRS = [('aligned  ', walign)]
for f in (0.30, 0.10, 0.03, 0.01, 0.0):
    w = f*walign + math.sqrt(max(0.0, 1 - f*f))*wblind
    w = w/np.linalg.norm(w)
    DIRS.append((f"mix f={f:4.2f}", w))
DIRS.append(('state Vdc', np.array([0., 0., 1., 0.])))
DIRS.append(('state th ', np.array([1., 0., 0., 0.])))
out("")
out("  observation direction      kappa_g = 2|<w,q>|   relative to aligned")
K0 = None
for tag, w in DIRS:
    kg = 2*abs(np.dot(w, qvec))
    if K0 is None:
        K0 = kg
    out(f"   {tag}                {kg:.6e}      {kg/K0:.3e}")

# --- free decay exciting BOTH modes -------------------------------------
k2 = max((i for i in range(4) if ev[i].imag > 1e-9),
         key=lambda i: -ev[i].real)               # the non-critical pair
_, VRa = np.linalg.eig(A)
q2 = VRa[:, int(np.argmin(np.abs(ev - ev[k2])))]
r0 = 0.55*rg
x0 = st + 2*np.real(r0*qvec) + 2*np.real(0.8*r0*q2)
Tn = 2*math.pi/w0
s = solve_ivp(lambda t, x: rhs(x, pr), (0, 60*Tn), x0, method='DOP853',
              rtol=1e-13, atol=1e-16, dense_output=True)
fs = 40*w0/(2*math.pi)                              # 40 samples per cycle
ts = np.arange(0, 60*Tn, 1.0/fs)
X = s.sol(ts)
out("")
out(f"  free decay: {len(ts)} samples at {fs:.1f} Hz, launch rho0="
    f"{r0:.4e} ({r0/rg:.2f} rho_g), second mode at 0.8x")

bb, aa = butter(4, [0.80*w0/(2*math.pi)/(fs/2),
                    1.20*w0/(2*math.pi)/(fs/2)], btype='band')


def readout(y, seg=(0.25, 0.85)):
    """band-pass + Hilbert envelope -> (alpha_fit, slope_fit) of
    D(rho) = alpha - Re c1 rho^2, in units where rho is the modal amplitude
    (kappa_g divided out using the known kappa_g of that sensor)."""
    yb = filtfilt(bb, aa, y)
    env = np.abs(hilbert(yb))
    n = len(env)
    i0, i1 = int(seg[0]*n), int(seg[1]*n)
    e = env[i0:i1]; t = ts[i0:i1]
    if np.any(e <= 0) or not np.all(np.isfinite(e)):
        return None
    g = np.log(e)
    # local log-slope over sliding windows -> D at the window centre
    m = 24
    rr = []; dd = []
    for j in range(0, len(t) - m, m//2):
        tt = t[j:j+m]; gg = g[j:j+m]
        sl = np.polyfit(tt, gg, 1)[0]
        rr.append(float(np.exp(np.mean(gg)))); dd.append(-float(sl))
    rr = np.array(rr); dd = np.array(dd)
    ok = np.isfinite(rr) & np.isfinite(dd) & (rr > 0)
    if ok.sum() < 4:
        return None
    return rr[ok], dd[ok]


out("")
out("  sensor        noise    kappa_g      alpha_fit   err      "
    "-Re c1 fit     err")
for tag, w in DIRS:
    kg = 2*abs(np.dot(w, qvec))
    y = (X.T @ w) - float(np.dot(w, st))
    scale = float(np.max(np.abs(y)))
    for eta in (0.0, 1e-4, 1e-3, 1e-2):
        rng = np.random.default_rng(11)
        yn = y + eta*scale*rng.standard_normal(len(y)) if eta > 0 else y
        r = readout(yn)
        if r is None:
            out(f"   {tag}  {eta:.0e}  {kg:.3e}   envelope unusable")
            continue
        rr, dd = r
        rho = rr/kg if kg > 0 else rr*np.nan
        M = np.vstack([np.ones_like(rho), rho**2]).T
        try:
            a_f, s_f = np.linalg.lstsq(M, dd, rcond=None)[0]
        except Exception:
            out(f"   {tag}  {eta:.0e}  {kg:.3e}   fit failed"); continue
        ea = (a_f-alpha)/alpha*100
        es = (s_f+c1r)/(-c1r)*100
        out(f"   {tag}  {eta:.0e}  {kg:.3e}   {a_f:.6f} {ea:+8.2f}%  "
            f"{s_f:+.5e} {es:+8.2f}%")
    out("")
out(f"DONE wall={time.time()-T0:.0f}s")
