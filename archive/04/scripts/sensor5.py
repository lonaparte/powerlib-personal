"""Where the readout's bias actually comes from -- decomposed, not attributed.

sensor4 showed the +1.6%/+14% common bias survives on a synthetic signal
built from the very law being fitted, so it is the extraction chain.  That
names the stage, not the cause, and "it's the extraction" is the kind of
answer that stops an investigation instead of finishing it.

My first guess for the cause was a Jensen effect: the sliding window pairs
an AVERAGE of D over the window with a single representative rho, and under
the nonlinear D(rho) = alpha - Re c1 rho^2 that biases the pair.  Its size
is computable: for rho ~ e^{-D t} over a window of length dt,
<rho^2>/rho_geo^2 = sinh(x)/x with x = D dt, so the bias on the rho^2
coefficient is ~x^2/6.  Here dt = 160/206.3 = 0.776 s and D <= 0.1, giving
x = 0.078 and a bias of 0.1% -- a factor 200 too small.  **Guess wrong.**

So decompose instead of guessing again.  The chain is
    y(t)  --band-pass-->  --Hilbert-->  env(t)  --sliding log-slope-->  (rho, D)
and each stage can be tested against the exact rho(t), which is known in
closed form for this law:
    rho(t)^-2 = c1/alpha + (rho_0^-2 - c1/alpha) e^{2 alpha t}

 A. feed the EXACT rho(t) to the sliding-log-slope stage alone.  Any bias
    here is the binning's.
 B. compare the Hilbert envelope of the filtered signal against the exact
    rho(t), point by point.  Any discrepancy here is the filter/Hilbert's.
 C. window-length sweep -- whatever the cause, the fix should show up as a
    trend in m.
 D. the fix that has no binning at all: fit the closed-form rho(t) to the
    envelope by nonlinear least squares in (alpha, c1, rho_0).  If that
    returns alpha and c1 accurately, the sensor conclusion upgrades from
    "invariant but biased by 14%" to "invariant and accurate", which is a
    materially stronger statement and the one that should be on record.
"""
exec(open('selfhead.py').read())
import time
from scipy.signal import hilbert, butter, filtfilt
from scipy.optimize import least_squares
LOG = open('sweep20/sensor5.log', 'w')
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
st = co['st']; w0 = co['w0']; alpha = co['alpha']; c1r = co['c1'].real
rg = math.sqrt(alpha/c1r)
out(f"alpha={alpha:.6f}  w0={w0:.5f}  Re c1={c1r:.6e}  rho_g={rg:.5e}")

Tn = 2*math.pi/w0
fs = 40*w0/(2*math.pi)
ts = np.arange(0, 150*Tn, 1.0/fs)
r0 = 0.70*rg


def rho_exact(t, a=alpha, c=c1r, rr0=r0):
    return 1.0/np.sqrt(c/a + (1.0/rr0**2 - c/a)*np.exp(2*a*t))


RHO = rho_exact(ts)
KG = 1.6274
bb, aa = butter(4, [0.93*w0/(2*math.pi)/(fs/2),
                    1.07*w0/(2*math.pi)/(fs/2)], btype='band')


def sliding(env, m, seg=(0.20, 0.95)):
    n = len(env)
    i0, i1 = int(seg[0]*n), int(seg[1]*n)
    e = env[i0:i1]; t = ts[i0:i1]
    g = np.log(e)
    rr = []; dd = []
    for j in range(0, len(t) - m, max(1, m//4)):
        tt = t[j:j+m]; gg = g[j:j+m]
        rr.append(float(np.exp(np.mean(gg))))
        dd.append(-float(np.polyfit(tt, gg, 1)[0]))
    rr = np.array(rr); dd = np.array(dd)
    M = np.vstack([np.ones_like(rr), rr**2]).T
    return np.linalg.lstsq(M, dd, rcond=None)[0]


out("")
out("=== A. sliding-log-slope stage alone, fed the EXACT rho(t)")
out("    (no filter, no Hilbert -- any bias here is the binning's)")
out("    m    | window (s) | alpha err | slope err")
for m in (40, 80, 160, 320, 640):
    a_f, s_f = sliding(KG*RHO, m)
    a_f = a_f; s_f = s_f/(KG*KG)*(KG*KG)   # rho scaled out below
    aa_, ss_ = sliding(RHO, m)
    out(f"   {m:4d} | {m/fs:10.4f} | {(aa_-alpha)/alpha*100:+8.3f}% | "
        f"{(ss_+c1r)/(-c1r)*100:+8.3f}%")

out("")
out("=== B. filter + Hilbert envelope against the exact rho(t)")
y = KG*RHO*np.cos(w0*ts)
env = np.abs(hilbert(filtfilt(bb, aa, y)))/KG
n = len(ts); i0, i1 = int(0.20*n), int(0.95*n)
rel = (env[i0:i1] - RHO[i0:i1])/RHO[i0:i1]
out(f"    envelope/exact - 1 over the fit window: mean {rel.mean():+.3e}, "
    f"rms {float(np.sqrt(np.mean(rel**2))):.3e}, max |.| {np.abs(rel).max():.3e}")
out(f"    at the two ends of the window: {rel[0]:+.3e} .. {rel[-1]:+.3e}")
out("    (a DRIFT across the window is what biases the slope: it tilts the")
out("     apparent decay rate in a rho-dependent way)")
sl = np.polyfit(ts[i0:i1], rel, 1)[0]
out(f"    linear drift of that relative error: {sl:+.3e} per second, i.e. "
    f"{sl/alpha*100:+.3f}% of alpha")

out("")
out("=== C. full chain, window sweep")
out("    m    | window (s) | alpha err | slope err")
for m in (40, 80, 160, 320, 640):
    a_f, s_f = sliding(env, m)
    out(f"   {m:4d} | {m/fs:10.4f} | {(a_f-alpha)/alpha*100:+8.3f}% | "
        f"{(s_f+c1r)/(-c1r)*100:+8.3f}%")

out("")
out("=== D. the fix: fit the closed-form rho(t), no binning at all")


def fit_closed(envv, seg=(0.20, 0.95)):
    n = len(envv); i0, i1 = int(seg[0]*n), int(seg[1]*n)
    e = envv[i0:i1]; t = ts[i0:i1] - ts[i0]

    def res(p):
        a, c, rr0 = math.exp(p[0]), math.exp(p[1]), math.exp(p[2])
        return np.log(rho_exact(t, a, c, rr0)) - np.log(e)
    p0 = [math.log(alpha*1.5), math.log(c1r*1.5), math.log(e[0]*1.4)]
    s = least_squares(res, p0, xtol=1e-14, ftol=1e-14, gtol=1e-14)
    return math.exp(s.x[0]), math.exp(s.x[1])


for tag, sig in (('exact rho(t)', RHO), ('filter+Hilbert envelope', env)):
    a_f, c_f = fit_closed(sig)
    out(f"    {tag:26s}: alpha {(a_f-alpha)/alpha*100:+8.4f}%   "
        f"Re c1 {(c_f-c1r)/c1r*100:+8.4f}%")

out("")
out("  and on the REAL 4-state cell, same fix, several sensors:")
ev, VRa = np.linalg.eig(jac(st, pr))
k2 = int(np.argmin([e.real if e.imag > 1e-9 else 1e9 for e in ev]))
q2 = VRa[:, k2]
qvec = co['q']; pvec = co['p']
x0 = st + 2*np.real(r0*qvec) + 2*np.real(0.30*r0*q2)


def _esc(t, x):
    return abs(x[0] - st[0]) - 0.5*(math.pi - 2*abs(st[0]))


_esc.terminal = True; _esc.direction = 1
s = solve_ivp(lambda t, x: rhs(x, pr), (0, 150*Tn), x0, method='DOP853',
              rtol=1e-11, atol=1e-14, dense_output=True, events=(_esc,))
X = s.sol(ts)
qr = np.real(qvec); qi = np.imag(qvec)
Bq = np.linalg.qr(np.vstack([qr, qi]).T)[0]
wbl = np.linalg.svd(np.eye(4) - Bq @ Bq.T)[0][:, 0]
wal = qr/np.linalg.norm(qr)
out("    sensor        kappa_g    | sliding(m=160) a,slope | closed-form a,slope")
for tag, w in (('aligned  ', wal),
               ('mix f=0.10', 0.10*wal + math.sqrt(1-0.01)*wbl),
               ('mix f=0.01', 0.01*wal + math.sqrt(1-1e-4)*wbl),
               ('state Vdc', np.array([0., 0., 1., 0.]))):
    w = w/np.linalg.norm(w)
    kg = 2*abs(np.dot(w, qvec))
    yy = (X.T @ w) - float(np.dot(w, st))
    ee = np.abs(hilbert(filtfilt(bb, aa, yy)))/kg
    a1, s1 = sliding(ee, 160)
    a2, c2 = fit_closed(ee)
    out(f"    {tag}  {kg:.3e} | {(a1-alpha)/alpha*100:+7.2f}%,"
        f"{(s1+c1r)/(-c1r)*100:+7.2f}% | {(a2-alpha)/alpha*100:+7.2f}%,"
        f"{(c2-c1r)/c1r*100:+7.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
