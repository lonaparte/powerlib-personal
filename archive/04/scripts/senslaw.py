"""Sensor tolerance as a scaling law, not a table of numbers.

On record: the readout was fixed by "fit the closed-form rho(t) in three
parameters and trim the tail", cross-sensor spread 0.037%, and the tolerance
was left as numbers.  A protocol plus a table is not a criterion -- the user
of the criterion needs to know what sensor is GOOD ENOUGH, in terms of their
own hardware.  That is a formula.

The chain is  y = kappa_g rho(t) cos(w0 t + phi) + n(t), kappa_g = 2|<w,q>|,
n white with per-sample variance sigma_n^2 at rate fs (two-sided PSD
sigma_n^2/fs).  Band-pass of width BW about w0 and take the analytic
envelope.  Writing the in-band noise in quadrature,
n_bp = n_c cos(w0 t + phi) - n_s sin(w0 t + phi), the envelope is
|kappa_g rho + n_c + i n_s| = kappa_g rho + n_c + O(n^2), so:

  * the envelope error is n_c, whose two-sided PSD is 2 sigma_n^2/fs
    -- twice the sensor's, because both sidebands fold onto baseband;
  * BW DOES NOT APPEAR.  A narrower filter lowers the instantaneous
    envelope noise (variance = S_one * BW) but by exactly the same factor
    lowers the number of independent samples in the window.  The record's
    "band-pass suppresses broadband noise by sqrt(BW_f/BW_n)" is true of the
    instantaneous reading and FALSE of the fitted parameters.  Only
    distortion sets the filter: BW must exceed the envelope's own bandwidth
    ~ alpha, and stay below the spacing to the nearest other mode.

For an additive-noise least-squares fit of the exact envelope law
    rho(t; alpha, c1, rho_0) = [c1/alpha + (rho_0^-2 - c1/alpha)
                                e^{2 alpha t}]^{-1/2}
the estimator covariance is the standard white-noise result, with the
sensor entering ONLY through kappa_g^-2:

    Cov(theta_hat) = (2 sigma_n^2 / (fs kappa_g^2)) M^{-1},
    M_jk = INT_window  (d rho/d theta_j)(d rho/d theta_k) dt              (S)

so the tolerance on the sensor is, for a demanded relative accuracy e on
alpha,

    kappa_g  >=  (sigma_n / (e alpha)) sqrt(2 (M^{-1})_{alpha alpha} / fs)

and since M ~ rho_0^2 T_w x (function of alpha T_w only), this is the
promised scaling: kappa_g rho_0 sqrt(fs T_w) / sigma_n above a pure number
that depends only on alpha T_w.  Nothing here is fitted -- (S) is derived,
and the test below is whether it predicts the SPREAD of a Monte-Carlo of
the full chain across sensors, noise levels, filter widths, sample rates
and window lengths, all at once.

If (S) holds, the blind-set statement upgrades from "codim 2" to a
quantitative usability boundary; if it fails, the readout is doing
something other than what I claim.  Budget ~10 min.
"""
exec(open('selfhead.py').read())
import time
from scipy.signal import hilbert, butter, filtfilt
from scipy.optimize import least_squares

LOG = open('sweep20/senslaw.log', 'w')


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
st = co['st']; w0 = co['w0']; ALP = co['alpha']; C1R = co['c1'].real
RG = math.sqrt(ALP/C1R)
R0 = 0.70*RG
out(f"G1 margin 0.10: alpha={ALP:.6f} w0={w0:.5f} Re c1={C1R:.6e} "
    f"rho_g={RG:.5e}  rho_0={R0:.5e}")


def rho_ex(t, a=ALP, c=C1R, r0=R0):
    return 1.0/np.sqrt(c/a + (1.0/r0**2 - c/a)*np.exp(2*a*t))


def Mmat(t, a=ALP, c=C1R, r0=R0):
    """M_jk = INT drho/dtheta_j drho/dtheta_k dt, theta = (alpha, c1, rho_0)"""
    h = 1e-6
    J = np.vstack([(rho_ex(t, a*(1+h), c, r0) - rho_ex(t, a*(1-h), c, r0))
                   / (2*h*a),
                   (rho_ex(t, a, c*(1+h), r0) - rho_ex(t, a, c*(1-h), r0))
                   / (2*h*c),
                   (rho_ex(t, a, c, r0*(1+h)) - rho_ex(t, a, c, r0*(1-h)))
                   / (2*h*r0)])
    return np.array([[float(np.trapezoid(J[i]*J[j], t)) for j in range(3)]
                     for i in range(3)])


def predict(t, kg, sig, fs):
    Mi = np.linalg.inv(Mmat(t))
    return np.sqrt(2.0*sig*sig/(fs*kg*kg)*np.diag(Mi))


def run_mc(kg, sig, fs, bwfrac, Tw, nseed=200, t0frac=0.0):
    f0 = w0/(2*math.pi)
    t = np.arange(0.0, Tw, 1.0/fs)
    R = rho_ex(t)
    bb, aa = butter(4, [(1-bwfrac)*f0/(fs/2), (1+bwfrac)*f0/(fs/2)],
                    btype='band')
    car = np.cos(w0*t + 0.7)
    est = []
    rng = np.random.default_rng(20260810)
    for _ in range(nseed):
        y = kg*R*car + sig*rng.standard_normal(len(t))
        env = np.abs(hilbert(filtfilt(bb, aa, y)))/kg

        def res(p):
            return rho_ex(t, math.exp(p[0]), math.exp(p[1]),
                          math.exp(p[2])) - env
        s = least_squares(res, [math.log(ALP), math.log(C1R), math.log(R0)],
                          xtol=1e-13, ftol=1e-13, gtol=1e-13)
        est.append([math.exp(s.x[0]), math.exp(s.x[1]), math.exp(s.x[2])])
    est = np.array(est)
    return est.std(axis=0, ddof=1), est.mean(axis=0), predict(t, kg, sig, fs)


Tn = 2*math.pi/w0
FS0 = 40*w0/(2*math.pi)
TW0 = 150*Tn
KG0 = 1.6274
SIG0 = 2.0e-4
out("")
out("=== (S) against Monte-Carlo of the full chain (200 seeds each)")
out("    every row changes ONE knob; the prediction uses no fitted constant")
out("  config                        | std(alpha)  pred      ratio | "
    "std(c1)     pred      ratio")
CFG = [('baseline                    ', KG0, SIG0, FS0, 0.07, TW0),
       ('kappa_g / 10                ', KG0/10, SIG0, FS0, 0.07, TW0),
       ('kappa_g / 100               ', KG0/100, SIG0, FS0, 0.07, TW0),
       ('sigma_n x 4                 ', KG0, 4*SIG0, FS0, 0.07, TW0),
       ('sigma_n / 4                 ', KG0, SIG0/4, FS0, 0.07, TW0),
       ('filter BW x 3  (0.07->0.21) ', KG0, SIG0, FS0, 0.21, TW0),
       ('filter BW / 3.5 (0.07->0.02)', KG0, SIG0, FS0, 0.02, TW0),
       ('fs x 2                      ', KG0, SIG0, 2*FS0, 0.07, TW0),
       ('fs / 2                      ', KG0, SIG0, FS0/2, 0.07, TW0),
       ('window x 1.5                ', KG0, SIG0, FS0, 0.07, 1.5*TW0),
       ('window / 1.5                ', KG0, SIG0, FS0, 0.07, TW0/1.5)]
rows = []
for tag, kg, sig, fs, bw, Tw in CFG:
    sd, mn, pd = run_mc(kg, sig, fs, bw, Tw)
    rows.append((tag, sd, pd))
    out(f"  {tag} | {sd[0]:.4e} {pd[0]:.4e} {sd[0]/pd[0]:6.3f} | "
        f"{sd[1]:.4e} {pd[1]:.4e} {sd[1]/pd[1]:6.3f}   "
        f"[{time.time()-T0:.0f}s]")
ra = np.array([r[1][0]/r[2][0] for r in rows])
rc = np.array([r[1][1]/r[2][1] for r in rows])
out(f"    alpha: mean ratio {ra.mean():.3f}, spread "
    f"{(ra.max()-ra.min())/ra.mean()*100:.1f}%   over kappa_g x100, "
    f"sigma x16, BW x10, fs x4, Tw x2.25")
out(f"    c1   : mean ratio {rc.mean():.3f}, spread "
    f"{(rc.max()-rc.min())/rc.mean()*100:.1f}%")

out("")
out("=== the tolerance, written as the formula it should have been")
t = np.arange(0.0, TW0, 1.0/FS0)
Mi = np.linalg.inv(Mmat(t))
out(f"    window = {TW0:.2f} s = {ALP*TW0:.3f}/alpha, fs = {FS0:.2f} Hz")
out(f"    sqrt((M^-1)_aa) = {math.sqrt(Mi[0,0]):.5e},  "
    f"sqrt((M^-1)_cc) = {math.sqrt(Mi[1,1]):.5e}")
out("    kappa_g >= (sigma_n/(e alpha)) sqrt(2 (M^-1)_aa / fs)")
for e in (0.01, 0.03, 0.10):
    kmin = SIG0/(e*ALP)*math.sqrt(2*Mi[0, 0]/FS0)
    out(f"      for {e*100:4.1f}% on alpha at sigma_n = {SIG0:.1e}: "
        f"kappa_g >= {kmin:.4e}   (baseline sensor has {KG0:.4f}, "
        f"headroom {KG0/kmin:.0f}x)")
out("    equivalently, with M ~ rho_0^2 T_w * h(alpha T_w), the group that")
out("    must exceed a pure number is   kappa_g rho_0 sqrt(fs T_w)/sigma_n .")

out("")
out("=== same law on the real 4-state cell, several sensors")
ts = np.arange(0, 150*Tn, 1.0/FS0)
ev, VRa = np.linalg.eig(jac(st, pr))
qvec = co['q']
qr = np.real(qvec); qi = np.imag(qvec)
Bq = np.linalg.qr(np.vstack([qr, qi]).T)[0]
wbl = np.linalg.svd(np.eye(4) - Bq @ Bq.T)[0][:, 0]
wal = qr/np.linalg.norm(qr)
k2 = int(np.argmin([e.real if e.imag > 1e-9 else 1e9 for e in ev]))
x0 = st + 2*np.real(R0*qvec) + 2*np.real(0.30*R0*VRa[:, k2])
s = solve_ivp(lambda tt, x: rhs(x, pr), (0, 150*Tn), x0, method='DOP853',
              rtol=1e-11, atol=1e-14, dense_output=True)
X = s.sol(ts)
f0 = w0/(2*math.pi)
bb, aa = butter(4, [0.93*f0/(FS0/2), 1.07*f0/(FS0/2)], btype='band')
out("    sensor       | kappa_g    | predicted std(alpha) | observed |error| "
    "over 40 noise draws")
rng = np.random.default_rng(7)
for tag, wv in (('aligned   ', wal),
                ('mix f=0.10', 0.10*wal + math.sqrt(1-0.01)*wbl),
                ('mix f=0.01', 0.01*wal + math.sqrt(1-1e-4)*wbl)):
    wv = wv/np.linalg.norm(wv)
    kg = 2*abs(np.dot(wv, qvec))
    yy = (X.T @ wv) - float(np.dot(wv, st))
    pdv = predict(ts, kg, SIG0, FS0)
    es = []
    for _ in range(40):
        env = np.abs(hilbert(filtfilt(bb, aa,
                                      yy + SIG0*rng.standard_normal(len(ts)))))/kg

        def res(p):
            return rho_ex(ts, math.exp(p[0]), math.exp(p[1]),
                          math.exp(p[2])) - env
        sl = least_squares(res, [math.log(ALP), math.log(C1R), math.log(R0)],
                           xtol=1e-13, ftol=1e-13, gtol=1e-13)
        es.append(math.exp(sl.x[0]))
    es = np.array(es)
    out(f"    {tag}   | {kg:.4e} | {pdv[0]:.4e}          | "
        f"{es.std(ddof=1):.4e}  (bias {(es.mean()-ALP)/ALP*100:+.3f}%)"
        f"   [{time.time()-T0:.0f}s]")
out(f"DONE wall={time.time()-T0:.0f}s")
