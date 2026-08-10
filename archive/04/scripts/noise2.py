"""Broadband drive, step 2: the noise-activated branch.

Everything in the decision tree so far is deterministic: a drive of a given
amplitude either does or does not carry the state past the guard, and the
threshold is sharp.  Under a random drive that is false.  There is no
threshold at all -- any noise intensity eventually carries the state over
the guard -- and the question changes from "does it escape" to "how long
until it does".  That is a different branch, not a correction to B1.

The mechanism is already fully determined by objects that have been derived
and verified, with no new fitted quantity.  In the rotating frame the
reduced equation is

    Zdot = -alpha_eff Z + Re c1 Z |Z|^2 + g u(t) e^{-i w0 t},
    g = <p, f_u> ,

and for a drive that is white on the envelope timescale the last term is an
isotropic complex Wiener increment.  With u white of intensity
<u(t)u(t')> = sigma^2 delta(t-t'):

    one-sided PSD          S_u(w) = sigma^2/pi ,
    erosion                alpha_eff = alpha - (sigma^2/2 pi) int Re c_x(w) dw,
    envelope diffusion     Dtilde = |g|^2 sigma^2/4 ,
    barrier height         Delta U = alpha_eff^2/(4 Re c1) ,

so the Kramers law reads

    ln T_esc  =  Delta U / Dtilde  +  const
              =  alpha_eff^2 / ( Re c1 |g|^2 sigma^2 )  +  const .

Both alpha_eff and the barrier use the SAME c_x and c1 that the
deterministic branch uses; the only thing the fit is allowed to supply is
the prefactor (the intercept), which is the entropic factor of escape over
a ring rather than a saddle.  So the mechanism claim is a SLOPE OF EXACTLY
ONE against the predicted exponent -- if the slope comes out at 0.6 or 1.7
the reduction is wrong, and no choice of prefactor can hide it.

Two things the run must also show, or the identification is not earned:
 - escape times exponentially distributed (std/mean -> 1), the signature of
   a rate process rather than a deterministic crossing;
 - the erosion term mattering: the same fit with alpha in place of
   alpha_eff must be visibly worse, otherwise the run has not tested it.

Noise is additive in the STATE, dx = f(x)dt + sigma b dW with b = f_V at the
equilibrium, so there is no Ito/Stratonovich ambiguity and the parametric
channel is deliberately absent; that is the case the formula above covers.
Budget ~45 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/noise2.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']; cx_hand = _ns['cx_hand']
hs = 1e-6

prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
lam = co['lam']; pvec = co['p']; qvec = co['q']; c1r = co['c1'].real
A = jac(st, pr)
dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
bvec = (rhs(st, dict(pr, V=pr['V']+hs))
        - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
g = np.vdot(pvec, bvec)
rg0 = math.sqrt(alpha/c1r)
out(f"G1 margin 0.10: alpha={alpha:.6f} w0={w0:.5f} Re c1={c1r:.6e}")
out(f"  |g|=|<p,f_V>|={abs(g):.6e}  rho_g(sigma=0)={rg0:.6e}")
out(f"  barrier at sigma=0: DeltaU = alpha^2/(4 Re c1) = "
    f"{alpha**2/(4*c1r):.6e}")

# ---- the erosion integral int Re c_x(w) dw, on a graded grid ----
def cxw(w):
    return cx_hand(A, st, pr, qvec, pvec, w0, w, bvec).real


WG = np.concatenate([np.linspace(0.02, 0.7, 40)*w0,
                     np.linspace(0.70, 1.30, 90)*w0,
                     np.linspace(1.30, 4.0, 60)*w0,
                     np.linspace(4.0, 60.0, 90)*w0])
WG = np.unique(WG)
CV = np.array([cxw(w) for w in WG])
Icx = float(np.trapezoid(CV, WG)) if hasattr(np, 'trapezoid') \
    else float(np.trapz(CV, WG))
tailA = CV[-1]*WG[-1]        # c_x ~ K/w^2  =>  tail integral = c_x(W) * W
out(f"  int Re c_x dw over [0.02, 60] w0 = {Icx:.6e}, "
    f"estimated tail beyond = {tailA:.6e} ({tailA/Icx*100:.2f}%)")
out(f"  Re c_x at 0.9 w0 = {cxw(0.9*w0):.5e}, at w0 = {cxw(w0):.5e}, "
    f"min over grid = {CV.min():.5e} at w/w0 = {WG[int(np.argmin(CV))]/w0:.3f}")
Icx = Icx + tailA


def alpha_eff(sig):
    return alpha - sig*sig*Icx/(2*math.pi)


def exponent(sig):
    ae = alpha_eff(sig)
    return ae*ae/(c1r*abs(g)**2*sig*sig)


# ---- Euler-Maruyama escape ----
def esc_time(sig, seed, Tmax, dt):
    rng = np.random.default_rng(seed)
    x = st.copy()
    sq = sig*math.sqrt(dt)
    n = int(Tmax/dt)
    blk = 20000
    t = 0.0
    done = 0
    while done < n:
        m = min(blk, n - done)
        xi = rng.standard_normal(m)
        for i in range(m):
            x = x + rhs(x, pr)*dt + bvec*(sq*xi[i])
            t += dt
            if abs(x[0] - st[0]) > dsad or x[2] < 0.20*Vdc0 \
                    or x[2] > 2.50*Vdc0 or not np.isfinite(x[0]):
                return t
        done += m
    return None


def rate_mle(sig, M, Tmax, dt, seed0):
    """MLE of the escape rate under right-censoring: n_esc / total exposure."""
    tot = 0.0; nesc = 0; samples = []
    for j in range(M):
        te = esc_time(sig, seed0 + j, Tmax, dt)
        if te is None:
            tot += Tmax
        else:
            tot += te; nesc += 1; samples.append(te)
    if nesc == 0:
        return None, 0, tot, samples
    return nesc/tot, nesc, tot, samples


# ---- calibrate sigma so the mean escape time lands in a workable range ----
DT = 2.0e-4
out("")
out("--- calibration: find sigma giving T_esc ~ 30 s ---")
sig = 4.0e-6
for it in range(9):
    r, ne, tot, _ = rate_mle(sig, 4, 400.0, DT, 1000 + 37*it)
    Tb = (1.0/r) if r else float('inf')
    out(f"  sigma={sig:.4e}  exponent={exponent(sig):8.4f}  "
        f"escapes {ne}/4  T_est={Tb:.2f}s  [{time.time()-T0:.0f}s]")
    if r is None or Tb > 80.0:
        sig *= 1.35
    elif Tb < 12.0:
        sig /= 1.35
    else:
        break
out(f"  calibrated sigma0 = {sig:.5e}")

# ---- dt convergence at the calibrated sigma ----
out("")
out("--- dt convergence (same seeds, halved step) ---")
for dtt in (4.0e-4, 2.0e-4, 1.0e-4):
    r, ne, tot, _ = rate_mle(sig, 10, 600.0, dtt, 5000)
    out(f"  dt={dtt:.1e}  escapes {ne}/10  T_est="
        f"{(1.0/r if r else float('inf')):.3f}s  [{time.time()-T0:.0f}s]")

# ---- the sweep ----
out("")
out("=== Kramers sweep: ln T against alpha_eff^2/(Re c1 |g|^2 sigma^2)")
out(" sigma      | alpha_eff | erosion% | exponent X | escapes | T_est   | "
    "ln T   | std/mean")
M = 40
ROWS = []
for fac in (0.80, 0.90, 1.00, 1.12, 1.25):
    s = sig*fac
    X = exponent(s)
    Tmax = 60.0*math.exp(min(6.0, X - exponent(sig)))*40.0
    Tmax = float(min(4000.0, max(300.0, Tmax)))
    r, ne, tot, sam = rate_mle(s, M, Tmax, DT, 20000 + int(10000*fac))
    if r is None:
        out(f" {s:.4e} | no escapes in {M} runs of {Tmax:.0f}s"); continue
    Tb = 1.0/r
    sm = (float(np.std(sam)/np.mean(sam)) if len(sam) > 3 else float('nan'))
    ae = alpha_eff(s)
    ROWS.append((s, X, Tb, ne, ae))
    out(f" {s:.4e} | {ae:.6f} | {(alpha-ae)/alpha*100:7.3f}% | {X:10.5f} | "
        f"{ne:3d}/{M} | {Tb:7.2f} | {math.log(Tb):6.3f} | {sm:.3f}   "
        f"[{time.time()-T0:.0f}s]")
out("")
if len(ROWS) >= 3:
    X = np.array([r[1] for r in ROWS])
    L = np.array([math.log(r[2]) for r in ROWS])
    sl, ic = np.polyfit(X, L, 1)
    res = L - (sl*X + ic)
    out(f"  ln T = {sl:.4f} X + {ic:.4f}   (mechanism requires slope = 1)")
    out(f"  residuals: " + ", ".join(f"{v:+.3f}" for v in res))
    X0 = np.array([alpha*alpha/(c1r*abs(g)**2*r[0]**2) for r in ROWS])
    sl0, ic0 = np.polyfit(X0, L, 1)
    res0 = L - (sl0*X0 + ic0)
    out(f"  same fit with alpha in place of alpha_eff (erosion ignored): "
        f"slope {sl0:.4f}, rms residual {float(np.sqrt(np.mean(res0**2))):.4f} "
        f"vs {float(np.sqrt(np.mean(res**2))):.4f} with erosion")
    out(f"  1-sigma noise floor on ln T at M={M}: "
        f"{1.0/math.sqrt(M):.4f}")
out(f"DONE wall={time.time()-T0:.0f}s")
