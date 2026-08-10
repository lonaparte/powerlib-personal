"""The noise-activated branch, with an integrator that can actually resolve it.

The first attempt used Euler-Maruyama at dt = 2e-4 and the escape time was
nowhere near converged: T = 14.08 s at dt = 4e-4 against 26.76 s at
2e-4, on identical seeds.  That is not a bad choice of dt, it is the
mechanism biting.  Escape time is exponential in the barrier-to-noise
ratio, ln T = X + const with X ~ 3.4 here, so a 10% error in the effective
diffusion moves T by 34%.  Any scheme whose discretisation error acts like
an effective noise gets amplified by exp(X); the measurement demands a
converged step, not a plausible one.

Two changes make that affordable rather than hopeless:

 - Heun (stochastic predictor-corrector).  For ADDITIVE noise there is no
   Ito/Stratonovich correction and no Milstein term, so Heun is weak order
   2 while Euler-Maruyama is weak order 1.  The dt at which the bias falls
   below the effect is then far larger.
 - a vectorised ensemble.  All M realisations advance as one (M,4) array,
   so the cost of 200 realisations is close to the cost of one, and dt can
   be pushed to 2.5e-5 without the run becoming unaffordable.

The physics being tested is unchanged and still carries no fitted constant.
With u white of intensity <u(t)u(t')> = sigma^2 delta(t-t'):

    one-sided PSD          S_u = sigma^2/pi
    erosion                alpha_eff = alpha - (sigma^2/2pi) int Re c_x(w) dw
    envelope diffusion     Dtilde = |g|^2 sigma^2/4 ,  g = <p, f_u>
    barrier                Delta U = alpha_eff^2/(4 Re c1)
    Kramers                ln T = Delta U/Dtilde + const
                                = alpha_eff^2/(Re c1 |g|^2 sigma^2) + const .

alpha_eff and the barrier are built from the SAME c_x and c1 as the
deterministic branch.  Only the prefactor (the intercept) is free, so the
claim under test is a slope of exactly one against the predicted exponent.

Three things must hold together or the identification is not earned:
 (a) escape times exponentially distributed -- std/mean -> 1 -- which is
     what distinguishes a rate process from a deterministic crossing;
 (b) slope 1 against X;
 (c) the erosion term earning its place: refitting with alpha instead of
     alpha_eff must be visibly worse.
Budget ~45 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/noise2b.log', 'w')
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
KP, KI, KPV, KIV, CC = pr['kp'], pr['ki'], pr['kpv'], pr['kiv'], pr['C']
PP, QQ, VV, XG = pr['P'], pr['Q'], pr['V'], pr['Xg']
out(f"G1 margin 0.10: alpha={alpha:.6f} w0={w0:.5f} Re c1={c1r:.6e}")
out(f"  |g|=|<p,f_V>|={abs(g):.6e}  rho_g(sigma=0)={rg0:.6e}  "
    f"DeltaU(sigma=0)={alpha**2/(4*c1r):.6e}")


def rhs_vec(X):
    th = X[:, 0]; xp = X[:, 1]; Vdc = X[:, 2]; xi = X[:, 3]
    idr = KPV*(1.0 - Vdc) + KIV*xi
    vgd = VV*np.cos(th) - XG*QQ
    vgq = -VV*np.sin(th) + XG*idr
    Vs = np.where(np.abs(Vdc) > 1e-6, Vdc, 1e-6)
    Y = np.empty_like(X)
    Y[:, 0] = KP*vgq + KI*xp
    Y[:, 1] = vgq
    Y[:, 2] = (PP + 1.5*(vgd*idr + vgq*QQ)/Vs)/CC
    Y[:, 3] = 1.0 - Vdc
    return Y


def out_of_box(X):
    return ((np.abs(X[:, 0] - st[0]) > dsad) | (X[:, 2] < 0.20*Vdc0)
            | (X[:, 2] > 2.50*Vdc0) | ~np.isfinite(X[:, 0]))


def ensemble(sig, M, Tmax, dt, seed):
    """Heun with additive noise; returns (escape times, censored count)."""
    rng = np.random.default_rng(seed)
    X = np.tile(st, (M, 1)).astype(float)
    alive = np.ones(M, bool)
    tesc = np.full(M, np.nan)
    sq = sig*math.sqrt(dt)
    n = int(round(Tmax/dt))
    t = 0.0
    chunk = 4000
    done = 0
    while done < n and alive.any():
        m = min(chunk, n - done)
        Z = rng.standard_normal((m, int(alive.sum()), 4)) if False else None
        xi = rng.standard_normal((m, M))
        for i in range(m):
            idx = alive
            Xi = X[idx]
            dW = (sq*xi[i][idx])[:, None]*bvec[None, :]
            F1 = rhs_vec(Xi)
            Xp = Xi + F1*dt + dW
            bad = ~np.isfinite(Xp).all(axis=1)
            Xp[bad] = Xi[bad]
            F2 = rhs_vec(Xp)
            Xn = Xi + 0.5*(F1 + F2)*dt + dW
            X[idx] = Xn
            t += dt
            gone = np.zeros(M, bool)
            gone[idx] = out_of_box(Xn)
            newly = gone & alive
            if newly.any():
                tesc[newly] = t
                alive &= ~newly
            if not alive.any():
                break
        done += m
    return tesc, int(alive.sum()), min(t, Tmax)


def rate_of(tesc, ncens, Tobs):
    esc = tesc[~np.isnan(tesc)]
    tot = float(esc.sum() + ncens*Tobs)
    if len(esc) == 0:
        return None, 0, float('nan')
    sm = float(np.std(esc)/np.mean(esc)) if len(esc) > 3 else float('nan')
    return len(esc)/tot, len(esc), sm


# ---- erosion integral ----
def cxw(w):
    return cx_hand(A, st, pr, qvec, pvec, w0, w, bvec).real


WG = np.unique(np.concatenate([np.linspace(0.02, 0.7, 40)*w0,
                               np.linspace(0.70, 1.30, 90)*w0,
                               np.linspace(1.30, 4.0, 60)*w0,
                               np.linspace(4.0, 80.0, 110)*w0]))
CV = np.array([cxw(w) for w in WG])
trap = np.trapezoid if hasattr(np, 'trapezoid') else np.trapz
Icx = float(trap(CV, WG)); tailA = float(CV[-1]*WG[-1])
out(f"  int Re c_x dw over [0.02,80] w0 = {Icx:.6e}, tail estimate "
    f"{tailA:.6e} ({tailA/Icx*100:.2f}%), Re c_x(w0)={cxw(w0):.5e}")
Icx += tailA


def alpha_eff(s):
    return alpha - s*s*Icx/(2*math.pi)


def exponent(s):
    ae = alpha_eff(s)
    return ae*ae/(c1r*abs(g)**2*s*s)


SIG = 4.0e-6
out("")
out(f"--- dt convergence, Heun, sigma={SIG:.3e}, X={exponent(SIG):.4f}, "
    f"M=120, identical seed ---")
prev = None
for dt in (2.0e-4, 1.0e-4, 5.0e-5, 2.5e-5):
    te, nc, Tob = ensemble(SIG, 120, 120.0, dt, 4242)
    r, ne, sm = rate_of(te, nc, Tob)
    Tb = (1.0/r) if r else float('inf')
    ch = "" if prev is None else f"  change {(Tb-prev)/prev*100:+7.2f}%"
    out(f"  dt={dt:.2e}  escapes {ne}/120  T={Tb:8.3f}s  std/mean={sm:.3f}"
        f"{ch}  [{time.time()-T0:.0f}s]")
    prev = Tb
DT = 5.0e-5

out("")
out("=== Kramers sweep: ln T against X = alpha_eff^2/(Re c1 |g|^2 sigma^2)")
out(" sigma      | alpha_eff | erosion | X        | escapes | T (s)    | "
    "ln T   | std/mean")
M = 200
ROWS = []
for fac in (0.82, 0.90, 1.00, 1.10, 1.22):
    s = SIG*fac
    X = exponent(s)
    Tmax = float(min(2500.0, max(150.0, 90.0*math.exp(X - exponent(SIG)))))
    te, nc, Tob = ensemble(s, M, Tmax, DT, 90000 + int(1000*fac*100))
    r, ne, sm = rate_of(te, nc, Tob)
    if r is None:
        out(f" {s:.4e} | no escapes in {M} runs of {Tmax:.0f}s")
        continue
    Tb = 1.0/r
    ae = alpha_eff(s)
    ROWS.append((s, X, Tb, ne, ae))
    out(f" {s:.4e} | {ae:.6f} | {(alpha-ae)/alpha*100:6.3f}% | {X:8.5f} | "
        f"{ne:3d}/{M} | {Tb:8.3f} | {math.log(Tb):6.3f} | {sm:.3f}   "
        f"[{time.time()-T0:.0f}s]")
out("")
if len(ROWS) >= 3:
    X = np.array([r[1] for r in ROWS]); L = np.array([math.log(r[2])
                                                      for r in ROWS])
    sl, ic = np.polyfit(X, L, 1)
    res = L - (sl*X + ic)
    out(f"  ln T = {sl:.4f} X + {ic:.4f}      (mechanism requires slope 1)")
    out(f"  residuals: " + ", ".join(f"{v:+.4f}" for v in res)
        + f"   rms {float(np.sqrt(np.mean(res**2))):.4f}")
    X0 = np.array([alpha*alpha/(c1r*abs(g)**2*r[0]**2) for r in ROWS])
    sl0, ic0 = np.polyfit(X0, L, 1)
    r0 = L - (sl0*X0 + ic0)
    out(f"  erosion ignored (alpha in place of alpha_eff): slope {sl0:.4f}, "
        f"rms {float(np.sqrt(np.mean(r0**2))):.4f}")
    out(f"  1-sigma noise floor on ln T at M={M}: {1.0/math.sqrt(M):.4f}")
    out(f"  X span {X.min():.4f}..{X.max():.4f} "
        f"(a slope test needs this >> the noise floor)")
out(f"DONE wall={time.time()-T0:.0f}s")
