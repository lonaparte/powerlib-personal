"""Kramers branch: split the claim so each half is testable in its own regime.

The full-system run hit a hard obstruction that is worth stating rather than
working around silently.  The escape time is T = T0 exp(X) with

    X = alpha_eff^2 / (Re c1 |g|^2 sigma^2)

and the measured prefactor is T0 ~ 42 s, about 4/alpha.  To keep T inside a
runnable window the sweep is forced to X <~ 1 -- and X <~ 1 means the
barrier is comparable to the noise, which is precisely where Kramers
asymptotics (barrier >> noise) does NOT apply.  The observed std/mean of
0.675 at X = 0.50 says the same thing: a genuine rate process has an
exponential first-passage time and std/mean -> 1, and 0.675 is the
signature of a nearly barrierless crossing.  Measuring the slope there
would be measuring the crossover, then calling it the asymptote.

So the claim is split into two, each tested where it is testable:

  (I) THE REDUCTION.  The 4-state system driven by additive white noise
      behaves like the 2D envelope SDE
          dZ = [-alpha_eff Z + c1 Z |Z|^2] dt + sqrt(2 Dtilde) dW,
          alpha_eff = alpha - (sigma^2/2pi) int Re c_x dw,
          Dtilde    = |g|^2 sigma^2/4 ,
      with alpha_eff, c1 and g all taken from the deterministic theory.
      Testable exactly where the full model is affordable, X ~ 0.5-1.5, by
      comparing escape-time distributions, not just means.

 (II) THE RATE LAW.  That 2D SDE obeys ln T = X + const.  Testable cheaply
      out to X ~ 6, because the reduced model has no fast timescale left
      (the carrier is rotated away, leaving rates alpha_eff ~ 0.05 and
      Re c1 rho^2 ~ 0.1), so dt = 1e-3 suffices where the full model needed
      5e-5 -- a factor 20 in step size on top of a 2-component state.

Together they are the original claim, and neither half is evaluated outside
its domain.  If (I) holds and (II) gives slope 1 with std/mean -> 1 as X
grows, the identification is earned.  If (I) fails, the reduction is wrong
and (II) is irrelevant; if (II) fails, the barrier formula is wrong.
Budget ~35 min.
"""
exec(open('selfhead.py').read())
exec(open('nf5drv.py').read())
import time
LOG = open('sweep20/noise3.log', 'w')
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
lam = co['lam']; pvec = co['p']; qvec = co['q']
c1c = co['c1']; c1r = c1c.real; c1i = c1c.imag
A = jac(st, pr)
dsad = math.pi - 2*abs(st[0]); Vdc0 = st[2]
bvec = (rhs(st, dict(pr, V=pr['V']+hs))
        - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
g = np.vdot(pvec, bvec)
KP, KI, KPV, KIV, CC = pr['kp'], pr['ki'], pr['kpv'], pr['kiv'], pr['C']
PP, QQ, VV, XG = pr['P'], pr['Q'], pr['V'], pr['Xg']
out(f"G1 margin 0.10: alpha={alpha:.6f} w0={w0:.5f} c1={c1c:.6e}")
out(f"  |g|={abs(g):.6e}")


def cxw(w):
    return cx_hand(A, st, pr, qvec, pvec, w0, w, bvec).real


WG = np.unique(np.concatenate([np.linspace(0.02, 0.7, 40)*w0,
                               np.linspace(0.70, 1.30, 90)*w0,
                               np.linspace(1.30, 4.0, 60)*w0,
                               np.linspace(4.0, 80.0, 110)*w0]))
CV = np.array([cxw(w) for w in WG])
trap = np.trapezoid if hasattr(np, 'trapezoid') else np.trapz
Icx = float(trap(CV, WG)) + float(CV[-1]*WG[-1])
out(f"  int Re c_x dw = {Icx:.6e}")


def alpha_eff(s):
    return alpha - s*s*Icx/(2*math.pi)


def Dt(s):
    return abs(g)**2*s*s/4.0


def exponent(s):
    ae = alpha_eff(s)
    return ae*ae/(c1r*abs(g)**2*s*s)


def rho_g(s):
    ae = alpha_eff(s)
    return math.sqrt(ae/c1r) if ae > 0 else float('nan')


# ---------------- reduced 2D envelope SDE ----------------
def reduced(sig, M, Tmax, dt, seed):
    rng = np.random.default_rng(seed)
    ae = alpha_eff(sig); D = Dt(sig)
    rgv = rho_g(sig)
    if not (rgv == rgv):
        return None, 0, Tmax
    sq = math.sqrt(2.0*D*dt)
    Z = np.zeros((M, 2))
    alive = np.ones(M, bool)
    tesc = np.full(M, np.nan)
    n = int(round(Tmax/dt)); t = 0.0
    blk = 20000; done = 0
    lim = (3.0*rgv)**2
    while done < n and alive.any():
        m = min(blk, n - done)
        xi = rng.standard_normal((m, M, 2))
        for i in range(m):
            idx = alive
            Zi = Z[idx]
            r2 = Zi[:, 0]**2 + Zi[:, 1]**2
            fx = -ae*Zi[:, 0] + c1r*r2*Zi[:, 0] - c1i*r2*Zi[:, 1]
            fy = -ae*Zi[:, 1] + c1r*r2*Zi[:, 1] + c1i*r2*Zi[:, 0]
            Zn = Zi.copy()
            Zn[:, 0] += fx*dt + sq*xi[i][idx][:, 0]
            Zn[:, 1] += fy*dt + sq*xi[i][idx][:, 1]
            Z[idx] = Zn
            t += dt
            gone = np.zeros(M, bool)
            gone[idx] = (Zn[:, 0]**2 + Zn[:, 1]**2 > lim) | \
                        ~np.isfinite(Zn).all(axis=1)
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
    sm = float(np.std(esc)/np.mean(esc)) if len(esc) > 5 else float('nan')
    return len(esc)/tot, len(esc), sm


# ---------------- full 4D system, Heun ----------------
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


def full4(sig, M, Tmax, dt, seed):
    rng = np.random.default_rng(seed)
    Xs = np.tile(st, (M, 1)).astype(float)
    alive = np.ones(M, bool)
    tesc = np.full(M, np.nan)
    sq = sig*math.sqrt(dt)
    n = int(round(Tmax/dt)); t = 0.0
    blk = 4000; done = 0
    while done < n and alive.any():
        m = min(blk, n - done)
        xi = rng.standard_normal((m, M))
        for i in range(m):
            idx = alive
            Xi = Xs[idx]
            dW = (sq*xi[i][idx])[:, None]*bvec[None, :]
            F1 = rhs_vec(Xi)
            Xp = Xi + F1*dt + dW
            bad = ~np.isfinite(Xp).all(axis=1)
            Xp[bad] = Xi[bad]
            Xn = Xi + 0.5*(F1 + rhs_vec(Xp))*dt + dW
            Xs[idx] = Xn
            t += dt
            gone = np.zeros(M, bool)
            gone[idx] = ((np.abs(Xn[:, 0] - st[0]) > dsad)
                         | (Xn[:, 2] < 0.20*Vdc0) | (Xn[:, 2] > 2.50*Vdc0)
                         | ~np.isfinite(Xn[:, 0]))
            newly = gone & alive
            if newly.any():
                tesc[newly] = t
                alive &= ~newly
            if not alive.any():
                break
        done += m
    return tesc, int(alive.sum()), min(t, Tmax)


SIG = 6.57213e-06
out("")
out("=== (I) does the 4-state system follow the 2D envelope SDE? ===")
out(" sigma      |   X    | full-4D T   n_esc std/mean | reduced T   "
    "n_esc std/mean | ratio")
for fac in (1.15, 1.00, 0.88):
    s = SIG*fac
    Xv = exponent(s)
    Tm = float(min(1200.0, max(120.0, 60.0*math.exp(Xv))))
    tf, nf, Tof = full4(s, 120, Tm, 2.0e-4, 31000 + int(1000*fac*100))
    rf, nef, smf = rate_of(tf, nf, Tof)
    tr, nr, Tor = reduced(s, 3000, Tm, 1.0e-3, 41000 + int(1000*fac*100))
    rr, ner, smr = rate_of(tr, nr, Tor)
    Tf = (1/rf) if rf else float('nan')
    Tr = (1/rr) if rr else float('nan')
    out(f" {s:.4e} | {Xv:6.3f} | {Tf:9.3f} {nef:4d} {smf:8.3f} | "
        f"{Tr:9.3f} {ner:5d} {smr:8.3f} | {Tf/Tr:.4f}  "
        f"[{time.time()-T0:.0f}s]")

out("")
out("=== (II) does the reduced SDE obey ln T = X + const? ===")
out(" sigma      | alpha_eff | erosion |   X    | n_esc/M  | T (s)      | "
    "ln T    | std/mean")
ROWS = []
for fac in (1.15, 1.00, 0.88, 0.78, 0.70, 0.62, 0.55, 0.50):
    s = SIG*fac
    Xv = exponent(s)
    if not (rho_g(s) == rho_g(s)):
        continue
    Tm = float(min(120000.0, max(200.0, 200.0*math.exp(Xv))))
    M = 3000 if Xv < 3.5 else 1200
    tr, nc, Tob = reduced(s, M, Tm, 1.0e-3, 55000 + int(1000*fac*100))
    r, ne, sm = rate_of(tr, nc, Tob)
    if r is None:
        out(f" {s:.4e} | no escapes in {M} runs of {Tm:.0f}s"); continue
    Tb = 1.0/r
    ae = alpha_eff(s)
    ROWS.append((s, Xv, Tb, ne, sm))
    out(f" {s:.4e} | {ae:.6f} | {(alpha-ae)/alpha*100:6.2f}% | {Xv:6.3f} | "
        f"{ne:5d}/{M:<5d}| {Tb:10.3f} | {math.log(Tb):7.3f} | {sm:.3f}  "
        f"[{time.time()-T0:.0f}s]")
out("")
if len(ROWS) >= 4:
    Xa = np.array([r[1] for r in ROWS])
    La = np.array([math.log(r[2]) for r in ROWS])
    sl, ic = np.polyfit(Xa, La, 1)
    res = La - (sl*Xa + ic)
    out(f"  all points:  ln T = {sl:.4f} X + {ic:.4f}   rms "
        f"{float(np.sqrt(np.mean(res**2))):.4f}")
    sel = Xa > 1.5
    if sel.sum() >= 3:
        sl2, ic2 = np.polyfit(Xa[sel], La[sel], 1)
        r2 = La[sel] - (sl2*Xa[sel] + ic2)
        out(f"  X > 1.5 only (the asymptotic regime): ln T = {sl2:.4f} X + "
            f"{ic2:.4f}   rms {float(np.sqrt(np.mean(r2**2))):.4f}")
        out(f"  Kramers requires slope 1; prefactor exp({ic2:.3f}) = "
            f"{math.exp(ic2):.1f} s = {math.exp(ic2)*alpha:.2f}/alpha")
    out("  std/mean must approach 1 as X grows (rate process): " +
        ", ".join(f"X={r[1]:.2f}:{r[4]:.2f}" for r in ROWS))
    X0 = np.array([alpha*alpha/(c1r*abs(g)**2*r[0]**2) for r in ROWS])
    sl0, ic0 = np.polyfit(X0, La, 1)
    rr0 = La - (sl0*X0 + ic0)
    out(f"  erosion ignored (alpha for alpha_eff): slope {sl0:.4f}, rms "
        f"{float(np.sqrt(np.mean(rr0**2))):.4f} vs "
        f"{float(np.sqrt(np.mean(res**2))):.4f} with erosion")
out(f"DONE wall={time.time()-T0:.0f}s")
