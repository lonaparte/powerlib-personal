"""盲区闭式 B=1-sqrt(1-zeta0^4) 验证 + 矩阵束法救回重阻尼/多模态频率读数"""
import numpy as np, math
from scipy.optimize import fsolve
from scipy.integrate import solve_ivp
from scipy.linalg import hankel, svd, pinv, eig as geig
from gfl_operating_point_stability_sim.analysis import equilibrium_angle
import sympy as sp

# ---- GFM 模型(同 r16wide) ----
delta, omega, Pf, Qf = sp.symbols('delta omega Pf Qf', real=True)
Ps_, Qs_, Vs_, Xs_, Ms_, Ds_, ms_, ws_, Es_ = sp.symbols('Pref Qref V Xg M D mq wc Enom', positive=True)
E_e = Es_ - ms_*(Qf - Qs_)
Pe = E_e*Vs_/Xs_*sp.sin(delta); Qe = (E_e**2 - E_e*Vs_*sp.cos(delta))/Xs_
fv = sp.Matrix([omega, (Ps_ - Pf - Ds_*omega)/Ms_, ws_*(Pe - Pf), ws_*(Qe - Qf)])
Jv = fv.jacobian(sp.Matrix([delta, omega, Pf, Qf]))
args = (delta, omega, Pf, Qf, Ps_, Qs_, Vs_, Xs_, Ms_, Ds_, ms_, ws_, Es_)
f_l = sp.lambdify(args, fv, 'numpy'); J_l = sp.lambdify(args, Jv, 'numpy')

def rhs(st, d): return np.array(f_l(*st, d['Pref'], d['Qref'], d['V'], d['Xg'],
                                    d['M'], d['D'], d['mq'], d['wc'], d['Enom']), float).ravel()
def equil(d):
    def res(z):
        r = rhs([z[0], 0.0, d['Pref'], z[1]], d); return [r[2], r[3]]
    for dl0 in (0.1, 0.3, 0.6, 0.9, 1.2, 1.45):
        z, info, ier, msg = fsolve(res, [dl0, 0.0], full_output=True)
        st = np.array([z[0], 0.0, d['Pref'], z[1]])
        if ier == 1 and np.max(np.abs(rhs(st, d))) < 1e-9 and 0 < z[0] < np.pi/2: return st
    return None
def Amat(d):
    st = equil(d)
    if st is None: return None, None
    return np.array(J_l(*st, d['Pref'], d['Qref'], d['V'], d['Xg'],
                        d['M'], d['D'], d['mq'], d['wc'], d['Enom']), float), st
def swing(A):
    lam, Vr = np.linalg.eig(A); Wl = np.linalg.inv(Vr)
    for k in np.argsort(-np.abs(np.imag(lam))):
        if abs(lam[k].imag) < 1e-7: break
        p = np.abs(Vr[:, k]*Wl[k, :]); p = p/p.sum()
        if p[0]+p[1] > 0.5: return lam[k]
    return None

GFM_SETS = {
    "M1": dict(M=0.02, D=0.05, mq=0.1, wc=2*math.pi*31),
    "M2": dict(M=0.1, D=0.2, mq=0.05, wc=2*math.pi*10),
    "M3": dict(M=0.005, D=0.02, mq=0.2, wc=2*math.pi*100),
    "M4": dict(M=0.05, D=0.5, mq=0.1, wc=2*math.pi*5),
    "M5": dict(M=0.02, D=0.02, mq=0.1, wc=2*math.pi*20),
    "M6": dict(M=0.02, D=0.05, mq=0.0, wc=2*math.pi*31),
    "M7": dict(M=0.02, D=0.05, mq=0.1, wc=2*math.pi*200),
    "M8": dict(M=0.02, D=0.05, mq=0.1, wc=2*math.pi*3),
    "M9": dict(M=0.5, D=1.0, mq=0.05, wc=2*math.pi*31),
    "M10": dict(M=0.002, D=0.1, mq=0.1, wc=2*math.pi*50),
}

print("== 1: 盲区闭式 B=1-sqrt(1-zeta0^4) vs 实测 ==")
errs = []; fullblind_pred_ok = 0; fullblind_pred_n = 0
by_wc = {}
for name, ps in GFM_SETS.items():
    for Xgv in (0.2, 0.5, 1.0):
        for Vv in (0.8, 1.0, 1.2):
            lo, hi = 0.01, 2.5*Vv/Xgv
            for _ in range(40):
                mid = 0.5*(lo+hi)
                if equil(dict(ps, Pref=mid, Qref=0.0, V=Vv, Xg=Xgv, Enom=1.0)) is None: hi = mid
                else: lo = mid
            pfold = lo
            # zeta0: 轻载端 K
            d0 = dict(ps, Pref=0.05*pfold, Qref=0.0, V=Vv, Xg=Xgv, Enom=1.0)
            A0, st0 = Amat(d0)
            if A0 is None: continue
            E0 = 1.0 - ps['mq']*(st0[3] - 0.0)
            K0 = E0*Vv*math.cos(st0[0])/Xgv
            z0 = ps['D']/(2*math.sqrt(ps['M']*K0))
            gam = z0*z0
            B_pred = 1.0 if gam >= 1 else 1 - math.sqrt(1-gam*gam)
            # 实测盲区
            grid = np.linspace(0.05*pfold, 0.999*pfold, 150)
            last_osc = None
            for P in grid:
                A, st = Amat(dict(ps, Pref=P, Qref=0.0, V=Vv, Xg=Xgv, Enom=1.0))
                if A is None: continue
                if swing(A) is not None: last_osc = P
            B_meas = 1.0 if last_osc is None else (pfold-last_osc)/pfold
            if B_pred >= 1.0 or B_meas >= 0.99:
                fullblind_pred_n += 1
                if (B_pred >= 1.0) == (B_meas >= 0.99): fullblind_pred_ok += 1
                continue
            errs.append((abs(B_pred-B_meas), name, Xgv, Vv, B_pred, B_meas))
            fc = ps['wc']/2/math.pi
            by_wc.setdefault(fc, []).append(B_pred-B_meas)
er = np.array([e[0] for e in errs])
print(f"  部分盲区 n={len(er)}: |B_pred-B_meas| 中位={np.median(er)*100:.2f}pp  max={er.max()*100:.1f}pp")
worst = sorted(errs, reverse=True)[:4]
for w in worst: print(f"    最差: {w[1]} Xg={w[2]} V={w[3]}  pred={w[4]*100:.1f}% meas={w[5]*100:.1f}%")
print(f"  全盲判定 (zeta0>=1): {fullblind_pred_ok}/{fullblind_pred_n} 正确")
print("  按滤波带宽的偏差方向 (pred-meas, 中位 pp):")
for fc in sorted(by_wc):
    print(f"    fc={fc:.0f}Hz: {np.median(by_wc[fc])*100:+.2f}")

# ---- 2: 矩阵束法 ----
def matrix_pencil(y, dt, K=4):
    N = len(y); L = N//3
    Y = hankel(y[:N-L], y[N-L-1:])
    Y0, Y1 = Y[:, :-1], Y[:, 1:]
    U, s, Vh = svd(Y0, full_matrices=False)
    k = min(K, int(np.sum(s > 1e-10*s[0])))
    Uk = U[:, :k]; Sk = np.diag(s[:k]); Vk = Vh[:k, :].conj().T
    A_ = Uk.conj().T @ Y1 @ Vk @ np.linalg.inv(Sk)
    z = np.linalg.eigvals(A_)
    lam = np.log(z.astype(complex))/dt
    return lam[np.abs(lam.imag) > 1e-3]

print()
print("== 2: 重阻尼/多模态: FFT vs 矩阵束 ==")
def ring(rhs_f, x0, T, n=4000):
    t = np.linspace(0, T, n)
    sol = solve_ivp(rhs_f, (0, T), x0, t_eval=t, rtol=1e-11, atol=1e-13, method='DOP853')
    return t, sol.y[0] - sol.y[0][-1]

# GFM M9 (重阻尼慢摆) 3 个负载点
ps = GFM_SETS["M9"]; Xgv = 0.5
lo, hi = 0.01, 5.0
for _ in range(40):
    mid = 0.5*(lo+hi)
    if equil(dict(ps, Pref=mid, Qref=0.0, V=1.0, Xg=Xgv, Enom=1.0)) is None: hi = mid
    else: lo = mid
pfold = lo
for frq in (0.2, 0.5, 0.8):
    d = dict(ps, Pref=frq*pfold, Qref=0.0, V=1.0, Xg=Xgv, Enom=1.0)
    A, st = Amat(d)
    lam_true = swing(A)
    T = 6.0/abs(lam_true.real)
    x0 = st.copy(); x0[0] += 0.02
    t, y = ring(lambda tt, x: rhs(x, d), x0, min(T, 40))
    lam_mp = matrix_pencil(y, t[1]-t[0])
    best = min(lam_mp, key=lambda z: abs(z - lam_true))
    ferr = abs(abs(best.imag)-abs(lam_true.imag))/abs(lam_true.imag)*100
    rerr = abs(best.real-lam_true.real)/abs(lam_true.real)*100
    print(f"  M9 P={frq:.1f}pf: 真值 {lam_true.real:+.3f}{abs(lam_true.imag):+.3f}j"
          f"  矩阵束 f 误差={ferr:.3f}%  Re 误差={rerr:.3f}%  (FFT 曾差 34-40%)")

# GFL G1 双模态一次读出
g = dict(kp=50, ki=1000, kpv=1, kiv=50, C=0.01)
def gdrift(x, P, Q, V, Xg, g):
    th, xp, Vdc, xi = x
    idr = g['kpv']*(1-Vdc) + g['kiv']*xi
    vgd = V*math.cos(th) - Xg*Q; vgq = -V*math.sin(th) + Xg*idr
    Vs = Vdc if abs(Vdc) > 1e-6 else 1e-6
    return np.array([g['kp']*vgq + g['ki']*xp, vgq, (P+1.5*(vgd*idr+vgq*Q)/Vs)/g['C'], 1-Vdc])
for P in (0.4, 0.9):
    th = equilibrium_angle(P, 0, 1.0, 0.5)
    x0 = np.array([th+0.01, 0.0, 1.0, math.sin(th)/0.5/g['kiv']])
    A = np.zeros((4, 4)); xeq = np.array([th, 0.0, 1.0, math.sin(th)/0.5/g['kiv']])
    for j in range(4):
        a = xeq.copy(); b = xeq.copy(); a[j] += 1e-7; b[j] -= 1e-7
        A[:, j] = (gdrift(a, P, 0, 1, 0.5, g)-gdrift(b, P, 0, 1, 0.5, g))/2e-7
    ev = np.linalg.eigvals(A)
    cplx = sorted([e for e in ev if e.imag > 1.0], key=lambda z: -z.imag)
    t, y = ring(lambda tt, x: gdrift(x, P, 0, 1.0, 0.5, g), x0, 4.0)
    lam_mp = matrix_pencil(y, t[1]-t[0])
    out = []
    for lt in cplx:
        best = min(lam_mp, key=lambda z: abs(z-lt))
        out.append(f"真{abs(lt.imag)/2/math.pi:.2f}Hz->测{abs(best.imag)/2/math.pi:.2f}Hz"
                   f"(f误差{abs(abs(best.imag)-abs(lt.imag))/abs(lt.imag)*100:.2f}%)")
    print(f"  G1 P={P}: 两模态同时读出: " + "; ".join(out) + "  (FFT 只能读单峰,曾差 11-20%)")
