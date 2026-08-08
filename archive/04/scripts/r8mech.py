"""R8 机理分析:两张 Hopf 面分开追踪 + 模态身份 + 耦合缩放"""
import numpy as np, math
from scipy.optimize import linear_sum_assignment
from gfl_operating_point_stability_sim.analysis import equilibrium_angle

G1 = dict(kp=50, ki=1000, kpv=1, kiv=50, C=0.01)

def drift4(x, P, Q, V, Xg, g):
    th, xp, Vdc, xi = x
    idr = g['kpv']*(1-Vdc) + g['kiv']*xi
    vgd = V*math.cos(th) - Xg*Q
    vgq = -V*math.sin(th) + Xg*idr
    Vs = Vdc if abs(Vdc) > 1e-6 else 1e-6
    return np.array([g['kp']*vgq + g['ki']*xp, vgq,
                     (P + 1.5*(vgd*idr + vgq*Q)/Vs)/g['C'], 1-Vdc])

def state(P, Q, V, Xg, g):
    th = equilibrium_angle(P, Q, V, Xg)
    if th is None: return None
    return np.array([th, 0.0, 1.0, V*math.sin(th)/Xg/g['kiv']])

def Amat(P, Q, V, Xg, g, h=1e-7):
    x = state(P, Q, V, Xg, g)
    if x is None: return None
    A = np.zeros((4, 4))
    for j in range(4):
        a = x.copy(); b = x.copy(); a[j] += h; b[j] -= h
        A[:, j] = (drift4(a, P, Q, V, Xg, g) - drift4(b, P, Q, V, Xg, g))/(2*h)
    return A

def Psn(Q, V, Xg):
    if Q == 0.0: return 0.75*V*V/Xg
    lo, hi = 0.01, 3*V*V/Xg
    for _ in range(50):
        mid = 0.5*(lo+hi)
        if equilibrium_angle(mid, Q, V, Xg) is None: hi = mid
        else: lo = mid
    return lo

def eig_sorted(A, prev):
    ev = np.linalg.eigvals(A)
    if prev is None:
        return ev[np.argsort(-np.abs(ev.imag))]  # 复对在前
    cost = np.abs(ev[:, None] - prev[None, :])
    r, c = linear_sum_assignment(cost)
    out = np.empty(4, complex)
    out[c] = ev[r]
    return out

def participation(A):
    """每个特征值的 PLL 态 {0,1} 参与度份额"""
    lam, Vr = np.linalg.eig(A)
    Wl = np.linalg.inv(Vr)
    shares = []
    for k in range(4):
        p = np.abs(Vr[:, k]*Wl[k, :])
        p = p/p.sum()
        shares.append(p[0]+p[1])
    return lam, np.array(shares)

# ---------- Part A: 两张面分开追踪 ----------
print("== A: 逐分支延拓 (G1, Q=0, V=1) ==")
print("身份判定: 低 P 端参与因子 PLL 份额 (>0.5 记 PLL, 否则 DC)")
XG_A = [0.20, 0.30, 0.35, 0.40, 0.43, 0.45, 0.47, 0.50, 0.55, 0.60, 0.80, 1.00]
sheetPLL, sheetDC = {}, {}
for Xg in XG_A:
    ps = Psn(0, 1, Xg)
    Pg = np.linspace(0.15*ps, 0.99995*ps, 800)
    prev = None; rows = []
    for P in Pg:
        A = Amat(P, 0, 1, Xg, G1)
        if A is None: break
        prev = eig_sorted(A, prev)
        rows.append((P, prev.copy()))
    # 低 P 端身份
    A0 = Amat(Pg[0], 0, 1, Xg, G1)
    lam0, sh0 = participation(A0)
    # 把 rows[0] 的槽位对应到 lam0 的身份
    cost = np.abs(rows[0][1][:, None] - lam0[None, :])
    r, c = linear_sum_assignment(cost)
    slot_share = np.empty(4); slot_share[r] = sh0[c]
    # 找两个复对槽位(低 P 端 |Im|>1)
    slots = [k for k in range(4) if abs(rows[0][1][k].imag) > 1.0]
    pairs = {}
    seen = set()
    for k in slots:
        conj_partner = None
        for m in slots:
            if m != k and abs(rows[0][1][m] - rows[0][1][k].conjugate()) < 1e-6:
                conj_partner = m
        if k in seen: continue
        seen.add(k); seen.add(conj_partner)
        ident = 'PLL' if slot_share[k] > 0.5 else 'DC'
        pairs[k] = ident
    info = []
    for k, ident in pairs.items():
        f0 = abs(rows[0][1][k].imag)/2/math.pi
        share0 = slot_share[k]
        # 沿 P 找该槽位实部首次过零
        Pc, fc = None, None
        for i in range(1, len(rows)):
            if rows[i-1][1][k].real < 0 <= rows[i][1][k].real:
                Pc = rows[i][0]; fc = abs(rows[i][1][k].imag)/2/math.pi
                break
        endre = rows[-1][1][k].real
        info.append((ident, share0, f0, Pc, fc, endre))
        d = sheetPLL if ident == 'PLL' else sheetDC
        d[Xg] = (Pc, fc)
    txt = "; ".join(
        f"{ident}(份额{s:.2f},f0={f0:.1f}Hz): " +
        (f"过零P={Pc:.4f} f={fc:.1f}Hz" if Pc else f"不过零(末端Re={er:.1f})")
        for ident, s, f0, Pc, fc, er in info)
    print(f"  Xg={Xg:.2f} P_SN={ps:.3f}: {txt}")

print()
print("== A 汇总: 两张面 ==")
print("  Xg    P_cross(PLL面)   P_cross(DC面)   实际边界=较小者")
for Xg in XG_A:
    a = sheetPLL.get(Xg, (None, None))[0]
    b = sheetDC.get(Xg, (None, None))[0]
    lo = 'PLL' if (a or 9e9) < (b or 9e9) else 'DC'
    fa = f"{a:.4f}" if a else "  无  "
    fb = f"{b:.4f}" if b else "  无  "
    print(f"  {Xg:.2f}   {fa}          {fb}         {lo}")

# ---------- Part B: 固定 P 扫 Xg,看两支 Re 的推斥 ----------
print()
print("== B: 固定 P, 扫 Xg — 两支实部与频率 ==")
for Pfix in [1.42, 1.45]:
    print(f"  [P={Pfix}]")
    prev = None
    for Xg in np.arange(0.34, 0.561, 0.02):
        A = Amat(Pfix, 0, 1, Xg, G1)
        if A is None:
            print(f"    Xg={Xg:.2f}: 无平衡点"); prev = None; continue
        prev = eig_sorted(A, prev)
        cplx = sorted({(round(e.real, 3), round(abs(e.imag), 3))
                       for e in prev if abs(e.imag) > 1.0}, key=lambda t: -t[1])
        s = "  ".join(f"Re={re:+.2f} f={im/2/math.pi:.2f}Hz" for re, im in cplx)
        print(f"    Xg={Xg:.2f}: {s}")

# ---------- Part C: 耦合缩放 A = D + kappa*C ----------
print()
print("== C: 耦合缩放 (块 {th,xp} x {Vdc,xi}), kappa 0->1 ==")
for Xg, Pfix in [(0.40, 1.42), (0.50, 1.42), (0.45, 1.47)]:
    A = Amat(Pfix, 0, 1, Xg, G1)
    if A is None:
        print(f"  Xg={Xg} P={Pfix}: 无平衡点"); continue
    D = A.copy(); D[0:2, 2:4] = 0; D[2:4, 0:2] = 0
    C = A - D
    print(f"  [Xg={Xg} P={Pfix}] 解耦块特征值:")
    evP = np.linalg.eigvals(D[0:2, 0:2]); evD = np.linalg.eigvals(D[2:4, 2:4])
    print(f"    PLL块: {['%+.1f%+.1fj(f=%.1fHz)'%(e.real,e.imag,abs(e.imag)/2/math.pi) for e in evP]}")
    print(f"    DC块 : {['%+.1f%+.1fj(f=%.1fHz)'%(e.real,e.imag,abs(e.imag)/2/math.pi) for e in evD]}")
    prev = None
    for kap in [0.0, 0.2, 0.4, 0.6, 0.8, 0.9, 1.0]:
        M = D + kap*C
        prev = eig_sorted(M, prev)
        cplx = sorted({(round(e.real, 2), round(abs(e.imag), 2))
                       for e in prev if abs(e.imag) > 1.0}, key=lambda t: -t[1])
        s = "  ".join(f"Re={re:+.2f} f={im/2/math.pi:.2f}Hz" for re, im in cplx)
        real = sorted({round(e.real, 2) for e in prev if abs(e.imag) <= 1.0})
        if real: s += "  实根:" + ",".join(f"{r:+.2f}" for r in real)
        print(f"    k={kap:.1f}: {s}")
