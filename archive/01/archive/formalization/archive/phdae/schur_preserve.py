"""
pH-DAE 核心问题：Schur 补何时保持 pH 结构？

系统：E x' = (J-R)Qx + Bu
分块：
  [Ed 0] [xd']   [J11-R11  J12-R12] [Qd xd]   [Bd]
  [0  0] [xa'] = [J21-R21  J22-R22] [Qa xa] + [Ba] u

代数方程：0 = (J21-R21)Qd xd + (J22-R22)Qa xa + Ba u
消去 xa：Qa xa = -(J22-R22)^{-1} [(J21-R21)Qd xd + Ba u]

约化动力学：Ed xd' = S Qd xd + B_eff u
其中 S = (J11-R11) - (J12-R12)(J22-R22)^{-1}(J21-R21)

问题：S = J_eff - R_eff 中 J_eff 反对称且 R_eff >= 0 吗？

理论分析：
"""
import numpy as np
from numpy.linalg import inv, eigvalsh, det

def check_ph_structure(J_full, R_full, n_d, n_a):
    """检查全矩阵的 pH 结构和 Schur 补的 pH 结构"""
    n = n_d + n_a
    
    # 提取分块
    J11 = J_full[:n_d, :n_d]
    J12 = J_full[:n_d, n_d:]
    J21 = J_full[n_d:, :n_d]
    J22 = J_full[n_d:, n_d:]
    
    R11 = R_full[:n_d, :n_d]
    R12 = R_full[:n_d, n_d:]
    R21 = R_full[n_d:, :n_d]
    R22 = R_full[n_d:, n_d:]
    
    # 检查全矩阵 pH 性质
    J_skew = np.max(np.abs(J_full + J_full.T))
    R_psd = np.min(eigvalsh(R_full))
    
    # 计算 Schur 补
    M22 = J22 - R22
    if abs(det(M22)) < 1e-10:
        return {"index_1": False, "reason": "J22-R22 singular (not index 1)"}
    
    M22_inv = inv(M22)
    M12 = J12 - R12
    M21 = J21 - R21
    
    S = (J11 - R11) - M12 @ M22_inv @ M21
    
    # 分解 S = J_eff - R_eff
    J_eff = (S - S.T) / 2  # 反对称部分
    R_eff = -(S + S.T) / 2  # 对称部分取负（因为 S = J-R, 对称部分 = -R）
    
    R_eff_eigvals = eigvalsh(R_eff)
    
    return {
        "index_1": True,
        "J_skew_error": J_skew,
        "R_min_eigval": R_psd,
        "S": S,
        "J_eff": J_eff,
        "R_eff": R_eff,
        "R_eff_min_eigval": np.min(R_eff_eigvals),
        "ph_preserved": np.min(R_eff_eigvals) >= -1e-10,
    }

# ================================================================
# 案例 1：两机通过电阻线路互联（标准情况）
# ================================================================
# 动态状态：w1, w2, delta（3个）
# 代数状态：网络中间节点电压 v_m（1个）
# 
# 实际上两机直接互联没有代数变量。
# 加一个中间节点：
# 机器1 -- 线路1(阻抗Z1) -- 节点m -- 线路2(阻抗Z2) -- 机器2
#
# 代数约束（节点m功率平衡）：
# P_{1m}/Z1 + P_{2m}/Z2 = 0（简化：电流守恒）
#
# 简化为线性模型（小角度）：
# 动态：w1' = -D1*w1 - K1*(d1-dm), w2' = -D2*w2 - K2*(dm-d2)
#        d1' = w1, d2' = w2
# 代数：K1*(d1-dm) + K2*(dm-d2) = 0 → dm = (K1*d1+K2*d2)/(K1+K2)
#
# pH 形式（4 动态 + 1 代数 = 5维）：

print("=" * 60)
print("Case 1: Two machines through intermediate bus")
print("=" * 60)

# 动态状态：(d1, d2, w1, w2)，代数状态：(dm)
# J_full: 反对称互联
# 简化模型 - 对角阻尼 + 互联

K1, K2 = 1.0, 1.0
D1, D2 = 1.0, 1.0

# 状态：(d1, d2, w1, w2 | dm)
# d1' = w1           → J 的 (0,2) = 1
# d2' = w2           → J 的 (1,3) = 1  
# w1' = -D1*w1 - K1*(d1-dm)  → R(2,2)=D1, J(2,0)=-K1... 
# 这不太好直接写成标准 pH 形式

# 用更简单的方式：差分模式 + 代数约束
# 动态：delta' = Omega, Omega' = -D*Omega - 2K*sin(delta) → 消去后无代数变量
# 这退化了...

# 让我构造一个真正有代数约束的 pH-DAE
# 简单的 RLC 网络：
# 动态：电感电流 iL' = (v1-v2)/L（2个电感）
# 代数：节点电压由 KCL 确定
#
# 最小例子：一个电感 + 一个电阻并联 + 一个电容
# 但这对电力系统不典型...

# 回到电力系统：用 3 节点系统
# 节点 1：发电机（动态：delta1, omega1）
# 节点 2：发电机（动态：delta2, omega2）
# 节点 3：负载节点（代数：功率平衡）

# pH-DAE 结构（线性化后）：
# 动态状态 xd = (delta1, delta2, omega1, omega2), nd=4
# 代数状态 xa = (theta3), na=1

# J_full (5x5 反对称)：
J_full = np.array([
    [0,  0,  1,  0,  0],   # delta1' ~ omega1
    [0,  0,  0,  1,  0],   # delta2' ~ omega2
    [-1, 0,  0,  0,  0],   # omega1' ~ -delta1 coupling
    [0, -1,  0,  0,  0],   # omega2' ~ -delta2 coupling
    [0,  0,  0,  0,  0],   # algebraic
])

# R_full (5x5 对称半正定)：
R_full = np.array([
    [0,   0,   0,   0,   0],
    [0,   0,   0,   0,   0],
    [0,   0,   D1,  0,   0],
    [0,   0,   0,   D2,  0],
    [0,   0,   0,   0,   0],  # 代数节点无耗散
])

# 加入网络耦合（通过代数节点）
K_val = 1.0
# omega1' 受 K*(delta1-theta3) 影响
J_full[2, 0] = -K_val  # -K*delta1 项
J_full[2, 4] = K_val   # +K*theta3 项
J_full[0, 2] = K_val   # 反对称
J_full[4, 2] = -K_val  # 反对称

# omega2' 受 K*(delta2-theta3) 影响  
J_full[3, 1] = -K_val
J_full[3, 4] = K_val
J_full[1, 3] = K_val
J_full[4, 3] = -K_val

# 代数方程：K*(delta1-theta3) + K*(delta2-theta3) = 0
# 即 K*delta1 + K*delta2 - 2K*theta3 = 0

# 检查 J 反对称
print(f"J skew-symmetric error: {np.max(np.abs(J_full + J_full.T)):.2e}")
print(f"R min eigenvalue: {np.min(eigvalsh(R_full)):.4f}")

result = check_ph_structure(J_full, R_full, 4, 1)
print(f"Index 1: {result['index_1']}")
if result['index_1']:
    print(f"Schur complement S:\n{result['S']}")
    print(f"J_eff (antisymmetric part):\n{result['J_eff']}")
    print(f"R_eff (symmetric part):\n{result['R_eff']}")
    print(f"R_eff min eigenvalue: {result['R_eff_min_eigval']:.6f}")
    print(f"pH structure preserved: {result['ph_preserved']}")

# ================================================================
# 案例 2：变化 K 看何时 index 1 失效
# ================================================================
print("\n" + "=" * 60)
print("Case 2: Varying network strength")
print("=" * 60)

for K_val in [10, 5, 2, 1, 0.5, 0.1, 0.01]:
    J_full_k = J_full.copy()
    J_full_k[2, 0] = -K_val; J_full_k[0, 2] = K_val
    J_full_k[2, 4] = K_val;  J_full_k[4, 2] = -K_val
    J_full_k[3, 1] = -K_val; J_full_k[1, 3] = K_val
    J_full_k[3, 4] = K_val;  J_full_k[4, 3] = -K_val
    
    result = check_ph_structure(J_full_k, R_full, 4, 1)
    if result['index_1']:
        print(f"K={K_val:6.2f}: R_eff_min={result['R_eff_min_eigval']:8.4f}, pH preserved={result['ph_preserved']}")
    else:
        print(f"K={K_val:6.2f}: NOT index 1!")

# ================================================================
# 案例 3：加入负阻尼（PLL 效应）看何时 R_eff >= 0 失效
# ================================================================
print("\n" + "=" * 60)
print("Case 3: Negative damping (PLL effect) on machine 2")
print("=" * 60)

for D2_val in [2, 1, 0.5, 0, -0.1, -0.5, -1, -2]:
    R_full_d = R_full.copy()
    R_full_d[3, 3] = D2_val
    
    # 全矩阵 R 还半正定吗？
    R_psd = np.min(eigvalsh(R_full_d)) >= -1e-10
    
    result = check_ph_structure(J_full, R_full_d, 4, 1)
    if result['index_1']:
        print(f"D2={D2_val:5.1f}: R_full PSD={R_psd}, R_eff_min={result['R_eff_min_eigval']:8.4f}, pH preserved={result['ph_preserved']}")
    else:
        print(f"D2={D2_val:5.1f}: NOT index 1!")

