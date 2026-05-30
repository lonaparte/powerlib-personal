# GFL 弱网 Hopf 分岔的数值证书

> 2026.05 | 跟网变流器（GFL）10 状态模型的 Hopf 分岔判据（subcritical / supercritical）

## 这是什么

Summary.md 把"PLL 的具体动态（而非等效负阻尼 D₂<0）"列为**未做**。本目录就是填这个洞：用一个**具体的 10 状态 GFL 变流器模型**（含 PLL、LC 滤波、电流环、刚性母线后的 RL 电网），研究它在**弱网**下失稳的 Hopf 分岔，并判定分岔类型。

- 模型记号、方程、平衡点、参数：见 `formalization/Conventions.md` §12（单一真源）。
- 核心量是**第一 Lyapunov 系数 l₁**（在 Hopf 点）：
  - **l₁ > 0：subcritical（硬失稳）** —— 临界点之前有限扰动即可触发大幅振荡，带迟滞。这是子同步振荡（SSCI）最危险的场景。
  - **l₁ < 0：supercritical（软失稳）** —— 临界点之后渐生小幅稳定极限环。
  - **l₁ = 0：Bautin 点（广义 Hopf）** —— 硬↔软的边界。

## 方法

- **严格区间证书**（`ivcert/ivparam/ivgrid/ivlocus`）：mpmath 区间算术（定向舍入）。
  - 平衡点闭式求解（二次型）。
  - 临界特征对 (iω, q) 与左特征对 p 用 **Krawczyk / 区间-Newton** 在 bordered 系统上**验证存在唯一**（对整个参数盒成立）。
  - l₁ 投影公式（Kuznetsov）全程区间求值；线性方程组解用区间收缩（Neumann）包络。
  - **平衡（balancing）**降条件数：l₁ 在状态缩放 x=Dx̃ 下不变，工作于 D⁻¹AD 坐标使 cond 从 4.6e7 降到 6.1e3。
- **浮点侦察**（`sweep/bautin`）：同一套 l₁ 管线的浮点版，快，用于沿轨迹/控制平面扫符号、定位 Bautin 曲线。符号已对区间法逐点校验。

## 脚本与结果

运行：`cd formalization/numerical && python3 <脚本>`（需 numpy/scipy/sympy/mpmath）。
名义工况：S_n=100kVA, V_n=380V, f=50Hz；PLL (Kp,Ki)=(0.30,150)；电网 X/R=10；i_dref=80A。
临界点 SCR_H≈0.9051（|Zg|≈1.595Ω, f_osc≈40.0Hz）。

| 脚本 | 做什么 | 关键结果 | 严格性 |
|------|--------|----------|--------|
| `ivcert.py` | 名义工况单点 Hopf 的 l₁ | l₁∈[2.371e-6, 2.371e-6] >0 → **subcritical** | 区间严格 |
| `ivparam.py` | **控制增益盒** (Kp,Ki,SCR) 上 l₁>0 | Kp=0.30±1e-5, Ki=150±2e-3, SCR=SCR_H±1e-5：l₁∈[1.17e-4, 3.22e-4] >0 | 区间严格 |
| `ivgrid.py` | **电网阻抗盒** (SCR, X/R) 上 l₁>0 | SCR∈[SCR_H±8e-6], X/R∈[10±8e-5]：l₁∈[7.85e-5, 3.61e-4] >0 | 区间严格 |
| `ivlocus.py` | **沿 Hopf 轨迹 B&B**：连续区间上 ∀ X/R | 40 个无缝瓦片 → l₁>0 对 **∀ X/R∈[9.996,10.004]**（瓦片半宽上限≈1e-4） | 区间严格 |
| `sweep.py` | 浮点 l₁ 沿整条弱网 Hopf 轨迹 | X/R∈[2,30] 全程 l₁>0（1.4e-6~2.6e-6），无变号 | 浮点证据 |
| `bautin.py` | 控制平面 (Kp,Ki) 的 Bautin 边界 | Kp\*(Ki): (60,0.283)(100,0.341)(150,**0.404**)(400,0.622)；名义 Kp=0.30 在**硬区** | 浮点证据 |

`bautin.py` 复用 `sweep.py`（`from sweep import ...`），需放同目录。

## 严格性等级（务必区分）

- **区间严格**（ivcert/ivparam/ivgrid/ivlocus）：经验证的区间算术机器证明，对盒内**整个连续统**成立。注意：这是**区间算术**意义的严格，不是 KeYmaera X 的 .kyx 证明；尚未落成 dL/Lean。
- **浮点证据**（sweep/bautin）：强数值证据，非证明。l₁ 的**符号**已对区间法校验（见下），但 l₁=0 的 Bautin 点是 codim-2，其**精确位置未经区间认证**，Kp\* 取 ~4 位有效数字为宜。

## 归一化约定（重要）

l₁ 的**量级依赖归一化/坐标约定**：
- 非平衡坐标（ivcert、sweep）：名义点 l₁≈2.37e-6。
- 平衡坐标（ivparam/ivgrid/ivlocus）：名义点 l₁≈2.2e-4。
- 二者差 ~100×，因为 Hermitian 归一化 ⟨q,q⟩=1 在不同坐标下不同。

**l₁ 的符号是坐标不变量，是物理量**（决定 sub/supercritical）；量级只是约定，不要跨脚本直接比大小。

## 交叉校验

- `sweep.py` 的 CHECK：平衡坐标浮点 l₁ = 2.195e-4，落在 `ivgrid/ivparam` 区间盒 [1.7e-4, 3.1e-4] 内 ✓。
- 修复过一个 bug：实矩阵中 λ 的左特征向量应取 Aᵀ 在 **conj(λ)** 处的向量；早期误取 λ 处，导致 ⟨p,q⟩≈0、l₁ 量级炸到 1e10。修正后符号/量级与区间法一致。
- Hopf 频率 f_osc≈40Hz、SCR_H≈0.905 三套脚本一致。

## 已知局限 / 下一步

1. **区间盒/瓦片偏小**：受 bordered 特征对 Krawczyk 条件数限制（X/R 半宽≈1e-4）。覆盖全程 [2,30] 需 ~14 万瓦片——算力问题（完全并行），非方法问题。改进方向：affine 算术 / 更优预条件。
2. **Bautin 点未区间认证**：可对 l₁=0 做区间求根 + 横截性验证。
3. **闭式/符号证书**：全 10 阶 l₁ 无闭式；可中心流形降阶后用 SOS/QE 求 {l₁>0} 的精确半代数区域（需对全模型校验）。
4. **未落 .kyx**：本目录是数值层；与 KeYmaera X/Lean 的形式层衔接尚未做。
