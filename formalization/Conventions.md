# 形式化约定

所有 .kyx 文件、Summary.md、数值脚本必须遵循以下约定。引入新符号或新约定时更新此文件。

---

## 1. 状态变量

| 变量 | 含义 | 单位/范围 |
|------|------|----------|
| `d1`, `d2` | 机器 1、2 的转子角度 | rad |
| `w1`, `w2` | 机器 1、2 的角频率偏差 | rad/s |
| `s` | sin(d1−d2) 的辅助变量 | [−1, 1] |
| `c` | cos(d1−d2) 的辅助变量 | [−1, 1] |
| `t` | 时间（渐近稳定性证明中使用） | s |
| `v0` | V 的初始值（渐近稳定性证明中冻结为常数，v0'=0） | — |
| `h0` | H 的初始值（守恒/增长证明中冻结为常数，h0'=0） | — |
| `u0` | 守恒量的初始值（K=0 必要性证明中使用） | — |

相对角度 δ = d1 − d2 不作为独立变量出现。d1、d2 各自积分 w1、w2。

## 2. sin/cos 编码

KeYmaera X 没有内置 sin/cos 函数。用辅助变量 s、c 和附加 ODE 编码：

```
s' = c*(w1 - w2)    /* d/dt sin(d1-d2) = cos(d1-d2)·(d1'-d2') */
c' = -s*(w1 - w2)   /* d/dt cos(d1-d2) = -sin(d1-d2)·(d1'-d2') */
```

不变量 `s^2 + c^2 = 1` 在以下位置维护：
- 作为前提条件（Problem 的初始条件）
- 作为演化域约束（`& s^2 + c^2 = 1`，用于需要它的证明）

dI 可以自动验证 s²+c²=1 是不变量（Lie 导数 = 2s·s'+2c·c' = 2s·c·(w1-w2)+2c·(−s)·(w1-w2) = 0）。

## 3. 系统方程

两机非线性系统（消去代数变量后的约化 ODE）：

```
d1' = w1
d2' = w2
w1' = -D1*w1 - K*s       /* 阻尼 + 耦合 */
w2' = -D2*w2 + K*s       /* 阻尼 + 耦合（符号相反） */
s'  = c*(w1 - w2)
c'  = -s*(w1 - w2)
```

耦合系数是 **K**（不是 K/2）。所有 .kyx 文件和 Summary.md 使用此约定。

## 4. 参数

| 参数 | 含义 | 符号约定 |
|------|------|---------|
| `D1` | 机器 1 阻尼系数 | D1 > 0：无源（耗散） |
| `D2` | 机器 2 阻尼系数 | D2 > 0：无源；D2 < 0：非无源（跟网/PLL 等效负阻尼） |
| `K` | 耦合系数（同步力矩） | K > 0 |
| `J1`, `J2` | 惯性常数 | `parametric.kyx` 中为符号参数；其余文件归一化为 J1=J2=1 |

惯性归一化 J1=J2=1 后，系统方程中 D1/J1 简化为 D1，K/J1 简化为 K。`parametric.kyx` 是唯一保留 J 符号参数的文件。

## 5. Hamiltonian

$$H = \omega_1^2 + \omega_2^2 + 2K(1 - \cos\delta)$$

KeYmaera X 中写为 `w1^2 + w2^2 + 2*K*(1 - c)`。

**不含 1/2 系数**。这是物理 Hamiltonian H_phys = (1/2)(ω₁²+ω₂²)+K(1−cosδ) 的 2 倍。选择此约定是因为 .kyx 文件中避免了分数。

能量平衡：
$$\dot{H} = -2D_1\omega_1^2 - 2D_2\omega_2^2$$

因子 2 来自 H 不含 1/2。Lean 4 的 `PHEnergyBalance.lean` 证明的是 H_phys 惯例下的等式（无因子 2）。

## 6. 平衡点与鞍点

| 点 | 状态 (w1,w2,s,c) | H 值 | 稳定性 |
|----|------------------|------|--------|
| 稳定平衡 | (0, 0, 0, 1) | 0 | D1,D2>0 时渐近稳定 |
| 鞍点 | (0, 0, 0, −1) | 4K | 不稳定（δ=π） |

稳定域（保守系统 D=0）：H < 4K。对应 δ 不超过 π（不越过鞍点）。

## 7. pH 结构

标准形式 ẋ = (J−R)∇H_phys，其中：

$$J = \begin{pmatrix} 0 & 1 & -1 \\ -1 & 0 & 0 \\ 1 & 0 & 0 \end{pmatrix}, \quad R = \begin{pmatrix} 0 & 0 & 0 \\ 0 & D_1 & 0 \\ 0 & 0 & D_2 \end{pmatrix}$$

状态 x = (δ, ω₁, ω₂)。J 反对称（J' = −J）→ ∇H'·J·∇H = 0（sin 项抵消）。R 对角半正定（D1,D2≥0 时）→ ∇H'·R·∇H ≥ 0（耗散）。

D2 < 0 时 R 不再半正定 → pH 结构的无源性失效 → H 不是 Lyapunov 函数。

## 8. 约化 ODE 与 DAE 的关系

当前所有分析都在**约化 ODE** 上（消去了代数变量后的系统）。原始 pH-DAE 形式为：

$$E\dot{x} = (J_{full} - R_{full})Q x + Bu$$

其中 E 可能奇异（代数约束）。消去代数变量后得到约化 ODE，Schur 补给出有效的 J_eff 和 R_eff。

**尚未做**：直接在 DAE 层面分析（不消去代数变量）。

## 9. 修正 Hamiltonian

渐近稳定性证明中使用修正 Hamiltonian：

$$V = H + a(\omega_1 - \omega_2)\sin\delta = \omega_1^2 + \omega_2^2 + 2K(1-c) + a(w_1-w_2)s$$

已证实例：
- K=D1=D2=1：a = 1/4，时间界 C = 12
- D1=1, D2=5, K=2：a = 1/4，时间界 C = 48

对一般 D1,D2,K > 0，a 和 C 的选取依赖参数，尚未找到统一的显式 witness。

## 10. 稳定性定义的 dL 编码

### Lyapunov 稳定性（安全性）

```
\forall eps (eps > 0 ->
  \exists delta (delta > 0 &
    \forall x (|x| < delta -> [{ODE}] |x| < eps)))
```

用 H 或分量 (w1²,w2²,1−c) 作为度量。对应 dL 的 box 模态 [{ODE}]。

### 渐近稳定性（活性 + 安全性）

编码为有限时间收敛：V 在有限时间内降到任意 target 以下。

```
\forall target (target > 0 & target < 1/2 ->
  (V0 > 0 & V0 < 1 & t = 0 ->
   [{ODE & domain & V >= target}]
   t < C*V0/target))
```

系统在时间 C·V0/target 内**必须**离开域 {V ≥ target}。结合 V<1→c>0（出口只能是 V<target），得到渐近收敛。

### 不稳定性（菱形模态）

```
\exists x (|x| < eps & <{ODE}> |x| > 2*eps)
```

菱形 `<{ODE}>` 表示存在一条轨迹到达目标状态。用于证明不稳定。

## 11. Routh-Hurwitz 边界

线性化系统 A 的特征多项式：

$$s^3 + (D_1+D_2)s^2 + (D_1 D_2 + 2K)s + K(D_1+D_2) = 0$$

Routh 判据给出稳定充要条件：
1. D₁ + D₂ > 0（即 |D₂| < D₁）
2. D₁D₂ + K > 0（即 |D₂| < K/D₁）

合并：**|D₂| < min(D₁, K/D₁)**。

注意：此边界对应耦合系数 K（本项目约定）。若使用 K/2 耦合约定，边界变为 |D₂| < min(D₁, K/(2D₁))。

---

## 12. GFL 跟网变流器 10 状态模型（PLL 具体动态）

§4 中 D₂<0 是"PLL 等效负阻尼"的抽象。本节给出其**具体控制器结构**：一个含 PLL、LC 滤波、电流环、经 RL 电网接刚性母线的跟网变流器。数值脚本见 `numerical/`。

### 12.1 状态变量（10 维）

| 变量 | 含义 |
|------|------|
| `i_d`, `i_q` | 变流器侧电流 dq |
| `v_cd`, `v_cq` | 滤波电容电压 dq |
| `i_gd`, `i_gq` | 电网侧电流 dq |
| `xdc`, `xqc` | 电流 PI 控制器积分态 |
| `eta` | PLL 积分态 |
| `th` | PLL 相位（相对额定的角度误差） |

dq 坐标随 PLL 旋转：`wpll = wn + Kp·v_cq + Ki·eta`（PLL 锁 v_cq→0）。

### 12.2 固定装置参数（归一化标幺前的取值）

`Cf=1e-4, Lf=1e-3, Rf=0.1`（LC 滤波 + 阻尼）；`Kpi=1.26, Kii=126`（电流环 PI）；`Kad=2`（有源阻尼）；`idr=80, iqr=0`（电流指令 A）。
`wn=2π·50`；`Vg=380·√(2/3)`。

### 12.3 方程（ẋ = f(x)）

```
i_d'  = (Kpi*(idr-i_d) + Kii*xdc - Kad*(i_d-i_gd) - Rf*i_d)/Lf
i_q'  = (Kpi*(iqr-i_q) + Kii*xqc - Kad*(i_q-i_gq) - Rf*i_q)/Lf
v_cd' = (i_d-i_gd)/Cf + wpll*v_cq
v_cq' = (i_q-i_gq)/Cf - wpll*v_cd
i_gd' = (v_cd - Vg*cos(th) - Rg*i_gd + wpll*Lg*i_gq)/Lg
i_gq' = (v_cq + Vg*sin(th) - Rg*i_gq - wpll*Lg*i_gd)/Lg
xdc'  = idr - i_d
xqc'  = iqr - i_q
eta'  = v_cq
th'   = Kp*v_cq + Ki*eta            (= wpll - wn)
```

### 12.4 控制与电网参数

| 参数 | 含义 | 名义值 |
|------|------|--------|
| `Kp` (=Kp_pll) | PLL 比例增益 | 0.30 |
| `Ki` (=Ki_pll) | PLL 积分增益 | 150 |
| `SCR` | 短路比（电网强度，**分岔参数**） | 临界 SCR_H≈0.9051 |
| `X/R` | 电网阻抗角 | 10 |

电网阻抗由 (SCR, X/R) 决定：`|Zg| = 380²/(1e5·SCR)`，`Rg = |Zg|/√(1+(X/R)²)`，`Lg = |Zg|·(X/R)/(√(1+(X/R)²)·wn)`。SCR 越小 = 电网越弱 = |Zg| 越大。

### 12.5 平衡点

`i_d=idr, i_q=iqr, v_cq=0, i_gd=idr, eta=0`；`i_gq=iqr-wn·Cf·vcd`；`xdc=Rf·idr/Kii`；`xqc=(Kad·(iqr-i_gq)+Rf·iqr)/Kii`。
设 `al=1-wn²·Lg·Cf, be=Rg·wn·Cf, K1=Rg·idr-wn·Lg·iqr, K2=Rg·iqr+wn·Lg·idr`，则
`cos(th)=(al·vcd-K1)/Vg`，`sin(th)=(K2-be·vcd)/Vg`，`vcd` 由 `cos²+sin²=1` 化出的二次方程 `(al²+be²)vcd² - 2(al·K1+be·K2)vcd + (K1²+K2²-Vg²)=0` 取正根。判别式<0 ⇒ 无平衡点（电压崩溃 / saddle-node）。

### 12.6 分岔分析量

- **A** = f 在平衡点的 Jacobian（10×10）。线性稳定 ⇔ max Re(eig A) < 0。
- **弱网 Hopf**：固定其余参数、减小 SCR（电网变弱），一对共轭特征值在 SCR=SCR_H 处穿过虚轴；`ω=Im(λ)`（名义下 f_osc≈40Hz）。
- **第一 Lyapunov 系数 l₁**（Kuznetsov 投影公式，在 Hopf 点）：
  - `l₁>0` ⇒ **subcritical（硬失稳，危险）**；`l₁<0` ⇒ **supercritical（软失稳）**；`l₁=0` ⇒ **Bautin 点**。
  - **l₁ 的符号是坐标不变量（物理量）；量级依赖归一化约定**（平衡 vs 非平衡坐标差 ~100×），不可跨脚本比大小。
- **Bautin 曲线** `Kp*(Ki)`：控制平面内 l₁=0 的边界，硬↔软分界（见 `numerical/bautin.py`）。

