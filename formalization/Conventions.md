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

---

## 13. 功率锁定 GFL-VSC 的 9 状态频率模式模型（freq_mode）

§12 的模型分析弱网 Hopf 分岔。本节是**另一个、独立的** GFL-VSC 模型：带**外环功率控制 + 摆动方程惯量**的电流控制变流器，研究其**慢频率模式**（grid-frequency mode）的特征值。`formalization/freq_mode/` 的全部 .kyx 证书以本节为单一真源。

所有量为实数。`e_k` = 标准基向量，`I_n` = n×n 单位阵。平衡点 = 向量场的零点；Jacobian = 在平衡点的一阶偏导矩阵。

### 13.1 状态（9 维）

`y = (i_d, i_q, ξ_dc, ξ_qc, η, θ_e, ξ_P, ξ_Q, dw) ∈ ℝ⁹`。

- 内部块 `z := (i_d, i_q, ξ_dc, ξ_qc, η, θ_e, ξ_P, ξ_Q) ∈ ℝ⁸`（坐标 1…8）
- 频率坐标 `dw ∈ ℝ`（坐标 9）= 电网频率偏移 `dw = wg − wn`
- 简写 `c := cos(θ_e)`, `s := sin(θ_e)`, `wg := wn + dw`

| 变量 | 含义 |
|------|------|
| `i_d, i_q` | 电流 dq |
| `ξ_dc, ξ_qc` | 电流环 PI 积分态 |
| `η` | PLL 积分态 |
| `θ_e` | PLL 相位误差 |
| `ξ_P, ξ_Q` | 有功/无功外环 PI 积分态 |
| `dw` | 电网频率偏移 |

### 13.2 参数（假设）

- (P1) `Lf, Lg, Rf, Rg > 0`；`Ltot := Lf+Lg`，`Rtot := Rf+Rg`，`g := (Lf·Rg − Rf·Lg)/Ltot`（实，符号不限）
- (P2) `wn > 0`, `Vg > 0`
- (P3) `Kpi, Kii > 0`（电流环）；`Kp_pll, Ki_pll > 0`（PLL）；`Kp_P, Ki_P, Kp_Q, Ki_Q > 0`（外环）；设定点 `P_ref, Q_ref ∈ ℝ`，`P_ref > 0`
- (P4) 摆动：`H > 0`（惯量），`D > 0`（阻尼），`Sn > 0`；`κ := wn/(2·H·Sn) > 0`，`b := D/(2·H) > 0`

### 13.3 代数定义（显式）

```
P_meas  := 1.5·Vg·i_d
Q_meas  := −1.5·Vg·i_q
e_P     := P_ref − P_meas
e_Q     := Q_ref − Q_meas
i_d_ref := Kp_P·e_P + Ki_P·ξ_P
i_q_ref := −(Kp_Q·e_Q + Ki_Q·ξ_Q)
i_dc    := c·i_d − s·i_q
i_qc    := s·i_d + c·i_q
e_d     := i_d_ref − i_dc
e_q     := i_q_ref − i_qc
K_d     := Kpi·e_d + Kii·ξ_dc − wn·Lf·i_qc + (Lf/Ltot)·c·Vg + g·i_dc
K_q     := Kpi·e_q + Kii·ξ_qc + wn·Lf·i_dc + (Lf/Ltot)·s·Vg + g·i_qc
u_dc    := (Ltot/Lf)·K_d
u_qc    := (Ltot/Lf)·K_q
u_d     := c·u_dc + s·u_qc
u_q     := −s·u_dc + c·u_qc
v_d     := (Lg/Ltot)·u_d + (Lf/Ltot)·Vg + g·i_d
v_q     := (Lg/Ltot)·u_q + g·i_q
v_cqc   := s·v_d + c·v_q
```

### 13.4 向量场

内部块 `F_inner : ℝ⁹ → ℝ⁸`：

```
F1 = (u_d − Vg − Rtot·i_d + Ltot·wg·i_q)/Ltot    = d(i_d)/dt
F2 = (u_q       − Rtot·i_q − Ltot·wg·i_d)/Ltot    = d(i_q)/dt
F3 = e_d                                          = d(ξ_dc)/dt
F4 = e_q                                          = d(ξ_qc)/dt
F5 = v_cqc                                        = d(η)/dt
F6 = −Kp_pll·v_cqc − Ki_pll·η − dw                = d(θ_e)/dt
F7 = e_P                                          = d(ξ_P)/dt
F8 = e_Q                                          = d(ξ_Q)/dt
```

**结构事实**（§13.4–13.3 按定义可查）：`dw` 只通过 `∂F1/∂dw = i_q`、`∂F2/∂dw = −i_d`、`∂F6/∂dw = −1` 进入 `F_inner`，其余 `∂Fk/∂dw = 0 (k∈{3,4,5,7,8})`。即
`c := ∂F_inner/∂dw = i_q·e₁ − i_d·e₂ − e₆ ∈ ℝ⁸`。

两个变体的第 9 式：
- **Variant U（未锚定）**：`F9_U := 0`，场 `f_U(y) := (F_inner(y), 0)`
- **Variant S（摆动锚定）**：`F9_S := κ·e_P − b·dw`，场 `f_S(y) := (F_inner(y), F9_S)`

适定性假设：(W1) 平衡点 `y*` 存在；(W2) 内部 Jacobian `A := ∂F_inner/∂z(y*) ∈ ℝ⁸ˣ⁸` 可逆（关心情形下 Hurwitz）；(W3) Variant U 有 C¹ 平衡分支 `d ↦ z*(d)`，`F_inner(z*(d), d) ≡ 0`。

### 13.5 Lemma 0（功率锁定）+ 推论

- **Lemma 0**：任一平衡点处 `e_P = 0`（因 `F7 = e_P = 0`），故 `P_meas = P_ref`，`i_d = P_ref/(1.5·Vg)`。
- **Cor 0a（同步系数为零）**：沿 `z*(d)`，`i_d*(d) = P_ref/(1.5·Vg)` 与 `d` 无关，故
  `K := d/dd[P_meas(z*(d))] = 1.5·Vg·d(i_d*)/dd = 0`（精确）。
- **Cor 0b**：`e_Q=0 ⟹ i_q=−Q_ref/(1.5·Vg)`；`e_d=e_q=0`；`v_cqc=0`；`F6=0 ⟹ η=−dw/Ki_pll`；Variant S 下 `F9_S=0 ∧ e_P=0 ⟹ b·dw=0 ⟹ dw*=0`。

### 13.6 Jacobian 块结构（在 y*）

```
J = [ A    c  ]      A ∈ ℝ⁸ˣ⁸,  c ∈ ℝ⁸,  ρ ∈ ℝ⁸,  j99 ∈ ℝ
    [ ρᵀ   j99 ]
```

`A := ∂F_inner/∂z`，`c := ∂F_inner/∂dw = i_q*·e₁ − i_d*·e₂ − e₆`，`ρᵀ := ∂F9/∂z`，`j99 := ∂F9/∂dw`。
- Variant U：`ρᵀ = 0ᵀ`，`j99 = 0`
- Variant S：`ρᵀ = −1.5·κ·Vg·e₁ᵀ`，`j99 = −b`

**行-7 关键事实**（功率锁定的矩阵形式）：`e₆ᵀA = ∂F7/∂z = −1.5·Vg·e₁ᵀ`，`c[6] = ∂F7/∂dw = 0`。

### 13.7 定理（freq_mode 证书所证）

- **Thm A（Variant U 零特征值）**：`e₉ᵀJ_U = 0ᵀ`，故 `0 ∈ spec(J_U)`，`e₉` 左特征向量。
- **Thm B（Variant S 慢特征值）**：约化（慢流形 `F_inner=0`）动力学 `dw' = κ(P_ref − P_meas(z*(dw))) − b·dw = −b·dw`（因 Cor 0a：P_meas≡P_ref），故 `λ_slow = −b = −D/(2H)`（约化模型精确）。全系统 Schur：`λ = j99 − ρᵀ(A−λI)⁻¹c`，O(1) 项 `ρᵀA⁻¹c = κ·K = 0`，故 `λ_slow = −b + O(b²)`（全 9×9 仅 O(b²)，约化才精确）。
- **Thm C（振荡需角→功率耦合）**：增广角状态 `δ'=dw`、恢复项 `−β·Ks·δ`（`β := wn/(2H) > 0`），约化 `(δ,dw)` 子系统特征多项式 `λ² + b·λ + β·Ks`：
  - (C1) `Ks=0 ⟹` 特征值 `{0, −b}`（实，回收 Thm A/B）
  - (C2) `Ks>0 ⟹ λ = (−b ± √(b²−4βKs))/2`；复（振荡）当且仅当 `β·Ks > b²/4`，实部 `−b/2`，`ω_osc = √(β·Ks − b²/4)`

### 13.8 数值锚点（SCR=1 工况；H=5, D=1, fn=50）

- `i_d* = 79.9307179224` A，对 `dw∈{0,5,20,50,100}` 十位一致 ⟹ `K=0`（Lemma 0/Cor 0a）
- Variant U：20 个工况各恰好一个零特征值（机器精度）（Thm A）
- Variant S：`λ_slow = −0.099968` vs `−D/(2H)=−0.1`（差 3.2e−5，FD-Jacobian 噪声 + O(b²)）；Schur 项 `ρᵀA⁻¹c = 2.9e−19`（Thm B）
- `−D/(2H)` 跨 `(H,D)∈{(2,.5),(5,.5),(5,1),(5,2),(10,1),(3,.3),(8,4)}` 均 `≤1e−4`
- Thm C 起振：`Ks=0 → {0,−b}` 实；`Ks∈{0.01,0.05,0.2,1} → 0.089,0.199,0.399,0.892 Hz`，匹配 `ω_osc/2π`（`β=wn/(2H)`）

### 13.9 dL 编码约定（重要 — KeYmaera X 证书与本节的差异）

`freq_mode/kyx/*.kyx` 在 KeYmaera X 中证明时遵循以下编码约定，与上面数学形式有**有意的差异**，必须知道：

1. **标识符无下划线**：KeYmaera X 解析器拒绝 `P_ref`、`i_d` 这类"下划线+字母"名。证书中用 `Pref`=P_ref，`id`=i_d，`iq`=i_q，`Kppll`=Kp_pll，`Kipll`=Ki_pll 等。
2. **无除法**：KeYmaera X 的 Z3 后端在除法上失败（`1/x*y=y/x` 返 SAT）。所有 Problem 写成乘法形式：`b=D/(2H)` 编码为 `2*H*b=D`；`βKs>b²/4` 编码为 `4βKs>b²`；`Re=−b/2` 编码为 `2r=−b`。
3. **矩阵事实标量化**：dL 不是线性代数库，无矩阵/特征向量/求逆原生对象。`e₉ᵀJ_U=0`、`ρᵀA⁻¹c=0` 等在 .kyx 中编码为它们**归约到的标量代数恒等式**（如把"`A·u=c` 第 7 分量读数 `(−1.5Vg)·U1=c6`"作为前提）。这些前提**本身**（完整 9×9 Jacobian 的第 7 行 = −1.5Vg·e₁ᵀ 等）在 `freq_mode/verify_freq_mode.py`（sympy 构造完整符号 Jacobian）验证，**不在 dL 内**。
4. **必须用 KeYmaera X 自带的 z3**（bundled v4.8.9），不要用 `-z3path` 指向外部 z3——外部 z3 4.16.0 会让启动期公理推导无限挂起。
5. **约化 vs 全系统**：Thm B 的 .kyx 证的是**约化模型**精确 `−D/(2H)` 与 leading-order；全 9×9 的 O(b²) 修正只在 sympy 数值确认，未声称严格精确。

