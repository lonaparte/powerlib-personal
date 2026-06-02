# GFL-VSC 风险机制的参数化证书(R1 / R2 / R3)

> 三类结构性失稳机制的参数化分析:**R1** 弱网电气模 onset、**R2** 同步平衡消失、
> **R3** 同步吸引域 vs PLL 阻尼。`kyx/` 是 KeYmaera X 5.1.2(自带 z3)证书,
> `numerical/` 是支撑数值,`results/` 是证明日志。

## 状态总览

| 文件 | entry | KeYmaera X | 内容 |
|------|-------|-----------|------|
| `kyx/R1_routh.kyx` | 3 | proved | Σ₁ Routh onset 签名 / 虚轴穿越 / 横截性符号 |
| `kyx/R2_fold.kyx` | 4 | proved | fold 根计数 / node-saddle / 经典极限 |
| `kyx/R2_sigma2_symbolic.kyx` | 2 | proved | **Σ₂ 全 6 参数闭式** Φ(p) |
| `kyx/R3note_l1_not_criterion.kyx` | 2 | proved | sign l₁ **不是**失同步判据 |
| `kyx/R3a_energy_barrier.kyx` | 3 | proved | **能量屏障** Vdot=−b·dw²(替代 SOS) |
| `kyx/R3_basin.kyx` | 4 | proved | 屏障不变性 / 鞍点排除 / c* 单调 / 阈值 Σ₃ |
| **合计** | **18** | **全 proved** | |

复现:`cd kyx && java -jar <keymaerax.jar> -prove <file>.kyx -tool z3`
(**必须用 KeYmaera X 自带 z3,不要 `-z3path` 外部 z3** — 外部会挂启动期公理推导);
`cd numerical && python3 risk_numerical.py`(需 numpy/sympy/scipy)。

## R1 — 弱网使电气模过虚轴(onset)

- **机制**:变流器-滤波器-线路阻抗谐振失阻尼,**非** PLL 分岔。
- **Σ₁ 交付**:8 状态 PLL-冻结电气子系统 A_e 的 Routh 行列式 **Δ₇(g)=0**(g=1/Lg),
  数值上是 **degree-13 多项式**,正实根隔离出 onset。
- **数值确认**(`risk_numerical.py`):onset 两点 Re λ≈0(−6e-13、+1.6e-12,真虚轴穿越);
  物理 onset `Lg*=0.00484 H` 处 **ω₀=75.15 rad/s(12 Hz)≠ ω_LCL=3473 rad/s(553 Hz)**;
  横截性 **dRe λ/dLg=+644>0**(弱网入 RHP)。
- **证书** `R1_routh.kyx`:Routh onset 签名(Δ₇=0 边界 + Δ₈=a₈Δ₇)、虚轴穿越存在性、
  横截性符号(先实测 +644 再写,改掉过一处一开始写反的符号)。

## R2 — 同步平衡消失(鞍结/折叠)

- **机制**:不平衡力矩 M=id_ref·wn·Lg+iq_ref·Rg 超过 Vg ⟹ 无同步平衡 ⟹ θ 无界失同步。
- **Σ₂ 全符号闭式**(标量问题,不超时,与 R1 的 8×8 不同):
  `Φ(p) = Lg²·id_ref²·wn² + 2·Lg·Rg·id_ref·iq_ref·wn + Rg²·iq_ref² − Vg²`,
  Φ<0 两平衡(node+saddle),Φ>0 零平衡;经典极限退化到 Wu 边界 |M|=Vg。
- **证书** `R2_fold.kyx`(4)+ `R2_sigma2_symbolic.kyx`(2)。

## R3 — 同步吸引域 vs PLL 阻尼

- **R3-pre(边界类型)**:吸引域边界 = **R2 鞍点的稳定流形**(数值 V_saddle=63 ≫ c*),
  不是极限环、不是同宿。
- **R3a(屏障证书)**:用**倾斜摆能量** `V=½dw²+K(cosδ*−cosδ)−Pm(δ−δ*)`,实算
  **Vdot=−b·dw² 精确**(误差 7e-17);LaSalle ⟹ {V<c*} 内估吸引域,c*=V(saddle)。
  这是精确多项式-三角恒等式,**不需要 SOS 求解器**,直接 QE 证。`R3a_energy_barrier.kyx`(3)。
- **R3b(单调性)**:c*(PLL 阻尼) 数值单调递增(0.05→2.41 … 0.40→5.18);
  阈值面 Σ₃={c*=0}。`R3_basin.kyx`(4)。
- **R3-note(否定结论)**:**sign l₁ 不是失同步判据**。数值开集:固定控制 Kp=0.8,Ki=150
  (l₁<0,Bautin 读法"安全"),SCR=0.40、id_ref∈{120,160} 时 **l₁<0 且 |M|/Vg>1**
  (已过 fold,全局失同步)。l₁ 管局部 Hopf(Σ₁),失同步管 fold(Σ₂),代数独立。
  `R3note_l1_not_criterion.kyx`(2)。

## 诚实边界(务必知道)

1. **dL/QE 不是线性代数/分析包**。证书证的是各机制**归约到的代数命题**(Routh 签名、
   fold 不等式、能量恒等式、单调蕴含),不是完整 8×8 符号谱或全局吸引域。完整 Δ₇(g)
   deg-13、特征值、Schur 等在 `numerical/` 的 sympy/numpy 层。
2. **Σ₁ 没有全符号闭式**:8×8 符号行列式即使部分符号也重,全 8 参数实测多次**超时**——
   这是 CAS 在高维符号行列式上的真实天花板,不是方法问题。交付的是沿分岔方向(Lg)的
   显式 Δ₇(g) 多项式面。Σ₂(标量)则做到了全符号闭式。
3. **R3a 是约化同步核 + 内估**,不是 10D 全状态严格吸引域。
   - **10D 全非线性 SOS 没做到**:`SumOfSquares`/picos 装不上;手搭 cvxpy SOS 对同步核
     **infeasible**(查实因:误用的交叉项 V 根本不是 Lyapunov 函数,1424 处 Vdot>0,
     SOS 正确拒绝证伪)。改用能量法绕过,得到的是**约化核**的严格屏障。
   - 10D **线性** Lyapunov 盆需 balancing 预处理才解得动(裸 SCS 在 cond=2.2e5 下失败);
     这条没单独落成证书,仅记录于此。
4. **R1 横截性 / R3b 单调性**的证书证的是**符号代数蕴含**(正×正=正、仿射单调),
   其中的数值斜率(+644、k>0)来自数值扫描,是前提不是结论的一部分,已在证书注释标明。
5. 这些是**参数化失稳机制的代数骨架**,适合作工程稳定边界的形式化锚点;**不**等价于
   "已严格证明该 10D 系统在某区域全局稳定"。

## 关于 l₁(与 `numerical/` 的关系)

R3-note 用到的 l₁(第一 Lyapunov 系数)来自 `formalization/numerical/sweep.py` 的弱网
Hopf 管线(另一条线)。R3-note 的要点正是:**那条线的 l₁ 符号不能用来判全局失同步** —
这也是为什么本目录的 R3 改用 R2-fold + 能量屏障而非 Bautin/l₁ 框架。
