# Powerlib

Lean 4 中的小信号稳定性与周期参数调制证明。当前开发分支为
`codex/parametric-theory-proofs`；`archive/` 中的原有草稿不参与导入或构建。

**当前还没有完成从原非线性系统六组结构假设到全部结论的端到端证明。**
已有平均模型的精确谱判据，以及模态响应、线性化、正规形和有限时间估计的证明组件。
组件各自的额外前提写在 Lean 定理中；不能把这些组件解释为原始假设已经推出全部前提。

## 文件与证明边界

`Powerlib.lean` 仅作为总导入入口。各文件按可独立使用的数学任务拆分：

| 文件 | 证明内容 | 使用边界 |
|---|---|---|
| `Powerlib/SmallSignal.lean` | 线性轨迹、指数稳定、实际特征多项式与 Hurwitz 定义；原有谱稳定公理及推论 | 矩阵已给定；谱性质到时域指数稳定仍使用一个显式领域公理 |
| `Powerlib/Parametric/Coupling.lean` | 模态 resolvent 的解与唯一性、基底无关性、双线性耦合展开、模态缩放下耦合模不变；谐波解及相位匹配 | 给定完整特征基底和相应导数所表示的线性／双线性映射 |
| `Powerlib/Parametric/Envelope.lean` | 二阶实矩阵与复幅值方程对应、两个特征值、相位旋转、谱判据、指标与有限阈值、紧参数集上的最优指标 | 给定二阶平均模型；最优值存在需要非空紧集和连续性，不据此断言原周期系统的长期增长率 |
| `Powerlib/Parametric/NormalForm.lean` | 显式求解非共振 Fourier 同调方程、周期性、近恒等变换、准确保留二阶余项、逆的存在与范数界 | 非共振条件仅施加于实际移除的通道；原 Jacobian 的余项仍须提供 |
| `Powerlib/Parametric/ModalBounds.lean` | Hurwitz 对角算子在模态 Euclidean 空间中的耗散性，以及加入小扰动后的单边界 | 范数必须与采用的模态坐标和内积一致 |
| `Powerlib/Parametric/ModalOperator.lean` | 将矩阵作用转换为 Euclidean 空间上的实线性算子，保持乘法、对角算子和同调方程的导数 | 为正规形与能量估计提供坐标接口 |
| `Powerlib/Parametric/FiniteTime.lean` | 从微分方程、单边能量界和二阶残差推出 `0 ≤ t ≤ L / ε` 上的显式 `O(ε)` 误差 | 初值、轨迹存在区间及系数界明确列为前提；不是无限时间结论 |
| `Powerlib/Parametric/Linearization.lean` | 相同输入的变分方程、`C³` 给出 Jacobian 的 `C²` 性、Hessian 拆分、Taylor 二阶余项、紧参数集上的一致余项 | 变分方程使用给定的光滑轨迹族；Taylor 估计使用给定的光滑参数路径 |
| `Powerlib/Parametric/PeriodicOrbit.lean` | 光滑返回映射的局部不动点延拓、唯一性和导数；返回初值与 ODE 唯一性推出周期性 | 返回映射的光滑性和导数性质尚未由原向量场构造出来 |
| `Powerlib/Parametric/PeriodicLinear.lean` | 稳定模态的周期乘子模小于一、周期线性算子的非退化性及基底变换 | 证明指定指数模态算子的性质；尚未把它识别为非线性流的导数 |
| `Powerlib/Parametric/SmoothFixedPoint.lean` | 构造压缩映射的不动点，证明唯一性、导数非退化性和参数光滑性 | 仍需从原 ODE 构造满足这些条件的周期解算子 |
| `Powerlib/Parametric/Integration.lean` | 连接正规形的余项范数界与有限时间比较，再控制近恒等变换和投影造成的误差 | 原始非线性系统到这些算子及轨迹的构造尚未完成 |

这些是可检查的条件定理。给定一条路径的 Taylor 展开，与从向量场构造
这条路径，是两个不同的证明任务；当前文件保留这一界限。

## 尚未闭合的连接

原文假设包括：局部 `C³`、名义平衡点、Hurwitz 线性化、复可对角化、简单正频率目标模态，
以及被移除通道的非共振界。正泵频率、固定输入归一化和充分小的调制幅值属于参数条件。

最主要的缺口是：从原 `C³` 向量场构造覆盖完整 forcing period 的解流，证明它对初值与
调制幅值联合光滑，并识别返回映射的导数。没有这一步，就尚未得到原文的周期轨道存在、
唯一性及其一阶响应定理。还需要把实际周期轨道接入 Jacobian 的一致展开，并把实状态空间、
复模态空间、保留的共轭二阶块及有限时间估计完整连接。

本分支不声明原周期系统的长期 Floquet 增长率、不从残差小推断精确稳定性，也不把
“耦合随频率变化很慢”当成已经量化证明的最优频率误差界。

## 唯一保留的领域公理

最初的最小系统保留在 `Powerlib/SmallSignal.lean`：

```lean
axiom linear_spectral_criterion (A : Matrix (Fin n) (Fin n) ℝ) :
  SmallSignalStable A ↔ Hurwitz A
```

`SmallSignalStable` 是所有线性轨迹的一致指数衰减性质；`Hurwitz` 是复化矩阵的实际
特征多项式所有根实部为负。该公理的分析证明尚未完成。

新增参数调制定理不使用该公理，唯一例外是明确命名的
`envelope_smallSignalStable_iff`，它将已证明的平均矩阵谱判据翻译成原有时域接口。
平均矩阵的特征值、Hurwitz 判据、阈值及有限时间比较本身不需要领域公理。

## 构建与核验

Lean 固定为 `v4.33.0`，Mathlib 固定为 `db584cd6d46c92f209a44c0f1c829460d327499d`。

```sh
lake exe cache get
lake build
```

`PowerlibTests.lean` 检查原有标量与振子示例，并审计所有 `Powerlib` 声明的传递公理依赖。
只允许标准逻辑公理 `propext`、`Classical.choice`、`Quot.sound` 以及明确保留的谱稳定公理。
额外检查禁止参数调制证明悄悄依赖谱稳定公理，唯一允许的翻译推论如上。
`sorryAx`、额外领域公理和原生计算信任公理均会使构建失败。

分支 CI 执行同一构建；证明接受与否以 Lean 检查结果为准。
