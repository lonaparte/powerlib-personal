# 最终障碍清单（经多轮核实）

> 2026.05 | 电力电子化电力系统 × 非线性 pH-DAE × Lean 4/Mathlib

---

## 已确认不是障碍的（Mathlib 中已有或可直接构造）

| 项目 | Mathlib 模块 |
|------|-------------|
| 隐函数定理 | `Mathlib.Analysis.Calculus.Implicit`（三个版本） |
| Schur 补 + 行列式公式 | `Mathlib.LinearAlgebra.Matrix.SchurComplement` |
| 分块矩阵代数 | `Mathlib.Data.Matrix.Block`（fromBlocks/乘法/转置） |
| 正定/半正定 + 合同变换保持 | `Mathlib.LinearAlgebra.Matrix.PosDef` |
| 分块正定 ↔ Schur 补正定 | `Matrix.PosDef.fromBlocks₁₁` |
| 二次型限制到子模 | `QuadraticMap.restrict` |
| 图 Laplacian 核维数 = 连通分量数 | `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` |
| Laplacian 半正定 | `SimpleGraph.posSemidef_lapMatrix` |
| S¹ 拓扑 / AddCircle | `Mathlib.Topology.Instances.AddCircle` |
| 可微性自动化 | `fun_prop` tactic |
| Knaster-Tarski 不动点 | `Mathlib.Order.FixedPoints` |
| 矩阵束 det(sE-A) 的表达 | `Matrix.det` over `Polynomial ℝ`（可表达，缺定理） |
| KKT 条件 | 独立 Lean 4 项目 arXiv:2503.18821（未入 Mathlib） |

---

## 真正的障碍（4 个）

### 障碍 1：非线性 DAE 的约束一致性——沿轨迹保持 index-1

**问题**：非线性 pH-DAE 的代数约束 g(x_d, x_a) = 0 通过隐函数定理给出
局部参数化 x_a = h(x_d)。但"局部"不够——需要沿整条轨迹保持：
- ∂g/∂x_a 非奇异（index-1 条件）
- x_a = h(x_d) 的解析延拓

**在 PHS 框架下的论证**：
1. Ḣ ≤ 0 → H(x(t)) ≤ H(x(0)) → x(t) ∈ {H ≤ c}（亚水平集）
2. 若 H 正常（proper）→ 亚水平集紧
3. ∂g/∂x_a 在紧集上连续且处处非奇异 → 在紧集上一致可逆
4. → index-1 沿轨迹保持

**形式化难度**：每一步 Mathlib 都有工具（紧集上连续函数有界/有极值、
连续非零函数在紧集上有正下界），但需要把 4 步串联成完整论证。
这是"引理组合"类型的工作，不是缺基础设施。

**估计**：~300-500 行 Lean 代码

---

### 障碍 2：调制 Dirac 结构的组合

**问题**：Cervera-van der Schaft-Baños (2007) 的组合定理证明了：
常数 Dirac 结构的组合仍是 Dirac 结构。但电力系统中变换器的
(J(x), R(x)) 可能状态依赖，对应的 Dirac 结构是逐点定义的。

需要证明：若 D₁(x) 和 D₂(x) 对每个 x 都是 Dirac 结构，
且互联约束与 x 无关（网络拓扑固定），
则组合 D₁(x) ‖ D₂(x) 对每个 x 仍是 Dirac 结构。

**实际上这可能不难**：如果 Dirac 结构的定义是逐点的
（对每个 x，D(x) 是流-势空间的极大各向同性子空间），
则组合定理可以逐点应用。关键是网络 Dirac 结构（关联矩阵）
是常数，所以组合操作对 x 是光滑/连续的。

**数学文献状态**：van der Schaft & Maschke (2018) 处理了
非线性 Dirac 结构，但形式化要求把"逐点应用"精确化。

**估计**：~200-400 行（如果逐点应用成立则较少）

---

### 障碍 3：Dirac 结构 + pH 系统的类型设计

**问题**：这不是数学定理，而是**形式化设计选择**——
没有先例可参考，需要回答：

(a) 流（flow）和势（effort）用什么类型表示？
    - 选项：Fin n → ℝ？EuclideanSpace？抽象 Banach 空间？
    - 需要支持内积/配对 ⟨e | f⟩

(b) Dirac 结构如何定义？
    - 选项 1：流-势空间的子空间，满足 D = D⊥（关于对称双线性形式）
    - 选项 2：矩阵对 (F, E) 使得 F'E + E'F = 0 且 [F E] 满秩
    - 选项 1 更抽象但更通用，选项 2 更具体但更好算

(c) pH 系统如何参数化？
    - 用 (E, J, R, Q, H) 的 structure？
    - 还是 (Dirac 结构, 储能元件, 耗散元件, 端口) 的几何定义？
    - 前者对应 Mehrmann 学派（代数），后者对应 van der Schaft 学派（几何）

(d) 组合运算如何类型化？
    - 两个 pH 系统组合：端口维度的类型级加法（p₁ + p₂）
    - Lean 的类型系统支持这种依值类型运算，但设计细节影响后续证明难度

**这是整个项目中最需要前期设计的部分。**
设计选错了不会导致数学错误，但会导致后续所有证明极其繁琐。
建议参考 EPHS 建模语言 (arXiv:2402.17640) 的 operad 语法设计。

**估计**：~500-800 行（定义 + 基本引理），但设计时间可能比编码时间长

---

### 障碍 4：Shifted Hamiltonian 在约束流形上的正定性

**问题**：电力系统运行在非零平衡点 x*。需要 shifted Hamiltonian

  H_s(x) = H(x) - H(x*) - ∇H(x*)'(x - x*)

在约束流形 M = {g = 0} 上、x* 附近正定。这要求：

  ∇²H(x*) 限制在 M 在 x* 处的切空间上是正定的

对含 -cos δ 的能量函数：Hessian 含 cos δ* 项，
需要条件 |δ*| < π/2。

**形式化难度**：
(a) Hessian 作为双线性型：Mathlib 有 iteratedFDeriv 但没有
    将其解释为 PosDef 双线性型的接口
(b) "限制到切空间"：需要用隐函数定理参数化 M，
    然后对参数化函数求二阶导。零件都有但需要组合。
(c) cos δ* > 0 条件：这是简单的前提假设，不是证明困难

**估计**：~300-600 行

---

## 总工作量（修正后）

| 模块 | 行数 | 性质 |
|------|------|------|
| Dirac 结构类型设计 + 定义 | 500-800 | 设计驱动 |
| pH-ODE 定义 + 能量平衡 | 200-400 | 代数推导 |
| Dirac 结构组合定理 | 300-600 | 线性代数（逐点） |
| pH-DAE 扩展（E 奇异） | 300-500 | 代数推导 |
| 约束一致性（沿轨迹 index-1） | 300-500 | 引理组合 |
| Shifted Hamiltonian 正定性 | 300-600 | 微积分+线性代数 |
| 五原型实例化 | 500-1000 | 参数化实例 |
| 网络互联（图 → Dirac） | 300-500 | 图论→线性代数 |
| 端到端案例 | 500-1000 | 整合 |
| **总计** | **3200-5900** | |

---

## 结论

经过多轮核实，障碍从最初的"10+ 个"收缩到了 **4 个**，
且没有一个是理论上不可能的：

1. 约束一致性 — 引理组合，不缺零件
2. 调制 Dirac 组合 — 可能逐点应用即可，待确认
3. 类型设计 — 工程设计问题，不是数学问题
4. Shifted Hessian — 零件在，需要胶水

**最大的风险不在任何单个障碍，而在于类型设计（障碍 3）——
一个好的设计让后续一切顺畅，一个差的设计让每个证明都痛苦。**
