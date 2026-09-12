# Powerlib：最小小信号稳定性公理化

这一版只处理给定实矩阵 `A` 的连续时间线性系统 `δx' = A δx`。
“小信号稳定”在这里精确定义为**线性系统的指数稳定**。

## 四个定义、一个公理

`Powerlib.lean` 包含：

1. `IsTrajectory A x`：`x` 是满足线性微分方程的全局可微轨迹。
2. `SmallSignalStable A`：存在与轨迹及初值无关的 `C > 0`、`α > 0`，使任意轨迹在
   `t ≥ 0` 时满足 `‖x(t)‖ ≤ C exp(-α t) ‖x(0)‖`。范数采用有限乘积空间的范数。
3. `HasEigenvalue A z`：`z : ℂ` 是 `A` 复化后**实际特征多项式**的根。
4. `Hurwitz A`：所有上述根均满足 `Re(z) < 0`。

唯一新增的领域公理是：

```lean
axiom linear_spectral_criterion (A : Matrix (Fin n) (Fin n) ℝ) :
  SmallSignalStable A ↔ Hurwitz A
```

两个定义分别表达时域性质和谱性质，公理连接二者。
**这条谱判据目前是显式假设，其分析证明尚未在本项目中完成。**
两个通用推论，以及示例的稳定性结论，均依赖该公理。

## 使用与验证

安装与 `lean-toolchain` 一致的 Lean 后，在仓库根目录运行：

```sh
lake exe cache get
lake build
```

`lake build` 同时编译核心和 `PowerlibTests.lean`，后者检查：

- 参数化的一维系统：`SmallSignalStable [a] ↔ a < 0`。
- `a = -1`、`a = 1`、`a = 0` 三个边界与符号示例。
- 二维无阻尼振子：特征值 `i` 的实部为零，因此不满足指数稳定判据。
- 所有 `Powerlib` 命名空间声明的传递公理依赖：只允许 Lean 的标准逻辑公理
  `propext`、`Classical.choice`、`Quot.sound` 的子集及上述唯一领域公理；
  `sorryAx`、额外领域公理与原生计算信任公理会导致构建失败。

Lean 固定为 `v4.33.0`，Mathlib 固定到该版本对应的提交，依赖记录在
`lake-manifest.json`。分支 CI 执行同一构建。

## 范围

输入 `A` 是已经给定的线性化状态矩阵。本版不证明它是某个非线性模型的 Jacobian，
也不处理奇异 DAE、未消除的参考角自由度或离散时间系统。
虚轴特征值只排除这里定义的指数稳定，不能单凭这一结果判定原非线性系统失稳。
本版提供精确命题和证明接口，不包含浮点特征值求解器。

数学背景可参照 [MIT 的线性系统与 Lyapunov 分析讲义](https://underactuated.mit.edu/lyapunov.html)。
特征多项式直接复用 [Mathlib 的定义](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean)。

`archive/` 保留原有草稿，不参与该工程的导入和构建。
