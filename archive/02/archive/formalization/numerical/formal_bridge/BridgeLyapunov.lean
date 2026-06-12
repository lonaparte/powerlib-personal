/-
  数值→形式 桥接（Lean 层）：强网二次 Lyapunov 与弱网 l₁>0 子临界性
  Numerical → formal bridge (Lean layer).

  本文件配合：
    - conjecture_gfl_strong_grid_lyapunov.kyx  （强网局部稳定，dL/KeYmaera X 层）
    - verify_strong_grid_lyapunov.py           （数值证书：A Hurwitz, P≻0, AᵀP+PA=-I）
    - BRIDGE.md                                （桥接设计说明）

  风格沿用 archive/Dynamics.lean / DeepDifficulties.lean：
  不依赖 Mathlib 的 ODE/LaSalle 理论，而是把"沿轨迹的李导数"和"l₁ 的符号"
  写成**代数命题**，用 ring / nlinarith / positivity 检验。

  环境说明：本仓库当前环境**没有安装 Lean / lake / elan**（也没有 KeYmaera X），
  因此本文件与 .kyx 一样**未经机器核验**。下方 nlinarith/positivity/ring 的证明
  是按 Mathlib 既有能力可判定的目标书写；10 状态 l₁ 的真正障碍以 `sorry` + 注释标出。
-/

import Mathlib

noncomputable section

namespace GFLBridge

/-! ###########################################################################
    第 1 部分：强网二次 Lyapunov 的**代数核心**

    .kyx 里证的是：对平衡/时间缩放后的线性系统 x' = A x，
      V = xᵀ P x,  且  AᵀP + PA = -I  (精确有理)，
    所以李导数  V̇ = xᵀ(AᵀP+PA)x = -(x1²+…+x10²) ≤ 0。

    这里把"李导数 = -‖x‖²"这一步抽象成一个**与维数无关的代数引理**：
    只要 P 对称且 AᵀP+PA = -I，则沿 x'=Ax 的 V̇ 等于 -‖x‖²，从而 ≤ 0。
    （矩阵层面，用 Mathlib 的 Matrix；这是 dI 那一步的纯代数内容。）
    ########################################################################### -/

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 二次型 V(x) = xᵀ P x。 -/
def quadForm (P : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (P.mulVec x)

/-- 沿线性场 x' = A x 的李导数：V̇(x) = xᵀ(AᵀP + PA)x。
    （这是 d/dt [x(t)ᵀ P x(t)] 在 ẋ=Ax 下的标准恒等式；此处作为定义式给出。） -/
def lieDeriv (A P : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  x ⬝ᵥ ((Aᵀ * P + P * A).mulVec x)

/-- **桥接引理（强网 dI 核心）**：若 AᵀP + PA = -I，则 V̇(x) = -‖x‖²，故 V̇ ≤ 0。
    这正是 .kyx 里 `dI` 想要的：李导数是平方和的相反数。 -/
theorem lieDeriv_eq_neg_sq (A P : Matrix n n ℝ)
    (hLyap : Aᵀ * P + P * A = -(1 : Matrix n n ℝ)) (x : n → ℝ) :
    lieDeriv A P x = -(x ⬝ᵥ x) := by
  unfold lieDeriv
  rw [hLyap]
  -- (-(1)).mulVec x = -x ;  x ⬝ᵥ (-x) = -(x ⬝ᵥ x)
  simp [Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg]

/-- 由此立刻得到非增性（V̇ ≤ 0），对应 .kyx 的 box-模态不变式。 -/
theorem lieDeriv_nonpos (A P : Matrix n n ℝ)
    (hLyap : Aᵀ * P + P * A = -(1 : Matrix n n ℝ)) (x : n → ℝ) :
    lieDeriv A P x ≤ 0 := by
  rw [lieDeriv_eq_neg_sq A P hLyap]
  have hsq : (0 : ℝ) ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  linarith

/-! ###########################################################################
    第 2 部分：l₁>0 子临界性的**桥接** —— 把数值结论落到代数判据上

    数值层（numerical/）已严格（区间算术）给出：名义 GFL Hopf 点 l₁>0
    （subcritical/硬失稳）。Kuznetsov 投影公式：
       l₁ = (1/2ω₀) · Re⟨p, g⟩,
    其中 g = C(q,q,q̄) − 2 B(q, A⁻¹B(q,q̄)) + B(q̄, (2iω₀I−A)⁻¹B(q,q))。

    我们把 l₁ 公式拆成"符号传播"（易）与"reInner 求值"（难）两段，分别处理。
    （archive/ 里的 Lean 文件只有自然语言注释、没有这条引理；这是新写的。）
    ########################################################################### -/

/-- l₁ 的代理量：l₁ = (1/2ω)·reInner，reInner = Re⟨p,g⟩。 -/
def l1Proxy (omega reInner : ℝ) : ℝ := (1 / (2 * omega)) * reInner

/-- 子临界性判据：l₁ > 0。 -/
def IsSubcritical (l1 : ℝ) : Prop := l1 > 0

/-- **符号传播（可判定，已证）**：ω>0 ∧ reInner>0 ⟹ l₁>0（subcritical）。
    这是 l₁ 判据中**平凡**的一段（乘以正因子保号）。
    真正的困难不在这一步，而在于**计算 reInner 的符号**（见第 3、4 部分）。 -/
theorem subcritical_of_reInner_pos {omega reInner : ℝ}
    (homega : 0 < omega) (hre : 0 < reInner) :
    IsSubcritical (l1Proxy omega reInner) := by
  unfold IsSubcritical l1Proxy
  have h2 : (0 : ℝ) < 2 * omega := by linarith
  have hinv : (0 : ℝ) < 1 / (2 * omega) := by positivity
  exact mul_pos hinv hre

/-! ###########################################################################
    第 3 部分：**可处理的**降阶 l₁ 多项式不等式（桥接的"易"端）

    全 10 阶 l₁ 没有闭式（reInner 是 A、B、C 全部元素的有理函数，
    经过两次 10×10 复线性求解）。但**平面（2D）Hopf 规范形**有教科书闭式：
      ẋ = -ω y + (a x − b y)(x²+y²)/… 之类，
    其 l₁ 与场系数是显式多项式/有理式。下面给出一个**具体的、可被 nlinarith
    判定**的代理：当三阶系数组合 `cubic` 与二阶-求逆耦合项 `quad` 满足
    `cubic > quad` 且 ω>0 时，规范形 l₁ = (cubic − quad)/(8ω) > 0。
    这演示了"桥接的易端"：一旦降到低维显式多项式，符号判定就是 nlinarith。 -/

/-- 平面 Hopf 规范形 l₁ 的显式代理：l₁ = (cubic − quad)/(8ω)。 -/
def l1Planar (omega cubic quad : ℝ) : ℝ := (cubic - quad) / (8 * omega)

/-- 降阶后 l₁>0 的判定（已证，nlinarith/positivity 可关闭）：
    ω>0 且三阶项主导二阶耦合项（cubic>quad）⟹ subcritical。 -/
theorem planar_subcritical {omega cubic quad : ℝ}
    (homega : 0 < omega) (hdom : quad < cubic) :
    IsSubcritical (l1Planar omega cubic quad) := by
  unfold IsSubcritical l1Planar
  have h8 : (0 : ℝ) < 8 * omega := by linarith
  have hnum : (0 : ℝ) < cubic - quad := by linarith
  exact div_pos hnum h8

/-- 一个**完全具体**的数值实例（对应 numerical 的"硬区"符号 l₁>0）：
    取 ω=40·2π 量级的代理 ω=251、cubic=3、quad=1，则 l₁>0。
    norm_num 直接判定，演示落地的可计算性。 -/
example : IsSubcritical (l1Planar 251 3 1) := by
  unfold IsSubcritical l1Planar; norm_num

/-! ###########################################################################
    第 4 部分：真正的障碍（10 状态 l₁ 无闭式）—— 以 sorry + 注释如实标出

    下面的命题陈述了**桥接的难端**：存在一个把 (A,B,C, q, p, ω) 映到 reInner
    的（确定性）函数 `reInnerOfModel`，使得在名义 GFL 参数下 reInner>0。
    数值层已用区间算术证明此 reInner>0；但在 Lean 中要：
      (1) 形式化 10×10 复特征对 q,p（临界 ±iω₀）；
      (2) 形式化两次 10 维复线性求解 A⁻¹·, (2iω₀I−A)⁻¹·；
      (3) 形式化 B、C（向量场的二、三阶导张量）；
      (4) 对所得有理函数做精确符号符号判定（QE/nlinarith 在此规模会爆炸）。
    这些都缺少自动化，故此处 `sorry`。详见 BRIDGE.md 的"障碍"小节。 -/

/-- 占位：把模型数据映到 reInner 的抽象函数（具体定义需 (1)-(3)，此处抽象）。 -/
opaque reInnerOfModel : Unit → ℝ

/-- **难端命题（未证，open）**：名义 GFL Hopf 点 reInner>0，从而 l₁>0。
    数值层（ivcert.py 区间算术）已严格证明；Lean 形式化是 open problem。 -/
theorem gfl_nominal_reInner_pos : 0 < reInnerOfModel () := by
  sorry

/-- 把"难端"与"符号传播"接起来：一旦 reInner>0 被证（无论数值还是将来 Lean），
    名义 GFL 即 subcritical。注意 ω>0 是 Hopf 频率，恒成立。 -/
theorem gfl_nominal_subcritical (omega : ℝ) (homega : 0 < omega) :
    IsSubcritical (l1Proxy omega (reInnerOfModel ())) :=
  subcritical_of_reInner_pos homega gfl_nominal_reInner_pos

end GFLBridge
